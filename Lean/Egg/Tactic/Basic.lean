import Egg.Core.Request.Basic
import Egg.Core.Explanation.Proof
import Egg.Tactic.Config.Option
import Egg.Tactic.Config.Modifier
import Egg.Tactic.Base
import Egg.Tactic.Guides
import Egg.Tactic.Premises.Gen
import Egg.Tactic.Trace
import Lean

open Lean Meta Elab Tactic

namespace Egg

-- Note: If `base? ≠ none`, the goal is an auxiliary goal and needs to be handled specially after
--       proof reconstruction.
private structure Goal extends Congr where
  id    : MVarId
  base? : Option FVarId

private def parseGoal (goal : MVarId) (base? : Option (TSyntax `egg_base)) : MetaM Goal := do
  let base? ← base?.mapM parseBase
  let cgr ← getCongr (← goal.getType') base?
  return { cgr with id := goal, base? }
where
  getCongr (goalType : Expr) (base? : Option FVarId) : MetaM Congr := do
    if let some base := base? then
      Congr.from! (← mkEq (← base.getType) goalType)
    else if let some c ← Congr.from? goalType then
      return c
    else
      throwError "expected goal to be of type '=' or '↔', but found:\n{← ppExpr goalType}"

-- TODO: We should also consider the level mvars of all `Fact`s.
private def collectAmbientMVars (goal : Goal) (guides : Guides) (proofErasure : Bool) :
    MetaM MVars.Ambient := do
  let expr ← MVars.Ambient.Expr.get
  let goalLvl := (← MVars.collect (← goal.expr) proofErasure).lvl
  let guidesLvl ← guides.foldlM (init := ∅) fun res g =>
    return res.merge (← MVars.collect g.expr proofErasure).lvl
  return { expr, lvl := goalLvl.merge guidesLvl }

private def resultToProof
    (result : Request.Result) (goal : Goal) (rws : Rewrites) (facts : Facts) (ctx : EncodingCtx)
    : TacticM Expr := do
  let proof ← result.expl.proof rws facts result.egraph ctx
  proof.trace `egg.proof
  let mut prf ← proof.prove goal.toCongr
  prf ← instantiateMVars prf
  withTraceNode `egg.proof.term (fun _ => return "Proof Term") do trace[egg.proof.term] prf
  -- When `goal.base? = some base`, then `proof` is a proof of `base = <goal type>`. We turn this
  -- into a proof of `<goal type>` here.
  if let some base := goal.base? then prf ← mkEqMP prf (.fvar base)
  catchLooseMVars prf ctx.amb proof.subgoals
  -- TODO: These mvars have the wrong depth.
  appendGoals proof.subgoals
  return prf
where
  catchLooseMVars (prf : Expr) (amb : MVars.Ambient) (subgoals : List MVarId) : MetaM Unit := do
    let mvars ← MVars.collect prf (proofErasure := false)
    for mvar in mvars.expr do
      unless subgoals.contains mvar || amb.expr.contains mvar do
        throwError m!"egg: final proof contains expression mvar {Expr.mvar mvar}"
    for lmvar in mvars.lvl do
      unless amb.lvl.contains lmvar do
        throwError m!"egg: final proof contains level mvar {Level.mvar lmvar}"

open Config.Modifier (egg_cfg_mod)

protected def eval
    (mod : TSyntax ``egg_cfg_mod) (prems : TSyntax `egg_premises) (base : Option (TSyntax `egg_base))
    (guides : Option (TSyntax `egg_guides)) (basket? : Option Name := none) : TacticM Unit := do
  let startTime ← IO.monoMsNow
  let goal ← getMainGoal
  let mod  ← Config.Modifier.parse mod
  let cfg := { (← Config.fromOptions).modify mod with basket? }
  cfg.trace `egg.config
  goal.withContext do
    let goal ← parseGoal goal base
    let guides := (← guides.mapM Guides.parseGuides).getD #[]
    let amb ← collectAmbientMVars goal guides cfg.eraseProofs
    amb.trace `egg.ambient
    -- We increase the mvar context depth, so that ambient mvars aren't unified during proof
    -- reconstruction. Note that this also means that we can't assign the `goal` mvar within this
    -- do-block.
    let proof? ← withNewMCtxDepth do
      let (rws, facts) ← Premises.gen goal.toCongr prems guides cfg amb
      let req ← Request.encoding goal.toCongr rws facts guides cfg amb
      withTraceNode `egg.encoded (fun _ => return "Encoded") do req.trace `egg.encoded
      if let .beforeEqSat := cfg.exitPoint then return none
      let result ← req.run fun failReport => do
        let msg := s!"egg failed to prove the goal ({failReport.stopReason.description}) "
        unless cfg.reporting do throwError msg
        throwError msg ++ formatReport cfg.flattenReports failReport
      if let .beforeProof := cfg.exitPoint then return none
      let beforeProof ← IO.monoMsNow
      let prf ← resultToProof result goal rws facts {amb, cfg}
      let proofTime := (← IO.monoMsNow) - beforeProof
      if cfg.reporting then
        let totalTime := (← IO.monoMsNow) - startTime
        logInfo (s!"egg succeeded " ++ formatReport cfg.flattenReports result.report totalTime proofTime result.expl)
      return some prf
    if let some proof := proof?
    then goal.id.assignIfDefeq' proof
    else goal.id.admit

syntax &"egg" egg_cfg_mod egg_premises (egg_base)? (egg_guides)? : tactic
elab_rules : tactic
  | `(tactic| egg $mod $prems $[$base]? $[$guides]?) => Egg.eval mod prems base guides

-- WORKAROUND: This fixes `Tests/EndOfInput *`.
macro "egg" mod:egg_cfg_mod : tactic => `(tactic| egg $mod)

elab "egg!" mod:egg_cfg_mod prems:egg_premises base:(egg_base)? guides:(egg_guides)? : tactic =>
  Egg.eval mod prems base guides `egg

-- WORKAROUND: This fixes a problem analogous to `Tests/EndOfInput *` for `egg!`.
macro "egg!" mod:egg_cfg_mod : tactic => `(tactic| egg! $mod)
