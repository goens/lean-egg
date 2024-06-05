import Lean.Elab.Term
import Egg

elab "Type*" : term => do
  let u ← Lean.Meta.mkFreshLevelMVar
  Lean.Elab.Term.levelMVarToParam (.sort (.succ u))

class Bracket (L M : Type*) where
  bracket : L → M → M

notation "⁅" x ", " y "⁆" => Bracket.bracket x y

class AddSemigroup (G : Type u) extends Add G where
  /-- Addition is associative -/
  add_assoc : ∀ a b c : G, a + b + c = a + (b + c)

class Zero.{u} (α : Type u) where
  zero : α
class One (α : Type u) where
  one : α

instance (priority := 300) Zero.toOfNat0 {α} [Zero α] : OfNat α (nat_lit 0) where
  ofNat := ‹Zero α›.1
instance (priority := 200) Zero.ofOfNat0 {α} [OfNat α (nat_lit 0)] : Zero α where
  zero := 0

instance (priority := 300) One.toOfNat1 {α} [One α] : OfNat α (nat_lit 1) where
  ofNat := ‹One α›.1
instance (priority := 200) One.ofOfNat1 {α} [OfNat α (nat_lit 1)] : One α where
  one := 1

class HSMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hSMul : α → β → γ

infixr:73 " • " => HSMul.hSMul
macro_rules | `($x • $y) => `(leftact% HSMul.hSMul $x $y)

class AddZeroClass (M : Type u) extends Zero M, Add M where
  /-- Zero is a left neutral element for addition -/
  protected zero_add : ∀ a : M, 0 + a = a
  /-- Zero is a right neutral element for addition -/
  protected add_zero : ∀ a : M, a + 0 = a

class AddMonoid (M : Type u) extends AddSemigroup M, AddZeroClass M where
  protected nsmul : ℕ → M → M
  protected nsmul_zero : ∀ x, nsmul 0 x = 0 := by intros; rfl
  protected nsmul_succ : ∀ (n : Nat) (x), nsmul (n + 1) x = nsmul n x + x := by intros; rfl

def SubNegMonoid.sub' {G : Type u} [AddMonoid G] [Neg G] (a b : G) : G := a + -b

class SubNegMonoid (G : Type u) extends AddMonoid G, Neg G, Sub G where
  sub := SubNegMonoid.sub'
  sub_eq_add_neg : ∀ a b : G, a - b = a + -b := by intros; rfl
  /-- Multiplication by an integer.
  Set this to `zsmulRec` unless `Module` diamonds are possible. -/
  zsmul : ℤ → G → G
  zsmul_zero' : ∀ a : G, zsmul 0 a = 0 := by intros; rfl
  zsmul_succ' (n : Nat) (a : G) :
      zsmul (Int.ofNat n.succ) a = zsmul (Int.ofNat n) a + a := by
    intros; rfl
  zsmul_neg' (n : Nat) (a : G) : zsmul (Int.negSucc n) a = -zsmul n.succ a := by
    intros; rfl

class AddGroup (A : Type u) extends SubNegMonoid A where
  add_left_neg : ∀ a : A, -a + a = 0

class AddCommMagma (G : Type u) extends Add G where
  add_comm : ∀ a b : G, a + b = b + a

class AddCommSemigroup (G : Type u) extends AddSemigroup G, AddCommMagma G where

class AddCommMonoid (M : Type u) extends AddMonoid M, AddCommSemigroup M

class AddCommGroup (G : Type u) extends AddGroup G, AddCommMonoid G

class Distrib (R : Type*) extends Mul R, Add R where
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

class MulZeroClass (M₀ : Type u) extends Mul M₀, Zero M₀ where
  zero_mul : ∀ a : M₀, 0 * a = 0
  mul_zero : ∀ a : M₀, a * 0 = 0

class NonUnitalNonAssocSemiring (α : Type u) extends AddCommMonoid α, Distrib α, MulZeroClass α
class Semigroup (G : Type u) extends Mul G where
  mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)
class SemigroupWithZero (S₀ : Type u) extends Semigroup S₀, MulZeroClass S₀
class NonUnitalSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, SemigroupWithZero α
class MulOneClass (M : Type u) extends One M, Mul M where
  one_mul : ∀ a : M, 1 * a = a
  mul_one : ∀ a : M, a * 1 = a
class MulZeroOneClass (M₀ : Type u) extends MulOneClass M₀, MulZeroClass M₀

def Nat.unaryCast [One R] [Zero R] [Add R] : Nat → R
  | 0 => 0
  | n + 1 => Nat.unaryCast n + 1

class AddMonoidWithOne (R : Type*) extends NatCast R, AddMonoid R, One R where
  natCast := Nat.unaryCast
  natCast_zero : natCast 0 = 0 := by intros; rfl
  natCast_succ : ∀ n, natCast (n + 1) = natCast n + 1 := by intros; rfl

class AddCommMonoidWithOne (R : Type*) extends AddMonoidWithOne R, AddCommMonoid R

class NonAssocSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, MulZeroOneClass α,
    AddCommMonoidWithOne α

class NonUnitalNonAssocRing (α : Type u) extends AddCommGroup α, NonUnitalNonAssocSemiring α

class NonUnitalRing (α : Type*) extends NonUnitalNonAssocRing α, NonUnitalSemiring α

def Int.castDef {R : Type u} [NatCast R] [Neg R] : Int → R
  | (n : Nat) => n
  | Int.negSucc n => -(n + 1 : Nat)

class AddGroupWithOne (R : Type u) extends IntCast R, AddMonoidWithOne R, AddGroup R where
  intCast := Int.castDef
  intCast_ofNat : ∀ n : Nat, intCast (n : Nat) = Nat.cast n := by intros; rfl
  intCast_negSucc : ∀ n : Nat, intCast (Int.negSucc n) = - Nat.cast (n + 1) := by intros; rfl

class AddCommGroupWithOne (R : Type u)
  extends AddCommGroup R, AddGroupWithOne R, AddCommMonoidWithOne R

class NonAssocRing (α : Type*) extends NonUnitalNonAssocRing α, NonAssocSemiring α,
    AddCommGroupWithOne α

def npowRec [One M] [Mul M] : Nat → M → M
  | 0, _ => 1
  | n + 1, a => npowRec n a * a

class Monoid (M : Type u) extends Semigroup M, MulOneClass M where
  npow : Nat → M → M := npowRec
  npow_zero : ∀ x, npow 0 x = 1 := by intros; rfl
  npow_succ : ∀ (n : Nat) (x), npow (n + 1) x = npow n x * x := by intros; rfl

class MonoidWithZero (M₀ : Type u) extends Monoid M₀, MulZeroOneClass M₀, SemigroupWithZero M₀

class Semiring (α : Type u) extends NonUnitalSemiring α, NonAssocSemiring α, MonoidWithZero α
class Ring (R : Type u) extends Semiring R, AddCommGroup R, AddGroupWithOne R
class CommMagma (G : Type u) extends Mul G where
  mul_comm : ∀ a b : G, a * b = b * a
class CommSemigroup (G : Type u) extends Semigroup G, CommMagma G where
class CommMonoid (M : Type u) extends Monoid M, CommSemigroup M
class CommRing (α : Type u) extends Ring α, CommMonoid α
class SMul (M : Type u) (α : Type v) where
  smul : M → α → α

instance instHSMul {α β} [SMul α β] : HSMul α β β where
  hSMul := SMul.smul

class MulAction (α : Type*) (β : Type*) [Monoid α] extends SMul α β where
  one_smul : ∀ b : β, (1 : α) • b = b
  mul_smul : ∀ (x y : α) (b : β), (x * y) • b = x • y • b

class DistribMulAction (M A : Type*) [Monoid M] [AddMonoid A] extends MulAction M A where
  smul_zero : ∀ a : M, a • (0 : A) = 0
  smul_add : ∀ (a : M) (x y : A), a • (x + y) = a • x + a • y

class Module (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] extends
  DistribMulAction R M where
  add_smul : ∀ (r s : R) (x : M), (r + s) • x = r • x + s • x
  zero_smul : ∀ x : M, (0 : R) • x = 0

class LieRing (L : Type v) extends AddCommGroup L, Bracket L L where
  add_lie : ∀ x y z : L, ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆
  lie_add : ∀ x y z : L, ⁅x, y + z⁆ = ⁅x, y⁆ + ⁅x, z⁆
  lie_self : ∀ x : L, ⁅x, x⁆ = 0
  leibniz_lie : ∀ x y z : L, ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆

class LieAlgebra (R : Type u) (L : Type v) [CommRing R] [LieRing L] extends Module R L where
  lie_smul : ∀ (t : R) (x y : L), ⁅x, t • y⁆ = t • ⁅x, y⁆

class LieRingModule (L : Type v) (M : Type w) [LieRing L] [AddCommGroup M] extends Bracket L M where
  add_lie : ∀ (x y : L) (m : M), ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆
  lie_add : ∀ (x : L) (m n : M), ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆
  leibniz_lie : ∀ (x y : L) (m : M), ⁅x, ⁅y, m⁆⁆ = ⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆

class LieModule (R : Type u) (L : Type v) (M : Type w) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] : Prop where
  smul_lie : ∀ (t : R) (x : L) (m : M), ⁅t • x, m⁆ = t • ⁅x, m⁆
  lie_smul : ∀ (t : R) (x : L) (m : M), ⁅x, t • m⁆ = t • ⁅x, m⁆

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁}
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]
variable (t : R) (x y z : L) (m n : M)

theorem lie_zero : ⁅x, 0⁆ = (0 : M) :=
  sorry --(AddMonoidHom.mk' _ (lie_add x)).map_zero

theorem zero_lie : ⁅(0 : L), m⁆ = 0 :=
  sorry --(AddMonoidHom.mk' (fun x : L => ⁅x, m⁆) fun x y => add_lie x y m).map_zero

theorem lie_self : ⁅x, x⁆ = 0 :=
  LieRing.lie_self x

instance lieRingSelfModule : LieRingModule L L :=
  { (inferInstance : LieRing L) with }

theorem neg_eq_iff_add_eq_zero [AddGroup G] {a b : G} : -a = b ↔ a + b = 0 := by sorry

set_option trace.egg true in
@[simp]
theorem lie_skew : -⁅y, x⁆ = ⁅x, y⁆ := by
  have h : ⁅x + y, x⁆ + ⁅x + y, y⁆ = 0 := by egg [LieRing.lie_add, lie_self, neg_eq_iff_add_eq_zero, lie_zero, zero_lie, LieRing.leibniz_lie, LieRing.add_lie] --rw [← lie_add]; apply lie_self
  egg [LieRing.lie_add, lie_self, neg_eq_iff_add_eq_zero, lie_zero, zero_lie, LieRing.leibniz_lie, LieRing.add_lie]
