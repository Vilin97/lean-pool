/-
Copyright (c) 2026 Scott Harper, Peiran Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Harper, Peiran Wu
-/
import LeanPool.OrderPQ.PrimeOrder
import Mathlib.Data.ZMod.Aut
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# LeanPool.OrderPQ.MulZMod
-/

section MulZMod

/-- `ZMod n` viewed as a multiplicative group. -/
def MulZMod (n : ℕ) : Type := Multiplicative (ZMod n)

instance {n : ℕ} : DecidableEq (MulZMod n) := instDecidableEqMultiplicative

instance {n : ℕ} [NeZero n] : Fintype (MulZMod n) := Multiplicative.fintype

instance {n : ℕ} : Mul (MulZMod n) := Multiplicative.mul

instance {n : ℕ} : MulOneClass (MulZMod n) := Multiplicative.mulOneClass

instance {n : ℕ} : Group (MulZMod n) := Multiplicative.group

instance {n : ℕ} : IsCyclic (MulZMod n) := isCyclic_multiplicative

@[simp]
lemma card_mulZMod {n : ℕ} [NeZero n] : Fintype.card (MulZMod n) = n := by
  have : Fintype.card (MulZMod n) = Fintype.card (ZMod n) :=
    Fintype.card_multiplicative (ZMod n)
  rw [this, ZMod.card]

lemma nat_card_mulZMod {n : ℕ} [NeZero n] : Nat.card (MulZMod n) = n := by simp

variable {p : ℕ} [hp : Fact p.Prime]

/-- A nonzero element of `ZMod p` (with `p` prime) viewed as a unit. -/
def unitOfNeZero (x : ZMod p) (hx : x ≠ 0) : (ZMod p)ˣ := by
  refine ZMod.unitOfCoprime x.val (Nat.coprime_of_lt_prime ?_ (ZMod.val_lt x) hp.elim).symm
  simp only [ne_eq, ZMod.val_eq_zero, hx, not_false_eq_true]

@[simp]
lemma val_unitOfNeZero (x : ZMod p) (hx : x ≠ 0) : ((unitOfNeZero x hx) : ZMod p) = x := by
  simp [unitOfNeZero, ZMod.coe_unitOfCoprime]

@[simp]
lemma unitOfNeZero_val (x : (ZMod p)ˣ) : unitOfNeZero x (Units.ne_zero _) = x := by
  ext
  exact val_unitOfNeZero _ (Units.ne_zero _)

/-- Multiplication by a unit in `ZMod p` as an additive automorphism. -/
@[simps -isSimp]
def addAutOfUnit (x : (ZMod p)ˣ) : AddAut (ZMod p) where
  toFun a := x.val * a
  invFun a := x.inv * a
  left_inv _ := by simp_rw [← mul_assoc, x.inv_val, one_mul]
  right_inv _ := by simp_rw [← mul_assoc, x.val_inv, one_mul]
  map_add' a b := by simp_rw [mul_add]

variable (p)

/-- The group of additive automorphisms of `ZMod p` (with `p` prime) is isomorphic to the
group of units of `ZMod p`. -/
def mulEquivAddAutZMod : AddAut (ZMod p) ≃+ Additive (ZMod p)ˣ :=
  ZMod.AddAutEquivUnits p

/-- The group of multiplicative automorphisms of `MulZMod p` (with `p` prime) is isomorphic
to the group of units of `ZMod p`. -/
def mulEquivMulAutMulZMod : MulAut (MulZMod p) ≃* (ZMod p)ˣ :=
  (MulAutMultiplicative (ZMod p)).trans (AddEquiv.toMultiplicativeLeft (mulEquivAddAutZMod p))

noncomputable instance : Fintype (MulAut (MulZMod p)) :=
  Fintype.ofEquiv (ZMod p)ˣ (mulEquivMulAutMulZMod p).symm.toEquiv

lemma mulAut_MulZMod_isCyclic : IsCyclic (MulAut (MulZMod p)) :=
  isCyclic_of_surjective (mulEquivMulAutMulZMod p).symm (mulEquivMulAutMulZMod p).symm.surjective

lemma addAut_ZMod_isCyclic : IsCyclic (Multiplicative (AddAut (ZMod p))) :=
  isCyclic_of_surjective (AddEquiv.toMultiplicativeLeft (mulEquivAddAutZMod p)).symm
    (AddEquiv.toMultiplicativeLeft (mulEquivAddAutZMod p)).symm.surjective

@[simp]
lemma card_mulAut_mulZMod :
    Fintype.card (MulAut (MulZMod p)) = p - 1 := by
  rw [Fintype.card_congr (mulEquivMulAutMulZMod p).toEquiv,
    ZMod.card_units_eq_totient, Nat.totient_prime hp.elim]

lemma nat_card_mulAut_mulZMod :
    Nat.card (MulAut (MulZMod p)) = p - 1 := by
  simp only [Nat.card_eq_fintype_card, card_mulAut_mulZMod]

end MulZMod
