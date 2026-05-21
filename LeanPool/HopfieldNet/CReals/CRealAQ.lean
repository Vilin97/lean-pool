/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.CReals.CRealRep

namespace Computable

/--
Extensional computable real numbers backed by an approximate-rational implementation `AQ`.

This is the `Quotient` of computational representatives (`CRealRep AQ`) by the setoid
whose equivalence is defined by agreement in the ℚ-specification model (`CReal.Pre`).

Design goal:
* proofs are done once against the ℚ model (`CReal` from `CRealPre.lean`),
* implementations can run fast against a concrete `AQ` (e.g. `Dyadic`) by working
  on representatives and using the transport lemmas.
-/
abbrev CRealAQ (AQ : Type) [ApproxRationals AQ] : Type :=
  Quotient (inferInstance : Setoid (CRealRep AQ))

namespace CRealAQ

variable {AQ : Type} [ApproxRationals AQ]

/-- Denotation into the existing extensional `CReal` (the ℚ-quotient). -/
def toCReal : CRealAQ AQ → CReal :=
  Quotient.lift (fun x : CRealRep AQ => CRealRep.denote (AQ := AQ) x)
    (by
      intro x y h
      exact CRealRep.denote_congr (AQ := AQ) h)

@[simp] theorem toCReal_mk (x : CRealRep AQ) :
    toCReal (AQ := AQ) (Quotient.mk _ x) = CRealRep.denote (AQ := AQ) x := rfl

theorem toCReal_injective : Function.Injective (toCReal (AQ := AQ)) := by
  intro a b hab
  refine Quotient.inductionOn₂ a b (fun x y => ?_) hab
  -- `hab : denote x = denote y` in the ℚ-quotient.
  intro hab
  have hpre : CReal.Pre.Equiv x.toPre y.toPre := Quotient.exact hab
  exact Quotient.sound hpre

/-- Coercion of computational representatives to the extensional quotient. -/
abbrev ofRep (x : CRealRep AQ) : CRealAQ AQ := Quotient.mk _ x

instance : Coe (CRealRep AQ) (CRealAQ AQ) := ⟨ofRep (AQ := AQ)⟩

/-- Rounded addition on the quotient, defined by lifting `CRealRep.addC`. -/
instance : Add (CRealAQ AQ) where
  add a b :=
    Quotient.liftOn₂ a b (fun x y : CRealRep AQ => (CRealRep.addC x y : CRealAQ AQ))
      (by
        intro x₁ x₂ y₁ y₂ hx hy
        exact Quotient.sound (CRealRep.addC_respects_equiv (AQ := AQ) hx hy))

/-- Rounded multiplication on the quotient, defined by lifting `CRealRep.mulC`. -/
instance : Mul (CRealAQ AQ) where
  mul a b :=
    Quotient.liftOn₂ a b (fun x y : CRealRep AQ => (CRealRep.mulC x y : CRealAQ AQ))
      (by
        intro x₁ x₂ y₁ y₂ hx hy
        exact Quotient.sound (CRealRep.mulC_respects_equiv (AQ := AQ) hx hy))

instance : Neg (CRealAQ AQ) where
  neg a :=
    Quotient.liftOn a (fun x : CRealRep AQ => (CRealRep.neg x : CRealAQ AQ))
      (by
        intro x y h
        exact Quotient.sound (CRealRep.neg_respects_equiv (AQ := AQ) h))

instance : Zero (CRealAQ AQ) where
  zero := (CRealRep.zero (AQ := AQ) : CRealAQ AQ)

instance : One (CRealAQ AQ) where
  one := (CRealRep.one (AQ := AQ) : CRealAQ AQ)

/-- `toCReal` is compatible with the rounded operations (simp normal form). -/
@[simp] theorem toCReal_zero : toCReal (AQ := AQ) (0 : CRealAQ AQ) = 0 := by
  change toCReal (AQ := AQ) (Quotient.mk _ (CRealRep.zero (AQ := AQ))) = 0
  simp [CRealAQ.toCReal, CRealRep.denote_zero (AQ := AQ)]

@[simp] theorem toCReal_one : toCReal (AQ := AQ) (1 : CRealAQ AQ) = 1 := by
  change toCReal (AQ := AQ) (Quotient.mk _ (CRealRep.one (AQ := AQ))) = 1
  simp [CRealAQ.toCReal, CRealRep.denote_one (AQ := AQ)]

@[simp] theorem toCReal_neg (a : CRealAQ AQ) :
    toCReal (AQ := AQ) (-a) = - toCReal (AQ := AQ) a := by
  refine Quotient.inductionOn a (fun x => ?_)
  change toCReal (AQ := AQ) (Quotient.mk _ (CRealRep.neg x)) =
    - toCReal (AQ := AQ) (Quotient.mk _ x)
  simp [CRealAQ.toCReal, CRealRep.denote_neg (AQ := AQ)]

@[simp] theorem toCReal_add (a b : CRealAQ AQ) :
    toCReal (AQ := AQ) (a + b) = toCReal (AQ := AQ) a + toCReal (AQ := AQ) b := by
  refine Quotient.inductionOn₂ a b (fun x y => ?_)
  change toCReal (AQ := AQ) (Quotient.mk _ (CRealRep.addC x y)) =
    toCReal (AQ := AQ) (Quotient.mk _ x) + toCReal (AQ := AQ) (Quotient.mk _ y)
  simp [CRealAQ.toCReal, CRealRep.denote_addC (AQ := AQ)]

@[simp] theorem toCReal_mul (a b : CRealAQ AQ) :
    toCReal (AQ := AQ) (a * b) = toCReal (AQ := AQ) a * toCReal (AQ := AQ) b := by
  refine Quotient.inductionOn₂ a b (fun x y => ?_)
  change toCReal (AQ := AQ) (Quotient.mk _ (CRealRep.mulC x y)) =
    toCReal (AQ := AQ) (Quotient.mk _ x) * toCReal (AQ := AQ) (Quotient.mk _ y)
  simp [CRealAQ.toCReal, CRealRep.denote_mulC (AQ := AQ)]

/-!
### Algebraic structure

We equip `CRealAQ AQ` with the same algebraic structure as `CReal`, by proving the
axioms via `toCReal` and injectivity.

This keeps proofs short and ensures the quotient operations are *definitionally*
implemented using the rounded/compressed representative operations.
-/

instance : CommRing (CRealAQ AQ) where
  add := (· + ·)
  add_assoc a b c := by
    apply toCReal_injective (AQ := AQ)
    simp [add_assoc]
  zero := (0 : CRealAQ AQ)
  zero_add a := by
    apply toCReal_injective (AQ := AQ)
    simp
  add_zero a := by
    apply toCReal_injective (AQ := AQ)
    simp
  nsmul := nsmulRec
  nsmul_zero := by intro; rfl
  nsmul_succ := by intro _ _; rfl
  neg := Neg.neg
  sub := fun a b => a + (-b)
  sub_eq_add_neg := by intro _ _; rfl
  zsmul := zsmulRec
  zsmul_zero' := by intro; rfl
  zsmul_succ' := by intro _ _; rfl
  zsmul_neg' := by intro _ _; rfl
  add_comm a b := by
    apply toCReal_injective (AQ := AQ)
    simp [add_comm]
  neg_add_cancel a := by
    apply toCReal_injective (AQ := AQ)
    simp
  mul := (· * ·)
  one := (1 : CRealAQ AQ)
  mul_assoc a b c := by
    apply toCReal_injective (AQ := AQ)
    simp [mul_assoc]
  one_mul a := by
    apply toCReal_injective (AQ := AQ)
    simp
  mul_one a := by
    apply toCReal_injective (AQ := AQ)
    simp
  left_distrib a b c := by
    apply toCReal_injective (AQ := AQ)
    simp [left_distrib]
  right_distrib a b c := by
    apply toCReal_injective (AQ := AQ)
    simp [right_distrib]
  mul_comm a b := by
    apply toCReal_injective (AQ := AQ)
    simp [mul_comm]
  zero_mul a := by
    apply toCReal_injective (AQ := AQ)
    simp
  mul_zero a := by
    apply toCReal_injective (AQ := AQ)
    simp

/-!
### Order transport (optional)

We intentionally do **not** declare a global `LE` instance here, because the upstream
`CRealPre` order is relatively heavy and many computational developments prefer to keep
order/classical structure in a separate file.

A follow-up PR can add an `instLE` and `Preorder`/`LinOrderedRing` by pulling back the
order along `toCReal`.
-/

end CRealAQ

/-- The fast extensional computable reals backed by dyadics. -/
abbrev CRealDyadic : Type := CRealAQ Dyadic

end Computable
