/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.CReals.CRealAQ

namespace Computable

namespace CRealAQ

variable {AQ : Type} [ApproxRationals AQ]

/--
`ofCReal : CReal → CRealAQ AQ` defined by lifting `CRealRep.ofPre`
through the `CReal` quotient.
-/
def ofCReal : CReal → CRealAQ AQ :=
  Quotient.lift
    (fun x : CReal.Pre => (Quotient.mk _ (CRealRep.ofPre (AQ := AQ) x)))
    (by
      intro a b hab
      apply Quotient.sound
      exact CRealRep.ofPre_respects_equiv (AQ := AQ) hab)

/-- `toCReal (ofCReal r) = r`. -/
theorem toCReal_ofCReal (r : CReal) : toCReal (AQ := AQ) (ofCReal (AQ := AQ) r) = r := by
  refine Quotient.inductionOn r (fun x => ?_)
  -- `toCReal (mk (ofPre x)) = mk (toPre (ofPre x))`, and that is equivalent to `mk x`
  apply Quotient.sound
  exact CRealRep.toPre_ofPre_equiv (AQ := AQ) x

/-- Surjectivity of `toCReal`. -/
theorem toCReal_surjective : Function.Surjective (toCReal (AQ := AQ)) := by
  intro r
  refine ⟨ofCReal (AQ := AQ) r, toCReal_ofCReal (AQ := AQ) r⟩

/--
Equivalence between `CRealAQ AQ` and `CReal`, with inverse `ofCReal`.
-/
def equivCReal : CRealAQ AQ ≃ CReal where
  toFun := toCReal (AQ := AQ)
  invFun := ofCReal (AQ := AQ)
  left_inv := by
    intro x
    apply toCReal_injective (AQ := AQ)
    simpa using toCReal_ofCReal (AQ := AQ) (toCReal (AQ := AQ) x)
  right_inv := toCReal_ofCReal (AQ := AQ)

/-- Ring equivalence induced by `toCReal`. -/
def ringEquivCReal : CRealAQ AQ ≃+* CReal where
  toEquiv := equivCReal (AQ := AQ)
  map_add' := by
    intro a b
    simp [equivCReal, CRealAQ.toCReal_add]
  map_mul' := by
    intro a b
    simp [equivCReal, CRealAQ.toCReal_mul]

end CRealAQ

end Computable
