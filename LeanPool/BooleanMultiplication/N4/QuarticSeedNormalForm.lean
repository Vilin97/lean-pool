/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.QuarticIdempotenceConsequences

/-!
# Circuit-level quartic seed-using normal form

The first useful suffix gate is first reduced to the two algebraic child
types.  Under a nonzero seed quartic, the low--low type is impossible.  The
remaining seed-using type is recorded together with its two Boolean
idempotence equations and the rational-annihilator certificate.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- The complete seed-using normal form, kept in `Prop` so that it can be
obtained from the existential useful-child certificate without choosing
data computationally. -/
@[expose]
def SeedUsingQuarticNormalForm (g : ANF 8) : Prop :=
  ∃ (correction factor target : ANF 8)
    (targetConst factorConst : F₂)
    (targetLinear factorLinear : LinearForm)
    (targetCoeff : TargetCoeff) (factorCoeff : Fin 3 → F₂),
    correction ∈ rationalLowSpace ∧
    factor ∈ rationalLowSpace ∧
    target = (g + correction) * factor ∧
    target ∈ targetAmbient 8 (mulTarget 4) ∧
    target ∉ rationalLowSpace ∧
    target = affineANF targetConst targetLinear + targetANF targetCoeff ∧
    factor = affineANF factorConst factorLinear + rationalANF factorCoeff ∧
    ¬ IsRationalCoeff targetCoeff ∧
    VanishesOnQuarticAnnihilatorProbe targetCoeff factorCoeff ∧
    (g + correction) * target = target ∧
    target * factor = target

/-- Under a nonzero seed quartic, the first useful child has the complete
seed-using algebraic normal form needed by the rest of the quartic
exclusion. -/
theorem NormalizedEight.seedUsingQuarticNormalForm
    {C : Circuit 8 8} (h : NormalizedEight C)
    (hquartic : quarticProbeANF (C.gate 3) ≠ 0) :
    SeedUsingQuarticNormalForm (C.gate 3) := by
  rcases h.usefulSeedChildData with
    ⟨target, representative, shift, htarget, htargetOld,
      _htargetNew, hshift, htargetEq, hshape⟩
  have hnotLowLow : ¬ IsLowLowProduct representative :=
    h.usefulSeedChild_not_lowLow hquartic htarget htargetOld hshift htargetEq
  have hseedUsing : IsSeedUsingProduct (C.gate 3) representative := by
    rcases hshape with hlow | hseed
    · exact (hnotLowLow hlow).elim
    · exact hseed
  rcases h.seedUsingTargetWitness htarget htargetOld hshift htargetEq
      hseedUsing with
    ⟨a, c, F, ha, hc, hF, hFAmbient, hFNotLow⟩
  rcases seedUsing_idempotence hF with ⟨hleft, hright⟩
  rcases quartic_data_of_right_idempotence
      hFAmbient hFNotLow hc hright with
    ⟨A, B, ell, m, T, delta, hFRep, hcRep, hTNotRat, hann⟩
  exact
    ⟨a, c, F, A, B, ell, m, T, delta,
      ha, hc, hF, hFAmbient, hFNotLow, hFRep, hcRep,
      hTNotRat, hann, hleft, hright⟩

end

end N4
end UnrestrictedBooleanMul
