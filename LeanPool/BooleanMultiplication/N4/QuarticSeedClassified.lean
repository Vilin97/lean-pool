/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.CubicTarget

/-!
# Classified quartic seed-using normal form

This is the circuit-level endpoint of the quartic and sextic identities.  It
adds the two independent seed coefficients, places the feedback coefficient
in their plane, excludes the zero feedback, and applies the rational
annihilator classification.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- A seed-using target witness with its factor in the classified quartic normal form. -/
@[expose]
def SeedUsingQuarticClassifiedForm (g : ANF 8) : Prop :=
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
    target * factor = target ∧
    ∃ (seedLeftConst seedRightConst : F₂)
      (seedLeftLinear seedRightLinear : LinearForm)
      (alpha beta : Fin 3 → F₂) (p q : F₂)
      (theta : Fin 3) (eps : F₂),
      g =
        (affineANF seedLeftConst seedLeftLinear + rationalANF alpha) *
          (affineANF seedRightConst seedRightLinear + rationalANF beta) ∧
      alpha ≠ 0 ∧ beta ≠ 0 ∧ alpha ≠ beta ∧
      factorCoeff = p • alpha + q • beta ∧
      factorCoeff = rationalSingleton theta ∧
      targetCoeff = rationalTangentAt theta eps

/-- A normalized eight-gate circuit with nonzero seed quartic reaches the
fully classified seed-using form. -/
theorem NormalizedEight.seedUsingQuarticClassifiedForm
    {C : Circuit 8 8} (h : NormalizedEight C)
    (hquartic : quarticProbeANF (C.gate 3) ≠ 0) :
    SeedUsingQuarticClassifiedForm (C.gate 3) := by
  rcases h.seedUsingQuarticNormalForm hquartic with
    ⟨correction, factor, target, targetConst, factorConst,
      targetLinear, factorLinear, targetCoeff, factorCoeff,
      hcorrection, hfactorLow, htargetEq, htargetMem, htargetNotLow,
      htargetRep, hfactorRep, htargetNonrational, hann, hleft, hright⟩
  rcases h.seedFactorData with
    ⟨leftAffine, rightAffine, alpha, beta,
      hleftAffine, hrightAffine, _hleftRep, _hrightRep, hseed⟩
  rcases exists_affineANF_of_mem hleftAffine with
    ⟨seedLeftConst, seedLeftLinear, hleftAffineRep⟩
  rcases exists_affineANF_of_mem hrightAffine with
    ⟨seedRightConst, seedRightLinear, hrightAffineRep⟩
  have hseedRep : C.gate 3 =
      (affineANF seedLeftConst seedLeftLinear + rationalANF alpha) *
        (affineANF seedRightConst seedRightLinear + rationalANF beta) := by
    simpa [rationalANF, hleftAffineRep, hrightAffineRep] using hseed
  have hseedProbe :
      quarticWedgeProbe (rationalTwo alpha) (rationalTwo beta) ≠ 0 := by
    intro hzero
    apply hquartic
    rw [hseedRep, lowProduct_quarticProjection, hzero]
  have hwedge : wedgeTwo (rationalTwo alpha) (rationalTwo beta) ≠ 0 :=
    wedge_ne_zero_of_quarticProbe_ne_zero _ _ hseedProbe
  have hind := rational_coeff_independent_of_wedge_ne_zero alpha beta hwedge
  have hfactorCoeffNonzero : factorCoeff ≠ 0 :=
    seedUsing_factorCoeff_ne_zero hquartic hcorrection htargetEq
      htargetMem htargetNotLow htargetRep hfactorRep
      htargetNonrational hright
  have hdet : rationalTripleDet alpha beta factorCoeff = 0 :=
    rationalTripleDet_eq_zero_of_seedUsing_target
      hseedRep hcorrection hfactorRep htargetEq htargetMem
  rcases rationalTripleDet_zero_mem_plane alpha beta factorCoeff
      hind.1 hind.2.1 hind.2.2 hdet with ⟨p, q, hplane⟩
  rcases rational_target_annihilator_classification
      factorCoeff targetCoeff hfactorCoeffNonzero htargetNonrational hann with
    ⟨theta, eps, hsingleton, htangent⟩
  exact
    ⟨correction, factor, target, targetConst, factorConst,
      targetLinear, factorLinear, targetCoeff, factorCoeff,
      hcorrection, hfactorLow, htargetEq, htargetMem, htargetNotLow,
      htargetRep, hfactorRep, htargetNonrational, hann, hleft, hright,
      seedLeftConst, seedRightConst, seedLeftLinear, seedRightLinear,
      alpha, beta, p, q, theta, eps, hseedRep,
      hind.1, hind.2.1, hind.2.2, hplane, hsingleton, htangent⟩

end

end N4
end UnrestrictedBooleanMul
