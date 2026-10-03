/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.PlaceSymmetry

/-!
# Complete quartic exclusion

The classified feedback place is transported algebraically to the zero
place.  The complete zero-place slice theorem then excludes every possible
second direction in the normalized seed plane.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

theorem seedUsingQuarticClassifiedForm_impossible
    {g : ANF 8} (h : SeedUsingQuarticClassifiedForm g) : False := by
  rcases h with
    ⟨correction, factor, target, targetConst, factorConst,
      targetLinear, factorLinear, targetCoeff, factorCoeff,
      hcorrection, _hfactorLow, htargetEq, _htargetMem,
      _htargetNotLow, htargetRep, hfactorRep, _htargetNonrational,
      _hann, _hleft, hright,
      seedLeftConst, seedRightConst, seedLeftLinear, seedRightLinear,
      alpha, beta, p, q, theta, eps, hseedRep,
      halpha, hbeta, hab, hfactorPlane, hfactorSingleton,
      htargetTangent⟩
  rcases exists_representedLowFactor_of_mem hcorrection with
    ⟨correctionConst, correctionLinear, correctionCoeff, hcorrectionRep⟩
  let Phi := anfPlaceNormalize theta
  let alpha' := normalizeRationalCoeff theta alpha
  let beta' := normalizeRationalCoeff theta beta
  have hseedRep' : Phi g =
      representedLowFactor seedLeftConst
          (normalizePlaceLinear theta seedLeftLinear) alpha' *
        representedLowFactor seedRightConst
          (normalizePlaceLinear theta seedRightLinear) beta' := by
    have hleftMap := anfPlaceNormalize_representedLowFactor theta
      seedLeftConst seedLeftLinear alpha
    have hrightMap := anfPlaceNormalize_representedLowFactor theta
      seedRightConst seedRightLinear beta
    calc
      Phi g = Phi
          (representedLowFactor seedLeftConst seedLeftLinear alpha *
            representedLowFactor seedRightConst seedRightLinear beta) :=
        congrArg Phi hseedRep
      _ = Phi (representedLowFactor seedLeftConst seedLeftLinear alpha) *
          Phi (representedLowFactor seedRightConst seedRightLinear beta) :=
        map_mul Phi _ _
      _ = representedLowFactor seedLeftConst
            (normalizePlaceLinear theta seedLeftLinear) alpha' *
          representedLowFactor seedRightConst
            (normalizePlaceLinear theta seedRightLinear) beta' := by
        rw [hleftMap, hrightMap]
  have hcorrectionRep' : Phi correction =
      representedLowFactor correctionConst
        (normalizePlaceLinear theta correctionLinear)
        (normalizeRationalCoeff theta correctionCoeff) := by
    rw [hcorrectionRep]
    exact anfPlaceNormalize_representedLowFactor theta correctionConst
      correctionLinear correctionCoeff
  have hcorrectionLow' : Phi correction ∈ rationalLowSpace := by
    rw [hcorrectionRep']
    exact representedLowFactor_mem _ _ _
  have halpha' : alpha' ≠ 0 :=
    normalizeRationalCoeff_ne_zero theta halpha
  have hbeta' : beta' ≠ 0 :=
    normalizeRationalCoeff_ne_zero theta hbeta
  have hab' : alpha' ≠ beta' :=
    normalizeRationalCoeff_ne theta hab
  have hplane' :
      InRationalCoeffPlane alpha' beta' (rationalSingleton 0) := by
    refine ⟨p, q, ?_⟩
    calc
      rationalSingleton 0 =
          normalizeRationalCoeff theta (rationalSingleton theta) :=
        (normalizeRationalCoeff_singleton_self theta).symm
      _ = normalizeRationalCoeff theta factorCoeff := by
        rw [hfactorSingleton]
      _ = normalizeRationalCoeff theta (p • alpha + q • beta) := by
        rw [hfactorPlane]
      _ = p • alpha' + q • beta' := by
        rw [normalizeRationalCoeff_add,
          normalizeRationalCoeff_smul, normalizeRationalCoeff_smul]
  have hzeroSeed :
      ZeroAnchoredQuarticSeedForm (Phi g) (Phi correction) :=
    zeroAnchoredQuarticSeedForm_of_plane hseedRep' hcorrectionLow'
      halpha' hbeta' hab' hplane'
  have htargetRep' : Phi target =
      affineANF targetConst (normalizePlaceLinear theta targetLinear) +
        targetANF (rationalTangentAt 0 eps) := by
    rw [htargetRep, map_add, anfPlaceNormalize_affineANF,
      htargetTangent, anfPlaceNormalize_tangent_self]
  have hfactorRep' : Phi factor =
      affineANF factorConst (normalizePlaceLinear theta factorLinear) +
        rationalANF (rationalSingleton 0) := by
    rw [hfactorRep, map_add, anfPlaceNormalize_affineANF,
      anfPlaceNormalize_rationalANF, hfactorSingleton,
      normalizeRationalCoeff_singleton_self]
  have htargetEq' :
      Phi target = (Phi g + Phi correction) * Phi factor := by
    calc
      Phi target = Phi ((g + correction) * factor) :=
        congrArg Phi htargetEq
      _ = Phi (g + correction) * Phi factor := map_mul Phi _ _
      _ = (Phi g + Phi correction) * Phi factor := by rw [map_add]
  have hright' : Phi target * Phi factor = Phi target := by
    calc
      Phi target * Phi factor = Phi (target * factor) :=
        (map_mul Phi _ _).symm
      _ = Phi target := congrArg Phi hright
  rcases zeroPlaceFeedbackForm_of_right_idempotence
      htargetRep' hfactorRep' hright' with
    ⟨delta, rho, sigma, hfeedback⟩
  exact no_zeroAnchored_quartic_feedback_target hzeroSeed htargetEq'
    htargetRep' hfeedback hright'

/-- The normalized seed gate has zero quartic high part. -/
theorem NormalizedEight.seed_quarticProbe_eq_zero
    {C : Circuit 8 8} (h : NormalizedEight C) :
    quarticProbeANF (C.gate 3) = 0 := by
  by_contra hnonzero
  exact seedUsingQuarticClassifiedForm_impossible
    (h.seedUsingQuarticClassifiedForm hnonzero)

end

end N4
end UnrestrictedBooleanMul
