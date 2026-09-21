/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.SpecialVectors
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.WeakNormsMaximizer

/-! # Weak Norm Input -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundCoarseFluctuations

open MeasureTheory

noncomputable section

/-!
# Weak-norm inputs for the coarse-fluctuation lemma

This file instantiates the deterministic weak-norm maximizer theorem at the
special vectors and beta-shifted Section 5.3 exponents.
-/

/-- Almost-sure beta-shifted weak-norm bounds for the special-vector scalar
maximizer.  This is the direct bridge from the second Section 5.3 lemma into
the third one. -/
theorem ae_specialWeakNormsMaximizer_homogenizationScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {k m : ℕ} (hkm : k < m) (e : Vec d) :
    ∀ᵐ a ∂P,
      let β := section53CoarseFluctuationBeta hP4
      let s := hP4.sLower + 2 * β
      let s' := hP4.sLower + β
      let t := hP4.sUpper + 2 * β
      let t' := hP4.sUpper + β
      let p_e := specialPAtScale hP hStruct (m : ℤ) e
      let q_e := specialQAtScale hP hStruct (m : ℤ) e
      let p0_e := (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ • q_e - p_e
      let q0_e := q_e - hP.barSigmaAtScale hStruct (m : ℤ) • p_e
      Ch04.canonicalScalarResponseGradientWeakNormCubeSet
          (originCube d (m : ℤ)) s p_e q_e p0_e a.toFun ≤
        2 *
          WeakNormsMaximizer.gradientRHSAtScale
            (WeakNormsMaximizer.section53WeakNormMaximizerConst d)
            (m : ℤ) (k : ℤ) s s' p_e q_e p0_e a ∧
      Ch04.canonicalScalarResponseFluxWeakNormCubeSet
          (originCube d (m : ℤ)) t p_e q_e q0_e a.toFun ≤
        2 *
          WeakNormsMaximizer.fluxRHSAtScale
            (WeakNormsMaximizer.section53WeakNormMaximizerConst d)
            (m : ℤ) (k : ℤ) t t' p_e q_e q0_e a := by
  have hkm_int : (k : ℤ) < (m : ℤ) := by exact_mod_cast hkm
  let β := section53CoarseFluctuationBeta hP4
  have hβ_pos : 0 < β := by
    simpa [β] using section53CoarseFluctuationBeta_pos hP4
  have hs : 0 < hP4.sLower + 2 * β := by
    linarith [hP4.sLower_pos, hβ_pos]
  have hs_le : hP4.sLower + 2 * β ≤ 1 := by
    simpa [β] using sLower_add_two_beta_le_one hP4
  have hs'_low : (hP4.sLower + 2 * β) / 2 ≤ hP4.sLower + β := by
    simpa [β] using half_sLower_add_two_beta_le_sLower_add_beta hP4
  have hs'_high : hP4.sLower + β < hP4.sLower + 2 * β := by
    simpa [β] using sLower_add_beta_lt_sLower_add_two_beta hP4
  have ht : 0 < hP4.sUpper + 2 * β := by
    linarith [hP4.sUpper_pos, hβ_pos]
  have ht_le : hP4.sUpper + 2 * β ≤ 1 := by
    simpa [β] using sUpper_add_two_beta_le_one hP4
  have ht'_low : (hP4.sUpper + 2 * β) / 2 ≤ hP4.sUpper + β := by
    simpa [β] using half_sUpper_add_two_beta_le_sUpper_add_beta hP4
  have ht'_high : hP4.sUpper + β < hP4.sUpper + 2 * β := by
    simpa [β] using sUpper_add_beta_lt_sUpper_add_two_beta hP4
  filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
  dsimp only
  exact
    WeakNormsMaximizer.weakNormsMaximizer_homogenizationScale
      a ha hkm_int hs hs_le hs'_low hs'_high ht ht_le ht'_low ht'_high
      (specialPAtScale hP hStruct (m : ℤ) e)
      (specialQAtScale hP hStruct (m : ℤ) e)
      ((hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹ •
        specialQAtScale hP hStruct (m : ℤ) e -
          specialPAtScale hP hStruct (m : ℤ) e)
      (specialQAtScale hP hStruct (m : ℤ) e -
        hP.barSigmaAtScale hStruct (m : ℤ) •
          specialPAtScale hP hStruct (m : ℤ) e)

end

end JUpperBoundCoarseFluctuations
end Section53
end Ch05
end Book
end Homogenization
