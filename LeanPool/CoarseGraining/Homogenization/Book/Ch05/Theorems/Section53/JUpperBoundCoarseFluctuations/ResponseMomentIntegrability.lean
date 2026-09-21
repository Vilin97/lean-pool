/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations.FluctuationIntegrability

/-! # Response Moment Integrability -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundCoarseFluctuations

open MeasureTheory

/-!
# Response moment integrability

This proof-internal file exposes the origin-cube `ζ`-moment integrability of
the response observable from the `L^2` response surface and `(P4)`.
-/

noncomputable section

theorem integrable_rpow_restrictionResponseJObservableCubeSet_originCube_from_P4
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    (k : ℕ) (p q : Vec d) :
    Integrable
      (fun a : RegCoeffField d =>
        Real.rpow
          (Ch04.restrictionResponseJObservableCubeSet (originCube d (k : ℤ)) p q a)
          (section53CoarseFluctuationZeta hP4)) P := by
  let : IsProbabilityMeasure P := hP.isProbability
  let ζ := section53CoarseFluctuationZeta hP4
  let J : RegCoeffField d → ℝ :=
    Ch04.restrictionResponseJObservableCubeSet (originCube d (k : ℤ)) p q
  have hζ_pos : 0 < ζ := by
    simpa [ζ] using section53CoarseFluctuationZeta_pos hP4
  have hζ_le_two : ENNReal.ofReal ζ ≤ (2 : ENNReal) := by
    rw [← ENNReal.ofReal_ofNat]
    exact ENNReal.ofReal_le_ofReal (by
      simpa [ζ] using section53CoarseFluctuationZeta_le_two hP4)
  have hJ_mem2 : MemLp J (2 : ENNReal) P := by
    simpa [J] using
      memLp_two_restrictionResponseJObservableCubeSet_originCube_from_P4
        hP hStruct hP4 k p q
  have hJ_memζ : MemLp J (ENNReal.ofReal ζ) P :=
    hJ_mem2.mono_exponent hζ_le_two
  have hζ_ne_zero : ENNReal.ofReal ζ ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le.mpr hζ_pos]
  have hζ_ne_top : ENNReal.ofReal ζ ≠ ⊤ := by
    simp
  have hint :
      Integrable (fun a : RegCoeffField d => ‖J a‖ ^ (ENNReal.ofReal ζ).toReal) P :=
    hJ_memζ.integrable_norm_rpow hζ_ne_zero hζ_ne_top
  refine hint.congr ?_
  filter_upwards with a
  have hJ_nonneg : 0 ≤ J a := by
    simpa [J] using
      Ch04.restrictionResponseJObservableCubeSet_nonneg (originCube d (k : ℤ)) p q a
  rw [ENNReal.toReal_ofReal hζ_pos.le, Real.norm_of_nonneg hJ_nonneg,
    Real.rpow_eq_pow]
end

end JUpperBoundCoarseFluctuations
end Section53
end Ch05
end Book
end Homogenization
