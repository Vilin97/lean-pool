/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ContinuousInterpolation.MeasurableRepresentative

/-!
# Measurability closure for the exact Euclidean fractional energy
-/

namespace Homogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

private theorem measurable_euclideanDist_pair (d : ℕ) :
    Measurable (fun z : Vec d × Vec d => euclideanDist z.1 z.2) := by
  have hsub : Measurable (fun z : Vec d × Vec d => z.1 - z.2) :=
    measurable_fst.sub measurable_snd
  have hh : Measurable (fun z : Vec d × Vec d => HilbertVec.ofVec (z.1 - z.2)) :=
    (HilbertVec.ofVecL d).continuous.measurable.comp hsub
  simpa only [euclideanDist, euclideanNorm_eq_norm_ofVec] using hh.norm

/-- A globally measurable representative has a measurable totalized exact
Euclidean fractional-energy integrand. -/
theorem measurable_euclideanHsIntegrand_of_measurable {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) (hF : Measurable F) :
    Measurable (euclideanHsIntegrand s F) := by
  unfold euclideanHsIntegrand
  apply Measurable.ennreal_ofReal
  apply Measurable.div
  · exact ((HilbertVec.ofVecL d).continuous.measurable.comp
      ((hF.comp measurable_fst).sub (hF.comp measurable_snd))).norm.pow measurable_const
  · change Measurable (fun z : Vec d × Vec d =>
      euclideanDist z.1 z.2 ^ ((d : ℝ) + 2 * s.1))
    exact (measurable_euclideanDist_pair d).pow measurable_const

/-- The exact Euclidean integrand is a.e.-measurable for every stored `L²`
field, by transport from its canonical measurable representative. -/
theorem aemeasurable_euclideanHsIntegrand {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    AEMeasurable (euclideanHsIntegrand s F) (euclideanHsProductMeasure d) := by
  exact (measurable_euclideanHsIntegrand_of_measurable s F.measurableRepresentative
    F.measurable_measurableRepresentative).aemeasurable.congr
      (euclideanHsIntegrand_congr_ae F.ae_eq_measurableRepresentative).symm

/-- With integrand measurability now automatic, exact fractional membership
is precisely finiteness of the extended Euclidean energy. -/
theorem memEuclideanHs_iff_energy_lt_top {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    MemEuclideanHs s F ↔ euclideanHsEnergy s F < ∞ := by
  constructor
  · exact fun h => h.energy_lt_top
  · exact fun h => ⟨aemeasurable_euclideanHsIntegrand s F, h⟩

/-- Taking the positive half-power preserves finiteness of the exact
Euclidean fractional energy. -/
theorem euclideanHsESeminorm_lt_top_iff_energy_lt_top {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    euclideanHsESeminorm s F < ∞ ↔ euclideanHsEnergy s F < ∞ := by
  unfold euclideanHsESeminorm
  exact ENNReal.rpow_lt_top_iff_of_pos (by norm_num)

/-- Exact fractional membership is equivalently finiteness of the extended
Euclidean fractional seminorm. -/
theorem memEuclideanHs_iff_euclideanHsESeminorm_lt_top {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    MemEuclideanHs s F ↔ euclideanHsESeminorm s F < ∞ := by
  rw [memEuclideanHs_iff_energy_lt_top, euclideanHsESeminorm_lt_top_iff_energy_lt_top]

end

end Homogenization
