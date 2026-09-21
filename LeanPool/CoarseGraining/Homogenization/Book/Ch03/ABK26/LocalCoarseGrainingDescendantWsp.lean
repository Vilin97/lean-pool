/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch03.ABK26.LocalCoarseGrainingPDE
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.EuclideanWspLocalization
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.EuclideanWspLpMembership

/-!
# Descendant localization of the source fractional-Sobolev carrier

The source finite-`p` datum is available on the parent cube.  This file
provides its literal restriction to every triadic descendant, so one-cube
estimates can construct their regularity witnesses locally without adding a
new hypothesis to the local coarse-graining theorem.
-/

namespace Homogenization
namespace Book
namespace Ch03
namespace ABK26

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

private theorem cubeEuclideanWspESeminorm_lt_top_on_descendant
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ}
    {s : FractionalOrder} {p : FiniteLpExponent} {g : Vec d → Vec d}
    (hR : R ∈ descendantsAtDepth Q j)
    (hg : MemCubeEuclideanWsp Q s p g) :
    cubeEuclideanWspESeminorm R s p g < ∞ := by
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  let E : TriadicCube d → ℝ≥0∞ := fun S =>
    (cubeEuclideanWspESeminorm S s p g) ^ p.exponent.toReal
  have hparent : (cubeEuclideanWspESeminorm Q s p g) ^ p.exponent.toReal < ∞ :=
    ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg hg.eSeminorm_lt_top.ne
  have havg : descendantsENNAverage Q j E < ∞ := by
    apply lt_of_le_of_lt
      (descendantsENNAverage_cubeEuclideanWspESeminorm_rpow_le Q j s p g)
    exact hparent
  have hD_nonempty : D.Nonempty := by
    simpa [D] using descendantsAtDepth_nonempty Q j
  have hcard_ne_zero : (D.card : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hD_nonempty
  have hcard_ne_top : (D.card : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  have hsum : ∑ S ∈ D, E S < ∞ := by
    have heq : ∑ S ∈ D, E S = (D.card : ℝ≥0∞) * descendantsENNAverage Q j E := by
      unfold descendantsENNAverage
      change ∑ S ∈ D, E S =
        (D.card : ℝ≥0∞) * ((D.card : ℝ≥0∞)⁻¹ * ∑ S ∈ D, E S)
      rw [← mul_assoc, ENNReal.mul_inv_cancel hcard_ne_zero hcard_ne_top, one_mul]
    rw [heq]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr ENNReal.coe_ne_top) havg
  have hterm : E R < ∞ := by
    apply lt_of_le_of_lt (Finset.single_le_sum (fun S _ => bot_le) (by simpa [D] using hR))
    exact hsum
  exact (ENNReal.rpow_lt_top_iff_of_pos
    (ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne)).mp hterm

/-- A parent full Euclidean `W^{s,p}` source witness restricts canonically to
every triadic descendant. -/
theorem MemCubeEuclideanFullWsp.onDescendant
    {d : ℕ} {Q R : TriadicCube d} {n : ℤ}
    {s : FractionalOrder} {p : FiniteLpExponent} {g : Vec d → Vec d}
    (hn : n ≤ Q.scale) (hR : R ∈ descendantsAtScale Q n)
    (hg : MemCubeEuclideanFullWsp Q s p g) :
    MemCubeEuclideanFullWsp R s p g := by
  have hRdepth : R ∈ descendantsAtDepth Q (Int.toNat (Q.scale - n)) := by
    rw [← descendantsAtScale_eq_descendantsAtDepth Q hn]
    exact hR
  refine ⟨memLp_on_descendant_of_memLp_generic hRdepth hg.1, ?_⟩
  exact memCubeEuclideanWsp_of_memLp_of_eSeminorm_lt_top
    (memLp_on_descendant_of_memLp_generic hRdepth hg.1)
    (cubeEuclideanWspESeminorm_lt_top_on_descendant hRdepth hg.2)

end
end ABK26
end Ch03
end Book
end Homogenization
