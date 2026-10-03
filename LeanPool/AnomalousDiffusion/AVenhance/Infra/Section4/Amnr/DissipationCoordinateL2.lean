/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FiniteSpatialWordBridge

/-! Scalar coordinate L2 jets extracted from actual vector dissipation. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

theorem amnr_coordinate_sq_le_vecNormSq (v : Vec 2) (q : Fin 2) :
    v q ^ 2 ≤ vecNormSq v := by
  simpa only [vecNormSq, vecDot, pow_two] using
    (Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => mul_self_nonneg (v i))
      (Finset.mem_univ q))

/-- Each scalar gradient coordinate is paid for by the actual full vector
quadratic dissipation, on the same measure. -/
theorem amnr_coordinate_eLpNorm_two_le_of_dissipation {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {g : α → Vec 2} (q : Fin 2)
    (hg : AEStronglyMeasurable (fun z => g z q) μ)
    (hint : Integrable (fun z => vecNormSq (g z)) μ)
    {G : ℝ} (hG : 0 ≤ G) (hbound : (∫ z, vecNormSq (g z) ∂μ) ≤ G ^ 2) :
    eLpNorm (fun z => g z q) 2 μ ≤ ENNReal.ofReal G := by
  have hs : Integrable (fun z => (g z q) ^ 2) μ := hint.mono' (hg.pow 2) (by
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact amnr_coordinate_sq_le_vecNormSq (g z) q)
  apply amnr_scalar_eLpNorm_two_le_of_square hg hs hG
  exact (integral_mono hs hint (fun z => amnr_coordinate_sq_le_vecNormSq (g z) q)).trans hbound

end AVenhance.Infra.Section4
