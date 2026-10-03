/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.SpatialCommutator

/-! Finite coordinate estimates for the physical tensor L2 norm. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- Coordinate L2 bounds control the actual finite Pi norm. This is the
finite-dimensional bridge needed after the scalar contraction induction. -/
theorem amnr_pi_L2_le_sum {ι : Type*} [Fintype ι] {F : Type*} [NormedAddCommGroup F]
    {μ : Measure AmnrSpace} {f : AmnrSpace → ι → F}
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ ≤ ∑ i : ι, eLpNorm (fun z => f z i) 2 μ := by
  have hnorm (z : AmnrSpace) : ‖f z‖ ≤ ‖∑ i : ι, ‖f z i‖‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
    apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).mpr
    intro i
    exact Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  have hh := eLpNorm_mono_ae hf (Filter.Eventually.of_forall hnorm) (p := 2)
  have heq : (fun z => ∑ i : ι, ‖f z i‖) = ∑ i : ι, (fun z => ‖f z i‖) := by
    funext z
    simp only [Finset.sum_apply]
  rw [heq] at hh
  refine hh.trans ((eLpNorm_sum_le (μ := μ) (p := 2) (s := Finset.univ)
    (f := fun i z => ‖f z i‖) (by norm_num)).trans_eq ?_)
  apply Finset.sum_congr rfl
  intro i _
  exact eLpNorm_norm (fun z => f z i) ((continuous_apply i).comp_aestronglyMeasurable hf)

/-- A uniform coordinate estimate controls the finite Pi norm with only the
number of coordinates. -/
theorem amnr_pi_L2_le_card {ι : Type*} [Fintype ι]
    {F : Type*} [NormedAddCommGroup F] {μ : Measure AmnrSpace}
    {f : AmnrSpace → ι → F} (hf : AEStronglyMeasurable f μ) {B : ℝ}
    (hb : ∀ i, eLpNorm (fun z => f z i) 2 μ ≤ ENNReal.ofReal B) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * B) := by
  refine (amnr_pi_L2_le_sum hf).trans ?_
  calc
    ∑ i : ι, eLpNorm (fun z => f z i) 2 μ ≤ ∑ _i : ι, ENNReal.ofReal B :=
      Finset.sum_le_sum (fun i _ => hb i)
    _ = ENNReal.ofReal ((Fintype.card ι : ℝ) * B) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- The physical three-index tensor norm follows from its eight scalar
coordinate estimates. This factor is uniform in every derivative index. -/
theorem amnr_tensor_L2_le_eight {μ : Measure AmnrSpace}
    {A : AmnrSpace → Fin 2 → Fin 2 → Fin 2 → ℝ}
    (hA : AEStronglyMeasurable A μ) {B : ℝ}
    (hb : ∀ i j k, eLpNorm (fun z => A z i j k) 2 μ ≤ ENNReal.ofReal B) :
    eLpNorm A 2 μ ≤ ENNReal.ofReal (8 * B) := by
  have hi (i : Fin 2) : AEStronglyMeasurable (fun z => A z i) μ :=
    (continuous_apply i).comp_aestronglyMeasurable hA
  have hij (i j : Fin 2) : AEStronglyMeasurable (fun z => A z i j) μ :=
    (continuous_apply j).comp_aestronglyMeasurable (hi i)
  have hjb (i j : Fin 2) : eLpNorm (fun z => A z i j) 2 μ ≤ ENNReal.ofReal (2 * B) := by
    simpa only [Fintype.card_fin, Nat.cast_ofNat] using amnr_pi_L2_le_card (hij i j) (hb i j)
  have hib (i : Fin 2) : eLpNorm (fun z => A z i) 2 μ ≤ ENNReal.ofReal (4 * B) := by
    have hh := amnr_pi_L2_le_card (hi i) (hjb i)
    convert hh using 1
    simp only [Fintype.card_fin, Nat.cast_ofNat]
    congr 1
    ring
  have hh := amnr_pi_L2_le_card hA hib
  convert hh using 1
  simp only [Fintype.card_fin, Nat.cast_ofNat]
  congr 1
  ring

end AVenhance.Infra.Section4
