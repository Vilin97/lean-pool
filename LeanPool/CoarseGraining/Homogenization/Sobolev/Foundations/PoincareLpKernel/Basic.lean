/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Geometry.ConvexDomain
import LeanPool.CoarseGraining.Homogenization.Geometry.Translation
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareSegment
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Basic -/

namespace Homogenization

open MeasureTheory Metric
open scoped ENNReal NNReal Pointwise

/-!
# Riesz-kernel tools for convex-domain Poincare — basic estimates

This file defines the Riesz kernel `(x, y) ↦ ‖x - y‖^(1 - d)` and establishes
its basic positivity, symmetry, and ball-localised `L¹` bounds. The bounded-
domain `L¹` size is controlled by the radius of `IsBoundedDomain`.
-/

/-- The order-`1` Riesz kernel in dimension `d`. -/
noncomputable def rieszKernel {d : ℕ} (x y : Vec d) : ℝ :=
  ‖x - y‖ ^ (1 - (d : ℝ))

theorem rieszKernel_nonneg {d : ℕ} (x y : Vec d) :
    0 ≤ rieszKernel x y := by
  unfold rieszKernel
  exact Real.rpow_nonneg (norm_nonneg _) _

theorem rieszKernel_symm {d : ℕ} (x y : Vec d) :
    rieszKernel x y = rieszKernel y x := by
  simp [rieszKernel, norm_sub_rev]

section NeZero

variable {d : ℕ} [NeZero d]

/-- Cache `Nontrivial (Vec d)` once per section so tactic-level typeclass
searches don't rediscover the NeZero → Nonempty → Nontrivial chain. -/
private instance instNontrivialVecNeZero : Nontrivial (Vec d) := inferInstance

private theorem integral_norm_rpow_one_sub_dim_ball {R : ℝ} (hR : 0 < R) :
    ∫ x in Metric.ball (0 : Vec d) R, ‖x‖ ^ (1 - (d : ℝ)) ∂MeasureTheory.volume =
      (d : ℝ) * (MeasureTheory.volume (Metric.ball (0 : Vec d) 1)).toReal * R := by
  let f : ℝ → ℝ := fun r => if 0 < r ∧ r < R then r ^ (1 - (d : ℝ)) else 0
  have hconv :
      ∫ x in Metric.ball (0 : Vec d) R, ‖x‖ ^ (1 - (d : ℝ)) ∂MeasureTheory.volume =
        ∫ x : Vec d, f (‖x‖) ∂MeasureTheory.volume := by
    rw [← MeasureTheory.integral_indicator measurableSet_ball]
    refine MeasureTheory.integral_congr_ae ?_
    have hmeas0 :
        (MeasureTheory.volume : Measure (Vec d)) {(0 : Vec d)} = 0 := by
      exact MeasureTheory.measure_singleton _
    have hae :
        ∀ᵐ x ∂(MeasureTheory.volume : Measure (Vec d)), x ∈ ({(0 : Vec d)} : Set (Vec d))ᶜ :=
      MeasureTheory.compl_mem_ae_iff.mpr hmeas0
    filter_upwards [hae] with x hx
    simp only [f, Set.indicator, Metric.mem_ball, dist_zero_right]
    have hx' : x ≠ (0 : Vec d) := by
      simpa using hx
    have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx'
    simp only [and_iff_right hpos]
  have hrad :
      ∫ x : Vec d, f (‖x‖) ∂MeasureTheory.volume =
        (Module.finrank ℝ (Vec d) : ℝ) •
            (MeasureTheory.volume : Measure (Vec d)).real (Metric.ball 0 1) •
              ∫ y in Set.Ioi (0 : ℝ), y ^ (Module.finrank ℝ (Vec d) - 1) • f y := by
    simpa [nsmul_eq_mul] using
      (MeasureTheory.integral_fun_norm_addHaar
        (μ := (MeasureTheory.volume : Measure (Vec d))) f)
  have hfin : Module.finrank ℝ (Vec d) = d := by
    simp [Vec]
  have h1d :
      ∫ y in Set.Ioi (0 : ℝ), y ^ (Module.finrank ℝ (Vec d) - 1) • f y = R := by
    rw [hfin]
    have hR_nonneg : 0 ≤ R := le_of_lt hR
    have hsupp :
        ∀ y ∈ Set.Ioi (0 : ℝ), y ^ (d - 1) • f y =
          Set.indicator (Set.Ioo 0 R) (fun _ => (1 : ℝ)) y := by
      intro y hy
      have hy_pos : 0 < y := hy
      by_cases hlt : y < R
      · simp only [f, smul_eq_mul, Set.indicator, Set.mem_Ioo, hy_pos, hlt, true_and,
          if_true]
        rw [← Real.rpow_natCast y (d - 1),
          Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)),
          ← Real.rpow_add hy_pos]
        norm_num
      · simp only [f, smul_eq_mul, Set.indicator, Set.mem_Ioo, hy_pos, hlt, true_and,
          if_false, mul_zero]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hsupp]
    rw [MeasureTheory.integral_indicator measurableSet_Ioo]
    simp [Measure.restrict_restrict, Set.inter_comm, Set.inter_eq_left.mpr Set.Ioo_subset_Ioi_self,
      smul_eq_mul, mul_one,
      Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal hR_nonneg]
  rw [hconv, hrad, h1d, hfin]
  simp [Measure.real]
  ring

theorem rieszKernel_integrableOn_ball {R : ℝ} (_hR : 0 < R) :
    MeasureTheory.IntegrableOn
      (fun x : Vec d => ‖x‖ ^ (1 - (d : ℝ)))
      (Metric.ball (0 : Vec d) R) MeasureTheory.volume := by
  let g : ℝ → ℝ := fun r => if r < R then r ^ (1 - (d : ℝ)) else 0
  have hag :
      (fun x : Vec d => ‖x‖ ^ (1 - (d : ℝ))) =ᵐ[MeasureTheory.volume.restrict (Metric.ball (0 : Vec d) R)]
        (g ∘ (‖·‖)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_ball] with x hx
    simp only [Function.comp_apply, g, Metric.mem_ball, dist_zero_right] at hx ⊢
    rw [if_pos hx]
  rw [MeasureTheory.IntegrableOn, MeasureTheory.integrable_congr hag]
  suffices h : MeasureTheory.Integrable (fun x : Vec d => g ‖x‖) MeasureTheory.volume from
    h.integrableOn
  have h1d :
      MeasureTheory.IntegrableOn
        (fun y : ℝ => y ^ (Module.finrank ℝ (Vec d) - 1) • g y)
        (Set.Ioi 0) := by
    have hfin : Module.finrank ℝ (Vec d) = d := by
      simp [Vec]
    set hInd : ℝ → ℝ := (Set.Ioo (0 : ℝ) R).indicator (fun _ => (1 : ℝ))
    have heq :
        Set.EqOn
          (fun y : ℝ => y ^ (Module.finrank ℝ (Vec d) - 1) • g y)
          hInd
          (Set.Ioi 0) := by
      intro r hr
      simp only [Set.mem_Ioi] at hr
      simp only [g, smul_eq_mul, hInd, Set.indicator, Set.mem_Ioo]
      split_ifs with h1 h2
      · rw [hfin, ← Real.rpow_natCast r (d - 1),
          Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)),
          ← Real.rpow_add hr]
        norm_num
      · next h2 => exact absurd ⟨hr, h1⟩ h2
      · next h1 h2 => exact absurd h2.2 h1
      · simp [mul_zero]
    have hInd_int : MeasureTheory.IntegrableOn hInd (Set.Ioi 0) := by
      apply MeasureTheory.Integrable.integrableOn
      exact (MeasureTheory.integrable_indicator_iff measurableSet_Ioo).mpr <|
        MeasureTheory.integrableOn_const (s := Set.Ioo 0 R)
          (hs := measure_Ioo_lt_top.ne)
    exact hInd_int.congr_fun heq.symm measurableSet_Ioi
  exact (MeasureTheory.integrable_fun_norm_addHaar (μ := MeasureTheory.volume) (f := g)).mpr h1d

theorem integrableOn_rieszKernel_ball
    {R : ℝ} (hR : 0 < R) (x : Vec d) (hx : x ∈ Metric.ball (0 : Vec d) R) :
    MeasureTheory.IntegrableOn (fun y : Vec d => rieszKernel x y)
      (Metric.ball (0 : Vec d) R) MeasureTheory.volume := by
  have hBsub : Metric.ball (0 : Vec d) R ⊆ Metric.ball x (2 * R) := by
    intro y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy ⊢
    have hxNorm : ‖x‖ < R := by
      simpa [Metric.mem_ball, dist_zero_right] using hx
    have hyNorm : ‖y‖ < R := by
      simpa using hy
    calc
      ‖y - x‖ ≤ ‖y‖ + ‖x‖ := norm_sub_le _ _
      _ < R + R := add_lt_add hyNorm hxNorm
      _ = 2 * R := by ring
  have hmp := MeasureTheory.measurePreserving_add_right (MeasureTheory.volume : Measure (Vec d)) x
  have hemb := (MeasurableEquiv.addRight x : Vec d ≃ᵐ Vec d).measurableEmbedding
  have hpre :
      (· + x) ⁻¹' Metric.ball x (2 * R) = Metric.ball (0 : Vec d) (2 * R) := by
    ext z
    simp [Metric.mem_ball]
  have hBigInt :
      MeasureTheory.IntegrableOn (fun y : Vec d => rieszKernel x y)
        (Metric.ball x (2 * R)) MeasureTheory.volume := by
    rw [← hmp.integrableOn_comp_preimage hemb, hpre]
    exact (rieszKernel_integrableOn_ball (d := d) (by linarith : 0 < 2 * R)).congr
      (Filter.Eventually.of_forall (fun z => by
        unfold rieszKernel
        show ‖z‖ ^ (1 - (d : ℝ)) = ‖x - (z + x)‖ ^ (1 - (d : ℝ))
        simp [norm_neg]))
  exact hBigInt.mono_set hBsub

theorem integral_rieszKernel_ball_le
    {R : ℝ} (hR : 0 < R) (x : Vec d) (hx : x ∈ Metric.ball (0 : Vec d) R) :
    ∫ y in Metric.ball (0 : Vec d) R, rieszKernel x y ∂MeasureTheory.volume ≤
      (d : ℝ) * (MeasureTheory.volume (Metric.ball (0 : Vec d) 1)).toReal * (2 * R) := by
  have hxDist : dist x 0 < R := Metric.mem_ball.mp hx
  have hBsub : Metric.ball (0 : Vec d) R ⊆ Metric.ball x (2 * R) := by
    intro y hy
    rw [Metric.mem_ball] at hy ⊢
    calc
      dist y x ≤ dist y 0 + dist 0 x := dist_triangle y 0 x
      _ < R + R := by
        rw [dist_comm] at hxDist
        linarith [Metric.mem_ball.mp hy]
      _ = 2 * R := by ring
  calc
    ∫ y in Metric.ball (0 : Vec d) R, rieszKernel x y ∂MeasureTheory.volume
        ≤ ∫ z in Metric.ball (0 : Vec d) (2 * R), ‖z‖ ^ (1 - (d : ℝ)) ∂MeasureTheory.volume := by
            have hmp := MeasureTheory.measurePreserving_add_right (MeasureTheory.volume : Measure (Vec d)) x
            have hemb := (MeasurableEquiv.addRight x : Vec d ≃ᵐ Vec d).measurableEmbedding
            have hpre :
                (· + x) ⁻¹' Metric.ball x (2 * R) = Metric.ball (0 : Vec d) (2 * R) := by
              ext z
              simp [Metric.mem_ball]
            have htrans :
                ∫ y in Metric.ball x (2 * R), rieszKernel x y ∂MeasureTheory.volume =
                  ∫ z in Metric.ball (0 : Vec d) (2 * R), ‖z‖ ^ (1 - (d : ℝ)) ∂MeasureTheory.volume := by
              rw [← hmp.setIntegral_preimage_emb hemb, hpre]
              congr 1 with z
              unfold rieszKernel
              show ‖x - (z + x)‖ ^ (1 - (d : ℝ)) = ‖z‖ ^ (1 - (d : ℝ))
              simp [norm_neg]
            have hinteg :
                MeasureTheory.IntegrableOn (fun y => rieszKernel x y)
                  (Metric.ball x (2 * R)) MeasureTheory.volume := by
              have h2R : (0 : ℝ) < 2 * R := by linarith
              rw [← hmp.integrableOn_comp_preimage hemb, hpre]
              exact (rieszKernel_integrableOn_ball (d := d) h2R).congr
                (Filter.Eventually.of_forall (fun z => by
                  unfold rieszKernel
                  show ‖z‖ ^ (1 - (d : ℝ)) = ‖x - (z + x)‖ ^ (1 - (d : ℝ))
                  simp [norm_neg]))
            calc
              ∫ y in Metric.ball (0 : Vec d) R, rieszKernel x y ∂MeasureTheory.volume
                  ≤ ∫ y in Metric.ball x (2 * R), rieszKernel x y ∂MeasureTheory.volume := by
                      apply MeasureTheory.setIntegral_mono_set hinteg
                      · exact Filter.Eventually.of_forall (fun y => rieszKernel_nonneg x y)
                      · exact hBsub.eventuallyLE
              _ = ∫ z in Metric.ball (0 : Vec d) (2 * R), ‖z‖ ^ (1 - (d : ℝ)) ∂MeasureTheory.volume :=
                    htrans
    _ = (d : ℝ) * (MeasureTheory.volume (Metric.ball (0 : Vec d) 1)).toReal * (2 * R) := by
          exact integral_norm_rpow_one_sub_dim_ball (d := d) (by linarith)

end NeZero

section BoundedDomain

variable {d : ℕ} {U : Set (Vec d)} [NeZero d]

/-- Cache `Nontrivial (Vec d)` once per section. -/
private instance instNontrivialVecBounded : Nontrivial (Vec d) := inferInstance

theorem IsBoundedDomain.integrableOn_rieszKernel
    (hU : IsBoundedDomain U) {x : Vec d} (hx : x ∈ U) :
    MeasureTheory.IntegrableOn (fun y : Vec d => rieszKernel x y) U MeasureTheory.volume := by
  let C := Classical.choose hU
  have hCpos : 0 < C := (Classical.choose_spec hU).1
  have hsub : U ⊆ Metric.ball (0 : Vec d) (2 * C) := by
    intro y hy
    rw [Metric.mem_ball, dist_zero_right]
    calc
      ‖y‖ ≤ C := hU.norm_le_choose hy
      _ < 2 * C := by linarith [hCpos]
  have hxBall : x ∈ Metric.ball (0 : Vec d) (2 * C) := hsub hx
  have hIntBall :
      MeasureTheory.IntegrableOn
        (fun y : Vec d => rieszKernel x y)
        (Metric.ball (0 : Vec d) (2 * C)) MeasureTheory.volume :=
    integrableOn_rieszKernel_ball (d := d) (by linarith [hCpos] : 0 < 2 * C) x hxBall
  exact hIntBall.mono_set hsub

theorem IsBoundedDomain.integral_rieszKernel_le
    (hU : IsBoundedDomain U) {x : Vec d} (hx : x ∈ U) :
    ∫ y in U, rieszKernel x y ∂MeasureTheory.volume ≤
      (d : ℝ) * (MeasureTheory.volume (Metric.ball (0 : Vec d) 1)).toReal *
        (4 * Classical.choose hU) := by
  let C := Classical.choose hU
  have hCpos : 0 < C := (Classical.choose_spec hU).1
  have hsub : U ⊆ Metric.ball (0 : Vec d) (2 * C) := by
    intro y hy
    rw [Metric.mem_ball, dist_zero_right]
    calc
      ‖y‖ ≤ C := hU.norm_le_choose hy
      _ < 2 * C := by linarith [hCpos]
  have hxBall : x ∈ Metric.ball (0 : Vec d) (2 * C) := hsub hx
  have hIntBall :
      MeasureTheory.IntegrableOn (fun y : Vec d => rieszKernel x y)
        (Metric.ball (0 : Vec d) (2 * C)) MeasureTheory.volume :=
    integrableOn_rieszKernel_ball (d := d) (by linarith [hCpos] : 0 < 2 * C) x hxBall
  calc
    ∫ y in U, rieszKernel x y ∂MeasureTheory.volume
        ≤ ∫ y in Metric.ball (0 : Vec d) (2 * C), rieszKernel x y ∂MeasureTheory.volume := by
            exact MeasureTheory.setIntegral_mono_set hIntBall
              (Filter.Eventually.of_forall (fun y => rieszKernel_nonneg x y))
              hsub.eventuallyLE
    _ ≤ (d : ℝ) * (MeasureTheory.volume (Metric.ball (0 : Vec d) 1)).toReal * (2 * (2 * C)) := by
          exact integral_rieszKernel_ball_le (d := d) (by linarith [hCpos] : 0 < 2 * C) x hxBall
    _ = (d : ℝ) * (MeasureTheory.volume (Metric.ball (0 : Vec d) 1)).toReal *
          (4 * Classical.choose hU) := by
            ring

theorem IsBoundedDomain.integrableOn_rieszKernel_right
    (hU : IsBoundedDomain U) {y : Vec d} (hy : y ∈ U) :
    MeasureTheory.IntegrableOn (fun x : Vec d => rieszKernel x y) U MeasureTheory.volume := by
  simpa [rieszKernel_symm] using hU.integrableOn_rieszKernel (x := y) hy

theorem IsBoundedDomain.integral_rieszKernel_right_le
    (hU : IsBoundedDomain U) {y : Vec d} (hy : y ∈ U) :
    ∫ x in U, rieszKernel x y ∂MeasureTheory.volume ≤
      (d : ℝ) * (MeasureTheory.volume (Metric.ball (0 : Vec d) 1)).toReal *
        (4 * Classical.choose hU) := by
  simpa [rieszKernel_symm] using hU.integral_rieszKernel_le (x := y) hy

theorem integrableOn_prod_rieszKernel_of_isSobolevRegularDomain
    (hU : IsSobolevRegularDomain U) :
    MeasureTheory.IntegrableOn
      (fun z : Vec d × Vec d => rieszKernel z.1 z.2)
      (U ×ˢ U) (MeasureTheory.volume.prod MeasureTheory.volume) := by
  let μU : MeasureTheory.Measure (Vec d) := MeasureTheory.volume.restrict U
  let : MeasureTheory.IsFiniteMeasure μU := hU.isBoundedDomain.isFiniteMeasure_restrict_volume
  set M : ℝ :=
    (d : ℝ) * (MeasureTheory.volume (Metric.ball (0 : Vec d) 1)).toReal *
      (4 * Classical.choose hU.isBoundedDomain)
  have hkernel_meas : Measurable (fun z : Vec d × Vec d => rieszKernel z.1 z.2) := by
    unfold rieszKernel
    fun_prop
  have hsections :
      ∀ᵐ y ∂μU, MeasureTheory.Integrable (fun x => rieszKernel x y) μU := by
    filter_upwards [MeasureTheory.ae_restrict_mem hU.measurableSet] with y hy
    simpa [μU, MeasureTheory.IntegrableOn] using
      hU.isBoundedDomain.integrableOn_rieszKernel_right hy
  have hkernel_swap_meas : Measurable (fun z : Vec d × Vec d => ‖rieszKernel z.2 z.1‖) := by
    unfold rieszKernel
    fun_prop
  have houter_meas :
      AEStronglyMeasurable (fun y => ∫ x, ‖rieszKernel x y‖ ∂μU) μU := by
    exact hkernel_swap_meas.aemeasurable.aestronglyMeasurable.integral_prod_right'
  have houter_bound :
      ∀ᵐ y ∂μU, ‖∫ x, ‖rieszKernel x y‖ ∂μU‖ ≤ M := by
    filter_upwards [MeasureTheory.ae_restrict_mem hU.measurableSet] with y hy
    have hnonneg :
        0 ≤ ∫ x, ‖rieszKernel x y‖ ∂μU :=
      MeasureTheory.integral_nonneg (fun x => norm_nonneg _)
    calc
      ‖∫ x, ‖rieszKernel x y‖ ∂μU‖
          = ∫ x, ‖rieszKernel x y‖ ∂μU := by
              rw [Real.norm_of_nonneg hnonneg]
      _ = ∫ x, rieszKernel x y ∂μU := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with x
            rw [Real.norm_of_nonneg (rieszKernel_nonneg x y)]
      _ ≤ M := by
            simpa [μU, M] using hU.isBoundedDomain.integral_rieszKernel_right_le hy
  have houter_int : MeasureTheory.Integrable (fun _ : Vec d => M) μU :=
    MeasureTheory.integrable_const M
  have hnorm_int :
      MeasureTheory.Integrable (fun y => ∫ x, ‖rieszKernel x y‖ ∂μU) μU :=
    houter_int.mono' houter_meas houter_bound
  have hprod_int :
      MeasureTheory.Integrable (fun z : Vec d × Vec d => rieszKernel z.1 z.2) (μU.prod μU) := by
    exact (MeasureTheory.integrable_prod_iff' hkernel_meas.aestronglyMeasurable).2
      ⟨hsections, hnorm_int⟩
  simpa [μU, MeasureTheory.IntegrableOn, MeasureTheory.Measure.prod_restrict] using hprod_int

end BoundedDomain

end Homogenization
