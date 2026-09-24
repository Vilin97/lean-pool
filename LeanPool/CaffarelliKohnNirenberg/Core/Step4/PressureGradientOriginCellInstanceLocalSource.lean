/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceCenteredSource
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceMeanNorm
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientCentredSWSData
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceSourceObligations

/-!
# Centered source control on arbitrary interior time boxes

The source estimate in `eq:pressure-gradient-morrey` is valid on any local
box of `def:sws`, not only on a backward cylinder's time window.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic

noncomputable section
namespace CKN.Core.Step4

/-- The actual centered tensor source is bounded by the integrable source
majorant on every interior ball-times-window box. -/
theorem origin_centered_source_le_majorant_on_local_box
    {Ω : Set Vec3} {I J : Set ℝ} {q ρ : ℝ} {x : Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) (hρ : 0 < ρ)
    (hbox : localBox Ω I (vec3Ball x ρ) J) :
    ∀ᵐ s ∂volume.restrict J,
      (∑ i : Fin 3, eLpNorm (fun y => pressureDivergenceCutoffSourceCentredTensor
        (mollifiedBallCutoff x hρ) (spatialDeriv (mollifiedBallCutoff x hρ))
        (fun y => u (y, s)) (fun y => Du (y, s))
        (fun j => average (volume.restrict (vec3Ball x ρ)) (fun y => u (y, s) j)) y i)
        (ENNReal.ofReal (6 / 5 : ℝ)) volume) ≤ originCenteredSourceMajorant x ρ u Du s := by
  have hu3 : Integrable (fun w : Vec3 × ℝ => vec3EuclideanNorm (u w) ^ (3 : ℕ))
      ((volume.restrict (vec3Ball x ρ)).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict]
    exact origin_velocity_cube_integrable_on_local_box hsol hbox
  have hglobal := origin_centered_source_memLp_ae_on_local_box hsol hbox hρ (Subset.refl _)
    (fun s j => average (volume.restrict (vec3Ball x ρ)) (fun y => u (y, s) j))
  let : IsFiniteMeasure (volume.restrict (vec3Ball x ρ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact
      (measure_mono subset_closure).trans_lt hbox.2.1.measure_lt_top⟩
  filter_upwards [hu3.prod_left_ae, slice_memLp_ae_of_sws hsol hbox, hglobal]
    with s hu3s hs hglob
  have hus := hs.1.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  let U := eLpNorm (fun y => vec3EuclideanNorm (u (y, s)))
    (ENNReal.ofReal (3 : ℝ)) (volume.restrict (vec3Ball x ρ))
  let D := eLpNorm (fun y => ‖Du (y, s)‖)
    (ENNReal.ofReal (2 : ℝ)) (volume.restrict (vec3Ball x ρ))
  let c : Vec3 := fun j => average (volume.restrict (vec3Ball x ρ)) (fun y => u (y, s) j)
  let V := pressureDivergenceCutoffSourceCentredTensor
    (mollifiedBallCutoff x hρ) (spatialDeriv (mollifiedBallCutoff x hρ))
    (fun y => u (y, s)) (fun y => Du (y, s)) c
  have hUi (i : Fin 3) : eLpNorm (fun y => u (y, s) i)
      (ENNReal.ofReal (3 : ℝ)) (volume.restrict (vec3Ball x ρ)) ≤ U := by
    apply eLpNorm_mono_ae (hs.1.eval i).aestronglyMeasurable
    exact Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, Real.norm_of_nonneg (vec3EuclideanNorm_nonneg _)]
      exact abs_apply_le_vec3EuclideanNorm _ i
  have hDi (i j : Fin 3) : eLpNorm (fun y => Du (y, s) i j)
      (ENNReal.ofReal (2 : ℝ)) (volume.restrict (vec3Ball x ρ)) ≤ D := by
    apply eLpNorm_mono_ae ((hs.2.eval i).eval j).aestronglyMeasurable
    exact Eventually.of_forall fun y => by
      rw [norm_norm]
      exact (norm_le_pi_norm (Du (y, s) i) j).trans (norm_le_pi_norm (Du (y, s)) i)
  have hWi (j : Fin 3) : eLpNorm (fun y => u (y, s) j - c j)
      (ENNReal.ofReal (3 : ℝ)) (volume.restrict (vec3Ball x ρ)) ≤
      (8 : ℝ≥0∞) ^ (1 / 3 : ℝ) * U :=
    origin_slice_mean_free_component_norm_bound hρ hus hu3s j
  have hCd : 0 ≤ cutoffGradientConstant / ρ :=
    (vecEuclideanNorm_nonneg _).trans (mollifiedBallCutoff_gradient_bound x hρ x)
  have hlocal (i : Fin 3) := origin_centered_tensor_source_slice_bound
    (c := c) (i := i) (by
      rw [Measure.restrict_apply_univ]
      exact (measure_mono (μ := volume) subset_closure).trans_lt (measure_closure_vec3Ball_lt_top hρ))
    (by norm_num : (0 : ℝ) ≤ 1) hCd
    (mollifiedBallCutoff_smooth x hρ).continuous.aestronglyMeasurable
    (Eventually.of_forall fun y => by
      rw [abs_of_nonneg (mollifiedBallCutoff_nonneg x hρ y)]
      exact mollifiedBallCutoff_le_one x hρ y)
    (fun j => (contDiff_spatialDeriv_smooth (mollifiedBallCutoff_smooth x hρ) j).continuous.aestronglyMeasurable)
    (fun j => Eventually.of_forall fun y =>
      (abs_apply_le_vecEuclideanNorm (classicalGradient (mollifiedBallCutoff x hρ) y) j).trans
        (mollifiedBallCutoff_gradient_bound x hρ y))
    (hUi i) (hDi i) hWi (fun j => (hs.1.eval j).aestronglyMeasurable)
    (fun j => ((hs.2.eval i).eval j).aestronglyMeasurable)
  have hbound (i : Fin 3) : eLpNorm (fun y => V y i) (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
      3 * (8 : ℝ≥0∞) ^ (1 / 3 : ℝ) *
        (D * U + ENNReal.ofReal (cutoffGradientConstant / ρ) *
          (U * U * volume (vec3Ball x ρ) ^ (1 / 6 : ℝ))) := by
    have hsupp : Function.support (fun y => V y i) ⊆ vec3Ball x ρ := by
      intro y hy
      by_contra hn
      have he : mollifiedBallCutoff x hρ y = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hn (pressure_cutoff_support_subset_ball x hρ h))
      have hd (j : Fin 3) : spatialDeriv (mollifiedBallCutoff x hρ) j y = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hn
          (pressure_cutoff_support_subset_ball x hρ ((tsupport_fderiv_apply_subset ℝ (basisVec j)) h)))
      apply hy
      simp only [V, pressureDivergenceCutoffSourceCentredTensor, he, hd, zero_mul,
        add_zero, Finset.sum_const_zero]
    rw [← eLpNorm_restrict_eq_of_support_subset (hglob i).aestronglyMeasurable hsupp]
    refine (hlocal i).trans_eq ?_
    simp only [ENNReal.ofReal_one, one_mul]
    ring
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hbound i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat, ← mul_assoc, show (3 : ℝ≥0∞) * 3 = 9 by norm_num] at hh
  refine hh.trans_eq ?_
  unfold originCenteredSourceMajorant
  dsimp only [U, D]
  ring


end CKN.Core.Step4
