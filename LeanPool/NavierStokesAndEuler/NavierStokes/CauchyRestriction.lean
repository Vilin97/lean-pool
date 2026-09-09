/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Bounded Cauchy differentiation between closed disks

The operator integrates on a circle of radius `σ - ρ` centered at each point
of the smaller disk. It is defined on all continuous outer-disk functions;
on holomorphic inputs it agrees with the actual complex derivative.
-/

noncomputable section

open Set Metric Complex MeasureTheory
open scoped Topology Interval ContDiff

namespace NavierStokes.CauchyRestriction

abbrev Disk (c : ℂ) (r : ℝ) := ↥(closedBall c r)

instance diskCompactSpace (c : ℂ) (r : ℝ) : CompactSpace (Disk c r) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall c r)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

noncomputable def inclusion (c : ℂ) {ρ σ : ℝ} (h : ρ ≤ σ) : C(Disk c ρ, Disk c σ) where
  toFun z := ⟨z.1, closedBall_subset_closedBall h z.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

def restrictionLinear (c : ℂ) {ρ σ : ℝ} (h : ρ ≤ σ) :
    C(Disk c σ, E) →ₗ[ℂ] C(Disk c ρ, E) where
  toFun f := f.comp (inclusion c h)
  map_add' f g := by ext z; rfl
  map_smul' a f := by ext z; rfl

theorem norm_restrictionLinear_le (c : ℂ) {ρ σ : ℝ} (h : ρ ≤ σ)
    (f : C(Disk c σ, E)) : ‖restrictionLinear c h f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).2
  intro z
  exact f.norm_coe_le_norm _

def restrictionCLM (c : ℂ) {ρ σ : ℝ} (h : ρ ≤ σ) :
    C(Disk c σ, E) →L[ℂ] C(Disk c ρ, E) :=
  (restrictionLinear c h).mkContinuous 1 (by
    intro f
    simpa only [one_mul] using norm_restrictionLinear_le c h f)

@[simp] theorem restrictionCLM_apply (c : ℂ) {ρ σ : ℝ} (h : ρ ≤ σ)
    (f : C(Disk c σ, E)) (z : Disk c ρ) :
    restrictionCLM c h f z = f ⟨z.1, closedBall_subset_closedBall h z.2⟩ := rfl

theorem restrictionCLM_comp (c : ℂ) {r ρ σ : ℝ} (h₁ : r ≤ ρ) (h₂ : ρ ≤ σ) :
    (restrictionCLM (E := E) c h₁).comp (restrictionCLM c h₂) =
      restrictionCLM c (h₁.trans h₂) := by
  ext f z
  rfl

theorem offset_ne_zero {δ : ℝ} (hδ : 0 < δ) (θ : ℝ) : circleMap 0 δ θ ≠ 0 := by
  intro h
  have hn := congrArg norm h
  simp only [norm_circleMap_zero, abs_of_pos hδ, norm_zero] at hn
  exact hδ.ne' hn

theorem translated_mem (c : ℂ) {ρ σ : ℝ} (hgap : ρ < σ)
    (z : Disk c ρ) (θ : ℝ) : z.1 + circleMap 0 (σ - ρ) θ ∈ closedBall c σ := by
  change dist (z.1 + circleMap 0 (σ - ρ) θ) c ≤ σ
  calc
    dist (z.1 + circleMap 0 (σ - ρ) θ) c ≤
      dist (z.1 + circleMap 0 (σ - ρ) θ) z.1 + dist z.1 c := dist_triangle _ _ _
    _ = ‖circleMap 0 (σ - ρ) θ‖ + dist z.1 c := by simp [dist_eq_norm]
    _ ≤ ‖circleMap 0 (σ - ρ) θ‖ + ρ := add_le_add_right z.2 _
    _ = σ := by rw [norm_circleMap_zero, abs_of_pos (sub_pos.mpr hgap)]; ring

def sample (c : ℂ) {ρ σ : ℝ} (hgap : ρ < σ) (θ : ℝ) :
    C(Disk c ρ, Disk c σ) where
  toFun z := ⟨z.1 + circleMap 0 (σ - ρ) θ, translated_mem c hgap z θ⟩
  continuous_toFun := (continuous_subtype_val.add continuous_const).subtype_mk _

def weight (δ θ : ℝ) : ℂ := I / circleMap 0 δ θ

theorem continuous_weight {δ : ℝ} (hδ : 0 < δ) : Continuous (weight δ) :=
  continuous_const.div (continuous_circleMap 0 δ) (offset_ne_zero hδ)

theorem norm_weight {δ : ℝ} (hδ : 0 < δ) (θ : ℝ) : ‖weight δ θ‖ = δ⁻¹ := by
  simp [weight, norm_circleMap_zero, abs_of_pos hδ, one_div]

def integrand (c : ℂ) {ρ σ : ℝ} (hgap : ρ < σ)
    (f : C(Disk c σ, E)) (θ : ℝ) : C(Disk c ρ, E) :=
  weight (σ - ρ) θ • f.comp (sample c hgap θ)

theorem continuous_integrand (c : ℂ) {ρ σ : ℝ} (hgap : ρ < σ)
    (f : C(Disk c σ, E)) : Continuous (integrand c hgap f) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ℝ × Disk c ρ =>
    weight (σ - ρ) p.1 • f ⟨p.2.1 + circleMap 0 (σ - ρ) p.1,
      translated_mem c hgap p.2 p.1⟩)
  apply ((continuous_weight (sub_pos.mpr hgap)).comp continuous_fst).smul
  exact f.continuous.comp ((continuous_snd.subtype_val.add
    ((continuous_circleMap 0 (σ - ρ)).comp continuous_fst)).subtype_mk _)

theorem norm_integrand_le (c : ℂ) {ρ σ : ℝ} (hgap : ρ < σ)
    (f : C(Disk c σ, E)) (θ : ℝ) :
    ‖integrand c hgap f θ‖ ≤ (σ - ρ)⁻¹ * ‖f‖ := by
  have hδ : 0 < σ - ρ := sub_pos.mpr hgap
  apply (ContinuousMap.norm_le _ (by positivity)).2
  intro z
  change ‖weight (σ - ρ) θ • f (sample c hgap θ z)‖ ≤ _
  rw [norm_smul, norm_weight (sub_pos.mpr hgap)]
  exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (by positivity)

def cauchyMap (c : ℂ) {ρ σ : ℝ} (hgap : ρ < σ)
    (f : C(Disk c σ, E)) : C(Disk c ρ, E) :=
  (2 * Real.pi * I : ℂ)⁻¹ • ∫ θ : ℝ in (0)..(2 * Real.pi), integrand c hgap f θ

theorem cauchyMap_add (c : ℂ) {ρ σ : ℝ} (hgap : ρ < σ)
    (f g : C(Disk c σ, E)) : cauchyMap c hgap (f + g) = cauchyMap c hgap f + cauchyMap c hgap g :=
      by
  have heq : integrand c hgap (f + g) = fun θ => integrand c hgap f θ + integrand c hgap g θ := by
    funext θ
    ext z
    exact smul_add _ _ _
  rw [cauchyMap, heq, intervalIntegral.integral_add
    ((continuous_integrand c hgap f).intervalIntegrable _ _)
    ((continuous_integrand c hgap g).intervalIntegrable _ _), smul_add]
  rfl

theorem cauchyMap_smul (c : ℂ) {ρ σ : ℝ} (hgap : ρ < σ)
    (a : ℂ) (f : C(Disk c σ, E)) : cauchyMap c hgap (a • f) = a • cauchyMap c hgap f := by
  have heq : integrand c hgap (a • f) = fun θ => a • integrand c hgap f θ := by
    funext θ
    ext z
    exact smul_comm _ _ _
  rw [cauchyMap, heq, intervalIntegral.integral_smul, smul_comm]
  rfl

theorem norm_cauchyMap_le (c : ℂ) {ρ σ : ℝ} (hgap : ρ < σ)
    (f : C(Disk c σ, E)) : ‖cauchyMap c hgap f‖ ≤ (σ - ρ)⁻¹ * ‖f‖ := by
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := 2 * Real.pi)
    (fun θ _ => norm_integrand_le c hgap f θ)
  have hnorm : ‖(2 * Real.pi * I : ℂ)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    simp [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [cauchyMap, norm_smul, hnorm]
  calc
    (2 * Real.pi)⁻¹ * ‖∫ θ : ℝ in (0)..(2 * Real.pi), integrand c hgap f θ‖ ≤
      (2 * Real.pi)⁻¹ * (((σ - ρ)⁻¹ * ‖f‖) * |2 * Real.pi - 0|) :=
        mul_le_mul_of_nonneg_left hi (by positivity)
    _ = (σ - ρ)⁻¹ * ‖f‖ := by
      rw [sub_zero, abs_of_pos Real.two_pi_pos]
      field_simp

def derivativeCLM (c : ℂ) {ρ σ : ℝ} (hgap : ρ < σ) :
    C(Disk c σ, E) →L[ℂ] C(Disk c ρ, E) :=
  ({ toFun := cauchyMap c hgap
     map_add' := cauchyMap_add c hgap
     map_smul' := cauchyMap_smul c hgap } :
       C(Disk c σ, E) →ₗ[ℂ] C(Disk c ρ, E)).mkContinuous
    (σ - ρ)⁻¹ (norm_cauchyMap_le c hgap)

theorem norm_derivativeCLM_le (c : ℂ) {ρ σ : ℝ} (hgap : ρ < σ) :
    ‖derivativeCLM (E := E) c hgap‖ ≤ (σ - ρ)⁻¹ := by
  have hδ : 0 < σ - ρ := sub_pos.mpr hgap
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact norm_cauchyMap_le c hgap

theorem norm_restrictionCLM_le (c : ℂ) {ρ σ : ℝ} (h : ρ ≤ σ) :
    ‖restrictionCLM (E := E) c h‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖restrictionLinear c h f‖ ≤ 1 * ‖f‖
  simpa only [one_mul] using norm_restrictionLinear_le c h f

variable [CompleteSpace E]

theorem derivativeCLM_apply_integral (c : ℂ) {ρ σ : ℝ} (hgap : ρ < σ)
    (f : C(Disk c σ, E)) (z : Disk c ρ) :
    derivativeCLM c hgap f z = (2 * Real.pi * I : ℂ)⁻¹ •
      ∫ θ : ℝ in (0)..(2 * Real.pi),
        weight (σ - ρ) θ • f (sample c hgap θ z) := by
  change cauchyMap c hgap f z = _
  rw [cauchyMap, ContinuousMap.smul_apply]
  congr 1
  have hi : IntervalIntegrable (integrand c hgap f) volume 0 (2 * Real.pi) :=
    (continuous_integrand c hgap f).intervalIntegrable _ _
  exact ((ContinuousMap.evalCLM ℂ z).intervalIntegral_comp_comm
    hi).symm

theorem ball_subset_outer (c : ℂ) {ρ σ : ℝ} (z : Disk c ρ) :
    ball (z : ℂ) (σ - ρ) ⊆ ball c σ := by
  intro w hw
  change dist w c < σ
  calc
    dist w c ≤ dist w (z : ℂ) + dist (z : ℂ) c := dist_triangle _ _ _
    _ < (σ - ρ) + ρ := add_lt_add_of_lt_of_le hw z.2
    _ = σ := by ring

omit [CompleteSpace E] in
theorem circle_kernel_identity {δ : ℝ} (hδ : 0 < δ) (z : ℂ) (θ : ℝ) (v : E) :
    weight δ θ • v = deriv (circleMap z δ) θ •
      ((circleMap z δ θ - z) ^ (-2 : ℤ) • v) := by
  rw [deriv_circleMap, smul_smul]
  have hsub : circleMap z δ θ - z = circleMap 0 δ θ := by simp [circleMap]
  rw [hsub]
  congr 1
  rw [weight, zpow_neg, zpow_two]
  field_simp [offset_ne_zero hδ θ]

/-- Use any holomorphic extension agreeing with the continuous outer-disk input. -/
theorem derivativeCLM_apply_of_eq (c : ℂ) {ρ σ : ℝ} (hgap : ρ < σ)
    (f : C(Disk c σ, E)) (F : ℂ → E)
    (hF : DiffContOnCl ℂ F (ball c σ))
    (hvalues : ∀ w : Disk c σ, f w = F w) (z : Disk c ρ) :
    derivativeCLM c hgap f z = deriv F z := by
  have hci := DiffContOnCl.deriv_eq_smul_circleIntegral
    (sub_pos.mpr hgap) (hF.mono (ball_subset_outer c z))
  have hfactor : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero]
  have hder : deriv F z = (2 * (Real.pi : ℂ) * I)⁻¹ •
      ∮ w in C(z, σ - ρ), (1 / (w - z) ^ 2) • F w := by
    rw [hci, inv_smul_smul₀ hfactor]
  rw [derivativeCLM_apply_integral, hder]
  congr 1
  rw [circleIntegral]
  apply intervalIntegral.integral_congr
  intro θ hθ
  dsimp only
  rw [hvalues]
  change weight (σ - ρ) θ • F ((z : ℂ) + circleMap 0 (σ - ρ) θ) = _
  have hpoint : (z : ℂ) + circleMap 0 (σ - ρ) θ = circleMap z (σ - ρ) θ := by
    simp [circleMap]
  rw [hpoint]
  simpa only [zpow_neg, zpow_two, pow_two, one_div] using
    circle_kernel_identity (sub_pos.mpr hgap) z θ (F (circleMap z (σ - ρ) θ))

noncomputable def ofContinuousOn (c : ℂ) (r : ℝ) (F : ℂ → E)
    (hF : ContinuousOn F (closedBall c r)) : C(Disk c r, E) :=
  ⟨fun z => F z, hF.domRestrict⟩

omit [NormedSpace ℂ E] [CompleteSpace E] in
@[simp] theorem ofContinuousOn_apply (c : ℂ) (r : ℝ) (F : ℂ → E)
    (hF : ContinuousOn F (closedBall c r)) (z : Disk c r) :
    ofContinuousOn c r F hF z = F z := rfl

/-- Agreement with the actual derivative under holomorphy in the open disk and
continuity on its closure. No smoothness of the derivative is assumed. -/
theorem derivativeCLM_apply_of_diffContOnCl (c : ℂ) {ρ σ : ℝ} (hgap : ρ < σ)
    (F : ℂ → E) (hF : DiffContOnCl ℂ F (ball c σ)) (z : Disk c ρ) :
    derivativeCLM c hgap (ofContinuousOn c σ F hF.continuousOn_ball) z = deriv F z :=
  derivativeCLM_apply_of_eq c hgap _ F hF (fun _ => rfl) z

theorem derivativeCLM_apply_of_differentiableOn (c : ℂ) {ρ σ : ℝ} (hgap : ρ < σ)
    (F : ℂ → E) (hF : DifferentiableOn ℂ F (closedBall c σ)) (z : Disk c ρ) :
    derivativeCLM c hgap (ofContinuousOn c σ F hF.continuousOn) z = deriv F z :=
  derivativeCLM_apply_of_eq c hgap _ F
    (DiffContOnCl.mk_ball (hF.mono ball_subset_closedBall) hF.continuousOn) (fun _ => rfl) z

/-- On holomorphic data, further restriction of the derivative does not depend
on which smaller target disk was used to construct the Cauchy integral. -/
theorem restrict_derivativeCLM_of_eq (c : ℂ) {r ρ σ : ℝ}
    (hr : r ≤ ρ) (hgap : ρ < σ) (f : C(Disk c σ, E)) (F : ℂ → E)
    (hF : DiffContOnCl ℂ F (ball c σ))
    (hvalues : ∀ w : Disk c σ, f w = F w) :
    restrictionCLM c hr (derivativeCLM c hgap f) =
      derivativeCLM c (hr.trans_lt hgap) f := by
  ext z
  change derivativeCLM c hgap f (inclusion c hr z) = _
  calc
    _ = deriv F z := derivativeCLM_apply_of_eq c hgap f F hF hvalues (inclusion c hr z)
    _ = _ := (derivativeCLM_apply_of_eq c (hr.trans_lt hgap) f F hF hvalues z).symm

/-- Restricting the source disk also gives the same derivative on common
smaller disks, provided the source represents a holomorphic function. -/
theorem derivativeCLM_restrict_of_eq (c : ℂ) {r ρ σ : ℝ}
    (hgap : r < ρ) (houter : ρ ≤ σ) (f : C(Disk c σ, E)) (F : ℂ → E)
    (hF : DiffContOnCl ℂ F (ball c σ))
    (hvalues : ∀ w : Disk c σ, f w = F w) :
    derivativeCLM c hgap (restrictionCLM c houter f) =
      derivativeCLM c (hgap.trans_le houter) f := by
  ext z
  calc
    _ = deriv F z := derivativeCLM_apply_of_eq c hgap (restrictionCLM c houter f) F
      (hF.mono (ball_subset_ball houter))
      (fun w => hvalues (inclusion c houter w)) z
    _ = _ := (derivativeCLM_apply_of_eq c (hgap.trans_le houter) f F hF hvalues z).symm

omit [CompleteSpace E] in
theorem continuous_derivative_path {X : Type*} [TopologicalSpace X]
    (c : ℂ) {ρ σ : ℝ} (hgap : ρ < σ) {f : X → C(Disk c σ, E)} (hf : Continuous f) :
    Continuous (fun x => derivativeCLM c hgap (f x)) :=
  (derivativeCLM c hgap).continuous.comp hf

omit [CompleteSpace E] in
theorem contDiff_derivative_path {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (c : ℂ) {ρ σ : ℝ} (hgap : ρ < σ) {n : WithTop ℕ∞}
    {f : X → C(Disk c σ, E)} (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun x => derivativeCLM c hgap (f x)) :=
  ((derivativeCLM c hgap).restrictScalars ℝ).contDiff.comp hf

end NavierStokes.CauchyRestriction
