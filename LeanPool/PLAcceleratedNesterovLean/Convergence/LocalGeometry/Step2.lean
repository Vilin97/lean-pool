/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.Core.NesterovScheme
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Local Geometry Step 2: Fiber Integration for Quadratic Growth and Strong Aiming

Fix x ∈ U₊, m = π(x), e = x - m. Define φ(t) = f(m + te).
Since U₊ is fiber-saturated, m + te ∈ U₊ for t ∈ [0,1].

φ(0) = f⋆, φ'(0) = 0, φ''(t) = eᵀ D²f(m+te) e ≥ μ'‖e‖².

## Quadratic growth (integrate φ'' twice):
  f(x) - f⋆ = φ(1) - φ(0) = ∫₀¹ (1-t) φ''(t) dt ≥ (μ'/2)‖e‖²

## Strong aiming (integration by parts):
  ⟨∇f(x), e⟩ - (f(x) - f⋆) = φ'(1) - (φ(1) - φ(0)) = ∫₀¹ t φ''(t) dt ≥ (μ'/2)‖e‖²
  So ⟨∇f(x), e⟩ ≥ f(x) - f⋆ + (μ'/2)‖e‖²
-/

noncomputable section

namespace PLAcceleratedNesterovLean

lemma differentiable_deriv_of_contDiff2 {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) :
    Differentiable ℝ (deriv φ) := by
  have hfderiv_C1 : ContDiff ℝ 1 (fderiv ℝ φ) :=
    hφ.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  have h1 : ContDiff ℝ 1 (fun x => (fderiv ℝ φ x) (1 : ℝ)) :=
    (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).contDiff.comp hfderiv_C1
  have h2 : deriv φ = fun x => (fderiv ℝ φ x) (1 : ℝ) := by
    ext x; exact fderiv_apply_one_eq_deriv.symm
  rw [h2]; exact h1.differentiable (by norm_num)

lemma hasDerivAt_const_mul_id (c x : ℝ) : HasDerivAt (fun t => c * t) c x := by
  have h := (hasDerivAt_id x).const_mul c
  simp only [mul_one] at h; exact h

lemma hasDerivAt_quad (c x : ℝ) :
    HasDerivAt (fun t => c / 2 * t ^ 2) (c * x) x := by
  have h1 : HasDerivAt (fun t : ℝ => t * t) (1 * x + x * 1) x :=
    (hasDerivAt_id x).mul (hasDerivAt_id x)
  have h2 : (fun t : ℝ => t * t) = (fun t => t ^ 2) := by ext t; ring
  rw [h2] at h1
  have h3 := h1.const_mul (c / 2)
  have : c / 2 * (1 * x + x * 1) = c * x := by ring
  rwa [this] at h3

lemma differentiable_sq : Differentiable ℝ (fun (t : ℝ) => t ^ 2) := by
  simp_all

lemma continuous_sq : Continuous (fun (t : ℝ) => t ^ 2) := by
  have : (fun t : ℝ => t ^ 2) = (fun t => t * t) := by ext; ring
  rw [this]; exact continuous_id.mul continuous_id

/-- If φ''(t) ≥ c for all t ∈ [0,1] and φ'(0) = 0, then φ(1) - φ(0) ≥ c/2.
    (Quadratic growth from Hessian lower bound.)
    Localized version: only requires ContinuousOn/DifferentiableOn on [0,1]. -/
theorem quadratic_growth_from_hessian (φ : ℝ → ℝ) (c : ℝ)
    (hφ_cont : ContinuousOn φ (Set.Icc 0 1))
    (hφ_diff : DifferentiableOn ℝ φ (Set.Ioo 0 1))
    (hφ'_cont : ContinuousOn (deriv φ) (Set.Icc 0 1))
    (hφ'_diff : DifferentiableOn ℝ (deriv φ) (Set.Ioo 0 1))
    (hφ'_zero : deriv φ 0 = 0)
    (hφ''_lower : ∀ t, 0 ≤ t → t ≤ 1 →
      deriv (deriv φ) t ≥ c) :
    φ 1 - φ 0 ≥ c / 2 := by
  -- Step 1: deriv φ t ≥ c * t for t ∈ [0,1]
  have hφ'_ge : ∀ t ∈ Set.Icc (0:ℝ) 1, deriv φ t - c * t ≥ 0 := by
    set g : ℝ → ℝ := fun t => deriv φ t - c * t
    have hg0 : g 0 = 0 := by
      change deriv φ 0 - c * 0 = 0; rw [hφ'_zero]; ring
    have hg_cont : ContinuousOn g (Set.Icc 0 1) :=
      hφ'_cont.sub (continuous_const.mul continuous_id).continuousOn
    have hg_diff : DifferentiableOn ℝ g (interior (Set.Icc 0 1)) := by
      rw [interior_Icc]
      exact hφ'_diff.sub
        ((differentiable_const c).mul differentiable_id).differentiableOn
    have hg'_nonneg : ∀ x ∈ interior (Set.Icc (0:ℝ) 1), 0 ≤ deriv g x := by
      intro x hx
      rw [interior_Icc] at hx
      have hda : HasDerivAt g (deriv (deriv φ) x - c) x :=
        (hφ'_diff.differentiableAt (Ioo_mem_nhds hx.1 hx.2)).hasDerivAt |>.sub
          (hasDerivAt_const_mul_id c x)
      rw [hda.deriv]
      linarith [hφ''_lower x (le_of_lt hx.1) (le_of_lt hx.2)]
    have hg_mono : MonotoneOn g (Set.Icc 0 1) :=
      monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hg_cont hg_diff hg'_nonneg
    intro t ht
    have h := hg_mono (Set.left_mem_Icc.mpr zero_le_one) ht ht.1
    linarith [hg0]
  -- Step 2: ψ(t) = φ(t) - c/2 * t² is monotone on [0,1]
  set ψ : ℝ → ℝ := fun t => φ t - c / 2 * t ^ 2
  have hψ_cont : ContinuousOn ψ (Set.Icc 0 1) :=
    hφ_cont.sub (continuous_const.mul continuous_sq).continuousOn
  have hψ_diff : DifferentiableOn ℝ ψ (interior (Set.Icc 0 1)) := by
    rw [interior_Icc]
    exact hφ_diff.sub
      ((differentiable_const (c/2)).mul differentiable_sq).differentiableOn
  have hψ'_nonneg : ∀ x ∈ interior (Set.Icc (0:ℝ) 1), 0 ≤ deriv ψ x := by
    intro x hx
    rw [interior_Icc] at hx
    have hda : HasDerivAt ψ (deriv φ x - c * x) x :=
      (hφ_diff.differentiableAt (Ioo_mem_nhds hx.1 hx.2)).hasDerivAt |>.sub
        (hasDerivAt_quad c x)
    rw [hda.deriv]
    linarith [hφ'_ge x (Set.mem_Icc.mpr ⟨le_of_lt hx.1, le_of_lt hx.2⟩)]
  have hψ_mono : MonotoneOn ψ (Set.Icc 0 1) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hψ_cont hψ_diff hψ'_nonneg
  have h := hψ_mono (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)
    zero_le_one
  simp only [ψ] at h
  linarith

/-- If φ''(t) ≥ c for all t ∈ [0,1] and φ'(0) = 0, then φ'(1) ≥ φ(1) - φ(0) + c/2.
    (Strong aiming from integration by parts.)
    Localized version: only requires ContinuousOn/DifferentiableOn on [0,1]. -/
theorem strong_aiming_from_hessian (φ : ℝ → ℝ) (c : ℝ)
    (hφ_cont : ContinuousOn φ (Set.Icc 0 1))
    (hφ_diff : DifferentiableOn ℝ φ (Set.Ioo 0 1))
    (hφ'_cont : ContinuousOn (deriv φ) (Set.Icc 0 1))
    (hφ'_diff : DifferentiableOn ℝ (deriv φ) (Set.Ioo 0 1))
    (hφ'_zero : deriv φ 0 = 0)
    (hφ''_lower : ∀ t, 0 ≤ t → t ≤ 1 →
      deriv (deriv φ) t ≥ c) :
    deriv φ 1 ≥ (φ 1 - φ 0) + c / 2 := by
  -- Define ψ(t) = t * φ'(t) - φ(t) + φ(0) - c/2 * t²
  set ψ : ℝ → ℝ := fun t => t * deriv φ t - φ t + φ 0 - c / 2 * t ^ 2
  have hψ0 : ψ 0 = 0 := by
    change 0 * deriv φ 0 - φ 0 + φ 0 - c / 2 * 0 ^ 2 = 0; rw [hφ'_zero]; ring
  have hψ_cont : ContinuousOn ψ (Set.Icc 0 1) := by
    apply ContinuousOn.sub
    · apply ContinuousOn.add
      · apply ContinuousOn.sub
        · exact continuous_id.continuousOn.mul hφ'_cont
        · exact hφ_cont
      · exact continuous_const.continuousOn
    · exact (continuous_const.mul continuous_sq).continuousOn
  have hψ_diff : DifferentiableOn ℝ ψ (interior (Set.Icc 0 1)) := by
    rw [interior_Icc]
    apply DifferentiableOn.sub
    · apply DifferentiableOn.add
      · apply DifferentiableOn.sub
        · exact differentiableOn_id.mul hφ'_diff
        · exact hφ_diff
      · exact differentiableOn_const _
    · exact ((differentiable_const (c/2)).mul differentiable_sq).differentiableOn
  have hψ'_nonneg : ∀ x ∈ interior (Set.Icc (0:ℝ) 1), 0 ≤ deriv ψ x := by
    intro x hx
    rw [interior_Icc] at hx
    -- ψ'(x) = x * (φ''(x) - c)
    have hφ_da : DifferentiableAt ℝ φ x :=
      hφ_diff.differentiableAt (Ioo_mem_nhds hx.1 hx.2)
    have hφ'_da : DifferentiableAt ℝ (deriv φ) x :=
      hφ'_diff.differentiableAt (Ioo_mem_nhds hx.1 hx.2)
    have hda_prod : HasDerivAt (fun t => t * deriv φ t)
      (1 * deriv φ x + x * deriv (deriv φ) x) x :=
      (hasDerivAt_id x).mul hφ'_da.hasDerivAt
    have hda_φ : HasDerivAt φ (deriv φ x) x := hφ_da.hasDerivAt
    have hda_const : HasDerivAt (fun _ => φ 0) 0 x := hasDerivAt_const x (φ 0)
    have hda : HasDerivAt ψ
      ((1 * deriv φ x + x * deriv (deriv φ) x) - deriv φ x + 0 - c * x) x :=
      ((hda_prod.sub hda_φ).add hda_const).sub (hasDerivAt_quad c x)
    rw [hda.deriv]
    have : (1 * deriv φ x + x * deriv (deriv φ) x) - deriv φ x + 0 - c * x =
           x * (deriv (deriv φ) x - c) := by ring
    rw [this]
    exact mul_nonneg (le_of_lt hx.1)
      (sub_nonneg.mpr (hφ''_lower x (le_of_lt hx.1) (le_of_lt hx.2)))
  have hψ_mono : MonotoneOn ψ (Set.Icc 0 1) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hψ_cont hψ_diff hψ'_nonneg
  have h := hψ_mono (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)
    zero_le_one
  simp only [ψ] at h
  linarith [hψ0]

/-- The fiber function φ(t) = f(m + t·e) has φ'(t) = ⟨∇f(m+te), e⟩. -/
theorem fiber_deriv {d : ℕ} (f : E d → ℝ) (m e : E d)
    (hf : Differentiable ℝ f) :
    ∀ t : ℝ, deriv (fun (s : ℝ) => f (m + s • e)) t =
      @inner ℝ _ _ (gradient f (m + t • e)) e := by
  intro t
  have hfat : DifferentiableAt ℝ f (m + t • e) := hf.differentiableAt
  have hg : HasDerivAt (fun s : ℝ => m + s • e) e t := by
    have h := (hasDerivAt_const t m).add ((hasDerivAt_id t).smul_const e)
    simp only [zero_add, one_smul] at h; exact h
  -- Chain rule: use @HasFDerivAt.comp_hasDerivAt_of_eq with explicit arguments
  have hcomp : HasDerivAt (f ∘ fun s => m + s • e) (fderiv ℝ f (m + t • e) e) t :=
    @HasFDerivAt.comp_hasDerivAt_of_eq ℝ _ (E d) _ _ ℝ _ _
      (fun s : ℝ => m + s • e) e t
      f (fderiv ℝ f (m + t • e)) (m + t • e)
      hfat.hasFDerivAt hg rfl
  have key := hcomp.deriv
  change deriv (f ∘ fun s => m + s • e) t = _
  simp_all

end PLAcceleratedNesterovLean
