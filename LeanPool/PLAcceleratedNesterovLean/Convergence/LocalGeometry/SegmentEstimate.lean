/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.Convergence.LocalGeometry.Step2
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Segment Estimate Helpers

Helper lemmas for the segment estimate used by `motion_bounds_curvature_error`.
Provides a generalized strong aiming lemma (no φ'(0) = 0 requirement)
and the fiber-path Hessian-to-second-derivative connection.
-/

noncomputable section

namespace PLAcceleratedNesterovLean

open scoped Topology NNReal

/-! ## Generalized segment estimate -/

/-- General segment estimate: if φ is C² and φ''(t) ≥ c for t ∈ [0,1],
then φ'(1) ≥ (φ(1) - φ(0)) + c/2.

Applies to C² functions with arbitrary φ'(0).
The proof uses ψ(t) = t·φ'(t) - φ(t) + φ(0) - (c/2)t², which satisfies
ψ(0) = 0 regardless of φ'(0) (since 0·φ'(0) = 0), and ψ'(t) = t·(φ''(t) - c) ≥ 0. -/
theorem segment_estimate_from_hessian (φ : ℝ → ℝ) (c : ℝ)
    (hφ_cont : ContinuousOn φ (Set.Icc 0 1))
    (hφ_diff : DifferentiableOn ℝ φ (Set.Ioo 0 1))
    (hφ'_cont : ContinuousOn (deriv φ) (Set.Icc 0 1))
    (hφ'_diff : DifferentiableOn ℝ (deriv φ) (Set.Ioo 0 1))
    (hφ''_lower : ∀ t, 0 ≤ t → t ≤ 1 →
      deriv (deriv φ) t ≥ c) :
    deriv φ 1 ≥ (φ 1 - φ 0) + c / 2 := by
  -- Define ψ(t) = t * φ'(t) - φ(t) + φ(0) - c/2 * t²
  set ψ : ℝ → ℝ := fun t => t * deriv φ t - φ t + φ 0 - c / 2 * t ^ 2
  -- Key: ψ(0) = 0 without needing φ'(0) = 0 (since 0 * φ'(0) = 0)
  have hψ0 : ψ 0 = 0 := by
    change 0 * deriv φ 0 - φ 0 + φ 0 - c / 2 * 0 ^ 2 = 0
    ring
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
    · exact ((differentiable_const (c/2)).mul differentiable_sq).differentiableOn.mono
        Set.Ioo_subset_Icc_self
  have hψ'_nonneg : ∀ x ∈ interior (Set.Icc (0:ℝ) 1), 0 ≤ deriv ψ x := by
    intro x hx
    rw [interior_Icc] at hx
    -- ψ'(x) = x * (φ''(x) - c)
    have hda_prod : HasDerivAt (fun t => t * deriv φ t)
      (1 * deriv φ x + x * deriv (deriv φ) x) x :=
      (hasDerivAt_id x).mul (hφ'_diff.differentiableAt (Ioo_mem_nhds hx.1 hx.2)).hasDerivAt
    have hda_φ : HasDerivAt φ (deriv φ x) x :=
      (hφ_diff.differentiableAt (Ioo_mem_nhds hx.1 hx.2)).hasDerivAt
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

/-! ## Fiber path second derivative = Hessian quadratic form -/

/-- The second derivative of the fiber path φ(t) = f(m + t·v) equals the
Hessian quadratic form at the corresponding point. -/
theorem fiber_path_second_deriv {d : ℕ} (f : E d → ℝ) (m v : E d)
    (t : ℝ) (hf_C2 : ContDiffAt ℝ 2 f (m + t • v)) :
    deriv (deriv (fun s => f (m + s • v))) t = hessianQuadForm f (m + t • v) v := by
  set φ : ℝ → ℝ := fun s => f (m + s • v)
  let ψ : ℝ → E d := fun s => m + s • v
  have hψ_da : ∀ s, HasDerivAt ψ v s := fun s => by
    have h := ((hasDerivAt_id s).smul_const v).const_add m
    convert h using 1
    · rfl
    · rfl
    · rfl
    · funext r
      change (fun s => m + s • v) r = m + r • v
      rfl
    · simp
  have hf_diffAt : DifferentiableAt ℝ f (ψ t) :=
    hf_C2.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  -- f is differentiable in a neighborhood of ψ(t)
  have hf_diff_ev : ∀ᶠ y in 𝓝 (ψ t), DifferentiableAt ℝ f y :=
    (hf_C2.eventually (by simp)).mono
      fun y hy => hy.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  -- Pull back along ψ: f differentiable at ψ(s) for s near t
  have hψ_smooth : ContDiff ℝ ⊤ (fun s : ℝ => (m : E d) + s • v) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hf_diffψ_ev : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ f (ψ s) :=
    hψ_smooth.continuous.continuousAt.tendsto.eventually hf_diff_ev
  set G : E d → ℝ := fun x => (fderiv ℝ f x) v with hG_def
  -- deriv φ agrees with G ∘ ψ near t
  have hderiv_ev : deriv φ =ᶠ[𝓝 t] fun s => G (ψ s) := by
    filter_upwards [hf_diffψ_ev] with s hs
    exact (hs.hasFDerivAt.comp_hasDerivAt s (hψ_da s)).deriv
  -- So second derivatives agree at t
  have hderiv2_eq : deriv (deriv φ) t = deriv (fun s => G (ψ s)) t :=
    hderiv_ev.deriv_eq
  -- fderiv ℝ f is C¹ at ψ(t), hence differentiable there
  have hfderiv_C1 : ContDiffAt ℝ 1 (fderiv ℝ f) (ψ t) :=
    hf_C2.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  have hfderiv_diff : DifferentiableAt ℝ (fderiv ℝ f) (ψ t) :=
    hfderiv_C1.differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  -- G is differentiable at ψ(t)
  have hG_diffAt : DifferentiableAt ℝ G (ψ t) :=
    hfderiv_diff.clm_apply (differentiableAt_const v)
  -- Compute deriv (G ∘ ψ) t
  have hGψ_da : HasDerivAt (G ∘ ψ) ((fderiv ℝ G (ψ t)) v) t :=
    hG_diffAt.hasFDerivAt.comp_hasDerivAt t (hψ_da t)
  have hderiv2 : deriv (fun s => G (ψ s)) t = (fderiv ℝ G (ψ t)) v :=
    hGψ_da.deriv
  -- Relate fderiv ℝ G to hessianQuadForm via eventual equality
  have hval_eq : (fderiv ℝ G (ψ t)) v = hessianQuadForm f (ψ t) v := by
    have hG_inner_ev : G =ᶠ[𝓝 (ψ t)] fun x => @inner ℝ (E d) _ (gradient f x) v := by
      simp_all
    rw [hG_inner_ev.fderiv_eq]
    have hgrad_diffAt : DifferentiableAt ℝ (gradient f) (ψ t) := by
      have hle := (InnerProductSpace.toDual ℝ (E d)).symm.toContinuousLinearEquiv.differentiable
      exact hle.differentiableAt.comp _ hfderiv_diff
    simp only [hessianQuadForm]
    rw [fderiv_inner_apply (𝕜 := ℝ) hgrad_diffAt (differentiableAt_const v)]
    simp only [fderiv_fun_const, Pi.zero_apply,
      zero_apply, inner_zero_right, zero_add]
  rw [hderiv2_eq, hderiv2, hval_eq]

/-- The fiber path φ(t) = f(m + t·v) is C² when f is C² on an open set
containing the entire line through m in direction v. -/
theorem fiber_path_contDiff2 {d : ℕ} (f : E d → ℝ) (m v : E d)
    {V : Set (E d)} (hV : IsOpen V) (hf_C2 : ContDiffOn ℝ 2 f V)
    (hseg : ∀ t : ℝ, m + t • v ∈ V) :
    ContDiff ℝ 2 (fun t : ℝ => f (m + t • v)) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  have hψ : ContDiff ℝ 2 (fun s : ℝ => m + s • v) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  exact (hf_C2.contDiffAt (hV.mem_nhds (hseg t))).comp t hψ.contDiffAt

/-- The fiber path φ(t) = f(m + t·v) is C² at every point t ∈ [0,1] when f is C²
on an open set containing the segment {m + t·v | t ∈ [0,1]}. -/
theorem fiber_path_C2at_on_segment {d : ℕ} (f : E d → ℝ) (m v : E d)
    {V : Set (E d)} (hV : IsOpen V) (hf_C2 : ContDiffOn ℝ 2 f V)
    (hseg : ∀ t : ℝ, t ∈ Set.Icc 0 1 → m + t • v ∈ V) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, ContDiffAt ℝ 2 (fun t : ℝ => f (m + t • v)) t := by
  intro t ht
  have hψ : ContDiff ℝ 2 (fun s : ℝ => m + s • v) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  exact (hf_C2.contDiffAt (hV.mem_nhds (hseg t ht))).comp t hψ.contDiffAt

end PLAcceleratedNesterovLean
