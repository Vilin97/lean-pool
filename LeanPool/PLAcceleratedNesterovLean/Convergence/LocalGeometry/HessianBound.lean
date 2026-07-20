/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.Convergence.LocalGeometry.Step1
import LeanPool.PLAcceleratedNesterovLean.MorseBott.HessianPL

/-!
# Hessian coercivity from the Polyak-Łojasiewicz condition

Proves that the Hessian of a C² function is μ-coercive on normal directions
to the minimizer set, given the μ-PL condition.

This file provides the bridge from global `PolyakLojasiewicz` to the core Hessian
bounds proved in `MorseBott.HessianPL`. The unique content here:
  1. `PL_to_local_MuPL`: converts global PL on U to local `MuPL` at a minimizer
  2. `hessianQuadForm_eq_hessian`: bridges `hessianQuadForm` to second Fréchet derivative
  3. `hessian_normal_bound_from_PL`: Hessian ≥ μ on normal directions (main export)
  4. `PL_gradient_hessian_bound`: gradient-form export
-/

noncomputable section

namespace PLAcceleratedNesterovLean

open Filter Topology Metric Submodule Asymptotics

variable {d : ℕ}

-- ════════════════════════════════════════════════════════════════════════════
-- § F. Bridge: hessianQuadForm = hessian applied twice
-- ════════════════════════════════════════════════════════════════════════════

/-- The quadratic form ⟨D(∇f)(x)ξ, ξ⟩ equals D²f(x)(ξ)(ξ) for C² functions.
    Uses the Riesz representation: gradient f = toDual⁻¹ ∘ fderiv ℝ f. -/
private lemma hessianQuadForm_eq_hessian (f : E d → ℝ) (x ξ : E d) (hf : ContDiffAt ℝ 2 f x) :
    hessianQuadForm f x ξ = hessian f x ξ ξ := by
  -- f is differentiable in a neighborhood of x
  obtain ⟨u, hu_mem, hu_C2⟩ := hf.contDiffOn le_rfl (by norm_num)
  have hf_diff_nhds : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y :=
    (hu_C2.differentiableOn two_ne_zero).eventually_differentiableAt hu_mem
  -- G(y) = (fderiv ℝ f y) ξ agrees with ⟨gradient f y, ξ⟩ near x
  set G : E d → ℝ := fun y => (fderiv ℝ f y) ξ
  have hG_eq : G =ᶠ[𝓝 x] fun y => @inner ℝ (E d) _ (gradient f y) ξ := by
    filter_upwards [hf_diff_nhds] with y hy
    exact (inner_gradient_left (𝕜 := ℝ) (f := f) (x := y) (y := ξ)).symm
  have hgrad_diff_at : DifferentiableAt ℝ (gradient f) x := by
    have hcle : Differentiable ℝ
        (InnerProductSpace.toDual ℝ (E d)).symm.toContinuousLinearEquiv :=
      (InnerProductSpace.toDual ℝ (E d)).symm.toContinuousLinearEquiv.differentiable
    have hfr : ContDiffAt ℝ 1 (fderiv ℝ f) x :=
      hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    exact hcle.differentiableAt.comp x (hfr.differentiableAt one_ne_zero)
  have hDf_diff : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right le_rfl).differentiableAt one_ne_zero
  -- (fderiv ℝ G x) ξ = hessianQuadForm f x ξ (via fderiv_inner_apply)
  have hleft : (fderiv ℝ G x) ξ = hessianQuadForm f x ξ := by
    have hfG : fderiv ℝ G x = fderiv ℝ (fun y => @inner ℝ (E d) _ (gradient f y) ξ) x :=
      hG_eq.fderiv_eq
    simp only [hfG, hessianQuadForm]
    rw [fderiv_inner_apply (𝕜 := ℝ) hgrad_diff_at (differentiableAt_const ξ)]
    simp only [fderiv_fun_const, Pi.zero_apply,
      zero_apply, inner_zero_right, zero_add]
  -- (fderiv ℝ G x) ξ = hessian f x ξ ξ (via chain rule: G = eval_ξ ∘ fderiv ℝ f)
  have hright : (fderiv ℝ G x) ξ = hessian f x ξ ξ := by
    have hcomp : HasFDerivAt G ((ContinuousLinearMap.apply ℝ ℝ ξ).comp (hessian f x)) x :=
      ((ContinuousLinearMap.apply ℝ ℝ ξ).hasFDerivAt).comp x hDf_diff.hasFDerivAt
    rw [hcomp.fderiv]
    rfl
  linarith

-- ════════════════════════════════════════════════════════════════════════════
-- § G. Convert PolyakLojasiewicz to local PL at a minimizer
-- ════════════════════════════════════════════════════════════════════════════

private lemma PL_to_local_MuPL (f : E d → ℝ) (μ : ℝ) (U : Set (E d))
    (hPL : PolyakLojasiewicz f μ U) (hU_open : IsOpen U)
    (m : E d) (hmS : m ∈ argminSet f) (hmU : m ∈ U) :
    MuPL f μ m := by
  have hfStar : fStar f = f m := by
    unfold fStar; apply le_antisymm
    · exact ciInf_le ⟨f m, fun _ ⟨y, hy⟩ => hy ▸ hmS y⟩ m
    · exact le_ciInf hmS
  have hnorm_eq : ∀ x, ‖gradient f x‖ = ‖fderiv ℝ f x‖ := fun x => by
    simp only [gradient]; exact (InnerProductSpace.toDual ℝ (E d)).symm.norm_map _
  have h2μ_pos : (0 : ℝ) < 2 * μ := by have := hPL.1; positivity
  filter_upwards [hU_open.mem_nhds hmU] with x hxU
  have hpl := hPL.2.2 x hxU; rw [hfStar, hnorm_eq] at hpl; rw [ge_iff_le] at hpl
  calc f x - f m
      = (2 * μ)⁻¹ * ((2 * μ) * (f x - f m)) := by
          rw [inv_mul_cancel_left₀ (ne_of_gt h2μ_pos)]
    _ ≤ (2 * μ)⁻¹ * ‖fderiv ℝ f x‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hpl (inv_nonneg.mpr h2μ_pos.le)

-- ════════════════════════════════════════════════════════════════════════════
-- § H. Main theorem
-- ════════════════════════════════════════════════════════════════════════════

/-- **Normal Hessian bound from PL**: For m ∈ argminSet f and ξ with Dπ(m)ξ = 0
    (normal direction), the Hessian quadratic form satisfies
    hessianQuadForm f m ξ ≥ μ · ‖ξ‖².

    The proof combines:
    1. PL → local MuPL at m
    2. hessianQuadForm = hessian (bridge via Riesz representation)
    3. ξ ∈ (hessKer f m)⊥ via self-adjointness of Dπ(m) + Morse-Bott condition
    4. Rayleigh quotient coercivity on (hessKer)⊥

    The Morse-Bott condition (hMB) states ker(D²f(m)) ⊆ range(Dπ(m)), i.e., every
    direction of zero Hessian curvature is tangent to the minimizer set. Combined with
    self-adjointness of Dπ(m) (which holds for smooth nearest-point projections), this
    gives ker(Dπ(m)) ⊆ (hessKer f m)⊥, so normal directions lie in the orthogonal
    complement of the Hessian kernel where μ-coercivity holds.
-/
theorem hessian_normal_bound_from_PL {d : ℕ}
    (f : E d → ℝ) (μ : ℝ) (U : Set (E d))
    (hPL : PolyakLojasiewicz f μ U)
    (hU_open : IsOpen U)
    (S : Set (E d)) (hS : S = argminSet f) (hS_sub : S ⊆ U)
    (_hgrad_zero : ∀ x ∈ S, gradient f x = 0)
    (π : E d → E d)
    (_hπ_proj : ∀ x ∈ U, π x ∈ S ∧ dist x (π x) = Metric.infDist x S)
    (m : E d) (hmS : m ∈ S)
    (hf_C2 : ContDiffAt ℝ 2 f m)
    (hπ_sa : ∀ u v : E d,
      @inner ℝ (E d) _ (fderiv ℝ π m u) v = @inner ℝ (E d) _ u (fderiv ℝ π m v))
    (hMB : ∀ w : E d, (fderiv ℝ (fderiv ℝ f) m).toLinearMap w = 0 →
      w ∈ LinearMap.range (fderiv ℝ π m).toLinearMap)
    (ξ : E d)
    (hξ_normal : fderiv ℝ π m ξ = 0) :
    hessianQuadForm f m ξ ≥ μ * ‖ξ‖ ^ 2 := by
  -- m is a global minimizer
  have hmin : ∀ y, f m ≤ f y := by rw [hS] at hmS; exact hmS
  have hmin_local : IsLocalMin f m := Filter.Eventually.of_forall hmin
  -- Convert PL to local form
  have hPL_local := PL_to_local_MuPL f μ U hPL hU_open m (by rwa [← hS]) (hS_sub hmS)
  -- Bridge to second Fréchet derivative
  rw [hessianQuadForm_eq_hessian f m ξ hf_C2]
  -- ξ ∈ (hessianKer f m)⊥:
  --   By hMB: hessianKer f m ⊆ range(Dπ(m)), so (range Dπ(m))⊥ ⊆ (hessianKer)⊥.
  --   By hπ_sa (self-adjointness): (range Dπ(m))⊥ = ker(Dπ(m)).
  --   And ξ ∈ ker(Dπ(m)) by hξ_normal.
  have hξ_orth : ξ ∈ (hessianKer f m).orthogonal := by
    rw [(hessianKer f m).mem_orthogonal]
    intro w hw
    obtain ⟨u, hu⟩ := LinearMap.mem_range.mp (hMB w (LinearMap.mem_ker.mp hw))
    simp only [ContinuousLinearMap.coe_coe] at hu
    rw [← hu, hπ_sa u ξ, hξ_normal, inner_zero_right]
  -- Apply Rayleigh quotient coercivity
  exact hessian_coercive_on_orthogonal_of_MuPL_impl f μ m hPL.1
    hf_C2 hmin_local hPL_local ξ hξ_orth

-- ════════════════════════════════════════════════════════════════════════════
-- § I. Export: gradient-form PL Hessian bound
-- ════════════════════════════════════════════════════════════════════════════

/-- Off-diagonal identity: ⟨D(∇f)(x) v, w⟩ = D²f(x)(v)(w) for C² functions.
    Generalizes `hessianQuadForm_eq_hessian` beyond the diagonal case. -/
private lemma gradient_hessian_inner (f : E d → ℝ) (x v w : E d) (hf : ContDiffAt ℝ 2 f x) :
    @inner ℝ (E d) _ (fderiv ℝ (gradient f) x v) w = hessian f x v w := by
  -- f is differentiable in a neighborhood of x
  obtain ⟨u, hu_mem, hu_C2⟩ := hf.contDiffOn le_rfl (by norm_num)
  have hf_diff_nhds : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y :=
    (hu_C2.differentiableOn two_ne_zero).eventually_differentiableAt hu_mem
  set Gw : E d → ℝ := fun y => (fderiv ℝ f y) w
  have hGw_eq : Gw =ᶠ[𝓝 x] fun y => @inner ℝ (E d) _ (gradient f y) w := by
    filter_upwards [hf_diff_nhds] with y hy
    exact (inner_gradient_left (𝕜 := ℝ) (f := f) (x := y) (y := w)).symm
  have hgrad_diff_at : DifferentiableAt ℝ (gradient f) x := by
    have hcle : Differentiable ℝ
        (InnerProductSpace.toDual ℝ (E d)).symm.toContinuousLinearEquiv :=
      (InnerProductSpace.toDual ℝ (E d)).symm.toContinuousLinearEquiv.differentiable
    have hfr : ContDiffAt ℝ 1 (fderiv ℝ f) x :=
      hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    exact hcle.differentiableAt.comp x (hfr.differentiableAt one_ne_zero)
  have hDf_diff : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right le_rfl).differentiableAt one_ne_zero
  have hleft : (fderiv ℝ Gw x) v = @inner ℝ (E d) _ (fderiv ℝ (gradient f) x v) w := by
    have hfGw : fderiv ℝ Gw x = fderiv ℝ (fun y => @inner ℝ (E d) _ (gradient f y) w) x :=
      hGw_eq.fderiv_eq
    simp only [hfGw]
    rw [fderiv_inner_apply (𝕜 := ℝ) hgrad_diff_at (differentiableAt_const w)]
    simp only [fderiv_fun_const, Pi.zero_apply,
      zero_apply, inner_zero_right, zero_add]
  have hright : (fderiv ℝ Gw x) v = hessian f x v w := by
    have hcomp : HasFDerivAt Gw ((ContinuousLinearMap.apply ℝ ℝ w).comp (hessian f x)) x :=
      ((ContinuousLinearMap.apply ℝ ℝ w).hasFDerivAt).comp x hDf_diff.hasFDerivAt
    rw [hcomp.fderiv]
    rfl
  linarith

/-- Under PL on U at a minimizer m, μ⟨D(∇f)(m) v, v⟩ ≤ ‖D(∇f)(m) v‖² for all v.
    Gradient-form export of the core PL Hessian bound. -/
theorem PL_gradient_hessian_bound (f : E d → ℝ) (μ : ℝ) (U : Set (E d))
    (hPL : PolyakLojasiewicz f μ U) (hU_open : IsOpen U)
    (m : E d) (hf : ContDiffAt ℝ 2 f m) (hmS : m ∈ argminSet f) (hmU : m ∈ U) (v : E d) :
    μ * @inner ℝ (E d) _ (fderiv ℝ (gradient f) m v) v ≤
    ‖fderiv ℝ (gradient f) m v‖ ^ 2 := by
  have hPL_local := PL_to_local_MuPL f μ U hPL hU_open m hmS hmU
  have hmin_local : IsLocalMin f m := Filter.Eventually.of_forall hmS
  have hbound := muPL_norm_sq_bound f μ m v hPL.1
    hf hmin_local hPL_local
  have h_inner : @inner ℝ (E d) _ (fderiv ℝ (gradient f) m v) v = hessian f m v v :=
    gradient_hessian_inner f m v v hf
  have h_toDual_eq : (InnerProductSpace.toDual ℝ (E d)) (fderiv ℝ (gradient f) m v) =
      hessian f m v := by
    ext w
    rw [InnerProductSpace.toDual_apply_apply]
    exact gradient_hessian_inner f m v w hf
  have h_norm : ‖fderiv ℝ (gradient f) m v‖ = ‖hessian f m v‖ := by
    have h := (InnerProductSpace.toDual ℝ (E d)).norm_map (fderiv ℝ (gradient f) m v)
    simp_all
  simp_all

end PLAcceleratedNesterovLean
