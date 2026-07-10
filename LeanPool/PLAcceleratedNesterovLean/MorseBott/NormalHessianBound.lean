/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.MorseBott.HessianPL
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# External Theorem 3: PL ⟹ Normal Hessian Lower Bound

## Statement

For all m ∈ argminSet f and all ξ ∈ ker(Hess f(m))⊥:
  D²f(m)(ξ,ξ) ≥ μ · ‖ξ‖²

This bridges the PLMB proof (HessianPL.lean) to the PLAcceleratedNesterovLean formulation.

## Two formulations

1. **Our formulation** (using `hessian`): `hessian f m ξ ξ ≥ μ * ‖ξ‖²`
   where `hessian f x = fderiv ℝ (fderiv ℝ f) x` (second Fréchet derivative).

2. **PLAcceleratedNesterovLean formulation** (using `hessianQuadForm`): `⟨D(∇f)(m)·ξ, ξ⟩ ≥ μ * ‖ξ‖²`
   where `gradient f x = (toDual ℝ E).symm (fderiv ℝ f x)` (Riesz representative).

These are equal for C² functions because:
  fderiv ℝ f = toDual ℝ E ∘ gradient f (Riesz representation)
  ⟹ hessian f x ξ ξ = ⟨fderiv ℝ (gradient f) x ξ, ξ⟩ (chain rule + toDual_symm_apply)

## References

- Rebjock & Boumal, Corollary 2.17
- PLMB/HessianPL.lean: `hessian_coercive_on_orthogonal_of_MuPL_impl`
-/

open Filter Topology Metric Submodule InnerProductSpace


noncomputable section

namespace PLAcceleratedNesterovLean

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- ════════════════════════════════════════════════════════════════════════════
-- § 1. PLAcceleratedNesterovLean-compatible definitions
-- ════════════════════════════════════════════════════════════════════════════

/-- The set of global minimizers of `f`. (PLAcceleratedNesterovLean: `argminSet`) -/
def ExternalThm3.argminSet (f : E → ℝ) : Set E := {x | ∀ y, f x ≤ f y}

/-- The global infimum of `f`. (PLAcceleratedNesterovLean: `fStar`) -/
def ExternalThm3.fStar (f : E → ℝ) : ℝ := ⨅ x, f x

/-- The Polyak–Łojasiewicz condition on a set `U`.
    Uses `‖fderiv ℝ f x‖` which equals `‖gradient f x‖` by Riesz representation.
    (PLAcceleratedNesterovLean: `PolyakLojasiewicz`) -/
def ExternalThm3.PolyakLojasiewicz (f : E → ℝ) (μ : ℝ) (U : Set E) : Prop :=
  0 < μ ∧ ∀ x ∈ U, ‖fderiv ℝ f x‖ ^ 2 ≥ 2 * μ * (f x - ExternalThm3.fStar f)

/-- The gradient of `f` at `x`, as the Riesz representative of `fderiv ℝ f x`.
    Matches Mathlib's `gradient` from `Analysis.Calculus.Gradient.Basic`. -/
def ExternalThm3.gradient (f : E → ℝ) (x : E) : E :=
  (toDual ℝ E).symm (fderiv ℝ f x)

/-- PLAcceleratedNesterovLean's Hessian quadratic form: `⟨D(∇f)(x)·ξ, ξ⟩`.
    Here `gradient f` is the Riesz representative of `fderiv ℝ f`. -/
def ExternalThm3.hessianQuadForm (f : E → ℝ) (x ξ : E) : ℝ :=
  @inner ℝ E _ (fderiv ℝ (ExternalThm3.gradient f) x ξ) ξ

-- ════════════════════════════════════════════════════════════════════════════
-- § 2. Bridge lemmas (fully proved)
-- ════════════════════════════════════════════════════════════════════════════

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Global minimizers are local minimizers. -/
lemma ExternalThm3.argminSet_isLocalMin (f : E → ℝ) (m : E)
    (hm : m ∈ ExternalThm3.argminSet f) :
    IsLocalMin f m :=
  Filter.Eventually.of_forall hm

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- At a global minimizer, `f(m) = f⋆`. -/
lemma ExternalThm3.fStar_eq_of_argmin (f : E → ℝ) (m : E)
    (hm : m ∈ ExternalThm3.argminSet f) :
    ExternalThm3.fStar f = f m := by
  apply le_antisymm
  · exact ciInf_le ⟨f m, by rintro _ ⟨y, rfl⟩; exact hm y⟩ m
  · exact le_ciInf hm

omit [FiniteDimensional ℝ E] in
/-- PLAcceleratedNesterovLean PL → our MuPL at global minimizers.
    Converts `‖Df(x)‖² ≥ 2μ(f(x) - f⋆)` to `f(x) - f(m) ≤ (2μ)⁻¹‖Df(x)‖²`. -/
lemma ExternalThm3.pl_to_muPL (f : E → ℝ) (μ : ℝ) (U : Set E) (m : E)
    (hm : m ∈ ExternalThm3.argminSet f)
    (hU : U ∈ 𝓝 m)
    (hPL : ExternalThm3.PolyakLojasiewicz f μ U) :
    MuPL f μ m := by
  obtain ⟨hμ, hPL_body⟩ := hPL
  have hfm : ExternalThm3.fStar f = f m := ExternalThm3.fStar_eq_of_argmin f m hm
  filter_upwards [hU] with x hxU
  have h := hPL_body x hxU
  rw [hfm] at h
  -- h : ‖fderiv ℝ f x‖ ^ 2 ≥ 2 * μ * (f x - f m)
  -- Goal: f x - f m ≤ (2 * μ)⁻¹ * ‖fderiv ℝ f x‖ ^ 2
  calc f x - f m
      = (2 * μ)⁻¹ * (2 * μ * (f x - f m)) := by field_simp
    _ ≤ (2 * μ)⁻¹ * ‖fderiv ℝ f x‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)

-- ════════════════════════════════════════════════════════════════════════════
-- § 3. Hessian quadratic form bridge
-- ════════════════════════════════════════════════════════════════════════════

/-- For C² functions, `⟨D(∇f)(x)ξ, ξ⟩ = D²f(x)(ξ,ξ)`.

    **Proof idea**: For every z, `⟨∇f(z), v⟩ = Df(z)·v` (Riesz representation,
    `inner_gradient_left`). Fixing v = ξ and differentiating both sides at x
    in direction ξ gives LHS = RHS. The chain rule steps use:
    - `innerSL ℝ ξ : E →L[ℝ] ℝ` (genuine CLM, no star) composed with `gradient f`
    - Evaluation at ξ composed with `fderiv ℝ f`
    Both are standard CLM chain rules. -/
lemma ExternalThm3.hessianQuadForm_eq_hessian (f : E → ℝ) (x ξ : E)
    (hf : ContDiffAt ℝ 2 f x) :
    ExternalThm3.hessianQuadForm f x ξ = hessian f x ξ ξ := by
  simp only [ExternalThm3.hessianQuadForm]
  -- Goal: ⟨fderiv ℝ (gradient f) x ξ, ξ⟩ = (fderiv ℝ (fderiv ℝ f) x ξ) ξ
  --
  -- The two real-valued functions φ, ψ : E → ℝ defined by
  --   φ(z) = ⟨gradient f z, ξ⟩ = ⟨ξ, gradient f z⟩    [by real_inner_comm]
  --   ψ(z) = (fderiv ℝ f z) ξ
  -- are equal by inner_gradient_left. So their fderivs at x, applied to ξ, agree.
  --
  -- Step 1: φ = ψ (pointwise)
  have h_eq : ∀ z, @inner ℝ E _ (ExternalThm3.gradient f z) ξ = (fderiv ℝ f z) ξ := by
    intro z
    simp only [ExternalThm3.gradient, toDual_symm_apply]
  -- Step 2: Since φ = ψ everywhere, fderiv φ x = fderiv ψ x
  have h_fderiv_eq : fderiv ℝ (fun z => @inner ℝ E _ (ExternalThm3.gradient f z) ξ) x =
      fderiv ℝ (fun z => (fderiv ℝ f z) ξ) x := by
    simp_all
  -- Step 3: Evaluate the RHS (fderiv of ψ)
  -- ψ(z) = (fderiv ℝ f z) ξ, its derivative at x is (hessian f x ·) ξ
  -- i.e., fderiv ℝ ψ x w = (hessian f x w) ξ
  --
  -- Step 4: Evaluate the LHS (fderiv of φ)
  -- φ(z) = ⟨ξ, gradient f z⟩ = (innerSL ℝ ξ) (gradient f z)
  -- Its derivative at x is (innerSL ℝ ξ).comp (fderiv ℝ (gradient f) x)
  -- i.e., fderiv ℝ φ x w = ⟨ξ, fderiv ℝ (gradient f) x w⟩
  --
  -- Step 5: From h_fderiv_eq with w = ξ:
  -- ⟨ξ, fderiv ℝ (gradient f) x ξ⟩ = (hessian f x ξ) ξ
  -- Using real_inner_comm: ⟨fderiv ℝ (gradient f) x ξ, ξ⟩ = (hessian f x ξ) ξ  ✓
  --
  -- The formal proof uses HasFDerivAt.clm_apply for ψ and fderiv_comp for φ.
  -- We extract the evaluated identity from h_fderiv_eq.
  -- Differentiability conditions
  have hf_diff : DifferentiableAt ℝ f x := hf.differentiableAt two_ne_zero
  have hfderiv_diff : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right le_rfl).differentiableAt one_ne_zero
  have hgrad_diff : DifferentiableAt ℝ (ExternalThm3.gradient f) x := by
    unfold ExternalThm3.gradient
    exact ((toDual ℝ E).symm.toContinuousLinearEquiv.differentiableAt).comp x
      hfderiv_diff
  -- For ψ: HasFDerivAt for z ↦ (fderiv ℝ f z) ξ
  have hψ_fderiv : HasFDerivAt (fun z => (fderiv ℝ f z) ξ)
      ((ContinuousLinearMap.apply ℝ ℝ ξ).comp (hessian f x)) x := by
    exact HasFDerivAt.comp x
      (ContinuousLinearMap.apply ℝ ℝ ξ).hasFDerivAt
      hfderiv_diff.hasFDerivAt
  -- For φ: HasFDerivAt for z ↦ ⟨ξ, gradient f z⟩
  have hφ_fderiv : HasFDerivAt (fun z => @inner ℝ E _ ξ (ExternalThm3.gradient f z))
      ((innerSL ℝ ξ).comp (fderiv ℝ (ExternalThm3.gradient f) x)) x := by
    exact HasFDerivAt.comp x
      (innerSL ℝ ξ).hasFDerivAt
      hgrad_diff.hasFDerivAt
  -- Rewrite φ using real_inner_comm
  have hφ_comm : (fun z => @inner ℝ E _ (ExternalThm3.gradient f z) ξ) =
      (fun z => @inner ℝ E _ ξ (ExternalThm3.gradient f z)) := by
    ext z; exact real_inner_comm _ _
  -- Combine: fderiv φ x ξ = fderiv ψ x ξ
  have h_LHS : fderiv ℝ (fun z => @inner ℝ E _ (ExternalThm3.gradient f z) ξ) x ξ =
      @inner ℝ E _ ξ (fderiv ℝ (ExternalThm3.gradient f) x ξ) := by
    rw [hφ_comm]
    rw [hφ_fderiv.fderiv]
    simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply]
  have h_RHS : fderiv ℝ (fun z => (fderiv ℝ f z) ξ) x ξ = (hessian f x ξ) ξ := by
    rw [hψ_fderiv.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  -- From h_fderiv_eq: LHS evaluated at ξ = RHS evaluated at ξ
  have h_combined := congr_fun (congr_arg DFunLike.coe h_fderiv_eq) ξ
  rw [h_LHS, h_RHS] at h_combined
  -- h_combined : ⟨ξ, fderiv ℝ (ExternalThm3.gradient f) x ξ⟩ = (hessian f x ξ) ξ
  rw [real_inner_comm] at h_combined
  exact h_combined

-- ════════════════════════════════════════════════════════════════════════════
-- § 4. Core theorem using our definitions (fully proved)
-- ════════════════════════════════════════════════════════════════════════════

/-- **Core theorem**: At a global minimizer under PL, the Hessian is μ-coercive
    on ker(Hess)⊥. Uses `hessian f m ξ ξ` (second Fréchet derivative). -/
theorem ExternalThm3.hessian_coercive_globalMin_PL
    (f : E → ℝ) (μ : ℝ) (U : Set E) (m ξ : E)
    (hf : ContDiffAt ℝ 2 f m)
    (hPL : ExternalThm3.PolyakLojasiewicz f μ U)
    (hm : m ∈ ExternalThm3.argminSet f)
    (hU : U ∈ 𝓝 m)
    (hξ : ξ ∈ (hessianKer f m).orthogonal) :
    hessian f m ξ ξ ≥ μ * ‖ξ‖ ^ 2 :=
  hessian_coercive_on_orthogonal_of_MuPL_impl f μ m hPL.1 hf
    (ExternalThm3.argminSet_isLocalMin f m hm)
    (ExternalThm3.pl_to_muPL f μ U m hm hU hPL) ξ hξ

-- ════════════════════════════════════════════════════════════════════════════
-- § 5. External Theorem 3 (in PLAcceleratedNesterovLean's hessianQuadForm language)
-- ════════════════════════════════════════════════════════════════════════════

/-- **External Theorem 3**: PL ⟹ Normal Hessian Lower Bound (PLAcceleratedNesterovLean language).

    For C² functions satisfying the Polyak–Łojasiewicz condition with constant μ
    on an open set U, at any global minimizer m, and for any ξ in the orthogonal
    complement of ker(Hess f(m)):

      ⟨D(∇f)(m)·ξ, ξ⟩ ≥ μ · ‖ξ‖²

    This is the PLAcceleratedNesterovLean `hessianQuadForm` version of the
    Hessian coercivity bound.

    **Note on the projection condition**: PLAcceleratedNesterovLean uses
    `fderiv ℝ π m ξ = 0` (where π is the nearest-point projection onto the
    minimizer set) to characterize normal vectors.
    Under the Morse-Bott property (proved in Theorem.lean), the minimizer set is a C¹
    submanifold with tangent space T = ker(Hess f(m)), and the normal space T⊥ equals
    ker(fderiv ℝ π m). So `fderiv ℝ π m ξ = 0 → ξ ∈ (hessianKer f m).orthogonal`. -/
theorem ExternalThm3.hessianQuadForm_bound
    (f : E → ℝ) (μ : ℝ) (U : Set E) (m ξ : E)
    (hf : ContDiffAt ℝ 2 f m)
    (hPL : ExternalThm3.PolyakLojasiewicz f μ U)
    (hm : m ∈ ExternalThm3.argminSet f)
    (hU : U ∈ 𝓝 m)
    (hξ : ξ ∈ (hessianKer f m).orthogonal) :
    ExternalThm3.hessianQuadForm f m ξ ≥ μ * ‖ξ‖ ^ 2 := by
  rw [ExternalThm3.hessianQuadForm_eq_hessian f m ξ hf]
  exact ExternalThm3.hessian_coercive_globalMin_PL f μ U m ξ hf hPL hm hU hξ

-- ════════════════════════════════════════════════════════════════════════════
-- § 6. Convenience corollary: quantified version
-- ════════════════════════════════════════════════════════════════════════════

/-- Quantified version: ∀ m ∈ argminSet f, ∀ ξ ∈ ker(Hess)⊥, bound holds. -/
theorem ExternalThm3.hessianQuadForm_bound_forall
    (f : E → ℝ) (μ : ℝ) (U : Set E)
    (hf : ContDiff ℝ 2 f)
    (hPL : ExternalThm3.PolyakLojasiewicz f μ U)
    (hU_open : IsOpen U)
    (hS_sub : ExternalThm3.argminSet f ⊆ U) :
    ∀ m ∈ ExternalThm3.argminSet f, ∀ ξ : E,
      ξ ∈ (hessianKer f m).orthogonal →
      ExternalThm3.hessianQuadForm f m ξ ≥ μ * ‖ξ‖ ^ 2 := by
  intro m hm ξ hξ
  exact ExternalThm3.hessianQuadForm_bound f μ U m ξ hf.contDiffAt hPL hm
    (hU_open.mem_nhds (hS_sub hm)) hξ

end PLAcceleratedNesterovLean
