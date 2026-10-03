/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# Invariance of the Laplacian and radial Laplacians (ported from TauCeti)

For a finite-dimensional real inner product space `E` and any `f : E → F`:

* `laplacian_comp_linearIsometryEquiv_right`: `Δ (f ∘ l) = (Δ f) ∘ l` for a linear isometry
  equivalence `l`;
* `laplacian_comp_add_right`: `Δ (fun y ↦ f (y + a)) = fun y ↦ Δ f (y + a)`;
* `ContDiff.laplacian_comp_norm_sq`: for `ρ : ℝ → ℝ` of class `C²`,
  `Δ (fun y ↦ ρ (‖y‖²)) x = 4 ‖x‖² ρ'' (‖x‖²) + 2 (dim E) ρ' (‖x‖²)`;
* `tsupport_laplacian_subset`: `tsupport (Δ f) ⊆ tsupport f`.

The invariance statements need no differentiability hypothesis on `f`.

## Provenance

Pool port: imports relocated under `LeanPool.ViscositySolutionTheory`; original
mathematical namespaces and copyright retained; checked with Lean/Mathlib v4.34.0.


* Upstream: TauCeti, https://github.com/TauCetiProject/TauCeti
* Path: `TauCeti/Analysis/InnerProductSpace/Laplacian/Basic.lean`
* Commit: 91f66a0514e6523efdccddb9e35fb82c96dd6405 (2026-09-24)
* License: Apache-2.0. Upstream `NOTICE`: none.
* Upstream notice: `Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.`;
  upstream authors: The Tau Ceti contributors.
* Extent: `iteratedFDeriv_comp_linearIsometryEquiv_apply`,
  `laplacian_comp_linearIsometryEquiv_right`, `laplacian_comp_add_right`,
  `ContDiff.laplacian_comp_norm_sq`, `tsupport_laplacian_subset` (verbatim up to namespace).
* Changes: ported from Lean v4.34.0-rc2 to Lean/Mathlib v4.30.0; `module`/`public import`
  removed; namespace `TauCeti` → `ViscositySolns.Analysis`; the affine-isometry, homothety and
  `laplacian_norm_sq` statements are not ported (not needed here).
-/

@[expose] public section

open InnerProductSpace
open scoped Laplacian

namespace ViscositySolns

namespace Analysis

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- The iterated derivative transforms under a linear isometry equivalence on the right by
pulling the directions through the isometry. -/
theorem iteratedFDeriv_comp_linearIsometryEquiv_apply (l : E ≃ₗᵢ[ℝ] E') (f : E' → F)
    (i : ℕ) (x : E) (m : Fin i → E) :
    iteratedFDeriv ℝ i (f ∘ l) x m = iteratedFDeriv ℝ i f (l x) (fun j ↦ l (m j)) := by
  have h := l.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ
    (x := x) (Set.mem_univ _) i
  rw [Set.preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at h
  rw [← LinearIsometryEquiv.coe_toContinuousLinearEquiv l]
  rw [h, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rfl

/-- **Invariance of the Laplacian under isometries.** `Δ (f ∘ l) = (Δ f) ∘ l` for a linear
isometry equivalence `l`. No differentiability hypothesis is needed. -/
theorem laplacian_comp_linearIsometryEquiv_right (l : E ≃ₗᵢ[ℝ] E') (f : E' → F) :
    Δ (f ∘ l) = (Δ f) ∘ l := by
  ext x
  simp only [Function.comp_apply,
    laplacian_eq_iteratedFDeriv_orthonormalBasis (f ∘ l) (stdOrthonormalBasis ℝ E),
    laplacian_eq_iteratedFDeriv_orthonormalBasis f ((stdOrthonormalBasis ℝ E).map l)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [iteratedFDeriv_comp_linearIsometryEquiv_apply l f 2 x]
  congr 1
  funext j
  fin_cases j <;> simp [OrthonormalBasis.map_apply]

/-- **Translation invariance of the Laplacian.** No differentiability hypothesis is needed. -/
theorem laplacian_comp_add_right (f : E → F) (a : E) :
    Δ (fun y ↦ f (y + a)) = fun y ↦ (Δ f) (y + a) := by
  ext x
  simp only [laplacian_eq_iteratedFDeriv_orthonormalBasis _ (stdOrthonormalBasis ℝ E)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [iteratedFDeriv_comp_add_right']

/-- **The Laplacian of a radial function.** For a `C²` function `ρ : ℝ → ℝ`, the Laplacian of
`x ↦ ρ (‖x‖ ^ 2)` is `4 ‖x‖² ρ'' (‖x‖²) + 2 (dim E) ρ' (‖x‖²)`. -/
theorem _root_.ContDiff.laplacian_comp_norm_sq {ρ : ℝ → ℝ} (hρ : ContDiff ℝ 2 ρ) (x : E) :
    Δ (fun y : E => ρ (‖y‖ ^ 2)) x =
      4 * ‖x‖ ^ 2 * deriv (deriv ρ) (‖x‖ ^ 2) +
        2 * (Module.finrank ℝ E : ℝ) * deriv ρ (‖x‖ ^ 2) := by
  have hρ1 : ContDiff ℝ 1 (deriv ρ) := hρ.deriv'
  have hρd : Differentiable ℝ ρ := hρ.differentiable (by norm_num)
  have hρ'd : Differentiable ℝ (deriv ρ) := hρ1.differentiable one_ne_zero
  -- The first derivative, by the chain rule through the squared norm.
  have hfst : fderiv ℝ (fun y : E => ρ (‖y‖ ^ 2)) =
      fun y => deriv ρ (‖y‖ ^ 2) • (2 • innerSL ℝ y) := by
    funext y
    exact ((hρd _).hasDerivAt.comp_hasFDerivAt y
      (hasStrictFDerivAt_norm_sq y).hasFDerivAt).fderiv
  -- The second derivative, by the product rule for `c • f` with `c = ρ' ∘ ‖·‖²`.
  have hc : DifferentiableAt ℝ (fun y : E => deriv ρ (‖y‖ ^ 2)) x :=
    ((hρ'd _).hasDerivAt.comp_hasFDerivAt x (hasStrictFDerivAt_norm_sq x).hasFDerivAt)
      |>.differentiableAt
  have hcd : fderiv ℝ (fun y : E => deriv ρ (‖y‖ ^ 2)) x =
      deriv (deriv ρ) (‖x‖ ^ 2) • (2 • innerSL ℝ x) :=
    ((hρ'd _).hasDerivAt.comp_hasFDerivAt x (hasStrictFDerivAt_norm_sq x).hasFDerivAt).fderiv
  have hi : DifferentiableAt ℝ (fun y : E => (2 • innerSL ℝ y : E →L[ℝ] ℝ)) x :=
    (2 • innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).differentiableAt
  have hid : fderiv ℝ (fun y : E => (2 • innerSL ℝ y : E →L[ℝ] ℝ)) x =
      (2 • innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) :=
    (2 • innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).fderiv
  set b := stdOrthonormalBasis ℝ E
  rw [congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis (fun y : E => ρ (‖y‖ ^ 2)) b) x]
  have hterm : ∀ i, iteratedFDeriv ℝ 2 (fun y : E => ρ (‖y‖ ^ 2)) x ![b i, b i] =
      4 * deriv (deriv ρ) (‖x‖ ^ 2) * ⟪x, b i⟫_ℝ ^ 2 + 2 * deriv ρ (‖x‖ ^ 2) := by
    intro i
    rw [iteratedFDeriv_two_apply, hfst, fderiv_fun_smul hc hi, hcd, hid]
    have hself : (innerSL ℝ (b i)) (b i) = (1 : ℝ) := by
      rw [innerSL_apply_apply, real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one, one_pow]
    simp [hself]
    ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib, ← Finset.mul_sum,
    b.sum_sq_inner_left x]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

open Topology in
/-- The Laplacian vanishes wherever the function vanishes identically: `Δ` is local. -/
theorem tsupport_laplacian_subset (f : E → F) : tsupport (Δ f) ⊆ tsupport f := by
  refine closure_minimal (fun x hx => ?_) (isClosed_tsupport f)
  by_contra hxf
  have h0 : Δ f =ᶠ[𝓝 x] Δ (fun _ : E => (0 : F)) :=
    laplacian_congr_nhds (notMem_tsupport_iff_eventuallyEq.mp hxf)
  exact hx (by simpa using h0.eq_of_nhds)

end Analysis

end ViscositySolns
