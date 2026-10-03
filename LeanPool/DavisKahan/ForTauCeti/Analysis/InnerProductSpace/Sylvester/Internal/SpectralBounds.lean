/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Spectral.Subspace
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Sylvester.Bound

/-!
# Internal finite-dimensional spectral bounds for Sylvester estimates

Eigenvalue-to-quadratic-form conversions and centered spectral bounds shared by
the interval and arbitrary-distance Sylvester arguments. These declarations are
implementation support rather than part of the public theorem surface.

## Sources

*Follows nothing in particular*: internal bounds extracted from the Sylvester estimate's
proof, kept separate so the main file states only the estimate.

## Provenance

*Moved, not restated.*  This file was
`DavisKahan/FiniteDimensional/Sylvester/Internal/SpectralBounds.lean`
before the whole remaining sin-Θ closure moved into
the staging layer.  Statements, proofs, signatures and namespaces are unchanged;
the declarations already lived in `TauCeti.*`, so the move was a path change and
an import repoint.

Y3(b2) and Y3(b3) are what made it possible: before them this file's import
closure crossed `ForMathlib`, which the `ForTauCeti` layer rule forbids.

-/

@[expose] public section

namespace TauCeti

open TauCeti

open scoped InnerProductSpace BigOperators

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Every eigenvalue is a point of the restricted spectrum on the whole space, witnessed by its own
eigenvector. -/
theorem eigenvalue_mem_restrictedPointSpectrum_top
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric)
    (i : Fin (Module.finrank 𝕜 E)) :
    hT.eigenvalues rfl i ∈ restrictedPointSpectrum T ⊤ :=
  mem_restrictedPointSpectrum Submodule.mem_top
    ((hT.eigenvectorBasis rfl).orthonormal.ne_zero i)
    (hT.apply_eigenvectorBasis rfl i)

/-- An upper bound on all eigenvalues gives an upper bound on the quadratic form, via the
eigenbasis expansion. -/
theorem re_inner_le_of_eigenvalues_le
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {c : ℝ}
    (hc : ∀ i : Fin (Module.finrank 𝕜 E), hT.eigenvalues rfl i ≤ c)
    (x : E) : RCLike.re ⟪T x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 := by
  rw [LinearMap.IsSymmetric.re_inner_apply_self_eq_sum_eigenvalues_mul_sq hT rfl x]
  calc
    (∑ i : Fin (Module.finrank 𝕜 E),
        hT.eigenvalues rfl i * ‖(hT.eigenvectorBasis rfl).repr x i‖ ^ 2)
        ≤ ∑ i : Fin (Module.finrank 𝕜 E),
            c * ‖(hT.eigenvectorBasis rfl).repr x i‖ ^ 2 := by
          exact Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_right (hc i) (sq_nonneg _)
    _ = c * ‖x‖ ^ 2 := by
          rw [← Finset.mul_sum]
          congr 1
          simp_rw [OrthonormalBasis.repr_apply_apply]
          exact (hT.eigenvectorBasis rfl).sum_sq_norm_inner_right x

/-- The lower-bound counterpart of `re_inner_le_of_eigenvalues_le`. -/
theorem le_re_inner_of_le_eigenvalues
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {c : ℝ}
    (hc : ∀ i : Fin (Module.finrank 𝕜 E), c ≤ hT.eigenvalues rfl i)
    (x : E) : c * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜 := by
  rw [LinearMap.IsSymmetric.re_inner_apply_self_eq_sum_eigenvalues_mul_sq hT rfl x]
  calc
    c * ‖x‖ ^ 2 = ∑ i : Fin (Module.finrank 𝕜 E),
        c * ‖(hT.eigenvectorBasis rfl).repr x i‖ ^ 2 := by
          rw [← Finset.mul_sum]
          congr 1
          simp_rw [OrthonormalBasis.repr_apply_apply]
          exact (hT.eigenvectorBasis rfl).sum_sq_norm_inner_right x |>.symm
    _ ≤ ∑ i : Fin (Module.finrank 𝕜 E),
        hT.eigenvalues rfl i * ‖(hT.eigenvectorBasis rfl).repr x i‖ ^ 2 := by
          exact Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_right (hc i) (sq_nonneg _)

/-- **Spectrum in `[a, b]` bounds the shifted operator norm by the half-width.**  Centring at the
midpoint is what turns a two-sided spectral bound into a single norm bound. -/
theorem opNorm_shift_le_of_pointSpectrumIn_Icc
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {a b : ℝ} (hab : a ≤ b)
    (hsp : PointSpectrumIn T ⊤ (Set.Icc a b)) :
    ‖(T - (((a + b) / 2 : ℝ) : 𝕜) • LinearMap.id).toContinuousLinearMap‖ ≤
      (b - a) / 2 := by
  let m : ℝ := (a + b) / 2
  let r : ℝ := (b - a) / 2
  let S : E →ₗ[𝕜] E := T - (m : 𝕜) • LinearMap.id
  have hS : S.IsSymmetric := hT.sub fun x y => by
    simp only [LinearMap.smul_apply, LinearMap.id_apply, inner_smul_left,
      inner_smul_right, RCLike.conj_ofReal]
  have ha : ∀ x, a * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜 :=
    le_re_inner_of_le_eigenvalues hT fun i =>
      (hsp (eigenvalue_mem_restrictedPointSpectrum_top hT i)).1
  have hb : ∀ x, RCLike.re ⟪T x, x⟫_𝕜 ≤ b * ‖x‖ ^ 2 :=
    re_inner_le_of_eigenvalues_le hT fun i =>
      (hsp (eigenvalue_mem_restrictedPointSpectrum_top hT i)).2
  have hr : 0 ≤ r := by simp only [r]; linarith
  have hform : ∀ x, |RCLike.re ⟪S x, x⟫_𝕜| ≤ r * ‖x‖ ^ 2 := by
    intro x
    have hval : RCLike.re ⟪S x, x⟫_𝕜 =
        RCLike.re ⟪T x, x⟫_𝕜 - m * ‖x‖ ^ 2 := by
      simp only [S, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        inner_sub_left, inner_smul_left, RCLike.conj_ofReal, map_sub,
        RCLike.re_ofReal_mul, inner_self_eq_norm_sq]
    rw [hval, abs_le]
    constructor <;> simp only [m, r] <;> nlinarith [ha x, hb x]
  -- names the application so the norm bound applies to it directly.
  change ‖S.toContinuousLinearMap‖ ≤ r
  exact ContinuousLinearMap.norm_le_of_abs_re_inner_map_self_le
    (fun x y => hS x y) hr hform

/-- The converse shape: spectrum avoiding a `δ`-enlarged interval bounds the shifted operator
*below*.  This is the separation hypothesis in the form the Sylvester estimates consume. -/
theorem norm_shift_lower_of_spectrumOutside
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) {a b δ : ℝ}
    (hab : a ≤ b) (hδ : 0 < δ)
    (hsp : PointSpectrumIn T ⊤ {lam | lam ∉ Set.Ioo (a - δ) (b + δ)}) :
    ∀ x : E, ((b - a) / 2 + δ) * ‖x‖ ≤
      ‖(T - (((a + b) / 2 : ℝ) : 𝕜) •
          (LinearMap.id : E →ₗ[𝕜] E)) x‖ := by
  let m : ℝ := (a + b) / 2
  let r : ℝ := (b - a) / 2
  let S : E →ₗ[𝕜] E := T - (m : 𝕜) • LinearMap.id
  have hS : S.IsSymmetric := hT.sub fun x y => by
    simp only [LinearMap.smul_apply, LinearMap.id_apply, inner_smul_left,
      inner_smul_right, RCLike.conj_ofReal]
  have hr : 0 ≤ r := by simp only [r]; linarith
  have hk : 0 ≤ r + δ := by linarith
  have hsep : ∀ i : Fin (Module.finrank 𝕜 E),
      r + δ ≤ |hT.eigenvalues rfl i - m| := by
    intro i
    have hi := hsp (eigenvalue_mem_restrictedPointSpectrum_top hT i)
    simp only [Set.mem_ofPred_eq, Set.mem_Ioo, not_and_or, not_lt] at hi
    rcases hi with hi | hi
    · rw [abs_of_nonpos]
      · simp only [m, r]
        linarith
      · simp only [m]
        linarith
    · rw [abs_of_nonneg]
      · simp only [m, r]
        linarith
      · simp only [m]
        linarith
  intro x
  have hsq : (r + δ) ^ 2 * ‖x‖ ^ 2 ≤ ‖S x‖ ^ 2 := by
    rw [← (hT.eigenvectorBasis rfl).sum_sq_norm_inner_right (S x),
      ← (hT.eigenvectorBasis rfl).sum_sq_norm_inner_right x, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hinner :
        ⟪hT.eigenvectorBasis rfl i, S x⟫_𝕜 =
          (((hT.eigenvalues rfl i - m : ℝ) : 𝕜) *
            ⟪hT.eigenvectorBasis rfl i, x⟫_𝕜) := by
      rw [← hS (hT.eigenvectorBasis rfl i) x]
      simp only [S, LinearMap.sub_apply, hT.apply_eigenvectorBasis,
        LinearMap.smul_apply, LinearMap.id_apply, inner_sub_left,
        inner_smul_left, RCLike.conj_ofReal, map_sub, sub_mul]
    rw [hinner, norm_mul, RCLike.norm_ofReal, mul_pow]
    gcongr
    exact hsep i
  -- names the application so the norm bound applies to it directly.
  change (r + δ) * ‖x‖ ≤ ‖S x‖
  rw [← sq_le_sq₀ (mul_nonneg hk (norm_nonneg x)) (norm_nonneg (S x))]
  simpa [mul_pow] using hsq

end TauCeti
