/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8
-/

/-
Staged for Tau Ceti, roadmap topic T01.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
additions to `Mathlib/Analysis/InnerProductSpace/Positive.lean`
(and a new `Mathlib/Analysis/InnerProductSpace/PositiveSqrt.lean`).

Sub-dev I of the operator polar decomposition project — COMPLETE
(proof-complete; reduction uses only:
`propext, Classical.choice, Quot.sound`). Tickets PD-01..PD-04.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.SelfAdjointFunctionalCalculus


/-! # The positive square root of a positive symmetric operator (Sub-dev I)

For a positive symmetric operator `T` on a finite-dimensional inner product space over
`𝕜 : RCLike`, we build the unique positive symmetric operator `sqrt T` with `sqrt T ∘ₗ sqrt T = T`,
via the spectral theorem (`sqrt T := ∑ᵢ √λᵢ • rankOne eᵢ eᵢ`).

Source: Horn & Johnson, *Matrix Analysis*, 2nd ed. (2013), **Theorem 7.2.6** (unique positive
semidefinite square root) and **Theorem 7.2.7(b)** (`ker (A⋆A) = ker A`).

This is the `𝕜`-generic (ℝ and ℂ) `LinearMap` counterpart of mathlib's ℂ-only `CFC.sqrt`/`CFC.abs`
on `E →L[ℂ] E`; the RCLike operator route needs it because the C⋆-algebra/CFC instances on
`E →L[𝕜] E` are registered only for `𝕜 = ℂ`.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Analysis.InnerProductSpace.PositiveSqrt`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `3676b55`.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`; declaration names and proofs are unchanged.
* Original authors / copyright: Jon Crall, Claude Opus 4.8; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

public section

open scoped InnerProductSpace
open InnerProductSpace

namespace LinearMap.IsPositive

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-! `LinearMap.IsPositive.sqrt` itself is defined in
`ForTauCeti/Analysis/InnerProductSpace/SelfAdjointFunctionalCalculus.lean`, as the
functional calculus of `Real.sqrt`.  It was once defined twice -- there and
here, with the two shown equal by `rfl` -- and
the duplicate has since been collapsed into the calculus.  This
module keeps what is special to the square root — that it is positive, that it
squares to `T`, and the uniqueness theory the general calculus has no analogue
for. -/

/-- The square root is positive. HJ 7.2.6 (it is the PSD square root). -/
theorem sqrt_isPositive {T : E →ₗ[𝕜] E} (hT : T.IsPositive) :
    hT.sqrt.IsPositive := by
  unfold IsPositive.sqrt TauCeti.selfAdjointFunctionalCalculus
  refine isPositive_sum _ fun i _ => ?_
  refine IsPositive.smul_of_nonneg ?_ (RCLike.ofReal_nonneg.mpr (Real.sqrt_nonneg _))
  exact (InnerProductSpace.isPositive_rankOne_self _).toLinearMap

/-- The square root is symmetric. -/
theorem sqrt_isSymmetric {T : E →ₗ[𝕜] E} (hT : T.IsPositive) :
    hT.sqrt.IsSymmetric :=
  hT.sqrt_isPositive.isSymmetric

/-- `sqrt T` acts on the `k`-th eigenvector as multiplication by `√λₖ` (it is diagonal in the same
eigenbasis as `T`). -/
theorem sqrt_apply_eigenvectorBasis {T : E →ₗ[𝕜] E} (hT : T.IsPositive)
    (k : Fin (Module.finrank 𝕜 E)) :
    hT.sqrt (hT.isSymmetric.eigenvectorBasis rfl k)
      = (Real.sqrt (hT.isSymmetric.eigenvalues rfl k) : 𝕜)
          • hT.isSymmetric.eigenvectorBasis rfl k := by
  -- the general calculus already proves this; the same `Finset.sum_eq_single`
  -- argument used to be written out a second time here
  exact TauCeti.selfAdjointFunctionalCalculus_apply_eigenvectorBasis
    hT.isSymmetric Real.sqrt k

/-- **Defining property:** `sqrt T` squares to `T`. HJ 7.2.6 (`B² = A`). -/
theorem sqrt_mul_self {T : E →ₗ[𝕜] E} (hT : T.IsPositive) :
    hT.sqrt ∘ₗ hT.sqrt = T := by
  apply (hT.isSymmetric.eigenvectorBasis rfl).toBasis.ext
  intro k
  have hnn := hT.nonneg_eigenvalues rfl k
  simp only [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply, sqrt_apply_eigenvectorBasis,
    map_smul, smul_smul, hT.isSymmetric.apply_eigenvectorBasis]
  rw [← RCLike.ofReal_mul, Real.mul_self_sqrt hnn]

omit [FiniteDimensional 𝕜 E] in
/-- Pointwise root: if `S ≥ 0` and `S² v = μ² v` with `μ ≥ 0`, then `S v = μ v`. The crux of
uniqueness — `v` lies in the `μ²`-eigenspace of `S²`, on which the positive `S` acts as `μ`. -/
theorem apply_eq_smul_of_apply_apply_eq_smul {S : E →ₗ[𝕜] E} (hS : S.IsPositive) {v : E} {μ : ℝ}
    (hμ : 0 ≤ μ) (hv : S (S v) = ((μ : 𝕜) * (μ : 𝕜)) • v) :
    S v = (μ : 𝕜) • v := by
  rcases hμ.eq_or_lt with hμ0 | hμpos
  · -- μ = 0: `S² v = 0`, so `‖S v‖² = re⟪v, S² v⟫ = 0`.
    have hμz : (μ : 𝕜) = 0 := by rw [← hμ0]; simp
    rw [hμz, zero_smul]
    have hSSv : S (S v) = 0 := by rw [hv, hμz]; simp
    have h2 : ‖S v‖ ^ 2 = 0 := by
      rw [norm_sq_eq_re_inner (𝕜 := 𝕜), hS.isSymmetric v (S v), hSSv]; simp
    have : ‖S v‖ = 0 := by
      by_contra hne
      exact absurd h2 (ne_of_gt (pow_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)) 2))
    exact norm_eq_zero.mp this
  · -- μ > 0: with `w = S v - μ v`, `(S + μ) w = S² v - μ² v = 0`, and `S ≥ 0` forces `w = 0`.
    set w := S v - (μ : 𝕜) • v with hwdef
    have hkey : S w + (μ : 𝕜) • w = 0 := by
      rw [hwdef, map_sub, map_smul, hv, smul_sub, smul_smul]; abel
    have hSw : S w = (-(μ : 𝕜)) • w := by
      rw [neg_smul, eq_neg_iff_add_eq_zero]; exact hkey
    have h1 := hS.re_inner_nonneg_left w
    -- Left as a `rw` chain on purpose: `simp only` with this same list reports
    -- `← RCLike.ofReal_neg` as a possibly-looping simp theorem and fails.  A reversed
    -- rewrite that is applied once, in position, is exactly what `rw` is for.
    rw [hSw, inner_smul_left, map_neg, RCLike.conj_ofReal, ← RCLike.ofReal_neg,
      RCLike.re_ofReal_mul, ← norm_sq_eq_re_inner] at h1
    have hw0 : w = 0 := by
      by_contra hne
      have hpos : 0 < ‖w‖ ^ 2 :=
        pow_pos (lt_of_le_of_ne (norm_nonneg _) (fun hq => hne (norm_eq_zero.mp hq.symm))) 2
      nlinarith [h1, hμpos, hpos]
    rw [hwdef, sub_eq_zero] at hw0
    exact hw0

/-- **Uniqueness:** any positive `S` with `S² = T` is `sqrt T`. HJ 7.2.6(a). -/
theorem sqrt_unique {T S : E →ₗ[𝕜] E} (hT : T.IsPositive) (hS : S.IsPositive)
    (h : S ∘ₗ S = T) : S = hT.sqrt := by
  apply (hT.isSymmetric.eigenvectorBasis rfl).toBasis.ext
  intro i
  rw [OrthonormalBasis.coe_toBasis, sqrt_apply_eigenvectorBasis]
  refine apply_eq_smul_of_apply_apply_eq_smul hS (Real.sqrt_nonneg _) ?_
  rw [← LinearMap.comp_apply, h, hT.isSymmetric.apply_eigenvectorBasis,
    ← RCLike.ofReal_mul, Real.mul_self_sqrt (hT.nonneg_eigenvalues rfl i)]

/-- **The isometry-defect identity** `‖sqrt T x‖² = re ⟪T x, x⟫`. This is the seed of the polar
decomposition norm identity `‖A x‖ = ‖|A| x‖`. -/
@[simp]
theorem sq_norm_sqrt_apply {T : E →ₗ[𝕜] E} (hT : T.IsPositive) (x : E) :
    ‖hT.sqrt x‖ ^ 2 = RCLike.re ⟪T x, x⟫_𝕜 := by
  have hss : hT.sqrt (hT.sqrt x) = T x := by
    rw [← LinearMap.comp_apply, sqrt_mul_self]
  rw [norm_sq_eq_re_inner (𝕜 := 𝕜), hT.sqrt_isSymmetric x (hT.sqrt x), hss,
    ← hT.isSymmetric x x]

/-- `ker (sqrt T) = ker T`. HJ 7.2.7(b) applied through `sqrt T ∘ₗ sqrt T = T`. -/
theorem ker_sqrt {T : E →ₗ[𝕜] E} (hT : T.IsPositive) :
    ker hT.sqrt = ker T := by
  have h := LinearMap.ker_adjoint_comp_self hT.sqrt
  rw [hT.sqrt_isPositive.adjoint_eq, hT.sqrt_mul_self] at h
  exact h.symm

/-- `range (sqrt T) = range T`. HJ 7.2.6(c). -/
theorem range_sqrt {T : E →ₗ[𝕜] E} (hT : T.IsPositive) :
    range hT.sqrt = range T := by
  have hs : (ker hT.sqrt)ᗮ = range hT.sqrt := by
    rw [LinearMap.orthogonal_ker, hT.sqrt_isPositive.adjoint_eq]
  have hTr : (ker T)ᗮ = range T := by
    rw [LinearMap.orthogonal_ker, hT.adjoint_eq]
  rw [← hs, ← hTr, ker_sqrt hT]

/-- On the invertible (strictly positive) case, `sqrt T` is invertible; this provides the inverse
square root used by the intertwining unitary. -/
theorem isUnit_sqrt_of_isUnit {T : E →ₗ[𝕜] E} (hT : T.IsPositive)
    (hunit : IsUnit T) : IsUnit hT.sqrt := by
  rw [LinearMap.isUnit_iff_ker_eq_bot] at hunit ⊢
  rwa [ker_sqrt hT]

end LinearMap.IsPositive
