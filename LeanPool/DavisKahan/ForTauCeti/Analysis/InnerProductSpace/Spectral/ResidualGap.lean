/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/

/-
Staged for Tau Ceti: additions to `Mathlib/Analysis/InnerProductSpace/Spectrum.lean`
alongside the finite-dimensional spectral perturbation material.
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Spectral.EigenFrame

/-! # The spectral-gap residual lower bound

Let `T` be symmetric, `U` a `T`-invariant subspace whose spectrum is
`Δ`-separated from the spectrum on `Uᗮ`, and let `w` be *any* family of trial
vectors carrying trial values `lam i` drawn from the spectrum on `U`.  Then the
mass of `w i` outside `U` is controlled by the residual `lam i • w i - T (w i)`:

`Δ² ∑ᵢ ‖P_{Uᗮ} wᵢ‖² ≤ ∑ᵢ ‖lam i • wᵢ − T wᵢ‖²`.

This is the lower half of the Davis--Kahan/Yu--Wang--Samworth residual sandwich,
stated where it actually lives: it needs nothing about `w` beyond the residual,
in particular neither orthonormality nor any relation to a second operator.  The
proof expands `P_{Uᗮ} wᵢ` in an eigenfamily of `T|Uᗮ` (`exists_isEigenFamily_span_eq`);
each coordinate is multiplied by `lam i − μₖ`, and every such difference is at
least `Δ` because `lam i` and `μₖ` sit on opposite sides of the gap.

Because the trial values are only required to lie in `restrictedPointSpectrum T U`,
the statement is insensitive to which eigenvectors were chosen inside a repeated
eigenspace — the point of `TauCeti.IsEigenFamily`.

## Main results

* `TauCeti.norm_sq_starProjection_of_span_range`: Parseval for the projection
  onto the span of an orthonormal family.
* `TauCeti.exists_isEigenFamily_span_eq`: an invariant subspace of a symmetric
  operator is spanned by an orthonormal eigenfamily.
* `TauCeti.sq_gap_mul_sum_sq_norm_starProjection_orthogonal_le`: the residual
  lower bound.
-/

public section

open Module (finrank)
open scoped InnerProductSpace BigOperators

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E}

/-- **Parseval for the projection onto the span of an orthonormal family.**
`‖P_W x‖² = ∑ₖ ‖⟪yₖ, x⟫‖²` whenever the orthonormal family `y` spans `W`.

`Orthonormal.norm_sq_starProjection_span_image` says this for the span written
as an image; this is the form a caller holding a named subspace can use. -/
theorem norm_sq_starProjection_of_span_range {W : Submodule 𝕜 E}
    [W.HasOrthogonalProjection] {m : ℕ} {y : Fin m → E} (hy : Orthonormal 𝕜 y)
    (hspan : Submodule.span 𝕜 (Set.range y) = W) (x : E) :
    ‖W.starProjection x‖ ^ 2 = ∑ k, ‖⟪y k, x⟫_𝕜‖ ^ 2 := by
  classical
  subst hspan
  have himg : Set.range y = y '' (↑(Finset.univ : Finset (Fin m)) : Set (Fin m)) := by
    simp
  simp only [himg]
  exact Orthonormal.norm_sq_starProjection_span_image hy Finset.univ x

/-- **An invariant subspace is spanned by an orthonormal eigenfamily.**
Diagonalize the restriction `T|W` and push its eigenbasis back into `E`. -/
theorem exists_isEigenFamily_span_eq (hT : T.IsSymmetric) {W : Submodule 𝕜 E}
    (hW : IsInvariant T W) :
    ∃ (m : ℕ) (y : Fin m → E) (c : Fin m → ℝ),
      IsEigenFamily T c y ∧ Submodule.span 𝕜 (Set.range y) = W := by
  classical
  have hsym : (T.restrict hW).IsSymmetric := hT.restrict_invariant hW
  have hm : finrank 𝕜 W = finrank 𝕜 W := rfl
  set b := hsym.eigenvectorBasis hm with hb
  have hon : Orthonormal 𝕜 fun k => ((b k : W) : E) :=
    b.orthonormal.comp_linearIsometry W.subtypeₗᵢ
  refine ⟨finrank 𝕜 W, fun k => ((b k : W) : E), fun k => hsym.eigenvalues hm k,
    ⟨hon, ?_⟩, ?_⟩
  · intro k
    have hk : (T.restrict hW) (b k) = (hsym.eigenvalues hm k : 𝕜) • b k :=
      hsym.apply_eigenvectorBasis hm k
    exact congrArg Subtype.val hk
  · refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr ?_) ?_
    · rintro _ ⟨k, rfl⟩
      exact (b k).2
    · rw [finrank_span_eq_card hon.linearIndependent, Fintype.card_fin]

/-- **The spectral-gap residual lower bound.**

With `U` invariant, `Δ`-separated from `Uᗮ` in `T`'s spectrum, and trial values
`lam i` carried by `U`, the component of `w i` outside `U` costs at least `Δ`
per unit of residual:
`Δ² ∑ᵢ ‖P_{Uᗮ} wᵢ‖² ≤ ∑ᵢ ‖lam i • wᵢ − T wᵢ‖²`.

No hypothesis is placed on `w`; the estimate is coordinatewise in an eigenfamily
of `T|Uᗮ` followed by Bessel. -/
theorem sq_gap_mul_sum_sq_norm_starProjection_orthogonal_le (hT : T.IsSymmetric)
    {U : Submodule 𝕜 E} {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hgap : PointInternalGap T U Δ) {d : ℕ} (w : Fin d → E) (lam : Fin d → ℝ)
    (hlam : ∀ i, lam i ∈ restrictedPointSpectrum T U) :
    Δ ^ 2 * ∑ i, ‖Uᗮ.starProjection (w i)‖ ^ 2
      ≤ ∑ i, ‖(lam i : 𝕜) • w i - T (w i)‖ ^ 2 := by
  classical
  have hU := hgap.1
  obtain ⟨m, y, c, hfam, hspan⟩ :=
    exists_isEigenFamily_span_eq hT (isInvariant_orthogonal_of_isSymmetric hT hU)
  -- Each complementary eigenvalue is separated from every trial value.
  have hsep : ∀ (i : Fin d) (k : Fin m), Δ ≤ |lam i - c k| := fun i k =>
    hgap.2 (lam i) (c k) (hlam i)
      (hspan ▸ hfam.eigenvalue_mem_restrictedPointSpectrum k)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  -- The residual's coordinate at `y k` is `(lam i − cₖ) ⟪yₖ, wᵢ⟫`.
  have hinner : ∀ k, ⟪y k, (lam i : 𝕜) • w i - T (w i)⟫_𝕜
      = ((lam i - c k : ℝ) : 𝕜) * ⟪y k, w i⟫_𝕜 := by
    intro k
    rw [inner_sub_right, inner_smul_right, ← hT (y k) (w i), hfam.apply_eq k,
      inner_smul_left, RCLike.conj_ofReal]
    push_cast
    ring
  calc Δ ^ 2 * ‖Uᗮ.starProjection (w i)‖ ^ 2
      = Δ ^ 2 * ∑ k, ‖⟪y k, w i⟫_𝕜‖ ^ 2 := by
        rw [norm_sq_starProjection_of_span_range hfam.orthonormal hspan]
    _ = ∑ k, Δ ^ 2 * ‖⟪y k, w i⟫_𝕜‖ ^ 2 := Finset.mul_sum _ _ _
    _ ≤ ∑ k, ‖⟪y k, (lam i : 𝕜) • w i - T (w i)⟫_𝕜‖ ^ 2 := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [hinner k, norm_mul, mul_pow, RCLike.norm_ofReal, sq_abs]
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        rw [show (lam i - c k) ^ 2 = |lam i - c k| ^ 2 from (sq_abs _).symm]
        exact pow_le_pow_left₀ hΔ (hsep i k) 2
    _ ≤ ‖(lam i : 𝕜) • w i - T (w i)‖ ^ 2 :=
        _root_.Orthonormal.sum_inner_products_le _ hfam.orthonormal

end TauCeti
