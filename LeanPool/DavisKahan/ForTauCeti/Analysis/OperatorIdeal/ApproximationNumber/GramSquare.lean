/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.GramSpectralRank
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.FiniteRestriction

/-!
# Approximation numbers of the Gram operator are the squares

```
aₙ(X†X) = aₙ(X)².
```

This is the bridge between a statement about an operator and the corresponding statement
about its *squared displacement*: Davis--Kahan Proposition 4.1 dominates approximation
numbers at the first power, while Proposition 4.3 is a Ky Fan statement about
`(1−W)†(1−W)`, and nothing else connects them.

## Why the two directions are not symmetric

The easy direction, `aₙ(X)² ≤ aₙ(X†X)`, is pure min--max and needs no spectral theory: on
a subspace where `s‖x‖ ≤ ‖Xx‖`, Cauchy--Schwarz gives
`‖X†Xx‖ ‖x‖ ≥ re ⟪X†Xx, x⟫ = ‖Xx‖² ≥ s²‖x‖²`, so the same subspace is an `s²` lower
witness for the Gram operator.

The other direction cannot be proved that way, and the failure is instructive.  A
*pointwise* lower bound `‖X†Xx‖ ≥ s‖x‖` on a subspace only yields `‖Xx‖ ≥ (s/‖X‖)‖x‖` —
the wrong power — because `‖X†Xx‖ ≤ ‖X‖‖Xx‖`.  The subspace that is optimal for `X†X` has
to be a *spectral* one, and then the cut commutes with the operator.  So the proof runs
through the Gram spectral projections: above a threshold `r' > aₙ(X)` the projection
`E_{X†X}((r'²,∞))` has rank at most `n`
(`rank_gramProjection_Ioi_le_natCast_of_approximationNumber_lt`), and on its orthogonal
band both `y` and `X†Xy` satisfy `‖X·‖ ≤ r‖·‖`, whence
`‖X†Xy‖² = ⟪Xy, X(X†Xy)⟫ ≤ r‖y‖ · r‖X†Xy‖`.  Feeding that band bound to
`approximationNumber_le_of_spectral_band` gives `aₙ(X†X) ≤ r²` for every `r > aₙ(X)`.

The two thresholds `r' < r` are not padding: they avoid having to decide where spectral
mass sitting exactly at the cutoff belongs.  The same device appears in the
infinite-dimensional Proposition 4.1 argument.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`; it has had no prior home.
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and `ForTauCeti`.
-/

@[expose] public section

open scoped InnerProductSpace

namespace TauCeti
namespace ApproximationNumber

open TauCeti.LinearPMap

noncomputable section

universe u v

variable {E0 : Type u} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0] [CompleteSpace E0]
variable {E1 : Type v} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1] [CompleteSpace E1]

/-- **The Gram operator commutes with each of its own spectral projections.**

This is what makes the spectral cut usable: the band is invariant, so the band bound
applies to `X†Xy` as well as to `y`. -/
theorem gramOperator_comm_gramProjection (X : E0 →L[ℂ] E1) (B : Set ℝ)
    (hB : MeasurableSet B) (z : E0) :
    gramOperator X ((gramSpectralPVM X).proj B hB z) =
      (gramSpectralPVM X).proj B hB (gramOperator X z) := by
  have hdom : z ∈ (gramLinearPMap X).domain := by
    rw [gramLinearPMap_domain]
    exact Submodule.mem_top
  have h := specProjection_apply_domain (gramLinearPMap_isSelfAdjoint X) B hB
    (⟨z, hdom⟩ : (gramLinearPMap X).domain)
  rw [gramSpectralPVM_proj_eq_specProjection]
  simpa only [gramLinearPMap_apply] using h

/-- **On the low Gram band the operator is bounded by the threshold.**

A vector killed by `E_{X†X}((r'²,∞))` has all its Gram spectral mass at or below `r'²`, so
in particular none in `[r²,∞)` once `r'² < r²`, and its energy `‖Xz‖²` is at most
`r²‖z‖²`. -/
theorem norm_apply_le_of_gramProjection_Ioi_apply_eq_zero (X : E0 →L[ℂ] E1) {r r' : ℝ}
    (hr0 : 0 ≤ r) (hlt : r' ^ 2 < r ^ 2) {z : E0}
    (hz : (gramSpectralPVM X).proj (Set.Ioi (r' ^ 2)) measurableSet_Ioi z = 0) :
    ‖X z‖ ≤ r * ‖z‖ := by
  have hIci : (gramSpectralPVM X).proj (Set.Ici (r ^ 2)) measurableSet_Ici z = 0 := by
    have hsub : Set.Ici (r ^ 2) ∩ Set.Ioi (r' ^ 2) = Set.Ici (r ^ 2) := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioi, and_iff_left_iff_imp]
      intro ht
      linarith
    have hmul : (gramSpectralPVM X).proj (Set.Ici (r ^ 2)) measurableSet_Ici *
        (gramSpectralPVM X).proj (Set.Ioi (r' ^ 2)) measurableSet_Ioi =
        (gramSpectralPVM X).proj (Set.Ici (r ^ 2)) measurableSet_Ici := by
      rw [(gramSpectralPVM X).proj_inter,
        (gramSpectralPVM X).proj_congr hsub
          (measurableSet_Ici.inter measurableSet_Ioi) measurableSet_Ici]
    have happ := congrArg (fun T : E0 →L[ℂ] E0 => T z) hmul
    simp only [_root_.mul_apply_eq_comp, hz, map_zero] at happ
    exact happ.symm
  have hdom : z ∈ (gramLinearPMap X).domain := by
    rw [gramLinearPMap_domain]
    exact Submodule.mem_top
  have henergy := LinearPMap.re_inner_le_of_specProjection_Ici_apply_eq_zero
    (gramLinearPMap_isSelfAdjoint X) (⟨z, hdom⟩ : (gramLinearPMap X).domain) (by
      rw [← gramSpectralPVM_proj_eq_specProjection X (Set.Ici (r ^ 2)) measurableSet_Ici]
      exact hIci)
  have hsq : ‖X z‖ ^ 2 ≤ r ^ 2 * ‖z‖ ^ 2 := by
    calc
      ‖X z‖ ^ 2 = RCLike.re ⟪gramOperator X z, z⟫_ℂ := (re_inner_gramOperator X z).symm
      _ = RCLike.re ⟪gramLinearPMap X (⟨z, hdom⟩ : (gramLinearPMap X).domain), z⟫_ℂ := by
        rw [gramLinearPMap_apply]
      _ ≤ r ^ 2 * ‖z‖ ^ 2 := henergy
  have hsq' : ‖X z‖ ^ 2 ≤ (r * ‖z‖) ^ 2 := by
    rw [mul_pow]
    exact hsq
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hr0 (norm_nonneg z))).1 hsq'

/-- **The easy direction**: `aₙ(X)² ≤ aₙ(X†X)`, by min--max alone.

An `s`-lower witness for `X` is an `s²`-lower witness for `X†X`, since
`‖X†Xx‖‖x‖ ≥ re ⟪X†Xx, x⟫ = ‖Xx‖²`. -/
theorem sq_approximationNumber_le_approximationNumber_gramOperator (X : E0 →L[ℂ] E1)
    (n : ℕ) :
    X.approximationNumber n ^ 2 ≤ (gramOperator X).approximationNumber n := by
  have key : ∀ r : ℝ, 0 ≤ r → r < X.approximationNumber n →
      r ^ 2 < (gramOperator X).approximationNumber n := by
    intro r hr0 hr
    obtain ⟨s, hrs, v, hv, hV⟩ :=
      (ContinuousLinearMap.lt_approximationNumber_iff_exists_finiteDimensional_lowerBound
        X n hr0).mp hr
    have hs0 : 0 ≤ s := hr0.trans hrs.le
    refine (ContinuousLinearMap.lt_approximationNumber_iff_exists_finiteDimensional_lowerBound
      (gramOperator X) n (by positivity)).mpr ⟨s ^ 2, by nlinarith, v, hv, ?_⟩
    intro x hx
    have hlow : s * ‖x‖ ≤ ‖X x‖ := hV x hx
    have hq : ‖X x‖ ^ 2 = RCLike.re ⟪gramOperator X x, x⟫_ℂ :=
      (re_inner_gramOperator X x).symm
    have hcs : RCLike.re ⟪gramOperator X x, x⟫_ℂ ≤ ‖gramOperator X x‖ * ‖x‖ :=
      (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
    have hsq : (s * ‖x‖) ^ 2 ≤ ‖X x‖ ^ 2 := by
      nlinarith [mul_nonneg hs0 (norm_nonneg x), norm_nonneg (X x)]
    have h2 : (s ^ 2 * ‖x‖) * ‖x‖ ≤ ‖gramOperator X x‖ * ‖x‖ := by
      calc
        (s ^ 2 * ‖x‖) * ‖x‖ = (s * ‖x‖) ^ 2 := by ring
        _ ≤ ‖X x‖ ^ 2 := hsq
        _ = RCLike.re ⟪gramOperator X x, x⟫_ℂ := hq
        _ ≤ ‖gramOperator X x‖ * ‖x‖ := hcs
    rcases eq_or_lt_of_le (norm_nonneg x) with hx0 | hx0
    · rw [← hx0, mul_zero]
      exact norm_nonneg _
    · exact le_of_mul_le_mul_right h2 hx0
  by_contra hcon
  have hcon' : (gramOperator X).approximationNumber n < X.approximationNumber n ^ 2 :=
    lt_of_not_ge hcon
  have ha0 : 0 ≤ X.approximationNumber n := X.approximationNumber_nonneg n
  have hg0 : 0 ≤ (gramOperator X).approximationNumber n :=
    (gramOperator X).approximationNumber_nonneg n
  have hlt : Real.sqrt ((gramOperator X).approximationNumber n) <
      X.approximationNumber n := by
    have h := Real.sqrt_lt_sqrt hg0 hcon'
    rwa [Real.sqrt_sq ha0] at h
  have hfin := key _ (Real.sqrt_nonneg _) hlt
  rw [Real.sq_sqrt hg0] at hfin
  exact lt_irrefl _ hfin

/-- **The spectral direction**: `aₙ(X†X) ≤ aₙ(X)²`.

For each `r > aₙ(X)` pick `r'` strictly between.  The Gram spectral projection above `r'²`
has rank at most `n`, its orthogonal band is invariant under `X†X`, and on that band
`‖X†Xy‖² = ⟪Xy, X(X†Xy)⟫ ≤ r‖y‖ · r‖X†Xy‖`, so the band bound is `r²`. -/
theorem approximationNumber_gramOperator_le_sq (X : E0 →L[ℂ] E1) (n : ℕ) :
    (gramOperator X).approximationNumber n ≤ X.approximationNumber n ^ 2 := by
  have ha0 : 0 ≤ X.approximationNumber n := X.approximationNumber_nonneg n
  have key : ∀ r : ℝ, X.approximationNumber n < r →
      (gramOperator X).approximationNumber n ≤ r ^ 2 := by
    intro r hr
    have hr0 : 0 ≤ r := ha0.trans hr.le
    obtain ⟨r', hr1, hr2⟩ := exists_between hr
    have hr'0 : 0 ≤ r' := ha0.trans hr1.le
    have hsqlt : r' ^ 2 < r ^ 2 := by nlinarith
    set P : E0 →L[ℂ] E0 :=
      (gramSpectralPVM X).proj (Set.Ioi (r' ^ 2)) measurableSet_Ioi with hPdef
    have hrank : P.rank ≤ (n : Cardinal) :=
      rank_gramProjection_Ioi_le_natCast_of_approximationNumber_lt X n hr'0 hr1
    have hidem : IsIdempotentElem P := (gramSpectralPVM X).proj_idem _ _
    have hsa : IsSelfAdjoint P := (gramSpectralPVM X).isSelfAdjoint_proj _ _
    refine ContinuousLinearMap.approximationNumber_le_of_spectral_band
      (by positivity) hidem hsa hrank ?_
    intro x
    have hPy : P (x - P x) = 0 := by
      have hPP : P (P x) = P x := by
        have h := congrArg (fun T : E0 →L[ℂ] E0 => T x) hidem
        simpa only [_root_.mul_apply_eq_comp, ContinuousLinearMap.comp_apply] using h
      rw [map_sub, hPP, sub_self]
    have hXy : ‖X (x - P x)‖ ≤ r * ‖x - P x‖ :=
      norm_apply_le_of_gramProjection_Ioi_apply_eq_zero X hr0 hsqlt hPy
    have hPGy : P (gramOperator X (x - P x)) = 0 := by
      rw [← gramOperator_comm_gramProjection, hPy, map_zero]
    have hXGy : ‖X (gramOperator X (x - P x))‖ ≤ r * ‖gramOperator X (x - P x)‖ :=
      norm_apply_le_of_gramProjection_Ioi_apply_eq_zero X hr0 hsqlt hPGy
    have hkey : (⟪gramOperator X (x - P x), gramOperator X (x - P x)⟫_ℂ) =
        ⟪X (x - P x), X (gramOperator X (x - P x))⟫_ℂ :=
      ContinuousLinearMap.adjoint_inner_left X (gramOperator X (x - P x))
        (X (x - P x))
    have hinner : ‖gramOperator X (x - P x)‖ ^ 2 =
        RCLike.re ⟪X (x - P x), X (gramOperator X (x - P x))⟫_ℂ := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), hkey]
    have hbound : ‖gramOperator X (x - P x)‖ ^ 2 ≤
        (r * ‖x - P x‖) * (r * ‖gramOperator X (x - P x)‖) := by
      rw [hinner]
      refine le_trans ((RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)) ?_
      exact mul_le_mul hXy hXGy (norm_nonneg _) (mul_nonneg hr0 (norm_nonneg _))
    rcases eq_or_lt_of_le (norm_nonneg (gramOperator X (x - P x))) with h0 | h0
    · rw [← h0]
      positivity
    · have hmul : ‖gramOperator X (x - P x)‖ * ‖gramOperator X (x - P x)‖ ≤
          (r ^ 2 * ‖x - P x‖) * ‖gramOperator X (x - P x)‖ := by
        calc
          ‖gramOperator X (x - P x)‖ * ‖gramOperator X (x - P x)‖
              = ‖gramOperator X (x - P x)‖ ^ 2 := by ring
          _ ≤ (r * ‖x - P x‖) * (r * ‖gramOperator X (x - P x)‖) := hbound
          _ = (r ^ 2 * ‖x - P x‖) * ‖gramOperator X (x - P x)‖ := by ring
      exact le_of_mul_le_mul_right hmul h0
  by_contra hcon
  have hcon' : X.approximationNumber n ^ 2 < (gramOperator X).approximationNumber n :=
    lt_of_not_ge hcon
  have hg0 : 0 ≤ (gramOperator X).approximationNumber n :=
    (gramOperator X).approximationNumber_nonneg n
  have hlt : X.approximationNumber n <
      Real.sqrt ((gramOperator X).approximationNumber n) := by
    have h := Real.sqrt_lt_sqrt (by positivity) hcon'
    rwa [Real.sqrt_sq ha0] at h
  obtain ⟨t, ht1, ht2⟩ := exists_between hlt
  have ht0 : 0 ≤ t := ha0.trans ht1.le
  have hts : t ^ 2 < (gramOperator X).approximationNumber n := by
    nlinarith [Real.sq_sqrt hg0, Real.sqrt_nonneg
      ((gramOperator X).approximationNumber n)]
  exact absurd (key t ht1) (not_le.mpr hts)

/-- **The approximation numbers of the Gram operator are the squares.**

`aₙ(X†X) = aₙ(X)²`.  This is the step that lets an approximation-number domination at the
first power be squared and summed into a Ky Fan statement about squared displacements. -/
theorem approximationNumber_gramOperator_complex (X : E0 →L[ℂ] E1) (n : ℕ) :
    (gramOperator X).approximationNumber n = X.approximationNumber n ^ 2 :=
  le_antisymm (approximationNumber_gramOperator_le_sq X n)
    (sq_approximationNumber_le_approximationNumber_gramOperator X n)

end

end ApproximationNumber
end TauCeti
