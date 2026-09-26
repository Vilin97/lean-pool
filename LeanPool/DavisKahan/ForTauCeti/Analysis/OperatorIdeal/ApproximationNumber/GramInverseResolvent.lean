/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.GramResolvent

/-!
# Approximation numbers of the inverse Gram resolvent `T (1 + T)⁻¹`

Write `T = Y⋆Y` for the Gram operator of a bounded operator `Y`.  The operator

```
Q = T (1 + T)⁻¹
```

is the inverse of the transformation `GramResolvent.lean` studies: with `T = tan²Θ`
it is `sin²Θ`.  This module proves

```
aₙ(Q) ≤ aₙ(Y)² / (1 + aₙ(Y)²).
```

## Why this is the missing half

`approximationNumber_le_of_gramResolvent` transfers approximation numbers *forwards*
along `u ↦ u/(1−u)`; its own module records that the reverse inequality
"needs the full spectral-order theory of monotone functional calculus".  It does
not: the reverse inequality for one monotone map is the *forward* inequality for
its inverse, and `u ↦ u/(1+u)` is the inverse of `u ↦ u/(1−u)`.  Composing the
two bounds gives an equality,

```
aₙ(tan Θ) = tan (arcsin aₙ(sin Θ)),
```

which is what a Davis--Kahan tangent statement phrased on the singular-value
*sequence* of the sine needs, and what an operator-level statement alone cannot
supply.

## The band estimate

The spectral cut is the same as in `GramResolvent.lean` and unavoidable for the
same reason.  On the band `ker E_{Y⋆Y}((r'², ∞))`, put `w = Q η` and `z = η − w`.
The defining relation `Q = T − T Q` gives `w = T z`, hence

* `‖w‖² = ⟪Y z, Y w⟫ ≤ r‖z‖ · r‖w‖`, so `‖w‖ ≤ r‖Y z‖ ≤ r²‖z‖`, and
* `‖η‖² = ‖z‖² + 2‖Y z‖² + ‖w‖²`, because `re ⟪z, w⟫ = re ⟪z, T z⟫ = ‖Y z‖²`.

Those two facts alone force `(1 + r²)‖w‖ ≤ r²‖η‖`.  No hypothesis `‖Y‖ < 1` is
needed: `u ↦ u/(1+u)` has no pole on `[0, ∞)`.

The band is entered through `Q` itself: `E((r'²,∞)) w = 0` is *derived* from
`(1 + T) E((r'²,∞)) w = 0` and the injectivity of `1 + T`, not assumed.

## Main results

* `TauCeti.ApproximationNumber.approximationNumber_le_of_gramContraction`.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`; it has had no prior home.
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and `ForTauCeti`.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation. III*,
  SIAM J. Numer. Anal. 7 (1970), 1--46, Sections 2 and 7: the tangent theorems,
  whose left-hand sides are norms of the tangent *sequence* of the principal
  angles.
-/

@[expose] public section

open scoped InnerProductSpace

namespace TauCeti
namespace ApproximationNumber

noncomputable section

universe u v

variable {E0 : Type u} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0] [CompleteSpace E0]
variable {E1 : Type v} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1] [CompleteSpace E1]

/-- `1 + Y⋆Y` is injective: its quadratic form dominates the squared norm. -/
theorem eq_zero_of_add_gramOperator_eq_zero (Y : E0 →L[ℂ] E1) {w : E0}
    (hw : w + gramOperator Y w = 0) : w = 0 := by
  have hform : RCLike.re ⟪gramOperator Y w, w⟫_ℂ = ‖Y w‖ ^ 2 := re_inner_gramOperator Y w
  have hzero : RCLike.re ⟪w + gramOperator Y w, w⟫_ℂ = 0 := by
    rw [hw]; simp
  rw [inner_add_left, map_add, hform] at hzero
  have hww : RCLike.re (⟪w, w⟫_ℂ) = ‖w‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) w).symm
  rw [hww] at hzero
  have : ‖w‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖Y w‖]
  simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this

/-- **The inverse Gram resolvent band estimate.**

If `Q = T − T Q` for `T = Y⋆Y`, and `η` is killed by the Gram spectral projection
above `r'²`, then `‖Q η‖ ≤ r²/(1 + r²) ‖η‖` for every `r` with `r'² < r²`. -/
theorem norm_gramContraction_apply_le_of_gramProjection_apply_eq_zero
    (Y : E0 →L[ℂ] E1) {Q : E0 →L[ℂ] E0}
    (hQ : ∀ y, Q y = gramOperator Y y - gramOperator Y (Q y))
    {r r' : ℝ} (hr0 : 0 ≤ r) (hlt : r' ^ 2 < r ^ 2) {η : E0}
    (hη : (gramSpectralPVM Y).proj (Set.Ioi (r' ^ 2)) measurableSet_Ioi η = 0) :
    ‖Q η‖ ≤ r ^ 2 / (1 + r ^ 2) * ‖η‖ := by
  set P : E0 →L[ℂ] E0 :=
    (gramSpectralPVM Y).proj (Set.Ioi (r' ^ 2)) measurableSet_Ioi with hPdef
  set T : E0 →L[ℂ] E0 := gramOperator Y with hTdef
  have hcomm : ∀ x : E0, T (P x) = P (T x) := by
    intro x
    rw [hPdef, hTdef]
    exact gramOperator_comm_gramProjection Y _ measurableSet_Ioi x
  set w : E0 := Q η with hwdef
  set z : E0 := η - w with hzdef
  -- `w = T z`: the defining relation, rearranged.
  have hw : w = T z := by
    rw [hzdef, map_sub, hwdef]
    exact hQ η
  -- the band contains `w`, hence `z`
  have hPw : P w = 0 := by
    have hstep : P w + T (P w) = 0 := by
      have hPz : P z = -P w := by
        rw [hzdef, map_sub, hη, zero_sub]
      have h : P w = T (P z) := by rw [hw, hcomm]
      rw [hPz, map_neg] at h
      exact eq_neg_iff_add_eq_zero.mp h
    exact eq_zero_of_add_gramOperator_eq_zero Y hstep
  have hPz : P z = 0 := by rw [hzdef, map_sub, hη, hPw, sub_zero]
  -- band bounds
  have hYz : ‖Y z‖ ≤ r * ‖z‖ :=
    norm_apply_le_of_gramProjection_Ioi_apply_eq_zero Y hr0 hlt hPz
  have hYw : ‖Y w‖ ≤ r * ‖w‖ :=
    norm_apply_le_of_gramProjection_Ioi_apply_eq_zero Y hr0 hlt hPw
  -- `‖w‖² = re ⟪Y z, Y w⟫`
  have hgram : ∀ x y : E0, ⟪T x, y⟫_ℂ = ⟪Y x, Y y⟫_ℂ := by
    intro x y
    rw [hTdef, gramOperator]
    exact ContinuousLinearMap.adjoint_inner_left Y y (Y x)
  have hwsq : ‖w‖ ^ 2 ≤ ‖Y z‖ * (r * ‖w‖) := by
    have hre : ‖w‖ ^ 2 = RCLike.re ⟪Y z, Y w⟫_ℂ := by
      have h0 : ‖w‖ ^ 2 = RCLike.re ⟪w, w⟫_ℂ := norm_sq_eq_re_inner (𝕜 := ℂ) w
      rw [h0]
      nth_rewrite 1 [hw]
      rw [hgram z w]
    rw [hre]
    refine le_trans ((RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)) ?_
    exact mul_le_mul_of_nonneg_left hYw (norm_nonneg _)
  -- `‖η‖² = ‖z‖² + 2‖Y z‖² + ‖w‖²`
  have hηsq : ‖η‖ ^ 2 = ‖z‖ ^ 2 + 2 * ‖Y z‖ ^ 2 + ‖w‖ ^ 2 := by
    have hsplit : η = z + w := by rw [hzdef]; abel
    have hcross : RCLike.re ⟪z, w⟫_ℂ = ‖Y z‖ ^ 2 := by
      have hzw : ⟪z, w⟫_ℂ = ⟪z, T z⟫_ℂ := by rw [hw]
      have hsymm : ⟪z, T z⟫_ℂ = starRingEnd ℂ ⟪T z, z⟫_ℂ := (inner_conj_symm _ _).symm
      rw [hzw, hsymm, RCLike.conj_re]
      exact re_inner_gramOperator Y z
    rw [hsplit, @norm_add_sq ℂ, hcross]
  -- combine
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
  have hb0 : 0 ≤ ‖Y z‖ := norm_nonneg _
  have hden : (0 : ℝ) < 1 + r ^ 2 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hden]
  -- `‖w‖ ≤ r ‖Y z‖`
  have hwb : ‖w‖ ≤ r * ‖Y z‖ := by
    rcases eq_or_lt_of_le hw0 with h0 | h0
    · rw [← h0]; positivity
    · have hmul : ‖w‖ * ‖w‖ ≤ (r * ‖Y z‖) * ‖w‖ := by
        calc ‖w‖ * ‖w‖ = ‖w‖ ^ 2 := by ring
          _ ≤ ‖Y z‖ * (r * ‖w‖) := hwsq
          _ = (r * ‖Y z‖) * ‖w‖ := by ring
      exact le_of_mul_le_mul_right hmul h0
  have hsq : (‖w‖ * (1 + r ^ 2)) ^ 2 ≤ (r ^ 2 * ‖η‖) ^ 2 := by
    have h1 : ‖w‖ ^ 2 ≤ r ^ 2 * ‖Y z‖ ^ 2 := by nlinarith
    have h2 : ‖Y z‖ ^ 2 ≤ r ^ 2 * ‖z‖ ^ 2 := by nlinarith
    have h4 : ‖w‖ ^ 2 ≤ r ^ 2 * (r ^ 2 * ‖z‖ ^ 2) := by nlinarith [sq_nonneg r]
    have h5 : r ^ 2 * ‖w‖ ^ 2 ≤ r ^ 2 * (r ^ 2 * ‖Y z‖ ^ 2) := by nlinarith [sq_nonneg r]
    have hexp : (r ^ 2 * ‖η‖) ^ 2 =
        r ^ 2 * r ^ 2 * (‖z‖ ^ 2 + 2 * ‖Y z‖ ^ 2 + ‖w‖ ^ 2) := by
      rw [mul_pow, ← hηsq]; ring
    rw [hexp]
    nlinarith [h4, h5, sq_nonneg r, sq_nonneg ‖w‖]
  have hlhs : 0 ≤ ‖w‖ * (1 + r ^ 2) := by positivity
  have hrhs : 0 ≤ r ^ 2 * ‖η‖ := by positivity
  exact (sq_le_sq₀ hlhs hrhs).1 hsq

/-- **The approximation numbers of the inverse Gram resolvent.**

If `Q = T − T Q` with `T = Y⋆Y` — that is, `Q = T (1 + T)⁻¹` — then

`aₙ(Q) ≤ aₙ(Y)² / (1 + aₙ(Y)²)`.

With `Y = tan Θ` and `Q = sin²Θ` this reads `aₙ(sin Θ)² ≤ tan²(arcsin …)⁻¹`-style,
and combines with `approximationNumber_le_of_gramResolvent` into the *equality*
`aₙ(tan Θ) = tan (arcsin aₙ(sin Θ))`. -/
theorem approximationNumber_le_of_gramContraction
    (Y : E0 →L[ℂ] E1) {Q : E0 →L[ℂ] E0}
    (hQ : ∀ y, Q y = gramOperator Y y - gramOperator Y (Q y)) (n : ℕ) :
    Q.approximationNumber n ≤
      Y.approximationNumber n ^ 2 / (1 + Y.approximationNumber n ^ 2) := by
  set a : ℝ := Y.approximationNumber n with hadef
  have ha0 : 0 ≤ a := Y.approximationNumber_nonneg n
  have key : ∀ r : ℝ, a < r → Q.approximationNumber n ≤ r ^ 2 / (1 + r ^ 2) := by
    intro r hr
    have hr0 : 0 ≤ r := ha0.trans hr.le
    obtain ⟨r', hr1', hr2'⟩ := exists_between hr
    have hr'0 : 0 ≤ r' := ha0.trans hr1'.le
    have hsqlt : r' ^ 2 < r ^ 2 := by nlinarith
    set P : E0 →L[ℂ] E0 :=
      (gramSpectralPVM Y).proj (Set.Ioi (r' ^ 2)) measurableSet_Ioi with hPdef
    have hrank : P.rank ≤ (n : Cardinal) :=
      rank_gramProjection_Ioi_le_natCast_of_approximationNumber_lt Y n hr'0 hr1'
    have hidem : IsIdempotentElem P := (gramSpectralPVM Y).proj_idem _ _
    have hsa : IsSelfAdjoint P := (gramSpectralPVM Y).isSelfAdjoint_proj _ _
    refine ContinuousLinearMap.approximationNumber_le_of_spectral_band
      (by positivity) hidem hsa hrank ?_
    intro x
    have hPy : P (x - P x) = 0 := by
      have hPP : P (P x) = P x := by
        have h := congrArg (fun S : E0 →L[ℂ] E0 => S x) hidem
        simpa only [_root_.mul_apply_eq_comp, ContinuousLinearMap.comp_apply] using h
      rw [map_sub, hPP, sub_self]
    exact norm_gramContraction_apply_le_of_gramProjection_apply_eq_zero Y hQ hr0 hsqlt hPy
  by_contra hcon
  have hcon' : a ^ 2 / (1 + a ^ 2) < Q.approximationNumber n := lt_of_not_ge hcon
  have hcont : ContinuousAt (fun u : ℝ => u ^ 2 / (1 + u ^ 2)) a := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · positivity
  have hev : ∀ᶠ r in nhdsWithin a (Set.Ioi a),
      (fun u : ℝ => u ^ 2 / (1 + u ^ 2)) r < Q.approximationNumber n :=
    Filter.Tendsto.eventually_lt_const hcon'
      (hcont.continuousWithinAt (s := Set.Ioi a))
  have hgt : ∀ᶠ r in nhdsWithin a (Set.Ioi a), a < r :=
    Filter.eventually_iff_exists_mem.mpr
      ⟨Set.Ioi a, self_mem_nhdsWithin, fun r hr => hr⟩
  obtain ⟨r, hr1, hr2⟩ := (hev.and hgt).exists
  exact absurd (key r hr2) (not_le.mpr hr1)

end

end ApproximationNumber
end TauCeti
