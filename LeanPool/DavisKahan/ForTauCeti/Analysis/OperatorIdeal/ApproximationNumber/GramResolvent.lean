/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.GramSquare

/-!
# Approximation numbers of the Gram resolvent `Q (1 − Q)⁻¹`

Write `Q = X⋆X` for the Gram operator of a strict contraction `X`.  The operator

```
T = Q (1 − Q)⁻¹
```

is the one the Davis--Kahan tangent produces: with `Q = sin²Θ` it is `tan²Θ`.  This
module computes the only thing the tangent theorem needs about it,

```
aₙ(T) ≤ aₙ(X)² / (1 − aₙ(X)²).
```

Equivalently `aₙ(T) ≤ tan (arcsin aₙ(X))²`: the *monotone* scalar transfer of
approximation numbers under the Möbius map `u ↦ u/(1−u)`.

## Why an inequality and not an identity

Only this direction is used, and only this direction is elementary.  The reverse
inequality is true as well but needs the full spectral-order theory of monotone
functional calculus; nothing downstream asks for it.

## Why a spectral cut is unavoidable

For a positive `A` and an increasing `f` with `f 0 = 0`, `aₙ(f(A)) ≤ f(aₙ(A))` is
*not* a consequence of any pointwise estimate: a subspace on which `‖Ax‖ ≤ t‖x‖`
says nothing about `f(A)` there unless the subspace is invariant.  The proof
therefore cuts with the Gram spectral projection `E_{X⋆X}((r'², ∞))`, whose rank is
at most `n` once `aₙ(X) < r'`, and works on the invariant band underneath it.

## The band estimate

On the band, write `η = x − Px` and `v = η + T η`.  The defining relation
`T = Q + Q T` gives simultaneously

* `Q v = T η` — so the value to be estimated is a Gram image, and
* `(1 − Q) v = η` — so the source vector is recovered from `v`.

Both `v` and `Q v` lie in the band, and there
`‖X v‖ ≤ r‖v‖`, hence `‖Q v‖ ≤ r²‖v‖` by the Cauchy--Schwarz step, while
`(1 − r²)‖v‖ ≤ ‖η‖` because `re ⟪η, v⟫ = ‖v‖² − ‖X v‖²`.  Combining,
`‖T η‖ ≤ r²/(1 − r²) ‖η‖`.

## Main results

* `TauCeti.ApproximationNumber.approximationNumber_le_of_gramResolvent`.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`; it has had no prior home.
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and `ForTauCeti`.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation. III*,
  SIAM J. Numer. Anal. 7 (1970), 1--46, Section 7: the ambient `tan Θ` estimate.
-/

public section

open scoped InnerProductSpace

namespace TauCeti
namespace ApproximationNumber

noncomputable section

universe u v

variable {E0 : Type u} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0] [CompleteSpace E0]
variable {E1 : Type v} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1] [CompleteSpace E1]

/-- The Gram operator has the squared norm. -/
theorem norm_gramOperator (X : E0 →L[ℂ] E1) : ‖gramOperator X‖ = ‖X‖ ^ 2 := by
  rw [gramOperator, ContinuousLinearMap.norm_adjoint_comp_self]
  ring

/-- For a strict contraction the Gram operator cannot fix a nonzero vector. -/
theorem eq_zero_of_gramOperator_eq (X : E0 →L[ℂ] E1) (hX : ‖X‖ < 1) {w : E0}
    (hw : gramOperator X w = w) : w = 0 := by
  by_contra hne
  have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hne
  have h1 : ‖gramOperator X w‖ ≤ ‖X‖ ^ 2 * ‖w‖ := by
    refine ((gramOperator X).le_opNorm w).trans ?_
    exact mul_le_mul_of_nonneg_right (le_of_eq (norm_gramOperator X)) (norm_nonneg w)
  rw [hw] at h1
  have hlt : ‖X‖ ^ 2 < 1 := by nlinarith [norm_nonneg X]
  nlinarith

/-- **The Gram resolvent band estimate.**

If `T = Q + Q T` for `Q = X⋆X`, and `η` is killed by the Gram spectral projection
above `r'²`, then `‖T η‖ ≤ r²/(1 − r²) ‖η‖` for every `r` with `r'² < r² < 1`. -/
theorem norm_gramResolvent_apply_le_of_gramProjection_apply_eq_zero
    (X : E0 →L[ℂ] E1) {T : E0 →L[ℂ] E0} (hX : ‖X‖ < 1)
    (hT : ∀ y, T y = gramOperator X y + gramOperator X (T y))
    {r r' : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hlt : r' ^ 2 < r ^ 2) {η : E0}
    (hη : (gramSpectralPVM X).proj (Set.Ioi (r' ^ 2)) measurableSet_Ioi η = 0) :
    ‖T η‖ ≤ r ^ 2 / (1 - r ^ 2) * ‖η‖ := by
  set P : E0 →L[ℂ] E0 :=
    (gramSpectralPVM X).proj (Set.Ioi (r' ^ 2)) measurableSet_Ioi with hPdef
  set Q : E0 →L[ℂ] E0 := gramOperator X with hQdef
  have hcomm : ∀ z : E0, P (Q z) = Q (P z) := by
    intro z
    rw [hPdef, hQdef]
    exact (gramOperator_comm_gramProjection X _ measurableSet_Ioi z).symm
  -- the value `T η` is again in the band
  have hPT : P (T η) = 0 := by
    have hstep : P (T η) = Q (P (T η)) := by
      have h := congrArg P (hT η)
      rw [map_add, hcomm, hcomm, hη, map_zero, zero_add] at h
      exact h
    exact eq_zero_of_gramOperator_eq X hX hstep.symm
  set v : E0 := η + T η with hvdef
  have hPv : P v = 0 := by rw [hvdef, map_add, hη, hPT, add_zero]
  have hQv : Q v = T η := by
    rw [hvdef, map_add]
    exact (hT η).symm
  have hηv : η = v - Q v := by rw [hQv, hvdef]; abel
  -- band bounds
  have hXv : ‖X v‖ ≤ r * ‖v‖ :=
    norm_apply_le_of_gramProjection_Ioi_apply_eq_zero X hr0 hlt hPv
  have hPQv : P (Q v) = 0 := by rw [hQv]; exact hPT
  have hXQv : ‖X (Q v)‖ ≤ r * ‖Q v‖ :=
    norm_apply_le_of_gramProjection_Ioi_apply_eq_zero X hr0 hlt hPQv
  -- `‖Q v‖ ≤ r² ‖v‖`
  have hgram : (⟪Q v, Q v⟫_ℂ) = ⟪X v, X (Q v)⟫_ℂ :=
    ContinuousLinearMap.adjoint_inner_left X (Q v) (X v)
  have hQvsq : ‖Q v‖ ^ 2 ≤ (r * ‖v‖) * (r * ‖Q v‖) := by
    have hre : ‖Q v‖ ^ 2 = RCLike.re ⟪X v, X (Q v)⟫_ℂ := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), hgram]
    rw [hre]
    refine le_trans ((RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)) ?_
    exact mul_le_mul hXv hXQv (norm_nonneg _) (mul_nonneg hr0 (norm_nonneg _))
  have hQvle : ‖Q v‖ ≤ r ^ 2 * ‖v‖ := by
    rcases eq_or_lt_of_le (norm_nonneg (Q v)) with h0 | h0
    · rw [← h0]
      positivity
    · have hmul : ‖Q v‖ * ‖Q v‖ ≤ (r ^ 2 * ‖v‖) * ‖Q v‖ := by
        calc ‖Q v‖ * ‖Q v‖ = ‖Q v‖ ^ 2 := by ring
          _ ≤ (r * ‖v‖) * (r * ‖Q v‖) := hQvsq
          _ = (r ^ 2 * ‖v‖) * ‖Q v‖ := by ring
      exact le_of_mul_le_mul_right hmul h0
  -- `(1 - r²) ‖v‖ ≤ ‖η‖`
  have hinner : RCLike.re ⟪η, v⟫_ℂ = ‖v‖ ^ 2 - ‖X v‖ ^ 2 := by
    rw [hηv]
    have hsplit : ⟪v - Q v, v⟫_ℂ = ⟪v, v⟫_ℂ - ⟪Q v, v⟫_ℂ := by
      rw [inner_sub_left]
    rw [hsplit, map_sub, ← re_inner_gramOperator X v]
    have hvv : RCLike.re (⟪v, v⟫_ℂ) = ‖v‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) v).symm
    rw [hvv]
  have hvη : (1 - r ^ 2) * ‖v‖ ≤ ‖η‖ := by
    rcases eq_or_lt_of_le (norm_nonneg v) with h0 | h0
    · rw [← h0, mul_zero]
      exact norm_nonneg _
    · have hcs : RCLike.re ⟪η, v⟫_ℂ ≤ ‖η‖ * ‖v‖ :=
        le_trans (RCLike.re_le_norm _) (norm_inner_le_norm _ _)
      have hXvsq : ‖X v‖ ^ 2 ≤ r ^ 2 * ‖v‖ ^ 2 := by
        have := mul_self_le_mul_self (norm_nonneg (X v)) hXv
        nlinarith [norm_nonneg (X v)]
      have hchain : (1 - r ^ 2) * ‖v‖ * ‖v‖ ≤ ‖η‖ * ‖v‖ := by
        nlinarith [hinner, hcs, hXvsq]
      exact le_of_mul_le_mul_right hchain h0
  -- combine
  have hden : 0 < 1 - r ^ 2 := by nlinarith
  rw [hQv] at hQvle
  rw [div_mul_eq_mul_div, le_div_iff₀ hden]
  nlinarith [norm_nonneg (T η), norm_nonneg v, hQvle, hvη, sq_nonneg r]

/-- **The approximation numbers of the Gram resolvent.**

If `T = Q + Q T` with `Q = X⋆X` — that is, `T = Q (1 − Q)⁻¹` — and `X` is a strict
contraction, then

`aₙ(T) ≤ aₙ(X)² / (1 − aₙ(X)²)`.

With `X` the directed sine block of a pair of subspaces this reads
`aₙ(tan²Θ) ≤ tan²(arcsin aₙ(sin Θ))`, which is the transfer the Davis--Kahan
ambient tangent theorem needs in order to feed the directed estimate into the
Lemma 6.1 block coupling. -/
theorem approximationNumber_le_of_gramResolvent
    (X : E0 →L[ℂ] E1) {T : E0 →L[ℂ] E0} (hX : ‖X‖ < 1)
    (hT : ∀ y, T y = gramOperator X y + gramOperator X (T y)) (n : ℕ) :
    T.approximationNumber n ≤
      X.approximationNumber n ^ 2 / (1 - X.approximationNumber n ^ 2) := by
  set a : ℝ := X.approximationNumber n with hadef
  have ha0 : 0 ≤ a := X.approximationNumber_nonneg n
  have ha1 : a < 1 := lt_of_le_of_lt (X.approximationNumber_le_norm n) hX
  have key : ∀ r : ℝ, a < r → r < 1 → T.approximationNumber n ≤ r ^ 2 / (1 - r ^ 2) := by
    intro r hr hr1
    have hr0 : 0 ≤ r := ha0.trans hr.le
    obtain ⟨r', hr1', hr2'⟩ := exists_between hr
    have hr'0 : 0 ≤ r' := ha0.trans hr1'.le
    have hsqlt : r' ^ 2 < r ^ 2 := by nlinarith
    set P : E0 →L[ℂ] E0 :=
      (gramSpectralPVM X).proj (Set.Ioi (r' ^ 2)) measurableSet_Ioi with hPdef
    have hrank : P.rank ≤ (n : Cardinal) :=
      rank_gramProjection_Ioi_le_natCast_of_approximationNumber_lt X n hr'0 hr1'
    have hidem : IsIdempotentElem P := (gramSpectralPVM X).proj_idem _ _
    have hsa : IsSelfAdjoint P := (gramSpectralPVM X).isSelfAdjoint_proj _ _
    have hden : 0 < 1 - r ^ 2 := by nlinarith
    refine ContinuousLinearMap.approximationNumber_le_of_spectral_band
      (by positivity) hidem hsa hrank ?_
    intro x
    have hPy : P (x - P x) = 0 := by
      have hPP : P (P x) = P x := by
        have h := congrArg (fun S : E0 →L[ℂ] E0 => S x) hidem
        simpa only [_root_.mul_apply_eq_comp, ContinuousLinearMap.comp_apply] using h
      rw [map_sub, hPP, sub_self]
    exact norm_gramResolvent_apply_le_of_gramProjection_apply_eq_zero X hX hT hr0 hr1
      hsqlt hPy
  by_contra hcon
  have hcon' : a ^ 2 / (1 - a ^ 2) < T.approximationNumber n := lt_of_not_ge hcon
  have hden : (1 : ℝ) - a ^ 2 ≠ 0 := by nlinarith
  have hcont : ContinuousAt (fun u : ℝ => u ^ 2 / (1 - u ^ 2)) a := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · exact hden
  have hev : ∀ᶠ r in nhdsWithin a (Set.Ioi a),
      (fun u : ℝ => u ^ 2 / (1 - u ^ 2)) r < T.approximationNumber n :=
    Filter.Tendsto.eventually_lt_const hcon'
      (hcont.continuousWithinAt (s := Set.Ioi a))
  have hlt1 : ∀ᶠ r in nhdsWithin a (Set.Ioi a), r < 1 :=
    Filter.eventually_iff_exists_mem.mpr
      ⟨Set.Iio 1, nhdsWithin_le_nhds (gt_mem_nhds ha1), fun r hr => hr⟩
  have hgt : ∀ᶠ r in nhdsWithin a (Set.Ioi a), a < r :=
    Filter.eventually_iff_exists_mem.mpr
      ⟨Set.Ioi a, self_mem_nhdsWithin, fun r hr => hr⟩
  obtain ⟨r, ⟨⟨hr1, hr2⟩, hr3⟩⟩ := ((hev.and hlt1).and hgt).exists
  exact absurd (key r hr3 hr2) (not_le.mpr hr1)

end

end ApproximationNumber
end TauCeti
