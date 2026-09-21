/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.GramInverseResolvent
public import LeanPool.DavisKahan.ForTauCeti.Analysis.SpecialFunctions.TanArcsin

/-!
# The tangent of an angle presented by its sine, at the level of singular values

Let `S` be a nonnegative self-adjoint strict contraction — a *sine* — and let `Tg`
be a nonnegative self-adjoint operator satisfying the Pythagorean relation

```
Tg² (1 − S²) = S²,
```

which is `tan² θ · cos² θ = sin² θ` written for operators.  Then `Tg` is *the*
tangent of the angle `S` presents, singular value by singular value:

```
aₙ(Tg) = tan (arcsin aₙ(S))   for every n.
```

## Why this is the theorem a tangent statement needs

Davis and Kahan write `‖tan Θ‖`, a norm of the sequence `tan θ₁, tan θ₂, …` of
tangents of the principal angles.  A statement about an *operator* `tan Θ` is
weaker than that unless one knows the operator's singular values are exactly
those tangents — and an existentially quantified operator "whose singular values
happen to be the tangents" says nothing at all when no such operator exists.

The relation above is the only input: it is a `cfc`-free identity, it holds for
the ambient tangent of a pair of subspaces and for the doubled angle alike, and
it fixes `Tg` up to nothing.  In particular no functional calculus, no spectral
mapping theorem, and no operator monotonicity is used.

## The proof

Both inequalities are Möbius transfers of approximation numbers along
`u ↦ u/(1−u)` and its inverse `u ↦ u/(1+u)`:

* `aₙ(Tg)² = aₙ(Tg²) ≤ aₙ(S)²/(1 − aₙ(S)²)` by `approximationNumber_le_of_gramResolvent`,
  because `Tg² = S² + S² Tg²`;
* `aₙ(S)² = aₙ(S²) ≤ aₙ(Tg)²/(1 + aₙ(Tg)²)` by `approximationNumber_le_of_gramContraction`,
  because `S² = Tg² − Tg² S²`.

The second is the same statement as the first read backwards, which is why the
identity needs no extra theory: the *reverse* direction of a monotone transfer is
the *forward* direction of the inverse transfer.

Self-adjointness enters once, to commute `S²` past `Tg²`: taking adjoints in
`Tg² = S² + Tg² S²` gives `Tg² = S² + S² Tg²`, which is the orientation the Gram
resolvent estimate consumes.

## Main results

* `TauCeti.ApproximationNumber.approximationNumber_eq_tanArcsin_of_gramMoebius` —
  the rectangular form, for corners.
* `TauCeti.ApproximationNumber.approximationNumber_eq_tanArcsin` — the
  self-adjoint endomorphism form.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`; it has had no prior home.
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and `ForTauCeti`.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation. III*,
  SIAM J. Numer. Anal. 7 (1970), 1--46, Section 2: the `tan Θ` and `tan 2Θ`
  theorems.
-/

public section

open scoped InnerProductSpace

namespace TauCeti
namespace ApproximationNumber

noncomputable section

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

section Moebius

variable {E₀ E₁ E₂ : Type v}
  [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀] [CompleteSpace E₀]
  [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℂ E₂] [CompleteSpace E₂]

/-- **The Gram Möbius relation determines the tangent's approximation numbers,
for rectangular maps.**

If `X` is a strict contraction and the Gram operators of `X` and `T` satisfy

`T⋆T = X⋆X + X⋆X · T⋆T`,

then `aₙ(T) = tan (arcsin aₙ(X))` for every `n`.  Neither `X` nor `T` need be an
endomorphism, and no relation between their codomains is assumed: everything
happens in the common domain, where both Gram operators live.

This is the shape a *corner* satisfies.  The sine and tangent corners of a
reducing reflection are maps `U → Uᗮ`, so the endomorphism form below does not
apply to them, while this does. -/
theorem approximationNumber_eq_tanArcsin_of_gramMoebius
    (X : E₀ →L[ℂ] E₁) (T : E₀ →L[ℂ] E₂) (hX : ‖X‖ < 1)
    (hmoebius : ∀ y,
      gramOperator T y = gramOperator X y + gramOperator X (gramOperator T y))
    (n : ℕ) :
    T.approximationNumber n = Real.tan (Real.arcsin (X.approximationNumber n)) := by
  set s : ℝ := X.approximationNumber n with hsdef
  set t : ℝ := T.approximationNumber n with htdef
  have hs0 : 0 ≤ s := X.approximationNumber_nonneg n
  have ht0 : 0 ≤ t := T.approximationNumber_nonneg n
  have hs1 : s < 1 := lt_of_le_of_lt (X.approximationNumber_le_norm n) hX
  have hden : (0 : ℝ) < 1 - s ^ 2 := by nlinarith
  -- the adjoint orientation: `Q = P + Q · P`, hence `P = Q − Q · P`
  have hop : gramOperator T = gramOperator X + gramOperator X * gramOperator T := by
    ext y
    simpa only [_root_.add_apply, _root_.mul_apply_eq_comp,
      ContinuousLinearMap.comp_apply] using hmoebius y
  have hswap : gramOperator T = gramOperator X + gramOperator T * gramOperator X := by
    have hstar := congrArg (star : (E₀ →L[ℂ] E₀) → (E₀ →L[ℂ] E₀)) hop
    simpa only [star_add, star_mul, (gramOperator_isSelfAdjoint X).star_eq,
      (gramOperator_isSelfAdjoint T).star_eq] using hstar
  -- forward transfer: `aₙ(T)² ≤ s²/(1 − s²)`
  have hfwd : t ^ 2 ≤ s ^ 2 / (1 - s ^ 2) := by
    have h := approximationNumber_le_of_gramResolvent X (T := gramOperator T) hX
      hmoebius n
    rwa [approximationNumber_gramOperator_complex T n] at h
  -- reverse transfer: `s² ≤ aₙ(T)²/(1 + aₙ(T)²)`
  have hrev : s ^ 2 ≤ t ^ 2 / (1 + t ^ 2) := by
    have hQ : ∀ y, gramOperator X y =
        gramOperator T y - gramOperator T (gramOperator X y) := by
      intro y
      have hQop : gramOperator X = gramOperator T - gramOperator T * gramOperator X :=
        eq_sub_iff_add_eq.mpr hswap.symm
      have h := congrArg (fun A : E₀ →L[ℂ] E₀ => A y) hQop
      simpa only [_root_.mul_apply_eq_comp, ContinuousLinearMap.comp_apply,
        _root_.sub_apply] using h
    have h := approximationNumber_le_of_gramContraction T (Q := gramOperator X) hQ n
    rwa [approximationNumber_gramOperator_complex X n] at h
  -- the scalar identity `tan (arcsin s)² = s²/(1 − s²)`
  have hsqrt : Real.sqrt (1 - s ^ 2) * Real.sqrt (1 - s ^ 2) = 1 - s ^ 2 :=
    Real.mul_self_sqrt hden.le
  have htanSq : Real.tan (Real.arcsin s) ^ 2 = s ^ 2 / (1 - s ^ 2) := by
    rw [Real.tan_arcsin, div_pow]
    congr 1
    nlinarith [hsqrt]
  have htanNonneg : 0 ≤ Real.tan (Real.arcsin s) := TanArcsin.tanArcsin_nonneg hs0
  refine le_antisymm ?_ ?_
  · have hle : t ^ 2 ≤ Real.tan (Real.arcsin s) ^ 2 := by rw [htanSq]; exact hfwd
    exact (sq_le_sq₀ ht0 htanNonneg).1 hle
  · have hstep : s ^ 2 / (1 - s ^ 2) ≤ t ^ 2 := by
      have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
      rw [le_div_iff₀ hpos] at hrev
      rw [div_le_iff₀ hden]
      nlinarith
    have hle : Real.tan (Real.arcsin s) ^ 2 ≤ t ^ 2 := by rw [htanSq]; exact hstep
    exact (sq_le_sq₀ htanNonneg ht0).1 hle

end Moebius

/-- The Gram operator of a self-adjoint operator is its square. -/
theorem gramOperator_of_isSelfAdjoint {S : E →L[ℂ] E} (hS : IsSelfAdjoint S) :
    gramOperator S = S * S := by
  rw [gramOperator, ContinuousLinearMap.isSelfAdjoint_iff'.mp hS]
  rfl

/-- **The Pythagorean relation determines the tangent's approximation numbers.**

If `S` is a self-adjoint strict contraction, `Tg` is self-adjoint, and

`Tg² = S² + Tg² S²`  (equivalently `Tg² (1 − S²) = S²`),

then `aₙ(Tg) = tan (arcsin aₙ(S))` for every `n`.  The endomorphism case of
`approximationNumber_eq_tanArcsin_of_gramMoebius`: self-adjointness makes each
Gram operator the square, and the Möbius relation is the Pythagorean one. -/
theorem approximationNumber_eq_tanArcsin
    {S Tg : E →L[ℂ] E} (hS : IsSelfAdjoint S) (hTg : IsSelfAdjoint Tg)
    (hSlt : ‖S‖ < 1)
    (hrel : Tg * Tg = S * S + Tg * Tg * (S * S)) (n : ℕ) :
    Tg.approximationNumber n = Real.tan (Real.arcsin (S.approximationNumber n)) := by
  refine approximationNumber_eq_tanArcsin_of_gramMoebius S Tg hSlt (fun y => ?_) n
  have hgS : gramOperator S = S * S := gramOperator_of_isSelfAdjoint hS
  have hgT : gramOperator Tg = Tg * Tg := gramOperator_of_isSelfAdjoint hTg
  have hswap : Tg * Tg = S * S + (S * S) * (Tg * Tg) := by
    have hstar := congrArg (star : (E →L[ℂ] E) → (E →L[ℂ] E)) hrel
    simp only [star_add, star_mul, hS.star_eq, hTg.star_eq] at hstar
    exact hstar
  rw [hgS, hgT]
  have h := congrArg (fun A : E →L[ℂ] E => A y) hswap
  simpa only [_root_.mul_apply_eq_comp, ContinuousLinearMap.comp_apply,
    _root_.add_apply] using h

end

end ApproximationNumber
end TauCeti
