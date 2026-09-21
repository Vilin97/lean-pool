/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.MinMaxUpper

/-!
# Finite-dimensional localization of approximation numbers

The `n`th approximation number of a bounded operator between Hilbert spaces is already
determined by the restrictions of the operator to `(n+1)`-generated subspaces of its source:

```
aₙ(T) = sSup { aₙ (T ∘L (span {v 0, …, v n}).subtypeL) | v : Fin (n + 1) → E }.
```

The supremum is a genuine least upper bound (`approximationNumber_isLUB_finiteRestrictions`),
not merely a bound, and the family is indexed by *all* families of `n + 1` vectors —
linearly dependent ones are harmless, contributing restrictions to smaller subspaces.

## Main results

* `ContinuousLinearMap.approximationNumber_comp_subtypeL_le`: restricting the source cannot
  increase an approximation number.  Stated for a general `RCLike` field;
* `ContinuousLinearMap.exists_finiteRestrictionApproximationNumber_gt_of_lt`: every strict
  lower bound is exceeded by one of the restrictions;
* `ContinuousLinearMap.approximationNumber_isLUB_finiteRestrictions`: the two together;
* `ContinuousLinearMap.lt_approximationNumber_iff_exists_finiteDimensional_lowerBound`: the
  epsilon form of the min--max characterisation, packaging
  `ContinuousLinearMap.exists_linearIndependent_lowerBound_of_lt_approximationNumber_complex` with
  its converse `ContinuousLinearMap.le_approximationNumber_of_linearIndependent` into an
  `Iff`.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `DavisKahan/Interop/Spectra/ApproximationNumberMinMax.lean`.
* Original declarations: `TauCeti.DavisKahan.Experimental.{`
  `approximationNumber_comp_subtypeL_le, finiteRestrictionApproximationNumbers,`
  `finiteRestrictionApproximationNumbers_upperBound,`
  `exists_finiteRestrictionApproximationNumber_gt_of_lt,`
  `approximationNumber_isLUB_finiteRestrictions,`
  `lt_approximationNumber_iff_exists_finiteDimensional_lowerBound}`.
* Original authors / copyright: Jon Crall, OpenAI GPT-5.6 Thinking; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Extraction class: **copied and renamespaced**.  The statements are unchanged apart from
  the generalisation of `approximationNumber_comp_subtypeL_le` to an arbitrary `RCLike`
  field; the declarations move from `TauCeti.DavisKahan.Experimental` to
  `ContinuousLinearMap`, so that dot notation resolves.
* Spectra influence: **none**.  The module was under `DavisKahan/Interop/Spectra/` because
  its threshold theorem was once proved from `vendor/Spectra`'s projection-valued measures.
  That proof was replaced on 2026-07-28 by
  `ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMaxUpper.lean`, after which
  nothing here touched Spectra and the module belonged in the staging layer.
-/

public section

namespace ContinuousLinearMap

open scoped InnerProductSpace

noncomputable section

universe u v w

section Restriction

variable {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Restriction to a subspace cannot increase an approximation number. -/
theorem approximationNumber_comp_subtypeL_le
    (T : E →L[𝕜] F) (n : ℕ) (V : Submodule 𝕜 E) :
    (T ∘L V.subtypeL).approximationNumber n ≤ T.approximationNumber n := by
  have h := T.approximationNumber_comp_le_mul_norm V.subtypeL n
  have hsub : ‖V.subtypeL‖ ≤ (1 : ℝ) := V.norm_subtypeL_le
  calc
    (T ∘L V.subtypeL).approximationNumber n
        ≤ T.approximationNumber n * ‖V.subtypeL‖ := h
    _ ≤ T.approximationNumber n * 1 :=
      mul_le_mul_of_nonneg_left hsub (T.approximationNumber_nonneg n)
    _ = T.approximationNumber n := by rw [mul_one]

/-- The approximation numbers of the restrictions of `T` to the spans of `n + 1` vectors.

Linearly dependent families are deliberately not excluded: they merely contribute
restrictions to subspaces of smaller dimension, which the supremum ignores. -/
def finiteRestrictionApproximationNumbers (T : E →L[𝕜] F) (n : ℕ) : Set ℝ :=
  Set.range fun v : Fin (n + 1) → E =>
    (T ∘L (Submodule.span 𝕜 (Set.range v)).subtypeL).approximationNumber n

/-- The ambient approximation number bounds every finite restriction. -/
theorem finiteRestrictionApproximationNumbers_upperBound (T : E →L[𝕜] F) (n : ℕ) :
    T.approximationNumber n ∈ upperBounds (T.finiteRestrictionApproximationNumbers n) := by
  rintro _ ⟨v, rfl⟩
  exact T.approximationNumber_comp_subtypeL_le n (Submodule.span 𝕜 (Set.range v))

/-- **The min--max lower-bound property** for a pair of Hilbert spaces over `𝕜`: strictly
below every approximation number of every `T : E →L[𝕜] F` there is a strictly larger uniform
lower modulus, attained on the span of `n + 1` independent vectors.

This is the *only* input to the approximation-number localization theory that depends on the
scalar field.  Over `ℂ` it is the min--max theorem
`ContinuousLinearMap.exists_linearIndependent_lowerBound_of_lt_approximationNumber_complex`, proved
from the continuous functional calculus on `T.modulus`; over `ℝ`, where that calculus is not
available for operators on the space itself, it is transported through the complexification.
Everything downstream — the finite-restriction localization, the least-upper-bound
characterisation, and through them the Ky Fan triangle inequality — is stated once against
this predicate rather than twice, once per field. -/
@[expose]
def HasMinMaxLowerBound (𝕜 : Type u) [RCLike 𝕜] (E : Type v) (F : Type w)
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] : Prop :=
  ∀ (T : E →L[𝕜] F) (n : ℕ) {r : ℝ}, 0 ≤ r → r < T.approximationNumber n →
    ∃ s : ℝ, r < s ∧ ∃ v : Fin (n + 1) → E, LinearIndependent 𝕜 v ∧
      ∀ x ∈ Submodule.span 𝕜 (Set.range v), s * ‖x‖ ≤ ‖T x‖

namespace HasMinMaxLowerBound

/-- Every strict lower threshold for the ambient approximation number is exceeded by an
approximation number of an `(n+1)`-generated restriction. -/
theorem exists_finiteRestrictionApproximationNumber_gt_of_lt
    (h : HasMinMaxLowerBound 𝕜 E F) (T : E →L[𝕜] F) (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r < T.approximationNumber n) :
    ∃ v : Fin (n + 1) → E,
      r < (T ∘L (Submodule.span 𝕜 (Set.range v)).subtypeL).approximationNumber n := by
  obtain ⟨s, hrs, v, hv, hV⟩ := h T n hr0 hr
  let V : Submodule 𝕜 E := Submodule.span 𝕜 (Set.range v)
  let b : Module.Basis (Fin (n + 1)) 𝕜 V := Module.Basis.span hv
  let w : Fin (n + 1) → V := fun i => b i
  have hw : LinearIndependent 𝕜 w := by
    simpa only [w] using b.linearIndependent
  have hsNN : s ≤ (T ∘L V.subtypeL).approximationNumber n := by
    apply ContinuousLinearMap.le_approximationNumber_of_linearIndependent
      (T ∘L V.subtypeL) n w hw
    intro x _ hxNorm
    have hxV : ((x : V) : E) ∈ V := x.property
    have hxNormE : ‖((x : V) : E)‖ = 1 := by simpa using hxNorm
    -- names the application so the norm bound applies to it directly.
    change s ≤ ‖T ((x : V) : E)‖
    calc
      s = s * ‖((x : V) : E)‖ := by rw [hxNormE, mul_one]
      _ ≤ ‖T ((x : V) : E)‖ := hV ((x : V) : E) hxV
  exact ⟨v, by simpa only [V] using hrs.trans_le hsNN⟩

/-- **Exact finite-dimensional localization.**  The ambient approximation number is the
least upper bound of the approximation numbers of the restrictions to spans of `n + 1`
vectors.

Approximation numbers are real-valued, so `IsLUB` is the conditionally-complete
formulation appropriate to `ℝ`; the family is nonempty and bounded above by the ambient
approximation number. -/
theorem approximationNumber_isLUB_finiteRestrictions
    (h : HasMinMaxLowerBound 𝕜 E F) (T : E →L[𝕜] F) (n : ℕ) :
    IsLUB (T.finiteRestrictionApproximationNumbers n) (T.approximationNumber n) := by
  refine ⟨T.finiteRestrictionApproximationNumbers_upperBound n, ?_⟩
  intro b hb
  -- Every upper bound of a nonempty family of nonnegative reals is nonnegative.
  have hb0 : 0 ≤ b :=
    (ContinuousLinearMap.approximationNumber_nonneg _ n).trans (hb ⟨fun _ => 0, rfl⟩)
  by_contra hnot
  obtain ⟨v, hv⟩ :=
    h.exists_finiteRestrictionApproximationNumber_gt_of_lt T n hb0 (lt_of_not_ge hnot)
  exact (not_le_of_gt hv) (hb ⟨v, rfl⟩)

/-- **Epsilon form of the min--max characterisation.**  `r` is strictly below `aₙ(T)`
exactly when `T` has a strictly larger uniform lower modulus on some `(n+1)`-dimensional
subspace.

The forward direction is the hypothesis and the reverse is
`ContinuousLinearMap.le_approximationNumber_of_linearIndependent`, so this is the statement
in which both halves of the min--max theorem appear together. -/
theorem lt_approximationNumber_iff_exists_finiteDimensional_lowerBound
    (h : HasMinMaxLowerBound 𝕜 E F) (T : E →L[𝕜] F) (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r) :
    r < T.approximationNumber n ↔
      ∃ s : ℝ, r < s ∧
        ∃ v : Fin (n + 1) → E, LinearIndependent 𝕜 v ∧
          ∀ x ∈ Submodule.span 𝕜 (Set.range v), s * ‖x‖ ≤ ‖T x‖ := by
  refine ⟨h T n hr0, ?_⟩
  rintro ⟨s, hrs, v, hv, hV⟩
  refine hrs.trans_le ?_
  apply ContinuousLinearMap.le_approximationNumber_of_linearIndependent T n v hv
  intro x hxV hxNorm
  calc
    s = s * ‖x‖ := by rw [hxNorm, mul_one]
    _ ≤ ‖T x‖ := hV x hxV

/-- Every positive tolerance admits a finite source restriction whose approximation number
is within that tolerance of the ambient one.  This is the exact hypothesis
`ContinuousLinearMap.kyFanGauge_add_le_of_exists_finiteRestriction` consumes, so it is the
last step before the Ky Fan triangle inequality holds over any field with a min--max lower
bound rather than over `ℂ` alone. -/
theorem exists_finiteRestrictionApproximationNumber_add_gt
    (h : HasMinMaxLowerBound 𝕜 E F) (T : E →L[𝕜] F) (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : Fin (n + 1) → E,
      T.approximationNumber n <
        (T ∘L (Submodule.span 𝕜 (Set.range v)).subtypeL).approximationNumber n + ε := by
  by_cases hsmall : T.approximationNumber n < ε
  · exact ⟨fun _ => 0, hsmall.trans_le
      (le_add_of_nonneg_left (ContinuousLinearMap.approximationNumber_nonneg _ _))⟩
  · have hεle : ε ≤ T.approximationNumber n := le_of_not_gt hsmall
    obtain ⟨v, hv⟩ := h.exists_finiteRestrictionApproximationNumber_gt_of_lt T n
      (sub_nonneg.mpr hεle) (sub_lt_self _ hε)
    exact ⟨v, by linarith⟩

end HasMinMaxLowerBound

/-- **The min--max lower bound, as a property of the scalar field alone.**

`HasMinMaxLowerBound` is a statement about one *pair* of spaces.  An operator ideal family,
by contrast, has to supply its laws for every pair at once, so it cannot take that predicate
as an argument — it needs the field to satisfy it uniformly.  This class is that
quantification and nothing more.

Both fields are instances: `hasMinMaxLowerBoundEverywhere_complex` from the functional
calculus, `TauCeti.ApproximationNumber.hasMinMaxLowerBoundEverywhere_real` by
complexification.  Together they are what lets the trace-class family be built once over
`RCLike 𝕜` rather than once per field.

Note what it does *not* assume: the Ky Fan triangle inequality itself.  Assuming that would
be assuming a theorem, and this class is one layer below it — the inequality is derived, in
`ContinuousLinearMap.kyFanGauge_add_le_of_hasMinMaxLowerBound`. -/
class HasMinMaxLowerBoundEverywhere (𝕜 : Type u) [RCLike 𝕜] : Prop where
  out : ∀ {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F],
    HasMinMaxLowerBound 𝕜 E F

end Restriction

section Complex

variable {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Over `ℂ` the min--max lower-bound property is the min--max theorem itself. -/
theorem hasMinMaxLowerBound_complex : HasMinMaxLowerBound ℂ E F :=
  fun T n _ hr0 hr =>
    T.exists_linearIndependent_lowerBound_of_lt_approximationNumber_complex n hr0 hr

/-- Every strict lower threshold for the ambient approximation number is exceeded by an
approximation number of an `(n+1)`-generated restriction. -/
theorem exists_finiteRestrictionApproximationNumber_gt_of_lt
    (T : E →L[ℂ] F) (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r < T.approximationNumber n) :
    ∃ v : Fin (n + 1) → E,
      r < (T ∘L (Submodule.span ℂ (Set.range v)).subtypeL).approximationNumber n :=
  hasMinMaxLowerBound_complex.exists_finiteRestrictionApproximationNumber_gt_of_lt T n hr0 hr

/-- **Exact finite-dimensional localization** over `ℂ`. -/
theorem approximationNumber_isLUB_finiteRestrictions (T : E →L[ℂ] F) (n : ℕ) :
    IsLUB (T.finiteRestrictionApproximationNumbers n) (T.approximationNumber n) :=
  hasMinMaxLowerBound_complex.approximationNumber_isLUB_finiteRestrictions T n

/-- **Epsilon form of the min--max characterisation** over `ℂ`. -/
theorem lt_approximationNumber_iff_exists_finiteDimensional_lowerBound
    (T : E →L[ℂ] F) (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r) :
    r < T.approximationNumber n ↔
      ∃ s : ℝ, r < s ∧
        ∃ v : Fin (n + 1) → E, LinearIndependent ℂ v ∧
          ∀ x ∈ Submodule.span ℂ (Set.range v), s * ‖x‖ ≤ ‖T x‖ :=
  hasMinMaxLowerBound_complex.lt_approximationNumber_iff_exists_finiteDimensional_lowerBound
    T n hr0

/-- `ℂ` has the min--max lower bound for every pair of Hilbert spaces. -/
instance hasMinMaxLowerBoundEverywhere_complex :
    HasMinMaxLowerBoundEverywhere.{0, v} ℂ where
  out := hasMinMaxLowerBound_complex

end Complex

end

end ContinuousLinearMap
