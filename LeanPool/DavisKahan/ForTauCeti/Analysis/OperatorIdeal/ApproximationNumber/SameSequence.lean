/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.OperatorModulus
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.FiniteRestriction
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.KyFan
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.ScalarTransport

/-!
# Operators with the same approximation-number sequence

Two bounded operators, possibly between different pairs of Hilbert spaces, **have the same
approximation numbers** when their whole sequences agree:

```
A.HasSameApproximationNumbers B ↔ ∀ n, A.approximationNumber n = B.approximationNumber n.
```

Since every unitarily invariant norm is a function of that sequence, this is the exact
hypothesis under which two operators are interchangeable for ideal-theoretic purposes, and
it is the relation the Davis--Kahan sine-theta development uses literally.

The relation is deliberately *heterogeneous* — the four spaces are independent — because its
uses compare an operator with a transported copy of itself living somewhere else.  That is
also why it is stated as a plain `Prop` rather than a `Setoid`: it is reflexive, symmetric
and transitive, but not on a single type.

Completeness of the four spaces is *not* assumed: approximation numbers are defined for
bounded operators between normed spaces, and nothing here needs more.  The source relation
carried the hypothesis, so this is a small generalisation.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `DavisKahan/Sources/DavisKahan1970/SineTheta/Norms/SingularValueTransport.lean`.
* Original declarations: `TauCeti.DavisKahan.Experimental.ExactSinTheta.{`
  `SameApproximationSingularSequence, SameApproximationSingularSequence.refl,`
  `SameApproximationSingularSequence.symm, SameApproximationSingularSequence.trans,`
  `SameApproximationSingularSequence.opNorm_eq,`
  `SameApproximationSingularSequence.kyFanApproximationGauge_eq}`.
* Original authors / copyright: Jon Crall, OpenAI GPT-5.6 Thinking; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Extraction class: **copied and renamespaced**.  The relation moves to
  `ContinuousLinearMap.HasSameApproximationNumbers` and is spelled with
  `approximationNumber` rather than its `approximationSingularValue` alias.
* Extraction motive: `DavisKahan/OperatorIdeal/ApproximationNumbers/BlockSum.lean` — a
  *generic* module — imported the source-layer file above for these six declarations alone.
  That backwards dependency was the last obstacle recorded against extraction cluster 1b.
* Spectra influence: none.
-/

public section

namespace ContinuousLinearMap

universe u v₁ w₁ v₂ w₂ v₃ w₃

variable {𝕜 : Type u} [RCLike 𝕜]
  {E₁ : Type v₁} {F₁ : Type w₁} {E₂ : Type v₂} {F₂ : Type w₂} {E₃ : Type v₃} {F₃ : Type w₃}
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
  [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]
  [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
  [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂]
  [NormedAddCommGroup E₃] [InnerProductSpace 𝕜 E₃]
  [NormedAddCommGroup F₃] [InnerProductSpace 𝕜 F₃]

/-- `A` and `B` have the same complete approximation-number sequence. -/
def HasSameApproximationNumbers (A : E₁ →L[𝕜] F₁) (B : E₂ →L[𝕜] F₂) : Prop :=
  ∀ n : ℕ, A.approximationNumber n = B.approximationNumber n

/-- Unfolding lemma for `ContinuousLinearMap.HasSameApproximationNumbers`.  The definition is
not exposed, so this is how a downstream module both introduces the relation and reads an
individual index out of it. -/
theorem hasSameApproximationNumbers_iff (A : E₁ →L[𝕜] F₁) (B : E₂ →L[𝕜] F₂) :
    A.HasSameApproximationNumbers B ↔
      ∀ n : ℕ, A.approximationNumber n = B.approximationNumber n :=
  Iff.rfl

namespace HasSameApproximationNumbers

/-- Having the same approximation numbers is reflexive. -/
@[refl] theorem refl (A : E₁ →L[𝕜] F₁) : A.HasSameApproximationNumbers A := fun _ => rfl

/-- Having the same approximation numbers is symmetric. -/
theorem symm {A : E₁ →L[𝕜] F₁} {B : E₂ →L[𝕜] F₂}
    (h : A.HasSameApproximationNumbers B) : B.HasSameApproximationNumbers A :=
  fun n => (h n).symm

/-- Having the same approximation numbers is transitive.  With `refl` and `symm` it is an
equivalence, which is what lets it be used to transport ideal membership. -/
theorem trans {A : E₁ →L[𝕜] F₁} {B : E₂ →L[𝕜] F₂} {C : E₃ →L[𝕜] F₃}
    (hAB : A.HasSameApproximationNumbers B) (hBC : B.HasSameApproximationNumbers C) :
    A.HasSameApproximationNumbers C :=
  fun n => (hAB n).trans (hBC n)

/-- Equal approximation numbers give equal operator norms: they agree already at `n = 0`. -/
theorem norm_eq {A : E₁ →L[𝕜] F₁} {B : E₂ →L[𝕜] F₂}
    (h : A.HasSameApproximationNumbers B) : ‖A‖ = ‖B‖ := by
  rw [← A.approximationNumber_index_zero, ← B.approximationNumber_index_zero, h 0]

/-- Equal approximation numbers give equal Ky Fan gauges. -/
theorem kyFanGauge_eq {A : E₁ →L[𝕜] F₁} {B : E₂ →L[𝕜] F₂}
    (h : A.HasSameApproximationNumbers B) (k : ℕ) :
    A.kyFanGauge k = B.kyFanGauge k :=
  Finset.sum_congr rfl fun n _ => h n

end HasSameApproximationNumbers

section MinMax

/-! ## Comparison through the min--max characterisation

These three were stated over `ℂ` until 2026-09-03, because the min--max lower bound they use
was available only there.  `ContinuousLinearMap.hasMinMaxLowerBound_rclike` proves it
at every `RCLike` field, so they are stated at every `RCLike` field, and no capability class
appears in any signature.  It is used in its *theorem* form rather than through the
`HasMinMaxLowerBoundEverywhere` class because that class fixes one universe for both spaces
and these statements are genuinely rectangular. -/

variable {X : Type v₁} {Y : Type w₁} {Z : Type w₂}
  [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y] [CompleteSpace Y]
  [NormedAddCommGroup Z] [InnerProductSpace 𝕜 Z] [CompleteSpace Z]

/-- **A pointwise norm bound is inherited by every approximation number.**

The proof is the min--max characterisation used twice: a strict lower bound for `aₙ A` is
realized as a uniform lower modulus on an `(n+1)`-dimensional subspace, and the pointwise
estimate carries that same witness over to `B`.  It is rank-safe — no averaging of `A`
against a second operator happens, so no rank doubling can occur. -/
theorem approximationNumber_le_of_norm_apply_le
    (A : X →L[𝕜] Y) (B : X →L[𝕜] Z) (h : ∀ x : X, ‖A x‖ ≤ ‖B x‖) (n : ℕ) :
    A.approximationNumber n ≤ B.approximationNumber n := by
  by_contra hnot
  have hlt : B.approximationNumber n < A.approximationNumber n := lt_of_not_ge hnot
  have hB0 : 0 ≤ B.approximationNumber n := B.approximationNumber_nonneg n
  have hmm : HasMinMaxLowerBound 𝕜 X Y := ContinuousLinearMap.hasMinMaxLowerBound_rclike 𝕜
  have hmm' : HasMinMaxLowerBound 𝕜 X Z := ContinuousLinearMap.hasMinMaxLowerBound_rclike 𝕜
  obtain ⟨s, hrs, v, hv, hV⟩ :=
    (hmm.lt_approximationNumber_iff_exists_finiteDimensional_lowerBound A n hB0).mp hlt
  exact lt_irrefl _
    ((hmm'.lt_approximationNumber_iff_exists_finiteDimensional_lowerBound B n hB0).mpr
      ⟨s, hrs, v, hv, fun x hx => (hV x hx).trans (h x)⟩)

/-- Pointwise equality of norms determines the whole approximation-number sequence.  The two
operators may have different targets, which is what the heterogeneous relation is for. -/
theorem hasSameApproximationNumbers_of_norm_apply_eq
    (A : X →L[𝕜] Y) (B : X →L[𝕜] Z) (h : ∀ x : X, ‖A x‖ = ‖B x‖) :
    A.HasSameApproximationNumbers B := fun n =>
  le_antisymm
    (approximationNumber_le_of_norm_apply_le A B (fun x => (h x).le) n)
    (approximationNumber_le_of_norm_apply_le B A (fun x => (h x).ge) n)

/-- **An operator and its modulus have the same approximation numbers.**  The modulus acts
on the source while the operator maps into the target, so this is genuinely the
heterogeneous relation.

Stated over `ℂ`, unlike the two above: the modulus needs a real functional calculus on the
operator algebra, which at an abstract `RCLike` field is available only under the local
instances of `ForTauCeti/Analysis/InnerProductSpace/OperatorRealAlgebra.lean`.  The general
statement is `TauCeti.DavisKahan.Angle.modulus_hasSameApproximationNumbers_rclike`, which
activates them. -/
theorem modulus_hasSameApproximationNumbers {Y' : Type w₁}
    [NormedAddCommGroup Y'] [InnerProductSpace ℂ Y'] [CompleteSpace Y']
    {X' : Type v₁} [NormedAddCommGroup X'] [InnerProductSpace ℂ X'] [CompleteSpace X']
    (T : X' →L[ℂ] Y') :
    T.modulus.HasSameApproximationNumbers T :=
  hasSameApproximationNumbers_of_norm_apply_eq _ _ T.norm_modulus_apply

end MinMax

end ContinuousLinearMap
