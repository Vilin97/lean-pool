/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.DavisKahan.TanTheta.Theorem63UnboundedInfiniteTrial
public import LeanPool.DavisKahan.DavisKahan.TanTheta.RitzPair
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.DirectedUnboundedReal
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.UnboundedCompressionReal
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.UnitaryInvariantNorm
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SymmetricNormingFanDominance

/-! # Tan Theta Directed Unbounded -/

@[expose] public section

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan 1970, the Section 2 `tan Θ` DIRECTED clause, at the source norm

The Section 2 tangent theorem has two printed conclusions:

```text
directed:  δ ‖tan Θ₀‖ ≤ ‖R‖
ambient:   δ ‖tan Θ‖  ≤ ‖H‖
```

The ambient clause is `tanTheta_ambient_unboundedRitz_symmetricNorming_complex` and its
real sibling.  This module supplies the **directed** clause at the same scope: an
unbounded self-adjoint ambient operator, an arbitrary complete trial subspace,
the source residual on the right-hand side, and an arbitrary
`SymmetricNormingFunction`.

## Why this was missing

The mathematics was already here.  `theorem6_3_unbounded_infiniteTrial_ideal` and
its real sibling prove exactly this estimate for every Ky-Fan-dominant ideal
family, with an unbounded `A : H →ₗ.[𝕜] H` and the residual `D.residual` on the
right.  What did not exist was the promotion to the paper's universal norm
quantifier, and the result inventory had registered in its place two declarations
that do not carry the scope they were credited with:

* `theorem6_3_perturbation_infiniteTrial` -- a **bounded** ambient
  operator (`T E : H →L[ℂ] H`) at a Ky Fan family;
* `partIII_tanTheta_ritzResidual_uiNorm` -- **finite-dimensional**
  (`[FiniteDimensional 𝕜 E]`, `[FiniteDimensional 𝕜 F]`) at a rectangular
  seminorm.

Both remain useful and remain registered as supporting evidence; neither
establishes the directed clause at the printed scope.

## The one structural point

The Ky-Fan-level theorem also has an existential form producing a tangent
representative.  That form cannot be promoted: the promotion evaluates the
estimate at every Ky Fan index, and an existential would return a possibly
different witness each time.  The representative is therefore a **parameter**
here, characterized by the paper's own instruction that its approximation numbers
be `tan θ_j` -- `HasTheorem63DirectedTangentApproximationNumbersInfinite`.  That
is the source's own way of saying what `tan Θ₀` is, and it makes the statement
independent of which representative a caller holds.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46: the Section 2 `tan Θ` theorem and
  Theorem 6.3.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.DavisKahan.TanTheta

noncomputable section

universe v

/-! ## Over a complex Hilbert space -/

section Complex

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Davis--Kahan 1970, the Section 2 `tan Θ` directed clause, over `ℂ`, at every
source unitarily invariant norm.**

`δ N(tan Θ₀) ≤ N(R)`, with `R` the trial residual, for an unbounded self-adjoint
ambient operator, an arbitrary complete trial subspace, arbitrary Hilbert
dimension, and an arbitrary `SymmetricNormingFunction`.

The gap is the source's ordered configuration: the trial compression is bounded
above by `α` in form and `A` has no spectrum in `(α, α + δ)`, so the exact space
is the spectral subspace for `(-∞, α]`.  Both separating intervals are
half-infinite, which is the scope the source states for this theorem. -/
theorem tanTheta_directed_unboundedTrial_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    {Z : Submodule ℂ H} [Z.HasOrthogonalProjection] [CompleteSpace Z]
    (D : TanTheta.BoundedCompressionTrialBlock A Z)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hgap : TauCeti.LinearPMap.specProjection hA (Set.Ioo alpha (alpha + delta))
      measurableSet_Ioo = 0)
    (hCompression : ∀ z : Z,
      RCLike.re ⟪D.operator z, z⟫_ℂ ≤ alpha * ‖z‖ ^ 2)
    (tanTheta0 : Z →L[ℂ] H)
    (htan : HasTheorem63DirectedTangentApproximationNumbersInfinite Z
      (selfAdjointSpectralSubspace A hA (Set.Iic alpha) measurableSet_Iic) tanTheta0)
    (hResidual : N.Mem D.residual) :
    N.Mem tanTheta0 ∧
      delta * N.gauge tanTheta0 ≤ N.gauge D.residual := by
  apply N.mul_gauge_le_of_all_mul_kyFan_le hdelta hResidual
  intro k
  by_cases hk : k = 0
  · subst hk
    simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have h := theorem6_3_unbounded_infiniteTrial_ideal
      (KyFanDominantIdealFamily.kyFan (𝕜 := ℂ) k hkpos) A hA D hdelta hgap
      hCompression tanTheta0 htan
      (KyFanDominantIdealFamily.kyFan_mem k hkpos D.residual)
    rw [KyFanDominantIdealFamily.kyFan_gauge,
      KyFanDominantIdealFamily.kyFan_gauge] at h
    exact h.2

end Complex

/-! ## Over a real Hilbert space -/

section Real

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open TauCeti.DavisKahan.RealSpectralRestriction

/-- **Davis--Kahan 1970, the Section 2 `tan Θ` directed clause, over `ℝ`, at every
source unitarily invariant norm.**  The real sibling of
`tanTheta_directed_unboundedTrial_symmetricNorming_complex`. -/
theorem tanTheta_directed_unboundedTrial_symmetricNorming_real
    (N : SymmetricNormingFunction)
    (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A)
    {Z : Submodule ℝ E} [Z.HasOrthogonalProjection] [CompleteSpace Z]
    (D : TanTheta.BoundedCompressionTrialBlock A Z)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hgap : realSelfAdjointSpectralProjection A hA (Set.Ioo alpha (alpha + delta))
      measurableSet_Ioo = 0)
    (hCompression : ∀ z : Z, ⟪D.operator z, z⟫_ℝ ≤ alpha * ‖z‖ ^ 2)
    (tanTheta0 : Z →L[ℝ] E)
    (htan : HasTheorem63DirectedTangentApproximationNumbersInfiniteReal Z
      (realSelfAdjointSpectralSubspace A hA (Set.Iic alpha) measurableSet_Iic) tanTheta0)
    (hResidual : N.Mem D.residual) :
    N.Mem tanTheta0 ∧
      delta * N.gauge tanTheta0 ≤ N.gauge D.residual := by
  apply N.mul_gauge_le_of_all_mul_kyFan_le hdelta hResidual
  intro k
  by_cases hk : k = 0
  · subst hk
    simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have h := theorem6_3_unbounded_infiniteTrial_ideal_real A hA
      (KyFanDominantIdealFamily.kyFan (𝕜 := ℝ) k hkpos) D hdelta hgap
      hCompression tanTheta0 htan
      (KyFanDominantIdealFamily.kyFan_mem k hkpos D.residual)
    rw [KyFanDominantIdealFamily.kyFan_gauge,
      KyFanDominantIdealFamily.kyFan_gauge] at h
    exact h.2

end Real

/-! ## The Appendix scope: the Ritz compression may itself be unbounded

The two endpoints above take a `TanTheta.BoundedCompressionTrialBlock`, whose Ritz
compression `operator : Z →L[𝕜] Z` is **bounded and everywhere defined on the
trial space**.  Its name records only that the *ambient* operator is unbounded.

That is not the Appendix's scope.  The Appendix to Section 6 states, of the
tangent theorem specifically, that it

> returns to the ordered hypotheses `A₀ ≤ α` and `Λ₁ ≥ α + δ` in the general case
> and allows *both* `A₀` and `Λ₁` to be unbounded; the residual entering the
> displayed norm estimate is still required to be bounded

-- so the compression `A₀` is a densely defined self-adjoint operator on the trial
space, and only the residual is bounded.  `UnboundedCompressionTrialData` is the
carrier for that, `UnboundedRitzPair` ties it to the ambient operator, and the
Ky-Fan-level estimate at that scope already exists on both scalar fields.  What
follows is the promotion to the paper's universal norm quantifier, in the same
`UnboundedRitzPair`/`ReducingComplement` vocabulary the *ambient* clause already uses.
-/

section AppendixComplex

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Davis--Kahan 1970, the Section 2 `tan Θ` directed clause at the Appendix's
own scope, over `ℂ`, at every source unitarily invariant norm.**

`δ N(tan Θ₀) ≤ N(R)` where the Ritz compression `A₀` is itself a densely defined
self-adjoint operator on the trial space -- **not** a bounded one -- the ambient
operator `A` is an unbounded self-adjoint partial map, only the residual `R` is
bounded, the Hilbert dimension is arbitrary, and `N` is an arbitrary
`SymmetricNormingFunction`.

The hypotheses are the printed ordered ones with both intervals half-infinite:
`hupper` is `A₀ ≤ α` as a form bound on the *partial* compression, and
`hUnwanted` is `Λ₁ ≥ α + δ` as a form bound on the reducing complement `Vᗮ`.
There is no `β`; the Appendix drops it, and this is the Appendix's statement.

`tanTheta0` is a parameter rather than an existential because the promotion
evaluates the Ky Fan estimate at every index and an existential could return a
different representative at each one; `htan` is the paper's own characterization
of `tan Θ₀`, that its approximation numbers are `tan θⱼ` of the directed sine
block. -/
theorem tanTheta_directed_unboundedRitz_symmetricNorming_complex
    (N : SymmetricNormingFunction)
    {A : H →ₗ.[ℂ] H}
    {Z V : Submodule ℂ H}
    [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace Z]
    (D : DavisKahan.UnboundedRitzPair A Z)
    (hV : DavisKahan.ReducingComplement A V)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℂ)
    (tanTheta0 : Z →L[ℂ] H)
    (htan : HasTheorem63DirectedTangentApproximationNumbersInfinite Z V tanTheta0)
    (hResidual : N.Mem D.trial.residual) :
    N.Mem tanTheta0 ∧
      delta * N.gauge tanTheta0 ≤ N.gauge D.trial.residual := by
  have hcross := D.trial.crossed_lower_of_reducing V A D.mem_domain D.action_eq
    hV.mapsDomain hV.commutes hUnwanted
  apply N.mul_gauge_le_of_all_mul_kyFan_le hdelta hResidual
  intro k
  by_cases hk : k = 0
  · subst hk
    simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have h := D.trial.ideal_of_formBounds V
      (KyFanDominantIdealFamily.kyFan (𝕜 := ℂ) k hkpos) hdelta hupper hcross
      tanTheta0 htan
      (KyFanDominantIdealFamily.kyFan_mem k hkpos D.trial.residual)
    rw [KyFanDominantIdealFamily.kyFan_gauge,
      KyFanDominantIdealFamily.kyFan_gauge] at h
    exact h.2

end AppendixComplex

section AppendixReal

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Davis--Kahan 1970, the Section 2 `tan Θ` directed clause at the Appendix's
own scope, over `ℝ`.**  The real sibling of
`tanTheta_directed_unboundedRitz_symmetricNorming_complex`: the Ritz compression is a
densely defined self-adjoint *partial* operator on the trial space, the ambient
operator is an unbounded self-adjoint partial map, only the residual is bounded,
and the norm is an arbitrary `SymmetricNormingFunction`. -/
theorem tanTheta_directed_unboundedRitz_symmetricNorming_real
    (N : SymmetricNormingFunction)
    {A : E →ₗ.[ℝ] E}
    {Z V : Submodule ℝ E}
    [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace Z]
    (D : DavisKahan.UnboundedRitzPair A Z)
    (hV : DavisKahan.ReducingComplement A V)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ ⟪A ⟨y, hy⟩, y⟫_ℝ)
    (tanTheta0 : Z →L[ℝ] E)
    (htan : HasTheorem63DirectedTangentApproximationNumbersInfiniteReal Z V tanTheta0)
    (hResidual : N.Mem D.trial.residual) :
    N.Mem tanTheta0 ∧
      delta * N.gauge tanTheta0 ≤ N.gauge D.trial.residual := by
  have hcross := D.trial.crossed_lower_of_reducing V A D.mem_domain D.action_eq
    hV.mapsDomain hV.commutes hUnwanted
  apply N.mul_gauge_le_of_all_mul_kyFan_le hdelta hResidual
  intro k
  by_cases hk : k = 0
  · subst hk
    simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have h := theorem6_3_unboundedCompression_ideal_real
      (KyFanDominantIdealFamily.kyFan (𝕜 := ℝ) k hkpos) D.trial V hdelta hupper
      hcross tanTheta0 htan
      (KyFanDominantIdealFamily.kyFan_mem k hkpos D.trial.residual)
    rw [KyFanDominantIdealFamily.kyFan_gauge,
      KyFanDominantIdealFamily.kyFan_gauge] at h
    exact h.2

end AppendixReal

/-! ## The Appendix clause with the representative exhibited and the pole excluded

Davis and Kahan's directed tangent conclusion is an inequality about the *sequence*
`tan θ₀, tan θ₁, …`.  The two endpoints above take a representative of that sequence as a
parameter, deliberately: an existential inside the Ky Fan quantifier could return a
different operator at every index.  What the printed statement additionally needs is that
such a representative exists at all, and that every `tan θⱼ` is a genuine tangent rather
than the value Lean's totalised `Real.tan` assigns at a pole.  Both follow from the same
form bounds, and neither is a hypothesis. -/

section AppendixExistsComplex

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **No principal angle between the trial and exact subspaces is a right angle**, under
the Appendix's own ordered form bounds and an unbounded Ritz compression.  This is the
directed tangent theorem's pole exclusion, derived rather than assumed. -/
theorem approximationSingularValue_directedSineBlock_lt_one_unboundedRitz_complex
    {A : H →ₗ.[ℂ] H}
    {Z V : Submodule ℂ H}
    [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace Z]
    (D : DavisKahan.UnboundedRitzPair A Z)
    (hV : DavisKahan.ReducingComplement A V)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℂ)
    (n : ℕ) :
    approximationSingularValue n (theorem63DirectedSineBlock Z V) < 1 :=
  D.trial.approximationSingularValue_sineBlock_lt_one V hdelta hupper
    (D.trial.crossed_lower_of_reducing V A D.mem_domain D.action_eq
      hV.mapsDomain hV.commutes hUnwanted) n

/-- **The Section 2 `tan Θ` directed clause at the Appendix's scope, over `ℂ`, with the
tangent representative exhibited and the pole excluded.**

Everything the printed clause asserts, with nothing assumed beyond the source hypotheses:
every principal angle is strictly acute, a bounded operator with exactly the paper's
approximation numbers `tan θⱼ` exists, and it satisfies `δ N(tan Θ₀) ≤ N(R)` in every
source unitarily invariant norm.  The Ritz compression is a densely defined self-adjoint
partial operator, the ambient operator is an unbounded self-adjoint partial map, and only
the residual is bounded.

`R` is the paper's own residual of (1.8), named as an explicit bounded operator and tied
to the Ritz data by `hR`; the source's `‖R‖` on the right of the estimate is then literally
what the conclusion bounds against.

This is the source-facing endpoint to cite for the directed clause.  The parameterized
`tanTheta_directed_unboundedRitz_symmetricNorming_complex` asks the caller to supply the
representative *and* a proof that its approximation numbers are the `tan θⱼ`; the source
asks for no such thing, and here both are produced from the form bounds. -/
theorem tanTheta_directed_unboundedRitz_symmetricNorming_exists_complex
    (N : SymmetricNormingFunction)
    {A : H →ₗ.[ℂ] H}
    {Z V : Submodule ℂ H}
    [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace Z]
    (D : DavisKahan.UnboundedRitzPair A Z)
    (hV : DavisKahan.ReducingComplement A V)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℂ)
    (R : Z →L[ℂ] H) (hR : D.trial.residual = R)
    (hResidual : N.Mem R) :
    (∀ n, approximationSingularValue n (theorem63DirectedSineBlock Z V) < 1) ∧
      ∃ tanTheta0 : Z →L[ℂ] H,
        HasTheorem63DirectedTangentApproximationNumbersInfinite Z V tanTheta0 ∧
        N.Mem tanTheta0 ∧
        delta * N.gauge tanTheta0 ≤ N.gauge R := by
  subst hR
  have hlt := approximationSingularValue_directedSineBlock_lt_one_unboundedRitz_complex
    D hV hdelta hupper hUnwanted
  obtain ⟨tanTheta0, htan⟩ :=
    exists_hasTheorem63DirectedTangentApproximationNumbersInfinite Z V hlt
  obtain ⟨hmem, hbound⟩ := tanTheta_directed_unboundedRitz_symmetricNorming_complex N D hV
    hdelta hupper hUnwanted tanTheta0 htan hResidual
  exact ⟨hlt, tanTheta0, htan, hmem, hbound⟩

/-- **Davis--Kahan 1970, the directed `tan Θ₀` theorem at the printed source scope
over `ℂ`.**

Separable ambient Hilbert space and normalized unitarily invariant norm.  The
pole-exclusion conjunct and the tangent representative are both produced from the
source data and do not mention the norm, so they are constructed once; only the
estimate goes through the Fan-dominance bridge. -/
theorem tanTheta_directed_unboundedRitz_normalizedUIN_complex
    
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℂ)
    {A : H →ₗ.[ℂ] H}
    {Z V : Submodule ℂ H}
    [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace Z]
    (D : DavisKahan.UnboundedRitzPair A Z)
    (hV : DavisKahan.ReducingComplement A V)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℂ)
    (R : Z →L[ℂ] H) (hR : D.trial.residual = R)
    (hResidual : N.Mem R) :
    (∀ n, approximationSingularValue n (theorem63DirectedSineBlock Z V) < 1) ∧
      ∃ tanTheta0 : Z →L[ℂ] H,
        HasTheorem63DirectedTangentApproximationNumbersInfinite Z V tanTheta0 ∧
        N.Mem tanTheta0 ∧
        delta * N.gauge tanTheta0 ≤ N.gauge R := by
  subst hR
  have hlt := approximationSingularValue_directedSineBlock_lt_one_unboundedRitz_complex
    D hV hdelta hupper hUnwanted
  obtain ⟨tanTheta0, htan⟩ :=
    exists_hasTheorem63DirectedTangentApproximationNumbersInfinite Z V hlt
  obtain ⟨hmem, hbound⟩ :=
    normalizedUnitaryInvariant_of_symmetricNorming N hdelta hResidual fun M hM =>
      tanTheta_directed_unboundedRitz_symmetricNorming_complex M D hV
        hdelta hupper hUnwanted tanTheta0 htan hM
  exact ⟨hlt, tanTheta0, htan, hmem, hbound⟩

end AppendixExistsComplex

section AppendixExistsReal

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The real sibling of
`approximationSingularValue_directedSineBlock_lt_one_unboundedRitz_complex`. -/
theorem approximationSingularValue_directedSineBlock_lt_one_unboundedRitz_real
    {A : E →ₗ.[ℝ] E}
    {Z V : Submodule ℝ E}
    [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace Z]
    (D : DavisKahan.UnboundedRitzPair A Z)
    (hV : DavisKahan.ReducingComplement A V)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ ⟪A ⟨y, hy⟩, y⟫_ℝ)
    (n : ℕ) :
    approximationSingularValue n (theorem63DirectedSineBlockReal Z V) < 1 :=
  approximationSingularValue_sineBlockReal_lt_one_unboundedCompression
    D.trial V hdelta hupper
    (D.trial.crossed_lower_of_reducing V A D.mem_domain D.action_eq
      hV.mapsDomain hV.commutes hUnwanted) n

/-- **The Section 2 `tan Θ` directed clause at the Appendix's scope, over `ℝ`, with the
tangent representative exhibited and the pole excluded.**

The real sibling of `tanTheta_directed_unboundedRitz_symmetricNorming_exists_complex`, and
the source-facing endpoint to cite for the directed clause over `ℝ`.  `R` is the paper's
residual of (1.8) as an explicit bounded operator. -/
theorem tanTheta_directed_unboundedRitz_symmetricNorming_exists_real
    (N : SymmetricNormingFunction)
    {A : E →ₗ.[ℝ] E}
    {Z V : Submodule ℝ E}
    [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace Z]
    (D : DavisKahan.UnboundedRitzPair A Z)
    (hV : DavisKahan.ReducingComplement A V)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ ⟪A ⟨y, hy⟩, y⟫_ℝ)
    (R : Z →L[ℝ] E) (hR : D.trial.residual = R)
    (hResidual : N.Mem R) :
    (∀ n, approximationSingularValue n (theorem63DirectedSineBlockReal Z V) < 1) ∧
      ∃ tanTheta0 : Z →L[ℝ] E,
        HasTheorem63DirectedTangentApproximationNumbersInfiniteReal Z V tanTheta0 ∧
        N.Mem tanTheta0 ∧
        delta * N.gauge tanTheta0 ≤ N.gauge R := by
  subst hR
  have hlt := approximationSingularValue_directedSineBlock_lt_one_unboundedRitz_real
    D hV hdelta hupper hUnwanted
  obtain ⟨tanTheta0, htan⟩ :=
    exists_hasTheorem63DirectedTangentApproximationNumbersReal Z V hlt
  obtain ⟨hmem, hbound⟩ := tanTheta_directed_unboundedRitz_symmetricNorming_real N D hV
    hdelta hupper hUnwanted tanTheta0 htan hResidual
  exact ⟨hlt, tanTheta0, htan, hmem, hbound⟩

/-- **Davis--Kahan 1970, the directed `tan Θ₀` theorem at the printed source scope
over `ℝ`.** -/
theorem tanTheta_directed_unboundedRitz_normalizedUIN_real
    
    (N : NormalizedUnitaryInvariantNorm.{0, v} ℝ)
    {A : E →ₗ.[ℝ] E}
    {Z V : Submodule ℝ E}
    [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace Z]
    (D : DavisKahan.UnboundedRitzPair A Z)
    (hV : DavisKahan.ReducingComplement A V)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ ⟪A ⟨y, hy⟩, y⟫_ℝ)
    (R : Z →L[ℝ] E) (hR : D.trial.residual = R)
    (hResidual : N.Mem R) :
    (∀ n, approximationSingularValue n (theorem63DirectedSineBlockReal Z V) < 1) ∧
      ∃ tanTheta0 : Z →L[ℝ] E,
        HasTheorem63DirectedTangentApproximationNumbersInfiniteReal Z V tanTheta0 ∧
        N.Mem tanTheta0 ∧
        delta * N.gauge tanTheta0 ≤ N.gauge R := by
  subst hR
  have hlt := approximationSingularValue_directedSineBlock_lt_one_unboundedRitz_real
    D hV hdelta hupper hUnwanted
  obtain ⟨tanTheta0, htan⟩ :=
    exists_hasTheorem63DirectedTangentApproximationNumbersReal Z V hlt
  obtain ⟨hmem, hbound⟩ :=
    normalizedUnitaryInvariant_of_symmetricNorming N hdelta hResidual fun M hM =>
      tanTheta_directed_unboundedRitz_symmetricNorming_real M D hV
        hdelta hupper hUnwanted tanTheta0 htan hM
  exact ⟨hlt, tanTheta0, htan, hmem, hbound⟩

end AppendixExistsReal

end


/-! ## Source-facing names for the ideal-gauge forms

The two Ky-Fan-dominant ideal-gauge endpoints behind the directed clause are declared in
`DavisKahan/TanTheta/`, their natural reusable home, but they carry *source numbering* in
their names.  A source-numbered declaration that a census row registers should be reachable
under `TauCeti.DavisKahan1970`, so these aliases give them that name; the reusable
declarations are unchanged.  Finding F6.4 of the 2026-09-04 hostile review. -/

/-- **Theorem 6.3 at an arbitrary Fan-dominant ideal gauge**, with the tangent representative
supplied by the caller.  The source-facing name for
`TauCeti.DavisKahan.TanTheta.theorem6_3_unbounded_infiniteTrial_ideal`. -/
alias theorem6_3_unbounded_infiniteTrial_ideal :=
  DavisKahan.TanTheta.theorem6_3_unbounded_infiniteTrial_ideal

/-- **Theorem 6.3 at an arbitrary Fan-dominant ideal gauge**, with the representative
existentially quantified.  The source-facing name for
`TauCeti.DavisKahan.TanTheta.theorem6_3_unbounded_infiniteTrial_ideal_exists`, and the complex
partner of `theorem6_3_unbounded_infiniteTrial_ideal_exists_real`. -/
alias theorem6_3_unbounded_infiniteTrial_ideal_exists :=
  DavisKahan.TanTheta.theorem6_3_unbounded_infiniteTrial_ideal_exists

end DavisKahan1970
end TauCeti
