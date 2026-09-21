/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Theorem61Universal
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Theorem62
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Presentation

/-! # Theorem61 -/

open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan 1970, Theorems 6.1 and 6.2, on ordinary mathematical hypotheses

Theorem 6.1 is the generalized directed sine theorem: the trial map need not be
isometric, only bounded below by `ε`, and the printed bound carries that constant,
`δ ε N(sin Θ₀) ≤ N(R)`.  Theorem 6.2 replaces the Sylvester gap by the source's
pairwise spectral-distance condition and specializes the norm to
Hilbert--Schmidt.

## What changed, and why

Both canonical declarations used to be *methods on a record* — `Theorem61Data`
and `Theorem62Data`, each bundling an `UnboundedSinThetaData` (itself a
record) together with the exact map, three self-adjointness fields, the exact
decomposition, the gap, and the frame bound.  A reader of the paper had to build
two nested records before invoking the theorem.

The theorems below take the mathematics directly.  They reuse the Section 2
vocabulary rather than inventing a second one:

* `DavisKahan1970.IsTrialResidualEquation A A₀ E₀ R` — `E₀` carries `dom A₀` into
  `dom A`, and `R = A E₀ − E₀ A₀` there.  This is `IsTrialResidual` with the
  isometry removed (`isTrialResidual_iff_equation_and_isometry`), which is
  exactly the difference between Section 2 and Section 6: Section 2 asks for an
  isometric trial map, these two ask only for `LowerFrameBound E₀ ε`.
* `DavisKahan1970.IsExactSpectralDecomposition A Λ₁ F₀ F₁` — reused unchanged.

```text
IsTrialResidualEquation + IsometricEmbedding E₀   ->  Section 2 sin Θ
IsTrialResidualEquation + LowerFrameBound E₀ ε    ->  Theorem 6.1 / Theorem 6.2
```

## What is preserved

The printed representative freedom is preserved exactly: the conclusion is stated
for an arbitrary `SinThetaRepresentativeAcross` of the canonical directed
block, which is the source's "`sin Θ₀` subject only to the singular-value
condition".  The lower-frame factor, the sharp constant, the arbitrary source
unitarily invariant norm (Theorem 6.1) and the Hilbert--Schmidt specialization
with the source's pairwise spectral-distance hypothesis (Theorem 6.2) are
unchanged.  The records remain as implementation and compatibility APIs; each
theorem below builds one internally.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46: Theorems 6.1 and 6.2.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan1970

open TauCeti.DavisKahan.ExactSinTheta


open TauCeti.DavisKahan
open DavisKahan1970

noncomputable section

universe v

section Components

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The `UnboundedSinThetaData` determined by the Section 6 component
hypotheses.  It is the proof's bookkeeping object, built here so that no
canonical Section 6 statement has to mention it. -/
def sectionSixData
    (A : E →ₗ.[𝕜] E) (A₀ : F →ₗ.[𝕜] F) (Λ₁ : G →ₗ.[𝕜] G)
    (E₀ : F →L[𝕜] E) (F₀ : H →L[𝕜] E) (F₁ : G →L[𝕜] E) (R : F →L[𝕜] E)
    (htrial : IsTrialResidualEquation A A₀ E₀ R)
    (hexact : IsExactSpectralDecomposition A Λ₁ F₀ F₁) :
    UnboundedSinThetaData (𝕜 := 𝕜) (E := E) (F := F) (G := G) where
  A := A
  A₀ := A₀
  Λ₁ := Λ₁
  X := E₀
  F₁ := F₁
  residual := R
  X_maps_domain := htrial.mapsDomain
  F₁_maps_domain := hexact.mapsDomain
  residual_eq := htrial.residualEquation
  intertwines := hexact.intertwines

/-- The exact orthogonal decomposition carried by `IsExactSpectralDecomposition`.

Not stated with dot notation: the predicate lives in the root `DavisKahan1970`
namespace and this file declares into `TauCeti.DavisKahan1970`. -/
theorem orthogonalExactDecomposition_of_isExactSpectralDecomposition
    {A : E →ₗ.[𝕜] E} {Λ₁ : G →ₗ.[𝕜] G} {F₀ : H →L[𝕜] E} {F₁ : G →L[𝕜] E}
    (hexact : IsExactSpectralDecomposition A Λ₁ F₀ F₁) :
    OrthogonalExactDecomposition F₀ F₁ :=
  { isometry₀ := hexact.desiredIsometry
    isometry₁ := hexact.complementIsometry
    orthogonal := hexact.orthogonal
    projection_sum := hexact.complete }

end Components

/-! ## The printed lower-frame hypothesis, and the Lean one -/

section LowerFrame

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **The source's lower-frame hypothesis is `LowerFrameBound`.**

Davis and Kahan print the Theorem 6.1 hypothesis as the operator inequality

`E₀* E₀ ≥ ε² I`,   `ε > 0`,

read in the usual quadratic-form sense.  The Lean statements take
`LowerFrameBound E₀ ε`, i.e. `ε ‖x‖ ≤ ‖E₀ x‖`.  The two are the same hypothesis,
and this is the theorem that says so rather than leaving a reviewer to supply the
equivalence.

Only `0 ≤ ε` is needed; the source's `ε > 0` is stronger.  The step is
`re ⟪E₀* E₀ x, x⟫ = ‖E₀ x‖²`, after which the two inequalities differ by squaring
nonnegative reals. -/
theorem lowerFrameBound_iff_operator_inequality
    (E₀ : F →L[𝕜] E) {ε : ℝ} (hε : 0 ≤ ε) :
    (∀ x : F, ε ^ 2 * ‖x‖ ^ 2 ≤
        RCLike.re (inner 𝕜 ((E₀.adjoint ∘L E₀) x) x)) ↔
      LowerFrameBound E₀ ε := by
  have hform : ∀ x : F,
      RCLike.re (inner 𝕜 ((E₀.adjoint ∘L E₀) x) x) = ‖E₀ x‖ ^ 2 := by
    intro x
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]
    simp
  constructor
  · intro h x
    have hx := h x
    rw [hform x] at hx
    have : (ε * ‖x‖) ^ 2 ≤ ‖E₀ x‖ ^ 2 := by
      calc (ε * ‖x‖) ^ 2 = ε ^ 2 * ‖x‖ ^ 2 := by ring
        _ ≤ ‖E₀ x‖ ^ 2 := hx
    exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp this
  · intro h x
    have hx := h x
    rw [hform x]
    calc ε ^ 2 * ‖x‖ ^ 2 = (ε * ‖x‖) ^ 2 := by ring
      _ ≤ ‖E₀ x‖ ^ 2 := by
          exact pow_le_pow_left₀ (by positivity) hx 2

/-- The source's printed hypothesis implies the Lean one, in the direction a
caller holding the operator inequality needs. -/
theorem lowerFrameBound_of_operator_inequality
    (E₀ : F →L[𝕜] E) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ x : F, ε ^ 2 * ‖x‖ ^ 2 ≤
        RCLike.re (inner 𝕜 ((E₀.adjoint ∘L E₀) x) x)) :
    LowerFrameBound E₀ ε :=
  (lowerFrameBound_iff_operator_inequality E₀ hε).mp h

end LowerFrame

/-! ## Theorem 6.1 -/

section Theorem61Complex

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Davis--Kahan 1970, Theorem 6.1, over `ℂ`, on component hypotheses.**

`δ ε N(sin Θ₀) ≤ N(R)` for every source unitarily invariant norm, where `ε` is
the lower frame bound of the trial map and `sin Θ₀` is any operator with the
canonical directed block's singular-value sequence.

Nothing about the proof's organisation appears: no `Theorem61Data`, no
`UnboundedSinThetaData`, no Ky Fan family, no capability class. -/
theorem theorem6_1_complex
    {E₀' F₀' : Type v}
    [NormedAddCommGroup E₀'] [InnerProductSpace ℂ E₀'] [CompleteSpace E₀']
    [NormedAddCommGroup F₀'] [InnerProductSpace ℂ F₀'] [CompleteSpace F₀']
    (N : SymmetricNormingFunction)
    (A : E →ₗ.[ℂ] E) (A₀ : F →ₗ.[ℂ] F) (Λ₁ : G →ₗ.[ℂ] G)
    (E₀ : F →L[ℂ] E) (F₀ : H →L[ℂ] E) (F₁ : G →L[ℂ] E) (R : F →L[ℂ] E)
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : IsTrialResidualEquation A A₀ E₀ R)
    (hexact : IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {ε : ℝ} (hε : 0 < ε) (hframe : LowerFrameBound E₀ ε)
    {δ : ℝ} (hδ : 0 < δ) (hgap : FormBoundedSylvesterGap A₀ Λ₁ δ)
    (S : SinThetaRepresentativeAcross (E₀ := E₀') (F₀ := F₀')
      (directedSinThetaOperator E₀ F₀ hframe hε))
    (hR : N.Mem R) :
    N.Mem S.operator ∧ δ * ε * N.gauge S.operator ≤ N.gauge R := by
  let P : Theorem61Data (E := E) (F := F) (G := G) (H := H) :=
    { data := sectionSixData A A₀ Λ₁ E₀ F₀ F₁ R htrial hexact
      exactMap := F₀
      ambient_selfAdjoint := hA
      trial_selfAdjoint := hA₀
      complement_selfAdjoint := hΛ₁
      exact_decomposition := orthogonalExactDecomposition_of_isExactSpectralDecomposition hexact
      gap := δ
      frameLowerBound := ε
      gap_pos := hδ
      frameLowerBound_pos := hε
      lowerFrame := hframe
      spectral_gap := hgap }
  exact P.result_every_unitarilyInvariantNorm_across S N hR

end Theorem61Complex

section Theorem61Real

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Davis--Kahan 1970, Theorem 6.1, over `ℝ`.**  The real sibling of
`theorem6_1_complex`, with the same hypotheses and the same conclusion. -/
theorem theorem6_1_real
    {E₀' F₀' : Type v}
    [NormedAddCommGroup E₀'] [InnerProductSpace ℝ E₀'] [CompleteSpace E₀']
    [NormedAddCommGroup F₀'] [InnerProductSpace ℝ F₀'] [CompleteSpace F₀']
    (N : SymmetricNormingFunction)
    (A : E →ₗ.[ℝ] E) (A₀ : F →ₗ.[ℝ] F) (Λ₁ : G →ₗ.[ℝ] G)
    (E₀ : F →L[ℝ] E) (F₀ : H →L[ℝ] E) (F₁ : G →L[ℝ] E) (R : F →L[ℝ] E)
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : IsTrialResidualEquation A A₀ E₀ R)
    (hexact : IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {ε : ℝ} (hε : 0 < ε) (hframe : LowerFrameBound E₀ ε)
    {δ : ℝ} (hδ : 0 < δ) (hgap : FormBoundedSylvesterGap A₀ Λ₁ δ)
    (S : SinThetaRepresentativeAcross (E₀ := E₀') (F₀ := F₀')
      (directedSinThetaOperatorReal E₀ F₀ hframe hε))
    (hR : N.Mem R) :
    N.Mem S.operator ∧ δ * ε * N.gauge S.operator ≤ N.gauge R := by
  let P : RealTheorem61Data (E := E) (F := F) (G := G) (H := H) :=
    { data := sectionSixData A A₀ Λ₁ E₀ F₀ F₁ R htrial hexact
      exactMap := F₀
      ambient_selfAdjoint := hA
      trial_selfAdjoint := hA₀
      complement_selfAdjoint := hΛ₁
      exact_decomposition := orthogonalExactDecomposition_of_isExactSpectralDecomposition hexact
      gap := δ
      frameLowerBound := ε
      gap_pos := hδ
      frameLowerBound_pos := hε
      lowerFrame := hframe
      spectral_gap := hgap }
  exact P.result_every_unitarilyInvariantNorm_across S N hR

end Theorem61Real

/-! ## Theorem 6.2 -/

section Theorem62Complex

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The canonical Theorem 6.2 sine block, named without a record so that the
representative condition can be stated on component hypotheses. -/
noncomputable def sectionSixSinThetaBlock
    (E₀ : F →L[ℂ] E) (F₁ : G →L[ℂ] E)
    {ε : ℝ} (hframe : LowerFrameBound E₀ ε) (hε : 0 < ε) : G →L[ℂ] F :=
  sinThetaBlockOfPolarData (lowerFramePolarData E₀ hframe hε) F₁

/-- **Davis--Kahan 1970, Theorem 6.2, over `ℂ`, on component hypotheses.**

The source's pairwise spectral-distance hypothesis in place of the Sylvester
gap, and the Hilbert--Schmidt norm in place of an arbitrary unitarily invariant
one: `δ ε ‖sin Θ₀‖_HS ≤ ‖R‖_HS`, with the same lower-frame factor and the same
representative freedom as Theorem 6.1.

This is the counted Theorem 6.2 statement.  The stronger arbitrary-UI-norm
theorem and the finite-rank operator-norm consequence are source-adjacent
material and are deliberately not what this states. -/
theorem theorem6_2_complex
    {E₀' F₀' : Type v}
    [NormedAddCommGroup E₀'] [InnerProductSpace ℂ E₀'] [CompleteSpace E₀']
    [NormedAddCommGroup F₀'] [InnerProductSpace ℂ F₀'] [CompleteSpace F₀']
    (A : E →ₗ.[ℂ] E) (A₀ : F →ₗ.[ℂ] F) (Λ₁ : G →ₗ.[ℂ] G)
    (E₀ : F →L[ℂ] E) (F₀ : H →L[ℂ] E) (F₁ : G →L[ℂ] E) (R : F →L[ℂ] E)
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : IsTrialResidualEquation A A₀ E₀ R)
    (hexact : IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {ε : ℝ} (hε : 0 < ε) (hframe : LowerFrameBound E₀ ε)
    {δ : ℝ} (hδ : 0 < δ) (hdist : PairwiseSpectrumGap A₀ Λ₁ δ)
    (S : SinThetaRepresentativeAcross (E₀ := E₀') (F₀ := F₀')
      (sectionSixSinThetaBlock E₀ F₁ hframe hε))
    (hR : approximationNumberEnergy R ≠ ⊤) :
    approximationNumberEnergy S.operator ≠ ⊤ ∧
      δ * ε * ContinuousLinearMap.hilbertSchmidtNorm S.operator ≤ ContinuousLinearMap.hilbertSchmidtNorm R := by
  let P : Theorem62Data (E := E) (F := F) (G := G) (H := H) :=
    { data := sectionSixData A A₀ Λ₁ E₀ F₀ F₁ R htrial hexact
      exactMap := F₀
      ambient_selfAdjoint := hA
      trial_selfAdjoint := hA₀
      complement_selfAdjoint := hΛ₁
      exact_decomposition :=
        orthogonalExactDecomposition_of_isExactSpectralDecomposition hexact
      gap := δ
      frameLowerBound := ε
      gap_pos := hδ
      frameLowerBound_pos := hε
      lowerFrame := hframe
      spectral_distance := hdist }
  exact P.result_across S hR

end Theorem62Complex

section Theorem62Real

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The canonical real Theorem 6.2 sine block. -/
noncomputable def sectionSixSinThetaBlockReal
    (E₀ : F →L[ℝ] E) (F₁ : G →L[ℝ] E)
    {ε : ℝ} (hframe : LowerFrameBound E₀ ε) (hε : 0 < ε) : G →L[ℝ] F :=
  sinThetaBlockOfPolarData (lowerFramePolarDataReal E₀ hframe hε) F₁

/-- **Davis--Kahan 1970, Theorem 6.2, over `ℝ`.**

The real sibling of `theorem6_2_complex`.  The pairwise spectral-distance
hypothesis is written out over `realSpectrum`, which is the real spelling of the
same condition. -/
theorem theorem6_2_real
    {E₀' F₀' : Type v}
    [NormedAddCommGroup E₀'] [InnerProductSpace ℝ E₀'] [CompleteSpace E₀']
    [NormedAddCommGroup F₀'] [InnerProductSpace ℝ F₀'] [CompleteSpace F₀']
    (A : E →ₗ.[ℝ] E) (A₀ : F →ₗ.[ℝ] F) (Λ₁ : G →ₗ.[ℝ] G)
    (E₀ : F →L[ℝ] E) (F₀ : H →L[ℝ] E) (F₁ : G →L[ℝ] E) (R : F →L[ℝ] E)
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : IsTrialResidualEquation A A₀ E₀ R)
    (hexact : IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {ε : ℝ} (hε : 0 < ε) (hframe : LowerFrameBound E₀ ε)
    {δ : ℝ} (hδ : 0 < δ)
    (hdist : ∀ lam ∈ TauCeti.LinearPMap.realSpectrum A₀,
      ∀ α ∈ TauCeti.LinearPMap.realSpectrum Λ₁, δ ≤ |lam - α|)
    (S : SinThetaRepresentativeAcross (E₀ := E₀') (F₀ := F₀')
      (sectionSixSinThetaBlockReal E₀ F₁ hframe hε))
    (hR : approximationNumberEnergy R ≠ ⊤) :
    approximationNumberEnergy S.operator ≠ ⊤ ∧
      δ * ε * ContinuousLinearMap.hilbertSchmidtNorm S.operator ≤ ContinuousLinearMap.hilbertSchmidtNorm R := by
  let P : RealTheorem62Data (E := E) (F := F) (G := G) (H := H) :=
    { data := sectionSixData A A₀ Λ₁ E₀ F₀ F₁ R htrial hexact
      exactMap := F₀
      ambient_selfAdjoint := hA
      trial_selfAdjoint := hA₀
      complement_selfAdjoint := hΛ₁
      exact_decomposition :=
        orthogonalExactDecomposition_of_isExactSpectralDecomposition hexact
      gap := δ
      frameLowerBound := ε
      gap_pos := hδ
      frameLowerBound_pos := hε
      lowerFrame := hframe
      spectral_distance := hdist }
  exact P.result_across S hR

end Theorem62Real

end

end DavisKahan1970
end TauCeti
