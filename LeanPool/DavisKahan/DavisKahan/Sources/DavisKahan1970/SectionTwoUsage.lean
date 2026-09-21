/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SectionTwo
import LeanPool.DavisKahan.DavisKahan.Sylvester.ScalarTransport
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.ScalarTransport

/-! # Section Two Usage -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Using the four Section 2 theorems

A worked reading of `DavisKahan.Sources.DavisKahan1970.SectionTwo` for someone who
knows operator theory and not this repository.  Nothing here is new mathematics:
each declaration below takes the data an operator theorist would already have and
hands it to one of the four canonical theorems, so the compiler checks that the
advertised entry points really are reachable from ordinary hypotheses.

What the four ask for, in the vocabulary of the subject:

* **the ambient operator** is a `LinearPMap` `A : H →ₗ.[𝕜] H` with
  `IsSelfAdjoint A` -- unbounded, with an explicit domain;
* **the trial or spectral subspace** is a `Submodule 𝕜 H` carrying
  `[HasOrthogonalProjection]`, or is selected from `A` by a measurable set of
  reals through `TauCeti.LinearPMap.specRange` / `realSpecRange`;
* **the gap** is either a `FormBoundedSylvesterGap` between two self-adjoint
  restrictions, or the printed ordered/interval separation written out;
* **the residual or perturbation** is bounded where it appears on the right-hand
  side: the directed sine statements use a residual `R`, while the ambient
  statements use the bounded perturbation;
* **the norm** on the canonical sine APIs is a
  `NormalizedSymmetricOperatorIdealFamily`, with `N.gaugeReal` used where the
  displayed operators belong to its domain.  Older convenience and tangent APIs
  in this file also use `SymmetricNormingFunction`; those stronger interfaces
  retain explicit ideal-membership conclusions;
* **the angle** in the conclusion is a paper object:
  `(I - F₀F₀⋆) E₀` for `sin Θ`, the directed and ambient
  `sinTwoAngleOperator` constructions for `sin 2Θ`, and the corresponding
  tangent operators for the tangent theorems.

Structural facts are carried by objects with constructors, so they never become
proof obligations for the caller:

```
DavisKahan.UnboundedRitzPair.ofTrialBlock        -- from a bounded compression bundle
DavisKahan.ReducingComplement.ofReducesSubspace  -- from `V` reduces `A`
DavisKahan.ReflectionIntertwines.ofReducesSubspace -- from `V` reduces `A + B`
```

The last two start from `TauCeti.LinearPMap.ReducesSubspace`, the generic
reducing-subspace vocabulary, which is what a spectral subspace already gives you.

No Sylvester witness, reflection block, secant, or capability instance appears
below, and none is needed.
-/

namespace TauCeti
namespace DavisKahan1970

universe u₁ v₁
namespace SectionTwoUsage

open scoped InnerProductSpace
open scoped TauCeti.CompleteSubspace

open TauCeti.DavisKahan.ExactSinTheta TauCeti.DavisKahanExt

noncomputable section

universe v

/-! ## Complete `sin 2Θ` from the shared Section 2 setup -/

section SinTwoThetaRCLike

variable {𝕜 : Type u₁} [RCLike 𝕜]
variable {H : Type v₁}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

/-- The complete scalar-generic Section 2 `sin 2Θ` entry point from ordinary
reducing-subspace data at the source common-domain scope.

`P` reduces the unperturbed operator `A`, `Q` reduces the perturbed operator `T`, and
`A` and `T` have the same domain. The directed branch introduces only its bounded
residual extension; the ambient branch independently introduces a bounded symmetric
perturbation realizing `T = A + H`. This example intentionally calls only the public
`SectionTwo.sinTwoTheta` alias. -/
theorem sinTwoTheta_from_shared_reducing_setup
    (N : NormalizedSymmetricOperatorIdealFamily.{u₁, v₁} 𝕜)
    {A T : H →ₗ.[𝕜] H} (hA : IsSelfAdjoint A) (hT : IsSelfAdjoint T)
    (hdom : T.domain = A.domain)
    {P Q : Submodule 𝕜 H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hQred : TauCeti.LinearPMap.ReducesSubspace T Q)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction T Q hQred)
      (TauCeti.LinearPMap.reducingRestriction T Qᗮ hQred.orthogonal) δ) :
    (∀ R : P →L[𝕜] H,
      (∀ p : P, ∀ hp : (p : H) ∈ T.domain,
        T ⟨(p : H), hp⟩ = A ⟨(p : H), by rw [← hdom]; exact hp⟩ + R p) →
      N.Mem (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator P Q) →
      N.Mem R →
        δ * N.gaugeReal (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator P Q) ≤
          2 * N.gaugeReal R) ∧
    (∀ Hop : H →L[𝕜] H, Hop.IsSymmetric →
      T = TauCeti.LinearPMap.addBounded A Hop →
      N.Mem (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) →
      N.Mem Hop →
        δ * N.gaugeReal (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) ≤
          2 * N.gaugeReal Hop) := by
  exact SectionTwo.sinTwoTheta N hA hT hdom hPred hQred hδ hgap

end SinTwoThetaRCLike

/-! ## `sin Θ` from the printed interval/exterior separation -/

section SinTheta

variable {E F G H : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Reading `sin Θ` with the separation in its printed shape: the trial spectrum
inside `[β, α]`, the complementary spectrum outside `(β - δ, α + δ)`.

`FormBoundedSylvesterGap.intervalExterior` turns that into the gap the theorem
takes, and `DavisKahan1970.sinTheta_unbounded_intervalExterior_symmetricNorming_complex` packages
the same step; this spells it out so the seam is visible. -/
theorem sinTheta_from_printed_separation
    (N : SymmetricNormingFunction)
    (A : E →ₗ.[ℂ] E) (A₀ : F →ₗ.[ℂ] F) (Λ₁ : G →ₗ.[ℂ] G)
    (E₀ : F →L[ℂ] E) (F₀ : H →L[ℂ] E) (F₁ : G →L[ℂ] E) (R : F →L[ℂ] E)
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : DavisKahan1970.IsTrialResidual A A₀ E₀ R)
    (hexact : DavisKahan1970.IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (htrialSpec : TauCeti.LinearPMap.realSpectrum A₀ ⊆ Set.Icc β α)
    (hcomplSpec : TauCeti.LinearPMap.realSpectrum Λ₁ ⊆
      {x : ℝ | x ≤ β - δ ∨ α + δ ≤ x})
    (hR : N.Mem R) :
    N.Mem ((ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L E₀) ∧
      δ * N.gauge ((ContinuousLinearMap.id ℂ E - F₀ ∘L F₀.adjoint) ∘L E₀) ≤
        N.gauge R :=
  DavisKahan1970.sinTheta_unbounded_formGap_symmetricNorming_complex
    N A A₀ Λ₁ E₀ F₀ F₁ R hA hA₀ hΛ₁ htrial hexact hδ
    (FormBoundedSylvesterGap.intervalExterior hβα (Or.inl ⟨htrialSpec, hcomplSpec⟩))
    hR

/-- The same stronger symmetric-norming API over an arbitrary `RCLike` field.

This checks reachability of the stronger scalar-generic implementation theorem.  The short
`SectionTwo.sinTheta` now names the separate where-defined RClike ledger witness. -/
theorem sinTheta_from_printed_separation_rclike
    {𝕜 : Type u₁} [RCLike 𝕜]
    {E F G H : Type v₁}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (N : SymmetricNormingFunction)
    (A : E →ₗ.[𝕜] E) (A₀ : F →ₗ.[𝕜] F) (Λ₁ : G →ₗ.[𝕜] G)
    (E₀ : F →L[𝕜] E) (F₀ : H →L[𝕜] E) (F₁ : G →L[𝕜] E) (R : F →L[𝕜] E)
    (hA : IsSelfAdjoint A) (hA₀ : IsSelfAdjoint A₀) (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : DavisKahan1970.IsTrialResidual A A₀ E₀ R)
    (hexact : DavisKahan1970.IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {β α δ : ℝ} (hβα : β ≤ α) (hδ : 0 < δ)
    (htrialSpec : TauCeti.LinearPMap.realSpectrum A₀ ⊆ Set.Icc β α)
    (hcomplSpec : TauCeti.LinearPMap.realSpectrum Λ₁ ⊆
      {x : ℝ | x ≤ β - δ ∨ α + δ ≤ x})
    (hR : N.Mem R) :
    N.Mem ((ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L E₀) ∧
      δ * N.gauge ((ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L E₀) ≤
        N.gauge R :=
  DavisKahan1970.sinTheta_unbounded_formGap_symmetricNorming_rclike
    N A A₀ Λ₁ E₀ F₀ F₁ R hA hA₀ hΛ₁ htrial hexact hδ
    (FormBoundedSylvesterGap.intervalExterior hβα (Or.inl ⟨htrialSpec, hcomplSpec⟩))
    hR

end SinTheta

/-! ## `tan Θ` from a Ritz pair and a reducing subspace -/

section TanTheta

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- Reading `tan Θ` when what you have is a reducing subspace rather than the
theorem's projection-commutation clauses.

`DavisKahan.ReducingComplement.ofReducesSubspace` is the only step; everything
else is the mathematics the theorem is about. -/
theorem tanTheta_from_reducingSubspace
    (N : SymmetricNormingFunction)
    {A : E →ₗ.[ℂ] E}
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace U]
    (D : DavisKahan.UnboundedRitzPair A U)
    (hVred : TauCeti.LinearPMap.ReducesSubspace A V)
    (Hop : E →L[ℂ] E) (hH : IsSelfAdjoint Hop)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℂ)
    (hdefined : HasDefinedAmbientTangent U V)
    (hResidual : D.trial.residual = Uᗮ.starProjection ∘L Hop ∘L U.subtypeL)
    (hMem : N.Mem Hop) :
    N.Mem (tanAngleOperatorC U V) ∧
      delta * N.gauge (tanAngleOperatorC U V) ≤ N.gauge Hop :=
  SectionTwo.tanTheta_ambient_complex N D (DavisKahan.ReducingComplement.ofReducesSubspace hVred)
    Hop hH hdelta hupper hUnwanted hdefined hResidual hMem

/-- The same reading with a bounded Ritz compression, which is the common case.

`DavisKahan.UnboundedRitzPair.ofTrialBlock` builds the Ritz pair from the
`BoundedCompressionTrialBlock` bundle, so neither of the two structural objects has to be
assembled by hand. -/
theorem tanTheta_from_trialBlock
    (N : SymmetricNormingFunction)
    {A : E →ₗ.[ℂ] E}
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace U]
    (D : DavisKahan.TanTheta.BoundedCompressionTrialBlock A U)
    (hVred : TauCeti.LinearPMap.ReducesSubspace A V)
    (Hop : E →L[ℂ] E) (hH : IsSelfAdjoint Hop)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove
      (DavisKahan.UnboundedRitzPair.ofTrialBlock D).trial.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℂ)
    (hdefined : HasDefinedAmbientTangent U V)
    (hResidual : D.residual = Uᗮ.starProjection ∘L Hop ∘L U.subtypeL)
    (hMem : N.Mem Hop) :
    N.Mem (tanAngleOperatorC U V) ∧
      delta * N.gauge (tanAngleOperatorC U V) ≤ N.gauge Hop :=
  SectionTwo.tanTheta_ambient_complex N (DavisKahan.UnboundedRitzPair.ofTrialBlock D)
    (DavisKahan.ReducingComplement.ofReducesSubspace hVred) Hop hH hdelta hupper
    hUnwanted hdefined hResidual hMem

end TanTheta

/-! ## Scalar-generic `tan Θ` from a Ritz pair and reducing complement -/

section TanThetaRCLike

variable {𝕜 : Type u₁} [RCLike 𝕜]
variable {E : Type v₁} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- The full-unbounded ambient tangent entry point no longer requires the caller to choose
between real and complex theorem names. -/
theorem tanTheta_from_reducingSubspace_rclike
    (N : SymmetricNormingFunction)
    {A : E →ₗ.[𝕜] E}
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] [CompleteSpace U]
    (D : DavisKahan.UnboundedRitzPair A U)
    (hVred : TauCeti.LinearPMap.ReducesSubspace A V)
    (Hop : E →L[𝕜] E) (hH : IsSelfAdjoint Hop)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.trial.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_𝕜)
    (hdefined : TauCeti.DavisKahan.Angle.HasDefinedTangent U V)
    (hResidual : D.trial.residual = Uᗮ.starProjection ∘L Hop ∘L U.subtypeL)
    (hMem : N.Mem Hop) :
    N.Mem (TauCeti.DavisKahan.Angle.tanAngleOperator U V) ∧
      delta * N.gauge (TauCeti.DavisKahan.Angle.tanAngleOperator U V) ≤ N.gauge Hop :=
  SectionTwo.tanTheta_ambient N D
    (DavisKahan.ReducingComplement.ofReducesSubspace hVred)
    Hop hH hdelta hupper hUnwanted hdefined hResidual hMem

end TanThetaRCLike

/-! ## `sin 2Θ` from a measurable spectral selection

This section was missing until 2026-08-31, and its absence hid a certification
defect: writing the call is what makes visible that the complex endpoint cannot
be reached at the source's half-infinite gap scope. -/

section SinTwoTheta

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- `sin 2Θ` over `ℂ`, from a measurable spectral selection and the printed
separation, through
`sinTwoTheta_directed_unbounded_addBounded_symmetricNorming_complex`.

This is the perturbation-norm corollary, `2 N(E)` on the right, not the printed
directed clause `2 N(R)`; the latter is `SectionTwo.sinTwoTheta_complex`, whose
right-hand side is the trial residual.

The separation is `FormBoundedSylvesterGap` between the two spectral
restrictions, which is the printed scope: it carries the bounded interval and
both half-infinite configurations.  `sinTwoTheta_from_halfInfinite_separation`
below exercises one of the latter, which is the case the endpoint could not be
written at until the complex full-gap route landed. -/
theorem sinTwoTheta_from_printed_separation
    (N : SymmetricNormingFunction)
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A)
    (Eop : E →L[ℂ] E) (hEop : Eop.IsSymmetric)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : DavisKahan.Sylvester.FormBoundedSylvesterGap
      (DavisKahan.selfAdjointSpectralRestriction A hA B hB)
      (DavisKahan.selfAdjointSpectralRestriction A hA Bᶜ hB.compl) δ)
    (hEmem : N.Mem Eop) :
    N.Mem (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperatorC
        (DavisKahan.selfAdjointSpectralSubspace A hA B hB)
        (DavisKahan.selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (DavisKahan.addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ∧
      δ * N.gauge (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperatorC
        (DavisKahan.selfAdjointSpectralSubspace A hA B hB)
        (DavisKahan.selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (DavisKahan.addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ≤
        2 * N.gauge Eop :=
  sinTwoTheta_directed_unbounded_addBounded_symmetricNorming_complex
    N A hA Eop hEop B S hB hS hδ hgap hEmem

/-- `sin 2Θ` over `ℂ` at a **half-infinite** separating interval.

The selected restriction is bounded below by `c + δ` in form and the
complementary restriction is bounded above by `c`; neither is bounded on the
other side.  Davis and Kahan state the four theorems with intervals that "may be
half-infinite", and this is that configuration: `[c + δ, ∞)` against `(-∞, c]`.

The caller supplies the two form bounds and nothing else — no finite `β ≤ α`, no
spectrum-avoidance certificate. -/
theorem sinTwoTheta_from_halfInfinite_separation
    (N : SymmetricNormingFunction)
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A)
    (Eop : E →L[ℂ] E) (hEop : Eop.IsSymmetric)
    (B S : Set ℝ) (hB : MeasurableSet B) (hS : MeasurableSet S)
    {c δ : ℝ} (hδ : 0 < δ)
    (hBlow : TauCeti.LinearPMap.SemiboundedBelow
      (DavisKahan.selfAdjointSpectralRestriction A hA B hB) (c + δ))
    (hBcomplHigh : TauCeti.LinearPMap.SemiboundedAbove
      (DavisKahan.selfAdjointSpectralRestriction A hA Bᶜ hB.compl) c)
    (hEmem : N.Mem Eop) :
    N.Mem (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperatorC
        (DavisKahan.selfAdjointSpectralSubspace A hA B hB)
        (DavisKahan.selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (DavisKahan.addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ∧
      δ * N.gauge (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperatorC
        (DavisKahan.selfAdjointSpectralSubspace A hA B hB)
        (DavisKahan.selfAdjointSpectralSubspace (TauCeti.LinearPMap.addBounded A Eop)
          (DavisKahan.addBounded_isSelfAdjoint A hA Eop hEop) S hS)) ≤
        2 * N.gauge Eop :=
  sinTwoTheta_directed_unbounded_addBounded_symmetricNorming_complex
    N A hA Eop hEop B S hB hS hδ
    (DavisKahan.Sylvester.FormBoundedSylvesterGap.leftAboveRightBelow
      c hBlow hBcomplHigh)
    hEmem

end SinTwoTheta

/-! ## `tan 2Θ` from a subspace reducing the perturbed operator -/

section TanTwoTheta

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- Reading `tan 2Θ` when what you have is a subspace reducing `A + B`.

`DavisKahan.ReflectionIntertwines.ofReducesSubspace` supplies the reflection and
its commutation; the caller never builds a spectral reflection, never proves it
self-adjoint or involutive, and never certifies that `cos 2θ` avoids zero -- the
ordered gap already forces that. -/
theorem tanTwoTheta_from_reducingSubspace
    (N : SymmetricNormingFunction)
    {A : E →ₗ.[ℂ] E} {B : E →L[ℂ] E} {a b c : ℝ}
    (V : Submodule ℂ E) [V.HasOrthogonalProjection]
    (hA : IsSelfAdjoint A)
    (hBsa : IsSelfAdjoint B)
    (hB : TauCeti.IsOddFor
      (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) B)
    (hVred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A B) V)
    (hUa : ∀ x : A.domain,
      (x : E) ∈ TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic →
      RCLike.re ⟪A x, (x : E)⟫_ℂ ≤ a * ‖(x : E)‖ ^ 2)
    (hUb : ∀ x : A.domain,
      (x : E) ∈
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic)ᗮ →
      b * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_ℂ)
    (hab : a < b) (hBmem : N.Mem B) :
    (∀ t ∈ spectrum ℝ (angleOperatorC
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) V),
        Real.cos (2 * t) ≠ 0) ∧
      N.Mem (absTanTwoAngleOperatorC
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) V) ∧
      (b - a) * N.gauge (absTanTwoAngleOperatorC
        (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) V) ≤
        2 * N.gauge B :=
  SectionTwo.tanTwoTheta_ambient_complex N V hA hBsa hB
    (DavisKahan.ReflectionIntertwines.ofReducesSubspace hVred) hUa hUb hab hBmem

end TanTwoTheta

/-! ## Scalar-generic `tan 2Θ` at arbitrary reducing subspaces -/

section TanTwoThetaRCLike

variable {𝕜 : Type u₁} [RCLike 𝕜]
variable {E : Type v₁} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- The branch-free full-unbounded ambient `tan 2Θ` API at an arbitrary `RCLike` field.
Both reducing subspaces are supplied directly; no scalar-specific spectral-selection object
appears in the statement. -/
theorem tanTwoTheta_from_reducingSubspaces_rclike
    (N : SymmetricNormingFunction)
    {A : E →ₗ.[𝕜] E} {B : E →L[𝕜] E} {a b : ℝ}
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (V : Submodule 𝕜 E) [V.HasOrthogonalProjection]
    (hA : IsSelfAdjoint A)
    (hUred : TauCeti.LinearPMap.ReducesSubspace A U)
    (hBsa : IsSelfAdjoint B)
    (hB : TauCeti.IsOddFor U B)
    (hVred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A B) V)
    (hUa : ∀ x : A.domain, (x : E) ∈ U →
      RCLike.re ⟪A x, (x : E)⟫_𝕜 ≤ a * ‖(x : E)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : E) ∈ Uᗮ →
      b * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : E)⟫_𝕜)
    (hab : a < b) (hBmem : N.Mem B) :
    TauCeti.DavisKahan.Angle.HasDefinedDoubleTangent U V ∧
      N.Mem (TauCeti.DavisKahan.Angle.absTanTwoAngleOperator U V) ∧
      (b - a) * N.gauge (TauCeti.DavisKahan.Angle.absTanTwoAngleOperator U V) ≤
        2 * N.gauge B :=
  SectionTwo.tanTwoTheta_ambient N V hA hUred hBsa hB hVred hUa hUb hab hBmem

end TanTwoThetaRCLike

end

end SectionTwoUsage
end DavisKahan1970
end TauCeti
