/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.All

/-!
# Regression invariants for the hostile-review repairs

Three independent hostile reviews found defects that a green certificate could
not see.  Every one had the same shape: correct Lean mathematics, a resolving and
compiling declaration, a statement pin that matched -- and a *different
mathematical object* from the printed one.

This module guards the repairs that a pin does not.  Statement pins follow the
declarations a census row names as canonical, so when a repaired theorem is
retargeted -- as several were when the source-exact façades became canonical --
the repaired statement drops out of the pinned set and can drift back unnoticed.

Each invariant below **restates** the repaired theorem and proves it by that
declaration.  If the declaration's statement moves, the restatement stops
elaborating and this module fails to build.  That is the whole mechanism: no new
checker, no new data file, and nothing to remember.

Run:

```bash
lake build DavisKahan.Sources.DavisKahan1970.Audits.HostileReviewRegressions
```

It is outside `DavisKahan.All` and inside `DavisKahan.Audits.All`.
-/

namespace TauCeti.DavisKahan1970.Audits.HostileReviewRegressions

open TauCeti.DavisKahan TauCeti.DavisKahan.ExactSinTheta
open TauCeti.DavisKahan.Sylvester
open scoped InnerProductSpace

universe v

/-! ## 1. The ambient `sin 2Θ` gap is on the perturbed blocks

Section 2's (1.3) puts `Λ₀, Λ₁` on `A + H` relative to `Q`, and the theorem's gap
is there.  The registered witness once had it on the *unperturbed* blocks, and the
inventory called that the printed hypothesis.

The restatement below is what fails if the gap argument moves back to `A` and `P`:
`hgap` is built from `reducingRestriction (addBounded A Hop) Q`. -/
/-- The ambient `sin 2Θ` gap hypothesis is read on the *perturbed* blocks of
`A + H` at `Q`, which is where (1.3) puts it. -/
theorem ambient_sinTwoTheta_gap_is_on_the_perturbed_blocks
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : SymmetricNormingFunction)
    {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (Hop : H →L[ℂ] H) (hHop : Hop.IsSymmetric)
    {P Q : Submodule ℂ H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hQred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A Hop) Q)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A Hop) Q hQred)
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A Hop) Qᗮ hQred.orthogonal) δ)
    (hHmem : N.Mem Hop) :
    N.Mem (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) ∧
      δ * N.gauge (TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q) ≤
        2 * N.gauge Hop :=
  TauCeti.DavisKahan1970.sinTwoTheta_ambient_unbounded_perturbedGap_symmetricNorming_complex
    N hA Hop hHop hPred hQred hδ hgap hHmem

/-! ## 2. The four steps of that role reversal

Each is exact rather than approximate, which is what makes the reversal a
correspondence and not an appeal to symmetry. -/
/-- Adding a bounded perturbation and then subtracting it returns the original
partial map on the nose, domains included. -/
theorem addBounded_cancellation_is_on_the_nose
    {𝕜 : Type*} [RCLike 𝕜] {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] 
    (A : H →ₗ.[𝕜] H) (V : H →L[𝕜] H) :
    TauCeti.LinearPMap.addBounded (TauCeti.LinearPMap.addBounded A V) (-V) = A :=
  TauCeti.LinearPMap.addBounded_neg_cancel A V

/-- The ambient `sin 2Θ` operator is symmetric in its pair of subspaces. -/
theorem ambient_sinTwoTheta_is_symmetric_in_the_pair
    {𝕜 : Type*} [RCLike 𝕜] {H : Type v}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    TauCeti.DavisKahan.Angle.sinTwoAngleOperator V U =
      TauCeti.DavisKahan.Angle.sinTwoAngleOperator U V :=
  TauCeti.DavisKahan.Angle.sinTwoAngleOperator_comm U V

/-- A symmetric gauge is blind to the sign of the perturbation, in both its
membership and its value. -/
theorem source_gauge_does_not_see_the_perturbation_sign
    {𝕜 : Type*} [RCLike 𝕜] {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (N : SymmetricNormingFunction) (A : E →L[𝕜] F) :
    N.gauge (-A) = N.gauge A ∧ (N.Mem (-A) ↔ N.Mem A) :=
  ⟨N.gauge_neg A, N.mem_neg⟩

/-! ## 3. Theorem 3.1's forward invariant is the source's angle operator

The classification was stated on `genericCosineBlock` -- Halmos's `cos²Θ` -- and
the row asserted that as the printed invariant.  The restatement names
`genericAngleBlock`, which is `Θ`. -/
/-- Theorem 3.1's forward invariant is the source's angle operator `Θ`, not
Halmos's `cos²Θ`. -/
theorem theorem3_1_invariant_is_the_angle_operator
    {H₁ : Type v} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    (U₁ V₁ : Submodule ℂ H₁) [U₁.HasOrthogonalProjection] [V₁.HasOrthogonalProjection]
    (U₂ V₂ : Submodule ℂ H₂) [U₂.HasOrthogonalProjection] [V₂.HasOrthogonalProjection]
    [TopologicalSpace.SeparableSpace H₁] [TopologicalSpace.SeparableSpace H₂] :
    DavisKahan.PairOfSubspacesUnitaryEquivalent U₁ V₁ U₂ V₂ ↔
      DavisKahan.SameHalmosTrivialDimensions U₁ V₁ U₂ V₂ ∧
      TauCeti.SameSpectralMultiplicity
        (TauCeti.DavisKahan1970.genericAngleBlock U₁ V₁)
        (TauCeti.DavisKahan1970.genericAngleBlock U₂ V₂) :=
  TauCeti.DavisKahan1970.theorem3_1_spectralMultiplicity_classification_sourceAngle_complex
    U₁ V₁ U₂ V₂

/-! ## 4. Corollary 3.1's classification is on the angle list

It was on `compactAngleEigenvalueList`, the *sine-square* list.  The restatement
names `compactAngleList`, the angles counted with multiplicity. -/
/-- Corollary 3.1 classifies by the list of angles counted with multiplicity,
not by the sine-square list. -/
theorem corollary3_1_invariant_is_the_angle_list
    {𝕜 : Type*} [RCLike 𝕜]
    {H₁ : Type v} [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
    {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]
    (W₁ X₁ : Submodule 𝕜 H₁) [W₁.HasOrthogonalProjection] [X₁.HasOrthogonalProjection]
    (W₂ X₂ : Submodule 𝕜 H₂) [W₂.HasOrthogonalProjection] [X₂.HasOrthogonalProjection]
    (hcompact₁ : IsCompactOperator
      (W₁.starProjection ∘L
        (ContinuousLinearMap.id 𝕜 H₁ - X₁.starProjection) ∘L
          W₁.starProjection))
    (hcompact₂ : IsCompactOperator
      (W₂.starProjection ∘L
        (ContinuousLinearMap.id 𝕜 H₂ - X₂.starProjection) ∘L
          W₂.starProjection)) :
    DavisKahan.PairOfSubspacesUnitaryEquivalent W₁ X₁ W₂ X₂ ↔
      DavisKahan.SameHalmosTrivialDimensions W₁ X₁ W₂ X₂ ∧
      TauCeti.DavisKahan1970.compactAngleList
          (DavisKahan.genericCosineBlock W₁ X₁ᗮ) =
        TauCeti.DavisKahan1970.compactAngleList
          (DavisKahan.genericCosineBlock W₂ X₂ᗮ) :=
  TauCeti.DavisKahan1970.corollary3_1_compact_defectBlock_sourceAngleList_classification
    W₁ X₁ W₂ X₂ hcompact₁ hcompact₂

/-! ## 5. Theorem 3.1's dimension clause is a proposition

The printed converse assumes `dim A₀ + dim A₁ = dim H`.  It once took a chosen
isometric equivalence from the caller, which is construction data rather than the
hypothesis. -/
/-- Theorem 3.1's printed dimension clause is a proposition about the pair, not
chosen construction data. -/
theorem theorem3_1_dimension_clause_is_a_proposition
    {𝕜 : Type*} [RCLike 𝕜]
    {A₀ : Type v} [NormedAddCommGroup A₀] [InnerProductSpace 𝕜 A₀]
    {A₁ : Type v} [NormedAddCommGroup A₁] [InnerProductSpace 𝕜 A₁]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] :
    TauCeti.DavisKahan1970.SameHilbertDimensionSum 𝕜 A₀ A₁ H =
      Nonempty (WithLp 2 (A₀ × A₁) ≃ₗᵢ[𝕜] H) :=
  rfl

end TauCeti.DavisKahan1970.Audits.HostileReviewRegressions
