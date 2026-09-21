/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
import LeanPool.Malliavin.Malliavin.BrownianHermiteClarkOcone
import LeanPool.Malliavin.Malliavin.BrownianPurePowerDuality
import LeanPool.Malliavin.Malliavin.ClarkOconeExamples
import LeanPool.Malliavin.Malliavin.NaturalFiltrationLeftContinuous

/-!
# Brownian Clark--Ocone on a generated linear Wiener space

`BrownianPurePowerDuality.lean` proves the higher Hermite/multiple-integral identity for every
Brownian process whose coordinates are continuous linear functionals generating the ambient
sigma-algebra.  This file composes that identity with the endpoint theorems of
`BrownianHermiteClarkOcone.lean`, so that natural martingale representation, the identification
of the inverse-Itô integrand with the predictable Malliavin derivative, the concrete
Clark--Ocone formula, and a Brownian-compatible `ClarkOconeFamily` are all available under the
standing hypotheses alone, with no remaining identity-family input.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace

noncomputable
section

namespace Malliavin

open BrownianIteratedConstruction

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

/-- Natural martingale representation on a generated linear Wiener space. -/
theorem naturalMartingaleRepresentation_of_generated
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {filtration : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : filtration = Filtration.natural B hsm) :
    NaturalMartingaleRepresentation hB hsm hnat :=
  naturalMartingaleRepresentation_of_hermiteMultipleIntegralIdentity hB hsm hnat generated
    (higherHermiteMultipleIntegralIdentity_of_generated
      hB coordinate coordinate_apply generated hsm)

/-- On a generated linear Wiener space, the inverse-Itô integrand of every `𝔻₁,₂` functional
is the predictable projection of its Malliavin derivative. -/
theorem bestNaturalItoIntegrand_eq_predictableProjection_of_generated
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {filtration : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : filtration = Filtration.natural B hsm)
    (F : D12 P) :
    bestNaturalItoIntegrand hB hsm hnat (centeredPartL2 F.1) =
      predictableProjection filtration
        (timeDerivative hB coordinate coordinate_apply generated
          (mderivD12 P F)) :=
  bestNaturalItoIntegrand_eq_predictableProjection_of_hermiteMultipleIntegralIdentity
    hB coordinate coordinate_apply generated hsm hnat
    (higherHermiteMultipleIntegralIdentity_of_generated
      hB coordinate coordinate_apply generated hsm) F

/-- **The Brownian Clark--Ocone formula** on a generated linear Wiener space:
`F = E[F] + ∫ E[Dₜ F | 𝓕ₜ] dBₜ` for every `F ∈ 𝔻₁,₂`, with the natural-filtration Itô integral
and the predictable projection of the Malliavin derivative. -/
theorem naturalClarkOcone_of_generated
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {filtration : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : filtration = Filtration.natural B hsm)
    (F : D12 P) :
    F.1 = expectationL2 F.1 + naturalItoIntegral hB hsm hnat
      (predictableProjection filtration
        (timeDerivative hB coordinate coordinate_apply generated
          (mderivD12 P F))) :=
  naturalClarkOcone_of_hermiteMultipleIntegralIdentity
    hB coordinate coordinate_apply generated hsm hnat
    (higherHermiteMultipleIntegralIdentity_of_generated
      hB coordinate coordinate_apply generated hsm) F

/-- Centered form of the Brownian Clark--Ocone formula on a generated linear Wiener space. -/
theorem sub_expectationL2_eq_naturalItoIntegral_of_generated
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {filtration : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : filtration = Filtration.natural B hsm)
    (F : D12 P) :
    F.1 - expectationL2 F.1 = naturalItoIntegral hB hsm hnat
      (predictableProjection filtration
        (timeDerivative hB coordinate coordinate_apply generated
          (mderivD12 P F))) :=
  sub_expectationL2_eq_naturalItoIntegral_of_hermiteMultipleIntegralIdentity
    hB coordinate coordinate_apply generated hsm hnat
    (higherHermiteMultipleIntegralIdentity_of_generated
      hB coordinate coordinate_apply generated hsm) F

/-- The concrete natural Brownian Clark--Ocone family of a generated linear Wiener space. -/
noncomputable def ClarkOconeFamily.ofGenerated
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {filtration : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : filtration = Filtration.natural B hsm) :
    ClarkOconeFamily B P filtration :=
  ClarkOconeFamily.ofHermiteMultipleIntegralIdentity
    hB coordinate coordinate_apply generated hsm hnat
    (higherHermiteMultipleIntegralIdentity_of_generated
      hB coordinate coordinate_apply generated hsm)

/-- The generated-space family has the genuine Brownian value on elementary adapted
processes. -/
theorem ClarkOconeFamily.ofGenerated_isBrownianOnElementary
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {filtration : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : filtration = Filtration.natural B hsm) :
    (ClarkOconeFamily.ofGenerated
      hB coordinate coordinate_apply generated hsm hnat).IsBrownianOnElementary :=
  ClarkOconeFamily.ofHermiteMultipleIntegralIdentity_isBrownianOnElementary
    hB coordinate coordinate_apply generated hsm hnat
    (higherHermiteMultipleIntegralIdentity_of_generated
      hB coordinate coordinate_apply generated hsm)

/-- **The textbook Brownian Clark--Ocone theorem** on a generated linear Wiener space.  For every
`F ∈ 𝔻₁,₂`, the natural-filtration predictable projection of `Dₜ F` has a predictable
representative `G` whose time sections are `E[Dₜ F | 𝓕ₜ]` for almost every positive time, and
`F = E[F] + ∫ G dB` with the natural Itô integral.  No identity-family hypothesis remains. -/
theorem naturalClarkOcone_condExp_of_generated
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {filtration : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : filtration = Filtration.natural B hsm)
    (F : D12 P) :
    ∃ G : ℝ≥0 × W → ℝ,
      StronglyMeasurable[filtration.predictable] G ∧
      (predictableProjection filtration
          (timeDerivative hB coordinate coordinate_apply generated (mderivD12 P F)) :
            ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P] G ∧
      (∀ᵐ t ∂nonnegativeLebesgueMeasure, 0 < t →
        (fun w ↦ G (t, w)) =ᵐ[P]
          P[(fun w ↦ (timeDerivative hB coordinate coordinate_apply generated
            (mderivD12 P F)) (t, w)) | filtration t]) ∧
      F.1 = expectationL2 F.1 + naturalItoIntegral hB hsm hnat
        (predictableProjection filtration
          (timeDerivative hB coordinate coordinate_apply generated (mderivD12 P F))) := by
  obtain ⟨G, hG, hGae, hsection⟩ :=
    exists_representative_predictableDerivative_condExp_natural
      (ClarkOconeFamily.ofGenerated hB coordinate coordinate_apply generated hsm hnat) F
  exact ⟨G, hG, hGae, hsection,
    naturalClarkOcone_of_generated hB coordinate coordinate_apply generated hsm hnat F⟩

/-! ### Concrete examples with the natural Itô integral -/

/-- **Clark--Ocone for `g (B T)`** on a generated linear Wiener space, for `g` of class `C¹` with
exponential growth: `g (B T) = E[g (B T)] + ∫ Π (g' (B T) 1_{(0, T]}) dB` with the natural
Itô integral, where `Π` is the predictable projection. -/
theorem naturalClarkOcone_comp_brownian
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {filtration : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : filtration = Filtration.natural B hsm)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {K c : ℝ} (hK : 0 ≤ K)
    (hc : 0 ≤ c) (hgb : ∀ x, |g x| ≤ K * Real.exp (c * |x|))
    (hgb' : ∀ x, |deriv g x| ≤ K * Real.exp (c * |x|)) (T : ℝ≥0) :
    (memLp_comp_brownian coordinate coordinate_apply hg hK hc hgb T).toLp _ =
      expectationL2 ((memLp_comp_brownian coordinate coordinate_apply hg hK hc hgb T).toLp _)
        + naturalItoIntegral hB hsm hnat (predictableProjection filtration
          (tensor (intervalIndicator T)
            ((memLp_deriv_comp_brownian coordinate coordinate_apply hg hK hc hgb' T).toLp
              _))) :=
  clarkOcone_comp_brownian
    (ClarkOconeFamily.ofGenerated hB coordinate coordinate_apply generated hsm hnat)
    hg hK hc hgb hgb' T

/-- **Clark--Ocone for polynomials of a Brownian coordinate** on a generated linear Wiener
space: `p (B T) = E[p (B T)] + ∫ Π (p' (B T) 1_{(0, T]}) dB` with the natural Itô integral. -/
theorem naturalClarkOcone_polynomial_brownian
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {filtration : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : filtration = Filtration.natural B hsm)
    (p : Polynomial ℝ) (T : ℝ≥0) :
    (memLp_polynomial_brownian coordinate coordinate_apply p T).toLp _ =
      expectationL2 ((memLp_polynomial_brownian coordinate coordinate_apply p T).toLp _)
        + naturalItoIntegral hB hsm hnat (predictableProjection filtration
          (tensor (intervalIndicator T)
            ((memLp_polynomial_derivative_brownian coordinate coordinate_apply p T).toLp
              _))) :=
  clarkOcone_polynomial_brownian
    (ClarkOconeFamily.ofGenerated hB coordinate coordinate_apply generated hsm hnat) p T

end Malliavin

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
