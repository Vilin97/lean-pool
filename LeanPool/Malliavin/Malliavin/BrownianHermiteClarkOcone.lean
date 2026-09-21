/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
import LeanPool.Malliavin.Malliavin.BrownianHermiteMultipleIntegral
import LeanPool.Malliavin.Malliavin.PastCylinderDensity

/-!
# Clark--Ocone from the Brownian Hermite/multiple-integral identity

The higher-order Hermite/multiple-integral identity supplies natural martingale representation.
The finite-coordinate density theorem supplies Malliavin--Itô duality without an additional
hypothesis.  Combining the two identifies the canonical inverse-Itô integrand with the
predictable Malliavin derivative and yields the concrete Clark--Ocone formula.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace

noncomputable section

namespace Malliavin

open BrownianIteratedConstruction

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

/-- Under the Hermite/multiple-integral identity, the inverse-Itô integrand is the predictable
Malliavin derivative. -/
theorem bestNaturalItoIntegrand_eq_predictableProjection_of_hermiteMultipleIntegralIdentity
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {filtration : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : filtration = Filtration.natural B hsm)
    (hid : BrownianHigherHermiteMultipleIntegralIdentity hB)
    (F : D12 P) :
    bestNaturalItoIntegrand hB hsm hnat (centeredPartL2 F.1) =
      predictableProjection filtration
        (timeDerivative hB coordinate coordinate_apply generated
          (mderivD12 P F)) := by
  let hMRT :=
    naturalMartingaleRepresentation_of_hermiteMultipleIntegralIdentity
      hB hsm hnat generated hid
  apply (naturalItoDuality_iff_bestNaturalItoIntegrand_eq_predictableProjection
    hB coordinate coordinate_apply generated hsm hnat hMRT F).mp
  intro U
  exact naturalItoDuality_natural
    hB coordinate coordinate_apply generated hsm hnat F U

/-- Concrete Clark--Ocone under precisely the higher-order Hermite/multiple-integral identity. -/
theorem naturalClarkOcone_of_hermiteMultipleIntegralIdentity
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {filtration : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : filtration = Filtration.natural B hsm)
    (hid : BrownianHigherHermiteMultipleIntegralIdentity hB)
    (F : D12 P) :
    F.1 = expectationL2 F.1 + naturalItoIntegral hB hsm hnat
      (predictableProjection filtration
        (timeDerivative hB coordinate coordinate_apply generated
          (mderivD12 P F))) := by
  apply naturalClarkOcone
    hB coordinate coordinate_apply generated hsm hnat
    (naturalMartingaleRepresentation_of_hermiteMultipleIntegralIdentity
      hB hsm hnat generated hid) F
  exact
    bestNaturalItoIntegrand_eq_predictableProjection_of_hermiteMultipleIntegralIdentity
      hB coordinate coordinate_apply generated hsm hnat hid F

/-- Centered form of Clark--Ocone under the Hermite/multiple-integral identity. -/
theorem sub_expectationL2_eq_naturalItoIntegral_of_hermiteMultipleIntegralIdentity
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {filtration : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : filtration = Filtration.natural B hsm)
    (hid : BrownianHigherHermiteMultipleIntegralIdentity hB)
    (F : D12 P) :
    F.1 - expectationL2 F.1 = naturalItoIntegral hB hsm hnat
      (predictableProjection filtration
        (timeDerivative hB coordinate coordinate_apply generated
          (mderivD12 P F))) := by
  apply sub_expectationL2_eq_naturalItoIntegral_predictableProjection
    hB coordinate coordinate_apply generated hsm hnat
    (naturalMartingaleRepresentation_of_hermiteMultipleIntegralIdentity
      hB hsm hnat generated hid) F
  exact
    bestNaturalItoIntegrand_eq_predictableProjection_of_hermiteMultipleIntegralIdentity
      hB coordinate coordinate_apply generated hsm hnat hid F

/-- The Hermite/multiple-integral identity constructs the concrete natural Brownian
Clark--Ocone family. -/
noncomputable def ClarkOconeFamily.ofHermiteMultipleIntegralIdentity
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {filtration : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : filtration = Filtration.natural B hsm)
    (hid : BrownianHigherHermiteMultipleIntegralIdentity hB) :
    ClarkOconeFamily B P filtration := by
  exact ClarkOconeFamily.ofNaturalIto
    hB coordinate coordinate_apply generated hsm hnat
    (naturalMartingaleRepresentation_of_hermiteMultipleIntegralIdentity
      hB hsm hnat generated hid)
    (fun F U ↦ naturalItoDuality_natural
      hB coordinate coordinate_apply generated hsm hnat F U)

/-- The identity-based family has the genuine Brownian value on elementary adapted processes. -/
theorem ClarkOconeFamily.ofHermiteMultipleIntegralIdentity_isBrownianOnElementary
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {filtration : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : filtration = Filtration.natural B hsm)
    (hid : BrownianHigherHermiteMultipleIntegralIdentity hB) :
    (ClarkOconeFamily.ofHermiteMultipleIntegralIdentity
      hB coordinate coordinate_apply generated hsm hnat hid
      ).IsBrownianOnElementary := by
  apply ClarkOconeFamily.isBrownianOnElementary_of_itoIntegral_eq_naturalItoIntegral
  rfl

end Malliavin

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
