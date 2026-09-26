/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
module

public import LeanPool.Malliavin.ClarkOconeSolution

/-!
Manifest-driven boundary for the Clark-Ocone surface.

Every declaration below has an explicit type and delegates to the production
declaration. A changed source signature therefore breaks elaboration, while
the manifest separately audits the production declaration's axioms.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Real Topology InnerProductSpace
noncomputable
section

namespace ClarkOconeBoundary

universe u

variable {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
  [BorelSpace W] [SecondCountableTopology W] in
/-- The standalone predictable sigma-algebra embeds in the ambient product space. -/
theorem predictable_le_prod_boundary
    (filtration : Filtration ℝ≥0 ‹MeasurableSpace W›) :
    filtration.predictable ≤ (inferInstance : MeasurableSpace (ℝ≥0 × W)) :=
  PalomarClarkOcone.predictable_le_prod filtration

/-- The standalone capstone supplies time-derivative and Itô-integral operators. -/
theorem generated_clark_ocone_boundary
    {B : ℝ≥0 → W → ℝ}
    (hB : IsPreBrownianReal B P)
    (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : PalomarClarkOcone.IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {filtration : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : filtration = Filtration.natural B hsm) :
    ∃ (_timeDerivative :
          Lp (PalomarClarkOcone.CameronMartin.Space P) 2 P →ₗᵢ[ℝ]
            PalomarClarkOcone.TimeProcessL2 P)
        (_itoIntegral :
          PalomarClarkOcone.PredictableProcessL2 filtration P →L[ℝ]
            PalomarClarkOcone.RandomL2 P),
      True :=
  let ⟨td, ii, _⟩ := PalomarClarkOcone.generated_clark_ocone hB coordinate
    coordinate_apply generated hsm hnat
  ⟨td, ii, trivial⟩

end ClarkOconeBoundary

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
