/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
module

public import LeanPool.Malliavin.Malliavin.BrownianChaos
public import LeanPool.Malliavin.Malliavin.ChaosMartingaleRepresentation

/-!
# Martingale representation from the canonical Brownian chaos tower

This file specializes the generic graded-submodule martingale-representation theorem to the
canonical Brownian multiple-integral ranges.  The remaining hypothesis is exactly totality of
that concrete tower.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace

noncomputable
section

namespace Malliavin.BrownianIteratedConstruction

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

/-- Totality of the canonical Brownian homogeneous chaos tower. -/
def BrownianChaosTotal (hB : IsPreBrownianReal B P) : Prop :=
  (⨆ n : ℕ, (brownianHomogeneousChaos hB n : Submodule ℝ (RandomL2 P))
    ).topologicalClosure = ⊤

omit [CompleteSpace W] [BorelSpace W] in
/-- Totality of the canonical Brownian chaos tower supplies natural martingale
representation. -/
theorem naturalMartingaleRepresentation_of_brownianChaosTotal
    (hB : IsPreBrownianReal B P)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (htotal : BrownianChaosTotal hB) :
    NaturalMartingaleRepresentation hB hsm hnat := by
  apply Malliavin.naturalMartingaleRepresentation_of_total_submodules hB hsm hnat
    (fun n => (brownianHomogeneousChaos hB n : Submodule ℝ (RandomL2 P)))
  · exact htotal
  · exact brownianHomogeneousChaos_zero_le_centeredPartCLM_ker hB
  · intro n hn
    exact brownianHomogeneousChaos_le_naturalItoRange hB hsm hnat n hn

end Malliavin.BrownianIteratedConstruction

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
