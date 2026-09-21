/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.Pochhammer.BetaIntegral

/-! # The real multivariate beta function -/

@[expose] public noncomputable section

namespace ProbabilityTheory

open Real

variable {ι : Type*} [Fintype ι]

/-- The multivariate real Beta function. -/
def mvRealBeta (b : ι → ℝ) : ℝ :=
  (∏ i, Gamma (b i)) / Gamma (∑ i, b i)

/-- Domain for `b` where the Beta function is defined as an integral. -/
def mvRealBetaDomain : Set (ι → ℝ) :=
  {b | ∀ i, 0 < b i}

/-- `mvRealBeta` is positive on `mvRealBetaDomain`. -/
theorem mvRealBeta_pos [Nonempty ι] {b : ι → ℝ} (hb : b ∈ mvRealBetaDomain) :
    0 < mvRealBeta b := by
  refine div_pos (Finset.prod_pos fun i _ => Gamma_pos_of_pos (hb i)) ?_
  exact Gamma_pos_of_pos (Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty)

end ProbabilityTheory

end
