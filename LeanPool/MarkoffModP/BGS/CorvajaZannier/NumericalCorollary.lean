/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.ParameterizedBound
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.NumericalOptimization

/-!
# The numerical Corvaja--Zannier Theorem 2 bound

This file composes the floor-parameter proof of Theorem 4 with the corrected
one-parameter optimization in `NumericalOptimization`.  Its only substantive
hypothesis is the ordinary Proposition 2 alternative for every admissible
pair of natural parameters.
-/

@[expose] public section

namespace BGS.CorvajaZannier

noncomputable section

/-- The exact numerical maximum in Corvaja--Zannier Theorem 2, deduced from
the numerical alternatives in Proposition 2.

The final optimization uses the corrected split recorded in
`theoremTwo_bound_of_theoremFour_bound`; it does not use the incompatible
parameter choices printed in the last paragraph of the source proof. -/
theorem theoremTwo_maxBound_of_propositionTwo
    (a b chi p : ℕ) (G : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hchi : 0 < chi) (hp : 0 < p)
    (hGNonneg : 0 ≤ G) (hGTrivial : G ≤ (a : ℝ))
    (hPropositionTwo : PropositionTwoNumericalAlternatives a b p chi G) :
    G ≤ max
      (3 * (2 * ((a : ℝ) * (b : ℝ) * (chi : ℝ))) ^ ((1 : ℝ) / 3))
      (12 * ((a : ℝ) * (b : ℝ)) / (p : ℝ)) := by
  have haReal : 0 < (a : ℝ) := by exact_mod_cast ha
  have hbReal : 0 < (b : ℝ) := by exact_mod_cast (lt_of_lt_of_le ha hab)
  have hchiReal : 0 < (chi : ℝ) := by exact_mod_cast hchi
  have hpReal : 0 < (p : ℝ) := by exact_mod_cast hp
  apply theoremTwo_bound_of_theoremFour_bound
    (p : ℝ) (a : ℝ) (b : ℝ) (chi : ℝ) G
    hpReal haReal hbReal hchiReal
  intro t ht hAdmissible
  apply theoremFour_parameterizedBound_of_propositionTwo
    a b chi p G t ha hab hchi hp hGNonneg hGTrivial ht hPropositionTwo
  apply (lt_div_iff₀ (by positivity : 0 < 8 * t ^ 3)).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using hAdmissible

end

end BGS.CorvajaZannier
