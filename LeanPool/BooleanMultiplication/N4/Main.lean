/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.FeedbackSaturation

/-!
# Exact unrestricted Boolean multiplicative complexity for four-term products

The structural contradiction rules out eight gates.  Together with the
algebraic seven-gate obstruction and the explicit nine-gate construction,
this closes the `n = 4` theorem.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- The normalized eight-gate state is inconsistent: gate six is useful by
the flag ledger and non-useful by first-jet saturation. -/
theorem normalizedEight_contradiction {C : Circuit 8 8}
    (h : NormalizedEight C) : False :=
  h.gateSix_not_useful h.gateSix_useful

/-- There is no unrestricted eight-AND circuit for four-term Boolean
multiplication. -/
theorem no_eight_gate_circuit : ¬ HasCircuit (Mul 4) 8 := by
  rintro ⟨⟨C, hC⟩⟩
  rcases exists_normalized_eight C hC with ⟨D, hD⟩
  exact normalizedEight_contradiction hD

/-- Every unrestricted circuit for `Mul 4` has at least nine AND gates. -/
theorem mul_four_lower (r : Nat) (hCircuit : HasCircuit (Mul 4) r) :
    9 ≤ r := by
  rcases hCircuit with ⟨⟨C, hC⟩⟩
  have hambient : targetAmbient 8 (mulTarget 4) ≤ C.finalWire :=
    targetAmbient_le_finalWire C hC
  have hdimension := Submodule.finrank_mono hambient
  have hfinalBound := finalWire_finrank_le_affine_add C
  rw [targetAmbient_four_finrank] at hdimension
  change Module.finrank F₂ C.finalWire ≤
    Module.finrank F₂ (affine 8) + r at hfinalBound
  rw [affine_eight_finrank] at hfinalBound
  have hdimBound : 16 ≤ 9 + r := hdimension.trans hfinalBound
  have hseven : 7 ≤ r := by omega
  by_contra hnine
  have hrange : r = 7 ∨ r = 8 := by omega
  rcases hrange with rfl | rfl
  · apply no_seven_gate_circuit
    exact ⟨⟨C, hC⟩⟩
  · apply no_eight_gate_circuit
    exact ⟨⟨C, hC⟩⟩

/-- The unrestricted Boolean multiplicative complexity of four-term
multiplication is exactly nine. -/
theorem mc_mul_four : MC(Mul 4) = 9 :=
  mc_eq_of_lower_upper mul_four_upper mul_four_lower

end

end N4
end UnrestrictedBooleanMul
