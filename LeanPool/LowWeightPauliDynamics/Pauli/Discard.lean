/-
Copyright (c) 2026 Jue Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jue Xu
-/

module

public import LeanPool.LowWeightPauliDynamics.Pauli.Truncate

/-!
# The operator discarded by a Pauli truncation

The component `Õ^{(d)}_{≥w*+1}` of `apd:eq:step_component` is an operator difference, `(1 - Π_{≤
w*}) A`,
where `A` is the evolved observable immediately before the truncation that ends step `d`. The
scalar `highNorm w A` measures the high-weight coefficients of `A`, but that definition alone
does not identify it with the norm of the discarded operator. This file proves the
identification.

`sub_truncOp` proves the general operator identity `A - Π_S A = Π_{Sᶜ} A`, using completeness of
the Pauli expansion. `pauliNorm_sub_truncOp_highSet_compl` then identifies the norm of the
operator discarded by a weight cut with `highNorm`. This is the norm identification in the last
equality of `apd:thm:triangle`, not that proposition's telescoping or expectation bound. No
trajectory, truncation schedule, or entanglement hypothesis enters here; trajectories and
schedules are in `Pauli/TrotterTruncate`, and the telescoping bound is in
`Pauli/TruncationError`.

All identities hold for arbitrary complex matrices indexed by bit strings, with Pauli strings
represented by the entrywise model `toMatrix`.

## Main results

* `coeff_ext`: an operator is determined by its Pauli coefficients.
* `sub_truncOp`, `sub_truncOp_compl`: `O - Π_S O = Π_{Sᶜ} O` and `O - Π_{Sᶜ} O = Π_S O`.
* `pauliNorm_truncOp`: the Pauli norm of `Π_S O` is the norm of the coefficient vector of `O`
  restricted to `S`.
* `pauliNorm_sub_truncOp_highSet_compl`: the operator discarded by a cut at weight `w` has Pauli
  norm `highNorm w O`.
-/

@[expose] public section

namespace Lean4LPD

open Finset

namespace PauliString

variable {n : ℕ}

/-- Coefficients preserve operator subtraction, an algebraic helper for the discarded component
`(1 - Π_{≤ w*}) A` in `apd:eq:step_component`. -/
theorem coeff_sub (A B : Matrix (Bits n) (Bits n) ℂ) (p : PauliIndex n) :
    coeff (A - B) p = coeff A p - coeff B p := by
  rw [coeff, coeff, coeff, Matrix.mul_sub, Matrix.trace_sub, mul_sub]

/-- Coefficient vectors preserve subtraction, so the operator difference of
`apd:eq:step_component` can be compared in coefficient space. -/
theorem coeffVec_sub (A B : Matrix (Bits n) (Bits n) ℂ) :
    coeffVec (A - B) = coeffVec A - coeffVec B := by
  ext p
  change coeff (A - B) p = coeff A p - coeff B p
  exact coeff_sub A B p

/-- Equality of every Pauli coefficient determines an operator. This is the completeness helper
used to identify the discarded operator in `apd:eq:step_component`, rather
than merely matching a scalar norm. -/
theorem coeff_ext {A B : Matrix (Bits n) (Bits n) ℂ}
    (h : ∀ p : PauliIndex n, coeff A p = coeff B p) : A = B := by
  calc
    A = ∑ p : PauliIndex n, coeff A p • toMatrix (herm p) :=
      (sum_coeff_smul_toMatrix_herm A).symm
    _ = ∑ p : PauliIndex n, coeff B p • toMatrix (herm p) :=
      Finset.sum_congr rfl fun p _ => by rw [h p]
    _ = B := sum_coeff_smul_toMatrix_herm B

/-- **The discarded operator is the complementary projection.** This generalizes the
`1 - Π_{≤ w*}` in `apd:eq:step_component` to any retained set `S`. -/
theorem sub_truncOp (S : Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) :
    O - truncOp S O = truncOp Sᶜ O := by
  apply coeff_ext
  intro p
  rw [coeff_sub, coeff_truncOp, coeff_truncOp]
  by_cases hp : p ∈ S <;> simp [hp, Finset.mem_compl]

/-- The complementary retained set discards exactly the `S` component; at `S = highSet n w*`
this is the operator identity in `apd:eq:step_component`. -/
theorem sub_truncOp_compl (S : Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) :
    O - truncOp Sᶜ O = truncOp S O := by
  simpa only [compl_compl] using sub_truncOp Sᶜ O

/-- The coefficient vector of the discarded operator `O - Π_S O` is the coefficient vector of
`O` restricted to the complement `Sᶜ`; a coefficient-space form of `apd:eq:step_component`. -/
theorem coeffVec_sub_truncOp (S : Finset (PauliIndex n))
    (O : Matrix (Bits n) (Bits n) ℂ) :
    coeffVec (O - truncOp S O) = restr Sᶜ (coeffVec O) := by
  rw [sub_truncOp, coeffVec_truncOp]

/-- A projected operator's Pauli norm is its restricted coefficient norm, the norm bridge used
for the discarded component in `apd:thm:triangle`. -/
theorem pauliNorm_truncOp (S : Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) :
    pauliNorm (truncOp S O) = ‖restr S (coeffVec O)‖ := by
  rw [← norm_coeffVec, coeffVec_truncOp]

/-- The norm of the operator discarded by retaining `S` is the norm on `Sᶜ`. This generalizes
the final norm identification of `apd:thm:triangle`. -/
theorem pauliNorm_sub_truncOp (S : Finset (PauliIndex n))
    (O : Matrix (Bits n) (Bits n) ℂ) :
    pauliNorm (O - truncOp S O) = ‖restr Sᶜ (coeffVec O)‖ := by
  rw [sub_truncOp, pauliNorm_truncOp]

/-- The norm of the operator discarded by retaining `Sᶜ` is the norm on `S`, the general-set
form of the final norm identification in `apd:thm:triangle`. -/
theorem pauliNorm_sub_truncOp_compl (S : Finset (PauliIndex n))
    (O : Matrix (Bits n) (Bits n) ℂ) :
    pauliNorm (O - truncOp Sᶜ O) = ‖restr S (coeffVec O)‖ := by
  rw [sub_truncOp_compl, pauliNorm_truncOp]

/-- The high-weight projection has norm `highNorm`, identifying the high-weight operator norm
appearing in `apd:thm:triangle`. -/
theorem pauliNorm_truncOp_highSet (w : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) :
    pauliNorm (truncOp (highSet n w) O) = highNorm w O := by
  rw [pauliNorm_truncOp, highNorm]

/-- **The high-weight scalar is the norm of the discarded operator.** Retaining the classes of
weight at most `w` discards an operator whose Pauli norm is exactly `highNorm w O`. This connects
the component `Õ^{(d)}_{≥w*+1}` of `apd:eq:step_component` with the high-weight norm
`apd:eq:def_high_weight_norm` that the ladder bounds (the identification of the truncated mass at
the start of the proof of `apd:thm:one_step_truncation_error`), and it holds for an arbitrary
operator `O`. -/
theorem pauliNorm_sub_truncOp_highSet_compl (w : ℕ) (O : Matrix (Bits n) (Bits n) ℂ) :
    pauliNorm (O - truncOp (highSet n w)ᶜ O) = highNorm w O := by
  rw [sub_truncOp_compl, pauliNorm_truncOp_highSet]

end PauliString

end Lean4LPD
