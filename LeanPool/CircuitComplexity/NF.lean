/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import LeanPool.CircuitComplexity.NF.Defs
import LeanPool.CircuitComplexity.Internal.NF
import LeanPool.CircuitComplexity.XOR

/-! # Normal Forms: CNF/DNF Lower Bound for XOR

Any CNF or DNF formula computing the N-input XOR function requires at least
`2^{N-1}` clauses (respectively terms).

The proof shows that every DNF for a flip-sensitive function must have each
satisfying term mention all N variables, making the terms injective on the
`2^{N-1}`-element true-set.  The CNF case reduces to the DNF case via
De Morgan duality (`CNF.neg`).

## Definitions (from `Circ.NF.Defs`)

* `Literal` — a Boolean variable with a polarity flag
* `CNF` — conjunction of clauses (disjunctions of literals)
* `DNF` — disjunction of terms (conjunctions of literals)
* `CNF.complexity` / `DNF.complexity` — clause/term count
* `CNF.toCircuit` / `DNF.toCircuit` — 2-level AON circuit embedding

## Main results

* `DNF.xorBool_complexity_lb` — any DNF computing XOR has `≥ 2^{N-1}` terms
* `CNF.xorBool_complexity_lb` — any CNF computing XOR has `≥ 2^{N-1}` clauses
-/

namespace CircuitComplexity


/-- Any DNF computing N-variable XOR requires at least `2^{N-1}` terms. -/
theorem DNF.xorBool_complexity_lb (φ : DNF N) (hN : 1 ≤ N)
    (hcomp : ∀ x, φ.eval x = Schnorr.xorBool N x) :
    2 ^ (N - 1) ≤ φ.complexity := by
  exact φ.flip_complexity_lb hN (Schnorr.xorBool N) hcomp
    (fun x i => Schnorr.xorBool_flip N x i)

/-- Any CNF computing N-variable XOR requires at least `2^{N-1}` clauses. -/
theorem CNF.xorBool_complexity_lb (φ : CNF N) (hN : 1 ≤ N)
    (hcomp : ∀ x, φ.eval x = Schnorr.xorBool N x) :
    2 ^ (N - 1) ≤ φ.complexity := by
  -- φ.neg is a DNF computing ¬xorBool, which is also flip-sensitive
  rw [← CNF.neg_complexity]
  apply DNF.flip_complexity_lb φ.neg hN (fun x => !(Schnorr.xorBool N x))
  · intro x; rw [CNF.eval_neg, hcomp]
  · intro x i
    rw [Schnorr.xorBool_flip, Bool.not_not]

end CircuitComplexity
