/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import LeanPool.CircuitComplexity.Basic

/-! # AND/OR/NOT Basis — Definitions

This module defines the AND/OR operations and various basis configurations
used throughout the circuit complexity library.

## Main definitions

* `AONOp` — AND/OR operations (negation is free via per-input gate flags)
* `AONOp.eval` — fold-based evaluation of AND/OR on `n` input bits
* `Basis.unboundedAON` — unbounded fan-in AND/OR basis
* `Basis.boundedAON` — fan-in bounded by `k` AND/OR basis
* `Basis.andOr2` — fan-in exactly 2 AND/OR basis (used in Shannon/Schnorr bounds)
-/

namespace CircuitComplexity


/-- Operations in an AND/OR basis. Negation is handled by per-input flags
    on gates, so only AND and OR need explicit representation. -/
inductive AONOp where
  | and
  | or
  deriving Repr, DecidableEq

/-- Evaluate an AND or OR operation on `n` input bits by folding.
    AND folds with `&&` starting from `true`; OR folds with `||` from `false`. -/
def AONOp.eval : (op : AONOp) → (n : Nat) → BitString n → Bool
  | .and, n, inputs => Fin.foldl n (fun acc i => acc && inputs i) true
  | .or, n, inputs => Fin.foldl n (fun acc i => acc || inputs i) false

/-- AND/OR basis with unbounded fan-in. Negation is free (per-input flags on gates). -/
def Basis.unboundedAON : Basis where
  Op := AONOp
  arity
    | .and => .unbounded
    | .or => .unbounded
  eval op n _ inputs := op.eval n inputs

/-- AND/OR basis with fan-in bounded by `k`. Negation is free (per-input flags on gates). -/
def Basis.boundedAON (k : Nat) : Basis where
  Op := AONOp
  arity
    | .and => .upto k
    | .or => .upto k
  eval op n _ inputs := op.eval n inputs

/-- Fan-in-2 AND/OR basis. Every gate has exactly 2 inputs.
    Negation is free (per-input flags on gates).
    This is the basis used in the Shannon and Schnorr lower bound theorems. -/
def Basis.andOr2 : Basis where
  Op := AONOp
  arity _ := .exactly 2
  eval op n _ inputs := op.eval n inputs

/-- Every gate over `Basis.andOr2` has fan-in exactly 2. -/
theorem andOr2_fanIn {W : Nat} (g : Gate Basis.andOr2 W) : g.fanIn = 2 := g.arityOk

/-- A fan-in-2 AND gate computes the conjunction of its two inputs. -/
theorem AONOp.eval_two_and (inputs : BitString 2) :
    AONOp.eval .and 2 inputs = (inputs 0 && inputs 1) := by
  simp [AONOp.eval, Fin.foldl_succ_last, Fin.foldl_zero]

/-- A fan-in-2 OR gate computes the disjunction of its two inputs. -/
theorem AONOp.eval_two_or (inputs : BitString 2) :
    AONOp.eval .or 2 inputs = (inputs 0 || inputs 1) := by
  simp [AONOp.eval, Fin.foldl_succ_last, Fin.foldl_zero]

end CircuitComplexity
