/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Circuits.Basic

/-! # AND/OR/NOT Basis — Definitions

This module defines the AND/OR operations and various basis configurations
used throughout the circuit complexity library.

## Main definitions

* `AndOrOp` — AND/OR operations (negation is free via per-input gate flags)
* `AndOrOp.eval` — fold-based evaluation of AND/OR on `n` input bits
* `AndOrOp.dual`, `AndOrOp.dualIf` — De Morgan duality
* `Basis.unboundedAndOr` — unbounded fan-in AND/OR basis
* `Basis.boundedAndOr` — fan-in bounded by `k` AND/OR basis
* `Basis.andOr2` — fan-in exactly 2 AND/OR basis (used in Shannon/Schnorr bounds)
-/


@[expose] public section

namespace Complexity

/-- Operations in an AND/OR basis. Negation is handled by per-input flags
    on gates, so only AND and OR need explicit representation. -/
inductive AndOrOp where
  /-- The AND operation: outputs `true` iff all inputs are `true`. -/
  | and
  /-- The OR operation: outputs `true` iff at least one input is `true`. -/
  | or
  deriving Repr, DecidableEq

/-- Evaluate an AND or OR operation on `n` input bits by folding.
    AND folds with `&&` starting from `true`; OR folds with `||` from `false`. -/
def AndOrOp.eval : (op : AndOrOp) → (n : Nat) → BitString n → Bool
  | .and, n, inputs => Fin.foldl n (fun acc i => acc && inputs i) true
  | .or, n, inputs => Fin.foldl n (fun acc i => acc || inputs i) false

/-- De Morgan duality swaps AND and OR. -/
def AndOrOp.dual : AndOrOp → AndOrOp
  | .and => .or
  | .or => .and

/-- Select the De Morgan dual exactly when `negated` is true. -/
def AndOrOp.dualIf (negated : Bool) (op : AndOrOp) : AndOrOp :=
  if negated then op.dual else op

/-- AND/OR basis with unbounded fan-in. Negation is free (per-input flags on gates). -/
def Basis.unboundedAndOr : Basis where
  Op := AndOrOp
  arity
    | .and => .unbounded
    | .or => .unbounded
  eval op n _ inputs := op.eval n inputs

/-- AND/OR basis with fan-in bounded by `k`. Negation is free (per-input flags on gates). -/
def Basis.boundedAndOr (k : Nat) : Basis where
  Op := AndOrOp
  arity
    | .and => .upto k
    | .or => .upto k
  eval op n _ inputs := op.eval n inputs

/-- Fan-in-2 AND/OR basis. Every gate has exactly 2 inputs.
    Negation is free (per-input flags on gates).
    This is the basis used in the Shannon and Schnorr lower bound theorems. -/
def Basis.andOr2 : Basis where
  Op := AndOrOp
  arity _ := .exactly 2
  eval op n _ inputs := op.eval n inputs

/-- Every gate over `Basis.andOr2` has fan-in exactly 2. -/
theorem fanIn_andOr2 {W : Nat} (g : Gate Basis.andOr2 W) : g.fanIn = 2 := g.arityOk

/-- A fan-in-2 AND gate computes the conjunction of its two inputs. -/
theorem AndOrOp.eval_two_and (inputs : BitString 2) :
    AndOrOp.eval .and 2 inputs = (inputs 0 && inputs 1) := by
  simp [AndOrOp.eval, Fin.foldl_succ_last, Fin.foldl_zero]

/-- A fan-in-2 OR gate computes the disjunction of its two inputs. -/
theorem AndOrOp.eval_two_or (inputs : BitString 2) :
    AndOrOp.eval .or 2 inputs = (inputs 0 || inputs 1) := by
  simp [AndOrOp.eval, Fin.foldl_succ_last, Fin.foldl_zero]

@[simp] theorem AndOrOp.dual_dual (op : AndOrOp) :
    op.dual.dual = op := by
  cases op <;> rfl

end Complexity
