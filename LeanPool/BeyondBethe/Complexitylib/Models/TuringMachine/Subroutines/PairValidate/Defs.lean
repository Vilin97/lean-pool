/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Encoding.Pairing
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators

/-!
# Pair-encoding validator — definitions

This file defines a finite-state scanner for the image of the library's
self-delimiting binary `pair` codec. Unlike `pairSplitCoreTM`, the validator
has total semantics: it writes `1` exactly when `unpair?` succeeds and writes
`0` on every malformed encoding.
-/


@[expose] public section

namespace Complexity

/-- The language of strings on which the canonical pair decoder succeeds. -/
def validPairEncoding : Language :=
  {z | (unpair? z).isSome = true}

namespace TM

/-- Finite control for recognizing the doubled prefix and `01` separator of a
pair encoding. Once the separator has been seen, every remaining bit belongs
to the unrestricted right component. -/
inductive PairValidateState where
  /-- Expect the first copy of the next doubled bit. -/
  | next
  /-- The first copy was `0`; `0` continues the prefix and `1` is the separator. -/
  | afterZero
  /-- The first copy was `1`; only a second `1` is valid. -/
  | afterOne
  /-- The separator has been seen; the remaining suffix is unrestricted. -/
  | suffix
  /-- A mismatched doubled bit was seen. -/
  | invalid
  deriving DecidableEq

instance : Fintype PairValidateState where
  elems := {.next, .afterZero, .afterOne, .suffix, .invalid}
  complete := by
    intro state
    cases state <;> simp

/-- One automaton step for the pair-encoding validator. -/
def pairValidateStep : PairValidateState → Bool → PairValidateState
  | .next, false => .afterZero
  | .next, true => .afterOne
  | .afterZero, false => .next
  | .afterZero, true => .suffix
  | .afterOne, false => .invalid
  | .afterOne, true => .next
  | .suffix, _ => .suffix
  | .invalid, _ => .invalid

/-- The scanner accepts exactly after it has seen the pair separator. -/
def pairValidateAccept : PairValidateState → Bool
  | .suffix => true
  | _ => false

/-- A total, zero-work-tape validator for the image of `pair`.

The generic scanner consumes the whole input, folds `pairValidateStep` in
finite control, and writes the final Boolean verdict to output cell `1`. -/
def pairValidateTM : TM 0 :=
  scannerTM .next pairValidateStep
    (fun state => if pairValidateAccept state then .one else .zero)

end TM

end Complexity
