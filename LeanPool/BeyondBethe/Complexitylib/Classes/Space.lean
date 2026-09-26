/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine
public import LeanPool.BeyondBethe.Complexitylib.Asymptotics

/-!
# Base space complexity classes

This file defines the parametric space complexity classes `DSPACE(S)` and
`NSPACE(S)`, the building blocks from which polynomial and log-space classes
are derived.

Work-tape head positions are bounded directly. The finite input region and its
first trailing blank are free, while farther input-head travel is charged. The
output verdict cell is free, while farther two-way output-head travel is also
charged. This prevents either infinite named tape from becoming hidden workspace.
-/


@[expose] public section

namespace Complexity


/-- `DSPACE(S)` is the class of languages decidable by a deterministic TM using
    `O(S(n))` auxiliary space under `Cfg.WithinDecisionSpace`. -/
def DSPACE (S : ℕ → ℕ) : Set Language :=
  {L | ∃ (k : ℕ) (tm : TM k) (f : ℕ → ℕ),
    tm.DecidesInSpace L f ∧ f =O S}

/-- `NSPACE(S)` is the class of languages decidable by a nondeterministic TM
    using `O(S(n))` auxiliary space under `Cfg.WithinDecisionSpace`. -/
def NSPACE (S : ℕ → ℕ) : Set Language :=
  {L | ∃ (k : ℕ) (tm : NTM k) (f : ℕ → ℕ),
    tm.DecidesInSpace L f ∧ f =O S}

end Complexity
