/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.RandomAccessMachine.Defs
public import LeanPool.BeyondBethe.Complexitylib.Asymptotics

/-!
# Random-access-machine complexity classes: definitions

This definitions layer places the logarithmic-cost RAM classes over the same
`Language` interface as the Turing-machine classes. It is intentionally
independent of either simulation direction.
-/


@[expose] public section

namespace Complexity

namespace RAM


/-- `RAM.DTIME(T)` is the class of languages decided by a RAM in logarithmic
time `O(T(n))`. -/
def DTIME (T : ℕ → ℕ) : Set Language :=
  {L | ∃ (P : Program) (f : ℕ → ℕ), P.DecidesInTime L f ∧ f =O T}

/-- `RAM.DSPACE(S)` is the class of languages decided by a RAM in logarithmic
space `O(S(n))`. -/
def DSPACE (S : ℕ → ℕ) : Set Language :=
  {L | ∃ (P : Program) (f : ℕ → ℕ), P.DecidesInSpace L f ∧ f =O S}

/-- `RAM.P` is polynomial logarithmic-cost RAM time. -/
def P : Set Language :=
  ⋃ k : ℕ, DTIME (· ^ k)

end RAM

end Complexity
