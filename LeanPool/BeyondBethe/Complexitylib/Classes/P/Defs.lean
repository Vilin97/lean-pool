/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Classes.Time
public import LeanPool.BeyondBethe.Complexitylib.Classes.Space

/-!
# P, FP, and PSPACE

This file defines **P** (polynomial time), **FP** (polynomial-time functions),
and **PSPACE** (polynomial space) in terms of the base classes `DTIME` and
`DSPACE`.
-/


@[expose] public section

namespace Complexity


/-- **P** is the class of languages decidable by a deterministic TM in
    polynomial time: `P = ⋃_k DTIME(n^k)`. -/
def P : Set Language :=
  ⋃ k : ℕ, DTIME (· ^ k)

/-- **FP** is the class of functions computable by a deterministic TM in
    polynomial time. -/
def FP : Set (List Bool → List Bool) :=
  {f | ∃ (d k : ℕ) (tm : TM k) (T : ℕ → ℕ),
    tm.ComputesInTime f T ∧ T =O (· ^ d)}

/-- **PSPACE** is the class of languages decidable by a deterministic TM using
    polynomial auxiliary space: `PSPACE = ⋃_k DSPACE(n^k)`. -/
def PSPACE : Set Language :=
  ⋃ k : ℕ, DSPACE (· ^ k)

end Complexity
