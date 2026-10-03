/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Classes.Time

/-!
# Exponential time complexity classes

This file defines **EXP** and **NEXP**, the exponential-time analogues of P
and NP respectively.
-/


@[expose] public section

namespace Complexity

/-- **EXP** is the class of languages decidable by a deterministic TM in
    exponential time: `EXP = ⋃_k DTIME(2^(n^k))`. -/
def EXP : Set Language :=
  ⋃ k : ℕ, DTIME (fun n => 2 ^ n ^ k)

/-- **NEXP** is the class of languages decidable by a nondeterministic TM in
    exponential time: `NEXP = ⋃_k NTIME(2^(n^k))`. -/
def NEXP : Set Language :=
  ⋃ k : ℕ, NTIME (fun n => 2 ^ n ^ k)

end Complexity
