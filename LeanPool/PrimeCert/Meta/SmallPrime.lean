/-
Copyright (c) 2026 Kenny Lau, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Bhavik Mehta
-/

import LeanPool.PrimeCert.Meta.PrimeCert

/-! # The `small` certificate method

Looks up a pre-existing `PrimeCert.prime_<n>` declaration (from `SmallPrimes.lean`),
e.g. `PrimeCert.prime_31`. Used as a base case in certificate ladders.
-/

open Lean Meta Elab Qq

namespace PrimeCert.Meta

/-- Syntax for the `small` method: just a numeric literal `n`.
Looks up the declaration `PrimeCert.prime_<n>` in the environment.

```lean
-- In a prime_cert% call:
prime_cert% [small {2; 3; 5; 7}, ...]
-- Each number must have a corresponding `PrimeCert.prime_<n>` theorem.
```
-/
syntax smallSpec := num

/-- The `small` certification method: parse a numeral `n` and return the proof term
`PrimeCert.prime_<n>` for its primality. -/
def mkSmallProof : PrimeCertMethod ``smallSpec := fun stx _ ↦ match stx with
  | `(smallSpec| $n:num) => do
    have n := n.getNat
    have name : Name := (`PrimeCert).str s!"prime_{n}"
    return ⟨n, mkNatLit n, mkConst name⟩
  | _ => throwUnsupportedSyntax

open Lean.Elab.Command in
run_cmd declareStepGroupSyntax "small" ``smallSpec

end PrimeCert.Meta
