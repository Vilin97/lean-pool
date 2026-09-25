/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair
-/
module


public import LeanPool.InflationTermination.TriangleInflation

/-!
# Solution to `Palomar.TriangleInflation.Challenge`

The Challenge states `TriangleInflation.no_finite_characterizing_order` over definitions it
carries itself, copied verbatim from `TriangleInflation/Defs.lean`. This module imports the
library, where those same definitions live under the same names, and declares the same
theorem, discharged by the library's `no_finite_characterizing_order_lib`
(`TriangleInflation/Main.lean`, paper Theorem 5.2).

This Solution sits under its own root module rather than under `Palomar`: Palomar's verifier
puts its recompiled Challenge first on `LEAN_PATH` and Lean resolves every module sharing
that root directory there, so a Solution under `Palomar.*` is never found
(PalomarSubmission#108).
-/

@[expose] public section

namespace TriangleInflation

/-- **Nontermination of the inflation hierarchy for the classical triangle.**

For every order `t ≥ 1` there is a three-bit law `P` which is a probability law, which is
ancestral-independence feasible at order `t` (`AIFeasible t P`, the stronger of the two
formalized tests), which is Navascués–Wolfe feasible at order `t` (`NWFeasible t P`), and
which is not triangle compatible (`¬ TriangleCompatible P`).

So no finite order of the hierarchy characterizes the triangle-compatible set: whatever
order `t` is chosen, the order-`t` test admits a law that no triangle model produces.
Paper Theorem 5.2 and the corollary that follows it. -/
theorem no_finite_characterizing_order (t : ℕ) (ht : 1 ≤ t) :
    ∃ P : ThreeBit → ℝ, IsLaw P ∧ AIFeasible t P ∧ NWFeasible t P ∧ ¬ TriangleCompatible P :=
  no_finite_characterizing_order_lib t ht

end TriangleInflation
