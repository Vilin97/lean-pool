/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair
-/
module


public import LeanPool.InflationTermination.TriangleInflation

/-!
# Solution to `Palomar.TriangleInflation.ClassificationChallenge`

The Challenge states `TriangleInflation.Graph.classification_NW` over definitions it carries
itself, copied verbatim from `TriangleInflation/Defs.lean` and
`TriangleInflation/Graph/Defs.lean`. This module imports the library, where those same
definitions live under the same names, and declares the same theorem, discharged by the
library's `classification_NW_lib` together with `doubleStar_terminates`
(`TriangleInflation/Graph/ClassificationTheorem.lean` and `Graph/DoubleStarForest.lean`,
paper Theorem 3.2 with the order-two clause of Theorem 3.10).

This Solution sits under its own root module rather than under `Palomar`: Palomar's verifier
puts its recompiled Challenge first on `LEAN_PATH` and Lean resolves every module sharing
that root directory there, so a Solution under `Palomar.*` is never found
(PalomarSubmission#108).
-/

@[expose] public section

namespace TriangleInflation.Graph

/-- **The termination classification for pair-source networks.**

Some finite order of the Navascués–Wolfe hierarchy characterizes compatibility for the
pair-source scenario `Γ` exactly when every connected component of its graph is a double
star, that is, a tree of diameter at most three.

The first conjunct, left to right, is the nontermination half: a graph with any other
component carries, at every order `t ≥ 1`, a law that passes the order-`t` test and has no
model. Right to left it is the reconstruction half. The second conjunct is the order stated
in the paper: on a double-star forest the order-two test already characterizes
compatibility.

Paper Theorem 3.2. -/
theorem classification_NW (Γ : PairGraph) :
    ((∃ t : ℕ, 1 ≤ t ∧ ∀ P : GTarget Γ, IsLaw P → (GNWFeasible Γ t P ↔ GCompatible Γ P))
      ↔ IsDoubleStarForest Γ.G) ∧
    (IsDoubleStarForest Γ.G →
      ∀ P : GTarget Γ, IsLaw P → (GNWFeasible Γ 2 P ↔ GCompatible Γ P)) :=
  ⟨classification_NW_lib Γ, fun hG P hP => doubleStar_terminates Γ hG P hP⟩

end TriangleInflation.Graph
