/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import LeanPool.ArchonFirstProofResults.FirstProof6.Auxiliary
import LeanPool.ArchonFirstProofResults.FirstProof6.Problem6

/-!
# Problem 6 — Large `ε`-light vertex subsets

For a simple graph `G = (V, E)` with Laplacian `L`, a vertex subset `S ⊆ V` is
`ε`-light when `ε • L - L_S` is positive semidefinite, where `L_S` is the
Laplacian of the induced subgraph on `S`. The main result
`Problem6.exists_eps_light_subset` shows that for every `G` and every
`ε ∈ (0, 1]` the vertex set contains an `ε`-light subset `S` with
`(ε / 256) * |V| ≤ |S|`, following the Batson–Spielman–Srivastava barrier method.
The proof lives in `Problem6`; supporting infrastructure is in the `Auxiliary`
sub-modules.
-/
