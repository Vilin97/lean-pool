/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Tactic.NormNum

/-!
# Algebraic connectivity of a finite simple graph

`algConn G` is the *algebraic connectivity* of a finite simple graph `G`: the
second-smallest eigenvalue of its Laplacian matrix `L(G) = D(G) - A(G)`.

`Matrix.IsHermitian.eigenvalues₀` lists the eigenvalues of a Hermitian matrix in
*antitone* (descending) order, so the smallest eigenvalue (always `0` for a graph
Laplacian) sits at index `card V - 1`, and the second-smallest — the algebraic
connectivity `λ₂` — at index `card V - 2`.
-/

public section

namespace ACMax

open Classical in
/-- Algebraic connectivity of a finite simple graph: the second-smallest eigenvalue
of the graph Laplacian `L(G) = D(G) - A(G)`. -/
noncomputable def algConn {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) : ℝ :=
  (SimpleGraph.posSemidef_lapMatrix ℝ G).isHermitian.eigenvalues₀
    ⟨Fintype.card V - 2, Nat.sub_lt Fintype.card_pos (by norm_num)⟩

end ACMax
