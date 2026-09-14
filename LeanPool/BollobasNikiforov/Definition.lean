/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-!
# Adjacency eigenvalues

This file records the spectral conventions used in `docs/sol.tex`. The
unordered family is indexed by the vertex type, so algebraic multiplicity is
counted automatically. The ordered family is Mathlib's antitone
`eigenvalues₀`, which is the paper's `λ₁ ≥ ⋯ ≥ λₙ` with `λ₁` at index `0`.
-/

@[expose] public section

namespace BollobasNikiforov

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The adjacency eigenvalues of a finite simple graph, indexed with algebraic
multiplicity by its vertex type. -/
noncomputable def adjacencyEigenvalues
    (G : SimpleGraph V) [DecidableRel G.Adj] : V → ℝ :=
  (G.isHermitian_adjMatrix ℝ).eigenvalues

/-- The adjacency eigenvalues in nonincreasing order. The value at `i` is the
paper's `λ_{i+1}(G)`. -/
noncomputable def adjacencyEigenvalues₀
    (G : SimpleGraph V) [DecidableRel G.Adj] : Fin (Fintype.card V) → ℝ :=
  (G.isHermitian_adjMatrix ℝ).eigenvalues₀

lemma adjacencyEigenvalues₀_antitone
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Antitone (adjacencyEigenvalues₀ G) :=
  (G.isHermitian_adjMatrix ℝ).eigenvalues₀_antitone

/-- The largest adjacency eigenvalue `λ₁(G)`. -/
noncomputable def lambda1
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V] : ℝ :=
  adjacencyEigenvalues₀ G ⟨0, Fintype.card_pos⟩

/-- The second-largest adjacency eigenvalue `λ₂(G)`. -/
noncomputable def lambda2
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V] : ℝ :=
  adjacencyEigenvalues₀ G ⟨1, Fintype.one_lt_card⟩

end BollobasNikiforov
