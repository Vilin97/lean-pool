/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module

public import LeanPool.BollobasNikiforov.Definition
public import Mathlib.Combinatorics.SimpleGraph.Clique
import LeanPool.BollobasNikiforov.Spectral.Interlace
import LeanPool.BollobasNikiforov.Spectral.Weighted

/-!
# The Bollobás--Nikiforov inequality

This file exposes the statement of Conjecture `conj:BN` in `docs/sol.tex`.
Adjacency eigenvalues are ordered nonincreasingly and counted with algebraic
multiplicity. Completeness is `G = ⊤`; the hypothesis `G ≠ ⊤` is the paper's
noncomplete assumption. `[Nontrivial V]` is the paper's `n ≥ 2`.
-/

@[expose] public section

namespace BollobasNikiforov

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
Every finite noncomplete simple undirected graph on at least two vertices
satisfies `λ₁(G)² + λ₂(G)² ≤ 2 (1 - 1/ω(G)) |E(G)|`.
-/
theorem lambda1_sq_add_lambda2_sq_le
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nontrivial V]
    (hG : G ≠ ⊤) :
    lambda1 G ^ 2 + lambda2 G ^ 2 ≤
      2 * (1 - 1 / (G.cliqueNum : ℝ)) * (G.edgeFinset.card : ℝ) := by
  rw [← F_adjMatrix_eq G hG]
  have hnn : ∀ i j, (0 : ℝ) ≤ G.adjMatrix ℝ i j := by
    intro i j
    simp only [SimpleGraph.adjMatrix_apply]
    split_ifs <;> norm_num
  have hdiag : ∀ i, G.adjMatrix ℝ i i = 0 := by
    intro i
    simp [SimpleGraph.adjMatrix_apply]
  have hsupp : ∀ i j, ¬ G.Adj i j → G.adjMatrix ℝ i j = 0 := by
    intro i j h
    simp [SimpleGraph.adjMatrix_apply, h]
  calc
    F (G.isHermitian_adjMatrix ℝ)
        ≤ turanFactor G * inner (G.adjMatrix ℝ) (G.adjMatrix ℝ) :=
      weighted (G.isHermitian_adjMatrix ℝ) hnn hdiag hsupp
    _ = 2 * (1 - 1 / (G.cliqueNum : ℝ)) * (G.edgeFinset.card : ℝ) := by
      rw [turanFactor, inner_adjMatrix_self]
      ring

end

end BollobasNikiforov
