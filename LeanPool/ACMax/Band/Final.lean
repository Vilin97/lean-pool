/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import LeanPool.ACMax.Band.AssemblyAllRange
public import LeanPool.ACMax.Counting.Windows

/-!
# Final two-range assembly

The conjecture is assembled from the same ranges used in the mathematical
paper:

* `4 ≤ n ≤ 31`;
* `n ≥ 32`.

The second range combines the direct incidence-capacity proof on
`32 ≤ n ≤ 49` with the exact Moore closure for `n ≥ 48`; their overlap at
orders `48` and `49` is harmless.
-/

@[expose] public section

namespace ACMax

open Classical in
/-- Every graph of order at least `32` with exactly `2(n-2)` edges has
algebraic connectivity at most `2`. -/
theorem upperBound_ge_32_exact {n : ℕ} [Nonempty (Fin n)]
    (hn32 : 32 ≤ n) (G : SimpleGraph (Fin n))
    (hm : G.edgeFinset.card = 2 * (n - 2)) : algConn G ≤ 2 := by
  by_cases hn49 : n ≤ 49
  · exact upperBound_range_49 (by omega) hn49 G hm
  · exact upperBound_ge_48_exact (by omega) G hm

open Classical in
/-- The ACMAX conjecture for every order `n ≥ 4`, assembled at the
paper's `31/32` boundary. -/
theorem acmax_conjecture_full :
    ∀ (n : ℕ) [Nonempty (Fin n)], 4 ≤ n →
      algConn (completeBipartiteGraph (Fin 2) (Fin (n - 2))) = 2 ∧
        ∀ G : SimpleGraph (Fin n),
          G.edgeFinset.card = 2 * (n - 2) → algConn G ≤ 2 := by
  intro n _inst hn4
  refine ⟨algConn_completeBipartite_two n hn4, ?_⟩
  intro G hm
  by_cases hn31 : n ≤ 31
  · exact upperBound_moat hn4 hn31 G hm
  · exact upperBound_ge_32_exact (by omega) G hm

open Classical in
/-- Canonical hypothesis-free formulation of the ACMAX conjecture. -/
theorem acmax_conjecture_general :
    ∀ (n : ℕ) [Nonempty (Fin n)], 4 ≤ n →
      algConn (completeBipartiteGraph (Fin 2) (Fin (n - 2))) = 2 ∧
        ∀ G : SimpleGraph (Fin n),
          G.edgeFinset.card = 2 * (n - 2) → algConn G ≤ 2 :=
  acmax_conjecture_full

open Classical in
/-- Every residual graph has algebraic connectivity at most `2`, as an
immediate corollary of the full theorem. -/
theorem residual_algConn_le_two {n : ℕ} [Nonempty (Fin n)]
    (G : SimpleGraph (Fin n)) (h : ResidualCore n G) : algConn G ≤ 2 :=
  (acmax_conjecture_general n (by have := h.n_ge; omega)).2 G h.edge_card

open Classical in
/-- Every graph on `Fin n`, `n ≥ 12`, with exactly `2(n-2)` edges has
algebraic connectivity at most `2`. -/
theorem algConn_le_two_of_card_general (n : ℕ) (hn : 12 ≤ n)
    [Nonempty (Fin n)] (G : SimpleGraph (Fin n))
    (hm : G.edgeFinset.card = 2 * (n - 2)) : algConn G ≤ 2 :=
  (acmax_conjecture_general n (by omega)).2 G hm

end ACMax
