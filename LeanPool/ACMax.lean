/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/

import LeanPool.ACMax.UpperBound
import LeanPool.ACMax.Reduction.GapReduction

/-!
# Kolokolnikov's ACMAX conjecture

Source: arxiv:1412.6147, doi:10.1016/j.laa.2014.12.023, url:https://github.com/MerLeanProver/ACMaxConjecture/tree/78736ca2f5c29a4d5ad7dfdee4ac715bbfcde770
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
Status: verified
Main declarations: `ACMax.acmax_conjecture`
Tags: spectral-graph-theory, extremal-graph-theory, laplacian, non-backtracking-walks
MSC: 05C50, 05C35
-/

/-!
# ACMAX conjecture (algebraic-connectivity maximizer for `m = 2(n-2)`)

For `n ≥ 4`, among all simple graphs on `n` vertices with exactly `2(n-2)` edges,
the algebraic connectivity is at most `2`, and this bound is attained by the complete
bipartite graph `K_{2,n-2}` (whose algebraic connectivity equals `2`).

The statement decomposes into the equality clause (`algConn_completeBipartite_two`)
and the universal upper-bound clause (`algConn_le_two_of_card`).
-/

namespace ACMax

open Classical in
/-- **ACMAX conjecture.** For `n ≥ 4`, the complete bipartite graph `K_{2,n-2}` has
algebraic connectivity `2`, and every simple graph on `n` vertices with exactly
`2(n-2)` edges has algebraic connectivity at most `2`. -/
theorem acmax_conjecture (n : ℕ) (hn : 4 ≤ n) [Nonempty (Fin n)] :
    algConn (completeBipartiteGraph (Fin 2) (Fin (n - 2))) = 2 ∧
      ∀ G : SimpleGraph (Fin n), G.edgeFinset.card = 2 * (n - 2) → algConn G ≤ 2 :=
  ⟨algConn_completeBipartite_two n hn,
    fun G hm => algConn_le_two_of_card n hn G hm⟩

end ACMax
