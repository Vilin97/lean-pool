/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import LeanPool.ACMax.Band.Final

/-!
# Universal upper bound

`algConn_le_two_of_card`: every simple graph on `Fin n` with exactly `2(n-2)`
edges has algebraic connectivity at most `2`.

This statement is Conjecture 1.5 of T. Kolokolnikov, *Maximizing algebraic
connectivity for certain families of graphs* (Linear Algebra and its
Applications, 2015; arXiv:1412.6147): the complete bipartite graph `K_{2,n-2}`
maximizes algebraic connectivity among all `n`-vertex graphs with `2(n-2)` edges.
This library proves the conjecture, sorry-free and axiom-clean, for every
`n ≥ 4`. The result below is the upper-bound component of the direct
two-range assembly in `Band.Final`: the low-order proof handles `4 ≤ n ≤ 31`,
and the incidence-capacity and exact Moore arguments jointly handle `n ≥ 32`.
-/

public section

namespace ACMax

open Classical in
/-- Every simple graph on `Fin n`, `n ≥ 4`, with exactly `2(n-2)` edges has
algebraic connectivity at most `2`. -/
theorem algConn_le_two_of_card (n : ℕ) (hn : 4 ≤ n) [Nonempty (Fin n)]
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2)) :
    algConn G ≤ 2 :=
  (acmax_conjecture_general n hn).2 G hm

end ACMax
