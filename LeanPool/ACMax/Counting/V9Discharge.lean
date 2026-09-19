/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
import Mathlib.Tactic.Convert
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Lift
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import LeanPool.ACMax.Counting.CompactCell
import LeanPool.ACMax.Counting.DoubleStar
import LeanPool.ACMax.Counting.StarvedCensus
import LeanPool.ACMax.Counting.SqrtGirth

/-!
# The tier-9 girth discharge of the starved census

Kills the never-firing starved census import-free for `n ≥ 388`, by a girth
argument on the honest population `V₉ = {v : deg v ≤ 4}` (twins and sea together).
On the window boundary the deg-4-only sea has excess `O(1)`, but including the
twins turns the honest excess into `t₉ = n − 4 − X − 3h = Θ(n)` (`X = excessX`,
`h = #heavies`), which the SQRT girth bound consumes.

## Main results

* `v9_size_row`, `v9_density_row_quant` — the tight size row `n ≤ |V₉| + X` and the
  honest quantitative excess `v9Pairs ≥ 2|V₉| + 2·t₉`.
* `v9_short_cycle_fires`, `v9_girth` — the direct deg-`≤ 4` instance of
  `master_cycle_fires` (a `V₉`-cycle with `9k ≤ n + 8` fires), so a never-firing
  graph has no short `V₉`-cycle.
* `GirthExcessBound`, `girth_excess_bound_holds` — the census-free girth import and
  its unconditional proof, assembling the SQRT cluster with a component descent.
* `starved_v9_kill_of_import`, `starved_v9_kill_sqrt` — the rebased kill, with the
  import discharged via the self-provable SQRT Moore side condition.
* `strip_cubic`, `moore_strip_core`, `moore_strip_arith`, `starved_dead_ge_388` —
  the import-free kill of the whole starved census for `n ≥ 388`, a single branch:
  the derived constraint `10X + 7h ≤ 4n − 200` (`slots_p_row`,
  `p_choke_row_unconditional`, `heavy_full_budget`) discharges the SQRT side
  condition at the ball radius `r = ⌊(⌊(n+8)/9⌋ − 1)/2⌋`.  The former `n ≥ 1100`
  threshold came from three separate losses in the girth bound (see
  `GirthExcessBound`) and a `119`-fold giant credit in `heavy_full_budget`.
-/

namespace ACMax

open Finset

open Classical in
/-- **The honest tier-9 population `V₉`**: the degree-`≤ 4` vertices (the twins `deg 3` together
with the sea `deg 4`).  Its complement is exactly the heavies `{deg ≥ 5}`, so `V₉` is almost
everything and its internal excess is `Θ(n)`. -/
noncomputable def v9Set {n : ℕ} (G : SimpleGraph (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun v => G.degree v ≤ 4)

open Classical in
/-- Membership in the tier-9 population. -/
theorem mem_v9Set {n : ℕ} {G : SimpleGraph (Fin n)} {v : Fin n} :
    v ∈ v9Set G ↔ G.degree v ≤ 4 := by
  unfold v9Set; simp

open Classical in
/-- **Ordered adjacent pairs within `V₉`** (twice the number of internal tier-9 edges);
`2·|V₉| < v9Pairs G` is the density row "average tier-9 degree `> 2`". -/
noncomputable def v9Pairs {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  ((v9Set G ×ˢ v9Set G).filter (fun q => G.Adj q.1 q.2)).card

open Classical in
/-- **The tier-9 size row.**  `n ≤ |V₉| + X` (`X = excessX n G`): `Fin n` partitions as
`V₉ ⊔ V₉ᶜ` with `V₉ᶜ ⊆ {deg ≥ 5}`, so `|V₉ᶜ| ≤ |heavies| ≤ X` (`heavy_le_excess`).  The twins
and sea are all inside `V₉`, so the size row is tight (`|V₉| ≥ n − X`, not `n − 8 − 2X`). -/
theorem v9_size_row {n : ℕ} (G : SimpleGraph (Fin n)) :
    n ≤ (v9Set G).card + excessX n G := by
  have hRsub : (v9Set G)ᶜ ⊆ Finset.univ.filter (fun w => 5 ≤ G.degree w) := by
    intro v hv
    rw [Finset.mem_compl, mem_v9Set] at hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, by omega⟩
  have hRcard : (v9Set G)ᶜ.card ≤ excessX n G :=
    le_trans (Finset.card_le_card hRsub) (heavy_le_excess G)
  have hcardsum : (v9Set G).card + (v9Set G)ᶜ.card = n := by
    rw [Finset.card_add_card_compl, Fintype.card_fin]
  omega

open Classical in
/-- **The tier-9 quantitative density row** (the honest `t₉ = Θ(n)`).  On a census graph
(`m = 2(n−2)`, `n ≥ 2`) the internal tier-9 pairs satisfy
`2|V₉| + 2n ≤ v9Pairs + 2X + 6h + 8` (`X = excessX n G`, `h = |V₉ᶜ|`), i.e.
`v9Pairs ≥ 2|V₉| + 2·t₉` with the honest excess `t₉ = n − 4 − X − 3h`.  The twins are inside
`V₉`, so the only leakage is to `V₉ᶜ ⊆ heavies`: the total-degree identity `∑ deg = 4n − 8`
(`residual_degree_sum`) and the bipartite `cross_count` give `v9Pairs ≥ 4n − 8 − 2∑_R deg`, and
`∑_R deg = ∑_R(deg − 4) + 4h ≤ X + 4h`. -/
theorem v9_density_row_quant {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 2 ≤ n)
    (hm : G.edgeFinset.card = 2 * (n - 2)) :
    2 * (v9Set G).card + 2 * n
      ≤ v9Pairs G + 2 * excessX n G + 6 * (v9Set G)ᶜ.card + 8 := by
  have hL : ∀ v : Fin n, (G.neighborFinset v ∩ v9Set G).card
      = ∑ w ∈ v9Set G, (if G.Adj v w then 1 else 0) := by
    intro v
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    exact Finset.sum_congr rfl (fun w _ => by simp only [G.mem_neighborFinset])
  have hSP : v9Pairs G = ∑ v ∈ v9Set G, (G.neighborFinset v ∩ v9Set G).card := by
    unfold v9Pairs
    rw [Finset.card_filter, Finset.sum_product]
    exact Finset.sum_congr rfl (fun a _ => (hL a).symm)
  have hpartv : ∀ v ∈ v9Set G,
      (G.neighborFinset v ∩ v9Set G).card + (G.neighborFinset v \ v9Set G).card
        = G.degree v := by
    intro v _
    rw [Finset.card_inter_add_card_sdiff, G.card_neighborFinset_eq_degree]
  have hsumV : v9Pairs G + ∑ v ∈ v9Set G, (G.neighborFinset v \ v9Set G).card
      = ∑ v ∈ v9Set G, G.degree v := by
    rw [hSP, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hpartv
  have hsdiff : ∀ v : Fin n, G.neighborFinset v \ v9Set G
      = G.neighborFinset v ∩ (v9Set G)ᶜ := by
    intro v; ext x
    simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_compl]
  have hLeave : ∑ v ∈ v9Set G, (G.neighborFinset v \ v9Set G).card
      ≤ ∑ w ∈ (v9Set G)ᶜ, G.degree w := by
    calc ∑ v ∈ v9Set G, (G.neighborFinset v \ v9Set G).card
        = ∑ v ∈ v9Set G, (G.neighborFinset v ∩ (v9Set G)ᶜ).card :=
          Finset.sum_congr rfl (fun v _ => by rw [hsdiff v])
      _ = ∑ w ∈ (v9Set G)ᶜ, (G.neighborFinset w ∩ v9Set G).card :=
          cross_count G (v9Set G) (v9Set G)ᶜ
      _ ≤ ∑ w ∈ (v9Set G)ᶜ, G.degree w :=
          Finset.sum_le_sum (fun w _ => by
            rw [← G.card_neighborFinset_eq_degree]
            exact Finset.card_le_card Finset.inter_subset_left)
  have htot : ∑ v : Fin n, G.degree v = 4 * n - 8 := residual_degree_sum n hn G hm
  have hsplit : (∑ v ∈ v9Set G, G.degree v) + ∑ w ∈ (v9Set G)ᶜ, G.degree w
      = ∑ v : Fin n, G.degree v := Finset.sum_add_sum_compl (v9Set G) (fun v => G.degree v)
  have hRsub : (v9Set G)ᶜ ⊆ Finset.univ.filter (fun w => 5 ≤ G.degree w) := by
    intro v hv
    rw [Finset.mem_compl, mem_v9Set] at hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, by omega⟩
  have hRexc : ∑ w ∈ (v9Set G)ᶜ, (G.degree w - 4) ≤ excessX n G := by
    unfold excessX
    exact Finset.sum_le_sum_of_subset hRsub
  have hRdeg : ∑ w ∈ (v9Set G)ᶜ, G.degree w
      = (∑ w ∈ (v9Set G)ᶜ, (G.degree w - 4)) + 4 * (v9Set G)ᶜ.card := by
    have hpt : ∀ w ∈ (v9Set G)ᶜ, G.degree w = (G.degree w - 4) + 4 := by
      intro w hw
      rw [Finset.mem_compl, mem_v9Set] at hw
      omega
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm]
  have hcardsum : (v9Set G).card + (v9Set G)ᶜ.card = n := by
    rw [Finset.card_add_card_compl, Fintype.card_fin]
  omega

open Classical in
/-- **N3 — the census-free girth import (SW5′).**  The single graph-generic girth surface that
replaces the falsified `AHLSeaTier9`/`AHLSeaTier18` bylines: quantified over an *arbitrary*
*nonempty* subset `S : Finset (Fin n)` and its excess `t` (no `seaSet`, no `excessX` — nothing
census; the `S.Nonempty` guard closes the vacuous `S = ∅, t = 0` slot where both side conditions
hold but no cycle can land), it says a subgraph on `S` with excess `2|S| + 2t ≤ pairs(S)`
(i.e. `e(S) ≥ |S| + t`) that also meets the
strength-specific Moore side condition — here the self-provable **SQRT** form, stated at the ball
*radius* `r` rather than at a cycle-length target, as

  `|S|² < |S|·(2r + 1) + t·(3r² − r)`

— contains a cycle of length `3 ≤ k ≤ 2r + 1` inside `S`.  This is the exact negation of the
`sqrt_double_count` conclusion transported from the `2`-core to `S`, so no strength is thrown away
between the ball count and the side condition: the older shape `2|S|² ≤ (L − 5)²·t` is the same
inequality after discarding the `|S|(2r+1)` ball term, weakening the level floor `|L_i| ≥ deg` to
`≥ 2`, and rounding `2r ≥ L − 2` down to `L − 5`.  Recovering those three losses is what moves the
import-free floor from `n ≥ 1071` to `n ≥ 379`.  Threaded through intermediate bounds and discharged by `girth_excess_bound_holds` below.
The separate AHL strength reaches further down the band. -/
def GirthExcessBound (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ (S : Finset (Fin n)) (t r : ℕ), S.Nonempty → 1 ≤ t → 1 ≤ r →
    2 * S.card + 2 * t ≤ ((S ×ˢ S).filter (fun q => G.Adj q.1 q.2)).card →
    S.card ^ 2 < S.card * (2 * r + 1) + t * (3 * r ^ 2 - r) →
    ∃ k : ℕ, 3 ≤ k ∧ k ≤ 2 * r + 1 ∧
      ∃ c : ZMod k → Fin n, Function.Injective c ∧
        (∀ i : ZMod k, G.Adj (c i) (c (i + 1))) ∧ (∀ i : ZMod k, c i ∈ S)

end ACMax

/-! ## The SQRT discharge of `GirthExcessBound`

Assembles the SQRT girth cluster into `girth_excess_bound_holds : ∀ n G,
GirthExcessBound n G`. The one new ingredient is the **component descent**: after
extracting a min-degree-2 core (`two_core_aux`), a mediant/pigeonhole selects a
component `C` on which `sqrt_double_count` gives `|C|·(1+2r) + 2·t_C·r² ≤ |C|²`,
colliding with the SQRT side condition to force a short cycle that lifts back to
`G`. `starved_v9_kill_sqrt` is the rebased kill with this import discharged. -/

namespace ACMax

open SimpleGraph Finset

variable {V : Type*}

open Classical in
/-- **Induced degree equals the within-`S` degree.**  For `w ∈ S`, the degree of `w` in the induced
subgraph `G.induce ↑S` is exactly `degWithin G S w`. -/
theorem induce_degree_eq_degWithin (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (w : (↑S : Set V)) :
    (G.induce (↑S : Set V)).degree w = degWithin G S w.val := by
  classical
  rw [degWithin, ← SimpleGraph.card_neighborFinset_eq_degree]
  refine Finset.card_bij (fun (u : (↑S : Set V)) _ => (u : V)) ?_ ?_ ?_
  · intro u hu
    rw [SimpleGraph.mem_neighborFinset, SimpleGraph.induce_adj] at hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_coe.mp u.2, hu⟩
  · intro u1 _ u2 _ heq
    exact Subtype.ext heq
  · intro z hz
    rw [Finset.mem_filter] at hz
    refine ⟨⟨z, Finset.mem_coe.mpr hz.1⟩, ?_, rfl⟩
    rw [SimpleGraph.mem_neighborFinset, SimpleGraph.induce_adj]
    exact hz.2

open Classical in
/-- **Component degree preservation.**  In a graph `H`, the degree of a vertex `u` in the induced
graph on its connected component's support equals its degree in `H`, since every neighbour of `u`
lies in the same component. -/
theorem degree_induce_supp_eq [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (C : H.ConnectedComponent) (u : (C.supp : Set V)) :
    (H.induce (C.supp : Set V)).degree u = H.degree u.val := by
  have hsub : H.neighborSet u.val ⊆ C.supp := fun w hw => C.mem_supp_of_adj_mem_supp u.2 hw
  exact SimpleGraph.degree_induce_of_neighborSet_subset hsub

open Classical in
/-- **Component size as a fibre.**  The number of vertices in a connected component `C` equals the
number of vertices mapping to `C` under `connectedComponentMk`. -/
theorem card_supp_eq_fiber [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    [DecidableEq H.ConnectedComponent] (C : H.ConnectedComponent) :
    Fintype.card C.supp
      = (Finset.univ.filter (fun v => H.connectedComponentMk v = C)).card := by
  rw [← Set.toFinset_card]
  congr 1
  ext v
  simp only [Set.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and,
    ConnectedComponent.mem_supp_iff]

open Classical in
/-- **Component degree sum.**  Summing `H.degree` over the vertices of a connected component `C`
equals twice the edge count of `C.toSimpleGraph`, via the component handshake and degree
preservation. -/
theorem sum_degree_component_eq [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] [DecidableEq H.ConnectedComponent] (C : H.ConnectedComponent) :
    ∑ v ∈ Finset.univ.filter (fun v => H.connectedComponentMk v = C), H.degree v
      = 2 * (H.induce (C.supp : Set V)).edgeFinset.card := by
  have hstep : (∑ v ∈ Finset.univ.filter (fun v => H.connectedComponentMk v = C), H.degree v)
      = ∑ a : {v // v ∈ C.supp}, H.degree (a : V) := by
    apply Finset.sum_subtype
    intro x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ConnectedComponent.mem_supp_iff]
  rw [hstep, ← (H.induce (C.supp : Set V)).sum_degrees_eq_twice_card_edges]
  exact Finset.sum_congr rfl (fun a _ => (degree_induce_supp_eq H C a).symm)

open Classical in
/-- **The mediant pigeonhole.**  Given nonneg fibre sizes `nc` and excesses `tc` over a nonempty
finite index with total size `N` and total excess `≥ t`, some index `C` satisfies
`nc C² · t ≤ N² · tc C`.  Otherwise summing the strict reverse inequalities collides with
`∑ nc² ≤ (∑ nc)² = N²`. -/
theorem exists_mediant_component {κ : Type*} [Fintype κ] (nc tc : κ → ℕ) {N t : ℕ}
    (hne : (Finset.univ : Finset κ).Nonempty) (hN : ∑ C : κ, nc C = N)
    (ht : t ≤ ∑ C : κ, tc C) :
    ∃ C : κ, nc C ^ 2 * t ≤ N ^ 2 * tc C := by
  by_contra hcon
  push Not at hcon
  have hsq : ∑ C : κ, nc C ^ 2 ≤ N ^ 2 := by
    have h1 : ∑ C : κ, nc C ^ 2 ≤ ∑ C : κ, nc C * N := by
      apply Finset.sum_le_sum
      intro C _
      have hle : nc C ≤ N := by
        rw [← hN]
        exact Finset.single_le_sum (fun D _ => Nat.zero_le _) (Finset.mem_univ C)
      calc nc C ^ 2 = nc C * nc C := pow_two (nc C)
        _ ≤ nc C * N := by gcongr
    calc ∑ C : κ, nc C ^ 2 ≤ ∑ C : κ, nc C * N := h1
      _ = (∑ C : κ, nc C) * N := by rw [Finset.sum_mul]
      _ = N * N := by rw [hN]
      _ = N ^ 2 := (pow_two N).symm
  have hsum : N ^ 2 * ∑ C : κ, tc C < t * ∑ C : κ, nc C ^ 2 := by
    have hlt : ∑ C : κ, N ^ 2 * tc C < ∑ C : κ, nc C ^ 2 * t :=
      Finset.sum_lt_sum_of_nonempty hne (fun C _ => hcon C)
    calc N ^ 2 * ∑ C : κ, tc C = ∑ C : κ, N ^ 2 * tc C := by rw [Finset.mul_sum]
      _ < ∑ C : κ, nc C ^ 2 * t := hlt
      _ = t * ∑ C : κ, nc C ^ 2 := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun C _ => by ring)
  have hbad : N ^ 2 * t < N ^ 2 * t := by
    calc N ^ 2 * t ≤ N ^ 2 * ∑ C : κ, tc C := by gcongr
      _ < t * ∑ C : κ, nc C ^ 2 := hsum
      _ ≤ t * N ^ 2 := by gcongr
      _ = N ^ 2 * t := by ring
  exact absurd hbad (lt_irrefl _)

open Classical in
/-- The girth-excess bound holds for every graph. A nonempty vertex set `S` with at least
`2 * S.card + 2 * t` ordered adjacent pairs and
`S.card ^ 2 < S.card * (2 * r + 1) + t * (3 * r ^ 2 - r)`, for positive `t` and `r`,
contains a cycle of length between `3` and `2 * r + 1`. The proof extracts a
minimum-degree-two core, selects an excess-carrying component, applies the
short-cycle bound, and lifts the cycle through the induced-graph embeddings. -/
theorem girth_excess_bound_holds (n : ℕ) (G : SimpleGraph (Fin n)) : GirthExcessBound n G := by
  classical
  intro S t r hSne ht1 hr1 hpairs hside
  have hScard1 : 1 ≤ S.card := Finset.card_pos.mpr hSne
  -- Rewrite the pair count as the within-`S` degree sum, then extract the `2`-core.
  have hpairs' : 2 * S.card + 2 * t ≤ edgeSumWithin G S := by
    rw [edgeSumWithin_eq_pairs]; exact hpairs
  obtain ⟨S', hS'sub, hS'ne, hS'min, hS'inv⟩ := two_core_aux G ht1 S hpairs'
  set H : SimpleGraph (↥(↑S' : Set (Fin n))) := G.induce (↑S' : Set (Fin n)) with hHdef
  have : Nonempty (↥(↑S' : Set (Fin n))) := (Finset.coe_nonempty.mpr hS'ne).to_subtype
  have : DecidableEq H.ConnectedComponent := Classical.decEq _
  have hcardV' : Fintype.card (↥(↑S' : Set (Fin n))) = S'.card := by
    rw [← Set.toFinset_card, Finset.toFinset_coe]
  set NN : ℕ := Fintype.card (↥(↑S' : Set (Fin n))) with hNNdef
  have hHexc : NN + t ≤ H.edgeFinset.card := by
    have hDS : edgeSumWithin G S' = 2 * H.edgeFinset.card := by
      rw [edgeSumWithin_eq_pairs]; exact induced_pairs_eq_two_mul_edges G S'
    rw [hcardV']; omega
  have hHmin : ∀ w : ↥(↑S' : Set (Fin n)), 2 ≤ H.degree w := by
    intro w
    have hh : H.degree w = degWithin G S' w.val := induce_degree_eq_degWithin G S' w
    rw [hh]
    exact hS'min w.val (Finset.mem_coe.mp w.2)
  -- Component partition data.
  have hnc_le_ec : ∀ C : H.ConnectedComponent,
      Fintype.card C.supp ≤ (H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).edgeFinset.card := by
    intro C
    have hkey := sum_degree_component_eq H C
    have hconst : ∑ _v ∈ Finset.univ.filter (fun v => H.connectedComponentMk v = C), (2 : ℕ)
        = 2 * Fintype.card C.supp := by
      rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm, card_supp_eq_fiber H C]
    have hge : 2 * Fintype.card C.supp
        ≤ ∑ v ∈ Finset.univ.filter (fun v => H.connectedComponentMk v = C), H.degree v := by
      rw [← hconst]
      exact Finset.sum_le_sum (fun v _ => hHmin v)
    rw [hkey] at hge
    omega
  have hcard_sum : ∑ C : H.ConnectedComponent, Fintype.card C.supp = NN := by
    have hfw := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (↥(↑S' : Set (Fin n)))))
      (t := (Finset.univ : Finset H.ConnectedComponent))
      (f := H.connectedComponentMk) (fun v _ => Finset.mem_univ _)
    simp only [Finset.card_univ] at hfw
    rw [hNNdef, hfw]
    exact Finset.sum_congr rfl (fun C _ => card_supp_eq_fiber H C)
  have hedge_part : ∑ C : H.ConnectedComponent,
      (H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).edgeFinset.card = H.edgeFinset.card := by
    have hfib := Finset.sum_fiberwise (Finset.univ : Finset (↥(↑S' : Set (Fin n))))
      H.connectedComponentMk (fun v => H.degree v)
    have hhand := H.sum_degrees_eq_twice_card_edges
    have h2 : ∑ C : H.ConnectedComponent,
          2 * (H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).edgeFinset.card
        = 2 * H.edgeFinset.card := by
      rw [← hhand, ← hfib]
      exact Finset.sum_congr rfl (fun C _ => (sum_degree_component_eq H C).symm)
    rw [← Finset.mul_sum] at h2
    omega
  have htc_sum : t ≤ ∑ C : H.ConnectedComponent,
      ((H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).edgeFinset.card - Fintype.card C.supp) := by
    have hsplit : (∑ C : H.ConnectedComponent,
          ((H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).edgeFinset.card - Fintype.card C.supp))
          + ∑ C : H.ConnectedComponent, Fintype.card C.supp
        = ∑ C : H.ConnectedComponent,
          (H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).edgeFinset.card := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun C _ => Nat.sub_add_cancel (hnc_le_ec C))
    rw [hcard_sum, hedge_part] at hsplit
    omega
  have hne : (Finset.univ : Finset H.ConnectedComponent).Nonempty := Finset.univ_nonempty
  -- Select the excess-carrying component via the mediant.
  obtain ⟨C, hmed⟩ := exists_mediant_component
    (fun C : H.ConnectedComponent => Fintype.card C.supp)
    (fun C : H.ConnectedComponent =>
      (H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).edgeFinset.card - Fintype.card C.supp)
    hne hcard_sum htc_sum
  have hmed2 : Fintype.card (C.supp : Set (↥(↑S' : Set (Fin n)))) ^ 2 * t
      ≤ NN ^ 2 * ((H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).edgeFinset.card
        - Fintype.card C.supp) := hmed
  have : Nonempty (C.supp : Set (↥(↑S' : Set (Fin n)))) :=
    (SimpleGraph.ConnectedComponent.nonempty_supp C).to_subtype
  -- No cycle of length `≤ 2r+1` collides with the SQRT side condition, so a short cycle exists.
  have hcyc : ∃ (u : (C.supp : Set (↥(↑S' : Set (Fin n)))))
      (w : (H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).Walk u u),
      w.IsCycle ∧ w.length ≤ 2 * r + 1 := by
    by_contra hcon
    push Not at hcon
    have hg : ∀ (u : (C.supp : Set (↥(↑S' : Set (Fin n)))))
        (w : (H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).Walk u u),
        w.IsCycle → 2 * r + 1 < w.length := fun u w hw => hcon u w hw
    have hmin_C : ∀ u : (C.supp : Set (↥(↑S' : Set (Fin n)))),
        2 ≤ (H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).degree u := by
      intro u
      rw [degree_induce_supp_eq H C u]
      exact hHmin u.val
    have hconn_C : (H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).Connected :=
      SimpleGraph.ConnectedComponent.connected_toSimpleGraph C
    have hle := hnc_le_ec C
    have hexc_C : Fintype.card (C.supp : Set (↥(↑S' : Set (Fin n))))
        + ((H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).edgeFinset.card - Fintype.card C.supp)
        ≤ (H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).edgeFinset.card := by omega
    have hsqrt := sqrt_double_count (H.induce (C.supp : Set (↥(↑S' : Set (Fin n)))))
      hmin_C hg hconn_C hexc_C
    -- Abbreviations for the arithmetic collision.
    set nc := Fintype.card (C.supp : Set (↥(↑S' : Set (Fin n)))) with hncval
    set ec := (H.induce (C.supp : Set (↥(↑S' : Set (Fin n))))).edgeFinset.card with hecval
    set w : ℕ := 3 * r ^ 2 - r with hwdef
    have hncpos : 0 < nc := Fintype.card_pos
    have hncNN : nc ≤ NN := by
      rw [← hcard_sum]
      exact Finset.single_le_sum (f := fun D : H.ConnectedComponent => Fintype.card D.supp)
        (fun D _ => Nat.zero_le _) (Finset.mem_univ C)
    have hNleS : NN ≤ S.card := by
      rw [hcardV']; exact Finset.card_le_card hS'sub
    -- (i) Multiply the component ball count by `NN²` and feed in the mediant, so that the
    -- component excess `ec − nc` is replaced by the global excess `t`.
    have key1 : NN ^ 2 * (nc * (2 * r + 1)) + w * (nc ^ 2 * t) ≤ NN ^ 2 * nc ^ 2 := by
      have hstep : w * (nc ^ 2 * t) ≤ NN ^ 2 * ((ec - nc) * w) := by
        calc w * (nc ^ 2 * t) ≤ w * (NN ^ 2 * (ec - nc)) := Nat.mul_le_mul_left w hmed2
          _ = NN ^ 2 * ((ec - nc) * w) := by ring
      calc NN ^ 2 * (nc * (2 * r + 1)) + w * (nc ^ 2 * t)
          ≤ NN ^ 2 * (nc * (1 + 2 * r)) + NN ^ 2 * ((ec - nc) * w) := by
            have hcomm : NN ^ 2 * (nc * (2 * r + 1)) = NN ^ 2 * (nc * (1 + 2 * r)) := by ring
            rw [hcomm]
            exact Nat.add_le_add_left hstep _
        _ = NN ^ 2 * (nc * (1 + 2 * r) + (ec - nc) * w) := by ring
        _ ≤ NN ^ 2 * nc ^ 2 := Nat.mul_le_mul_left _ hsqrt
    -- (ii) Trade one factor `NN` for `nc` in the ball term and cancel `nc²`.
    have key2 : NN * (2 * r + 1) + t * w ≤ NN ^ 2 := by
      have hmul : (NN * (2 * r + 1) + t * w) * nc ^ 2 ≤ NN ^ 2 * nc ^ 2 := by
        have hswap : NN * (2 * r + 1) * nc ^ 2 ≤ NN ^ 2 * (nc * (2 * r + 1)) := by
          have e1 : NN * (2 * r + 1) * nc ^ 2 = (nc * (2 * r + 1)) * (nc * NN) := by ring
          have e2 : NN ^ 2 * (nc * (2 * r + 1)) = (nc * (2 * r + 1)) * (NN * NN) := by ring
          rw [e1, e2]
          gcongr
        have hrest : t * w * nc ^ 2 = w * (nc ^ 2 * t) := by ring
        calc (NN * (2 * r + 1) + t * w) * nc ^ 2
            = NN * (2 * r + 1) * nc ^ 2 + t * w * nc ^ 2 := by ring
          _ ≤ NN ^ 2 * (nc * (2 * r + 1)) + w * (nc ^ 2 * t) := by
              rw [hrest]; exact Nat.add_le_add_right hswap _
          _ ≤ NN ^ 2 * nc ^ 2 := key1
      exact Nat.le_of_mul_le_mul_right hmul (pow_pos hncpos 2)
    -- (iii) Transport `NN ↦ |S|`: `x ↦ x² − x(2r+1)` is monotone above `(2r+1)/2`, and `key2`
    -- itself forces `2r + 1 ≤ NN`.
    have hNNpos : 0 < NN := lt_of_lt_of_le hncpos hncNN
    have h2r1 : 2 * r + 1 ≤ NN := by
      have h : NN * (2 * r + 1) ≤ NN * NN := by
        calc NN * (2 * r + 1) ≤ NN * (2 * r + 1) + t * w := Nat.le_add_right _ _
          _ ≤ NN ^ 2 := key2
          _ = NN * NN := by ring
      exact Nat.le_of_mul_le_mul_left h hNNpos
    have hmono : NN ^ 2 + S.card * (2 * r + 1) ≤ S.card ^ 2 + NN * (2 * r + 1) := by
      obtain ⟨d, hd⟩ : ∃ d, S.card = NN + d := ⟨S.card - NN, by omega⟩
      have h1 : d * (2 * r + 1) ≤ d * NN := Nat.mul_le_mul_left d h2r1
      rw [hd]
      nlinarith [h1]
    -- (iv) Collide with the side condition.
    omega
  -- Lift the short cycle from the component graph to `G` and convert to `ZMod`.
  obtain ⟨u, w, hwcyc, hwlen⟩ := hcyc
  set w1 := w.map
    (SimpleGraph.Embedding.induce (G := H) (C.supp : Set (↥(↑S' : Set (Fin n))))).toHom with hw1def
  set w2 := w1.map (SimpleGraph.Embedding.induce (G := G) (↑S' : Set (Fin n))).toHom with hw2def
  have hw1cyc : w1.IsCycle := by
    rw [hw1def]
    exact hwcyc.map
      (SimpleGraph.Embedding.induce (G := H) (C.supp : Set (↥(↑S' : Set (Fin n))))).injective
  have hw2cyc : w2.IsCycle := by
    rw [hw2def]
    exact hw1cyc.map (SimpleGraph.Embedding.induce (G := G) (↑S' : Set (Fin n))).injective
  have hlen : w2.length = w.length := by
    rw [hw2def, hw1def, SimpleGraph.Walk.length_map, SimpleGraph.Walk.length_map]
  have hsupp : ∀ x ∈ w2.support, x ∈ S := by
    intro x hx
    rw [hw2def, SimpleGraph.Walk.support_map, List.mem_map] at hx
    obtain ⟨y, _, rfl⟩ := hx
    exact hS'sub (Finset.mem_coe.mp y.2)
  obtain ⟨hk3, hex⟩ := cycle_walk_to_zmod hw2cyc hsupp
  exact ⟨w2.length, hk3, by omega, hex⟩

end ACMax

/-! ## The honest heavy budget

The one counting row that lives here rather than in `Counting.StarvedCensus`: the heavy budget
`h + h₆₊ + 4·n_g ≤ X`, which the `MASTER′` assembly consumes.  The `n ≥ 388` dispatch that this
section used to carry has been superseded by `Counting.V9DischargeSharp` (`starved_dead_ge_123`),
which runs the same collision at the bulk-credited moat radius of `Counting.MoatSharp`.
-/

namespace ACMax

open Finset

open Classical in
/-- **The honest heavy budget** (D1′).  At `n ≥ 57` the total excess `X = excessX n G` dominates
`h + h₆₊ + 4·n_g`, where `h = |V₉ᶜ|` counts the heavies (`deg ≥ 5`), `h₆₊` the non-giant
deg-`≥6` hubs and `n_g` the giants (`n + 15 < 9·deg`).  Each deg-`≥5` vertex spends `deg − 4 ≥ 1`
excess (that is `h`), each deg-`≥6` non-giant an extra `1` (so `2 ≤ deg − 4`), and each giant
(`deg ≥ 9` already at `n ≥ 57`) an extra `4` (so `5 ≤ deg − 4`).

The giant credit is `4` — exactly what the `MASTER′` assembly consumes (`28·n_g ≤ 7·4·n_g`).  It
used to be `119`, which forced `n ≥ 1100` on this row alone and so on the whole import-free band;
`4` costs the assembly nothing and holds from `n = 57`. -/
theorem heavy_full_budget {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 57 ≤ n) :
    (v9Set G)ᶜ.card
      + ((hubSet G).filter (fun h => 6 ≤ G.degree h ∧ ¬ (n + 15 < 9 * G.degree h))).card
      + 4 * ((hubSet G).filter (fun h => n + 15 < 9 * G.degree h)).card
      ≤ excessX n G := by
  have hhub : hubSet G = Finset.univ.filter (fun v => 4 ≤ G.degree v) := rfl
  have hexc : excessX n G = ∑ v ∈ hubSet G, (G.degree v - 4) := by
    unfold excessX
    rw [hhub]
    refine Finset.sum_subset ?_ ?_
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      omega
    · intro v hv hv2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv hv2
      omega
  have hcard5 : (v9Set G)ᶜ.card = ((hubSet G).filter (fun v => 5 ≤ G.degree v)).card := by
    congr 1
    ext v
    simp only [Finset.mem_compl, mem_v9Set, Finset.mem_filter, mem_hubSet]
    omega
  rw [hexc, hcard5, Finset.card_filter, Finset.card_filter, Finset.card_filter,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro v hv
  rw [mem_hubSet] at hv
  split_ifs <;> omega

end ACMax
