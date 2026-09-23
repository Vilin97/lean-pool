/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import LeanPool.ACMax.Counting.PoorCorner

/-!
# The cherry case (`e(M) ≥ 2`)

The dispatch for the **cherry world** `CaseCherry G` (`4 ≤ mIncidence G`, i.e.
the degree-3 set spans at least two edges), and its unconditional closure in the
sea `e(M) = 2` regime. A *cherry* is a degree-3 centre `z` with two non-adjacent
degree-3 neighbours `x, y`; its three vertices form the `N`-block of a two-block
cut, so any disjoint `3`-block `P` with `2·e(P,N) + leak(P) ≤ 7` closes.

## Main results

* `exists_cherry`, `residualCore_cherry` — a cherry always exists in the cherry
  world (either some degree-3 vertex has two degree-3 neighbours, or the `M`-edges
  form a `≥ 2`-edge matching whose disjoint pairs would give a forbidden `2K₂`).
* `cherry_assemble` and the three cut certificates
  `two_twin_cherry_twoBlock` (a degree-`≤ 5` hub with two iso twins avoiding the
  cherry), `single_vertex_cherry_twoBlock` (an iso apex plus two hub neighbours,
  boundary `2(c₁+c₂) + deg h₁ + deg h₂ ≤ 8 + 2·[h₁~h₂]`) and
  `hub_triangle_cherry_twoBlock` (three mutually adjacent hubs,
  `2·∑cross + ∑deg ≤ 13`).
* `cherryHubs_card_le_five` — at most `5` hubs meet a cherry;
  `shared_twin_hubs_nonadj` — two degree-`≤ 4` hubs on a common twin are
  non-adjacent (a `(3,4,4)`-triangle has `∑deg = 11 ≤ thr(n)`, `n ≥ 18`).
* `six_richLow_twoBlock`, `iso_apex_dichotomy` — the supply-side pigeonhole:
  `≥ 6` rich low hubs close the cherry world, and every iso apex either fires the
  SingleVertex certificate or has `≥ 2` *bad* neighbours (degree `≥ 5` or
  cherry-touching).
* `caseCherry_dichotomy` — under `ResidualCore n G` and `CaseCherry G`, either
  `TwoBlockConfig G`, or the graph sits in the precisely described **blocked
  cherry corner** (a cherry exists, `≤ 5` rich low hubs, every iso twin has `≥ 2`
  bad neighbours).
* `blockedCherryCorner_close`, `caseCherry_algConn_le_two_of_sea_eM_four` — the
  closure of the blocked corner, and hence of the whole cherry case, in the sea
  `Δ ≤ 4`, `e(M) = 2` regime for every `n ≥ 18`.
-/

@[expose] public section

namespace ACMax

variable {V : Type*} [Fintype V]

/-! ## The cherry -/

open Classical in
/-- A **cherry**: a degree-`3` centre `z` with two distinct, non-adjacent degree-`3`
neighbours `x, y` — the `P₃` inside the degree-`3` graph `M` that every `e(M) ≥ 2`
residual contains (`exists_cherry`).  The blocks below always use the cherry as the
`N`-side `{z, x, y}` (leak `≤ 5` for size `3`: excess `−1`, the best small block in the
calculus). -/
structure Cherry (G : SimpleGraph V) (x z y : V) : Prop where
  deg_x : G.degree x = 3
  deg_z : G.degree z = 3
  deg_y : G.degree y = 3
  adj_zx : G.Adj z x
  adj_zy : G.Adj z y
  ne_xy : x ≠ y
  nadj_xy : ¬G.Adj x y

namespace Cherry

variable {G : SimpleGraph V} {x z y : V}

open Classical in
theorem ne_zx (h : Cherry G x z y) : z ≠ x := G.ne_of_adj h.adj_zx

open Classical in
theorem ne_zy (h : Cherry G x z y) : z ≠ y := G.ne_of_adj h.adj_zy

open Classical in
/-- The cherry block `{z, x, y}` has exactly `3` vertices. -/
theorem card_three (h : Cherry G x z y) : ({z, x, y} : Finset V).card = 3 := by
  rw [Finset.card_insert_of_notMem (by simp [h.ne_zx, h.ne_zy]), Finset.card_pair h.ne_xy]

open Classical in
/-- No cherry member is `M`-isolated (each has a degree-`3` neighbour). -/
theorem notMem_isoTwins (h : Cherry G x z y) {v : V} (hv : v ∈ isoTwins G) :
    v ∉ ({z, x, y} : Finset V) := by
  intro hmem
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hmem
  obtain ⟨-, hiso⟩ := mem_isoTwins.mp hv
  rcases hmem with rfl | rfl | rfl
  · exact hiso x h.adj_zx h.deg_x
  · exact hiso z (G.adj_symm h.adj_zx) h.deg_z
  · exact hiso z (G.adj_symm h.adj_zy) h.deg_z

open Classical in
/-- An `M`-isolated twin sends no edge into the cherry. -/
theorem iso_cross_zero (h : Cherry G x z y) {t : V} (ht : t ∈ isoTwins G) :
    (G.neighborFinset t ∩ ({z, x, y} : Finset V)).card = 0 := by
  obtain ⟨-, hiso⟩ := mem_isoTwins.mp ht
  exact nbr_inter_triple_zero G t z x y
    (fun hadj => hiso z hadj h.deg_z)
    (fun hadj => hiso x hadj h.deg_x)
    (fun hadj => hiso y hadj h.deg_y)

end Cherry

/-! ## Small Finset helpers -/

open Classical in
/-- Leak of a single vertex against a block containing `k` of its neighbours. -/
private theorem leak_le_of_inter (G : SimpleGraph V) (p : V) (S : Finset V) (k : ℕ)
    (hk : k ≤ (G.neighborFinset p ∩ S).card) :
    (G.neighborFinset p \ S).card + k ≤ G.degree p := by
  have h := Finset.card_sdiff_add_card_inter (G.neighborFinset p) S
  have hd := G.card_neighborFinset_eq_degree p
  omega

open Classical in
omit [Fintype V] in
private theorem sum_triple (f : V → ℕ) {a b c : V} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : ∑ p ∈ ({a, b, c} : Finset V), f p = f a + f b + f c := by
  rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_pair hbc]
  ring

open Classical in
omit [Fintype V] in
private theorem card_triple {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Finset V).card = 3 := by
  rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]

/-! ## The cherry `N`-side leak bound and the assembly lemma -/

open Classical in
/-- **The cherry leaks at most `5`**: the centre keeps two edges inside (`leak ≤ 1`),
each end keeps one (`leak ≤ 2`).  Size `3`, leak `5`: excess `−1` — the cherry is the
canonical twin-anchored small block of the design's block calculus. -/
theorem cherry_leak_le_five (G : SimpleGraph V) {x z y : V} (hch : Cherry G x z y) :
    ∑ q ∈ ({z, x, y} : Finset V),
      (G.neighborFinset q \ ({z, x, y} : Finset V)).card ≤ 5 := by
  have hzx := hch.ne_zx
  have hzy := hch.ne_zy
  have hxy := hch.ne_xy
  rw [sum_triple _ hzx hzy hxy]
  -- centre: `x, y ∈ N(z) ∩ {z,x,y}`.
  have hz : (G.neighborFinset z \ ({z, x, y} : Finset V)).card + 2 ≤ G.degree z := by
    refine leak_le_of_inter G z _ 2 ?_
    have hsub : ({x, y} : Finset V) ⊆ G.neighborFinset z ∩ ({z, x, y} : Finset V) := by
      intro w hw
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [Finset.mem_inter, G.mem_neighborFinset]
      rcases hw with rfl | rfl
      · exact ⟨hch.adj_zx, by simp⟩
      · exact ⟨hch.adj_zy, by simp⟩
    calc 2 = ({x, y} : Finset V).card := (Finset.card_pair hxy).symm
      _ ≤ _ := Finset.card_le_card hsub
  -- ends: `z ∈ N(x) ∩ {z,x,y}` and `z ∈ N(y) ∩ {z,x,y}`.
  have hx : (G.neighborFinset x \ ({z, x, y} : Finset V)).card + 1 ≤ G.degree x := by
    refine leak_le_of_inter G x _ 1 ?_
    refine Finset.card_pos.mpr ⟨z, ?_⟩
    rw [Finset.mem_inter, G.mem_neighborFinset]
    exact ⟨G.adj_symm hch.adj_zx, by simp⟩
  have hy : (G.neighborFinset y \ ({z, x, y} : Finset V)).card + 1 ≤ G.degree y := by
    refine leak_le_of_inter G y _ 1 ?_
    refine Finset.card_pos.mpr ⟨z, ?_⟩
    rw [Finset.mem_inter, G.mem_neighborFinset]
    exact ⟨G.adj_symm hch.adj_zy, by simp⟩
  have h3z := hch.deg_z
  have h3x := hch.deg_x
  have h3y := hch.deg_y
  omega

open Classical in
/-- **The cherry assembly lemma**: any `3`-block `P` disjoint from the cherry with
`2·e(P, N) + leak(P) ≤ 7` is a two-block witness against the cherry
(`2·e + leak(P) + leak(N) ≤ 7 + 5 = 12 = 4·3`).  All three cherry cut certificates
below are instances. -/
theorem cherry_assemble (G : SimpleGraph V) {x z y : V} (hch : Cherry G x z y)
    (P : Finset V) (hcard : P.card = 3)
    (hdisj : Disjoint P ({z, x, y} : Finset V))
    (hbound : 2 * (∑ p ∈ P, (G.neighborFinset p ∩ ({z, x, y} : Finset V)).card)
        + (∑ p ∈ P, (G.neighborFinset p \ P).card) ≤ 7) :
    TwoBlockConfig G := by
  have hN3 := hch.card_three
  refine ⟨P, {z, x, y}, hdisj, by omega, by omega, ?_⟩
  have hleak := cherry_leak_le_five G hch
  omega

/-! ## The three cherry cut certificates -/

open Classical in
/-- **The TwoTwin cherry certificate** (port of `two_twin_cut_certificate_*` /
`twotwin_assemble_cherry_nineteen`, `n`-generic): a hub `h` with `4 ≤ deg h ≤ 5`
(degree-`5` hubs ARE eligible — the slack that kills the fat regime), two `M`-isolated
twins `t₁ ≠ t₂`, and no edge from `h` into the cherry, yield a two-block witness
`P = {h, t₁, t₂}` against `N = {z, x, y}`:
`leak(P) ≤ (deg h − 2) + 2 + 2 ≤ 7`, `e(P, N) = 0`. -/
theorem two_twin_cherry_twoBlock (G : SimpleGraph V) {x z y h t₁ t₂ : V}
    (hch : Cherry G x z y)
    (hh4 : 4 ≤ G.degree h) (hh5 : G.degree h ≤ 5)
    (ht₁ : t₁ ∈ isoTwins G) (ht₂ : t₂ ∈ isoTwins G) (hne : t₁ ≠ t₂)
    (ha₁ : G.Adj h t₁) (ha₂ : G.Adj h t₂)
    (hnz : ¬G.Adj h z) (hnx : ¬G.Adj h x) (hny : ¬G.Adj h y) :
    TwoBlockConfig G := by
  obtain ⟨hd₁, hiso₁⟩ := mem_isoTwins.mp ht₁
  obtain ⟨hd₂, hiso₂⟩ := mem_isoTwins.mp ht₂
  have hht₁ : h ≠ t₁ := by intro e; rw [e, hd₁] at hh4; omega
  have hht₂ : h ≠ t₂ := by intro e; rw [e, hd₂] at hh4; omega
  set P : Finset V := {h, t₁, t₂} with hP
  have hPcard : P.card = 3 := card_triple hht₁ hht₂ hne
  -- disjointness from the cherry
  have hdisj : Disjoint P ({z, x, y} : Finset V) := by
    rw [Finset.disjoint_left]
    intro p hp hpN
    rw [hP, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hpN
      have hz3 := hch.deg_z
      have hx3 := hch.deg_x
      have hy3 := hch.deg_y
      rcases hpN with rfl | rfl | rfl <;> omega
    · exact hch.notMem_isoTwins ht₁ hpN
    · exact hch.notMem_isoTwins ht₂ hpN
  refine cherry_assemble G hch P hPcard hdisj ?_
  -- cross edges: none.
  have hcross : ∑ p ∈ P, (G.neighborFinset p ∩ ({z, x, y} : Finset V)).card = 0 := by
    rw [hP, sum_triple _ hht₁ hht₂ hne, nbr_inter_triple_zero G h z x y hnz hnx hny,
      hch.iso_cross_zero ht₁, hch.iso_cross_zero ht₂]
  -- leaks.
  have hlh : (G.neighborFinset h \ P).card + 2 ≤ G.degree h := by
    refine leak_le_of_inter G h P 2 ?_
    have hsub : ({t₁, t₂} : Finset V) ⊆ G.neighborFinset h ∩ P := by
      intro w hw
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [Finset.mem_inter, G.mem_neighborFinset]
      rcases hw with rfl | rfl
      · exact ⟨ha₁, by rw [hP]; simp⟩
      · exact ⟨ha₂, by rw [hP]; simp⟩
    calc 2 = ({t₁, t₂} : Finset V).card := (Finset.card_pair hne).symm
      _ ≤ _ := Finset.card_le_card hsub
  have hlt₁ : (G.neighborFinset t₁ \ P).card + 1 ≤ G.degree t₁ := by
    refine leak_le_of_inter G t₁ P 1 ?_
    refine Finset.card_pos.mpr ⟨h, ?_⟩
    rw [Finset.mem_inter, G.mem_neighborFinset]
    exact ⟨G.adj_symm ha₁, by rw [hP]; simp⟩
  have hlt₂ : (G.neighborFinset t₂ \ P).card + 1 ≤ G.degree t₂ := by
    refine leak_le_of_inter G t₂ P 1 ?_
    refine Finset.card_pos.mpr ⟨h, ?_⟩
    rw [Finset.mem_inter, G.mem_neighborFinset]
    exact ⟨G.adj_symm ha₂, by rw [hP]; simp⟩
  rw [hP] at hlh hlt₁ hlt₂
  rw [hcross, hP, sum_triple _ hht₁ hht₂ hne]
  omega

open Classical in
/-- **The SingleVertex cherry certificate** (port of `single_vertex_cut_certificate_*`,
`n`-generic): an `M`-isolated apex `t` with two hub neighbours `h₁ ≠ h₂` satisfying the
exact per-`n` boundary arithmetic

  `2·(c₁ + c₂) + deg h₁ + deg h₂ ≤ 8 + 2·[h₁ ~ h₂]`

(`cᵢ` = the cherry cross count of `hᵢ`) yields a two-block witness `P = {t, h₁, h₂}`:
the apex leaks `≤ 1` and crosses `0` (isolated), each hub leaks
`≤ deg − 1 − [h₁ ~ h₂]`. -/
theorem single_vertex_cherry_twoBlock (G : SimpleGraph V) {x z y t h₁ h₂ : V}
    (hch : Cherry G x z y) (ht : t ∈ isoTwins G)
    (hne : h₁ ≠ h₂) (ha₁ : G.Adj t h₁) (ha₂ : G.Adj t h₂)
    (hd₁ : 4 ≤ G.degree h₁) (hd₂ : 4 ≤ G.degree h₂)
    (hbound : 2 * ((G.neighborFinset h₁ ∩ ({z, x, y} : Finset V)).card
          + (G.neighborFinset h₂ ∩ ({z, x, y} : Finset V)).card)
        + G.degree h₁ + G.degree h₂ ≤ 8 + 2 * adjInd G h₁ h₂) :
    TwoBlockConfig G := by
  obtain ⟨hdt, hisot⟩ := mem_isoTwins.mp ht
  have hth₁ : t ≠ h₁ := by intro e; rw [← e, hdt] at hd₁; omega
  have hth₂ : t ≠ h₂ := by intro e; rw [← e, hdt] at hd₂; omega
  set P : Finset V := {t, h₁, h₂} with hP
  have hPcard : P.card = 3 := card_triple hth₁ hth₂ hne
  have hdisj : Disjoint P ({z, x, y} : Finset V) := by
    rw [Finset.disjoint_left]
    intro p hp hpN
    rw [hP, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hp
    have hz3 := hch.deg_z
    have hx3 := hch.deg_x
    have hy3 := hch.deg_y
    rcases hp with rfl | rfl | rfl
    · exact hch.notMem_isoTwins ht hpN
    · rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hpN
      rcases hpN with rfl | rfl | rfl <;> omega
    · rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hpN
      rcases hpN with rfl | rfl | rfl <;> omega
  refine cherry_assemble G hch P hPcard hdisj ?_
  -- the adjacency indicator
  have hadj01 : adjInd G h₁ h₂ = 0 ∨ adjInd G h₁ h₂ = 1 := by
    unfold adjInd
    split_ifs <;> simp
  -- apex leak `≤ 1`, apex cross `= 0`
  have hlt : (G.neighborFinset t \ P).card + 2 ≤ G.degree t := by
    refine leak_le_of_inter G t P 2 ?_
    have hsub : ({h₁, h₂} : Finset V) ⊆ G.neighborFinset t ∩ P := by
      intro w hw
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [Finset.mem_inter, G.mem_neighborFinset]
      rcases hw with rfl | rfl
      · exact ⟨ha₁, by rw [hP]; simp⟩
      · exact ⟨ha₂, by rw [hP]; simp⟩
    calc 2 = ({h₁, h₂} : Finset V).card := (Finset.card_pair hne).symm
      _ ≤ _ := Finset.card_le_card hsub
  -- hub leaks: `t` is inside, plus the partner when adjacent.
  have hlh₁ : (G.neighborFinset h₁ \ P).card + (1 + adjInd G h₁ h₂) ≤ G.degree h₁ := by
    refine leak_le_of_inter G h₁ P (1 + adjInd G h₁ h₂) ?_
    by_cases hadj : G.Adj h₁ h₂
    · have hsub : ({t, h₂} : Finset V) ⊆ G.neighborFinset h₁ ∩ P := by
        intro w hw
        rw [Finset.mem_insert, Finset.mem_singleton] at hw
        rw [Finset.mem_inter, G.mem_neighborFinset]
        rcases hw with rfl | rfl
        · exact ⟨G.adj_symm ha₁, by rw [hP]; simp⟩
        · exact ⟨hadj, by rw [hP]; simp⟩
      have h2c : ({t, h₂} : Finset V).card = 2 := Finset.card_pair hth₂
      have := Finset.card_le_card hsub
      unfold adjInd
      rw [ite_eq_left hadj]
      omega
    · unfold adjInd
      rw [ite_eq_right hadj]
      refine le_trans (by omega) (Finset.card_pos.mpr ⟨t, ?_⟩)
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨G.adj_symm ha₁, by rw [hP]; simp⟩
  have hlh₂ : (G.neighborFinset h₂ \ P).card + (1 + adjInd G h₁ h₂) ≤ G.degree h₂ := by
    refine leak_le_of_inter G h₂ P (1 + adjInd G h₁ h₂) ?_
    by_cases hadj : G.Adj h₁ h₂
    · have hsub : ({t, h₁} : Finset V) ⊆ G.neighborFinset h₂ ∩ P := by
        intro w hw
        rw [Finset.mem_insert, Finset.mem_singleton] at hw
        rw [Finset.mem_inter, G.mem_neighborFinset]
        rcases hw with rfl | rfl
        · exact ⟨G.adj_symm ha₂, by rw [hP]; simp⟩
        · exact ⟨G.adj_symm hadj, by rw [hP]; simp⟩
      have h2c : ({t, h₁} : Finset V).card = 2 := Finset.card_pair hth₁
      have := Finset.card_le_card hsub
      unfold adjInd
      rw [ite_eq_left hadj]
      omega
    · unfold adjInd
      rw [ite_eq_right hadj]
      refine le_trans (by omega) (Finset.card_pos.mpr ⟨t, ?_⟩)
      rw [Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨G.adj_symm ha₂, by rw [hP]; simp⟩
  rw [hP] at hlt hlh₁ hlh₂
  rw [hP, sum_triple _ hth₁ hth₂ hne, sum_triple _ hth₁ hth₂ hne,
    hch.iso_cross_zero ht]
  omega

/-! ## Cherry extraction -/

open Classical in
/-- **Cherry extraction.**  In the cherry world (`4 ≤ mIncidence`, i.e. `e(M) ≥ 2`) with
no good triangle and no induced `2K₂` on degree-`3` vertices, a cherry exists: either
some degree-`3` vertex has two degree-`3` neighbours, or `M` is a matching with `≥ 2`
edges whose two edges have no cross adjacency (any cross adjacency would give a vertex
two degree-`3` neighbours) — an induced `2K₂`, excluded.  The ends are non-adjacent
since a degree-`3` triangle has `∑deg = 9`, good for every `n ≥ 6`. -/
theorem exists_cherry (n : ℕ) (hn : 6 ≤ n) (G : SimpleGraph (Fin n))
    (hT : ¬HasGoodTriangle n G) (h2k2 : ¬HasDeg3Ind2K2 n G)
    (hch : CaseCherry G) : ∃ x z y : Fin n, Cherry G x z y := by
  unfold CaseCherry at hch
  rw [mIncidence_eq_sum] at hch
  -- non-adjacency of two degree-3 neighbours of a degree-3 centre
  have hends : ∀ v a b : Fin n, G.degree v = 3 → G.degree a = 3 → G.degree b = 3 →
      G.Adj v a → G.Adj v b → a ≠ b → ¬G.Adj a b := by
    intro v a b hv ha hb hva hvb hab hadj
    refine hT ⟨v, a, b, G.ne_of_adj hva, hab, G.ne_of_adj hvb, hva, hadj, hvb, ?_⟩
    rw [hv, ha, hb]
    have h9 : (3 + 3 + 3 - 6 : ℕ) = 3 := by norm_num
    rw [h9]
    omega
  by_cases hbig : ∃ v ∈ deg3Set G, 2 ≤ (G.neighborFinset v ∩ deg3Set G).card
  · -- direct cherry at a centre with two degree-3 neighbours
    obtain ⟨v, hv, h2⟩ := hbig
    obtain ⟨a, haM, b, hbM, hab⟩ := Finset.one_lt_card.mp
      (show 1 < (G.neighborFinset v ∩ deg3Set G).card by omega)
    rw [Finset.mem_inter, G.mem_neighborFinset, mem_deg3Set] at haM hbM
    have hv3 := mem_deg3Set.mp hv
    exact ⟨a, v, b, ⟨haM.2, hv3, hbM.2, haM.1, hbM.1, hab,
      hends v a b hv3 haM.2 hbM.2 haM.1 hbM.1 hab⟩⟩
  · -- matching case: extract an induced `2K₂` — contradiction.
    exfalso
    push Not at hbig
    have hle1 : ∀ v ∈ deg3Set G, (G.neighborFinset v ∩ deg3Set G).card ≤ 1 :=
      fun v hv => by have := hbig v hv; omega
    -- a first `M`-edge `a ~ b`
    have hpos : ∃ a ∈ deg3Set G, 1 ≤ (G.neighborFinset a ∩ deg3Set G).card := by
      by_contra hcon
      push Not at hcon
      have hz : ∀ v ∈ deg3Set G, (G.neighborFinset v ∩ deg3Set G).card = 0 :=
        fun v hv => by have := hcon v hv; omega
      rw [Finset.sum_congr rfl hz, Finset.sum_const, smul_eq_mul, mul_zero] at hch
      omega
    obtain ⟨a, haD, hapos⟩ := hpos
    obtain ⟨b, hbmem⟩ := Finset.card_pos.mp
      (show 0 < (G.neighborFinset a ∩ deg3Set G).card by omega)
    rw [Finset.mem_inter, G.mem_neighborFinset] at hbmem
    obtain ⟨hab, hbD⟩ := hbmem
    have hne_ab : a ≠ b := G.ne_of_adj hab
    -- the unique-`M`-neighbour facts
    have huniq : ∀ v w w' : Fin n, v ∈ deg3Set G → G.Adj v w → w ∈ deg3Set G →
        G.Adj v w' → w' ∈ deg3Set G → w = w' := by
      intro v w w' hvD hvw hwD hvw' hw'D
      by_contra hne
      have hsub : ({w, w'} : Finset (Fin n)) ⊆ G.neighborFinset v ∩ deg3Set G := by
        intro u hu
        rw [Finset.mem_insert, Finset.mem_singleton] at hu
        rw [Finset.mem_inter, G.mem_neighborFinset]
        rcases hu with rfl | rfl
        · exact ⟨hvw, hwD⟩
        · exact ⟨hvw', hw'D⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_pair hne] at this
      have := hle1 v hvD
      omega
    -- a second `M`-edge `c ~ d`, disjoint from `{a, b}`
    have hsecond : ∃ c ∈ deg3Set G, c ≠ a ∧ c ≠ b ∧
        1 ≤ (G.neighborFinset c ∩ deg3Set G).card := by
      by_contra hcon
      push Not at hcon
      have hz : ∀ v ∈ deg3Set G \ ({a, b} : Finset (Fin n)),
          (G.neighborFinset v ∩ deg3Set G).card = 0 := by
        intro v hv
        rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hv
        obtain ⟨hvD, hvne⟩ := hv
        have := hcon v hvD (fun h => hvne (Or.inl h)) (fun h => hvne (Or.inr h))
        omega
      have hsplit : ∑ v ∈ ({a, b} : Finset (Fin n)),
            (G.neighborFinset v ∩ deg3Set G).card
          + ∑ v ∈ deg3Set G \ ({a, b} : Finset (Fin n)),
            (G.neighborFinset v ∩ deg3Set G).card
          = ∑ v ∈ deg3Set G, (G.neighborFinset v ∩ deg3Set G).card := by
        rw [add_comm]
        refine Finset.sum_sdiff ?_
        intro u hu
        rw [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl <;> assumption
      rw [Finset.sum_congr rfl hz, Finset.sum_const, smul_eq_mul, mul_zero,
        Finset.sum_pair hne_ab] at hsplit
      have h1 := hle1 a haD
      have h2 := hle1 b hbD
      omega
    obtain ⟨c, hcD, hca, hcb, hcpos⟩ := hsecond
    obtain ⟨d, hdmem⟩ := Finset.card_pos.mp
      (show 0 < (G.neighborFinset c ∩ deg3Set G).card by omega)
    rw [Finset.mem_inter, G.mem_neighborFinset] at hdmem
    obtain ⟨hcd, hdD⟩ := hdmem
    -- `d ∉ {a, b}`: `a`'s unique `M`-neighbour is `b`, `b`'s is `a`.
    have hda : d ≠ a := by
      intro e
      have hac : G.Adj a c := G.adj_symm (e ▸ hcd)
      exact hcb (huniq a b c haD hab hbD hac hcD).symm
    have hdb : d ≠ b := by
      intro e
      have hbc : G.Adj b c := G.adj_symm (e ▸ hcd)
      exact hca (huniq b a c hbD (G.adj_symm hab) haD hbc hcD).symm
    have hdc : c ≠ d := G.ne_of_adj hcd
    -- no cross edges (uniqueness of `M`-neighbours)
    have hnac' : ¬G.Adj a c := fun h => by
      have := huniq a b c haD hab hbD h hcD
      exact hcb this.symm
    have hnad : ¬G.Adj a d := fun h => by
      have := huniq a b d haD hab hbD h hdD
      exact hdb this.symm
    have hnbc : ¬G.Adj b c := fun h => by
      have := huniq b a c hbD (G.adj_symm hab) haD h hcD
      exact hca this.symm
    have hnbd : ¬G.Adj b d := fun h => by
      have := huniq b a d hbD (G.adj_symm hab) haD h hdD
      exact hda this.symm
    have hcard4 : ({a, b, c, d} : Finset (Fin n)).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp [hne_ab, Ne.symm hca, Ne.symm hda]),
        Finset.card_insert_of_notMem (by simp [Ne.symm hcb, Ne.symm hdb]),
        Finset.card_pair hdc]
    exact h2k2 ⟨a, b, c, d, hcard4, mem_deg3Set.mp haD, mem_deg3Set.mp hbD,
      mem_deg3Set.mp hcD, mem_deg3Set.mp hdD, hab, hcd, hnac', hnad, hnbc, hnbd⟩

open Classical in
/-- Cherry extraction from the residual core (the `ResidualCore` fields supply
exactly the needed exclusions; `n ≥ 12 ≥ 6`). -/
theorem residualCore_cherry (n : ℕ) (G : SimpleGraph (Fin n)) (h : ResidualCore n G)
    (hch : CaseCherry G) : ∃ x z y : Fin n, Cherry G x z y :=
  exists_cherry n (by have := h.n_ge; omega) G h.no_good_triangle h.no_deg3_ind2K2 hch

/-! ## The counting layer -/

open Classical in
/-- The **cherry-touching hubs**: hubs adjacent to a cherry vertex. -/
noncomputable def cherryHubs (G : SimpleGraph V) (x z y : V) : Finset V :=
  (hubSet G).filter (fun w => G.Adj w z ∨ G.Adj w x ∨ G.Adj w y)

open Classical in
theorem mem_cherryHubs {G : SimpleGraph V} {x z y w : V} :
    w ∈ cherryHubs G x z y ↔
      4 ≤ G.degree w ∧ (G.Adj w z ∨ G.Adj w x ∨ G.Adj w y) := by
  unfold cherryHubs hubSet
  simp

open Classical in
/-- **The cherry-touching hub budget** — at most `5` hubs meet a cherry: the centre
carries `≤ 1` hub (two of its three edges stay in the cherry), each end `≤ 2`. -/
theorem cherryHubs_card_le_five (G : SimpleGraph V) {x z y : V} (hch : Cherry G x z y) :
    (cherryHubs G x z y).card ≤ 5 := by
  have hsub : cherryHubs G x z y ⊆ (G.neighborFinset z ∩ hubSet G)
      ∪ ((G.neighborFinset x ∩ hubSet G) ∪ (G.neighborFinset y ∩ hubSet G)) := by
    intro w hw
    obtain ⟨hd, hadj⟩ := mem_cherryHubs.mp hw
    rw [Finset.mem_union, Finset.mem_union]
    rcases hadj with h | h | h
    · exact Or.inl (Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset z w).mpr (G.adj_symm h), mem_hubSet.mpr hd⟩)
    · exact Or.inr (Or.inl (Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset x w).mpr (G.adj_symm h), mem_hubSet.mpr hd⟩))
    · exact Or.inr (Or.inr (Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset y w).mpr (G.adj_symm h), mem_hubSet.mpr hd⟩))
  -- centre: `x, y ∈ N(z) \ Hub`.
  have hz1 : (G.neighborFinset z ∩ hubSet G).card + 2 ≤ G.degree z := by
    have hsplit := Finset.card_sdiff_add_card_inter (G.neighborFinset z) (hubSet G)
    have hdz := G.card_neighborFinset_eq_degree z
    have hsub2 : ({x, y} : Finset V) ⊆ G.neighborFinset z \ hubSet G := by
      intro w hw
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [Finset.mem_sdiff, G.mem_neighborFinset]
      rcases hw with rfl | rfl
      · exact ⟨hch.adj_zx, fun hmem => by
          have := mem_hubSet.mp hmem; rw [hch.deg_x] at this; omega⟩
      · exact ⟨hch.adj_zy, fun hmem => by
          have := mem_hubSet.mp hmem; rw [hch.deg_y] at this; omega⟩
    have h2 : 2 ≤ (G.neighborFinset z \ hubSet G).card := by
      calc 2 = ({x, y} : Finset V).card := (Finset.card_pair hch.ne_xy).symm
        _ ≤ _ := Finset.card_le_card hsub2
    omega
  -- ends: `z ∈ N(x) \ Hub`, `z ∈ N(y) \ Hub`.
  have hx1 : (G.neighborFinset x ∩ hubSet G).card + 1 ≤ G.degree x := by
    have hsplit := Finset.card_sdiff_add_card_inter (G.neighborFinset x) (hubSet G)
    have hdx := G.card_neighborFinset_eq_degree x
    have h1 : 1 ≤ (G.neighborFinset x \ hubSet G).card := by
      refine Finset.card_pos.mpr ⟨z, ?_⟩
      rw [Finset.mem_sdiff, G.mem_neighborFinset]
      exact ⟨G.adj_symm hch.adj_zx, fun hmem => by
        have := mem_hubSet.mp hmem; rw [hch.deg_z] at this; omega⟩
    omega
  have hy1 : (G.neighborFinset y ∩ hubSet G).card + 1 ≤ G.degree y := by
    have hsplit := Finset.card_sdiff_add_card_inter (G.neighborFinset y) (hubSet G)
    have hdy := G.card_neighborFinset_eq_degree y
    have h1 : 1 ≤ (G.neighborFinset y \ hubSet G).card := by
      refine Finset.card_pos.mpr ⟨z, ?_⟩
      rw [Finset.mem_sdiff, G.mem_neighborFinset]
      exact ⟨G.adj_symm hch.adj_zy, fun hmem => by
        have := mem_hubSet.mp hmem; rw [hch.deg_z] at this; omega⟩
    omega
  have hcz := hch.deg_z
  have hcx := hch.deg_x
  have hcy := hch.deg_y
  calc (cherryHubs G x z y).card
      ≤ ((G.neighborFinset z ∩ hubSet G)
          ∪ ((G.neighborFinset x ∩ hubSet G) ∪ (G.neighborFinset y ∩ hubSet G))).card :=
        Finset.card_le_card hsub
    _ ≤ (G.neighborFinset z ∩ hubSet G).card
        + ((G.neighborFinset x ∩ hubSet G) ∪ (G.neighborFinset y ∩ hubSet G)).card :=
        Finset.card_union_le _ _
    _ ≤ (G.neighborFinset z ∩ hubSet G).card
        + ((G.neighborFinset x ∩ hubSet G).card
          + (G.neighborFinset y ∩ hubSet G).card) := by
        have := Finset.card_union_le (G.neighborFinset x ∩ hubSet G)
          (G.neighborFinset y ∩ hubSet G)
        omega
    _ ≤ 5 := by omega

open Classical in
/-- **Shared-twin hubs are non-adjacent** (`n ≥ 18`): two degree-`≤ 4` hubs adjacent to
a common degree-`3` vertex cannot be adjacent — the `(3,4,4)`-triangle has
`∑deg ≤ 11 = thr(n)`, a good triangle for every `n ≥ 18`.  The structural atom of the
sea-side host-capacity analysis (host pairs of an iso twin are pairwise non-adjacent). -/
theorem shared_twin_hubs_nonadj (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Fin n))
    (hT : ¬HasGoodTriangle n G) {t g h : Fin n} (hdt : G.degree t = 3)
    (hdg : G.degree g ≤ 4) (hdh : G.degree h ≤ 4)
    (hgt : G.Adj g t) (hht : G.Adj h t) (hne : g ≠ h) : ¬G.Adj g h := by
  intro hadj
  refine hT ⟨g, h, t, hne, G.ne_of_adj hht, G.ne_of_adj hgt, hadj, hht, hgt, ?_⟩
  have hs : G.degree g + G.degree h + G.degree t - 6 ≤ 5 := by omega
  calc n * (G.degree g + G.degree h + G.degree t - 6)
      ≤ n * 5 := Nat.mul_le_mul_left n hs
    _ ≤ 2 * (3 * (n - 3)) := by omega

/-! ## The pigeonholes -/

open Classical in
/-- The **rich low hubs**: hubs of degree `≤ 5` with at least two `M`-isolated twins —
exactly the TwoTwin-eligible centres. -/
noncomputable def richLowHubs (G : SimpleGraph V) : Finset V :=
  (hubSet G).filter
    (fun w => G.degree w ≤ 5 ∧ 2 ≤ (G.neighborFinset w ∩ isoTwins G).card)

open Classical in
theorem mem_richLowHubs {G : SimpleGraph V} {w : V} :
    w ∈ richLowHubs G ↔ 4 ≤ G.degree w ∧ G.degree w ≤ 5 ∧
      2 ≤ (G.neighborFinset w ∩ isoTwins G).card := by
  unfold richLowHubs hubSet
  simp

open Classical in
/-- The **bad neighbours** of an apex `t` against a cherry: neighbours of degree `≥ 5`
or touching the cherry — the vertices that block the SingleVertex pair selection. -/
noncomputable def badApexNbrs (G : SimpleGraph V) (x z y t : V) : Finset V :=
  (G.neighborFinset t).filter (fun w => 5 ≤ G.degree w ∨ w ∈ cherryHubs G x z y)

open Classical in
/-- **The C0 pigeonhole (the design's "fat + cherry → TwoTwin" counting)**: `≥ 6` rich
low hubs close the cherry world — at most `5` hubs touch the cherry, so some rich low
hub avoids it and fires the TwoTwin certificate. -/
theorem six_richLow_twoBlock (G : SimpleGraph V) {x z y : V} (hch : Cherry G x z y)
    (h6 : 6 ≤ (richLowHubs G).card) : TwoBlockConfig G := by
  have h5 := cherryHubs_card_le_five G hch
  have hne : (richLowHubs G \ cherryHubs G x z y).Nonempty := by
    rw [← Finset.card_pos]
    have := Finset.le_card_sdiff (cherryHubs G x z y) (richLowHubs G)
    omega
  obtain ⟨h, hmem⟩ := hne
  rw [Finset.mem_sdiff] at hmem
  obtain ⟨hrich, hct⟩ := hmem
  obtain ⟨hh4, hh5, htwins⟩ := mem_richLowHubs.mp hrich
  have havoid : ¬(G.Adj h z ∨ G.Adj h x ∨ G.Adj h y) := by
    intro hadj
    exact hct (mem_cherryHubs.mpr ⟨hh4, hadj⟩)
  push Not at havoid
  obtain ⟨t₁, ht₁, t₂, ht₂, hne12⟩ := Finset.one_lt_card.mp
    (show 1 < (G.neighborFinset h ∩ isoTwins G).card by omega)
  rw [Finset.mem_inter, G.mem_neighborFinset] at ht₁ ht₂
  exact two_twin_cherry_twoBlock G hch hh4 hh5 ht₁.2 ht₂.2 hne12 ht₁.1 ht₂.1
    havoid.1 havoid.2.1 havoid.2.2

open Classical in
/-- **The sea-side dispatch atom**: every `M`-isolated apex `t` either fires the
SingleVertex certificate outright (two neighbours of degree exactly `4` avoiding the
cherry), or has `≥ 2` **bad** neighbours — degree `≥ 5` or cherry-touching.  (The
`δ ≥ 3` hypothesis makes all of `t`'s three neighbours hubs.) -/
theorem iso_apex_dichotomy (G : SimpleGraph V) (hdeg3 : ∀ v : V, 3 ≤ G.degree v)
    {x z y t : V} (hch : Cherry G x z y) (ht : t ∈ isoTwins G) :
    TwoBlockConfig G ∨ 2 ≤ (badApexNbrs G x z y t).card := by
  by_cases hbad : 2 ≤ (badApexNbrs G x z y t).card
  · exact Or.inr hbad
  · left
    obtain ⟨hdt, hisot⟩ := mem_isoTwins.mp ht
    have hNt : (G.neighborFinset t).card = 3 := by
      rw [G.card_neighborFinset_eq_degree, hdt]
    -- at least two good neighbours
    have hgood : 2 ≤ ((G.neighborFinset t).filter
        (fun w => ¬(5 ≤ G.degree w ∨ w ∈ cherryHubs G x z y))).card := by
      have := Finset.card_filter_add_card_filter_not
        (s := G.neighborFinset t)
        (p := fun w => 5 ≤ G.degree w ∨ w ∈ cherryHubs G x z y)
      unfold badApexNbrs at hbad
      omega
    obtain ⟨h₁, hh₁, h₂, hh₂, hne⟩ := Finset.one_lt_card.mp
      (show 1 < ((G.neighborFinset t).filter
        (fun w => ¬(5 ≤ G.degree w ∨ w ∈ cherryHubs G x z y))).card by omega)
    rw [Finset.mem_filter] at hh₁ hh₂
    obtain ⟨hh₁N, hh₁good⟩ := hh₁
    obtain ⟨hh₂N, hh₂good⟩ := hh₂
    push Not at hh₁good hh₂good
    obtain ⟨hh₁deg, hh₁ct⟩ := hh₁good
    obtain ⟨hh₂deg, hh₂ct⟩ := hh₂good
    have ha₁ : G.Adj t h₁ := (G.mem_neighborFinset t h₁).mp hh₁N
    have ha₂ : G.Adj t h₂ := (G.mem_neighborFinset t h₂).mp hh₂N
    -- the neighbours of an iso twin are hubs
    have hd₁ : 4 ≤ G.degree h₁ := by
      have := hisot h₁ ha₁
      have := hdeg3 h₁
      omega
    have hd₂ : 4 ≤ G.degree h₂ := by
      have := hisot h₂ ha₂
      have := hdeg3 h₂
      omega
    have hcher₁ : ¬(G.Adj h₁ z ∨ G.Adj h₁ x ∨ G.Adj h₁ y) := by
      intro hadj
      exact hh₁ct (mem_cherryHubs.mpr ⟨hd₁, hadj⟩)
    have hcher₂ : ¬(G.Adj h₂ z ∨ G.Adj h₂ x ∨ G.Adj h₂ y) := by
      intro hadj
      exact hh₂ct (mem_cherryHubs.mpr ⟨hd₂, hadj⟩)
    push Not at hcher₁ hcher₂
    have hc₁ : (G.neighborFinset h₁ ∩ ({z, x, y} : Finset V)).card = 0 :=
      nbr_inter_triple_zero G h₁ z x y hcher₁.1 hcher₁.2.1 hcher₁.2.2
    have hc₂ : (G.neighborFinset h₂ ∩ ({z, x, y} : Finset V)).card = 0 :=
      nbr_inter_triple_zero G h₂ z x y hcher₂.1 hcher₂.2.1 hcher₂.2.2
    refine single_vertex_cherry_twoBlock G hch ht hne ha₁ ha₂ hd₁ hd₂ ?_
    rw [hc₁, hc₂]
    omega

/-! ## The dispatch -/

open Classical in
/-- **The cherry dichotomy** (the main dispatch of this file): under `ResidualCore` and
`CaseCherry`, either a `TwoBlockConfig` exists (via the certificates above), or the
graph lies in the sharply-described **blocked cherry corner**: a cherry with `≤ 5` rich
low hubs and every `M`-isolated twin double-blocked (`≥ 2` neighbours of degree `≥ 5` or
cherry-touching).  The corner predicate is exactly the interface the L4 continuation
(the sea-side host-capacity pigeonhole) must close; every adversarial build probed at
`n ∈ {25, 30, 40}` that satisfies it is nevertheless killed by `TwoHub ⊂ W1`
(`scratchpad/general_cherry_sweep.py`). -/
theorem caseCherry_dichotomy (n : ℕ) (G : SimpleGraph (Fin n)) (h : ResidualCore n G)
    (hch : CaseCherry G) :
    TwoBlockConfig G ∨
      ∃ x z y : Fin n, Cherry G x z y ∧ (richLowHubs G).card ≤ 5 ∧
        ∀ t ∈ isoTwins G, 2 ≤ (badApexNbrs G x z y t).card := by
  obtain ⟨x, z, y, hcherry⟩ := residualCore_cherry n G h hch
  by_cases h6 : 6 ≤ (richLowHubs G).card
  · exact Or.inl (six_richLow_twoBlock G hcherry h6)
  · by_cases hall : ∀ t ∈ isoTwins G, 2 ≤ (badApexNbrs G x z y t).card
    · exact Or.inr ⟨x, z, y, hcherry, by omega, hall⟩
    · push Not at hall
      obtain ⟨t, ht, htlt⟩ := hall
      rcases iso_apex_dichotomy G h.min_degree hcherry ht with htb | hge
      · exact Or.inl htb
      · omega

end ACMax

/-! ## Closing the blocked cherry corner in the sea `e(M) = 2` regime

Closes the residual `blockedCherryCorner` of `caseCherry_dichotomy` when
`mIncidence G = 4` (`e(M) = 2`, so `M` is exactly the `P₃` cherry) and `Δ ≤ 4`
(the sea), for every `n ≥ 18`. With `e(M) = 2` the cherry carries the whole of
`M` (`eM_four_nbrs`), so every degree-3 vertex outside `{x, z, y}` is an iso twin
and `|Iso| ≥ 5` (`eM_four_iso_card`). In the sea *bad = cherry-touching*, so the
corner demands `∑_{t∈Iso} |N(t) ∩ CT| ≥ 2|Iso|`, forcing `≥ 3` rich
cherry-touching hubs, of which `z` blocks at most one — hence two `z`-avoiding
rich hubs (`corner_rich_pair_exists`). Such a pair closes (`p3_pair_close`): the
crossing budget vanishes (`mCross_eq_zero_of_zavoid`) and a short case analysis
on `|D3| ∈ {3, 4}` and adjacency fires `W1Config` with or without a far pad, or
falls back to the raw `two_hub_private_pair_twoBlock`. -/

namespace ACMax

variable {V : Type*} [Fintype V]

/-! ## Small helpers -/

open Classical in
private theorem mem_hubTwins {G : SimpleGraph V} {g t : V} :
    t ∈ hubTwins G g ↔ G.Adj g t ∧ G.degree t = 3 := by
  unfold hubTwins
  rw [Finset.mem_inter, G.mem_neighborFinset, mem_deg3Set]

open Classical in
/-- The **iso-twin neighbours** of a hub, as a pinned `def` so that its instances stay
stable across the `Fin n` / generic-`V` boundary. -/
noncomputable def isoNbrs (G : SimpleGraph V) (g : V) : Finset V :=
  G.neighborFinset g ∩ isoTwins G

open Classical in
theorem mem_isoNbrs {G : SimpleGraph V} {g t : V} :
    t ∈ isoNbrs G g ↔ G.Adj g t ∧ t ∈ isoTwins G := by
  unfold isoNbrs
  rw [Finset.mem_inter, G.mem_neighborFinset]

open Classical in
/-- The cherry ends and centre are not `M`-isolated (each has a degree-`3` neighbour). -/
theorem cherry_x_not_iso (G : SimpleGraph V) {x z y : V} (hch : Cherry G x z y) :
    x ∉ isoTwins G :=
  fun hx => (mem_isoTwins.mp hx).2 z hch.adj_zx.symm hch.deg_z

open Classical in
theorem cherry_y_not_iso (G : SimpleGraph V) {x z y : V} (hch : Cherry G x z y) :
    y ∉ isoTwins G :=
  fun hy => (mem_isoTwins.mp hy).2 z hch.adj_zy.symm hch.deg_z

open Classical in
theorem cherry_z_not_iso (G : SimpleGraph V) {x z y : V} (hch : Cherry G x z y) :
    z ∉ isoTwins G :=
  fun hz => (mem_isoTwins.mp hz).2 x hch.adj_zx hch.deg_x

/-! ## The `e(M) = 2` structure: the cherry is the whole of `M` -/

open Classical in
/-- **The `mIncidence = 4` structure theorem.**  When `e(M) = 2`, the cherry accounts
for the entire `D`–`D` incidence sum: the only degree-`3` neighbour of each end is the
centre `z`, and every degree-`3` vertex other than `x, z, y` is an `M`-isolated twin. -/
theorem eM_four_nbrs (G : SimpleGraph V) {x z y : V}
    (hch : Cherry G x z y) (heM : mIncidence G = 4) :
    (∀ w : V, G.Adj x w → G.degree w = 3 → w = z) ∧
      (∀ w : V, G.Adj y w → G.degree w = 3 → w = z) ∧
      ∀ v : V, G.degree v = 3 → v ≠ z → v ≠ x → v ≠ y → v ∈ isoTwins G := by
  have hxD : x ∈ deg3Set G := mem_deg3Set.mpr hch.deg_x
  have hzD : z ∈ deg3Set G := mem_deg3Set.mpr hch.deg_z
  have hyD : y ∈ deg3Set G := mem_deg3Set.mpr hch.deg_y
  have hzx := hch.ne_zx
  have hzy := hch.ne_zy
  have hxy := hch.ne_xy
  -- memberships of the three anchors
  have hzmemx : z ∈ G.neighborFinset x ∩ deg3Set G :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x z).mpr hch.adj_zx.symm, hzD⟩
  have hzmemy : z ∈ G.neighborFinset y ∩ deg3Set G :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y z).mpr hch.adj_zy.symm, hzD⟩
  have hxysub : ({x, y} : Finset V) ⊆ G.neighborFinset z ∩ deg3Set G := by
    intro w hw
    rw [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z w).mpr hch.adj_zx, hxD⟩
    · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z w).mpr hch.adj_zy, hyD⟩
  -- lower bounds
  have hx1 : 1 ≤ (G.neighborFinset x ∩ deg3Set G).card := Finset.card_pos.mpr ⟨z, hzmemx⟩
  have hy1 : 1 ≤ (G.neighborFinset y ∩ deg3Set G).card := Finset.card_pos.mpr ⟨z, hzmemy⟩
  have hz2 : 2 ≤ (G.neighborFinset z ∩ deg3Set G).card := by
    calc 2 = ({x, y} : Finset V).card := (Finset.card_pair hxy).symm
      _ ≤ _ := Finset.card_le_card hxysub
  -- the sum split
  have htsub : ({z, x, y} : Finset V) ⊆ deg3Set G := by
    intro v hv
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl <;> assumption
  have hsplit : ∑ v ∈ deg3Set G \ ({z, x, y} : Finset V),
        (G.neighborFinset v ∩ deg3Set G).card
      + ∑ v ∈ ({z, x, y} : Finset V), (G.neighborFinset v ∩ deg3Set G).card
      = ∑ v ∈ deg3Set G, (G.neighborFinset v ∩ deg3Set G).card :=
    Finset.sum_sdiff htsub
  have htriple : ∑ v ∈ ({z, x, y} : Finset V), (G.neighborFinset v ∩ deg3Set G).card
      = (G.neighborFinset z ∩ deg3Set G).card + (G.neighborFinset x ∩ deg3Set G).card
        + (G.neighborFinset y ∩ deg3Set G).card := by
    rw [Finset.sum_insert (by simp [hzx, hzy]), Finset.sum_insert (by simp [hxy]),
      Finset.sum_singleton]
    ring
  have hsum4 : ∑ v ∈ deg3Set G, (G.neighborFinset v ∩ deg3Set G).card = 4 := by
    rw [← mIncidence_eq_sum]
    exact heM
  have hrest0 : ∑ v ∈ deg3Set G \ ({z, x, y} : Finset V),
      (G.neighborFinset v ∩ deg3Set G).card = 0 := by omega
  have hfx : (G.neighborFinset x ∩ deg3Set G).card = 1 := by omega
  have hfy : (G.neighborFinset y ∩ deg3Set G).card = 1 := by omega
  have hxset : G.neighborFinset x ∩ deg3Set G = {z} :=
    (Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr hzmemx)
      (by rw [Finset.card_singleton, hfx])).symm
  have hyset : G.neighborFinset y ∩ deg3Set G = {z} :=
    (Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr hzmemy)
      (by rw [Finset.card_singleton, hfy])).symm
  refine ⟨?_, ?_, ?_⟩
  · intro w hxw hw3
    have hwmem : w ∈ G.neighborFinset x ∩ deg3Set G :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x w).mpr hxw, mem_deg3Set.mpr hw3⟩
    rw [hxset] at hwmem
    exact Finset.mem_singleton.mp hwmem
  · intro w hyw hw3
    have hwmem : w ∈ G.neighborFinset y ∩ deg3Set G :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y w).mpr hyw, mem_deg3Set.mpr hw3⟩
    rw [hyset] at hwmem
    exact Finset.mem_singleton.mp hwmem
  · intro v hv3 hvz hvx hvy
    have hvD : v ∈ deg3Set G := mem_deg3Set.mpr hv3
    have hvmem : v ∈ deg3Set G \ ({z, x, y} : Finset V) :=
      Finset.mem_sdiff.mpr ⟨hvD, by simp [hvz, hvx, hvy]⟩
    have hv0 : (G.neighborFinset v ∩ deg3Set G).card = 0 :=
      (Finset.sum_eq_zero_iff.mp hrest0) v hvmem
    rw [mem_isoTwins]
    refine ⟨hv3, fun w hw hw3 => ?_⟩
    have hwmem : w ∈ G.neighborFinset v ∩ deg3Set G :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset v w).mpr hw, mem_deg3Set.mpr hw3⟩
    have := Finset.card_pos.mpr ⟨w, hwmem⟩
    omega

open Classical in
/-- **The iso-twin supply of the `e(M) = 2` world**: `|Iso| ≥ |D| − 3 ≥ 5`. -/
theorem eM_four_iso_card (n : ℕ) (hn : 8 ≤ n) (G : SimpleGraph (Fin n))
    (hm : G.edgeFinset.card = 2 * (n - 2)) (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    {x z y : Fin n} (hch : Cherry G x z y) (heM : mIncidence G = 4) :
    5 ≤ (isoTwins G).card := by
  obtain ⟨-, -, hiso⟩ := eM_four_nbrs G hch heM
  have hD8 : 8 ≤ (deg3Set G).card := by
    have h := card_deg3_ge_eight n hn G hm h3
    unfold deg3Set
    exact h
  have hsub : deg3Set G \ ({z, x, y} : Finset (Fin n)) ⊆ isoTwins G := by
    intro v hv
    rw [Finset.mem_sdiff] at hv
    obtain ⟨hvD, hvT⟩ := hv
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hvT
    push Not at hvT
    exact hiso v (mem_deg3Set.mp hvD) hvT.1 hvT.2.1 hvT.2.2
  have hsplit := Finset.card_sdiff_add_card_inter (deg3Set G)
    ({z, x, y} : Finset (Fin n))
  have hT3 : ({z, x, y} : Finset (Fin n)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hch.ne_zx, hch.ne_zy]),
      Finset.card_pair hch.ne_xy]
  have hint3 : (deg3Set G ∩ ({z, x, y} : Finset (Fin n))).card ≤ 3 := by
    calc (deg3Set G ∩ ({z, x, y} : Finset (Fin n))).card
        ≤ ({z, x, y} : Finset (Fin n)).card :=
          Finset.card_le_card Finset.inter_subset_right
      _ = 3 := hT3
  have := Finset.card_le_card hsub
  omega

/-! ## The pair atoms -/

open Classical in
/-- **The crossing budget vanishes for `z`-avoiding pairs**: in the `e(M) = 2` world
every `M`-edge touches the centre `z`, and `z` lies in neither private side of a pair
of hubs avoiding it — so `mCross(g, h) = 0` *structurally*. -/
theorem mCross_eq_zero_of_zavoid (G : SimpleGraph V) {x z y : V}
    (hch : Cherry G x z y) (heM : mIncidence G = 4) {g h : V}
    (hgz : ¬G.Adj g z) (hhz : ¬G.Adj h z) :
    mCross G g h = 0 := by
  obtain ⟨hxN, hyN, hiso⟩ := eM_four_nbrs G hch heM
  unfold mCross
  refine Finset.sum_eq_zero fun t ht => ?_
  obtain ⟨hgt, ht3, -⟩ := privTwins_spec.mp ht
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro w hw
  rw [Finset.mem_inter] at hw
  obtain ⟨hwN, hwP⟩ := hw
  have htw : G.Adj t w := (G.mem_neighborFinset t w).mp hwN
  obtain ⟨hhw, hw3, -⟩ := privTwins_spec.mp hwP
  have htz : t ≠ z := fun e => hgz (e ▸ hgt)
  have hwz : w ≠ z := fun e => hhz (e ▸ hhw)
  by_cases htx : t = x
  · exact hwz (hxN w (htx ▸ htw) hw3)
  · by_cases hty : t = y
    · exact hwz (hyN w (hty ▸ htw) hw3)
    · exact (mem_isoTwins.mp (hiso t ht3 htz htx hty)).2 w htw hw3

open Classical in
/-- **The share bound for `z`-avoiding pairs** (`n ≥ 16`): two non-adjacent degree-`4`
hubs avoiding `z` share at most one degree-`3` twin — any two shared twins live in
`{x, y} ∪ Iso`, hence are non-adjacent, and give the good `C₄` `Σ = 14`. -/
theorem sharedTwins_card_le_one_of_zavoid (n : ℕ) (hn : 16 ≤ n)
    (G : SimpleGraph (Fin n)) (hC4 : ¬HasGoodC4 n G) {x z y : Fin n}
    (hch : Cherry G x z y) (heM : mIncidence G = 4) {g h : Fin n}
    (hdg : G.degree g = 4) (hdh : G.degree h = 4)
    (hne : g ≠ h) (hnadj : ¬G.Adj g h) (hgz : ¬G.Adj g z) :
    (sharedTwins G g h).card ≤ 1 := by
  obtain ⟨hxN, hyN, hiso⟩ := eM_four_nbrs G hch heM
  by_contra hgt
  rw [not_le] at hgt
  obtain ⟨t₁, ht1, t₂, ht2, hne12⟩ := Finset.one_lt_card.mp hgt
  obtain ⟨hgt1, hht1, h31⟩ := sharedTwins_spec.mp ht1
  obtain ⟨hgt2, hht2, h32⟩ := sharedTwins_spec.mp ht2
  have ht1z : t₁ ≠ z := fun e => hgz (e ▸ hgt1)
  have ht2z : t₂ ≠ z := fun e => hgz (e ▸ hgt2)
  -- the two shared twins are non-adjacent
  have hnadj12 : ¬G.Adj t₁ t₂ := by
    intro hadj
    by_cases h1x : t₁ = x
    · exact ht2z (hxN t₂ (h1x ▸ hadj) h32)
    · by_cases h1y : t₁ = y
      · exact ht2z (hyN t₂ (h1y ▸ hadj) h32)
      · exact (mem_isoTwins.mp (hiso t₁ h31 ht1z h1x h1y)).2 t₂ hadj h32
  -- distinctness
  have hgt1' : g ≠ t₁ := fun e => by rw [← e] at h31; omega
  have hgt2' : g ≠ t₂ := fun e => by rw [← e] at h32; omega
  have hht1' : h ≠ t₁ := fun e => by rw [← e] at h31; omega
  have hht2' : h ≠ t₂ := fun e => by rw [← e] at h32; omega
  -- the good C₄ `g – t₁ – h – t₂`
  apply hC4
  refine ⟨g, t₁, h, t₂, ?_, hgt1, hht1.symm, hht2, hgt2.symm, hnadj, hnadj12, ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [hgt1', hne, hgt2']),
      Finset.card_insert_of_notMem (by simp [Ne.symm hht1', hne12]),
      Finset.card_insert_of_notMem (by simp [hht2']), Finset.card_singleton]
  · rw [hdg, h31, hdh, h32]
    omega

open Classical in
/-- **Adjacent low hubs share nothing** (`n ≥ 18`, wraps `shared_twin_hubs_nonadj`):
an adjacent pair of degree-`≤ 4` hubs with a common degree-`3` twin is a
`(3,4,4)`-triangle. -/
theorem sharedTwins_eq_empty_of_adj (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Fin n))
    (hT : ¬HasGoodTriangle n G) {g h : Fin n}
    (hdg : G.degree g ≤ 4) (hdh : G.degree h ≤ 4) (hadj : G.Adj g h) :
    sharedTwins G g h = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro t ht
  obtain ⟨hgt, hht, ht3⟩ := sharedTwins_spec.mp ht
  exact shared_twin_hubs_nonadj n hn G hT ht3 hdg hdh hgt hht (G.ne_of_adj hadj) hadj

open Classical in
/-- The rich-CT `D3`-card bound: a hub with a non-iso degree-`3` neighbour `c` has
`|D3| ≥ |isoNbrs| + 1`. -/
theorem hubTwins_card_bounds (G : SimpleGraph V) {g c : V}
    (hgc : G.Adj g c) (hc3 : G.degree c = 3) (hcIso : c ∉ isoTwins G) :
    (isoNbrs G g).card + 1 ≤ (hubTwins G g).card := by
  have hsub : insert c (isoNbrs G g) ⊆ hubTwins G g := by
    intro w hw
    rw [Finset.mem_insert] at hw
    rcases hw with rfl | hw
    · exact mem_hubTwins.mpr ⟨hgc, hc3⟩
    · obtain ⟨h1, h2⟩ := mem_isoNbrs.mp hw
      exact mem_hubTwins.mpr ⟨h1, (mem_isoTwins.mp h2).1⟩
  have hcnot : c ∉ isoNbrs G g := fun hc => hcIso (mem_isoNbrs.mp hc).2
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hcnot] at hcard
  omega

/-! ## The pair closes -/

open Classical in
/-- **The gap case of the pair analysis** (`|D3| = (4, 3)`, non-adjacent, share `≤ 1`,
no crossing): either an iso twin outside `N(g) ∪ N(h)` pads the W1 double star, or
`Iso ⊆ N(g) ∪ N(h)` forces disjoint `(3, 2)` iso-twin sets and the raw two-hub cut
fires. -/
private theorem p3_pair_gap (G : SimpleGraph V) {g h : V}
    (hne : g ≠ h) (hnadj : ¬G.Adj g h)
    (hdg : G.degree g = 4) (hdh : G.degree h = 4)
    (hIso5 : 5 ≤ (isoTwins G).card)
    (hgA : (isoNbrs G g).card + 1 ≤ (hubTwins G g).card)
    (hhA : (isoNbrs G h).card + 1 ≤ (hubTwins G h).card)
    (hgr : 2 ≤ (isoNbrs G g).card) (hhr : 2 ≤ (isoNbrs G h).card)
    (hg4 : (hubTwins G g).card = 4) (hh3 : (hubTwins G h).card = 3)
    (hs1 : (sharedTwins G g h).card ≤ 1) (hmx : mCross G g h = 0) :
    W1Config G ∨ TwoBlockConfig G := by
  have e1 := privTwins_card_add_shared G g h
  have e2 := privTwins_card_add_shared G h g
  rw [sharedTwins_comm G h g] at e2
  by_cases hpad : ∃ f ∈ isoTwins G, ¬G.Adj g f ∧ ¬G.Adj h f
  · -- W1 with the single far pad
    obtain ⟨f, hfI, hfg, hfh⟩ := hpad
    left
    refine w1Config_of_pair G g h {f} (by omega) (by omega) hne ?_ ?_ ?_ ?_
    · intro f' hf'
      rw [Finset.mem_singleton] at hf'
      subst hf'
      exact (mem_isoTwins.mp hfI).1
    · intro f' hf' w hw
      rw [Finset.mem_singleton] at hf'
      subst hf'
      rw [Finset.mem_union, Finset.mem_insert, Finset.mem_insert] at hw
      rcases hw with (rfl | hwP) | (rfl | hwN)
      · exact fun ha => hfg ha.symm
      · exact fun ha => (mem_isoTwins.mp hfI).2 w ha (privTwins_spec.mp hwP).2.1
      · exact fun ha => hfh ha.symm
      · exact fun ha => (mem_isoTwins.mp hfI).2 w ha (privTwins_spec.mp hwN).2.1
    · rw [Finset.card_singleton]
      omega
    · unfold dsValue
      have i1 := hubTwins_card_add_intDeg G g
      have i2 := hubTwins_card_add_intDeg G h
      rw [hdg] at i1
      rw [hdh] at i2
      have hadj0 : adjInd G g h = 0 := by unfold adjInd; rw [ite_eq_right hnadj]
      rw [hadj0, hmx]
      omega
  · -- no pad: `Iso` is covered, the iso-twin sets are disjoint, two-hub fires
    right
    push Not at hpad
    have hcover : isoTwins G ⊆ isoNbrs G g ∪ isoNbrs G h := by
      intro f hf
      by_cases hgf : G.Adj g f
      · exact Finset.mem_union_left _ (mem_isoNbrs.mpr ⟨hgf, hf⟩)
      · exact Finset.mem_union_right _ (mem_isoNbrs.mpr ⟨hpad f hf hgf, hf⟩)
    have hUI := Finset.card_le_card hcover
    have hIE := Finset.card_union_add_card_inter (isoNbrs G g) (isoNbrs G h)
    -- the intersection is empty by the (3, 2) capacity count
    have hABz : (isoNbrs G g ∩ isoNbrs G h).card = 0 := by omega
    have hABz' : (isoNbrs G h ∩ isoNbrs G g).card = 0 := by
      rw [Finset.inter_comm]
      exact hABz
    -- private iso-twin counts
    have hp : ∀ a b : V, (isoNbrs G a ∩ isoNbrs G b).card = 0 →
        (isoNbrs G a).card ≤ (isoNbrs G a \ G.neighborFinset b).card := by
      intro a b hab
      have hsplit := Finset.card_sdiff_add_card_inter (isoNbrs G a)
        (G.neighborFinset b)
      have hsub2 : isoNbrs G a ∩ G.neighborFinset b ⊆ isoNbrs G a ∩ isoNbrs G b := by
        intro w hw
        rw [Finset.mem_inter] at hw ⊢
        exact ⟨hw.1, mem_isoNbrs.mpr
          ⟨(G.mem_neighborFinset b w).mp hw.2, (mem_isoNbrs.mp hw.1).2⟩⟩
      have := Finset.card_le_card hsub2
      omega
    exact two_hub_private_pair_twoBlock G g h hdg hdh hne hnadj
      (le_trans hgr (hp g h hABz)) (le_trans hhr (hp h g hABz'))

open Classical in
/-- **The `z`-avoiding rich pair closes** (the main pair theorem, `n ≥ 18`): two
distinct rich cherry-touching degree-`4` hubs avoiding the centre give a `W1Config` or
a `TwoBlockConfig`, by the adjacent / equal / gap / two-hub case tree. -/
theorem p3_pair_close (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Fin n))
    (hT : ¬HasGoodTriangle n G) (hC4 : ¬HasGoodC4 n G)
    {x z y : Fin n} (hch : Cherry G x z y) (heM : mIncidence G = 4)
    (hIso5 : 5 ≤ (isoTwins G).card)
    {g h : Fin n} (hne : g ≠ h)
    (hdg : G.degree g = 4) (hdh : G.degree h = 4)
    (hgxy : G.Adj g x ∨ G.Adj g y) (hhxy : G.Adj h x ∨ G.Adj h y)
    (hgz : ¬G.Adj g z) (hhz : ¬G.Adj h z)
    (hgr : 2 ≤ (isoNbrs G g).card) (hhr : 2 ≤ (isoNbrs G h).card) :
    W1Config G ∨ TwoBlockConfig G := by
  -- the cherry attachment of each hub
  obtain ⟨cg, hgcg, hcg3, hcgI⟩ : ∃ c, G.Adj g c ∧ G.degree c = 3 ∧ c ∉ isoTwins G := by
    rcases hgxy with hgx | hgy
    · exact ⟨x, hgx, hch.deg_x, cherry_x_not_iso G hch⟩
    · exact ⟨y, hgy, hch.deg_y, cherry_y_not_iso G hch⟩
  obtain ⟨ch', hhch, hch3', hchI⟩ : ∃ c, G.Adj h c ∧ G.degree c = 3 ∧ c ∉ isoTwins G := by
    rcases hhxy with hhx | hhy
    · exact ⟨x, hhx, hch.deg_x, cherry_x_not_iso G hch⟩
    · exact ⟨y, hhy, hch.deg_y, cherry_y_not_iso G hch⟩
  have hgA := hubTwins_card_bounds G hgcg hcg3 hcgI
  have hhA := hubTwins_card_bounds G hhch hch3' hchI
  have hgle4 : (hubTwins G g).card ≤ 4 := by
    have := hubTwins_card_add_intDeg G g
    omega
  have hhle4 : (hubTwins G h).card ≤ 4 := by
    have := hubTwins_card_add_intDeg G h
    omega
  have hmxgh : mCross G g h = 0 := mCross_eq_zero_of_zavoid G hch heM hgz hhz
  have hmxhg : mCross G h g = 0 := mCross_eq_zero_of_zavoid G hch heM hhz hgz
  by_cases hadj : G.Adj g h
  · -- adjacent: no shared twin, |D3| = 3 both, W1 at the tie with no pads
    left
    have hsE : sharedTwins G g h = ∅ :=
      sharedTwins_eq_empty_of_adj n hn G hT (le_of_eq hdg) (le_of_eq hdh) hadj
    have hg3 : (hubTwins G g).card = 3 := by
      have hsub : hubTwins G g ⊆ (G.neighborFinset g).erase h := by
        intro t ht
        obtain ⟨hadj', ht3⟩ := mem_hubTwins.mp ht
        refine Finset.mem_erase.mpr ⟨fun e => ?_, (G.mem_neighborFinset g t).mpr hadj'⟩
        rw [e] at ht3
        omega
      have hc := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem ((G.mem_neighborFinset g h).mpr hadj),
        G.card_neighborFinset_eq_degree, hdg] at hc
      omega
    have hh3 : (hubTwins G h).card = 3 := by
      have hsub : hubTwins G h ⊆ (G.neighborFinset h).erase g := by
        intro t ht
        obtain ⟨hadj', ht3⟩ := mem_hubTwins.mp ht
        refine Finset.mem_erase.mpr ⟨fun e => ?_, (G.mem_neighborFinset h t).mpr hadj'⟩
        rw [e] at ht3
        omega
      have hc := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem ((G.mem_neighborFinset h g).mpr hadj.symm),
        G.card_neighborFinset_eq_degree, hdh] at hc
      omega
    have e1 := privTwins_card_add_shared G g h
    have e2 := privTwins_card_add_shared G h g
    rw [sharedTwins_comm G h g] at e2
    rw [hsE, Finset.card_empty] at e1 e2
    refine w1Config_of_pair G g h ∅ (by omega) (by omega) hne
      (fun f hf => absurd hf (Finset.notMem_empty f))
      (fun f hf w _ => absurd hf (Finset.notMem_empty f)) ?_ ?_
    · rw [Finset.card_empty]
      omega
    · unfold dsValue
      have i1 := hubTwins_card_add_intDeg G g
      have i2 := hubTwins_card_add_intDeg G h
      rw [hdg] at i1
      rw [hdh] at i2
      have hadj1 : adjInd G g h = 1 := by unfold adjInd; rw [ite_eq_left hadj]
      rw [hadj1, hmxgh, hsE, Finset.card_empty]
      omega
  · -- non-adjacent: share ≤ 1, split on the D3-card comparison
    have hs1 : (sharedTwins G g h).card ≤ 1 :=
      sharedTwins_card_le_one_of_zavoid n (by omega) G hC4 hch heM hdg hdh hne hadj hgz
    have hs1' : (sharedTwins G h g).card ≤ 1 := by
      rw [sharedTwins_comm G h g]
      exact hs1
    have hg3le : 3 ≤ (hubTwins G g).card := by omega
    have hh3le : 3 ≤ (hubTwins G h).card := by omega
    rcases Nat.lt_trichotomy (hubTwins G g).card (hubTwins G h).card with hlt | heq | hgt
    · -- `h` is the clean one: the ordered gap lemma on `(h, g)`
      exact p3_pair_gap G (Ne.symm hne) (fun ha => hadj ha.symm) hdh hdg hIso5
        hhA hgA hhr hgr (by omega) (by omega) hs1' hmxhg
    · -- equal `D3`-cards: W1 with `F = ∅`
      left
      have e1 := privTwins_card_add_shared G g h
      have e2 := privTwins_card_add_shared G h g
      rw [sharedTwins_comm G h g] at e2
      refine w1Config_of_pair G g h ∅ (by omega) (by omega) hne
        (fun f hf => absurd hf (Finset.notMem_empty f))
        (fun f hf w _ => absurd hf (Finset.notMem_empty f)) ?_ ?_
      · rw [Finset.card_empty]
        omega
      · unfold dsValue
        have i1 := hubTwins_card_add_intDeg G g
        have i2 := hubTwins_card_add_intDeg G h
        rw [hdg] at i1
        rw [hdh] at i2
        have hadj0 : adjInd G g h = 0 := by unfold adjInd; rw [ite_eq_right hadj]
        rw [hadj0, hmxgh]
        omega
    · -- `g` is the clean one
      exact p3_pair_gap G hne hadj hdg hdh hIso5 hgA hhA hgr hhr
        (by omega) (by omega) hs1 hmxgh

/-! ## The pigeonhole: two `z`-avoiding rich cherry-touching hubs exist -/

open Classical in
/-- **The corner pigeonhole** (sea regime): if every iso twin has `≥ 2` bad neighbours
and there is no degree-`≥ 5` vertex, the `≥ 2|Iso| ≥ 10` cherry-touching incidence
demand against the `≤ 5`-hub, `≤ 3`-each capacity forces `≥ 3` rich cherry-touching
hubs, of which at most one is adjacent to the centre `z` — leaving the two hubs the
pair theorem needs. -/
theorem corner_rich_pair_exists (G : SimpleGraph V)
    (hsea : ∀ v : V, G.degree v ≤ 4)
    {x z y : V} (hch : Cherry G x z y)
    (hIso5 : 5 ≤ (isoTwins G).card)
    (hblock : ∀ t ∈ isoTwins G, 2 ≤ (badApexNbrs G x z y t).card) :
    ∃ g h : V, g ≠ h ∧ G.degree g = 4 ∧ G.degree h = 4 ∧
      (G.Adj g x ∨ G.Adj g y) ∧ (G.Adj h x ∨ G.Adj h y) ∧
      ¬G.Adj g z ∧ ¬G.Adj h z ∧
      2 ≤ (isoNbrs G g).card ∧ 2 ≤ (isoNbrs G h).card := by
  -- in the sea, bad = cherry-touching
  have hstep1 : ∀ t ∈ isoTwins G,
      2 ≤ (G.neighborFinset t ∩ cherryHubs G x z y).card := by
    intro t ht
    refine le_trans (hblock t ht) (Finset.card_le_card ?_)
    intro w hw
    unfold badApexNbrs at hw
    rw [Finset.mem_filter] at hw
    obtain ⟨hwN, hw5⟩ := hw
    rcases hw5 with h5 | hct
    · have := hsea w
      omega
    · exact Finset.mem_inter.mpr ⟨hwN, hct⟩
  -- demand
  have hdemand : 2 * (isoTwins G).card
      ≤ ∑ w ∈ cherryHubs G x z y, (G.neighborFinset w ∩ isoTwins G).card := by
    rw [← cross_count G (isoTwins G) (cherryHubs G x z y)]
    calc 2 * (isoTwins G).card = ∑ _t ∈ isoTwins G, 2 := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ _ := Finset.sum_le_sum hstep1
  -- capacity: each cherry-touching hub holds ≤ 3 iso twins
  have hcap : ∀ w ∈ cherryHubs G x z y,
      (G.neighborFinset w ∩ isoTwins G).card ≤ 3 := by
    intro w hw
    obtain ⟨hw4, hwadj⟩ := mem_cherryHubs.mp hw
    obtain ⟨c, hcN, hcI⟩ : ∃ c, c ∈ G.neighborFinset w ∧ c ∉ isoTwins G := by
      rcases hwadj with hz' | hx' | hy'
      · exact ⟨z, (G.mem_neighborFinset w z).mpr hz', cherry_z_not_iso G hch⟩
      · exact ⟨x, (G.mem_neighborFinset w x).mpr hx', cherry_x_not_iso G hch⟩
      · exact ⟨y, (G.mem_neighborFinset w y).mpr hy', cherry_y_not_iso G hch⟩
    have hsub : G.neighborFinset w ∩ isoTwins G ⊆ (G.neighborFinset w).erase c := by
      intro u hu
      exact Finset.mem_erase.mpr
        ⟨fun e => hcI (e ▸ (Finset.mem_inter.mp hu).2), (Finset.mem_inter.mp hu).1⟩
    have hle := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hcN, G.card_neighborFinset_eq_degree] at hle
    have := hsea w
    omega
  -- ≥ 3 rich cherry-touching hubs
  have hCT5 : (cherryHubs G x z y).card ≤ 5 := cherryHubs_card_le_five G hch
  have hsplit := Finset.sum_filter_add_sum_filter_not (cherryHubs G x z y)
    (fun w => 2 ≤ (G.neighborFinset w ∩ isoTwins G).card)
    (fun w => (G.neighborFinset w ∩ isoTwins G).card)
  have hfc := Finset.card_filter_add_card_filter_not (s := cherryHubs G x z y)
    (p := fun w => 2 ≤ (G.neighborFinset w ∩ isoTwins G).card)
  have hrich_sum : ∑ w ∈ (cherryHubs G x z y).filter
        (fun w => 2 ≤ (G.neighborFinset w ∩ isoTwins G).card),
        (G.neighborFinset w ∩ isoTwins G).card
      ≤ 3 * ((cherryHubs G x z y).filter
        (fun w => 2 ≤ (G.neighborFinset w ∩ isoTwins G).card)).card := by
    calc ∑ w ∈ (cherryHubs G x z y).filter
          (fun w => 2 ≤ (G.neighborFinset w ∩ isoTwins G).card),
          (G.neighborFinset w ∩ isoTwins G).card
        ≤ ∑ _w ∈ (cherryHubs G x z y).filter
            (fun w => 2 ≤ (G.neighborFinset w ∩ isoTwins G).card), 3 :=
          Finset.sum_le_sum fun w hw => hcap w (Finset.mem_of_mem_filter w hw)
      _ = _ := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hpoor_sum : ∑ w ∈ (cherryHubs G x z y).filter
        (fun w => ¬2 ≤ (G.neighborFinset w ∩ isoTwins G).card),
        (G.neighborFinset w ∩ isoTwins G).card
      ≤ ((cherryHubs G x z y).filter
        (fun w => ¬2 ≤ (G.neighborFinset w ∩ isoTwins G).card)).card := by
    calc ∑ w ∈ (cherryHubs G x z y).filter
          (fun w => ¬2 ≤ (G.neighborFinset w ∩ isoTwins G).card),
          (G.neighborFinset w ∩ isoTwins G).card
        ≤ ∑ _w ∈ (cherryHubs G x z y).filter
            (fun w => ¬2 ≤ (G.neighborFinset w ∩ isoTwins G).card), 1 := by
          refine Finset.sum_le_sum fun w hw => ?_
          have := (Finset.mem_filter.mp hw).2
          omega
      _ = _ := by rw [Finset.sum_const, smul_eq_mul, mul_one]
  have hRC3 : 3 ≤ ((cherryHubs G x z y).filter
      (fun w => 2 ≤ (G.neighborFinset w ∩ isoTwins G).card)).card := by omega
  -- at most one rich hub is adjacent to z
  have hS1 : (((cherryHubs G x z y).filter
        (fun w => 2 ≤ (G.neighborFinset w ∩ isoTwins G).card)).filter
        (fun w => G.Adj w z)).card ≤ 1 := by
    have hxNz : x ∈ G.neighborFinset z := (G.mem_neighborFinset z x).mpr hch.adj_zx
    have hyNz : y ∈ (G.neighborFinset z).erase x :=
      Finset.mem_erase.mpr
        ⟨Ne.symm hch.ne_xy, (G.mem_neighborFinset z y).mpr hch.adj_zy⟩
    have hsub : ((cherryHubs G x z y).filter
          (fun w => 2 ≤ (G.neighborFinset w ∩ isoTwins G).card)).filter
          (fun w => G.Adj w z)
        ⊆ ((G.neighborFinset z).erase x).erase y := by
      intro w hw
      rw [Finset.mem_filter, Finset.mem_filter] at hw
      obtain ⟨⟨hwCT, -⟩, hwz⟩ := hw
      have hw4 := (mem_cherryHubs.mp hwCT).1
      refine Finset.mem_erase.mpr ⟨fun e => ?_, Finset.mem_erase.mpr ⟨fun e => ?_, ?_⟩⟩
      · rw [e, hch.deg_y] at hw4; omega
      · rw [e, hch.deg_x] at hw4; omega
      · exact (G.mem_neighborFinset z w).mpr hwz.symm
    have hle := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hyNz, Finset.card_erase_of_mem hxNz,
      G.card_neighborFinset_eq_degree, hch.deg_z] at hle
    omega
  have hfc2 := Finset.card_filter_add_card_filter_not
    (s := (cherryHubs G x z y).filter
      (fun w => 2 ≤ (G.neighborFinset w ∩ isoTwins G).card))
    (p := fun w => G.Adj w z)
  have h2le : 1 < (((cherryHubs G x z y).filter
      (fun w => 2 ≤ (G.neighborFinset w ∩ isoTwins G).card)).filter
      (fun w => ¬G.Adj w z)).card := by omega
  obtain ⟨g, hg, h, hh, hne⟩ := Finset.one_lt_card.mp h2le
  rw [Finset.mem_filter, Finset.mem_filter] at hg hh
  obtain ⟨⟨hgCT, hgrich⟩, hgz⟩ := hg
  obtain ⟨⟨hhCT, hhrich⟩, hhz⟩ := hh
  obtain ⟨hg4, hgadj⟩ := mem_cherryHubs.mp hgCT
  obtain ⟨hh4, hhadj⟩ := mem_cherryHubs.mp hhCT
  have hgd : G.degree g = 4 := le_antisymm (hsea g) hg4
  have hhd : G.degree h = 4 := le_antisymm (hsea h) hh4
  have hgxy : G.Adj g x ∨ G.Adj g y := by
    rcases hgadj with h' | h' | h'
    · exact absurd h' hgz
    · exact Or.inl h'
    · exact Or.inr h'
  have hhxy : G.Adj h x ∨ G.Adj h y := by
    rcases hhadj with h' | h' | h'
    · exact absurd h' hhz
    · exact Or.inl h'
    · exact Or.inr h'
  exact ⟨g, h, hne, hgd, hhd, hgxy, hhxy, hgz, hhz, hgrich, hhrich⟩

/-! ## The corner closure and the C0 assembly -/

open Classical in
/-- **THE BLOCKED CHERRY CORNER CLOSES** in the `e(M) = 2` sea regime (`n ≥ 18`,
`Δ ≤ 4`, `mIncidence = 4`): under `ResidualCore`, a cherry all of whose iso twins are
double-blocked forces a `W1Config` or a `TwoBlockConfig` — the exact conclusion the
`caseCherry_dichotomy` corner interface asks for. -/
theorem blockedCherryCorner_close (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Fin n))
    (h : ResidualCore n G) (hsea : ∀ v : Fin n, G.degree v ≤ 4)
    (heM : mIncidence G = 4) {x z y : Fin n} (hch : Cherry G x z y)
    (hblock : ∀ t ∈ isoTwins G, 2 ≤ (badApexNbrs G x z y t).card) :
    W1Config G ∨ TwoBlockConfig G := by
  have hIso5 : 5 ≤ (isoTwins G).card :=
    eM_four_iso_card n (by omega) G h.edge_card h.min_degree hch heM
  obtain ⟨g, h', hne, hdg, hdh, hgxy, hhxy, hgz, hhz, hgr, hhr⟩ :=
    corner_rich_pair_exists G hsea hch hIso5 hblock
  exact p3_pair_close n hn G h.no_good_triangle h.no_good_C4 hch heM hIso5
    hne hdg hdh hgxy hhxy hgz hhz hgr hhr

open Classical in
/-- **The C0 closure on the `e(M) = 2` sea regime** (the strongest honest form of
`caseCherry_algConn_le_two`): a `ResidualCore` graph with `Δ ≤ 4` and
`mIncidence = 4` has `algConn G ≤ 2` — unconditionally, for every `n ≥ 18`.  Both
branches of `caseCherry_dichotomy` are discharged: the supply side by the cherry cut
certificates, the blocked corner by `blockedCherryCorner_close`. -/
theorem caseCherry_algConn_le_two_of_sea_eM_four (n : ℕ) [Nonempty (Fin n)]
    (hn : 18 ≤ n) (G : SimpleGraph (Fin n)) (h : ResidualCore n G)
    (hsea : ∀ v : Fin n, G.degree v ≤ 4) (heM : mIncidence G = 4) :
    algConn G ≤ 2 := by
  have hcc : CaseCherry G := by unfold CaseCherry; omega
  rcases caseCherry_dichotomy n G h hcc with htb | ⟨x, z, y, hcherry, -, hblock⟩
  · exact two_block_cut_certificate G htb
  · rcases blockedCherryCorner_close n hn G h hsea heM hcherry hblock with hw | htb
    · exact w1_algConn_le_two G hw
    · exact two_block_cut_certificate G htb

end ACMax
