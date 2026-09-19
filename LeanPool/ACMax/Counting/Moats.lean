/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
import LeanPool.ACMax.Counting.Quotient
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Two-cluster moat kills and the thin-twin averaging row

The *moat* family of two-cluster cut certificates: a low-degree tie-block `S₁`
whose closed neighbourhood forms a zeroed *moat* `F`, so that
`algConn_le_two_of_two_clusters` fires `algConn G ≤ 2` with no diameter, census
or cell hypotheses. Each vertex of `S₁` keeps an external degree budget of `2`,
so the boundary hits the two-cluster tie `∂₁ ≤ 2|S₁|` and the excess ledger
`Σ_v (deg v − 3) = n − 8` (`total_excess_eq`) caps the bulk boundary.

## Main results

* `medge_moat_fires` — an `M`-edge (a degree-3–degree-3 edge) fires at `n ≥ 12`.
* `star_moat_fires` (and `z1_star_moat_fires`) — a hub `h` hoarding `deg h − 2`
  degree-3 twins fires at `9·deg h ≤ n + 15`.
* `master_cycle_fires` — a cycle with degree-sum tie `Σ deg ≤ 4k` fires at
  `n ≥ 3·Σ(deg − 1) − 8`.
* `deco_edge_moat_fires` (and `z4c_fires`) — an adjacent hub pair hoarding
  `deg u − 3`, `deg v − 3` twins fires at `9·(deg u + deg v) ≤ n + 42`.
* The **thin-twin averaging row**: the double-counting swap
  `∑_{t∈T} E₁(t) = ∑_v (deg v − 3)·|N(v) ∩ T|` (`twin_E1_sum_swap`) with the
  excess ledger and a multiplicity cap `K` yields
  `∃ t ∈ T, |T|·E₁(t) ≤ K·(n − 8)` (`thin_twin_exists_of_multcap`), with the
  unconditional instances `thin_twin_exists_deg5` and
  `thin_twin_exists_iso_of_multcap`.
-/

/-! ## The thin-twin averaging row

The averaging engine producing a *thin* twin (bounded `1`-ball excess
`E₁(t) = sphereExc G t 1`). The double-counting swap `twin_E1_sum_swap` holds for
any root set `T`; combined with `total_excess_eq` and a multiplicity cap
`|N(v) ∩ T| ≤ K` it gives `∑_{t∈T} E₁(t) ≤ K·(n − 8)` and the averaging existence
`thin_twin_exists_of_multcap`. The cap `K` stays explicit (a heavy vertex's
multiplicity is unbounded); the clean instances are `thin_twin_exists_deg5`
(`K = 5` when `Δ ≤ 5`) and `thin_twin_exists_iso_of_multcap` (on `isoTwins G`). -/

namespace ACMax

open Finset

open Classical in
/-- **The excess ledger.**  On the `m = 2(n−2)`, `δ ≥ 3` census (`n ≥ 8`) the total degree
excess is `Σ_v (deg v − 3) = n − 8`: the handshake `Σ deg = 2·2(n−2) = 4n − 8` minus the
base `3n`. -/
theorem total_excess_eq {n : ℕ} (hn : 8 ≤ n) (G : SimpleGraph (Fin n))
    (hm : G.edgeFinset.card = 2 * (n - 2)) (h3 : ∀ v : Fin n, 3 ≤ G.degree v) :
    ∑ v : Fin n, (G.degree v - 3) = n - 8 := by
  have hhandshake : ∑ v : Fin n, G.degree v = 2 * (2 * (n - 2)) := by
    rw [G.sum_degrees_eq_twice_card_edges, hm]
  have hcancel : ∑ v : Fin n, G.degree v = (∑ v : Fin n, (G.degree v - 3)) + 3 * n := by
    have h3n : ∑ _v : Fin n, (3 : ℕ) = 3 * n := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]
    rw [← h3n, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun v _ => (Nat.sub_add_cancel (h3 v)).symm)
  omega

/-! ## The M-moat kill

Instantiates `algConn_le_two_of_two_clusters` with the tie-block `S₁ = {u, p}`
(an `M`-edge) against the bulk, moat `F = (N(u) ∪ N(p)) ∖ {u,p}`: `∂₁ = 4`,
`|F| ≤ 4`, so `medge_moat_fires` gives `algConn G ≤ 2` for every `n ≥ 12`. -/

open Classical in
/-- **QM1 — the M-moat certificate.**  A graph on `Fin n` (`n ≥ 12`) with `2(n−2)` edges,
minimum degree `≥ 3`, and one degree-`3`–degree-`3` edge `u–p` has `algConn G ≤ 2`.

Instantiate the two-cluster law with the tie-block `S₁ = {u, p}` against the bulk
`S₂ = ({u, p} ∪ F)ᶜ`, where `F = (N(u) ∪ N(p)) ∖ {u, p}` is the moat.  Boundary counts:
`∂₁ ≤ 4`, and (using that each moat vertex is adjacent to `u` or `p`, and the excess ledger
`Σ_v (deg v − 3) = n − 8`) `∂₂ ≤ 2·|S₂|`; the Fiedler cut condition then holds since `|F| ≤ 4`
and `n ≥ 12`. -/
theorem medge_moat_fires {n : ℕ} [Nonempty (Fin n)] (hn : 12 ≤ n)
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) (u p : Fin n) (hM : G.Adj u p)
    (hu : G.degree u = 3) (hp : G.degree p = 3) :
    algConn G ≤ 2 := by
  classical
  let : DecidableEq (Fin n) := Classical.decEq (Fin n)
  have hup : u ≠ p := hM.ne
  set S₁ : Finset (Fin n) := {u, p} with hS1def
  set F : Finset (Fin n) := (G.neighborFinset u ∪ G.neighborFinset p) \ S₁ with hFdef
  set S₂ : Finset (Fin n) := (S₁ ∪ F)ᶜ with hS2def
  -- basic cardinalities and memberships
  have hS1card : S₁.card = 2 := by rw [hS1def]; exact Finset.card_pair hup
  have hFsub : F ⊆ G.neighborFinset u ∪ G.neighborFinset p := by
    rw [hFdef]; exact Finset.sdiff_subset
  have huF : u ∉ F := by
    rw [hFdef, Finset.mem_sdiff]
    rintro ⟨_, hu2⟩
    exact hu2 (by rw [hS1def]; exact Finset.mem_insert_self u {p})
  have hpF : p ∉ F := by
    rw [hFdef, Finset.mem_sdiff]
    rintro ⟨_, hp2⟩
    exact hp2 (by rw [hS1def]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self p))
  have hFcard : F.card ≤ 4 := by
    have hsubpair : S₁ ⊆ G.neighborFinset u ∪ G.neighborFinset p := by
      rw [hS1def]
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_union, G.mem_neighborFinset, G.mem_neighborFinset]
      rcases hx with rfl | rfl
      · exact Or.inr hM.symm
      · exact Or.inl hM
    have hunion : (G.neighborFinset u ∪ G.neighborFinset p).card ≤ 6 := by
      calc (G.neighborFinset u ∪ G.neighborFinset p).card
          ≤ (G.neighborFinset u).card + (G.neighborFinset p).card := Finset.card_union_le _ _
        _ = 6 := by
            rw [G.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree, hu, hp]
    rw [hFdef, Finset.card_sdiff_of_subset hsubpair, hS1card]
    omega
  have hdisjS1F : Disjoint S₁ F := by
    rw [Finset.disjoint_left]
    intro a ha haF
    rw [hFdef, Finset.mem_sdiff] at haF
    exact haF.2 ha
  have hS2card : S₂.card = n - (2 + F.card) := by
    rw [hS2def, Finset.card_compl, Fintype.card_fin,
      Finset.card_union_of_disjoint hdisjS1F, hS1card]
  -- the counting helper: an ordered adjacency block splits into neighbourhood slices
  have hcnt : ∀ (A C : Finset (Fin n)),
      ((A ×ˢ C).filter (fun q => G.Adj q.1 q.2)).card
        = ∑ a ∈ A, (G.neighborFinset a ∩ C).card := by
    intro A C
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hset : G.neighborFinset a ∩ C = C.filter (fun v => G.Adj a v) := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact and_comm
    rw [hset, Finset.card_filter]
  -- the transpose helper (adjacency is symmetric)
  have htrans : ∀ (A C : Finset (Fin n)),
      ((A ×ˢ C).filter (fun q => G.Adj q.1 q.2)).card
        = ((C ×ˢ A).filter (fun q => G.Adj q.1 q.2)).card := by
    intro A C
    refine Finset.card_bij (fun q _ => (q.2, q.1)) ?_ ?_ ?_
    · intro q hq
      rw [Finset.mem_filter, Finset.mem_product] at hq ⊢
      exact ⟨⟨hq.1.2, hq.1.1⟩, G.adj_symm hq.2⟩
    · intro q _ r _ hqr
      exact Prod.ext (congrArg Prod.snd hqr) (congrArg Prod.fst hqr)
    · intro q hq
      refine ⟨(q.2, q.1), ?_, rfl⟩
      rw [Finset.mem_filter, Finset.mem_product] at hq ⊢
      exact ⟨⟨hq.1.2, hq.1.1⟩, G.adj_symm hq.2⟩
  -- ∂₁ ≤ 4
  have he1 : ((S₁ ×ˢ F).filter (fun q => G.Adj q.1 q.2)).card ≤ 4 := by
    rw [hcnt S₁ F, hS1def, Finset.sum_pair hup]
    have hu2 : (G.neighborFinset u ∩ F).card ≤ 2 := by
      have hsub : G.neighborFinset u ∩ F ⊆ (G.neighborFinset u).erase p := by
        intro x hx
        rw [Finset.mem_inter] at hx
        rw [Finset.mem_erase]
        exact ⟨fun hxp => hpF (hxp ▸ hx.2), hx.1⟩
      calc (G.neighborFinset u ∩ F).card
          ≤ ((G.neighborFinset u).erase p).card := Finset.card_le_card hsub
        _ = G.degree u - 1 := by
            rw [Finset.card_erase_of_mem ((G.mem_neighborFinset u p).mpr hM),
              G.card_neighborFinset_eq_degree]
        _ = 2 := by rw [hu]
    have hp2 : (G.neighborFinset p ∩ F).card ≤ 2 := by
      have hsub : G.neighborFinset p ∩ F ⊆ (G.neighborFinset p).erase u := by
        intro x hx
        rw [Finset.mem_inter] at hx
        rw [Finset.mem_erase]
        exact ⟨fun hxu => huF (hxu ▸ hx.2), hx.1⟩
      calc (G.neighborFinset p ∩ F).card
          ≤ ((G.neighborFinset p).erase u).card := Finset.card_le_card hsub
        _ = G.degree p - 1 := by
            rw [Finset.card_erase_of_mem ((G.mem_neighborFinset p u).mpr hM.symm),
              G.card_neighborFinset_eq_degree]
        _ = 2 := by rw [hp]
    omega
  -- ∂₂ ≤ 2·|S₂|
  have he2 : ((S₂ ×ˢ F).filter (fun q => G.Adj q.1 q.2)).card ≤ 2 * S₂.card := by
    rw [htrans S₂ F, hcnt F S₂]
    have hbound : ∀ w ∈ F, (G.neighborFinset w ∩ S₂).card ≤ G.degree w - 1 := by
      intro w hw
      obtain ⟨a, haS1, haw⟩ : ∃ a, a ∈ S₁ ∧ G.Adj a w := by
        have hmem : w ∈ G.neighborFinset u ∪ G.neighborFinset p := hFsub hw
        rw [Finset.mem_union, G.mem_neighborFinset, G.mem_neighborFinset] at hmem
        rcases hmem with h | h
        · exact ⟨u, by rw [hS1def]; exact Finset.mem_insert_self u {p}, h⟩
        · exact ⟨p, by rw [hS1def]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self p), h⟩
      have haNw : a ∈ G.neighborFinset w := (G.mem_neighborFinset w a).mpr haw.symm
      have haS2 : a ∉ S₂ := by
        rw [hS2def, Finset.mem_compl, not_not]
        exact Finset.mem_union_left F haS1
      have hsub : G.neighborFinset w ∩ S₂ ⊆ (G.neighborFinset w).erase a := by
        intro x hx
        rw [Finset.mem_inter] at hx
        rw [Finset.mem_erase]
        refine ⟨?_, hx.1⟩
        rintro rfl
        exact haS2 hx.2
      calc (G.neighborFinset w ∩ S₂).card
          ≤ ((G.neighborFinset w).erase a).card := Finset.card_le_card hsub
        _ = G.degree w - 1 := by
            rw [Finset.card_erase_of_mem haNw, G.card_neighborFinset_eq_degree]
    have hexc : ∑ w ∈ F, (G.degree w - 3) ≤ n - 8 := by
      calc ∑ w ∈ F, (G.degree w - 3)
          ≤ ∑ w : Fin n, (G.degree w - 3) := Finset.sum_le_sum_of_subset (Finset.subset_univ F)
        _ = n - 8 := total_excess_eq (by omega) G hm h3
    have hpt : ∀ w ∈ F, G.degree w - 1 = (G.degree w - 3) + 2 := by
      intro w _
      have := h3 w
      omega
    calc ∑ w ∈ F, (G.neighborFinset w ∩ S₂).card
        ≤ ∑ w ∈ F, (G.degree w - 1) := Finset.sum_le_sum hbound
      _ = ∑ w ∈ F, (G.degree w - 3) + F.card * 2 := by
          rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_const,
            smul_eq_mul]
      _ ≤ 2 * S₂.card := by omega
  -- assemble the two-cluster law
  have hS1ne : S₁.Nonempty := by rw [hS1def]; exact Finset.insert_nonempty u {p}
  have hS2ne : S₂.Nonempty := by
    rw [← Finset.card_pos, hS2card]; omega
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro a ha1 ha2
    rw [hS2def, Finset.mem_compl] at ha2
    exact ha2 (Finset.mem_union_left F ha1)
  have hnc : ∀ a ∈ S₁, ∀ v ∈ S₂, ¬G.Adj a v := by
    intro a ha v hv hadj
    rw [hS2def, Finset.mem_compl] at hv
    have hvnotS1 : v ∉ S₁ := fun h => hv (Finset.mem_union_left F h)
    have hvnotF : v ∉ F := fun h => hv (Finset.mem_union_right S₁ h)
    rw [hS1def, Finset.mem_insert, Finset.mem_singleton] at ha
    have hvmem : v ∈ G.neighborFinset u ∪ G.neighborFinset p := by
      rw [Finset.mem_union, G.mem_neighborFinset, G.mem_neighborFinset]
      rcases ha with rfl | rfl
      · exact Or.inl hadj
      · exact Or.inr hadj
    apply hvnotF
    rw [hFdef, Finset.mem_sdiff]
    exact ⟨hvmem, hvnotS1⟩
  have hFeq : (S₁ ∪ S₂)ᶜ = F := by
    ext v
    constructor
    · intro hv
      rw [Finset.mem_compl, Finset.mem_union, not_or] at hv
      obtain ⟨hvS1, hvS2⟩ := hv
      rw [hS2def, Finset.mem_compl, not_not, Finset.mem_union] at hvS2
      rcases hvS2 with h | h
      · exact absurd h hvS1
      · exact h
    · intro hv
      rw [Finset.mem_compl, Finset.mem_union, not_or]
      exact ⟨Finset.disjoint_right.mp hdisjS1F hv,
        by rw [hS2def, Finset.mem_compl, not_not]; exact Finset.mem_union_right S₁ hv⟩
  refine algConn_le_two_of_two_clusters G S₁ S₂ hS1ne hS2ne hdisj hnc ?_
  rw [hFeq, hS1card]
  have hbound1 := Nat.mul_le_mul he1 (le_refl (S₂.card ^ 2))
  have hbound2 := Nat.mul_le_mul he2 (le_refl ((2 : ℕ) ^ 2))
  refine le_trans (add_le_add hbound1 hbound2) (le_of_eq ?_)
  ring

/-! ## The star-moat kill

The `e(M) = 0` generalization: the star tie-block `S₁ = insert h K` (a hub `h`
with `|K| = deg h − 2` degree-3 twins), each `S₁`-vertex keeping external budget
`2`, so crediting the hub's excess back gives `star_moat_fires` at
`9·deg h ≤ n + 15` (`z1_star_moat_fires`: a degree-4 hub with two twins at
`n ≥ 21`). The twins need not be pairwise non-adjacent — an internal edge only
shrinks the boundary slices. -/

open Classical in
private theorem star_moat_fires_hsliceT : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (h : Fin n) (K :
  Finset (Fin n))
  (_ : K ⊆ G.neighborFinset h) (_ : ∀ t ∈ K, G.degree t = 3),
  let _ := Classical.decEq (Fin n);
  ∀ (S₁ : Finset (Fin n)) (_ : S₁ = insert h K), ∀ t ∈ K, #(G.neighborFinset t \ S₁) ≤ 2 := by
  classical
  intro n G h K hKsub hKdeg this S₁ hS1def t htK
  have htNh : t ∈ G.neighborFinset h := hKsub htK
  have hht : G.Adj h t := (G.mem_neighborFinset h t).mp htNh
  have hhNt : h ∈ G.neighborFinset t := (G.mem_neighborFinset t h).mpr hht.symm
  have hsub : G.neighborFinset t \ S₁ ⊆ (G.neighborFinset t).erase h := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    rw [Finset.mem_erase]
    refine ⟨fun hxh => hx.2 ?_, hx.1⟩
    rw [hS1def, hxh]
    exact Finset.mem_insert_self h K
  calc (G.neighborFinset t \ S₁).card
      ≤ ((G.neighborFinset t).erase h).card := Finset.card_le_card hsub
    _ = G.degree t - 1 := by
        rw [Finset.card_erase_of_mem hhNt, G.card_neighborFinset_eq_degree]
    _ = 2 := by rw [hKdeg t htK]

open Classical in
private theorem star_moat_fires_he2 : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (_ : ∀ (v : Fin n), 3 ≤
  G.degree v) (h : Fin n)
  (K : Finset (Fin n)) (_ : 9 * G.degree h ≤ n + 15),
  let _ := Classical.decEq (Fin n);
  ∀ (_ : 3 ≤ G.degree h),
    let S₁ := insert h K;
    ∀ (F : Finset (Fin n)) (_ : F = (S₁.biUnion fun x => G.neighborFinset x) \ S₁),
      let S₂ := (S₁ ∪ F)ᶜ;
      ∀ (_ : S₂ = (S₁ ∪ F)ᶜ) (_ : #S₁ = G.degree h - 1) (_ : #S₂ = n - (#S₁ + #F))
        (_ : ∀ (A C : Finset (Fin n)), #({q ∈ A ×ˢ C | G.Adj q.1 q.2}) = ∑ a ∈ A,
          #(G.neighborFinset a ∩ C))
        (_ : ∀ (A C : Finset (Fin n)), #({q ∈ A ×ˢ C | G.Adj q.1 q.2}) = #({q ∈ C ×ˢ A | G.Adj q.1
          q.2}))
        (_ : #F ≤ 2 * #S₁) (_ : ∑ w ∈ F, (G.degree w - 3) ≤ n - 8 - (G.degree h - 3)),
        #({q ∈ S₂ ×ˢ F | G.Adj q.1 q.2}) ≤ 2 * #S₂ := by
  classical
  intro n G h3 h K hfire this hdeg3 S₁ F hFdef S₂ hS2def hS1card hS2card hcnt htrans hFcard hexc
  rw [htrans S₂ F, hcnt F S₂]
  have hbound : ∀ w ∈ F, (G.neighborFinset w ∩ S₂).card ≤ G.degree w - 1 := by
    intro w hw
    obtain ⟨a, haS1, haw⟩ : ∃ a ∈ S₁, G.Adj a w := by
      have hwF := hw
      rw [hFdef, Finset.mem_sdiff, Finset.mem_biUnion] at hwF
      obtain ⟨⟨a, haS1, hwa⟩, _⟩ := hwF
      exact ⟨a, haS1, (G.mem_neighborFinset a w).mp hwa⟩
    have haNw : a ∈ G.neighborFinset w := (G.mem_neighborFinset w a).mpr haw.symm
    have haS2 : a ∉ S₂ := by
      rw [hS2def, Finset.mem_compl, not_not]
      exact Finset.mem_union_left F haS1
    have hsub : G.neighborFinset w ∩ S₂ ⊆ (G.neighborFinset w).erase a := by
      intro x hx
      rw [Finset.mem_inter] at hx
      rw [Finset.mem_erase]
      refine ⟨?_, hx.1⟩
      rintro rfl
      exact haS2 hx.2
    calc (G.neighborFinset w ∩ S₂).card
        ≤ ((G.neighborFinset w).erase a).card := Finset.card_le_card hsub
      _ = G.degree w - 1 := by
          rw [Finset.card_erase_of_mem haNw, G.card_neighborFinset_eq_degree]
  have hpt : ∀ w ∈ F, G.degree w - 1 = (G.degree w - 3) + 2 := by
    intro w _
    have := h3 w
    omega
  calc ∑ w ∈ F, (G.neighborFinset w ∩ S₂).card
      ≤ ∑ w ∈ F, (G.degree w - 1) := Finset.sum_le_sum hbound
    _ = ∑ w ∈ F, (G.degree w - 3) + F.card * 2 := by
        rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_const,
          smul_eq_mul]
    _ ≤ 2 * S₂.card := by omega

open Classical in
/-- **MZ1 — the star-moat certificate.**  A graph on `Fin n` with `2(n−2)` edges, minimum
degree `≥ 3`, a hub `h` and a twin set `K ⊆ N(h)` of degree-`3` vertices with `|K| = deg h − 2`
has `algConn G ≤ 2` whenever `9·deg h ≤ n + 15`.

Instantiate the two-cluster law with the tie-block `S₁ = insert h K` against the bulk
`S₂ = (S₁ ∪ F)ᶜ`, `F = (⋃_{x ∈ S₁} N(x)) ∖ S₁` the moat: each slice `N(x) ∖ S₁` has `≤ 2`
elements (hub loses `K`, twins lose the hub), so `∂₁ ≤ 2|S₁|` and `|F| ≤ 2|S₁|`, and the
hub-credited excess ledger gives `∂₂ ≤ 2|S₂|`; the Fiedler cut condition closes by `ring`. -/
theorem star_moat_fires {n : ℕ} [Nonempty (Fin n)]
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) (h : Fin n) (K : Finset (Fin n))
    (hKsub : K ⊆ G.neighborFinset h) (hKdeg : ∀ t ∈ K, G.degree t = 3)
    (hKcard : K.card = G.degree h - 2) (hfire : 9 * G.degree h ≤ n + 15) :
    algConn G ≤ 2 := by
  classical
  let : DecidableEq (Fin n) := Classical.decEq (Fin n)
  have hdeg3 : 3 ≤ G.degree h := h3 h
  have hn8 : 8 ≤ n := by omega
  have hhK : h ∉ K := by
    intro hh
    have hmem := hKsub hh
    rw [G.mem_neighborFinset] at hmem
    exact (G.ne_of_adj hmem) rfl
  set S₁ : Finset (Fin n) := insert h K with hS1def
  set F : Finset (Fin n) := (S₁.biUnion (fun x => G.neighborFinset x)) \ S₁ with hFdef
  set S₂ : Finset (Fin n) := (S₁ ∪ F)ᶜ with hS2def
  have hS1card : S₁.card = G.degree h - 1 := by
    rw [hS1def, Finset.card_insert_of_notMem hhK, hKcard]
    omega
  have hS1ne : S₁.Nonempty := by rw [hS1def]; exact Finset.insert_nonempty h K
  have huF : h ∉ F := by
    rw [hFdef]
    intro hmem
    rw [Finset.mem_sdiff] at hmem
    exact hmem.2 (by rw [hS1def]; exact Finset.mem_insert_self h K)
  have hdisjS1F : Disjoint S₁ F := by
    rw [Finset.disjoint_left]
    intro a ha haF
    rw [hFdef, Finset.mem_sdiff] at haF
    exact haF.2 ha
  have hS2card : S₂.card = n - (S₁.card + F.card) := by
    rw [hS2def, Finset.card_compl, Fintype.card_fin,
      Finset.card_union_of_disjoint hdisjS1F]
  -- the counting helper: an ordered adjacency block splits into neighbourhood slices
  have hcnt : ∀ (A C : Finset (Fin n)),
      ((A ×ˢ C).filter (fun q => G.Adj q.1 q.2)).card
        = ∑ a ∈ A, (G.neighborFinset a ∩ C).card := by
    intro A C
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hset : G.neighborFinset a ∩ C = C.filter (fun v => G.Adj a v) := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact and_comm
    rw [hset, Finset.card_filter]
  -- the transpose helper (adjacency is symmetric)
  have htrans : ∀ (A C : Finset (Fin n)),
      ((A ×ˢ C).filter (fun q => G.Adj q.1 q.2)).card
        = ((C ×ˢ A).filter (fun q => G.Adj q.1 q.2)).card := by
    intro A C
    refine Finset.card_bij (fun q _ => (q.2, q.1)) ?_ ?_ ?_
    · intro q hq
      rw [Finset.mem_filter, Finset.mem_product] at hq ⊢
      exact ⟨⟨hq.1.2, hq.1.1⟩, G.adj_symm hq.2⟩
    · intro q _ r _ hqr
      exact Prod.ext (congrArg Prod.snd hqr) (congrArg Prod.fst hqr)
    · intro q hq
      refine ⟨(q.2, q.1), ?_, rfl⟩
      rw [Finset.mem_filter, Finset.mem_product] at hq ⊢
      exact ⟨⟨hq.1.2, hq.1.1⟩, G.adj_symm hq.2⟩
  -- every slice `N(x) ∖ S₁` has at most two elements (external-degree budget 2)
  have hsliceH : (G.neighborFinset h \ S₁).card ≤ 2 := by
    have hsub : G.neighborFinset h \ S₁ ⊆ G.neighborFinset h \ K :=
      Finset.sdiff_subset_sdiff (le_refl _) (by rw [hS1def]; exact Finset.subset_insert h K)
    calc (G.neighborFinset h \ S₁).card
        ≤ (G.neighborFinset h \ K).card := Finset.card_le_card hsub
      _ = (G.neighborFinset h).card - K.card := Finset.card_sdiff_of_subset hKsub
      _ = G.degree h - K.card := by rw [G.card_neighborFinset_eq_degree]
      _ ≤ 2 := by rw [hKcard]; omega
  have hsliceT :=
      star_moat_fires_hsliceT (n := n) (G := G) (h := h) (K := K) (hKsub) (hKdeg) (S₁ := S₁)
        (hS1def)
  have hslice : ∀ x ∈ S₁, (G.neighborFinset x \ S₁).card ≤ 2 := by
    intro x hx
    rw [hS1def, Finset.mem_insert] at hx
    rcases hx with rfl | hxK
    · exact hsliceH
    · exact hsliceT x hxK
  -- ∂₁ ≤ 2·|S₁|
  have hterm : ∀ a ∈ S₁, (G.neighborFinset a ∩ F).card ≤ 2 := by
    intro a ha
    have hsub : G.neighborFinset a ∩ F ⊆ G.neighborFinset a \ S₁ := by
      intro x hx
      rw [Finset.mem_inter] at hx
      rw [Finset.mem_sdiff]
      refine ⟨hx.1, ?_⟩
      have hxF := hx.2
      rw [hFdef, Finset.mem_sdiff] at hxF
      exact hxF.2
    exact le_trans (Finset.card_le_card hsub) (hslice a ha)
  have he1 : ((S₁ ×ˢ F).filter (fun q => G.Adj q.1 q.2)).card ≤ 2 * S₁.card := by
    rw [hcnt S₁ F]
    calc ∑ a ∈ S₁, (G.neighborFinset a ∩ F).card
        ≤ ∑ _a ∈ S₁, 2 := Finset.sum_le_sum hterm
      _ = 2 * S₁.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  -- |F| ≤ 2·|S₁|
  have hFcard : F.card ≤ 2 * S₁.card := by
    have hFsub2 : F ⊆ S₁.biUnion (fun x => G.neighborFinset x \ S₁) := by
      intro y hy
      rw [hFdef, Finset.mem_sdiff] at hy
      obtain ⟨hyNS, hyS1⟩ := hy
      rw [Finset.mem_biUnion] at hyNS ⊢
      obtain ⟨x, hxS1, hyx⟩ := hyNS
      exact ⟨x, hxS1, Finset.mem_sdiff.mpr ⟨hyx, hyS1⟩⟩
    calc F.card
        ≤ (S₁.biUnion (fun x => G.neighborFinset x \ S₁)).card := Finset.card_le_card hFsub2
      _ ≤ ∑ x ∈ S₁, (G.neighborFinset x \ S₁).card := Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ S₁, 2 := Finset.sum_le_sum hslice
      _ = 2 * S₁.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  -- the hub-credited excess ledger: Σ_F (deg − 3) ≤ (n − 8) − (deg h − 3)
  have hFsubErase : F ⊆ Finset.univ.erase h := by
    intro x hx
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ x⟩
    rintro rfl
    exact huF hx
  have hexc : ∑ w ∈ F, (G.degree w - 3) ≤ n - 8 - (G.degree h - 3) := by
    have hle : ∑ w ∈ F, (G.degree w - 3)
        ≤ ∑ w ∈ Finset.univ.erase h, (G.degree w - 3) :=
      Finset.sum_le_sum_of_subset hFsubErase
    have hsplit : (G.degree h - 3) + ∑ w ∈ Finset.univ.erase h, (G.degree w - 3)
        = ∑ w : Fin n, (G.degree w - 3) :=
      Finset.add_sum_erase _ (fun w => G.degree w - 3) (Finset.mem_univ h)
    have htot : ∑ w : Fin n, (G.degree w - 3) = n - 8 := total_excess_eq hn8 G hm h3
    omega
  have hS2ne : S₂.Nonempty := by
    rw [← Finset.card_pos, hS2card]; omega
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro a ha1 ha2
    rw [hS2def, Finset.mem_compl] at ha2
    exact ha2 (Finset.mem_union_left F ha1)
  have hnc : ∀ a ∈ S₁, ∀ v ∈ S₂, ¬G.Adj a v := by
    intro a ha v hv hadj
    rw [hS2def, Finset.mem_compl] at hv
    have hvnotS1 : v ∉ S₁ := fun hh => hv (Finset.mem_union_left F hh)
    have hvnotF : v ∉ F := fun hh => hv (Finset.mem_union_right S₁ hh)
    apply hvnotF
    rw [hFdef, Finset.mem_sdiff]
    refine ⟨?_, hvnotS1⟩
    rw [Finset.mem_biUnion]
    exact ⟨a, ha, (G.mem_neighborFinset a v).mpr hadj⟩
  have hFeq : (S₁ ∪ S₂)ᶜ = F := by
    ext v
    constructor
    · intro hv
      rw [Finset.mem_compl, Finset.mem_union, not_or] at hv
      obtain ⟨hvS1, hvS2⟩ := hv
      rw [hS2def, Finset.mem_compl, not_not, Finset.mem_union] at hvS2
      rcases hvS2 with hh | hh
      · exact absurd hh hvS1
      · exact hh
    · intro hv
      rw [Finset.mem_compl, Finset.mem_union, not_or]
      exact ⟨Finset.disjoint_right.mp hdisjS1F hv,
        by rw [hS2def, Finset.mem_compl, not_not]; exact Finset.mem_union_right S₁ hv⟩
  -- ∂₂ ≤ 2·|S₂|
  have he2 := star_moat_fires_he2 (n := n) (G := G) (h3) (h := h) (K := K) (hfire)
      (hdeg3) (F := F) (hFdef) (hS2def) (hS1card) (hS2card) (hcnt) (htrans) (hFcard) (hexc)
  -- assemble the two-cluster law at the tie
  refine algConn_le_two_of_two_clusters G S₁ S₂ hS1ne hS2ne hdisj hnc ?_
  rw [hFeq]
  have hbound1 := Nat.mul_le_mul he1 (le_refl (S₂.card ^ 2))
  have hbound2 := Nat.mul_le_mul he2 (le_refl (S₁.card ^ 2))
  refine le_trans (add_le_add hbound1 hbound2) (le_of_eq ?_)
  ring

/-! ## The master-cycle kill

A cycle `c : ZMod k → Fin n` (injective, cyclic adjacency) with degree-sum tie
`Σ deg ≤ 4·k` is a tie-block: each cycle vertex has two on-cycle neighbours so
external slice `≤ deg − 2`, giving `∂₁ ≤ Σ(deg − 2) ≤ 2k`; crediting the cycle
excess back, `master_cycle_fires` fires at `n ≥ 3·Σ(deg − 1) − 8` (specializing
to `C_k`, the `(3,4,5)`-triangle at `n ≥ 19`, and alternating rows). -/

open Classical in
private theorem master_cycle_fires_hsliceIdx : ∀ {n k : ℕ} [NeZero k] (G : SimpleGraph (Fin n)) (c
  : ZMod k → Fin n)
  (_ : Function.Injective c) (_ : ∀ (i : ZMod k), G.Adj (c i) (c (i + 1))),
  let _ := Classical.decEq (Fin n);
  ∀ (_ : (2 : ZMod k) ≠ 0),
    let S₁ := image c univ;
    ∀ (i : ZMod k), #(G.neighborFinset (c i) \ S₁) ≤ G.degree (c i) - 2 := by
  classical
  intro n k inst G c hcinj hadj this h2ne S₁ i
  have hib : (i - 1) + 1 = i := by ring
  have hadjb : G.Adj (c i) (c (i - 1)) := by
    have hh := hadj (i - 1)
    rw [hib] at hh
    exact hh.symm
  have hkey : (i : ZMod k) + 1 ≠ i - 1 := by
    intro heq
    apply h2ne
    have h2 : (2 : ZMod k) = (i + 1) - (i - 1) := by ring
    rw [heq, sub_self] at h2
    exact h2
  have hdist : c (i + 1) ≠ c (i - 1) := fun heq => hkey (hcinj heq)
  have h2le : 2 ≤ (G.neighborFinset (c i) ∩ S₁).card := by
    have hsub : ({c (i + 1), c (i - 1)} : Finset (Fin n))
        ⊆ G.neighborFinset (c i) ∩ S₁ := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_inter]
      rcases hx with rfl | rfl
      · exact ⟨(G.mem_neighborFinset _ _).mpr (hadj i),
          Finset.mem_image.mpr ⟨i + 1, Finset.mem_univ _, rfl⟩⟩
      · exact ⟨(G.mem_neighborFinset _ _).mpr hadjb,
          Finset.mem_image.mpr ⟨i - 1, Finset.mem_univ _, rfl⟩⟩
    calc 2 = ({c (i + 1), c (i - 1)} : Finset (Fin n)).card := by
          rw [Finset.card_pair hdist]
      _ ≤ _ := Finset.card_le_card hsub
  have hcard : (G.neighborFinset (c i) ∩ S₁).card + (G.neighborFinset (c i) \ S₁).card
      = G.degree (c i) := by
    rw [Finset.card_inter_add_card_sdiff, G.card_neighborFinset_eq_degree]
  omega

open Classical in
private theorem master_cycle_fires_he1 : ∀ {n k : ℕ} [NeZero k] (G : SimpleGraph (Fin n)) (c :
  ZMod k → Fin n),
  let _ := Classical.decEq (Fin n);
  let S₁ := image c univ;
  ∀ (F : Finset (Fin n)) (_ : F = (S₁.biUnion fun x => G.neighborFinset x) \ S₁),
    let D := ∑ i, G.degree (c i);
    ∀ (_ : D ≤ 4 * k) (_ : #S₁ = k) (_ : ∑ x ∈ S₁, G.degree x = D)
      (_ : ∀ x ∈ S₁, #(G.neighborFinset x \ S₁) ≤ G.degree x - 2)
      (_ : ∀ (A C : Finset (Fin n)), #({q ∈ A ×ˢ C | G.Adj q.1 q.2}) = ∑ a ∈ A, #(G.neighborFinset
        a ∩ C))
      (_ : ∑ x ∈ S₁, (G.degree x - 2) + 2 * #S₁ = D) (_ : ∑ x ∈ S₁, (G.degree x - 3) + 3 * #S₁ = D),
      #({q ∈ S₁ ×ˢ F | G.Adj q.1 q.2}) ≤ 2 * #S₁ := by
  classical
  intro n k inst G c this S₁ F hFdef D hsum hS1card hDS1 hslice hcnt keyB keyX
  rw [hcnt S₁ F]
  have hterm : ∀ a ∈ S₁, (G.neighborFinset a ∩ F).card ≤ G.degree a - 2 := by
    intro a ha
    have hsub : G.neighborFinset a ∩ F ⊆ G.neighborFinset a \ S₁ := by
      intro x hx
      rw [Finset.mem_inter] at hx
      rw [Finset.mem_sdiff]
      refine ⟨hx.1, ?_⟩
      have hxF := hx.2
      rw [hFdef, Finset.mem_sdiff] at hxF
      exact hxF.2
    exact le_trans (Finset.card_le_card hsub) (hslice a ha)
  calc ∑ a ∈ S₁, (G.neighborFinset a ∩ F).card
      ≤ ∑ a ∈ S₁, (G.degree a - 2) := Finset.sum_le_sum hterm
    _ ≤ 2 * S₁.card := by
        have := keyB; have := hsum; have := hS1card; omega

open Classical in
private theorem master_cycle_fires_he2 : ∀ {n k : ℕ} [NeZero k] (G : SimpleGraph (Fin n))
  (_ : ∀ (v : Fin n), 3 ≤ G.degree v) (c : ZMod k → Fin n) (_ : 3 * ∑ i, (G.degree (c i) - 1) ≤ n
    + 8),
  let _ := Classical.decEq (Fin n);
  ∀ (_ : 8 ≤ n),
    let S₁ := image c univ;
    ∀ (F : Finset (Fin n)) (_ : F = (S₁.biUnion fun x => G.neighborFinset x) \ S₁),
      let S₂ := (S₁ ∪ F)ᶜ;
      ∀ (_ : S₂ = (S₁ ∪ F)ᶜ),
        let D := ∑ i, G.degree (c i);
        ∀ (_ : D ≤ 4 * k) (_ : #S₁ = k) (_ : ∑ x ∈ S₁, G.degree x = D) (_ : #S₂ = n - (#S₁ + #F))
          (_ : #S₁ + #F ≤ n)
          (_ : ∀ (A C : Finset (Fin n)), #({q ∈ A ×ˢ C | G.Adj q.1 q.2}) = ∑ a ∈ A,
            #(G.neighborFinset a ∩ C))
          (_ : ∀ (A C : Finset (Fin n)), #({q ∈ A ×ˢ C | G.Adj q.1 q.2}) = #({q ∈ C ×ˢ A | G.Adj
            q.1 q.2}))
          (_ : ∑ x ∈ S₁, (G.degree x - 2) + 2 * #S₁ = D) (_ : ∑ x ∈ S₁, (G.degree x - 3) + 3 * #S₁
            = D)
          (_ : ∑ i, (G.degree (c i) - 1) + k = D) (_ : #F ≤ ∑ x ∈ S₁, (G.degree x - 2)) (_ : #F +
            2 * #S₁ ≤ D)
          (_ : ∑ w ∈ F, (G.degree w - 3) + ∑ x ∈ S₁, (G.degree x - 3) ≤ n - 8),
          #({q ∈ S₂ ×ˢ F | G.Adj q.1 q.2}) ≤ 2 * #S₂ := by
  classical
  intro n k inst G h3 c hn this hn8 S₁ F hFdef S₂ hS2def D hsum hS1card hDS1 hS2card hkfn hcnt
    htrans keyB keyX keyP hFB keyF hexc
  rw [htrans S₂ F, hcnt F S₂]
  have hbound : ∀ w ∈ F, (G.neighborFinset w ∩ S₂).card ≤ G.degree w - 1 := by
    intro w hw
    obtain ⟨a, haS1, haw⟩ : ∃ a ∈ S₁, G.Adj a w := by
      have hwF := hw
      rw [hFdef, Finset.mem_sdiff, Finset.mem_biUnion] at hwF
      obtain ⟨⟨a, haS1, hwa⟩, _⟩ := hwF
      exact ⟨a, haS1, (G.mem_neighborFinset a w).mp hwa⟩
    have haNw : a ∈ G.neighborFinset w := (G.mem_neighborFinset w a).mpr haw.symm
    have haS2 : a ∉ S₂ := by
      rw [hS2def, Finset.mem_compl, not_not]
      exact Finset.mem_union_left F haS1
    have hsub : G.neighborFinset w ∩ S₂ ⊆ (G.neighborFinset w).erase a := by
      intro x hx
      rw [Finset.mem_inter] at hx
      rw [Finset.mem_erase]
      refine ⟨?_, hx.1⟩
      rintro rfl
      exact haS2 hx.2
    calc (G.neighborFinset w ∩ S₂).card
        ≤ ((G.neighborFinset w).erase a).card := Finset.card_le_card hsub
      _ = G.degree w - 1 := by
          rw [Finset.card_erase_of_mem haNw, G.card_neighborFinset_eq_degree]
  have hpt : ∀ w ∈ F, G.degree w - 1 = (G.degree w - 3) + 2 := by
    intro w _
    have := h3 w
    omega
  calc ∑ w ∈ F, (G.neighborFinset w ∩ S₂).card
      ≤ ∑ w ∈ F, (G.degree w - 1) := Finset.sum_le_sum hbound
    _ = ∑ w ∈ F, (G.degree w - 3) + F.card * 2 := by
        rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_const,
          smul_eq_mul]
    _ ≤ 2 * S₂.card := by
        have := hexc; have := keyX; have := keyP; have := hsum; have := hn
        have := keyF; have := hS2card; have := hkfn; have := hS1card
        omega

open Classical in
/-- **W1 — the master-cycle certificate.**  A graph on `Fin n` with `2(n−2)` edges, minimum
degree `≥ 3`, and an injective `c : ZMod k → Fin n` (`k ≥ 3`) forming a cycle
(`c i ~ c (i+1)` cyclically) whose degree sum satisfies the tie `Σ deg (c i) ≤ 4·k` has
`algConn G ≤ 2` whenever `3·Σ (deg (c i) − 1) ≤ n + 8`.

Instantiate the two-cluster law with the tie-block `S₁ = image c` (the cycle) against the bulk
`S₂ = (S₁ ∪ F)ᶜ`, `F = (⋃_{x ∈ S₁} N(x)) ∖ S₁` the moat: each slice `N(c i) ∖ S₁` has
`≤ deg (c i) − 2` elements (the two cycle neighbours stay inside), so `∂₁ ≤ Σ(deg − 2) ≤ 2·k`
and `|F| ≤ Σ(deg − 2)`, and the full excess ledger gives `∂₂ ≤ 2·|S₂|`; the Fiedler cut
condition closes by `ring`. -/
theorem master_cycle_fires {n : ℕ} [Nonempty (Fin n)] {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) (c : ZMod k → Fin n) (hcinj : Function.Injective c)
    (hadj : ∀ i : ZMod k, G.Adj (c i) (c (i + 1)))
    (hsum : ∑ i : ZMod k, G.degree (c i) ≤ 4 * k)
    (hn : 3 * (∑ i : ZMod k, (G.degree (c i) - 1)) ≤ n + 8) :
    algConn G ≤ 2 := by
  classical
  let : DecidableEq (Fin n) := Classical.decEq (Fin n)
  have hn8 : 8 ≤ n := by
    have hb : 3 * k ≤ ∑ i : ZMod k, G.degree (c i) := by
      calc 3 * k = ∑ _i : ZMod k, 3 := by
            rw [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul, mul_comm]
        _ ≤ ∑ i : ZMod k, G.degree (c i) := Finset.sum_le_sum (fun i _ => h3 (c i))
    have hP : 2 * k ≤ ∑ i : ZMod k, (G.degree (c i) - 1) := by
      calc 2 * k = ∑ _i : ZMod k, 2 := by
            rw [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul, mul_comm]
        _ ≤ ∑ i : ZMod k, (G.degree (c i) - 1) :=
            Finset.sum_le_sum (fun i _ => by have := h3 (c i); omega)
    omega
  -- the two distinct cycle neighbours of every vertex live in `S₁`
  have h2ne : (2 : ZMod k) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod k) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  set S₁ : Finset (Fin n) := Finset.image c Finset.univ with hS1def
  set F : Finset (Fin n) := (S₁.biUnion (fun x => G.neighborFinset x)) \ S₁ with hFdef
  set S₂ : Finset (Fin n) := (S₁ ∪ F)ᶜ with hS2def
  set D : ℕ := ∑ i : ZMod k, G.degree (c i) with hDdef
  have hS1card : S₁.card = k := by
    rw [hS1def, Finset.card_image_of_injective _ hcinj, Finset.card_univ, ZMod.card]
  have hS1ne : S₁.Nonempty :=
    ⟨c 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ 0, rfl⟩⟩
  have hDS1 : ∑ x ∈ S₁, G.degree x = D := by
    rw [hDdef, hS1def, Finset.sum_image (fun x _ y _ h => hcinj h)]
  -- per-vertex slice bound: each cycle vertex has `≥ 2` neighbours inside `S₁`
  have hsliceIdx :=
      master_cycle_fires_hsliceIdx (n := n) (k := k) (G := G) (c := c) (hcinj) (hadj) (h2ne)
  have hslice : ∀ x ∈ S₁, (G.neighborFinset x \ S₁).card ≤ G.degree x - 2 := by
    intro x hx
    rw [hS1def, Finset.mem_image] at hx
    obtain ⟨i, _, rfl⟩ := hx
    exact hsliceIdx i
  -- the disjointness / cardinality bookkeeping (mirrors `star_moat_fires`)
  have hdisjS1F : Disjoint S₁ F := by
    rw [Finset.disjoint_left]
    intro a ha haF
    rw [hFdef, Finset.mem_sdiff] at haF
    exact haF.2 ha
  have hS2card : S₂.card = n - (S₁.card + F.card) := by
    rw [hS2def, Finset.card_compl, Fintype.card_fin,
      Finset.card_union_of_disjoint hdisjS1F]
  have hkfn : S₁.card + F.card ≤ n := by
    have h : (S₁ ∪ F).card ≤ Fintype.card (Fin n) := Finset.card_le_univ _
    rw [Fintype.card_fin, Finset.card_union_of_disjoint hdisjS1F] at h
    exact h
  -- the counting helper: an ordered adjacency block splits into neighbourhood slices
  have hcnt : ∀ (A C : Finset (Fin n)),
      ((A ×ˢ C).filter (fun q => G.Adj q.1 q.2)).card
        = ∑ a ∈ A, (G.neighborFinset a ∩ C).card := by
    intro A C
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hset : G.neighborFinset a ∩ C = C.filter (fun v => G.Adj a v) := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact and_comm
    rw [hset, Finset.card_filter]
  -- the transpose helper (adjacency is symmetric)
  have htrans : ∀ (A C : Finset (Fin n)),
      ((A ×ˢ C).filter (fun q => G.Adj q.1 q.2)).card
        = ((C ×ˢ A).filter (fun q => G.Adj q.1 q.2)).card := by
    intro A C
    refine Finset.card_bij (fun q _ => (q.2, q.1)) ?_ ?_ ?_
    · intro q hq
      rw [Finset.mem_filter, Finset.mem_product] at hq ⊢
      exact ⟨⟨hq.1.2, hq.1.1⟩, G.adj_symm hq.2⟩
    · intro q _ r _ hqr
      exact Prod.ext (congrArg Prod.snd hqr) (congrArg Prod.fst hqr)
    · intro q hq
      refine ⟨(q.2, q.1), ?_, rfl⟩
      rw [Finset.mem_filter, Finset.mem_product] at hq ⊢
      exact ⟨⟨hq.1.2, hq.1.1⟩, G.adj_symm hq.2⟩
  -- `Σ_{S₁}(deg − 2) + 2·|S₁| = D` and `Σ_{S₁}(deg − 3) + 3·|S₁| = D`
  have keyB : (∑ x ∈ S₁, (G.degree x - 2)) + 2 * S₁.card = D := by
    have h1 : 2 * S₁.card = ∑ _x ∈ S₁, 2 := by
      rw [Finset.sum_const, smul_eq_mul, mul_comm]
    rw [h1, ← Finset.sum_add_distrib, ← hDS1]
    exact Finset.sum_congr rfl (fun x _ => Nat.sub_add_cancel (by have := h3 x; omega))
  have keyX : (∑ x ∈ S₁, (G.degree x - 3)) + 3 * S₁.card = D := by
    have h1 : 3 * S₁.card = ∑ _x ∈ S₁, 3 := by
      rw [Finset.sum_const, smul_eq_mul, mul_comm]
    rw [h1, ← Finset.sum_add_distrib, ← hDS1]
    exact Finset.sum_congr rfl (fun x _ => Nat.sub_add_cancel (h3 x))
  have keyP : (∑ i : ZMod k, (G.degree (c i) - 1)) + k = D := by
    have hstep : ∑ i : ZMod k, ((G.degree (c i) - 1) + 1) = D := by
      rw [hDdef]
      exact Finset.sum_congr rfl (fun i _ => Nat.sub_add_cancel (by have := h3 (c i); omega))
    rw [Finset.sum_add_distrib] at hstep
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul, mul_one] at hstep
    exact hstep
  -- the moat is capped by the same slice budget
  have hFB : F.card ≤ ∑ x ∈ S₁, (G.degree x - 2) := by
    have hFsub2 : F ⊆ S₁.biUnion (fun x => G.neighborFinset x \ S₁) := by
      intro y hy
      rw [hFdef, Finset.mem_sdiff] at hy
      obtain ⟨hyNS, hyS1⟩ := hy
      rw [Finset.mem_biUnion] at hyNS ⊢
      obtain ⟨x, hxS1, hyx⟩ := hyNS
      exact ⟨x, hxS1, Finset.mem_sdiff.mpr ⟨hyx, hyS1⟩⟩
    calc F.card
        ≤ (S₁.biUnion (fun x => G.neighborFinset x \ S₁)).card := Finset.card_le_card hFsub2
      _ ≤ ∑ x ∈ S₁, (G.neighborFinset x \ S₁).card := Finset.card_biUnion_le
      _ ≤ ∑ x ∈ S₁, (G.degree x - 2) := Finset.sum_le_sum hslice
  have keyF : F.card + 2 * S₁.card ≤ D := by
    have := keyB
    omega
  -- the full excess ledger: `Σ_F(deg − 3) + Σ_{S₁}(deg − 3) ≤ n − 8`
  have hexc : (∑ w ∈ F, (G.degree w - 3)) + (∑ x ∈ S₁, (G.degree x - 3)) ≤ n - 8 := by
    have hunion : (∑ w ∈ F, (G.degree w - 3)) + (∑ x ∈ S₁, (G.degree x - 3))
        = ∑ w ∈ (F ∪ S₁), (G.degree w - 3) := (Finset.sum_union hdisjS1F.symm).symm
    rw [hunion]
    calc ∑ w ∈ (F ∪ S₁), (G.degree w - 3)
        ≤ ∑ w : Fin n, (G.degree w - 3) := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = n - 8 := total_excess_eq hn8 G hm h3
  have hS2ne : S₂.Nonempty := by
    rw [← Finset.card_pos, hS2card]
    have := keyF; have := hsum; have := keyX; have := keyP; have := hn; have := hS1card
    omega
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro a ha1 ha2
    rw [hS2def, Finset.mem_compl] at ha2
    exact ha2 (Finset.mem_union_left F ha1)
  have hnc : ∀ a ∈ S₁, ∀ v ∈ S₂, ¬G.Adj a v := by
    intro a ha v hv hadjav
    rw [hS2def, Finset.mem_compl] at hv
    have hvnotS1 : v ∉ S₁ := fun hh => hv (Finset.mem_union_left F hh)
    have hvnotF : v ∉ F := fun hh => hv (Finset.mem_union_right S₁ hh)
    apply hvnotF
    rw [hFdef, Finset.mem_sdiff]
    refine ⟨?_, hvnotS1⟩
    rw [Finset.mem_biUnion]
    exact ⟨a, ha, (G.mem_neighborFinset a v).mpr hadjav⟩
  have hFeq : (S₁ ∪ S₂)ᶜ = F := by
    ext v
    constructor
    · intro hv
      rw [Finset.mem_compl, Finset.mem_union, not_or] at hv
      obtain ⟨hvS1, hvS2⟩ := hv
      rw [hS2def, Finset.mem_compl, not_not, Finset.mem_union] at hvS2
      rcases hvS2 with hh | hh
      · exact absurd hh hvS1
      · exact hh
    · intro hv
      rw [Finset.mem_compl, Finset.mem_union, not_or]
      exact ⟨Finset.disjoint_right.mp hdisjS1F hv,
        by rw [hS2def, Finset.mem_compl, not_not]; exact Finset.mem_union_right S₁ hv⟩
  -- ∂₁ ≤ 2·|S₁|
  have he1 := master_cycle_fires_he1 (n := n) (k := k) (G := G) (c := c) (F := F) (hFdef)
      (hsum) (hS1card) (hDS1) (hslice) (hcnt) (keyB) (keyX)
  -- ∂₂ ≤ 2·|S₂|
  have he2 :=
      master_cycle_fires_he2 (n := n) (k := k) (G := G) (h3) (c := c) (hn) (hn8) (F := F) (hFdef)
        (hS2def) (hsum) (hS1card) (hDS1) (hS2card) (hkfn) (hcnt) (htrans) (keyB) (keyX) (keyP)
        (hFB) (keyF) (hexc)
  -- assemble the two-cluster law at the tie
  refine algConn_le_two_of_two_clusters G S₁ S₂ hS1ne hS2ne hdisj hnc ?_
  rw [hFeq]
  have hbound1 := Nat.mul_le_mul he1 (le_refl (S₂.card ^ 2))
  have hbound2 := Nat.mul_le_mul he2 (le_refl (S₁.card ^ 2))
  refine le_trans (add_le_add hbound1 hbound2) (le_of_eq ?_)
  ring

/-! ## The decorated-edge moat kill

The *decorated-edge* generalization of the star-moat certificate: the tie-block
`S₁ = {u, v} ∪ Ku ∪ Kv` (an adjacent hub pair with `|Ku| = deg u − 3`,
`|Kv| = deg v − 3` twins), each `S₁`-vertex keeping external budget `2`;
crediting both hubs' excess back, `deco_edge_moat_fires` fires at
`9·(deg u + deg v) ≤ n + 42` (`z4c_fires`: adjacent degree-4 hubs with one twin
each at `n ≥ 30`). -/

open Classical in
private theorem deco_edge_moat_fires_hsliceU : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n)
  (Ku Kv : Finset (Fin n))
  (_ : G.Adj u v) (_ : Ku ⊆ G.neighborFinset u) (_ : #Ku = G.degree u - 3) (_ : v ∉ Ku),
  let _ := Classical.decEq (Fin n);
  ∀ (_ : 3 ≤ G.degree u) (_ : 3 ≤ G.degree v) (_ : u ≠ v) (S₁ : Finset (Fin n))
    (_ : S₁ = insert u (insert v (Ku ∪ Kv))), #(G.neighborFinset u \ S₁) ≤ 2 := by
  classical
  intro n G u v Ku Kv huv hKusub hKucard hvKu this hdeg3u hdeg3v huv' S₁ hS1def
  have hivku_nb : insert v Ku ⊆ G.neighborFinset u :=
    Finset.insert_subset ((G.mem_neighborFinset u v).mpr huv) hKusub
  have hivku_S1 : insert v Ku ⊆ S₁ := by
    refine Finset.insert_subset ?_ ?_
    · rw [hS1def]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self v _)
    · intro x hxKu
      rw [hS1def]
      exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_union_left Kv hxKu))
  have hsub : G.neighborFinset u \ S₁ ⊆ G.neighborFinset u \ insert v Ku :=
    Finset.sdiff_subset_sdiff (le_refl _) hivku_S1
  calc (G.neighborFinset u \ S₁).card
      ≤ (G.neighborFinset u \ insert v Ku).card := Finset.card_le_card hsub
    _ = (G.neighborFinset u).card - (insert v Ku).card :=
        Finset.card_sdiff_of_subset hivku_nb
    _ = G.degree u - (insert v Ku).card := by rw [G.card_neighborFinset_eq_degree]
    _ = 2 := by rw [Finset.card_insert_of_notMem hvKu, hKucard]; omega

open Classical in
private theorem deco_edge_moat_fires_hsliceV : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n)
  (Ku Kv : Finset (Fin n))
  (_ : G.Adj u v) (_ : Kv ⊆ G.neighborFinset v) (_ : #Kv = G.degree v - 3) (_ : u ∉ Kv),
  let _ := Classical.decEq (Fin n);
  ∀ (_ : 3 ≤ G.degree u) (_ : 3 ≤ G.degree v) (_ : u ≠ v) (S₁ : Finset (Fin n))
    (_ : S₁ = insert u (insert v (Ku ∪ Kv))), #(G.neighborFinset v \ S₁) ≤ 2 := by
  classical
  intro n G u v Ku Kv huv hKvsub hKvcard huKv this hdeg3u hdeg3v huv' S₁ hS1def
  have hiukv_nb : insert u Kv ⊆ G.neighborFinset v :=
    Finset.insert_subset ((G.mem_neighborFinset v u).mpr huv.symm) hKvsub
  have hiukv_S1 : insert u Kv ⊆ S₁ := by
    refine Finset.insert_subset ?_ ?_
    · rw [hS1def]; exact Finset.mem_insert_self u _
    · intro x hxKv
      rw [hS1def]
      exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_union_right Ku hxKv))
  have hsub : G.neighborFinset v \ S₁ ⊆ G.neighborFinset v \ insert u Kv :=
    Finset.sdiff_subset_sdiff (le_refl _) hiukv_S1
  calc (G.neighborFinset v \ S₁).card
      ≤ (G.neighborFinset v \ insert u Kv).card := Finset.card_le_card hsub
    _ = (G.neighborFinset v).card - (insert u Kv).card :=
        Finset.card_sdiff_of_subset hiukv_nb
    _ = G.degree v - (insert u Kv).card := by rw [G.card_neighborFinset_eq_degree]
    _ = 2 := by rw [Finset.card_insert_of_notMem huKv, hKvcard]; omega

open Classical in
private theorem deco_edge_moat_fires_hsliceTu : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n)
  (Ku Kv : Finset (Fin n))
  (_ : Ku ⊆ G.neighborFinset u) (_ : ∀ t ∈ Ku, G.degree t = 3),
  let _ := Classical.decEq (Fin n);
  ∀ (S₁ : Finset (Fin n)) (_ : S₁ = insert u (insert v (Ku ∪ Kv))), ∀ t ∈ Ku, #(G.neighborFinset t
    \ S₁) ≤ 2 := by
  classical
  intro n G u v Ku Kv hKusub hKudeg this S₁ hS1def t htK
  have htNu : t ∈ G.neighborFinset u := hKusub htK
  have hut : G.Adj u t := (G.mem_neighborFinset u t).mp htNu
  have huNt : u ∈ G.neighborFinset t := (G.mem_neighborFinset t u).mpr hut.symm
  have hsub : G.neighborFinset t \ S₁ ⊆ (G.neighborFinset t).erase u := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    rw [Finset.mem_erase]
    refine ⟨fun hxu => hx.2 ?_, hx.1⟩
    rw [hS1def, hxu]
    exact Finset.mem_insert_self u _
  calc (G.neighborFinset t \ S₁).card
      ≤ ((G.neighborFinset t).erase u).card := Finset.card_le_card hsub
    _ = G.degree t - 1 := by
        rw [Finset.card_erase_of_mem huNt, G.card_neighborFinset_eq_degree]
    _ = 2 := by rw [hKudeg t htK]

open Classical in
private theorem deco_edge_moat_fires_hsliceTv : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n)
  (Ku Kv : Finset (Fin n))
  (_ : Kv ⊆ G.neighborFinset v) (_ : ∀ t ∈ Kv, G.degree t = 3),
  let _ := Classical.decEq (Fin n);
  ∀ (S₁ : Finset (Fin n)) (_ : S₁ = insert u (insert v (Ku ∪ Kv))), ∀ t ∈ Kv, #(G.neighborFinset t
    \ S₁) ≤ 2 := by
  classical
  intro n G u v Ku Kv hKvsub hKvdeg this S₁ hS1def t htK
  have htNv : t ∈ G.neighborFinset v := hKvsub htK
  have hvt : G.Adj v t := (G.mem_neighborFinset v t).mp htNv
  have hvNt : v ∈ G.neighborFinset t := (G.mem_neighborFinset t v).mpr hvt.symm
  have hsub : G.neighborFinset t \ S₁ ⊆ (G.neighborFinset t).erase v := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    rw [Finset.mem_erase]
    refine ⟨fun hxv => hx.2 ?_, hx.1⟩
    rw [hS1def, hxv]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self v _)
  calc (G.neighborFinset t \ S₁).card
      ≤ ((G.neighborFinset t).erase v).card := Finset.card_le_card hsub
    _ = G.degree t - 1 := by
        rw [Finset.card_erase_of_mem hvNt, G.card_neighborFinset_eq_degree]
    _ = 2 := by rw [hKvdeg t htK]

open Classical in
private theorem deco_edge_moat_fires_he2 : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (_ : ∀ (w : Fin n),
  3 ≤ G.degree w)
  (u v : Fin n) (Ku Kv : Finset (Fin n)) (_ : #Ku = G.degree u - 3) (_ : #Kv = G.degree v - 3)
  (_ : 9 * (G.degree u + G.degree v) ≤ n + 42),
  let _ := Classical.decEq (Fin n);
  ∀ (_ : 3 ≤ G.degree u) (_ : 3 ≤ G.degree v) (_ : 8 ≤ n) (_ : u ≠ v),
    let S₁ := insert u (insert v (Ku ∪ Kv));
    ∀ (F : Finset (Fin n)) (_ : F = (S₁.biUnion fun x => G.neighborFinset x) \ S₁),
      let S₂ := (S₁ ∪ F)ᶜ;
      ∀ (_ : S₂ = (S₁ ∪ F)ᶜ) (_ : #S₁ = G.degree u + G.degree v - 4) (_ : #S₂ = n - (#S₁ + #F))
        (_ : ∀ (A C : Finset (Fin n)), #({q ∈ A ×ˢ C | G.Adj q.1 q.2}) = ∑ a ∈ A,
          #(G.neighborFinset a ∩ C))
        (_ : ∀ (A C : Finset (Fin n)), #({q ∈ A ×ˢ C | G.Adj q.1 q.2}) = #({q ∈ C ×ˢ A | G.Adj q.1
          q.2}))
        (_ : #F ≤ 2 * #S₁) (_ : ∑ w ∈ F, (G.degree w - 3) ≤ n - 8 - (G.degree u - 3) - (G.degree v
          - 3)),
        #({q ∈ S₂ ×ˢ F | G.Adj q.1 q.2}) ≤ 2 * #S₂ := by
  classical
  intro n G h3 u v Ku Kv hKucard hKvcard hfire this hdeg3u hdeg3v hn8 huv' S₁ F hFdef S₂ hS2def
    hS1card hS2card hcnt htrans hFcard hexc
  rw [htrans S₂ F, hcnt F S₂]
  have hbound : ∀ w ∈ F, (G.neighborFinset w ∩ S₂).card ≤ G.degree w - 1 := by
    intro w hw
    obtain ⟨a, haS1, haw⟩ : ∃ a ∈ S₁, G.Adj a w := by
      have hwF := hw
      rw [hFdef, Finset.mem_sdiff, Finset.mem_biUnion] at hwF
      obtain ⟨⟨a, haS1, hwa⟩, _⟩ := hwF
      exact ⟨a, haS1, (G.mem_neighborFinset a w).mp hwa⟩
    have haNw : a ∈ G.neighborFinset w := (G.mem_neighborFinset w a).mpr haw.symm
    have haS2 : a ∉ S₂ := by
      rw [hS2def, Finset.mem_compl, not_not]
      exact Finset.mem_union_left F haS1
    have hsub : G.neighborFinset w ∩ S₂ ⊆ (G.neighborFinset w).erase a := by
      intro x hx
      rw [Finset.mem_inter] at hx
      rw [Finset.mem_erase]
      refine ⟨?_, hx.1⟩
      rintro rfl
      exact haS2 hx.2
    calc (G.neighborFinset w ∩ S₂).card
        ≤ ((G.neighborFinset w).erase a).card := Finset.card_le_card hsub
      _ = G.degree w - 1 := by
          rw [Finset.card_erase_of_mem haNw, G.card_neighborFinset_eq_degree]
  have hpt : ∀ w ∈ F, G.degree w - 1 = (G.degree w - 3) + 2 := by
    intro w _
    have := h3 w
    omega
  calc ∑ w ∈ F, (G.neighborFinset w ∩ S₂).card
      ≤ ∑ w ∈ F, (G.degree w - 1) := Finset.sum_le_sum hbound
    _ = ∑ w ∈ F, (G.degree w - 3) + F.card * 2 := by
        rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_const,
          smul_eq_mul]
    _ ≤ 2 * S₂.card := by omega

open Classical in
/-- **W3 — the decorated-edge moat certificate.**  A graph on `Fin n` with `2(n−2)` edges,
minimum degree `≥ 3`, adjacent hubs `u, v`, and twin sets `Ku ⊆ N(u)`, `Kv ⊆ N(v)` of degree-`3`
vertices with `|Ku| = deg u − 3`, `|Kv| = deg v − 3` (disjoint, and avoiding the opposite hub)
has `algConn G ≤ 2` whenever `9·(deg u + deg v) ≤ n + 42`.

Instantiate the two-cluster law with the tie-block `S₁ = {u, v} ∪ Ku ∪ Kv` against the bulk
`S₂ = (S₁ ∪ F)ᶜ`, `F = (⋃_{x ∈ S₁} N(x)) ∖ S₁` the moat: each slice `N(x) ∖ S₁` has `≤ 2`
elements (each hub loses the other hub and its twins; each twin loses its hub), so `∂₁ ≤ 2|S₁|`
and `|F| ≤ 2|S₁|`, and the pair-credited excess ledger gives `∂₂ ≤ 2|S₂|`; the Fiedler cut
condition closes by `ring`. -/
theorem deco_edge_moat_fires {n : ℕ} [Nonempty (Fin n)]
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ w : Fin n, 3 ≤ G.degree w) (u v : Fin n) (Ku Kv : Finset (Fin n))
    (huv : G.Adj u v)
    (hKusub : Ku ⊆ G.neighborFinset u) (hKudeg : ∀ t ∈ Ku, G.degree t = 3)
    (hKucard : Ku.card = G.degree u - 3)
    (hKvsub : Kv ⊆ G.neighborFinset v) (hKvdeg : ∀ t ∈ Kv, G.degree t = 3)
    (hKvcard : Kv.card = G.degree v - 3)
    (huKv : u ∉ Kv) (hvKu : v ∉ Ku) (hKuKv : Disjoint Ku Kv)
    (hfire : 9 * (G.degree u + G.degree v) ≤ n + 42) :
    algConn G ≤ 2 := by
  classical
  let : DecidableEq (Fin n) := Classical.decEq (Fin n)
  have hdeg3u : 3 ≤ G.degree u := h3 u
  have hdeg3v : 3 ≤ G.degree v := h3 v
  have hn8 : 8 ≤ n := by omega
  have huv' : u ≠ v := G.ne_of_adj huv
  have huKu : u ∉ Ku := by
    intro hu
    have hmem := hKusub hu
    rw [G.mem_neighborFinset] at hmem
    exact (G.ne_of_adj hmem) rfl
  have hvKv : v ∉ Kv := by
    intro hv
    have hmem := hKvsub hv
    rw [G.mem_neighborFinset] at hmem
    exact (G.ne_of_adj hmem) rfl
  set S₁ : Finset (Fin n) := insert u (insert v (Ku ∪ Kv)) with hS1def
  set F : Finset (Fin n) := (S₁.biUnion (fun x => G.neighborFinset x)) \ S₁ with hFdef
  set S₂ : Finset (Fin n) := (S₁ ∪ F)ᶜ with hS2def
  have hu_notin : u ∉ insert v (Ku ∪ Kv) := by
    rw [Finset.mem_insert, Finset.mem_union]
    rintro (h | h | h)
    · exact huv' h
    · exact huKu h
    · exact huKv h
  have hv_notin : v ∉ Ku ∪ Kv := by
    rw [Finset.mem_union]
    rintro (h | h)
    · exact hvKu h
    · exact hvKv h
  have hS1card : S₁.card = G.degree u + G.degree v - 4 := by
    rw [hS1def, Finset.card_insert_of_notMem hu_notin,
      Finset.card_insert_of_notMem hv_notin, Finset.card_union_of_disjoint hKuKv,
      hKucard, hKvcard]
    omega
  have hS1ne : S₁.Nonempty := by rw [hS1def]; exact Finset.insert_nonempty u _
  have huF : u ∉ F := by
    rw [hFdef]
    intro hmem
    rw [Finset.mem_sdiff] at hmem
    exact hmem.2 (by rw [hS1def]; exact Finset.mem_insert_self u _)
  have hvF : v ∉ F := by
    rw [hFdef]
    intro hmem
    rw [Finset.mem_sdiff] at hmem
    exact hmem.2 (by rw [hS1def]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self v _))
  have hdisjS1F : Disjoint S₁ F := by
    rw [Finset.disjoint_left]
    intro a ha haF
    rw [hFdef, Finset.mem_sdiff] at haF
    exact haF.2 ha
  have hS2card : S₂.card = n - (S₁.card + F.card) := by
    rw [hS2def, Finset.card_compl, Fintype.card_fin,
      Finset.card_union_of_disjoint hdisjS1F]
  -- the counting helper: an ordered adjacency block splits into neighbourhood slices
  have hcnt : ∀ (A C : Finset (Fin n)),
      ((A ×ˢ C).filter (fun q => G.Adj q.1 q.2)).card
        = ∑ a ∈ A, (G.neighborFinset a ∩ C).card := by
    intro A C
    rw [Finset.card_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hset : G.neighborFinset a ∩ C = C.filter (fun v => G.Adj a v) := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact and_comm
    rw [hset, Finset.card_filter]
  -- the transpose helper (adjacency is symmetric)
  have htrans : ∀ (A C : Finset (Fin n)),
      ((A ×ˢ C).filter (fun q => G.Adj q.1 q.2)).card
        = ((C ×ˢ A).filter (fun q => G.Adj q.1 q.2)).card := by
    intro A C
    refine Finset.card_bij (fun q _ => (q.2, q.1)) ?_ ?_ ?_
    · intro q hq
      rw [Finset.mem_filter, Finset.mem_product] at hq ⊢
      exact ⟨⟨hq.1.2, hq.1.1⟩, G.adj_symm hq.2⟩
    · intro q _ r _ hqr
      exact Prod.ext (congrArg Prod.snd hqr) (congrArg Prod.fst hqr)
    · intro q hq
      refine ⟨(q.2, q.1), ?_, rfl⟩
      rw [Finset.mem_filter, Finset.mem_product] at hq ⊢
      exact ⟨⟨hq.1.2, hq.1.1⟩, G.adj_symm hq.2⟩
  -- every slice `N(x) ∖ S₁` has at most two elements (external-degree budget 2)
  have hsliceU :=
      deco_edge_moat_fires_hsliceU (n := n) (G := G) (u := u) (v := v) (Ku := Ku) (Kv := Kv)
        (huv) (hKusub) (hKucard) (hvKu) (hdeg3u)
        (hdeg3v) (huv') (S₁ := S₁) (hS1def)
  have hsliceV :=
      deco_edge_moat_fires_hsliceV (n := n) (G := G) (u := u) (v := v) (Ku := Ku) (Kv := Kv)
        (huv) (hKvsub) (hKvcard) (huKv) (hdeg3u)
        (hdeg3v) (huv') (S₁ := S₁) (hS1def)
  have hsliceTu :=
      deco_edge_moat_fires_hsliceTu (n := n) (G := G) (u := u) (v := v) (Ku := Ku) (Kv := Kv)
        (hKusub) (hKudeg) (S₁ := S₁) (hS1def)
  have hsliceTv :=
      deco_edge_moat_fires_hsliceTv (n := n) (G := G) (u := u) (v := v) (Ku := Ku) (Kv := Kv)
        (hKvsub) (hKvdeg) (S₁ := S₁) (hS1def)
  have hslice : ∀ x ∈ S₁, (G.neighborFinset x \ S₁).card ≤ 2 := by
    intro x hx
    rw [hS1def, Finset.mem_insert, Finset.mem_insert, Finset.mem_union] at hx
    rcases hx with rfl | rfl | hxKu | hxKv
    · exact hsliceU
    · exact hsliceV
    · exact hsliceTu x hxKu
    · exact hsliceTv x hxKv
  -- ∂₁ ≤ 2·|S₁|
  have hterm : ∀ a ∈ S₁, (G.neighborFinset a ∩ F).card ≤ 2 := by
    intro a ha
    have hsub : G.neighborFinset a ∩ F ⊆ G.neighborFinset a \ S₁ := by
      intro x hx
      rw [Finset.mem_inter] at hx
      rw [Finset.mem_sdiff]
      refine ⟨hx.1, ?_⟩
      have hxF := hx.2
      rw [hFdef, Finset.mem_sdiff] at hxF
      exact hxF.2
    exact le_trans (Finset.card_le_card hsub) (hslice a ha)
  have he1 : ((S₁ ×ˢ F).filter (fun q => G.Adj q.1 q.2)).card ≤ 2 * S₁.card := by
    rw [hcnt S₁ F]
    calc ∑ a ∈ S₁, (G.neighborFinset a ∩ F).card
        ≤ ∑ _a ∈ S₁, 2 := Finset.sum_le_sum hterm
      _ = 2 * S₁.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  -- |F| ≤ 2·|S₁|
  have hFcard : F.card ≤ 2 * S₁.card := by
    have hFsub2 : F ⊆ S₁.biUnion (fun x => G.neighborFinset x \ S₁) := by
      intro y hy
      rw [hFdef, Finset.mem_sdiff] at hy
      obtain ⟨hyNS, hyS1⟩ := hy
      rw [Finset.mem_biUnion] at hyNS ⊢
      obtain ⟨x, hxS1, hyx⟩ := hyNS
      exact ⟨x, hxS1, Finset.mem_sdiff.mpr ⟨hyx, hyS1⟩⟩
    calc F.card
        ≤ (S₁.biUnion (fun x => G.neighborFinset x \ S₁)).card := Finset.card_le_card hFsub2
      _ ≤ ∑ x ∈ S₁, (G.neighborFinset x \ S₁).card := Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ S₁, 2 := Finset.sum_le_sum hslice
      _ = 2 * S₁.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  -- the pair-credited excess ledger: Σ_F (deg − 3) ≤ (n − 8) − (deg u − 3) − (deg v − 3)
  have hFsubErase : F ⊆ (Finset.univ.erase u).erase v := by
    intro x hx
    rw [Finset.mem_erase, Finset.mem_erase]
    refine ⟨?_, ?_, Finset.mem_univ x⟩
    · rintro rfl; exact hvF hx
    · rintro rfl; exact huF hx
  have hexc : ∑ w ∈ F, (G.degree w - 3)
      ≤ (n - 8) - (G.degree u - 3) - (G.degree v - 3) := by
    have hle : ∑ w ∈ F, (G.degree w - 3)
        ≤ ∑ w ∈ (Finset.univ.erase u).erase v, (G.degree w - 3) :=
      Finset.sum_le_sum_of_subset hFsubErase
    have hsplit1 : (G.degree u - 3) + ∑ w ∈ Finset.univ.erase u, (G.degree w - 3)
        = ∑ w : Fin n, (G.degree w - 3) :=
      Finset.add_sum_erase _ (fun w => G.degree w - 3) (Finset.mem_univ u)
    have hsplit2 : (G.degree v - 3) + ∑ w ∈ (Finset.univ.erase u).erase v, (G.degree w - 3)
        = ∑ w ∈ Finset.univ.erase u, (G.degree w - 3) :=
      Finset.add_sum_erase _ (fun w => G.degree w - 3)
        (Finset.mem_erase.mpr ⟨huv'.symm, Finset.mem_univ v⟩)
    have htot : ∑ w : Fin n, (G.degree w - 3) = n - 8 := total_excess_eq hn8 G hm h3
    omega
  have hS2ne : S₂.Nonempty := by
    rw [← Finset.card_pos, hS2card]; omega
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro a ha1 ha2
    rw [hS2def, Finset.mem_compl] at ha2
    exact ha2 (Finset.mem_union_left F ha1)
  have hnc : ∀ a ∈ S₁, ∀ w ∈ S₂, ¬G.Adj a w := by
    intro a ha w hw hadj
    rw [hS2def, Finset.mem_compl] at hw
    have hwnotS1 : w ∉ S₁ := fun hh => hw (Finset.mem_union_left F hh)
    have hwnotF : w ∉ F := fun hh => hw (Finset.mem_union_right S₁ hh)
    apply hwnotF
    rw [hFdef, Finset.mem_sdiff]
    refine ⟨?_, hwnotS1⟩
    rw [Finset.mem_biUnion]
    exact ⟨a, ha, (G.mem_neighborFinset a w).mpr hadj⟩
  have hFeq : (S₁ ∪ S₂)ᶜ = F := by
    ext w
    constructor
    · intro hw
      rw [Finset.mem_compl, Finset.mem_union, not_or] at hw
      obtain ⟨hwS1, hwS2⟩ := hw
      rw [hS2def, Finset.mem_compl, not_not, Finset.mem_union] at hwS2
      rcases hwS2 with hh | hh
      · exact absurd hh hwS1
      · exact hh
    · intro hw
      rw [Finset.mem_compl, Finset.mem_union, not_or]
      exact ⟨Finset.disjoint_right.mp hdisjS1F hw,
        by rw [hS2def, Finset.mem_compl, not_not]; exact Finset.mem_union_right S₁ hw⟩
  -- ∂₂ ≤ 2·|S₂|
  have he2 :=
      deco_edge_moat_fires_he2 (n := n) (G := G) (h3) (u := u) (v := v) (Ku := Ku) (Kv
        := Kv) (hKucard) (hKvcard) (hfire) (hdeg3u) (hdeg3v) (hn8) (huv') (F := F) (hFdef)
          (hS2def) (hS1card) (hS2card) (hcnt) (htrans) (hFcard) (hexc)
  -- assemble the two-cluster law at the tie
  refine algConn_le_two_of_two_clusters G S₁ S₂ hS1ne hS2ne hdisj hnc ?_
  rw [hFeq]
  have hbound1 := Nat.mul_le_mul he1 (le_refl (S₂.card ^ 2))
  have hbound2 := Nat.mul_le_mul he2 (le_refl (S₁.card ^ 2))
  refine le_trans (add_le_add hbound1 hbound2) (le_of_eq ?_)
  ring

open Classical in
/-- **Z4c — the adjacent degree-`4` decorated edge.**  Adjacent degree-`4` hubs `u, v`, each with
a degree-`3` neighbour (`tu` of `u`, `tv` of `v`, distinct and off the hubs), fire at every
`n ≥ 30` (`9·(4 + 4) = 72 ≤ n + 42 ⟺ n ≥ 30`).  The twins may be adjacent to each other. -/
theorem z4c_fires {n : ℕ} [Nonempty (Fin n)] (hn : 30 ≤ n)
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ w : Fin n, 3 ≤ G.degree w) (u v tu tv : Fin n)
    (huv : G.Adj u v) (hdu : G.degree u = 4) (hdv : G.degree v = 4)
    (hutu : G.Adj u tu) (hvtv : G.Adj v tv)
    (hdtu : G.degree tu = 3) (hdtv : G.degree tv = 3)
    (htuv : tu ≠ tv) (hutv : u ≠ tv) (hvtu : v ≠ tu) :
    algConn G ≤ 2 := by
  refine deco_edge_moat_fires G hm h3 u v {tu} {tv} huv ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    rw [G.mem_neighborFinset]; exact hutu
  · intro t ht
    rw [Finset.mem_singleton] at ht
    subst ht; exact hdtu
  · rw [Finset.card_singleton, hdu]
  · intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    rw [G.mem_neighborFinset]; exact hvtv
  · intro t ht
    rw [Finset.mem_singleton] at ht
    subst ht; exact hdtv
  · rw [Finset.card_singleton, hdv]
  · rw [Finset.mem_singleton]; exact hutv
  · rw [Finset.mem_singleton]; exact hvtu
  · rw [Finset.disjoint_singleton]; exact htuv
  · rw [hdu, hdv]; omega

end ACMax
