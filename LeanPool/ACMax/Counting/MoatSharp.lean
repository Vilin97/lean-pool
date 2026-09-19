/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
import LeanPool.ACMax.Counting.CompactCell
import LeanPool.ACMax.Counting.Moats

/-!
# The bulk-credited master-cycle moat (`master_cycle_fires_sharp`)

`master_cycle_fires` (`Counting/Moats.lean`) bounds the outer boundary `∂₂ ≤ Σ_F(deg − 1)` and
then caps `Σ_F(deg − 3)` by the *whole* excess budget `n − 8`, via `F ∪ S₁ ⊆ univ`.  That step
throws away `Σ_{S₂}(deg − 3)`, the excess sitting in the **bulk** — which, on the starved census,
is the bulk of the excess: only `n₃ = X + 8` vertices have degree `3`, so every one of the other
`|S₂| − n₃` bulk vertices spends at least `1`.

Keeping that term turns the ledger into an identity over the partition `S₁ ⊔ F ⊔ S₂ = univ` and
replaces the firing threshold

  `3·Σ_{S₁}(deg − 1) ≤ n + 8`     (i.e. `9k ≤ n + 8` on a degree-`≤ 4` cycle)

by the strictly weaker

  `4·Σ_{S₁} deg + n₃ ≤ 2n + 8 + 4k`   (i.e. `12k + n₃ ≤ 2n + 8`, i.e. `12k + X ≤ 2n`).

Since the hoarding law gives `3X + 26 ≤ n`, the new threshold dominates the old at *every* cell:
the forbidden cycle length rises from `(n+8)/9` to `(2n − X)/12`, a factor `1.2`–`1.5`.

Everything else — the slice bound, the moat cap `|F| ≤ Σ_{S₁}(deg − 2)`, the two-cluster tie — is
verbatim `master_cycle_fires`; only the ledger and the threshold change.
-/

namespace ACMax

open Finset

open Classical in
private theorem master_cycle_fires_sharp_hsliceIdx : ∀ {n k : ℕ} [NeZero k] (G :
  SimpleGraph (Fin n))
  (c : ZMod k → Fin n) (_ : Function.Injective c) (_ : ∀ (i : ZMod k), G.Adj (c i) (c (i +
    1))),
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
private theorem master_cycle_fires_sharp_hE2 : ∀ {n k n₃ : ℕ} [NeZero k] (G : SimpleGraph
  (Fin n))
  (_ : ∀ (v : Fin n), 3 ≤ G.degree v) (c : ZMod k → Fin n) (_ : #(Finset.univ.filter fun v =>
    G.degree v = 3) ≤ n₃),
  let _ := Classical.decEq (Fin n);
  let S₁ := image c univ;
  let F := (S₁.biUnion fun x => G.neighborFinset x) \ S₁;
  let S₂ := (S₁ ∪ F)ᶜ;
  ∀ (_ : #S₂ = n - (#S₁ + #F)), #S₂ ≤ ∑ v ∈ S₂, (G.degree v - 3) + n₃ := by
  classical
  intro n k n₃ inst G h3 c hn3 this S₁ F S₂ hS2card
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := S₂) (p := fun v => G.degree v = 3)
  have hle : (S₂.filter (fun v => G.degree v = 3)).card ≤ n₃ := by
    refine le_trans (Finset.card_le_card ?_) hn3
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact hv.2
  have hge : (S₂.filter (fun v => ¬ G.degree v = 3)).card
      ≤ ∑ v ∈ S₂, (G.degree v - 3) := by
    calc (S₂.filter (fun v => ¬ G.degree v = 3)).card
        = ∑ _v ∈ S₂.filter (fun v => ¬ G.degree v = 3), 1 := by
          rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ ∑ v ∈ S₂.filter (fun v => ¬ G.degree v = 3), (G.degree v - 3) := by
          refine Finset.sum_le_sum fun v hv => ?_
          rw [Finset.mem_filter] at hv
          have := h3 v
          omega
      _ ≤ ∑ v ∈ S₂, (G.degree v - 3) :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  omega

open Classical in
private theorem master_cycle_fires_sharp_he1 : ∀ {n k : ℕ} [NeZero k] (G : SimpleGraph
  (Fin n)) (c : ZMod k → Fin n),
  let _ := Classical.decEq (Fin n);
  let S₁ := image c univ;
  ∀ (F : Finset (Fin n)) (_ : F = (S₁.biUnion fun x => G.neighborFinset x) \ S₁),
    let S₂ := (S₁ ∪ F)ᶜ;
    let D := ∑ i, G.degree (c i);
    ∀ (_ : D ≤ 4 * k) (_ : #S₁ = k) (_ : ∑ x ∈ S₁, G.degree x = D)
      (_ : ∀ x ∈ S₁, #(G.neighborFinset x \ S₁) ≤ G.degree x - 2)
      (_ : ∀ (A C : Finset (Fin n)), #({q ∈ A ×ˢ C | G.Adj q.1 q.2}) = ∑ a ∈ A,
        #(G.neighborFinset a ∩ C))
      (_ : ∑ x ∈ S₁, (G.degree x - 2) + 2 * #S₁ = D) (_ : ∑ x ∈ S₁, (G.degree x - 3) + 3 *
        #S₁ = D)
      (_ : ∑ i, (G.degree (c i) - 1) + k = D)
      (_ : ∑ w ∈ F, (G.degree w - 3) + ∑ x ∈ S₁, (G.degree x - 3) + ∑ v ∈ S₂, (G.degree v - 3)
        = n - 8),
      #({q ∈ S₁ ×ˢ F | G.Adj q.1 q.2}) ≤ 2 * #S₁ := by
  classical
  intro n k inst G c this S₁ F hFdef S₂ D hsum hS1card hDS1 hslice hcnt keyB keyX keyP hexc3
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
private theorem master_cycle_fires_sharp_he2 : ∀ {n k n₃ : ℕ} [NeZero k] (G : SimpleGraph
  (Fin n))
  (_ : ∀ (v : Fin n), 3 ≤ G.degree v) (c : ZMod k → Fin n),
  let _ := Classical.decEq (Fin n);
  ∀ (_ : 8 ≤ n),
    let S₁ := image c univ;
    ∀ (F : Finset (Fin n)) (_ : F = (S₁.biUnion fun x => G.neighborFinset x) \ S₁),
      let S₂ := (S₁ ∪ F)ᶜ;
      ∀ (_ : S₂ = (S₁ ∪ F)ᶜ),
        let D := ∑ i, G.degree (c i);
        ∀ (_ : D ≤ 4 * k) (_ : 4 * D + n₃ ≤ 2 * n + 8 + 4 * k) (_ : #S₁ = k) (_ : ∑ x
          ∈ S₁, G.degree x = D)
          (_ : #S₂ = n - (#S₁ + #F)) (_ : #S₁ + #F ≤ n)
          (_ : ∀ (A C : Finset (Fin n)), #({q ∈ A ×ˢ C | G.Adj q.1 q.2}) = ∑ a ∈ A,
            #(G.neighborFinset a ∩ C))
          (_ : ∀ (A C : Finset (Fin n)), #({q ∈ A ×ˢ C | G.Adj q.1 q.2}) = #({q ∈ C ×ˢ A |
            G.Adj q.1 q.2}))
          (_ : ∑ x ∈ S₁, (G.degree x - 2) + 2 * #S₁ = D) (_ : ∑ x ∈ S₁, (G.degree x - 3) + 3
            * #S₁ = D)
          (_ : ∑ i, (G.degree (c i) - 1) + k = D) (_ : #F ≤ ∑ x ∈ S₁, (G.degree x - 2)) (_
            : #F + 2 * #S₁ ≤ D)
          (_ : ∑ w ∈ F, (G.degree w - 3) + ∑ x ∈ S₁, (G.degree x - 3) + ∑ v ∈ S₂, (G.degree v
            - 3) = n - 8)
          (_ : #S₂ ≤ ∑ v ∈ S₂, (G.degree v - 3) + n₃), #({q ∈ S₂ ×ˢ F | G.Adj q.1 q.2}) ≤ 2 *
            #S₂ := by
  classical
  intro n k n₃ inst G h3 c this hn8 S₁ F hFdef S₂ hS2def D hsum hn hS1card hDS1 hS2card hkfn hcnt
    htrans keyB keyX keyP hFB keyF hexc3 hE2
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
        have := hexc3; have := hE2; have := keyX; have := hsum; have := hn
        have := keyF; have := hS2card; have := hkfn; have := hS1card
        omega

open Classical in
theorem master_cycle_fires_sharp {n : ℕ} [Nonempty (Fin n)] {k n₃ : ℕ} [NeZero k]
    (hk : 3 ≤ k)
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) (c : ZMod k → Fin n) (hcinj : Function.Injective c)
    (hadj : ∀ i : ZMod k, G.Adj (c i) (c (i + 1)))
    (hsum : ∑ i : ZMod k, G.degree (c i) ≤ 4 * k)
    (hn3 : (Finset.univ.filter (fun v : Fin n => G.degree v = 3)).card ≤ n₃)
    (hn : 4 * (∑ i : ZMod k, G.degree (c i)) + n₃ ≤ 2 * n + 8 + 4 * k) :
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
      master_cycle_fires_sharp_hsliceIdx (n := n) (k := k) (G := G) (c := c) (hcinj) (hadj)
        (h2ne)
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
  -- the **full** excess ledger: `S₁ ⊔ F ⊔ S₂ = univ`, so the bulk excess is kept, not discarded
  have hexc3 : (∑ w ∈ F, (G.degree w - 3)) + (∑ x ∈ S₁, (G.degree x - 3))
      + (∑ v ∈ S₂, (G.degree v - 3)) = n - 8 := by
    have hunion : (∑ w ∈ F, (G.degree w - 3)) + (∑ x ∈ S₁, (G.degree x - 3))
        = ∑ w ∈ (F ∪ S₁), (G.degree w - 3) := (Finset.sum_union hdisjS1F.symm).symm
    have hcompl : S₂ = (F ∪ S₁)ᶜ := by rw [hS2def, Finset.union_comm]
    rw [hunion, hcompl, Finset.sum_add_sum_compl]
    exact total_excess_eq hn8 G hm h3
  -- the bulk excess is at least `|S₂| − n₃`: every non-degree-`3` bulk vertex spends `≥ 1`
  have hE2 :=
      master_cycle_fires_sharp_hE2 (n := n) (k := k) (n₃ := n₃) (G := G) (h3) (c := c)
        (hn3) (hS2card)
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
  have he1 := master_cycle_fires_sharp_he1 (n := n) (k := k) (G := G) (c := c) (F := F)
      (hFdef) (hsum) (hS1card) (hDS1) (hslice) (hcnt) (keyB) (keyX) (keyP) (hexc3)
  -- ∂₂ ≤ 2·|S₂|
  have he2 :=
      master_cycle_fires_sharp_he2 (n := n) (k := k) (n₃ := n₃) (G := G) (h3) (c := c)
        (hn8) (F := F) (hFdef) (hS2def) (hsum) (hn) (hS1card) (hDS1) (hS2card) (hkfn) (hcnt)
          (htrans) (keyB) (keyX) (keyP) (hFB) (keyF) (hexc3) (hE2)
  -- assemble the two-cluster law at the tie
  refine algConn_le_two_of_two_clusters G S₁ S₂ hS1ne hS2ne hdisj hnc ?_
  rw [hFeq]
  have hbound1 := Nat.mul_le_mul he1 (le_refl (S₂.card ^ 2))
  have hbound2 := Nat.mul_le_mul he2 (le_refl (S₁.card ^ 2))
  refine le_trans (add_le_add hbound1 hbound2) (le_of_eq ?_)
  ring

open Classical in
/-- **The degree-`3` census identity** `n₃ = X + 8`.  From the excess ledger
`Σ_v (deg v − 3) = n − 8`: a degree-`3` vertex spends `0`, and every other vertex spends
`(deg − 4) + 1`, so `n − 8 = X + (n − n₃)`. -/
theorem n3_eq_excess_add_eight {n : ℕ} (hn : 8 ≤ n) (G : SimpleGraph (Fin n))
    (hm : G.edgeFinset.card = 2 * (n - 2)) (h3 : ∀ v : Fin n, 3 ≤ G.degree v) :
    (Finset.univ.filter (fun v : Fin n => G.degree v = 3)).card = excessX n G + 8 := by
  classical
  have htot := total_excess_eq hn G hm h3
  set A := Finset.univ.filter (fun v : Fin n => G.degree v = 3) with hA
  set B := Finset.univ.filter (fun v : Fin n => ¬ G.degree v = 3) with hB
  have hcard : A.card + B.card = n := by
    rw [hA, hB, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
  have hsplit : (∑ v ∈ A, (G.degree v - 3)) + (∑ v ∈ B, (G.degree v - 3)) = n - 8 := by
    rw [hA, hB, Finset.sum_filter_add_sum_filter_not]; exact htot
  have hA0 : (∑ v ∈ A, (G.degree v - 3)) = 0 := by
    refine Finset.sum_eq_zero fun v hv => ?_
    rw [hA, Finset.mem_filter] at hv
    omega
  have hBval : (∑ v ∈ B, (G.degree v - 3)) = (∑ v ∈ B, (G.degree v - 4)) + B.card := by
    have hpt : ∀ v ∈ B, G.degree v - 3 = (G.degree v - 4) + 1 := by
      intro v hv
      rw [hB, Finset.mem_filter] at hv
      have := h3 v
      omega
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
  have hexc : (∑ v ∈ B, (G.degree v - 4)) = excessX n G := by
    unfold excessX
    refine (Finset.sum_subset ?_ ?_).symm
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · intro v hv hv2
      simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv2
      have := h3 v
      omega
  omega

open Classical in
/-- **The sharpened tier-9 short-cycle kill.**  A cycle of degree-`≤ 4` vertices fires the
two-cluster moat whenever `12·k + X ≤ 2n` — against `9·k ≤ n + 8` for `v9_short_cycle_fires`.
Since the hoarding law gives `3X + 26 ≤ n`, the new threshold is strictly weaker at every cell:
the forbidden length rises from `(n+8)/9` to `(2n − X)/12`. -/
theorem v9_short_cycle_fires_sharp {n : ℕ} [Nonempty (Fin n)] {k : ℕ} [NeZero k] (hk : 3 ≤ k)
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) (c : ZMod k → Fin n)
    (hcinj : Function.Injective c) (hadj : ∀ i : ZMod k, G.Adj (c i) (c (i + 1)))
    (hdeg : ∀ i : ZMod k, G.degree (c i) ≤ 4) (hn8 : 8 ≤ n)
    (hn : 12 * k + excessX n G ≤ 2 * n) :
    algConn G ≤ 2 := by
  have hDle : ∑ i : ZMod k, G.degree (c i) ≤ 4 * k := by
    calc ∑ i : ZMod k, G.degree (c i)
        ≤ ∑ _i : ZMod k, 4 := Finset.sum_le_sum (fun i _ => hdeg i)
      _ = 4 * k := by
          rw [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul, mul_comm]
  refine master_cycle_fires_sharp (n₃ := excessX n G + 8) hk G hm h3 c hcinj hadj hDle
    (le_of_eq (n3_eq_excess_add_eight hn8 G hm h3)) ?_
  omega

end ACMax
