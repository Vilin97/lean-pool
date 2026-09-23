/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Tauto
public import LeanPool.ACMax.InternalEdgesEven
public import LeanPool.ACMax.Reduction.Residual

/-!
# Double-open-star certificates and the M-edge dispatch vocabulary

The signed-cut toolbox for two-hub configurations, together with the vocabulary
that classifies a residual graph by its `M`-edges (edges between degree-3
vertices). Two hubs `g ≠ h` and their degree-3 twins assemble a *double open
star*, whose signed cut bounds algebraic connectivity by `2` under an explicit
leak budget.

## Vocabulary

`deg3Set` (the degree-3 set `D`), `hubSet` (degree `≥ 4`), `hubTwins g`
(degree-3 neighbours of `g`), `privTwins g h` / `sharedTwins g h` (twins of `g`
private to it / shared with `h`), `intDeg g` (non-degree-3 neighbours of `g`),
`mCross g h`, `mIncidence` (the `D`–`D` incidence sum), and `isoTwins`
(degree-3 vertices with no degree-3 neighbour).

## Main results

* `W1Config`, `w1_cut_certificate`, `w1_algConn_le_two` — the **W1
  double-open-star certificate**: with `P = {g} ∪ privTwins g h` and
  `N = {h} ∪ privTwins h g ∪ F` (far pads `F` balancing the sizes), the leak
  budget `|F| + intDeg g + intDeg h + 2·sharedTwins + 2·[g ~ h] + 4·mCross ≤ 4`
  produces a `TwoBlockConfig`, hence `algConn G ≤ 2`.
* `eM_trichotomy` — `mIncidence G ∈ {0, 2} ∨ 4 ≤ mIncidence G`, the gate
  splitting the dispatch into the no-`M`-edge, single-`M`-edge and cherry cases.
* `SeaFatBoundary`, `w1Config_of_pair`, `dsValue` — the resource boundary where
  no hub pair yields a cheap W1 witness, and the firing bridge back into
  `W1Config`.
* `two_hub_opposite_twin_twoBlock`, `two_hub_private_pair_twoBlock`,
  `star3_leak_le_six` — raw six-vertex two-block certificates (over
  `[DecidableEq V]`) that tolerate shared twins and `M`-crosses beyond the W1
  master arithmetic, used in the rich-sea regime.
-/

@[expose] public section

namespace ACMax

variable {V : Type*} [Fintype V]

/-! ## The double-star vocabulary -/

open Classical in
/-- The degree-3 set `D`. -/
noncomputable def deg3Set (G : SimpleGraph V) : Finset V :=
  Finset.univ.filter (fun v => G.degree v = 3)

open Classical in
theorem mem_deg3Set {G : SimpleGraph V} {v : V} : v ∈ deg3Set G ↔ G.degree v = 3 := by
  unfold deg3Set
  simp

open Classical in
/-- The degree-3 twins of a hub: `D3(g) = N(g) ∩ D`. -/
noncomputable def hubTwins (G : SimpleGraph V) (g : V) : Finset V :=
  G.neighborFinset g ∩ deg3Set G

open Classical in
/-- The **private** twins of `g` against `h`: `D3(g) \ D3(h)` — the `P`-side block body
of the double open star. -/
noncomputable def privTwins (G : SimpleGraph V) (g h : V) : Finset V :=
  hubTwins G g \ hubTwins G h

open Classical in
/-- The **shared** twins `s(g,h) = D3(g) ∩ D3(h)`. -/
noncomputable def sharedTwins (G : SimpleGraph V) (g h : V) : Finset V :=
  hubTwins G g ∩ hubTwins G h

open Classical in
/-- The **internal degree** `i(g) = deg g − |D3(g)|` — the number of non-degree-3
neighbours (the design's `intdeg`). -/
noncomputable def intDeg (G : SimpleGraph V) (g : V) : ℕ :=
  (G.neighborFinset g \ deg3Set G).card

open Classical in
/-- The **`M`-cross count**: the number of edges between the two private sides (each such
edge is a `D`–`D` edge, i.e. an `M`-edge; in the residual world `e(M) ≤ 1` forces
`mCross ≤ 1`, so this count coincides with the design's `[M-cross]` indicator). -/
noncomputable def mCross (G : SimpleGraph V) (g h : V) : ℕ :=
  ∑ t ∈ privTwins G g h, (G.neighborFinset t ∩ privTwins G h g).card

open Classical in
/-- The adjacency indicator `[g ~ h]`. -/
noncomputable def adjInd (G : SimpleGraph V) (g h : V) : ℕ :=
  if G.Adj g h then 1 else 0

open Classical in
/-- The `D`–`D` incidence sum `∑_{v∈D} |N(v) ∩ D| = 2·e(M)`. -/
noncomputable def mIncidence (G : SimpleGraph V) : ℕ :=
  ∑ v ∈ deg3Set G, (G.neighborFinset v ∩ deg3Set G).card

/-! ### Vocabulary lemmas -/

open Classical in
theorem privTwins_spec {G : SimpleGraph V} {g h t : V} :
    t ∈ privTwins G g h ↔ G.Adj g t ∧ G.degree t = 3 ∧ ¬G.Adj h t := by
  unfold privTwins hubTwins deg3Set
  simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
    true_and, SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨⟨ha, h3⟩, hn⟩
    exact ⟨ha, h3, fun hah => hn ⟨hah, h3⟩⟩
  · rintro ⟨ha, h3, hnadj⟩
    exact ⟨⟨ha, h3⟩, fun hc => hnadj hc.1⟩

open Classical in
theorem sharedTwins_spec {G : SimpleGraph V} {g h t : V} :
    t ∈ sharedTwins G g h ↔ G.Adj g t ∧ G.Adj h t ∧ G.degree t = 3 := by
  unfold sharedTwins hubTwins deg3Set
  simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
    SimpleGraph.mem_neighborFinset]
  tauto

open Classical in
theorem sharedTwins_comm (G : SimpleGraph V) (g h : V) :
    sharedTwins G g h = sharedTwins G h g :=
  Finset.inter_comm _ _

open Classical in
/-- The two private sides are always disjoint. -/
theorem privTwins_disjoint (G : SimpleGraph V) (g h : V) :
    Disjoint (privTwins G g h) (privTwins G h g) := by
  rw [Finset.disjoint_left]
  intro t ht ht'
  exact (privTwins_spec.mp ht').2.2 (privTwins_spec.mp ht).1

open Classical in
/-- Twin/internal split of a hub's neighbourhood: `|D3(g)| + i(g) = deg g`. -/
theorem hubTwins_card_add_intDeg (G : SimpleGraph V) (g : V) :
    (hubTwins G g).card + intDeg G g = G.degree g := by
  have h := Finset.card_sdiff_add_card_inter (G.neighborFinset g) (deg3Set G)
  have hd := G.card_neighborFinset_eq_degree g
  unfold hubTwins intDeg
  omega

open Classical in
/-- Private/shared split of the twin set: `|priv(g,h)| + |s(g,h)| = |D3(g)|`. -/
theorem privTwins_card_add_shared (G : SimpleGraph V) (g h : V) :
    (privTwins G g h).card + (sharedTwins G g h).card = (hubTwins G g).card := by
  have h1 := Finset.card_sdiff_add_card_inter (hubTwins G g) (hubTwins G h)
  unfold privTwins sharedTwins
  omega

/-! ## Part 1 — the W1 certificate

The leak/cross bookkeeping of the double open star, block by block. -/

open Classical in
/-- **Centre leak bound.**  The centre `g` of `P = {g} ∪ priv(g,h)` leaks at most
`s(g,h) + i(g)`: its neighbourhood is `priv(g,h) ⊔ shared(g,h) ⊔ (N(g) \ D)`, and the
private part stays inside `P`. -/
theorem doubleStar_center_leak (G : SimpleGraph V) (g h : V) :
    (G.neighborFinset g \ insert g (privTwins G g h)).card
      ≤ (sharedTwins G g h).card + intDeg G g := by
  have hsub : G.neighborFinset g \ insert g (privTwins G g h)
      ⊆ sharedTwins G g h ∪ (G.neighborFinset g \ deg3Set G) := by
    intro w hw
    rw [Finset.mem_sdiff, Finset.mem_insert] at hw
    obtain ⟨hwN, hwP⟩ := hw
    have hadj : G.Adj g w := (G.mem_neighborFinset g w).mp hwN
    rw [Finset.mem_union]
    by_cases hw3 : G.degree w = 3
    · left
      by_cases hwh : G.Adj h w
      · exact sharedTwins_spec.mpr ⟨hadj, hwh, hw3⟩
      · exact absurd (Or.inr (privTwins_spec.mpr ⟨hadj, hw3, hwh⟩)) hwP
    · right
      rw [Finset.mem_sdiff]
      exact ⟨hwN, fun hmem => hw3 (mem_deg3Set.mp hmem)⟩
  calc (G.neighborFinset g \ insert g (privTwins G g h)).card
      ≤ (sharedTwins G g h ∪ (G.neighborFinset g \ deg3Set G)).card :=
        Finset.card_le_card hsub
    _ ≤ (sharedTwins G g h).card + intDeg G g := Finset.card_union_le _ _

open Classical in
/-- **Twin leak bound.**  Each private twin `t ∈ priv(g,h)` (degree `3`, one edge back to
`g ∈ P`) leaks at most `2` out of `P`. -/
theorem doubleStar_twin_leak (G : SimpleGraph V) (g h : V) {t : V}
    (ht : t ∈ privTwins G g h) :
    (G.neighborFinset t \ insert g (privTwins G g h)).card ≤ 2 := by
  obtain ⟨hadj, h3, -⟩ := privTwins_spec.mp ht
  have hg : g ∈ G.neighborFinset t := (G.mem_neighborFinset t g).mpr hadj.symm
  have hsub : G.neighborFinset t \ insert g (privTwins G g h)
      ⊆ (G.neighborFinset t).erase g := by
    intro w hw
    rw [Finset.mem_sdiff, Finset.mem_insert] at hw
    exact Finset.mem_erase.mpr ⟨fun e => hw.2 (Or.inl e), hw.1⟩
  have hcalc : (G.neighborFinset t \ insert g (privTwins G g h)).card
      ≤ G.degree t - 1 := by
    calc (G.neighborFinset t \ insert g (privTwins G g h)).card
        ≤ ((G.neighborFinset t).erase g).card := Finset.card_le_card hsub
      _ = G.degree t - 1 := by
          rw [Finset.card_erase_of_mem hg, G.card_neighborFinset_eq_degree]
  omega

open Classical in
/-- **`P`-side leak bound** (assembled): `leak(P) ≤ s(g,h) + i(g) + 2·|priv(g,h)|`. -/
theorem doubleStar_P_leak (G : SimpleGraph V) (g h : V) :
    ∑ p ∈ insert g (privTwins G g h),
        (G.neighborFinset p \ insert g (privTwins G g h)).card
      ≤ (sharedTwins G g h).card + intDeg G g + 2 * (privTwins G g h).card := by
  have hgP : g ∉ privTwins G g h := fun hg' => G.irrefl (privTwins_spec.mp hg').1
  rw [Finset.sum_insert hgP]
  have hcenter := doubleStar_center_leak G g h
  have hsum : ∑ t ∈ privTwins G g h,
      (G.neighborFinset t \ insert g (privTwins G g h)).card
      ≤ 2 * (privTwins G g h).card := by
    calc ∑ t ∈ privTwins G g h,
          (G.neighborFinset t \ insert g (privTwins G g h)).card
        ≤ ∑ _t ∈ privTwins G g h, 2 :=
          Finset.sum_le_sum fun t ht => doubleStar_twin_leak G g h ht
      _ = 2 * (privTwins G g h).card := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
  omega

open Classical in
/-- **`P`-side cross bound**: with far pads, the only cross-edges out of `P` into
`N = {h} ∪ priv(h,g) ∪ F` are the (possible) `g–h` edge and the `M`-edges between the
private sides: `e(P,N) ≤ [g ~ h] + mCross(g,h)`. -/
theorem doubleStar_P_cross (G : SimpleGraph V) (g h : V) (F : Finset V)
    (hfar : ∀ f ∈ F, ∀ w ∈ insert g (privTwins G g h) ∪ insert h (privTwins G h g),
      ¬G.Adj f w) :
    ∑ p ∈ insert g (privTwins G g h),
        (G.neighborFinset p ∩ (insert h (privTwins G h g) ∪ F)).card
      ≤ adjInd G g h + mCross G g h := by
  have hgP : g ∉ privTwins G g h := fun hg' => G.irrefl (privTwins_spec.mp hg').1
  rw [Finset.sum_insert hgP]
  -- the centre crosses only into `h`
  have hcg : (G.neighborFinset g ∩ (insert h (privTwins G h g) ∪ F)).card
      ≤ adjInd G g h := by
    have hsub : G.neighborFinset g ∩ (insert h (privTwins G h g) ∪ F)
        ⊆ {h} := by
      intro w hw
      rw [Finset.mem_inter, Finset.mem_union, Finset.mem_insert] at hw
      obtain ⟨hwN, hw2⟩ := hw
      have hadj : G.Adj g w := (G.mem_neighborFinset g w).mp hwN
      rcases hw2 with (hwh | hwpriv) | hwF
      · rw [Finset.mem_singleton]; exact hwh
      · exact absurd hadj (privTwins_spec.mp hwpriv).2.2
      · exact absurd hadj.symm
          (hfar w hwF g (Finset.mem_union_left _ (Finset.mem_insert_self g _)))
    by_cases hadj : G.Adj g h
    · have h1 : (G.neighborFinset g ∩ (insert h (privTwins G h g) ∪ F)).card ≤ 1 := by
        calc (G.neighborFinset g ∩ (insert h (privTwins G h g) ∪ F)).card
            ≤ ({h} : Finset V).card := Finset.card_le_card hsub
          _ = 1 := Finset.card_singleton h
      unfold adjInd
      rw [ite_eq_left hadj]
      exact h1
    · have hempty : G.neighborFinset g ∩ (insert h (privTwins G h g) ∪ F) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro w hw
        have hwh := hsub hw
        rw [Finset.mem_singleton] at hwh
        subst hwh
        exact hadj ((G.mem_neighborFinset g w).mp (Finset.mem_inter.mp hw).1)
      rw [hempty, Finset.card_empty]
      omega
  -- each private twin crosses only into the opposite private side
  have hct : ∀ t ∈ privTwins G g h,
      (G.neighborFinset t ∩ (insert h (privTwins G h g) ∪ F)).card
        ≤ (G.neighborFinset t ∩ privTwins G h g).card := by
    intro t ht
    obtain ⟨-, -, hnht⟩ := privTwins_spec.mp ht
    apply Finset.card_le_card
    intro w hw
    rw [Finset.mem_inter] at hw ⊢
    obtain ⟨hwN, hw2⟩ := hw
    refine ⟨hwN, ?_⟩
    rw [Finset.mem_union, Finset.mem_insert] at hw2
    rcases hw2 with (hwh | hwpriv) | hwF
    · exfalso
      subst hwh
      exact hnht ((G.mem_neighborFinset t w).mp hwN).symm
    · exact hwpriv
    · exact absurd ((G.mem_neighborFinset t w).mp hwN).symm
        (hfar w hwF t (Finset.mem_union_left _ (Finset.mem_insert_of_mem ht)))
  have hsum : ∑ t ∈ privTwins G g h,
      (G.neighborFinset t ∩ (insert h (privTwins G h g) ∪ F)).card
      ≤ ∑ t ∈ privTwins G g h, (G.neighborFinset t ∩ privTwins G h g).card :=
    Finset.sum_le_sum hct
  have hmc : mCross G g h
      = ∑ t ∈ privTwins G g h, (G.neighborFinset t ∩ privTwins G h g).card := rfl
  omega

open Classical in
/-- **The W1 (DOUBLE-OPEN-STAR) configuration** — the design's `DS_pair` witness in its
exact validated form (`scratchpad/general_w1_check.py`: 74/74 saved escapers fire, all
assembled witnesses re-verified integer-exactly).  Data: hubs `g ≠ h` and a **far pad
set** `F` (degree-3 vertices with no edge into `P₀ ∪ N₀`) padding the `h`-side to equal
size, satisfying the **master arithmetic**

  `|F| + i(g) + i(h) + 2·s(g,h) + 2·[g ~ h] + 4·mCross(g,h) ≤ 4`

(`|F| = gap`; the `4·mCross` count form matches the design's `4·[M-cross]` indicator on
the whole `e(M) ≤ 1` residual world, and is one-sidedly *stronger* as a hypothesis when
`mCross ≥ 2`, so the certificate below is sound for it verbatim).  Instances: TwoHub is
the `(4,4,2,2,s=0)` **tie**; the clean TwoStar is `(d,d,0,0,s=0)` at slack `4`; blocking
a pair needs DS-value `≥ 5`.  The design's `(+2 M-pad)` refinement (using the `e(M) = 1`
edge pair as a 2-pad at cost `4` instead of `6`) is NOT formalized — the base `≤ 4` form
is the one validated on all 74 + 301 builds. -/
def W1Config (G : SimpleGraph V) : Prop :=
  ∃ g h : V, ∃ F : Finset V,
    4 ≤ G.degree g ∧ 4 ≤ G.degree h ∧ g ≠ h ∧
    (∀ f ∈ F, G.degree f = 3) ∧
    (∀ f ∈ F, ∀ w ∈ insert g (privTwins G g h) ∪ insert h (privTwins G h g),
      ¬G.Adj f w) ∧
    F.card + (privTwins G h g).card = (privTwins G g h).card ∧
    F.card + intDeg G g + intDeg G h + 2 * (sharedTwins G g h).card
      + 2 * adjInd G g h + 4 * mCross G g h ≤ 4

open Classical in
/-- **The W1 cut certificate** (Part 1, the main theorem): a double-open-star witness is a
two-block witness.  `P = {g} ∪ priv(g,h)`, `N = {h} ∪ priv(h,g) ∪ F`;

  `2·e(P,N) + leak(P) + leak(N)`
  `  ≤ 2([g~h] + mCross) + (s + i(g) + 2·p_g) + (s + i(h) + 2·p_h + 3·|F|)`
  `  = 4·p_g + (|F| + i(g) + i(h) + 2s + 2[g~h] + 2·mCross) ≤ 4·p_g + 4 = 4|P|`

using `p_h + |F| = p_g` — exactly the master arithmetic (with the crossing `M`-edges'
true cost `2·mCross ≤ 4·mCross`). -/
theorem w1_cut_certificate (G : SimpleGraph V) (hcfg : W1Config G) :
    TwoBlockConfig G := by
  obtain ⟨g, h, F, hg4, hh4, hne, hF3, hfar, hcard, hineq⟩ := hcfg
  have hgP : g ∉ privTwins G g h := fun hg' => G.irrefl (privTwins_spec.mp hg').1
  have hhP : h ∉ privTwins G h g := fun hh' => G.irrefl (privTwins_spec.mp hh').1
  -- the pad set is disjoint from the `h`-side core
  have hdN0F : Disjoint (insert h (privTwins G h g)) F := by
    rw [Finset.disjoint_left]
    intro x hx hxF
    have hx3 := hF3 x hxF
    rw [Finset.mem_insert] at hx
    rcases hx with hxh | hxPh
    · subst hxh; omega
    · exact hfar x hxF h (Finset.mem_union_right _ (Finset.mem_insert_self h _))
        ((privTwins_spec.mp hxPh).1).symm
  -- the blocks are disjoint
  have hdPN : Disjoint (insert g (privTwins G g h)) (insert h (privTwins G h g) ∪ F) := by
    rw [Finset.disjoint_left]
    intro x hxP hxN
    rw [Finset.mem_insert] at hxP
    rw [Finset.mem_union, Finset.mem_insert] at hxN
    rcases hxP with hxg | hxPg
    · subst hxg
      rcases hxN with (hxh | hxPh) | hxF
      · exact hne hxh
      · have := (privTwins_spec.mp hxPh).2.1
        omega
      · have := hF3 _ hxF
        omega
    · rcases hxN with (hxh | hxPh) | hxF
      · have h3 := (privTwins_spec.mp hxPg).2.1
        rw [hxh] at h3
        omega
      · exact Finset.disjoint_left.mp (privTwins_disjoint G g h) hxPg hxPh
      · exact hfar x hxF g (Finset.mem_union_left _ (Finset.mem_insert_self g _))
          ((privTwins_spec.mp hxPg).1).symm
  refine ⟨insert g (privTwins G g h), insert h (privTwins G h g) ∪ F, hdPN, ?_, ?_, ?_⟩
  · -- equal cards: `p_g + 1 = (p_h + 1) + |F|`
    rw [Finset.card_insert_of_notMem hgP, Finset.card_union_of_disjoint hdN0F,
      Finset.card_insert_of_notMem hhP]
    omega
  · rw [Finset.card_insert_of_notMem hgP]
    omega
  · -- the two-block inequality
    have hcross := doubleStar_P_cross G g h F hfar
    have hleakP := doubleStar_P_leak G g h
    have hleakN0 := doubleStar_P_leak G h g
    rw [sharedTwins_comm G h g] at hleakN0
    have hmono : ∑ q ∈ insert h (privTwins G h g),
        (G.neighborFinset q \ (insert h (privTwins G h g) ∪ F)).card
        ≤ ∑ q ∈ insert h (privTwins G h g),
            (G.neighborFinset q \ insert h (privTwins G h g)).card :=
      Finset.sum_le_sum fun q _ => Finset.card_le_card
        (Finset.sdiff_subset_sdiff (Finset.Subset.refl _) Finset.subset_union_left)
    have hpad : ∑ f ∈ F,
        (G.neighborFinset f \ (insert h (privTwins G h g) ∪ F)).card
        ≤ 3 * F.card := by
      calc ∑ f ∈ F, (G.neighborFinset f \ (insert h (privTwins G h g) ∪ F)).card
          ≤ ∑ f ∈ F, 3 := by
            refine Finset.sum_le_sum fun f hf => ?_
            calc (G.neighborFinset f \ (insert h (privTwins G h g) ∪ F)).card
                ≤ (G.neighborFinset f).card := Finset.card_le_card Finset.sdiff_subset
              _ = G.degree f := G.card_neighborFinset_eq_degree f
              _ = 3 := hF3 f hf
        _ = 3 * F.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    rw [Finset.card_insert_of_notMem hgP, Finset.sum_union hdN0F]
    omega

open Classical in
/-- The W1 configuration closes the graph: `algConn G ≤ 2`. -/
theorem w1_algConn_le_two [Nonempty V] (G : SimpleGraph V) (h : W1Config G) :
    algConn G ≤ 2 :=
  two_block_cut_certificate G (w1_cut_certificate G h)

/-! ### Subsumption: TwoHub and TwoStar are W1 instances -/

/-! ## The M-edge dispatch predicates

The case predicates of the glue tree, with the mechanical dispatch-direction
lemmas: the `mIncidence` trichotomy that isolates the cherry / single-`M`-edge /
no-`M`-edge worlds, and the `SeaFatBoundary` resource gate. -/

open Classical in
/-- **C0 — the cherry world**: `e(M) ≥ 2` (incidence form).  Routed to the per-`n`
cherry constructions (SingleVertex / TwoTwin / HubTriangle). -/
def CaseCherry (G : SimpleGraph V) : Prop := 4 ≤ mIncidence G

open Classical in
/-- **C5 — the `e(M) = 0` world.**  Closing counting: NEEDS-NEW-COUNTING (L5.7; the
MaxHub-style extremal counting survives only `n ≤ 20`). -/
def CaseMZero (G : SimpleGraph V) : Prop := mIncidence G = 0

open Classical in
/-- The `e(M)` **dispatch gate**: the `D`–`D` incidence sum is even (each `M`-edge is
counted from both ends), so every graph is `e(M) = 0`, `e(M) = 1` (`mIncidence = 2`), or
in the cherry world.  This is the C0/C5 split of the glue tree. -/
theorem eM_trichotomy (G : SimpleGraph V) :
    CaseMZero G ∨ mIncidence G = 2 ∨ CaseCherry G := by
  have hev : Even (mIncidence G) := sum_inDegree_even G (deg3Set G)
  obtain ⟨k, hk⟩ := hev
  unfold CaseMZero CaseCherry
  omega

open Classical in
/-- **The DS value of a hub pair** — the design's master-arithmetic left-hand side, with
the gap in `ℕ`-symmetric form `(p_g − p_h) + (p_h − p_g) = |p_g − p_h|`. -/
noncomputable def dsValue (G : SimpleGraph V) (g h : V) : ℕ :=
  ((privTwins G g h).card - (privTwins G h g).card)
    + ((privTwins G h g).card - (privTwins G g h).card)
    + intDeg G g + intDeg G h + 2 * (sharedTwins G g h).card
    + 2 * adjInd G g h + 4 * mCross G g h

open Classical in
/-- **C2 — the ¬W1-resource boundary predicate** (design §2a): every hub pair is
DS-blocked (`value ≥ 5`).  The output of the (open) C2 resource LP: `≤ 1` clean deg-4
hub, `O(√n)` unburied hubs, `e_H ≥ (3/2)(|Hub| − O(√n))` — NEEDS-C2-COUNTING. -/
def SeaFatBoundary (G : SimpleGraph V) : Prop :=
  ∀ g h : V, 4 ≤ G.degree g → 4 ≤ G.degree h → g ≠ h → 5 ≤ dsValue G g h

open Classical in
/-- **The firing bridge**: a hub pair of DS-value `≤ 4` with an exact far-pad supply *is*
a W1 configuration (the master inequality is the DS value with `gap = |F|`). -/
theorem w1Config_of_pair (G : SimpleGraph V) (g h : V) (F : Finset V)
    (hg4 : 4 ≤ G.degree g) (hh4 : 4 ≤ G.degree h) (hne : g ≠ h)
    (hF3 : ∀ f ∈ F, G.degree f = 3)
    (hfar : ∀ f ∈ F, ∀ w ∈ insert g (privTwins G g h) ∪ insert h (privTwins G h g),
      ¬G.Adj f w)
    (hcard : F.card + (privTwins G h g).card = (privTwins G g h).card)
    (hds : dsValue G g h ≤ 4) :
    W1Config G := by
  refine ⟨g, h, F, hg4, hh4, hne, hF3, hfar, hcard, ?_⟩
  unfold dsValue at hds
  omega

open Classical in
/-- The `M`-isolated degree-3 twins (`Iso`): degree-3 vertices with no degree-3
neighbour. -/
noncomputable def isoTwins (G : SimpleGraph V) : Finset V :=
  (deg3Set G).filter (fun t => ∀ w : V, G.Adj t w → G.degree w ≠ 3)

end ACMax

/-! ## Rich-sea two-block cut certificates

Raw six-vertex two-block certificates over `[DecidableEq V]`, used in the
rich-sea regime where shared twins and `M`-crosses block the clean W1 master
arithmetic. The `[DecidableEq V]` binder lets every `∩`/`∪` in the statements
instantiate to the ambient instance; `classical_inter_eq` / `classical_sdiff_eq`
bridge it to the `Classical` instance pinned inside `richHubs` / `mIncidence`
(`DecidableEq` is a subsingleton). Key certificates:
`two_hub_opposite_twin_twoBlock`, `two_hub_private_pair_twoBlock`, and the leak
bound `star3_leak_le_six`. -/

namespace ACMax

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The classical-instance bridges -/

open Classical in
/-- Bridge: `Finset.inter` under the `Classical` instance equals `∩` under the ambient
open Classical in
instance (`DecidableEq` is a subsingleton). -/
theorem classical_inter_eq {α : Type*} [inst : DecidableEq α] (s t : Finset α) :
    @Inter.inter _ (@Finset.instInter _ (fun a b => Classical.propDecidable (a = b))) s t
      = s ∩ t := by
  have h : (fun a b => Classical.propDecidable (a = b) : DecidableEq α) = inst :=
    Subsingleton.elim _ _
  rw [h]

open Classical in
/-- Bridge: `Finset.sdiff` under the `Classical` instance equals `\` under the ambient
instance. -/
theorem classical_sdiff_eq {α : Type*} [inst : DecidableEq α] (s t : Finset α) :
    @SDiff.sdiff _ (@Finset.instSDiff _ (fun a b => Classical.propDecidable (a = b))) s t
      = s \ t := by
  have h : (fun a b => Classical.propDecidable (a = b) : DecidableEq α) = inst :=
    Subsingleton.elim _ _
  rw [h]

open Classical in
/-- The hub set: vertices of degree `≥ 4`. -/
noncomputable def hubSet (G : SimpleGraph V) : Finset V :=
  Finset.univ.filter (fun v => 4 ≤ G.degree v)

open Classical in
omit [DecidableEq V] in
theorem mem_hubSet {G : SimpleGraph V} {v : V} : v ∈ hubSet G ↔ 4 ≤ G.degree v := by
  unfold hubSet
  simp

open Classical in
omit [DecidableEq V] in
theorem mem_isoTwins {G : SimpleGraph V} {t : V} :
    t ∈ isoTwins G ↔ G.degree t = 3 ∧ ∀ w : V, G.Adj t w → G.degree w ≠ 3 := by
  unfold isoTwins deg3Set
  simp

open Classical in
/-- `mIncidence` in the ambient-instance sum form. -/
theorem mIncidence_eq_sum (G : SimpleGraph V) :
    mIncidence G = ∑ v ∈ deg3Set G, (G.neighborFinset v ∩ deg3Set G).card := by
  unfold mIncidence
  simp only [classical_inter_eq]

/-! ### Iso-twin bookkeeping -/

omit [DecidableEq V] in
open Classical in
/-- Two iso twins are never adjacent. -/
theorem isoTwins_not_adj (G : SimpleGraph V) {s t : V}
    (hs : s ∈ isoTwins G) (ht : t ∈ isoTwins G) : ¬G.Adj s t :=
  fun hadj => (mem_isoTwins.mp hs).2 t hadj (mem_isoTwins.mp ht).1

/-! ### The certificates -/

open Classical in
/-- Neighbourhood–triple non-adjacency gives a zero cross count. -/
theorem nbr_inter_triple_zero (G : SimpleGraph V) (p x y z : V)
    (hx : ¬G.Adj p x) (hy : ¬G.Adj p y) (hz : ¬G.Adj p z) :
    (G.neighborFinset p ∩ ({x, y, z} : Finset V)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro w hw
  rw [Finset.mem_inter, G.mem_neighborFinset] at hw
  obtain ⟨hadj, hmem⟩ := hw
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl
  · exact hx hadj
  · exact hy hadj
  · exact hz hadj

open Classical in
/-- **Open-star boundary count**: a hub of degree `≤ 4` with two degree-`3` leaves inside
its triple leaks at most `(4 − 2) + 2 + 2 = 6` — the `P`-side arithmetic of the two-hub
cut, `n`-independent. -/
theorem star3_leak_le_six (G : SimpleGraph V) (h a b : V)
    (hne_ha : h ≠ a) (hne_hb : h ≠ b) (hne_ab : a ≠ b)
    (hadj_a : G.Adj a h) (hadj_b : G.Adj b h)
    (hda : G.degree a = 3) (hdb : G.degree b = 3) (hdh : G.degree h ≤ 4) :
    ∑ p ∈ ({h, a, b} : Finset V),
      (G.neighborFinset p \ ({h, a, b} : Finset V)).card ≤ 6 := by
  have hhP : h ∈ ({h, a, b} : Finset V) := Finset.mem_insert_self _ _
  have haP : a ∈ ({h, a, b} : Finset V) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hbP : b ∈ ({h, a, b} : Finset V) :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  -- Centre leak `≤ deg h − 2`.
  have hcen : (G.neighborFinset h \ ({h, a, b} : Finset V)).card + 2 ≤ G.degree h := by
    have hsub : ({a, b} : Finset V) ⊆ G.neighborFinset h ∩ ({h, a, b} : Finset V) := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h x).mpr hadj_a.symm, haP⟩
      · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset h x).mpr hadj_b.symm, hbP⟩
    have h2 : 2 ≤ (G.neighborFinset h ∩ ({h, a, b} : Finset V)).card := by
      have hle := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem (by simp [hne_ab]), Finset.card_singleton] at hle
      omega
    have hsplit := Finset.card_sdiff_add_card_inter (G.neighborFinset h)
      ({h, a, b} : Finset V)
    have hd := G.card_neighborFinset_eq_degree h
    omega
  -- Leaf leak `≤ 2`.
  have hleaf : ∀ x : V, G.Adj x h → G.degree x = 3 →
      (G.neighborFinset x \ ({h, a, b} : Finset V)).card ≤ 2 := by
    intro x hadj hdx
    have hin : h ∈ G.neighborFinset x ∩ ({h, a, b} : Finset V) :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x h).mpr hadj, hhP⟩
    have h1 : 1 ≤ (G.neighborFinset x ∩ ({h, a, b} : Finset V)).card :=
      Finset.card_pos.mpr ⟨h, hin⟩
    have hsplit := Finset.card_sdiff_add_card_inter (G.neighborFinset x)
      ({h, a, b} : Finset V)
    have hd := G.card_neighborFinset_eq_degree x
    omega
  have hla := hleaf a hadj_a hda
  have hlb := hleaf b hadj_b hdb
  rw [Finset.sum_insert (by simp [hne_ha, hne_hb]),
    Finset.sum_insert (by simp [hne_ab]), Finset.sum_singleton]
  omega

omit [DecidableEq V] in
open Classical in
/-- **The two-hub opposite-twin cut, generic `V`** (port of
`two_hub_opposite_twin_cert_nineteen`, output `TwoBlockConfig`): the boundary tie
`2·0 + 6 + 6 = 12 ≤ 4·3`.  The hub degrees are only required `≤ 4` (slack-tolerant
strengthening; the per-`n` versions used `= 4`). -/
theorem two_hub_opposite_twin_twoBlock (G : SimpleGraph V) (h₁ h₂ a b c d : V)
    (hdegh₁ : G.degree h₁ ≤ 4) (hdegh₂ : G.degree h₂ ≤ 4)
    (hdega : G.degree a = 3) (hdegb : G.degree b = 3)
    (hdegc : G.degree c = 3) (hdegd : G.degree d = 3)
    (hadj_ah₁ : G.Adj a h₁) (hadj_bh₁ : G.Adj b h₁)
    (hadj_ch₂ : G.Adj c h₂) (hadj_dh₂ : G.Adj d h₂)
    (hn_h₁h₂ : ¬G.Adj h₁ h₂) (hn_h₁c : ¬G.Adj h₁ c) (hn_h₁d : ¬G.Adj h₁ d)
    (hn_ah₂ : ¬G.Adj a h₂) (hn_ac : ¬G.Adj a c) (hn_ad : ¬G.Adj a d)
    (hn_bh₂ : ¬G.Adj b h₂) (hn_bc : ¬G.Adj b c) (hn_bd : ¬G.Adj b d)
    (ne_h₁h₂ : h₁ ≠ h₂)
    (ne_h₁a : h₁ ≠ a) (ne_h₁b : h₁ ≠ b) (ne_h₁c : h₁ ≠ c) (ne_h₁d : h₁ ≠ d)
    (ne_h₂a : h₂ ≠ a) (ne_h₂b : h₂ ≠ b) (ne_h₂c : h₂ ≠ c) (ne_h₂d : h₂ ≠ d)
    (ne_ab : a ≠ b) (ne_ac : a ≠ c) (ne_ad : a ≠ d)
    (ne_bc : b ≠ c) (ne_bd : b ≠ d) (ne_cd : c ≠ d) :
    TwoBlockConfig G := by
  classical
  have hPcard : ({h₁, a, b} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [ne_h₁a, ne_h₁b]),
      Finset.card_insert_of_notMem (by simp [ne_ab]), Finset.card_singleton]
  have hNcard : ({h₂, c, d} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [ne_h₂c, ne_h₂d]),
      Finset.card_insert_of_notMem (by simp [ne_cd]), Finset.card_singleton]
  have hdisj : Disjoint ({h₁, a, b} : Finset V) ({h₂, c, d} : Finset V) := by
    rw [Finset.disjoint_left]
    intro w hw hw'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw hw'
    rcases hw with rfl | rfl | rfl <;> rcases hw' with rfl | rfl | rfl <;>
      first
        | exact ne_h₁h₂ rfl | exact ne_h₁c rfl | exact ne_h₁d rfl
        | exact ne_h₂a rfl.symm | exact ne_ac rfl | exact ne_ad rfl
        | exact ne_h₂b rfl.symm | exact ne_bc rfl | exact ne_bd rfl
  have hcr1 := nbr_inter_triple_zero G h₁ h₂ c d hn_h₁h₂ hn_h₁c hn_h₁d
  have hcr2 := nbr_inter_triple_zero G a h₂ c d hn_ah₂ hn_ac hn_ad
  have hcr3 := nbr_inter_triple_zero G b h₂ c d hn_bh₂ hn_bc hn_bd
  have hcross : ∑ p ∈ ({h₁, a, b} : Finset V),
      (G.neighborFinset p ∩ ({h₂, c, d} : Finset V)).card = 0 := by
    rw [Finset.sum_insert (by simp [ne_h₁a, ne_h₁b]),
      Finset.sum_insert (by simp [ne_ab]), Finset.sum_singleton]
    omega
  have hleakP := star3_leak_le_six G h₁ a b ne_h₁a ne_h₁b ne_ab hadj_ah₁ hadj_bh₁
    hdega hdegb hdegh₁
  have hleakN := star3_leak_le_six G h₂ c d ne_h₂c ne_h₂d ne_cd hadj_ch₂ hadj_dh₂
    hdegc hdegd hdegh₂
  refine ⟨({h₁, a, b} : Finset V), ({h₂, c, d} : Finset V), hdisj,
    (by rw [hPcard, hNcard]), (by rw [hPcard]; norm_num), ?_⟩
  rw [hPcard, hcross]
  omega

open Classical in
/-- **Two hubs with `2 + 2` private iso twins give a two-block cut** — the positive form
of the per-`n` `hno2hub` selector (`select_finish` + `two_hub_config`): whenever the
selector's existential holds, the cut fires. -/
theorem two_hub_private_pair_twoBlock (G : SimpleGraph V) (h₁ h₂ : V)
    (hdh₁ : G.degree h₁ = 4) (hdh₂ : G.degree h₂ = 4)
    (hne : h₁ ≠ h₂) (hnadj : ¬G.Adj h₁ h₂)
    (hpriv1 : 2 ≤ ((G.neighborFinset h₁ ∩ isoTwins G) \ G.neighborFinset h₂).card)
    (hpriv2 : 2 ≤ ((G.neighborFinset h₂ ∩ isoTwins G) \ G.neighborFinset h₁).card) :
    TwoBlockConfig G := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < ((G.neighborFinset h₁
    ∩ isoTwins G) \ G.neighborFinset h₂).card)
  obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp (by omega : 1 < ((G.neighborFinset h₂
    ∩ isoTwins G) \ G.neighborFinset h₁).card)
  have unpack1 : ∀ t : V, t ∈ (G.neighborFinset h₁ ∩ isoTwins G) \ G.neighborFinset h₂ →
      G.Adj t h₁ ∧ t ∈ isoTwins G ∧ ¬G.Adj t h₂ := by
    intro t ht
    rw [Finset.mem_sdiff, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset] at ht
    exact ⟨ht.1.1.symm, ht.1.2, fun h => ht.2 h.symm⟩
  have unpack2 : ∀ t : V, t ∈ (G.neighborFinset h₂ ∩ isoTwins G) \ G.neighborFinset h₁ →
      G.Adj t h₂ ∧ t ∈ isoTwins G ∧ ¬G.Adj t h₁ := by
    intro t ht
    rw [Finset.mem_sdiff, Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset] at ht
    exact ⟨ht.1.1.symm, ht.1.2, fun h => ht.2 h.symm⟩
  obtain ⟨ha1, haI, hna2⟩ := unpack1 a ha
  obtain ⟨hb1, hbI, hnb2⟩ := unpack1 b hb
  obtain ⟨hc2, hcI, hnc1⟩ := unpack2 c hc
  obtain ⟨hd2, hdI, hnd1⟩ := unpack2 d hd
  have hda := (mem_isoTwins.mp haI).1
  have hdb := (mem_isoTwins.mp hbI).1
  have hdc := (mem_isoTwins.mp hcI).1
  have hdd := (mem_isoTwins.mp hdI).1
  exact two_hub_opposite_twin_twoBlock G h₁ h₂ a b c d (by omega) (by omega)
    hda hdb hdc hdd ha1 hb1 hc2 hd2 hnadj (fun h => hnc1 h.symm) (fun h => hnd1 h.symm)
    hna2 (isoTwins_not_adj G haI hcI) (isoTwins_not_adj G haI hdI)
    hnb2 (isoTwins_not_adj G hbI hcI) (isoTwins_not_adj G hbI hdI)
    hne
    (fun e => by rw [e] at hdh₁; omega) (fun e => by rw [e] at hdh₁; omega)
    (fun e => by rw [e] at hdh₁; omega) (fun e => by rw [e] at hdh₁; omega)
    (fun e => by rw [e] at hdh₂; omega) (fun e => by rw [e] at hdh₂; omega)
    (fun e => by rw [e] at hdh₂; omega) (fun e => by rw [e] at hdh₂; omega)
    hab (fun e => hnc1 (e ▸ ha1)) (fun e => hnd1 (e ▸ ha1))
    (fun e => hnc1 (e ▸ hb1)) (fun e => hnd1 (e ▸ hb1)) hcd

end ACMax
