/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import LeanPool.ACMax.Counting.CompactCell
import LeanPool.ACMax.Counting.DoubleStar

/-!
# Compact-cell counting ledgers

The counting infrastructure of the compact cell: a family of double-counting
inequalities that bound the population of usable / suppressed degree-3 vertices by
the total degree excess `X = excessX` plus explicit constants. These *ledgers*
turn the compact cell into a search bounded in `n` for each fixed excess.

## Main results

* `sfb_forces_sharing`, `no_two_saturated_deg6` — on the `SeaFatBoundary`, a pair
  of clean same-count hubs is forced to share `≥ 3` twins, and two saturated
  degree-6 hubs would build a forbidden good `K_{2,3}`.
* `mIncidence_le_two`, `medge_endpoint_card_le` — the global cap on the
  degree-3–degree-3 adjacency mass.
* `anchored_sharing_count`, `class_cap_with_adj` — the anchored twin-sharing
  double count `σ₀·(|T| − 1) ≤ 2a` and the class cap `|T| ≤ 1 + i₀ + 2a`.
* `w1_of_unblocked_eq_twins`, `w1_of_unblocked_pad_supply` — the far-pad supply
  discharging the `W1` firing bridge.
* The suppressed-vertex ledgers `3·#S ≤ Σ_{deg ≥ 4} |hubTwins|` etc.,
  `weighted_heavy_ledger` `(3/2)·#S ≤ Σ_{deg ≥ 5} σ·|hubTwins|`, and their
  absorption `suppressed_card_le` `(3/2)·#S ≤ (4/3)·X + 5703`.
* `usable_deg3_pair_coverage` — the pair-coverage inequality on the usable
  degree-3 set.
* `mid_leaves_card_le` / `mid_leaves_card_le_sharp` (`|L₈| ≤ 143`, sharpened to
  `108`), `mid_usable5_card_le`, and the splits `usable_deg3_split_mid`,
  `w5_card_split` isolating the big-neighbour cloud classes.
-/

/-! ## The Sea-Fat-Boundary sharing law and the `K₂,₃` bridge

On the `SeaFatBoundary` (every hub pair DS-blocked, `dsValue ≥ 5`), a pair of
same-count hubs with zero internal degree, zero `mCross` and no adjacency shares
`≥ 3` twins (`sfb_forces_sharing`); two saturated degree-6 hubs with independent
shared twins would assemble a good `K_{2,3}` (`Σ₅deg = 21`), contradicting
`no_good_K23` (`no_two_saturated_deg6`). -/

namespace ACMax

variable {V : Type*} [Fintype V]

open Classical in
/-- Partition of `N(g)` by `deg3Set`-membership: `|D3(g)| + i(g) = deg g`. -/
theorem card_hubTwins_add_intDeg (G : SimpleGraph V) (g : V) :
    (hubTwins G g).card + intDeg G g = G.degree g := by
  unfold hubTwins intDeg
  rw [Finset.card_inter_add_card_sdiff]
  exact G.card_neighborFinset_eq_degree g

open Classical in
/-- Partition of `D3(g)` by `D3(h)`-membership: `p(g,h) + s(g,h) = |D3(g)|`. -/
theorem privTwins_card_eq (G : SimpleGraph V) (g h : V) :
    (privTwins G g h).card + (sharedTwins G g h).card = (hubTwins G g).card := by
  unfold privTwins sharedTwins
  exact Finset.card_sdiff_add_card_inter _ _

end ACMax

/-! ## A global cap on the `M`-incidence count

In the residual core the degree-3–degree-3 adjacency mass is globally bounded by a
constant: `mIncidence_le_two` (`mIncidence G ≤ 2` under the block-law matching),
`medge_endpoint_card_le_two` (at most `2` degree-3 `M`-edge endpoints) and
`medge_endpoint_hub_card_le_four` (at most `4` hubs own an `M`-endpoint twin). The
constants are deliberately crude; only their existence matters downstream. -/

namespace ACMax

open Classical in
/-- `mIncidence` written with the ambient decidability instances of `Fin n` (bridging the
`Classical` instances baked into the definition over an abstract vertex type). -/
theorem mIncidence_eq (n : ℕ) (G : SimpleGraph (Fin n)) :
    mIncidence G = ∑ v ∈ deg3Set G, (G.neighborFinset v ∩ deg3Set G).card := by
  unfold mIncidence
  refine Finset.sum_congr rfl fun v _ => ?_
  congr 1
  ext w
  simp only [Finset.mem_inter]

open Classical in
/-- Membership in `hubTwins`, stated over a general vertex type so that the classical
decidability instances inside the definition match those synthesised in the proof. -/
theorem mem_hubTwins_adj {V : Type*} [Fintype V] {G : SimpleGraph V} {g v : V} :
    v ∈ hubTwins G g ↔ G.Adj g v ∧ G.degree v = 3 := by
  unfold hubTwins
  rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, mem_deg3Set]

open Classical in
/-- **The incidence collapse**: when all `M`-edges coincide, the incidence
count is at most `2` — the two endpoints of the single edge. -/
theorem mIncidence_le_two (n : ℕ) (G : SimpleGraph (Fin n))
    (huniq : ∀ t₁ t₂ t₃ t₄ : Fin n, G.Adj t₁ t₂ → G.Adj t₃ t₄ →
      G.degree t₁ = 3 → G.degree t₂ = 3 → G.degree t₃ = 3 →
      G.degree t₄ = 3 →
      ({t₁, t₂} : Finset (Fin n)) = ({t₃, t₄} : Finset (Fin n))) :
    mIncidence G ≤ 2 := by
  classical
  rw [mIncidence_eq]
  by_cases hE : ∃ a b : Fin n, G.Adj a b ∧ G.degree a = 3 ∧ G.degree b = 3
  · obtain ⟨a, b, hab, ha3, hb3⟩ := hE
    have hterm : ∀ t ∈ deg3Set G, t ≠ a → t ≠ b →
        (G.neighborFinset t ∩ deg3Set G).card = 0 := by
      intro t ht hta htb
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro u hu
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hu
      have := huniq t u a b hu.1 hab (mem_deg3Set.mp ht)
        (mem_deg3Set.mp hu.2) ha3 hb3
      have hmem : t ∈ ({a, b} : Finset (Fin n)) := by
        rw [← this]
        exact Finset.mem_insert_self t {u}
      rw [Finset.mem_insert, Finset.mem_singleton] at hmem
      tauto
    have htermab : ∀ t : Fin n, G.degree t = 3 →
        (G.neighborFinset t ∩ deg3Set G).card ≤ 1 := by
      intro t ht3
      by_cases hta : t = a
      · subst hta
        have hsub : G.neighborFinset t ∩ deg3Set G ⊆ {b} := by
          intro u hu
          rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hu
          have := huniq t u t b hu.1 hab ht3 (mem_deg3Set.mp hu.2) ht3 hb3
          have hmem : u ∈ ({t, b} : Finset (Fin n)) := by
            rw [← this]
            exact Finset.mem_insert_of_mem (Finset.mem_singleton_self u)
          rw [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with rfl | rfl
          · exact absurd hu.1 (G.irrefl)
          · exact Finset.mem_singleton_self u
        calc (G.neighborFinset t ∩ deg3Set G).card
            ≤ ({b} : Finset (Fin n)).card := Finset.card_le_card hsub
          _ = 1 := Finset.card_singleton b
      · by_cases htb : t = b
        · have hsub : G.neighborFinset t ∩ deg3Set G ⊆ {a} := by
            intro u hu
            rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hu
            have heq := huniq u t a b hu.1.symm hab (mem_deg3Set.mp hu.2)
              ht3 ha3 hb3
            have hmem : u ∈ ({a, b} : Finset (Fin n)) := by
              rw [← heq]
              exact Finset.mem_insert_self u {t}
            rw [Finset.mem_insert, Finset.mem_singleton] at hmem
            rcases hmem with rfl | rfl
            · exact Finset.mem_singleton_self u
            · exact absurd hu.1 (by
                rw [htb]
                exact fun h => G.irrefl h)
          calc (G.neighborFinset t ∩ deg3Set G).card
              ≤ ({a} : Finset (Fin n)).card := Finset.card_le_card hsub
            _ = 1 := Finset.card_singleton a
        · rw [hterm t (mem_deg3Set.mpr ht3) hta htb]
          omega
    calc ∑ t ∈ deg3Set G, (G.neighborFinset t ∩ deg3Set G).card
        = ∑ t ∈ (deg3Set G).filter (fun t => t = a ∨ t = b),
            (G.neighborFinset t ∩ deg3Set G).card
          + ∑ t ∈ (deg3Set G).filter (fun t => ¬(t = a ∨ t = b)),
            (G.neighborFinset t ∩ deg3Set G).card :=
          (Finset.sum_filter_add_sum_filter_not _ _ _).symm
      _ ≤ 2 + 0 := by
          refine Nat.add_le_add ?_ ?_
          · calc ∑ t ∈ (deg3Set G).filter (fun t => t = a ∨ t = b),
                (G.neighborFinset t ∩ deg3Set G).card
                ≤ ∑ _t ∈ (deg3Set G).filter (fun t => t = a ∨ t = b), 1 := by
                  refine Finset.sum_le_sum fun t ht => ?_
                  exact htermab t (mem_deg3Set.mp (Finset.mem_of_mem_filter t ht))
              _ = ((deg3Set G).filter (fun t => t = a ∨ t = b)).card := by
                  rw [Finset.sum_const, smul_eq_mul, Nat.mul_one]
              _ ≤ ({a, b} : Finset (Fin n)).card := by
                  refine Finset.card_le_card ?_
                  intro t ht
                  rw [Finset.mem_filter] at ht
                  rw [Finset.mem_insert, Finset.mem_singleton]
                  exact ht.2
              _ ≤ 2 := Finset.card_insert_le a {b} |>.trans (by
                  rw [Finset.card_singleton])
          · refine Nat.le_of_eq (Finset.sum_eq_zero fun t ht => ?_)
            rw [Finset.mem_filter] at ht
            push Not at ht
            exact hterm t ht.1 ht.2.1 ht.2.2
      _ = 2 := rfl
  · push Not at hE
    refine Nat.le_of_eq ?_ |>.trans (by omega : (0:ℕ) ≤ 2)
    refine Finset.sum_eq_zero fun t ht => ?_
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro u hu
    rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hu
    exact hE t u hu.1 (mem_deg3Set.mp ht) (mem_deg3Set.mp hu.2)

open Classical in
/-- `M`-endpoints under the dichotomy: at most `2`. -/
theorem medge_endpoint_card_le_two (n : ℕ) (G : SimpleGraph (Fin n))
    (huniq : ∀ t₁ t₂ t₃ t₄ : Fin n, G.Adj t₁ t₂ → G.Adj t₃ t₄ →
      G.degree t₁ = 3 → G.degree t₂ = 3 → G.degree t₃ = 3 →
      G.degree t₄ = 3 →
      ({t₁, t₂} : Finset (Fin n)) = ({t₃, t₄} : Finset (Fin n))) :
    ((deg3Set G).filter (fun t => ∃ t' : Fin n, G.Adj t t' ∧ G.degree t' = 3)).card
      ≤ 2 := by
  have hle : ((deg3Set G).filter
        (fun t => ∃ t' : Fin n, G.Adj t t' ∧ G.degree t' = 3)).card
      ≤ mIncidence G := by
    rw [mIncidence_eq]
    calc ((deg3Set G).filter
          (fun t => ∃ t' : Fin n, G.Adj t t' ∧ G.degree t' = 3)).card
        = ∑ _t ∈ (deg3Set G).filter
            (fun t => ∃ t' : Fin n, G.Adj t t' ∧ G.degree t' = 3), 1 :=
          Finset.card_eq_sum_ones _
      _ ≤ ∑ t ∈ (deg3Set G).filter
            (fun t => ∃ t' : Fin n, G.Adj t t' ∧ G.degree t' = 3),
            (G.neighborFinset t ∩ deg3Set G).card := by
          refine Finset.sum_le_sum fun t ht => ?_
          rw [Finset.mem_filter] at ht
          obtain ⟨-, t', hadj, ht'3⟩ := ht
          refine Finset.card_pos.mpr ⟨t', ?_⟩
          rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
          exact ⟨hadj, mem_deg3Set.mpr ht'3⟩
      _ ≤ ∑ t ∈ deg3Set G, (G.neighborFinset t ∩ deg3Set G).card := by
          refine Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
  exact hle.trans (mIncidence_le_two n G huniq)

open Classical in
/-- Endpoint hubs under the dichotomy: at most `4`. -/
theorem medge_endpoint_hub_card_le_four (n : ℕ) (G : SimpleGraph (Fin n))
    (_h : ResidualCore n G)
    (huniq : ∀ t₁ t₂ t₃ t₄ : Fin n, G.Adj t₁ t₂ → G.Adj t₃ t₄ →
      G.degree t₁ = 3 → G.degree t₂ = 3 → G.degree t₃ = 3 →
      G.degree t₄ = 3 →
      ({t₁, t₂} : Finset (Fin n)) = ({t₃, t₄} : Finset (Fin n))) :
    (Finset.univ.filter (fun g : Fin n => 4 ≤ G.degree g ∧
        ∃ t ∈ hubTwins G g, ∃ t' : Fin n, G.Adj t t' ∧ G.degree t' = 3)).card
      ≤ 4 := by
  classical
  set T := (deg3Set G).filter
    (fun t => ∃ t' : Fin n, G.Adj t t' ∧ G.degree t' = 3) with hT
  have hTcard : T.card ≤ 2 := by
    rw [hT]
    exact medge_endpoint_card_le_two n G huniq
  have hsub : Finset.univ.filter (fun g : Fin n => 4 ≤ G.degree g ∧
        ∃ t ∈ hubTwins G g, ∃ t' : Fin n, G.Adj t t' ∧ G.degree t' = 3)
      ⊆ T.biUnion (fun t =>
        (G.neighborFinset t).filter (fun g => 4 ≤ G.degree g)) := by
    intro g hg
    rw [Finset.mem_filter] at hg
    obtain ⟨-, h4, t, htw, t', hadj, ht'3⟩ := hg
    obtain ⟨hgt, htD3⟩ := mem_hubTwins_adj.mp htw
    rw [Finset.mem_biUnion]
    refine ⟨t, ?_, ?_⟩
    · rw [hT, Finset.mem_filter]
      exact ⟨mem_deg3Set.mpr htD3, t', hadj, ht'3⟩
    · rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact ⟨hgt.symm, h4⟩
  calc (Finset.univ.filter (fun g : Fin n => 4 ≤ G.degree g ∧
        ∃ t ∈ hubTwins G g, ∃ t' : Fin n, G.Adj t t' ∧ G.degree t' = 3)).card
      ≤ ∑ t ∈ T, ((G.neighborFinset t).filter
          (fun g => 4 ≤ G.degree g)).card :=
        (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ T, 2 := by
        refine Finset.sum_le_sum fun t ht => ?_
        rw [hT, Finset.mem_filter] at ht
        have ht3 : G.degree t = 3 := mem_deg3Set.mp ht.1
        obtain ⟨t', hadj, ht'3⟩ := ht.2
        have ht'mem : t' ∈ G.neighborFinset t :=
          (G.mem_neighborFinset t t').mpr hadj
        have hsub2 : (G.neighborFinset t).filter (fun g => 4 ≤ G.degree g)
            ⊆ (G.neighborFinset t).erase t' := by
          intro g hg
          rw [Finset.mem_filter] at hg
          refine Finset.mem_erase.mpr ⟨?_, hg.1⟩
          rintro rfl
          omega
        calc ((G.neighborFinset t).filter (fun g => 4 ≤ G.degree g)).card
            ≤ ((G.neighborFinset t).erase t').card :=
              Finset.card_le_card hsub2
          _ = G.degree t - 1 := by
              rw [Finset.card_erase_of_mem ht'mem,
                G.card_neighborFinset_eq_degree]
          _ ≤ 2 := by omega
    _ = T.card * 2 := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 4 := by omega

end ACMax

/-! ## The anchored twin-sharing double count

Fix a class `T` of clean same-count hubs on the `SeaFatBoundary`. Anchoring at
`g₀ ∈ T` and counting shared-twin incidences `I = #{(t, h) : h ∈ T∖{g₀},
t ∈ sharedTwins g₀ h}` gives `σ₀·(|T| − 1) ≤ I ≤ 2a` (`anchored_sharing_count`),
where each pair shares `≥ σ₀` twins (`sfb_forces_sharing_of_intDeg_le`, with
`σ₀ = 3 − i₀` under `intDeg ≤ i₀`) and each twin is adjacent to `≤ 2` members. -/

namespace ACMax

variable {V : Type*} [Fintype V]

open Classical in
/-- Membership in the twin set: `t ∈ D3(g) ↔ g ~ t ∧ deg t = 3`. -/
private theorem mem_hubTwins_cap {G : SimpleGraph V} {g t : V} :
    t ∈ hubTwins G g ↔ G.Adj g t ∧ G.degree t = 3 := by
  unfold hubTwins
  rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, mem_deg3Set]

open Classical in
/-- `sharedTwins g h` is the anchor's twin set filtered by `h`-twin membership. -/
private theorem sharedTwins_eq_filter_cap [DecidableEq V] (G : SimpleGraph V) (g h : V) :
    sharedTwins G g h = (hubTwins G g).filter (fun t => t ∈ hubTwins G h) := by
  ext t
  simp [sharedTwins, Finset.mem_filter, Finset.mem_inter]

open Classical in
/-- **The anchored double count.**  If every member of `T \ {g₀}` shares at least `σ₀`
twins with the anchor `g₀`, whose twin set has size `a` and consists of degree-3
vertices, then `σ₀·|T \ {g₀}| ≤ 2a`: counting incidences `(t, h)` with
`t ∈ sharedTwins g₀ h`, each `h` contributes `≥ σ₀`, while each twin `t` has only
`|N(t)| = 3` slots, one of which is `g₀` itself — so `t` serves at most `2` members. -/
theorem anchored_sharing_count [DecidableEq V] (G : SimpleGraph V) (g₀ : V)
    (T : Finset V) (σ₀ a : ℕ)
    (hshare : ∀ h ∈ T.erase g₀, σ₀ ≤ (sharedTwins G g₀ h).card)
    (ha : (hubTwins G g₀).card = a)
    (h3T : ∀ t ∈ hubTwins G g₀, G.degree t = 3) :
    σ₀ * (T.erase g₀).card ≤ 2 * a := by
  -- Lower bound: each of the `|T \ {g₀}|` members contributes `≥ σ₀` incidences.
  have hlow : (T.erase g₀).card * σ₀
      ≤ ∑ h ∈ T.erase g₀, (sharedTwins G g₀ h).card := by
    have h := Finset.sum_le_sum hshare
    rwa [Finset.sum_const, smul_eq_mul] at h
  -- Swap the double count: incidences grouped by the twin `t`.
  have hswap : ∑ h ∈ T.erase g₀, (sharedTwins G g₀ h).card
      = ∑ t ∈ hubTwins G g₀,
          ((T.erase g₀).filter (fun h => t ∈ hubTwins G h)).card := by
    calc ∑ h ∈ T.erase g₀, (sharedTwins G g₀ h).card
        = ∑ h ∈ T.erase g₀, ∑ t ∈ hubTwins G g₀,
            (if t ∈ hubTwins G h then 1 else 0) := by
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [sharedTwins_eq_filter_cap, Finset.card_filter]
      _ = ∑ t ∈ hubTwins G g₀, ∑ h ∈ T.erase g₀,
            (if t ∈ hubTwins G h then 1 else 0) := Finset.sum_comm
      _ = ∑ t ∈ hubTwins G g₀,
            ((T.erase g₀).filter (fun h => t ∈ hubTwins G h)).card := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.card_filter]
  -- Upper bound per twin: the serving members inject into `N(t) \ {g₀}` of size `2`.
  have hbound : ∀ t ∈ hubTwins G g₀,
      ((T.erase g₀).filter (fun h => t ∈ hubTwins G h)).card ≤ 2 := by
    intro t ht
    have hdt : G.degree t = 3 := h3T t ht
    have hg₀N : g₀ ∈ G.neighborFinset t := by
      rw [SimpleGraph.mem_neighborFinset]
      exact ((mem_hubTwins_cap.mp ht).1).symm
    have hsub : (T.erase g₀).filter (fun h => t ∈ hubTwins G h)
        ⊆ (G.neighborFinset t).erase g₀ := by
      intro h hh
      rw [Finset.mem_filter, Finset.mem_erase] at hh
      obtain ⟨⟨hne, _⟩, hmem⟩ := hh
      rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset]
      exact ⟨hne, ((mem_hubTwins_cap.mp hmem).1).symm⟩
    calc ((T.erase g₀).filter (fun h => t ∈ hubTwins G h)).card
        ≤ ((G.neighborFinset t).erase g₀).card := Finset.card_le_card hsub
      _ = (G.neighborFinset t).card - 1 := Finset.card_erase_of_mem hg₀N
      _ = 3 - 1 := by rw [G.card_neighborFinset_eq_degree, hdt]
      _ ≤ 2 := by omega
  -- Assemble: `σ₀·|T \ {g₀}| ≤ I ≤ 2·a`.
  have hup : ∑ t ∈ hubTwins G g₀,
      ((T.erase g₀).filter (fun h => t ∈ hubTwins G h)).card ≤ 2 * a := by
    have h := Finset.sum_le_sum hbound
    rw [Finset.sum_const, smul_eq_mul, ha] at h
    omega
  calc σ₀ * (T.erase g₀).card
      = (T.erase g₀).card * σ₀ := mul_comm _ _
    _ ≤ ∑ h ∈ T.erase g₀, (sharedTwins G g₀ h).card := hlow
    _ = ∑ t ∈ hubTwins G g₀,
          ((T.erase g₀).filter (fun h => t ∈ hubTwins G h)).card := hswap
    _ ≤ 2 * a := hup

/-! ## The saturated class cap (`intDeg = 0`) -/

/-! ## The general interaction version (`intDeg ≤ i₀`, `2·i₀ < 5`) -/

open Classical in
/-- **Forced sharing at internal degree `≤ i₀`.**  On the `SeaFatBoundary`, a nonadjacent
equal-twin-count hub pair with `intDeg ≤ i₀` each and `mCross = 0` shares at least
`3 − i₀` twins: the gap terms of `dsValue` cancel, so `5 ≤ i(g) + i(h) + 2s ≤ 2i₀ + 2s`,
and since `5 − 2i₀` is odd, `s ≥ ⌈(5 − 2i₀)/2⌉ = 3 − i₀`. -/
theorem sfb_forces_sharing_of_intDeg_le (G : SimpleGraph V) (hb : SeaFatBoundary G)
    (g h : V) (i₀ : ℕ) (hne : g ≠ h) (hg4 : 4 ≤ G.degree g) (hh4 : 4 ≤ G.degree h)
    (heq : (hubTwins G g).card = (hubTwins G h).card)
    (hig : intDeg G g ≤ i₀) (hih : intDeg G h ≤ i₀)
    (hmx : mCross G g h = 0) (hadj : ¬G.Adj g h) :
    3 - i₀ ≤ (sharedTwins G g h).card := by
  have hds : 5 ≤ dsValue G g h := hb g h hg4 hh4 hne
  have h1 := privTwins_card_eq G g h
  have h2 := privTwins_card_eq G h g
  have hsc : (sharedTwins G h g).card = (sharedTwins G g h).card := by
    rw [sharedTwins_comm G h g]
  have hai : adjInd G g h = 0 := by
    unfold adjInd
    simp [hadj]
  unfold dsValue at hds
  omega

/-! ## Pad supply for the `W1` firing bridge

Two ways to discharge the far-pad requirement of `w1Config_of_pair`:
`w1_of_unblocked_eq_twins` (gap-0: equal private-twin counts, empty pad set) and
`w1_of_unblocked_pad_supply` (pad supply: when the degree-3 supply exceeds the two
twin counts by `20`, the forbidden pads number at most `|D3(g)| + |D3(h')| + 16`,
leaving `≥ 4 ≥ gap` far pads). -/

open Classical in
/-- **Gap-0 firing**: a DS-unblocked hub pair with *equal* private-twin counts is a W1
configuration — the empty pad set closes the count. -/
theorem w1_of_unblocked_eq_twins (G : SimpleGraph V) (g h : V)
    (hg4 : 4 ≤ G.degree g) (hh4 : 4 ≤ G.degree h) (hne : g ≠ h)
    (heq : (privTwins G g h).card = (privTwins G h g).card)
    (hds : dsValue G g h ≤ 4) : W1Config G := by
  refine w1Config_of_pair G g h ∅ hg4 hh4 hne
    (fun f hf => absurd hf (Finset.notMem_empty f))
    (fun f hf => absurd hf (Finset.notMem_empty f)) ?_ hds
  simpa using heq.symm

end ACMax

/-! ## The anchor bound and the suppressed ledgers

**Anchor bound**: on the compact cell every usable vertex lies in the radius-3
ball around a usable degree-3 anchor `t`, so
`#{v : deg v = 3, sigS v ≤ 2} ≤ 1 + |hubTwins t| + Σ_{x∈N(t)} |hubTwins x| +
Σ_{x∈N(t)} Σ_{y∈N(x)} |hubTwins y|`. **Suppressed ledgers**: a suppressed vertex
(`deg = 3`, `sigS > 2`) has, by `nonusable_deg3_structure`, `3` hub neighbours,
`2` of degree `≥ 5` and `1` of degree `≥ 6`; double-counting gives
`3·#S ≤ Σ_{deg ≥ 4} |hubTwins|`, `2·#S ≤ Σ_{deg ≥ 5} |hubTwins|`,
`#S ≤ Σ_{deg ≥ 6} |hubTwins|`. -/

namespace ACMax

open Finset

/-! ## `hubTwins` as a degree filter (generic `V`, keeping the classical
instances of `GeneralDoubleStar` stable) -/

section GenericV

variable {V : Type*} [Fintype V]

open Classical in
/-- Membership in `hubTwins`: a hub twin of `g` is a degree-3 neighbour. -/
theorem mem_hubTwins_iff {G : SimpleGraph V} {g v : V} :
    v ∈ hubTwins G g ↔ G.Adj g v ∧ G.degree v = 3 := by
  unfold hubTwins
  rw [Finset.mem_inter, G.mem_neighborFinset, mem_deg3Set]

end GenericV

end ACMax

/-! ## The weighted heavy ledger

A σ-weighted refinement of the suppressed ledgers. A suppressed vertex has at
most one degree-4 neighbour (contributing `σ(4) = 1/2`), so the σ-mass from heavy
(degree `≥ 5`) neighbours is `≥ 3/2` (`heavy_sigma_into_suppressed`); summing and
swapping the double count gives the **weighted heavy ledger**
`(3/2)·#S ≤ Σ_{deg w ≥ 5} σ(deg w)·|hubTwins w|`. -/

namespace ACMax

open Finset

variable {n : ℕ}

/-! ## The integer-profile sharpening: `3/2 → 32/21` -/

open Classical in
/-- **The σ-value pair gap.**  Two heavy σ-values summing strictly above `3/2`
sum to at least `32/21`: the σ-value set `{2/3, 3/4, 4/5, 5/6, 6/7, …}` is
discrete, so the sum cannot approach `3/2` from above — the minimum is the
`(5, 9)`-profile `2/3 + 6/7 = 32/21`. -/
theorem sigma_pair_gap {d₁ d₂ : ℕ} (h₁ : 5 ≤ d₁) (h₂ : 5 ≤ d₂)
    (h : (3 / 2 : ℝ) < sigma d₁ + sigma d₂) :
    (32 / 21 : ℝ) ≤ sigma d₁ + sigma d₂ := by
  -- σ(d) > 5/6 forces d ≥ 9, hence σ(d) ≥ 6/7
  have key : ∀ d : ℕ, 5 ≤ d → (5 / 6 : ℝ) < sigma d → (6 / 7 : ℝ) ≤ sigma d := by
    intro d hd hgt
    have hd9 : 9 ≤ d := by
      by_contra hcon
      have h8 : d ≤ 8 := by omega
      have hle : sigma d ≤ sigma 8 := sigma_mono (by omega) h8
      have h8v : sigma 8 = 5 / 6 := by norm_num [sigma]
      linarith
    have hge : sigma 9 ≤ sigma d := sigma_mono (by norm_num) hd9
    have h9v : sigma 9 = 6 / 7 := by norm_num [sigma]
    linarith
  by_cases hd₁5 : d₁ = 5
  · have h₁v : sigma d₁ = 2 / 3 := by rw [hd₁5]; exact sigma_five
    have hgt : (5 / 6 : ℝ) < sigma d₂ := by
      rw [h₁v] at h
      linarith
    have := key d₂ h₂ hgt
    rw [h₁v]
    linarith
  by_cases hd₂5 : d₂ = 5
  · have h₂v : sigma d₂ = 2 / 3 := by rw [hd₂5]; exact sigma_five
    have hgt : (5 / 6 : ℝ) < sigma d₁ := by
      rw [h₂v] at h
      linarith
    have := key d₁ h₁ hgt
    rw [h₂v]
    linarith
  -- both degrees ≥ 6
  have h₁6 : 6 ≤ d₁ := by omega
  have h₂6 : 6 ≤ d₂ := by omega
  have hs₁ : (3 / 4 : ℝ) ≤ sigma d₁ := by
    have := sigma_mono (by norm_num : 3 ≤ 6) h₁6
    rw [sigma_six] at this
    linarith
  have hs₂ : (3 / 4 : ℝ) ≤ sigma d₂ := by
    have := sigma_mono (by norm_num : 3 ≤ 6) h₂6
    rw [sigma_six] at this
    linarith
  by_cases hd₁6 : d₁ = 6
  · by_cases hd₂6 : d₂ = 6
    · rw [hd₁6, hd₂6, sigma_six] at h
      norm_num at h
    · have h₂7 : 7 ≤ d₂ := by omega
      have hσ₂ : (4 / 5 : ℝ) ≤ sigma d₂ := by
        have := sigma_mono (by norm_num : 3 ≤ 7) h₂7
        have h7v : sigma 7 = 4 / 5 := by norm_num [sigma]
        linarith
      rw [hd₁6, sigma_six]
      linarith
  · have h₁7 : 7 ≤ d₁ := by omega
    have hσ₁ : (4 / 5 : ℝ) ≤ sigma d₁ := by
      have := sigma_mono (by norm_num : 3 ≤ 7) h₁7
      have h7v : sigma 7 = 4 / 5 := by norm_num [sigma]
      linarith
    linarith

open Classical in
/-- **Sharp heavy σ-inflow (integer profile).**  A suppressed vertex receives
σ-mass at least `32/21` from its heavy neighbours: with a degree-4 neighbour
present, the remaining two heavy σ-values sum strictly above `3/2`, hence to
at least `32/21` by the pair gap; with no degree-4 neighbour the heavy sum
already exceeds `2`. -/
theorem heavy_sigma_into_suppressed_sharp (G : SimpleGraph (Fin n)) (t : Fin n)
    (h3 : ∀ v, 3 ≤ G.degree v) (hd : G.degree t = 3) (hs : 2 < sigS G t) :
    (32 / 21 : ℝ) ≤ ∑ w ∈ (G.neighborFinset t).filter (fun w => 5 ≤ G.degree w),
      sigma (G.degree w) := by
  obtain ⟨hall4, -, htwo⟩ := nonusable_deg3_structure G t hd h3 hs
  have hsplit :
      (∑ w ∈ (G.neighborFinset t).filter (fun w => 5 ≤ G.degree w),
          sigma (G.degree w))
        + ∑ w ∈ (G.neighborFinset t).filter (fun w => ¬ 5 ≤ G.degree w),
            sigma (G.degree w)
      = sigS G t := by
    rw [sigS]
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have hcards :
      ((G.neighborFinset t).filter (fun w => 5 ≤ G.degree w)).card
        + ((G.neighborFinset t).filter (fun w => ¬ 5 ≤ G.degree w)).card
      = (G.neighborFinset t).card :=
    Finset.card_filter_add_card_filter_not _
  have hN3 : (G.neighborFinset t).card = 3 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hd
  by_cases hcomp0 :
      ((G.neighborFinset t).filter (fun w => ¬ 5 ≤ G.degree w)).card = 0
  · -- no light neighbour: the heavy sum is all of `sigS > 2 > 32/21`
    have hempty : (G.neighborFinset t).filter (fun w => ¬ 5 ≤ G.degree w) = ∅ :=
      Finset.card_eq_zero.mp hcomp0
    have hzero : ∑ w ∈ (G.neighborFinset t).filter (fun w => ¬ 5 ≤ G.degree w),
        sigma (G.degree w) = 0 := by
      rw [hempty, Finset.sum_empty]
    linarith
  · -- exactly one light neighbour, of degree 4
    have hcomp1 :
        ((G.neighborFinset t).filter (fun w => ¬ 5 ≤ G.degree w)).card = 1 := by
      omega
    obtain ⟨w₀, hw₀⟩ := Finset.card_eq_one.mp hcomp1
    have hw₀mem : w₀ ∈ (G.neighborFinset t).filter (fun w => ¬ 5 ≤ G.degree w) := by
      rw [hw₀]
      exact Finset.mem_singleton_self w₀
    have hw₀4 : G.degree w₀ = 4 := by
      obtain ⟨hwN, hw5⟩ := Finset.mem_filter.mp hw₀mem
      have := hall4 w₀ hwN
      omega
    have hcompsum :
        ∑ w ∈ (G.neighborFinset t).filter (fun w => ¬ 5 ≤ G.degree w),
            sigma (G.degree w) = 1 / 2 := by
      rw [hw₀, Finset.sum_singleton, hw₀4, sigma_four]
    -- the heavy filter has exactly two elements
    have hheavy2 :
        ((G.neighborFinset t).filter (fun w => 5 ≤ G.degree w)).card = 2 := by
      omega
    obtain ⟨w₁, w₂, hne, hpair⟩ := Finset.card_eq_two.mp hheavy2
    have hw₁mem : w₁ ∈ (G.neighborFinset t).filter (fun w => 5 ≤ G.degree w) := by
      rw [hpair]
      exact Finset.mem_insert_self _ _
    have hw₂mem : w₂ ∈ (G.neighborFinset t).filter (fun w => 5 ≤ G.degree w) := by
      rw [hpair]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self w₂)
    have hw₁5 : 5 ≤ G.degree w₁ := (Finset.mem_filter.mp hw₁mem).2
    have hw₂5 : 5 ≤ G.degree w₂ := (Finset.mem_filter.mp hw₂mem).2
    have hsum2 :
        ∑ w ∈ (G.neighborFinset t).filter (fun w => 5 ≤ G.degree w),
            sigma (G.degree w)
        = sigma (G.degree w₁) + sigma (G.degree w₂) := by
      rw [hpair, Finset.sum_pair hne]
    have hgt : (3 / 2 : ℝ) < sigma (G.degree w₁) + sigma (G.degree w₂) := by
      rw [← hsum2]
      linarith
    rw [hsum2]
    exact sigma_pair_gap hw₁5 hw₂5 hgt

open Classical in
/-- **The sharp weighted heavy ledger** (integer-profile demand):

  `(32/21)·#suppressed ≤ Σ_{deg w ≥ 5} σ(deg w)·|hubTwins w|`. -/
theorem weighted_heavy_ledger_sharp (G : SimpleGraph (Fin n))
    (h3 : ∀ v, 3 ≤ G.degree v) :
    (32 / 21 : ℝ) * ((Finset.univ.filter
          (fun v : Fin n => G.degree v = 3 ∧ 2 < sigS G v)).card : ℝ)
      ≤ ∑ w ∈ Finset.univ.filter (fun w : Fin n => 5 ≤ G.degree w),
          sigma (G.degree w) * ((hubTwins G w).card : ℝ) := by
  set S := Finset.univ.filter
    (fun v : Fin n => G.degree v = 3 ∧ 2 < sigS G v) with hS
  set H := Finset.univ.filter (fun w : Fin n => 5 ≤ G.degree w) with hH
  have hset : ∀ t : Fin n, H.filter (fun w => G.Adj t w)
      = (G.neighborFinset t).filter (fun w => 5 ≤ G.degree w) := by
    intro t
    ext w
    rw [hH]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      SimpleGraph.mem_neighborFinset]
    exact and_comm
  calc (32 / 21 : ℝ) * (S.card : ℝ)
      ≤ ∑ t ∈ S, ∑ w ∈ (G.neighborFinset t).filter (fun w => 5 ≤ G.degree w),
          sigma (G.degree w) := by
        have hb := Finset.card_nsmul_le_sum S
          (fun t => ∑ w ∈ (G.neighborFinset t).filter (fun w => 5 ≤ G.degree w),
            sigma (G.degree w)) ((32 : ℝ) / 21)
          (fun t ht => by
            rw [hS, Finset.mem_filter] at ht
            exact heavy_sigma_into_suppressed_sharp G t h3 ht.2.1 ht.2.2)
        rw [nsmul_eq_mul] at hb
        linarith
    _ = ∑ t ∈ S, ∑ w ∈ H, (if G.Adj t w then sigma (G.degree w) else 0) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [← hset t, Finset.sum_filter]
    _ = ∑ w ∈ H, ∑ t ∈ S, (if G.Adj t w then sigma (G.degree w) else 0) :=
        Finset.sum_comm
    _ ≤ ∑ w ∈ H, sigma (G.degree w) * ((hubTwins G w).card : ℝ) := by
        refine Finset.sum_le_sum fun w hw => ?_
        have hw5 : 5 ≤ G.degree w := by
          rw [hH] at hw
          exact (Finset.mem_filter.mp hw).2
        have hσ : (0 : ℝ) ≤ sigma (G.degree w) := sigma_nonneg (h3 w)
        have hcard : (S.filter (fun t => G.Adj t w)).card
            ≤ (hubTwins G w).card := by
          refine Finset.card_le_card fun t ht => ?_
          rw [hS] at ht
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
          exact mem_hubTwins_iff.mpr ⟨ht.2.symm, ht.1.1⟩
        calc ∑ t ∈ S, (if G.Adj t w then sigma (G.degree w) else 0)
            = ∑ t ∈ S.filter (fun t => G.Adj t w), sigma (G.degree w) :=
              (Finset.sum_filter _ _).symm
          _ = ((S.filter (fun t => G.Adj t w)).card : ℝ)
                * sigma (G.degree w) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ((hubTwins G w).card : ℝ) * sigma (G.degree w) := by
              have : ((S.filter (fun t => G.Adj t w)).card : ℝ)
                  ≤ ((hubTwins G w).card : ℝ) := by exact_mod_cast hcard
              exact mul_le_mul_of_nonneg_right this hσ
          _ = sigma (G.degree w) * ((hubTwins G w).card : ℝ) := mul_comm _ _

end ACMax

/-! ## The D1 summation: the heavy ledger absorbed by the excess

The σ-weighted heavy sum `Σ_{deg w ≥ 5} σ(deg w)·|hubTwins w|` is at most
`(4/3)·X + 5703` (`X = excessX`), via a three-way partition of the heavy set:
parts `A` (`a + 3 ≤ d`) and `B` (`d ≥ 13`) absorb into `(4/3)·excessX` by the
pointwise `sigma_mul_le_four_thirds`; the capped part `C` (`5 ≤ d ≤ 12`) is
bounded in cardinality by the adjacency-tolerant class cap `class_cap_with_adj`
(`|T| ≤ 1 + i₀ + 2a ≤ 27`, anchoring the double count with `σ₀ = 1`), giving
`|C| ≤ 528` and `Σ_C ≤ 5703`. Chaining with `weighted_heavy_ledger` yields
`suppressed_card_le` : `(3/2)·#S ≤ (4/3)·excessX + 5703`. -/

namespace ACMax

open Finset

variable {V : Type*} [Fintype V]

/-! ## Small vocabulary lemmas -/

open Classical in
/-- The twin count never exceeds the degree: `|D3(g)| ≤ deg g`. -/
theorem hubTwins_card_le_degree (G : SimpleGraph V) (g : V) :
    (hubTwins G g).card ≤ G.degree g := by
  have h := card_hubTwins_add_intDeg G g
  omega

open Classical in
/-- A nonzero `mCross` produces an explicit cross edge: a private twin `t` of
`g` against `h` adjacent to a private twin `t'` of `h` against `g`. -/
theorem exists_cross_edge_of_mCross_ne_zero (G : SimpleGraph V) (g h : V)
    (hmx : mCross G g h ≠ 0) :
    ∃ t ∈ privTwins G g h, ∃ t' ∈ privTwins G h g, G.Adj t t' := by
  unfold mCross at hmx
  obtain ⟨t, ht, hcard⟩ : ∃ t ∈ privTwins G g h,
      (G.neighborFinset t ∩ privTwins G h g).card ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hmx (Finset.sum_eq_zero hall)
  obtain ⟨t', ht'⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hcard)
  rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at ht'
  exact ⟨t, ht, t', ht'.2, ht'.1⟩

/-! ## The adjacency-tolerant class cap -/

open Classical in
/-- **Adjacency-tolerant class cap.**  On the `SeaFatBoundary`, a class `T` of
hubs with `deg ≥ 4`, `intDeg ≤ i₀ ≤ 2`, the same twin count `a`, and vanishing
pairwise `mCross` satisfies `|T| ≤ 1 + i₀ + 2a`: anchored at any `g₀ ∈ T`, at
most `i₀` partners are adjacent to `g₀` (they are non-degree-3 neighbours) and
at most `2a` are nonadjacent (each shares `≥ 3 − i₀ ≥ 1` twins with `g₀`, and
each of `g₀`'s `a` twins serves at most `2` partners). -/
theorem class_cap_with_adj (n : ℕ) (G : SimpleGraph (Fin n))
    (hb : SeaFatBoundary G) (a i₀ : ℕ) (hi : i₀ ≤ 2) (T : Finset (Fin n))
    (hT : ∀ g ∈ T, 4 ≤ G.degree g ∧ intDeg G g ≤ i₀ ∧ (hubTwins G g).card = a)
    (hmx : ∀ g ∈ T, ∀ h ∈ T, g ≠ h → mCross G g h = 0) :
    T.card ≤ 1 + i₀ + 2 * a := by
  rcases T.eq_empty_or_nonempty with rfl | ⟨g₀, hg₀⟩
  · simp
  obtain ⟨hg4, hig, hag⟩ := hT g₀ hg₀
  -- split the partners by adjacency to the anchor
  have hsplit : ((T.erase g₀).filter (fun x => G.Adj g₀ x)).card
      + ((T.erase g₀).filter (fun x => ¬G.Adj g₀ x)).card
      = (T.erase g₀).card :=
    Finset.card_filter_add_card_filter_not _
  -- adjacent partners are non-degree-3 neighbours of the anchor
  have hadj_le : ((T.erase g₀).filter (fun x => G.Adj g₀ x)).card ≤ i₀ := by
    -- adjacent partners land in `N(g₀) \ D3(g₀)`, of size `intDeg g₀`
    have hTwinSub : hubTwins G g₀ ⊆ G.neighborFinset g₀ := fun t ht =>
      (SimpleGraph.mem_neighborFinset G g₀ t).mpr (mem_hubTwins_iff.mp ht).1
    have hsub : (T.erase g₀).filter (fun x => G.Adj g₀ x)
        ⊆ G.neighborFinset g₀ \ hubTwins G g₀ := by
      intro x hx
      rw [Finset.mem_filter, Finset.mem_erase] at hx
      obtain ⟨⟨hne, hxT⟩, hadj⟩ := hx
      obtain ⟨hx4, -, -⟩ := hT x hxT
      rw [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset]
      refine ⟨hadj, fun hmem => ?_⟩
      have := (mem_hubTwins_iff.mp hmem).2
      omega
    have hcards : (G.neighborFinset g₀ \ hubTwins G g₀).card
        = G.degree g₀ - (hubTwins G g₀).card := by
      rw [Finset.card_sdiff_of_subset hTwinSub, G.card_neighborFinset_eq_degree]
    have hle := Finset.card_le_card hsub
    have hsum := card_hubTwins_add_intDeg G g₀
    omega
  -- nonadjacent partners: forced sharing + the anchored double count
  have hnon_le : ((T.erase g₀).filter (fun x => ¬G.Adj g₀ x)).card ≤ 2 * a := by
    set Tn : Finset (Fin n) := (T.erase g₀).filter (fun x => ¬G.Adj g₀ x)
      with hTn
    have hg₀Tn : g₀ ∉ Tn := by
      rw [hTn]
      intro hmem
      exact Finset.notMem_erase g₀ T (Finset.mem_of_mem_filter _ hmem)
    have hshare : ∀ x ∈ (insert g₀ Tn).erase g₀,
        1 ≤ (sharedTwins G g₀ x).card := by
      intro x hx
      rw [Finset.erase_insert hg₀Tn, hTn, Finset.mem_filter,
        Finset.mem_erase] at hx
      obtain ⟨⟨hne, hxT⟩, hnadj⟩ := hx
      obtain ⟨hx4, hix, hax⟩ := hT x hxT
      have hs := sfb_forces_sharing_of_intDeg_le G hb g₀ x i₀ (Ne.symm hne)
        hg4 hx4 (by rw [hag, hax]) hig hix
        (hmx g₀ hg₀ x hxT (Ne.symm hne)) hnadj
      omega
    have hcount := anchored_sharing_count G g₀ (insert g₀ Tn) 1 a hshare hag
      (fun t ht => (mem_hubTwins_iff.mp ht).2)
    rw [Finset.erase_insert hg₀Tn] at hcount
    omega
  have hcarde : (T.erase g₀).card = T.card - 1 := Finset.card_erase_of_mem hg₀
  have hpos : 1 ≤ T.card := Finset.card_pos.mpr ⟨g₀, hg₀⟩
  omega

/-! ## The capped-part cardinality bound -/

/-! ## The D1 summation -/

/-! ## Corollary: the suppressed set is absorbed by the excess -/

end ACMax

/-! ## Pair coverage of usable degree-3 vertices

On the compact cell two distinct usable vertices must be adjacent, share a
neighbour, or carry an edge between their neighbourhoods (else they form a usable
far pair). Double-counting the ordered pairs of `U₃ = {v : deg v = 3 ∧ sigS v ≤ 2}`
by mechanism yields `usable_deg3_pair_coverage`:
`|U₃|·(|U₃|−1) ≤ mIncidence G + Σ_w a(w)(a(w)−1) + Σ_w Σ_{w'∈N(w)} a(w)·a(w')`,
with `a(w) = |hubTwins G w|`. -/

namespace ACMax

open Finset

open Classical in
/-- On the compact cell (`¬HasUsableFarPair`), two distinct usable vertices are
adjacent, share a common neighbour, or carry an edge between their
neighbourhoods: the negation of all three would exhibit a usable clean far
pair. -/
theorem usable_pair_mechanism {n : ℕ} (G : SimpleGraph (Fin n))
    (hcpt : ¬HasUsableFarPair G) (t t' : Fin n) (hne : t ≠ t')
    (ht : sigS G t ≤ 2) (ht' : sigS G t' ≤ 2) :
    G.Adj t t' ∨ (∃ w, G.Adj t w ∧ G.Adj t' w) ∨
      (∃ w w', G.Adj t w ∧ G.Adj t' w' ∧ G.Adj w w') := by
  by_cases hadj : G.Adj t t'
  · exact Or.inl hadj
  by_cases hcom : ∃ w, G.Adj t w ∧ G.Adj t' w
  · exact Or.inr (Or.inl hcom)
  by_cases hnn : ∃ w w', G.Adj t w ∧ G.Adj t' w' ∧ G.Adj w w'
  · exact Or.inr (Or.inr hnn)
  exact absurd ⟨t, t', hne, hadj, fun w hw => hcom ⟨w, hw⟩,
    fun w w' hw hw' hww' => hnn ⟨w, w', hw, hw', hww'⟩, ht, ht'⟩ hcpt

/-! ## The mid-leaves Moore bound (`Δ ≤ 8`)

On the compact cell the set of *mid leaves*
`L₈ = {u : deg u = 3 ∧ sigS u ≤ 2 ∧ every neighbour has deg ≤ 8}` has at most
`143` elements — the `Δ = 8` Moore bound. Fixing one mid leaf `u₀`, every usable
vertex is adjacent to `u₀`, shares a neighbour, or sits at the far end of an edge
out of `N(u₀)` through a `≤ 8`-degree middle vertex, so `L₈` sits in a
parent-erased radius-2 ball of volume `≤ 1 + 1 + 3·5 + 21·6 = 143`. The corollary
`usable_deg3_split_mid` splits the usable degree-3 count into this mid part and
the big-neighbour (`deg ≥ 9`) population, whose partners are degree-`≤ 4` by
`usable_twin_partners_deg_le_four`. -/

end ACMax

/-! ## The mid-usable Moore bound and the `W₅` split

The `W₅` class (usable degree-5 hubs with exactly two twins) splits by its
heaviest neighbour: the all-neighbours-`≤ 8` part is Moore-bounded by
`1 + 5 + 5·7 + 5·7·7 = 286` (`mid_usable5_card_le`), and the remainder is the
big-hub cloud class `W₅ᵇ`. `w5_card_split` records `N₅ ≤ 286 + N₅ᵇ`. -/

namespace ACMax

open Finset

variable {n : ℕ}

open Classical in
/-- **Mid-usable Moore bound.**  On the compact cell, the set of degree-5
usable vertices all of whose neighbours have degree `≤ 8` has at most `286`
elements: every member mediates with a fixed member `u₀` within the
parent-erased ball `1 + 5 + 5·7 + 5·7·7 = 286` around `u₀`. -/
theorem mid_usable5_card_le (n : ℕ) (G : SimpleGraph (Fin n))
    (hcpt : ¬HasUsableFarPair G) :
    (Finset.univ.filter (fun u : Fin n =>
      G.degree u = 5 ∧ sigS G u ≤ 2 ∧ (hubTwins G u).card = 2 ∧
      ∀ x ∈ G.neighborFinset u, G.degree x ≤ 8)).card ≤ 206 := by
  set L₈ : Finset (Fin n) := Finset.univ.filter (fun u : Fin n =>
      G.degree u = 5 ∧ sigS G u ≤ 2 ∧ (hubTwins G u).card = 2 ∧
      ∀ x ∈ G.neighborFinset u, G.degree x ≤ 8) with hL8def
  rcases L₈.eq_empty_or_nonempty with hemp | ⟨u₀, hu0⟩
  · rw [hemp]; simp
  have hu0props : G.degree u₀ = 5 ∧ sigS G u₀ ≤ 2 ∧
      (hubTwins G u₀).card = 2 ∧
      ∀ x ∈ G.neighborFinset u₀, G.degree x ≤ 8 := by
    rw [hL8def, Finset.mem_filter] at hu0
    exact hu0.2
  set A : Finset (Fin n) := G.neighborFinset u₀ with hAdef
  set B : Finset (Fin n) := A.biUnion (fun a => (G.neighborFinset a).erase u₀)
    with hBdef
  set C : Finset (Fin n) := A.biUnion (fun a =>
      ((G.neighborFinset a).erase u₀).biUnion (fun b =>
        if G.degree b ≤ 8 then (G.neighborFinset b).erase a else ∅)) with hCdef
  set S : Finset (Fin n) := insert u₀ (A ∪ B ∪ C) with hSdef
  have hsub : L₈ ⊆ S := by
    intro u hu
    rw [hL8def, Finset.mem_filter] at hu
    obtain ⟨-, hdeg, hsig, -, hmidu⟩ := hu
    rw [hSdef]
    rcases eq_or_ne u u₀ with rfl | hne
    · exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      rcases usable_pair_mechanism G hcpt u₀ u hne.symm hu0props.2.1 hsig with
        hadj | ⟨w, hw0, hwu⟩ | ⟨w, w', hw0, hwu', hww'⟩
      · apply Finset.mem_union_left
        apply Finset.mem_union_left
        rw [hAdef]
        exact (G.mem_neighborFinset u₀ u).mpr hadj
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        rw [hBdef, hAdef]
        refine Finset.mem_biUnion.mpr ⟨w, (G.mem_neighborFinset u₀ w).mpr hw0, ?_⟩
        exact Finset.mem_erase.mpr ⟨hne, (G.mem_neighborFinset w u).mpr hwu.symm⟩
      · by_cases hw'u₀ : w' = u₀
        · apply Finset.mem_union_left
          apply Finset.mem_union_left
          rw [hAdef]
          exact (G.mem_neighborFinset u₀ u).mpr (hw'u₀ ▸ hwu').symm
        by_cases huw : u = w
        · apply Finset.mem_union_left
          apply Finset.mem_union_left
          rw [hAdef]
          exact huw ▸ (G.mem_neighborFinset u₀ w).mpr hw0
        apply Finset.mem_union_right
        rw [hCdef, hAdef]
        refine Finset.mem_biUnion.mpr ⟨w, (G.mem_neighborFinset u₀ w).mpr hw0, ?_⟩
        refine Finset.mem_biUnion.mpr ⟨w', Finset.mem_erase.mpr
          ⟨hw'u₀, (G.mem_neighborFinset w w').mpr hww'⟩, ?_⟩
        have hdegw' : G.degree w' ≤ 8 :=
          hmidu w' ((G.mem_neighborFinset u w').mpr hwu')
        rw [ite_eq_left hdegw']
        exact Finset.mem_erase.mpr ⟨huw, (G.mem_neighborFinset w' u).mpr hwu'.symm⟩
  have hA : A.card = 5 := by
    rw [hAdef, G.card_neighborFinset_eq_degree]; exact hu0props.1
  have hmid : ∀ a ∈ A, G.degree a ≤ 8 := by rw [hAdef]; exact hu0props.2.2.2
  have hAtwins : (A.filter (fun a => G.degree a = 3)).card = 2 := by
    have h2 : A.filter (fun a => G.degree a = 3) = hubTwins G u₀ := by
      rw [hAdef, hubTwins]
      ext t
      simp only [Finset.mem_filter, Finset.mem_inter, mem_deg3Set]
    rw [h2]
    exact hu0props.2.2.1
  have htermA : ∀ a ∈ A, ((G.neighborFinset a).erase u₀).card
      = G.degree a - 1 := by
    intro a ha
    have hu₀a : u₀ ∈ G.neighborFinset a := by
      rw [SimpleGraph.mem_neighborFinset]
      exact ((G.mem_neighborFinset u₀ a).mp (hAdef ▸ ha)).symm
    rw [Finset.card_erase_of_mem hu₀a, G.card_neighborFinset_eq_degree]
  have hAother : (A.filter (fun a => ¬G.degree a = 3)).card = 3 := by
    have hsplit2 := Finset.card_filter_add_card_filter_not
      (s := A) (p := fun a => G.degree a = 3)
    have hA5 : A.card = 5 := hA
    omega
  have hB : B.card ≤ 25 := by
    rw [hBdef]
    calc (A.biUnion (fun a => (G.neighborFinset a).erase u₀)).card
        ≤ ∑ a ∈ A, ((G.neighborFinset a).erase u₀).card :=
          Finset.card_biUnion_le
      _ = ∑ a ∈ A.filter (fun a => G.degree a = 3),
            ((G.neighborFinset a).erase u₀).card
          + ∑ a ∈ A.filter (fun a => ¬G.degree a = 3),
            ((G.neighborFinset a).erase u₀).card :=
          (Finset.sum_filter_add_sum_filter_not A _ _).symm
      _ ≤ ∑ _a ∈ A.filter (fun a => G.degree a = 3), 2
          + ∑ _a ∈ A.filter (fun a => ¬G.degree a = 3), 7 := by
          refine Nat.add_le_add (Finset.sum_le_sum fun a ha => ?_)
            (Finset.sum_le_sum fun a ha => ?_)
          · rw [Finset.mem_filter] at ha
            rw [htermA a ha.1, ha.2]
          · rw [Finset.mem_filter] at ha
            rw [htermA a ha.1]
            have := hmid a ha.1
            omega
      _ = (A.filter (fun a => G.degree a = 3)).card * 2
          + (A.filter (fun a => ¬G.degree a = 3)).card * 7 := by
          rw [Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
      _ ≤ 25 := by
          rw [hAtwins, hAother]
  have hInner : ∀ a ∈ A,
      (((G.neighborFinset a).erase u₀).biUnion (fun b =>
        if G.degree b ≤ 8 then (G.neighborFinset b).erase a else ∅)).card ≤ (G.degree a - 1) * 7
          := by
    intro a ha
    have hterm : ∀ b ∈ (G.neighborFinset a).erase u₀,
        (if G.degree b ≤ 8 then (G.neighborFinset b).erase a
         else (∅ : Finset (Fin n))).card ≤ 7 := by
      intro b hb
      by_cases hb8 : G.degree b ≤ 8
      · have hab : a ∈ G.neighborFinset b := by
          rw [SimpleGraph.mem_neighborFinset]
          exact ((G.mem_neighborFinset a b).mp (Finset.mem_of_mem_erase hb)).symm
        rw [ite_eq_left hb8, Finset.card_erase_of_mem hab,
          G.card_neighborFinset_eq_degree]
        omega
      · rw [ite_eq_right hb8, Finset.card_empty]; omega
    calc (((G.neighborFinset a).erase u₀).biUnion (fun b =>
          if G.degree b ≤ 8 then (G.neighborFinset b).erase a else ∅)).card
        ≤ ∑ b ∈ (G.neighborFinset a).erase u₀,
            (if G.degree b ≤ 8 then (G.neighborFinset b).erase a
             else (∅ : Finset (Fin n))).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _b ∈ (G.neighborFinset a).erase u₀, 7 := Finset.sum_le_sum hterm
      _ = ((G.neighborFinset a).erase u₀).card * 7 := by
          rw [Finset.sum_const, smul_eq_mul]
      _ = (G.degree a - 1) * 7 := by rw [htermA a ha]
  have hC : C.card ≤ 175 := by
    rw [hCdef]
    calc (A.biUnion (fun a =>
          ((G.neighborFinset a).erase u₀).biUnion (fun b =>
            if G.degree b ≤ 8 then (G.neighborFinset b).erase a else ∅))).card
        ≤ ∑ a ∈ A, (((G.neighborFinset a).erase u₀).biUnion (fun b =>
            if G.degree b ≤ 8 then (G.neighborFinset b).erase a else ∅)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ a ∈ A, (G.degree a - 1) * 7 := Finset.sum_le_sum hInner
      _ = ∑ a ∈ A.filter (fun a => G.degree a = 3), (G.degree a - 1) * 7
          + ∑ a ∈ A.filter (fun a => ¬G.degree a = 3), (G.degree a - 1) * 7 :=
          (Finset.sum_filter_add_sum_filter_not A _ _).symm
      _ ≤ ∑ _a ∈ A.filter (fun a => G.degree a = 3), 14
          + ∑ _a ∈ A.filter (fun a => ¬G.degree a = 3), 49 := by
          refine Nat.add_le_add (Finset.sum_le_sum fun a ha => ?_)
            (Finset.sum_le_sum fun a ha => ?_)
          · rw [Finset.mem_filter] at ha
            rw [ha.2]
          · rw [Finset.mem_filter] at ha
            have := hmid a ha.1
            have h1 : G.degree a - 1 ≤ 7 := by omega
            calc (G.degree a - 1) * 7 ≤ 7 * 7 := Nat.mul_le_mul_right 7 h1
              _ = 49 := by norm_num
      _ = (A.filter (fun a => G.degree a = 3)).card * 14
          + (A.filter (fun a => ¬G.degree a = 3)).card * 49 := by
          rw [Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
      _ ≤ 175 := by
          rw [hAtwins, hAother]
  have hScard : S.card ≤ 206 := by
    rw [hSdef]
    have h1 : (A ∪ B ∪ C).card ≤ (A ∪ B).card + C.card := Finset.card_union_le _ _
    have h2 : (A ∪ B).card ≤ A.card + B.card := Finset.card_union_le _ _
    have h3 : (insert u₀ (A ∪ B ∪ C)).card ≤ (A ∪ B ∪ C).card + 1 :=
      Finset.card_insert_le _ _
    omega
  calc L₈.card ≤ S.card := Finset.card_le_card hsub
    _ ≤ 206 := hScard

open Classical in
/-- **The `W₅` split**: the usable degree-5 two-twin class is covered by the
mid-usable Moore class together with the big-hub cloud class `W₅ᵇ`:

  `N₅ ≤ 206 + N₅ᵇ`. -/
theorem w5_card_split (n : ℕ) (G : SimpleGraph (Fin n))
    (hcpt : ¬HasUsableFarPair G) :
    ((Finset.univ.filter (fun w : Fin n =>
        G.degree w = 5 ∧ sigS G w ≤ 2 ∧ (hubTwins G w).card = 2)).card : ℝ)
      ≤ 206 + ((Finset.univ.filter (fun w : Fin n =>
          G.degree w = 5 ∧ sigS G w ≤ 2 ∧ (hubTwins G w).card = 2
            ∧ ∃ x ∈ G.neighborFinset w, 9 ≤ G.degree x)).card : ℝ) := by
  classical
  have hsub : Finset.univ.filter (fun w : Fin n =>
        G.degree w = 5 ∧ sigS G w ≤ 2 ∧ (hubTwins G w).card = 2)
      ⊆ Finset.univ.filter (fun u : Fin n =>
          G.degree u = 5 ∧ sigS G u ≤ 2 ∧ (hubTwins G u).card = 2 ∧
          ∀ x ∈ G.neighborFinset u, G.degree x ≤ 8)
        ∪ Finset.univ.filter (fun w : Fin n =>
          G.degree w = 5 ∧ sigS G w ≤ 2 ∧ (hubTwins G w).card = 2
            ∧ ∃ x ∈ G.neighborFinset w, 9 ≤ G.degree x) := by
    intro w hw
    rw [Finset.mem_filter] at hw
    obtain ⟨-, hd, hs, ha⟩ := hw
    by_cases hbig : ∃ x ∈ G.neighborFinset w, 9 ≤ G.degree x
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ w, hd, hs, ha, hbig⟩)
    · refine Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ w, hd, hs, ha, fun x hx => ?_⟩)
      by_contra hcon
      exact hbig ⟨x, hx, by omega⟩
  have hcard := Finset.card_le_card hsub
  have hcard2 := le_trans hcard (Finset.card_union_le _ _)
  have hmoore := mid_usable5_card_le n G hcpt
  have : (Finset.univ.filter (fun w : Fin n =>
        G.degree w = 5 ∧ sigS G w ≤ 2 ∧ (hubTwins G w).card = 2)).card
      ≤ 206 + (Finset.univ.filter (fun w : Fin n =>
          G.degree w = 5 ∧ sigS G w ≤ 2 ∧ (hubTwins G w).card = 2
            ∧ ∃ x ∈ G.neighborFinset w, 9 ≤ G.degree x)).card := by
    omega
  exact_mod_cast this

end ACMax

/-! ## The sharpened mid-leaves Moore bound

Sharpens `|L₈| ≤ 143` to `|L₈| ≤ 108`. Since the base mid leaf `u₀` is itself
usable, `Σσ_{u₀} = σ(d₁) + σ(d₂) + σ(d₃) ≤ 2` caps the neighbour-degree sum
`d₁ + d₂ + d₃ ≤ 19` (maximiser `{8,8,3}`). As the two expansion layers grow
linearly in the neighbour degrees, the ball volume is
`1 + 1 + Σ(dᵢ − 3) + Σ 6(dᵢ − 1) = 7·Σdᵢ − 25 ≤ 108` (`mid_leaves_card_le_sharp`).
`usable_deg3_split_mid_sharp` is the drop-in split (extra `min degree ≥ 3`
hypothesis, from `ResidualCore.min_degree`). -/

namespace ACMax

open Finset

open Classical in
/-- **The `σ` integer program.**  Three neighbour degrees in `[3,8]` whose slot
values sum to `≤ 2` have degree sum `≤ 19` — the `{8,8,3}` maximiser
(`σ = 5/6+5/6+0 = 5/3`).  `{8,8,4}` already costs `13/6 > 2`. -/
theorem sigma_deg_triple_sum_le {da db dc : ℕ}
    (ha3 : 3 ≤ da) (ha8 : da ≤ 8) (hb3 : 3 ≤ db) (hb8 : db ≤ 8)
    (hc3 : 3 ≤ dc) (hc8 : dc ≤ 8)
    (hs : sigma da + sigma db + sigma dc ≤ 2) :
    da + db + dc ≤ 19 := by
  interval_cases da <;> interval_cases db <;> interval_cases dc <;>
    first
      | omega
      | (exfalso; revert hs; norm_num [sigma])

open Classical in
/-- **The neighbour-degree cap.**  A usable degree-3 vertex `u` (`sigS u ≤ 2`)
whose neighbours all have degree `≤ 8`, in a graph of minimum degree `≥ 3`, has
neighbour-degree sum `≤ 19`. -/
theorem nbr_deg_sum_le_nineteen (n : ℕ) (G : SimpleGraph (Fin n))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (u : Fin n) (hdeg : G.degree u = 3) (hsig : sigS G u ≤ 2)
    (hmid : ∀ x ∈ G.neighborFinset u, G.degree x ≤ 8) :
    ∑ x ∈ G.neighborFinset u, G.degree x ≤ 19 := by
  have hcard : (G.neighborFinset u).card = 3 := by
    rw [G.card_neighborFinset_eq_degree]; exact hdeg
  obtain ⟨a, b, c, hab, hac, hbc, hset⟩ := Finset.card_eq_three.mp hcard
  have ha : a ∈ G.neighborFinset u := by rw [hset]; simp
  have hb : b ∈ G.neighborFinset u := by rw [hset]; simp
  have hc : c ∈ G.neighborFinset u := by rw [hset]; simp
  have hexp : sigS G u
      = sigma (G.degree a) + sigma (G.degree b) + sigma (G.degree c) := by
    unfold sigS
    rw [hset, Finset.sum_insert (by simp [hab, hac]),
      Finset.sum_insert (by simp [hbc]), Finset.sum_singleton]
    ring
  have hsig3 : sigma (G.degree a) + sigma (G.degree b) + sigma (G.degree c) ≤ 2 := by
    rw [← hexp]; exact hsig
  have hdsum : ∑ x ∈ G.neighborFinset u, G.degree x
      = G.degree a + G.degree b + G.degree c := by
    rw [hset, Finset.sum_insert (by simp [hab, hac]),
      Finset.sum_insert (by simp [hbc]), Finset.sum_singleton]
    omega
  rw [hdsum]
  exact sigma_deg_triple_sum_le (h3 a) (hmid a ha) (h3 b) (hmid b hb)
    (h3 c) (hmid c hc) hsig3

open Classical in
private theorem mid_leaves_card_le_sharp_hsub : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (_ :
  ¬HasUsableFarPair G)
  (L₈ : Finset (Fin n)) (_ : L₈ = (Finset.univ.filter fun u => G.degree u = 3 ∧ sigS G u ≤ 2
    ∧ ∀ x ∈ G.neighborFinset u, G.degree x ≤ 8))
  (u₀ : Fin n) (_ : u₀ ∈ L₈),
  let A := G.neighborFinset u₀;
  ∀ (_ : G.degree u₀ = 3 ∧ sigS G u₀ ≤ 2 ∧ ∀ x ∈ A, G.degree x ≤ 8) (_ : A =
    G.neighborFinset u₀),
    let B := A.biUnion fun a => (G.neighborFinset a).erase u₀;
    ∀ (_ : B = A.biUnion fun a => (G.neighborFinset a).erase u₀),
      let C :=
        A.biUnion fun a =>
          ((G.neighborFinset a).erase u₀).biUnion fun b => if G.degree b ≤ 8 then
            (G.neighborFinset b).erase a else ∅;
      ∀
        (_ :
          C =
            A.biUnion fun a =>
              ((G.neighborFinset a).erase u₀).biUnion fun b =>
                if G.degree b ≤ 8 then (G.neighborFinset b).erase a else ∅),
        let S := insert u₀ (A ∪ B ∪ C);
        ∀ (_ : S = insert u₀ (A ∪ B ∪ C)) (_ : #A = 3) (x y z : Fin n) (_ : A = {x,
          y, z})
          (_ : ∑ a ∈ A, G.degree a ≤ 19), L₈ ⊆ S := by
  classical
  intro n G hcpt L₈ hL8def u₀ hu0 A hu0props hAdef B hBdef C hCdef S hSdef hAcard x y z hAset
    hDsum u hu
  rw [hL8def, Finset.mem_filter] at hu
  obtain ⟨-, hdeg, hsig, hmidu⟩ := hu
  rw [hSdef]
  rcases eq_or_ne u u₀ with rfl | hne
  · exact Finset.mem_insert_self _ _
  · apply Finset.mem_insert_of_mem
    rcases usable_pair_mechanism G hcpt u₀ u hne.symm hu0props.2.1 hsig with
      hadj | ⟨w, hw0, hwu⟩ | ⟨w, w', hw0, hwu', hww'⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      rw [hAdef]
      exact (G.mem_neighborFinset u₀ u).mpr hadj
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      rw [hBdef, hAdef]
      refine Finset.mem_biUnion.mpr ⟨w, (G.mem_neighborFinset u₀ w).mpr hw0, ?_⟩
      exact Finset.mem_erase.mpr ⟨hne, (G.mem_neighborFinset w u).mpr hwu.symm⟩
    · by_cases hw'u₀ : w' = u₀
      · apply Finset.mem_union_left
        apply Finset.mem_union_left
        rw [hAdef]
        exact (G.mem_neighborFinset u₀ u).mpr (hw'u₀ ▸ hwu').symm
      by_cases huw : u = w
      · apply Finset.mem_union_left
        apply Finset.mem_union_left
        rw [hAdef]
        exact huw ▸ (G.mem_neighborFinset u₀ w).mpr hw0
      apply Finset.mem_union_right
      rw [hCdef, hAdef]
      refine Finset.mem_biUnion.mpr ⟨w, (G.mem_neighborFinset u₀ w).mpr hw0, ?_⟩
      refine Finset.mem_biUnion.mpr ⟨w', Finset.mem_erase.mpr
        ⟨hw'u₀, (G.mem_neighborFinset w w').mpr hww'⟩, ?_⟩
      have hdegw' : G.degree w' ≤ 8 :=
        hmidu w' ((G.mem_neighborFinset u w').mpr hwu')
      rw [ite_eq_left hdegw']
      exact Finset.mem_erase.mpr ⟨huw, (G.mem_neighborFinset w' u).mpr hwu'.symm⟩

open Classical in
private theorem mid_leaves_card_le_sharp_hLC : ∀ (n : ℕ) (G : SimpleGraph (Fin n))
  (_ : ∀ (w : Fin n), G.degree w ≤ 8 → #({t ∈ G.neighborFinset w | G.degree t = 3}) ≤
    G.degree w - 2),
  let L₈ := (Finset.univ.filter fun u => G.degree u = 3 ∧ sigS G u ≤ 2 ∧ ∀ x ∈ G.neighborFinset u,
    G.degree x ≤ 8);
  ∀ (u₀ : Fin n) (A : Finset (Fin n)) (_ : A = G.neighborFinset u₀),
    let C :=
      A.biUnion fun a =>
        ((G.neighborFinset a).erase u₀).biUnion fun b => if G.degree b ≤ 8 then (G.neighborFinset
          b).erase a else ∅;
    ∀
      (_ :
        C =
          A.biUnion fun a =>
            ((G.neighborFinset a).erase u₀).biUnion fun b => if G.degree b ≤ 8 then
              (G.neighborFinset b).erase a else ∅)
      (_ : ∀ u ∈ L₈, G.degree u = 3), #(L₈ ∩ C) ≤ ∑ a ∈ A, (G.degree a - 1) * 6 := by
  classical
  intro n G hd3cap L₈ u₀ A hAdef C hCdef hL3
  rw [hCdef]
  calc (L₈ ∩ A.biUnion (fun a =>
        ((G.neighborFinset a).erase u₀).biUnion (fun b =>
          if G.degree b ≤ 8 then (G.neighborFinset b).erase a else ∅))).card
      ≤ ∑ a ∈ A, (L₈ ∩ ((G.neighborFinset a).erase u₀).biUnion (fun b =>
          if G.degree b ≤ 8 then (G.neighborFinset b).erase a else ∅)).card := by
        rw [Finset.inter_biUnion]
        exact Finset.card_biUnion_le
    _ ≤ ∑ a ∈ A, (G.degree a - 1) * 6 := by
        refine Finset.sum_le_sum fun a ha => ?_
        have hu₀a : u₀ ∈ G.neighborFinset a := by
          rw [SimpleGraph.mem_neighborFinset]
          exact ((G.mem_neighborFinset u₀ a).mp (hAdef ▸ ha)).symm
        have hEr : ((G.neighborFinset a).erase u₀).card = G.degree a - 1 := by
          rw [Finset.card_erase_of_mem hu₀a, G.card_neighborFinset_eq_degree]
        calc (L₈ ∩ ((G.neighborFinset a).erase u₀).biUnion (fun b =>
              if G.degree b ≤ 8 then (G.neighborFinset b).erase a
              else ∅)).card
            ≤ ∑ b ∈ (G.neighborFinset a).erase u₀,
                (L₈ ∩ (if G.degree b ≤ 8 then (G.neighborFinset b).erase a
                  else ∅)).card := by
              rw [Finset.inter_biUnion]
              exact Finset.card_biUnion_le
          _ ≤ ∑ _b ∈ (G.neighborFinset a).erase u₀, 6 := by
              refine Finset.sum_le_sum fun b hb => ?_
              by_cases hb8 : G.degree b ≤ 8
              · rw [ite_eq_left hb8]
                have hsub2 : L₈ ∩ (G.neighborFinset b).erase a
                    ⊆ (G.neighborFinset b).filter
                      (fun t => G.degree t = 3) := by
                  intro t ht
                  rw [Finset.mem_inter] at ht
                  rw [Finset.mem_filter]
                  exact ⟨Finset.mem_of_mem_erase ht.2, hL3 t ht.1⟩
                have := hd3cap b hb8
                calc (L₈ ∩ (G.neighborFinset b).erase a).card
                    ≤ ((G.neighborFinset b).filter
                        (fun t => G.degree t = 3)).card :=
                      Finset.card_le_card hsub2
                  _ ≤ 6 := by omega
              · rw [ite_eq_right hb8]
                simp
          _ = ((G.neighborFinset a).erase u₀).card * 6 := by
              rw [Finset.sum_const, smul_eq_mul]
          _ = (G.degree a - 1) * 6 := by rw [hEr]

open Classical in
/-- **Sharpened mid-leaves Moore bound.**  On the compact cell, in a graph of
minimum degree `≥ 3`, the set of degree-3 usable vertices all of whose
neighbours have degree `≤ 8` has at most `108` elements. -/
theorem mid_leaves_card_le_sharp (n : ℕ) (G : SimpleGraph (Fin n))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (hcpt : ¬HasUsableFarPair G)
    (hblk : ∀ w : Fin n, G.degree w ≤ 15 →
      (hubTwins G w).card + 2 ≤ G.degree w) :
    (Finset.univ.filter (fun u : Fin n =>
      G.degree u = 3 ∧ sigS G u ≤ 2 ∧
      ∀ x ∈ G.neighborFinset u, G.degree x ≤ 8)).card ≤ 108 := by
  have hd3cap : ∀ w : Fin n, G.degree w ≤ 8 →
      ((G.neighborFinset w).filter (fun t => G.degree t = 3)).card
        ≤ G.degree w - 2 := by
    intro w hw8
    have h1 := hblk w (by omega)
    have h2 : (G.neighborFinset w).filter (fun t => G.degree t = 3)
        = hubTwins G w := by
      rw [hubTwins]
      ext t
      simp only [Finset.mem_filter, Finset.mem_inter, mem_deg3Set]
    rw [h2]
    omega
  set L₈ : Finset (Fin n) := Finset.univ.filter (fun u : Fin n =>
      G.degree u = 3 ∧ sigS G u ≤ 2 ∧
      ∀ x ∈ G.neighborFinset u, G.degree x ≤ 8) with hL8def
  rcases L₈.eq_empty_or_nonempty with hemp | ⟨u₀, hu0⟩
  · rw [hemp]; simp
  -- properties of the chosen mid leaf `u₀`
  have hu0props : G.degree u₀ = 3 ∧ sigS G u₀ ≤ 2 ∧
      ∀ x ∈ G.neighborFinset u₀, G.degree x ≤ 8 := by
    rw [hL8def, Finset.mem_filter] at hu0
    exact hu0.2
  -- the radius-two reach set, in three layers
  set A : Finset (Fin n) := G.neighborFinset u₀ with hAdef
  set B : Finset (Fin n) := A.biUnion (fun a => (G.neighborFinset a).erase u₀)
    with hBdef
  set C : Finset (Fin n) := A.biUnion (fun a =>
      ((G.neighborFinset a).erase u₀).biUnion (fun b =>
        if G.degree b ≤ 8 then (G.neighborFinset b).erase a else ∅)) with hCdef
  set S : Finset (Fin n) := insert u₀ (A ∪ B ∪ C) with hSdef
  -- the three neighbours of `u₀`, and the σ-driven degree-sum cap
  have hAcard : A.card = 3 := by
    rw [hAdef, G.card_neighborFinset_eq_degree]; exact hu0props.1
  obtain ⟨x, y, z, hxy, hxz, hyz, hAset⟩ := Finset.card_eq_three.mp hAcard
  have hDsum : ∑ a ∈ A, G.degree a ≤ 19 := by
    rw [hAdef]
    exact nbr_deg_sum_le_nineteen n G h3 u₀ hu0props.1 hu0props.2.1 hu0props.2.2
  -- CLAIM: every mid leaf lands in the reach set (verbatim from the base bound)
  have hsub :=
      mid_leaves_card_le_sharp_hsub (n := n) (G := G) (hcpt) (L₈ := L₈) (hL8def) (u₀ := u₀) (hu0)
        (hu0props) (hAdef) (hBdef)
        (hCdef) (hSdef) (hAcard) (x := x) (y := y) (z := z) (hAset) (hDsum)
  -- member-counting with the per-neighbour degrees kept explicit
  have hmid : ∀ a ∈ A, G.degree a ≤ 8 := by
    rw [hAdef]
    exact hu0props.2.2
  have hL3 : ∀ u ∈ L₈, G.degree u = 3 := by
    intro u hu
    rw [hL8def, Finset.mem_filter] at hu
    exact hu.2.1
  have hLA : (L₈ ∩ A).card ≤ 1 := by
    have hsub2 : L₈ ∩ A ⊆ (G.neighborFinset u₀).filter
        (fun t => G.degree t = 3) := by
      intro t ht
      rw [Finset.mem_inter] at ht
      rw [Finset.mem_filter]
      exact ⟨hAdef ▸ ht.2, hL3 t ht.1⟩
    have := hd3cap u₀ (by omega)
    calc (L₈ ∩ A).card
        ≤ ((G.neighborFinset u₀).filter (fun t => G.degree t = 3)).card :=
          Finset.card_le_card hsub2
      _ ≤ 1 := by
          have h3' := hu0props.1
          omega
  -- layer B: neighbour `a` holds `≤ deg a − 3` mid leaves (erasing the deg-3 root)
  have hLB : (L₈ ∩ B).card ≤ ∑ a ∈ A, (G.degree a - 3) := by
    rw [hBdef]
    calc (L₈ ∩ A.biUnion (fun a => (G.neighborFinset a).erase u₀)).card
        ≤ ∑ a ∈ A, (L₈ ∩ (G.neighborFinset a).erase u₀).card := by
          rw [Finset.inter_biUnion]
          exact Finset.card_biUnion_le
      _ ≤ ∑ a ∈ A, (G.degree a - 3) := by
          refine Finset.sum_le_sum fun a ha => ?_
          have hu₀mem : u₀ ∈ (G.neighborFinset a).filter
              (fun t => G.degree t = 3) := by
            rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
            exact ⟨((G.mem_neighborFinset u₀ a).mp (hAdef ▸ ha)).symm, hu0props.1⟩
          have hsub2 : L₈ ∩ (G.neighborFinset a).erase u₀
              ⊆ ((G.neighborFinset a).filter (fun t => G.degree t = 3)).erase u₀ := by
            intro t ht
            rw [Finset.mem_inter] at ht
            rw [Finset.mem_erase]
            refine ⟨(Finset.mem_erase.mp ht.2).1, ?_⟩
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_of_mem_erase ht.2, hL3 t ht.1⟩
          have hcard := hd3cap a (hmid a ha)
          calc (L₈ ∩ (G.neighborFinset a).erase u₀).card
              ≤ (((G.neighborFinset a).filter
                  (fun t => G.degree t = 3)).erase u₀).card :=
                Finset.card_le_card hsub2
            _ = ((G.neighborFinset a).filter (fun t => G.degree t = 3)).card - 1 :=
                Finset.card_erase_of_mem hu₀mem
            _ ≤ G.degree a - 3 := by omega
  -- layer C: neighbour `a` expands `deg a − 1` middles, each holding `≤ 6`
  have hLC : (L₈ ∩ C).card ≤ ∑ a ∈ A, (G.degree a - 1) * 6 :=
      mid_leaves_card_le_sharp_hLC (n := n) (G := G) (hd3cap) (u₀ := u₀) (A := A)
        (hAdef) (hCdef) (hL3)
  -- expand the three layer sums and the degree-sum cap over `A = {x,y,z}`
  have eB : ∑ a ∈ A, (G.degree a - 3)
      = (G.degree x - 3) + (G.degree y - 3) + (G.degree z - 3) := by
    rw [hAset, Finset.sum_insert (by simp [hxy, hxz]),
      Finset.sum_insert (by simp [hyz]), Finset.sum_singleton]
    omega
  have eC : ∑ a ∈ A, (G.degree a - 1) * 6
      = (G.degree x - 1) * 6 + (G.degree y - 1) * 6 + (G.degree z - 1) * 6 := by
    rw [hAset, Finset.sum_insert (by simp [hxy, hxz]),
      Finset.sum_insert (by simp [hyz]), Finset.sum_singleton]
    omega
  have eD : ∑ a ∈ A, G.degree a = G.degree x + G.degree y + G.degree z := by
    rw [hAset, Finset.sum_insert (by simp [hxy, hxz]),
      Finset.sum_insert (by simp [hyz]), Finset.sum_singleton]
    omega
  rw [eB] at hLB
  rw [eC] at hLC
  rw [eD] at hDsum
  have hx := h3 x; have hy := h3 y; have hz := h3 z
  -- assemble
  have hcover2 : L₈ = L₈ ∩ S := (Finset.inter_eq_left.mpr hsub).symm
  calc L₈.card = (L₈ ∩ S).card := by rw [← hcover2]
    _ = (L₈ ∩ insert u₀ (A ∪ B ∪ C)).card := by rw [hSdef]
    _ ≤ (insert u₀ ((L₈ ∩ A) ∪ (L₈ ∩ B) ∪ (L₈ ∩ C))).card := by
        refine Finset.card_le_card ?_
        intro t ht
        rw [Finset.mem_inter, Finset.mem_insert] at ht
        obtain ⟨htL, rfl | htm⟩ := ht
        · exact Finset.mem_insert_self _ _
        · refine Finset.mem_insert_of_mem ?_
          rw [Finset.mem_union, Finset.mem_union] at htm ⊢
          rcases htm with (h1 | h2) | h3
          · exact Or.inl (Or.inl (Finset.mem_inter.mpr ⟨htL, h1⟩))
          · exact Or.inl (Or.inr (Finset.mem_inter.mpr ⟨htL, h2⟩))
          · exact Or.inr (Finset.mem_inter.mpr ⟨htL, h3⟩)
    _ ≤ ((L₈ ∩ A) ∪ (L₈ ∩ B) ∪ (L₈ ∩ C)).card + 1 := Finset.card_insert_le _ _
    _ ≤ 108 := by
        have h1 : ((L₈ ∩ A) ∪ (L₈ ∩ B) ∪ (L₈ ∩ C)).card
            ≤ ((L₈ ∩ A) ∪ (L₈ ∩ B)).card + (L₈ ∩ C).card :=
          Finset.card_union_le _ _
        have h2 : ((L₈ ∩ A) ∪ (L₈ ∩ B)).card
            ≤ (L₈ ∩ A).card + (L₈ ∩ B).card := Finset.card_union_le _ _
        omega

open Classical in
/-- The usable degree-3 set splits into the sharpened mid part (`≤ 108` on the
compact cell, min degree `≥ 3`) and the vertices carrying a **big** (`deg ≥ 9`)
neighbour.  Drop-in replacement for `usable_deg3_split_mid` with the improved
constant. -/
theorem usable_deg3_split_mid_sharp (n : ℕ) (G : SimpleGraph (Fin n))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (hcpt : ¬HasUsableFarPair G)
    (hblk : ∀ w : Fin n, G.degree w ≤ 15 →
      (hubTwins G w).card + 2 ≤ G.degree w) :
    (Finset.univ.filter (fun u : Fin n => G.degree u = 3 ∧ sigS G u ≤ 2)).card ≤
      108 + (Finset.univ.filter (fun u : Fin n =>
        G.degree u = 3 ∧ sigS G u ≤ 2 ∧
        ∃ x ∈ G.neighborFinset u, 9 ≤ G.degree x)).card := by
  have hsub :
      (Finset.univ.filter (fun u : Fin n => G.degree u = 3 ∧ sigS G u ≤ 2)) ⊆
        (Finset.univ.filter (fun u : Fin n =>
          G.degree u = 3 ∧ sigS G u ≤ 2 ∧
          ∀ x ∈ G.neighborFinset u, G.degree x ≤ 8)) ∪
        (Finset.univ.filter (fun u : Fin n =>
          G.degree u = 3 ∧ sigS G u ≤ 2 ∧
          ∃ x ∈ G.neighborFinset u, 9 ≤ G.degree x)) := by
    intro u hu
    rw [Finset.mem_filter] at hu
    obtain ⟨-, hdeg, hsig⟩ := hu
    by_cases hall : ∀ x ∈ G.neighborFinset u, G.degree x ≤ 8
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ u, hdeg, hsig, hall⟩)
    · simp only [not_forall, not_le, exists_prop] at hall
      obtain ⟨x, hxmem, hxgt⟩ := hall
      exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ u, hdeg, hsig, ⟨x, hxmem, by omega⟩⟩)
  calc (Finset.univ.filter (fun u : Fin n => G.degree u = 3 ∧ sigS G u ≤ 2)).card
      ≤ ((Finset.univ.filter (fun u : Fin n =>
            G.degree u = 3 ∧ sigS G u ≤ 2 ∧
            ∀ x ∈ G.neighborFinset u, G.degree x ≤ 8)) ∪
          (Finset.univ.filter (fun u : Fin n =>
            G.degree u = 3 ∧ sigS G u ≤ 2 ∧
            ∃ x ∈ G.neighborFinset u, 9 ≤ G.degree x))).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ.filter (fun u : Fin n =>
            G.degree u = 3 ∧ sigS G u ≤ 2 ∧
            ∀ x ∈ G.neighborFinset u, G.degree x ≤ 8)).card +
        (Finset.univ.filter (fun u : Fin n =>
            G.degree u = 3 ∧ sigS G u ≤ 2 ∧
            ∃ x ∈ G.neighborFinset u, 9 ≤ G.degree x)).card := Finset.card_union_le _ _
    _ ≤ 108 + (Finset.univ.filter (fun u : Fin n =>
            G.degree u = 3 ∧ sigS G u ≤ 2 ∧
            ∃ x ∈ G.neighborFinset u, 9 ≤ G.degree x)).card := by
        have := mid_leaves_card_le_sharp n G h3 hcpt hblk
        omega

end ACMax
