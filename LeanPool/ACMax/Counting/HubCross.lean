/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
import LeanPool.ACMax.Counting.Incidence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import LeanPool.ACMax.Counting.FarPair
import LeanPool.ACMax.Counting.CompactCell
import LeanPool.ACMax.Counting.CompactLedgers

/-!
# The hub-cross firing law and the big-clean-twin structure

The spectral closer for the hub–hub mediation channel of the m-bound, together
with the rigidity of the twin population it controls.

## Main results

* `algConn_le_two_of_hub_cross_pair` — the **hub-cross firing law**: two
  non-adjacent degree-3 vertices `u ≠ v` with no common neighbour, partners all
  of degree `≤ 4` (hub degrees `D, D' ≥ 4` unbounded), and whose only possible
  `N(u)`–`N(v)` edge is the hub–hub edge `g ~ g'`, force `algConn G ≤ 2`. It
  strictly extends the cross-free usable far-pair law: instantiating the
  weighted double-star master with `au = av = 1`, hub weights `s = 1/(D−1)` and a
  balance-shifted partner weight makes the hub leak-identity
  `(1−s)² + (D−2)s² = 1 − s` yield worst-case slack `−(s+s')` (the hub–hub cross
  is spectrally cheap).
* `usable_twin_partners_deg_le_four` — σ-rigidity: a usable degree-3 twin of a
  degree-`≥ 9` hub has both other partners of degree `≤ 4`
  (`σ(9) + σ(5) + σ(4) > 2`). So the firing law applies to every cross-cloud twin
  pair mediated only by a hub–hub edge.
* `bigCleanTwins` and its structure lemmas `bigCleanTwins_nbr_deg` (neighbours
  have degree `4` or `≥ 9`), `bigCleanTwins_unique_big` (exactly one big
  neighbour, two degree-4 partners), `sum_big_inc_le`, `sum_small_inc_le` — the
  bipartite incidence counts feeding the hub-cross coverage argument.
-/

namespace ACMax

open Finset

variable {V : Type*} [Fintype V]

open Classical in
/-- **σ-rigidity of big-hub twins.**  A usable degree-3 vertex `t` (`sigS ≤ 2`)
adjacent to a hub `g` of degree `≥ 9` has both partners of degree `≤ 4`,
provided neither partner is degree-3 (i.e. off the `M`-cluster):
`σ(9) + σ(5) + σ(4) = 6/7 + 2/3 + 1/2 = 85/42 > 2`. -/
theorem usable_twin_partners_deg_le_four (G : SimpleGraph V) (t g w w' : V)
    (ht3 : G.degree t = 3) (htg : G.Adj t g) (htw : G.Adj t w) (htw' : G.Adj t w')
    (hgw : w ≠ g) (hgw' : w' ≠ g) (hww' : w ≠ w')
    (hD : 9 ≤ G.degree g) (husable : sigS G t ≤ 2)
    (hw4 : 4 ≤ G.degree w) (hw'4 : 4 ≤ G.degree w') :
    G.degree w ≤ 4 ∧ G.degree w' ≤ 4 := by
  classical
  -- `N(t) = {g, w, w'}`.
  have hgt : g ∈ G.neighborFinset t := (G.mem_neighborFinset t g).mpr htg
  have hwt : w ∈ G.neighborFinset t := (G.mem_neighborFinset t w).mpr htw
  have hw't : w' ∈ G.neighborFinset t := (G.mem_neighborFinset t w').mpr htw'
  have hcard : (G.neighborFinset t).card = 3 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; exact ht3
  have hsub : ({g, w, w'} : Finset V) ⊆ G.neighborFinset t := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> assumption
  have hset : G.neighborFinset t = ({g, w, w'} : Finset V) := by
    refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
    rw [hcard]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton]
    · simp [hww']
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hgw h.symm, fun h => hgw' h.symm⟩
  -- Decompose `sigS`.
  have hsig : sigS G t = sigma (G.degree g) + sigma (G.degree w)
      + sigma (G.degree w') := by
    unfold sigS
    rw [hset]
    rw [Finset.sum_insert (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hgw h.symm, fun h => hgw' h.symm⟩)]
    rw [Finset.sum_insert (by simp [hww'])]
    rw [Finset.sum_singleton]
    ring
  -- σ lower bounds.
  have hσg : sigma 9 ≤ sigma (G.degree g) := sigma_mono (by norm_num) hD
  have h9 : sigma 9 = 6 / 7 := by norm_num [sigma]
  constructor
  · -- If `deg w ≥ 5`, then `σ ≥ 6/7 + 2/3 + 1/2 > 2`.
    by_contra hcon
    have hw5 : 5 ≤ G.degree w := by omega
    have hσw : sigma 5 ≤ sigma (G.degree w) := sigma_mono (by norm_num) hw5
    have hσw' : sigma 4 ≤ sigma (G.degree w') := sigma_mono (by norm_num) hw'4
    have h5 : sigma 5 = 2 / 3 := sigma_five
    have h4 : sigma 4 = 1 / 2 := sigma_four
    rw [hsig] at husable
    rw [h9] at hσg; rw [h5] at hσw; rw [h4] at hσw'
    linarith
  · by_contra hcon
    have hw5 : 5 ≤ G.degree w' := by omega
    have hσw : sigma 4 ≤ sigma (G.degree w) := sigma_mono (by norm_num) hw4
    have hσw' : sigma 5 ≤ sigma (G.degree w') := sigma_mono (by norm_num) hw5
    have h5 : sigma 5 = 2 / 3 := sigma_five
    have h4 : sigma 4 = 1 / 2 := sigma_four
    rw [hsig] at husable
    rw [h9] at hσg; rw [h4] at hσw; rw [h5] at hσw'
    linarith

open Classical in
private theorem algConn_le_two_of_hub_cross_pair_hleakA : ∀ {V : Type u_1} [Fintype V] (G :
  SimpleGraph V)
  (u v g _ : V) (_ : ∀ (w : V), G.Adj u w → w ≠ g → G.degree w ≤ (4 : ℕ)),
  let A : Finset V := G.neighborFinset u;
  let B : Finset V := G.neighborFinset v;
  ∀ w ∈ A.erase g, (↑(#(G.neighborFinset w \ insert u B)) : ℝ) ≤ (3 : ℝ) := by
  classical
  intro V inst G u v g g' hpart A B w hw
  have hwA : w ∈ A := Finset.mem_of_mem_erase hw
  have hwadj : G.Adj u w := (G.mem_neighborFinset u w).mp hwA
  have hdeg : G.degree w ≤ 4 := hpart w hwadj (Finset.ne_of_mem_erase hw)
  have huw : u ∈ G.neighborFinset w := (G.mem_neighborFinset w u).mpr hwadj.symm
  have hsub : G.neighborFinset w \ insert u B ⊆ (G.neighborFinset w).erase u := by
    intro z hz
    rw [Finset.mem_sdiff] at hz
    rw [Finset.mem_erase]
    exact ⟨fun h => hz.2 (h ▸ Finset.mem_insert_self u B), hz.1⟩
  have hc : (G.neighborFinset w \ insert u B).card ≤ 3 := by
    calc (G.neighborFinset w \ insert u B).card
        ≤ ((G.neighborFinset w).erase u).card := Finset.card_le_card hsub
      _ = (G.neighborFinset w).card - 1 := Finset.card_erase_of_mem huw
      _ ≤ 3 := by
          rw [SimpleGraph.card_neighborFinset_eq_degree]
          omega
  exact_mod_cast hc

open Classical in
private theorem algConn_le_two_of_hub_cross_pair_hleakB : ∀ {V : Type u_1} [Fintype V] (G :
  SimpleGraph V)
  (u v _ g' : V) (_ : ∀ (w : V), G.Adj v w → w ≠ g' → G.degree w ≤ (4 : ℕ)),
  let A : Finset V := G.neighborFinset u;
  let B : Finset V := G.neighborFinset v;
  ∀ w ∈ B.erase g', (↑(#(G.neighborFinset w \ insert v A)) : ℝ) ≤ (3 : ℝ) := by
  classical
  intro V inst G u v g g' hpart' A B w hw
  have hwB : w ∈ B := Finset.mem_of_mem_erase hw
  have hwadj : G.Adj v w := (G.mem_neighborFinset v w).mp hwB
  have hdeg : G.degree w ≤ 4 := hpart' w hwadj (Finset.ne_of_mem_erase hw)
  have hvw : v ∈ G.neighborFinset w := (G.mem_neighborFinset w v).mpr hwadj.symm
  have hsub : G.neighborFinset w \ insert v A ⊆ (G.neighborFinset w).erase v := by
    intro z hz
    rw [Finset.mem_sdiff] at hz
    rw [Finset.mem_erase]
    exact ⟨fun h => hz.2 (h ▸ Finset.mem_insert_self v A), hz.1⟩
  have hc : (G.neighborFinset w \ insert v A).card ≤ 3 := by
    calc (G.neighborFinset w \ insert v A).card
        ≤ ((G.neighborFinset w).erase v).card := Finset.card_le_card hsub
      _ = (G.neighborFinset w).card - 1 := Finset.card_erase_of_mem hvw
      _ ≤ 3 := by
          rw [SimpleGraph.card_neighborFinset_eq_degree]
          omega
  exact_mod_cast hc

open Classical in
private theorem algConn_le_two_of_hub_cross_pair_hleak_sumA : ∀ {V : Type u_1} [Fintype V]
  (G : SimpleGraph V)
  (u v g : V),
  let A : Finset V := G.neighborFinset u;
  let B : Finset V := G.neighborFinset v;
  ∀ (_ : g ∈ A) (_ : #(A.erase g) = (2 : ℕ)),
    let _ : ℝ := (↑(G.degree g) : ℝ) - (1 : ℝ);
    ∀ (s : ℝ),
      let p : V → ℝ := fun w => if w = g then s else (1 / 2 : ℝ);
      ∀ (_ : ∀ w ∈ A.erase g, p w = (1 / 2 : ℝ)) (_ : p g = s)
        (_ : ∀ w ∈ A.erase g, (↑(#(G.neighborFinset w \ insert u B)) : ℝ) ≤ (3 : ℝ)) (Lg : ℝ),
        (↑(#(G.neighborFinset g \ insert u B)) : ℝ) ≤ Lg →
          ∑ w ∈ A, (↑(#(G.neighborFinset w \ insert u B)) : ℝ) * p w ^ (2 : ℕ) ≤ Lg * s ^ (2 : ℕ)
            + (3 / 2 : ℝ) := by
  classical
  intro V inst G u v g A B hgA hcardAe a s p hpe hpg hleakA Lg hLg
  rw [← Finset.add_sum_erase _
    (fun w => ((G.neighborFinset w \ insert u B).card : ℝ) * p w ^ 2) hgA, hpg]
  have h1 : ((G.neighborFinset g \ insert u B).card : ℝ) * s ^ 2 ≤ Lg * s ^ 2 :=
    mul_le_mul_of_nonneg_right hLg (sq_nonneg s)
  have h2 : (∑ w ∈ A.erase g,
      ((G.neighborFinset w \ insert u B).card : ℝ) * p w ^ 2) ≤ 3 / 2 := by
    have hpt : ∀ w ∈ A.erase g,
        ((G.neighborFinset w \ insert u B).card : ℝ) * p w ^ 2 ≤ 3 / 4 := by
      intro w hw
      rw [hpe w hw]
      have := hleakA w hw
      nlinarith only [this,
        (Nat.cast_nonneg (G.neighborFinset w \ insert u B).card : (0 : ℝ) ≤ _)]
    calc (∑ w ∈ A.erase g, ((G.neighborFinset w \ insert u B).card : ℝ) * p w ^ 2)
        ≤ ∑ _w ∈ A.erase g, (3 / 4 : ℝ) := Finset.sum_le_sum hpt
      _ = 3 / 2 := by rw [Finset.sum_const, hcardAe]; norm_num
  linarith

open Classical in
private theorem algConn_le_two_of_hub_cross_pair_hleak_sumB : ∀ {V : Type u_1} [Fintype V]
  (G : SimpleGraph V)
  (u v g g' : V),
  let A : Finset V := G.neighborFinset u;
  let B : Finset V := G.neighborFinset v;
  ∀ (_ : g' ∈ B) (_ : #(B.erase g') = (2 : ℕ)),
    let a : ℝ := (↑(G.degree g) : ℝ) - (1 : ℝ);
    let _ : ℝ := (↑(G.degree g') : ℝ) - (1 : ℝ);
    let s : ℝ := (1 : ℝ) / a;
    ∀ (s' : ℝ),
      let w0 : ℝ := (1 / 2 : ℝ) + (s - s') / (2 : ℝ);
      let q : V → ℝ := fun w => if w = g' then s' else w0;
      ∀ (_ : ∀ w ∈ B.erase g', q w = w0) (_ : q g' = s')
        (_ : ∀ w ∈ B.erase g', (↑(#(G.neighborFinset w \ insert v A)) : ℝ) ≤ (3 : ℝ)) (Lg : ℝ),
        (↑(#(G.neighborFinset g' \ insert v A)) : ℝ) ≤ Lg →
          ∑ w ∈ B, (↑(#(G.neighborFinset w \ insert v A)) : ℝ) * q w ^ (2 : ℕ) ≤
            Lg * s' ^ (2 : ℕ) + (6 : ℝ) * w0 ^ (2 : ℕ) := by
  classical
  intro V inst G u v g g' A B hg'B hcardBe a b s s' w0 q hqe hqg' hleakB Lg hLg
  rw [← Finset.add_sum_erase _
    (fun w => ((G.neighborFinset w \ insert v A).card : ℝ) * q w ^ 2) hg'B, hqg']
  have h1 : ((G.neighborFinset g' \ insert v A).card : ℝ) * s' ^ 2 ≤ Lg * s' ^ 2 :=
    mul_le_mul_of_nonneg_right hLg (sq_nonneg s')
  have h2 : (∑ w ∈ B.erase g',
      ((G.neighborFinset w \ insert v A).card : ℝ) * q w ^ 2) ≤ 6 * w0 ^ 2 := by
    have hpt : ∀ w ∈ B.erase g',
        ((G.neighborFinset w \ insert v A).card : ℝ) * q w ^ 2 ≤ 3 * w0 ^ 2 := by
      intro w hw
      rw [hqe w hw]
      have := hleakB w hw
      nlinarith only [this,
        (Nat.cast_nonneg (G.neighborFinset w \ insert v A).card : (0 : ℝ) ≤ _),
        sq_nonneg w0]
    calc (∑ w ∈ B.erase g', ((G.neighborFinset w \ insert v A).card : ℝ) * q w ^ 2)
        ≤ ∑ _w ∈ B.erase g', 3 * w0 ^ 2 := Finset.sum_le_sum hpt
      _ = 6 * w0 ^ 2 := by rw [Finset.sum_const, hcardBe]; ring
  linarith

open Classical in
private theorem algConn_le_two_of_hub_cross_pair_hLg_1 : ∀ {V : Type u_1} [Fintype V] (G :
  SimpleGraph V)
  (u v g g' : V) (_ : (4 : ℕ) ≤ G.degree g),
  let B : Finset V := G.neighborFinset v;
  ∀ (_ : g' ∈ B) (a : ℝ) (_ : a = (↑(G.degree g) : ℝ) - (1 : ℝ)) (_ : u ∈
    G.neighborFinset g)
    (_ : u ≠ g') (_ : g' ∈ G.neighborFinset g), (↑(#(G.neighborFinset g \ insert u B)) : ℝ)
      ≤ a - (1 : ℝ) := by
  classical
  intro V inst G u v g g' hD B hg'B a ha_def hugmem hug' hg'g
  have hsub2 : G.neighborFinset g \ insert u B
      ⊆ ((G.neighborFinset g).erase u).erase g' := by
    intro z hz
    rw [Finset.mem_sdiff] at hz
    rw [Finset.mem_erase, Finset.mem_erase]
    exact ⟨fun h => hz.2 (h ▸ Finset.mem_insert_of_mem hg'B),
      fun h => hz.2 (h ▸ Finset.mem_insert_self u B), hz.1⟩
  have hgue : g' ∈ (G.neighborFinset g).erase u :=
    Finset.mem_erase.mpr ⟨fun h => hug' h.symm, hg'g⟩
  have hc : (G.neighborFinset g \ insert u B).card + 2 ≤ G.degree g := by
    have h1 : (G.neighborFinset g \ insert u B).card
        ≤ (((G.neighborFinset g).erase u).erase g').card :=
      Finset.card_le_card hsub2
    rw [Finset.card_erase_of_mem hgue, Finset.card_erase_of_mem hugmem,
      SimpleGraph.card_neighborFinset_eq_degree] at h1
    omega
  have hcR : ((G.neighborFinset g \ insert u B).card : ℝ) + 2
      ≤ (G.degree g : ℝ) := by exact_mod_cast hc
  rw [ha_def]
  linarith

open Classical in
private theorem algConn_le_two_of_hub_cross_pair_hLg_2 : ∀ {V : Type u_1} [Fintype V] (G :
  SimpleGraph V)
  (u v g g' : V) (_ : (4 : ℕ) ≤ G.degree g'),
  let A : Finset V := G.neighborFinset u;
  ∀ (_ : g ∈ A) (b : ℝ) (_ : b = (↑(G.degree g') : ℝ) - (1 : ℝ)) (_ : v ∈
    G.neighborFinset g')
    (_ : v ≠ g) (_ : g ∈ G.neighborFinset g'), (↑(#(G.neighborFinset g' \ insert v A)) : ℝ)
      ≤ b - (1 : ℝ) := by
  classical
  intro V inst G u v g g' hD' A hgA b hb_def hvg'mem hvg hgng'
  have hsub2 : G.neighborFinset g' \ insert v A
      ⊆ ((G.neighborFinset g').erase v).erase g := by
    intro z hz
    rw [Finset.mem_sdiff] at hz
    rw [Finset.mem_erase, Finset.mem_erase]
    exact ⟨fun h => hz.2 (h ▸ Finset.mem_insert_of_mem hgA),
      fun h => hz.2 (h ▸ Finset.mem_insert_self v A), hz.1⟩
  have hgve : g ∈ (G.neighborFinset g').erase v :=
    Finset.mem_erase.mpr ⟨fun h => hvg h.symm, hgng'⟩
  have hc : (G.neighborFinset g' \ insert v A).card + 2 ≤ G.degree g' := by
    have h1 : (G.neighborFinset g' \ insert v A).card
        ≤ (((G.neighborFinset g').erase v).erase g).card :=
      Finset.card_le_card hsub2
    rw [Finset.card_erase_of_mem hgve, Finset.card_erase_of_mem hvg'mem,
      SimpleGraph.card_neighborFinset_eq_degree] at h1
    omega
  have hcR : ((G.neighborFinset g' \ insert v A).card : ℝ) + 2
      ≤ (G.degree g' : ℝ) := by exact_mod_cast hc
  rw [hb_def]
  linarith

open Classical in
private theorem algConn_le_two_of_hub_cross_pair_hLg_step1 : ∀ {V : Type u_1} [Fintype V]
  (G : SimpleGraph V)
  (u v g _ : V) (_ : (4 : ℕ) ≤ G.degree g),
  let B : Finset V := G.neighborFinset v;
  ∀ (a : ℝ) (_ : a = (↑(G.degree g) : ℝ) - (1 : ℝ)) (_ : u ∈ G.neighborFinset g)
    (_ : G.neighborFinset g \ insert u B ⊆ (G.neighborFinset g).erase u),
    (↑(#(G.neighborFinset g \ insert u B)) : ℝ) ≤ a := by
  classical
  intro V inst G u v g g' hD B a ha_def hugmem hleakg_base
  have hc : (G.neighborFinset g \ insert u B).card + 1 ≤ G.degree g := by
    have h1 : (G.neighborFinset g \ insert u B).card
        ≤ ((G.neighborFinset g).erase u).card :=
      Finset.card_le_card hleakg_base
    rw [Finset.card_erase_of_mem hugmem,
      SimpleGraph.card_neighborFinset_eq_degree] at h1
    omega
  have hcR : ((G.neighborFinset g \ insert u B).card : ℝ) + 1
      ≤ (G.degree g : ℝ) := by exact_mod_cast hc
  rw [ha_def]
  linarith

open Classical in
private theorem algConn_le_two_of_hub_cross_pair_hLg_step2 : ∀ {V : Type u_1} [Fintype V]
  (G : SimpleGraph V)
  (u v _ g' : V) (_ : (4 : ℕ) ≤ G.degree g'),
  let A : Finset V := G.neighborFinset u;
  ∀ (b : ℝ) (_ : b = (↑(G.degree g') : ℝ) - (1 : ℝ)) (_ : v ∈ G.neighborFinset g')
    (_ : G.neighborFinset g' \ insert v A ⊆ (G.neighborFinset g').erase v),
    (↑(#(G.neighborFinset g' \ insert v A)) : ℝ) ≤ b := by
  classical
  intro V inst G u v g g' hD' A b hb_def hvg'mem hleakg'_base
  have hc : (G.neighborFinset g' \ insert v A).card + 1 ≤ G.degree g' := by
    have h1 : (G.neighborFinset g' \ insert v A).card
        ≤ ((G.neighborFinset g').erase v).card :=
      Finset.card_le_card hleakg'_base
    rw [Finset.card_erase_of_mem hvg'mem,
      SimpleGraph.card_neighborFinset_eq_degree] at h1
    omega
  have hcR : ((G.neighborFinset g' \ insert v A).card : ℝ) + 1
      ≤ (G.degree g' : ℝ) := by exact_mod_cast hc
  rw [hb_def]
  linarith

open Classical in
private theorem hub_cross_weighted_certificate : ∀ {V : Type u_1} [Fintype V] [Nonempty V]
  (G : SimpleGraph V) (u v g g' : V) (_ : u ≠ v) (_ : ¬G.Adj u v) (_ : ∀ (w : V), ¬(G.Adj u
    w ∧ G.Adj v w))
  (_ : (4 : ℕ) ≤ G.degree g) (_ : (4 : ℕ) ≤ G.degree g'),
  let A : Finset V := G.neighborFinset u;
  ∀ (_ : A = G.neighborFinset u),
    let B : Finset V := G.neighborFinset v;
    ∀ (_ : B = G.neighborFinset v) (_ : g ∈ A) (_ : g' ∈ B),
      let a : ℝ := (↑(G.degree g) : ℝ) - (1 : ℝ);
      ∀ (_ : a = (↑(G.degree g) : ℝ) - (1 : ℝ)),
        let b : ℝ := (↑(G.degree g') : ℝ) - (1 : ℝ);
        ∀ (_ : b = (↑(G.degree g') : ℝ) - (1 : ℝ)),
          let s : ℝ := (1 : ℝ) / a;
          let s' : ℝ := (1 : ℝ) / b;
          ∀ (_ : (0 : ℝ) < s) (_ : (0 : ℝ) < s'),
            let w0 : ℝ := (1 / 2 : ℝ) + (s - s') / (2 : ℝ);
            ∀ (_ : w0 = (1 / 2 : ℝ) + (s - s') / (2 : ℝ)) (_ : (0 : ℝ) < w0),
              let p : V → ℝ := fun w => if w = g then s else (1 / 2 : ℝ);
              ∀ (_ : p = fun w => if w = g then s else (1 / 2 : ℝ)),
                let q : V → ℝ := fun w => if w = g' then s' else w0;
                ∀ (_ : q = fun w => if w = g' then s' else w0) (_ : ∑ w ∈ A, p w = s +
                  (1 : ℝ))
                  (_ : ∑ w ∈ B, q w = s' + (2 : ℝ) * w0)
                  (_ : ∑ w ∈ A, p w ^ (2 : ℕ) = s ^ (2 : ℕ) + (1 / 2 : ℝ))
                  (_ : ∑ w ∈ B, q w ^ (2 : ℕ) = s' ^ (2 : ℕ) + (2 : ℝ) * w0 ^ (2 : ℕ))
                  (_ : ∑ w ∈ A, ((1 : ℝ) - p w) ^ (2 : ℕ) = ((1 : ℝ) - s) ^ (2 : ℕ) + (1 / 2
                    : ℝ))
                  (_ :
                    ∑ w ∈ B, ((1 : ℝ) - q w) ^ (2 : ℕ) = ((1 : ℝ) - s') ^ (2 : ℕ) + (2 : ℝ) * ((1
                      : ℝ) - w0) ^ (2 : ℕ))
                  (_ : u ∈ G.neighborFinset g) (_ : v ∈ G.neighborFinset g')
                  (_ : G.neighborFinset g \ insert u B ⊆ (G.neighborFinset g).erase u)
                  (_ : G.neighborFinset g' \ insert v A ⊆ (G.neighborFinset g').erase v)
                  (_ :
                    (∑ w ∈ A, ∑ w' ∈ B, if G.Adj w w' then (p w + q w') ^ (2 : ℕ) else (0 : ℝ)) ≤
                      if G.Adj g g' then (s + s') ^ (2 : ℕ) else (0 : ℝ))
                  (_ :
                    ∀ (Lg : ℝ),
                      (↑(#(G.neighborFinset g \ insert u B)) : ℝ) ≤ Lg →
                        ∑ w ∈ A, (↑(#(G.neighborFinset w \ insert u B)) : ℝ) * p w ^ (2 : ℕ) ≤
                          Lg * s ^ (2 : ℕ) + (3 / 2 : ℝ))
                  (_ :
                    ∀ (Lg : ℝ),
                      (↑(#(G.neighborFinset g' \ insert v A)) : ℝ) ≤ Lg →
                        ∑ w ∈ B, (↑(#(G.neighborFinset w \ insert v A)) : ℝ) * q w ^ (2 : ℕ) ≤
                          Lg * s' ^ (2 : ℕ) + (6 : ℝ) * w0 ^ (2 : ℕ))
                  (_ : u ≠ g') (_ : v ≠ g) (_ : a * s ^ (2 : ℕ) = s) (_ : b * s' ^ (2 :
                    ℕ) = s'),
                  algConn G ≤ (2 : ℝ) := by
  classical
  intro V inst inst_1 G u v g g' hne huv hcap hD hD' A hA B hB hgA hg'B a ha_def b hb_def s s'
    hs_pos hs'_pos w0 hw0_def hw0_pos p hp_def q hq_def hsum_p hsum_q hsum_p2 hsum_q2 hsum_1p
    hsum_1q hugmem hvg'mem hleakg_base hleakg'_base hcross_sum hleak_sumA hleak_sumB hug' hvg has2
    hbs2
  refine algConn_le_two_of_weighted_double_star G u v 1 1 p q hne huv hcap
    (by norm_num)
    (fun w hw => ?_) (fun w hw => ?_) ?_ ?_
  · -- `p ≥ 0` on `N(u)`.
    simp only [hp_def]
    split
    · exact hs_pos.le
    · norm_num
  · -- `q ≥ 0` on `N(v)`.
    simp only [hq_def]
    split
    · exact hs'_pos.le
    · exact hw0_pos.le
  · -- Balance.
    rw [← hA, ← hB, hsum_p, hsum_q, hw0_def]
    ring
  · -- The quadratic bound, by cases on the hub–hub edge.
    rw [← hA, ← hB]
    rw [one_pow, hsum_p2, hsum_q2, hsum_1p, hsum_1q]
    by_cases hgg : G.Adj g g'
    · -- Edge present: hub leaks `≤ deg − 2`, cross `≤ (s+s')²`.
      have hg'g : g' ∈ G.neighborFinset g := (G.mem_neighborFinset g g').mpr hgg
      have hgng' : g ∈ G.neighborFinset g' := (G.mem_neighborFinset g' g).mpr hgg.symm
      -- Hub leak `g`: exclude `u` and `g'`.
      have hLg :=
          algConn_le_two_of_hub_cross_pair_hLg_1 (V := V) (G := G) (u := u) (v := v) (g := g)
            (g' := g') (hD) (hg'B) (a := a) (ha_def) (hugmem)
            (hug') (hg'g)
      -- Hub leak `g'`: exclude `v` and `g`.
      have hLg' :=
          algConn_le_two_of_hub_cross_pair_hLg_2 (V := V) (G := G) (u := u) (v := v) (g := g)
            (g' := g') (hD') (hgA) (b := b) (hb_def) (hvg'mem)
            (hvg) (hgng')
      have hSA := hleak_sumA (a - 1) hLg
      have hSB := hleak_sumB (b - 1) hLg'
      have hCR : (∑ w ∈ A, ∑ w' ∈ B, (if G.Adj w w' then (p w + q w') ^ 2 else 0))
          ≤ (s + s') ^ 2 := by
        calc (∑ w ∈ A, ∑ w' ∈ B, (if G.Adj w w' then (p w + q w') ^ 2 else 0))
            ≤ (if G.Adj g g' then (s + s') ^ 2 else 0) := hcross_sum
          _ = (s + s') ^ 2 := ite_eq_left hgg
      -- Final scalar inequality: worst-case slack `= −(s+s')`.
      have key : (1 - s) ^ 2 + 1 / 2 + ((1 - s') ^ 2 + 2 * (1 - w0) ^ 2)
          + (s + s') ^ 2 + ((a - 1) * s ^ 2 + 3 / 2) + ((b - 1) * s' ^ 2 + 6 * w0 ^ 2)
          ≤ 2 * (1 + (s ^ 2 + 1 / 2) + (1 + (s' ^ 2 + 2 * w0 ^ 2))) := by
        have h1 : (a - 1) * s ^ 2 = s - s ^ 2 := by rw [sub_mul, has2, one_mul]
        have h2 : (b - 1) * s' ^ 2 = s' - s' ^ 2 := by rw [sub_mul, hbs2, one_mul]
        rw [h1, h2, hw0_def]
        nlinarith only [hs_pos, hs'_pos]
      linarith only [hSA, hSB, hCR, key]
    · -- Edge absent: hub leaks `≤ deg − 1`, no cross term at all.
      have hLg :=
          algConn_le_two_of_hub_cross_pair_hLg_step1 (V := V) (G := G) (u := u) (v := v) (g :=
            g) (g') (hD) (a := a) (ha_def) (hugmem) (hleakg_base)
      have hLg' :=
          algConn_le_two_of_hub_cross_pair_hLg_step2 (V := V) (G := G) (u := u) (v := v) (g) (g'
            := g') (hD') (b := b) (hb_def) (hvg'mem)
            (hleakg'_base)
      have hSA := hleak_sumA a hLg
      have hSB := hleak_sumB b hLg'
      have hCR : (∑ w ∈ A, ∑ w' ∈ B, (if G.Adj w w' then (p w + q w') ^ 2 else 0))
          ≤ 0 := by
        calc (∑ w ∈ A, ∑ w' ∈ B, (if G.Adj w w' then (p w + q w') ^ 2 else 0))
            ≤ (if G.Adj g g' then (s + s') ^ 2 else 0) := hcross_sum
          _ = 0 := ite_eq_right hgg
      -- Final scalar inequality: worst-case slack `= −(s+s') − 2ss'`.
      have key : (1 - s) ^ 2 + 1 / 2 + ((1 - s') ^ 2 + 2 * (1 - w0) ^ 2)
          + (a * s ^ 2 + 3 / 2) + (b * s' ^ 2 + 6 * w0 ^ 2)
          ≤ 2 * (1 + (s ^ 2 + 1 / 2) + (1 + (s' ^ 2 + 2 * w0 ^ 2))) := by
        rw [has2, hbs2, hw0_def]
        nlinarith only [hs_pos, hs'_pos, mul_pos hs_pos hs'_pos]
      linarith only [hSA, hSB, hCR, key]

open Classical in
/-- **The hub-cross firing law.**  `u ≠ v` degree-3, non-adjacent, no common
neighbour; `g ∈ N(u)`, `g' ∈ N(v)` hubs of degree `≥ 4` (unbounded above); all
other neighbours (*partners*) of `u` and of `v` have degree `≤ 4`; and every
`N(u)`–`N(v)` edge is the hub–hub edge `(g, g')`.  Then `algConn G ≤ 2` — the
single hub–hub cross is spectrally cheap and cannot block the double-star
certificate.  Weights: `au = av = 1`, hub weights `1/(deg−1)`, `u`-partners
`½`, `v`-partners `½ + (s−s')/2`; worst-case quadratic slack `= −(s+s')` (edge
present) resp. `−(s+s')−2ss'` (absent). -/
theorem algConn_le_two_of_hub_cross_pair [Nonempty V]
    (G : SimpleGraph V) (u v g g' : V)
    (hu3 : G.degree u = 3) (hv3 : G.degree v = 3)
    (hne : u ≠ v) (huv : ¬G.Adj u v)
    (hcap : ∀ w : V, ¬(G.Adj u w ∧ G.Adj v w))
    (hgu : G.Adj u g) (hg'v : G.Adj v g')
    (hD : 4 ≤ G.degree g) (hD' : 4 ≤ G.degree g')
    (hpart : ∀ w : V, G.Adj u w → w ≠ g → G.degree w ≤ 4)
    (hpart' : ∀ w : V, G.Adj v w → w ≠ g' → G.degree w ≤ 4)
    (hcross : ∀ w w' : V, G.Adj u w → G.Adj v w' → G.Adj w w' → w = g ∧ w' = g') :
    algConn G ≤ 2 := by
  classical
  -- Abbreviations.
  set A := G.neighborFinset u with hA
  set B := G.neighborFinset v with hB
  have hgA : g ∈ A := (G.mem_neighborFinset u g).mpr hgu
  have hg'B : g' ∈ B := (G.mem_neighborFinset v g').mpr hg'v
  have hcardA : A.card = 3 := by
    rw [hA, SimpleGraph.card_neighborFinset_eq_degree]; exact hu3
  have hcardB : B.card = 3 := by
    rw [hB, SimpleGraph.card_neighborFinset_eq_degree]; exact hv3
  have hcardAe : (A.erase g).card = 2 := by
    rw [Finset.card_erase_of_mem hgA, hcardA]
  have hcardBe : (B.erase g').card = 2 := by
    rw [Finset.card_erase_of_mem hg'B, hcardB]
  -- The real weights.
  set a : ℝ := (G.degree g : ℝ) - 1 with ha_def
  set b : ℝ := (G.degree g' : ℝ) - 1 with hb_def
  have ha3 : (3 : ℝ) ≤ a := by
    rw [ha_def]
    have : (4 : ℝ) ≤ (G.degree g : ℝ) := by exact_mod_cast hD
    linarith
  have hb3 : (3 : ℝ) ≤ b := by
    rw [hb_def]
    have : (4 : ℝ) ≤ (G.degree g' : ℝ) := by exact_mod_cast hD'
    linarith
  have ha0 : a ≠ 0 := by linarith
  have hb0 : b ≠ 0 := by linarith
  set s : ℝ := 1 / a with hs_def
  set s' : ℝ := 1 / b with hs'_def
  have hs_pos : 0 < s := by rw [hs_def]; positivity
  have hs'_pos : 0 < s' := by rw [hs'_def]; positivity
  have hs_le : s ≤ 1 / 3 := by
    rw [hs_def]
    exact one_div_le_one_div_of_le (by norm_num) ha3
  have hs'_le : s' ≤ 1 / 3 := by
    rw [hs'_def]
    exact one_div_le_one_div_of_le (by norm_num) hb3
  have has : a * s = 1 := by rw [hs_def]; field_simp
  have hbs : b * s' = 1 := by rw [hs'_def]; field_simp
  set w0 : ℝ := 1 / 2 + (s - s') / 2 with hw0_def
  have hw0_pos : 0 < w0 := by rw [hw0_def]; linarith
  set p : V → ℝ := fun w => if w = g then s else 1 / 2 with hp_def
  set q : V → ℝ := fun w => if w = g' then s' else w0 with hq_def
  -- Values off the hubs.
  have hpe : ∀ w ∈ A.erase g, p w = 1 / 2 := by
    intro w hw
    rw [hp_def]
    exact ite_eq_right (Finset.ne_of_mem_erase hw)
  have hqe : ∀ w ∈ B.erase g', q w = w0 := by
    intro w hw
    rw [hq_def]
    exact ite_eq_right (Finset.ne_of_mem_erase hw)
  have hpg : p g = s := by rw [hp_def]; simp
  have hqg' : q g' = s' := by rw [hq_def]; simp
  -- Weight sums.
  have hsum_p : ∑ w ∈ A, p w = s + 1 := by
    rw [← Finset.add_sum_erase _ p hgA, hpg,
      Finset.sum_congr rfl hpe, Finset.sum_const, hcardAe]
    ring
  have hsum_q : ∑ w ∈ B, q w = s' + 2 * w0 := by
    rw [← Finset.add_sum_erase _ q hg'B, hqg',
      Finset.sum_congr rfl hqe, Finset.sum_const, hcardBe]
    ring
  have hsum_p2 : ∑ w ∈ A, p w ^ 2 = s ^ 2 + 1 / 2 := by
    rw [← Finset.add_sum_erase _ (fun w => p w ^ 2) hgA, hpg,
      Finset.sum_congr rfl (fun w hw => by rw [hpe w hw]),
      Finset.sum_const, hcardAe]
    ring
  have hsum_q2 : ∑ w ∈ B, q w ^ 2 = s' ^ 2 + 2 * w0 ^ 2 := by
    rw [← Finset.add_sum_erase _ (fun w => q w ^ 2) hg'B, hqg',
      Finset.sum_congr rfl (fun w hw => by rw [hqe w hw]),
      Finset.sum_const, hcardBe]
    ring
  have hsum_1p : ∑ w ∈ A, (1 - p w) ^ 2 = (1 - s) ^ 2 + 1 / 2 := by
    rw [← Finset.add_sum_erase _ (fun w => (1 - p w) ^ 2) hgA, hpg,
      Finset.sum_congr rfl (fun w hw => by rw [hpe w hw]),
      Finset.sum_const, hcardAe]
    ring
  have hsum_1q : ∑ w ∈ B, (1 - q w) ^ 2 = (1 - s') ^ 2 + 2 * (1 - w0) ^ 2 := by
    rw [← Finset.add_sum_erase _ (fun w => (1 - q w) ^ 2) hg'B, hqg',
      Finset.sum_congr rfl (fun w hw => by rw [hqe w hw]),
      Finset.sum_const, hcardBe]
    ring
  -- Leak bounds.  Partners: `≤ 3` (degree ≤ 4 and `u` resp. `v` is a neighbour).
  have hleakA :=
      algConn_le_two_of_hub_cross_pair_hleakA (V := V) (G := G) (u := u) (v := v) (g := g) (g')
        (hpart)
  have hleakB :=
      algConn_le_two_of_hub_cross_pair_hleakB (V := V) (G := G) (u := u) (v := v) (g) (g'
        := g') (hpart')
  -- Hub leaks: `u ∈ N(g)` always; if `g ~ g'` additionally `g' ∈ N(g) ∩ B`.
  have hugmem : u ∈ G.neighborFinset g := (G.mem_neighborFinset g u).mpr hgu.symm
  have hvg'mem : v ∈ G.neighborFinset g' := (G.mem_neighborFinset g' v).mpr hg'v.symm
  have hleakg_base : G.neighborFinset g \ insert u B ⊆ (G.neighborFinset g).erase u := by
    intro z hz
    rw [Finset.mem_sdiff] at hz
    rw [Finset.mem_erase]
    exact ⟨fun h => hz.2 (h ▸ Finset.mem_insert_self u B), hz.1⟩
  have hleakg'_base : G.neighborFinset g' \ insert v A ⊆ (G.neighborFinset g').erase v := by
    intro z hz
    rw [Finset.mem_sdiff] at hz
    rw [Finset.mem_erase]
    exact ⟨fun h => hz.2 (h ▸ Finset.mem_insert_self v A), hz.1⟩
  -- Cross-edge sum: by `hcross` the only possible cross is `(g, g')`.
  have hcross_sum : (∑ w ∈ A, ∑ w' ∈ B, (if G.Adj w w' then (p w + q w') ^ 2 else 0))
      ≤ (if G.Adj g g' then (s + s') ^ 2 else 0) := by
    have hsupport : ∀ w ∈ A, ∀ w' ∈ B, G.Adj w w' → w = g ∧ w' = g' := by
      intro w hw w' hw' hadj
      exact hcross w w' ((G.mem_neighborFinset u w).mp hw)
        ((G.mem_neighborFinset v w').mp hw') hadj
    simpa only [hpg, hqg'] using le_of_eq
      (sum_adj_eq_single G A B g g' (fun w w' => (p w + q w') ^ 2)
        hgA hg'B hsupport)
  -- Leak sums.
  have hleak_sumA : ∀ Lg : ℝ, ((G.neighborFinset g \ insert u B).card : ℝ) ≤ Lg →
      (∑ w ∈ A, ((G.neighborFinset w \ insert u B).card : ℝ) * p w ^ 2)
        ≤ Lg * s ^ 2 + 3 / 2 :=
      algConn_le_two_of_hub_cross_pair_hleak_sumA (V := V) (G := G) (u := u) (v := v) (g := g)
        (hgA) (hcardAe) (s := s) (hpe) (hpg) (hleakA)
  have hleak_sumB : ∀ Lg : ℝ, ((G.neighborFinset g' \ insert v A).card : ℝ) ≤ Lg →
      (∑ w ∈ B, ((G.neighborFinset w \ insert v A).card : ℝ) * q w ^ 2)
        ≤ Lg * s' ^ 2 + 6 * w0 ^ 2 :=
      algConn_le_two_of_hub_cross_pair_hleak_sumB (V := V) (G := G) (u := u) (v := v) (g := g)
        (g' := g') (hg'B) (hcardBe) (s' := s') (hqe) (hqg')
        (hleakB)
  -- Simple exclusions.
  have hug' : u ≠ g' := by
    intro h
    apply huv
    rw [h]
    exact hg'v.symm
  have hvg : v ≠ g := by
    intro h
    apply huv
    rw [h]
    exact hgu
  -- Square identities from `a·s = 1`, `b·s' = 1`.
  have has2 : a * s ^ 2 = s := by
    rw [pow_two, ← mul_assoc, has, one_mul]
  have hbs2 : b * s' ^ 2 = s' := by
    rw [pow_two, ← mul_assoc, hbs, one_mul]
  -- Apply the master certificate.
  exact hub_cross_weighted_certificate (V := V) (G := G) (u := u) (v := v) (g := g) (g' := g')
    (hne) (huv) (hcap) (hD) (hD') (hA) (hB) (hgA) (hg'B) (ha_def) (hb_def) (hs_pos) (hs'_pos)
      (hw0_def) (hw0_pos) (hp_def) (hq_def)
    (hsum_p) (hsum_q) (hsum_p2) (hsum_q2) (hsum_1p) (hsum_1q) (hugmem) (hvg'mem) (hleakg_base)
      (hleakg'_base) (hcross_sum) (hleak_sumA) (hleak_sumB) (hug') (hvg) (has2) (hbs2)

end ACMax

/-! ## Big clean twins

The *big clean twins* `bigCleanTwins G = {u : deg u = 3 ∧ sigS u ≤ 2 ∧
(∃ x ~ u, deg x ≥ 9) ∧ (∀ x ~ u, deg x ≠ 3)}` are the usable degree-3 vertices
with a big neighbour and no degree-3 neighbour. By σ-rigidity their
neighbourhoods are completely determined (`bigCleanTwins_nbr_deg`,
`bigCleanTwins_unique_big`), and the bipartite incidence counts `sum_big_inc_le`
/ `sum_small_inc_le` feed the hub-cross pair-coverage count. -/

namespace ACMax

open Finset

open Classical in
/-- The **big clean twins**: usable degree-3 vertices with a degree-`≥ 9`
neighbour and no degree-3 neighbour. -/
noncomputable def bigCleanTwins {n : ℕ} (G : SimpleGraph (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun u : Fin n =>
    G.degree u = 3 ∧ sigS G u ≤ 2 ∧
    (∃ x ∈ G.neighborFinset u, 9 ≤ G.degree x) ∧
    (∀ x ∈ G.neighborFinset u, G.degree x ≠ 3))

open Classical in
theorem mem_bigCleanTwins {n : ℕ} {G : SimpleGraph (Fin n)} {u : Fin n} :
    u ∈ bigCleanTwins G ↔
      G.degree u = 3 ∧ sigS G u ≤ 2 ∧
      (∃ x ∈ G.neighborFinset u, 9 ≤ G.degree x) ∧
      (∀ x ∈ G.neighborFinset u, G.degree x ≠ 3) := by
  unfold bigCleanTwins
  simp

open Classical in
/-- **Neighbourhood rigidity.**  Every neighbour of a big clean twin has degree
`4` or degree `≥ 9`. -/
theorem bigCleanTwins_nbr_deg {n : ℕ} (G : SimpleGraph (Fin n))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    {u : Fin n} (hu : u ∈ bigCleanTwins G) {x : Fin n}
    (hx : x ∈ G.neighborFinset u) :
    G.degree x = 4 ∨ 9 ≤ G.degree x := by
  classical
  obtain ⟨hdeg, hsig, ⟨gbig, hgmem, hgbig⟩, hno3⟩ := mem_bigCleanTwins.mp hu
  by_cases hxg : x = gbig
  · exact Or.inr (hxg ▸ hgbig)
  -- `x ≠ gbig`: `x` is a partner.  Get the third neighbour.
  have hxne3 : G.degree x ≠ 3 := hno3 x hx
  have hx4 : 4 ≤ G.degree x := by
    have := h3 x
    omega
  -- the third neighbour `y`: `N(u) = {gbig, x, y}`
  have hcard : (G.neighborFinset u).card = 3 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hdeg
  have hcard2 : (((G.neighborFinset u).erase gbig).erase x).card = 1 := by
    rw [Finset.card_erase_of_mem, Finset.card_erase_of_mem hgmem, hcard]
    exact Finset.mem_erase.mpr ⟨hxg, hx⟩
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hcard2
  have hymem : y ∈ ((G.neighborFinset u).erase gbig).erase x := by
    rw [hy]; exact Finset.mem_singleton_self y
  have hyx : y ≠ x := (Finset.mem_erase.mp hymem).1
  have hyg : y ≠ gbig := (Finset.mem_erase.mp (Finset.mem_erase.mp hymem).2).1
  have hyN : y ∈ G.neighborFinset u := (Finset.mem_erase.mp (Finset.mem_erase.mp hymem).2).2
  have hy4 : 4 ≤ G.degree y := by
    have h1 := hno3 y hyN
    have h2 := h3 y
    omega
  -- σ-rigidity: partners of a `≥ 9` hub are degree `≤ 4`
  have hle := usable_twin_partners_deg_le_four G u gbig x y hdeg
    ((G.mem_neighborFinset u gbig).mp hgmem)
    ((G.mem_neighborFinset u x).mp hx)
    ((G.mem_neighborFinset u y).mp hyN)
    hxg hyg hyx.symm hgbig hsig hx4 hy4
  exact Or.inl (le_antisymm hle.1 hx4)

open Classical in
/-- **Unique big neighbour.**  A big clean twin has exactly one big neighbour:
there is a big neighbour `g`, and every other neighbour has degree `≤ 4`. -/
theorem bigCleanTwins_unique_big {n : ℕ} (G : SimpleGraph (Fin n))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    {u : Fin n} (hu : u ∈ bigCleanTwins G) :
    ∃ g ∈ G.neighborFinset u, 9 ≤ G.degree g ∧
      ∀ x ∈ G.neighborFinset u, x ≠ g → G.degree x = 4 := by
  classical
  obtain ⟨hdeg, hsig, ⟨gbig, hgmem, hgbig⟩, hno3⟩ := mem_bigCleanTwins.mp hu
  refine ⟨gbig, hgmem, hgbig, ?_⟩
  intro x hx hxg
  rcases bigCleanTwins_nbr_deg G h3 hu hx with h4 | h9
  · exact h4
  -- two big neighbours: contradiction via σ-rigidity (`x` would be a partner of
  -- degree `≥ 9 > 4`).
  exfalso
  -- third neighbour `y` of `u` besides `gbig, x`
  have hcard : (G.neighborFinset u).card = 3 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]; exact hdeg
  have hcard2 : (((G.neighborFinset u).erase gbig).erase x).card = 1 := by
    rw [Finset.card_erase_of_mem, Finset.card_erase_of_mem hgmem, hcard]
    exact Finset.mem_erase.mpr ⟨hxg, hx⟩
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hcard2
  have hymem : y ∈ ((G.neighborFinset u).erase gbig).erase x := by
    rw [hy]; exact Finset.mem_singleton_self y
  have hyx : y ≠ x := (Finset.mem_erase.mp hymem).1
  have hyg : y ≠ gbig := (Finset.mem_erase.mp (Finset.mem_erase.mp hymem).2).1
  have hyN : y ∈ G.neighborFinset u := (Finset.mem_erase.mp (Finset.mem_erase.mp hymem).2).2
  have hy4 : 4 ≤ G.degree y := by
    have h1 := hno3 y hyN
    have h2 := h3 y
    omega
  have hle := usable_twin_partners_deg_le_four G u gbig x y hdeg
    ((G.mem_neighborFinset u gbig).mp hgmem)
    ((G.mem_neighborFinset u x).mp hx)
    ((G.mem_neighborFinset u y).mp hyN)
    hxg hyg hyx.symm hgbig hsig (by omega) hy4
  omega

open Classical in
/-- **Bipartite incidence exchange** (indicator double count):
`Σ_{w ∈ s} |N(w) ∩ t| = Σ_{u ∈ t} |N(u) ∩ s|`. -/
theorem sum_nbr_inter_comm {n : ℕ} (G : SimpleGraph (Fin n))
    (s t : Finset (Fin n)) :
    ∑ w ∈ s, (G.neighborFinset w ∩ t).card
      = ∑ u ∈ t, (G.neighborFinset u ∩ s).card := by
  classical
  have hleft : ∀ w : Fin n, (G.neighborFinset w ∩ t).card
      = ∑ u ∈ t, (if G.Adj w u then 1 else 0) := by
    intro w
    have hset : G.neighborFinset w ∩ t = t.filter (fun u => G.Adj w u) := by
      ext u
      simp [Finset.mem_inter, Finset.mem_filter, SimpleGraph.mem_neighborFinset,
        and_comm]
    rw [hset, Finset.card_filter]
  have hright : ∀ u : Fin n, (G.neighborFinset u ∩ s).card
      = ∑ w ∈ s, (if G.Adj w u then 1 else 0) := by
    intro u
    have hset : G.neighborFinset u ∩ s = s.filter (fun w => G.Adj w u) := by
      ext w
      simp only [Finset.mem_inter, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨hu, hw⟩
        exact ⟨hw, hu.symm⟩
      · rintro ⟨hw, hu⟩
        exact ⟨hu.symm, hw⟩
    rw [hset, Finset.card_filter]
  simp_rw [hleft, hright]
  exact Finset.sum_comm

open Classical in
/-- **Big-incidence exchange.**  The incidences between big vertices and big
clean twins number at most `|bigCleanTwins|` — each twin has exactly one big
neighbour. -/
theorem sum_big_inc_le {n : ℕ} (G : SimpleGraph (Fin n))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) :
    ∑ w ∈ Finset.univ.filter (fun w : Fin n => 9 ≤ G.degree w),
        (G.neighborFinset w ∩ bigCleanTwins G).card
      ≤ (bigCleanTwins G).card := by
  classical
  rw [sum_nbr_inter_comm]
  calc ∑ u ∈ bigCleanTwins G,
      (G.neighborFinset u ∩ Finset.univ.filter (fun w : Fin n => 9 ≤ G.degree w)).card
      ≤ ∑ _u ∈ bigCleanTwins G, 1 := by
        refine Finset.sum_le_sum (fun u hu => ?_)
        obtain ⟨g, hgmem, hgbig, hrest⟩ := bigCleanTwins_unique_big G h3 hu
        refine Finset.card_le_one.mpr (fun x hx y hy => ?_)
        rw [Finset.mem_inter, Finset.mem_filter] at hx hy
        have hxg : x = g := by
          by_contra hne
          have := hrest x hx.1 hne
          have := hx.2.2
          omega
        have hyg : y = g := by
          by_contra hne
          have := hrest y hy.1 hne
          have := hy.2.2
          omega
        rw [hxg, hyg]
    _ = (bigCleanTwins G).card := by rw [Finset.sum_const, smul_eq_mul, mul_one]

open Classical in
/-- **Small-incidence exchange.**  The incidences between degree-`≤ 8` vertices
and big clean twins number at most `2·|bigCleanTwins|` — each twin has exactly
two degree-4 partners. -/
theorem sum_small_inc_le {n : ℕ} (G : SimpleGraph (Fin n))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) :
    ∑ w ∈ Finset.univ.filter (fun w : Fin n => G.degree w ≤ 8),
        (G.neighborFinset w ∩ bigCleanTwins G).card
      ≤ 2 * (bigCleanTwins G).card := by
  classical
  rw [sum_nbr_inter_comm]
  calc ∑ u ∈ bigCleanTwins G,
      (G.neighborFinset u ∩ Finset.univ.filter (fun w : Fin n => G.degree w ≤ 8)).card
      ≤ ∑ _u ∈ bigCleanTwins G, 2 := by
        refine Finset.sum_le_sum (fun u hu => ?_)
        obtain ⟨g, hgmem, hgbig, hrest⟩ := bigCleanTwins_unique_big G h3 hu
        -- the small neighbours avoid `g`, and `N(u) \ {g}` has two elements
        have hsub : G.neighborFinset u ∩
            Finset.univ.filter (fun w : Fin n => G.degree w ≤ 8)
            ⊆ (G.neighborFinset u).erase g := by
          intro x hx
          rw [Finset.mem_inter, Finset.mem_filter] at hx
          refine Finset.mem_erase.mpr ⟨?_, hx.1⟩
          intro hxg
          have h8 : G.degree x ≤ 8 := hx.2.2
          rw [hxg] at h8
          omega
        have hcard : (G.neighborFinset u).card = 3 := by
          rw [SimpleGraph.card_neighborFinset_eq_degree]
          exact (mem_bigCleanTwins.mp hu).1
        calc (G.neighborFinset u ∩
              Finset.univ.filter (fun w : Fin n => G.degree w ≤ 8)).card
            ≤ ((G.neighborFinset u).erase g).card := Finset.card_le_card hsub
          _ = 2 := by rw [Finset.card_erase_of_mem hgmem, hcard]
    _ = 2 * (bigCleanTwins G).card := by
        rw [Finset.sum_const, smul_eq_mul]
        ring

open Classical in
/-- The `M`-population under the dichotomy: at most `2` degree-3 vertices
have a degree-3 neighbour. -/
theorem deg3_with_deg3_nbr_card_le_two {n : ℕ} (G : SimpleGraph (Fin n))
    (huniq : ∀ t₁ t₂ t₃ t₄ : Fin n, G.Adj t₁ t₂ → G.Adj t₃ t₄ →
      G.degree t₁ = 3 → G.degree t₂ = 3 → G.degree t₃ = 3 →
      G.degree t₄ = 3 →
      ({t₁, t₂} : Finset (Fin n)) = ({t₃, t₄} : Finset (Fin n))) :
    (Finset.univ.filter (fun u : Fin n =>
      G.degree u = 3 ∧ ∃ x ∈ G.neighborFinset u, G.degree x = 3)).card ≤ 2 := by
  classical
  have hsub : Finset.univ.filter (fun u : Fin n =>
        G.degree u = 3 ∧ ∃ x ∈ G.neighborFinset u, G.degree x = 3)
      ⊆ (deg3Set G).filter
        (fun t => ∃ t' : Fin n, G.Adj t t' ∧ G.degree t' = 3) := by
    intro u hu
    rw [Finset.mem_filter] at hu
    obtain ⟨-, hu3, x, hxm, hx3⟩ := hu
    rw [Finset.mem_filter]
    exact ⟨mem_deg3Set.mpr hu3, x, (G.mem_neighborFinset u x).mp hxm, hx3⟩
  exact (Finset.card_le_card hsub).trans
    (medge_endpoint_card_le_two n G huniq)

end ACMax
