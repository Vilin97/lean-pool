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
import LeanPool.ACMax.Reduction.Residual
import LeanPool.ACMax.Counting.FarPair
import LeanPool.ACMax.Counting.DoubleStar

/-!
# The far-pair closure of the poor corner

Closes the `x = 0`, `e(M) ≤ 1` corner (all degrees `3` or `4`, exactly `8`
degree-3 vertices, no good triangle `Σ ≤ 11`, no good `C₄` `Σ ≤ 14`) for every
`n ≥ 18`, by exhibiting a far degree-3 pair on which a test-vector certificate
bounds algebraic connectivity by `2`.

## Main results

* `algConn_le_two_of_far_deg3_pair` — the **uniform workhorse**: the integer test
  vector `(6, 2·𝟙_{N(t)}, −6, −2·𝟙_{N(t')})` certifies `algConn G ≤ 2` for any
  two degree-3 vertices `t, t'` at distance `≥ 3` with all neighbour degrees
  `≤ 4` and at most `3` cross edges between `N(t)` and `N(t')`. The worst-case
  Rayleigh numerator is `Q ≤ 168 + 8c ≤ 192 = 2N`, an exact tie at `c = 3`,
  shape-independent in the cross pattern.
* `exists_far_deg3_pair` — **some two degree-3 vertices are at distance `≥ 3`**.
  If every pair were within distance `2`, the twins and their hubs would form a
  linear space; the fibre profiles force four size-4 lines carrying all eight
  points, and `8 > C(4,2) = 6` yields two lines sharing two points, a
  contradiction.
* `exists_far_deg3_pair_lowcross` — some far pair has cross count `≤ 3`, feeding
  the workhorse directly. Assuming every far pair has cross `≥ 4`, the far pair
  from `exists_far_deg3_pair` has either an `M`-end endpoint (killed by Lemma E,
  `service_count_end`) or two iso endpoints (killed by Lemma S,
  `service_count_iso`); both are `omega`-impossible service-supply counts over
  the φ-slot budgets `phi_iso` / `phi_end`.
* `x0_corner_close` — the corner closure `algConn G ≤ 2` for every `n ≥ 23`,
  assembled from the three results above.
-/

namespace ACMax

variable {V : Type*} [Fintype V]

open Classical in
/-- **The uniform far-deg-3-pair certificate (B1+B3 unified).**  Two degree-3
vertices at distance `≥ 3` (combinatorially: distinct, non-adjacent, no common
neighbour), all of whose neighbours have degree `≤ 4`, with at most `3` cross
edges between their neighbourhoods, certify `algConn G ≤ 2` via the integer
vector `(6, 2·𝟙_{N(t)}, −6, −2·𝟙_{N(t')})`.  Worst case `Q = 168 + 8c ≤ 192 = 2N`
(tie at `c = 3`), independent of the cross-pattern shape. -/
theorem algConn_le_two_of_far_deg3_pair [Nonempty V]
    (G : SimpleGraph V) (t t' : V) (hne : t ≠ t') (hnadj : ¬G.Adj t t')
    (hcap : ∀ w : V, ¬(G.Adj t w ∧ G.Adj t' w))
    (hdt : G.degree t = 3) (hdt' : G.degree t' = 3)
    (hnb : ∀ w : V, G.Adj t w → G.degree w ≤ 4)
    (hnb' : ∀ w : V, G.Adj t' w → G.degree w ≤ 4)
    (hcross : ∑ w ∈ G.neighborFinset t,
        (G.neighborFinset w ∩ G.neighborFinset t').card ≤ 3) :
    algConn G ≤ 2 := by
  classical
  apply algConn_le_two_of_weighted_double_star G t t' 6 6
    (fun _ => (2:ℝ)) (fun _ => (2:ℝ)) hne hnadj hcap (by norm_num)
    (fun _ _ => by norm_num) (fun _ _ => by norm_num)
  · -- balance: `6 + 3·2 = 12` on both sides.
    rw [Finset.sum_const, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
      SimpleGraph.card_neighborFinset_eq_degree, hdt, hdt']
  · -- the worst-case quadratic bound.
    set c : ℕ := ∑ w ∈ G.neighborFinset t,
      (G.neighborFinset w ∩ G.neighborFinset t').card with hc
    -- Centre-edge sums: `3·(6−2)² = 48` per side.
    have hS1 : (∑ _w ∈ G.neighborFinset t, ((6:ℝ) - 2) ^ 2) = 48 := by
      rw [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, hdt]
      norm_num
    have hS2 : (∑ _w ∈ G.neighborFinset t', ((6:ℝ) - 2) ^ 2) = 48 := by
      rw [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, hdt']
      norm_num
    -- Cross sum: `16·c`.
    have hS3 : (∑ w ∈ G.neighborFinset t, ∑ w' ∈ G.neighborFinset t',
        (if G.Adj w w' then ((2:ℝ) + 2) ^ 2 else 0)) = 16 * (c : ℝ) := by
      have hinner : ∀ w : V, (∑ w' ∈ G.neighborFinset t',
          (if G.Adj w w' then ((2:ℝ) + 2) ^ 2 else 0))
          = 16 * ((G.neighborFinset w ∩ G.neighborFinset t').card : ℝ) := by
        intro w
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
          nsmul_eq_mul]
        have hfe : (G.neighborFinset t').filter (fun w' => G.Adj w w')
            = G.neighborFinset w ∩ G.neighborFinset t' := by
          ext a
          simp only [Finset.mem_filter, Finset.mem_inter,
            SimpleGraph.mem_neighborFinset]
          tauto
        rw [hfe]
        norm_num
        ring
      rw [Finset.sum_congr rfl fun w _ => hinner w, ← Finset.mul_sum, hc]
      rw [Nat.cast_sum]
    -- Leak bounds: `Σ (deg w − 1 − c_w)·4 ≤ 36 − 4c` per side.
    have hkey : ∀ (w : V), G.Adj t w →
        (G.neighborFinset w \ insert t (G.neighborFinset t')).card
          + (G.neighborFinset w ∩ G.neighborFinset t').card + 1 ≤ 4 := by
      intro w hw
      have htw : t ∈ G.neighborFinset w := (G.mem_neighborFinset w t).mpr (G.adj_symm hw)
      have htnot : t ∉ G.neighborFinset w ∩ G.neighborFinset t' := by
        rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
          SimpleGraph.mem_neighborFinset]
        rintro ⟨-, h2⟩
        exact hnadj (G.adj_symm h2)
      have hins : G.neighborFinset w ∩ insert t (G.neighborFinset t')
          = insert t (G.neighborFinset w ∩ G.neighborFinset t') := by
        ext a
        simp only [Finset.mem_inter, Finset.mem_insert, SimpleGraph.mem_neighborFinset]
        constructor
        · rintro ⟨h1, h2 | h2⟩
          · exact Or.inl h2
          · exact Or.inr ⟨h1, h2⟩
        · rintro (h2 | ⟨h1, h2⟩)
          · refine ⟨?_, Or.inl h2⟩
            rw [h2]
            exact (G.mem_neighborFinset w t).mp htw
          · exact ⟨h1, Or.inr h2⟩
      have hsplit := Finset.card_sdiff_add_card_inter (G.neighborFinset w)
        (insert t (G.neighborFinset t'))
      rw [hins, Finset.card_insert_of_notMem htnot,
        SimpleGraph.card_neighborFinset_eq_degree] at hsplit
      have hd4 : G.degree w ≤ 4 := hnb w hw
      omega
    have hkey' : ∀ (w : V), G.Adj t' w →
        (G.neighborFinset w \ insert t' (G.neighborFinset t)).card
          + (G.neighborFinset w ∩ G.neighborFinset t).card + 1 ≤ 4 := by
      intro w hw
      have htw : t' ∈ G.neighborFinset w := (G.mem_neighborFinset w t').mpr (G.adj_symm hw)
      have htnot : t' ∉ G.neighborFinset w ∩ G.neighborFinset t := by
        rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
          SimpleGraph.mem_neighborFinset]
        rintro ⟨-, h2⟩
        exact hnadj h2
      have hins : G.neighborFinset w ∩ insert t' (G.neighborFinset t)
          = insert t' (G.neighborFinset w ∩ G.neighborFinset t) := by
        ext a
        simp only [Finset.mem_inter, Finset.mem_insert, SimpleGraph.mem_neighborFinset]
        constructor
        · rintro ⟨h1, h2 | h2⟩
          · exact Or.inl h2
          · exact Or.inr ⟨h1, h2⟩
        · rintro (h2 | ⟨h1, h2⟩)
          · refine ⟨?_, Or.inl h2⟩
            rw [h2]
            exact (G.mem_neighborFinset w t').mp htw
          · exact ⟨h1, Or.inr h2⟩
      have hsplit := Finset.card_sdiff_add_card_inter (G.neighborFinset w)
        (insert t' (G.neighborFinset t))
      rw [hins, Finset.card_insert_of_notMem htnot,
        SimpleGraph.card_neighborFinset_eq_degree] at hsplit
      have hd4 : G.degree w ≤ 4 := hnb' w hw
      omega
    have hS4 : (∑ w ∈ G.neighborFinset t,
        ((G.neighborFinset w \ insert t (G.neighborFinset t')).card : ℝ) * (2:ℝ) ^ 2)
        ≤ 36 - 4 * (c : ℝ) := by
      have hstep : ∀ w ∈ G.neighborFinset t,
          ((G.neighborFinset w \ insert t (G.neighborFinset t')).card : ℝ) * (2:ℝ) ^ 2
          ≤ (3 - ((G.neighborFinset w ∩ G.neighborFinset t').card : ℝ)) * 4 := by
        intro w hw
        have h1 := hkey w ((G.mem_neighborFinset t w).mp hw)
        have h2 : ((G.neighborFinset w \ insert t (G.neighborFinset t')).card : ℝ)
            ≤ 3 - ((G.neighborFinset w ∩ G.neighborFinset t').card : ℝ) := by
          have : (G.neighborFinset w \ insert t (G.neighborFinset t')).card
              + (G.neighborFinset w ∩ G.neighborFinset t').card ≤ 3 := by omega
          have hcast : (((G.neighborFinset w \ insert t (G.neighborFinset t')).card
              + (G.neighborFinset w ∩ G.neighborFinset t').card : ℕ) : ℝ) ≤ 3 := by
            exact_mod_cast this
          push_cast at hcast
          linarith
        nlinarith [h2]
      calc (∑ w ∈ G.neighborFinset t,
            ((G.neighborFinset w \ insert t (G.neighborFinset t')).card : ℝ)
              * (2:ℝ) ^ 2)
          ≤ ∑ w ∈ G.neighborFinset t,
              (3 - ((G.neighborFinset w ∩ G.neighborFinset t').card : ℝ)) * 4 :=
            Finset.sum_le_sum hstep
        _ = 36 - 4 * (c : ℝ) := by
            simp_rw [sub_mul]
            rw [Finset.sum_sub_distrib, Finset.sum_const,
              SimpleGraph.card_neighborFinset_eq_degree, hdt, ← Finset.sum_mul, hc,
              ← Nat.cast_sum]
            push_cast
            ring
    have hS5 : (∑ w ∈ G.neighborFinset t',
        ((G.neighborFinset w \ insert t' (G.neighborFinset t)).card : ℝ) * (2:ℝ) ^ 2)
        ≤ 36 - 4 * (c : ℝ) := by
      -- the `t'`-side cross count equals `c` by the bipartite double count.
      have hcc : ∑ w ∈ G.neighborFinset t',
          (G.neighborFinset w ∩ G.neighborFinset t).card = c := by
        rw [hc]
        exact (cross_count G (G.neighborFinset t) (G.neighborFinset t')).symm ▸
          (cross_count G (G.neighborFinset t') (G.neighborFinset t))
      have hstep : ∀ w ∈ G.neighborFinset t',
          ((G.neighborFinset w \ insert t' (G.neighborFinset t)).card : ℝ) * (2:ℝ) ^ 2
          ≤ (3 - ((G.neighborFinset w ∩ G.neighborFinset t).card : ℝ)) * 4 := by
        intro w hw
        have h1 := hkey' w ((G.mem_neighborFinset t' w).mp hw)
        have h2 : ((G.neighborFinset w \ insert t' (G.neighborFinset t)).card : ℝ)
            ≤ 3 - ((G.neighborFinset w ∩ G.neighborFinset t).card : ℝ) := by
          have : (G.neighborFinset w \ insert t' (G.neighborFinset t)).card
              + (G.neighborFinset w ∩ G.neighborFinset t).card ≤ 3 := by omega
          have hcast : (((G.neighborFinset w \ insert t' (G.neighborFinset t)).card
              + (G.neighborFinset w ∩ G.neighborFinset t).card : ℕ) : ℝ) ≤ 3 := by
            exact_mod_cast this
          push_cast at hcast
          linarith
        nlinarith [h2]
      calc (∑ w ∈ G.neighborFinset t',
            ((G.neighborFinset w \ insert t' (G.neighborFinset t)).card : ℝ)
              * (2:ℝ) ^ 2)
          ≤ ∑ w ∈ G.neighborFinset t',
              (3 - ((G.neighborFinset w ∩ G.neighborFinset t).card : ℝ)) * 4 :=
            Finset.sum_le_sum hstep
        _ = 36 - 4 * (c : ℝ) := by
            simp_rw [sub_mul]
            rw [Finset.sum_sub_distrib, Finset.sum_const,
              SimpleGraph.card_neighborFinset_eq_degree, hdt', ← Finset.sum_mul,
              ← Nat.cast_sum, hcc]
            ring
    -- Norm sums.
    have hN1 : (∑ _w ∈ G.neighborFinset t, ((2:ℝ)) ^ 2) = 12 := by
      rw [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, hdt]
      norm_num
    have hN2 : (∑ _w ∈ G.neighborFinset t', ((2:ℝ)) ^ 2) = 12 := by
      rw [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, hdt']
      norm_num
    have hc3 : (c : ℝ) ≤ 3 := by exact_mod_cast hcross
    rw [hS1, hS2, hS3, hN1, hN2]
    -- `48 + 48 + 16c + S4 + S5 ≤ 168 + 8c ≤ 192`.
    linarith [hS4, hS5, hc3]

/-! ## Existence of a far twin pair -/

open Classical in
private theorem exists_far_deg3_pair_hDcard : ∀ (n : ℕ) (_ : 18 ≤ n) (G : SimpleGraph (Fin n))
  (_ : G.edgeFinset.card = 2 * (n - 2)) (_ : ∀ (v : Fin n), G.degree v = 3 ∨ G.degree v = 4) (D :
    Finset (Fin n))
  (_ : D = (Finset.univ.filter fun v => G.degree v = 3)) (_ : ∀ (v : Fin n), v ∈ D ↔ G.degree v =
    3), D.card = 8 := by
  classical
  intro n hn G hm hdeg D hD hmemD
  have hsum : ∑ v : Fin n, G.degree v = 4 * n - 8 :=
    residual_degree_sum n (by omega) G hm
  have hpart := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun v : Fin n => G.degree v = 3) (fun v : Fin n => G.degree v)
  rw [← hD] at hpart
  have hDsum : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl fun v hv => (hmemD v).mp hv, Finset.sum_const,
      smul_eq_mul, mul_comm]
  have hHsum : ∑ v ∈ Finset.univ.filter (fun v : Fin n => ¬G.degree v = 3),
      G.degree v
      = 4 * (Finset.univ.filter (fun v : Fin n => ¬G.degree v = 3)).card := by
    have h4 : ∀ v ∈ Finset.univ.filter (fun v : Fin n => ¬G.degree v = 3),
        G.degree v = 4 := by
      intro v hv
      rw [Finset.mem_filter] at hv
      rcases hdeg v with h | h
      · exact absurd h hv.2
      · exact h
    rw [Finset.sum_congr rfl h4, Finset.sum_const, smul_eq_mul, mul_comm]
  have hcards := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun v : Fin n => G.degree v = 3)
  rw [← hD, Finset.card_univ, Fintype.card_fin] at hcards
  rw [hDsum, hHsum] at hpart
  omega

open Classical in
private theorem exists_far_deg3_pair_huniq : ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
  let D : Finset (Fin n) := (Finset.univ.filter fun v => G.degree v = 3);
  ∀ (_ : ∀ (v : Fin n), v ∈ D ↔ G.degree v = 3) (_ : ∀ (v : Fin n), G.degree v ≤ 4)
    (_ : ∀ (x y z : Fin n), G.Adj x y → G.Adj y z → G.Adj x z → G.degree x + G.degree y + G.degree
      z ≤ 11 → False)
    (_ :
      ∀ (a b c d : Fin n),
        (Finset.card {a, b, c, d}) = 4 →
          G.Adj a b →
            G.Adj b c →
              G.Adj c d →
                G.Adj d a → ¬G.Adj a c → ¬G.Adj b d → G.degree a + G.degree b + G.degree c +
                  G.degree d ≤ 14 → False)
    (s z w w' : Fin n),
    s ∈ D → z ∈ D → s ≠ z → ¬G.Adj s z → G.Adj s w → G.Adj z w → G.Adj s w' → G.Adj z w' → w = w'
      := by
  classical
  intro n G D hmemD hdeg4 htri hc4 s z w w' hsD hzD hsz hnadj hsw hzw hsw' hzw'
  by_contra hww
  have hds : G.degree s = 3 := (hmemD s).mp hsD
  have hdz : G.degree z = 3 := (hmemD z).mp hzD
  by_cases hadj : G.Adj w w'
  · exact htri s w w' hsw hadj hsw'
      (by have := hdeg4 w; have := hdeg4 w'; omega)
  · have h1 : s ≠ w := G.ne_of_adj hsw
    have h2 : z ≠ w := G.ne_of_adj hzw
    have h3 : s ≠ w' := G.ne_of_adj hsw'
    have h4 : z ≠ w' := G.ne_of_adj hzw'
    have hcard : ({s, w, z, w'} : Finset (Fin n)).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp [h1, hsz, h3]),
        Finset.card_insert_of_notMem (by simp [Ne.symm h2, hww]),
        Finset.card_insert_of_notMem (by simp [h4]), Finset.card_singleton]
    exact hc4 s w z w' hcard hsw (G.adj_symm hzw) hzw' (G.adj_symm hsw')
      hnadj hadj (by have := hdeg4 w; have := hdeg4 w'; omega)

open Classical in
private theorem exists_far_deg3_pair_hprofile : ∀ (n : ℕ) (G : SimpleGraph (Fin n))
  (_ :
    ∀ (s t : Fin n) (_ : G.degree s = 3) (_ : G.degree t = 3) (_ : s ≠ t) (_ : ¬G.Adj s t), ∃ w,
      G.Adj s w ∧ G.Adj t w),
  let D : Finset (Fin n) := (Finset.univ.filter fun v => G.degree v = 3);
  ∀ (_ : ∀ (v : Fin n), v ∈ D ↔ G.degree v = 3) (_ : ∀ (v : Fin n), G.degree v ≤ 4) (_ : D.card = 8)
    (_ :
      ∀ (h h' s z : Fin n), h ≠ h' → s ≠ z → s ∈ D → z ∈ D → G.Adj h s → G.Adj h z → G.Adj h' s →
        G.Adj h' z → False),
    let R4 := fun z => (Finset.card {h ∈ G.neighborFinset z | (G.neighborFinset h ∩ D).card = 4});
    let R3 := fun z => (Finset.card {h ∈ G.neighborFinset z | (G.neighborFinset h ∩ D).card = 3});
    let R2 := fun z => (Finset.card {h ∈ G.neighborFinset z | (G.neighborFinset h ∩ D).card = 2});
    ∀ z ∈ D, (∀ (w : Fin n), G.Adj z w → w ∉ D) → 3 * R4 z + 2 * R3 z + R2 z = 7 ∧ R4 z + R3 z +
      R2 z ≤ 3 := by
  classical
  intro n G hcon D hmemD hdeg4 hDcard hshare R4 R3 R2 z hzD hziso
  have hdz : G.degree z = 3 := (hmemD z).mp hzD
  -- fibre partition of `D.erase z` over `N(z)`.
  have hbi : D.erase z = (G.neighborFinset z).biUnion
      (fun h => (G.neighborFinset h ∩ D).erase z) := by
    ext s
    simp only [Finset.mem_erase, Finset.mem_biUnion, Finset.mem_inter,
      SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨hsz, hsD⟩
      have hnadj : ¬G.Adj z s := fun hadj => hziso s hadj hsD
      obtain ⟨w, hzw, hsw⟩ := hcon z s hdz ((hmemD s).mp hsD) (Ne.symm hsz) hnadj
      exact ⟨w, hzw, hsz, G.adj_symm hsw, hsD⟩
    · rintro ⟨h, hzh, hsz, hhs, hsD⟩
      exact ⟨hsz, hsD⟩
  have hdisj : ∀ h₁ ∈ G.neighborFinset z, ∀ h₂ ∈ G.neighborFinset z, h₁ ≠ h₂ →
      Disjoint ((G.neighborFinset h₁ ∩ D).erase z)
        ((G.neighborFinset h₂ ∩ D).erase z) := by
    intro h₁ hh₁ h₂ hh₂ hne12
    rw [Finset.disjoint_left]
    intro s hs1 hs2
    rw [Finset.mem_erase, Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hs1 hs2
    exact hshare h₁ h₂ s z hne12 hs1.1 hs1.2.2 hzD hs1.2.1
      (G.adj_symm ((G.mem_neighborFinset z h₁).mp hh₁)) hs2.2.1
      (G.adj_symm ((G.mem_neighborFinset z h₂).mp hh₂))
  have hfib : ∑ h ∈ G.neighborFinset z,
      ((G.neighborFinset h ∩ D).erase z).card = 7 := by
    rw [← Finset.card_biUnion hdisj, ← hbi, Finset.card_erase_of_mem hzD, hDcard]
  have hzT : ∀ h ∈ G.neighborFinset z, z ∈ G.neighborFinset h ∩ D := by
    intro h hh
    rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨G.adj_symm ((G.mem_neighborFinset z h).mp hh), hzD⟩
  have hpt : ∀ h ∈ G.neighborFinset z,
      ((G.neighborFinset h ∩ D).erase z).card
      = 3 * (if (G.neighborFinset h ∩ D).card = 4 then 1 else 0)
        + 2 * (if (G.neighborFinset h ∩ D).card = 3 then 1 else 0)
        + (if (G.neighborFinset h ∩ D).card = 2 then 1 else 0) := by
    intro h hh
    rw [Finset.card_erase_of_mem (hzT h hh)]
    have h1 : 1 ≤ (G.neighborFinset h ∩ D).card :=
      Finset.card_pos.mpr ⟨z, hzT h hh⟩
    have h4 : (G.neighborFinset h ∩ D).card ≤ 4 := by
      calc (G.neighborFinset h ∩ D).card
          ≤ (G.neighborFinset h).card :=
            Finset.card_le_card Finset.inter_subset_left
        _ = G.degree h := G.card_neighborFinset_eq_degree h
        _ ≤ 4 := hdeg4 h
    by_cases e4 : (G.neighborFinset h ∩ D).card = 4 <;>
      by_cases e3 : (G.neighborFinset h ∩ D).card = 3 <;>
      by_cases e2 : (G.neighborFinset h ∩ D).card = 2 <;>
      (simp [e4, e3, e2]; try omega)
  have hsum_pt : ∑ h ∈ G.neighborFinset z,
      ((G.neighborFinset h ∩ D).erase z).card
      = 3 * R4 z + 2 * R3 z + R2 z := by
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.card_filter, ← Finset.card_filter,
      ← Finset.card_filter]
  have hcnt : R4 z + R3 z + R2 z ≤ 3 := by
    have hstep : ∀ h ∈ G.neighborFinset z,
        (if (G.neighborFinset h ∩ D).card = 4 then 1 else 0)
        + ((if (G.neighborFinset h ∩ D).card = 3 then 1 else 0)
        + (if (G.neighborFinset h ∩ D).card = 2 then 1 else 0)) ≤ 1 := by
      intro h _
      by_cases e4 : (G.neighborFinset h ∩ D).card = 4 <;>
        by_cases e3 : (G.neighborFinset h ∩ D).card = 3 <;>
        by_cases e2 : (G.neighborFinset h ∩ D).card = 2 <;>
        simp [e4, e3, e2]
    have heq : R4 z + (R3 z + R2 z)
        = ∑ h ∈ G.neighborFinset z,
            ((if (G.neighborFinset h ∩ D).card = 4 then 1 else 0)
            + ((if (G.neighborFinset h ∩ D).card = 3 then 1 else 0)
            + (if (G.neighborFinset h ∩ D).card = 2 then 1 else 0))) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.card_filter,
        ← Finset.card_filter, ← Finset.card_filter]
    have hle : R4 z + (R3 z + R2 z) ≤ ∑ _h ∈ G.neighborFinset z, 1 := by
      rw [heq]
      exact Finset.sum_le_sum hstep
    rw [Finset.sum_const, smul_eq_mul, mul_one,
      SimpleGraph.card_neighborFinset_eq_degree, hdz] at hle
    omega
  constructor
  · rw [← hsum_pt]
    exact hfib
  · exact hcnt

open Classical in
private theorem exists_far_deg3_pair_hpig : ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
  let D : Finset (Fin n) := (Finset.univ.filter fun v => G.degree v = 3);
  ∀
    (_ :
      ∀ (h h' s z : Fin n), h ≠ h' → s ≠ z → s ∈ D → z ∈ D → G.Adj h s → G.Adj h z → G.Adj h' s →
        G.Adj h' z → False),
    let Fours := (Finset.univ.filter fun h => (G.neighborFinset h ∩ D).card = 4);
    let R4 := fun z => (Finset.card {h ∈ G.neighborFinset z | (G.neighborFinset h ∩ D).card = 4});
    ∀ (_ : ∀ (z : Fin n), R4 z = (G.neighborFinset z ∩ Fours).card),
      2 * (Finset.card {z ∈ D | R4 z = 2}) ≤ Fours.card * (Fours.card - 1) := by
  classical
  intro n G D hshare Fours R4 hR4inter
  have h1 : (D.filter (fun z => R4 z = 2)).card ≤ (Fours.powersetCard 2).card := by
    apply Finset.card_le_card_of_injOn (fun z => G.neighborFinset z ∩ Fours)
    · intro z hz
      rw [Finset.mem_coe, Finset.mem_filter] at hz
      simp only [Finset.mem_coe, Finset.mem_powersetCard]
      exact ⟨Finset.inter_subset_right, by rw [← hR4inter z]; exact hz.2⟩
    · intro z hz z' hz' heq
      by_contra hzz
      rw [Finset.mem_coe, Finset.mem_filter] at hz hz'
      have heq' : G.neighborFinset z ∩ Fours = G.neighborFinset z' ∩ Fours := heq
      have hcard2 : (G.neighborFinset z ∩ Fours).card = 2 := by
        rw [← hR4inter z]
        exact hz.2
      obtain ⟨L, L', hLL', hS⟩ := Finset.card_eq_two.mp hcard2
      have hLz : L ∈ G.neighborFinset z ∩ Fours := by rw [hS]; simp
      have hL'z : L' ∈ G.neighborFinset z ∩ Fours := by rw [hS]; simp
      have hLz' : L ∈ G.neighborFinset z' ∩ Fours := by rw [← heq', hS]; simp
      have hL'z' : L' ∈ G.neighborFinset z' ∩ Fours := by rw [← heq', hS]; simp
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hLz hL'z hLz' hL'z'
      exact hshare L L' z z' hLL' hzz hz.1 hz'.1 (G.adj_symm hLz.1)
        (G.adj_symm hLz'.1) (G.adj_symm hL'z.1) (G.adj_symm hL'z'.1)
  rw [Finset.card_powersetCard] at h1
  have h2 : 2 * Nat.choose Fours.card 2 ≤ Fours.card * (Fours.card - 1) := by
    rw [Nat.choose_two_right]
    calc 2 * (Fours.card * (Fours.card - 1) / 2)
        = (Fours.card * (Fours.card - 1) / 2) * 2 := by ring
      _ ≤ Fours.card * (Fours.card - 1) := Nat.div_mul_le_self _ _
  omega

open Classical in
private theorem exists_far_deg3_pair_hsplit12 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
  let D : Finset (Fin n) := (Finset.univ.filter fun v => G.degree v = 3);
  let R4 := fun z => (Finset.card {h ∈ G.neighborFinset z | (G.neighborFinset h ∩ D).card = 4});
  ∀ (S : Finset (Fin n)), (∀ z ∈ S, R4 z = 1 ∨ R4 z = 2) → ∑ z ∈ S, R4 z = S.card + (Finset.card
    {z ∈ S | R4 z = 2}) := by
  classical
  intro n G D R4 S hS
  rw [← Finset.sum_filter_add_sum_filter_not S (fun z => R4 z = 2)]
  have h2 : ∑ z ∈ S.filter (fun z => R4 z = 2), R4 z
      = 2 * (S.filter (fun z => R4 z = 2)).card := by
    rw [Finset.sum_congr rfl fun z hz => (Finset.mem_filter.mp hz).2,
      Finset.sum_const, smul_eq_mul, mul_comm]
  have hone : ∀ z ∈ S.filter (fun z => ¬R4 z = 2), R4 z = 1 := by
    intro z hz
    have hmem := Finset.mem_filter.mp hz
    rcases hS z hmem.1 with h | h
    · exact h
    · exact absurd h hmem.2
  have h1 : ∑ z ∈ S.filter (fun z => ¬R4 z = 2), R4 z
      = (S.filter (fun z => ¬R4 z = 2)).card := by
    rw [Finset.sum_congr rfl hone, Finset.sum_const, smul_eq_mul, mul_one]
  have hc := Finset.card_filter_add_card_filter_not
    (s := S) (p := fun z => R4 z = 2)
  omega

open Classical in
private theorem exists_far_deg3_pair_hMend : ∀ (n : ℕ) (G : SimpleGraph (Fin n))
  (_ :
    ∀ (s t : Fin n) (_ : G.degree s = 3) (_ : G.degree t = 3) (_ : s ≠ t) (_ : ¬G.Adj s t), ∃ w,
      G.Adj s w ∧ G.Adj t w),
  let D : Finset (Fin n) := (Finset.univ.filter fun v => G.degree v = 3);
  ∀ (_ : ∀ (v : Fin n), v ∈ D ↔ G.degree v = 3) (_ : ∀ (v : Fin n), G.degree v ≤ 4) (_ : D.card = 8)
    (_ : ∀ (x y z : Fin n), G.Adj x y → G.Adj y z → G.Adj x z → G.degree x + G.degree y + G.degree
      z ≤ 11 → False)
    (_ :
      ∀ (h h' s z : Fin n), h ≠ h' → s ≠ z → s ∈ D → z ∈ D → G.Adj h s → G.Adj h z → G.Adj h' s →
        G.Adj h' z → False)
    (R4 : Fin n → ℕ) (_ : R4 = fun z => (Finset.card {h ∈ G.neighborFinset z | (G.neighborFinset h
      ∩ D).card = 4})),
    let R3 := fun z => (Finset.card {h ∈ G.neighborFinset z | (G.neighborFinset h ∩ D).card = 3});
    ∀ (_ : R3 = fun z => (Finset.card {h ∈ G.neighborFinset z | (G.neighborFinset h ∩ D).card =
      3})) (a b : Fin n),
      a ∈ D →
        b ∈ D →
          G.Adj a b →
            G.neighborFinset a ∩ D = {b} →
              G.neighborFinset b ∩ D = {a} →
                (∀ z ∈ D, z ≠ a → z ≠ b → (G.neighborFinset z ∩ D).card = 0) → R4 a = 2 ∧ R3 a = 0
                  := by
  classical
  intro n G hcon D hmemD hdeg4 hDcard htri hshare R4 hR4 R3 hR3 a b haD hbD hab hNa hNb hothers
  have hda : G.degree a = 3 := (hmemD a).mp haD
  have hab' : a ≠ b := G.ne_of_adj hab
  have hbNa : b ∈ G.neighborFinset a := (G.mem_neighborFinset a b).mpr hab
  have hScard : ((G.neighborFinset a).erase b).card = 2 := by
    rw [Finset.card_erase_of_mem hbNa,
      SimpleGraph.card_neighborFinset_eq_degree, hda]
  have hbiM : (D.erase a).erase b = ((G.neighborFinset a).erase b).biUnion
      (fun h => (G.neighborFinset h ∩ D).erase a) := by
    ext s
    simp only [Finset.mem_erase, Finset.mem_biUnion, Finset.mem_inter,
      SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨hsb, hsa, hsD⟩
      have hnadj : ¬G.Adj a s := by
        intro hadj
        have hmem : s ∈ G.neighborFinset a ∩ D := by
          rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
          exact ⟨hadj, hsD⟩
        rw [hNa, Finset.mem_singleton] at hmem
        exact hsb hmem
      obtain ⟨w, haw, hsw⟩ := hcon a s hda ((hmemD s).mp hsD) (Ne.symm hsa) hnadj
      have hwb : w ≠ b := by
        intro hwbe
        have hmem : b ∈ G.neighborFinset s ∩ D := by
          rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
          exact ⟨hwbe ▸ hsw, hbD⟩
        have hpos := Finset.card_pos.mpr ⟨b, hmem⟩
        have h0 := hothers s hsD hsa hsb
        omega
      exact ⟨w, ⟨hwb, haw⟩, hsa, G.adj_symm hsw, hsD⟩
    · rintro ⟨h, ⟨hhb, hah⟩, hsa, hhs, hsD⟩
      refine ⟨?_, hsa, hsD⟩
      intro hsbe
      exact htri a h b hah (hsbe ▸ hhs) hab
        (by have := hdeg4 h; have := (hmemD b).mp hbD; omega)
  have hdisjM : ∀ h₁ ∈ (G.neighborFinset a).erase b,
      ∀ h₂ ∈ (G.neighborFinset a).erase b, h₁ ≠ h₂ →
      Disjoint ((G.neighborFinset h₁ ∩ D).erase a)
        ((G.neighborFinset h₂ ∩ D).erase a) := by
    intro h₁ hh₁ h₂ hh₂ hne12
    rw [Finset.disjoint_left]
    intro s hs1 hs2
    rw [Finset.mem_erase, Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      at hs1 hs2
    rw [Finset.mem_erase] at hh₁ hh₂
    exact hshare h₁ h₂ s a hne12 hs1.1 hs1.2.2 haD hs1.2.1
      (G.adj_symm ((G.mem_neighborFinset a h₁).mp hh₁.2)) hs2.2.1
      (G.adj_symm ((G.mem_neighborFinset a h₂).mp hh₂.2))
  have hbmem : b ∈ D.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab', hbD⟩
  have hfib6 : ∑ h ∈ (G.neighborFinset a).erase b,
      ((G.neighborFinset h ∩ D).erase a).card = 6 := by
    rw [← Finset.card_biUnion hdisjM, ← hbiM, Finset.card_erase_of_mem hbmem,
      Finset.card_erase_of_mem haD, hDcard]
  obtain ⟨h₁, h₂, hne12, hSeq⟩ := Finset.card_eq_two.mp hScard
  have hh₁S : h₁ ∈ (G.neighborFinset a).erase b := by rw [hSeq]; simp
  have hh₂S : h₂ ∈ (G.neighborFinset a).erase b := by rw [hSeq]; simp
  have hamem : ∀ h ∈ (G.neighborFinset a).erase b,
      a ∈ G.neighborFinset h ∩ D := by
    intro h hh
    rw [Finset.mem_erase] at hh
    rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨G.adj_symm ((G.mem_neighborFinset a h).mp hh.2), haD⟩
  have hb4 : ∀ h ∈ (G.neighborFinset a).erase b,
      (G.neighborFinset h ∩ D).card ≤ 4 := by
    intro h _
    calc (G.neighborFinset h ∩ D).card
        ≤ (G.neighborFinset h).card :=
          Finset.card_le_card Finset.inter_subset_left
      _ = G.degree h := G.card_neighborFinset_eq_degree h
      _ ≤ 4 := hdeg4 h
  have hsum2 : ((G.neighborFinset h₁ ∩ D).erase a).card
      + ((G.neighborFinset h₂ ∩ D).erase a).card = 6 := by
    rw [hSeq, Finset.sum_pair hne12] at hfib6
    exact hfib6
  have he1 : ((G.neighborFinset h₁ ∩ D).erase a).card
      = (G.neighborFinset h₁ ∩ D).card - 1 :=
    Finset.card_erase_of_mem (hamem h₁ hh₁S)
  have he2 : ((G.neighborFinset h₂ ∩ D).erase a).card
      = (G.neighborFinset h₂ ∩ D).card - 1 :=
    Finset.card_erase_of_mem (hamem h₂ hh₂S)
  have hp1 : 1 ≤ (G.neighborFinset h₁ ∩ D).card :=
    Finset.card_pos.mpr ⟨a, hamem h₁ hh₁S⟩
  have hp2 : 1 ≤ (G.neighborFinset h₂ ∩ D).card :=
    Finset.card_pos.mpr ⟨a, hamem h₂ hh₂S⟩
  have hk4 : ∀ h ∈ (G.neighborFinset a).erase b,
      (G.neighborFinset h ∩ D).card = 4 := by
    intro h hh
    rw [hSeq, Finset.mem_insert, Finset.mem_singleton] at hh
    have hb1 := hb4 h₁ hh₁S
    have hb2 := hb4 h₂ hh₂S
    rcases hh with rfl | rfl <;> omega
  have hNa_insert : G.neighborFinset a = insert b ((G.neighborFinset a).erase b) :=
    (Finset.insert_erase hbNa).symm
  constructor
  · simp only [hR4]
    have hpb : ¬(G.neighborFinset b ∩ D).card = 4 := by
      rw [hNb, Finset.card_singleton]
      omega
    rw [hNa_insert, Finset.filter_insert, ite_eq_right hpb,
      Finset.filter_true_of_mem hk4, hScard]
  · simp only [hR3]
    have hpb : ¬(G.neighborFinset b ∩ D).card = 3 := by
      rw [hNb, Finset.card_singleton]
      omega
    have hfalse : ∀ h ∈ (G.neighborFinset a).erase b,
        ¬(G.neighborFinset h ∩ D).card = 3 := by
      intro h hh
      rw [hk4 h hh]
      omega
    rw [hNa_insert, Finset.filter_insert, ite_eq_right hpb,
      Finset.filter_false_of_mem hfalse, Finset.card_empty]

open Classical in
private theorem exists_far_deg3_pair_hDfilt : ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
  let D : Finset (Fin n) := (Finset.univ.filter fun v => G.degree v = 3);
  let Fours := (Finset.univ.filter fun h => (G.neighborFinset h ∩ D).card = 4);
  let Threes := (Finset.univ.filter fun h => (G.neighborFinset h ∩ D).card = 3);
  let R4 := fun z => (Finset.card {h ∈ G.neighborFinset z | (G.neighborFinset h ∩ D).card = 4});
  let R3 := fun z => (Finset.card {h ∈ G.neighborFinset z | (G.neighborFinset h ∩ D).card = 3});
  ∀ (_ : ∑ z ∈ D, R4 z = 4 * Fours.card) (_ : ∑ z ∈ D, R3 z = 3 * Threes.card) (u₀ u₁ : Fin n) (_
    : u₀ ∈ D)
    (_ : u₁ ∈ D) (_ : R4 u₀ = 2) (_ : R3 u₀ = 0) (_ : R4 u₁ = 2) (_ : R3 u₁ = 0)
    (_ : ((D.erase u₀).erase u₁).card = 6) (_ : ∀ z ∈ (D.erase u₀).erase u₁, z ∈ D ∧ z ≠ u₀ ∧ z ≠
      u₁)
    (_ :
      ∑ z ∈ (D.erase u₀).erase u₁, R4 z = ((D.erase u₀).erase u₁).card + (Finset.card {z ∈
        (D.erase u₀).erase u₁ | R4 z = 2}))
    (_ :
      2 * ∑ z ∈ (D.erase u₀).erase u₁, R4 z + ∑ z ∈ (D.erase u₀).erase u₁, R3 z = 4 * ((D.erase
        u₀).erase u₁).card)
    (_ : ∑ z ∈ D, R4 z = R4 u₀ + (R4 u₁ + ∑ z ∈ (D.erase u₀).erase u₁, R4 z))
    (_ : ∑ z ∈ D, R3 z = R3 u₀ + (R3 u₁ + ∑ z ∈ (D.erase u₀).erase u₁, R3 z))
    (_ : u₁ ∉ {z ∈ (D.erase u₀).erase u₁ | R4 z = 2})
    (_ : u₀ ∉ insert u₁ ({z ∈ (D.erase u₀).erase u₁ | R4 z = 2})),
    2 + (Finset.card {z ∈ (D.erase u₀).erase u₁ | R4 z = 2}) ≤ (Finset.card {z ∈ D | R4 z = 2}) :=
      by
  classical
  intro n G D Fours Threes R4 R3 hglob4 hglob3 u₀ u₁ hu0D hu1D hR4u0 hR3u0 hR4u1 hR3u1 hDisoCard
    hDisoSub hs4I hs34I hsum4D hsum3D hu1no hu0no
  have hsub : insert u₀ (insert u₁
      (((D.erase u₀).erase u₁).filter (fun z => R4 z = 2)))
      ⊆ D.filter (fun z => R4 z = 2) := by
    intro w hw
    simp only [Finset.mem_insert] at hw
    rcases hw with h | h | h
    · rw [h]
      exact Finset.mem_filter.mpr ⟨hu0D, hR4u0⟩
    · rw [h]
      exact Finset.mem_filter.mpr ⟨hu1D, hR4u1⟩
    · have hmem := Finset.mem_filter.mp h
      exact Finset.mem_filter.mpr ⟨(hDisoSub w hmem.1).1, hmem.2⟩
  have hcard2 := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hu0no, Finset.card_insert_of_notMem hu1no]
    at hcard2
  omega

open Classical in
private theorem exists_far_deg3_pair_hc4_step1 : ∀ (n : ℕ) (_ : (18 : ℕ) ≤ n) (G : SimpleGraph
  (Fin n)) (_ : ¬HasGoodC4 n G)
  (a b c d : Fin n),
  (Finset.card {a, b, c, d}) = (4 : ℕ) →
    G.Adj a b →
      G.Adj b c →
        G.Adj c d →
          G.Adj d a →
            ¬G.Adj a c → ¬G.Adj b d → G.degree a + G.degree b + G.degree c + G.degree d ≤ (14 : ℕ)
              → False := by
  classical
  intro n hn G hC4 a b c d hcard hab hbc hcd hda hac hbd hsum
  have h := no_good_C4_sum_gt (n := n) (by omega) hC4 hcard hab hbc hcd hda hac hbd
  have h14 : 14 ≤ goodC4Threshold n := by
    rcases lt_or_ge n 32 with hlt | hge
    · rw [goodC4Threshold_eq_of_window (by omega) hlt]
    · rw [goodC4Threshold_eq_of_ge_thirtytwo hge]
      omega
  omega

open Classical in
private theorem exists_far_deg3_pair_hsum2pts_step1 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
  let D : Finset (Fin n) := (Finset.univ.filter fun v => G.degree v = (3 : ℕ));
  ∀ (_ : ∑ z ∈ D, (G.neighborFinset z ∩ D).card ≤ (2 : ℕ)) (a b : Fin n),
    a ∈ D → b ∈ D → a ≠ b → (G.neighborFinset a ∩ D).card + (G.neighborFinset b ∩ D).card ≤ (2 :
      ℕ) := by
  classical
  intro n G D heM a b haD hbD hab
  have hsub : ({a, b} : Finset (Fin n)) ⊆ D := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hle : ∑ v ∈ ({a, b} : Finset (Fin n)), (G.neighborFinset v ∩ D).card
      ≤ ∑ v ∈ D, (G.neighborFinset v ∩ D).card :=
    Finset.sum_le_sum_of_subset hsub
  rw [Finset.sum_pair hab] at hle
  omega

open Classical in
private theorem exists_far_deg3_pair_hsum3pts_step1 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
  let D : Finset (Fin n) := (Finset.univ.filter fun v => G.degree v = (3 : ℕ));
  ∀ (_ : ∑ z ∈ D, (G.neighborFinset z ∩ D).card ≤ (2 : ℕ)) (a b c : Fin n),
    a ∈ D →
      b ∈ D →
        c ∈ D →
          a ≠ b →
            a ≠ c →
              b ≠ c →
                (G.neighborFinset a ∩ D).card + (G.neighborFinset b ∩ D).card + (G.neighborFinset
                  c ∩ D).card ≤
                  (2 : ℕ) := by
  classical
  intro n G D heM a b c haD hbD hcD hab hac hbc
  have hsub : ({a, b, c} : Finset (Fin n)) ⊆ D := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hle : ∑ v ∈ ({a, b, c} : Finset (Fin n)), (G.neighborFinset v ∩ D).card
      ≤ ∑ v ∈ D, (G.neighborFinset v ∩ D).card :=
    Finset.sum_le_sum_of_subset hsub
  rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_pair hbc] at hle
  omega

open Classical in
private theorem exists_far_deg3_pair_hNu0_step1 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
  let D : Finset (Fin n) := (Finset.univ.filter fun v => G.degree v = (3 : ℕ));
  ∀
    (_ :
      ∀ (a b : Fin n), a ∈ D → b ∈ D → a ≠ b → (G.neighborFinset a ∩ D).card + (G.neighborFinset b
        ∩ D).card ≤ (2 : ℕ))
    (u₀ u₁ : Fin n) (_ : u₀ ∈ D) (_ : u₁ ∈ D) (_ : u₀ ≠ u₁) (_ : u₁ ∈ G.neighborFinset u₀ ∩ D)
    (_ : u₀ ∈ G.neighborFinset u₁ ∩ D), G.neighborFinset u₀ ∩ D = {u₁} := by
  classical
  intro n G D hsum2pts u₀ u₁ hu0D hu1D hu01 hu1mem hu0mem
  have h2 := hsum2pts u₀ u₁ hu0D hu1D hu01
  have h01 : 1 ≤ (G.neighborFinset u₀ ∩ D).card :=
    Finset.card_pos.mpr ⟨u₁, hu1mem⟩
  have h10 : 1 ≤ (G.neighborFinset u₁ ∩ D).card :=
    Finset.card_pos.mpr ⟨u₀, hu0mem⟩
  have h1 : (G.neighborFinset u₀ ∩ D).card = 1 := by omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
  rw [ha] at hu1mem ⊢
  rw [Finset.mem_singleton] at hu1mem
  rw [hu1mem]

open Classical in
private theorem exists_far_deg3_pair_hNu1_step1 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
  let D : Finset (Fin n) := (Finset.univ.filter fun v => G.degree v = (3 : ℕ));
  ∀
    (_ :
      ∀ (a b : Fin n), a ∈ D → b ∈ D → a ≠ b → (G.neighborFinset a ∩ D).card + (G.neighborFinset b
        ∩ D).card ≤ (2 : ℕ))
    (u₀ u₁ : Fin n) (_ : u₀ ∈ D) (_ : u₁ ∈ D) (_ : u₀ ≠ u₁) (_ : u₁ ∈ G.neighborFinset u₀ ∩ D)
    (_ : u₀ ∈ G.neighborFinset u₁ ∩ D), G.neighborFinset u₁ ∩ D = {u₀} := by
  classical
  intro n G D hsum2pts u₀ u₁ hu0D hu1D hu01 hu1mem hu0mem
  have h2 := hsum2pts u₀ u₁ hu0D hu1D hu01
  have h01 : 1 ≤ (G.neighborFinset u₀ ∩ D).card :=
    Finset.card_pos.mpr ⟨u₁, hu1mem⟩
  have h10 : 1 ≤ (G.neighborFinset u₁ ∩ D).card :=
    Finset.card_pos.mpr ⟨u₀, hu0mem⟩
  have h1 : (G.neighborFinset u₁ ∩ D).card = 1 := by omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
  rw [ha] at hu0mem ⊢
  rw [Finset.mem_singleton] at hu0mem
  rw [hu0mem]

open Classical in
private theorem six_isolated_twins_contradiction : ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
  let D : Finset (Fin n) := (Finset.univ.filter fun v => G.degree v = (3 : ℕ));
  ∀ (_ : D.card = (8 : ℕ)),
    let Fours : Finset (Fin n) := (Finset.univ.filter fun h => (G.neighborFinset h ∩ D).card = (4
      : ℕ));
    let Threes : Finset (Fin n) := (Finset.univ.filter fun h => (G.neighborFinset h ∩ D).card = (3
      : ℕ));
    let R4 : Fin n → ℕ := fun z => (Finset.card {h ∈ G.neighborFinset z | (G.neighborFinset h ∩
      D).card = (4 : ℕ)});
    let R3 : Fin n → ℕ := fun z => (Finset.card {h ∈ G.neighborFinset z | (G.neighborFinset h ∩
      D).card = (3 : ℕ)});
    let R2 : Fin n → ℕ := fun z => (Finset.card {h ∈ G.neighborFinset z | (G.neighborFinset h ∩
      D).card = (2 : ℕ)});
    ∀ (_ : ∑ z ∈ D, R4 z = (4 : ℕ) * Fours.card) (_ : ∑ z ∈ D, R3 z = (3 : ℕ) * Threes.card)
      (_ :
        ∀ z ∈ D,
          (∀ (w : Fin n), G.Adj z w → w ∉ D) →
            (3 : ℕ) * R4 z + (2 : ℕ) * R3 z + R2 z = (7 : ℕ) ∧ R4 z + R3 z + R2 z ≤ (3 : ℕ))
      (_ : (2 : ℕ) * (Finset.card {z ∈ D | R4 z = (2 : ℕ)}) ≤ Fours.card * (Fours.card - (1 : ℕ)))
      (_ : ∀ m ≤ (4 : ℕ), m * (m - (1 : ℕ)) ≤ (12 : ℕ))
      (_ :
        ∀ (S : Finset (Fin n)),
          (∀ z ∈ S, R4 z = (1 : ℕ) ∨ R4 z = (2 : ℕ)) → ∑ z ∈ S, R4 z = S.card + (Finset.card {z ∈
            S | R4 z = (2 : ℕ)}))
      (_ :
        ∀ (S : Finset (Fin n)),
          (∀ z ∈ S, (2 : ℕ) * R4 z + R3 z = (4 : ℕ)) → (2 : ℕ) * ∑ z ∈ S, R4 z + ∑ z ∈ S, R3 z =
            (4 : ℕ) * S.card)
      (u₀ u₁ : Fin n) (_ : u₀ ∈ D) (_ : u₁ ∈ D) (_ : u₀ ≠ u₁)
      (_ : ∀ z ∈ D, z ≠ u₀ → z ≠ u₁ → ∀ (w : Fin n), G.Adj z w → w ∉ D) (_ : R4 u₀ = (2 : ℕ))
      (_ : R3 u₀ = (0 : ℕ)) (_ : R4 u₁ = (2 : ℕ)) (_ : R3 u₁ = (0 : ℕ)), False := by
  classical
  intro n G D hDcard Fours Threes R4 R3 R2 hglob4 hglob3 hprofile hpig hsq12 hsplit12 h34sum u₀ u₁
    hu0D hu1D hu01 hisoO hR4u0 hR3u0 hR4u1 hR3u1
  -- The six isolated twins.
  have hu1mem' : u₁ ∈ D.erase u₀ := Finset.mem_erase.mpr ⟨Ne.symm hu01, hu1D⟩
  have hDisoCard : ((D.erase u₀).erase u₁).card = 6 := by
    rw [Finset.card_erase_of_mem hu1mem', Finset.card_erase_of_mem hu0D, hDcard]
  have hDisoSub : ∀ z ∈ (D.erase u₀).erase u₁, z ∈ D ∧ z ≠ u₀ ∧ z ≠ u₁ := by
    intro z hz
    rw [Finset.mem_erase, Finset.mem_erase] at hz
    exact ⟨hz.2.2, hz.2.1, hz.1⟩
  have hprofI : ∀ z ∈ (D.erase u₀).erase u₁,
      3 * R4 z + 2 * R3 z + R2 z = 7 ∧ R4 z + R3 z + R2 z ≤ 3 := by
    intro z hz
    obtain ⟨hzD, hz0, hz1⟩ := hDisoSub z hz
    exact hprofile z hzD (hisoO z hzD hz0 hz1)
  have h12I : ∀ z ∈ (D.erase u₀).erase u₁, R4 z = 1 ∨ R4 z = 2 := by
    intro z hz
    have := hprofI z hz
    omega
  have h34I : ∀ z ∈ (D.erase u₀).erase u₁, 2 * R4 z + R3 z = 4 := by
    intro z hz
    have := hprofI z hz
    omega
  have hs4I : ∑ z ∈ (D.erase u₀).erase u₁, R4 z
      = ((D.erase u₀).erase u₁).card
        + (((D.erase u₀).erase u₁).filter (fun z => R4 z = 2)).card :=
    hsplit12 _ h12I
  have hs34I : 2 * (∑ z ∈ (D.erase u₀).erase u₁, R4 z)
      + ∑ z ∈ (D.erase u₀).erase u₁, R3 z = 4 * ((D.erase u₀).erase u₁).card :=
    h34sum _ h34I
  have hsum4D : ∑ z ∈ D, R4 z
      = R4 u₀ + (R4 u₁ + ∑ z ∈ (D.erase u₀).erase u₁, R4 z) := by
    rw [Finset.add_sum_erase _ R4 hu1mem', Finset.add_sum_erase _ R4 hu0D]
  have hsum3D : ∑ z ∈ D, R3 z
      = R3 u₀ + (R3 u₁ + ∑ z ∈ (D.erase u₀).erase u₁, R3 z) := by
    rw [Finset.add_sum_erase _ R3 hu1mem', Finset.add_sum_erase _ R3 hu0D]
  -- Lower bound for the pigeonhole set.
  have hu1no : u₁ ∉ ((D.erase u₀).erase u₁).filter (fun z => R4 z = 2) := by
    intro h
    exact (hDisoSub u₁ (Finset.mem_filter.mp h).1).2.2 rfl
  have hu0no : u₀ ∉ insert u₁ (((D.erase u₀).erase u₁).filter (fun z => R4 z = 2)) := by
    simp only [Finset.mem_insert]
    rintro (h | h)
    · exact hu01 h
    · exact (hDisoSub u₀ (Finset.mem_filter.mp h).1).2.1 rfl
  have hDfilt : 2 + (((D.erase u₀).erase u₁).filter (fun z => R4 z = 2)).card
      ≤ (D.filter (fun z => R4 z = 2)).card := by
    exact exists_far_deg3_pair_hDfilt (n := n) (G := G) (hglob4) (hglob3)
      (u₀ := u₀) (u₁ := u₁) (hu0D) (hu1D) (hR4u0) (hR3u0)
      (hR4u1) (hR3u1) (hDisoCard) (hDisoSub) (hs4I) (hs34I) (hsum4D) (hsum3D) (hu1no) (hu0no)
  have hxle : (((D.erase u₀).erase u₁).filter (fun z => R4 z = 2)).card ≤ 6 := by
    have := Finset.card_filter_le ((D.erase u₀).erase u₁) (fun z => R4 z = 2)
    omega
  have hF4 : Fours.card ≤ 4 := by omega
  have hxbound : 2 * (2 + (((D.erase u₀).erase u₁).filter (fun z => R4 z = 2)).card)
      ≤ 12 := by
    have h2 := hsq12 Fours.card hF4
    omega
  omega

open Classical in
/-- **Lemma B2.**  In the `x = 0`, `e(M) ≤ 1` corner (`n ≥ 18`): all degrees `3`
or `4`, `2(n−2)` edges (hence exactly `8` degree-3 vertices), no good triangle,
no good `C₄`, and at most one edge inside the degree-3 set (`Σ_{z∈D}|N(z)∩D| ≤ 2`),
**some two degree-3 vertices are at distance `≥ 3`**: distinct, non-adjacent,
with no common neighbour.  Proof: otherwise twins + multi-twin hubs form a
linear space; fibre partition forces per-point profiles, incidence double
counts force the design `(α, β, γ) = (4, 0, 4)` resp. `(4, 0, 3)`, and the
`Σ C(r₄,2) = 8 > C(4,2) = 6` pigeonhole gives two 4-lines sharing two twins —
a forbidden induced `C₄`. -/
theorem exists_far_deg3_pair (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Fin n))
    (hm : G.edgeFinset.card = 2 * (n - 2))
    (hdeg : ∀ v : Fin n, G.degree v = 3 ∨ G.degree v = 4)
    (hT : ¬HasGoodTriangle n G) (hC4 : ¬HasGoodC4 n G)
    (heM : ∑ z ∈ Finset.univ.filter (fun v : Fin n => G.degree v = 3),
        (G.neighborFinset z
          ∩ Finset.univ.filter (fun v : Fin n => G.degree v = 3)).card ≤ 2) :
    ∃ s t : Fin n, G.degree s = 3 ∧ G.degree t = 3 ∧ s ≠ t ∧ ¬G.Adj s t ∧
      ∀ w : Fin n, ¬(G.Adj s w ∧ G.Adj t w) := by
  classical
  by_contra hcon
  push Not at hcon
  -- `hcon : ∀ s t, deg s = 3 → deg t = 3 → s ≠ t → ¬Adj s t → ∃ w, Adj s w ∧ Adj t w`
  set D := Finset.univ.filter (fun v : Fin n => G.degree v = 3) with hD
  have hmemD : ∀ v : Fin n, v ∈ D ↔ G.degree v = 3 := by
    intro v
    rw [hD]
    simp
  have hdeg4 : ∀ v : Fin n, G.degree v ≤ 4 := fun v => by
    rcases hdeg v with h | h <;> omega
  -- `|D| = 8`.
  have hDcard : D.card = 8 := by
    exact exists_far_deg3_pair_hDcard (n := n) (hn) (G := G) (hm) (hdeg) (D :=
      D) (hD) (hmemD)
  -- Good-certificate helpers.
  have htri : ∀ x y z : Fin n, G.Adj x y → G.Adj y z → G.Adj x z →
      G.degree x + G.degree y + G.degree z ≤ 11 → False := by
    intro x y z hxy hyz hxz hsum
    have h := no_good_triangle_sum_gt (n := n) (by omega) hT (G.ne_of_adj hxy)
      (G.ne_of_adj hyz) (G.ne_of_adj hxz) hxy hyz hxz
    rw [goodTriThreshold_eq_of_ge_eighteen hn] at h
    omega
  have hc4 : ∀ a b c d : Fin n, ({a, b, c, d} : Finset (Fin n)).card = 4 →
      G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → ¬G.Adj a c → ¬G.Adj b d →
      G.degree a + G.degree b + G.degree c + G.degree d ≤ 14 → False := by
    exact exists_far_deg3_pair_hc4_step1 (n := n) (hn) (G := G) (hC4)
  -- Unique common neighbour of a non-adjacent twin pair (F2).
  have huniq : ∀ s z w w' : Fin n, s ∈ D → z ∈ D → s ≠ z → ¬G.Adj s z →
      G.Adj s w → G.Adj z w → G.Adj s w' → G.Adj z w' → w = w' := by
    exact exists_far_deg3_pair_huniq (n := n) (G := G) (hmemD) (hdeg4) (htri) (hc4)
  -- Two vertices share at most one twin (elementwise form).
  have hshare : ∀ h h' s z : Fin n, h ≠ h' → s ≠ z → s ∈ D → z ∈ D →
      G.Adj h s → G.Adj h z → G.Adj h' s → G.Adj h' z → False := by
    intro h h' s z hhh hsz hsD hzD h1 h2 h3 h4
    by_cases hadj : G.Adj s z
    · exact htri s z h hadj (G.adj_symm h2) (G.adj_symm h1)
        (by have := (hmemD s).mp hsD; have := (hmemD z).mp hzD
            have := hdeg4 h; omega)
    · exact hhh (huniq s z h h' hsD hzD hsz hadj (G.adj_symm h1) (G.adj_symm h2)
        (G.adj_symm h3) (G.adj_symm h4))
  -- `heM` bounds on two and three twins.
  have hsum2pts : ∀ a b : Fin n, a ∈ D → b ∈ D → a ≠ b →
      (G.neighborFinset a ∩ D).card + (G.neighborFinset b ∩ D).card ≤ 2 := by
    exact exists_far_deg3_pair_hsum2pts_step1 (n := n) (G := G) (heM)
  have hsum3pts : ∀ a b c : Fin n, a ∈ D → b ∈ D → c ∈ D → a ≠ b → a ≠ c → b ≠ c →
      (G.neighborFinset a ∩ D).card + (G.neighborFinset b ∩ D).card
        + (G.neighborFinset c ∩ D).card ≤ 2 := by
    exact exists_far_deg3_pair_hsum3pts_step1 (n := n) (G := G) (heM)
  -- The line-size counters.
  set Fours := Finset.univ.filter
    (fun h : Fin n => (G.neighborFinset h ∩ D).card = 4) with hFours
  set Threes := Finset.univ.filter
    (fun h : Fin n => (G.neighborFinset h ∩ D).card = 3) with hThrees
  set R4 : Fin n → ℕ := fun z =>
    ((G.neighborFinset z).filter
      (fun h => (G.neighborFinset h ∩ D).card = 4)).card with hR4
  set R3 : Fin n → ℕ := fun z =>
    ((G.neighborFinset z).filter
      (fun h => (G.neighborFinset h ∩ D).card = 3)).card with hR3
  set R2 : Fin n → ℕ := fun z =>
    ((G.neighborFinset z).filter
      (fun h => (G.neighborFinset h ∩ D).card = 2)).card with hR2
  have hR4inter : ∀ z : Fin n, R4 z = (G.neighborFinset z ∩ Fours).card := by
    intro z
    simp only [hR4, hFours]
    congr 1
    ext a
    simp
  have hR3inter : ∀ z : Fin n, R3 z = (G.neighborFinset z ∩ Threes).card := by
    intro z
    simp only [hR3, hThrees]
    congr 1
    ext a
    simp
  -- Global incidence double counts.
  have hglob4 : ∑ z ∈ D, R4 z = 4 * Fours.card := by
    rw [Finset.sum_congr rfl fun z _ => hR4inter z, cross_count G D Fours]
    have h2 : ∀ h ∈ Fours, (G.neighborFinset h ∩ D).card = 4 := by
      intro h hh
      rw [hFours, Finset.mem_filter] at hh
      exact hh.2
    rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, mul_comm]
  have hglob3 : ∑ z ∈ D, R3 z = 3 * Threes.card := by
    rw [Finset.sum_congr rfl fun z _ => hR3inter z, cross_count G D Threes]
    have h2 : ∀ h ∈ Threes, (G.neighborFinset h ∩ D).card = 3 := by
      intro h hh
      rw [hThrees, Finset.mem_filter] at hh
      exact hh.2
    rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, mul_comm]
  -- Per-point profile of an isolated twin.
  have hprofile : ∀ z ∈ D, (∀ w : Fin n, G.Adj z w → w ∉ D) →
      3 * R4 z + 2 * R3 z + R2 z = 7 ∧ R4 z + R3 z + R2 z ≤ 3 := by
    exact exists_far_deg3_pair_hprofile (n := n) (G := G) (hcon) (hmemD) (hdeg4) (hDcard) (hshare)
  -- The 4-line pigeonhole.
  have hpig : 2 * (D.filter (fun z => R4 z = 2)).card
      ≤ Fours.card * (Fours.card - 1) := by
    exact exists_far_deg3_pair_hpig (n := n) (G := G) (hshare) (hR4inter)
  have hsq12 : ∀ m : ℕ, m ≤ 4 → m * (m - 1) ≤ 12 := by
    intro m hm
    have h5 : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by omega
    rcases h5 with rfl | rfl | rfl | rfl | rfl <;> norm_num
  -- Splitting helpers.
  have hsplit12 : ∀ S : Finset (Fin n), (∀ z ∈ S, R4 z = 1 ∨ R4 z = 2) →
      ∑ z ∈ S, R4 z = S.card + (S.filter (fun z => R4 z = 2)).card := by
    exact exists_far_deg3_pair_hsplit12 (n := n) (G := G)
  have h34sum : ∀ S : Finset (Fin n), (∀ z ∈ S, 2 * R4 z + R3 z = 4) →
      2 * (∑ z ∈ S, R4 z) + ∑ z ∈ S, R3 z = 4 * S.card := by
    intro S hS
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_congr rfl hS,
      Finset.sum_const, smul_eq_mul, mul_comm]
  -- Case split on an `M`-edge.
  by_cases hM : ∃ a b : Fin n, a ∈ D ∧ b ∈ D ∧ G.Adj a b
  · -- `e(M) = 1`: an adjacent twin pair exists.
    obtain ⟨u₀, u₁, hu0D, hu1D, hadj01⟩ := hM
    have hu01 : u₀ ≠ u₁ := G.ne_of_adj hadj01
    have hu1mem : u₁ ∈ G.neighborFinset u₀ ∩ D := by
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨hadj01, hu1D⟩
    have hu0mem : u₀ ∈ G.neighborFinset u₁ ∩ D := by
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨G.adj_symm hadj01, hu0D⟩
    have hcard0 : ∀ z ∈ D, z ≠ u₀ → z ≠ u₁ → (G.neighborFinset z ∩ D).card = 0 := by
      intro z hzD hz0 hz1
      have h3 := hsum3pts u₀ u₁ z hu0D hu1D hzD hu01 (Ne.symm hz0) (Ne.symm hz1)
      have h01 : 1 ≤ (G.neighborFinset u₀ ∩ D).card :=
        Finset.card_pos.mpr ⟨u₁, hu1mem⟩
      have h10 : 1 ≤ (G.neighborFinset u₁ ∩ D).card :=
        Finset.card_pos.mpr ⟨u₀, hu0mem⟩
      omega
    have hisoO : ∀ z ∈ D, z ≠ u₀ → z ≠ u₁ → ∀ w : Fin n, G.Adj z w → w ∉ D := by
      intro z hzD hz0 hz1 w hadj hwD
      have h0 := hcard0 z hzD hz0 hz1
      have hmem : w ∈ G.neighborFinset z ∩ D := by
        rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
        exact ⟨hadj, hwD⟩
      have := Finset.card_pos.mpr ⟨w, hmem⟩
      omega
    have hNu0 : G.neighborFinset u₀ ∩ D = {u₁} := by
      exact exists_far_deg3_pair_hNu0_step1 (n := n) (G := G) (hsum2pts) (u₀ := u₀)
        (u₁ := u₁) (hu0D) (hu1D) (hu01) (hu1mem) (hu0mem)
    have hNu1 : G.neighborFinset u₁ ∩ D = {u₀} := by
      exact exists_far_deg3_pair_hNu1_step1 (n := n) (G := G) (hsum2pts) (u₀ := u₀)
        (u₁ := u₁) (hu0D) (hu1D) (hu01) (hu1mem) (hu0mem)
    -- The `M`-end profile: both lines through an `M`-end are 4-lines.
    have hMend : ∀ a b : Fin n, a ∈ D → b ∈ D → G.Adj a b →
        G.neighborFinset a ∩ D = {b} → G.neighborFinset b ∩ D = {a} →
        (∀ z ∈ D, z ≠ a → z ≠ b → (G.neighborFinset z ∩ D).card = 0) →
        R4 a = 2 ∧ R3 a = 0 := by
      exact exists_far_deg3_pair_hMend (n := n) (G := G) (hcon) (hmemD) (hdeg4) (hDcard) (htri)
        (hshare) (R4 := R4) (hR4) (hR3)
    obtain ⟨hR4u0, hR3u0⟩ := hMend u₀ u₁ hu0D hu1D hadj01 hNu0 hNu1 hcard0
    obtain ⟨hR4u1, hR3u1⟩ := hMend u₁ u₀ hu1D hu0D (G.adj_symm hadj01) hNu1 hNu0
      (fun z hz hz1 hz0 => hcard0 z hz hz0 hz1)
    exact six_isolated_twins_contradiction (n := n) (G := G) (hDcard) (hglob4)
      (hglob3) (hprofile) (hpig) (hsq12) (hsplit12) (h34sum) (u₀ := u₀) (u₁ := u₁) (hu0D) (hu1D)
        (hu01) (hisoO) (hR4u0) (hR3u0) (hR4u1) (hR3u1)
  · -- `e(M) = 0`: every twin is isolated.
    have hiso : ∀ z ∈ D, ∀ w : Fin n, G.Adj z w → w ∉ D := by
      intro z hz w hadj hwD
      exact hM ⟨z, w, hz, hwD, hadj⟩
    have hprof : ∀ z ∈ D, 3 * R4 z + 2 * R3 z + R2 z = 7 ∧ R4 z + R3 z + R2 z ≤ 3 :=
      fun z hz => hprofile z hz (hiso z hz)
    have h12 : ∀ z ∈ D, R4 z = 1 ∨ R4 z = 2 := by
      intro z hz
      have := hprof z hz
      omega
    have h34 : ∀ z ∈ D, 2 * R4 z + R3 z = 4 := by
      intro z hz
      have := hprof z hz
      omega
    have hs4 : ∑ z ∈ D, R4 z = D.card + (D.filter (fun z => R4 z = 2)).card :=
      hsplit12 D h12
    have hs34 : 2 * (∑ z ∈ D, R4 z) + ∑ z ∈ D, R3 z = 4 * D.card := h34sum D h34
    have hxle : (D.filter (fun z => R4 z = 2)).card ≤ 8 := by
      have := Finset.card_filter_le D (fun z => R4 z = 2)
      omega
    have hF4 : Fours.card ≤ 4 := by omega
    have hxbound : 2 * (D.filter (fun z => R4 z = 2)).card ≤ 12 := by
      have h2 := hsq12 Fours.card hF4
      omega
    omega

end ACMax

/-! ## The service-bound counting closure (Lemmas S and E)

The service bound behind `exists_far_deg3_pair_lowcross`. Assuming every far
pair has cross `≥ 4`, the far pair from `exists_far_deg3_pair` has an endpoint
that is either an `M`-end or iso. **Lemma E** (`service_count_end`) rules out the
`M`-end via demand `≥ 3k₀` against slot budget `B₀ = k₀` (`phi_end`) and pair
budget `6x + y ≤ k₀² − k₀`. **Lemma S** (`service_count_iso`) rules out the iso
side via demand `≥ 4k − 1` against `B = k + 2` (`phi_iso`) and `6x + y ≤ k² − k`
(`service_supply`); `omega` closes both endgames (`service_endgame_end`,
`service_endgame_iso`). The section builds the vocabulary, threshold bricks,
corner structure, mediator swap, service supply, deg-3 bonus and φ-identities
these two lemmas consume. -/

namespace ACMax

/-! ## Vocabulary: the far set of a degree-3 vertex -/

open Classical in
/-- `farOf n G t`: the degree-3 vertices at combinatorial distance `≥ 3` from `t`
(distinct, non-adjacent, no common neighbour). -/
noncomputable def farOf (n : ℕ) (G : SimpleGraph (Fin n)) (t : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun s => G.degree s = 3 ∧ s ≠ t ∧ ¬G.Adj t s ∧
    ∀ w : Fin n, ¬(G.Adj t w ∧ G.Adj s w))

open Classical in
theorem mem_farOf {n : ℕ} {G : SimpleGraph (Fin n)} {t s : Fin n} :
    s ∈ farOf n G t ↔ G.degree s = 3 ∧ s ≠ t ∧ ¬G.Adj t s ∧
      ∀ w : Fin n, ¬(G.Adj t w ∧ G.Adj s w) := by
  simp [farOf]

/-! ## Threshold bricks (tri-11 / C4-14, valid for all `n ≥ 18`) -/

open Classical in
/-- No good triangle: a triangle with degree sum `≤ 11` is impossible (`n ≥ 18`). -/
theorem tri11_false {n : ℕ} (hn : 18 ≤ n) {G : SimpleGraph (Fin n)}
    (hT : ¬HasGoodTriangle n G) {x y z : Fin n}
    (hxy : G.Adj x y) (hyz : G.Adj y z) (hxz : G.Adj x z)
    (hsum : G.degree x + G.degree y + G.degree z ≤ 11) : False := by
  have h := no_good_triangle_sum_gt (n := n) (by omega) hT (G.ne_of_adj hxy)
    (G.ne_of_adj hyz) (G.ne_of_adj hxz) hxy hyz hxz
  rw [goodTriThreshold_eq_of_ge_eighteen hn] at h
  omega

open Classical in
/-- No good `C₄`: an induced `C₄` with degree sum `≤ 14` is impossible (`n ≥ 16`). -/
theorem c4_14_false {n : ℕ} (hn : 16 ≤ n) {G : SimpleGraph (Fin n)}
    (hC4 : ¬HasGoodC4 n G) {a b c d : Fin n}
    (hcard : ({a, b, c, d} : Finset (Fin n)).card = 4)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : ¬G.Adj a c) (hbd : ¬G.Adj b d)
    (hsum : G.degree a + G.degree b + G.degree c + G.degree d ≤ 14) : False := by
  have h := no_good_C4_sum_gt (n := n) (by omega) hC4 hcard hab hbc hcd hda hac hbd
  have h14 : 14 ≤ goodC4Threshold n := by
    rcases lt_or_ge n 32 with hlt | hge
    · rw [goodC4Threshold_eq_of_window (by omega) hlt]
    · rw [goodC4Threshold_eq_of_ge_thirtytwo hge]
      omega
  omega

open Classical in
/-- **F2/F3 combined — twin-pair common-neighbour uniqueness**: two distinct
degree-3 vertices have at most one common neighbour (elementwise form).
Adjacent pairs actually share none (good triangle at `Σ ≤ 10`); non-adjacent
pairs share at most one (good triangle at `Σ ≤ 11` / good `C₄` at `Σ ≤ 14`). -/
theorem twin_common_unique {n : ℕ} (hn : 18 ≤ n) {G : SimpleGraph (Fin n)}
    (hT : ¬HasGoodTriangle n G) (hC4 : ¬HasGoodC4 n G)
    (hdeg4 : ∀ v : Fin n, G.degree v ≤ 4)
    {s z : Fin n} (hs : G.degree s = 3) (hz : G.degree z = 3) (hsz : s ≠ z) :
    ∀ w w' : Fin n, G.Adj s w → G.Adj z w → G.Adj s w' → G.Adj z w' → w = w' := by
  intro w w' hsw hzw hsw' hzw'
  by_cases hadj : G.Adj s z
  · exact (tri11_false hn hT hadj hzw hsw (by have := hdeg4 w; omega)).elim
  · by_contra hww
    by_cases hadj' : G.Adj w w'
    · exact tri11_false hn hT hsw hadj' hsw'
        (by have := hdeg4 w; have := hdeg4 w'; omega)
    · have h1 : s ≠ w := G.ne_of_adj hsw
      have h2 : z ≠ w := G.ne_of_adj hzw
      have h3 : s ≠ w' := G.ne_of_adj hsw'
      have h4 : z ≠ w' := G.ne_of_adj hzw'
      have hcard : ({s, w, z, w'} : Finset (Fin n)).card = 4 := by
        rw [Finset.card_insert_of_notMem (by simp [h1, hsz, h3]),
          Finset.card_insert_of_notMem (by simp [Ne.symm h2, hww]),
          Finset.card_insert_of_notMem (by simp [h4]), Finset.card_singleton]
      exact c4_14_false (by omega) hC4 hcard hsw (G.adj_symm hzw) hzw' (G.adj_symm hsw')
        hadj hadj' (by have := hdeg4 w; have := hdeg4 w'; omega)

open Classical in
/-- Cardinality form of `twin_common_unique`. -/
theorem twin_common_card_le_one {n : ℕ} (hn : 18 ≤ n) {G : SimpleGraph (Fin n)}
    (hT : ¬HasGoodTriangle n G) (hC4 : ¬HasGoodC4 n G)
    (hdeg4 : ∀ v : Fin n, G.degree v ≤ 4)
    {s z : Fin n} (hs : G.degree s = 3) (hz : G.degree z = 3) (hsz : s ≠ z) :
    (G.neighborFinset s ∩ G.neighborFinset z).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
    SimpleGraph.mem_neighborFinset] at ha hb
  exact twin_common_unique hn hT hC4 hdeg4 hs hz hsz a b ha.1 ha.2 hb.1 hb.2

/-! ## The corner degree-3 set and the unique `M`-edge -/

open Classical in
/-- In the `x = 0` corner (`∑deg = 4n − 8`, degrees `∈ {3,4}`) there are exactly
`8` degree-3 vertices. -/
theorem corner_deg3_card (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Fin n))
    (hm : G.edgeFinset.card = 2 * (n - 2))
    (hdeg : ∀ v : Fin n, G.degree v = 3 ∨ G.degree v = 4) :
    (Finset.univ.filter (fun v : Fin n => G.degree v = 3)).card = 8 := by
  classical
  set D := Finset.univ.filter (fun v : Fin n => G.degree v = 3) with hD
  have hsum : ∑ v : Fin n, G.degree v = 4 * n - 8 :=
    residual_degree_sum n (by omega) G hm
  have hpart := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun v : Fin n => G.degree v = 3) (fun v : Fin n => G.degree v)
  rw [← hD] at hpart
  have hmemD : ∀ v : Fin n, v ∈ D ↔ G.degree v = 3 := by
    intro v
    rw [hD]
    simp
  have hDsum : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl fun v hv => (hmemD v).mp hv, Finset.sum_const,
      smul_eq_mul, mul_comm]
  have hHsum : ∑ v ∈ Finset.univ.filter (fun v : Fin n => ¬G.degree v = 3), G.degree v
      = 4 * (Finset.univ.filter (fun v : Fin n => ¬G.degree v = 3)).card := by
    have h4 : ∀ v ∈ Finset.univ.filter (fun v : Fin n => ¬G.degree v = 3),
        G.degree v = 4 := by
      intro v hv
      rw [Finset.mem_filter] at hv
      rcases hdeg v with h | h
      · exact absurd h hv.2
      · exact h
    rw [Finset.sum_congr rfl h4, Finset.sum_const, smul_eq_mul, mul_comm]
  have hcards := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun v : Fin n => G.degree v = 3)
  rw [← hD, Finset.card_univ, Fintype.card_fin] at hcards
  rw [hDsum, hHsum] at hpart
  omega

open Classical in
/-- Three distinct degree-3 vertices: their internal-degree sum obeys the `heM`
budget. -/
theorem three_deg3_sum_le {n : ℕ} {G : SimpleGraph (Fin n)} {D : Finset (Fin n)}
    (heM : ∑ z ∈ D, (G.neighborFinset z ∩ D).card ≤ 2)
    {a b c : Fin n} (haD : a ∈ D) (hbD : b ∈ D) (hcD : c ∈ D)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (G.neighborFinset a ∩ D).card + (G.neighborFinset b ∩ D).card
      + (G.neighborFinset c ∩ D).card ≤ 2 := by
  have hsub : ({a, b, c} : Finset (Fin n)) ⊆ D := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hle : ∑ v ∈ ({a, b, c} : Finset (Fin n)), (G.neighborFinset v ∩ D).card
      ≤ ∑ v ∈ D, (G.neighborFinset v ∩ D).card :=
    Finset.sum_le_sum_of_subset hsub
  rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_pair hbc] at hle
  omega

open Classical in
/-- **The unique `M`-edge**: under `e(M) ≤ 1` (the `heM` sum form), once one edge
inside the degree-3 set is known, every degree-3–degree-3 edge coincides with it. -/
theorem m_edge_unique {n : ℕ} {G : SimpleGraph (Fin n)} {D : Finset (Fin n)}
    (hD : ∀ v : Fin n, v ∈ D ↔ G.degree v = 3)
    (heM : ∑ z ∈ D, (G.neighborFinset z ∩ D).card ≤ 2)
    {a b : Fin n} (ha : G.degree a = 3) (hb : G.degree b = 3) (hab : G.Adj a b) :
    ∀ z u : Fin n, G.degree z = 3 → G.degree u = 3 → G.Adj z u →
      (z = a ∧ u = b) ∨ (z = b ∧ u = a) := by
  intro z u hz hu hzu
  have haD : a ∈ D := (hD a).mpr ha
  have hbD : b ∈ D := (hD b).mpr hb
  have hzD : z ∈ D := (hD z).mpr hz
  have huD : u ∈ D := (hD u).mpr hu
  have hane : a ≠ b := G.ne_of_adj hab
  have hzune : z ≠ u := G.ne_of_adj hzu
  have hpos : ∀ x y : Fin n, x ∈ D → G.Adj y x →
      1 ≤ (G.neighborFinset y ∩ D).card := by
    intro x y hxD hadj
    refine Finset.card_pos.mpr ⟨x, ?_⟩
    rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hadj, hxD⟩
  by_contra hcon
  push Not at hcon
  have p1 := hpos b a hbD hab
  have p2 := hpos a b haD (G.adj_symm hab)
  by_cases hza : z = a
  · -- `z = a`: then `u ∉ {a, b}` and `a, b, u` work
    have hub : u ≠ b := hcon.1 hza
    have hua : u ≠ a := fun h => hzune (by rw [hza, h])
    have h3 := three_deg3_sum_le heM haD hbD huD hane (Ne.symm hua) (Ne.symm hub)
    have p3 := hpos z u hzD (G.adj_symm hzu)
    omega
  · by_cases hzb : z = b
    · -- `z = b`: then `u ∉ {a, b}` and `a, b, u` work
      have hub : u ≠ a := hcon.2 hzb
      have huz : u ≠ b := fun h => hzune (by rw [hzb, h])
      have h3 := three_deg3_sum_le heM haD hbD huD hane (Ne.symm hub) (Ne.symm huz)
      have p3 := hpos z u hzD (G.adj_symm hzu)
      omega
    · -- `z ∉ {a, b}`: three distinct twins `a, b, z` with positive internal degree
      have h3 := three_deg3_sum_le heM haD hbD hzD hane (Ne.symm hza) (Ne.symm hzb)
      have p3 := hpos u z huD hzu
      omega

open Classical in
/-- An `M`-end's degree-3 neighbourhood is exactly its partner. -/
theorem mend_nbr_inter_deg3 {n : ℕ} {G : SimpleGraph (Fin n)} {D : Finset (Fin n)}
    (hD : ∀ v : Fin n, v ∈ D ↔ G.degree v = 3)
    (heM : ∑ z ∈ D, (G.neighborFinset z ∩ D).card ≤ 2)
    {e₀ e₁ : Fin n} (he₀ : G.degree e₀ = 3) (he₁ : G.degree e₁ = 3)
    (hadj : G.Adj e₀ e₁) :
    G.neighborFinset e₀ ∩ D = {e₁} := by
  have hMuniq := m_edge_unique hD heM he₀ he₁ hadj
  have hne01 : e₀ ≠ e₁ := G.ne_of_adj hadj
  ext w
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
  constructor
  · rintro ⟨hadj', hwD⟩
    rcases hMuniq e₀ w he₀ ((hD w).mp hwD) hadj' with ⟨-, h1⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd h1 hne01
  · intro hw
    rw [hw]
    exact ⟨hadj, (hD e₁).mpr he₁⟩

/-! ## The mediator regrouping (the anchor swap) -/

open Classical in
/-- Splitting a sum at a cut set: `∑_{s∩t} + ∑_{s∖t} = ∑_s`. -/
theorem sum_inter_add_sum_diff' {n : ℕ} (s t : Finset (Fin n)) (f : Fin n → ℕ) :
    ∑ w ∈ s ∩ t, f w + ∑ w ∈ s \ t, f w = ∑ w ∈ s, f w := by
  classical
  have hd : s \ t = s \ (s ∩ t) := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  rw [add_comm, hd]
  exact Finset.sum_sdiff Finset.inter_subset_left

open Classical in
/-- **Anchor swap**: a double sum over slots `(h, w ∈ N(h) ∩ S)` of a
mediator-only weight, regrouped by the mediator. -/
theorem anchor_swap {n : ℕ} (G : SimpleGraph (Fin n)) (H S : Finset (Fin n))
    (f : Fin n → ℕ) :
    ∑ h ∈ H, ∑ w ∈ G.neighborFinset h ∩ S, f w
      = ∑ w ∈ S, (G.neighborFinset w ∩ H).card * f w := by
  have h1 : ∀ h ∈ H, ∑ w ∈ G.neighborFinset h ∩ S, f w
      = ∑ w ∈ S, if G.Adj h w then f w else 0 := by
    intro h _
    rw [← Finset.sum_filter]
    congr 1
    ext w
    simp only [Finset.mem_inter, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    tauto
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, smul_eq_mul]
  have hset : H.filter (fun h => G.Adj h w) = G.neighborFinset w ∩ H := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨hx, hadj⟩
      exact ⟨G.adj_symm hadj, hx⟩
    · rintro ⟨hadj, hx⟩
      exact ⟨hx, G.adj_symm hadj⟩
  rw [hset]

open Classical in
/-- **The triple double count**: the total cross of `F` against the anchor `H`,
regrouped by mediator and split at the degree-3 set `D`. -/
theorem service_decomp {n : ℕ} (G : SimpleGraph (Fin n)) (H F D : Finset (Fin n)) :
    ∑ s ∈ F, ∑ h ∈ H, (G.neighborFinset h ∩ G.neighborFinset s).card
      = (∑ h ∈ H, ∑ w ∈ G.neighborFinset h ∩ D, (G.neighborFinset w ∩ F).card)
        + ∑ h ∈ H, ∑ w ∈ G.neighborFinset h \ D, (G.neighborFinset w ∩ F).card := by
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [sum_inter_add_sum_diff']
  have hcomm : ∀ s ∈ F, (G.neighborFinset h ∩ G.neighborFinset s).card
      = (G.neighborFinset s ∩ G.neighborFinset h).card := by
    intro s _
    rw [Finset.inter_comm]
  rw [Finset.sum_congr rfl hcomm]
  exact cross_count G F (G.neighborFinset h)

/-! ## The service supply bound (shared core of Lemmas S and E) -/

open Classical in
/-- **The service supply bound.**  For an anchor set `H` of degree-4 vertices and
a target set `F` of degree-3 vertices any two of which share at most one common
neighbour, the deg-4-mediated service `∑_{h∈H} ∑_{w∈N(h)∖D} |N(w) ∩ F|` is at
most `B + 2x + y` for slot masses `x + y ≤ B := ∑_{h∈H} |N(h)∖D|` obeying the
pair budget `6x + y ≤ |F|² − |F|`.  (`x`/`y` = slot mass on mediators serving
`3`/`2` far partners; the coupling `m(w) + v(w) ≤ 4` and the pair budget
`∑ v(v−1) ≤ k(k−1)` are the two nontrivial inputs.) -/
theorem service_supply {n : ℕ} (G : SimpleGraph (Fin n)) {D : Finset (Fin n)}
    (hD : ∀ v : Fin n, v ∈ D ↔ G.degree v = 3)
    (hdeg : ∀ v : Fin n, G.degree v = 3 ∨ G.degree v = 4)
    (H F : Finset (Fin n))
    (hH4 : ∀ h ∈ H, G.degree h = 4)
    (hF3 : ∀ s ∈ F, G.degree s = 3)
    (huniq : ∀ s ∈ F, ∀ s' ∈ F, s ≠ s' → ∀ w w' : Fin n,
      G.Adj s w → G.Adj s' w → G.Adj s w' → G.Adj s' w' → w = w') :
    ∃ x y : ℕ,
      x + y ≤ ∑ h ∈ H, (G.neighborFinset h \ D).card ∧
      6 * x + y ≤ F.card * F.card - F.card ∧
      ∑ h ∈ H, ∑ w ∈ G.neighborFinset h \ D, (G.neighborFinset w ∩ F).card
        ≤ (∑ h ∈ H, (G.neighborFinset h \ D).card) + 2 * x + y := by
  classical
  -- rewrite the sdiff slot sets through the complement anchor-swap
  have hsd : ∀ h : Fin n, G.neighborFinset h \ D = G.neighborFinset h ∩ Dᶜ := by
    intro h
    ext w
    simp [Finset.mem_sdiff, Finset.mem_compl]
  -- the mediator regrouping of the slot sum and the budget
  have hslot : ∑ h ∈ H, ∑ w ∈ G.neighborFinset h \ D, (G.neighborFinset w ∩ F).card
      = ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ H).card * (G.neighborFinset w ∩ F).card := by
    simp_rw [hsd]
    exact anchor_swap G H Dᶜ _
  have hB : ∑ h ∈ H, (G.neighborFinset h \ D).card
      = ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ H).card := by
    have h1 : ∀ h ∈ H, (G.neighborFinset h \ D).card
        = ∑ w ∈ G.neighborFinset h ∩ Dᶜ, 1 := by
      intro h _
      rw [← hsd, Finset.card_eq_sum_ones]
    rw [Finset.sum_congr rfl h1, anchor_swap]
    simp
  -- the per-mediator coupling `m + v ≤ 4` off `D`
  have hmv : ∀ w : Fin n, w ∉ D →
      (G.neighborFinset w ∩ H).card + (G.neighborFinset w ∩ F).card ≤ 4 := by
    intro w hw
    have hw4 : G.degree w = 4 := by
      rcases hdeg w with h | h
      · exact absurd ((hD w).mpr h) hw
      · exact h
    have hdisj : Disjoint (G.neighborFinset w ∩ H) (G.neighborFinset w ∩ F) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rw [Finset.mem_inter] at hx1 hx2
      have h4 := hH4 x hx1.2
      have h3 := hF3 x hx2.2
      omega
    calc (G.neighborFinset w ∩ H).card + (G.neighborFinset w ∩ F).card
        = ((G.neighborFinset w ∩ H) ∪ (G.neighborFinset w ∩ F)).card :=
          (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ (G.neighborFinset w).card := Finset.card_le_card (by
          intro x hx
          rw [Finset.mem_union, Finset.mem_inter, Finset.mem_inter] at hx
          rcases hx with h | h <;> exact h.1)
      _ = G.degree w := G.card_neighborFinset_eq_degree w
      _ ≤ 4 := le_of_eq hw4
  -- the pair budget `∑ v(v−1) ≤ k(k−1)` (offDiag double count + uniqueness)
  have hpair : ∑ w ∈ Dᶜ,
      (G.neighborFinset w ∩ F).card * ((G.neighborFinset w ∩ F).card - 1)
      ≤ F.card * F.card - F.card := by
    have hset : ∀ w : Fin n, (G.neighborFinset w ∩ F).offDiag
        = F.offDiag.filter (fun p => G.Adj w p.1 ∧ G.Adj w p.2) := by
      intro w
      ext p
      simp only [Finset.mem_offDiag, Finset.mem_filter, Finset.mem_inter,
        SimpleGraph.mem_neighborFinset]
      tauto
    have hswap2 : ∑ w ∈ Dᶜ, ((G.neighborFinset w ∩ F).offDiag).card
        = ∑ p ∈ F.offDiag, (Dᶜ.filter (fun w => G.Adj w p.1 ∧ G.Adj w p.2)).card := by
      simp_rw [hset, Finset.card_filter]
      exact Finset.sum_comm
    have hone : ∀ p ∈ F.offDiag,
        (Dᶜ.filter (fun w => G.Adj w p.1 ∧ G.Adj w p.2)).card ≤ 1 := by
      intro p hp
      rw [Finset.mem_offDiag] at hp
      rw [Finset.card_le_one]
      intro x hx y hy
      rw [Finset.mem_filter] at hx hy
      exact huniq p.1 hp.1 p.2 hp.2.1 hp.2.2 x y (G.adj_symm hx.2.1)
        (G.adj_symm hx.2.2) (G.adj_symm hy.2.1) (G.adj_symm hy.2.2)
    calc ∑ w ∈ Dᶜ,
        (G.neighborFinset w ∩ F).card * ((G.neighborFinset w ∩ F).card - 1)
        = ∑ w ∈ Dᶜ, ((G.neighborFinset w ∩ F).offDiag).card :=
          Finset.sum_congr rfl fun w _ => by
            rw [Finset.offDiag_card]
            exact Nat.mul_pred _ _
      _ = ∑ p ∈ F.offDiag, (Dᶜ.filter (fun w => G.Adj w p.1 ∧ G.Adj w p.2)).card :=
          hswap2
      _ ≤ ∑ _p ∈ F.offDiag, 1 := Finset.sum_le_sum hone
      _ = F.offDiag.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ = F.card * F.card - F.card := Finset.offDiag_card F
  -- the two slot classes
  have hdisj32 : Disjoint (Dᶜ.filter (fun w => (G.neighborFinset w ∩ F).card = 3))
      (Dᶜ.filter (fun w => (G.neighborFinset w ∩ F).card = 2)) := by
    rw [Finset.disjoint_left]
    intro w h3 h2
    rw [Finset.mem_filter] at h3 h2
    omega
  refine ⟨∑ w ∈ Dᶜ.filter (fun w => (G.neighborFinset w ∩ F).card = 3),
      (G.neighborFinset w ∩ H).card,
    ∑ w ∈ Dᶜ.filter (fun w => (G.neighborFinset w ∩ F).card = 2),
      (G.neighborFinset w ∩ H).card, ?_, ?_, ?_⟩
  · -- `x + y ≤ B`
    rw [hB, ← Finset.sum_union hdisj32]
    exact Finset.sum_le_sum_of_subset
      (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
  · -- `6x + y ≤ k² − k`
    have hx1 : ∀ w ∈ Dᶜ.filter (fun w => (G.neighborFinset w ∩ F).card = 3),
        (G.neighborFinset w ∩ H).card ≤ 1 := by
      intro w hw
      rw [Finset.mem_filter, Finset.mem_compl] at hw
      have := hmv w hw.1
      omega
    have hx2 : ∀ w ∈ Dᶜ.filter (fun w => (G.neighborFinset w ∩ F).card = 2),
        (G.neighborFinset w ∩ H).card ≤ 2 := by
      intro w hw
      rw [Finset.mem_filter, Finset.mem_compl] at hw
      have := hmv w hw.1
      omega
    have hxa : ∑ w ∈ Dᶜ.filter (fun w => (G.neighborFinset w ∩ F).card = 3),
        (G.neighborFinset w ∩ H).card
        ≤ (Dᶜ.filter (fun w => (G.neighborFinset w ∩ F).card = 3)).card := by
      calc _ ≤ ∑ _w ∈ Dᶜ.filter (fun w => (G.neighborFinset w ∩ F).card = 3), 1 :=
            Finset.sum_le_sum hx1
        _ = _ := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    have hya : ∑ w ∈ Dᶜ.filter (fun w => (G.neighborFinset w ∩ F).card = 2),
        (G.neighborFinset w ∩ H).card
        ≤ 2 * (Dᶜ.filter (fun w => (G.neighborFinset w ∩ F).card = 2)).card := by
      calc _ ≤ ∑ _w ∈ Dᶜ.filter (fun w => (G.neighborFinset w ∩ F).card = 2), 2 :=
            Finset.sum_le_sum hx2
        _ = _ := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have h63 : ∑ w ∈ Dᶜ.filter (fun w => (G.neighborFinset w ∩ F).card = 3),
        (G.neighborFinset w ∩ F).card * ((G.neighborFinset w ∩ F).card - 1)
        = 6 * (Dᶜ.filter (fun w => (G.neighborFinset w ∩ F).card = 3)).card := by
      have hc : ∀ w ∈ Dᶜ.filter (fun w => (G.neighborFinset w ∩ F).card = 3),
          (G.neighborFinset w ∩ F).card * ((G.neighborFinset w ∩ F).card - 1) = 6 := by
        intro w hw
        rw [Finset.mem_filter] at hw
        rw [hw.2]
      rw [Finset.sum_congr rfl hc, Finset.sum_const, smul_eq_mul, mul_comm]
    have h62 : ∑ w ∈ Dᶜ.filter (fun w => (G.neighborFinset w ∩ F).card = 2),
        (G.neighborFinset w ∩ F).card * ((G.neighborFinset w ∩ F).card - 1)
        = 2 * (Dᶜ.filter (fun w => (G.neighborFinset w ∩ F).card = 2)).card := by
      have hc : ∀ w ∈ Dᶜ.filter (fun w => (G.neighborFinset w ∩ F).card = 2),
          (G.neighborFinset w ∩ F).card * ((G.neighborFinset w ∩ F).card - 1) = 2 := by
        intro w hw
        rw [Finset.mem_filter] at hw
        rw [hw.2]
      rw [Finset.sum_congr rfl hc, Finset.sum_const, smul_eq_mul, mul_comm]
    have hsub : ∑ w ∈ Dᶜ.filter (fun w => (G.neighborFinset w ∩ F).card = 3),
        (G.neighborFinset w ∩ F).card * ((G.neighborFinset w ∩ F).card - 1)
        + ∑ w ∈ Dᶜ.filter (fun w => (G.neighborFinset w ∩ F).card = 2),
          (G.neighborFinset w ∩ F).card * ((G.neighborFinset w ∩ F).card - 1)
        ≤ ∑ w ∈ Dᶜ,
          (G.neighborFinset w ∩ F).card * ((G.neighborFinset w ∩ F).card - 1) := by
      rw [← Finset.sum_union hdisj32]
      exact Finset.sum_le_sum_of_subset
        (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
    omega
  · -- `SlotSum ≤ B + 2x + y`
    rw [hslot, hB]
    have hpt : ∀ w ∈ Dᶜ,
        (G.neighborFinset w ∩ H).card * (G.neighborFinset w ∩ F).card
        ≤ (G.neighborFinset w ∩ H).card
          + (2 * (if (G.neighborFinset w ∩ F).card = 3
              then (G.neighborFinset w ∩ H).card else 0)
            + (if (G.neighborFinset w ∩ F).card = 2
              then (G.neighborFinset w ∩ H).card else 0)) := by
      intro w hw
      have h4 := hmv w (Finset.mem_compl.mp hw)
      have hc : (G.neighborFinset w ∩ F).card = 0 ∨ (G.neighborFinset w ∩ F).card = 1
          ∨ (G.neighborFinset w ∩ F).card = 2 ∨ (G.neighborFinset w ∩ F).card = 3
          ∨ (G.neighborFinset w ∩ F).card = 4 := by omega
      rcases hc with h | h | h | h | h <;> rw [h] <;> simp <;> omega
    have hchain : ∑ w ∈ Dᶜ,
        (G.neighborFinset w ∩ H).card * (G.neighborFinset w ∩ F).card
        ≤ (∑ w ∈ Dᶜ, (G.neighborFinset w ∩ H).card)
          + (2 * ∑ w ∈ Dᶜ.filter (fun w => (G.neighborFinset w ∩ F).card = 3),
              (G.neighborFinset w ∩ H).card
            + ∑ w ∈ Dᶜ.filter (fun w => (G.neighborFinset w ∩ F).card = 2),
              (G.neighborFinset w ∩ H).card) := by
      calc ∑ w ∈ Dᶜ, (G.neighborFinset w ∩ H).card * (G.neighborFinset w ∩ F).card
          ≤ ∑ w ∈ Dᶜ, ((G.neighborFinset w ∩ H).card
            + (2 * (if (G.neighborFinset w ∩ F).card = 3
                then (G.neighborFinset w ∩ H).card else 0)
              + (if (G.neighborFinset w ∩ F).card = 2
                then (G.neighborFinset w ∩ H).card else 0))) :=
            Finset.sum_le_sum hpt
        _ = _ := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum,
              Finset.sum_filter, Finset.sum_filter]
            simp only [mul_ite, mul_zero]
    omega

/-! ## The degree-3 bonus bounds -/

open Classical in
/-- **The degree-3 bonus, iso side**: for an iso twin `t` and a far family `F`,
the deg-3-mediated service `∑_{h∈N(t)} ∑_{w∈N(h)∩D} |N(w) ∩ F|` is at most `1`
(the only possible contributor is the unique `M`-edge, once, through one hub). -/
theorem bonus_le_one_iso {n : ℕ} (hn : 18 ≤ n) {G : SimpleGraph (Fin n)}
    (hT : ¬HasGoodTriangle n G) (hC4 : ¬HasGoodC4 n G)
    (hdeg4 : ∀ v : Fin n, G.degree v ≤ 4)
    {D : Finset (Fin n)} (hD : ∀ v : Fin n, v ∈ D ↔ G.degree v = 3)
    (heM : ∑ z ∈ D, (G.neighborFinset z ∩ D).card ≤ 2)
    {t : Fin n} (ht : G.degree t = 3)
    {F : Finset (Fin n)} (hF3 : ∀ s ∈ F, G.degree s = 3)
    (hFfar : ∀ s ∈ F, ∀ w : Fin n, ¬(G.Adj t w ∧ G.Adj s w))
    (hFnadj : ∀ s ∈ F, ¬G.Adj t s) :
    ∑ h ∈ G.neighborFinset t, ∑ w ∈ G.neighborFinset h ∩ D,
      (G.neighborFinset w ∩ F).card ≤ 1 := by
  classical
  rw [anchor_swap]
  by_cases hex : ∃ w₀ ∈ D, ∃ s₀ ∈ F, G.Adj w₀ s₀
  · obtain ⟨w₀, hw₀D, s₀, hs₀F, hadj₀⟩ := hex
    have hw₀3 : G.degree w₀ = 3 := (hD w₀).mp hw₀D
    have hs₀3 : G.degree s₀ = 3 := hF3 s₀ hs₀F
    have hMuniq := m_edge_unique hD heM hw₀3 hs₀3 hadj₀
    have hw₀t : w₀ ≠ t := by
      rintro rfl
      exact hFnadj s₀ hs₀F hadj₀
    have hpt : ∀ w ∈ D, (G.neighborFinset w ∩ G.neighborFinset t).card
        * (G.neighborFinset w ∩ F).card ≤ if w = w₀ then 1 else 0 := by
      intro w hwD
      by_cases hww : w = w₀
      · subst hww
        rw [ite_eq_left rfl]
        have hm1 : (G.neighborFinset w ∩ G.neighborFinset t).card ≤ 1 :=
          twin_common_card_le_one hn hT hC4 hdeg4 ((hD w).mp hwD) ht hw₀t
        have hsub : G.neighborFinset w ∩ F ⊆ {s₀} := by
          intro a ha
          rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at ha
          rw [Finset.mem_singleton]
          rcases hMuniq w a ((hD w).mp hwD) (hF3 a ha.2) ha.1 with ⟨-, h1⟩ | ⟨h1, h2⟩
          · exact h1
          · exact h2.trans h1
        have hv1 : (G.neighborFinset w ∩ F).card ≤ 1 := by
          calc (G.neighborFinset w ∩ F).card ≤ ({s₀} : Finset (Fin n)).card :=
              Finset.card_le_card hsub
            _ = 1 := Finset.card_singleton s₀
        calc (G.neighborFinset w ∩ G.neighborFinset t).card
            * (G.neighborFinset w ∩ F).card ≤ 1 * 1 := Nat.mul_le_mul hm1 hv1
          _ = 1 := by norm_num
      · rw [ite_eq_right hww, Nat.le_zero, Nat.mul_eq_zero]
        by_cases hv : (G.neighborFinset w ∩ F).card = 0
        · exact Or.inr hv
        · left
          obtain ⟨a, ha⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hv)
          rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at ha
          have hws₀ : w = s₀ := by
            rcases hMuniq w a ((hD w).mp hwD) (hF3 a ha.2) ha.1 with ⟨h1, -⟩ | ⟨h1, -⟩
            · exact absurd h1 hww
            · exact h1
          subst hws₀
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro x hx
          rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
            SimpleGraph.mem_neighborFinset] at hx
          exact hFfar w hs₀F x ⟨hx.2, hx.1⟩
    calc ∑ w ∈ D, (G.neighborFinset w ∩ G.neighborFinset t).card
          * (G.neighborFinset w ∩ F).card
        ≤ ∑ w ∈ D, if w = w₀ then 1 else 0 := Finset.sum_le_sum hpt
      _ = if w₀ ∈ D then 1 else 0 := Finset.sum_ite_eq' D w₀ (fun _ => 1)
      _ ≤ 1 := by rw [ite_eq_left hw₀D]
  · push Not at hex
    have hzero : ∀ w ∈ D, (G.neighborFinset w ∩ G.neighborFinset t).card
        * (G.neighborFinset w ∩ F).card = 0 := by
      intro w hwD
      rw [Nat.mul_eq_zero]
      right
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro a ha
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at ha
      exact hex w hwD a ha.2 ha.1
    rw [Finset.sum_congr rfl hzero, Finset.sum_const, smul_eq_mul, mul_zero]
    omega

open Classical in
/-- If every member of `F` is itself iso (no degree-3 neighbour), the deg-3 bonus
vanishes entirely — the `k = 1` clause of Lemma S. -/
theorem bonus_zero_of_iso_partners {n : ℕ} {G : SimpleGraph (Fin n)}
    {D : Finset (Fin n)} (hD : ∀ v : Fin n, v ∈ D ↔ G.degree v = 3)
    (H : Finset (Fin n)) {F : Finset (Fin n)}
    (hFiso : ∀ s ∈ F, ∀ z : Fin n, G.Adj s z → G.degree z ≠ 3) :
    ∑ h ∈ H, ∑ w ∈ G.neighborFinset h ∩ D, (G.neighborFinset w ∩ F).card = 0 := by
  refine Finset.sum_eq_zero fun h _ => Finset.sum_eq_zero fun w hw => ?_
  rw [Finset.mem_inter] at hw
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro s hs
  rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hs
  exact hFiso s hs.2 w (G.adj_symm hs.1) ((hD w).mp hw.2)

open Classical in
/-- **The degree-3 bonus, `M`-end side, vanishes pointwise**: no degree-3 vertex
is adjacent to a far partner of the `M`-end `e₀`. -/
theorem far_deg3_inter_zero_end {n : ℕ} {G : SimpleGraph (Fin n)}
    {D : Finset (Fin n)} (hD : ∀ v : Fin n, v ∈ D ↔ G.degree v = 3)
    (heM : ∑ z ∈ D, (G.neighborFinset z ∩ D).card ≤ 2)
    {e₀ e₁ : Fin n} (he₀ : G.degree e₀ = 3) (he₁ : G.degree e₁ = 3)
    (hadj : G.Adj e₀ e₁) :
    ∀ w ∈ D, (G.neighborFinset w ∩ farOf n G e₀).card = 0 := by
  intro w hwD
  have hMuniq := m_edge_unique hD heM he₀ he₁ hadj
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro s hs
  rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hs
  have hsF := hs.2
  rw [mem_farOf] at hsF
  rcases hMuniq w s ((hD w).mp hwD) hsF.1 hs.1 with ⟨-, h1⟩ | ⟨-, h1⟩
  · exact hsF.2.2.1 (by rw [h1]; exact hadj)
  · exact hsF.2.1 h1

/-! ## The φ-identities (slot budgets) -/

open Classical in
/-- **The iso φ-identity**: for an iso twin `t` in the corner, the slot budget is
`∑_{h∈N(t)} |N(h)∖D| = k + 2` where `k = |farOf t| ≤ 7`. -/
theorem phi_iso {n : ℕ} (hn : 18 ≤ n) {G : SimpleGraph (Fin n)}
    (hm : G.edgeFinset.card = 2 * (n - 2))
    (hdeg : ∀ v : Fin n, G.degree v = 3 ∨ G.degree v = 4)
    (hT : ¬HasGoodTriangle n G) (hC4 : ¬HasGoodC4 n G)
    {D : Finset (Fin n)} (hD : ∀ v : Fin n, v ∈ D ↔ G.degree v = 3)
    {t : Fin n} (ht : G.degree t = 3)
    (hiso : ∀ w : Fin n, G.Adj t w → G.degree w ≠ 3) :
    (farOf n G t).card ≤ 7 ∧
      ∑ h ∈ G.neighborFinset t, (G.neighborFinset h \ D).card
        = (farOf n G t).card + 2 := by
  classical
  have hdeg4 : ∀ v : Fin n, G.degree v ≤ 4 := fun v => by
    rcases hdeg v with h | h <;> omega
  have hDeq : D = Finset.univ.filter (fun v : Fin n => G.degree v = 3) := by
    ext v
    simp [hD v]
  have hDcard : D.card = 8 := by
    rw [hDeq]
    exact corner_deg3_card n hn G hm hdeg
  have htD : t ∈ D := (hD t).mpr ht
  have hFsub : farOf n G t ⊆ D.erase t := by
    intro s hs
    rw [mem_farOf] at hs
    exact Finset.mem_erase.mpr ⟨hs.2.1, (hD s).mpr hs.1⟩
  have hk7 : (farOf n G t).card ≤ 7 := by
    calc (farOf n G t).card ≤ (D.erase t).card := Finset.card_le_card hFsub
      _ = 7 := by rw [Finset.card_erase_of_mem htD, hDcard]
  refine ⟨hk7, ?_⟩
  -- the load sum through the bipartite double count
  have hcc : ∑ h ∈ G.neighborFinset t, (G.neighborFinset h ∩ D).card
      = ∑ z ∈ D, (G.neighborFinset z ∩ G.neighborFinset t).card :=
    cross_count G (G.neighborFinset t) D
  have hsplit : ∑ z ∈ D, (G.neighborFinset z ∩ G.neighborFinset t).card
      = (G.neighborFinset t ∩ G.neighborFinset t).card
        + ∑ z ∈ D.erase t, (G.neighborFinset z ∩ G.neighborFinset t).card :=
    (Finset.add_sum_erase D _ htD).symm
  have hself : (G.neighborFinset t ∩ G.neighborFinset t).card = 3 := by
    rw [Finset.inter_self, SimpleGraph.card_neighborFinset_eq_degree, ht]
  have hfar0 : ∀ z ∈ farOf n G t,
      (G.neighborFinset z ∩ G.neighborFinset t).card = 0 := by
    intro z hz
    rw [mem_farOf] at hz
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro w hw
    rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      SimpleGraph.mem_neighborFinset] at hw
    exact hz.2.2.2 w ⟨hw.2, hw.1⟩
  have hclose1 : ∀ z ∈ (D.erase t) \ farOf n G t,
      (G.neighborFinset z ∩ G.neighborFinset t).card = 1 := by
    intro z hz
    rw [Finset.mem_sdiff, Finset.mem_erase] at hz
    obtain ⟨⟨hzt, hzD⟩, hzF⟩ := hz
    have hz3 : G.degree z = 3 := (hD z).mp hzD
    have hnadj : ¬G.Adj t z := fun h => hiso z h hz3
    have hcommon : ∃ w : Fin n, G.Adj t w ∧ G.Adj z w := by
      by_contra hno
      push Not at hno
      exact hzF (mem_farOf.mpr ⟨hz3, hzt, hnadj, fun w hw => hno w hw.1 hw.2⟩)
    obtain ⟨w, htw, hzw⟩ := hcommon
    have hle := twin_common_card_le_one hn hT hC4 hdeg4 hz3 ht hzt
    have hge : 1 ≤ (G.neighborFinset z ∩ G.neighborFinset t).card := by
      refine Finset.card_pos.mpr ⟨w, ?_⟩
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
        SimpleGraph.mem_neighborFinset]
      exact ⟨hzw, htw⟩
    omega
  have hsum_erase : ∑ z ∈ D.erase t, (G.neighborFinset z ∩ G.neighborFinset t).card
      = ((D.erase t) \ farOf n G t).card := by
    rw [← Finset.sum_sdiff hFsub, Finset.sum_congr rfl hclose1,
      Finset.sum_congr rfl hfar0, Finset.sum_const, Finset.sum_const]
    simp
  have hsdcard : ((D.erase t) \ farOf n G t).card + (farOf n G t).card = 7 := by
    rw [Finset.card_sdiff_add_card_eq_card hFsub, Finset.card_erase_of_mem htD, hDcard]
  -- the per-hub degree split
  have hBS : ∑ h ∈ G.neighborFinset t,
      ((G.neighborFinset h \ D).card + (G.neighborFinset h ∩ D).card) = 12 := by
    have h1 : ∀ h ∈ G.neighborFinset t,
        (G.neighborFinset h \ D).card + (G.neighborFinset h ∩ D).card = 4 := by
      intro h hh
      rw [SimpleGraph.mem_neighborFinset] at hh
      rw [Finset.card_sdiff_add_card_inter, SimpleGraph.card_neighborFinset_eq_degree]
      rcases hdeg h with h3 | h4
      · exact absurd h3 (hiso h hh)
      · exact h4
    rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul,
      SimpleGraph.card_neighborFinset_eq_degree, ht]
  rw [Finset.sum_add_distrib] at hBS
  have hStotal : ∑ h ∈ G.neighborFinset t, (G.neighborFinset h ∩ D).card
      + (farOf n G t).card = 10 := by
    rw [hcc, hsplit, hself, hsum_erase]
    omega
  omega

open Classical in
/-- **The end φ-identity**: for the `M`-end `e₀` (partner `e₁`) in the corner, the
slot budget over the two hub neighbours is exactly `k₀ = |farOf e₀| ≤ 6`. -/
theorem phi_end {n : ℕ} (hn : 18 ≤ n) {G : SimpleGraph (Fin n)}
    (hm : G.edgeFinset.card = 2 * (n - 2))
    (hdeg : ∀ v : Fin n, G.degree v = 3 ∨ G.degree v = 4)
    (hT : ¬HasGoodTriangle n G) (hC4 : ¬HasGoodC4 n G)
    {D : Finset (Fin n)} (hD : ∀ v : Fin n, v ∈ D ↔ G.degree v = 3)
    (heM : ∑ z ∈ D, (G.neighborFinset z ∩ D).card ≤ 2)
    {e₀ e₁ : Fin n} (he₀ : G.degree e₀ = 3) (he₁ : G.degree e₁ = 3)
    (hadj : G.Adj e₀ e₁) :
    (farOf n G e₀).card ≤ 6 ∧
      ∑ γ ∈ G.neighborFinset e₀ \ D, (G.neighborFinset γ \ D).card
        = (farOf n G e₀).card := by
  classical
  have hdeg4 : ∀ v : Fin n, G.degree v ≤ 4 := fun v => by
    rcases hdeg v with h | h <;> omega
  have hDeq : D = Finset.univ.filter (fun v : Fin n => G.degree v = 3) := by
    ext v
    simp [hD v]
  have hDcard : D.card = 8 := by
    rw [hDeq]
    exact corner_deg3_card n hn G hm hdeg
  have hMuniq := m_edge_unique hD heM he₀ he₁ hadj
  have hne01 : e₀ ≠ e₁ := G.ne_of_adj hadj
  have he₀D : e₀ ∈ D := (hD e₀).mpr he₀
  have he₁D : e₁ ∈ D := (hD e₁).mpr he₁
  have he₁mem : e₁ ∈ D.erase e₀ := Finset.mem_erase.mpr ⟨Ne.symm hne01, he₁D⟩
  have hND : G.neighborFinset e₀ ∩ D = {e₁} := mend_nbr_inter_deg3 hD heM he₀ he₁ hadj
  have hH0card : (G.neighborFinset e₀ \ D).card = 2 := by
    have h1 := Finset.card_sdiff_add_card_inter (G.neighborFinset e₀) D
    rw [hND, Finset.card_singleton, SimpleGraph.card_neighborFinset_eq_degree, he₀] at h1
    omega
  have hFsub : farOf n G e₀ ⊆ (D.erase e₀).erase e₁ := by
    intro s hs
    rw [mem_farOf] at hs
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨hs.2.1, (hD s).mpr hs.1⟩⟩
    rintro rfl
    exact hs.2.2.1 hadj
  have hk6 : (farOf n G e₀).card ≤ 6 := by
    calc (farOf n G e₀).card ≤ ((D.erase e₀).erase e₁).card :=
        Finset.card_le_card hFsub
      _ = 6 := by
        rw [Finset.card_erase_of_mem he₁mem, Finset.card_erase_of_mem he₀D, hDcard]
  refine ⟨hk6, ?_⟩
  -- the per-hub degree split: `B₀ + S₀ = 8`
  have hBS : ∑ γ ∈ G.neighborFinset e₀ \ D,
      ((G.neighborFinset γ \ D).card + (G.neighborFinset γ ∩ D).card) = 8 := by
    have h1 : ∀ γ ∈ G.neighborFinset e₀ \ D,
        (G.neighborFinset γ \ D).card + (G.neighborFinset γ ∩ D).card = 4 := by
      intro γ hγ
      rw [Finset.mem_sdiff] at hγ
      rw [Finset.card_sdiff_add_card_inter, SimpleGraph.card_neighborFinset_eq_degree]
      rcases hdeg γ with h3 | h4
      · exact absurd ((hD γ).mpr h3) hγ.2
      · exact h4
    rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul, hH0card]
  rw [Finset.sum_add_distrib] at hBS
  -- `S₀` through the bipartite double count
  have hcc : ∑ γ ∈ G.neighborFinset e₀ \ D, (G.neighborFinset γ ∩ D).card
      = ∑ z ∈ D, (G.neighborFinset z ∩ (G.neighborFinset e₀ \ D)).card :=
    cross_count G (G.neighborFinset e₀ \ D) D
  have hterm0 : (G.neighborFinset e₀ ∩ (G.neighborFinset e₀ \ D)).card = 2 := by
    rw [Finset.inter_eq_right.mpr Finset.sdiff_subset, hH0card]
  have hterm1 : (G.neighborFinset e₁ ∩ (G.neighborFinset e₀ \ D)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro γ hγ
    rw [Finset.mem_inter, Finset.mem_sdiff, SimpleGraph.mem_neighborFinset,
      SimpleGraph.mem_neighborFinset] at hγ
    exact tri11_false hn hT hadj hγ.1 hγ.2.1 (by have := hdeg4 γ; omega)
  have hfar0 : ∀ z ∈ farOf n G e₀,
      (G.neighborFinset z ∩ (G.neighborFinset e₀ \ D)).card = 0 := by
    intro z hz
    rw [mem_farOf] at hz
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro γ hγ
    rw [Finset.mem_inter, Finset.mem_sdiff, SimpleGraph.mem_neighborFinset,
      SimpleGraph.mem_neighborFinset] at hγ
    exact hz.2.2.2 γ ⟨hγ.2.1, hγ.1⟩
  have hclose1 : ∀ z ∈ ((D.erase e₀).erase e₁) \ farOf n G e₀,
      (G.neighborFinset z ∩ (G.neighborFinset e₀ \ D)).card = 1 := by
    intro z hz
    rw [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_erase] at hz
    obtain ⟨⟨hze₁, hze₀, hzD⟩, hzF⟩ := hz
    have hz3 : G.degree z = 3 := (hD z).mp hzD
    have hnadj : ¬G.Adj e₀ z := by
      intro h
      rcases hMuniq e₀ z he₀ hz3 h with ⟨-, h1⟩ | ⟨h1, -⟩
      · exact hze₁ h1
      · exact hne01 h1
    have hcommon : ∃ w : Fin n, G.Adj e₀ w ∧ G.Adj z w := by
      by_contra hno
      push Not at hno
      exact hzF (mem_farOf.mpr ⟨hz3, hze₀, hnadj, fun w hw => hno w hw.1 hw.2⟩)
    obtain ⟨w, h0w, hzw⟩ := hcommon
    have hwD : w ∉ D := by
      intro hwD
      have hw3 := (hD w).mp hwD
      rcases hMuniq e₀ w he₀ hw3 h0w with ⟨-, h1⟩ | ⟨h1, -⟩
      · rw [h1] at hzw
        rcases hMuniq z e₁ hz3 he₁ hzw with ⟨h2, -⟩ | ⟨h2, -⟩
        · exact hze₀ h2
        · exact hze₁ h2
      · exact hne01 h1
    have hge : 1 ≤ (G.neighborFinset z ∩ (G.neighborFinset e₀ \ D)).card := by
      refine Finset.card_pos.mpr ⟨w, ?_⟩
      rw [Finset.mem_inter, Finset.mem_sdiff, SimpleGraph.mem_neighborFinset,
        SimpleGraph.mem_neighborFinset]
      exact ⟨hzw, h0w, hwD⟩
    have hle : (G.neighborFinset z ∩ (G.neighborFinset e₀ \ D)).card
        ≤ (G.neighborFinset z ∩ G.neighborFinset e₀).card := by
      apply Finset.card_le_card
      intro x hx
      rw [Finset.mem_inter, Finset.mem_sdiff] at hx
      exact Finset.mem_inter.mpr ⟨hx.1, hx.2.1⟩
    have hle1 := twin_common_card_le_one hn hT hC4 hdeg4 hz3 he₀ hze₀
    omega
  have hDsplit : ∑ z ∈ D, (G.neighborFinset z ∩ (G.neighborFinset e₀ \ D)).card
      = 2 + (0 + ∑ z ∈ (D.erase e₀).erase e₁,
          (G.neighborFinset z ∩ (G.neighborFinset e₀ \ D)).card) := by
    rw [← Finset.add_sum_erase D _ he₀D, hterm0,
      ← Finset.add_sum_erase (D.erase e₀) _ he₁mem, hterm1]
  have hsum_erase : ∑ z ∈ (D.erase e₀).erase e₁,
      (G.neighborFinset z ∩ (G.neighborFinset e₀ \ D)).card
      = (((D.erase e₀).erase e₁) \ farOf n G e₀).card := by
    rw [← Finset.sum_sdiff hFsub, Finset.sum_congr rfl hclose1,
      Finset.sum_congr rfl hfar0, Finset.sum_const, Finset.sum_const]
    simp
  have hsdcard : (((D.erase e₀).erase e₁) \ farOf n G e₀).card
      + (farOf n G e₀).card = 6 := by
    rw [Finset.card_sdiff_add_card_eq_card hFsub, Finset.card_erase_of_mem he₁mem,
      Finset.card_erase_of_mem he₀D, hDcard]
  rw [hcc, hDsplit, hsum_erase] at hBS
  omega

/-! ## The omega endgames -/

open Classical in
/-- The Lemma-S endgame arithmetic: demand `4k` versus supply
`bonus + (k+2) + 2x + y` under the slot and pair budgets is infeasible for every
`1 ≤ k ≤ 7` (the `k = 1` tie needs `bonus = 0`). -/
theorem service_endgame_iso (k bonus B X x y : ℕ) (hk1 : 1 ≤ k) (hk7 : k ≤ 7)
    (hB : B = k + 2) (hxy : x + y ≤ B) (h6 : 6 * x + y ≤ k * k - k)
    (hbonus : bonus ≤ 1) (hbz : k = 1 → bonus = 0)
    (hdem : 4 * k ≤ bonus + X) (hX : X ≤ B + 2 * x + y) : False := by
  subst hB
  interval_cases k
  · have := hbz rfl
    omega
  all_goals omega

open Classical in
/-- The Lemma-E endgame arithmetic: demand `3k₀` versus supply `k₀ + 2x + y`
under `x + y ≤ k₀` and the pair budget is infeasible for every `1 ≤ k₀ ≤ 6`. -/
theorem service_endgame_end (k X x y : ℕ) (hk1 : 1 ≤ k) (hk6 : k ≤ 6)
    (hxy : x + y ≤ k) (h6 : 6 * x + y ≤ k * k - k)
    (hdem : 3 * k ≤ X) (hX : X ≤ k + 2 * x + y) : False := by
  interval_cases k <;> omega

/-! ## Lemma S and Lemma E -/

open Classical in
/-- **Lemma S — the iso-twin service bound.**  In the corner, an iso twin `t` with
at least one far partner cannot have ALL far partners at cross `≥ 4` (given the
`k = 1` far partner iso — the excluded case is exactly the one routed to Lemma E). -/
theorem service_count_iso (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Fin n))
    (hm : G.edgeFinset.card = 2 * (n - 2))
    (hdeg : ∀ v : Fin n, G.degree v = 3 ∨ G.degree v = 4)
    (hT : ¬HasGoodTriangle n G) (hC4 : ¬HasGoodC4 n G)
    (heM : ∑ z ∈ Finset.univ.filter (fun v : Fin n => G.degree v = 3),
        (G.neighborFinset z
          ∩ Finset.univ.filter (fun v : Fin n => G.degree v = 3)).card ≤ 2)
    (t : Fin n) (ht : G.degree t = 3)
    (hiso : ∀ w : Fin n, G.Adj t w → G.degree w ≠ 3)
    (hne : (farOf n G t).Nonempty)
    (hone : (farOf n G t).card = 1 →
      ∀ s ∈ farOf n G t, ∀ z : Fin n, G.Adj s z → G.degree z ≠ 3)
    (hdemand : ∀ s ∈ farOf n G t,
      4 ≤ ∑ h ∈ G.neighborFinset t,
        (G.neighborFinset h ∩ G.neighborFinset s).card) :
    False := by
  classical
  set D := Finset.univ.filter (fun v : Fin n => G.degree v = 3) with hDdef
  have hD : ∀ v : Fin n, v ∈ D ↔ G.degree v = 3 := by
    intro v
    rw [hDdef]
    simp
  have hdeg4 : ∀ v : Fin n, G.degree v ≤ 4 := fun v => by
    rcases hdeg v with h | h <;> omega
  have hF3 : ∀ s ∈ farOf n G t, G.degree s = 3 := fun s hs => (mem_farOf.mp hs).1
  have hFfar : ∀ s ∈ farOf n G t, ∀ w : Fin n, ¬(G.Adj t w ∧ G.Adj s w) :=
    fun s hs => (mem_farOf.mp hs).2.2.2
  have hFnadj : ∀ s ∈ farOf n G t, ¬G.Adj t s := fun s hs => (mem_farOf.mp hs).2.2.1
  obtain ⟨hk7, hB⟩ := phi_iso hn hm hdeg hT hC4 hD ht hiso
  -- demand
  have hdem : 4 * (farOf n G t).card ≤ ∑ s ∈ farOf n G t, ∑ h ∈ G.neighborFinset t,
      (G.neighborFinset h ∩ G.neighborFinset s).card := by
    have h0 : ∑ _s ∈ farOf n G t, (4 : ℕ) ≤ ∑ s ∈ farOf n G t,
        ∑ h ∈ G.neighborFinset t, (G.neighborFinset h ∩ G.neighborFinset s).card :=
      Finset.sum_le_sum hdemand
    rw [Finset.sum_const, smul_eq_mul] at h0
    omega
  rw [service_decomp G (G.neighborFinset t) (farOf n G t) D] at hdem
  -- bonus bounds
  have hbonus : ∑ h ∈ G.neighborFinset t, ∑ w ∈ G.neighborFinset h ∩ D,
      (G.neighborFinset w ∩ farOf n G t).card ≤ 1 :=
    bonus_le_one_iso hn hT hC4 hdeg4 hD heM ht hF3 hFfar hFnadj
  have hbz : (farOf n G t).card = 1 →
      ∑ h ∈ G.neighborFinset t, ∑ w ∈ G.neighborFinset h ∩ D,
        (G.neighborFinset w ∩ farOf n G t).card = 0 :=
    fun h1 => bonus_zero_of_iso_partners hD (G.neighborFinset t) (hone h1)
  -- supply
  obtain ⟨x, y, hxy, h6, hslot⟩ := service_supply G hD hdeg (G.neighborFinset t)
    (farOf n G t)
    (fun h hh => by
      rw [SimpleGraph.mem_neighborFinset] at hh
      rcases hdeg h with h3 | h4
      · exact absurd h3 (hiso h hh)
      · exact h4)
    hF3
    (fun s hs s' hs' hss =>
      twin_common_unique hn hT hC4 hdeg4 (hF3 s hs) (hF3 s' hs') hss)
  exact service_endgame_iso (farOf n G t).card
    (∑ h ∈ G.neighborFinset t, ∑ w ∈ G.neighborFinset h ∩ D,
      (G.neighborFinset w ∩ farOf n G t).card)
    (∑ h ∈ G.neighborFinset t, (G.neighborFinset h \ D).card)
    (∑ h ∈ G.neighborFinset t, ∑ w ∈ G.neighborFinset h \ D,
      (G.neighborFinset w ∩ farOf n G t).card)
    x y (Finset.card_pos.mpr hne) hk7 hB hxy h6 hbonus hbz hdem hslot

open Classical in
/-- **Lemma E — the `M`-end service bound.**  In the corner, the `M`-end `e₀`
(partner `e₁`) with at least one far partner cannot have ALL far partners at
cross `≥ 4`. -/
theorem service_count_end (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Fin n))
    (hm : G.edgeFinset.card = 2 * (n - 2))
    (hdeg : ∀ v : Fin n, G.degree v = 3 ∨ G.degree v = 4)
    (hT : ¬HasGoodTriangle n G) (hC4 : ¬HasGoodC4 n G)
    (heM : ∑ z ∈ Finset.univ.filter (fun v : Fin n => G.degree v = 3),
        (G.neighborFinset z
          ∩ Finset.univ.filter (fun v : Fin n => G.degree v = 3)).card ≤ 2)
    (e₀ e₁ : Fin n) (he₀ : G.degree e₀ = 3) (he₁ : G.degree e₁ = 3)
    (hadj : G.Adj e₀ e₁)
    (hne : (farOf n G e₀).Nonempty)
    (hdemand : ∀ s ∈ farOf n G e₀,
      4 ≤ ∑ γ ∈ G.neighborFinset e₀,
        (G.neighborFinset γ ∩ G.neighborFinset s).card) :
    False := by
  classical
  set D := Finset.univ.filter (fun v : Fin n => G.degree v = 3) with hDdef
  have hD : ∀ v : Fin n, v ∈ D ↔ G.degree v = 3 := by
    intro v
    rw [hDdef]
    simp
  have hdeg4 : ∀ v : Fin n, G.degree v ≤ 4 := fun v => by
    rcases hdeg v with h | h <;> omega
  have hF3 : ∀ s ∈ farOf n G e₀, G.degree s = 3 := fun s hs => (mem_farOf.mp hs).1
  have hFnadj : ∀ s ∈ farOf n G e₀, ¬G.Adj e₀ s := fun s hs => (mem_farOf.mp hs).2.2.1
  obtain ⟨hk6, hB⟩ := phi_end hn hm hdeg hT hC4 hD heM he₀ he₁ hadj
  have hND : G.neighborFinset e₀ ∩ D = {e₁} := mend_nbr_inter_deg3 hD heM he₀ he₁ hadj
  -- the hub-mediated demand `≥ 3` per far partner
  have hdem3 : ∀ s ∈ farOf n G e₀, 3 ≤ ∑ γ ∈ G.neighborFinset e₀ \ D,
      (G.neighborFinset γ ∩ G.neighborFinset s).card := by
    intro s hs
    have h4 := hdemand s hs
    have hsplit : ∑ γ ∈ G.neighborFinset e₀,
        (G.neighborFinset γ ∩ G.neighborFinset s).card
        = (∑ γ ∈ G.neighborFinset e₀ ∩ D,
            (G.neighborFinset γ ∩ G.neighborFinset s).card)
          + ∑ γ ∈ G.neighborFinset e₀ \ D,
            (G.neighborFinset γ ∩ G.neighborFinset s).card :=
      (sum_inter_add_sum_diff' _ _ _).symm
    rw [hND, Finset.sum_singleton] at hsplit
    have hse₁ : s ≠ e₁ := by
      rintro rfl
      exact hFnadj s hs hadj
    have hle1 : (G.neighborFinset e₁ ∩ G.neighborFinset s).card ≤ 1 :=
      twin_common_card_le_one hn hT hC4 hdeg4 he₁ (hF3 s hs) (Ne.symm hse₁)
    omega
  have hdem : 3 * (farOf n G e₀).card ≤ ∑ s ∈ farOf n G e₀,
      ∑ γ ∈ G.neighborFinset e₀ \ D,
        (G.neighborFinset γ ∩ G.neighborFinset s).card := by
    have h0 : ∑ _s ∈ farOf n G e₀, (3 : ℕ) ≤ ∑ s ∈ farOf n G e₀,
        ∑ γ ∈ G.neighborFinset e₀ \ D,
          (G.neighborFinset γ ∩ G.neighborFinset s).card :=
      Finset.sum_le_sum hdem3
    rw [Finset.sum_const, smul_eq_mul] at h0
    omega
  rw [service_decomp G (G.neighborFinset e₀ \ D) (farOf n G e₀) D] at hdem
  -- the deg-3 bonus vanishes at the end
  have hb0 : ∑ γ ∈ G.neighborFinset e₀ \ D, ∑ w ∈ G.neighborFinset γ ∩ D,
      (G.neighborFinset w ∩ farOf n G e₀).card = 0 := by
    refine Finset.sum_eq_zero fun γ _ => Finset.sum_eq_zero fun w hw => ?_
    rw [Finset.mem_inter] at hw
    exact far_deg3_inter_zero_end hD heM he₀ he₁ hadj w hw.2
  rw [hb0, zero_add] at hdem
  -- supply
  obtain ⟨x, y, hxy, h6, hslot⟩ := service_supply G hD hdeg (G.neighborFinset e₀ \ D)
    (farOf n G e₀)
    (fun γ hγ => by
      rw [Finset.mem_sdiff] at hγ
      rcases hdeg γ with h3 | h4
      · exact absurd ((hD γ).mpr h3) hγ.2
      · exact h4)
    hF3
    (fun s hs s' hs' hss =>
      twin_common_unique hn hT hC4 hdeg4 (hF3 s hs) (hF3 s' hs') hss)
  rw [hB] at hxy hslot
  exact service_endgame_end (farOf n G e₀).card
    (∑ γ ∈ G.neighborFinset e₀ \ D, ∑ w ∈ G.neighborFinset γ \ D,
      (G.neighborFinset w ∩ farOf n G e₀).card)
    x y (Finset.card_pos.mpr hne) hk6 hxy h6 hdem hslot

/-! ## B2⁺ — the low-cross far pair -/

open Classical in
/-- **B2⁺ (`exists_far_deg3_pair_lowcross`).**  In the `x = 0`, `e(M) ≤ 1` corner
(`n ≥ 18`): all degrees `3` or `4`, `2(n−2)` edges, no good triangle, no good
`C₄`, at most one edge inside the degree-3 set — **some far degree-3 pair has
cross count `≤ 3`**, in the exact `hcross` form of the workhorse
`algConn_le_two_of_far_deg3_pair`.  Proof: B2 (`exists_far_deg3_pair`) gives a
far pair; if all far pairs had cross `≥ 4`, an `M`-end endpoint is killed by
Lemma E and an iso pair by Lemma S. -/
theorem exists_far_deg3_pair_lowcross (n : ℕ) (hn : 18 ≤ n)
    (G : SimpleGraph (Fin n))
    (hm : G.edgeFinset.card = 2 * (n - 2))
    (hdeg : ∀ v : Fin n, G.degree v = 3 ∨ G.degree v = 4)
    (hT : ¬HasGoodTriangle n G) (hC4 : ¬HasGoodC4 n G)
    (heM : ∑ z ∈ Finset.univ.filter (fun v : Fin n => G.degree v = 3),
        (G.neighborFinset z
          ∩ Finset.univ.filter (fun v : Fin n => G.degree v = 3)).card ≤ 2) :
    ∃ s t : Fin n, G.degree s = 3 ∧ G.degree t = 3 ∧ s ≠ t ∧ ¬G.Adj s t ∧
      (∀ w : Fin n, ¬(G.Adj s w ∧ G.Adj t w)) ∧
      ∑ w ∈ G.neighborFinset s,
        (G.neighborFinset w ∩ G.neighborFinset t).card ≤ 3 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨a, b, ha3, hb3, hab, hnadj, hcap⟩ :=
    exists_far_deg3_pair n hn G hm hdeg hT hC4 heM
  -- the cross demand at any base vertex, in the Lemma-S/E form
  have hdemand : ∀ t₀ : Fin n, G.degree t₀ = 3 → ∀ s ∈ farOf n G t₀,
      4 ≤ ∑ h ∈ G.neighborFinset t₀,
        (G.neighborFinset h ∩ G.neighborFinset s).card := by
    intro t₀ ht₀ s hs
    rw [mem_farOf] at hs
    have h3 := hcon t₀ s ht₀ hs.1 (Ne.symm hs.2.1) hs.2.2.1
      (fun w hw hw' => hs.2.2.2 w ⟨hw, hw'⟩)
    omega
  by_cases hbiso : ∀ z : Fin n, G.Adj b z → G.degree z ≠ 3
  · by_cases haiso : ∀ z : Fin n, G.Adj a z → G.degree z ≠ 3
    · -- both endpoints iso: Lemma S at `a`
      have hbF : b ∈ farOf n G a := mem_farOf.mpr ⟨hb3, Ne.symm hab, hnadj, hcap⟩
      refine service_count_iso n hn G hm hdeg hT hC4 heM a ha3 haiso ⟨b, hbF⟩ ?_
        (hdemand a ha3)
      -- `k = 1`: the unique far partner is `b`, which is iso
      intro h1 s hs z hsz
      have hsb : s = b := by
        obtain ⟨c, hc⟩ := Finset.card_eq_one.mp h1
        have h1' := hc ▸ hs
        have h2' := hc ▸ hbF
        rw [Finset.mem_singleton] at h1' h2'
        rw [h1', h2']
      subst hsb
      exact hbiso z hsz
    · -- `a` is an `M`-end: Lemma E at `a`
      push Not at haiso
      obtain ⟨z, haz, hz3⟩ := haiso
      have hbF : b ∈ farOf n G a := mem_farOf.mpr ⟨hb3, Ne.symm hab, hnadj, hcap⟩
      exact service_count_end n hn G hm hdeg hT hC4 heM a z ha3 hz3 haz ⟨b, hbF⟩
        (hdemand a ha3)
  · -- `b` is an `M`-end: Lemma E at `b`
    push Not at hbiso
    obtain ⟨z, hbz, hz3⟩ := hbiso
    have haF : a ∈ farOf n G b := mem_farOf.mpr ⟨ha3, hab,
      fun h => hnadj (G.adj_symm h), fun w hw => hcap w ⟨hw.2, hw.1⟩⟩
    exact service_count_end n hn G hm hdeg hT hC4 heM b z hb3 hz3 hbz ⟨a, haF⟩
      (hdemand b hb3)

/-! ## The band dispatch and the corner closure -/

open Classical in
/-- **The band far-pair dispatch (B1 + B2 + B2⁺): the `x = 0`, `e(M) ≤ 1` corner
is closed for EVERY `n ≥ 18`.**  B2⁺ produces a far degree-3 pair with cross
`≤ 3`; the uniform workhorse vector then certifies `algConn G ≤ 2`. -/
theorem farpair_dispatch_band (n : ℕ) (hn : 18 ≤ n) [Nonempty (Fin n)]
    (G : SimpleGraph (Fin n))
    (hm : G.edgeFinset.card = 2 * (n - 2))
    (hdeg : ∀ v : Fin n, G.degree v = 3 ∨ G.degree v = 4)
    (hT : ¬HasGoodTriangle n G) (hC4 : ¬HasGoodC4 n G)
    (heM : ∑ z ∈ Finset.univ.filter (fun v : Fin n => G.degree v = 3),
        (G.neighborFinset z
          ∩ Finset.univ.filter (fun v : Fin n => G.degree v = 3)).card ≤ 2) :
    algConn G ≤ 2 := by
  classical
  obtain ⟨s, t, hs3, ht3, hst, hnadj, hcap, hcross⟩ :=
    exists_far_deg3_pair_lowcross n hn G hm hdeg hT hC4 heM
  have hdeg4 : ∀ v : Fin n, G.degree v ≤ 4 := fun v => by
    rcases hdeg v with h | h <;> omega
  refine algConn_le_two_of_far_deg3_pair G s t hst hnadj hcap hs3 ht3
    (fun w _ => hdeg4 w) (fun w _ => hdeg4 w) ?_
  -- bridge the `Classical` `∩`-instance of the generic-`V` workhorse statement
  -- to the ambient `instDecidableEqFin` instance of the `Fin n` B2⁺ conclusion
  simpa only [classical_inter_eq] using hcross

open Classical in
/-- **The `x = 0` corner of `ResidualCore`, closed for every `n ≥ 18`** — the
band extension of `x0_corner_farpair` (which required `n ≥ 32`): a
`ResidualCore` graph with all degrees `≤ 4` whose degree-3 set spans at most
one edge satisfies `algConn G ≤ 2`. -/
theorem x0_corner_farpair_general (n : ℕ) (hn : 18 ≤ n) [Nonempty (Fin n)]
    (G : SimpleGraph (Fin n))
    (h : ResidualCore n G) (hdeg4 : ∀ v : Fin n, G.degree v ≤ 4)
    (heM : ∑ z ∈ Finset.univ.filter (fun v : Fin n => G.degree v = 3),
        (G.neighborFinset z
          ∩ Finset.univ.filter (fun v : Fin n => G.degree v = 3)).card ≤ 2) :
    algConn G ≤ 2 :=
  farpair_dispatch_band n hn G h.edge_card
    (fun v => by have := h.min_degree v; have := hdeg4 v; omega)
    h.no_good_triangle h.no_good_C4 heM

open Classical in
/-- `x0_corner_farpair_general` in the `mIncidence` vocabulary of the C-case
tree, at the honest `n ≥ 18` threshold. -/
theorem x0_corner_farpair_general_mIncidence (n : ℕ) (hn : 18 ≤ n)
    [Nonempty (Fin n)] (G : SimpleGraph (Fin n))
    (h : ResidualCore n G) (hdeg4 : ∀ v : Fin n, G.degree v ≤ 4)
    (heM : mIncidence G ≤ 2) :
    algConn G ≤ 2 := by
  classical
  apply x0_corner_farpair_general n hn G h hdeg4
  rw [mIncidence_eq_sum] at heM
  unfold deg3Set at heM
  exact heM

open Classical in
/-- **The band corner closure (the combined corollary, `n ≥ 23`).**  The `x = 0`,
`e(M) ≤ 1` poor corner of `ResidualCore` is closed for **all** `n ≥ 23` — this
single theorem covers both the band `23 ≤ n ≤ 31` (new, via B2⁺) and re-proves
the `n ≥ 32` range of `x0_corner_farpair`/`x0_corner_farpair_mIncidence`
(which remain valid; the counting here is in fact valid from `n ≥ 18`, see
`x0_corner_farpair_general_mIncidence`).  This is the corner node the C-tree
dispatcher should route through, replacing its `n ≥ 32` guard. -/
theorem x0_corner_close (n : ℕ) (hn : 23 ≤ n) [Nonempty (Fin n)]
    (G : SimpleGraph (Fin n))
    (h : ResidualCore n G) (hdeg4 : ∀ v : Fin n, G.degree v ≤ 4)
    (heM : mIncidence G ≤ 2) :
    algConn G ≤ 2 :=
  x0_corner_farpair_general_mIncidence n (by omega) G h hdeg4 heM

end ACMax
