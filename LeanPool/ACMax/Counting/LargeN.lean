/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import LeanPool.ACMax.Counting.CompactLedgers
public import LeanPool.ACMax.Counting.XBoundAssembly
public import LeanPool.ACMax.Counting.CompactCell
public import LeanPool.ACMax.Cuts.TwoCut
public import LeanPool.ACMax.Counting.HubCross
public import LeanPool.ACMax.Counting.FarPair
public import LeanPool.ACMax.Reduction.Residual

/-!
# The large-`n` assembly and the cloud bound

Assembles the compact-cell machinery into the unconditional ACMAX theorem for
large `n`, reducing the general conjecture to a finite range `19 ≤ n ≤ 17692`.
The chain: kill the hoarding regime, reduce the m-bound to a max-cloud bound via
the hub-cross law, bound the cloud by the apex-tie law, and sharpen the constants.

## Main results

* `hoarding_impossible`, `hunblocked_large` — on the compact cell (`n ≥ 520`) a
  DS-unblocked hub pair cannot hoard the degree-3 supply, so off the
  `SeaFatBoundary` some pair fires as a `W1Config`.
* `acmax_general_final`, `acmax_general_final_threeconn` — the general dispatch
  (sea / usable far pair / boundary-with-m-bound / `W1`), with the 3-connectivity
  reduction `HasTwoCut` / `algConn_le_two_of_hasTwoCut` discharging the two-cut
  case directly.
* `acmax_general_final_cloud`, `usable_deg3_card_le_of_cloud` — the hub-cross
  coverage `m ≤ 13·A + 172` reducing the m-bound to the max-cloud bound `A`.
* `cloud_usable_card_le`, `acmax_general_residual_large` — the apex-tie cloud
  bound (`A ≤ 61`, hence `m ≤ 151`), giving unconditional ACMAX for large `n`.
* `cloud_card_le_sharp` (`A ≤ 13`), `usable_deg3_card_le_sharp` and the mid-leaf
  sharpening — the constant chain pushing the wall down to `boundLin 3203 = 17692`
  (`acmax_conjecture_large_n_sharp`).
-/

/-! ## Hoarding basics for the two-mega pair

`unblocked_gap_pos_nonadj`: a DS-unblocked pair (`dsValue ≤ 4`) of degree-`≥ 4`
hubs with a positive private-twin gap is non-adjacent (adjacency already costs
`1 + 1 + 1 + 2 = 5 > 4`). -/

public section

namespace ACMax

open Finset

variable {V : Type*} [Fintype V]

open Classical in
/-- **Unblocked positive-gap pairs are non-adjacent.**  If `dsValue G g h ≤ 4`, both
hubs have degree ≥ 4, and the private-twin gap is positive, then `g` and `h` cannot
be adjacent: adjacency puts each hub in the other's internal degree (they are not
degree-3) and switches on the adjacency indicator, forcing `dsValue ≥ 5`. -/
theorem unblocked_gap_pos_nonadj (G : SimpleGraph V) (g h : V)
    (hg4 : 4 ≤ G.degree g) (hh4 : 4 ≤ G.degree h)
    (hds : dsValue G g h ≤ 4)
    (hgap : (privTwins G h g).card < (privTwins G g h).card) :
    ¬G.Adj g h := by
  intro hadj
  -- `h` is a non-degree-3 neighbour of `g`.
  have hig : 1 ≤ intDeg G g := by
    unfold intDeg
    refine Finset.card_pos.mpr ⟨h, ?_⟩
    rw [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset]
    exact ⟨hadj, fun hd => absurd (mem_deg3Set.mp hd) (by omega)⟩
  -- `g` is a non-degree-3 neighbour of `h`.
  have hih : 1 ≤ intDeg G h := by
    unfold intDeg
    refine Finset.card_pos.mpr ⟨g, ?_⟩
    rw [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset]
    exact ⟨hadj.symm, fun hd => absurd (mem_deg3Set.mp hd) (by omega)⟩
  have hai : adjInd G g h = 1 := by
    unfold adjInd
    rw [ite_eq_left hadj]
  unfold dsValue at hds
  omega

open Classical in
/-- **The DS-unblocked double-star fire** (the v66 tie-breaker, n-free).  A
DS-unblocked pair (`dsValue ≤ 4`) of degree-≥4 hubs with non-negative private
gap either fires the double-star two-cluster cut outright or is a gap-0 `W1`
configuration.  The `dsValue` budget does all the work: `mCross ≥ 1` or
adjacency force gap `0`; otherwise the intDeg/shared patterns satisfy the
exact double-star condition — the `(0,3)`-corner dies on `deg g ≥ 4`.
No largeness of `n` is required. -/
theorem ds_unblocked_fires (n : ℕ) [Nonempty (Fin n)] (G : SimpleGraph (Fin n))
    (g h' : Fin n) (hg4 : 4 ≤ G.degree g) (hh4 : 4 ≤ G.degree h') (hne : g ≠ h')
    (hds : dsValue G g h' ≤ 4)
    (hgap : (privTwins G h' g).card ≤ (privTwins G g h').card) :
    algConn G ≤ 2 ∨ W1Config G := by
  classical
  by_cases heq : (privTwins G g h').card = (privTwins G h' g).card
  · exact Or.inr (w1_of_unblocked_eq_twins G g h' hg4 hh4 hne heq hds)
  · refine Or.inl ?_
    have hgap1 : (privTwins G h' g).card + 1 ≤ (privTwins G g h').card := by
      omega
    -- unpack the DS budget: with a positive gap, no cross `M`-edge, no adjacency
    have hds' := hds
    simp only [dsValue] at hds'
    have hnadj : ¬G.Adj g h' :=
      unblocked_gap_pos_nonadj G g h' hg4 hh4 hds (by omega)
    have hadj0 : adjInd G g h' = 0 := by
      unfold adjInd
      rw [ite_eq_right hnadj]
    rw [hadj0] at hds'
    have hmx : mCross G g h' = 0 := by omega
    -- block non-adjacency from the spec + `mCross = 0`
    have hK₁3 : ∀ t ∈ privTwins G g h', G.degree t = 3 :=
      fun t ht => (privTwins_spec.mp ht).2.1
    have hK₂3 : ∀ t ∈ privTwins G h' g, G.degree t = 3 :=
      fun t ht => (privTwins_spec.mp ht).2.1
    have hK₁a : ∀ t ∈ privTwins G g h', G.Adj g t :=
      fun t ht => (privTwins_spec.mp ht).1
    have hK₂a : ∀ t ∈ privTwins G h' g, G.Adj h' t :=
      fun t ht => (privTwins_spec.mp ht).1
    have hgK₁ : g ∉ privTwins G g h' := fun hg => by
      have := (privTwins_spec.mp hg).2.1
      omega
    have hh'K₂ : h' ∉ privTwins G h' g := fun hh => by
      have := (privTwins_spec.mp hh).2.1
      omega
    have hcross : ∀ t₁ ∈ privTwins G g h', ∀ t₂ ∈ privTwins G h' g,
        ¬G.Adj t₁ t₂ := by
      intro t₁ ht₁ t₂ ht₂ hA
      have hz := (Finset.sum_eq_zero_iff.mp hmx) t₁ ht₁
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hz
      have h2 := hz t₂
      simp only [Finset.mem_inter] at h2
      exact h2 ⟨(G.mem_neighborFinset t₁ t₂).mpr hA, ht₂⟩
    -- degree partitions: `d = p + shared + intDeg`
    have hsh : (sharedTwins G g h').card = (sharedTwins G h' g).card := by
      rw [sharedTwins_comm]
    have hd₁ : G.degree g = (privTwins G g h').card
        + (sharedTwins G g h').card + intDeg G g := by
      have h1 := card_hubTwins_add_intDeg G g
      have h2 := privTwins_card_add_shared G g h'
      omega
    have hd₂ : G.degree h' = (privTwins G h' g).card
        + (sharedTwins G h' g).card + intDeg G h' := by
      have h1 := card_hubTwins_add_intDeg G h'
      have h2 := privTwins_card_add_shared G h' g
      omega
    -- fire the double-star
    refine algConn_le_two_of_double_star' G g h'
      (privTwins G g h') (privTwins G h' g) hgK₁ hh'K₂
      hK₁a hK₁3 hK₂a hK₂3 hne
      (fun hg => by
        have := (privTwins_spec.mp hg).2.1
        omega)
      (fun hh => by
        have := (privTwins_spec.mp hh).2.1
        omega)
      (Finset.disjoint_left.mpr fun {a} ha hb =>
        (privTwins_spec.mp hb).2.2 ((privTwins_spec.mp ha).1))
      hnadj
      (fun t ht hA => (privTwins_spec.mp ht).2.2 hA)
      (fun t ht hA => (privTwins_spec.mp ht).2.2 hA)
      hcross ?_
    -- the exact fire condition, by the ε-pattern analysis
    · set p₁ := (privTwins G g h').card with hp₁
      set p₂ := (privTwins G h' g).card with hp₂
      set sh := (sharedTwins G g h').card with hshd
      set i₁ := intDeg G g with hi₁
      set i₂ := intDeg G h' with hi₂
      have hbudget : (p₁ - p₂) + i₁ + i₂ + 2 * sh ≤ 4 := by
        have : (p₂ - p₁) = 0 := by omega
        omega
      have hde₁ : G.degree g = p₁ + (sh + i₁) := by omega
      have hde₂ : G.degree h' = p₂ + (sh + i₂) := by omega
      set e₁ := sh + i₁ with he₁
      set e₂ := sh + i₂ with he₂
      have hesum : e₁ + e₂ + (p₁ - p₂) ≤ 4 := by omega
      have hd₁4 : 4 ≤ p₁ + e₁ := by omega
      have hd₂4 : 4 ≤ p₂ + e₂ := by omega
      rw [hde₁, hde₂]
      -- goal: (p₁+e₁+p₁)(p₂+1)² + (p₂+e₂+p₂)(p₁+1)² ≤ 2(p₁+1)(p₂+1)(p₁+p₂+2)
      have hst : p₂ + 1 ≤ p₁ + 1 := by omega
      rcases Nat.lt_or_ge 2 e₂ with he₂3 | he₂2
      · -- `e₂ = 3, e₁ = 0, gap = 1`: forces `p₂ ≥ 3` via `deg g ≥ 4`
        have he₂' : e₂ = 3 := by omega
        have he₁' : e₁ = 0 := by omega
        have hgap' : p₁ = p₂ + 1 := by omega
        have hp₂3 : 3 ≤ p₂ := by omega
        rw [hgap', he₁', he₂']
        nlinarith only [hp₂3]
      · rcases Nat.lt_or_ge 2 e₁ with he₁3 | he₁2
        · -- `e₁ = 3, e₂ = 0`: `s ≥ t` gives `2s² ≥ t²`
          have he₁' : e₁ = 3 := by omega
          have he₂' : e₂ = 0 := by omega
          rw [he₁', he₂']
          have hsq : (p₂ + 1) * (p₂ + 1) ≤ (p₁ + 1) * (p₁ + 1) :=
            Nat.mul_le_mul hst hst
          nlinarith only [hsq]
        · -- both `≤ 2`: termwise `2pᵢ + eᵢ ≤ 2(pᵢ+1)` and ring
          calc (p₁ + e₁ + p₁) * (p₂ + 1) ^ 2 + (p₂ + e₂ + p₂) * (p₁ + 1) ^ 2
              ≤ (2 * (p₁ + 1)) * (p₂ + 1) ^ 2
                + (2 * (p₂ + 1)) * (p₁ + 1) ^ 2 :=
              Nat.add_le_add
                (Nat.mul_le_mul_right _ (by omega))
                (Nat.mul_le_mul_right _ (by omega))
            _ = 2 * (p₁ + 1) * (p₂ + 1) * (p₁ + p₂ + 2) := by ring

/-! ## Killing the hoarding regime and the final assembly

`dsValue_comm` (the DS value is symmetric); `hoarding_impossible` (for `n ≥ 520`
on the compact cell a DS-unblocked pair with a positive gap cannot hoard the
degree-3 supply — the cross-pack bound `|Pg|·|Ph| ≤ |D|·(76 + 14S)` contradicts a
quadratic lower bound); `hunblocked_large` (off the `SeaFatBoundary` some pair
fires as a `W1Config`); and the dispatch `acmax_general_final`. -/

omit [Fintype V] in
open Classical in
/-- The adjacency indicator is symmetric. -/
theorem adjInd_comm (G : SimpleGraph V) (g h : V) : adjInd G g h = adjInd G h g := by
  unfold adjInd
  by_cases hadj : G.Adj g h
  · rw [ite_eq_left hadj, ite_eq_left hadj.symm]
  · rw [ite_eq_right hadj, ite_eq_right fun hc => hadj hc.symm]

open Classical in
/-- The `M`-cross count is symmetric: both directions count the edges between the
two private sides (indicator double count). -/
theorem mCross_comm (G : SimpleGraph V) (g h : V) : mCross G g h = mCross G h g := by
  unfold mCross
  have hrep : ∀ (t : V) (Q : Finset V), (G.neighborFinset t ∩ Q).card
      = ∑ u ∈ Q, if G.Adj t u then 1 else 0 := by
    intro t Q
    have hQ : G.neighborFinset t ∩ Q = Q.filter (fun u => G.Adj t u) := by
      ext u
      simp [SimpleGraph.mem_neighborFinset, and_comm]
    rw [hQ, Finset.card_filter]
  calc ∑ t ∈ privTwins G g h, (G.neighborFinset t ∩ privTwins G h g).card
      = ∑ t ∈ privTwins G g h, ∑ u ∈ privTwins G h g, if G.Adj t u then 1 else 0 :=
        Finset.sum_congr rfl fun t _ => hrep t _
    _ = ∑ u ∈ privTwins G h g, ∑ t ∈ privTwins G g h, if G.Adj t u then 1 else 0 :=
        Finset.sum_comm
    _ = ∑ u ∈ privTwins G h g, (G.neighborFinset u ∩ privTwins G g h).card := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [hrep u]
        refine Finset.sum_congr rfl fun t _ => ?_
        by_cases hadj : G.Adj t u
        · rw [ite_eq_left hadj, ite_eq_left hadj.symm]
        · rw [ite_eq_right hadj, ite_eq_right fun hc => hadj hc.symm]

open Classical in
/-- **The DS value is symmetric**: the two ℕ-gap terms swap, the internal degrees
commute, and the shared-twin, adjacency and `M`-cross terms are symmetric. -/
theorem dsValue_comm (G : SimpleGraph V) (g h : V) : dsValue G g h = dsValue G h g := by
  unfold dsValue
  rw [sharedTwins_comm G g h, adjInd_comm G g h, mCross_comm G g h]
  omega

open Classical in
/-- **Off the boundary, every graph fires — at every `n`** (the v66 routing).
`¬SeaFatBoundary` produces a DS-unblocked pair; WLOG the gap is non-negative
and `ds_unblocked_fires` closes it via the double-star cut or the gap-0 `W1`
route.  No largeness of `n`, compactness, or M-matching hypothesis is used. -/
theorem hunblocked_all (n : ℕ) [Nonempty (Fin n)] (G : SimpleGraph (Fin n))
    (hb : ¬SeaFatBoundary G) :
    algConn G ≤ 2 ∨ W1Config G := by
  classical
  unfold SeaFatBoundary at hb
  push Not at hb
  obtain ⟨g, h', hg4, hh4, hne, hds5⟩ := hb
  have hds : dsValue G g h' ≤ 4 := by omega
  rcases le_total (privTwins G h' g).card (privTwins G g h').card with hle | hle
  · exact ds_unblocked_fires n G g h' hg4 hh4 hne hds hle
  · have hds' : dsValue G h' g ≤ 4 := by rw [dsValue_comm]; exact hds
    exact ds_unblocked_fires n G h' g hh4 hg4 hne.symm hds' hle

open Classical in
/-- **The final general assembly.**  For `n` beyond `boundLin ((128·C_m + 34508)/23)`
(and the trivial floor `520`), a single hypothesis — the usable degree-3 count is at most `C_m` on
the
boundary of the compact cell — gives `algConn G ≤ 2` for every `ResidualCore` graph:
sea → `residual_sea_algConn_le_two`; usable far pair → direct; boundary → the m-bound
excess route contradicts compactness; otherwise → `hunblocked_large` fires a W1. -/
theorem acmax_general_final (C_m n : ℕ) [Nonempty (Fin n)]
    (G : SimpleGraph (Fin n)) (h : ResidualCore n G)
    (hn : boundLin ((128 * C_m + 34508) / 23) < n) (hnBig : 520 ≤ n)
    (hmb : SeaFatBoundary G → ¬HasUsableFarPair G →
      (Finset.univ.filter
        (fun v : Fin n => G.degree v = 3 ∧ sigS G v ≤ 2)).card ≤ C_m) :
    algConn G ≤ 2 := by
  classical
  by_cases hsea : ∀ v : Fin n, G.degree v ≤ 4
  · exact residual_sea_algConn_le_two n (by omega) G h hsea
  · by_cases hsp : HasUsableFarPair G
    · exact hasUsableFarPair_algConn_le_two G h.min_degree hsp
    · by_cases hb : SeaFatBoundary G
      · -- the boundary branch, split on the existence of a light usable vertex
        have hnmax : max ((151 + 11 * ((128 * C_m + 34508) / 23)) / 2) 520 < n := by
          have hn' := hn
          unfold boundLin at hn'
          exact hn'
        by_cases hlight : ∃ u : Fin n, sigS G u ≤ 2 ∧ G.degree u ≤ 4
        · rcases sfb_excess_bound_beta n (by omega) G h hb hsp C_m (hmb hb hsp)
            with hfire | hX
          · exact hfire
          · have hXle : excessX n G ≤ (128 * C_m + 34508) / 23 :=
              (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
            have hcov := compact_covering_eleven_halves n G h.edge_card h.min_degree
              hsp hlight
            have : 2 * n ≤ 151 + 11 * ((128 * C_m + 34508) / 23) := by
              calc 2 * n ≤ 151 + 11 * excessX n G := hcov
                _ ≤ 151 + 11 * ((128 * C_m + 34508) / 23) := by omega
            omega
        · have hm0 : (Finset.univ.filter
              (fun v : Fin n => G.degree v = 3 ∧ sigS G v ≤ 2)).card = 0 := by
            rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
            intro v hv
            rw [Finset.mem_filter] at hv
            exact hlight ⟨v, hv.2.2, by omega⟩
          rcases sfb_excess_bound_beta n (by omega) G h hb hsp 0 (by omega)
            with hfire | hX
          · exact hfire
          · have hcorner := all_heavy_corner_count n (by omega) G h
              (fun u hu => by
                by_contra hc
                exact hlight ⟨u, hu, by omega⟩)
            omega
      · rcases hunblocked_all n G hb with halg | hw1
        · exact halg
        · exact w1_algConn_le_two G hw1

end ACMax

/-! ## The 3-connectivity reduction

`HasTwoCut` (a two-vertex cut `{a, b}` separating nonempty disjoint sets with no
cross edges, the hypothesis bundle of `algConn_le_two_of_two_vertex_cut`),
`algConn_le_two_of_hasTwoCut` (any two-cut gives `algConn G ≤ 2`), and
`acmax_general_final_threeconn` (the dispatch with the boundary m-bound hypothesis
weakened by also assuming `¬HasTwoCut G`). -/

namespace ACMax

open Finset

open Classical in
/-- A two-vertex cut: `a ≠ b` together with nonempty disjoint `A`, `B`
covering all remaining vertices and with no `A`–`B` edges. -/
def HasTwoCut {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ (a b : Fin n) (A B : Finset (Fin n)),
    a ≠ b ∧ A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
    a ∉ A ∪ B ∧ b ∉ A ∪ B ∧
    (∀ v : Fin n, v ∈ A ∨ v ∈ B ∨ v = a ∨ v = b) ∧
    (∀ u ∈ A, ∀ v ∈ B, ¬G.Adj u v)

open Classical in
/-- Any graph with a two-vertex cut has `algConn G ≤ 2`. -/
theorem algConn_le_two_of_hasTwoCut {n : ℕ} [Nonempty (Fin n)]
    (G : SimpleGraph (Fin n)) (h : HasTwoCut G) : algConn G ≤ 2 := by
  obtain ⟨a, b, A, B, hab, hA, hB, hdisj, haA, hbB, hcover, hsep⟩ := h
  exact algConn_le_two_of_two_vertex_cut G a b hab A B hA hB hdisj haA hbB
    hcover hsep

open Classical in
/-- **The final general assembly, 3-connected form.**  Same as
`acmax_general_final`, but the boundary m-bound hypothesis may additionally
assume there is no two-vertex cut: if a two-cut exists, the cut certificate
gives `algConn G ≤ 2` outright. -/
theorem acmax_general_final_threeconn (C_m n : ℕ) [Nonempty (Fin n)]
    (G : SimpleGraph (Fin n)) (h : ResidualCore n G)
    (hn : boundLin ((128 * C_m + 34508) / 23) < n) (hnBig : 520 ≤ n)
    (hmb : SeaFatBoundary G → ¬HasUsableFarPair G → ¬HasTwoCut G →
      (Finset.univ.filter
        (fun v : Fin n => G.degree v = 3 ∧ sigS G v ≤ 2)).card ≤ C_m) :
    algConn G ≤ 2 := by
  by_cases htc : HasTwoCut G
  · exact algConn_le_two_of_hasTwoCut G htc
  · exact acmax_general_final C_m n G h hn hnBig (fun hb hcpt => hmb hb hcpt htc)

/-! ## Hub-cross pair coverage: m-bound to max-cloud bound

The payoff of the hub-cross firing law: on the compact boundary cell the usable
degree-3 count `m` is linearly controlled by the max-cloud bound
`A = max_{deg w ≥ 9} #(usable degree-3 neighbours of w)`. By `usable_deg3_split_mid`,
`m ≤ 268 + |T'|` with `T' = bigCleanTwins G`; unless a `FiringConfig` exists,
every ordered pair of `T'` is covered by a common neighbour or a
partner-involving cross (the pure hub–hub cross being excluded by the law), and
charging every cross to the degree-4 partner set gives
`|T'|·(|T'|−1) ≤ (13A + 26)·|T'|`, hence `m ≤ 13·A + 172`
(`usable_deg3_card_le_of_cloud`). `acmax_general_final_cloud` replaces the m-bound
hypothesis of `acmax_general_final_threeconn` by this max-cloud bound. -/

/-! ## The firing configuration -/

open Classical in
/-- A **firing configuration** for the hub-cross law: the full hypothesis set of
`algConn_le_two_of_hub_cross_pair`. -/
def FiringConfig (n : ℕ) (G : SimpleGraph (Fin n)) (u v g g' : Fin n) : Prop :=
  G.degree u = 3 ∧ G.degree v = 3 ∧ u ≠ v ∧ ¬G.Adj u v ∧
  (∀ w, ¬(G.Adj u w ∧ G.Adj v w)) ∧ G.Adj u g ∧ G.Adj v g' ∧
  4 ≤ G.degree g ∧ 4 ≤ G.degree g' ∧
  (∀ w, G.Adj u w → w ≠ g → G.degree w ≤ 4) ∧
  (∀ w, G.Adj v w → w ≠ g' → G.degree w ≤ 4) ∧
  (∀ w w', G.Adj u w → G.Adj v w' → G.Adj w w' → w = g ∧ w' = g')

open Classical in
/-- A firing configuration closes the graph, via the hub-cross law. -/
theorem firingConfig_closes {n : ℕ} [Nonempty (Fin n)] (G : SimpleGraph (Fin n))
    {u v g g' : Fin n} (hf : FiringConfig n G u v g g') : algConn G ≤ 2 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hf
  exact algConn_le_two_of_hub_cross_pair G u v g g' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

open Classical in
/-- **The mechanism, given no firing configuration.**  If no firing
configuration exists, then any two distinct big clean twins share a common
neighbour or carry a **partner-involving** cross edge (one end of degree `≤ 4`).
The pure hub–hub cross is impossible: it would complete a firing
configuration. -/
theorem bigclean_mechanism_of_no_firing (n : ℕ) (G : SimpleGraph (Fin n))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (hnf : ¬∃ u v g g' : Fin n, FiringConfig n G u v g g') :
    ∀ u v : Fin n, u ∈ bigCleanTwins G → v ∈ bigCleanTwins G → u ≠ v →
      (∃ w, G.Adj u w ∧ G.Adj v w) ∨
      (∃ w w', G.Adj u w ∧ G.Adj v w' ∧ G.Adj w w' ∧
        (G.degree w ≤ 4 ∨ G.degree w' ≤ 4)) := by
  intro u v hu hv hne
  by_cases hcap : ∃ w, G.Adj u w ∧ G.Adj v w
  · exact Or.inl hcap
  right
  obtain ⟨g, hgmem, hgbig, hgrest⟩ := bigCleanTwins_unique_big G h3 hu
  obtain ⟨g', hg'mem, hg'big, hg'rest⟩ := bigCleanTwins_unique_big G h3 hv
  have hu3 : G.degree u = 3 := (mem_bigCleanTwins.mp hu).1
  have hv3 : G.degree v = 3 := (mem_bigCleanTwins.mp hv).1
  have huno3 := (mem_bigCleanTwins.mp hu).2.2.2
  have hadj : ¬G.Adj u v := fun hadj =>
    huno3 v ((G.mem_neighborFinset u v).mpr hadj) hv3
  have hcap' : ∀ w, ¬(G.Adj u w ∧ G.Adj v w) := fun w hw => hcap ⟨w, hw⟩
  have hpart : ∀ w, G.Adj u w → w ≠ g → G.degree w ≤ 4 := fun w hw hwg =>
    le_of_eq (hgrest w ((G.mem_neighborFinset u w).mpr hw) hwg)
  have hpart' : ∀ w, G.Adj v w → w ≠ g' → G.degree w ≤ 4 := fun w hw hwg =>
    le_of_eq (hg'rest w ((G.mem_neighborFinset v w).mpr hw) hwg)
  by_cases hcross : ∀ w w', G.Adj u w → G.Adj v w' → G.Adj w w' → w = g ∧ w' = g'
  · exact absurd ⟨u, v, g, g', hu3, hv3, hne, hadj, hcap',
      (G.mem_neighborFinset u g).mp hgmem, (G.mem_neighborFinset v g').mp hg'mem,
      by omega, by omega, hpart, hpart', hcross⟩ hnf
  · simp only [not_forall] at hcross
    obtain ⟨w, w', hw, hw', hww', hng⟩ := hcross
    refine ⟨w, w', hw, hw', hww', ?_⟩
    by_cases hwg : w = g
    · refine Or.inr (hpart' w' hw' (fun h => ?_))
      exact hng ⟨hwg, h⟩
    · exact Or.inl (hpart w hw hwg)

/-! ## Auxiliary caps -/

open Classical in
/-- A mid-degree (`5 ≤ deg ≤ 8`) vertex has **no** big-clean-twin neighbours. -/
theorem aT_zero_of_mid {n : ℕ} (G : SimpleGraph (Fin n))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) {w : Fin n}
    (hw5 : 5 ≤ G.degree w) (hw8 : G.degree w ≤ 8) :
    (G.neighborFinset w ∩ bigCleanTwins G).card = 0 := by
  rw [Finset.card_eq_zero]
  by_contra hne
  obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  rw [Finset.mem_inter] at hu
  have hwu : w ∈ G.neighborFinset u := by
    rw [SimpleGraph.mem_neighborFinset] at hu ⊢
    exact hu.1.symm
  rcases bigCleanTwins_nbr_deg G h3 hu.2 hwu with h4 | h9 <;> omega

/-! ## The pair-coverage master count -/

open Classical in
private theorem bigclean_pair_coverage_hP2le : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : ∀ (v :
  Fin n), 3 ≤ G.degree v) (A : ℕ)
  (T : Finset (Fin n)) (_ : ∀ (w : Fin n), 9 ≤ G.degree w → #(G.neighborFinset w ∩ T) ≤ A)
  (_ : T = bigCleanTwins G) (_ : ∀ (z : Fin n), G.degree z ≤ 4 → #(G.neighborFinset z ∩ T) ≤
    2),
  let P2 := {p ∈ T.offDiag | ∃ w, G.Adj p.1 w ∧ G.Adj p.2 w};
  #P2 ≤ (A + 2) * #T := by
  classical
  intro n G h3 A T hA hTdef hlT P2
  have hsub : P2 ⊆ Finset.univ.biUnion
      (fun w : Fin n => (G.neighborFinset w ∩ T).offDiag) := by
    intro p hp
    obtain ⟨hpd, w, hw1, hw2⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1, hp2, hpne⟩ := Finset.mem_offDiag.mp hpd
    refine Finset.mem_biUnion.mpr ⟨w, Finset.mem_univ w, ?_⟩
    refine Finset.mem_offDiag.mpr ⟨?_, ?_, hpne⟩
    · exact Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset w p.1).mpr hw1.symm, hp1⟩
    · exact Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset w p.2).mpr hw2.symm, hp2⟩
  have hbound : ∑ w : Fin n, (G.neighborFinset w ∩ T).offDiag.card
      ≤ (A + 2) * T.card := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun w : Fin n => 9 ≤ G.degree w)]
    have hbig : ∑ w ∈ Finset.univ.filter (fun w : Fin n => 9 ≤ G.degree w),
        (G.neighborFinset w ∩ T).offDiag.card ≤ A * T.card := by
      calc ∑ w ∈ Finset.univ.filter (fun w : Fin n => 9 ≤ G.degree w),
          (G.neighborFinset w ∩ T).offDiag.card
          ≤ ∑ w ∈ Finset.univ.filter (fun w : Fin n => 9 ≤ G.degree w),
            A * (G.neighborFinset w ∩ T).card := by
            refine Finset.sum_le_sum (fun w hw => ?_)
            rw [Finset.mem_filter] at hw
            rw [Finset.offDiag_card]
            have hcap := hA w hw.2
            have hmul : (G.neighborFinset w ∩ T).card * (G.neighborFinset w ∩ T).card
                ≤ A * (G.neighborFinset w ∩ T).card :=
              Nat.mul_le_mul_right _ hcap
            exact le_trans (Nat.sub_le _ _) hmul
        _ = A * ∑ w ∈ Finset.univ.filter (fun w : Fin n => 9 ≤ G.degree w),
              (G.neighborFinset w ∩ T).card := by rw [Finset.mul_sum]
        _ ≤ A * T.card := by
            simpa only [hTdef] using Nat.mul_le_mul_left A (sum_big_inc_le G h3)
    have hsmall : ∑ w ∈ Finset.univ.filter
        (fun w : Fin n => ¬9 ≤ G.degree w),
        (G.neighborFinset w ∩ T).offDiag.card ≤ 2 * T.card := by
      calc ∑ w ∈ Finset.univ.filter (fun w : Fin n => ¬9 ≤ G.degree w),
          (G.neighborFinset w ∩ T).offDiag.card
          ≤ ∑ w ∈ Finset.univ.filter (fun w : Fin n => ¬9 ≤ G.degree w),
            1 * (G.neighborFinset w ∩ T).card := by
            refine Finset.sum_le_sum (fun w hw => ?_)
            rw [Finset.mem_filter] at hw
            have h4 : (G.neighborFinset w ∩ T).card ≤ 2 := by
              rcases Nat.eq_zero_or_pos (G.neighborFinset w ∩ T).card
                with h0 | hpos
              · omega
              · obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
                rw [Finset.mem_inter] at hu
                have hwu : w ∈ G.neighborFinset u := by
                  rw [SimpleGraph.mem_neighborFinset] at hu ⊢
                  exact hu.1.symm
                rcases bigCleanTwins_nbr_deg G h3 (hTdef ▸ hu.2) hwu
                  with h4' | h9
                · exact hlT w (by omega)
                · omega
            rw [Finset.offDiag_card, Nat.sub_le_iff_le_add]
            have hmul : (G.neighborFinset w ∩ T).card * (G.neighborFinset w ∩ T).card
                ≤ 2 * (G.neighborFinset w ∩ T).card := Nat.mul_le_mul_right _ h4
            linarith
        _ = 1 * ∑ w ∈ Finset.univ.filter (fun w : Fin n => ¬9 ≤ G.degree w),
              (G.neighborFinset w ∩ T).card := by
            rw [Finset.mul_sum]
        _ ≤ 1 * (2 * T.card) := by
            refine Nat.mul_le_mul_left 1 ?_
            have := sum_small_inc_le G h3
            calc ∑ w ∈ Finset.univ.filter (fun w : Fin n => ¬9 ≤ G.degree w),
                (G.neighborFinset w ∩ T).card
                = ∑ w ∈ Finset.univ.filter (fun w : Fin n => G.degree w ≤ 8),
                  (G.neighborFinset w ∩ T).card := by
                  apply Finset.sum_congr
                  · ext w
                    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                    omega
                  · intros; rfl
              _ ≤ 2 * T.card := by simpa only [hTdef] using this
        _ = 2 * T.card := by ring
    have hdist : (A + 2) * T.card = A * T.card + 2 * T.card := by ring
    linarith
  calc P2.card
      ≤ (Finset.univ.biUnion
          (fun w : Fin n => (G.neighborFinset w ∩ T).offDiag)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ w : Fin n, (G.neighborFinset w ∩ T).offDiag.card := Finset.card_biUnion_le
    _ ≤ (A + 2) * T.card := hbound

open Classical in
private theorem bigclean_pair_coverage_hP3le : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : ∀ (v :
  Fin n), 3 ≤ G.degree v) (A : ℕ)
  (T : Finset (Fin n)) (_ : ∀ (w : Fin n), 9 ≤ G.degree w → #(G.neighborFinset w ∩ T) ≤ A)
  (_ : T = bigCleanTwins G) (_ : ∀ (z : Fin n), G.degree z ≤ 4 → #(G.neighborFinset z ∩ T) ≤
    2),
  let P3 := {p ∈ T.offDiag | ∃ w w', G.Adj p.1 w ∧ G.Adj p.2 w' ∧ G.Adj w w' ∧ (G.degree w ≤ 4 ∨
    G.degree w' ≤ 4)};
  let P := T.biUnion fun t => {w ∈ G.neighborFinset t | G.degree w ≤ 4};
  ∀ (_ : P = T.biUnion fun t => {w ∈ G.neighborFinset t | G.degree w ≤ 4}) (_ : ∀ x ∈ P,
    G.degree x = 4),
    #P3 ≤ (12 * A + 24) * #T := by
  classical
  intro n G h3 A T hA hTdef hlT P3 P hPdef hPdeg
  have hsub : P3 ⊆ P.biUnion (fun x : Fin n =>
      (G.neighborFinset x).biUnion (fun y : Fin n =>
        ((G.neighborFinset x ∩ T) ×ˢ (G.neighborFinset y ∩ T)) ∪
        ((G.neighborFinset y ∩ T) ×ˢ (G.neighborFinset x ∩ T)))) := by
    intro p hp
    obtain ⟨hpd, w, w', hw, hw', hww', htag⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1, hp2, hpne⟩ := Finset.mem_offDiag.mp hpd
    rcases htag with hw4 | hw'4
    · -- `w` is a partner of `p.1`
      have hwP : w ∈ P := by
        rw [hPdef]
        refine Finset.mem_biUnion.mpr ⟨p.1, hp1, ?_⟩
        exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset p.1 w).mpr hw, hw4⟩
      refine Finset.mem_biUnion.mpr ⟨w, hwP, ?_⟩
      refine Finset.mem_biUnion.mpr ⟨w', (G.mem_neighborFinset w w').mpr hww', ?_⟩
      refine Finset.mem_union_left _ (Finset.mem_product.mpr ⟨?_, ?_⟩)
      · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w p.1).mpr hw.symm, hp1⟩
      · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w' p.2).mpr hw'.symm, hp2⟩
    · -- `w'` is a partner of `p.2`
      have hw'P : w' ∈ P := by
        rw [hPdef]
        refine Finset.mem_biUnion.mpr ⟨p.2, hp2, ?_⟩
        exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset p.2 w').mpr hw', hw'4⟩
      refine Finset.mem_biUnion.mpr ⟨w', hw'P, ?_⟩
      refine Finset.mem_biUnion.mpr
        ⟨w, (G.mem_neighborFinset w' w).mpr hww'.symm, ?_⟩
      refine Finset.mem_union_right _ (Finset.mem_product.mpr ⟨?_, ?_⟩)
      · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w p.1).mpr hw.symm, hp1⟩
      · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w' p.2).mpr hw'.symm, hp2⟩
  -- **Uniform mediator cap.**  Every mediator `y` carries at most `A + 2` big
  -- clean twins: big `y` by the cloud cap `A`, non-big `y` by `≤ 2`.
  have hdle : ∀ y : Fin n, (G.neighborFinset y ∩ T).card ≤ A + 2 := by
    intro y
    by_cases hybig : 9 ≤ G.degree y
    · have hcap := hA y hybig
      omega
    · rcases Nat.lt_or_ge 4 (G.degree y) with hy5 | hy4
      · have hz : (G.neighborFinset y ∩ T).card = 0 := by
          rw [hTdef]
          exact aT_zero_of_mid G h3 (w := y) (by omega) (by omega)
        omega
      · have hcap := hlT y hy4
        omega
  -- **Convexity input** (exact bipartite double count): each twin has at most
  -- two degree-4 partners, so `Σ_{x∈P} |N(x)∩T| ≤ 2|T|`.
  have hCsum : ∑ x ∈ P, (G.neighborFinset x ∩ T).card ≤ 2 * T.card := by
    rw [sum_nbr_inter_comm]
    calc ∑ u ∈ T, (G.neighborFinset u ∩ P).card
        ≤ ∑ _u ∈ T, 2 := by
          refine Finset.sum_le_sum (fun u hu => ?_)
          obtain ⟨g, hgmem, hgbig, -⟩ :=
            bigCleanTwins_unique_big G h3 (hTdef ▸ hu)
          have hsub2 : G.neighborFinset u ∩ P ⊆ (G.neighborFinset u).erase g := by
            intro x hx
            rw [Finset.mem_inter] at hx
            refine Finset.mem_erase.mpr ⟨?_, hx.1⟩
            intro hxg
            have hd := hPdeg x hx.2
            rw [hxg] at hd
            omega
          have hcard3 : (G.neighborFinset u).card = 3 := by
            rw [G.card_neighborFinset_eq_degree]
            exact (mem_bigCleanTwins.mp (hTdef ▸ hu)).1
          calc (G.neighborFinset u ∩ P).card
              ≤ ((G.neighborFinset u).erase g).card := Finset.card_le_card hsub2
            _ = 2 := by rw [Finset.card_erase_of_mem hgmem, hcard3]
      _ = 2 * T.card := by rw [Finset.sum_const, smul_eq_mul]; ring
  calc P3.card
      ≤ (P.biUnion (fun x : Fin n =>
          (G.neighborFinset x).biUnion (fun y : Fin n =>
            ((G.neighborFinset x ∩ T) ×ˢ (G.neighborFinset y ∩ T)) ∪
            ((G.neighborFinset y ∩ T) ×ˢ (G.neighborFinset x ∩ T))))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ x ∈ P, ((G.neighborFinset x).biUnion (fun y : Fin n =>
          ((G.neighborFinset x ∩ T) ×ˢ (G.neighborFinset y ∩ T)) ∪
          ((G.neighborFinset y ∩ T) ×ˢ (G.neighborFinset x ∩ T)))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ x ∈ P, ∑ y ∈ G.neighborFinset x,
          (((G.neighborFinset x ∩ T) ×ˢ (G.neighborFinset y ∩ T)) ∪
            ((G.neighborFinset y ∩ T) ×ˢ (G.neighborFinset x ∩ T))).card :=
        Finset.sum_le_sum (fun x _ => Finset.card_biUnion_le)
    _ ≤ ∑ x ∈ P, 6 * (A + 2) * (G.neighborFinset x ∩ T).card := by
        refine Finset.sum_le_sum (fun x hx => ?_)
        -- factor `c_x = |N(x)∩T|` out of the per-`x` sum; the cell at `x`'s own
        -- twin vanishes (a big clean twin has no `T` neighbour), leaving `3`
        -- slots, each `≤ 2·c_x·(A+2)`
        obtain ⟨t, htT, hxt⟩ := Finset.mem_biUnion.mp (by
          rw [hPdef] at hx
          exact hx)
        rw [Finset.mem_filter] at hxt
        have htx : t ∈ G.neighborFinset x := by
          rw [SimpleGraph.mem_neighborFinset]
          exact ((G.mem_neighborFinset t x).mp hxt.1).symm
        have hNtT : G.neighborFinset t ∩ T = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro z hz
          rw [Finset.mem_inter] at hz
          have hz3 : G.degree z = 3 :=
            (mem_bigCleanTwins.mp (hTdef ▸ hz.2)).1
          exact (mem_bigCleanTwins.mp (hTdef ▸ htT)).2.2.2 z hz.1 hz3
        have hzero :
            (((G.neighborFinset x ∩ T) ×ˢ (G.neighborFinset t ∩ T)) ∪
              ((G.neighborFinset t ∩ T) ×ˢ (G.neighborFinset x ∩ T))).card = 0 := by
          rw [Finset.card_eq_zero, Finset.union_eq_empty]
          constructor
          · rw [Finset.product_eq_empty]
            exact Or.inr hNtT
          · rw [Finset.product_eq_empty]
            exact Or.inl hNtT
        rw [← Finset.add_sum_erase _ _ htx, hzero, Nat.zero_add]
        have hcellle : ∀ y ∈ (G.neighborFinset x).erase t,
            (((G.neighborFinset x ∩ T) ×ˢ (G.neighborFinset y ∩ T)) ∪
              ((G.neighborFinset y ∩ T) ×ˢ (G.neighborFinset x ∩ T))).card
            ≤ 2 * (G.neighborFinset x ∩ T).card * (G.neighborFinset y ∩ T).card := by
          intro y _
          calc (((G.neighborFinset x ∩ T) ×ˢ (G.neighborFinset y ∩ T)) ∪
                ((G.neighborFinset y ∩ T) ×ˢ (G.neighborFinset x ∩ T))).card
              ≤ ((G.neighborFinset x ∩ T) ×ˢ (G.neighborFinset y ∩ T)).card
                + ((G.neighborFinset y ∩ T) ×ˢ (G.neighborFinset x ∩ T)).card :=
                Finset.card_union_le _ _
            _ = (G.neighborFinset x ∩ T).card * (G.neighborFinset y ∩ T).card
                + (G.neighborFinset y ∩ T).card * (G.neighborFinset x ∩ T).card := by
                rw [Finset.card_product, Finset.card_product]
            _ = 2 * (G.neighborFinset x ∩ T).card
                  * (G.neighborFinset y ∩ T).card := by ring
        calc (∑ y ∈ (G.neighborFinset x).erase t,
            (((G.neighborFinset x ∩ T) ×ˢ (G.neighborFinset y ∩ T)) ∪
              ((G.neighborFinset y ∩ T) ×ˢ (G.neighborFinset x ∩ T))).card)
            ≤ ∑ y ∈ (G.neighborFinset x).erase t,
                2 * (G.neighborFinset x ∩ T).card
                  * (G.neighborFinset y ∩ T).card :=
              Finset.sum_le_sum hcellle
          _ = 2 * (G.neighborFinset x ∩ T).card *
                ∑ y ∈ (G.neighborFinset x).erase t,
                  (G.neighborFinset y ∩ T).card := by rw [Finset.mul_sum]
          _ ≤ 2 * (G.neighborFinset x ∩ T).card *
                ∑ _y ∈ (G.neighborFinset x).erase t, (A + 2) := by
              refine Nat.mul_le_mul_left (2 * (G.neighborFinset x ∩ T).card) ?_
              exact Finset.sum_le_sum (fun y _ => hdle y)
          _ = 2 * (G.neighborFinset x ∩ T).card *
                (((G.neighborFinset x).erase t).card * (A + 2)) := by
              rw [Finset.sum_const, smul_eq_mul]
          _ = 2 * (G.neighborFinset x ∩ T).card * (3 * (A + 2)) := by
              have hx4 : (G.neighborFinset x).card = 4 := by
                rw [G.card_neighborFinset_eq_degree]
                exact hPdeg x hx
              have h3c : ((G.neighborFinset x).erase t).card = 3 := by
                rw [Finset.card_erase_of_mem htx, hx4]
              rw [h3c]
          _ = 6 * (A + 2) * (G.neighborFinset x ∩ T).card := by ring
    _ = 6 * (A + 2) * ∑ x ∈ P, (G.neighborFinset x ∩ T).card := by
        rw [Finset.mul_sum]
    _ ≤ 6 * (A + 2) * (2 * T.card) := Nat.mul_le_mul_left (6 * (A + 2)) hCsum
    _ = (12 * A + 24) * T.card := by ring

open Classical in
/-- **Hub-cross pair coverage.**  Given the mechanism (no firing configuration)
and the big-cloud cap `A`, the ordered distinct pairs of big clean twins are
covered by common neighbours (`P2 ≤ (A+2)|T|`) and partner-involving crosses,
every cross edge charged to the partner set `P = ⋃_{t∈T} {deg-≤4 neighbours of
t}` (`|P| ≤ 2|T|`, all degree `4`).  In the cross channel, factoring the twin
count `c_x = |N(x)∩T| ≤ 2` out of each per-`x` sum, using that the mediator at
`x`'s own twin vanishes (a big clean twin has no degree-3 neighbour) and that
every mediator carries `≤ A + 2` twins, gives `per-x ≤ 6·c_x·(A+2)`; the exact
double count `Σ_{x∈P} c_x = 2|T|` then yields `P3 ≤ (12A + 24)|T|`.  Hence

  `|T|·(|T|−1) ≤ (13A + 26)·|T|`,   i.e.   `|T| ≤ 13A + 27` —

with **no** dependence on `n` or on the excess. -/
theorem bigclean_pair_coverage (n : ℕ) (G : SimpleGraph (Fin n))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (hmech : ∀ u v : Fin n, u ∈ bigCleanTwins G → v ∈ bigCleanTwins G → u ≠ v →
      (∃ w, G.Adj u w ∧ G.Adj v w) ∨
      (∃ w w', G.Adj u w ∧ G.Adj v w' ∧ G.Adj w w' ∧
        (G.degree w ≤ 4 ∨ G.degree w' ≤ 4)))
    (A : ℕ) (hA : ∀ w : Fin n, 9 ≤ G.degree w →
      (G.neighborFinset w ∩ bigCleanTwins G).card ≤ A)
    (hml : ∀ z : Fin n, G.degree z ≤ 4 →
      ((G.neighborFinset z).filter (fun t => G.degree t = 3)).card
        ≤ G.degree z - 2) :
    (bigCleanTwins G).card ≤ 13 * A + 27 := by
  classical
  set T : Finset (Fin n) := bigCleanTwins G with hTdef
  have hlT : ∀ z : Fin n, G.degree z ≤ 4 →
      (G.neighborFinset z ∩ T).card ≤ 2 := by
    intro z hz4
    have h1 : G.neighborFinset z ∩ T
        ⊆ (G.neighborFinset z).filter (fun t => G.degree t = 3) := by
      intro t ht
      rw [Finset.mem_inter] at ht
      rw [Finset.mem_filter]
      exact ⟨ht.1, (mem_bigCleanTwins.mp (hTdef ▸ ht.2)).1⟩
    have h2 := hml z hz4
    calc (G.neighborFinset z ∩ T).card
        ≤ ((G.neighborFinset z).filter
            (fun t => G.degree t = 3)).card := Finset.card_le_card h1
      _ ≤ G.degree z - 2 := h2
      _ ≤ 2 := by omega
  -- ordered distinct pairs = offDiag
  have hcard : T.card * (T.card - 1) = T.offDiag.card := by
    rw [Finset.offDiag_card, Nat.mul_sub, Nat.mul_one]
  -- the two mechanism classes
  set P2 : Finset (Fin n × Fin n) :=
    T.offDiag.filter (fun p => ∃ w, G.Adj p.1 w ∧ G.Adj p.2 w) with hP2def
  set P3 : Finset (Fin n × Fin n) :=
    T.offDiag.filter (fun p => ∃ w w', G.Adj p.1 w ∧ G.Adj p.2 w' ∧ G.Adj w w' ∧
      (G.degree w ≤ 4 ∨ G.degree w' ≤ 4)) with hP3def
  have hcover : T.offDiag ⊆ P2 ∪ P3 := by
    intro p hp
    obtain ⟨hp1, hp2, hpne⟩ := Finset.mem_offDiag.mp hp
    rcases hmech p.1 p.2 hp1 hp2 hpne with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, h⟩)
  have hsplit : T.offDiag.card ≤ P2.card + P3.card :=
    (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  -- the partner set: the degree-≤4 neighbours of the twins
  set P : Finset (Fin n) :=
    T.biUnion (fun t => (G.neighborFinset t).filter (fun w => G.degree w ≤ 4))
    with hPdef
  have hPcard : P.card ≤ 2 * T.card := by
    calc P.card ≤ ∑ t ∈ T, ((G.neighborFinset t).filter
          (fun w => G.degree w ≤ 4)).card := Finset.card_biUnion_le
      _ ≤ ∑ _t ∈ T, 2 := by
          refine Finset.sum_le_sum (fun t ht => ?_)
          obtain ⟨g, hgmem, hgbig, -⟩ :=
            bigCleanTwins_unique_big G h3 (hTdef ▸ ht)
          have hsub : (G.neighborFinset t).filter (fun w => G.degree w ≤ 4)
              ⊆ (G.neighborFinset t).erase g := by
            intro w hw
            rw [Finset.mem_filter] at hw
            refine Finset.mem_erase.mpr ⟨?_, hw.1⟩
            intro hwg
            rw [hwg] at hw
            omega
          have ht3 : G.degree t = 3 := (mem_bigCleanTwins.mp (hTdef ▸ ht)).1
          calc ((G.neighborFinset t).filter (fun w => G.degree w ≤ 4)).card
              ≤ ((G.neighborFinset t).erase g).card := Finset.card_le_card hsub
            _ = 2 := by
                rw [Finset.card_erase_of_mem hgmem,
                  G.card_neighborFinset_eq_degree, ht3]
      _ = 2 * T.card := by rw [Finset.sum_const, smul_eq_mul]; ring
  have hPdeg : ∀ x ∈ P, G.degree x = 4 := by
    intro x hx
    rw [hPdef] at hx
    obtain ⟨t, htT, hxt⟩ := Finset.mem_biUnion.mp hx
    rw [Finset.mem_filter] at hxt
    rcases bigCleanTwins_nbr_deg G h3 (hTdef ▸ htT) hxt.1 with h4 | h9
    · exact h4
    · omega
  -- (I) common-neighbour class (unchanged: big mediators `A·|T|`, small `6|T|`)
  have hP2le :=
      bigclean_pair_coverage_hP2le (n := n) (G := G) (h3) (A := A) (T := T) (hA)
        (hTdef) (hlT)
  -- (II) cross class: every cross edge has an endpoint in `P`
  have hP3le :=
      bigclean_pair_coverage_hP3le (n := n) (G := G) (h3) (A := A) (T := T) (hA)
        (hTdef) (hlT) (hPdef) (hPdeg)
  -- assemble and cancel one factor of `|T|`
  have hquad : T.card * (T.card - 1) ≤ (13 * A + 26) * T.card := by
    calc T.card * (T.card - 1) = T.offDiag.card := hcard
      _ ≤ P2.card + P3.card := hsplit
      _ ≤ (A + 2) * T.card + (12 * A + 24) * T.card :=
          Nat.add_le_add hP2le hP3le
      _ = (13 * A + 26) * T.card := by ring
  rcases Nat.eq_zero_or_pos T.card with h0 | hpos
  · omega
  · have h1 : (T.card - 1) * T.card ≤ (13 * A + 26) * T.card := by
      rwa [Nat.mul_comm (T.card) (T.card - 1)] at hquad
    have := Nat.le_of_mul_le_mul_right h1 hpos
    omega

/-! ## Quadratic root + the m-bound assembly -/

open Classical in
/-- Crude quadratic-root bound over `ℕ`: `x(x−1) ≤ bx + c → x ≤ b + c + 1`. -/
theorem nat_quad_bound (x b c : ℕ) (h : x * (x - 1) ≤ b * x + c) :
    x ≤ b + c + 1 := by
  by_contra hcon
  have h2 : b + c + 1 ≤ x - 1 := by omega
  have h3 : x * (b + c + 1) ≤ x * (x - 1) := Nat.mul_le_mul_left x h2
  have heq : x * (b + c + 1) = b * x + (c * x + x) := by ring
  have hcx : c ≤ c * x := Nat.le_mul_of_pos_right c (by omega)
  have hx1 : 1 ≤ x := by omega
  linarith

/-! ## The cloud bound and unconditional large-`n` ACMAX

The payoff of the apex-tie law: the A-bound is a theorem. Fix a hub `g` of degree
`≥ 9` with clean twin cloud `C = N(g) ∩ bigCleanTwins G`, `A = |C|`. Unless an
apex configuration exists, every ordered pair of `C` is covered by a shared
degree-4 partner (`≤ 6A`) or a partner–partner cross (`≤ 128A`), so
`A(A−1) ≤ 102A`, i.e. `A ≤ 61`, and the usable cloud of any degree-`≥ 9` vertex
has `≤ 151` members (`cloud_usable_card_le`). `acmax_general_residual_large` then
proves `algConn ≤ 2` for large `n` with no cell hypotheses, reducing the general
conjecture to a finite range. -/

/-! ## The apex firing configuration -/

open Classical in
/-- An **apex configuration**: the full hypothesis set of the apex-tie law
`algConn_le_two_of_apex_twin_pair`. -/
def ApexConfig (n : ℕ) (G : SimpleGraph (Fin n)) (u v g : Fin n) : Prop :=
  G.degree u = 3 ∧ G.degree v = 3 ∧ u ≠ v ∧ ¬G.Adj u v ∧
  G.Adj u g ∧ G.Adj v g ∧
  (∀ w, w ≠ g → ¬(G.Adj u w ∧ G.Adj v w)) ∧
  (∀ w, G.Adj u w → w ≠ g → G.degree w ≤ 4) ∧
  (∀ w, G.Adj v w → w ≠ g → G.degree w ≤ 4) ∧
  (∀ w w', G.Adj u w → w ≠ g → G.Adj v w' → w' ≠ g → ¬G.Adj w w')

open Classical in
/-- An apex configuration closes the graph, via the apex-tie law. -/
theorem apexConfig_closes {n : ℕ} [Nonempty (Fin n)] (G : SimpleGraph (Fin n))
    {u v g : Fin n} (hf : ApexConfig n G u v g) : algConn G ≤ 2 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hf
  exact algConn_le_two_of_apex_twin_pair G u v g h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

/-! ## Cloud structure helpers -/

open Classical in
/-- The unique big neighbour of a big clean twin `u ∈ N(g)` with `deg g ≥ 9`
is `g` itself: every other neighbour has degree `4`. -/
theorem cloud_partner_deg {n : ℕ} (G : SimpleGraph (Fin n))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v) {g u : Fin n} (hg : 9 ≤ G.degree g)
    (hu : u ∈ bigCleanTwins G) (hug : G.Adj u g) :
    ∀ w : Fin n, G.Adj u w → w ≠ g → G.degree w = 4 := by
  obtain ⟨g₀, hg₀mem, hg₀big, hrest⟩ := bigCleanTwins_unique_big G h3 hu
  have hgg₀ : g = g₀ := by
    by_contra hne
    have := hrest g ((G.mem_neighborFinset u g).mpr hug) hne
    omega
  intro w hw hwg
  exact hrest w ((G.mem_neighborFinset u w).mpr hw) (hgg₀ ▸ hwg)

open Classical in
/-- With the block law (every degree-4 vertex has at most 2 degree-3
neighbours), a non-apex vertex meets the cloud in at most `2` members. -/
theorem cloud_inter_card_le_two {n : ℕ} (G : SimpleGraph (Fin n))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (hblk4 : ∀ x : Fin n, G.degree x = 4 → (hubTwins G x).card ≤ 2)
    {g : Fin n} (hg : 9 ≤ G.degree g) {w : Fin n} (hwg : w ≠ g) :
    (G.neighborFinset w ∩ (G.neighborFinset g ∩ bigCleanTwins G)).card ≤ 2 := by
  rcases Nat.eq_zero_or_pos
    (G.neighborFinset w ∩ (G.neighborFinset g ∩ bigCleanTwins G)).card with h0 | hpos
  · omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_inter, Finset.mem_inter] at hu
  have hdw : G.degree w = 4 :=
    cloud_partner_deg G h3 hg hu.2.2
      ((G.mem_neighborFinset g u).mp hu.2.1).symm w
      ((G.mem_neighborFinset w u).mp hu.1).symm hwg
  have hsub : G.neighborFinset w ∩ (G.neighborFinset g ∩ bigCleanTwins G)
      ⊆ hubTwins G w := by
    intro t ht
    rw [Finset.mem_inter, Finset.mem_inter] at ht
    refine mem_hubTwins_iff.mpr ⟨?_, ?_⟩
    · exact ((G.mem_neighborFinset w t).mp ht.1)
    · exact (mem_bigCleanTwins.mp ht.2.2).1
  calc (G.neighborFinset w ∩ (G.neighborFinset g ∩ bigCleanTwins G)).card
      ≤ (hubTwins G w).card := Finset.card_le_card hsub
    _ ≤ 2 := hblk4 w hdw

/-! ## The same-cloud mechanism -/

open Classical in
/-- **The same-cloud mechanism, given no apex configuration.**  Two distinct
members of a degree-`≥ 9` cloud share a non-apex (degree-4) neighbour or carry
a partner–partner cross edge. -/
theorem cloud_pair_mechanism {n : ℕ} (G : SimpleGraph (Fin n))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (hnf : ¬∃ u v g : Fin n, ApexConfig n G u v g)
    {g : Fin n} (hg : 9 ≤ G.degree g) :
    ∀ u v : Fin n, u ∈ G.neighborFinset g ∩ bigCleanTwins G →
      v ∈ G.neighborFinset g ∩ bigCleanTwins G → u ≠ v →
      (∃ w, w ≠ g ∧ G.Adj u w ∧ G.Adj v w) ∨
      (∃ w w', G.Adj u w ∧ w ≠ g ∧ G.Adj v w' ∧ w' ≠ g ∧ G.Adj w w') := by
  intro u v hu hv hne
  rw [Finset.mem_inter] at hu hv
  have hu3 : G.degree u = 3 := (mem_bigCleanTwins.mp hu.2).1
  have hv3 : G.degree v = 3 := (mem_bigCleanTwins.mp hv.2).1
  have hgu : G.Adj u g := ((G.mem_neighborFinset g u).mp hu.1).symm
  have hgv : G.Adj v g := ((G.mem_neighborFinset g v).mp hv.1).symm
  have huno3 := (mem_bigCleanTwins.mp hu.2).2.2.2
  have huv : ¬G.Adj u v := fun hadj =>
    huno3 v ((G.mem_neighborFinset u v).mpr hadj) hv3
  have hpart : ∀ w, G.Adj u w → w ≠ g → G.degree w ≤ 4 := fun w hw hwg =>
    le_of_eq (cloud_partner_deg G h3 hg hu.2 hgu w hw hwg)
  have hpart' : ∀ w, G.Adj v w → w ≠ g → G.degree w ≤ 4 := fun w hw hwg =>
    le_of_eq (cloud_partner_deg G h3 hg hv.2 hgv w hw hwg)
  by_cases hcap : ∃ w, w ≠ g ∧ G.Adj u w ∧ G.Adj v w
  · exact Or.inl hcap
  right
  have hcap' : ∀ w, w ≠ g → ¬(G.Adj u w ∧ G.Adj v w) := fun w hwg hw =>
    hcap ⟨w, hwg, hw⟩
  by_cases hcross : ∀ w w', G.Adj u w → w ≠ g → G.Adj v w' → w' ≠ g → ¬G.Adj w w'
  · exact absurd ⟨u, v, g, hu3, hv3, hne, huv, hgu, hgv, hcap', hpart, hpart',
      hcross⟩ hnf
  · simp only [not_forall, not_not] at hcross
    obtain ⟨w, w', hw, hwg, hw', hw'g, hww'⟩ := hcross
    exact ⟨w, w', hw, hwg, hw', hw'g, hww'⟩

/-! ## Sharpening the usable-count cap chain

Sharpens the concrete m-bound by two improvements. `cloud_card_le_sharp` tightens
the cloud cap to `A ≤ 13`: charging both the shared-partner and partner-cross
channels to the same degree-4 partner set gives `offDiag + cross ≤ 6·c_x`
pointwise, so `A(A−1) ≤ 12A`. `usable_deg3_card_le_sharp` then gives `m ≤ 341` via
`usable_deg3_card_le_of_cloud`, and `acmax_general_residual_large_sharp` /
`acmax_conjecture_large_n_sharp` rethread the argument with `C_m' = 341`, reducing
the wall to `boundLin ((128·341 + 34508)/23) = 18764`. The standalone lever
`iso_twin_le_one_double_hub` (every degree-3 vertex has at most one degree-4
neighbour carrying a second degree-3 neighbour) is proved here but not consumed by
the sharpened bound. -/

/-! ## The sharpened cloud bound `A ≤ 13` -/

open Classical in
private theorem cloud_card_le_sharp_hperx : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (_ : ∀ (v : Fin
  n), 3 ≤ G.degree v)
  (_ : ∀ (x : Fin n), G.degree x = 4 → #(hubTwins G x) ≤ 2) {g : Fin n} (_ : 9 ≤ G.degree g)
    (C : Finset (Fin n))
  (_ : C = G.neighborFinset g ∩ bigCleanTwins G) (_ : #C * (#C - 1) = #C.offDiag),
  let P2 := {p ∈ C.offDiag | ∃ w, w ≠ g ∧ G.Adj p.1 w ∧ G.Adj p.2 w};
  ∀ (_ : P2 = {p ∈ C.offDiag | ∃ w, w ≠ g ∧ G.Adj p.1 w ∧ G.Adj p.2 w}),
    let P3 := {p ∈ C.offDiag | ∃ w w', G.Adj p.1 w ∧ w ≠ g ∧ G.Adj p.2 w' ∧ w' ≠ g ∧ G.Adj w w'};
    ∀ (_ : P3 = {p ∈ C.offDiag | ∃ w w', G.Adj p.1 w ∧ w ≠ g ∧ G.Adj p.2 w' ∧ w' ≠ g ∧ G.Adj
      w w'})
      (_ : C.offDiag ⊆ P2 ∪ P3) (_ : #C.offDiag ≤ #P2 + #P3)
      (_ : ∑ w ∈ univ.erase g, #(G.neighborFinset w ∩ C) = 2 * #C),
      let P := C.biUnion fun t => (G.neighborFinset t).erase g;
      ∀ (_ : P = C.biUnion fun t => (G.neighborFinset t).erase g) (_ : P ⊆ univ.erase g)
        (_ : ∀ x ∈ P, G.degree x = 4) (_ : ∑ x ∈ P, #(G.neighborFinset x ∩ C) ≤ 2 * #C)
        (_ : P2 ⊆ P.biUnion fun x => (G.neighborFinset x ∩ C).offDiag)
        (_ :
          P3 ⊆
            P.biUnion fun x =>
              ((G.neighborFinset x).erase g).biUnion fun x' => (G.neighborFinset x ∩ C) ×ˢ
                (G.neighborFinset x' ∩ C))
        (_ : ∀ c ≤ 2, c * c - c + c * ((4 - c) * 2) ≤ 6 * c),
        ∀ x ∈ P,
          #(G.neighborFinset x ∩ C).offDiag +
              ∑ x' ∈ (G.neighborFinset x).erase g, #((G.neighborFinset x ∩ C) ×ˢ (G.neighborFinset
                x' ∩ C)) ≤
            6 * #(G.neighborFinset x ∩ C) := by
  classical
  intro n G h3 hblk4 g hg C hCdef hcard P2 hP2def P3 hP3def hcover hsplit hexch P hPdef hPsub
    hPdeg hPincid hP2sub hP3sub hfin x hx
  have hxg : x ≠ g := by
    have := hPdeg x hx
    intro hxg; rw [hxg] at this; omega
  have hcx2 : (G.neighborFinset x ∩ C).card ≤ 2 := by
    rw [hCdef]
    exact cloud_inter_card_le_two G h3 hblk4 hg hxg
  -- own-twins-vanish bound: `Σ_{x'∈N(x).erase g} c_{x'} ≤ (4 − c_x)·2`
  have hsum_bound : ∑ x' ∈ (G.neighborFinset x).erase g,
      (G.neighborFinset x' ∩ C).card
      ≤ (4 - (G.neighborFinset x ∩ C).card) * 2 := by
    have hsum_eq : ∑ x' ∈ (G.neighborFinset x).erase g,
        (G.neighborFinset x' ∩ C).card
        = ∑ x' ∈ (G.neighborFinset x).erase g \ C,
          (G.neighborFinset x' ∩ C).card := by
      refine (Finset.sum_subset Finset.sdiff_subset
        (fun x' hx' hx'notin => ?_)).symm
      have hx'C : x' ∈ C := by
        by_contra hc
        exact hx'notin (Finset.mem_sdiff.mpr ⟨hx', hc⟩)
      have hempty : G.neighborFinset x' ∩ C = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro z hz
        rw [Finset.mem_inter] at hz
        have hzC := hz.2
        rw [hCdef, Finset.mem_inter] at hzC
        have hz3 : G.degree z = 3 := (mem_bigCleanTwins.mp hzC.2).1
        have hx'C' := hx'C
        rw [hCdef, Finset.mem_inter] at hx'C'
        exact (mem_bigCleanTwins.mp hx'C'.2).2.2.2 z hz.1 hz3
      rw [hempty, Finset.card_empty]
    rw [hsum_eq]
    have hdiff_card : ((G.neighborFinset x).erase g \ C).card
        ≤ 4 - (G.neighborFinset x ∩ C).card := by
      have hinter : ((G.neighborFinset x).erase g ∩ C).card
          = (G.neighborFinset x ∩ C).card := by
        congr 1
        ext z
        simp only [Finset.mem_inter, Finset.mem_erase]
        constructor
        · rintro ⟨⟨_, hz⟩, hzC⟩
          exact ⟨hz, hzC⟩
        · rintro ⟨hz, hzC⟩
          refine ⟨⟨?_, hz⟩, hzC⟩
          rintro rfl
          rw [hCdef, Finset.mem_inter] at hzC
          have := (mem_bigCleanTwins.mp hzC.2).1
          omega
      have hsplit2 := Finset.card_inter_add_card_sdiff
        ((G.neighborFinset x).erase g) C
      have hNxcard : ((G.neighborFinset x).erase g).card ≤ 4 := by
        calc ((G.neighborFinset x).erase g).card
            ≤ (G.neighborFinset x).card :=
              Finset.card_le_card (Finset.erase_subset _ _)
          _ = G.degree x := G.card_neighborFinset_eq_degree x
          _ = 4 := hPdeg x hx
      omega
    calc ∑ x' ∈ (G.neighborFinset x).erase g \ C,
          (G.neighborFinset x' ∩ C).card
        ≤ ∑ _x' ∈ (G.neighborFinset x).erase g \ C, 2 := by
          refine Finset.sum_le_sum (fun x' hx' => ?_)
          rw [Finset.mem_sdiff, Finset.mem_erase] at hx'
          rw [hCdef]
          exact cloud_inter_card_le_two G h3 hblk4 hg hx'.1.1
      _ = ((G.neighborFinset x).erase g \ C).card * 2 := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (4 - (G.neighborFinset x ∩ C).card) * 2 :=
          Nat.mul_le_mul_right _ hdiff_card
  have hcross : ∑ x' ∈ (G.neighborFinset x).erase g,
      ((G.neighborFinset x ∩ C) ×ˢ (G.neighborFinset x' ∩ C)).card
      ≤ (G.neighborFinset x ∩ C).card * ((4 - (G.neighborFinset x ∩ C).card) * 2) := by
    calc ∑ x' ∈ (G.neighborFinset x).erase g,
          ((G.neighborFinset x ∩ C) ×ˢ (G.neighborFinset x' ∩ C)).card
        = ∑ x' ∈ (G.neighborFinset x).erase g,
            (G.neighborFinset x ∩ C).card * (G.neighborFinset x' ∩ C).card :=
          Finset.sum_congr rfl (fun x' _ => Finset.card_product _ _)
      _ = (G.neighborFinset x ∩ C).card *
            ∑ x' ∈ (G.neighborFinset x).erase g,
              (G.neighborFinset x' ∩ C).card := by rw [Finset.mul_sum]
      _ ≤ (G.neighborFinset x ∩ C).card *
            ((4 - (G.neighborFinset x ∩ C).card) * 2) :=
          Nat.mul_le_mul_left _ hsum_bound
  rw [Finset.offDiag_card]
  exact le_trans (Nat.add_le_add_left hcross _) (hfin _ hcx2)

open Classical in
/-- **The sharpened cloud bound.**  If no apex configuration exists, every
degree-`≥ 9` vertex has at most `13` big-clean-twin neighbours.  The shared-partner
channel `P2` and the partner-cross channel `P3` are both charged to the *same*
degree-`4` partner set `P`; combining the two per-mediator bounds pointwise gives
`offDiag(x) + cross(x) ≤ 6·c_x` for every `x ∈ P` (`c_x = |N(x)∩C| ≤ 2`), so
`P2 + P3 ≤ 6·Σ_x c_x = 12A` and `A(A−1) ≤ 12A ⟹ A ≤ 13` (vs. the loose `14A`
of `cloud_card_le`, which bounds the two channels separately). -/
theorem cloud_card_le_sharp {n : ℕ} (G : SimpleGraph (Fin n))
    (h3 : ∀ v : Fin n, 3 ≤ G.degree v)
    (hblk4 : ∀ x : Fin n, G.degree x = 4 → (hubTwins G x).card ≤ 2)
    (hnf : ¬∃ u v g : Fin n, ApexConfig n G u v g)
    {g : Fin n} (hg : 9 ≤ G.degree g) :
    (G.neighborFinset g ∩ bigCleanTwins G).card ≤ 13 := by
  classical
  set C : Finset (Fin n) := G.neighborFinset g ∩ bigCleanTwins G with hCdef
  have hcard : C.card * (C.card - 1) = C.offDiag.card := by
    rw [Finset.offDiag_card, Nat.mul_sub, Nat.mul_one]
  set P2 : Finset (Fin n × Fin n) :=
    C.offDiag.filter (fun p => ∃ w, w ≠ g ∧ G.Adj p.1 w ∧ G.Adj p.2 w) with hP2def
  set P3 : Finset (Fin n × Fin n) :=
    C.offDiag.filter (fun p => ∃ w w', G.Adj p.1 w ∧ w ≠ g ∧ G.Adj p.2 w' ∧
      w' ≠ g ∧ G.Adj w w') with hP3def
  have hcover : C.offDiag ⊆ P2 ∪ P3 := by
    intro p hp
    obtain ⟨hp1, hp2, hpne⟩ := Finset.mem_offDiag.mp hp
    rcases cloud_pair_mechanism G h3 hnf hg p.1 p.2 hp1 hp2 hpne with h' | h'
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, h'⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, h'⟩)
  have hsplit : C.offDiag.card ≤ P2.card + P3.card :=
    (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  -- the exchange identity: the non-`g` incidences into `C` total `2·|C|`
  have hexch : ∑ w ∈ Finset.univ.erase g, (G.neighborFinset w ∩ C).card
      = 2 * C.card := by
    rw [sum_nbr_inter_comm]
    have hpt : ∀ u ∈ C,
        (G.neighborFinset u ∩ Finset.univ.erase g).card = 2 := by
      intro u hu
      have huC : u ∈ C := hu
      rw [hCdef, Finset.mem_inter] at huC
      have hu3 : G.degree u = 3 := (mem_bigCleanTwins.mp huC.2).1
      have hgu : g ∈ G.neighborFinset u := by
        rw [SimpleGraph.mem_neighborFinset]
        exact ((G.mem_neighborFinset g u).mp huC.1).symm
      have hset : G.neighborFinset u ∩ Finset.univ.erase g
          = (G.neighborFinset u).erase g := by
        ext z
        simp [Finset.mem_inter, Finset.mem_erase, and_comm]
      rw [hset, Finset.card_erase_of_mem hgu,
        SimpleGraph.card_neighborFinset_eq_degree, hu3]
    calc ∑ u ∈ C, (G.neighborFinset u ∩ Finset.univ.erase g).card
        = ∑ _u ∈ C, 2 := Finset.sum_congr rfl hpt
      _ = 2 * C.card := by rw [Finset.sum_const, smul_eq_mul]; ring
  -- the partner set `P`
  set P : Finset (Fin n) := C.biUnion (fun t => (G.neighborFinset t).erase g)
    with hPdef
  have hPsub : P ⊆ Finset.univ.erase g := by
    intro x hx
    rw [hPdef] at hx
    obtain ⟨t, -, hxt⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_erase.mpr
      ⟨(Finset.mem_erase.mp hxt).1, Finset.mem_univ x⟩
  have hPdeg : ∀ x ∈ P, G.degree x = 4 := by
    intro x hx
    rw [hPdef] at hx
    obtain ⟨t, htC, hxt⟩ := Finset.mem_biUnion.mp hx
    have htC' := htC
    rw [hCdef, Finset.mem_inter] at htC'
    exact cloud_partner_deg G h3 hg htC'.2
      ((G.mem_neighborFinset g t).mp htC'.1).symm x
      ((G.mem_neighborFinset t x).mp (Finset.mem_of_mem_erase hxt))
      (Finset.ne_of_mem_erase hxt)
  have hPincid : ∑ x ∈ P, (G.neighborFinset x ∩ C).card ≤ 2 * C.card := by
    calc ∑ x ∈ P, (G.neighborFinset x ∩ C).card
        ≤ ∑ w ∈ Finset.univ.erase g, (G.neighborFinset w ∩ C).card :=
          Finset.sum_le_sum_of_subset_of_nonneg hPsub
            (fun _ _ _ => Nat.zero_le _)
      _ = 2 * C.card := hexch
  -- P2 is charged to `P`
  have hP2sub : P2 ⊆ P.biUnion (fun x : Fin n => (G.neighborFinset x ∩ C).offDiag) := by
    intro p hp
    obtain ⟨hpd, w, hwg, hw1, hw2⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1, hp2, hpne⟩ := Finset.mem_offDiag.mp hpd
    have hwP : w ∈ P := by
      rw [hPdef]
      exact Finset.mem_biUnion.mpr ⟨p.1, hp1,
        Finset.mem_erase.mpr ⟨hwg, (G.mem_neighborFinset p.1 w).mpr hw1⟩⟩
    refine Finset.mem_biUnion.mpr ⟨w, hwP, ?_⟩
    refine Finset.mem_offDiag.mpr ⟨?_, ?_, hpne⟩
    · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w p.1).mpr hw1.symm, hp1⟩
    · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w p.2).mpr hw2.symm, hp2⟩
  -- P3 is charged to `P`
  have hP3sub : P3 ⊆ P.biUnion (fun x : Fin n =>
      ((G.neighborFinset x).erase g).biUnion (fun x' : Fin n =>
        (G.neighborFinset x ∩ C) ×ˢ (G.neighborFinset x' ∩ C))) := by
    intro p hp
    obtain ⟨hpd, w, w', hw, hwg, hw', hw'g, hww'⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1, hp2, hpne⟩ := Finset.mem_offDiag.mp hpd
    have hwP : w ∈ P := by
      rw [hPdef]
      exact Finset.mem_biUnion.mpr ⟨p.1, hp1,
        Finset.mem_erase.mpr ⟨hwg, (G.mem_neighborFinset p.1 w).mpr hw⟩⟩
    refine Finset.mem_biUnion.mpr ⟨w, hwP, ?_⟩
    refine Finset.mem_biUnion.mpr
      ⟨w', Finset.mem_erase.mpr ⟨hw'g, (G.mem_neighborFinset w w').mpr hww'⟩, ?_⟩
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w p.1).mpr hw.symm, hp1⟩
    · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset w' p.2).mpr hw'.symm, hp2⟩
  -- the pointwise combined mediator bound: `offDiag(x) + cross(x) ≤ 6·c_x`
  have hfin : ∀ c : ℕ, c ≤ 2 → c * c - c + c * ((4 - c) * 2) ≤ 6 * c := by
    intro c hc
    interval_cases c <;> omega
  have hperx :=
      cloud_card_le_sharp_hperx (n := n) (G := G) (h3) (hblk4) (g := g) (hg) (C := C) (hCdef)
        (hcard) (hP2def) (hP3def) (hcover) (hsplit) (hexch) (hPdef) (hPsub) (hPdeg) (hPincid)
        (hP2sub) (hP3sub) (hfin)
  -- assemble the combined bound `P2 + P3 ≤ 12A`
  have hP2c : P2.card ≤ ∑ x ∈ P, (G.neighborFinset x ∩ C).offDiag.card :=
    (Finset.card_le_card hP2sub).trans Finset.card_biUnion_le
  have hP3c : P3.card ≤ ∑ x ∈ P, ∑ x' ∈ (G.neighborFinset x).erase g,
      ((G.neighborFinset x ∩ C) ×ˢ (G.neighborFinset x' ∩ C)).card := by
    calc P3.card
        ≤ (P.biUnion (fun x : Fin n =>
            ((G.neighborFinset x).erase g).biUnion (fun x' : Fin n =>
              (G.neighborFinset x ∩ C) ×ˢ (G.neighborFinset x' ∩ C)))).card :=
          Finset.card_le_card hP3sub
      _ ≤ ∑ x ∈ P, (((G.neighborFinset x).erase g).biUnion (fun x' : Fin n =>
            (G.neighborFinset x ∩ C) ×ˢ (G.neighborFinset x' ∩ C))).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ x ∈ P, ∑ x' ∈ (G.neighborFinset x).erase g,
            ((G.neighborFinset x ∩ C) ×ˢ (G.neighborFinset x' ∩ C)).card :=
          Finset.sum_le_sum (fun x _ => Finset.card_biUnion_le)
  have hcomb : P2.card + P3.card ≤ 12 * C.card := by
    calc P2.card + P3.card
        ≤ (∑ x ∈ P, (G.neighborFinset x ∩ C).offDiag.card)
          + ∑ x ∈ P, ∑ x' ∈ (G.neighborFinset x).erase g,
              ((G.neighborFinset x ∩ C) ×ˢ (G.neighborFinset x' ∩ C)).card :=
          Nat.add_le_add hP2c hP3c
      _ = ∑ x ∈ P, ((G.neighborFinset x ∩ C).offDiag.card
            + ∑ x' ∈ (G.neighborFinset x).erase g,
                ((G.neighborFinset x ∩ C) ×ˢ (G.neighborFinset x' ∩ C)).card) :=
          (Finset.sum_add_distrib).symm
      _ ≤ ∑ x ∈ P, 6 * (G.neighborFinset x ∩ C).card :=
          Finset.sum_le_sum hperx
      _ = 6 * ∑ x ∈ P, (G.neighborFinset x ∩ C).card := by rw [Finset.mul_sum]
      _ ≤ 6 * (2 * C.card) := Nat.mul_le_mul_left 6 hPincid
      _ = 12 * C.card := by ring
  have hquad : C.card * (C.card - 1) ≤ 12 * C.card + 0 := by
    calc C.card * (C.card - 1) = C.offDiag.card := hcard
      _ ≤ P2.card + P3.card := hsplit
      _ ≤ 12 * C.card := hcomb
      _ = 12 * C.card + 0 := by ring
  have := nat_quad_bound C.card 12 0 hquad
  omega

/-! ## Threading the sharpened mid-leaf bound into the wall chain

Threads the sharpened mid-leaves bound (`143 → 108`, from spending the base mid
leaf's own σ-budget `Σσ ≤ 2 ⟹ Σdeg ≤ 19`) through the usable-count chain: the
coverage improves to `13A + 137`, the usable cap to `C_m = 306`, and the wall to
`boundLin 3203 = 17692`. The three theorems mirror `usable_deg3_card_le_of_cloud`,
`usable_deg3_card_le_sharp` and `acmax_conjecture_large_n_sharp` with the
sharpened constants; the original chain is left untouched. -/

open Classical in
/-- **The sharpened m-bound from the max-cloud bound** (no firing configuration).
Mirror of `usable_deg3_card_le_of_cloud` with the sharpened mid split
(`usable_deg3_split_mid_sharp`, `108`) in place of `usable_deg3_split_mid`
(`143`); the coverage constant drops accordingly to

  `m ≤ 13·A + 137`

(`108` mid split + `2` M-bridge + the coverage bound `13A + 27`).  Needs the
extra `min degree ≥ 3` hypothesis, which is available here as `h.min_degree`. -/
theorem usable_deg3_card_le_of_cloud_sharp (n : ℕ) (G : SimpleGraph (Fin n))
    (h : ResidualCore n G) (hcpt : ¬HasUsableFarPair G)
    (hmech : ∀ u v : Fin n, u ∈ bigCleanTwins G → v ∈ bigCleanTwins G → u ≠ v →
      (∃ w, G.Adj u w ∧ G.Adj v w) ∨
      (∃ w w', G.Adj u w ∧ G.Adj v w' ∧ G.Adj w w' ∧
        (G.degree w ≤ 4 ∨ G.degree w' ≤ 4)))
    (A : ℕ) (hA : ∀ w : Fin n, 9 ≤ G.degree w →
      (G.neighborFinset w ∩ bigCleanTwins G).card ≤ A)
    (hblk : ∀ w : Fin n, G.degree w ≤ 15 →
      (hubTwins G w).card + 2 ≤ G.degree w)
    (huniq : ∀ t₁ t₂ t₃ t₄ : Fin n, G.Adj t₁ t₂ → G.Adj t₃ t₄ →
      G.degree t₁ = 3 → G.degree t₂ = 3 → G.degree t₃ = 3 →
      G.degree t₄ = 3 →
      ({t₁, t₂} : Finset (Fin n)) = ({t₃, t₄} : Finset (Fin n))) :
    (Finset.univ.filter (fun v : Fin n => G.degree v = 3 ∧ sigS G v ≤ 2)).card
      ≤ 13 * A + 137 := by
  classical
  have hml : ∀ z : Fin n, G.degree z ≤ 4 →
      ((G.neighborFinset z).filter (fun t => G.degree t = 3)).card
        ≤ G.degree z - 2 := by
    intro z hz4
    have h1 := hblk z (by omega)
    have h2 : (G.neighborFinset z).filter (fun t => G.degree t = 3)
        = hubTwins G z := by
      rw [hubTwins]
      ext t
      simp only [Finset.mem_filter, Finset.mem_inter, mem_deg3Set]
    rw [h2]
    omega
  -- `m ≤ 108 + |bigCleanTwins| + 2`: sharpened mid split + M-bridge
  have h1 := usable_deg3_split_mid_sharp n G h.min_degree hcpt hblk
  have h2 : (Finset.univ.filter (fun u : Fin n =>
      G.degree u = 3 ∧ sigS G u ≤ 2 ∧
      ∃ x ∈ G.neighborFinset u, 9 ≤ G.degree x)).card
      ≤ (bigCleanTwins G).card + 2 := by
    have hsub : (Finset.univ.filter (fun u : Fin n =>
        G.degree u = 3 ∧ sigS G u ≤ 2 ∧
        ∃ x ∈ G.neighborFinset u, 9 ≤ G.degree x))
        ⊆ bigCleanTwins G ∪ (Finset.univ.filter (fun u : Fin n =>
          G.degree u = 3 ∧ ∃ x ∈ G.neighborFinset u, G.degree x = 3)) := by
      intro u hu
      rw [Finset.mem_filter] at hu
      obtain ⟨-, hd, hs, hbigx⟩ := hu
      by_cases hno3 : ∀ x ∈ G.neighborFinset u, G.degree x ≠ 3
      · exact Finset.mem_union_left _
          (mem_bigCleanTwins.mpr ⟨hd, hs, hbigx, hno3⟩)
      · simp only [not_forall, ne_eq, not_not] at hno3
        obtain ⟨x, hxmem, hx3⟩ := hno3
        exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨Finset.mem_univ u, hd, x, hxmem, hx3⟩)
    calc (Finset.univ.filter (fun u : Fin n =>
        G.degree u = 3 ∧ sigS G u ≤ 2 ∧
        ∃ x ∈ G.neighborFinset u, 9 ≤ G.degree x)).card
        ≤ (bigCleanTwins G ∪ (Finset.univ.filter (fun u : Fin n =>
            G.degree u = 3 ∧ ∃ x ∈ G.neighborFinset u, G.degree x = 3))).card :=
          Finset.card_le_card hsub
      _ ≤ (bigCleanTwins G).card + (Finset.univ.filter (fun u : Fin n =>
            G.degree u = 3 ∧ ∃ x ∈ G.neighborFinset u, G.degree x = 3)).card :=
          Finset.card_union_le _ _
      _ ≤ (bigCleanTwins G).card + 2 := by
          have := deg3_with_deg3_nbr_card_le_two G huniq
          omega
  -- the coverage bound
  have hcov := bigclean_pair_coverage n G h.min_degree hmech A hA hml
  omega

open Classical in
/-- **The sharpened concrete m-bound** `m ≤ 306 = 13·13 + 137`.  Mirror of
`usable_deg3_card_le_sharp` (`GeneralCloudSharp`) feeding the sharpened cloud cap
`A = 13` (`cloud_card_le_sharp`) through the sharpened coverage assembly
`usable_deg3_card_le_of_cloud_sharp` (`m ≤ 13A + 137`).  Down from `341`. -/
theorem usable_deg3_card_le_sharp2 (n : ℕ) (G : SimpleGraph (Fin n))
    (h : ResidualCore n G) (hcpt : ¬HasUsableFarPair G)
    (hnofire : ¬∃ u v g g' : Fin n, FiringConfig n G u v g g')
    (hnapex : ¬∃ u v g : Fin n, ApexConfig n G u v g)
    (hblk : ∀ w : Fin n, G.degree w ≤ 15 →
      (hubTwins G w).card + 2 ≤ G.degree w)
    (huniq : ∀ t₁ t₂ t₃ t₄ : Fin n, G.Adj t₁ t₂ → G.Adj t₃ t₄ →
      G.degree t₁ = 3 → G.degree t₂ = 3 → G.degree t₃ = 3 →
      G.degree t₄ = 3 →
      ({t₁, t₂} : Finset (Fin n)) = ({t₃, t₄} : Finset (Fin n))) :
    (Finset.univ.filter (fun v : Fin n => G.degree v = 3 ∧ sigS G v ≤ 2)).card
      ≤ 306 := by
  classical
  have hblk4 : ∀ x : Fin n, G.degree x = 4 → (hubTwins G x).card ≤ 2 := by
    intro x hx4
    have h1 := hblk x (by omega)
    omega
  have hA : ∀ w : Fin n, 9 ≤ G.degree w →
      (G.neighborFinset w ∩ bigCleanTwins G).card ≤ 13 :=
    fun w hw => cloud_card_le_sharp G h.min_degree hblk4 hnapex hw
  have := usable_deg3_card_le_of_cloud_sharp n G h hcpt
    (bigclean_mechanism_of_no_firing n G h.min_degree hnofire) 13 hA hblk huniq
  omega

open Classical in
/-- The doubly-sharpened residual threshold
`boundLin ((128·306 + 34508)/23) = boundLin 3203 = 17692`. -/
theorem boundLin_sharp2_eq : boundLin ((128 * 306 + 34508) / 23) = 17692 := by
  norm_num [boundLin]

open Classical in
/-- **General ACMAX for large `n`, doubly-sharpened form.**  Every `ResidualCore`
graph with `n > 17692` has `algConn ≤ 2` — no open hypotheses.  Same dispatch as
`acmax_general_residual_large_sharp`, but with the doubly-sharpened concrete
m-bound `m ≤ 306` (mid split `108`, cloud cap `A = 13`), lowering the threshold
from `18764` to `17692`. -/
theorem acmax_general_residual_large_sharp2 (n : ℕ) [Nonempty (Fin n)]
    (G : SimpleGraph (Fin n)) (h : ResidualCore n G)
    (hn : boundLin ((128 * 306 + 34508) / 23) < n) :
    algConn G ≤ 2 := by
  classical
  have hnBig : 520 ≤ n := by
    unfold boundLin at hn
    omega
  rcases blocks_or_smallcap n (by omega) G with hblkfire | hblk
  · exact hblkfire
  rcases medges_or_single n (by omega) G with hmfire | huniq
  · exact hmfire
  by_cases hfire : ∃ u v g g' : Fin n, FiringConfig n G u v g g'
  · obtain ⟨u, v, g, g', hf⟩ := hfire
    exact firingConfig_closes G hf
  by_cases hapex : ∃ u v g : Fin n, ApexConfig n G u v g
  · obtain ⟨u, v, g, hf⟩ := hapex
    exact apexConfig_closes G hf
  exact acmax_general_final_threeconn 306 n G h hn hnBig
    (fun _ hcpt _ =>
      usable_deg3_card_le_sharp2 n G h hcpt hfire hapex hblk huniq)

open Classical in
/-- **Kolokolnikov Conjecture 1.5 for large `n`, doubly-sharpened.**  Every simple
graph on `Fin n` with exactly `2(n−2)` edges and `n > 17692` has algebraic
connectivity at most `2` — the finite residual range shrinks to
`19 ≤ n ≤ 17692` (from `19 ≤ n ≤ 18764`). -/
theorem acmax_conjecture_large_n_sharp2 (n : ℕ) [Nonempty (Fin n)]
    (G : SimpleGraph (Fin n)) (hm : G.edgeFinset.card = 2 * (n - 2))
    (hn : boundLin ((128 * 306 + 34508) / 23) < n) :
    algConn G ≤ 2 := by
  have hn12 : 12 ≤ n := by
    unfold boundLin at hn
    omega
  exact algConn_le_two_of_card_general_cond n hn12 G hm
    (fun h => acmax_general_residual_large_sharp2 n G h hn)

end ACMax
