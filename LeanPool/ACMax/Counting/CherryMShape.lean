/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import LeanPool.ACMax.Counting.Cherry
public import LeanPool.ACMax.Counting.PoorCorner

/-!
# The M-shape analysis and the complete `Δ ≤ 4` closure

Closes the `e(M) ≥ 3` part of the blocked cherry corner in the sea regime
(`Δ ≤ 4`), and assembles the full `Δ ≤ 4` ("sea") closure of the residual core.
Under `ResidualCore` the degree-3 graph `M` on `D = deg3Set` has no triangle, no
`4`-cycle, no induced `2K₂` and `Δ(M) ≤ 3`, so with `e(M) ≥ 3` its support is
exactly one of five shapes: `P4`, `claw`, `chair`, `S22` (double star) or `C5`,
with every other degree-3 vertex an iso twin.

## Main results

* `mshape_classify` — the M-shape classification of the `e(M) ≥ 3` support.
* Two structural atoms: `hub_mnbrs_not_adj` (a hub sees at most one end of each
  `M`-edge; `(≤4,3,3)`-triangle, `n ≥ 9`) and `hub_no_dist2_pair` (a hub never
  sees two `M`-vertices at `M`-distance `2`; `C₄` `∑ = 13`, `n ≥ 11`), so a rich
  hub's `M`-neighbourhood is pairwise `M`-distance `≥ 3`.
* `s22_split_twoBlock` — the `S22` shape splits unconditionally into its two
  stars (tie `2·1 + 5 + 5 = 12`).
* `p4_corner_close` and the claw/chair/C5 kills — every other shape closes: in
  claw/chair/C5 a corner-provided rich hub misses a cherry and fires
  `two_twin_cherry_twoBlock`; the `P4` shape needs the role analysis (`β`/`γ`/`α*`
  pinned by the two atoms and the share bound `hubs_share_le_one`) feeding
  `two_hub_opposite_twin_twoBlock` or the private-iso pair cut.
* `blockedCherryCorner_close_eM_ge3`, `caseCherry_algConn_le_two_of_sea` — the
  `e(M) ≥ 3` corner closure and hence the complete cherry-case closure for
  `Δ ≤ 4`.
* `residual_sea_algConn_le_two` — for every `n ≥ 23`, a `ResidualCore` graph with
  `Δ ≤ 4` has `algConn G ≤ 2`, dispatched by `eM_trichotomy`: `e(M) ≤ 1` via
  `x0_corner_close`, `e(M) ≥ 2` via `caseCherry_algConn_le_two_of_sea`. Only the
  `Δ ≥ 5` ("fat") side of `ResidualCore` remains open.
-/

@[expose] public section

namespace ACMax

variable {V : Type*} [Fintype V]

/-! ## Small neighbourhood atoms -/

open Classical in
/-- A degree-`3` vertex with three known distinct neighbours has no others. -/
theorem deg3_nbr_pin (G : SimpleGraph V) {v p q r w : V} (hdv : G.degree v = 3)
    (hp : G.Adj v p) (hq : G.Adj v q) (hr : G.Adj v r)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (hw : G.Adj v w) :
    w = p ∨ w = q ∨ w = r := by
  have hsub : ({p, q, r} : Finset V) ⊆ G.neighborFinset v := by
    intro u hu
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · exact (G.mem_neighborFinset v u).mpr hp
    · exact (G.mem_neighborFinset v u).mpr hq
    · exact (G.mem_neighborFinset v u).mpr hr
  have hcard : ({p, q, r} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hpq, hpr]), Finset.card_pair hqr]
  have hle : (G.neighborFinset v).card ≤ ({p, q, r} : Finset V).card := by
    rw [hcard, G.card_neighborFinset_eq_degree, hdv]
  have heq := Finset.eq_of_subset_of_card_le hsub hle
  have : w ∈ ({p, q, r} : Finset V) := by
    rw [heq]
    exact (G.mem_neighborFinset v w).mpr hw
  simpa using this

open Classical in
/-- A degree-`4` vertex with four known distinct neighbours has no others. -/
theorem deg4_nbr_pin (G : SimpleGraph V) {g p q r s w : V} (hdg : G.degree g = 4)
    (hp : G.Adj g p) (hq : G.Adj g q) (hr : G.Adj g r) (hs : G.Adj g s)
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (hw : G.Adj g w) : w = p ∨ w = q ∨ w = r ∨ w = s := by
  have hsub : ({p, q, r, s} : Finset V) ⊆ G.neighborFinset g := by
    intro u hu
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact (G.mem_neighborFinset g u).mpr hp
    · exact (G.mem_neighborFinset g u).mpr hq
    · exact (G.mem_neighborFinset g u).mpr hr
    · exact (G.mem_neighborFinset g u).mpr hs
  have hcard : ({p, q, r, s} : Finset V).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hpq, hpr, hps]),
      Finset.card_insert_of_notMem (by simp [hqr, hqs]), Finset.card_pair hrs]
  have hle : (G.neighborFinset g).card ≤ ({p, q, r, s} : Finset V).card := by
    rw [hcard, G.card_neighborFinset_eq_degree, hdg]
  have heq := Finset.eq_of_subset_of_card_le hsub hle
  have : w ∈ ({p, q, r, s} : Finset V) := by
    rw [heq]
    exact (G.mem_neighborFinset g w).mpr hw
  simpa using this

open Classical in
/-- An `M`-vertex (a degree-`3` vertex with a degree-`3` neighbour) is not iso. -/
theorem not_iso_of_mnbr (G : SimpleGraph V) {v w : V}
    (hvw : G.Adj v w) (hw3 : G.degree w = 3) : v ∉ isoTwins G :=
  fun hv => (mem_isoTwins.mp hv).2 w hvw hw3

open Classical in
/-- An iso twin is adjacent to no degree-`3` vertex (symmetric form). -/
theorem deg3_not_adj_iso (G : SimpleGraph V) {v t : V}
    (hv3 : G.degree v = 3) (ht : t ∈ isoTwins G) : ¬G.Adj v t :=
  fun hadj => (mem_isoTwins.mp ht).2 v hadj.symm hv3

/-! ## The exclusion atoms (F0 / F1 / F5 / the universal share bound) -/

open Classical in
/-- **F0**: no triangle of degree-`3` vertices (`∑ = 9`, good from `n = 6`). -/
theorem deg3_triangle_false (n : ℕ) (hn : 6 ≤ n) (G : SimpleGraph (Fin n))
    (hT : ¬HasGoodTriangle n G) {u v w : Fin n}
    (hdu : G.degree u = 3) (hdv : G.degree v = 3) (hdw : G.degree w = 3)
    (huv : G.Adj u v) (hvw : G.Adj v w) (huw : G.Adj u w) : False := by
  refine hT ⟨u, v, w, G.ne_of_adj huv, G.ne_of_adj hvw, G.ne_of_adj huw, huv, hvw,
    huw, ?_⟩
  rw [hdu, hdv, hdw]
  have h9 : (3 + 3 + 3 - 6 : ℕ) = 3 := by norm_num
  rw [h9]
  omega

open Classical in
/-- **F1**: a degree-`≤ 4` hub never sees both ends of an `M`-edge
(`∑ ≤ 10`, good from `n = 9`). -/
theorem hub_mnbrs_not_adj (n : ℕ) (hn : 9 ≤ n) (G : SimpleGraph (Fin n))
    (hT : ¬HasGoodTriangle n G) {g t₁ t₂ : Fin n}
    (hdg : G.degree g ≤ 4) (hd₁ : G.degree t₁ = 3) (hd₂ : G.degree t₂ = 3)
    (h12 : G.Adj t₁ t₂) (hg1 : G.Adj g t₁) (hg2 : G.Adj g t₂) : False := by
  refine hT ⟨g, t₁, t₂, G.ne_of_adj hg1, G.ne_of_adj h12, G.ne_of_adj hg2, hg1, h12,
    hg2, ?_⟩
  rw [hd₁, hd₂]
  calc n * (G.degree g + 3 + 3 - 6)
      ≤ n * 4 := Nat.mul_le_mul_left n (by omega)
    _ ≤ 2 * (3 * (n - 3)) := by omega

open Classical in
/-- **F5**: a degree-`4` hub never sees two `M`-vertices at `M`-distance `2`
(the `C₄` `g−t₁−v−t₂` has `∑ = 13`, good from `n = 11`). -/
theorem hub_no_dist2_pair (n : ℕ) (hn : 11 ≤ n) (G : SimpleGraph (Fin n))
    (hT : ¬HasGoodTriangle n G) (hC4 : ¬HasGoodC4 n G) {g v t₁ t₂ : Fin n}
    (hdg : G.degree g = 4) (hdv : G.degree v = 3)
    (hd₁ : G.degree t₁ = 3) (hd₂ : G.degree t₂ = 3) (hne : t₁ ≠ t₂)
    (hv1 : G.Adj v t₁) (hv2 : G.Adj v t₂)
    (hg1 : G.Adj g t₁) (hg2 : G.Adj g t₂) : False := by
  by_cases h12 : G.Adj t₁ t₂
  · exact deg3_triangle_false n (by omega) G hT hdv hd₁ hd₂ hv1 h12 hv2
  by_cases hgv : G.Adj g v
  · exact hub_mnbrs_not_adj n (by omega) G hT (le_of_eq hdg) hd₁ hdv hv1.symm hg1 hgv
  have hgv' : g ≠ v := fun e => by rw [e, hdv] at hdg; omega
  have hgt₁ : g ≠ t₁ := G.ne_of_adj hg1
  have hgt₂ : g ≠ t₂ := G.ne_of_adj hg2
  have hvt₁ : t₁ ≠ v := (G.ne_of_adj hv1).symm
  have hvt₂ : v ≠ t₂ := G.ne_of_adj hv2
  refine hC4 ⟨g, t₁, v, t₂, ?_, hg1, hv1.symm, hv2, hg2.symm, hgv, h12, ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [hgt₁, hgv', hgt₂]),
      Finset.card_insert_of_notMem (by simp [hvt₁, hne]),
      Finset.card_pair hvt₂]
  · rw [hdg, hdv, hd₁, hd₂]
    calc n * (4 + 3 + 3 + 3 - 8)
        = n * 5 := by norm_num
      _ ≤ 2 * (4 * (n - 4)) := by omega

open Classical in
/-- **The universal share bound** (`n ≥ 18`): two distinct degree-`4` hubs share at
most one degree-`3` twin — adjacent twins die by the `(4,3,3)`-triangle, adjacent
hubs by the `(4,4,3)`-triangle, and the rest by the `∑ = 14` good `C₄`. -/
theorem hubs_share_le_one (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Fin n))
    (hT : ¬HasGoodTriangle n G) (hC4 : ¬HasGoodC4 n G) {g h : Fin n}
    (hdg : G.degree g = 4) (hdh : G.degree h = 4) (hne : g ≠ h) :
    (sharedTwins G g h).card ≤ 1 := by
  by_contra hgt
  rw [not_le] at hgt
  obtain ⟨t₁, ht1, t₂, ht2, hne12⟩ := Finset.one_lt_card.mp hgt
  obtain ⟨hgt1, hht1, h31⟩ := sharedTwins_spec.mp ht1
  obtain ⟨hgt2, hht2, h32⟩ := sharedTwins_spec.mp ht2
  by_cases h12 : G.Adj t₁ t₂
  · exact hub_mnbrs_not_adj n (by omega) G hT (le_of_eq hdg) h31 h32 h12 hgt1 hgt2
  by_cases hgh : G.Adj g h
  · exact shared_twin_hubs_nonadj n hn G hT h31 (le_of_eq hdg) (le_of_eq hdh)
      hgt1 hht1 hne hgh
  have hgt1' : g ≠ t₁ := fun e => by rw [← e] at h31; omega
  have hgt2' : g ≠ t₂ := fun e => by rw [← e] at h32; omega
  have hht1' : h ≠ t₁ := fun e => by rw [← e] at h31; omega
  have hht2' : h ≠ t₂ := fun e => by rw [← e] at h32; omega
  refine hC4 ⟨g, t₁, h, t₂, ?_, hgt1, hht1.symm, hht2, hgt2.symm, hgh, h12, ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [hgt1', hne, hgt2']),
      Finset.card_insert_of_notMem (by simp [Ne.symm hht1', hne12]),
      Finset.card_insert_of_notMem (by simp [hht2']), Finset.card_singleton]
  · rw [hdg, hdh, h31, h32]
    calc n * (4 + 3 + 4 + 3 - 8)
        = n * 6 := by norm_num
      _ ≤ 2 * (4 * (n - 4)) := by omega

open Classical in
/-- Two shared twins force `False` (extraction form of `hubs_share_le_one`). -/
theorem hubs_share_two_false (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Fin n))
    (hT : ¬HasGoodTriangle n G) (hC4 : ¬HasGoodC4 n G) {g h t₁ t₂ : Fin n}
    (hdg : G.degree g = 4) (hdh : G.degree h = 4) (hne : g ≠ h) (hne12 : t₁ ≠ t₂)
    (hd₁ : G.degree t₁ = 3) (hd₂ : G.degree t₂ = 3)
    (hg1 : G.Adj g t₁) (hh1 : G.Adj h t₁) (hg2 : G.Adj g t₂) (hh2 : G.Adj h t₂) :
    False := by
  have hsub : ({t₁, t₂} : Finset (Fin n)) ⊆ sharedTwins G g h := by
    intro u hu
    rw [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact sharedTwins_spec.mpr ⟨hg1, hh1, hd₁⟩
    · exact sharedTwins_spec.mpr ⟨hg2, hh2, hd₂⟩
  have h2 : 2 ≤ (sharedTwins G g h).card := by
    calc 2 = ({t₁, t₂} : Finset (Fin n)).card := (Finset.card_pair hne12).symm
      _ ≤ _ := Finset.card_le_card hsub
  have := hubs_share_le_one n hn G hT hC4 hdg hdh hne
  omega

/-! ## The iso-twin supply and the corner pigeonhole -/

open Classical in
/-- Iso-twin supply through a covering set: if every degree-`3` vertex outside `S`
is iso, then `|D| ≤ |Iso| + |S|`. -/
theorem iso_card_of_cover (G : SimpleGraph V) (S : Finset V)
    (hS : ∀ v : V, G.degree v = 3 → v ∉ S → v ∈ isoTwins G) :
    (deg3Set G).card ≤ (isoTwins G).card + S.card := by
  have hsub : deg3Set G \ S ⊆ isoTwins G := by
    intro v hv
    rw [Finset.mem_sdiff] at hv
    exact hS v (mem_deg3Set.mp hv.1) hv.2
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_sdiff_add_card_inter (deg3Set G) S
  have h3 : (deg3Set G ∩ S).card ≤ S.card :=
    Finset.card_le_card Finset.inter_subset_right
  omega

open Classical in
/-- **The corner pigeonhole count** (sea regime): if every iso twin is
double-blocked, then `2·|Iso| ≤ 2·#(rich CT hubs) + |CT|`. -/
theorem corner_rich_bound (G : SimpleGraph V) (hsea : ∀ v : V, G.degree v ≤ 4)
    {x z y : V} (hch : Cherry G x z y)
    (hblock : ∀ t ∈ isoTwins G, 2 ≤ (badApexNbrs G x z y t).card) :
    2 * (isoTwins G).card
      ≤ 2 * ((cherryHubs G x z y).filter (fun w => 2 ≤ (isoNbrs G w).card)).card
        + (cherryHubs G x z y).card := by
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
  have hdemand : 2 * (isoTwins G).card
      ≤ ∑ w ∈ cherryHubs G x z y, (G.neighborFinset w ∩ isoTwins G).card := by
    rw [← cross_count G (isoTwins G) (cherryHubs G x z y)]
    calc 2 * (isoTwins G).card = ∑ _t ∈ isoTwins G, 2 := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ _ := Finset.sum_le_sum hstep1
  have hcap : ∀ w ∈ cherryHubs G x z y, (isoNbrs G w).card ≤ 3 := by
    intro w hw
    obtain ⟨hw4, hwadj⟩ := mem_cherryHubs.mp hw
    obtain ⟨c, hcN, hcI⟩ : ∃ c, c ∈ G.neighborFinset w ∧ c ∉ isoTwins G := by
      rcases hwadj with hz' | hx' | hy'
      · exact ⟨z, (G.mem_neighborFinset w z).mpr hz', cherry_z_not_iso G hch⟩
      · exact ⟨x, (G.mem_neighborFinset w x).mpr hx', cherry_x_not_iso G hch⟩
      · exact ⟨y, (G.mem_neighborFinset w y).mpr hy', cherry_y_not_iso G hch⟩
    have hsub : isoNbrs G w ⊆ (G.neighborFinset w).erase c := by
      intro u hu
      obtain ⟨h1, h2⟩ := mem_isoNbrs.mp hu
      exact Finset.mem_erase.mpr
        ⟨fun e => hcI (e ▸ h2), (G.mem_neighborFinset w u).mpr h1⟩
    have hle := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hcN, G.card_neighborFinset_eq_degree] at hle
    have := hsea w
    omega
  have hsplit2 := Finset.sum_filter_add_sum_filter_not (cherryHubs G x z y)
    (fun w => 2 ≤ (isoNbrs G w).card)
    (fun w => (isoNbrs G w).card)
  have hrich : ∑ w ∈ (cherryHubs G x z y).filter (fun w => 2 ≤ (isoNbrs G w).card),
      (isoNbrs G w).card
      ≤ 3 * ((cherryHubs G x z y).filter (fun w => 2 ≤ (isoNbrs G w).card)).card := by
    calc ∑ w ∈ (cherryHubs G x z y).filter (fun w => 2 ≤ (isoNbrs G w).card),
          (isoNbrs G w).card
        ≤ ∑ _w ∈ (cherryHubs G x z y).filter (fun w => 2 ≤ (isoNbrs G w).card), 3 :=
          Finset.sum_le_sum fun w hw => hcap w (Finset.mem_of_mem_filter w hw)
      _ = _ := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hpoor : ∑ w ∈ (cherryHubs G x z y).filter
        (fun w => ¬2 ≤ (isoNbrs G w).card), (isoNbrs G w).card
      ≤ ((cherryHubs G x z y).filter (fun w => ¬2 ≤ (isoNbrs G w).card)).card := by
    calc ∑ w ∈ (cherryHubs G x z y).filter
          (fun w => ¬2 ≤ (isoNbrs G w).card), (isoNbrs G w).card
        ≤ ∑ _w ∈ (cherryHubs G x z y).filter
            (fun w => ¬2 ≤ (isoNbrs G w).card), 1 := by
          refine Finset.sum_le_sum fun w hw => ?_
          have := (Finset.mem_filter.mp hw).2
          omega
      _ = _ := by rw [Finset.sum_const, smul_eq_mul, mul_one]
  have hfc := Finset.card_filter_add_card_filter_not (s := cherryHubs G x z y)
    (p := fun w => 2 ≤ (isoNbrs G w).card)
  have hdemand' : 2 * (isoTwins G).card
      ≤ ∑ w ∈ cherryHubs G x z y, (isoNbrs G w).card := by
    unfold isoNbrs
    exact hdemand
  omega

open Classical in
/-- Extraction: with `|Iso| ≥ 3`, the corner provides a **rich cherry-touching
hub**: degree exactly `4`, `≥ 2` iso twins, adjacent to a cherry vertex. -/
theorem corner_rich_one (G : SimpleGraph V) (hsea : ∀ v : V, G.degree v ≤ 4)
    {x z y : V} (hch : Cherry G x z y)
    (hblock : ∀ t ∈ isoTwins G, 2 ≤ (badApexNbrs G x z y t).card)
    (hIso : 3 ≤ (isoTwins G).card) :
    ∃ g : V, G.degree g = 4 ∧ 2 ≤ (isoNbrs G g).card ∧
      (G.Adj g z ∨ G.Adj g x ∨ G.Adj g y) := by
  have hb := corner_rich_bound G hsea hch hblock
  have h5 := cherryHubs_card_le_five G hch
  have hpos : 0 < ((cherryHubs G x z y).filter
      (fun w => 2 ≤ (isoNbrs G w).card)).card := by omega
  obtain ⟨g, hg⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at hg
  obtain ⟨hgCT, hgr⟩ := hg
  obtain ⟨hg4, hgadj⟩ := mem_cherryHubs.mp hgCT
  exact ⟨g, le_antisymm (hsea g) hg4, hgr, hgadj⟩

open Classical in
/-- Extraction: with `|Iso| ≥ 4`, the corner provides **two** rich cherry-touching
hubs. -/
theorem corner_rich_two (G : SimpleGraph V) (hsea : ∀ v : V, G.degree v ≤ 4)
    {x z y : V} (hch : Cherry G x z y)
    (hblock : ∀ t ∈ isoTwins G, 2 ≤ (badApexNbrs G x z y t).card)
    (hIso : 4 ≤ (isoTwins G).card) :
    ∃ g h : V, g ≠ h ∧
      (G.degree g = 4 ∧ 2 ≤ (isoNbrs G g).card ∧
        (G.Adj g z ∨ G.Adj g x ∨ G.Adj g y)) ∧
      (G.degree h = 4 ∧ 2 ≤ (isoNbrs G h).card ∧
        (G.Adj h z ∨ G.Adj h x ∨ G.Adj h y)) := by
  have hb := corner_rich_bound G hsea hch hblock
  have h5 := cherryHubs_card_le_five G hch
  have hpos : 1 < ((cherryHubs G x z y).filter
      (fun w => 2 ≤ (isoNbrs G w).card)).card := by omega
  obtain ⟨g, hg, h, hh, hne⟩ := Finset.one_lt_card.mp hpos
  rw [Finset.mem_filter] at hg hh
  obtain ⟨hgCT, hgr⟩ := hg
  obtain ⟨hhCT, hhr⟩ := hh
  obtain ⟨hg4, hgadj⟩ := mem_cherryHubs.mp hgCT
  obtain ⟨hh4, hhadj⟩ := mem_cherryHubs.mp hhCT
  exact ⟨g, h, hne, ⟨le_antisymm (hsea g) hg4, hgr, hgadj⟩,
    ⟨le_antisymm (hsea h) hh4, hhr, hhadj⟩⟩

open Classical in
/-- **The TwoTwin fire**: a degree-`4` hub with `≥ 2` iso twins avoiding a cherry
closes the graph (wrapper around `two_twin_cherry_twoBlock`). -/
theorem rich_avoiding_twoBlock (G : SimpleGraph V) {g x' z' y' : V}
    (hch : Cherry G x' z' y') (hdg : G.degree g = 4) (hr : 2 ≤ (isoNbrs G g).card)
    (hnz : ¬G.Adj g z') (hnx : ¬G.Adj g x') (hny : ¬G.Adj g y') :
    TwoBlockConfig G := by
  obtain ⟨t₁, ht₁, t₂, ht₂, hne⟩ := Finset.one_lt_card.mp hr
  obtain ⟨ha₁, hI₁⟩ := mem_isoNbrs.mp ht₁
  obtain ⟨ha₂, hI₂⟩ := mem_isoNbrs.mp ht₂
  exact two_twin_cherry_twoBlock G hch (by omega) (by omega) hI₁ hI₂ hne ha₁ ha₂
    hnz hnx hny

open Classical in
/-- `cherryHubs` is symmetric in the two cherry ends. -/
theorem cherryHubs_swap (G : SimpleGraph V) (x z y : V) :
    cherryHubs G x z y = cherryHubs G y z x := by
  unfold cherryHubs
  refine Finset.filter_congr fun w _ => ?_
  constructor
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)

open Classical in
/-- `badApexNbrs` is symmetric in the two cherry ends. -/
theorem badApexNbrs_swap (G : SimpleGraph V) (x z y t : V) :
    badApexNbrs G x z y t = badApexNbrs G y z x t := by
  unfold badApexNbrs
  rw [cherryHubs_swap]

open Classical in
/-- A `Cherry` with the two ends swapped. -/
theorem Cherry.swap {G : SimpleGraph V} {x z y : V} (h : Cherry G x z y) :
    Cherry G y z x :=
  ⟨h.deg_y, h.deg_z, h.deg_x, h.adj_zy, h.adj_zx, h.ne_xy.symm,
    fun hadj => h.nadj_xy hadj.symm⟩

/-! ## The five M-shapes

Each shape structure records: the degrees, the `M`-edges, all pairwise
distinctness, the **`M`-neighbour pinning** of every shape vertex (`mnbr_*`: its
only degree-`3` neighbours are its `M`-partners), and the isolation of every
degree-`3` vertex outside the shape (`iso_rest`).  These are exactly the facts the
classification tree produces and the kill lemmas consume. -/

open Classical in
/-- The `P4` shape: `M` is the path `a−b−c−d` (plus iso twins). -/
structure MShapeP4 (G : SimpleGraph V) (a b c d : V) : Prop where
  deg_a : G.degree a = 3
  deg_b : G.degree b = 3
  deg_c : G.degree c = 3
  deg_d : G.degree d = 3
  adj_ab : G.Adj a b
  adj_bc : G.Adj b c
  adj_cd : G.Adj c d
  ne_ac : a ≠ c
  ne_ad : a ≠ d
  ne_bd : b ≠ d
  mnbr_a : ∀ w : V, G.Adj a w → G.degree w = 3 → w = b
  mnbr_b : ∀ w : V, G.Adj b w → G.degree w = 3 → w = a ∨ w = c
  mnbr_c : ∀ w : V, G.Adj c w → G.degree w = 3 → w = b ∨ w = d
  mnbr_d : ∀ w : V, G.Adj d w → G.degree w = 3 → w = c
  iso_rest : ∀ v : V, G.degree v = 3 → v ≠ a → v ≠ b → v ≠ c → v ≠ d →
    v ∈ isoTwins G

namespace MShapeP4

variable {G : SimpleGraph V} {a b c d : V}

open Classical in
theorem nadj_ac (hs : MShapeP4 G a b c d) : ¬G.Adj a c := fun h =>
  (G.ne_of_adj hs.adj_bc).symm (hs.mnbr_a c h hs.deg_c)

open Classical in
theorem nadj_bd (hs : MShapeP4 G a b c d) : ¬G.Adj b d := fun h => by
  rcases hs.mnbr_b d h hs.deg_d with e | e
  · exact hs.ne_ad e.symm
  · exact G.ne_of_adj hs.adj_cd e.symm

open Classical in
/-- The reversed path is the same shape. -/
theorem rev (hs : MShapeP4 G a b c d) : MShapeP4 G d c b a where
  deg_a := hs.deg_d
  deg_b := hs.deg_c
  deg_c := hs.deg_b
  deg_d := hs.deg_a
  adj_ab := hs.adj_cd.symm
  adj_bc := hs.adj_bc.symm
  adj_cd := hs.adj_ab.symm
  ne_ac := hs.ne_bd.symm
  ne_ad := hs.ne_ad.symm
  ne_bd := hs.ne_ac.symm
  mnbr_a := hs.mnbr_d
  mnbr_b := fun w hw h3 => (hs.mnbr_c w hw h3).symm
  mnbr_c := fun w hw h3 => (hs.mnbr_b w hw h3).symm
  mnbr_d := hs.mnbr_a
  iso_rest := fun v h3 h1 h2 h3' h4 => hs.iso_rest v h3 h4 h3' h2 h1

open Classical in
theorem a_not_iso (hs : MShapeP4 G a b c d) : a ∉ isoTwins G :=
  not_iso_of_mnbr G hs.adj_ab hs.deg_b
open Classical in
theorem b_not_iso (hs : MShapeP4 G a b c d) : b ∉ isoTwins G :=
  not_iso_of_mnbr G hs.adj_ab.symm hs.deg_a
open Classical in
theorem c_not_iso (hs : MShapeP4 G a b c d) : c ∉ isoTwins G :=
  not_iso_of_mnbr G hs.adj_bc.symm hs.deg_b
open Classical in
theorem d_not_iso (hs : MShapeP4 G a b c d) : d ∉ isoTwins G :=
  not_iso_of_mnbr G hs.adj_cd.symm hs.deg_c

open Classical in
theorem iso_ge (n : ℕ) (hn : 8 ≤ n) (G' : SimpleGraph (Fin n)) {a b c d : Fin n}
    (hs : MShapeP4 G' a b c d) (hm : G'.edgeFinset.card = 2 * (n - 2))
    (h3 : ∀ v : Fin n, 3 ≤ G'.degree v) : 4 ≤ (isoTwins G').card := by
  have hD8 : 8 ≤ (deg3Set G').card := by
    have h := card_deg3_ge_eight n hn G' hm h3
    unfold deg3Set
    exact h
  have hcov := iso_card_of_cover G' ({a, b, c, d} : Finset (Fin n))
    (fun v h3v h1 => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at h1
      push Not at h1
      exact hs.iso_rest v h3v h1.1 h1.2.1 h1.2.2.1 h1.2.2.2)
  have hle : ({a, b, c, d} : Finset (Fin n)).card ≤ 4 := by
    apply le_trans (Finset.card_insert_le _ _)
    apply Nat.succ_le_succ
    apply le_trans (Finset.card_insert_le _ _)
    apply Nat.succ_le_succ
    exact Finset.card_insert_le _ _
  omega

end MShapeP4

open Classical in
/-- The `claw` shape: `M` is `K_{1,3}` at centre `z₀` with leaves `x₁, x₂, x₃`. -/
structure MShapeClaw (G : SimpleGraph V) (z₀ x₁ x₂ x₃ : V) : Prop where
  deg_z : G.degree z₀ = 3
  deg_1 : G.degree x₁ = 3
  deg_2 : G.degree x₂ = 3
  deg_3 : G.degree x₃ = 3
  adj_1 : G.Adj z₀ x₁
  adj_2 : G.Adj z₀ x₂
  adj_3 : G.Adj z₀ x₃
  ne_12 : x₁ ≠ x₂
  ne_13 : x₁ ≠ x₃
  ne_23 : x₂ ≠ x₃
  mnbr_1 : ∀ w : V, G.Adj x₁ w → G.degree w = 3 → w = z₀
  mnbr_2 : ∀ w : V, G.Adj x₂ w → G.degree w = 3 → w = z₀
  mnbr_3 : ∀ w : V, G.Adj x₃ w → G.degree w = 3 → w = z₀
  iso_rest : ∀ v : V, G.degree v = 3 → v ≠ z₀ → v ≠ x₁ → v ≠ x₂ → v ≠ x₃ →
    v ∈ isoTwins G

open Classical in
/-- The `chair` shape: centre `q` with leaves `l₁, l₂` and the path `q−p−e`. -/
structure MShapeChair (G : SimpleGraph V) (q l₁ l₂ p e : V) : Prop where
  deg_q : G.degree q = 3
  deg_l₁ : G.degree l₁ = 3
  deg_l₂ : G.degree l₂ = 3
  deg_p : G.degree p = 3
  deg_e : G.degree e = 3
  adj_l₁ : G.Adj q l₁
  adj_l₂ : G.Adj q l₂
  adj_p : G.Adj q p
  adj_pe : G.Adj p e
  ne_l₁l₂ : l₁ ≠ l₂
  ne_l₁p : l₁ ≠ p
  ne_l₂p : l₂ ≠ p
  ne_l₁e : l₁ ≠ e
  ne_l₂e : l₂ ≠ e
  ne_qe : q ≠ e
  mnbr_l₁ : ∀ w : V, G.Adj l₁ w → G.degree w = 3 → w = q
  mnbr_l₂ : ∀ w : V, G.Adj l₂ w → G.degree w = 3 → w = q
  mnbr_p : ∀ w : V, G.Adj p w → G.degree w = 3 → w = q ∨ w = e
  mnbr_e : ∀ w : V, G.Adj e w → G.degree w = 3 → w = p
  iso_rest : ∀ v : V, G.degree v = 3 → v ≠ q → v ≠ l₁ → v ≠ l₂ → v ≠ p → v ≠ e →
    v ∈ isoTwins G

open Classical in
/-- The `S22` shape: the double star — adjacent centres `q₁ ~ q₂` with leaves
`l₁, l₂` at `q₁` and `m₁, m₂` at `q₂`. -/
structure MShapeS22 (G : SimpleGraph V) (q₁ q₂ l₁ l₂ m₁ m₂ : V) : Prop where
  deg_q₁ : G.degree q₁ = 3
  deg_q₂ : G.degree q₂ = 3
  deg_l₁ : G.degree l₁ = 3
  deg_l₂ : G.degree l₂ = 3
  deg_m₁ : G.degree m₁ = 3
  deg_m₂ : G.degree m₂ = 3
  adj_qq : G.Adj q₁ q₂
  adj_l₁ : G.Adj q₁ l₁
  adj_l₂ : G.Adj q₁ l₂
  adj_m₁ : G.Adj q₂ m₁
  adj_m₂ : G.Adj q₂ m₂
  ne_l₁l₂ : l₁ ≠ l₂
  ne_m₁m₂ : m₁ ≠ m₂
  ne_q₁m₁ : q₁ ≠ m₁
  ne_q₁m₂ : q₁ ≠ m₂
  ne_q₂l₁ : q₂ ≠ l₁
  ne_q₂l₂ : q₂ ≠ l₂
  ne_l₁m₁ : l₁ ≠ m₁
  ne_l₁m₂ : l₁ ≠ m₂
  ne_l₂m₁ : l₂ ≠ m₁
  ne_l₂m₂ : l₂ ≠ m₂
  mnbr_l₁ : ∀ w : V, G.Adj l₁ w → G.degree w = 3 → w = q₁
  mnbr_l₂ : ∀ w : V, G.Adj l₂ w → G.degree w = 3 → w = q₁
  mnbr_m₁ : ∀ w : V, G.Adj m₁ w → G.degree w = 3 → w = q₂
  mnbr_m₂ : ∀ w : V, G.Adj m₂ w → G.degree w = 3 → w = q₂
  iso_rest : ∀ v : V, G.degree v = 3 → v ≠ q₁ → v ≠ q₂ → v ≠ l₁ → v ≠ l₂ →
    v ≠ m₁ → v ≠ m₂ → v ∈ isoTwins G

open Classical in
/-- The `C5` shape: `M` is the `5`-cycle `v₀−v₁−v₂−v₃−v₄−v₀`. -/
structure MShapeC5 (G : SimpleGraph V) (v₀ v₁ v₂ v₃ v₄ : V) : Prop where
  deg_0 : G.degree v₀ = 3
  deg_1 : G.degree v₁ = 3
  deg_2 : G.degree v₂ = 3
  deg_3 : G.degree v₃ = 3
  deg_4 : G.degree v₄ = 3
  adj_01 : G.Adj v₀ v₁
  adj_12 : G.Adj v₁ v₂
  adj_23 : G.Adj v₂ v₃
  adj_34 : G.Adj v₃ v₄
  adj_40 : G.Adj v₄ v₀
  ne_02 : v₀ ≠ v₂
  ne_03 : v₀ ≠ v₃
  ne_13 : v₁ ≠ v₃
  ne_14 : v₁ ≠ v₄
  ne_24 : v₂ ≠ v₄
  mnbr_0 : ∀ w : V, G.Adj v₀ w → G.degree w = 3 → w = v₁ ∨ w = v₄
  mnbr_1 : ∀ w : V, G.Adj v₁ w → G.degree w = 3 → w = v₀ ∨ w = v₂
  mnbr_2 : ∀ w : V, G.Adj v₂ w → G.degree w = 3 → w = v₁ ∨ w = v₃
  mnbr_3 : ∀ w : V, G.Adj v₃ w → G.degree w = 3 → w = v₂ ∨ w = v₄
  mnbr_4 : ∀ w : V, G.Adj v₄ w → G.degree w = 3 → w = v₃ ∨ w = v₀
  iso_rest : ∀ v : V, G.degree v = 3 → v ≠ v₀ → v ≠ v₁ → v ≠ v₂ → v ≠ v₃ →
    v ≠ v₄ → v ∈ isoTwins G

/-! ## The S22 kill: the double star splits into its two stars

`P = {q₁, l₁, l₂}` vs `N = {q₂, m₁, m₂}`: the only crossing edge is `q₁q₂`,
each centre leaks `≤ 1`, each leaf `≤ 2` — the exact tie `2·1 + 5 + 5 = 12 = 4·3`.
Unconditional: no corner, no sea, no `n`-threshold. -/

open Classical in
private theorem leak_le_of_inter' (G : SimpleGraph V) (p : V) (S : Finset V) (k : ℕ)
    (hk : k ≤ (G.neighborFinset p ∩ S).card) :
    (G.neighborFinset p \ S).card + k ≤ G.degree p := by
  have h := Finset.card_sdiff_add_card_inter (G.neighborFinset p) S
  have hd := G.card_neighborFinset_eq_degree p
  omega

open Classical in
omit [Fintype V] in
private theorem sum_triple' (f : V → ℕ) {a b c : V} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : ∑ p ∈ ({a, b, c} : Finset V), f p = f a + f b + f c := by
  rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_pair hbc]
  ring

open Classical in
omit [Fintype V] in
private theorem card_triple' {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Finset V).card = 3 := by
  rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]

open Classical in
/-- **The S22 split.** -/
theorem s22_split_twoBlock (G : SimpleGraph V) {q₁ q₂ l₁ l₂ m₁ m₂ : V}
    (hs : MShapeS22 G q₁ q₂ l₁ l₂ m₁ m₂) : TwoBlockConfig G := by
  have ne_q₁l₁ : q₁ ≠ l₁ := G.ne_of_adj hs.adj_l₁
  have ne_q₁l₂ : q₁ ≠ l₂ := G.ne_of_adj hs.adj_l₂
  have ne_q₂m₁ : q₂ ≠ m₁ := G.ne_of_adj hs.adj_m₁
  have ne_q₂m₂ : q₂ ≠ m₂ := G.ne_of_adj hs.adj_m₂
  have ne_qq : q₁ ≠ q₂ := G.ne_of_adj hs.adj_qq
  -- cross non-adjacencies from the mnbr pins
  have nadj_l₁q₂ : ¬G.Adj l₁ q₂ := fun h =>
    ne_qq (hs.mnbr_l₁ q₂ h hs.deg_q₂).symm
  have nadj_l₂q₂ : ¬G.Adj l₂ q₂ := fun h =>
    ne_qq (hs.mnbr_l₂ q₂ h hs.deg_q₂).symm
  have nadj_l₁m₁ : ¬G.Adj l₁ m₁ := fun h => by
    have := hs.mnbr_l₁ m₁ h hs.deg_m₁
    exact hs.ne_q₁m₁ this.symm
  have nadj_l₁m₂ : ¬G.Adj l₁ m₂ := fun h => by
    have := hs.mnbr_l₁ m₂ h hs.deg_m₂
    exact hs.ne_q₁m₂ this.symm
  have nadj_l₂m₁ : ¬G.Adj l₂ m₁ := fun h => by
    have := hs.mnbr_l₂ m₁ h hs.deg_m₁
    exact hs.ne_q₁m₁ this.symm
  have nadj_l₂m₂ : ¬G.Adj l₂ m₂ := fun h => by
    have := hs.mnbr_l₂ m₂ h hs.deg_m₂
    exact hs.ne_q₁m₂ this.symm
  have nadj_q₁m₁ : ¬G.Adj q₁ m₁ := fun h => by
    have := hs.mnbr_m₁ q₁ h.symm hs.deg_q₁
    exact ne_qq this
  have nadj_q₁m₂ : ¬G.Adj q₁ m₂ := fun h => by
    have := hs.mnbr_m₂ q₁ h.symm hs.deg_q₁
    exact ne_qq this
  set P : Finset V := {q₁, l₁, l₂} with hP
  set N : Finset V := {q₂, m₁, m₂} with hN
  have hPcard : P.card = 3 := card_triple' ne_q₁l₁ ne_q₁l₂ hs.ne_l₁l₂
  have hNcard : N.card = 3 := card_triple' ne_q₂m₁ ne_q₂m₂ hs.ne_m₁m₂
  have hdisj : Disjoint P N := by
    rw [Finset.disjoint_left]
    intro w hw hw'
    rw [hP, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hw
    rw [hN, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hw'
    rcases hw with rfl | rfl | rfl <;> rcases hw' with rfl | rfl | rfl
    · exact ne_qq rfl
    · exact hs.ne_q₁m₁ rfl
    · exact hs.ne_q₁m₂ rfl
    · exact hs.ne_q₂l₁ rfl.symm
    · exact hs.ne_l₁m₁ rfl
    · exact hs.ne_l₁m₂ rfl
    · exact hs.ne_q₂l₂ rfl.symm
    · exact hs.ne_l₂m₁ rfl
    · exact hs.ne_l₂m₂ rfl
  -- crossing count: only `q₁ ~ q₂`
  have hcr_q₁ : (G.neighborFinset q₁ ∩ N).card ≤ 1 := by
    have hsub : G.neighborFinset q₁ ∩ N ⊆ {q₂} := by
      intro w hw
      rw [Finset.mem_inter, G.mem_neighborFinset] at hw
      obtain ⟨hadj, hwN⟩ := hw
      rw [hN, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hwN
      rcases hwN with rfl | rfl | rfl
      · exact Finset.mem_singleton_self _
      · exact absurd hadj nadj_q₁m₁
      · exact absurd hadj nadj_q₁m₂
    calc (G.neighborFinset q₁ ∩ N).card ≤ ({q₂} : Finset V).card :=
        Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton _
  have hcr_l₁ : (G.neighborFinset l₁ ∩ N).card = 0 :=
    nbr_inter_triple_zero G l₁ q₂ m₁ m₂ nadj_l₁q₂ nadj_l₁m₁ nadj_l₁m₂
  have hcr_l₂ : (G.neighborFinset l₂ ∩ N).card = 0 :=
    nbr_inter_triple_zero G l₂ q₂ m₁ m₂ nadj_l₂q₂ nadj_l₂m₁ nadj_l₂m₂
  -- leaks
  have hlk_q₁ : (G.neighborFinset q₁ \ P).card + 2 ≤ G.degree q₁ := by
    refine leak_le_of_inter' G q₁ P 2 ?_
    have hsub : ({l₁, l₂} : Finset V) ⊆ G.neighborFinset q₁ ∩ P := by
      intro w hw
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [Finset.mem_inter, G.mem_neighborFinset]
      rcases hw with rfl | rfl
      · exact ⟨hs.adj_l₁, by rw [hP]; simp⟩
      · exact ⟨hs.adj_l₂, by rw [hP]; simp⟩
    calc 2 = ({l₁, l₂} : Finset V).card := (Finset.card_pair hs.ne_l₁l₂).symm
      _ ≤ _ := Finset.card_le_card hsub
  have hlk_leaf : ∀ w : V, G.Adj q₁ w → G.degree w = 3 →
      (G.neighborFinset w \ P).card + 1 ≤ G.degree w := by
    intro w hadj _
    refine leak_le_of_inter' G w P 1 ?_
    refine Finset.card_pos.mpr ⟨q₁, ?_⟩
    rw [Finset.mem_inter, G.mem_neighborFinset]
    exact ⟨hadj.symm, by rw [hP]; simp⟩
  have hlk_l₁ := hlk_leaf l₁ hs.adj_l₁ hs.deg_l₁
  have hlk_l₂ := hlk_leaf l₂ hs.adj_l₂ hs.deg_l₂
  have hlk_q₂ : (G.neighborFinset q₂ \ N).card + 2 ≤ G.degree q₂ := by
    refine leak_le_of_inter' G q₂ N 2 ?_
    have hsub : ({m₁, m₂} : Finset V) ⊆ G.neighborFinset q₂ ∩ N := by
      intro w hw
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [Finset.mem_inter, G.mem_neighborFinset]
      rcases hw with rfl | rfl
      · exact ⟨hs.adj_m₁, by rw [hN]; simp⟩
      · exact ⟨hs.adj_m₂, by rw [hN]; simp⟩
    calc 2 = ({m₁, m₂} : Finset V).card := (Finset.card_pair hs.ne_m₁m₂).symm
      _ ≤ _ := Finset.card_le_card hsub
  have hlk_mleaf : ∀ w : V, G.Adj q₂ w → G.degree w = 3 →
      (G.neighborFinset w \ N).card + 1 ≤ G.degree w := by
    intro w hadj _
    refine leak_le_of_inter' G w N 1 ?_
    refine Finset.card_pos.mpr ⟨q₂, ?_⟩
    rw [Finset.mem_inter, G.mem_neighborFinset]
    exact ⟨hadj.symm, by rw [hN]; simp⟩
  have hlk_m₁ := hlk_mleaf m₁ hs.adj_m₁ hs.deg_m₁
  have hlk_m₂ := hlk_mleaf m₂ hs.adj_m₂ hs.deg_m₂
  refine ⟨P, N, hdisj, by rw [hPcard, hNcard], by rw [hPcard]; norm_num, ?_⟩
  rw [hP, hN] at *
  rw [sum_triple' _ ne_q₁l₁ ne_q₁l₂ hs.ne_l₁l₂,
    sum_triple' _ ne_q₁l₁ ne_q₁l₂ hs.ne_l₁l₂,
    sum_triple' _ ne_q₂m₁ ne_q₂m₂ hs.ne_m₁m₂]
  rw [hPcard]
  have hd₁ := hs.deg_q₁
  have hd₂ := hs.deg_q₂
  have hd₃ := hs.deg_l₁
  have hd₄ := hs.deg_l₂
  have hd₅ := hs.deg_m₁
  have hd₆ := hs.deg_m₂
  omega

/-! ## The claw / chair / C5 kills: any rich hub TwoTwin-fires

By F1/F5 the `M`-neighbourhood of a degree-`4` hub is a pairwise-`M`-distance-`≥ 3`
set — and in these three shapes every such set misses one of the shape's cherries,
so a rich hub avoids a full cherry and `two_twin_cherry_twoBlock` fires.  The
corner pigeonhole (`corner_rich_one`) supplies the rich hub. -/

open Classical in
/-- **The claw rich-hub kill** (unconditional in the rich hub). -/
theorem claw_rich_kill (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Fin n))
    (hT : ¬HasGoodTriangle n G) (hC4 : ¬HasGoodC4 n G) {z₀ x₁ x₂ x₃ : Fin n}
    (hs : MShapeClaw G z₀ x₁ x₂ x₃) {g : Fin n}
    (hdg : G.degree g = 4) (hgr : 2 ≤ (isoNbrs G g).card) : TwoBlockConfig G := by
  -- no hub touches the centre
  have hgz : ¬G.Adj g z₀ := by
    intro hadj
    have h1 := hs.deg_1
    have h2 := hs.deg_2
    have h3 := hs.deg_3
    rcases deg3_nbr_pin G hs.deg_z hs.adj_1 hs.adj_2 hs.adj_3 hs.ne_12 hs.ne_13
      hs.ne_23 hadj.symm with e | e | e <;> rw [e] at hdg <;> omega
  -- leaves are pairwise non-adjacent (deg-3 triangle through the centre)
  have hnadj : ∀ {u v : Fin n}, G.degree u = 3 → G.degree v = 3 → G.Adj z₀ u →
      G.Adj z₀ v → u ≠ v → ¬G.Adj u v := by
    intro u v hu hv hzu hzv huv hadj
    exact deg3_triangle_false n (by omega) G hT hs.deg_z hu hv hzu hadj hzv
  have hch₁₂ : Cherry G x₁ z₀ x₂ :=
    ⟨hs.deg_1, hs.deg_z, hs.deg_2, hs.adj_1, hs.adj_2, hs.ne_12,
      hnadj hs.deg_1 hs.deg_2 hs.adj_1 hs.adj_2 hs.ne_12⟩
  have hch₂₃ : Cherry G x₂ z₀ x₃ :=
    ⟨hs.deg_2, hs.deg_z, hs.deg_3, hs.adj_2, hs.adj_3, hs.ne_23,
      hnadj hs.deg_2 hs.deg_3 hs.adj_2 hs.adj_3 hs.ne_23⟩
  have hch₁₃ : Cherry G x₁ z₀ x₃ :=
    ⟨hs.deg_1, hs.deg_z, hs.deg_3, hs.adj_1, hs.adj_3, hs.ne_13,
      hnadj hs.deg_1 hs.deg_3 hs.adj_1 hs.adj_3 hs.ne_13⟩
  -- F5: g touches at most one leaf
  have hF5 : ∀ {u v : Fin n}, G.degree u = 3 → G.degree v = 3 → G.Adj z₀ u →
      G.Adj z₀ v → u ≠ v → G.Adj g u → ¬G.Adj g v := by
    intro u v hu hv hzu hzv huv hgu hgv
    exact hub_no_dist2_pair n (by omega) G hT hC4 hdg hs.deg_z hu hv huv hzu hzv
      hgu hgv
  by_cases h1 : G.Adj g x₁
  · exact rich_avoiding_twoBlock G hch₂₃ hdg hgr hgz
      (hF5 hs.deg_1 hs.deg_2 hs.adj_1 hs.adj_2 hs.ne_12 h1)
      (hF5 hs.deg_1 hs.deg_3 hs.adj_1 hs.adj_3 hs.ne_13 h1)
  by_cases h2 : G.Adj g x₂
  · exact rich_avoiding_twoBlock G hch₁₃ hdg hgr hgz h1
      (hF5 hs.deg_2 hs.deg_3 hs.adj_2 hs.adj_3 hs.ne_23 h2)
  · exact rich_avoiding_twoBlock G hch₁₂ hdg hgr hgz h1 h2

open Classical in
/-- **The chair rich-hub kill**. -/
theorem chair_rich_kill (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Fin n))
    (hT : ¬HasGoodTriangle n G) (hC4 : ¬HasGoodC4 n G) {q l₁ l₂ p e : Fin n}
    (hs : MShapeChair G q l₁ l₂ p e) {g : Fin n}
    (hdg : G.degree g = 4) (hgr : 2 ≤ (isoNbrs G g).card) : TwoBlockConfig G := by
  have hgq : ¬G.Adj g q := by
    intro hadj
    have h1 := hs.deg_l₁
    have h2 := hs.deg_l₂
    have h3 := hs.deg_p
    rcases deg3_nbr_pin G hs.deg_q hs.adj_l₁ hs.adj_l₂ hs.adj_p hs.ne_l₁l₂
      hs.ne_l₁p hs.ne_l₂p hadj.symm with e | e | e <;> rw [e] at hdg <;> omega
  have hnadj : ∀ {u v : Fin n}, G.degree u = 3 → G.degree v = 3 → G.Adj q u →
      G.Adj q v → u ≠ v → ¬G.Adj u v := by
    intro u v hu hv hzu hzv huv hadj
    exact deg3_triangle_false n (by omega) G hT hs.deg_q hu hv hzu hadj hzv
  have hF5 : ∀ {u v : Fin n}, G.degree u = 3 → G.degree v = 3 → G.Adj q u →
      G.Adj q v → u ≠ v → G.Adj g u → ¬G.Adj g v := by
    intro u v hu hv hzu hzv huv hgu hgv
    exact hub_no_dist2_pair n (by omega) G hT hC4 hdg hs.deg_q hu hv huv hzu hzv
      hgu hgv
  have hch_ll : Cherry G l₁ q l₂ :=
    ⟨hs.deg_l₁, hs.deg_q, hs.deg_l₂, hs.adj_l₁, hs.adj_l₂, hs.ne_l₁l₂,
      hnadj hs.deg_l₁ hs.deg_l₂ hs.adj_l₁ hs.adj_l₂ hs.ne_l₁l₂⟩
  have hch_l₂p : Cherry G l₂ q p :=
    ⟨hs.deg_l₂, hs.deg_q, hs.deg_p, hs.adj_l₂, hs.adj_p, hs.ne_l₂p,
      hnadj hs.deg_l₂ hs.deg_p hs.adj_l₂ hs.adj_p hs.ne_l₂p⟩
  have hch_l₁p : Cherry G l₁ q p :=
    ⟨hs.deg_l₁, hs.deg_q, hs.deg_p, hs.adj_l₁, hs.adj_p, hs.ne_l₁p,
      hnadj hs.deg_l₁ hs.deg_p hs.adj_l₁ hs.adj_p hs.ne_l₁p⟩
  by_cases hp : G.Adj g p
  · exact rich_avoiding_twoBlock G hch_ll hdg hgr hgq
      (hF5 hs.deg_p hs.deg_l₁ hs.adj_p hs.adj_l₁ (Ne.symm hs.ne_l₁p) hp)
      (hF5 hs.deg_p hs.deg_l₂ hs.adj_p hs.adj_l₂ (Ne.symm hs.ne_l₂p) hp)
  by_cases h1 : G.Adj g l₁
  · exact rich_avoiding_twoBlock G hch_l₂p hdg hgr hgq
      (hF5 hs.deg_l₁ hs.deg_l₂ hs.adj_l₁ hs.adj_l₂ hs.ne_l₁l₂ h1) hp
  by_cases h2 : G.Adj g l₂
  · exact rich_avoiding_twoBlock G hch_l₁p hdg hgr hgq h1 hp
  · exact rich_avoiding_twoBlock G hch_ll hdg hgr hgq h1 h2

open Classical in
/-- **The C5 rich-hub kill**. -/
theorem c5_rich_kill (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Fin n))
    (hT : ¬HasGoodTriangle n G) (hC4 : ¬HasGoodC4 n G) {v₀ v₁ v₂ v₃ v₄ : Fin n}
    (hs : MShapeC5 G v₀ v₁ v₂ v₃ v₄) {g : Fin n}
    (hdg : G.degree g = 4) (hgr : 2 ≤ (isoNbrs G g).card) : TwoBlockConfig G := by
  -- cherries of the cycle
  have hnadj_arc : ∀ {u v w : Fin n}, G.degree u = 3 → G.degree v = 3 →
      G.degree w = 3 → G.Adj v u → G.Adj v w → u ≠ w → ¬G.Adj u w := by
    intro u v w hu hv hw hvu hvw huw hadj
    exact deg3_triangle_false n (by omega) G hT hv hu hw hvu hadj hvw
  have hF1 : ∀ {u v : Fin n}, G.degree u = 3 → G.degree v = 3 → G.Adj u v →
      G.Adj g u → ¬G.Adj g v := by
    intro u v hu hv huv hgu hgv
    exact hub_mnbrs_not_adj n (by omega) G hT (le_of_eq hdg) hu hv huv hgu hgv
  have hF5 : ∀ {u v w : Fin n}, G.degree u = 3 → G.degree v = 3 →
      G.degree w = 3 → G.Adj v u → G.Adj v w → u ≠ w → G.Adj g u → ¬G.Adj g w := by
    intro u v w hu hv hw hvu hvw huw hgu hgw
    exact hub_no_dist2_pair n (by omega) G hT hC4 hdg hv hu hw huw hvu hvw hgu hgw
  have hch012 : Cherry G v₀ v₁ v₂ :=
    ⟨hs.deg_0, hs.deg_1, hs.deg_2, hs.adj_01.symm, hs.adj_12, hs.ne_02,
      hnadj_arc hs.deg_0 hs.deg_1 hs.deg_2 hs.adj_01.symm hs.adj_12 hs.ne_02⟩
  have hch123 : Cherry G v₁ v₂ v₃ :=
    ⟨hs.deg_1, hs.deg_2, hs.deg_3, hs.adj_12.symm, hs.adj_23, hs.ne_13,
      hnadj_arc hs.deg_1 hs.deg_2 hs.deg_3 hs.adj_12.symm hs.adj_23 hs.ne_13⟩
  have hch234 : Cherry G v₂ v₃ v₄ :=
    ⟨hs.deg_2, hs.deg_3, hs.deg_4, hs.adj_23.symm, hs.adj_34, hs.ne_24,
      hnadj_arc hs.deg_2 hs.deg_3 hs.deg_4 hs.adj_23.symm hs.adj_34 hs.ne_24⟩
  have hch340 : Cherry G v₃ v₄ v₀ :=
    ⟨hs.deg_3, hs.deg_4, hs.deg_0, hs.adj_34.symm, hs.adj_40, hs.ne_03.symm,
      hnadj_arc hs.deg_3 hs.deg_4 hs.deg_0 hs.adj_34.symm hs.adj_40 hs.ne_03.symm⟩
  have hch401 : Cherry G v₄ v₀ v₁ :=
    ⟨hs.deg_4, hs.deg_0, hs.deg_1, hs.adj_40.symm, hs.adj_01, hs.ne_14.symm,
      hnadj_arc hs.deg_4 hs.deg_0 hs.deg_1 hs.adj_40.symm hs.adj_01 hs.ne_14.symm⟩
  by_cases h0 : G.Adj g v₀
  · -- M-nbhd = {v₀}: avoid (v₁,v₂,v₃)
    exact rich_avoiding_twoBlock G hch123 hdg hgr
      (hF5 hs.deg_0 hs.deg_1 hs.deg_2 hs.adj_01.symm hs.adj_12 hs.ne_02 h0)
      (hF1 hs.deg_0 hs.deg_1 hs.adj_01 h0)
      (hF5 hs.deg_0 hs.deg_4 hs.deg_3 hs.adj_40 hs.adj_34.symm hs.ne_03 h0)
  by_cases h1 : G.Adj g v₁
  · -- avoid (v₂,v₃,v₄)
    exact rich_avoiding_twoBlock G hch234 hdg hgr
      (hF5 hs.deg_1 hs.deg_2 hs.deg_3 hs.adj_12.symm hs.adj_23 hs.ne_13 h1)
      (hF1 hs.deg_1 hs.deg_2 hs.adj_12 h1)
      (hF5 hs.deg_1 hs.deg_0 hs.deg_4 hs.adj_01 hs.adj_40.symm hs.ne_14 h1)
  by_cases h2 : G.Adj g v₂
  · -- avoid (v₃,v₄,v₀): v₃ by F1, v₄ by F5 (via v₃), v₀ by branch
    exact rich_avoiding_twoBlock G hch340 hdg hgr
      (hF5 hs.deg_2 hs.deg_3 hs.deg_4 hs.adj_23.symm hs.adj_34 hs.ne_24 h2)
      (hF1 hs.deg_2 hs.deg_3 hs.adj_23 h2) h0
  by_cases h3 : G.Adj g v₃
  · -- avoid (v₄,v₀,v₁): v₄ by F1, v₀/v₁ by branches
    exact rich_avoiding_twoBlock G hch401 hdg hgr h0
      (hF1 hs.deg_3 hs.deg_4 hs.adj_34 h3) h1
  · -- avoid (v₀,v₁,v₂) by branches
    exact rich_avoiding_twoBlock G hch012 hdg hgr h1 h0 h2

/-! ## The P4 kill

The only shape with genuine corner escapers.  Roles for a rich hub `g`
(by F1/F5): `B` (`~b` only), `C` (`~c` only), `A` (`~a ∧ ~d`); anything else
avoids the cherry `(a,b,c)` or `(b,c,d)` and is TT-killed.  The corner
pigeonhole gives two rich cherry-touching hubs, double roles are impossible,
and each role pair fires an explicit cut. -/

open Classical in
/-- **The P4 role trichotomy** for a rich degree-`4` hub. -/
theorem p4_rich_role (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Fin n))
    (hT : ¬HasGoodTriangle n G) (hC4 : ¬HasGoodC4 n G) {a b c d : Fin n}
    (hs : MShapeP4 G a b c d) {g : Fin n}
    (hdg : G.degree g = 4) (hgr : 2 ≤ (isoNbrs G g).card) :
    TwoBlockConfig G ∨
      (G.Adj g b ∧ ¬G.Adj g a ∧ ¬G.Adj g c ∧ ¬G.Adj g d) ∨
      (G.Adj g c ∧ ¬G.Adj g a ∧ ¬G.Adj g b ∧ ¬G.Adj g d) ∨
      (G.Adj g a ∧ G.Adj g d ∧ ¬G.Adj g b ∧ ¬G.Adj g c) := by
  have hF1 : ∀ {u v : Fin n}, G.degree u = 3 → G.degree v = 3 → G.Adj u v →
      G.Adj g u → ¬G.Adj g v := fun hu hv huv hgu hgv =>
    hub_mnbrs_not_adj n (by omega) G hT (le_of_eq hdg) hu hv huv hgu hgv
  have hF5 : ∀ {u v w : Fin n}, G.degree u = 3 → G.degree v = 3 → G.degree w = 3 →
      G.Adj v u → G.Adj v w → u ≠ w → G.Adj g u → ¬G.Adj g w :=
    fun hu hv hw hvu hvw huw hgu hgw =>
    hub_no_dist2_pair n (by omega) G hT hC4 hdg hv hu hw huw hvu hvw hgu hgw
  by_cases hb : G.Adj g b
  · exact Or.inr (Or.inl ⟨hb,
      hF1 hs.deg_b hs.deg_a hs.adj_ab.symm hb,
      hF1 hs.deg_b hs.deg_c hs.adj_bc hb,
      hF5 hs.deg_b hs.deg_c hs.deg_d hs.adj_bc.symm hs.adj_cd hs.ne_bd hb⟩)
  by_cases hc : G.Adj g c
  · exact Or.inr (Or.inr (Or.inl ⟨hc,
      hF5 hs.deg_c hs.deg_b hs.deg_a hs.adj_bc hs.adj_ab.symm hs.ne_ac.symm hc,
      hb, hF1 hs.deg_c hs.deg_d hs.adj_cd hc⟩))
  by_cases ha : G.Adj g a
  · by_cases hd : G.Adj g d
    · exact Or.inr (Or.inr (Or.inr ⟨ha, hd, hb, hc⟩))
    · left
      have hch : Cherry G b c d := ⟨hs.deg_b, hs.deg_c, hs.deg_d, hs.adj_bc.symm,
        hs.adj_cd, hs.ne_bd, hs.nadj_bd⟩
      exact rich_avoiding_twoBlock G hch hdg hgr hc hb hd
  · left
    have hch : Cherry G a b c := ⟨hs.deg_a, hs.deg_b, hs.deg_c, hs.adj_ab.symm,
      hs.adj_bc, hs.ne_ac, hs.nadj_ac⟩
    exact rich_avoiding_twoBlock G hch hdg hgr hb ha hc

open Classical in
/-- **The (B,A) pair cut**: `P = {α, d, k}` vs `N = {β, b, i}` — the opposite-twin
two-hub cut with the `M`-vertices `d` and `b` as twins. -/
theorem p4_pair_BA (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Fin n))
    (hT : ¬HasGoodTriangle n G) (hC4 : ¬HasGoodC4 n G) {a b c d : Fin n}
    (hs : MShapeP4 G a b c d) {β α : Fin n}
    (hβ4 : G.degree β = 4) (hβr : 2 ≤ (isoNbrs G β).card)
    (hβb : G.Adj β b) (hβa : ¬G.Adj β a) (_ : ¬G.Adj β c) (hβd : ¬G.Adj β d)
    (hα4 : G.degree α = 4) (hαr : 2 ≤ (isoNbrs G α).card)
    (hαa : G.Adj α a) (hαd : G.Adj α d) (hαb : ¬G.Adj α b) (_ : ¬G.Adj α c) :
    TwoBlockConfig G := by
  obtain ⟨k₁, hk₁, k₂, hk₂, hk12⟩ := Finset.one_lt_card.mp hαr
  obtain ⟨hαk₁, hIk₁⟩ := mem_isoNbrs.mp hk₁
  obtain ⟨hαk₂, hIk₂⟩ := mem_isoNbrs.mp hk₂
  have hane : α ≠ β := fun e => hβa (e ▸ hαa)
  have hd3k₁ := (mem_isoTwins.mp hIk₁).1
  have hd3k₂ := (mem_isoTwins.mp hIk₂).1
  have hak₁ : a ≠ k₁ := fun e => hs.a_not_iso (by rw [e]; exact hIk₁)
  have hak₂ : a ≠ k₂ := fun e => hs.a_not_iso (by rw [e]; exact hIk₂)
  have hdk₁ : d ≠ k₁ := fun e => hs.d_not_iso (by rw [e]; exact hIk₁)
  have hdk₂ : d ≠ k₂ := fun e => hs.d_not_iso (by rw [e]; exact hIk₂)
  have hpin : ∀ w : Fin n, G.Adj α w → w = a ∨ w = d ∨ w = k₁ ∨ w = k₂ :=
    fun w hw => deg4_nbr_pin G hα4 hαa hαd hαk₁ hαk₂ hs.ne_ad hak₁ hak₂ hdk₁
      hdk₂ hk12 hw
  have hnadj_αβ : ¬G.Adj α β := by
    intro hadj
    have h1 := hs.deg_a
    have h2 := hs.deg_d
    rcases hpin β hadj with e | e | e | e <;> rw [e] at hβ4 <;> omega
  have hkpick : ∃ k, k ∈ isoTwins G ∧ G.Adj α k ∧ ¬G.Adj β k := by
    by_cases h1 : G.Adj β k₁
    · by_cases h2 : G.Adj β k₂
      · exact (hubs_share_two_false n hn G hT hC4 hβ4 hα4 hane.symm hk12
          hd3k₁ hd3k₂ h1 hαk₁ h2 hαk₂).elim
      · exact ⟨k₂, hIk₂, hαk₂, h2⟩
    · exact ⟨k₁, hIk₁, hαk₁, h1⟩
  obtain ⟨k, hIk, hαk, hβk⟩ := hkpick
  obtain ⟨i₁, hi₁, i₂, hi₂, hi12⟩ := Finset.one_lt_card.mp hβr
  obtain ⟨hβi₁, hIi₁⟩ := mem_isoNbrs.mp hi₁
  obtain ⟨hβi₂, hIi₂⟩ := mem_isoNbrs.mp hi₂
  have hipick : ∃ i, i ∈ isoTwins G ∧ G.Adj β i ∧ ¬G.Adj α i := by
    by_cases h1 : G.Adj α i₁
    · by_cases h2 : G.Adj α i₂
      · exact (hubs_share_two_false n hn G hT hC4 hβ4 hα4 hane.symm hi12
          (mem_isoTwins.mp hIi₁).1 (mem_isoTwins.mp hIi₂).1 hβi₁ h1 hβi₂ h2).elim
      · exact ⟨i₂, hIi₂, hβi₂, h2⟩
    · exact ⟨i₁, hIi₁, hβi₁, h1⟩
  obtain ⟨i, hIi, hβi, hαi⟩ := hipick
  have hd3k := (mem_isoTwins.mp hIk).1
  have hd3i := (mem_isoTwins.mp hIi).1
  have hda := hs.deg_a
  have hdb := hs.deg_b
  have hdd := hs.deg_d
  exact two_hub_opposite_twin_twoBlock G α β d k b i (le_of_eq hα4) (le_of_eq hβ4)
    hdd hd3k hdb hd3i hαd.symm hαk.symm hβb.symm hβi.symm
    hnadj_αβ hαb hαi
    (fun h => hβd h.symm) (fun h => hs.nadj_bd h.symm)
    (deg3_not_adj_iso G hdd hIi)
    (fun h => hβk h.symm) (fun h => (mem_isoTwins.mp hIk).2 b h hdb)
    (isoTwins_not_adj G hIk hIi)
    hane
    (fun e => by rw [e] at hα4; omega) (fun e => by rw [e] at hα4; omega)
    (fun e => by rw [e] at hα4; omega) (fun e => by rw [e] at hα4; omega)
    (fun e => by rw [e] at hβ4; omega) (fun e => by rw [e] at hβ4; omega)
    (fun e => by rw [e] at hβ4; omega) (fun e => by rw [e] at hβ4; omega)
    (fun e => hs.d_not_iso (by rw [e]; exact hIk)) hs.ne_bd.symm
    (fun e => hs.d_not_iso (by rw [e]; exact hIi))
    (fun e => hs.b_not_iso (by rw [← e]; exact hIk))
    (fun e => hαi (e ▸ hαk))
    (fun e => hs.b_not_iso (by rw [e]; exact hIi))

open Classical in
/-- **The (C,A) pair cut**: `P = {α, a, k}` vs `N = {γ, c, j}`. -/
theorem p4_pair_CA (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Fin n))
    (hT : ¬HasGoodTriangle n G) (hC4 : ¬HasGoodC4 n G) {a b c d : Fin n}
    (hs : MShapeP4 G a b c d) {γ α : Fin n}
    (hγ4 : G.degree γ = 4) (hγr : 2 ≤ (isoNbrs G γ).card)
    (hγc : G.Adj γ c) (hγa : ¬G.Adj γ a) (hγb : ¬G.Adj γ b) (hγd : ¬G.Adj γ d)
    (hα4 : G.degree α = 4) (hαr : 2 ≤ (isoNbrs G α).card)
    (hαa : G.Adj α a) (hαd : G.Adj α d) (hαb : ¬G.Adj α b) (hαc : ¬G.Adj α c) :
    TwoBlockConfig G := by
  exact p4_pair_BA n hn G hT hC4 hs.rev hγ4 hγr hγc hγd hγb hγa
    hα4 hαr hαd hαa hαc hαb

open Classical in
/-- A rich `a`-hub is TT-killed or is an `α*` (role `A`). -/
theorem p4_rich_ahub (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Fin n))
    (hT : ¬HasGoodTriangle n G) (hC4 : ¬HasGoodC4 n G) {a b c d : Fin n}
    (hs : MShapeP4 G a b c d) {α : Fin n}
    (hα4 : G.degree α = 4) (hαr : 2 ≤ (isoNbrs G α).card) (hαa : G.Adj α a) :
    TwoBlockConfig G ∨
      (G.Adj α a ∧ G.Adj α d ∧ ¬G.Adj α b ∧ ¬G.Adj α c) := by
  rcases p4_rich_role n hn G hT hC4 hs hα4 hαr with htb | hB | hC | hA
  · exact Or.inl htb
  · exact absurd hαa hB.2.1
  · exact absurd hαa hC.2.1
  · exact Or.inr hA

open Classical in
/-- The two hubs of `a` (endpoint of the path). -/
theorem p4_ahubs (n : ℕ) (G : SimpleGraph (Fin n))
    (hmin : ∀ v : Fin n, 3 ≤ G.degree v) (hsea : ∀ v : Fin n, G.degree v ≤ 4)
    {a b c d : Fin n} (hs : MShapeP4 G a b c d) :
    ∃ α₁ α₂ : Fin n, α₁ ≠ α₂ ∧ G.Adj a α₁ ∧ G.Adj a α₂ ∧
      G.degree α₁ = 4 ∧ G.degree α₂ = 4 ∧
      ∀ w : Fin n, G.Adj a w → 4 ≤ G.degree w → w = α₁ ∨ w = α₂ := by
  have hbmem : b ∈ G.neighborFinset a := (G.mem_neighborFinset a b).mpr hs.adj_ab
  have hec : ((G.neighborFinset a).erase b).card = 2 := by
    rw [Finset.card_erase_of_mem hbmem, G.card_neighborFinset_eq_degree, hs.deg_a]
  obtain ⟨α₁, h1, α₂, h2, hne⟩ := Finset.one_lt_card.mp (by omega : 1 <
    ((G.neighborFinset a).erase b).card)
  have hdeg4 : ∀ w ∈ (G.neighborFinset a).erase b, G.degree w = 4 := by
    intro w hw
    obtain ⟨hwb, hwN⟩ := Finset.mem_erase.mp hw
    have hadj := (G.mem_neighborFinset a w).mp hwN
    have hm := hmin w
    have hse := hsea w
    by_cases h3 : G.degree w = 3
    · exact absurd (hs.mnbr_a w hadj h3) hwb
    · omega
  have hadj₁ := (G.mem_neighborFinset a α₁).mp (Finset.mem_erase.mp h1).2
  have hadj₂ := (G.mem_neighborFinset a α₂).mp (Finset.mem_erase.mp h2).2
  refine ⟨α₁, α₂, hne, hadj₁, hadj₂, hdeg4 α₁ h1, hdeg4 α₂ h2, ?_⟩
  intro w hw hw4
  have hwb : w ≠ b := fun e => by rw [e, hs.deg_b] at hw4; omega
  have hwmem : w ∈ (G.neighborFinset a).erase b :=
    Finset.mem_erase.mpr ⟨hwb, (G.mem_neighborFinset a w).mpr hw⟩
  have hpair : (G.neighborFinset a).erase b = {α₁, α₂} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro u hu
      rw [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact h1
      · exact h2
    · rw [hec, Finset.card_pair hne]
  rw [hpair] at hwmem
  simpa using hwmem

open Classical in
/-- Any degree-`≥ 4` hub of `b` equals the given one (`b` has one hub slot). -/
theorem p4_bpin (G : SimpleGraph V) {a b c d : V} (hs : MShapeP4 G a b c d)
    {β w : V} (hβb : G.Adj β b) (hβ4 : G.degree β = 4)
    (hw : G.Adj w b) (hw4 : 4 ≤ G.degree w) : w = β := by
  have haβ : a ≠ β := fun e => by rw [← e] at hβ4; rw [hs.deg_a] at hβ4; omega
  have hcβ : c ≠ β := fun e => by rw [← e] at hβ4; rw [hs.deg_c] at hβ4; omega
  rcases deg3_nbr_pin G hs.deg_b hs.adj_ab.symm hs.adj_bc hβb.symm hs.ne_ac haβ
    hcβ hw.symm with e | e | e
  · rw [e] at hw4; rw [hs.deg_a] at hw4; omega
  · rw [e] at hw4; rw [hs.deg_c] at hw4; omega
  · exact e

open Classical in
/-- Any degree-`≥ 4` hub of `c` equals the given one. -/
theorem p4_cpin (G : SimpleGraph V) {a b c d : V} (hs : MShapeP4 G a b c d)
    {γ w : V} (hγc : G.Adj γ c) (hγ4 : G.degree γ = 4)
    (hw : G.Adj w c) (hw4 : 4 ≤ G.degree w) : w = γ := by
  have hbγ : b ≠ γ := fun e => by rw [← e] at hγ4; rw [hs.deg_b] at hγ4; omega
  have hdγ : d ≠ γ := fun e => by rw [← e] at hγ4; rw [hs.deg_d] at hγ4; omega
  rcases deg3_nbr_pin G hs.deg_c hs.adj_bc.symm hs.adj_cd hγc.symm hs.ne_bd hbγ
    hdγ hw.symm with e | e | e
  · rw [e] at hw4; rw [hs.deg_b] at hw4; omega
  · rw [e] at hw4; rw [hs.deg_d] at hw4; omega
  · exact e

open Classical in
/-- Unpack two distinct bad-apex neighbours (sea regime: both cherry-touching). -/
theorem badApex_two (G : SimpleGraph V) (hsea : ∀ v : V, G.degree v ≤ 4)
    {x z y t : V} (h2 : 2 ≤ (badApexNbrs G x z y t).card) :
    ∃ w₁ w₂ : V, w₁ ≠ w₂ ∧
      (G.Adj t w₁ ∧ 4 ≤ G.degree w₁ ∧ (G.Adj w₁ z ∨ G.Adj w₁ x ∨ G.Adj w₁ y)) ∧
      (G.Adj t w₂ ∧ 4 ≤ G.degree w₂ ∧ (G.Adj w₂ z ∨ G.Adj w₂ x ∨ G.Adj w₂ y)) := by
  obtain ⟨w₁, h1, w₂, h2', hne⟩ := Finset.one_lt_card.mp h2
  unfold badApexNbrs at h1 h2'
  rw [Finset.mem_filter] at h1 h2'
  obtain ⟨h1N, h1P⟩ := h1
  obtain ⟨h2N, h2P⟩ := h2'
  have hu : ∀ w : V, (5 ≤ G.degree w ∨ w ∈ cherryHubs G x z y) →
      4 ≤ G.degree w ∧ (G.Adj w z ∨ G.Adj w x ∨ G.Adj w y) := by
    intro w hw
    rcases hw with h5 | hct
    · have := hsea w
      omega
    · exact mem_cherryHubs.mp hct
  exact ⟨w₁, w₂, hne, ⟨(G.mem_neighborFinset t w₁).mp h1N, (hu w₁ h1P).1,
    (hu w₁ h1P).2⟩, ⟨(G.mem_neighborFinset t w₂).mp h2N, (hu w₂ h2P).1,
    (hu w₂ h2P).2⟩⟩

omit [Fintype V] in
open Classical in
/-- Two distinct vertices in `{e₀, α₁, α₂}`, both adjacent to `t`: at least one
of the `α`'s is adjacent to `t`. -/
private theorem alpha_of_two (G : SimpleGraph V) {t e₀ α₁ α₂ w₁ w₂ : V}
    (hw12 : w₁ ≠ w₂) (ha1 : G.Adj t w₁) (ha2 : G.Adj t w₂)
    (h1 : w₁ = e₀ ∨ w₁ = α₁ ∨ w₁ = α₂) (h2 : w₂ = e₀ ∨ w₂ = α₁ ∨ w₂ = α₂) :
    G.Adj α₁ t ∨ G.Adj α₂ t := by
  rcases h1 with e | e | e
  · rcases h2 with f | f | f
    · exact absurd (e.trans f.symm) hw12
    · exact Or.inl (f ▸ ha2).symm
    · exact Or.inr (f ▸ ha2).symm
  · exact Or.inl (e ▸ ha1).symm
  · exact Or.inr (e ▸ ha1).symm

open Classical in
/-- The three-pigeon rich-`α` extraction. -/
private theorem alpha_rich_of_three (G : SimpleGraph V) {α₁ α₂ t₁ t₂ t₃ : V}
    (hne12 : t₁ ≠ t₂) (hne13 : t₁ ≠ t₃) (hne23 : t₂ ≠ t₃)
    (hI1 : t₁ ∈ isoTwins G) (hI2 : t₂ ∈ isoTwins G) (hI3 : t₃ ∈ isoTwins G)
    (h1 : G.Adj α₁ t₁ ∨ G.Adj α₂ t₁) (h2 : G.Adj α₁ t₂ ∨ G.Adj α₂ t₂)
    (h3 : G.Adj α₁ t₃ ∨ G.Adj α₂ t₃) :
    2 ≤ (isoNbrs G α₁).card ∨ 2 ≤ (isoNbrs G α₂).card := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hc1, hc2⟩ := hcon
  have hsub : ({t₁, t₂, t₃} : Finset V) ⊆ isoNbrs G α₁ ∪ isoNbrs G α₂ := by
    intro u hu
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl
    · rcases h1 with h | h
      · exact Finset.mem_union_left _ (mem_isoNbrs.mpr ⟨h, hI1⟩)
      · exact Finset.mem_union_right _ (mem_isoNbrs.mpr ⟨h, hI1⟩)
    · rcases h2 with h | h
      · exact Finset.mem_union_left _ (mem_isoNbrs.mpr ⟨h, hI2⟩)
      · exact Finset.mem_union_right _ (mem_isoNbrs.mpr ⟨h, hI2⟩)
    · rcases h3 with h | h
      · exact Finset.mem_union_left _ (mem_isoNbrs.mpr ⟨h, hI3⟩)
      · exact Finset.mem_union_right _ (mem_isoNbrs.mpr ⟨h, hI3⟩)
  have hcard := Finset.card_le_card hsub
  rw [card_triple' hne12 hne13 hne23] at hcard
  have := Finset.card_union_le (isoNbrs G α₁) (isoNbrs G α₂)
  omega

open Classical in
/-- **The (B,C) pair closes** — private pair, or a pinch/adjacency counting
rederivation of a rich `a`-hub feeding `p4_pair_BA`. -/
theorem p4_pair_BC (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Fin n))
    (hT : ¬HasGoodTriangle n G) (hC4 : ¬HasGoodC4 n G)
    (hmin : ∀ v : Fin n, 3 ≤ G.degree v) (hsea : ∀ v : Fin n, G.degree v ≤ 4)
    {a b c d : Fin n} (hs : MShapeP4 G a b c d)
    (hblock : ∀ t ∈ isoTwins G, 2 ≤ (badApexNbrs G a b c t).card)
    (hIso : 4 ≤ (isoTwins G).card) {β γ : Fin n}
    (hβ4 : G.degree β = 4) (hβr : 2 ≤ (isoNbrs G β).card)
    (hβb : G.Adj β b) (hβa : ¬G.Adj β a) (hβc : ¬G.Adj β c) (hβd : ¬G.Adj β d)
    (hγ4 : G.degree γ = 4) (hγr : 2 ≤ (isoNbrs G γ).card)
    (hγc : G.Adj γ c) (_ : ¬G.Adj γ a) (hγb : ¬G.Adj γ b) (_ : ¬G.Adj γ d) :
    TwoBlockConfig G := by
  obtain ⟨α₁, α₂, hα12, haα₁, haα₂, hα₁4, hα₂4, hαpin⟩ := p4_ahubs n G hmin hsea hs
  have hβγ : β ≠ γ := fun e => hγb (e ▸ hβb)
  -- the rich-α finisher
  have finish : ∀ α' : Fin n, G.Adj a α' → G.degree α' = 4 →
      2 ≤ (isoNbrs G α').card → TwoBlockConfig G := by
    intro α' hadj h4 hr
    rcases p4_rich_ahub n hn G hT hC4 hs h4 hr hadj.symm with htb | ⟨_, hd', hb', hc'⟩
    · exact htb
    · exact p4_pair_BA n hn G hT hC4 hs hβ4 hβr hβb hβa hβc hβd h4 hr hadj.symm
        hd' hb' hc'
  -- CT-neighbour identification
  have hctid : ∀ w : Fin n, 4 ≤ G.degree w →
      (G.Adj w b ∨ G.Adj w a ∨ G.Adj w c) → w = β ∨ w = γ ∨ w = α₁ ∨ w = α₂ := by
    intro w hw4 htouch
    rcases htouch with h | h | h
    · exact Or.inl (p4_bpin G hs hβb hβ4 h hw4)
    · rcases hαpin w h.symm hw4 with e | e
      · exact Or.inr (Or.inr (Or.inl e))
      · exact Or.inr (Or.inr (Or.inr e))
    · exact Or.inr (Or.inl (p4_cpin G hs hγc hγ4 h hw4))
  -- iso twins avoiding both a given single hub and one of β/γ hit an α
  have hget : ∀ t : Fin n, t ∈ isoTwins G →
      (¬G.Adj β t ∨ ¬G.Adj γ t) → G.Adj α₁ t ∨ G.Adj α₂ t := by
    intro t htI hex
    obtain ⟨w₁, w₂, hw12, ⟨hta1, hd1, ht1⟩, ⟨hta2, hd2, ht2⟩⟩ :=
      badApex_two G hsea (hblock t htI)
    have hid1 := hctid w₁ hd1 ht1
    have hid2 := hctid w₂ hd2 ht2
    have halpha : G.Adj α₁ t ∨ G.Adj α₂ t := by
      rcases hex with hexβ | hexγ
      · -- β excluded: both CT-nbrs in {γ, α₁, α₂}
        have h1' : w₁ = γ ∨ w₁ = α₁ ∨ w₁ = α₂ := by
          rcases hid1 with e | rest
          · exact absurd (e ▸ hta1) (fun hh => hexβ hh.symm)
          · exact rest
        have h2' : w₂ = γ ∨ w₂ = α₁ ∨ w₂ = α₂ := by
          rcases hid2 with e | rest
          · exact absurd (e ▸ hta2) (fun hh => hexβ hh.symm)
          · exact rest
        exact alpha_of_two G hw12 hta1 hta2 h1' h2'
      · -- γ excluded: both CT-nbrs in {β, α₁, α₂}
        have h1' : w₁ = β ∨ w₁ = α₁ ∨ w₁ = α₂ := by
          rcases hid1 with e | e | rest
          · exact Or.inl e
          · exact absurd (e ▸ hta1) (fun hh => hexγ hh.symm)
          · exact Or.inr rest
        have h2' : w₂ = β ∨ w₂ = α₁ ∨ w₂ = α₂ := by
          rcases hid2 with e | e | rest
          · exact Or.inl e
          · exact absurd (e ▸ hta2) (fun hh => hexγ hh.symm)
          · exact Or.inr rest
        exact alpha_of_two G hw12 hta1 hta2 h1' h2'
    exact halpha
  -- the three-pigeon closer, given three suitable iso twins
  have close3 : ∀ t₁ t₂ t₃ : Fin n, t₁ ≠ t₂ → t₁ ≠ t₃ → t₂ ≠ t₃ →
      t₁ ∈ isoTwins G → t₂ ∈ isoTwins G → t₃ ∈ isoTwins G →
      (G.Adj α₁ t₁ ∨ G.Adj α₂ t₁) → (G.Adj α₁ t₂ ∨ G.Adj α₂ t₂) →
      (G.Adj α₁ t₃ ∨ G.Adj α₂ t₃) → TwoBlockConfig G := by
    intro t₁ t₂ t₃ h12 h13 h23 hI1 hI2 hI3 m1 m2 m3
    rcases alpha_rich_of_three G h12 h13 h23 hI1 hI2 hI3 m1 m2 m3 with hr | hr
    · exact finish α₁ haα₁ hα₁4 hr
    · exact finish α₂ haα₂ hα₂4 hr
  by_cases hadjBC : G.Adj β γ
  · -- adjacent branch: shares impossible; all four iso twins of β/γ hit the α's
    have hnoshare : ∀ t : Fin n, G.degree t = 3 → G.Adj β t → ¬G.Adj γ t := by
      intro t h3 hβt hγt
      exact (shared_twin_hubs_nonadj n hn G hT h3 (le_of_eq hβ4) (le_of_eq hγ4)
        hβt hγt hβγ) hadjBC
    obtain ⟨i₁, hi₁, i₂, hi₂, hi12⟩ := Finset.one_lt_card.mp hβr
    obtain ⟨hβi₁, hIi₁⟩ := mem_isoNbrs.mp hi₁
    obtain ⟨hβi₂, hIi₂⟩ := mem_isoNbrs.mp hi₂
    obtain ⟨j₁, hj₁, -, -, -⟩ := Finset.one_lt_card.mp hγr
    obtain ⟨hγj₁, hIj₁⟩ := mem_isoNbrs.mp hj₁
    have hij₁ : i₁ ≠ j₁ := fun e =>
      hnoshare i₁ (mem_isoTwins.mp hIi₁).1 hβi₁ (e ▸ hγj₁)
    have hij₂ : i₂ ≠ j₁ := fun e =>
      hnoshare i₂ (mem_isoTwins.mp hIi₂).1 hβi₂ (e ▸ hγj₁)
    exact close3 i₁ i₂ j₁ hi12 hij₁ hij₂ hIi₁ hIi₂ hIj₁
      (hget i₁ hIi₁ (Or.inr (hnoshare i₁ (mem_isoTwins.mp hIi₁).1 hβi₁)))
      (hget i₂ hIi₂ (Or.inr (hnoshare i₂ (mem_isoTwins.mp hIi₂).1 hβi₂)))
      (hget j₁ hIj₁ (Or.inl (fun hβj => hnoshare j₁ (mem_isoTwins.mp hIj₁).1
        hβj hγj₁)))
  · -- non-adjacent branch
    have hshare1 := hubs_share_le_one n hn G hT hC4 hβ4 hγ4 hβγ
    by_cases hp2 : 2 ≤ ((isoNbrs G γ) \ G.neighborFinset β).card
    · by_cases hp1 : 2 ≤ ((isoNbrs G β) \ G.neighborFinset γ).card
      · -- private pair
        refine two_hub_private_pair_twoBlock G β γ hβ4 hγ4 hβγ hadjBC ?_ ?_
        · unfold isoNbrs at hp1
          rw [classical_inter_eq] at hp1
          exact hp1
        · unfold isoNbrs at hp2
          rw [classical_inter_eq] at hp2
          exact hp2
      · -- β pinched: T := iso \ isoNbrs β + the private twin of β
        rw [not_le] at hp1
        -- β's iso nbrs meeting γ are shared: ≤ 1
        have hint : ((isoNbrs G β) ∩ G.neighborFinset γ).card ≤ 1 := by
          refine le_trans (Finset.card_le_card ?_) hshare1
          intro u hu
          rw [Finset.mem_inter] at hu
          obtain ⟨huI, huN⟩ := hu
          obtain ⟨hβu, huiso⟩ := mem_isoNbrs.mp huI
          exact sharedTwins_spec.mpr ⟨hβu, (G.mem_neighborFinset γ u).mp huN,
            (mem_isoTwins.mp huiso).1⟩
        have hsplit := Finset.card_sdiff_add_card_inter (isoNbrs G β)
          (G.neighborFinset γ)
        have hβcard : (isoNbrs G β).card = 2 := by omega
        -- the private twin i of β
        have hpriv1 : 1 ≤ ((isoNbrs G β) \ G.neighborFinset γ).card := by omega
        obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 <
          ((isoNbrs G β) \ G.neighborFinset γ).card)
        rw [Finset.mem_sdiff] at hi
        obtain ⟨hiI, hiN⟩ := hi
        obtain ⟨hβi, hIi⟩ := mem_isoNbrs.mp hiI
        have hγi : ¬G.Adj γ i := fun h => hiN ((G.mem_neighborFinset γ i).mpr h)
        -- two iso twins outside isoNbrs β
        have hT2 : 2 ≤ ((isoTwins G) \ (isoNbrs G β)).card := by
          have hle := Finset.le_card_sdiff (isoNbrs G β) (isoTwins G)
          omega
        obtain ⟨t₁, ht₁, t₂, ht₂, ht12⟩ := Finset.one_lt_card.mp (by omega : 1 <
          ((isoTwins G) \ (isoNbrs G β)).card)
        rw [Finset.mem_sdiff] at ht₁ ht₂
        obtain ⟨ht₁I, ht₁N⟩ := ht₁
        obtain ⟨ht₂I, ht₂N⟩ := ht₂
        have hβt₁ : ¬G.Adj β t₁ := fun h => ht₁N (mem_isoNbrs.mpr ⟨h, ht₁I⟩)
        have hβt₂ : ¬G.Adj β t₂ := fun h => ht₂N (mem_isoNbrs.mpr ⟨h, ht₂I⟩)
        have hit₁ : i ≠ t₁ := fun e => ht₁N (e ▸ hiI)
        have hit₂ : i ≠ t₂ := fun e => ht₂N (e ▸ hiI)
        exact close3 i t₁ t₂ hit₁ hit₂ ht12 hIi ht₁I ht₂I
          (hget i hIi (Or.inr hγi))
          (hget t₁ ht₁I (Or.inl hβt₁))
          (hget t₂ ht₂I (Or.inl hβt₂))
    · -- γ pinched (symmetric)
      rw [not_le] at hp2
      have hint : ((isoNbrs G γ) ∩ G.neighborFinset β).card ≤ 1 := by
        refine le_trans (Finset.card_le_card ?_) hshare1
        intro u hu
        rw [Finset.mem_inter] at hu
        obtain ⟨huI, huN⟩ := hu
        obtain ⟨hγu, huiso⟩ := mem_isoNbrs.mp huI
        exact sharedTwins_spec.mpr ⟨(G.mem_neighborFinset β u).mp huN, hγu,
          (mem_isoTwins.mp huiso).1⟩
      have hsplit := Finset.card_sdiff_add_card_inter (isoNbrs G γ)
        (G.neighborFinset β)
      have hγcard : (isoNbrs G γ).card = 2 := by omega
      obtain ⟨j, hj⟩ := Finset.card_pos.mp (by omega : 0 <
        ((isoNbrs G γ) \ G.neighborFinset β).card)
      rw [Finset.mem_sdiff] at hj
      obtain ⟨hjI, hjN⟩ := hj
      obtain ⟨hγj, hIj⟩ := mem_isoNbrs.mp hjI
      have hβj : ¬G.Adj β j := fun h => hjN ((G.mem_neighborFinset β j).mpr h)
      have hT2 : 2 ≤ ((isoTwins G) \ (isoNbrs G γ)).card := by
        have hle := Finset.le_card_sdiff (isoNbrs G γ) (isoTwins G)
        omega
      obtain ⟨t₁, ht₁, t₂, ht₂, ht12⟩ := Finset.one_lt_card.mp (by omega : 1 <
        ((isoTwins G) \ (isoNbrs G γ)).card)
      rw [Finset.mem_sdiff] at ht₁ ht₂
      obtain ⟨ht₁I, ht₁N⟩ := ht₁
      obtain ⟨ht₂I, ht₂N⟩ := ht₂
      have hγt₁ : ¬G.Adj γ t₁ := fun h => ht₁N (mem_isoNbrs.mpr ⟨h, ht₁I⟩)
      have hγt₂ : ¬G.Adj γ t₂ := fun h => ht₂N (mem_isoNbrs.mpr ⟨h, ht₂I⟩)
      have hjt₁ : j ≠ t₁ := fun e => ht₁N (e ▸ hjI)
      have hjt₂ : j ≠ t₂ := fun e => ht₂N (e ▸ hjI)
      exact close3 j t₁ t₂ hjt₁ hjt₂ ht12 hIj ht₁I ht₂I
        (hget j hIj (Or.inl hβj))
        (hget t₁ ht₁I (Or.inr hγt₁))
        (hget t₂ ht₂I (Or.inr hγt₂))

open Classical in
/-- **The P4 main tree** (cherry normalized to `(a, b, c)`). -/
theorem p4_close_main (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Fin n))
    (hT : ¬HasGoodTriangle n G) (hC4 : ¬HasGoodC4 n G)
    (hmin : ∀ v : Fin n, 3 ≤ G.degree v) (hsea : ∀ v : Fin n, G.degree v ≤ 4)
    {a b c d : Fin n} (hs : MShapeP4 G a b c d)
    (hIso : 4 ≤ (isoTwins G).card)
    (hblock : ∀ t ∈ isoTwins G, 2 ≤ (badApexNbrs G a b c t).card) :
    TwoBlockConfig G := by
  have hch : Cherry G a b c := ⟨hs.deg_a, hs.deg_b, hs.deg_c, hs.adj_ab.symm,
    hs.adj_bc, hs.ne_ac, hs.nadj_ac⟩
  obtain ⟨g, h', hne, ⟨hg4, hgr, -⟩, ⟨hh4, hhr, -⟩⟩ :=
    corner_rich_two G hsea hch hblock hIso
  rcases p4_rich_role n hn G hT hC4 hs hg4 hgr with htb | hgB | hgC | hgA
  · exact htb
  · rcases p4_rich_role n hn G hT hC4 hs hh4 hhr with htb | hhB | hhC | hhA
    · exact htb
    · exact absurd (p4_bpin G hs hgB.1 hg4 hhB.1 (by omega)) (Ne.symm hne)
    · exact p4_pair_BC n hn G hT hC4 hmin hsea hs hblock hIso hg4 hgr hgB.1
        hgB.2.1 hgB.2.2.1 hgB.2.2.2 hh4 hhr hhC.1 hhC.2.1 hhC.2.2.1 hhC.2.2.2
    · exact p4_pair_BA n hn G hT hC4 hs hg4 hgr hgB.1 hgB.2.1 hgB.2.2.1
        hgB.2.2.2 hh4 hhr hhA.1 hhA.2.1 hhA.2.2.1 hhA.2.2.2
  · rcases p4_rich_role n hn G hT hC4 hs hh4 hhr with htb | hhB | hhC | hhA
    · exact htb
    · exact p4_pair_BC n hn G hT hC4 hmin hsea hs hblock hIso hh4 hhr hhB.1
        hhB.2.1 hhB.2.2.1 hhB.2.2.2 hg4 hgr hgC.1 hgC.2.1 hgC.2.2.1 hgC.2.2.2
    · exact absurd (p4_cpin G hs hgC.1 hg4 hhC.1 (by omega)) (Ne.symm hne)
    · exact p4_pair_CA n hn G hT hC4 hs hg4 hgr hgC.1 hgC.2.1 hgC.2.2.1
        hgC.2.2.2 hh4 hhr hhA.1 hhA.2.1 hhA.2.2.1 hhA.2.2.2
  · rcases p4_rich_role n hn G hT hC4 hs hh4 hhr with htb | hhB | hhC | hhA
    · exact htb
    · exact p4_pair_BA n hn G hT hC4 hs hh4 hhr hhB.1 hhB.2.1 hhB.2.2.1
        hhB.2.2.2 hg4 hgr hgA.1 hgA.2.1 hgA.2.2.1 hgA.2.2.2
    · exact p4_pair_CA n hn G hT hC4 hs hh4 hhr hhC.1 hhC.2.1 hhC.2.2.1
        hhC.2.2.2 hg4 hgr hgA.1 hgA.2.1 hgA.2.2.1 hgA.2.2.2
    · exact (hubs_share_two_false n hn G hT hC4 hg4 hh4 hne hs.ne_ad hs.deg_a
        hs.deg_d hgA.1 hhA.1 hgA.2.1 hhA.2.1).elim

open Classical in
/-- **The P4 corner closure** (arbitrary blocked cherry): normalize the cherry
position by the path reversal and end swap, then run the main tree. -/
theorem p4_corner_close (n : ℕ) (hn : 18 ≤ n) (G : SimpleGraph (Fin n))
    (h : ResidualCore n G) (hsea : ∀ v : Fin n, G.degree v ≤ 4)
    {a b c d : Fin n} (hs : MShapeP4 G a b c d) {x z y : Fin n}
    (hch : Cherry G x z y)
    (hblock : ∀ t ∈ isoTwins G, 2 ≤ (badApexNbrs G x z y t).card) :
    TwoBlockConfig G := by
  have hIso : 4 ≤ (isoTwins G).card :=
    MShapeP4.iso_ge n (by omega) G hs h.edge_card h.min_degree
  have main : ∀ x' z' y' : Fin n, x' = a → z' = b → y' = c →
      (∀ t ∈ isoTwins G, 2 ≤ (badApexNbrs G x' z' y' t).card) →
      TwoBlockConfig G := by
    intro x' z' y' ex ez ey hb'
    rw [ex, ez, ey] at hb'
    exact p4_close_main n hn G h.no_good_triangle h.no_good_C4 h.min_degree
      hsea hs hIso hb'
  have main' : ∀ x' z' y' : Fin n, x' = d → z' = c → y' = b →
      (∀ t ∈ isoTwins G, 2 ≤ (badApexNbrs G x' z' y' t).card) →
      TwoBlockConfig G := by
    intro x' z' y' ex ez ey hb'
    rw [ex, ez, ey] at hb'
    exact p4_close_main n hn G h.no_good_triangle h.no_good_C4 h.min_degree
      hsea hs.rev
      (by
        have := hIso
        exact this) hb'
  have hswap : ∀ t ∈ isoTwins G, 2 ≤ (badApexNbrs G y z x t).card := by
    intro t ht
    have := hblock t ht
    rwa [badApexNbrs_swap G x z y t] at this
  have hz_mem : z = a ∨ z = b ∨ z = c ∨ z = d := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2, h3, h4⟩ := hcon
    have := hs.iso_rest z hch.deg_z h1 h2 h3 h4
    exact (mem_isoTwins.mp this).2 x hch.adj_zx hch.deg_x
  rcases hz_mem with ez | ez | ez | ez
  · -- z = a: both ends would be b
    have hx := hs.mnbr_a x (ez ▸ hch.adj_zx) hch.deg_x
    have hy := hs.mnbr_a y (ez ▸ hch.adj_zy) hch.deg_y
    exact absurd (hx.trans hy.symm) hch.ne_xy
  · -- z = b
    have hx := hs.mnbr_b x (ez ▸ hch.adj_zx) hch.deg_x
    have hy := hs.mnbr_b y (ez ▸ hch.adj_zy) hch.deg_y
    rcases hx with ex | ex <;> rcases hy with ey | ey
    · exact absurd (ex.trans ey.symm) hch.ne_xy
    · exact main x z y ex ez ey hblock
    · exact main y z x ey ez ex hswap
    · exact absurd (ex.trans ey.symm) hch.ne_xy
  · -- z = c: run the reversed shape
    have hx := hs.mnbr_c x (ez ▸ hch.adj_zx) hch.deg_x
    have hy := hs.mnbr_c y (ez ▸ hch.adj_zy) hch.deg_y
    rcases hx with ex | ex <;> rcases hy with ey | ey
    · exact absurd (ex.trans ey.symm) hch.ne_xy
    · -- (x, y) = (b, d): reversed main wants (d, c, b)
      exact main' y z x ey ez ex hswap
    · exact main' x z y ex ez ey hblock
    · exact absurd (ex.trans ey.symm) hch.ne_xy
  · -- z = d: both ends would be c
    have hx := hs.mnbr_d x (ez ▸ hch.adj_zx) hch.deg_x
    have hy := hs.mnbr_d y (ez ▸ hch.adj_zy) hch.deg_y
    exact absurd (hx.trans hy.symm) hch.ne_xy

/-! ## The M-shape classification

Under `¬goodTriangle` (`n ≥ 6`), `¬goodC4` (`n ≥ 8`) and `¬deg3-2K₂`, the
degree-`3` graph with `e(M) ≥ 3` is exactly one of the five shapes.  The tree:
a vertex of `M`-degree `3` exists (→ claw / chair / S22, by the third-neighbour
case analysis) or not (→ P4 / C5, growing the cherry to a path). -/

open Classical in
/-- No `4`-cycle among degree-`3` vertices (diagonals die by the degree-`3`
triangle, the induced cycle by the `∑ = 12` good `C₄`, `n ≥ 8`). -/
theorem mC4_false (n : ℕ) (hn : 8 ≤ n) (G : SimpleGraph (Fin n))
    (hT : ¬HasGoodTriangle n G) (hC4 : ¬HasGoodC4 n G) {p q r s : Fin n}
    (h3p : G.degree p = 3) (h3q : G.degree q = 3) (h3r : G.degree r = 3)
    (h3s : G.degree s = 3) (hpq : G.Adj p q) (hqr : G.Adj q r) (hrs : G.Adj r s)
    (hsp : G.Adj s p) (hpr : p ≠ r) (hqs : q ≠ s) : False := by
  by_cases hac : G.Adj p r
  · exact deg3_triangle_false n (by omega) G hT h3p h3q h3r hpq hqr hac
  by_cases hbd : G.Adj q s
  · exact deg3_triangle_false n (by omega) G hT h3q h3r h3s hqr hrs hbd
  refine hC4 ⟨p, q, r, s, ?_, hpq, hqr, hrs, hsp, hac, hbd, ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [G.ne_of_adj hpq, hpr,
        (G.ne_of_adj hsp).symm]),
      Finset.card_insert_of_notMem (by simp [G.ne_of_adj hqr, hqs]),
      Finset.card_pair (G.ne_of_adj hrs)]
  · rw [h3p, h3q, h3r, h3s]
    calc n * (3 + 3 + 3 + 3 - 8) = n * 4 := by norm_num
      _ ≤ 2 * (4 * (n - 4)) := by omega

open Classical in
/-- Two vertex-disjoint `M`-edges have a crossing `M`-edge (no induced `2K₂`). -/
theorem cross_of_no2K2 (n : ℕ) (G : SimpleGraph (Fin n))
    (h2k2 : ¬HasDeg3Ind2K2 n G) {u v p q : Fin n}
    (hu : G.degree u = 3) (hv : G.degree v = 3) (hp : G.degree p = 3)
    (hq : G.degree q = 3) (huv : G.Adj u v) (hpq : G.Adj p q)
    (hup : u ≠ p) (huq : u ≠ q) (hvp : v ≠ p) (hvq : v ≠ q) :
    G.Adj u p ∨ G.Adj u q ∨ G.Adj v p ∨ G.Adj v q := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3, h4⟩ := hcon
  refine h2k2 ⟨u, v, p, q, ?_, hu, hv, hp, hq, huv, hpq, h1, h2, h3, h4⟩
  rw [Finset.card_insert_of_notMem (by simp [G.ne_of_adj huv, hup, huq]),
    Finset.card_insert_of_notMem (by simp [hvp, hvq]),
    Finset.card_pair (G.ne_of_adj hpq)]

open Classical in
/-- **Outside vertices are iso**: every shape-closed predicate `P` holding on an
`M`-edge `p−q` isolates all degree-`3` vertices outside `P` (any outside `M`-edge
would be an induced `2K₂` against `p−q`). -/
theorem outside_iso (n : ℕ) (G : SimpleGraph (Fin n)) (h2k2 : ¬HasDeg3Ind2K2 n G)
    (P : Fin n → Prop) {p q : Fin n}
    (hp3 : G.degree p = 3) (hq3 : G.degree q = 3) (hpq : G.Adj p q)
    (hpP : P p) (hqP : P q)
    (hclosed : ∀ u w : Fin n, P u → G.degree u = 3 → G.degree w = 3 →
      G.Adj u w → P w)
    {v : Fin n} (hv3 : G.degree v = 3) (hvP : ¬P v) : v ∈ isoTwins G := by
  rw [mem_isoTwins]
  refine ⟨hv3, fun u hvu hu3 => ?_⟩
  have huP : ¬P u := fun h => hvP (hclosed u v h hu3 hv3 hvu.symm)
  have hvp : v ≠ p := fun e => hvP (e ▸ hpP)
  have hvq : v ≠ q := fun e => hvP (e ▸ hqP)
  have hup : u ≠ p := fun e => huP (e ▸ hpP)
  have huq : u ≠ q := fun e => huP (e ▸ hqP)
  rcases cross_of_no2K2 n G h2k2 hv3 hu3 hp3 hq3 hvu hpq hvp hvq hup huq with
    h | h | h | h
  · exact hvP (hclosed p v hpP hp3 hv3 h.symm)
  · exact hvP (hclosed q v hqP hq3 hv3 h.symm)
  · exact huP (hclosed p u hpP hp3 hu3 h.symm)
  · exact huP (hclosed q u hqP hq3 hu3 h.symm)

open Classical in
private theorem classify_branch1_hmnbr_1 : ∀ (n : ℕ) (_ : 8 ≤ n) (G : SimpleGraph (Fin n)) (_ :
  ¬HasGoodTriangle n G)
  (_ : ¬HasGoodC4 n G) (_ : ¬HasDeg3Ind2K2 n G) {v₀ w₁ p : Fin n} (_ : G.degree w₁ = 3) (_ :
    G.degree p = 3)
  (_ : G.Adj w₁ p) (p' : Fin n) (_ : G.Adj w₁ p') (_ : G.degree p' = 3) (_ : p' ≠ p)
  (_ : ∀ (w : Fin n), G.Adj w₁ w → w = v₀ ∨ w = p ∨ w = p') {wl : Fin n},
  G.degree wl = 3 →
    G.Adj v₀ wl →
      wl ≠ w₁ → ¬G.Adj wl w₁ → ¬G.Adj wl p → ¬G.Adj wl p' → ∀ (r : Fin n), G.Adj wl r → G.degree r
        = 3 → r = v₀ := by
  classical
  intro n hn G hT hC4 h2k2 v₀ w₁ p h1 hp3 hap p' hap' hp'3 hp'p hpinw₁ wl hwl3 hawl hwlw₁ hnw₁ hnp
    hnp' r har hr3
  by_contra hrv
  have hrw₁ : r ≠ w₁ := fun e => hnw₁ (e ▸ har)
  have hrp : r ≠ p := fun e => hnp (e ▸ har)
  have hrp' : r ≠ p' := fun e => hnp' (e ▸ har)
  have hwlp : wl ≠ p := fun e => hnw₁ (by rw [e]; exact hap.symm)
  have hwlp' : wl ≠ p' := fun e => hnw₁ (by rw [e]; exact hap'.symm)
  have hf1 : G.Adj r p := by
    rcases cross_of_no2K2 n G h2k2 hwl3 hr3 h1 hp3 har hap hwlw₁ hwlp
      hrw₁ hrp with h | h | h | h
    · exact absurd h hnw₁
    · exact absurd h hnp
    · rcases hpinw₁ r h.symm with e | e | e
      · exact absurd e hrv
      · exact absurd e hrp
      · exact absurd e hrp'
    · exact h
  have hf2 : G.Adj r p' := by
    rcases cross_of_no2K2 n G h2k2 hwl3 hr3 h1 hp'3 har hap' hwlw₁ hwlp'
      hrw₁ hrp' with h | h | h | h
    · exact absurd h hnw₁
    · exact absurd h hnp'
    · rcases hpinw₁ r h.symm with e | e | e
      · exact absurd e hrv
      · exact absurd e hrp
      · exact absurd e hrp'
    · exact h
  exact mC4_false n hn G hT hC4 hp3 hr3 hp'3 h1 hf1.symm hf2 hap'.symm hap
    hp'p.symm hrw₁

open Classical in
private theorem classify_branch1_hmnbr_2 : ∀ (n : ℕ) (_ : 8 ≤ n) (G : SimpleGraph (Fin n)) (_ :
  ¬HasGoodTriangle n G)
  (_ : ¬HasGoodC4 n G) (_ : ¬HasDeg3Ind2K2 n G) {v₀ w₁ p : Fin n} (_ : G.degree v₀ = 3) (_ :
    G.degree w₁ = 3)
  (_ : G.degree p = 3) (_ : G.Adj v₀ w₁) (_ : G.Adj w₁ p) (_ : p ≠ v₀) (_ : ¬G.Adj p v₀)
  (_ : ∀ (w : Fin n), G.Adj w₁ w → G.degree w = 3 → w = v₀ ∨ w = p) {wl wo : Fin n},
  G.degree wl = 3 →
    G.degree wo = 3 →
      G.Adj v₀ wl →
        G.Adj v₀ wo →
          wl ≠ w₁ →
            wo ≠ w₁ →
              wo ≠ wl →
                ¬G.Adj wl w₁ →
                  ¬G.Adj wo w₁ →
                    ¬G.Adj wl wo →
                      ¬G.Adj wl p →
                        ¬G.Adj wo p →
                          (∀ (w : Fin n), G.Adj v₀ w → w = w₁ ∨ w = wl ∨ w = wo) →
                            ∀ (r : Fin n), G.Adj wl r → G.degree r = 3 → r = v₀ := by
  classical
  intro n hn G hT hC4 h2k2 v₀ w₁ p h0 h1 hp3 ha1 hap hpv hnpv₀ hpinw₁ wl wo hwl3 hwo3 hawl hawo
    hwlw₁ hwow₁ hwowl hnw₁ hnow₁ hnwo hnp hnop hpin0' r har hr3
  by_contra hrv
  have hrw₁ : r ≠ w₁ := fun e => hnw₁ (e ▸ har)
  have hrp : r ≠ p := fun e => hnp (e ▸ har)
  have hrwo : r ≠ wo := fun e => hnwo (e ▸ har)
  have hrwl : r ≠ wl := (G.ne_of_adj har).symm
  have hwlp : wl ≠ p := fun e => hnw₁ (by rw [e]; exact hap.symm)
  have hwop : wo ≠ p := fun e => hnow₁ (by rw [e]; exact hap.symm)
  have hf : G.Adj r p := by
    rcases cross_of_no2K2 n G h2k2 hwl3 hr3 h1 hp3 har hap hwlw₁ hwlp
      hrw₁ hrp with h | h | h | h
    · exact absurd h hnw₁
    · exact absurd h hnp
    · rcases hpinw₁ r h.symm hr3 with e | e
      · exact absurd e hrv
      · exact absurd e hrp
    · exact h
  -- C5-plus-pendant contradiction: (v₀, wo) vs (r, p)
  rcases cross_of_no2K2 n G h2k2 h0 hwo3 hr3 hp3 hawo hf
    (Ne.symm hrv) (Ne.symm hpv) hrwo.symm hwop with h | h | h | h
  · rcases hpin0' r h with e | e | e
    · exact hrw₁ e
    · exact hrwl e
    · exact hrwo e
  · exact hnpv₀ h.symm
  · exact mC4_false n hn G hT hC4 h0 hwo3 hr3 hwl3 hawo h har.symm
      hawl.symm (Ne.symm hrv) hwowl
  · exact mC4_false n hn G hT hC4 h0 hwo3 hp3 h1 hawo h hap.symm ha1.symm
      (Ne.symm hpv) hwow₁

open Classical in
/-- **The extended-centre branch**: a degree-`3` claw centre whose leaf `w₁` has a
further `M`-neighbour `p` gives the chair or the S22. -/
theorem classify_branch1 (n : ℕ) (hn : 8 ≤ n) (G : SimpleGraph (Fin n))
    (hT : ¬HasGoodTriangle n G) (hC4 : ¬HasGoodC4 n G) (h2k2 : ¬HasDeg3Ind2K2 n G)
    {v₀ w₁ w₂ w₃ p : Fin n}
    (h0 : G.degree v₀ = 3) (h1 : G.degree w₁ = 3) (h2 : G.degree w₂ = 3)
    (h3 : G.degree w₃ = 3) (hp3 : G.degree p = 3)
    (ha1 : G.Adj v₀ w₁) (ha2 : G.Adj v₀ w₂) (ha3 : G.Adj v₀ w₃)
    (h12 : w₁ ≠ w₂) (h13 : w₁ ≠ w₃) (h23 : w₂ ≠ w₃)
    (hap : G.Adj w₁ p) (hpv : p ≠ v₀) :
    (∃ q l₁ l₂ p' e', MShapeChair G q l₁ l₂ p' e') ∨
    (∃ q₁ q₂ l₁ l₂ m₁ m₂, MShapeS22 G q₁ q₂ l₁ l₂ m₁ m₂) := by
  have htri : ∀ {r s t : Fin n}, G.degree r = 3 → G.degree s = 3 →
      G.degree t = 3 → G.Adj r s → G.Adj s t → G.Adj r t → False :=
    fun hr hs ht hrs hst hrt =>
    deg3_triangle_false n (by omega) G hT hr hs ht hrs hst hrt
  have hnadj12 : ¬G.Adj w₁ w₂ := fun h => htri h0 h1 h2 ha1 h ha2
  have hnadj13 : ¬G.Adj w₁ w₃ := fun h => htri h0 h1 h3 ha1 h ha3
  have hnadj23 : ¬G.Adj w₂ w₃ := fun h => htri h0 h2 h3 ha2 h ha3
  have hpin0 : ∀ w : Fin n, G.Adj v₀ w → w = w₁ ∨ w = w₂ ∨ w = w₃ :=
    fun w hw => deg3_nbr_pin G h0 ha1 ha2 ha3 h12 h13 h23 hw
  have hpw₁ : p ≠ w₁ := (G.ne_of_adj hap).symm
  have hpw₂ : p ≠ w₂ := fun e => hnadj12 (e ▸ hap)
  have hpw₃ : p ≠ w₃ := fun e => hnadj13 (e ▸ hap)
  have hnpv₀ : ¬G.Adj p v₀ := by
    intro h
    rcases hpin0 p h.symm with e | e | e
    · exact hpw₁ e
    · exact hpw₂ e
    · exact hpw₃ e
  have hnpw₂ : ¬G.Adj p w₂ :=
    fun h => mC4_false n hn G hT hC4 hp3 h1 h0 h2 hap.symm ha1.symm ha2 h.symm
      hpv h12
  have hnpw₃ : ¬G.Adj p w₃ :=
    fun h => mC4_false n hn G hT hC4 hp3 h1 h0 h3 hap.symm ha1.symm ha3 h.symm
      hpv h13
  by_cases hp' : ∃ p' : Fin n, G.Adj w₁ p' ∧ G.degree p' = 3 ∧ p' ≠ v₀ ∧ p' ≠ p
  · -- S22 (centres v₀, w₁; leaves w₂, w₃ / p, p')
    right
    obtain ⟨p', hap', hp'3, hp'v, hp'p⟩ := hp'
    have hp'w₁ : p' ≠ w₁ := (G.ne_of_adj hap').symm
    have hp'w₂ : p' ≠ w₂ := fun e => hnadj12 (e ▸ hap')
    have hp'w₃ : p' ≠ w₃ := fun e => hnadj13 (e ▸ hap')
    have hnp'v₀ : ¬G.Adj p' v₀ := by
      intro h
      rcases hpin0 p' h.symm with e | e | e
      · exact hp'w₁ e
      · exact hp'w₂ e
      · exact hp'w₃ e
    have hnp'w₂ : ¬G.Adj p' w₂ :=
      fun h => mC4_false n hn G hT hC4 hp'3 h1 h0 h2 hap'.symm ha1.symm ha2
        h.symm hp'v h12
    have hnp'w₃ : ¬G.Adj p' w₃ :=
      fun h => mC4_false n hn G hT hC4 hp'3 h1 h0 h3 hap'.symm ha1.symm ha3
        h.symm hp'v h13
    have hpinw₁ : ∀ w : Fin n, G.Adj w₁ w → w = v₀ ∨ w = p ∨ w = p' :=
      fun w hw => deg3_nbr_pin G h1 ha1.symm hap hap' (Ne.symm hpv)
        (Ne.symm hp'v) (Ne.symm hp'p) hw
    -- inner-leaf pins (w₂, w₃)
    have hmnbr : ∀ {wl : Fin n}, G.degree wl = 3 → G.Adj v₀ wl → wl ≠ w₁ →
        ¬G.Adj wl w₁ → ¬G.Adj wl p → ¬G.Adj wl p' →
        ∀ r : Fin n, G.Adj wl r → G.degree r = 3 → r = v₀ :=
        classify_branch1_hmnbr_1 (n := n) (hn) (G := G) (hT) (hC4) (h2k2) (v₀ := v₀) (w₁ := w₁) (p
          := p) (h1) (hp3) (hap) (p' := p') (hap') (hp'3) (hp'p) (hpinw₁)
    have hmnbr2 := hmnbr h2 ha2 (Ne.symm h12) (fun h => hnadj12 h.symm)
      (fun h => hnpw₂ h.symm) (fun h => hnp'w₂ h.symm)
    have hmnbr3 := hmnbr h3 ha3 (Ne.symm h13) (fun h => hnadj13 h.symm)
      (fun h => hnpw₃ h.symm) (fun h => hnp'w₃ h.symm)
    -- outer-leaf pins (p, p')
    have hmnbrO : ∀ {po : Fin n}, G.degree po = 3 → G.Adj w₁ po → po ≠ v₀ →
        po ≠ w₂ → ¬G.Adj po v₀ → ¬G.Adj po w₂ → ¬G.Adj po w₃ →
        ∀ q : Fin n, G.Adj po q → G.degree q = 3 → q = w₁ := by
      intro po hpo3 hapo hpov hpow₂ hnv hnw₂' hnw₃' q haq hq3
      by_contra hqw₁
      have hqv : q ≠ v₀ := fun e => hnv (e ▸ haq)
      have hqw₂ : q ≠ w₂ := fun e => hnw₂' (e ▸ haq)
      have hqw₃ : q ≠ w₃ := fun e => hnw₃' (e ▸ haq)
      rcases cross_of_no2K2 n G h2k2 hpo3 hq3 h0 h2 haq ha2 hpov hpow₂
        hqv hqw₂ with h | h | h | h
      · exact hnv h
      · exact hnw₂' h
      · rcases hpin0 q h.symm with e | e | e
        · exact hqw₁ e
        · exact hqw₂ e
        · exact hqw₃ e
      · exact hqv (hmnbr2 q h.symm hq3)
    have hmnbrp := hmnbrO hp3 hap hpv hpw₂ hnpv₀ hnpw₂ hnpw₃
    have hmnbrp' := hmnbrO hp'3 hap' hp'v hp'w₂ hnp'v₀ hnp'w₂ hnp'w₃
    refine ⟨v₀, w₁, w₂, w₃, p, p', ?_⟩
    refine
      { deg_q₁ := h0, deg_q₂ := h1, deg_l₁ := h2, deg_l₂ := h3
        deg_m₁ := hp3, deg_m₂ := hp'3
        adj_qq := ha1, adj_l₁ := ha2, adj_l₂ := ha3, adj_m₁ := hap, adj_m₂ := hap'
        ne_l₁l₂ := h23, ne_m₁m₂ := Ne.symm hp'p
        ne_q₁m₁ := Ne.symm hpv, ne_q₁m₂ := Ne.symm hp'v
        ne_q₂l₁ := h12, ne_q₂l₂ := h13
        ne_l₁m₁ := Ne.symm hpw₂, ne_l₁m₂ := Ne.symm hp'w₂
        ne_l₂m₁ := Ne.symm hpw₃, ne_l₂m₂ := Ne.symm hp'w₃
        mnbr_l₁ := hmnbr2, mnbr_l₂ := hmnbr3
        mnbr_m₁ := hmnbrp, mnbr_m₂ := hmnbrp'
        iso_rest := ?_ }
    intro v hv3 hv1 hv2 hv3' hv4 hv5 hv6
    refine outside_iso n G h2k2
      (fun u => u = v₀ ∨ u = w₁ ∨ u = w₂ ∨ u = w₃ ∨ u = p ∨ u = p')
      h0 h1 ha1 (Or.inl rfl) (Or.inr (Or.inl rfl)) ?_ hv3
      (by push Not; exact ⟨hv1, hv2, hv3', hv4, hv5, hv6⟩)
    intro u w hu hu3 hw3 huw
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    · rcases hpin0 w huw with rfl | rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · rcases hpinw₁ w huw with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    · exact Or.inl (hmnbr2 w huw hw3)
    · exact Or.inl (hmnbr3 w huw hw3)
    · exact Or.inr (Or.inl (hmnbrp w huw hw3))
    · exact Or.inr (Or.inl (hmnbrp' w huw hw3))
  · -- Chair (centre v₀; leaves w₂, w₃; path v₀−w₁−p)
    left
    push Not at hp'
    have hpinw₁ : ∀ w : Fin n, G.Adj w₁ w → G.degree w = 3 → w = v₀ ∨ w = p := by
      intro w hw h3'
      by_cases hwv : w = v₀
      · exact Or.inl hwv
      · exact Or.inr (hp' w hw h3' hwv)
    -- inner-leaf pins (generic in the ordered leaf pair)
    have hmnbr : ∀ {wl wo : Fin n}, G.degree wl = 3 → G.degree wo = 3 →
        G.Adj v₀ wl → G.Adj v₀ wo → wl ≠ w₁ → wo ≠ w₁ → wo ≠ wl →
        ¬G.Adj wl w₁ → ¬G.Adj wo w₁ → ¬G.Adj wl wo → ¬G.Adj wl p → ¬G.Adj wo p →
        (∀ w : Fin n, G.Adj v₀ w → w = w₁ ∨ w = wl ∨ w = wo) →
        ∀ r : Fin n, G.Adj wl r → G.degree r = 3 → r = v₀ :=
        classify_branch1_hmnbr_2 (n := n) (hn) (G := G) (hT) (hC4) (h2k2) (v₀ := v₀) (w₁ := w₁) (p
          := p) (h0) (h1) (hp3) (ha1) (hap) (hpv) (hnpv₀) (hpinw₁)
    have hmnbr2 : ∀ r : Fin n, G.Adj w₂ r → G.degree r = 3 → r = v₀ :=
      hmnbr h2 h3 ha2 ha3 (Ne.symm h12) (Ne.symm h13) (Ne.symm h23)
        (fun h => hnadj12 h.symm) (fun h => hnadj13 h.symm) hnadj23
        (fun h => hnpw₂ h.symm) (fun h => hnpw₃ h.symm) hpin0
    have hmnbr3 : ∀ r : Fin n, G.Adj w₃ r → G.degree r = 3 → r = v₀ :=
      hmnbr h3 h2 ha3 ha2 (Ne.symm h13) (Ne.symm h12) h23
        (fun h => hnadj13 h.symm) (fun h => hnadj12 h.symm)
        (fun h => hnadj23 h.symm)
        (fun h => hnpw₃ h.symm) (fun h => hnpw₂ h.symm)
        (fun w hw => by
          rcases hpin0 w hw with e | e | e
          · exact Or.inl e
          · exact Or.inr (Or.inr e)
          · exact Or.inr (Or.inl e))
    -- the path-end pin
    have hmnbrp : ∀ q : Fin n, G.Adj p q → G.degree q = 3 → q = w₁ := by
      intro q haq hq3
      by_contra hqw₁
      have hqv : q ≠ v₀ := fun e => hnpv₀ (e ▸ haq)
      have hqw₂ : q ≠ w₂ := fun e => hnpw₂ (e ▸ haq)
      have hqw₃ : q ≠ w₃ := fun e => hnpw₃ (e ▸ haq)
      rcases cross_of_no2K2 n G h2k2 hp3 hq3 h0 h2 haq ha2 hpv hpw₂
        hqv hqw₂ with h | h | h | h
      · exact hnpv₀ h
      · exact hnpw₂ h
      · rcases hpin0 q h.symm with e | e | e
        · exact hqw₁ e
        · exact hqw₂ e
        · exact hqw₃ e
      · exact hqv (hmnbr2 q h.symm hq3)
    refine ⟨v₀, w₂, w₃, w₁, p, ?_⟩
    refine
      { deg_q := h0, deg_l₁ := h2, deg_l₂ := h3, deg_p := h1, deg_e := hp3
        adj_l₁ := ha2, adj_l₂ := ha3, adj_p := ha1, adj_pe := hap
        ne_l₁l₂ := h23, ne_l₁p := Ne.symm h12, ne_l₂p := Ne.symm h13
        ne_l₁e := Ne.symm hpw₂, ne_l₂e := Ne.symm hpw₃, ne_qe := Ne.symm hpv
        mnbr_l₁ := hmnbr2, mnbr_l₂ := hmnbr3
        mnbr_p := hpinw₁, mnbr_e := hmnbrp
        iso_rest := ?_ }
    intro v hv3 hv1 hv2 hv3' hv4 hv5
    refine outside_iso n G h2k2
      (fun u => u = v₀ ∨ u = w₁ ∨ u = w₂ ∨ u = w₃ ∨ u = p)
      h0 h1 ha1 (Or.inl rfl) (Or.inr (Or.inl rfl)) ?_ hv3
      (by push Not; exact ⟨hv1, hv4, hv2, hv3', hv5⟩)
    intro u w hu hu3 hw3 huw
    rcases hu with rfl | rfl | rfl | rfl | rfl
    · rcases hpin0 w huw with rfl | rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · rcases hpinw₁ w huw hw3 with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    · exact Or.inl (hmnbr2 w huw hw3)
    · exact Or.inl (hmnbr3 w huw hw3)
    · exact Or.inr (Or.inl (hmnbrp w huw hw3))

open Classical in
/-- **Case I of the classification**: a vertex of `M`-degree `3` gives the claw,
the chair, or the S22. -/
theorem classify_center3 (n : ℕ) (hn : 8 ≤ n) (G : SimpleGraph (Fin n))
    (hT : ¬HasGoodTriangle n G) (hC4 : ¬HasGoodC4 n G) (h2k2 : ¬HasDeg3Ind2K2 n G)
    {v₀ w₁ w₂ w₃ : Fin n}
    (h0 : G.degree v₀ = 3) (h1 : G.degree w₁ = 3) (h2 : G.degree w₂ = 3)
    (h3 : G.degree w₃ = 3)
    (ha1 : G.Adj v₀ w₁) (ha2 : G.Adj v₀ w₂) (ha3 : G.Adj v₀ w₃)
    (h12 : w₁ ≠ w₂) (h13 : w₁ ≠ w₃) (h23 : w₂ ≠ w₃) :
    (∃ z₀ x₁ x₂ x₃, MShapeClaw G z₀ x₁ x₂ x₃) ∨
    (∃ q l₁ l₂ p' e', MShapeChair G q l₁ l₂ p' e') ∨
    (∃ q₁ q₂ l₁ l₂ m₁ m₂, MShapeS22 G q₁ q₂ l₁ l₂ m₁ m₂) := by
  by_cases he1 : ∃ p : Fin n, G.Adj w₁ p ∧ G.degree p = 3 ∧ p ≠ v₀
  · obtain ⟨p, hap, hp3, hpv⟩ := he1
    rcases classify_branch1 n hn G hT hC4 h2k2 h0 h1 h2 h3 hp3 ha1 ha2 ha3
      h12 h13 h23 hap hpv with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  by_cases he2 : ∃ p : Fin n, G.Adj w₂ p ∧ G.degree p = 3 ∧ p ≠ v₀
  · obtain ⟨p, hap, hp3, hpv⟩ := he2
    rcases classify_branch1 n hn G hT hC4 h2k2 h0 h2 h1 h3 hp3 ha2 ha1 ha3
      (Ne.symm h12) h23 h13 hap hpv with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  by_cases he3 : ∃ p : Fin n, G.Adj w₃ p ∧ G.degree p = 3 ∧ p ≠ v₀
  · obtain ⟨p, hap, hp3, hpv⟩ := he3
    rcases classify_branch1 n hn G hT hC4 h2k2 h0 h3 h1 h2 hp3 ha3 ha1 ha2
      (Ne.symm h13) (Ne.symm h23) h12 hap hpv with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · -- Claw
    left
    push Not at he1 he2 he3
    have hpin0 : ∀ w : Fin n, G.Adj v₀ w → w = w₁ ∨ w = w₂ ∨ w = w₃ :=
      fun w hw => deg3_nbr_pin G h0 ha1 ha2 ha3 h12 h13 h23 hw
    have htri : ∀ {r s t : Fin n}, G.degree r = 3 → G.degree s = 3 →
        G.degree t = 3 → G.Adj r s → G.Adj s t → G.Adj r t → False :=
      fun hr hs ht hrs hst hrt =>
      deg3_triangle_false n (by omega) G hT hr hs ht hrs hst hrt
    refine ⟨v₀, w₁, w₂, w₃, ?_⟩
    refine
      { deg_z := h0, deg_1 := h1, deg_2 := h2, deg_3 := h3
        adj_1 := ha1, adj_2 := ha2, adj_3 := ha3
        ne_12 := h12, ne_13 := h13, ne_23 := h23
        mnbr_1 := he1, mnbr_2 := he2, mnbr_3 := he3
        iso_rest := ?_ }
    intro v hv3 hv1 hv2 hv3' hv4
    refine outside_iso n G h2k2
      (fun u => u = v₀ ∨ u = w₁ ∨ u = w₂ ∨ u = w₃)
      h0 h1 ha1 (Or.inl rfl) (Or.inr (Or.inl rfl)) ?_ hv3
      (by push Not; exact ⟨hv1, hv2, hv3', hv4⟩)
    intro u w hu hu3 hw3 huw
    rcases hu with rfl | rfl | rfl | rfl
    · rcases hpin0 w huw with rfl | rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inl (he1 w huw hw3)
    · exact Or.inl (he2 w huw hw3)
    · exact Or.inl (he3 w huw hw3)

open Classical in
/-- **Case II of the classification** (no `M`-degree-`3` vertex): the cherry with
an end extension gives the P4 or the C5. -/
theorem classify_path_ext (n : ℕ) (hn : 8 ≤ n) (G : SimpleGraph (Fin n))
    (hT : ¬HasGoodTriangle n G) (hC4 : ¬HasGoodC4 n G) (h2k2 : ¬HasDeg3Ind2K2 n G)
    (hno3 : ∀ v u₁ u₂ u₃ : Fin n, G.degree v = 3 → G.degree u₁ = 3 →
      G.degree u₂ = 3 → G.degree u₃ = 3 → G.Adj v u₁ → G.Adj v u₂ → G.Adj v u₃ →
      u₁ ≠ u₂ → u₁ ≠ u₃ → u₂ ≠ u₃ → False)
    {x z y a : Fin n} (hch : Cherry G x z y)
    (hxa : G.Adj x a) (ha3 : G.degree a = 3) (haz : a ≠ z) :
    (∃ a' b' c' d', MShapeP4 G a' b' c' d') ∨
    (∃ v₀ v₁ v₂ v₃ v₄, MShapeC5 G v₀ v₁ v₂ v₃ v₄) := by
  have hpinz : ∀ w : Fin n, G.Adj z w → G.degree w = 3 → w = x ∨ w = y := by
    intro w hw h3'
    by_contra hcon
    push Not at hcon
    exact hno3 z x y w hch.deg_z hch.deg_x hch.deg_y h3' hch.adj_zx hch.adj_zy
      hw hch.ne_xy (Ne.symm hcon.1) (Ne.symm hcon.2)
  have hax : a ≠ x := (G.ne_of_adj hxa).symm
  have hay : a ≠ y := fun e => hch.nadj_xy (e ▸ hxa)
  have hnaz : ¬G.Adj a z := by
    intro h
    rcases hpinz a h.symm ha3 with e | e
    · exact hax e
    · exact hay e
  have hnay : ¬G.Adj a y := fun h =>
    mC4_false n hn G hT hC4 ha3 hch.deg_x hch.deg_z hch.deg_y hxa.symm
      hch.adj_zx.symm hch.adj_zy h.symm haz hch.ne_xy
  have hpinx : ∀ w : Fin n, G.Adj x w → G.degree w = 3 → w = z ∨ w = a := by
    intro w hw h3'
    by_contra hcon
    push Not at hcon
    exact hno3 x z a w hch.deg_x hch.deg_z ha3 h3' hch.adj_zx.symm hxa hw
      (Ne.symm haz) (Ne.symm hcon.1) (Ne.symm hcon.2)
  by_cases hyext : ∃ r : Fin n, G.Adj y r ∧ G.degree r = 3 ∧ r ≠ z
  · -- C5 (z, x, a, r, y)
    right
    obtain ⟨r, hyr, hr3, hrz⟩ := hyext
    have hry : r ≠ y := (G.ne_of_adj hyr).symm
    have hrx : r ≠ x := fun e => hch.nadj_xy (e ▸ hyr).symm
    have hra : r ≠ a := fun e => hnay (e ▸ hyr).symm
    have hpiny : ∀ w : Fin n, G.Adj y w → G.degree w = 3 → w = z ∨ w = r := by
      intro w hw h3'
      by_contra hcon
      push Not at hcon
      exact hno3 y z r w hch.deg_y hch.deg_z hr3 h3' hch.adj_zy.symm hyr hw
        (Ne.symm hrz) (Ne.symm hcon.1) (Ne.symm hcon.2)
    have haar : G.Adj a r := by
      rcases cross_of_no2K2 n G h2k2 hch.deg_x ha3 hch.deg_y hr3 hxa hyr
        hch.ne_xy (Ne.symm hrx) hay (Ne.symm hra) with h | h | h | h
      · exact absurd h hch.nadj_xy
      · rcases hpinx r h hr3 with e | e
        · exact absurd e hrz
        · exact absurd e hra
      · exact absurd h hnay
      · exact h
    have hpina : ∀ w : Fin n, G.Adj a w → G.degree w = 3 → w = x ∨ w = r := by
      intro w hw h3'
      by_contra hcon
      push Not at hcon
      exact hno3 a x r w ha3 hch.deg_x hr3 h3' hxa.symm haar hw
        hrx.symm (Ne.symm hcon.1) (Ne.symm hcon.2)
    have hpinr : ∀ w : Fin n, G.Adj r w → G.degree w = 3 → w = a ∨ w = y := by
      intro w hw h3'
      by_contra hcon
      push Not at hcon
      exact hno3 r a y w hr3 ha3 hch.deg_y h3' haar.symm hyr.symm hw
        hay (Ne.symm hcon.1) (Ne.symm hcon.2)
    refine ⟨z, x, a, r, y, ?_⟩
    refine
      { deg_0 := hch.deg_z, deg_1 := hch.deg_x, deg_2 := ha3, deg_3 := hr3
        deg_4 := hch.deg_y
        adj_01 := hch.adj_zx, adj_12 := hxa, adj_23 := haar, adj_34 := hyr.symm
        adj_40 := hch.adj_zy.symm
        ne_02 := Ne.symm haz, ne_03 := Ne.symm hrz, ne_13 := Ne.symm hrx
        ne_14 := hch.ne_xy, ne_24 := hay
        mnbr_0 := fun w hw h3' => hpinz w hw h3'
        mnbr_1 := hpinx, mnbr_2 := hpina, mnbr_3 := hpinr
        mnbr_4 := fun w hw h3' => (hpiny w hw h3').symm
        iso_rest := ?_ }
    intro v hv3 hv0 hv1 hv2 hv3' hv4
    refine outside_iso n G h2k2
      (fun u => u = z ∨ u = x ∨ u = a ∨ u = r ∨ u = y)
      hch.deg_z hch.deg_x hch.adj_zx (Or.inl rfl) (Or.inr (Or.inl rfl)) ?_ hv3
      (by push Not; exact ⟨hv0, hv1, hv2, hv3', hv4⟩)
    intro u w hu hu3 hw3 huw
    rcases hu with rfl | rfl | rfl | rfl | rfl
    · rcases hpinz w huw hw3 with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    · rcases hpinx w huw hw3 with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
    · rcases hpina w huw hw3 with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · rcases hpinr w huw hw3 with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
    · rcases hpiny w huw hw3 with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · -- P4 (a, x, z, y)
    left
    push Not at hyext
    have hpina : ∀ w : Fin n, G.Adj a w → G.degree w = 3 → w = x := by
      intro q haq hq3
      by_contra hqx
      have hqz : q ≠ z := fun e => hnaz (e ▸ haq)
      have hqy : q ≠ y := fun e => hnay (e ▸ haq)
      rcases cross_of_no2K2 n G h2k2 ha3 hq3 hch.deg_z hch.deg_y haq hch.adj_zy
        haz hay hqz hqy with h | h | h | h
      · exact hnaz h
      · exact hnay h
      · rcases hpinz q h.symm hq3 with e | e
        · exact hqx e
        · exact hqy e
      · exact hqz (hyext q h.symm hq3)
    refine ⟨a, x, z, y, ?_⟩
    refine
      { deg_a := ha3, deg_b := hch.deg_x, deg_c := hch.deg_z, deg_d := hch.deg_y
        adj_ab := hxa.symm, adj_bc := hch.adj_zx.symm, adj_cd := hch.adj_zy
        ne_ac := haz, ne_ad := hay, ne_bd := hch.ne_xy
        mnbr_a := hpina
        mnbr_b := fun w hw h3' => (hpinx w hw h3').symm
        mnbr_c := hpinz
        mnbr_d := hyext
        iso_rest := ?_ }
    intro v hv3 hva hvx hvz hvy
    refine outside_iso n G h2k2
      (fun u => u = a ∨ u = x ∨ u = z ∨ u = y)
      ha3 hch.deg_x hxa.symm (Or.inl rfl) (Or.inr (Or.inl rfl)) ?_ hv3
      (by push Not; exact ⟨hva, hvx, hvz, hvy⟩)
    intro u w hu hu3 hw3 huw
    rcases hu with rfl | rfl | rfl | rfl
    · rw [hpina w huw hw3]
      exact Or.inr (Or.inl rfl)
    · rcases hpinx w huw hw3 with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inl rfl
    · rcases hpinz w huw hw3 with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr rfl))
    · rw [hyext w huw hw3]
      exact Or.inr (Or.inr (Or.inl rfl))

open Classical in
/-- With `mIncidence ≥ 5` some `M`-edge leaves the cherry. -/
theorem third_edge_of_mIncidence (n : ℕ) (G : SimpleGraph (Fin n))
    {x z y : Fin n} (hch : Cherry G x z y) (heM : 5 ≤ mIncidence G) :
    ∃ u v : Fin n, G.degree u = 3 ∧ G.degree v = 3 ∧ G.Adj u v ∧
      v ≠ x ∧ v ≠ z ∧ v ≠ y := by
  by_contra hcon
  push Not at hcon
  have hmem : ∀ u v : Fin n, G.degree u = 3 → G.degree v = 3 → G.Adj u v →
      v = x ∨ v = z ∨ v = y := by
    intro u v hu hv hadj
    by_cases e1 : v = x
    · exact Or.inl e1
    by_cases e2 : v = z
    · exact Or.inr (Or.inl e2)
    · exact Or.inr (Or.inr (hcon u v hu hv hadj e1 e2))
  have hz2 : (G.neighborFinset z ∩ deg3Set G).card = 2 := by
    have heq : G.neighborFinset z ∩ deg3Set G = {x, y} := by
      ext w
      rw [Finset.mem_inter, G.mem_neighborFinset, mem_deg3Set,
        Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hadj, h3⟩
        rcases hmem z w hch.deg_z h3 hadj with e | e | e
        · exact Or.inl e
        · exact absurd (e ▸ hadj) G.irrefl
        · exact Or.inr e
      · rintro (rfl | rfl)
        · exact ⟨hch.adj_zx, hch.deg_x⟩
        · exact ⟨hch.adj_zy, hch.deg_y⟩
    rw [heq, Finset.card_pair hch.ne_xy]
  have hx1 : (G.neighborFinset x ∩ deg3Set G).card = 1 := by
    have heq : G.neighborFinset x ∩ deg3Set G = {z} := by
      ext u
      rw [Finset.mem_inter, G.mem_neighborFinset, mem_deg3Set,
        Finset.mem_singleton]
      constructor
      · rintro ⟨hadj, h3⟩
        rcases hmem x u hch.deg_x h3 hadj with e | e | e
        · exact absurd (e ▸ hadj) G.irrefl
        · exact e
        · exact absurd (e ▸ hadj) hch.nadj_xy
      · rintro rfl
        exact ⟨hch.adj_zx.symm, hch.deg_z⟩
    rw [heq, Finset.card_singleton]
  have hy1 : (G.neighborFinset y ∩ deg3Set G).card = 1 := by
    have heq : G.neighborFinset y ∩ deg3Set G = {z} := by
      ext u
      rw [Finset.mem_inter, G.mem_neighborFinset, mem_deg3Set,
        Finset.mem_singleton]
      constructor
      · rintro ⟨hadj, h3⟩
        rcases hmem y u hch.deg_y h3 hadj with e | e | e
        · exact absurd ((e ▸ hadj) : G.Adj y x) (fun h => hch.nadj_xy h.symm)
        · exact e
        · exact absurd (e ▸ hadj) G.irrefl
      · rintro rfl
        exact ⟨hch.adj_zy.symm, hch.deg_z⟩
    rw [heq, Finset.card_singleton]
  have hrest : ∀ v : Fin n, G.degree v = 3 → v ≠ x → v ≠ z → v ≠ y →
      (G.neighborFinset v ∩ deg3Set G).card = 0 := by
    intro v hv3 h1 h2 h3
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro u hu
    rw [Finset.mem_inter, G.mem_neighborFinset, mem_deg3Set] at hu
    obtain ⟨hadj, hu3⟩ := hu
    rcases hmem u v hu3 hv3 hadj.symm with e | e | e
    · exact h1 e
    · exact h2 e
    · exact h3 e
  -- the sum
  have hsub : ({z, x, y} : Finset (Fin n)) ⊆ deg3Set G := by
    intro v hv
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact mem_deg3Set.mpr hch.deg_z
    · exact mem_deg3Set.mpr hch.deg_x
    · exact mem_deg3Set.mpr hch.deg_y
  have hsplit := Finset.sum_sdiff (f := fun v : Fin n =>
    (G.neighborFinset v ∩ deg3Set G).card) hsub
  have hzero : ∑ v ∈ deg3Set G \ ({z, x, y} : Finset (Fin n)),
      (G.neighborFinset v ∩ deg3Set G).card = 0 := by
    refine Finset.sum_eq_zero fun v hv => ?_
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_singleton] at hv
    obtain ⟨hvD, hvne⟩ := hv
    push Not at hvne
    exact hrest v (mem_deg3Set.mp hvD) hvne.2.1 hvne.1 hvne.2.2
  have htriple : ∑ v ∈ ({z, x, y} : Finset (Fin n)),
      (G.neighborFinset v ∩ deg3Set G).card = 4 := by
    rw [Finset.sum_insert (by simp [hch.ne_zx, hch.ne_zy]),
      Finset.sum_pair hch.ne_xy, hz2, hx1, hy1]
    norm_num
  have hsum := mIncidence_eq_sum G
  omega

open Classical in
/-- **THE M-SHAPE CLASSIFICATION**: under the residual exclusions, a cherry and
`mIncidence ≥ 5` force the degree-`3` graph to be exactly one of the five
shapes (each with all other degree-`3` vertices iso). -/
theorem mshape_classify (n : ℕ) (hn : 8 ≤ n) (G : SimpleGraph (Fin n))
    (hT : ¬HasGoodTriangle n G) (hC4 : ¬HasGoodC4 n G) (h2k2 : ¬HasDeg3Ind2K2 n G)
    {x z y : Fin n} (hch : Cherry G x z y) (heM : 5 ≤ mIncidence G) :
    (∃ a b c d, MShapeP4 G a b c d) ∨
    (∃ z₀ x₁ x₂ x₃, MShapeClaw G z₀ x₁ x₂ x₃) ∨
    (∃ q l₁ l₂ p e, MShapeChair G q l₁ l₂ p e) ∨
    (∃ q₁ q₂ l₁ l₂ m₁ m₂, MShapeS22 G q₁ q₂ l₁ l₂ m₁ m₂) ∨
    (∃ v₀ v₁ v₂ v₃ v₄, MShapeC5 G v₀ v₁ v₂ v₃ v₄) := by
  by_cases hcen : ∃ v₀ u₁ u₂ u₃ : Fin n, G.degree v₀ = 3 ∧ G.degree u₁ = 3 ∧
      G.degree u₂ = 3 ∧ G.degree u₃ = 3 ∧ G.Adj v₀ u₁ ∧ G.Adj v₀ u₂ ∧
      G.Adj v₀ u₃ ∧ u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₂ ≠ u₃
  · obtain ⟨v₀, u₁, u₂, u₃, h0, h1, h2, h3, ha1, ha2, ha3, h12, h13, h23⟩ := hcen
    rcases classify_center3 n hn G hT hC4 h2k2 h0 h1 h2 h3 ha1 ha2 ha3 h12 h13
      h23 with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · have hno3 : ∀ v u₁ u₂ u₃ : Fin n, G.degree v = 3 → G.degree u₁ = 3 →
        G.degree u₂ = 3 → G.degree u₃ = 3 → G.Adj v u₁ → G.Adj v u₂ →
        G.Adj v u₃ → u₁ ≠ u₂ → u₁ ≠ u₃ → u₂ ≠ u₃ → False :=
      fun v u₁ u₂ u₃ a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 =>
      hcen ⟨v, u₁, u₂, u₃, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩
    obtain ⟨u, v, hu3, hv3, huv, hvx, hvz, hvy⟩ :=
      third_edge_of_mIncidence n G hch heM
    -- locate u: it is z (impossible), x, y, or outside
    by_cases hux : u = x
    · rcases classify_path_ext n hn G hT hC4 h2k2 hno3 hch (hux ▸ huv) hv3 hvz
        with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    by_cases huy : u = y
    · rcases classify_path_ext n hn G hT hC4 h2k2 hno3 hch.swap (huy ▸ huv) hv3
        hvz with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    · -- u ∉ {x, y}: u ≠ z too (z's D-neighbours are x, y), so the edge (u,v) is
      -- disjoint from the cherry; a cross edge to (z,x) or (z,y) relocates it
      have hpinz : ∀ w : Fin n, G.Adj z w → G.degree w = 3 → w = x ∨ w = y := by
        intro w hw h3'
        by_contra hc
        push Not at hc
        exact hno3 z x y w hch.deg_z hch.deg_x hch.deg_y h3' hch.adj_zx
          hch.adj_zy hw hch.ne_xy (Ne.symm hc.1) (Ne.symm hc.2)
      have huz : u ≠ z := by
        intro e
        rcases hpinz v (e ▸ huv) hv3 with e' | e'
        · exact hvx e'
        · exact hvy e'
      rcases cross_of_no2K2 n G h2k2 hu3 hv3 hch.deg_z hch.deg_x huv
        hch.adj_zx huz hux hvz hvx with h | h | h | h
      · -- Adj u z: u ∈ {x, y} — excluded
        rcases hpinz u h.symm hu3 with e | e
        · exact absurd e hux
        · exact absurd e huy
      · -- Adj u x: x has the extension u
        rcases classify_path_ext n hn G hT hC4 h2k2 hno3 hch h.symm hu3 huz
          with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inr (Or.inr (Or.inr h')))
      · -- Adj v z: v ∈ {x, y} — excluded
        rcases hpinz v h.symm hv3 with e | e
        · exact absurd e hvx
        · exact absurd e hvy
      · -- Adj v x
        rcases classify_path_ext n hn G hT hC4 h2k2 hno3 hch h.symm hv3 hvz
          with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inr (Or.inr (Or.inr h')))

/-! ## The assembly: the `e(M) ≥ 3` corner closure and the full Δ ≤ 4 C0 -/

open Classical in
/-- **THE BLOCKED CHERRY CORNER CLOSES for `e(M) ≥ 3`** (`mIncidence ≥ 5`), in
the sea regime, for every `n ≥ 18`: classify the `M`-shape and run the
per-shape kill. -/
theorem blockedCherryCorner_close_eM_ge3 (n : ℕ) (hn : 18 ≤ n)
    (G : SimpleGraph (Fin n)) (h : ResidualCore n G)
    (hsea : ∀ v : Fin n, G.degree v ≤ 4) (heM : 5 ≤ mIncidence G)
    {x z y : Fin n} (hch : Cherry G x z y)
    (hblock : ∀ t ∈ isoTwins G, 2 ≤ (badApexNbrs G x z y t).card) :
    TwoBlockConfig G := by
  have hD8 : 8 ≤ (deg3Set G).card := by
    have hh := card_deg3_ge_eight n (by omega) G h.edge_card h.min_degree
    unfold deg3Set
    exact hh
  rcases mshape_classify n (by omega) G h.no_good_triangle h.no_good_C4
    h.no_deg3_ind2K2 hch heM with
    ⟨a, b, c, d, hs⟩ | ⟨z₀, x₁, x₂, x₃, hs⟩ | ⟨q, l₁, l₂, p, e, hs⟩ |
    ⟨q₁, q₂, l₁, l₂, m₁, m₂, hs⟩ | ⟨v₀, v₁, v₂, v₃, v₄, hs⟩
  · exact p4_corner_close n hn G h hsea hs hch hblock
  · -- claw: |Iso| ≥ 4 ≥ 3 and any rich hub kills
    have hIso : 3 ≤ (isoTwins G).card := by
      have hcov := iso_card_of_cover G ({z₀, x₁, x₂, x₃} : Finset (Fin n))
        (fun v h3 hnot => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hnot
          push Not at hnot
          exact hs.iso_rest v h3 hnot.1 hnot.2.1 hnot.2.2.1 hnot.2.2.2)
      have hle : ({z₀, x₁, x₂, x₃} : Finset (Fin n)).card ≤ 4 := by
        apply le_trans (Finset.card_insert_le _ _)
        apply Nat.succ_le_succ
        apply le_trans (Finset.card_insert_le _ _)
        apply Nat.succ_le_succ
        exact Finset.card_insert_le _ _
      omega
    obtain ⟨g, hg4, hgr, -⟩ := corner_rich_one G hsea hch hblock hIso
    exact claw_rich_kill n hn G h.no_good_triangle h.no_good_C4 hs hg4 hgr
  · -- chair: |Iso| ≥ 3
    have hIso : 3 ≤ (isoTwins G).card := by
      have hcov := iso_card_of_cover G ({q, l₁, l₂, p, e} : Finset (Fin n))
        (fun v h3 hnot => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hnot
          push Not at hnot
          exact hs.iso_rest v h3 hnot.1 hnot.2.1 hnot.2.2.1 hnot.2.2.2.1
            hnot.2.2.2.2)
      have hle : ({q, l₁, l₂, p, e} : Finset (Fin n)).card ≤ 5 := by
        apply le_trans (Finset.card_insert_le _ _)
        apply Nat.succ_le_succ
        apply le_trans (Finset.card_insert_le _ _)
        apply Nat.succ_le_succ
        apply le_trans (Finset.card_insert_le _ _)
        apply Nat.succ_le_succ
        exact Finset.card_insert_le _ _
      omega
    obtain ⟨g, hg4, hgr, -⟩ := corner_rich_one G hsea hch hblock hIso
    exact chair_rich_kill n hn G h.no_good_triangle h.no_good_C4 hs hg4 hgr
  · exact s22_split_twoBlock G hs
  · -- C5: |Iso| ≥ 3
    have hIso : 3 ≤ (isoTwins G).card := by
      have hcov := iso_card_of_cover G ({v₀, v₁, v₂, v₃, v₄} : Finset (Fin n))
        (fun v h3 hnot => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hnot
          push Not at hnot
          exact hs.iso_rest v h3 hnot.1 hnot.2.1 hnot.2.2.1 hnot.2.2.2.1
            hnot.2.2.2.2)
      have hle : ({v₀, v₁, v₂, v₃, v₄} : Finset (Fin n)).card ≤ 5 := by
        apply le_trans (Finset.card_insert_le _ _)
        apply Nat.succ_le_succ
        apply le_trans (Finset.card_insert_le _ _)
        apply Nat.succ_le_succ
        apply le_trans (Finset.card_insert_le _ _)
        apply Nat.succ_le_succ
        exact Finset.card_insert_le _ _
      omega
    obtain ⟨g, hg4, hgr, -⟩ := corner_rich_one G hsea hch hblock hIso
    exact c5_rich_kill n hn G h.no_good_triangle h.no_good_C4 hs hg4 hgr

open Classical in
/-- **THE COMPLETE Δ ≤ 4 C0 CLOSURE**: a `ResidualCore` graph with `Δ ≤ 4` in
the cherry world (`CaseCherry`, i.e. `e(M) ≥ 2`) has `algConn G ≤ 2`,
unconditionally, for every `n ≥ 18` — combining the `e(M) = 2` closure
`caseCherry_algConn_le_two_of_sea_eM_four` with the `e(M) ≥ 3` shape closure
above. -/
theorem caseCherry_algConn_le_two_of_sea (n : ℕ) [Nonempty (Fin n)]
    (hn : 18 ≤ n) (G : SimpleGraph (Fin n)) (h : ResidualCore n G)
    (hsea : ∀ v : Fin n, G.degree v ≤ 4) (hcc : CaseCherry G) :
    algConn G ≤ 2 := by
  by_cases heM : mIncidence G = 4
  · exact caseCherry_algConn_le_two_of_sea_eM_four n hn G h hsea heM
  · have heM5 : 5 ≤ mIncidence G := by
      unfold CaseCherry at hcc
      omega
    rcases caseCherry_dichotomy n G h hcc with htb | ⟨x, z, y, hcherry, -, hblock⟩
    · exact two_block_cut_certificate G htb
    · exact two_block_cut_certificate G
        (blockedCherryCorner_close_eM_ge3 n hn G h hsea heM5 hcherry hblock)

end ACMax

/-! ## The complete `Δ ≤ 4` sea closure

Assembles the `Δ ≤ 4` sub-cases of `ResidualCore` into `residual_sea_algConn_le_two`,
dispatched by `eM_trichotomy` on `mIncidence G` (`= 2·e(M)`): `e(M) ≤ 1` (the poor
corner) via `x0_corner_close`, and `CaseCherry` (`e(M) ≥ 2`) via
`caseCherry_algConn_le_two_of_sea`. -/

namespace ACMax

open Classical in
/-- **The complete `Δ ≤ 4` closure of the general ACMAX residual.**  For every
`n ≥ 23`, a `ResidualCore` graph on `Fin n` whose maximum degree is at most `4`
has `algConn G ≤ 2`.  Assembled from the poor-corner service bound
(`x0_corner_close`) and the complete cherry closure
(`caseCherry_algConn_le_two_of_sea`) via `eM_trichotomy`. -/
theorem residual_sea_algConn_le_two (n : ℕ) [Nonempty (Fin n)] (hn : 23 ≤ n)
    (G : SimpleGraph (Fin n)) (h : ResidualCore n G)
    (hsea : ∀ v : Fin n, G.degree v ≤ 4) :
    algConn G ≤ 2 := by
  rcases eM_trichotomy G with hz | h2 | hcherry
  · -- `mIncidence = 0 ≤ 2`
    exact x0_corner_close n hn G h hsea (by
      have : mIncidence G = 0 := hz
      omega)
  · -- `mIncidence = 2 ≤ 2`
    exact x0_corner_close n hn G h hsea (by omega)
  · -- `CaseCherry` (`mIncidence ≥ 4`)
    exact caseCherry_algConn_le_two_of_sea n (by omega) G h hsea hcherry

end ACMax
