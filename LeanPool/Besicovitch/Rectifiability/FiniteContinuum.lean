/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.Rectifiability.Continuum
public import LeanPool.Besicovitch.Rectifiability.Basic
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# Finite-length continua

Compact connected subsets of the Euclidean plane with finite Hausdorff one-measure have a
Lipschitz parametrization.  This is the Eilenberg--Harrold finite-length continuum theorem.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped BoundedContinuousFunction ENNReal NNReal unitInterval

namespace LeanPool.Besicovitch

private theorem exists_short_closed_walk {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hG : G.Connected) :
    ∃ v, ∃ p : G.Walk v v, (∀ w, w ∈ p.support) ∧
      p.length ≤ 2 * (Fintype.card V - 1) := by
  classical
  induction hn : Fintype.card V using Nat.strong_induction_on generalizing V with | h n ih => ?_
  by_cases hcard : Fintype.card V = 1
  · let v : V := Classical.choice hG.nonempty
    refine ⟨v, .nil, ?_, by simp⟩
    intro w
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton]
    exact Fintype.card_le_one_iff.mp hcard.le w v
  · have hcard_two : 2 ≤ Fintype.card V := by
      have hcard_pos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr hG.nonempty
      omega
    letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hcard_two
    obtain ⟨v, hv⟩ := hG.exists_connected_induce_compl_singleton_of_finite_nontrivial
    let t : Set V := {v}ᶜ
    letI : Fintype t := Fintype.ofFinite t
    have ht_card_eq : Fintype.card t = Fintype.card V - 1 := by
      rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
      simpa [t] using Set.ncard_compl ({v} : Set V)
    have ht_card : Fintype.card t < Fintype.card V := by rw [ht_card_eq]; omega
    obtain ⟨r, p, hp, hp_len⟩ := ih (Fintype.card t) (hn ▸ ht_card) (G.induce t) hv rfl
    have hv_support : v ∈ G.support := by simp [hG.preconnected.support_eq_univ]
    obtain ⟨u, hvu⟩ : ∃ u, G.Adj v u := hv_support
    have hu_ne : u ≠ v := hvu.ne'
    let u' : t := ⟨u, by simp [t, hu_ne]⟩
    have hu'_mem : u' ∈ p.support := hp u'
    let q : G.Walk u u :=
      (p.rotate u' hu'_mem).map (SimpleGraph.Embedding.induce t).toHom
    let e : G.Walk u u := .cons hvu.symm (.cons hvu .nil)
    refine ⟨u, q.append e, ?_, ?_⟩
    · intro w
      by_cases hw : w = v
      · subst w
        exact SimpleGraph.Walk.support_subset_support_append_right q e (by simp [e])
      · let w' : t := ⟨w, by simp [t, hw]⟩
        apply SimpleGraph.Walk.support_subset_support_append_left q e
        change w ∈ ((p.rotate u' hu'_mem).map
          (SimpleGraph.Embedding.induce t).toHom).support
        rw [SimpleGraph.Walk.support_map]
        apply List.mem_map.mpr
        exact ⟨w', (SimpleGraph.Walk.mem_support_rotate_iff p u' hu'_mem).mpr (hp w'), rfl⟩
    · rw [SimpleGraph.Walk.length_append]
      have hq_len : q.length = p.length := by
        change ((p.rotate u' hu'_mem).map
          (SimpleGraph.Embedding.induce t).toHom).length = p.length
        rw [SimpleGraph.Walk.length_map, SimpleGraph.Walk.length_rotate]
      have he_len : e.length = 2 := by simp [e]
      rw [hq_len, he_len]
      rw [ht_card_eq, hn] at hp_len
      omega

/-- The polygonal chain through `x :: l`, with one unit of time allotted to each edge. -/
private def polygonalChain (x : (EuclideanSpace ℝ (Fin 2))) :
    List (EuclideanSpace ℝ (Fin 2)) → ℝ → (EuclideanSpace ℝ (Fin 2))
  | [], _ => x
  | y :: l, t =>
      if t < 1 then AffineMap.lineMap x y t else polygonalChain y l (t - 1)

@[simp]
private theorem polygonalChain_nil (x : (EuclideanSpace ℝ (Fin 2))) :
    polygonalChain x [] = fun _ ↦ x := rfl

@[simp]
private theorem polygonalChain_zero (x : (EuclideanSpace ℝ (Fin 2)))
    (l : List (EuclideanSpace ℝ (Fin 2))) :
    polygonalChain x l 0 = x := by
  cases l <;> simp [polygonalChain]

private theorem polygonalChain_cons_of_lt (x y : (EuclideanSpace ℝ (Fin 2)))
    (l : List (EuclideanSpace ℝ (Fin 2))) {t : ℝ}
    (ht : t < 1) : polygonalChain x (y :: l) t = AffineMap.lineMap x y t := by
  simp [polygonalChain, ht]

private theorem polygonalChain_cons_of_one_le (x y : (EuclideanSpace ℝ (Fin 2)))
    (l : List (EuclideanSpace ℝ (Fin 2))) {t : ℝ}
    (ht : 1 ≤ t) : polygonalChain x (y :: l) t = polygonalChain y l (t - 1) := by
  simp [polygonalChain, ht.not_gt]

private theorem polygonalChain_dist_le_crossing
    {x y : (EuclideanSpace ℝ (Fin 2))}
    {l : List (EuclideanSpace ℝ (Fin 2))} {δ : ℝ≥0}
    (hxy : dist x y ≤ δ)
    (htail : LipschitzOnWith δ (polygonalChain y l) (Icc (0 : ℝ) l.length))
    {a b : ℝ} (ha_one : a < 1) (hb_one : 1 ≤ b)
    (hb_upper : b ≤ (l.length : ℝ) + 1) :
    dist (polygonalChain x (y :: l) a) (polygonalChain x (y :: l) b) ≤ δ * dist a b := by
  have hb_sub_mem : b - 1 ∈ Icc (0 : ℝ) l.length := by
    constructor <;> linarith
  rw [polygonalChain_cons_of_lt _ _ _ ha_one,
    polygonalChain_cons_of_one_le _ _ _ hb_one]
  calc
    dist (AffineMap.lineMap x y a) (polygonalChain y l (b - 1)) ≤
        dist (AffineMap.lineMap x y a) y + dist y (polygonalChain y l (b - 1)) :=
      dist_triangle _ _ _
    _ ≤ δ * (1 - a) + δ * (b - 1) := by
      gcongr
      · rw [dist_lineMap_right, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        calc
          (1 - a) * dist x y ≤ (1 - a) * δ :=
            mul_le_mul_of_nonneg_left hxy (by linarith)
          _ = δ * (1 - a) := mul_comm _ _
      · have hdist := htail.dist_le_mul 0 (by simp) (b - 1) hb_sub_mem
        rw [Real.dist_eq, abs_of_nonpos (by linarith)] at hdist
        have hdist' : dist (polygonalChain y l 0) (polygonalChain y l (b - 1)) ≤
            δ * (b - 1) := by
          convert hdist using 1
          ring
        simpa only [polygonalChain_zero] using hdist'
    _ = δ * dist a b := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (ha_one.le.trans hb_one))]
      ring

private theorem mem_range_polygonalChain {x z : (EuclideanSpace ℝ (Fin 2))}
    {l : List (EuclideanSpace ℝ (Fin 2))} (hz : z ∈ x :: l) :
    ∃ t ∈ Icc (0 : ℝ) l.length, polygonalChain x l t = z := by
  induction l generalizing x with
  | nil =>
      simp only [List.mem_singleton] at hz
      subst z
      exact ⟨0, by simp, polygonalChain_zero x []⟩
  | cons y l ih =>
      rcases List.mem_cons.mp hz with hzx | hz
      · subst z
        refine ⟨0, ⟨le_rfl, ?_⟩, polygonalChain_zero x (y :: l)⟩
        positivity
      · obtain ⟨t, ht, htz⟩ := ih hz
        refine ⟨t + 1, ?_, ?_⟩
        · constructor
          · linarith [ht.1]
          · simpa only [List.length_cons, Nat.cast_add, Nat.cast_one, add_comm] using
              add_le_add_right ht.2 1
        · rw [polygonalChain_cons_of_one_le _ _ _ (by linarith [ht.1]),
            add_sub_cancel_right]
          exact htz

private theorem polygonalChain_lipschitzOn {x : (EuclideanSpace ℝ (Fin 2))}
    {l : List (EuclideanSpace ℝ (Fin 2))} {δ : ℝ≥0}
    (hchain : List.IsChain (fun a b : (EuclideanSpace ℝ (Fin 2)) ↦ dist a b ≤ δ) (x :: l)) :
    LipschitzOnWith δ (polygonalChain x l) (Icc (0 : ℝ) l.length) := by
  induction l generalizing x with
  | nil =>
      simpa [polygonalChain] using
        ((LipschitzWith.const (α := ℝ) x).weaken zero_le).lipschitzOnWith
  | cons y l ih =>
      rw [List.isChain_cons_cons] at hchain
      have htail := ih hchain.2
      apply LipschitzOnWith.of_dist_le_mul
      intro a ha b hb
      wlog hab : a ≤ b generalizing a b
      · simpa only [dist_comm a b, dist_comm (polygonalChain x (y :: l) a)] using
          this b hb a ha (le_of_not_ge hab)
      by_cases hb_one : b < 1
      · have ha_one : a < 1 := hab.trans_lt hb_one
        rw [polygonalChain_cons_of_lt _ _ _ ha_one,
          polygonalChain_cons_of_lt _ _ _ hb_one]
        exact (lipschitzWith_lineMap x y).weaken (by exact_mod_cast hchain.1) |>.dist_le_mul a b
      by_cases ha_one : a < 1
      · apply polygonalChain_dist_le_crossing hchain.1 htail ha_one (le_of_not_gt hb_one)
        simpa only [List.length_cons, Nat.cast_add, Nat.cast_one] using hb.2
      · have ha_one' : 1 ≤ a := le_of_not_gt ha_one
        have hb_one' : 1 ≤ b := ha_one'.trans hab
        have ha_upper : a ≤ (l.length : ℝ) + 1 := by
          simpa only [List.length_cons, Nat.cast_add, Nat.cast_one] using ha.2
        have hb_upper : b ≤ (l.length : ℝ) + 1 := by
          simpa only [List.length_cons, Nat.cast_add, Nat.cast_one] using hb.2
        rw [polygonalChain_cons_of_one_le _ _ _ ha_one',
          polygonalChain_cons_of_one_le _ _ _ hb_one']
        simpa only [Real.dist_eq, sub_sub_sub_cancel_right] using
          htail.dist_le_mul (a - 1) (by
            constructor <;> linarith) (b - 1) (by
              constructor <;> linarith)

private theorem polygonalChain_near_vertex {x : (EuclideanSpace ℝ (Fin 2))}
    {l : List (EuclideanSpace ℝ (Fin 2))} {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hchain : List.IsChain
      (fun a b : (EuclideanSpace ℝ (Fin 2)) ↦ dist a b ≤ δ) (x :: l))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) l.length) :
    ∃ z ∈ x :: l, dist (polygonalChain x l t) z ≤ δ := by
  induction l generalizing x t with
  | nil =>
      refine ⟨x, by simp, ?_⟩
      simp only [List.length_nil, Nat.cast_zero] at ht
      have : t = 0 := le_antisymm ht.2 ht.1
      simp [this, hδ]
  | cons y l ih =>
      rw [List.isChain_cons_cons] at hchain
      by_cases ht_one : t < 1
      · refine ⟨x, by simp, ?_⟩
        rw [polygonalChain_cons_of_lt _ _ _ ht_one, dist_lineMap_left,
          Real.norm_eq_abs, abs_of_nonneg ht.1]
        calc
          t * dist x y ≤ 1 * δ := mul_le_mul ht_one.le hchain.1 dist_nonneg zero_le_one
          _ = δ := one_mul δ
      · have ht_one' : 1 ≤ t := le_of_not_gt ht_one
        obtain ⟨z, hz, hdist⟩ := ih hchain.2 (t := t - 1) (by
          constructor <;> norm_num at ht ⊢ <;> linarith)
        refine ⟨z, by simp [hz], ?_⟩
        rwa [polygonalChain_cons_of_one_le _ _ _ ht_one']

/-- The polygonal chain rescaled to the unit interval. -/
private def unitPolygonalChain (x : (EuclideanSpace ℝ (Fin 2)))
    (l : List (EuclideanSpace ℝ (Fin 2))) (t : I) : (EuclideanSpace ℝ (Fin 2)) :=
  polygonalChain x l (l.length * (t : ℝ))

private theorem unitPolygonalChain_lipschitz {x : (EuclideanSpace ℝ (Fin 2))}
    {l : List (EuclideanSpace ℝ (Fin 2))} {δ : ℝ≥0}
    (hchain : List.IsChain (fun a b : (EuclideanSpace ℝ (Fin 2)) ↦ dist a b ≤ δ) (x :: l)) :
    LipschitzWith (δ * l.length) (unitPolygonalChain x l) := by
  have hpoly := polygonalChain_lipschitzOn hchain
  apply LipschitzWith.of_dist_le_mul
  intro t u
  have ht : (l.length : ℝ) * (t : ℝ) ∈ Icc (0 : ℝ) l.length := by
    constructor
    · exact mul_nonneg (Nat.cast_nonneg _) t.2.1
    · calc
        (l.length : ℝ) * (t : ℝ) ≤ l.length * 1 :=
          mul_le_mul_of_nonneg_left t.2.2 (Nat.cast_nonneg _)
        _ = l.length := mul_one _
  have hu : (l.length : ℝ) * (u : ℝ) ∈ Icc (0 : ℝ) l.length := by
    constructor
    · exact mul_nonneg (Nat.cast_nonneg _) u.2.1
    · calc
        (l.length : ℝ) * (u : ℝ) ≤ l.length * 1 :=
          mul_le_mul_of_nonneg_left u.2.2 (Nat.cast_nonneg _)
        _ = l.length := mul_one _
  calc
    dist (unitPolygonalChain x l t) (unitPolygonalChain x l u) ≤
        δ * dist ((l.length : ℝ) * (t : ℝ)) (l.length * (u : ℝ)) :=
      hpoly.dist_le_mul _ ht _ hu
    _ = (δ * l.length) * dist t u := by
      rw [Real.dist_eq, Subtype.dist_eq, ← mul_sub, abs_mul,
        abs_of_nonneg (Nat.cast_nonneg l.length)]
      rw [Real.dist_eq]
      ring

private theorem vertex_mem_range_unitPolygonalChain
    {x z : (EuclideanSpace ℝ (Fin 2))} {l : List (EuclideanSpace ℝ (Fin 2))}
    (hz : z ∈ x :: l) : z ∈ range (unitPolygonalChain x l) := by
  obtain ⟨t, ht, htz⟩ := mem_range_polygonalChain hz
  by_cases hl : l.length = 0
  · have ht_le : t ≤ 0 := by simpa [hl] using ht.2
    have ht_zero : t = 0 := le_antisymm ht_le ht.1
    have hxz : x = z := by simpa [ht_zero] using htz
    refine ⟨⟨0, by simp⟩, ?_⟩
    simpa [unitPolygonalChain, hl] using hxz
  · have hl_pos : (0 : ℝ) < l.length := by positivity
    let u : I := ⟨t / l.length, by
      constructor
      · exact div_nonneg ht.1 hl_pos.le
      · exact (div_le_one hl_pos).mpr ht.2⟩
    refine ⟨u, ?_⟩
    rw [unitPolygonalChain]
    convert htz using 1
    dsimp only [u]
    field_simp

private theorem unitPolygonalChain_near_vertex {x : (EuclideanSpace ℝ (Fin 2))}
    {l : List (EuclideanSpace ℝ (Fin 2))} {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hchain : List.IsChain
      (fun a b : (EuclideanSpace ℝ (Fin 2)) ↦ dist a b ≤ δ) (x :: l))
    (t : I) : ∃ z ∈ x :: l, dist (unitPolygonalChain x l t) z ≤ δ := by
  apply polygonalChain_near_vertex hδ hchain
  constructor
  · exact mul_nonneg (Nat.cast_nonneg _) t.2.1
  · calc
      (l.length : ℝ) * (t : ℝ) ≤ l.length * 1 :=
        mul_le_mul_of_nonneg_left t.2.2 (Nat.cast_nonneg _)
      _ = l.length := mul_one _

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A connected set reaching distance `r` from `x` has at least `r` units of length inside the
closed `r`-ball about `x`. -/
theorem hausdorffMeasure_one_inter_closedBall_ge {s : Set X} (hs : IsPreconnected s)
    {x y : X} (hx : x ∈ s) (hy : y ∈ s) {r : ℝ} (hry : r ≤ dist x y) :
    ENNReal.ofReal r ≤ μH[1] (s ∩ Metric.closedBall x r) := by
  let f : X → ℝ := fun z ↦ dist x z
  have hf : LipschitzWith 1 f := LipschitzWith.dist_right x
  have hfull : Icc 0 (dist x y) ⊆ f '' s := by
    simpa [f] using hs.intermediate_value hx hy hf.continuous.continuousOn
  have hIcc : Icc 0 r ⊆ f '' (s ∩ Metric.closedBall x r) := by
    intro t ht
    have ht' : t ∈ Icc 0 (dist x y) := ⟨ht.1, ht.2.trans hry⟩
    obtain ⟨z, hz, hzt⟩ := hfull ht'
    refine ⟨z, ⟨hz, ?_⟩, hzt⟩
    rw [Metric.mem_closedBall]
    calc
      dist z x = f z := by simp [f, dist_comm]
      _ = t := hzt
      _ ≤ r := ht.2
  calc
    ENNReal.ofReal r = μH[1] (Icc 0 r) := by
      rw [hausdorffMeasure_real, Real.volume_Icc]
      simp
    _ ≤ μH[1] (f '' (s ∩ Metric.closedBall x r)) := measure_mono hIcc
    _ ≤ μH[1] (s ∩ Metric.closedBall x r) := by
      simpa using hf.hausdorffMeasure_image_le (d := 1) zero_le_one
        (s ∩ Metric.closedBall x r)

omit [MeasurableSpace X] [BorelSpace X] in
private theorem proximityGraph_connected {s F : Set X} (hs : IsConnected s)
    (hFs : F ⊆ s) {ε : ℝ≥0} (hε : 0 < ε) (hcover : Metric.IsCover (2 * ε) s F) :
    (SimpleGraph.fromRel fun x y : F ↦ dist (x : X) y < 6 * ε).Connected := by
  let G : SimpleGraph F := SimpleGraph.fromRel fun x y ↦ dist (x : X) y < 6 * ε
  letI : Nonempty F := (hcover.nonempty hs.nonempty).to_subtype
  refine ⟨?_⟩
  intro u v
  by_contra huv
  let U : Set X := ⋃ w : F, ⋃ (_ : G.Reachable u w), Metric.ball (w : X) (3 * ε)
  let V : Set X := ⋃ w : F, ⋃ (_ : ¬G.Reachable u w), Metric.ball (w : X) (3 * ε)
  have hU : IsOpen U := isOpen_iUnion fun _ ↦ isOpen_iUnion fun _ ↦ Metric.isOpen_ball
  have hV : IsOpen V := isOpen_iUnion fun _ ↦ isOpen_iUnion fun _ ↦ Metric.isOpen_ball
  have hUV : Disjoint U V := by
    rw [Set.disjoint_left]
    intro z hzU hzV
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hzU
    obtain ⟨hup, hzp⟩ := Set.mem_iUnion.mp hp
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hzV
    obtain ⟨huq, hzq⟩ := Set.mem_iUnion.mp hq
    have hpq_ne : p ≠ q := fun hpq ↦ huq (hpq ▸ hup)
    have hpq_dist : dist (p : X) q < 6 * ε := calc
      dist (p : X) q ≤ dist (p : X) z + dist z q := dist_triangle _ _ _
      _ < 3 * ε + 3 * ε := add_lt_add (by simpa [dist_comm] using hzp) hzq
      _ = 6 * ε := by ring
    have hpq : G.Adj p q := (SimpleGraph.fromRel_adj _ _ _).mpr ⟨hpq_ne, Or.inl hpq_dist⟩
    exact huq (hup.trans hpq.reachable)
  have hsUV : s ⊆ U ∪ V := by
    intro z hz
    have hzcover := hcover.subset_iUnion_closedBall hz
    simp only [Set.mem_iUnion] at hzcover
    obtain ⟨w, hwF, hzw⟩ := hzcover
    let w' : F := ⟨w, hwF⟩
    have hzw' : z ∈ Metric.ball (w' : X) (3 * ε) := by
      rw [Metric.mem_closedBall] at hzw
      rw [Metric.mem_ball]
      have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
      norm_num at hzw ⊢
      linarith
    by_cases huw : G.Reachable u w'
    · left
      exact Set.mem_iUnion_of_mem w' (Set.mem_iUnion_of_mem huw hzw')
    · right
      exact Set.mem_iUnion_of_mem w' (Set.mem_iUnion_of_mem huw hzw')
  have huU : (u : X) ∈ U := by
    exact Set.mem_iUnion_of_mem u (Set.mem_iUnion_of_mem (.refl u) (by
      simpa only [Metric.mem_ball, dist_self] using show (0 : ℝ) < 3 * ε by positivity))
  have hvV : (v : X) ∈ V := by
    exact Set.mem_iUnion_of_mem v (Set.mem_iUnion_of_mem huv (by
      simpa only [Metric.mem_ball, dist_self] using show (0 : ℝ) < 3 * ε by positivity))
  rcases hs.isPreconnected.subset_or_subset hU hV hUV hsUV with hsU | hsV
  · exact (Set.disjoint_left.mp hUV (hsU (hFs v.2)) hvV)
  · exact (Set.disjoint_left.mp hUV huU (hsV (hFs u.2)))

private theorem card_mul_scale_le_two_measure {s F : Set X} (hs : IsConnected s)
    (hsc : IsCompact s) (hFs : F ⊆ s) (hFfin : F.Finite) {ε : ℝ≥0}
    (hsep : Metric.IsSeparated (2 * ε) F) {a b : X} (ha : a ∈ s) (hb : b ∈ s)
    (hε : (ε : ℝ) ≤ dist a b) (hmeasure : μH[1] s ≠ ∞) :
    (F.ncard : ℝ) * ε ≤ 2 * (μH[1] s).toReal := by
  let A : F → Set X := fun p ↦ s ∩ Metric.closedBall p (ε / 2)
  letI : Fintype F := hFfin.fintype
  have hA_disjoint : Pairwise (Function.onFun Disjoint A) := by
    intro p q hpq
    have hpq_sep := hsep p.2 q.2 (fun hpq' ↦ hpq (Subtype.ext hpq'))
    have hpq_sep' : (2 * (ε : ℝ)) < dist (p : X) q := by
      have := (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top
        (edist_ne_top (p : X) q)).mpr hpq_sep
      simpa [edist_dist] using this
    apply Disjoint.mono inter_subset_right inter_subset_right
    apply Metric.closedBall_disjoint_closedBall
    norm_num
    nlinarith [ε.coe_nonneg]
  have hA_measurable (p : F) : MeasurableSet (A p) :=
    hsc.isClosed.measurableSet.inter measurableSet_closedBall
  have hA_mass (p : F) : ENNReal.ofReal ((ε : ℝ) / 2) ≤ μH[1] (A p) := by
    have hfar : (ε : ℝ) / 2 ≤ dist (p : X) a ∨ (ε : ℝ) / 2 ≤ dist (p : X) b := by
      by_contra h
      push Not at h
      have htriangle := dist_triangle a (p : X) b
      rw [dist_comm a (p : X)] at htriangle
      linarith
    rcases hfar with hpa | hpb
    · exact hausdorffMeasure_one_inter_closedBall_ge hs.isPreconnected (hFs p.2) ha hpa
    · exact hausdorffMeasure_one_inter_closedBall_ge hs.isPreconnected (hFs p.2) hb hpb
  have hsum : ∑ _p : F, ENNReal.ofReal ((ε : ℝ) / 2) ≤ μH[1] s := calc
    ∑ p : F, ENNReal.ofReal ((ε : ℝ) / 2) ≤ ∑ p : F, μH[1] (A p) :=
      Finset.sum_le_sum fun p _ ↦ hA_mass p
    _ = μH[1] (⋃ p : F, A p) := by
      symm
      simpa only [tsum_fintype] using
        MeasureTheory.measure_iUnion hA_disjoint hA_measurable
    _ ≤ μH[1] s := measure_mono (by
      intro z hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨p, hp⟩ := hz
      exact hp.1)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hleft : (Fintype.card F : ℝ≥0∞) * ENNReal.ofReal ((ε : ℝ) / 2) ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) (by simp)
  have hsum' := (ENNReal.toReal_le_toReal hleft hmeasure).mpr hsum
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (by positivity)] at hsum'
  have hcard : F.ncard = Fintype.card F := by
    rw [← Nat.card_coe_set_eq F, Nat.card_eq_fintype_card]
  rw [hcard]
  linarith

omit [MeasurableSpace X] [BorelSpace X] in
private theorem exists_finite_separated_cover (s : Set X) (hsc : IsCompact s) {ε : ℝ≥0}
    (hε : 0 < ε) : ∃ F : Set X, F.Finite ∧ F ⊆ s ∧ Metric.IsSeparated (2 * ε) F ∧
      Metric.IsCover (2 * ε) s F := by
  obtain ⟨N, -, hNfin, hNcover⟩ := Metric.exists_finite_isCover_of_isCompact hε.ne' hsc
  have hexternal : Metric.externalCoveringNumber ε s ≠ ⊤ :=
    ne_top_of_le_ne_top hNfin.encard_lt_top.ne hNcover.externalCoveringNumber_le_encard
  have hpacking : Metric.packingNumber (2 * ε) s ≠ ⊤ :=
    ne_top_of_le_ne_top hexternal (Metric.packingNumber_two_mul_le_externalCoveringNumber ε s)
  let F : Set X := Metric.maximalSeparatedSet (2 * ε) s
  have hFfin : F.Finite := by
    simp only [F, Metric.maximalSeparatedSet, dif_pos hpacking]
    exact (Metric.exists_set_encard_eq_packingNumber hpacking).choose_spec.2.1
  exact ⟨F, hFfin, Metric.maximalSeparatedSet_subset, Metric.isSeparated_maximalSeparatedSet,
    Metric.isCover_maximalSeparatedSet hpacking⟩

private theorem exists_short_polygonal_tour
    {s : Set (EuclideanSpace ℝ (Fin 2))} (hs : IsConnected s)
    (hsc : IsCompact s) {a b : (EuclideanSpace ℝ (Fin 2))} (ha : a ∈ s) (hb : b ∈ s)
    (hmeasure : μH[1] s ≠ ∞) {ε : ℝ≥0} (hεpos : 0 < ε)
    (hεdiam : (ε : ℝ) ≤ dist a b) :
    ∃ v : (EuclideanSpace ℝ (Fin 2)), ∃ l : List (EuclideanSpace ℝ (Fin 2)),
      List.IsChain (fun x y : (EuclideanSpace ℝ (Fin 2)) ↦ dist x y ≤ 6 * ε) (v :: l) ∧
      (∀ x ∈ v :: l, x ∈ s) ∧
      (∀ x ∈ s, ∃ y ∈ v :: l, dist x y ≤ 2 * ε) ∧
      (6 * (ε : ℝ)) * l.length ≤ 24 * (μH[1] s).toReal := by
  obtain ⟨F, hFfin, hFs, hFsep, hFcover⟩ := exists_finite_separated_cover s hsc hεpos
  letI : Fintype F := hFfin.fintype
  let G : SimpleGraph F := SimpleGraph.fromRel fun x y ↦
    dist (x : (EuclideanSpace ℝ (Fin 2))) y < 6 * ε
  have hG : G.Connected := proximityGraph_connected hs hFs hεpos hFcover
  obtain ⟨v, p, hp, hp_len⟩ := exists_short_closed_walk G hG
  let l : List (EuclideanSpace ℝ (Fin 2)) := p.support.tail.map Subtype.val
  have hl_len : l.length = p.length := by
    simp only [l, List.length_map, List.length_tail, p.length_support]
    omega
  have hlist : (v : (EuclideanSpace ℝ (Fin 2))) :: l = p.support.map Subtype.val := by
    rw [← p.cons_tail_support]
    rfl
  have hchain : List.IsChain
      (fun x y : (EuclideanSpace ℝ (Fin 2)) ↦ dist x y ≤ 6 * ε)
      ((v : (EuclideanSpace ℝ (Fin 2))) :: l) := by
    rw [hlist, List.isChain_map]
    apply p.isChain_adj_support.imp
    intro x y hxy
    rcases (SimpleGraph.fromRel_adj _ x y).mp hxy |>.2 with hxy | hxy
    · exact hxy.le
    · simpa only [dist_comm] using hxy.le
  have hvertices : ∀ x ∈ (v : (EuclideanSpace ℝ (Fin 2))) :: l, x ∈ s := by
    intro x hx
    rw [hlist] at hx
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hx
    exact hFs w.2
  have hnet : ∀ x ∈ s,
      ∃ y ∈ (v : (EuclideanSpace ℝ (Fin 2))) :: l, dist x y ≤ 2 * ε := by
    intro x hx
    have hxcover := hFcover.subset_iUnion_closedBall hx
    simp only [Set.mem_iUnion] at hxcover
    obtain ⟨w, hwF, hxw⟩ := hxcover
    let w' : F := ⟨w, hwF⟩
    refine ⟨w, ?_, hxw⟩
    rw [hlist]
    exact List.mem_map.mpr ⟨w', hp w', rfl⟩
  have hcard := card_mul_scale_le_two_measure hs hsc hFs hFfin hFsep ha hb hεdiam hmeasure
  have hcard_eq : F.ncard = Fintype.card F := by
    rw [← Nat.card_coe_set_eq F, Nat.card_eq_fintype_card]
  rw [hcard_eq] at hcard
  have hp_len' : p.length ≤ 2 * Fintype.card F := by omega
  have hp_len_real : (p.length : ℝ) ≤ 2 * Fintype.card F := by exact_mod_cast hp_len'
  refine ⟨v, l, hchain, hvertices, hnet, ?_⟩
  calc
    (6 * (ε : ℝ)) * l.length = 6 * ε * p.length := by rw [hl_len]
    _ ≤ 6 * ε * (2 * Fintype.card F) := mul_le_mul_of_nonneg_left hp_len_real (by positivity)
    _ = 12 * ((Fintype.card F : ℝ) * ε) := by ring
    _ ≤ 12 * (2 * (μH[1] s).toReal) := mul_le_mul_of_nonneg_left hcard (by norm_num)
    _ = 24 * (μH[1] s).toReal := by ring

private theorem exists_uniform_lipschitz_approximation
    {s : Set (EuclideanSpace ℝ (Fin 2))} (hs : IsConnected s)
    (hsc : IsCompact s) {a b : (EuclideanSpace ℝ (Fin 2))} (ha : a ∈ s) (hb : b ∈ s)
    (hmeasure : μH[1] s ≠ ∞) {ε : ℝ≥0} (hεpos : 0 < ε)
    (hεdiam : (ε : ℝ) ≤ dist a b) :
    ∃ f : I → (EuclideanSpace ℝ (Fin 2)),
      LipschitzWith (Real.toNNReal (24 * (μH[1] s).toReal)) f ∧
      (∀ x ∈ s, ∃ t, dist x (f t) ≤ 2 * ε) ∧
      ∀ t, ∃ x ∈ s, dist (f t) x ≤ 6 * ε := by
  obtain ⟨v, l, hchain, hvertices, hcover, hslope⟩ :=
    exists_short_polygonal_tour hs hsc ha hb hmeasure hεpos hεdiam
  let f : I → (EuclideanSpace ℝ (Fin 2)) := unitPolygonalChain v l
  have hf_raw : LipschitzWith ((6 * ε) * l.length) f :=
    unitPolygonalChain_lipschitz hchain
  have hconstant : (6 * ε) * l.length ≤
      Real.toNNReal (24 * (μH[1] s).toReal) := by
    apply NNReal.coe_le_coe.mp
    change (6 * (ε : ℝ)) * l.length ≤
      (Real.toNNReal (24 * (μH[1] s).toReal) : ℝ)
    rw [Real.coe_toNNReal _ (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)]
    exact hslope
  have hf : LipschitzWith (Real.toNNReal (24 * (μH[1] s).toReal)) f :=
    hf_raw.weaken hconstant
  refine ⟨f, hf, ?_, ?_⟩
  · intro x hx
    obtain ⟨w, hwlist, hxw⟩ := hcover x hx
    obtain ⟨t, htw⟩ := vertex_mem_range_unitPolygonalChain hwlist
    refine ⟨t, ?_⟩
    rw [show f t = w by exact htw]
    exact hxw
  · intro t
    obtain ⟨x, hxlist, htx⟩ := unitPolygonalChain_near_vertex (by positivity) hchain t
    exact ⟨x, hvertices x hxlist, htx⟩

private theorem exists_lipschitz_uniform_subsequence
    (F : ℕ → I →ᵇ (EuclideanSpace ℝ (Fin 2))) {K : ℝ≥0}
    (hF : ∀ n, LipschitzWith K (F n)) {a : (EuclideanSpace ℝ (Fin 2))} {R : ℝ}
    (hball : ∀ n t, F n t ∈ Metric.closedBall a R) :
    ∃ g : I →ᵇ (EuclideanSpace ℝ (Fin 2)), ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Tendsto (fun n ↦ F (ψ n)) atTop (𝓝 g) ∧ LipschitzWith K g := by
  let A : Set (I →ᵇ (EuclideanSpace ℝ (Fin 2))) := range F
  have hA_equi : Equicontinuous ((↑) : A → I → (EuclideanSpace ℝ (Fin 2))) := by
    apply Metric.equicontinuous_of_continuity_modulus (fun r ↦ (K : ℝ) * r) (by
      have hmul := (continuousAt_const.mul continuousAt_id :
        ContinuousAt (fun r : ℝ ↦ (K : ℝ) * r) 0)
      change Tendsto (fun r : ℝ ↦ (K : ℝ) * r) (𝓝 0) (𝓝 ((K : ℝ) * 0)) at hmul
      simpa using hmul)
    intro x y q
    rcases q with ⟨q, ⟨n, rfl⟩⟩
    exact (hF n).dist_le_mul x y
  have hA_ball (q : I →ᵇ (EuclideanSpace ℝ (Fin 2))) (t : I) (hq : q ∈ A) :
      q t ∈ Metric.closedBall a R := by
    obtain ⟨n, rfl⟩ := hq
    exact hball n t
  have hcompact : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli (Metric.closedBall a R)
      (isCompact_closedBall a R) A hA_ball hA_equi
  have hF_closure (n : ℕ) : F n ∈ closure A := subset_closure ⟨n, rfl⟩
  obtain ⟨g, -, ψ, hψ, hψlim⟩ := hcompact.tendsto_subseq hF_closure
  refine ⟨g, ψ, hψ, hψlim, ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro t u
  apply isClosed_Iic.mem_of_tendsto ((hψlim.eval_const t).dist (hψlim.eval_const u))
  exact Filter.Eventually.of_forall fun n ↦ (hF (ψ n)).dist_le_mul t u

private theorem range_uniform_limit_subset_of_near
    {s : Set (EuclideanSpace ℝ (Fin 2))} (hs : IsClosed s)
    {ε : ℕ → ℝ≥0} (hε : Tendsto (fun n ↦ (ε n : ℝ)) atTop (𝓝 0))
    {F : ℕ → I →ᵇ (EuclideanSpace ℝ (Fin 2))}
    {g : I →ᵇ (EuclideanSpace ℝ (Fin 2))} (hF : Tendsto F atTop (𝓝 g))
    (hnear : ∀ n t, ∃ x ∈ s, dist (F n t) x ≤ 6 * ε n) : range g ⊆ s := by
  intro z hz
  obtain ⟨t, rfl⟩ := hz
  rw [← hs.closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro r hr
  have hclose := (Metric.tendsto_nhds.mp (hF.eval_const t)) (r / 2) (half_pos hr)
  have hsmall := hε.eventually_lt_const (show (0 : ℝ) < r / 12 by positivity)
  obtain ⟨n, hnclose, hnsmall⟩ := (hclose.and hsmall).exists
  obtain ⟨x, hxs, hdist⟩ := hnear n t
  refine ⟨x, hxs, ?_⟩
  calc
    dist (g t) x ≤ dist (g t) (F n t) + dist (F n t) x := dist_triangle _ _ _
    _ < r / 2 + r / 2 :=
      add_lt_add (by simpa [dist_comm] using hnclose) (hdist.trans_lt (by nlinarith [hnsmall]))
    _ = r := add_halves r

private theorem subset_range_uniform_limit_of_dense
    {s : Set (EuclideanSpace ℝ (Fin 2))} {ε : ℕ → ℝ≥0}
    (hε : Tendsto (fun n ↦ (ε n : ℝ)) atTop (𝓝 0))
    {F : ℕ → I →ᵇ (EuclideanSpace ℝ (Fin 2))}
    {g : I →ᵇ (EuclideanSpace ℝ (Fin 2))} (hF : Tendsto F atTop (𝓝 g))
    (hcover : ∀ n x, x ∈ s → ∃ t, dist x (F n t) ≤ 2 * ε n) : s ⊆ range g := by
  intro x hx
  let t : ℕ → I := fun n ↦ (hcover n x hx).choose
  have ht_dist (n : ℕ) : dist x (F n (t n)) ≤ 2 * ε n := (hcover n x hx).choose_spec
  obtain ⟨u, φ, hφ, hφlim⟩ := CompactSpace.tendsto_subseq t
  have hcurve_lim : Tendsto (fun n ↦ F (φ n) (t (φ n))) atTop (𝓝 (g u)) :=
    (hF.comp hφ.tendsto_atTop).eval hφlim
  have hpoint_lim : Tendsto (fun n ↦ F (φ n) (t (φ n))) atTop (𝓝 x) := by
    rw [Metric.tendsto_nhds]
    intro r hr
    have hsmall := (hε.comp hφ.tendsto_atTop).eventually_lt_const
      (show (0 : ℝ) < r / 2 by positivity)
    filter_upwards [hsmall] with n hn
    change (ε (φ n) : ℝ) < r / 2 at hn
    calc
      dist (F (φ n) (t (φ n))) x = dist x (F (φ n) (t (φ n))) := dist_comm _ _
      _ ≤ 2 * ε (φ n) := ht_dist (φ n)
      _ < r := by linarith
  exact ⟨u, tendsto_nhds_unique hcurve_lim hpoint_lim⟩

private theorem exists_unitInterval_lipschitz_surjection_of_not_subsingleton
    {s : Set (EuclideanSpace ℝ (Fin 2))} (hs : IsConnected s)
    (hsc : IsCompact s) (hss : ¬s.Subsingleton)
    (hmeasure : μH[1] s ≠ ∞) :
    ∃ f : I → (EuclideanSpace ℝ (Fin 2)),
      LipschitzWith (Real.toNNReal (24 * (μH[1] s).toReal)) f ∧ range f = s := by
  push Not at hss
  obtain ⟨a, ha, b, hb, hab⟩ := hss
  let ε : ℕ → ℝ≥0 := fun n ↦ nndist a b / (n + 1)
  have hεpos (n : ℕ) : 0 < ε n := by
    apply div_pos
    · apply NNReal.coe_pos.mp
      simpa only [coe_nndist] using dist_pos.mpr hab
    · positivity
  have hεdiam (n : ℕ) : (ε n : ℝ) ≤ dist a b := by
    simp only [ε, NNReal.coe_div, coe_nndist]
    exact div_le_self dist_nonneg (by norm_num)
  have hεlim : Filter.Tendsto (fun n ↦ (ε n : ℝ)) Filter.atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (dist a b)
    convert h using 1
    · ext n
      norm_num [ε, div_eq_mul_inv]
    · simp
  have hexists (n : ℕ) :=
    exists_uniform_lipschitz_approximation hs hsc ha hb hmeasure (hεpos n) (hεdiam n)
  choose f hf hcover hnear using hexists
  let K : ℝ≥0 := Real.toNNReal (24 * (μH[1] s).toReal)
  let F : ℕ → I →ᵇ (EuclideanSpace ℝ (Fin 2)) := fun n ↦
    BoundedContinuousFunction.mkOfCompact ⟨f n, (hf n).continuous⟩
  obtain ⟨R, hR⟩ := hsc.isBounded.subset_closedBall a
  have hdR : dist a b ≤ R := by
    have := hR hb
    simpa only [Metric.mem_closedBall, dist_comm] using this
  have hF_ball (n : ℕ) (t : I) : F n t ∈ Metric.closedBall a (7 * R) := by
    obtain ⟨x, hx, hfx⟩ := hnear n t
    rw [Metric.mem_closedBall]
    calc
      dist (F n t) a ≤ dist (F n t) x + dist x a := dist_triangle _ _ _
      _ ≤ 6 * ε n + R := add_le_add hfx (hR hx)
      _ ≤ 6 * dist a b + R := by gcongr; exact hεdiam n
      _ ≤ 7 * R := by linarith
  have hFlip (n : ℕ) : LipschitzWith K (F n) := hf n
  obtain ⟨g, ψ, hψ, hψlim, hglip⟩ :=
    exists_lipschitz_uniform_subsequence F hFlip hF_ball
  have hεψ : Tendsto (fun n ↦ (ε (ψ n) : ℝ)) atTop (𝓝 0) :=
    hεlim.comp hψ.tendsto_atTop
  have hgs : range g ⊆ s := range_uniform_limit_subset_of_near hsc.isClosed hεψ hψlim
    (fun n ↦ hnear (ψ n))
  have hsg : s ⊆ range g := subset_range_uniform_limit_of_dense hεψ hψlim
    (fun n ↦ hcover (ψ n))
  exact ⟨g, hglip, Set.Subset.antisymm hgs hsg⟩

/-- **Eilenberg--Harrold.** A compact connected planar set of finite length is the range of a
global Lipschitz curve. -/
theorem IsConnected.exists_lipschitzWith_range_eq
    {s : Set (EuclideanSpace ℝ (Fin 2))} (hs : IsConnected s)
    (hsc : IsCompact s) (hmeasure : μH[1] s ≠ ∞) :
    ∃ K : ℝ≥0, ∃ f : ℝ → (EuclideanSpace ℝ (Fin 2)),
      LipschitzWith K f ∧ range f = s := by
  by_cases hss : s.Subsingleton
  · obtain ⟨a, ha⟩ := hs.nonempty
    have hs_eq : s = {a} := Set.eq_singleton_iff_unique_mem.mpr ⟨ha, fun _ hx ↦ hss hx ha⟩
    refine ⟨0, fun _ ↦ a, LipschitzWith.const a, ?_⟩
    simp [hs_eq]
  · obtain ⟨g, hg, hgs⟩ :=
      exists_unitInterval_lipschitz_surjection_of_not_subsingleton hs hsc hss hmeasure
    let f : ℝ → (EuclideanSpace ℝ (Fin 2)) := g ∘ Set.projIcc 0 1 zero_le_one
    refine ⟨Real.toNNReal (24 * (μH[1] s).toReal), f, ?_, ?_⟩
    · simpa only [mul_one] using hg.comp (LipschitzWith.projIcc zero_le_one)
    · change range (g ∘ Set.projIcc 0 1 zero_le_one) = s
      rw [Set.range_comp, Set.range_projIcc, image_univ, hgs]

/-- A compact connected planar set of finite Hausdorff one-measure is countably
one-rectifiable. -/
theorem IsConnected.isCountablyOneRectifiable_of_isCompact {s : Set (EuclideanSpace ℝ (Fin 2))}
    (hs : IsConnected s) (hsc : IsCompact s) (hmeasure : μH[1] s ≠ ∞) :
    IsCountablyOneRectifiable s := by
  obtain ⟨K, f, hf, hfs⟩ := IsConnected.exists_lipschitzWith_range_eq hs hsc hmeasure
  refine ⟨fun _ ↦ f, fun _ ↦ ⟨K, hf⟩, ?_⟩
  simp only [hfs]
  rw [Set.iUnion_const, sdiff_self, measure_empty]

end LeanPool.Besicovitch
