/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Descriptive.CantorAntichain
import LeanPool.InfinitaryLogic.Descriptive.PerfectAntichain
import LeanPool.InfinitaryLogic.Descriptive.CountingDichotomy
import Mathlib.Topology.MetricSpace.Perfect
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.MeasureTheory.Constructions.Polish.Basic
/-!
# Silver-Burgess Dichotomy for Borel Equivalence Relations

This file proves the Silver-Burgess splitting lemmas and Silver's theorem for closed
equivalence relations on Polish spaces; the Borel case and the full
`SilverBurgessDichotomy` for standard Borel spaces are derived in
`GandyHarrington.lean` (sorry-free since 2026-06-10).

## Main Results

The perfect-set and Polish-quotient cardinal facts this file used to open with now live in
`InfinitaryLogic/Descriptive/PerfectAntichain.lean` (`Perfect.mk_eq_continuum`,
`continuum_classes_of_perfect_transversal`, and the three companions).  The names are the same,
but the statements are not identical: several now assume less than they did here — in
particular `continuum_classes_of_perfect_transversal` no longer requires second countability.
None of them mentions a dichotomy or a splitting hypothesis.

- `splitting_lemma_closed`: Closed equiv relation with uncountably many classes splits
  into disjoint closed pieces, each uncountable, cross-inequivalent.
- `splitting_lemma_closed_small_diam`: the same splitting with diameter ≤ ε control
  (shrink around a condensation point first).
- `silver_core_closed`: Silver's theorem for closed equivalence relations on Polish spaces,
  obtained by feeding `splitting_lemma_closed_small_diam` to the abstract Cantor-antichain
  builder `CantorScheme.exists_antichain_map_of_splitting`
  (`InfinitaryLogic/Descriptive/CantorAntichain.lean`).
- `silver_core_polish` and `silverBurgessDichotomy` live in `GandyHarrington.lean`,
  derived from `gandy_harrington_for_relation` (proved via the category route in
  `SilverCategoryRoute.lean`).
-/

open Cardinal Set MeasureTheory

universe u v

/-! ### Splitting lemma for closed equivalence relations -/

/-- A condensation point for E-classes in U: every open neighborhood meets
uncountably many E-classes. -/
def IsClassCondensationPt (r : Setoid α) [TopologicalSpace α] (U : Set α) (x : α) : Prop :=
  x ∈ U ∧ ∀ V : Set α, IsOpen V → x ∈ V → ¬(Set.Countable {q : Quotient r | ∃ y ∈ U ∩ V, ⟦y⟧ = q})

/-- In a second-countable space, if U meets uncountably many E-classes,
there exist condensation points in uncountably many classes. -/
theorem exists_classCondensationPt_of_uncountable {α : Type u}
    [TopologicalSpace α] [SecondCountableTopology α]
    (r : Setoid α) {U : Set α}
    (hunc : ¬(Set.Countable {q : Quotient r | ∃ y ∈ U, ⟦y⟧ = q})) :
    ∃ x, IsClassCondensationPt r U x := by
  -- By contradiction: if no condensation point, every class in U is covered
  -- by a countable-basis element witnessing countability, giving a contradiction.
  by_contra h_no_cond
  push Not at h_no_cond
  -- h_no_cond : ∀ x, ¬IsClassCondensationPt r U x
  -- i.e., ∀ x, x ∉ U ∨ ∃ V, IsOpen V ∧ x ∈ V ∧ Countable {q | ∃ y ∈ U ∩ V, ⟦y⟧ = q}
  simp only [IsClassCondensationPt, not_and_or, not_forall, not_not] at h_no_cond
  -- Get a countable topological basis
  obtain ⟨basis, hbasis_count, _, hbasis⟩ := TopologicalSpace.exists_countable_basis α
  -- For each y ∈ U, find a basis element containing y with countably many classes
  have h_cover : ∀ y ∈ U, ∃ B ∈ basis, y ∈ B ∧
      Set.Countable {q : Quotient r | ∃ z ∈ U ∩ B, ⟦z⟧ = q} := by
    intro y hy
    rcases h_no_cond y with h_notU | ⟨V, hV_open, hV_mem, hV_count⟩
    · exact absurd hy h_notU
    · obtain ⟨B, hB_mem, hB_y, hB_sub⟩ := hbasis.exists_subset_of_mem_open hV_mem hV_open
      refine ⟨B, hB_mem, hB_y, hV_count.mono (fun q hq => ?_)⟩
      obtain ⟨z, ⟨hz_U, hz_B⟩, hz_eq⟩ := hq
      exact ⟨z, ⟨hz_U, hB_sub hz_B⟩, hz_eq⟩
  -- The classes meeting U are covered by the countable union over basis elements
  apply hunc
  have h_sub : {q : Quotient r | ∃ y ∈ U, ⟦y⟧ = q} ⊆
      ⋃ B ∈ basis, {q : Quotient r | ∃ z ∈ U ∩ B, ⟦z⟧ = q} := by
    intro q ⟨y, hy_U, hy_eq⟩
    obtain ⟨B, hB_mem, hB_y, _⟩ := h_cover y hy_U
    exact Set.mem_biUnion hB_mem ⟨y, ⟨hy_U, hB_y⟩, hy_eq⟩
  -- Each piece in the union is countable (by the cover property, we only need
  -- that it's a subset of countable sets). Actually, we use the countable union directly.
  -- Define the "countable" basis elements
  set S := {B ∈ basis | Set.Countable {q : Quotient r | ∃ z ∈ U ∩ B, ⟦z⟧ = q}} with hS_def
  -- Refine the subset to use only S
  have h_sub' : {q : Quotient r | ∃ y ∈ U, ⟦y⟧ = q} ⊆
      ⋃ B ∈ S, {q : Quotient r | ∃ z ∈ U ∩ B, ⟦z⟧ = q} := by
    intro q ⟨y, hy_U, hy_eq⟩
    obtain ⟨B, hB_mem, hB_y, hB_count⟩ := h_cover y hy_U
    exact Set.mem_biUnion (show B ∈ S from ⟨hB_mem, hB_count⟩) ⟨y, ⟨hy_U, hB_y⟩, hy_eq⟩
  exact ((hbasis_count.mono (fun _ h => h.1)).biUnion (fun B hB => hB.2)).mono h_sub'

/-- In a second-countable space, if U meets uncountably many E-classes,
then uncountably many classes have a condensation point representative in U. -/
theorem uncountable_classCondensationPt_classes {α : Type u}
    [TopologicalSpace α] [SecondCountableTopology α]
    (r : Setoid α) {U : Set α}
    (hunc : ¬(Set.Countable {q : Quotient r | ∃ y ∈ U, ⟦y⟧ = q})) :
    ¬(Set.Countable {q : Quotient r | ∃ x, IsClassCondensationPt r U x ∧ ⟦x⟧ = q}) := by
  -- The set of non-condensation classes is countable (same argument as above).
  obtain ⟨basis, hbasis_count, _, hbasis⟩ := TopologicalSpace.exists_countable_basis α
  -- Non-condensation classes: those where every representative in U has a "small" basis nbhd
  set condensClasses := {q : Quotient r | ∃ x, IsClassCondensationPt r U x ∧ ⟦x⟧ = q}
  set allClasses := {q : Quotient r | ∃ y ∈ U, ⟦y⟧ = q}
  -- Show allClasses \ condensClasses is countable
  suffices h : (allClasses \ condensClasses).Countable by
    intro h_cond_count
    exact hunc (h.union h_cond_count |>.mono (Set.subset_union_left.trans
      (by intro q; simp only [Set.mem_union, Set.mem_sdiff]; tauto)))
  -- For each q ∈ allClasses \ condensClasses, every representative y ∈ U of q
  -- is NOT a condensation point, so has a basis nbhd with countably many classes.
  -- Key: allClasses \ condensClasses ⊆ ⋃ (B ∈ "countable" basis elts), classes(U ∩ B)
  suffices h_sub : allClasses \ condensClasses ⊆
      ⋃ (B : Set α) (_ : B ∈ basis ∧ Set.Countable {q : Quotient r | ∃ z ∈ U ∩ B, ⟦z⟧ = q}),
        {q : Quotient r | ∃ z ∈ U ∩ B, ⟦z⟧ = q} by
    have hS_count : Set.Countable {B : Set α | B ∈ basis ∧
        Set.Countable {q : Quotient r | ∃ z ∈ U ∩ B, ⟦z⟧ = q}} :=
      hbasis_count.mono (fun _ h => h.1)
    exact (hS_count.biUnion (fun B hB => hB.2)).mono h_sub
  intro q ⟨hq_all, hq_not_cond⟩
  obtain ⟨y, hy_U, hy_eq⟩ := hq_all
  -- y is not a condensation point
  simp only [condensClasses, Set.mem_ofPred_eq, not_exists, not_and] at hq_not_cond
  have h_not_cond : ¬IsClassCondensationPt r U y := by
    intro h_cond
    exact hq_not_cond y h_cond hy_eq
  simp only [IsClassCondensationPt, not_and_or, not_forall, not_not] at h_not_cond
  rcases h_not_cond with h_notU | ⟨V, hV_open, hV_mem, hV_count⟩
  · exact absurd hy_U h_notU
  · obtain ⟨B, hB_mem, hB_y, hB_sub⟩ := hbasis.exists_subset_of_mem_open hV_mem hV_open
    have hB_count : Set.Countable {q : Quotient r | ∃ z ∈ U ∩ B, ⟦z⟧ = q} := by
      exact hV_count.mono (fun q hq => by
        obtain ⟨z, ⟨hz_U, hz_B⟩, hz_eq⟩ := hq
        exact ⟨z, ⟨hz_U, hB_sub hz_B⟩, hz_eq⟩)
    exact Set.mem_biUnion ⟨hB_mem, hB_count⟩ ⟨y, ⟨hy_U, hB_y⟩, hy_eq⟩

/-- **Splitting lemma** for closed equivalence relations on metric spaces.
If a closed set U meets uncountably many classes of a closed equivalence
relation, it contains disjoint closed subsets each meeting uncountably
many classes with no cross-equivalence. -/
theorem splitting_lemma_closed {α : Type u}
    [MetricSpace α] [SecondCountableTopology α]
    (r : Setoid α) (hclosed_r : IsClosed {p : α × α | r.r p.1 p.2})
    {U : Set α} (hU : IsClosed U)
    (hunc : ¬(Set.Countable {q : Quotient r | ∃ y ∈ U, ⟦y⟧ = q})) :
    ∃ U₀ U₁ : Set α,
      IsClosed U₀ ∧ IsClosed U₁ ∧
      U₀ ⊆ U ∧ U₁ ⊆ U ∧
      Disjoint (U₀ : Set α) U₁ ∧
      ¬(Set.Countable {q : Quotient r | ∃ y ∈ U₀, ⟦y⟧ = q}) ∧
      ¬(Set.Countable {q : Quotient r | ∃ y ∈ U₁, ⟦y⟧ = q}) ∧
      (∀ x ∈ U₀, ∀ y ∈ U₁, ¬ r.r x y) := by
  -- Step 1: Get uncountably many condensation classes
  have hunc_cond := uncountable_classCondensationPt_classes r hunc
  -- Step 2: Pick two condensation points in DIFFERENT classes
  -- First pick one condensation point
  have hne : (({q : Quotient r | ∃ x, IsClassCondensationPt r U x ∧ ⟦x⟧ = q}) : Set _).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    exact hunc_cond (h ▸ Set.countable_empty)
  obtain ⟨q₀, x₀, hx₀_cond, hx₀_eq⟩ := hne
  -- Now pick a second condensation point in a different class
  have hne2 : ({q : Quotient r | ∃ x, IsClassCondensationPt r U x ∧ ⟦x⟧ = q} \ {q₀}).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have : {q : Quotient r | ∃ x, IsClassCondensationPt r U x ∧ ⟦x⟧ = q} ⊆ {q₀} := by
      intro q hq
      by_contra hq_ne
      exact (h ▸ (Set.mem_empty_iff_false q).mp : ¬_) ⟨hq, hq_ne⟩
    exact hunc_cond ((Set.countable_singleton q₀).mono this)
  obtain ⟨q₁, ⟨x₁, hx₁_cond, hx₁_eq⟩, hq₁_ne⟩ := hne2
  simp only [Set.mem_singleton_iff] at hq₁_ne
  -- x₀ and x₁ are in different classes
  have hx₀_mem : x₀ ∈ U := hx₀_cond.1
  have hx₁_mem : x₁ ∈ U := hx₁_cond.1
  have h_not_equiv : ¬ r.r x₀ x₁ := by
    intro h_eq
    apply hq₁_ne
    rw [← hx₀_eq, ← hx₁_eq]
    exact Quotient.sound (r.iseqv.symm h_eq)
  -- Step 3: Since E is closed, Eᶜ is open and contains (x₀, x₁)
  have h_open_compl : IsOpen {p : α × α | r.r p.1 p.2}ᶜ := hclosed_r.isOpen_compl
  have h_mem_compl : (x₀, x₁) ∈ {p : α × α | r.r p.1 p.2}ᶜ := h_not_equiv
  -- Use product topology to get open neighborhoods V₀, V₁
  obtain ⟨V₀, V₁, hV₀_open, hV₁_open, hV₀_mem, hV₁_mem, hV_prod⟩ :=
    isOpen_prod_iff.mp h_open_compl x₀ x₁ h_mem_compl
  -- Step 4: Use metric structure to get ε-balls inside V₀, V₁
  obtain ⟨ε₀, hε₀_pos, hε₀_sub⟩ := Metric.isOpen_iff.mp hV₀_open x₀ hV₀_mem
  obtain ⟨ε₁, hε₁_pos, hε₁_sub⟩ := Metric.isOpen_iff.mp hV₁_open x₁ hV₁_mem
  -- Positive distance between x₀ and x₁ (since they're in different classes, and in a metric space)
  -- Actually, we need x₀ ≠ x₁. Since they're in different classes, they can't be equal.
  have hx_ne : x₀ ≠ x₁ := by
    intro h_eq
    exact h_not_equiv (h_eq ▸ r.iseqv.refl x₀)
  have h_dist_pos : 0 < dist x₀ x₁ := dist_pos.mpr hx_ne
  -- Pick ε strictly less than ε₀, ε₁, and dist/3 for all conditions
  set ε := min (min (ε₀ / 2) (ε₁ / 2)) (dist x₀ x₁ / 4) with hε_def
  have hε_pos : 0 < ε :=
    lt_min (lt_min (half_pos hε₀_pos) (half_pos hε₁_pos)) (div_pos h_dist_pos (by norm_num))
  have hε_lt_ε₀ : ε < ε₀ :=
    lt_of_le_of_lt (min_le_left _ _) (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε₀_pos))
  have hε_lt_ε₁ : ε < ε₁ :=
    lt_of_le_of_lt (min_le_left _ _) (lt_of_le_of_lt (min_le_right _ _) (half_lt_self hε₁_pos))
  have hε_le_dist4 : ε ≤ dist x₀ x₁ / 4 := min_le_right _ _
  -- Define U₀ and U₁
  refine ⟨U ∩ Metric.closedBall x₀ ε, U ∩ Metric.closedBall x₁ ε, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- IsClosed U₀
  · exact hU.inter Metric.isClosed_closedBall
  -- IsClosed U₁
  · exact hU.inter Metric.isClosed_closedBall
  -- U₀ ⊆ U
  · exact Set.inter_subset_left
  -- U₁ ⊆ U
  · exact Set.inter_subset_left
  -- Disjoint U₀ U₁
  · have h_disj : Disjoint (Metric.closedBall x₀ ε) (Metric.closedBall x₁ ε) := by
      apply Metric.closedBall_disjoint_closedBall
      calc ε + ε ≤ dist x₀ x₁ / 4 + dist x₀ x₁ / 4 := add_le_add hε_le_dist4 hε_le_dist4
        _ = dist x₀ x₁ / 2 := by ring
        _ < dist x₀ x₁ := half_lt_self h_dist_pos
    exact h_disj.mono Set.inter_subset_right Set.inter_subset_right
  -- Uncountably many classes in U₀
  · have hball_open₀ : IsOpen (Metric.ball x₀ ε) := Metric.isOpen_ball
    have hball_mem₀ : x₀ ∈ Metric.ball x₀ ε := Metric.mem_ball_self hε_pos
    -- x₀ is a condensation point, so U ∩ ball x₀ ε meets uncountably many classes
    have hunc₀ := hx₀_cond.2 _ hball_open₀ hball_mem₀
    -- classes meeting U ∩ ball x₀ ε ⊆ classes meeting U ∩ closedBall x₀ ε
    exact fun h_count => hunc₀ (h_count.mono (fun q hq => by
      obtain ⟨z, ⟨hz_U, hz_ball⟩, hz_eq⟩ := hq
      exact ⟨z, ⟨hz_U, Metric.ball_subset_closedBall hz_ball⟩, hz_eq⟩))
  -- Uncountably many classes in U₁
  · have hball_open₁ : IsOpen (Metric.ball x₁ ε) := Metric.isOpen_ball
    have hball_mem₁ : x₁ ∈ Metric.ball x₁ ε := Metric.mem_ball_self hε_pos
    have hunc₁ := hx₁_cond.2 _ hball_open₁ hball_mem₁
    exact fun h_count => hunc₁ (h_count.mono (fun q hq => by
      obtain ⟨z, ⟨hz_U, hz_ball⟩, hz_eq⟩ := hq
      exact ⟨z, ⟨hz_U, Metric.ball_subset_closedBall hz_ball⟩, hz_eq⟩))
  -- Cross-disjointness: ∀ a ∈ U₀, ∀ b ∈ U₁, ¬ r.r a b
  · intro a ⟨_, ha_ball⟩ b ⟨_, hb_ball⟩ h_r
    -- a ∈ closedBall x₀ ε ⊆ ball x₀ ε₀ ⊆ V₀
    have ha_V₀ : a ∈ V₀ := hε₀_sub (Metric.closedBall_subset_ball hε_lt_ε₀ ha_ball)
    -- b ∈ closedBall x₁ ε ⊆ ball x₁ ε₁ ⊆ V₁
    have hb_V₁ : b ∈ V₁ := hε₁_sub (Metric.closedBall_subset_ball hε_lt_ε₁ hb_ball)
    -- (a, b) ∈ V₀ ×ˢ V₁ ⊆ Eᶜ, so ¬ r.r a b
    exact hV_prod (Set.mk_mem_prod ha_V₀ hb_V₁) h_r

/-- **Small-diameter splitting** for closed equivalence relations: a closed set meeting
uncountably many classes splits into two disjoint closed pieces of diameter ≤ ε, each
nonempty, each meeting uncountably many classes, with no cross-equivalence. Obtained from
`splitting_lemma_closed` by first shrinking around a condensation point. -/
theorem splitting_lemma_closed_small_diam {α : Type u}
    [MetricSpace α] [SecondCountableTopology α]
    (r : Setoid α) (hclosed_r : IsClosed {p : α × α | r.r p.1 p.2})
    {E : Set α} (hE_cl : IsClosed E)
    (hE_unc : ¬Set.Countable {q : Quotient r | ∃ y ∈ E, ⟦y⟧ = q})
    {ε : ENNReal} (hε : 0 < ε) :
    ∃ E₀ E₁ : Set α,
      (IsClosed E₀ ∧ E₀.Nonempty ∧ E₀ ⊆ E ∧ Metric.ediam E₀ ≤ ε ∧
        ¬Set.Countable {q : Quotient r | ∃ y ∈ E₀, ⟦y⟧ = q}) ∧
      (IsClosed E₁ ∧ E₁.Nonempty ∧ E₁ ⊆ E ∧ Metric.ediam E₁ ≤ ε ∧
        ¬Set.Countable {q : Quotient r | ∃ y ∈ E₁, ⟦y⟧ = q}) ∧
      Disjoint E₀ E₁ ∧
      (∀ x ∈ E₀, ∀ y ∈ E₁, ¬ r.r x y) := by
  -- Pick a condensation point
  obtain ⟨x₀, hx₀_mem, hx₀_cond⟩ :=
    exists_classCondensationPt_of_uncountable r hE_unc
  -- Get a real radius δ > 0 with 2 * ofReal δ ≤ ε
  obtain ⟨δ, hδ_pos, hδ_bound⟩ : ∃ δ : ℝ, 0 < δ ∧ 2 * ENNReal.ofReal δ ≤ ε := by
    by_cases hε_top : ε = ⊤
    · exact ⟨1, one_pos, by simp [hε_top]⟩
    · have hε2_ne : ε / 2 ≠ ⊤ := ENNReal.div_ne_top hε_top (by norm_num)
      have hε2_pos : 0 < ε / 2 := ENNReal.div_pos hε.ne' (by norm_num)
      refine ⟨(ε / 2).toReal, ENNReal.toReal_pos hε2_pos.ne' hε2_ne, ?_⟩
      rw [ENNReal.ofReal_toReal hε2_ne, two_mul, ENNReal.add_halves]
  -- Shrink to E ∩ closedBall x₀ δ; this is still closed and uncountable-classes
  set E' := E ∩ Metric.closedBall x₀ δ with hE'_def
  have hE'_cl : IsClosed E' := hE_cl.inter Metric.isClosed_closedBall
  have hE'_unc : ¬Set.Countable {q : Quotient r | ∃ y ∈ E', ⟦y⟧ = q} := by
    intro h_count
    apply hx₀_cond (Metric.ball x₀ δ) Metric.isOpen_ball (Metric.mem_ball_self hδ_pos)
    exact h_count.mono fun q hq => by
      obtain ⟨y, ⟨hy_E, hy_ball⟩, hy_eq⟩ := hq
      exact ⟨y, ⟨hy_E, Metric.ball_subset_closedBall hy_ball⟩, hy_eq⟩
  -- Split E'
  obtain ⟨U₀, U₁, hU₀_cl, hU₁_cl, hU₀_sub, hU₁_sub, hU_disj,
    hU₀_unc, hU₁_unc, hU_cross⟩ :=
    splitting_lemma_closed r hclosed_r hE'_cl hE'_unc
  -- U₀, U₁ ⊆ E' ⊆ closedBall x₀ δ, so ediam ≤ 2δ ≤ ε
  -- `EMetric.closedBall` moved to `Metric.closedEBall` and `Metric.emetric_closedBall` was
  -- renamed to `Metric.closedEBall_ofReal`.
  have hball_eq : Metric.closedBall x₀ δ = Metric.closedEBall x₀ (ENNReal.ofReal δ) :=
    (Metric.closedEBall_ofReal hδ_pos.le).symm
  have hball_diam : Metric.ediam (Metric.closedBall x₀ δ) ≤ 2 * ENNReal.ofReal δ := by
    rw [hball_eq]; exact Metric.ediam_closedEBall_le
  have hU₀_diam : Metric.ediam U₀ ≤ ε :=
    (Metric.ediam_mono (hU₀_sub.trans Set.inter_subset_right)).trans
      (hball_diam.trans hδ_bound)
  have hU₁_diam : Metric.ediam U₁ ≤ ε :=
    (Metric.ediam_mono (hU₁_sub.trans Set.inter_subset_right)).trans
      (hball_diam.trans hδ_bound)
  have hU₀_ne : U₀.Nonempty := by
    by_contra h; rw [Set.not_nonempty_iff_eq_empty] at h
    exact hU₀_unc (h ▸ by simp [Set.countable_empty])
  have hU₁_ne : U₁.Nonempty := by
    by_contra h; rw [Set.not_nonempty_iff_eq_empty] at h
    exact hU₁_unc (h ▸ by simp [Set.countable_empty])
  exact ⟨U₀, U₁,
    ⟨hU₀_cl, hU₀_ne, hU₀_sub.trans Set.inter_subset_left, hU₀_diam, hU₀_unc⟩,
    ⟨hU₁_cl, hU₁_ne, hU₁_sub.trans Set.inter_subset_left, hU₁_diam, hU₁_unc⟩,
    hU_disj, hU_cross⟩

/-! ### Core Silver theorem -/

/-- **Silver's theorem** (core Polish space version, for closed equivalence
relations): A closed equivalence relation on a Polish space has countably many
equivalence classes, or admits a continuous injection from Cantor space whose
images are pairwise inequivalent. -/
theorem silver_core_closed {α : Type u}
    [MetricSpace α] [CompleteSpace α] [SecondCountableTopology α]
    (r : Setoid α) (hclosed_r : IsClosed {p : α × α | r.r p.1 p.2}) :
    Countable (Quotient r) ∨
      ∃ f : (ℕ → Bool) → α,
        Continuous f ∧ Function.Injective f ∧
        ∀ a b, a ≠ b → ¬ r.r (f a) (f b) := by
  -- Case split: countable or uncountable quotient
  by_cases hcount : Set.Countable {q : Quotient r | ∃ y ∈ Set.univ, ⟦y⟧ = q}
  · left
    have : Set.Countable (Set.univ : Set (Quotient r)) := by
      convert hcount using 1; ext q; simp [Quotient.exists_rep]
    exact Set.countable_univ_iff.mp this
  · right
    -- Instantiate the abstract Cantor-antichain builder with the largeness predicate
    -- "closed and meeting uncountably many classes"; the splitting hypothesis is
    -- `splitting_lemma_closed_small_diam`.
    obtain ⟨f, hcont, hinj, -, hanti⟩ :=
      CantorScheme.exists_antichain_map_of_splitting r
        (P := fun F => IsClosed F ∧
          ¬Set.Countable {q : Quotient r | ∃ y ∈ F, ⟦y⟧ = q})
        (fun F hF => hF.1)
        (fun F hF => by
          by_contra h
          rw [Set.not_nonempty_iff_eq_empty] at h
          exact hF.2 (h ▸ by simp [Set.countable_empty]))
        ⟨isClosed_univ, hcount⟩
        (fun F hF ε hε => by
          obtain ⟨E₀, E₁, ⟨h0cl, -, h0sub, h0diam, h0unc⟩,
            ⟨h1cl, -, h1sub, h1diam, h1unc⟩, -, hcross⟩ :=
            splitting_lemma_closed_small_diam r hclosed_r hF.1 hF.2 hε
          exact ⟨E₀, E₁, ⟨h0cl, h0unc⟩, ⟨h1cl, h1unc⟩,
            h0sub, h1sub, h0diam, h1diam, hcross⟩)
    exact ⟨f, hcont, hinj, hanti⟩

-- silver_core_polish and silverBurgessDichotomy are in GandyHarrington.lean
-- (which imports this file and provides the Borel→closed reduction).

-- silverBurgessDichotomy is in GandyHarrington.lean
