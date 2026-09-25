/-
Copyright (c) 2026 Jim Fowler, Dennis Sweeney. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jim Fowler, Dennis Sweeney
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic


/-!
# RealIntervals

Supporting results for the classification of compact one-dimensional manifolds.
-/

@[expose] public section

open Set

namespace RealIntervals

-- Use the order topology on ℝ throughout
lemma ordconn_of_connected {X : Set ℝ} (conn : IsConnected X)
    (a : ℝ) (aX : a ∈ X) (b : ℝ) (bX : b ∈ X) : Icc a b ⊆ X := by
  have : OrdConnected X :=
    IsPreconnected.ordConnected (IsConnected.isPreconnected conn)
  exact Set.Icc_subset X aX bX

-- Shouldn't this already be in mathlib?
lemma Real.exists_isGLB {S : Set ℝ} (hne : S.Nonempty) (hbdd : BddBelow S)
    : ∃ x, IsGLB S x := by
  exact ⟨sInf S, isGLB_csInf hne hbdd⟩

-- classifying real intervals

-- Note: Much of what's below already exists in mathlib:
-- Use IsPreconnected.mem_intervals
-- and Real.instConditionallyCompleteLinearOrderReal

lemma connected_bddAbove_subset_contains_Ioo {X : Set ℝ} {supX : ℝ} {x : ℝ}
    (conn : IsConnected X) (h_supX : IsLUB X supX) (xX : x ∈ X)
    : Ioo x supX ⊆ X := by
  intro y ⟨x_lt_y, y_lt_supX⟩
  by_cases h: ∃ z ∈ X, y ≤ z
  · rcases h with ⟨z, zX, y_le_z⟩
    have : Icc x z ⊆ X := ordconn_of_connected conn x xX z zX
    exact this ⟨LT.lt.le x_lt_y, y_le_z⟩
  · push Not at h
    have : y ∈ upperBounds X := fun z ↦ fun zX ↦ LT.lt.le (h z zX)
    have : supX ≤ y := h_supX.2 this
    linarith

lemma connected_bddBelow_subset_contains_Ioo {X : Set ℝ} {infX : ℝ} {x : ℝ}
    (conn : IsConnected X) (h_infX : IsGLB X infX) (xX : x ∈ X)
    : Ioo infX x ⊆ X := by
  intro y ⟨infX_lt_y, y_lt_x⟩
  by_cases h: ∃ z ∈ X, z ≤ y
  · rcases h with ⟨z, zX, z_le_y⟩
    have : Icc z x ⊆ X := ordconn_of_connected conn z zX x xX
    exact this ⟨z_le_y, LT.lt.le y_lt_x⟩
  · push Not at h
    have : y ∈ lowerBounds X := fun z ↦ fun zX ↦ LT.lt.le (h z zX)
    have : y ≤ infX := h_infX.2 this
    linarith

lemma connected_bdd_subset_contains_Ioo
    {X : Set ℝ} {infX supX : ℝ}
    (conn : IsConnected X) (h_infX : IsGLB X infX) (h_supX : IsLUB X supX)
    : Ioo infX supX ⊆ X := by
  let ⟨z, zX⟩ := IsConnected.nonempty conn
  have h₁ : Ioo infX z ⊆ X := connected_bddBelow_subset_contains_Ioo conn h_infX zX
  have h₂ : Ioo z supX ⊆ X := connected_bddAbove_subset_contains_Ioo conn h_supX zX
  have h₃ : Ioo infX supX ⊆ Ioo infX z ∪ {z} ∪ Ioo z supX := by
    intro x ⟨infX_lt_x, x_lt_supX⟩
    rcases lt_trichotomy x z with (x_lt_z | x_eq_z | z_lt_z)
    · left; left
      exact ⟨infX_lt_x, x_lt_z⟩
    · left; right
      rw [mem_singleton_iff, x_eq_z]
    · right
      exact ⟨z_lt_z, x_lt_supX⟩
  have h₄ : Ioo infX z ∪ {z} ∪ Ioo z supX ⊆ X := by
    rintro x ((_ | x_eq_z) | _)
    · apply h₁; assumption
    · rw [mem_singleton_iff] at x_eq_z
      rw [x_eq_z]
      exact zX
    · apply h₂; assumption
  intro x x_Ioo
  exact h₄ (h₃ x_Ioo)

lemma bdd_subset_Icc
    {X : Set ℝ} {infX supX : ℝ}
    (h_infX : IsGLB X infX) (h_supX : IsLUB X supX)
    : X ⊆ Icc infX supX := by
  intro x xX
  exact ⟨h_infX.1 xX, h_supX.1 xX⟩

lemma x_lt_excluded_supX {x supX : ℝ} (xX : x ∈ X)
    (h_supX : IsLUB X supX) (supX_X : supX ∉ X) : x < supX := by
  have : x ≠ supX := by
    intro x_eq_supX
    rw [← x_eq_supX] at supX_X
    contradiction
  exact Ne.lt_of_le this (h_supX.1 xX)

lemma excluded_infX_lt_x {x infX : ℝ} (xX : x ∈ X)
  (h_infX : IsGLB X infX) (infX_X : infX ∉ X) : infX < x := by
  have : infX ≠ x := by
    intro x_eq_supX
    rw [x_eq_supX] at infX_X
    contradiction
  exact Ne.lt_of_le this (h_infX.1 xX)

lemma Ico_Ioo_with_endpoint {a b : ℝ} (hab : a < b)
    : Ico a b = (Ioo a b) ∪ {a} := by
  apply Subset.antisymm
  · intro x ⟨x_le_a, x_lt_b⟩
    by_cases xa : x = a
    · right; exact xa
    · left; exact ⟨Ne.lt_of_le' xa x_le_a, x_lt_b⟩
  · rintro x (x_Ioo | x_a)
    · exact ⟨LT.lt.le x_Ioo.1, x_Ioo.2⟩
    · exact ⟨Eq.ge x_a, Eq.trans_lt x_a hab⟩

lemma Ioc_Ioo_with_endpoint {a b : ℝ} (hab : a < b)
    : Ioc a b = (Ioo a b) ∪ {b} := by
  apply Subset.antisymm
  · intro x ⟨a_lt_x, x_le_b⟩
    by_cases xb : x = b
    · right; exact xb
    have : x < b := Ne.lt_of_le xb x_le_b
    left; exact ⟨a_lt_x, this⟩
  · rintro x (x_Ioo | x_b)
    · exact ⟨x_Ioo.1, LT.lt.le x_Ioo.2⟩
    · exact ⟨(by rw [x_b]; exact hab), Eq.le x_b⟩

lemma characterize_Ioo {X : Set ℝ} (conn : IsConnected X) {infX supX : ℝ}
    (h_infX : IsGLB X infX) (h_supX : IsLUB X supX)
    (infX_X : infX ∉ X) (supX_X : supX ∉ X)
    : X = Ioo infX supX := by
  apply Subset.antisymm
  · intro x xX
    exact ⟨excluded_infX_lt_x xX h_infX infX_X,
           x_lt_excluded_supX xX h_supX supX_X⟩
  · exact connected_bdd_subset_contains_Ioo conn h_infX h_supX

lemma characterize_Ioc {X : Set ℝ} (conn : IsConnected X) {infX supX : ℝ}
    (inf_lt_sup : infX < supX)
    (h_infX : IsGLB X infX) (h_supX : IsLUB X supX)
    (infX_X : infX ∉ X) (supX_X : supX ∈ X)
    : X = Ioc infX supX := by
  apply Subset.antisymm
  · intro x xX
    exact ⟨excluded_infX_lt_x xX h_infX infX_X,
           h_supX.1 xX⟩
  · rw [Ioc_Ioo_with_endpoint inf_lt_sup, union_subset_iff]
    exact ⟨connected_bdd_subset_contains_Ioo conn h_infX h_supX,
           singleton_subset_iff.mpr supX_X⟩

lemma characterize_Ico {X : Set ℝ} (conn : IsConnected X) {infX supX : ℝ}
    (inf_lt_sup : infX < supX)
    (h_infX : IsGLB X infX) (h_supX : IsLUB X supX)
    (infX_X : infX ∈ X) (supX_X : supX ∉ X)
    : X = Ico infX supX := by
  apply Subset.antisymm
  · intro x xX
    exact ⟨h_infX.1 xX,
           x_lt_excluded_supX xX h_supX supX_X⟩
  · rw [Ico_Ioo_with_endpoint inf_lt_sup, union_subset_iff]
    exact ⟨connected_bdd_subset_contains_Ioo conn h_infX h_supX,
           singleton_subset_iff.mpr infX_X⟩

lemma characterize_Icc {X : Set ℝ} (conn : IsConnected X) {infX supX : ℝ}
    (h_infX : IsGLB X infX) (h_supX : IsLUB X supX)
    (infX_X : infX ∈ X) (supX_X : supX ∈ X)
    : X = Icc infX supX := by
  apply Subset.antisymm
  · exact bdd_subset_Icc h_infX h_supX
  · exact (ordconn_of_connected conn) infX infX_X supX supX_X

lemma characterize_singleton {X : Set ℝ} {a : ℝ}
    (h_infX : IsGLB X a) (h_supX : IsLUB X a)
    : (X = {a}) := by
  apply Subset.antisymm
  · apply subset_trans (bdd_subset_Icc h_infX h_supX)
    exact Set.Icc_subset {a} rfl rfl
  · rw [singleton_subset_iff]
    rcases IsLUB.nonempty h_supX with ⟨x, xX⟩
    have : a = x := LE.le.antisymm (h_infX.1 xX) (h_supX.1 xX)
    exact mem_of_eq_of_mem (id this) xX

/-- The four possibilities for including the two endpoints of a bounded interval. -/
inductive BoundedIntervalKind | IooKind | IocKind | IcoKind | IccKind

open BoundedIntervalKind

/-- Two ordered real endpoints together with their inclusion convention. -/
structure BoundedInterval where
  /-- The left endpoint of the interval. -/
  leftEndpoint : ℝ
  /-- The right endpoint of the interval. -/
  rightEndpoint : ℝ
  left_lt_right : leftEndpoint < rightEndpoint
  /-- Which endpoints belong to the interval. -/
  kind : BoundedIntervalKind

/-- Interpret the interval's endpoints and inclusion convention as a set of reals. -/
def BoundedIntervalAsSet : BoundedInterval → Set ℝ
  | ⟨a, b, _, IooKind⟩ => Ioo a b
  | ⟨a, b, _, IocKind⟩ => Ioc a b
  | ⟨a, b, _, IcoKind⟩ => Ico a b
  | ⟨a, b, _, IccKind⟩ => Icc a b

/-- The set is a nondegenerate bounded interval with some endpoint convention. -/
def isBoundedInterval (X : Set ℝ) :=
  ∃ I : BoundedInterval, X = BoundedIntervalAsSet I

lemma isBoundedInterval_Ioo (a b : ℝ) (lt : a < b) : isBoundedInterval (Ioo a b) := by
  use ⟨a, b, lt, IooKind⟩; simp only [BoundedIntervalAsSet]
lemma isBoundedInterval_Ioc (a b : ℝ) (lt : a < b) : isBoundedInterval (Ioc a b) := by
  use ⟨a, b, lt, IocKind⟩; simp only [BoundedIntervalAsSet]
lemma isBoundedInterval_Ico (a b : ℝ) (lt : a < b) : isBoundedInterval (Ico a b) := by
  use ⟨a, b, lt, IcoKind⟩; simp only [BoundedIntervalAsSet]
lemma isBoundedInterval_Icc (a b : ℝ) (lt : a < b) : isBoundedInterval (Icc a b) := by
  use ⟨a, b, lt, IccKind⟩; simp only [BoundedIntervalAsSet]

/-- The set consists of exactly one real number. -/
def isSingleton (X : Set ℝ) :=
  ∃ a : ℝ, X = {a}

lemma classify_connected_reals_with_GLB_lt_LUB
  {X : Set ℝ} (conn : IsConnected X) {infX supX : ℝ}
  (h_infX : IsGLB X infX) (h_supX : IsLUB X supX) (lt : infX < supX)
  : isBoundedInterval X := by
  by_cases infX_X : infX ∈ X
  · by_cases supX_X : supX ∈ X
    · use ⟨infX, supX, lt, IccKind⟩
      exact characterize_Icc conn h_infX h_supX infX_X supX_X
    · use ⟨infX, supX, lt, IcoKind⟩
      exact characterize_Ico conn lt h_infX h_supX infX_X supX_X
  · by_cases supX_X : supX ∈ X
    · use ⟨infX, supX, lt, IocKind⟩
      exact characterize_Ioc conn lt h_infX h_supX infX_X supX_X
    · use ⟨infX, supX, lt, IooKind⟩
      exact characterize_Ioo conn h_infX h_supX infX_X supX_X

theorem classify_connected_bounded_reals
    {X : Set ℝ} (conn : IsConnected X) (above : BddAbove X) (below : BddBelow X)
    : isSingleton X ∨ isBoundedInterval X := by
  have nonempty := IsConnected.nonempty conn
  have ⟨supX, h_supX⟩ := Real.exists_isLUB nonempty above
  have ⟨infX, h_infX⟩ := Real.exists_isGLB nonempty below
  by_cases inf_eq_sup : infX = supX
  · left; rw [isSingleton]; use infX
    rw [← inf_eq_sup] at h_supX
    apply characterize_singleton h_infX h_supX
  · right
    have : infX ≤ supX := isGLB_le_isLUB h_infX h_supX nonempty
    have : infX < supX := Ne.lt_of_le inf_eq_sup this
    exact classify_connected_reals_with_GLB_lt_LUB conn h_infX h_supX this

theorem classify_connected_bounded_reals_nonempty_interior
    {X : Set ℝ} (conn : IsConnected X) (above : BddAbove X) (below : BddBelow X)
    (h : (interior X) ≠ ∅)
    : isBoundedInterval X := by
  rcases classify_connected_bounded_reals conn above below with ⟨a, ha⟩ | bdd
  · rw [ha, interior_singleton] at h
    exact (h rfl).elim
  · exact bdd

-- Some lemmas about bounded intervals in ℝ

lemma isConnected_BoundedInterval (I : BoundedInterval)
    : IsConnected (BoundedIntervalAsSet I) := by
  rw [BoundedIntervalAsSet.eq_def]
  have ⟨a, b, lt, kind⟩ := I
  match kind with
  | IooKind => exact isConnected_Ioo lt
  | IocKind => exact isConnected_Ioc lt
  | IcoKind => exact isConnected_Ico lt
  | IccKind => exact isConnected_Icc (LT.lt.le lt)

lemma BoundedInterval_subset_Icc (I : BoundedInterval)
    : BoundedIntervalAsSet I ⊆ Icc I.leftEndpoint I.rightEndpoint := by
  have ⟨a, b, lt, kind⟩ := I
  match kind with
  | IooKind => exact Ioo_subset_Icc_self
  | IocKind => exact Ioc_subset_Icc_self
  | IcoKind => exact Ico_subset_Icc_self
  | IccKind => exact Eq.subset rfl

lemma BoundedInterval_contains_Ioo (I : BoundedInterval)
    : Ioo I.leftEndpoint I.rightEndpoint ⊆ BoundedIntervalAsSet I := by
  have ⟨a, b, lt, kind⟩ := I
  match kind with
  | IooKind => exact Eq.subset rfl
  | IocKind => exact Ioo_subset_Ioc_self
  | IcoKind => exact Ioo_subset_Ico_self
  | IccKind => exact Ioo_subset_Icc_self

lemma closure_BoundedInterval (I : BoundedInterval) : closure (BoundedIntervalAsSet I) = Icc
    I.leftEndpoint I.rightEndpoint := by
  apply Subset.antisymm
  · calc closure (BoundedIntervalAsSet I)
      ⊆ closure (Icc I.leftEndpoint I.rightEndpoint)
        := closure_mono (BoundedInterval_subset_Icc I)
    _ = Icc I.leftEndpoint I.rightEndpoint
        := IsClosed.closure_eq isClosed_Icc
  · calc Icc I.leftEndpoint I.rightEndpoint
      = closure (Ioo I.leftEndpoint I.rightEndpoint)
        := (closure_Ioo (ne_of_lt I.left_lt_right)).symm
    _ ⊆ closure (BoundedIntervalAsSet I)
        := closure_mono (BoundedInterval_contains_Ioo I)

lemma isBoundedBelow_BoundedInterval (I : BoundedInterval)
    : BddBelow (BoundedIntervalAsSet I) :=
  BddBelow.mono (BoundedInterval_subset_Icc I) bddBelow_Icc

lemma isBoundedAbove_BoundedInterval (I : BoundedInterval)
    : BddAbove (BoundedIntervalAsSet I) :=
  BddAbove.mono (BoundedInterval_subset_Icc I) bddAbove_Icc

@[simp]
lemma interior_BoundedInterval (I : BoundedInterval)
    : interior (BoundedIntervalAsSet I) = Ioo I.leftEndpoint I.rightEndpoint := by
  rw [BoundedIntervalAsSet.eq_def]
  have ⟨a, b, lt, kind⟩ := I
  match kind with
  | IooKind => dsimp; exact interior_Ioo
  | IocKind => dsimp; exact interior_Ioc
  | IcoKind => dsimp; exact interior_Ico
  | IccKind => dsimp; exact interior_Icc

-- Shouldn't this already be in mathlib?
@[simp]
lemma Icc_diff_Ioo {a b : ℝ} (lt : a < b) : (Icc a b) \ (Ioo a b) = {a, b} := by
  apply Subset.antisymm
  · rw [← Icc_sdiff_both]
    exact sdiff_sdiff_le
  · rintro x (xleft | xright)
    · rw [mem_sdiff, mem_Icc, mem_Ioo, not_and]
      exact ⟨⟨by linarith, by linarith⟩, (by intro _; linarith)⟩
    · simp only [mem_singleton_iff] at xright
      rw [xright]
      simp only [mem_sdiff, mem_Icc, le_refl, and_true, mem_Ioo, lt_self_iff_false, and_false,
        not_false_eq_true]
      exact LT.lt.le lt

@[simp]
lemma frontier_BoundedInterval (I : BoundedInterval)
    : frontier (BoundedIntervalAsSet I) = {I.leftEndpoint, I.rightEndpoint} := by
  rw [frontier, closure_BoundedInterval I, interior_BoundedInterval I]
  exact Icc_diff_Ioo I.left_lt_right

lemma pair_has_other {a b c : ℝ} (ne : a ≠ b) (h : c ∈ ({a, b} : Set ℝ))
    : ∃ (d : ℝ), d ∈ ({a, b} : Set ℝ) ∧ d ≠ c  := by
  simp only [mem_insert_iff, mem_singleton_iff, ne_eq, exists_eq_or_imp, exists_eq_left]
  simp only [mem_insert_iff, mem_singleton_iff] at h
  rcases h with ca | cb
  · rw [← ca] at ne; right; exact ne.symm
  · rw [← cb] at ne; left; exact ne

theorem other_endpoint
    {X : Set ℝ} (int : (interior X) ≠ ∅)
    (conn : IsConnected X) (above : BddAbove X) (below : BddBelow X)
    (a : ℝ) (ha : a ∈ frontier X) : ∃b : ℝ, b ∈ frontier X ∧ b ≠ a:= by
  have ⟨I, XI⟩ := classify_connected_bounded_reals_nonempty_interior conn above below int
  rw [XI, frontier_BoundedInterval]
  rw [XI, frontier_BoundedInterval] at ha
  have : I.leftEndpoint ≠ I.rightEndpoint := by
    exact ne_of_lt I.left_lt_right
  exact pair_has_other (ne_of_lt I.left_lt_right) ha

-- Continue to classify all connected sets in ℝ
lemma characterize_univ {X : Set ℝ} (conn : IsConnected X)
  (below : ¬ BddBelow X) (above : ¬ BddAbove X)
    : X = univ := by
  rw [bddBelow_def] at below; push Not at below
  rw [bddAbove_def] at above; push Not at above
  ext x
  simp only [mem_univ, iff_true]
  have ⟨B, BX, Bbig⟩ := above x
  have ⟨A, AX, Asmall⟩ := below x
  have : Icc A B ⊆ X := (ordconn_of_connected conn) A AX B BX
  exact this ⟨LT.lt.le Asmall, LT.lt.le Bbig⟩

lemma characterize_Ioi {X : Set ℝ} (conn : IsConnected X)
    {infX : ℝ} (h_infX : IsGLB X infX) (infX_X : infX ∉ X)
    (above : ¬ BddAbove X) : X = Ioi infX := by
  rw [bddAbove_def] at above; push Not at above
  apply Subset.antisymm
  · intro x xX
    exact excluded_infX_lt_x xX h_infX infX_X
  · intro x infX_lt_x
    rw [mem_Ioi] at infX_lt_x
    let ⟨B, BX, Bbig⟩ := above x
    have : Ioo infX B ⊆ X :=
      connected_bddBelow_subset_contains_Ioo conn h_infX BX
    exact this ⟨infX_lt_x, Bbig⟩

lemma characterize_Ici {X : Set ℝ} (conn : IsConnected X)
    {infX : ℝ} (h_infX : IsGLB X infX) (infX_X : infX ∈ X)
    (above : ¬ BddAbove X) : X = Ici infX := by
  rw [bddAbove_def] at above; push Not at above
  apply Set.Subset.antisymm
  · intro x xX
    exact h_infX.1 xX
  · intro x infX_le_x
    have ⟨B, BX, Bbig⟩ := above x
    have : Set.Icc infX B ⊆ X := (ordconn_of_connected conn) infX infX_X B BX
    exact this ⟨infX_le_x, LT.lt.le Bbig⟩

lemma classify_Ixi {X : Set ℝ} (conn : IsConnected X)
    (below : BddBelow X) (above : ¬ BddAbove X)
    : ∃ a : ℝ, (X = Ioi a ∨ X = Ici a) := by
  have ⟨infX, h_infX⟩ := Real.exists_isGLB (IsConnected.nonempty conn) below
  use infX
  by_cases infX_X : infX ∈ X
  · right; exact characterize_Ici conn h_infX infX_X above
  · left; exact characterize_Ioi conn h_infX infX_X above

lemma characterize_Iio {X : Set ℝ} (conn : IsConnected X)
    {supX : ℝ} (h_supX : IsLUB X supX) (supX_X : supX ∉ X)
    (below : ¬ BddBelow X) : X = Iio supX := by
  rw [bddBelow_def] at below; push Not at below
  apply Set.Subset.antisymm
  · intro x xX
    exact x_lt_excluded_supX xX h_supX supX_X
  · intro x x_lt_supX
    rw [Set.mem_Iio] at x_lt_supX
    let ⟨A, AX, Asmall⟩ := below x
    have : Set.Ioo A supX ⊆ X :=
      connected_bddAbove_subset_contains_Ioo conn h_supX AX
    exact this ⟨Asmall, x_lt_supX⟩

lemma characterize_Iic {X : Set ℝ} (conn : IsConnected X)
    {supX : ℝ} (h_supX : IsLUB X supX) (supX_X : supX ∈ X)
    (below : ¬ BddBelow X) : X = Iic supX := by
  rw [bddBelow_def] at below; push Not at below
  apply Set.Subset.antisymm
  · intro x xX
    exact h_supX.1 xX
  · intro x x_le_supX
    let ⟨A, AX, Asmall⟩ := below x
    have : Set.Icc A supX ⊆ X := (ordconn_of_connected conn) A AX supX supX_X
    exact this ⟨LT.lt.le Asmall, x_le_supX⟩

lemma classify_Iix {X : Set ℝ} (conn : IsConnected X)
    (below : ¬ BddBelow X) (above : BddAbove X)
    : ∃ a : ℝ, (X = Iio a ∨ X = Iic a) := by
  have ⟨supX, h_supX⟩ := Real.exists_isLUB (IsConnected.nonempty conn) above
  use supX
  by_cases supX_X : supX ∈ X
  · right; exact characterize_Iic conn h_supX supX_X below
  · left; exact characterize_Iio conn h_supX supX_X below

-- Give names to the cases
/-- The possible forms of a nonempty connected subset of the real line. -/
inductive ConnectedRealClassification
  | of_univ : ConnectedRealClassification
  | of_Iio : ℝ → ConnectedRealClassification
  | of_Iic : ℝ → ConnectedRealClassification
  | of_Ioi : ℝ → ConnectedRealClassification
  | of_Ici : ℝ → ConnectedRealClassification
  | of_singleton : ℝ → ConnectedRealClassification
  | of_bounded_interval : BoundedInterval → ConnectedRealClassification

open ConnectedRealClassification

/-- Interpret a connected-set classification as a subset of the real line. -/
def ConnectedRealClassificationAsSet : ConnectedRealClassification → Set ℝ
  | of_univ => univ
  | of_Iio a => Iio a
  | of_Iic a => Iic a
  | of_Ioi a => Ioi a
  | of_Ici a => Ici a
  | of_singleton a => {a}
  | of_bounded_interval I => BoundedIntervalAsSet I

/-- The set is represented by one of the connected real-set forms. -/
def isConnectedRealClassification (X : Set ℝ) :=
  ∃ I : ConnectedRealClassification, X = ConnectedRealClassificationAsSet I

theorem classify_connected_reals {X : Set ℝ} (conn : IsConnected X)
    : isConnectedRealClassification X := by
  by_cases below : BddBelow X
  · by_cases above : BddAbove X
    · rcases classify_connected_bounded_reals conn above below with sing | bdd
      · let ⟨a, ha⟩ := sing
        use of_singleton a; exact ha
      · let ⟨I, hI⟩ := bdd
        use of_bounded_interval I; exact hI
    · rcases classify_Ixi conn below above with ⟨a, hIoi | hIci⟩
      · use of_Ioi a; exact hIoi
      · use of_Ici a; exact hIci
  · by_cases above : BddAbove X
    · rcases classify_Iix conn below above with ⟨a, hIio | hIic⟩
      · use of_Iio a
        exact hIio
      · use of_Iic a
        exact hIic
    · use of_univ
      exact characterize_univ conn below above

end RealIntervals
