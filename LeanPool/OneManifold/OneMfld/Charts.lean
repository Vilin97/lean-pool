/-
Copyright (c) 2026 Jim Fowler, Dennis Sweeney. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jim Fowler, Dennis Sweeney
-/
module

public import Mathlib.Tactic
public import LeanPool.OneManifold.OneMfld.PartialHomeomorphHelpers


/-! Interval charts on a 1-manifold charted on `ℝ≥0`, and the `Overlap` relation.

An `OChart` has an open-interval target `Ioo x y` (an interior chart); an `HChart` has a
half-open target `Iio x` (a boundary chart); an `IChart` is either.
-/

@[expose] public section

/-- A one-dimensional chart with an open bounded interval as target. -/
structure OChart (M : Type*) [TopologicalSpace M]
  extends OpenPartialHomeomorph M NNReal where
  target_ioo : (∃ x y, (Set.Ioo x y = target))

/-- A boundary chart with a half-open interval as target. -/
structure HChart (M : Type*) [TopologicalSpace M]
  extends OpenPartialHomeomorph M NNReal where
  target_iio : (∃ x, (Set.Iio x = target))

/-- A chart whose target is an open interval or a half-open interval. -/
structure IChart (M : Type*) [TopologicalSpace M]
  extends OpenPartialHomeomorph M NNReal where
  is_interval : (∃ x y, (Set.Ioo x y = target)) ∨ (∃ x, (Set.Iio x = target))

variable
  {M : Type*}
  [TopologicalSpace M]

/-- Regard an interior chart as an interval chart. -/
def OChart.toIChart (a : OChart M) : IChart M :=
  { a with is_interval := Or.inl a.target_ioo }

/-- Regard a boundary chart as an interval chart. -/
def HChart.toIChart (a : HChart M) : IChart M :=
  { a with is_interval := Or.inr a.target_iio }

/-- Two sets meet and each has a point outside the other. -/
def Overlap (U : Set α) (V : Set α) : Prop :=
  (U ∩ V).Nonempty ∧ (U \ V).Nonempty ∧ (V \ U).Nonempty

theorem does_overlap' (U : Set α) (V : Set α) (hu : ¬ U ⊆ V)
  : (U \ V).Nonempty := Set.sdiff_nonempty.mpr hu

theorem does_overlap (U : Set α) (V : Set α) (h : (U ∩ V).Nonempty) (hu : ¬ U ⊆ V) (hv : ¬ V ⊆ U)
  : Overlap U V := by
    apply And.intro
    · exact h
    · apply And.intro
      · exact does_overlap' U V hu
      · exact does_overlap' V U hv

theorem overlap_symm {U : Set α} {V : Set α} (h : Overlap U V) : Overlap V U := by
  dsimp [Overlap] at h
  apply And.intro
  · exact Set.inter_nonempty_iff_exists_right.mpr h.1
  · apply And.intro
    · exact h.2.2
    · exact h.2.1

lemma Overlap.nonempty {U : Set α} {V : Set α} (h : Overlap U V) : (Nonempty U) ∧ (Nonempty V) := by
  have nonempty : (U ∩ V).Nonempty := h.1
  apply And.intro
  · exact Set.Nonempty.to_subtype (Set.Nonempty.left nonempty)
  · exact Set.Nonempty.to_subtype (Set.Nonempty.right nonempty)

lemma chart_target_nonempty (φ : OpenPartialHomeomorph M NNReal) (h : φ.source.Nonempty) :
    φ.target.Nonempty := by
  rw [← PartialEquiv.image_source_eq_target φ.toPartialEquiv]
  exact h.image _

lemma OChart.connected_source (a : OChart M) (h : a.source.Nonempty) :
    IsConnected a.source := by
  apply (partial_homeo_source_connected_iff_target_connected a.toOpenPartialHomeomorph).mpr
  obtain ⟨x, y, hxy⟩ := a.target_ioo
  have hne : a.target.Nonempty := chart_target_nonempty _ h
  rw [←hxy] at hne ⊢
  exact isConnected_Ioo (Set.nonempty_Ioo.mp hne)

lemma HChart.connected_source (a : HChart M) (h : a.source.Nonempty) :
    IsConnected a.source := by
  apply (partial_homeo_source_connected_iff_target_connected a.toOpenPartialHomeomorph).mpr
  obtain ⟨x, hx⟩ := a.target_iio
  have hne : a.target.Nonempty := chart_target_nonempty _ h
  rw [←hx] at hne ⊢
  exact ⟨hne, isPreconnected_Iio⟩

lemma IChart.connected_source (a : IChart M) (h : a.source.Nonempty) :
    IsConnected a.source := by
  apply (partial_homeo_source_connected_iff_target_connected a.toOpenPartialHomeomorph).mpr
  have hne : a.target.Nonempty := chart_target_nonempty _ h
  rcases a.is_interval with (⟨x, y, hxy⟩ | ⟨x, hx⟩)
  · rw [←hxy] at hne ⊢
    exact isConnected_Ioo (Set.nonempty_Ioo.mp hne)
  · rw [←hx] at hne ⊢
    exact ⟨hne, isPreconnected_Iio⟩
