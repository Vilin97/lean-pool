/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.Multivalued.Separator.Basic

/-!
# `NRR.Multivalued.Separator.Fibers` — vertical fibers meet the carrier

Every vertical interval `{x} × SignedInterval` meets the carrier of a top–bottom separator. The
argument is a pure connectedness fact: if the vertical fiber avoided the carrier, then the two
disjoint open regions `lower` and `upper` would pull back along the vertical embedding to a
separation of the connected signed interval, with the bottom endpoint on the lower side and the top
endpoint on the upper side. This contradicts connectedness of `SignedInterval`.

Consequences: each vertical fiber is nonempty, the carrier is nonempty whenever `X` is nonempty, and
the vertical path through any point meets the carrier. Nonemptiness of the carrier is therefore
derived rather than assumed, so no separate nonemptiness field is needed.
-/

namespace NRR

/-- A connected space cannot be covered by two disjoint nonempty open sets. -/
theorem connected_univ_not_open_separation
    {Y : Type*} [TopologicalSpace Y] [ConnectedSpace Y]
    {L U : Set Y}
    (hL : IsOpen L) (hU : IsOpen U)
    (hdisj : Disjoint L U) (hcover : L ∪ U = Set.univ)
    {l u : Y} (hl : l ∈ L) (hu : u ∈ U) :
    False := by
  have hpre : IsPreconnected (Set.univ : Set Y) := isPreconnected_univ
  have hsub : (Set.univ : Set Y) ⊆ L ∪ U := by rw [hcover]
  have hLne : (Set.univ ∩ L).Nonempty := ⟨l, Set.mem_univ l, hl⟩
  have hUne : (Set.univ ∩ U).Nonempty := ⟨u, Set.mem_univ u, hu⟩
  obtain ⟨z, _, hzL, hzU⟩ := hpre L U hL hU hsub hLne hUne
  exact hdisj.le_bot ⟨hzL, hzU⟩

namespace TopBottomSeparator

variable {X : Type*} [TopologicalSpace X]

/-- Every vertical fiber over `x` meets the carrier of the separator. -/
theorem exists_mem_fiber
    (S : TopBottomSeparator X) (x : X) :
    ∃ y : SignedInterval, (x, y) ∈ S.carrier := by
  by_contra h
  push Not at h
  -- Pull the two regions back along the vertical embedding.
  set v : SignedInterval → X × SignedInterval := SignedInterval.vertical X x with hv
  set L : Set SignedInterval := v ⁻¹' S.lower with hLdef
  set U : Set SignedInterval := v ⁻¹' S.upper with hUdef
  have hcont : Continuous v := SignedInterval.continuous_vertical x
  have hLopen : IsOpen L := S.isOpen_lower.preimage hcont
  have hUopen : IsOpen U := S.isOpen_upper.preimage hcont
  have hdisj : Disjoint L U := by
    rw [Set.disjoint_left]
    intro y hyL hyU
    exact S.disjoint_lower_upper.le_bot ⟨hyL, hyU⟩
  have hcover : L ∪ U = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    have hnot : (x, y) ∉ S.carrier := h y
    have := S.mem_lower_or_upper_of_not_mem hnot
    rcases this with hlow | hup
    · exact Or.inl hlow
    · exact Or.inr hup
  have hl : SignedInterval.left ∈ L := S.bottom_mem_lower x
  have hu : SignedInterval.right ∈ U := S.top_mem_upper x
  exact connected_univ_not_open_separation hLopen hUopen hdisj hcover hl hu

/-- The vertical fiber over `x` is nonempty. -/
theorem fiber_nonempty
    (S : TopBottomSeparator X) (x : X) :
    {y : SignedInterval | (x, y) ∈ S.carrier}.Nonempty := by
  obtain ⟨y, hy⟩ := S.exists_mem_fiber x
  exact ⟨y, hy⟩

/-- The carrier is nonempty whenever `X` is nonempty. -/
theorem carrier_nonempty
    [Nonempty X] (S : TopBottomSeparator X) :
    S.carrier.Nonempty := by
  obtain ⟨y, hy⟩ := S.exists_mem_fiber (Classical.arbitrary X)
  exact ⟨(Classical.arbitrary X, y), hy⟩

/-- The vertical path through `x` meets the carrier. -/
theorem vertical_path_intersects
    (S : TopBottomSeparator X) (x : X) :
    (Set.range (SignedInterval.vertical X x) ∩ S.carrier).Nonempty := by
  obtain ⟨y, hy⟩ := S.exists_mem_fiber x
  exact ⟨(x, y), ⟨y, rfl⟩, hy⟩

end TopBottomSeparator

end NRR
