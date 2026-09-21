/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Tactic

/-! # Connectedness from connected traces of neighborhoods -/

@[expose] public section
open Set

namespace LichnerowiczObata

/-- A dense region in a preconnected space is preconnected if each ambient
point has an open neighborhood whose trace on the region is preconnected. -/
theorem isPreconnected_of_dense_local_traces {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] {s : Set X} (hd : Dense s)
    (hl : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsPreconnected (U ∩ s)) :
    IsPreconnected s := by
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hs huv
  have hdisj : closure (s ∩ u) ∩ closure (s ∩ v) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨U, hU, hxU, hconn⟩ := hl x
    obtain ⟨y, hyU, hys, hyu⟩ := mem_closure_iff.mp hx.1 U hU hxU
    obtain ⟨z, hzU, hzs, hzv⟩ := mem_closure_iff.mp hx.2 U hU hxU
    obtain ⟨w, hw, hwu, hwv⟩ := hconn u v hu hv
      (fun w hw => hs hw.2) ⟨y, ⟨hyU, hys⟩, hyu⟩ ⟨z, ⟨hzU, hzs⟩, hzv⟩
    have hn : w ∈ s ∩ (u ∩ v) := ⟨hw.2, hwu, hwv⟩
    rw [huv] at hn
    exact hn
  have hcover : (univ : Set X) ⊆ closure (s ∩ u) ∪ closure (s ∩ v) := by
    rw [← closure_union, ← hd.closure_eq]
    apply closure_mono
    intro x hx
    rcases hs hx with hxu | hxv
    · exact Or.inl ⟨hx, hxu⟩
    · exact Or.inr ⟨hx, hxv⟩
  have hside := isPreconnected_iff_subset_of_disjoint_closed.mp isPreconnected_univ
    (closure (s ∩ u)) (closure (s ∩ v)) isClosed_closure isClosed_closure hcover
    (by rw [hdisj, inter_empty])
  rcases hside with hleft | hright
  · left
    intro x hx
    rcases hs hx with hxu | hxv
    · exact hxu
    · have hn : x ∈ closure (s ∩ u) ∩ closure (s ∩ v) :=
        ⟨hleft (mem_univ x), subset_closure ⟨hx, hxv⟩⟩
      rw [hdisj] at hn
      exact hn.elim
  · right
    intro x hx
    rcases hs hx with hxu | hxv
    · have hn : x ∈ closure (s ∩ u) ∩ closure (s ∩ v) :=
        ⟨subset_closure ⟨hx, hxu⟩, hright (mem_univ x)⟩
      rw [hdisj] at hn
      exact hn.elim
    · exact hxv

end LichnerowiczObata
