/-
Copyright (c) 2026 Jim Fowler, Dennis Sweeney. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jim Fowler, Dennis Sweeney
-/
module

public import Mathlib.Tactic
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.OpenPartialHomeomorph.Defs


/-!
# PartialHomeomorphHelpers

Supporting results for the classification of compact one-dimensional manifolds.
-/

@[expose] public section

namespace OneMfld

lemma partial_homeo_connected {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (h : OpenPartialHomeomorph X Y) (conn : IsConnected h.source) : (IsConnected h.target) := by
  have ht : h.target = h.toFun '' h.source
  · exact Eq.symm (PartialEquiv.image_source_eq_target h.toPartialEquiv)
  rw [ht]
  apply IsConnected.image conn ↑h.toPartialEquiv h.continuousOn_toFun

lemma partial_homeo_connected' {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (h : OpenPartialHomeomorph X Y) (conn : IsConnected h.target) : (IsConnected h.source) := by
  have hst : h.symm.source = h.target := rfl
  have hts : h.symm.target = h.source := rfl
  have conn' : IsConnected h.symm.source := by
    rw [hst]
    exact conn
  have h'' := partial_homeo_connected h.symm conn'
  rw [←hts]
  exact h''

lemma partial_homeo_source_connected_iff_target_connected {X : Type*} {Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
  (h : OpenPartialHomeomorph X Y) : IsConnected h.source ↔ IsConnected h.target := by
  constructor
  · exact fun a => partial_homeo_connected h a
  · exact fun a => partial_homeo_connected' h a

/-- For `t ⊆ φ.target`, the target of `φ` restricted to `φ.symm '' t` is exactly `t`;
this computes `(φ.restrOpen (φ.symm '' t) _).target`. -/
lemma restrOpen_symm_image_target {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (φ : OpenPartialHomeomorph X Y) {t : Set Y} (ht : t ⊆ φ.target) :
  φ.target ∩ ↑φ.symm ⁻¹' (↑φ.symm '' t) = t := by
  ext z
  apply Iff.intro
  · intro hz
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_image] at hz
    rcases hz with ⟨hz1, ⟨z', hz2, hz3⟩⟩
    have inj : Set.InjOn φ.symm φ.target := OpenPartialHomeomorph.injOn φ.symm
    have : z' = z := inj (ht hz2) hz1 hz3
    rw [←this]
    exact hz2
  · intro hz
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_image]
    exact ⟨ht hz, z, hz, rfl⟩

end OneMfld
