/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.GeometryReduction
import Mathlib.Logic.Equiv.Fintype

/-! # Erdős 97 convex-octagon formalization: Relabelling -/

namespace Erdos97Octagon

/-- The canonical first witness row used by the finite classification. -/
def standardTargets : Finset Vertex := {1, 2, 3, 4}

/-- The canonical witness row has four vertices. -/
@[simp] theorem card_standardTargets : standardTargets.card = 4 := by
  decide

/-- The canonical witness row does not contain its centre. -/
@[simp] theorem zero_notMem_standardTargets : (0 : Vertex) ∉ standardTargets := by
  decide

namespace OctagonIncidence

/-- Simultaneously relabel the centres and every entry of their witness rows. -/
def relabel (Q : OctagonIncidence) (e : Vertex ≃ Vertex) : OctagonIncidence where
  targets v := (Q.targets (e.symm v)).map e.toEmbedding
  card_targets v := by simp [Q.card_targets]
  centre_not_mem v := by simpa using Q.centre_not_mem (e.symm v)

/-- A system is normalized when row zero is the canonical four-set. -/
def Normalized (Q : OctagonIncidence) : Prop :=
  Q.targets 0 = standardTargets

private theorem exists_perm_fix_zero_map
    (S : Finset Vertex) (hcard : S.card = 4) (hzero : (0 : Vertex) ∉ S) :
    ∃ e : Vertex ≃ Vertex,
      e 0 = 0 ∧ S.map e.toEmbedding = standardTargets := by
  classical
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq S standardTargets (by
    simpa only [card_standardTargets] using hcard)
  have hσzero : σ 0 ∉ standardTargets := by
    intro hmem
    rw [← hσ] at hmem
    obtain ⟨x, hxS, hx⟩ := Finset.mem_map.mp hmem
    apply hzero
    have hxzero : x = 0 := σ.injective (by simpa using hx)
    simpa [hxzero] using hxS
  let τ : Vertex ≃ Vertex := Equiv.swap (σ 0) 0
  have hτ (x : Vertex) (hx : x ∈ standardTargets) : τ x = x := by
    apply Equiv.swap_apply_of_ne_of_ne
    · exact fun h => hσzero (h ▸ hx)
    · exact fun h => zero_notMem_standardTargets (h ▸ hx)
  let e := σ.trans τ
  refine ⟨e, ?_, ?_⟩
  · simp [e, τ]
  · rw [show e.toEmbedding = σ.toEmbedding.trans τ.toEmbedding by rfl]
    rw [← Finset.map_map, hσ]
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      change τ y ∈ standardTargets
      rw [hτ y hy]
      exact hy
    · intro hx
      exact Finset.mem_map.mpr ⟨x, hx, hτ x hx⟩

/-- Every octagon incidence system is isomorphic to one with canonical row zero. -/
theorem exists_normalized_relabel (Q : OctagonIncidence) :
    ∃ e : Vertex ≃ Vertex, (Q.relabel e).Normalized := by
  obtain ⟨e, he0, hmap⟩ :=
    exists_perm_fix_zero_map (Q.targets 0) (Q.card_targets 0) (Q.centre_not_mem 0)
  have hesymm : e.symm 0 = 0 := by
    apply e.injective
    simp [he0]
  refine ⟨e, ?_⟩
  simpa [Normalized, relabel, hesymm] using hmap

end OctagonIncidence

/-- Relabel a planar configuration contragrediently with its incidence system. -/
def relabelPoints (p : Vertex → Plane) (e : Vertex ≃ Vertex) : Vertex → Plane :=
  p ∘ e.symm

/-- Equal-distance realisability is invariant under simultaneous relabelling. -/
theorem realises_relabel
    {p : Vertex → Plane} {Q : OctagonIncidence} (hR : Realises p Q)
    (e : Vertex ≃ Vertex) :
    Realises (relabelPoints p e) (Q.relabel e) := by
  intro v
  obtain ⟨r, hr⟩ := hR (e.symm v)
  refine ⟨r, fun w hw => ?_⟩
  have hw' : e.symm w ∈ Q.targets (e.symm v) := by
    simpa [OctagonIncidence.relabel] using hw
  simpa [relabelPoints] using hr (e.symm w) hw'

/-- Convex independence is invariant under relabelling. -/
theorem convexIndependent_relabel
    {p : Vertex → Plane} (hC : ConvexIndependent ℝ p) (e : Vertex ≃ Vertex) :
    ConvexIndependent ℝ (relabelPoints p e) := by
  simpa [relabelPoints] using hC.comp_embedding e.symm.toEmbedding

/-- A failed convex octagon has a normalized balanced pair-sparse realisation. -/
theorem normalized_reduction_of_all_hasFour
    {p : Vertex → Plane} (hC : ConvexIndependent ℝ p)
    (h : ∀ v, HasFourEquidistant p v) :
    ∃ p' : Vertex → Plane, ∃ Q : OctagonIncidence,
      ConvexIndependent ℝ p' ∧ Realises p' Q ∧ Q.Normalized ∧
        Q.PairSparse ∧ Q.Balanced := by
  obtain ⟨Q, hR⟩ := incidence_of_all_hasFour h
  obtain ⟨e, hN⟩ := Q.exists_normalized_relabel
  let p' := relabelPoints p e
  let Q' := Q.relabel e
  have hC' : ConvexIndependent ℝ p' := convexIndependent_relabel hC e
  have hR' : Realises p' Q' := realises_relabel hR e
  have hS' : Q'.PairSparse := pairSparse_of_realises hC' Q' hR'
  exact ⟨p', Q', hC', hR', hN, hS', Q'.balanced_of_pairSparse hS'⟩

end Erdos97Octagon
