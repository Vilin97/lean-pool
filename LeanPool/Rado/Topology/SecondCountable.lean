/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.LocalAtTarget

/-!
# Second-countability helpers

Point-set topology preliminaries for the Poincaré–Volterra lemma
(`Rado/Topology/PoincareVolterra.lean`):

* a compact set in a locally second-countable space is second countable;
* a countable cover by second-countable open sets gives second countability
  (set-of-sets version of `secondCountableTopology_of_countable_cover`);
* ccc: a second-countable space has no uncountable pairwise-disjoint family of
  nonempty open sets;
* countable-branching reachability is countable.

All statements are pure topology, independent of the rest of the development.
-/

open Set Topology

namespace Rado

/-- A compact set each of whose points has a second-countable open neighbourhood
is second countable in the subspace topology (cover by finitely many). -/
theorem IsCompact.secondCountableTopology {Z : Type*} [TopologicalSpace Z] {K : Set Z}
    (hK : IsCompact K)
    (hloc : ∀ z ∈ K, ∃ U : Set Z, z ∈ U ∧ IsOpen U ∧ SecondCountableTopology U) :
    SecondCountableTopology K := by
  choose U hzU hUo hUsc using fun z : K ↦ hloc z z.2
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hUo fun x hx ↦
    mem_iUnion.2 ⟨⟨x, hx⟩, hzU ⟨x, hx⟩⟩
  -- cover the subtype `↥K` by the preimages of the finitely many `U i`, `i ∈ t`
  have : ∀ i : t, SecondCountableTopology
      (Subtype.val ⁻¹' U i.1 : Set K) := by
    intro i
    have := hUsc i.1
    exact (Topology.IsEmbedding.subtypeVal.restrictPreimage
      (U i.1)).secondCountableTopology
  refine TopologicalSpace.secondCountableTopology_of_countable_cover
    (U := fun i : t ↦ (Subtype.val ⁻¹' U i.1 : Set K))
    (fun i ↦ (hUo i.1).preimage continuous_subtype_val) ?_
  ext x
  simp only [mem_iUnion, mem_preimage, mem_univ, iff_true]
  obtain ⟨i, hit, hxi⟩ := mem_iUnion₂.1 (ht x.2)
  exact ⟨⟨i, hit⟩, hxi⟩

/-- A countable family of second-countable open sets covering `Z` makes `Z`
second countable. -/
theorem secondCountableTopology_of_countable_setCover {Z : Type*} [TopologicalSpace Z]
    {𝒰 : Set (Set Z)} (hct : 𝒰.Countable) (ho : ∀ U ∈ 𝒰, IsOpen U)
    (hsc : ∀ U ∈ 𝒰, SecondCountableTopology U) (hcov : ⋃₀ 𝒰 = univ) :
    SecondCountableTopology Z := by
  have : Countable ↥𝒰 := hct.to_subtype
  have : ∀ U : ↥𝒰, SecondCountableTopology U.1 := fun U ↦ hsc U.1 U.2
  have hcov' : ⋃ U : ↥𝒰, (U : Set Z) = univ := by
    rw [← sUnion_eq_iUnion, hcov]
  exact TopologicalSpace.secondCountableTopology_of_countable_cover
    (U := fun U : ↥𝒰 ↦ U.1) (fun U ↦ ho U.1 U.2) hcov'

/-- ccc: in a second-countable space, every pairwise-disjoint family of nonempty
open sets is countable. -/
theorem countable_of_pairwiseDisjoint_isOpen {Z : Type*} [TopologicalSpace Z]
    [SecondCountableTopology Z] {𝒰 : Set (Set Z)} (ho : ∀ U ∈ 𝒰, IsOpen U)
    (hne : ∀ U ∈ 𝒰, U.Nonempty) (hdisj : 𝒰.PairwiseDisjoint id) :
    𝒰.Countable := by
  obtain ⟨T, hTc, hT𝒰, hTU⟩ := TopologicalSpace.isOpen_sUnion_countable 𝒰 ho
  refine hTc.mono fun U hU ↦ ?_
  obtain ⟨x, hxU⟩ := hne U hU
  have hx : x ∈ ⋃₀ T := by rw [hTU]; exact ⟨U, hU, hxU⟩
  obtain ⟨V, hVT, hxV⟩ := hx
  rcases eq_or_ne U V with rfl | hUV
  · exact hVT
  · exact absurd hxV (disjoint_left.1 (hdisj hU (hT𝒰 hVT) hUV) hxU)

/-- Levels of reachability along a relation `r`, starting at `a₀`: `reachLevel r a₀ n`
is the set of points reachable in exactly `n` steps. -/
private def reachLevel {α : Type*} (r : α → α → Prop) (a₀ : α) : ℕ → Set α
  | 0 => {a₀}
  | n + 1 => ⋃ a ∈ reachLevel r a₀ n, {b | r a b}

private lemma reachLevel_succ {α : Type*} (r : α → α → Prop) (a₀ : α) (n : ℕ) :
    reachLevel r a₀ (n + 1) = ⋃ a ∈ reachLevel r a₀ n, {b | r a b} := rfl

/-- The reflexive-transitive closure of a countably-branching relation reaches
only countably many elements from a fixed start. -/
theorem countable_setOf_reflTransGen {α : Type*} {r : α → α → Prop} (a₀ : α)
    (h : ∀ a, {b | r a b}.Countable) :
    {b | Relation.ReflTransGen r a₀ b}.Countable := by
  have hS : ∀ n, (reachLevel r a₀ n).Countable := by
    intro n
    induction n with
    | zero => exact countable_singleton a₀
    | succ n ih =>
      rw [reachLevel_succ]
      exact ih.biUnion fun a _ ↦ h a
  refine (countable_iUnion hS).mono fun b hb ↦ ?_
  simp only [mem_ofPred_eq] at hb
  induction hb with
  | refl => exact mem_iUnion.2 ⟨0, mem_singleton a₀⟩
  | tail hab hbc ih =>
    obtain ⟨n, hn⟩ := mem_iUnion.1 ih
    refine mem_iUnion.2 ⟨n + 1, ?_⟩
    rw [reachLevel_succ]
    exact mem_biUnion hn hbc

end Rado
