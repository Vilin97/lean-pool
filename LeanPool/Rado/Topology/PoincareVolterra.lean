/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import LeanPool.Rado.Topology.SecondCountable

/-!
# The Poincaré–Volterra lemma

If `Z` is a connected, Hausdorff, locally compact, locally connected, locally
second-countable topological space and `f : Z → Y` is a continuous map into a
second-countable Hausdorff space whose fibers are discrete, then `Z` is second
countable.

This is the purely topological endgame of Radó's theorem; see Forster,
*Lectures on Riemann Surfaces*, Lemma 23.2 (= Rainer's notes 23.2, full proof
in `reference/rado/rainer.txt`), or Anghel–Stan arXiv:2008.12189, Appendix C.

Proof sketch. Let `V` be a countable basis of `Y` and let `𝒰` be the family of
all connected components `U` of preimages `f ⁻¹' V`, `V ∈ V`, such that `U` is
second countable (as a subspace). Then:

1. `𝒰` covers `Z`: given `z`, discreteness of the fiber through `z`, local
   compactness and local second countability give a relatively compact open
   `W ∋ z` with second-countable compact closure and
   `closure W ∩ f ⁻¹' {f z} = {z}`; pick `V ∈ V` with
   `f z ∈ V ⊆ Y \ f '' (frontier W)` (the image of the frontier is compact,
   hence closed, and misses `f z`); the component `U ∋ z` of `f ⁻¹' V` avoids
   `frontier W`, meets `W`, hence `U ⊆ W` (connectedness), so `U` is second
   countable, open (local connectedness), and `U ∈ 𝒰`.
2. Each `U₀ ∈ 𝒰` meets only countably many members of `𝒰`: for fixed `V`, the
   components of `f ⁻¹' V` are pairwise disjoint, so those meeting `U₀` trace a
   pairwise-disjoint family of nonempty opens in the second-countable `U₀`
   (ccc), countable; sum over the countable basis.
3. Chain argument: the members reachable from a fixed `U₀ ∈ 𝒰` by finite chains
   form a countable subfamily `R` whose union `G` is open; `G` is also closed
   (a boundary point `z` lies in some `U ∈ 𝒰` by 1, which meets `G`, hence is
   reachable, hence `z ∈ G`); connectedness gives `G = Z`, so countably many
   second-countable open sets cover `Z`.
-/

open Set Topology TopologicalSpace

namespace Rado

/-- Second countability passes to a smaller subset: if `t ⊆ s` and the subspace
`s` is second countable, so is the subspace `t` (via the inclusion embedding). -/
private theorem secondCountableTopology_of_subset {Z : Type*} [TopologicalSpace Z]
    {s t : Set Z} (hst : t ⊆ s) (hs : SecondCountableTopology s) :
    SecondCountableTopology t := by
  have := hs
  exact (Topology.IsEmbedding.inclusion hst).secondCountableTopology

/-- ccc argument: a family of connected components of a fixed open set `F` in a
locally connected space, all of whose members meet a fixed second-countable
subspace `U₀`, is countable. -/
private theorem countable_components_meeting {Z : Type*} [TopologicalSpace Z]
    [LocallyConnectedSpace Z] {F U₀ : Set Z} (hF : IsOpen F)
    (hU₀ : SecondCountableTopology U₀) {𝒱 : Set (Set Z)}
    (hcomp : ∀ U ∈ 𝒱, ∃ z ∈ F, U = connectedComponentIn F z)
    (hmeet : ∀ U ∈ 𝒱, (U ∩ U₀).Nonempty) :
    𝒱.Countable := by
  have := hU₀
  -- distinct members are disjoint (they are components of the same set)
  have hdisj : ∀ U₁ ∈ 𝒱, ∀ U₂ ∈ 𝒱, U₁ ≠ U₂ → Disjoint U₁ U₂ := by
    intro U₁ hU₁ U₂ hU₂ hne
    obtain ⟨z₁, hz₁, rfl⟩ := hcomp U₁ hU₁
    obtain ⟨z₂, hz₂, rfl⟩ := hcomp U₂ hU₂
    rw [Set.disjoint_left]
    intro w hw₁ hw₂
    exact hne ((connectedComponentIn_eq hw₁).trans (connectedComponentIn_eq hw₂).symm)
  -- the traces in `U₀` form a pairwise-disjoint family of nonempty open sets
  have key : ((fun U : Set Z ↦ (Subtype.val ⁻¹' U : Set U₀)) '' 𝒱).Countable := by
    apply Rado.countable_of_pairwiseDisjoint_isOpen
    · rintro W ⟨U, hU, rfl⟩
      obtain ⟨z, hz, rfl⟩ := hcomp U hU
      exact (hF.connectedComponentIn).preimage continuous_subtype_val
    · rintro W ⟨U, hU, rfl⟩
      obtain ⟨x, hxU, hxU₀⟩ := hmeet U hU
      exact ⟨⟨x, hxU₀⟩, hxU⟩
    · rintro W₁ ⟨U₁, hU₁, rfl⟩ W₂ ⟨U₂, hU₂, rfl⟩ hne
      have hne' : U₁ ≠ U₂ := by rintro rfl; exact hne rfl
      exact (hdisj U₁ hU₁ U₂ hU₂ hne').preimage _
  -- the trace map is injective on `𝒱`
  refine Set.countable_of_injective_of_countable_image ?_ key
  intro U₁ hU₁ U₂ hU₂ hg
  have hg' : (Subtype.val ⁻¹' U₁ : Set U₀) = Subtype.val ⁻¹' U₂ := hg
  by_contra hne
  obtain ⟨x, hxU₁, hxU₀⟩ := hmeet U₁ hU₁
  have hx1 : (⟨x, hxU₀⟩ : U₀) ∈ (Subtype.val ⁻¹' U₁ : Set U₀) := hxU₁
  rw [hg'] at hx1
  exact Set.disjoint_left.mp (hdisj U₁ hU₁ U₂ hU₂ hne) hxU₁ hx1

/-- **Poincaré–Volterra lemma** (Forster 23.2). A connected Hausdorff, locally
compact, locally connected, locally second-countable space admitting a
continuous map with discrete fibers into a second-countable Hausdorff space is
second countable. -/
theorem poincare_volterra {Z : Type*} [TopologicalSpace Z] [T2Space Z] [ConnectedSpace Z]
    [LocallyCompactSpace Z] [LocallyConnectedSpace Z]
    (hloc : ∀ z : Z, ∃ U : Set Z, z ∈ U ∧ IsOpen U ∧ SecondCountableTopology U)
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    {f : Z → Y} (hf : Continuous f)
    (hdisc : ∀ z : Z, ∃ U ∈ 𝓝 z, ∀ w ∈ U, f w = f z → w = z) :
    SecondCountableTopology Z := by
  classical
  -- the empty space is trivially second countable (empty cover)
  rcases isEmpty_or_nonempty Z with hZ | hne
  · refine Rado.secondCountableTopology_of_countable_setCover (𝒰 := ∅) countable_empty
      (fun U hU ↦ absurd hU (Set.notMem_empty U))
      (fun U hU ↦ absurd hU (Set.notMem_empty U)) ?_
    rw [sUnion_empty]
    exact (Set.univ_eq_empty_iff.mpr hZ).symm
  obtain ⟨z₀⟩ := hne
  -- the family of second-countable components of preimages of basic sets
  set 𝒰 : Set (Set Z) := {U | ∃ V ∈ countableBasis Y,
      (∃ z ∈ f ⁻¹' V, U = connectedComponentIn (f ⁻¹' V) z) ∧ SecondCountableTopology U}
    with h𝒰
  have mem𝒰 : ∀ U : Set Z, U ∈ 𝒰 ↔ ∃ V ∈ countableBasis Y,
      (∃ z ∈ f ⁻¹' V, U = connectedComponentIn (f ⁻¹' V) z) ∧ SecondCountableTopology U := by
    intro U
    rw [h𝒰]
    exact Iff.rfl
  have h𝒰open : ∀ U ∈ 𝒰, IsOpen U := by
    intro U hU
    obtain ⟨V, hVB, ⟨z, hzV, rfl⟩, -⟩ := (mem𝒰 U).mp hU
    exact ((isOpen_of_mem_countableBasis hVB).preimage hf).connectedComponentIn
  have h𝒰sc : ∀ U ∈ 𝒰, SecondCountableTopology U := by
    intro U hU
    obtain ⟨V, hVB, -, hsc⟩ := (mem𝒰 U).mp hU
    exact hsc
  -- Step 1: `𝒰` refines every open neighbourhood (in particular, covers `Z`)
  have step1 : ∀ z : Z, ∀ D : Set Z, z ∈ D → IsOpen D → ∃ U ∈ 𝒰, z ∈ U ∧ U ⊆ D := by
    intro z D hzD hD
    -- a compact neighbourhood inside `D` meeting the fiber of `z` only in `z`
    obtain ⟨N, hN, hNz⟩ := hdisc z
    have hnhds : N ∩ D ∈ 𝓝 z := Filter.inter_mem hN (hD.mem_nhds hzD)
    obtain ⟨K, hKz, hKsub, hKc⟩ := local_compact_nhds hnhds
    have hzW : z ∈ interior K := mem_interior_iff_mem_nhds.mpr hKz
    have hWo : IsOpen (interior K) := isOpen_interior
    have hfrontK : frontier (interior K) ⊆ K :=
      frontier_subset_closure.trans (closure_minimal interior_subset hKc.isClosed)
    -- the frontier of `interior K` misses the fiber of `z`
    have hfront_fiber : ∀ w ∈ frontier (interior K), f w ≠ f z := by
      intro w hw hfw
      have hwz : w = z := hNz w (hKsub (hfrontK hw)).1 hfw
      rw [hWo.frontier_eq] at hw
      exact hw.2 (by rw [hwz]; exact hzW)
    -- so its image is a closed set missing `f z`
    have hfrc : IsCompact (frontier (interior K)) :=
      hKc.of_isClosed_subset isClosed_frontier hfrontK
    have himg : IsClosed (f '' frontier (interior K)) := (hfrc.image hf).isClosed
    have hfz : f z ∈ (f '' frontier (interior K))ᶜ := by
      rintro ⟨w, hw, hwz⟩
      exact hfront_fiber w hw hwz
    -- choose a basic set `V ∋ f z` avoiding that image
    obtain ⟨V, hVB, hfzV, hVsub⟩ :=
      (isBasis_countableBasis Y).exists_subset_of_mem_open hfz himg.isOpen_compl
    have hzV : z ∈ f ⁻¹' V := hfzV
    have hzU : z ∈ connectedComponentIn (f ⁻¹' V) z := mem_connectedComponentIn hzV
    have hUV : connectedComponentIn (f ⁻¹' V) z ⊆ f ⁻¹' V := connectedComponentIn_subset _ _
    -- the component of `z` avoids the frontier, hence stays inside `interior K`
    have hUsub : connectedComponentIn (f ⁻¹' V) z ⊆
        interior K ∪ (closure (interior K))ᶜ := by
      intro w hw
      rcases em (w ∈ interior K) with hwW | hwW
      · exact mem_union_left _ hwW
      · refine mem_union_right _ fun hwc ↦ ?_
        have hwf : w ∈ frontier (interior K) := by
          rw [hWo.frontier_eq]
          exact ⟨hwc, hwW⟩
        exact hVsub (hUV hw) ⟨w, hwf, rfl⟩
    have hUW : connectedComponentIn (f ⁻¹' V) z ⊆ interior K :=
      isPreconnected_connectedComponentIn.subset_left_of_subset_union hWo
        isClosed_closure.isOpen_compl (disjoint_compl_right.mono_left subset_closure)
        hUsub ⟨z, hzU, hzW⟩
    -- second countability: the component sits inside the compact `K`
    have hKsc : SecondCountableTopology K :=
      Rado.IsCompact.secondCountableTopology hKc fun w _ ↦ hloc w
    have hUK : connectedComponentIn (f ⁻¹' V) z ⊆ K := hUW.trans interior_subset
    have hUsc : SecondCountableTopology (connectedComponentIn (f ⁻¹' V) z) :=
      secondCountableTopology_of_subset hUK hKsc
    exact ⟨connectedComponentIn (f ⁻¹' V) z, (mem𝒰 _).mpr ⟨V, hVB, ⟨z, hzV, rfl⟩, hUsc⟩,
      hzU, fun w hw ↦ (hKsub (hUK hw)).2⟩
  -- Step 2: each member of `𝒰` meets only countably many members of `𝒰`
  have step2 : ∀ A ∈ 𝒰, {C : Set Z | C ∈ 𝒰 ∧ (A ∩ C).Nonempty}.Countable := by
    intro A hA
    have hAsc : SecondCountableTopology A := h𝒰sc A hA
    have hsub : {C : Set Z | C ∈ 𝒰 ∧ (A ∩ C).Nonempty} ⊆
        ⋃ V ∈ countableBasis Y,
          {U : Set Z | (∃ z ∈ f ⁻¹' V, U = connectedComponentIn (f ⁻¹' V) z) ∧
            (U ∩ A).Nonempty} := by
      rintro C ⟨hC𝒰, hCA⟩
      obtain ⟨V, hVB, hcomp, -⟩ := (mem𝒰 C).mp hC𝒰
      obtain ⟨x, hxA, hxC⟩ := hCA
      exact mem_biUnion hVB ⟨hcomp, ⟨x, hxC, hxA⟩⟩
    refine Set.Countable.mono hsub ?_
    refine (countable_countableBasis Y).biUnion fun V hVB ↦ ?_
    exact countable_components_meeting ((isOpen_of_mem_countableBasis hVB).preimage hf) hAsc
      (fun U hU ↦ hU.1) (fun U hU ↦ hU.2)
  -- Step 3: chain argument from a fixed starting member
  obtain ⟨U₀, hU₀𝒰, hz₀U₀, -⟩ := step1 z₀ univ (mem_univ z₀) isOpen_univ
  have hbranch : ∀ A : Set Z,
      {C : Set Z | A ∈ 𝒰 ∧ C ∈ 𝒰 ∧ (A ∩ C).Nonempty}.Countable := by
    intro A
    by_cases hA : A ∈ 𝒰
    · refine Set.Countable.mono ?_ (step2 A hA)
      intro C hC
      exact ⟨hC.2.1, hC.2.2⟩
    · refine Set.Countable.mono ?_ countable_empty
      intro C hC
      exact (hA hC.1).elim
  have hreach𝒰 : ∀ C : Set Z, Relation.ReflTransGen
      (fun A C : Set Z ↦ A ∈ 𝒰 ∧ C ∈ 𝒰 ∧ (A ∩ C).Nonempty) U₀ C → C ∈ 𝒰 := by
    intro C hC
    induction hC with
    | refl => exact hU₀𝒰
    | tail hab hbc ih => exact hbc.2.1
  -- the countable saturated reachable family
  obtain ⟨R, hRc, hRU₀, hR𝒰, hRsat⟩ :
      ∃ R : Set (Set Z), R.Countable ∧ U₀ ∈ R ∧ (∀ C ∈ R, C ∈ 𝒰) ∧
        ∀ A ∈ R, ∀ C ∈ 𝒰, (A ∩ C).Nonempty → C ∈ R := by
    refine ⟨{C : Set Z | Relation.ReflTransGen
        (fun A C : Set Z ↦ A ∈ 𝒰 ∧ C ∈ 𝒰 ∧ (A ∩ C).Nonempty) U₀ C},
      Rado.countable_setOf_reflTransGen U₀ hbranch, ?_, ?_, ?_⟩
    · exact Relation.ReflTransGen.refl
    · exact hreach𝒰
    · intro A hA C hC𝒰 hne
      exact Relation.ReflTransGen.tail hA ⟨hreach𝒰 A hA, hC𝒰, hne⟩
  -- the union of the reachable family is clopen and nonempty, hence everything
  have hGopen : IsOpen (⋃₀ R) := isOpen_sUnion fun U hU ↦ h𝒰open U (hR𝒰 U hU)
  have hGclosed : IsClosed (⋃₀ R) := by
    apply isClosed_of_closure_subset
    intro z hz
    obtain ⟨U, hU𝒰, hzU, -⟩ := step1 z univ (mem_univ z) isOpen_univ
    rw [mem_closure_iff] at hz
    obtain ⟨w, hwU, A, hAR, hwA⟩ := hz U (h𝒰open U hU𝒰) hzU
    exact mem_sUnion.mpr ⟨U, hRsat A hAR U hU𝒰 ⟨w, hwA, hwU⟩, hzU⟩
  have hGuniv : ⋃₀ R = univ :=
    IsClopen.eq_univ ⟨hGclosed, hGopen⟩ ⟨z₀, mem_sUnion.mpr ⟨U₀, hRU₀, hz₀U₀⟩⟩
  exact Rado.secondCountableTopology_of_countable_setCover hRc
    (fun U hU ↦ h𝒰open U (hR𝒰 U hU)) (fun U hU ↦ h𝒰sc U (hR𝒰 U hU)) hGuniv

end Rado
