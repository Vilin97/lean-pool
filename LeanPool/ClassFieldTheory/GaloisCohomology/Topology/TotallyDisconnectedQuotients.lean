/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.Group.Quotient
/-!
# Totally disconnected quotient groups

This file proves that a closed normal quotient of a compact Hausdorff totally
disconnected topological group is totally disconnected.
-/

namespace QuotientGroup

/-- A closed normal quotient of a compact Hausdorff totally disconnected
topological group is totally disconnected. -/
theorem totallyDisconnectedSpace_of_isClosed
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    TotallyDisconnectedSpace (G ⧸ N) := by
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hsep : Pairwise (fun a b : G ⧸ N =>
      ∃ U : Set (G ⧸ N), IsClopen U ∧ a ∈ U ∧ b ∈ Uᶜ) := by
    intro a b hab
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N b
    let g : G := x⁻¹ * y
    have hgN : g ∉ N := by
      intro hgN
      apply hab
      apply inv_mul_eq_one.mp
      change q g = 1
      exact (QuotientGroup.eq_one_iff g).2 hgN
    let W : Set G := {u | g * u⁻¹ ∉ N}
    have hWopen : IsOpen W := by
      change IsOpen ((fun u : G => g * u⁻¹) ⁻¹' ((N : Set G)ᶜ))
      exact hN.isOpen_compl.preimage (continuous_const.mul continuous_inv)
    have hWone : (1 : G) ∈ W := by
      simpa only [W, Set.mem_ofPred_eq, inv_one, mul_one] using hgN
    obtain ⟨V, hVW⟩ :=
      ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
        (G := G) hWopen hWone
    let K : Subgroup G := N ⊔ (V : Subgroup G)
    have hKopen : IsOpen (K : Set G) :=
      Subgroup.isOpen_of_openSubgroup K
        (show (V : Subgroup G) ≤ K from le_sup_right)
    have hNK : N ≤ K := le_sup_left
    have hgK : g ∉ K := by
      intro hgK
      rcases (Subgroup.mem_sup_of_normal_right
          (s := N) (t := (V : Subgroup G))).1 hgK with
        ⟨n, hnN, v, hvV, hnv⟩
      have hvW : v ∈ W := hVW hvV
      have hgn : g * v⁻¹ = n := by
        calc
          g * v⁻¹ = (n * v) * v⁻¹ := by rw [hnv]
          _ = n := by simp only [mul_assoc, mul_inv_cancel, mul_one]
      apply hvW
      simpa only [hgn] using hnN
    let Kbar : Subgroup (G ⧸ N) := K.map q
    have hKbarOpen : IsOpen (Kbar : Set (G ⧸ N)) := by
      change IsOpen (((↑) : G → G ⧸ N) '' (K : Set G))
      exact QuotientGroup.isOpenMap_coe (K : Set G) hKopen
    have hqgKbar : q g ∉ Kbar := by
      intro hqgKbar
      have hgComap : g ∈ Kbar.comap q := hqgKbar
      have hker : q.ker ≤ K := by
        simpa only [q, QuotientGroup.ker_mk'] using hNK
      have hcomap : Kbar.comap q = K := by
        simpa only [Kbar] using Subgroup.comap_map_eq_self hker
      rw [hcomap] at hgComap
      exact hgK hgComap
    let U : Set (G ⧸ N) := {z | (q x)⁻¹ * z ∈ Kbar}
    have hUclopen : IsClopen U := by
      have hcont : Continuous (fun z : G ⧸ N => (q x)⁻¹ * z) :=
        (continuous_const :
          Continuous (fun _ : G ⧸ N => (q x)⁻¹)).mul continuous_id
      exact
        ⟨(Subgroup.isClosed_of_isOpen Kbar hKbarOpen).preimage hcont,
          hKbarOpen.preimage hcont⟩
    refine ⟨U, hUclopen, ?_, ?_⟩
    · change (q x)⁻¹ * q x ∈ Kbar
      rw [inv_mul_cancel]
      exact Kbar.one_mem
    · change (q x)⁻¹ * q y ∉ Kbar
      change q (x⁻¹ * y) ∉ Kbar at hqgKbar
      simpa only [map_mul, map_inv] using hqgKbar
  let : TotallySeparatedSpace (G ⧸ N) :=
    totallySeparatedSpace_iff_exists_isClopen.2 hsep
  infer_instance

end QuotientGroup

namespace QuotientGroup

/-- The identity component of a topological group is a normal subgroup. -/
instance Subgroup.Normal.connectedComponentOfOne
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    (Subgroup.connectedComponentOfOne G).Normal where
  conj_mem x hx g := by
    change g * x * g⁻¹ ∈ connectedComponent (1 : G)
    simpa only [mul_one, mul_inv_cancel] using
      (IsTopologicalGroup.continuous_conj g).mapsTo_connectedComponent
        (1 : G) hx

/-- Quotienting a topological group by its identity component produces a
totally disconnected topological group. -/
theorem totallyDisconnectedSpace_quotient_connectedComponentOfOne
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    TotallyDisconnectedSpace
      (G ⧸ Subgroup.connectedComponentOfOne G) := by
  let N : Subgroup G := Subgroup.connectedComponentOfOne G
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hfibers : ∀ y : G ⧸ N, IsConnected (q ⁻¹' {y}) := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N y
    have hfiber :
        q ⁻¹' {q g} =
          (fun x : G ↦ x * g) '' connectedComponent (1 : G) := by
      ext x
      constructor
      · intro hx
        change q x = q g at hx
        have hxN : x / g ∈ N := QuotientGroup.eq_iff_div_mem.mp hx
        exact ⟨x / g, hxN, div_mul_cancel x g⟩
      · rintro ⟨n, hn, rfl⟩
        change q (n * g) = q g
        rw [map_mul]
        have hnN : n ∈ N := hn
        have hqn : q n = 1 := by
          change (n : G ⧸ N) = 1
          exact (QuotientGroup.eq_one_iff n).2 hnN
        rw [hqn, one_mul]
    rw [hfiber]
    exact
      isConnected_connectedComponent.image _
        (continuous_id.mul continuous_const).continuousOn
  apply totallyDisconnectedSpace_iff_connectedComponent_one.mpr
  apply (QuotientGroup.mk'_surjective N).preimage_injective
  change
    (QuotientGroup.mk ⁻¹'
        connectedComponent (1 : G ⧸ N)) =
      QuotientGroup.mk ⁻¹' {1}
  calc
    QuotientGroup.mk ⁻¹'
        connectedComponent (1 : G ⧸ N) =
        connectedComponent (1 : G) := by
      simpa only [QuotientGroup.mk_one] using
        (QuotientGroup.isQuotientMap_mk N).isCoinducing.preimage_connectedComponent
          hfibers (1 : G)
    _ = (N : Set G) := rfl
    _ = QuotientGroup.mk ⁻¹' {1} := by
      ext x
      change x ∈ N ↔ (QuotientGroup.mk x : G ⧸ N) = 1
      exact (QuotientGroup.eq_one_iff x).symm

end QuotientGroup

namespace ContinuousMonoidHom

/-- A continuous homomorphism from a topological group to a totally disconnected
topological group vanishes on the identity component. -/
theorem connectedComponentOfOne_le_ker
    {G H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TotallyDisconnectedSpace H]
    (f : G →ₜ* H) :
    Subgroup.connectedComponentOfOne G ≤ f.ker := by
  intro g hg
  have hfg : f g ∈ connectedComponent (1 : H) := by
    have hmap : f g ∈ connectedComponent (f (1 : G)) :=
      f.continuous_toFun.mapsTo_connectedComponent (1 : G) hg
    simpa only [map_one] using hmap
  have hcomponent : connectedComponent (1 : H) = {1} :=
    totallyDisconnectedSpace_iff_connectedComponent_singleton.mp inferInstance 1
  change f g = 1
  simpa only [hcomponent, Set.mem_singleton_iff] using hfg

end ContinuousMonoidHom
