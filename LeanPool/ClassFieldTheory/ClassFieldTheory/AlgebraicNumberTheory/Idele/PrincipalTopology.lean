/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.Core
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.SPlaces
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
/-!
# The topology of the principal ideles

This file proves that the principal ideles form a discrete,
and hence closed, subgroup of the idele group.

The proof uses the same arithmetic separation as the classical argument.
The finite-place condition forces a principal idele into the ring of
integers.  Its infinite component then lies in the Minkowski integer lattice,
whose topology is discrete.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace IdeleGroup

/-- The infinite component of an idele, written in Minkowski space. -/
def infiniteMixedEmbedding (a : IdeleGroup K) :
    NumberField.mixedEmbedding.mixedSpace K :=
  NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K
    (a.1 : NumberField.InfiniteAdeleRing K)

theorem continuous_infiniteMixedEmbedding :
    Continuous (infiniteMixedEmbedding (K := K)) := by
  rw [show infiniteMixedEmbedding (K := K) = fun a =>
      (fun v : {w : InfinitePlace K // w.IsReal} =>
          NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
            v.2 ((a.1 : NumberField.InfiniteAdeleRing K) v),
       fun v : {w : InfinitePlace K // w.IsComplex} =>
          NumberField.InfinitePlace.Completion.extensionEmbedding v.1
            ((a.1 : NumberField.InfiniteAdeleRing K) v)) by
    funext a
    exact NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace_apply K _]
  apply Continuous.prodMk
  · apply continuous_pi
    intro v
    have hcomponent :
        Continuous (fun a : IdeleGroup K =>
          ((a.1 : NumberField.InfiniteAdeleRing K)
            (v : InfinitePlace K))) := by
      exact
        Units.continuous_val.comp
          (infiniteComponentContinuous
            (v : InfinitePlace K)).continuous
    exact
      (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
        v.2).continuous.comp hcomponent
  · apply continuous_pi
    intro v
    have hcomponent :
        Continuous (fun a : IdeleGroup K =>
          ((a.1 : NumberField.InfiniteAdeleRing K)
            (v : InfinitePlace K))) := by
      exact
        Units.continuous_val.comp
          (infiniteComponentContinuous
            (v : InfinitePlace K)).continuous
    exact
      (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding
        v.1).continuous.comp hcomponent

@[simp]
theorem infiniteMixedEmbedding_principal (x : Kˣ) :
    infiniteMixedEmbedding (principalIdele K x) =
      NumberField.mixedEmbedding K (x : K) := by
  rw [infiniteMixedEmbedding,
    NumberField.InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  rfl

omit [NumberField K] in
theorem mixedEmbedding_one_mem_integerLattice :
    NumberField.mixedEmbedding K (1 : K) ∈
      NumberField.mixedEmbedding.integerLattice K := by
  change _ ∈ LinearMap.range _
  refine ⟨1, ?_⟩
  simp

/-- A principal idele that is a unit at every finite place has infinite
component in the Minkowski integer lattice. -/
theorem principal_infiniteMixedEmbedding_mem_integerLattice
    (x : Kˣ)
    (hx : principalIdele K x ∈
      integralAtFinitePlaces (K := K)) :
    infiniteMixedEmbedding (principalIdele K x) ∈
      NumberField.mixedEmbedding.integerLattice K := by
  have hker :
      fractionalIdeal (principalIdele K x) = 1 := by
    rw [← MonoidHom.mem_ker, fractionalIdeal_ker]
    exact hx
  have hprincipal :
      toPrincipalIdeal (𝓞 K) K x = 1 := by
    rw [← fractionalIdeal_principalIdele]
    exact hker
  have hxmem :
      (x : K) ∈
        (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    rw [← show
      ((toPrincipalIdeal (𝓞 K) K x :
          FractionalIdealGroup K) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = 1 by
          exact congrArg Units.val hprincipal,
      coe_toPrincipalIdeal]
    exact FractionalIdeal.mem_spanSingleton_self _ _
  obtain ⟨y, hy⟩ :=
    (FractionalIdeal.mem_one_iff
      (nonZeroDivisors (𝓞 K))).mp hxmem
  rw [infiniteMixedEmbedding_principal]
  change _ ∈ LinearMap.range _
  refine ⟨y, ?_⟩
  change NumberField.mixedEmbedding K
      (algebraMap (𝓞 K) K y) =
    NumberField.mixedEmbedding K (x : K)
  rw [hy]

/-- The principal ideles have the discrete subspace
topology. -/
instance principalSubgroupDiscreteTopology :
    DiscreteTopology (principalSubgroup K) := by
  rw [discreteTopology_iff_isOpen_singleton_one]
  let z : NumberField.mixedEmbedding.integerLattice K :=
    ⟨NumberField.mixedEmbedding K (1 : K),
      mixedEmbedding_one_mem_integerLattice (K := K)⟩
  have hzOpen :
      IsOpen ({z} :
        Set (NumberField.mixedEmbedding.integerLattice K)) :=
    isOpen_discrete _
  rw [isOpen_induced_iff] at hzOpen
  obtain ⟨U, hU, hUeq⟩ := hzOpen
  have hzU :
      (z : NumberField.mixedEmbedding.mixedSpace K) ∈ U := by
    have hz :
        z ∈ Subtype.val ⁻¹' U :=
      hUeq.symm ▸ Set.mem_singleton z
    exact hz
  let V : Set (IdeleGroup K) :=
    (integralAtFinitePlaces (K := K) : Set (IdeleGroup K)) ∩
      infiniteMixedEmbedding ⁻¹' U
  have hIntegralOpen :
      IsOpen
        ((integralAtFinitePlaces (K := K) :
          Subgroup (IdeleGroup K)) : Set (IdeleGroup K)) := by
    have h :=
      isOpen_supportedAt (K := K)
        (∅ : Finset (HeightOneSpectrum (𝓞 K)))
    simpa only [Finset.coe_empty, supportedAt_empty (K := K)] using h
  have hVOpen : IsOpen V :=
    hIntegralOpen.inter
      (hU.preimage continuous_infiniteMixedEmbedding)
  have hpreOpen :
      IsOpen
        (Subtype.val ⁻¹' V :
          Set (principalSubgroup K)) :=
    hVOpen.preimage continuous_subtype_val
  have hpre :
      (Subtype.val ⁻¹' V :
          Set (principalSubgroup K)) = {1} := by
    ext p
    constructor
    · intro hp
      change (p : IdeleGroup K) ∈ V at hp
      obtain ⟨x, hx⟩ := p.property
      have hxIntegral :
          principalIdele K x ∈
            integralAtFinitePlaces (K := K) := by
        rw [hx]
        exact hp.1
      let y : NumberField.mixedEmbedding.integerLattice K :=
        ⟨infiniteMixedEmbedding (principalIdele K x),
          principal_infiniteMixedEmbedding_mem_integerLattice x hxIntegral⟩
      have hyU :
          (y : NumberField.mixedEmbedding.mixedSpace K) ∈ U := by
        change infiniteMixedEmbedding (principalIdele K x) ∈ U
        rw [hx]
        exact hp.2
      have hySingleton : y ∈ ({z} :
          Set (NumberField.mixedEmbedding.integerLattice K)) := by
        rw [← hUeq]
        exact hyU
      have hyz : y = z := Set.mem_singleton_iff.mp hySingleton
      have hmix :
          NumberField.mixedEmbedding K (x : K) =
            NumberField.mixedEmbedding K (1 : K) := by
        simpa [y, z] using congrArg Subtype.val hyz
      have hxOne : x = 1 := by
        apply Units.ext
        exact NumberField.mixedEmbedding_injective K hmix
      apply Set.mem_singleton_iff.mpr
      apply Subtype.ext
      rw [← hx, hxOne, map_one]
      rfl
    · intro hp
      have hpOne : p = 1 := Set.mem_singleton_iff.mp hp
      subst p
      change (1 : IdeleGroup K) ∈ V
      constructor
      · exact (integralAtFinitePlaces (K := K)).one_mem
      · change infiniteMixedEmbedding (1 : IdeleGroup K) ∈ U
        rw [← map_one (principalIdele K),
          infiniteMixedEmbedding_principal]
        exact hzU
  rw [← hpre]
  exact hpreOpen

/-- The principal ideles form a closed subgroup. -/
theorem principalSubgroup_isClosed :
    IsClosed
      ((principalSubgroup K :
        Subgroup (IdeleGroup K)) : Set (IdeleGroup K)) :=
  Subgroup.isClosed_of_discreteTopology

end IdeleGroup
