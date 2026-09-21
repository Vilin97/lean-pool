/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.HasseNormPrinciple
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteLocalFamily
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalArtin
/-!
# Finite-support reduction for the global Artin map

For a finite abelian extension `L / K`, only finitely many finite local
Artin factors of an idele are nontrivial.  Keeping precisely those finite
components, together with every infinite component, gives an idele with
finite one-place support.  The quotient of the original idele by this
approximation is an actual relative-idele norm: outside the retained
finite set this follows from the local Artin kernel theorem, and at the
retained and infinite places it follows because the quotient component is
one.

Consequently both the preliminary global Artin map and the canonical
idele-class norm quotient may be evaluated on this finite-support
approximation.
-/

open scoped NumberField TensorProduct Classical BigOperators
open NumberField IsDedekindDomain
open IdeleGroup RelativeIdeleGroup

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

/-- Supply the canonical commutativity used by the finite-support norm quotient. -/
private theorem artinFiniteSupportIdeleClassIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

attribute [local instance] artinFiniteSupportIdeleClassIsMulCommutative

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L]

/-- The finite places at which the local Artin factor of `a` is
nontrivial. -/
noncomputable def globalArtinFiniteSupport
    (a : IdeleGroup K) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  (finitePlaceArtinFactors_hasFiniteMulSupport
    (K := K) (L := L) a).toFinset

/-- Membership in the finite Artin support is equivalent to nontriviality of
the corresponding chosen local Artin factor. -/
@[simp]
theorem mem_globalArtinFiniteSupport_iff
    (a : IdeleGroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    v ∈ globalArtinFiniteSupport (K := K) (L := L) a ↔
      chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v
          (IdeleGroup.finiteComponent v a) ≠ 1 := by
  unfold globalArtinFiniteSupport
  exact
    (finitePlaceArtinFactors_hasFiniteMulSupport
      (K := K) (L := L) a).mem_toFinset

/-- The finite-support Artin approximation of an idele.  It is the
product of the one-place ideles carrying all infinite components and the
one-place ideles carrying exactly the finite components with nontrivial
local Artin factor. -/
noncomputable def artinFiniteSupportApproximation
    (a : IdeleGroup K) :
    IdeleGroup K :=
  (∏ v : InfinitePlace K,
    infinitePlaceIdele v
      (IdeleGroup.infiniteComponent v a)) *
  ∏ v : ↥(globalArtinFiniteSupport
      (K := K) (L := L) a),
    finitePlaceIdele v.1
      (IdeleGroup.finiteComponent v.1 a)

/-- The finite-support Artin approximation retains every infinite
component. -/
@[simp]
theorem artinFiniteSupportApproximation_infiniteComponent
    (a : IdeleGroup K)
    (w : InfinitePlace K) :
    IdeleGroup.infiniteComponent w
        (artinFiniteSupportApproximation
          (K := K) (L := L) a) =
      IdeleGroup.infiniteComponent w a := by
  classical
  rw [artinFiniteSupportApproximation,
    prod_finitePlaceIdele_eq_ideleOfFiniteLocalFamily,
    map_mul, map_prod]
  change
    (∏ v : InfinitePlace K,
      IdeleGroup.infiniteComponent w
        (infinitePlaceIdele v
          (IdeleGroup.infiniteComponent v a))) * 1 =
      IdeleGroup.infiniteComponent w a
  rw [mul_one, Finset.prod_eq_single w]
  · exact
      infinitePlaceIdele_infiniteComponent_same w
        (IdeleGroup.infiniteComponent w a)
  · intro v _ hvw
    apply
      infinitePlaceIdele_infiniteComponent_of_ne v w
        (IdeleGroup.infiniteComponent v a)
    intro hwv
    exact hvw hwv.symm
  · intro hw
    exact (hw (Finset.mem_univ w)).elim

/-- At a finite place, the approximation is the original component
exactly on the finite Artin support and is one elsewhere. -/
theorem artinFiniteSupportApproximation_finiteComponent
    (a : IdeleGroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    IdeleGroup.finiteComponent v
        (artinFiniteSupportApproximation
          (K := K) (L := L) a) =
      if v ∈ globalArtinFiniteSupport
          (K := K) (L := L) a then
        IdeleGroup.finiteComponent v a
      else 1 := by
  classical
  rw [artinFiniteSupportApproximation,
    prod_finitePlaceIdele_eq_ideleOfFiniteLocalFamily]
  have hinfinite :
      IdeleGroup.finiteComponent v
          (∏ w : InfinitePlace K,
            infinitePlaceIdele w
              (IdeleGroup.infiniteComponent w a)) =
        1 := by
    rw [map_prod]
    apply Finset.prod_eq_one
    intro w _
    exact
      infinitePlaceIdele_finiteComponent w v
        (IdeleGroup.infiniteComponent w a)
  rw [map_mul, hinfinite, one_mul]
  change
    IdeleGroup.finiteIdeleOfFinset
        (globalArtinFiniteSupport
          (K := K) (L := L) a)
        (fun w =>
          IdeleGroup.finiteComponent w.1 a) v =
      if v ∈ globalArtinFiniteSupport
          (K := K) (L := L) a then
        IdeleGroup.finiteComponent v a
      else 1
  by_cases hv :
      v ∈ globalArtinFiniteSupport
        (K := K) (L := L) a
  · rw [ite_eq_left hv]
    exact
      IdeleGroup.finiteIdeleOfFinset_apply_mem
        (globalArtinFiniteSupport
          (K := K) (L := L) a)
        (fun w =>
          IdeleGroup.finiteComponent w.1 a)
        ⟨v, hv⟩
  · rw [ite_eq_right hv]
    exact
      IdeleGroup.finiteIdeleOfFinset_apply_notMem
        (globalArtinFiniteSupport
          (K := K) (L := L) a)
        (fun w =>
          IdeleGroup.finiteComponent w.1 a)
        v hv

/-- At a place in the Artin support, the finite-support approximation keeps
the original finite component. -/
@[simp]
theorem artinFiniteSupportApproximation_finiteComponent_of_mem
    (a : IdeleGroup K)
    (v : HeightOneSpectrum (𝓞 K))
    (hv :
      v ∈ globalArtinFiniteSupport
        (K := K) (L := L) a) :
    IdeleGroup.finiteComponent v
        (artinFiniteSupportApproximation
          (K := K) (L := L) a) =
      IdeleGroup.finiteComponent v a := by
  rw [artinFiniteSupportApproximation_finiteComponent,
    ite_eq_left hv]

/-- Away from the Artin support, the finite-support approximation has trivial
finite component. -/
@[simp]
theorem artinFiniteSupportApproximation_finiteComponent_of_notMem
    (a : IdeleGroup K)
    (v : HeightOneSpectrum (𝓞 K))
    (hv :
      v ∉ globalArtinFiniteSupport
        (K := K) (L := L) a) :
    IdeleGroup.finiteComponent v
        (artinFiniteSupportApproximation
          (K := K) (L := L) a) =
      1 := by
  rw [artinFiniteSupportApproximation_finiteComponent,
    ite_eq_right hv]

/-- The quotient of an idele by its finite-support Artin approximation
is an actual relative-idele norm. -/
theorem
    artinFiniteSupportApproximation_remainder_mem_relativeIdeleNorm_range
    (a : IdeleGroup K) :
    a * (artinFiniteSupportApproximation
        (K := K) (L := L) a)⁻¹ ∈
      (RelativeIdeleGroup.norm K L).range := by
  rw [
    _root_.GlobalClassFieldTheory.ClassFieldAxiom.relativeIdeleNorm_range_eq_allPlaceLocalNormCondition]
  constructor
  · rw [_root_.GlobalClassFieldTheory.ClassFieldAxiom.allFinitePlaceLocalNormCondition]
    apply Subgroup.mem_iInf.mpr
    intro v
    change
      IdeleGroup.finiteComponent v
          (a * (artinFiniteSupportApproximation
            (K := K) (L := L) a)⁻¹) ∈
        _root_.chosenFinitePlaceLocalNormSubgroup
          (K := K) (L := L) v
    by_cases hv :
        v ∈ globalArtinFiniteSupport
          (K := K) (L := L) a
    · rw [map_mul, map_inv,
        artinFiniteSupportApproximation_finiteComponent_of_mem
          (K := K) (L := L) a v hv,
        mul_inv_cancel]
      exact Subgroup.one_mem _
    · have hArtin :
          chosenFinitePlaceArtinMonoidHom
              (K := K) (L := L) v
              (IdeleGroup.finiteComponent v a) =
            1 := by
        by_contra hne
        exact hv
          ((mem_globalArtinFiniteSupport_iff
            (K := K) (L := L) a v).2 hne)
      have hLocalNorm :
          IdeleGroup.finiteComponent v a ∈
            _root_.chosenFinitePlaceLocalNormSubgroup
              (K := K) (L := L) v := by
        rw [← chosenFinitePlaceArtinMonoidHom_ker
          (K := K) (L := L) v]
        exact MonoidHom.mem_ker.mpr hArtin
      simpa only [map_mul, map_inv,
        artinFiniteSupportApproximation_finiteComponent_of_notMem
          (K := K) (L := L) a v hv,
        inv_one, mul_one] using hLocalNorm
  · rw [_root_.GlobalClassFieldTheory.ClassFieldAxiom.allInfinitePlaceLocalNormCondition]
    apply Subgroup.mem_iInf.mpr
    intro v
    change
      IdeleGroup.infiniteComponent v
          (a * (artinFiniteSupportApproximation
            (K := K) (L := L) a)⁻¹) ∈
        (Units.map
          (Algebra.norm v.Completion :
            (v.Completion ⊗[K] L) →* v.Completion)).range
    rw [map_mul, map_inv,
      artinFiniteSupportApproximation_infiniteComponent,
      mul_inv_cancel]
    exact Subgroup.one_mem _

omit [IsAbelianGalois K L] in
/-- The canonical idele-class norm quotient kills every actual
relative-idele norm. -/
@[simp]
theorem globalNormClassFromIdele_relativeIdeleNorm_eq_one
    (z : RelativeIdeleGroup K L) :
    globalNormClassFromIdele K L
        (RelativeIdeleGroup.norm K L z) =
      1 := by
  change
    QuotientGroup.mk'
        (_root_.ideleClassNorm K L).range
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K)
          (RelativeIdeleGroup.norm K L z)) =
      1
  apply (QuotientGroup.eq_one_iff _).2
  refine
    ⟨QuotientGroup.mk'
        (IdeleGroup.principalSubgroup L)
        (relativeIdeleBaseChangeMulEquiv
          (K := K) (L := L) z), ?_⟩
  rw [_root_.ideleClassNorm_mk,
    IdeleGroup.norm_relativeIdeleBaseChangeMulEquiv]

/-- The global Artin value of an idele is already determined by its
finite-support Artin approximation. -/
theorem globalArtinMonoidHom_eq_artinFiniteSupportApproximation
    (a : IdeleGroup K) :
    globalArtinMonoidHom (K := K) (L := L) a =
      globalArtinMonoidHom (K := K) (L := L)
        (artinFiniteSupportApproximation
          (K := K) (L := L) a) := by
  obtain ⟨z, hz⟩ :=
    artinFiniteSupportApproximation_remainder_mem_relativeIdeleNorm_range
      (K := K) (L := L) a
  have hquotient :
      globalArtinMonoidHom (K := K) (L := L)
          (a * (artinFiniteSupportApproximation
            (K := K) (L := L) a)⁻¹) =
        1 := by
    rw [← hz]
    exact
      globalArtinMonoidHom_relativeIdeleNorm_eq_one
        (K := K) (L := L) z
  have hmul :
      globalArtinMonoidHom (K := K) (L := L) a *
          (globalArtinMonoidHom (K := K) (L := L)
            (artinFiniteSupportApproximation
              (K := K) (L := L) a))⁻¹ =
        1 := by
    simpa only [map_mul, map_inv] using hquotient
  exact mul_inv_eq_one.mp hmul

/-- The norm class of an idele is already determined by its
finite-support Artin approximation. -/
theorem globalNormClassFromIdele_eq_artinFiniteSupportApproximation
    (a : IdeleGroup K) :
    globalNormClassFromIdele K L a =
      globalNormClassFromIdele K L
        (artinFiniteSupportApproximation
          (K := K) (L := L) a) := by
  obtain ⟨z, hz⟩ :=
    artinFiniteSupportApproximation_remainder_mem_relativeIdeleNorm_range
      (K := K) (L := L) a
  have hquotient :
      globalNormClassFromIdele K L
          (a * (artinFiniteSupportApproximation
            (K := K) (L := L) a)⁻¹) =
        1 := by
    rw [← hz]
    exact
      globalNormClassFromIdele_relativeIdeleNorm_eq_one
        (K := K) (L := L) z
  have hmul :
      globalNormClassFromIdele K L a *
          (globalNormClassFromIdele K L
            (artinFiniteSupportApproximation
              (K := K) (L := L) a))⁻¹ =
        1 := by
    simpa only [map_mul, map_inv] using hquotient
  exact mul_inv_eq_one.mp hmul

end Reciprocity
end GlobalClassFieldTheory
