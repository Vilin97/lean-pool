/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.Topology.Algebra.Group.TopologicalAbelianization
/-!
# Absolute abelianization inside the separable closure

For an arbitrary field, this module identifies the topological abelianization
of the Galois group of its separable closure with the Galois group of the
maximal abelian subextension.  Working inside the separable closure makes the
construction uniform in every characteristic.
-/

noncomputable section

open scoped IsMulCommutative

variable (K : Type) [Field K]

/-- The closure of the commutator subgroup of the separable absolute Galois
group, packaged as a closed subgroup. -/
def absoluteCommutatorClosure :
    ClosedSubgroup Gal(SeparableClosure K/K) where
  toSubgroup :=
    (commutator Gal(SeparableClosure K/K)).topologicalClosure
  isClosed' := Subgroup.isClosed_topologicalClosure _

/-- The topological closure of the absolute commutator subgroup is normal. -/
instance absoluteCommutatorClosure_normal :
    (absoluteCommutatorClosure K).Normal := by
  change
    ((commutator Gal(SeparableClosure K/K)).topologicalClosure).Normal
  infer_instance

/-- The maximal abelian subextension of the separable closure. -/
def maximalAbelianExtension :
    IntermediateField K (SeparableClosure K) :=
  IntermediateField.fixedField (absoluteCommutatorClosure K).toSubgroup

/-- The maximal abelian subextension is Galois over the base field. -/
instance maximalAbelianExtension_isGalois :
    IsGalois K (maximalAbelianExtension K) := by
  apply (InfiniteGalois.normal_iff_isGalois
    (maximalAbelianExtension K)).1
  change
    (IntermediateField.fixedField
      (absoluteCommutatorClosure K).toSubgroup).fixingSubgroup.Normal
  rw [InfiniteGalois.fixingSubgroup_fixedField
    (absoluteCommutatorClosure K)]
  infer_instance

/-- The algebraic quotient equivalence from the absolute topological
abelianization to the Galois group of the maximal abelian extension. -/
noncomputable def absoluteAbelianizationMulEquivMaximalAbelianGalois :
    TopologicalAbelianization Gal(SeparableClosure K/K) ≃*
      Gal(maximalAbelianExtension K/K) :=
  InfiniteGalois.normalAutEquivQuotient (absoluteCommutatorClosure K)

/-- The algebraic equivalence sends a quotient class to restriction to the
maximal abelian extension. -/
@[simp]
theorem absoluteAbelianizationMulEquivMaximalAbelianGalois_mk
    (sigma : Gal(SeparableClosure K/K)) :
    absoluteAbelianizationMulEquivMaximalAbelianGalois K
        (QuotientGroup.mk sigma) =
      AlgEquiv.restrictNormalHom (maximalAbelianExtension K) sigma :=
  rfl

/-- The algebraic equivalence from the absolute abelianization is continuous. -/
theorem absoluteAbelianizationMulEquivMaximalAbelianGalois_continuous :
    Continuous (absoluteAbelianizationMulEquivMaximalAbelianGalois K) := by
  apply (QuotientGroup.isQuotientMap_mk
    (absoluteCommutatorClosure K).toSubgroup).continuous_iff.2
  refine (InfiniteGalois.restrictNormalHom_continuous
    (maximalAbelianExtension K)).congr ?_
  intro sigma
  exact
    (absoluteAbelianizationMulEquivMaximalAbelianGalois_mk K sigma).symm

/-- The canonical topological identification of the absolute separable
Galois group's abelianization with the maximal abelian Galois group. -/
noncomputable def absoluteTopologicalAbelianizationEquivMaximalAbelianGalois :
    TopologicalAbelianization Gal(SeparableClosure K/K) ≃ₜ*
      Gal(maximalAbelianExtension K/K) := by
  letI : T2Space Gal(maximalAbelianExtension K/K) :=
    krullTopology_t2
  let h :
      TopologicalAbelianization Gal(SeparableClosure K/K) ≃ₜ
        Gal(maximalAbelianExtension K/K) :=
    Continuous.homeoOfEquivCompactToT2
      (f := (absoluteAbelianizationMulEquivMaximalAbelianGalois K).toEquiv)
      (absoluteAbelianizationMulEquivMaximalAbelianGalois_continuous K)
  exact
    { h with
      map_mul' :=
        (absoluteAbelianizationMulEquivMaximalAbelianGalois K).map_mul }

/-- The absolute topological abelianization is totally disconnected. -/
instance absoluteTopologicalAbelianization_totallyDisconnectedSpace :
    TotallyDisconnectedSpace
      (TopologicalAbelianization Gal(SeparableClosure K/K)) :=
  Homeomorph.totallyDisconnectedSpace
    (absoluteTopologicalAbelianizationEquivMaximalAbelianGalois K).symm.toHomeomorph

/-- The maximal abelian subextension has an abelian Galois group. -/
instance maximalAbelianExtension_isAbelianGalois :
    IsAbelianGalois K (maximalAbelianExtension K) where
  is_comm.comm sigma tau := by
    apply
      (absoluteTopologicalAbelianizationEquivMaximalAbelianGalois K).symm.injective
    simp only [map_mul]
    exact mul_comm _ _

/-- Every finite abelian intermediate field of the separable closure is
contained in the maximal abelian extension. -/
theorem finiteAbelianIntermediateField_le_maximalAbelianExtension
    (E : IntermediateField K (SeparableClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E] :
    E ≤ maximalAbelianExtension K := by
  rw [maximalAbelianExtension, IntermediateField.le_iff_le]
  change
    (commutator Gal(SeparableClosure K/K)).topologicalClosure ≤
      E.fixingSubgroup
  apply Subgroup.topologicalClosure_minimal
  · rw [← E.restrictNormalHom_ker]
    exact
      Abelianization.commutator_subset_ker
        (AlgEquiv.restrictNormalHom
          (F := K) (K₁ := SeparableClosure K) E)
  · exact E.fixingSubgroup_isClosed

/-- A selected embedding of a finite abelian extension into the maximal
abelian extension.  Naming this embedding keeps downstream finite-coordinate
arguments independent of the implementation of the separable closure. -/
noncomputable def finiteAbelianExtensionEmbeddingIntoMaximalAbelianExtension
    (L : Type*) [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L] :
    L →ₐ[K] maximalAbelianExtension K := by
  let i : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let e : L ≃ₐ[K] i.fieldRange := i.equivFieldRange
  letI : FiniteDimensional K i.fieldRange :=
    e.toLinearEquiv.finiteDimensional
  letI : IsAbelianGalois K i.fieldRange :=
    IsAbelianGalois.of_algHom e.symm.toAlgHom
  have hle : i.fieldRange ≤ maximalAbelianExtension K :=
    finiteAbelianIntermediateField_le_maximalAbelianExtension K i.fieldRange
  exact
    i.codRestrict (maximalAbelianExtension K).toSubalgebra
      (fun x => hle (AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩))

/-- The finite Galois intermediate field of the maximal abelian extension
selected by a finite abelian extension. -/
noncomputable def finiteAbelianExtensionInMaximalAbelianExtension
    (L : Type*) [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L] :
    FiniteGaloisIntermediateField K (maximalAbelianExtension K) :=
  let j := finiteAbelianExtensionEmbeddingIntoMaximalAbelianExtension K L
  { toIntermediateField := j.fieldRange
    finiteDimensional := j.equivFieldRange.toLinearEquiv.finiteDimensional
    isGalois := IsGalois.of_algEquiv j.equivFieldRange }

/-- The selected finite layer is canonically equivalent to the original
finite abelian extension. -/
noncomputable def finiteAbelianExtensionEquivInMaximalAbelianExtension
    (L : Type*) [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L] :
    L ≃ₐ[K] finiteAbelianExtensionInMaximalAbelianExtension K L :=
  (finiteAbelianExtensionEmbeddingIntoMaximalAbelianExtension K L).equivFieldRange
