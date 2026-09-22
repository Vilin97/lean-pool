/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormConductor
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidue
import Mathlib.FieldTheory.KrullTopology
import Mathlib.Topology.Algebra.Group.Quotient
/-!
# Topological global norm-residue reciprocity

For a finite abelian extension of number fields, the genuine
idele-class norm range is open in the ordinary idele-class topology.
Hence its native quotient topology is discrete.  The finite Krull
Galois group is discrete as well, so the algebraic global norm-residue
equivalence upgrades to a homeomorphic multiplicative equivalence.

This file also bundles the quotient map and the global norm-residue map
as continuous homomorphisms, and proves that forgetting their topology
recovers the previously constructed actual global norm-residue symbol.
-/

open scoped IsMulCommutative NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

/-- Fix the canonical class-group dictionary before bundling norm-quotient maps. -/
@[instance_reducible]
private noncomputable def topologicalNormResidueIdeleClassCommGroup
    (F : Type) [Field F] [NumberField F] :
    CommGroup (IdeleClassGroup F) :=
  QuotientGroup.Quotient.commGroup (IdeleGroup.principalSubgroup F)

attribute [local instance] topologicalNormResidueIdeleClassCommGroup

private theorem topologicalNormResidueIdeleClassIsMulCommutative
    (F : Type) [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  IsMulCommutative.of_comm (fun a b => mul_comm a b)

attribute [local instance] topologicalNormResidueIdeleClassIsMulCommutative

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

/-- The native quotient topology on
`C_K / N_{L/K}(C_L)` is discrete because the genuine ordinary
idele-class norm range is open. -/
theorem ideleClassNormQuotient_discreteTopology :
    DiscreteTopology
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) := by
  apply QuotientGroup.discreteTopology
  exact
    GlobalClassFields.ideleClassNorm_range_isOpen
      (K := K) (L := L)

/-- Global norm-residue reciprocity as a homeomorphic multiplicative
equivalence between the native norm quotient and the finite Krull
Galois group.  Both directions are continuous in their genuine
topologies. -/
noncomputable def globalNormResidueContinuousMulEquiv :
    (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) ≃ₜ*
      Gal(L/K) := by
  let : DiscreteTopology
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :=
    ideleClassNormQuotient_discreteTopology K L
  let e :
      (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) ≃*
        Gal(L/K) :=
    AddEquiv.toMultiplicative
      (globalNormResidueEquiv K L)
  exact
    { e with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

/-- Evaluation of the topological norm-residue equivalence is the
existing actual norm-residue equivalence on the same quotient class. -/
@[simp]
theorem globalNormResidueContinuousMulEquiv_apply
    (c :
      IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :
    globalNormResidueContinuousMulEquiv K L c =
      Additive.toMul
        (globalNormResidueEquiv K L
          (Additive.ofMul c)) := by
  rfl

/-- Global reciprocity in the direction used by the class-field
correspondence,

`Gal(L / K) ≃ₜ* C_K / N_{L/K}(C_L)`.

This is the inverse of the norm-residue equivalence as a
`ContinuousMulEquiv`, so the Krull topology on the finite Galois group
and the native quotient topology on the idele-class quotient are part
of the public statement. -/
noncomputable def globalReciprocityContinuousMulEquiv :
    Gal(L/K) ≃ₜ*
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :=
  (globalNormResidueContinuousMulEquiv K L).symm

/-- Evaluation of topological global reciprocity is the inverse of the
actual norm-residue equivalence, with no additional choice of an
abstract group isomorphism. -/
@[simp]
theorem globalReciprocityContinuousMulEquiv_apply
    (σ : Gal(L/K)) :
    globalReciprocityContinuousMulEquiv K L σ =
      Additive.toMul
        ((globalNormResidueEquiv K L).symm
          (Additive.ofMul σ)) := by
  rfl

/-- The genuine quotient map
`C_K → C_K / N_{L/K}(C_L)`, bundled with continuity for the native
ordinary quotient topology. -/
noncomputable def ideleClassNormQuotientContinuousMonoidHom :
    IdeleClassGroup K →ₜ*
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :=
  { QuotientGroup.mk'
      (_root_.ideleClassNorm K L).range with
    continuous_toFun := QuotientGroup.continuous_mk }

/-- The actual global norm-residue map, bundled as a continuous
homomorphism on the ordinary idele-class topology. -/
noncomputable def globalNormResidueContinuousMonoidHom :
    IdeleClassGroup K →ₜ* Gal(L/K) :=
  (ContinuousMonoidHom.toContinuousMonoidHom
      (globalNormResidueContinuousMulEquiv K L)).comp
    (ideleClassNormQuotientContinuousMonoidHom K L)

/-- Evaluation of the continuous global norm-residue map agrees with
the existing actual global norm-residue symbol. -/
@[simp]
theorem globalNormResidueContinuousMonoidHom_apply
    (c : IdeleClassGroup K) :
    globalNormResidueContinuousMonoidHom K L c =
      globalNormResidueMonoidHom K L c := by
  rfl

/-- The existing actual global norm-residue homomorphism is continuous
for the ordinary idele-class topology and the finite Krull topology. -/
theorem globalNormResidueMonoidHom_continuous :
    Continuous (globalNormResidueMonoidHom K L) :=
  (globalNormResidueContinuousMonoidHom K L).continuous.congr
    (fun c =>
      globalNormResidueContinuousMonoidHom_apply K L c)

end Reciprocity
end GlobalClassFieldTheory
