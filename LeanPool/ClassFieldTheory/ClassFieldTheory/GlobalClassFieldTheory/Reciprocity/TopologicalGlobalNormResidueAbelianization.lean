/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.NormConductor
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidueAbelianization
import Mathlib.FieldTheory.KrullTopology
import Mathlib.Topology.Algebra.Group.Quotient
/-!
# Topological global reciprocity for finite Galois extensions

For a finite Galois extension `L / K`, global norm-residue reciprocity
identifies the native idele-class norm quotient with the abelianization
of the finite Krull Galois group.  This file records the identification
as a `ContinuousMulEquiv` in both mathematical directions:

* norm-residue: `C_K / N_{L/K}(C_L) ≃ₜ* Gal(L / K)ᵃᵇ`;
* reciprocity: `Gal(L / K)ᵃᵇ ≃ₜ* C_K / N_{L/K}(C_L)`.

The evaluation lemmas below ensure that these are the already
constructed actual global symbols, rather than unrelated abstract
isomorphisms between finite groups.
-/

open scoped IsMulCommutative NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- Keep quotient normality out of every exported declaration type. -/
local instance
    topologicalGlobalNormResidueAbelianization_ideleClassGroupIsMulCommutative :
    IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

/-- `Abelianization` is an opaque quotient alias, so install its native
quotient topology explicitly before asking for topological properties. -/
local instance
    topologicalGlobalNormResidueAbelianizationGaloisAbelianizationTopology :
    TopologicalSpace (Abelianization (Gal(L/K))) := by
  change
    TopologicalSpace
      (Gal(L/K) ⧸ commutator (Gal(L/K)))
  infer_instance

/-- The native topology on the actual idele-class norm quotient is
discrete.  The openness used here is the genuine ordinary norm-range
theorem for the given finite Galois extension. -/
theorem ideleClassNormAbelianizationQuotient_discreteTopology :
    DiscreteTopology
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) := by
  apply QuotientGroup.discreteTopology
  exact
    GlobalClassFields.ideleClassNorm_range_isOpen
      (K := K) (L := L)

omit [NumberField K] [NumberField L] [IsGalois K L] in
/-- The abelianization of a finite Krull Galois group carries the
discrete quotient topology. -/
theorem finiteGaloisAbelianization_discreteTopology :
    DiscreteTopology
      (Abelianization (Gal(L/K))) := by
  change
    DiscreteTopology
      (Gal(L/K) ⧸
        commutator (Gal(L/K)))
  apply QuotientGroup.discreteTopology
  exact isOpen_discrete _

local instance
    topologicalGlobalNormResidueAbelianization_normQuotientDiscreteTopology :
    DiscreteTopology
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :=
  ideleClassNormAbelianizationQuotient_discreteTopology K L

local instance
    topologicalGlobalNormResidueAbelianization_galoisAbelianizationDiscreteTopology :
    DiscreteTopology (Abelianization (Gal(L/K))) :=
  finiteGaloisAbelianization_discreteTopology K L

/-- The full finite-Galois norm-residue isomorphism with its native
topologies:

`C_K / N_{L/K}(C_L) ≃ₜ* Gal(L / K)ᵃᵇ`. -/
noncomputable def globalNormResidueAbelianizationContinuousMulEquiv :
    (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) ≃ₜ*
      Abelianization (Gal(L/K)) := by
  let e :
      (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) ≃*
        Abelianization (Gal(L/K)) :=
    AddEquiv.toMultiplicative
      (globalNormResidueAbelianizationEquiv K L)
  exact
    { e with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

/-- Evaluation of the topological finite-Galois norm-residue
equivalence is the previously constructed actual norm-residue
equivalence. -/
@[simp]
theorem globalNormResidueAbelianizationContinuousMulEquiv_apply
    (c :
      IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :
    globalNormResidueAbelianizationContinuousMulEquiv K L c =
      Additive.toMul
        (globalNormResidueAbelianizationEquiv K L
          (Additive.ofMul c)) := by
  rfl

/-- Global reciprocity for a finite Galois extension in the direction
used by the class-field correspondence:

`Gal(L / K)ᵃᵇ ≃ₜ* C_K / N_{L/K}(C_L)`. -/
noncomputable def globalReciprocityAbelianizationContinuousMulEquiv :
    Abelianization (Gal(L/K)) ≃ₜ*
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :=
  (globalNormResidueAbelianizationContinuousMulEquiv K L).symm

/-- Evaluation in the reciprocity direction is exactly the inverse
actual finite-Galois norm-residue map. -/
@[simp]
theorem globalReciprocityAbelianizationContinuousMulEquiv_apply
    (σ : Abelianization (Gal(L/K))) :
    globalReciprocityAbelianizationContinuousMulEquiv K L σ =
      Additive.toMul
        ((globalNormResidueAbelianizationEquiv K L).symm
          (Additive.ofMul σ)) := by
  rfl

/-- The native quotient projection
`C_K → C_K / N_{L/K}(C_L)` as a continuous homomorphism. -/
noncomputable def
    ideleClassNormAbelianizationQuotientContinuousMonoidHom :
    IdeleClassGroup K →ₜ*
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range) :=
  { QuotientGroup.mk'
      (_root_.ideleClassNorm K L).range with
    continuous_toFun := QuotientGroup.continuous_mk }

/-- The global norm-residue symbol
`C_K → Gal(L / K)ᵃᵇ` as a continuous homomorphism in the natural
idele-class and finite Krull quotient topologies. -/
noncomputable def
    globalNormResidueAbelianizationContinuousMonoidHom :
    IdeleClassGroup K →ₜ*
      Abelianization (Gal(L/K)) :=
  (ContinuousMonoidHom.toContinuousMonoidHom
      (globalNormResidueAbelianizationContinuousMulEquiv K L)).comp
    (ideleClassNormAbelianizationQuotientContinuousMonoidHom K L)

/-- Forgetting continuity from the topological finite-Galois
norm-residue map recovers the previously constructed actual symbol. -/
@[simp]
theorem globalNormResidueAbelianizationContinuousMonoidHom_apply
    (c : IdeleClassGroup K) :
    globalNormResidueAbelianizationContinuousMonoidHom K L c =
      globalNormResidueAbelianizationMonoidHom K L c := by
  rfl

/-- The actual finite-Galois norm-residue symbol is continuous. -/
theorem globalNormResidueAbelianizationMonoidHom_continuous :
    Continuous
      (globalNormResidueAbelianizationMonoidHom K L) :=
  (globalNormResidueAbelianizationContinuousMonoidHom K L).continuous.congr
    (fun c =>
      globalNormResidueAbelianizationContinuousMonoidHom_apply
        K L c)

end Reciprocity
end GlobalClassFieldTheory
