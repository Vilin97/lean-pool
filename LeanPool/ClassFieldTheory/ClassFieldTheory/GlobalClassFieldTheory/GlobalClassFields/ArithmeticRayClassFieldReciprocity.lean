/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.RayClassFieldRealization
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ArithmeticNormalization
/-!
# Arithmetic reciprocity for actual ray class fields

This is the canonical topological isomorphism
`Gal(Kᵐ/K) ≃ₜ* C_K/C_Kᵐ` with arithmetic Frobenius
normalization.  It uses the actual selected ray class field, its exact
idèle norm range, the finite Krull topology, and the native ray-class
quotient topology.
-/

open scoped Classical NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open NumberField
open Reciprocity

private theorem arithmeticRayClassIdeleClassGroupIsMulCommutative
    {F : Type} [Field F] [NumberField F] :
    IsMulCommutative (IdeleClassGroup F) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

attribute [local instance] arithmeticRayClassIdeleClassGroupIsMulCommutative

variable {K : Type} [Field K] [NumberField K]

/-- Arithmetic reciprocity followed by transport between equal norm
quotients sends a norm-residue symbol to its represented quotient class. -/
private theorem
    arithmeticReciprocity_quotientMulEquivOfEq_globalNormResidue
    {F E : Type} [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E]
    [FiniteDimensional F E] [IsAbelianGalois F E]
    (H : Subgroup (IdeleClassGroup F))
    (h : (_root_.ideleClassNorm F E).range = H)
    (c : IdeleClassGroup F) :
    QuotientGroup.quotientMulEquivOfEq h
        (arithmeticGlobalReciprocityContinuousMulEquiv F E
          (arithmeticGlobalNormResidueMonoidHom F E c)) =
      QuotientGroup.mk' H c := by
  let e := arithmeticGlobalReciprocityContinuousMulEquiv F E
  let q :=
    QuotientGroup.mk'
      (_root_.ideleClassNorm F E).range c
  have hsymm :
      e.symm q = arithmeticGlobalNormResidueMonoidHom F E c :=
    arithmeticGlobalReciprocityContinuousMulEquiv_symm_mk F E c
  have he :
      e (arithmeticGlobalNormResidueMonoidHom F E c) = q := by
    calc
      e (arithmeticGlobalNormResidueMonoidHom F E c) =
          e (e.symm q) :=
        congrArg (fun σ => e σ) hsymm.symm
      _ = q := e.apply_symm_apply q
  calc
    QuotientGroup.quotientMulEquivOfEq h
        (arithmeticGlobalReciprocityContinuousMulEquiv F E
          (arithmeticGlobalNormResidueMonoidHom F E c)) =
        QuotientGroup.quotientMulEquivOfEq h q :=
      congrArg (fun x => QuotientGroup.quotientMulEquivOfEq h x) he
    _ = QuotientGroup.mk' H c :=
      QuotientGroup.quotientMulEquivOfEq_mk h c

/-- Arithmetic global reciprocity for the actual selected ray class
field, bundled with both native topologies. -/
noncomputable def
    arithmeticRayClassFieldGaloisContinuousMulEquivRayClassGroup
    (m : RayClass.Modulus K) :
    Gal((rayClassField K m) / K) ≃ₜ*
      RayClass.RayClassGroup m := by
  letI normQuotientDiscreteTopology : DiscreteTopology
      (IdeleClassGroup K ⧸
        (_root_.ideleClassNorm
          K (rayClassField K m)).range) :=
    ideleClassNormQuotient_discreteTopology
      K (rayClassField K m)
  letI rayClassGroupDiscreteTopology : DiscreteTopology
      (RayClass.RayClassGroup m) :=
    QuotientGroup.discreteTopology
      (RayClass.isOpen_congruenceSubgroup m)
  let quotientTransport :
      (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm
            K (rayClassField K m)).range) ≃ₜ*
        RayClass.RayClassGroup m :=
    { QuotientGroup.quotientMulEquivOfEq
        (rayClassField_ideleClassNorm_range_over_original
          (K := K) m) with
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  exact
    (arithmeticGlobalReciprocityContinuousMulEquiv
      K (rayClassField K m)).trans
        quotientTransport

/-- Pointwise evaluation of arithmetic ray-class reciprocity separates
global reciprocity from the transport between the equal norm quotients. -/
private theorem
    arithmeticRayClassFieldGaloisContinuousMulEquivRayClassGroup_apply
    (m : RayClass.Modulus K)
    (σ : Gal((rayClassField K m)/K)) :
    arithmeticRayClassFieldGaloisContinuousMulEquivRayClassGroup
        (K := K) m σ =
      QuotientGroup.quotientMulEquivOfEq
        (rayClassField_ideleClassNorm_range_over_original
          (K := K) m)
        (arithmeticGlobalReciprocityContinuousMulEquiv
          K (rayClassField K m) σ) := by
  rfl

/-- Arithmetic ray-class reciprocity sends the arithmetic global
norm-residue symbol of an idèle class to its literal ray class. -/
@[simp]
theorem
    arithmeticRayClassFieldGaloisContinuousMulEquivRayClassGroup_globalNormResidue
    (m : RayClass.Modulus K)
    (c : IdeleClassGroup K) :
    arithmeticRayClassFieldGaloisContinuousMulEquivRayClassGroup
        (K := K) m
        (arithmeticGlobalNormResidueMonoidHom
          K (rayClassField K m) c) =
      QuotientGroup.mk'
        (RayClass.Modulus.congruenceSubgroup m) c := by
  calc
    arithmeticRayClassFieldGaloisContinuousMulEquivRayClassGroup
        (K := K) m
        (arithmeticGlobalNormResidueMonoidHom
          K (rayClassField K m) c) =
      QuotientGroup.quotientMulEquivOfEq
          (rayClassField_ideleClassNorm_range_over_original
            (K := K) m)
          (arithmeticGlobalReciprocityContinuousMulEquiv
            K (rayClassField K m)
            (arithmeticGlobalNormResidueMonoidHom
              K (rayClassField K m) c)) :=
      arithmeticRayClassFieldGaloisContinuousMulEquivRayClassGroup_apply
        (K := K) m _
    _ = QuotientGroup.mk'
          (RayClass.Modulus.congruenceSubgroup m) c :=
      arithmeticReciprocity_quotientMulEquivOfEq_globalNormResidue
        (RayClass.Modulus.congruenceSubgroup m)
        (rayClassField_ideleClassNorm_range_over_original
          (K := K) m) c

/-- Inverse arithmetic ray reciprocity sends a represented ray class
back to the arithmetic global norm-residue symbol. -/
@[simp]
theorem
    arithmeticRayClassFieldGaloisContinuousMulEquivRayClassGroup_symm_mk
    (m : RayClass.Modulus K)
    (c : IdeleClassGroup K) :
    (arithmeticRayClassFieldGaloisContinuousMulEquivRayClassGroup
      (K := K) m).symm
        (QuotientGroup.mk'
          (RayClass.Modulus.congruenceSubgroup m) c) =
      arithmeticGlobalNormResidueMonoidHom
        K (rayClassField K m) c := by
  let e :=
    arithmeticRayClassFieldGaloisContinuousMulEquivRayClassGroup
      (K := K) m
  apply e.injective
  calc
    e (e.symm
        (QuotientGroup.mk'
          (RayClass.Modulus.congruenceSubgroup m) c)) =
        QuotientGroup.mk'
          (RayClass.Modulus.congruenceSubgroup m) c :=
      e.apply_symm_apply _
    _ = e
          (arithmeticGlobalNormResidueMonoidHom
            K (rayClassField K m) c) :=
      (arithmeticRayClassFieldGaloisContinuousMulEquivRayClassGroup_globalNormResidue
        (K := K) m c).symm

end GlobalClassFields
end GlobalClassFieldTheory
