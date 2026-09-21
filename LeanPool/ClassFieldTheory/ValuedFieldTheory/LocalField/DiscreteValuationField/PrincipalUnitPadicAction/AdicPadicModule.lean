/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.Algebra.Module.MinimalAxioms
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.ProdiscretePadicModule
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.AdicProdiscreteComparison
/-!
# The p-adic module on adic principal units

The coordinatewise p-adic action is transported across the canonical adic/prodiscrete
comparison, producing its linear and topological forms on first principal units.
-/

noncomputable section

open scoped BigOperators

universe u v

namespace LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField
namespace CompleteDVF
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
namespace higherPrincipalUnitGroup

open LubinTate
open LubinTate.Valuations

variable {K : Type u} [Field K]

open Internal

/-- Transport the coordinatewise p-adic scalar multiplication from the
inverse limit to `U^1`. -/
noncomputable instance principalUnitPadicSMul
    (F : LocalField.{u, v} K) :
    SMul ℤ_[F.residueCharacteristic]
      (Additive ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF) 1)) where
  smul a x :=
    (principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF).symm
      (a • principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF x)

/--
Establishes the identity `a • x = (principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF).symm
(a • principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF x)`.
-/
@[simp] theorem principalUnitPadic_smul_def
    (F : LocalField.{u, v} K)
    (a : ℤ_[F.residueCharacteristic])
    (x : Additive ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF) 1)) :
    a • x =
      (principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF).symm
        (a • principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF x) :=
  rfl

/-- The standard `Z_p`-module structure on the first principal units of a
local field. -/
noncomputable instance principalUnitPadicModule
    (F : LocalField.{u, v} K) :
    Module ℤ_[F.residueCharacteristic]
      (Additive ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF) 1)) :=
  Module.ofMinimalAxioms
    (fun (a : ℤ_[F.residueCharacteristic])
        (x y : Additive
          ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF) 1)) => by
      apply (principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF).injective
      simp only [principalUnitPadic_smul_def, AddEquiv.apply_symm_apply,
        (principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF).map_add]
      exact (principalUnitInverseLimitCarrierPadicModule F).smul_add a
        (principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF x)
        (principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF y))
    (fun (a b : ℤ_[F.residueCharacteristic])
        (x : Additive
          ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF) 1)) => by
      apply (principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF).injective
      simp only [principalUnitPadic_smul_def, AddEquiv.apply_symm_apply,
        (principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF).map_add]
      exact (principalUnitInverseLimitCarrierPadicModule F).add_smul a b
        (principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF x))
    (fun (a b : ℤ_[F.residueCharacteristic])
        (x : Additive
          ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF) 1)) => by
      apply (principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF).injective
      simp only [principalUnitPadic_smul_def, AddEquiv.apply_symm_apply]
      exact (principalUnitInverseLimitCarrierPadicModule F).mul_smul a b
        (principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF x))
    (fun (x : Additive
        ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF) 1)) => by
      apply (principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF).injective
      simp only [principalUnitPadic_smul_def, AddEquiv.apply_symm_apply]
      exact (principalUnitInverseLimitCarrierPadicModule F).one_smul
        (principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF x))

/--
Equips the target in `Module ℤ_[F.residueCharacteristic] (AdicPrincipalUnits F.toCompleteDVF)`
with the indicated module structure.
-/
noncomputable instance adicPrincipalUnitsPadicModule
    (F : LocalField.{u, v} K) :
    Module ℤ_[F.residueCharacteristic]
      (AdicPrincipalUnits F.toCompleteDVF) :=
  AddEquiv.module
    (β := Additive
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        F.toCompleteDVF) 1))
    ℤ_[F.residueCharacteristic]
    (AdicPrincipalUnits.addEquiv F.toCompleteDVF)

/--
Establishes the identity `AdicPrincipalUnits.addEquiv F.toCompleteDVF (a • x) = a •
AdicPrincipalUnits.addEquiv F.toCompleteDVF x`.
-/
@[simp]
theorem AdicPrincipalUnits.addEquiv_map_smul
    (F : LocalField.{u, v} K) (a : ℤ_[F.residueCharacteristic])
    (x : AdicPrincipalUnits F.toCompleteDVF) :
    AdicPrincipalUnits.addEquiv F.toCompleteDVF (a • x) =
      a • AdicPrincipalUnits.addEquiv F.toCompleteDVF x :=
  rfl

/-- The adic wrapper and its underlying principal-unit module are canonically
`Z_p`-linearly equivalent. -/
noncomputable def AdicPrincipalUnits.linearEquivUnderlying
    (F : LocalField.{u, v} K) :
    AdicPrincipalUnits F.toCompleteDVF ≃ₗ[ℤ_[F.residueCharacteristic]]
      Additive
        ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
          F.toCompleteDVF) 1) :=
  { AdicPrincipalUnits.addEquiv F.toCompleteDVF with
    map_smul' := AdicPrincipalUnits.addEquiv_map_smul F }

/--
Establishes the identity `principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF (a • x) = a •
principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF x`.
-/
@[simp] theorem Internal.principalUnitAddEquivInverseLimitCarrier_map_smul
    (F : LocalField.{u, v} K)
    (a : ℤ_[F.residueCharacteristic])
    (x : Additive ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF) 1)) :
    principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF (a • x) =
      a • principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF x := by
  change
    principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF
        ((principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF).symm
          (a • principalUnitAddEquivInverseLimitCarrier
            F.toCompleteDVF x)) =
      a • principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF x
  exact (principalUnitAddEquivInverseLimitCarrier
    F.toCompleteDVF).apply_symm_apply _

/-- Coordinate formula for the canonical action: the class of `a • x` at
level `n` is obtained by reducing `a` modulo `p^(f*n)` and acting on the class
of `x`. -/
@[simp] theorem Internal.principalUnitPadic_smul_carrier_coordinate
    (F : LocalField.{u, v} K)
    (a : ℤ_[F.residueCharacteristic])
    (x : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF) 1) (n : ℕ) :
    Additive.ofMul
        ((principalUnitMulEquivInverseLimitCarrier F.toCompleteDVF
          (Additive.toMul (a • Additive.ofMul x))).1 n) =
      principalUnitQuotientCarrierPadicScalar F n a
        (Additive.ofMul
          ((principalUnitMulEquivInverseLimitCarrier F.toCompleteDVF x).1 n)) := by
  rw [principalUnitQuotientCarrierPadicScalar_eq_smul]
  have h := congrArg
    (fun z : Additive
        (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF) =>
      Additive.ofMul ((Additive.toMul z).1 n))
      (principalUnitAddEquivInverseLimitCarrier_map_smul
      F a (Additive.ofMul x))
  exact h

/-- The canonical identification of adic principal units with the
prodiscrete limit respects the p-adic action. -/
theorem adicPrincipalUnitsHomeomorphProdiscreteLimit_map_smul
    (F : LocalField.{u, v} K)
    (a : ℤ_[F.residueCharacteristic])
    (x : AdicPrincipalUnits F.toCompleteDVF) :
    adicPrincipalUnitsHomeomorphProdiscreteLimit F.toCompleteDVF (a • x) =
      a • adicPrincipalUnitsHomeomorphProdiscreteLimit F.toCompleteDVF x := by
  apply (PrincipalUnitProdiscreteLimit.addEquiv F.toCompleteDVF).injective
  rw [adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv,
    PrincipalUnitProdiscreteLimit.addEquiv_map_smul,
    adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv,
    AdicPrincipalUnits.addEquiv_map_smul,
    Internal.principalUnitAddEquivInverseLimitCarrier_map_smul]

/--
Establishes the identity `adicPrincipalUnitsAddEquivProdiscreteLimit F.toCompleteDVF (a • x) = a •
adicPrincipalUnitsAddEquivProdiscreteLimit F.toCompleteDVF x`.
-/
@[simp]
theorem adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul
    (F : LocalField.{u, v} K)
    (a : ℤ_[F.residueCharacteristic])
    (x : AdicPrincipalUnits F.toCompleteDVF) :
    adicPrincipalUnitsAddEquivProdiscreteLimit F.toCompleteDVF (a • x) =
      a • adicPrincipalUnitsAddEquivProdiscreteLimit F.toCompleteDVF x := by
  apply (PrincipalUnitProdiscreteLimit.addEquiv F.toCompleteDVF).injective
  change
    PrincipalUnitProdiscreteLimit.addEquiv F.toCompleteDVF
        ((PrincipalUnitProdiscreteLimit.addEquiv F.toCompleteDVF).symm
          (principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF
            (AdicPrincipalUnits.addEquiv F.toCompleteDVF (a • x)))) =
      PrincipalUnitProdiscreteLimit.addEquiv F.toCompleteDVF
        (a •
          (PrincipalUnitProdiscreteLimit.addEquiv F.toCompleteDVF).symm
            (principalUnitAddEquivInverseLimitCarrier F.toCompleteDVF
              (AdicPrincipalUnits.addEquiv F.toCompleteDVF x)))
  rw [(PrincipalUnitProdiscreteLimit.addEquiv F.toCompleteDVF).apply_symm_apply,
    PrincipalUnitProdiscreteLimit.addEquiv_map_smul,
    (PrincipalUnitProdiscreteLimit.addEquiv F.toCompleteDVF).apply_symm_apply,
    AdicPrincipalUnits.addEquiv_map_smul,
    Internal.principalUnitAddEquivInverseLimitCarrier_map_smul]

/-- `Z_p`-linear form of the canonical adic/prodiscrete comparison. -/
noncomputable def adicPrincipalUnitsLinearEquivProdiscreteLimit
    (F : LocalField.{u, v} K) :
    AdicPrincipalUnits F.toCompleteDVF ≃ₗ[ℤ_[F.residueCharacteristic]]
      PrincipalUnitProdiscreteLimit F.toCompleteDVF :=
  { adicPrincipalUnitsAddEquivProdiscreteLimit F.toCompleteDVF with
    map_smul' := adicPrincipalUnitsAddEquivProdiscreteLimit_map_smul F }

/-- Projection from adic first principal units to one wrapped quotient
coordinate. -/
noncomputable def adicPrincipalUnitsCoordinateLinear
    (F : LocalField.{u, v} K) (n : ℕ) :
    AdicPrincipalUnits F.toCompleteDVF →ₗ[ℤ_[F.residueCharacteristic]]
      DiscretePrincipalUnitQuotient F.toCompleteDVF n :=
  (PrincipalUnitProdiscreteLimit.coordinateLinear F n).comp
    (adicPrincipalUnitsLinearEquivProdiscreteLimit F).toLinearMap

/--
The specified map is continuous: `Continuous fun z : ℤ_[F.residueCharacteristic] ×
AdicPrincipalUnits F.toCompleteDVF => z.1 • z.2`.
-/
theorem continuous_adicPrincipalUnitsPadic_smul
    (F : LocalField.{u, v} K) :
    Continuous fun z : ℤ_[F.residueCharacteristic] ×
        AdicPrincipalUnits F.toCompleteDVF =>
      z.1 • z.2 := by
  let e := adicPrincipalUnitsHomeomorphProdiscreteLimit F.toCompleteDVF
  have hpair : Continuous fun z : ℤ_[F.residueCharacteristic] ×
      AdicPrincipalUnits F.toCompleteDVF =>
      (z.1, e z.2) :=
    continuous_fst.prodMk (e.continuous.comp continuous_snd)
  have htransport := e.continuous_symm.comp (continuous_smul.comp hpair)
  exact htransport

/--
The scalar action in `ContinuousSMul ℤ_[F.residueCharacteristic] (AdicPrincipalUnits
F.toCompleteDVF)` is continuous.
-/
noncomputable instance adicPrincipalUnitsContinuousSMul
    (F : LocalField.{u, v} K) :
    ContinuousSMul ℤ_[F.residueCharacteristic]
      (AdicPrincipalUnits F.toCompleteDVF) :=
  ⟨continuous_adicPrincipalUnitsPadic_smul F⟩

/-- Addition on the adic principal-unit model is continuous. -/
noncomputable instance adicPrincipalUnitsContinuousAdd
    (F : LocalField.{u, v} K) :
    ContinuousAdd (AdicPrincipalUnits F.toCompleteDVF) := by
  let e := adicPrincipalUnitsContinuousAddEquivProdiscreteLimit F.toCompleteDVF
  refine ⟨?_⟩
  have hpair : Continuous fun z :
      AdicPrincipalUnits F.toCompleteDVF ×
        AdicPrincipalUnits F.toCompleteDVF =>
      (e z.1, e z.2) :=
    (e.continuous.comp continuous_fst).prodMk
      (e.continuous.comp continuous_snd)
  have h := e.continuous_symm.comp
    (continuous_add.comp hpair)
  convert h using 1
  funext z
  change z.1 + z.2 = e.symm (e z.1 + e z.2)
  apply e.injective
  rw [e.apply_symm_apply]
  exact e.map_add z.1 z.2

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField
