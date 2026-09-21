/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.InverseLimitTopology
/-!
# Adic and prodiscrete principal-unit models

The adic topology on first principal units agrees with the prodiscrete topology carried
by the inverse limit of finite quotient coordinates.
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

namespace Internal

/-- Internal comparison from the type-level adic model to the raw
instance-parametric carrier. -/
noncomputable def adicPrincipalUnitsHomeomorphUnderlying
    (F : CompleteDVF.{u, v} K) :
    letI : TopologicalSpace F.valuationSubring :=
      (uniformizerPowerIdeal
        (chosenPrincipalUnitPadicUniformizer F) 1).adicTopology
    AdicPrincipalUnits F ≃ₜ
      Additive
        ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) := by
  letI : TopologicalSpace F.valuationSubring :=
    (uniformizerPowerIdeal
      (chosenPrincipalUnitPadicUniformizer F) 1).adicTopology
  exact (AdicPrincipalUnits.homeomorph F).trans
    (WithTopology.homeomorph
      (α := Additive
        ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1))
      (topology := principalUnitAdicTopology F))

/--
The homeomorphism from the adic principal-unit model evaluates through its underlying additive
equivalence.
-/
@[simp]
theorem adicPrincipalUnitsHomeomorphUnderlying_apply
    (F : CompleteDVF.{u, v} K) (x : AdicPrincipalUnits F) :
    letI : TopologicalSpace F.valuationSubring :=
      (uniformizerPowerIdeal
        (chosenPrincipalUnitPadicUniformizer F) 1).adicTopology
    adicPrincipalUnitsHomeomorphUnderlying F x =
      AdicPrincipalUnits.addEquiv F x :=
  rfl

/-- Internal comparison from the type-level prodiscrete model to the raw
instance-parametric inverse-limit carrier. -/
noncomputable def principalUnitProdiscreteLimitHomeomorphUnderlying
    (F : CompleteDVF.{u, v} K) :
    letI : (n : ℕ) → TopologicalSpace (Internal.principalUnitQuotientCarrier F n) :=
      fun _ => ⊥
    PrincipalUnitProdiscreteLimit F ≃ₜ
      Additive (Internal.principalUnitInverseLimitCarrier F) := by
  letI : (n : ℕ) → TopologicalSpace (Internal.principalUnitQuotientCarrier F n) :=
    fun _ => ⊥
  exact (PrincipalUnitProdiscreteLimit.homeomorph F).trans
    (WithTopology.homeomorph
      (α := Additive (Internal.principalUnitInverseLimitCarrier F))
      (topology := principalUnitProdiscreteTopology F))

/--
The homeomorphism from the prodiscrete limit evaluates through its underlying additive
equivalence.
-/
@[simp]
theorem principalUnitProdiscreteLimitHomeomorphUnderlying_apply
    (F : CompleteDVF.{u, v} K) (x : PrincipalUnitProdiscreteLimit F) :
    letI : (n : ℕ) → TopologicalSpace
        (Internal.principalUnitQuotientCarrier F n) := fun _ => ⊥
    principalUnitProdiscreteLimitHomeomorphUnderlying F x =
      PrincipalUnitProdiscreteLimit.addEquiv F x :=
  rfl

end Internal

/-- The only bridge where the raw instance-parametric presentations are
installed.  Public topology APIs use `AdicPrincipalUnits` and
`PrincipalUnitProdiscreteLimit` instead. -/
noncomputable def adicPrincipalUnitsHomeomorphProdiscreteLimit
    (F : CompleteDVF.{u, v} K) :
    AdicPrincipalUnits F ≃ₜ PrincipalUnitProdiscreteLimit F := by
  letI : TopologicalSpace F.valuationSubring :=
    (uniformizerPowerIdeal
      (chosenPrincipalUnitPadicUniformizer F) 1).adicTopology
  letI : (n : ℕ) → TopologicalSpace (Internal.principalUnitQuotientCarrier F n) :=
    fun _ => ⊥
  let source := Internal.adicPrincipalUnitsHomeomorphUnderlying F
  let target := Internal.principalUnitProdiscreteLimitHomeomorphUnderlying F
  exact source.trans
    ((Internal.principalUnitAddHomeomorphInverseLimitCarrier F).trans target.symm)

/--
Establishes the identity `PrincipalUnitProdiscreteLimit.addEquiv F
(adicPrincipalUnitsHomeomorphProdiscreteLimit F x) = principalUnitAddEquivInverseLimitCarrier F
(AdicPrincipalUnits.addEquiv F x)`.
-/
@[simp]
theorem adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv
    (F : CompleteDVF.{u, v} K) (x : AdicPrincipalUnits F) :
    PrincipalUnitProdiscreteLimit.addEquiv F
        (adicPrincipalUnitsHomeomorphProdiscreteLimit F x) =
      principalUnitAddEquivInverseLimitCarrier F
        (AdicPrincipalUnits.addEquiv F x) := by
  let : TopologicalSpace F.valuationSubring :=
    (uniformizerPowerIdeal
      (chosenPrincipalUnitPadicUniformizer F) 1).adicTopology
  let : (n : ℕ) → TopologicalSpace
      (Internal.principalUnitQuotientCarrier F n) := fun _ => ⊥
  let source := Internal.adicPrincipalUnitsHomeomorphUnderlying F
  let target := Internal.principalUnitProdiscreteLimitHomeomorphUnderlying F
  calc
    PrincipalUnitProdiscreteLimit.addEquiv F
        (adicPrincipalUnitsHomeomorphProdiscreteLimit F x) =
      target (adicPrincipalUnitsHomeomorphProdiscreteLimit F x) := by
        rw [Internal.principalUnitProdiscreteLimitHomeomorphUnderlying_apply]
    _ = principalUnitAddHomeomorphInverseLimitCarrier F (source x) := by
      exact target.apply_symm_apply _
    _ = principalUnitAddEquivInverseLimitCarrier F
        (AdicPrincipalUnits.addEquiv F x) := by
      rw [principalUnitAddHomeomorphInverseLimitCarrier_apply,
        Internal.adicPrincipalUnitsHomeomorphUnderlying_apply]

/-- The prodiscrete principal-unit limit is Hausdorff. -/
noncomputable instance principalUnitProdiscreteLimitT2Space
    (F : CompleteDVF.{u, v} K) :
    T2Space (PrincipalUnitProdiscreteLimit F) := by
  let : (n : ℕ) → TopologicalSpace (Internal.principalUnitQuotientCarrier F n) :=
    fun _ => ⊥
  let : (n : ℕ) → DiscreteTopology (Internal.principalUnitQuotientCarrier F n) :=
    fun _ => ⟨rfl⟩
  let : (n : ℕ) → T2Space (Internal.principalUnitQuotientCarrier F n) :=
    fun _ => DiscreteTopology.toT2Space
  let : T2Space (Internal.principalUnitInverseLimitCarrier F) := by
    infer_instance
  let : T2Space (Additive (Internal.principalUnitInverseLimitCarrier F)) := by
    change T2Space (Internal.principalUnitInverseLimitCarrier F)
    infer_instance
  exact T2Space.of_injective_continuous
    (Internal.principalUnitProdiscreteLimitHomeomorphUnderlying F).injective
    (Internal.principalUnitProdiscreteLimitHomeomorphUnderlying F).continuous

/-- Algebraic form of the canonical identification between adic principal
units and their prodiscrete limit. -/
noncomputable def adicPrincipalUnitsAddEquivProdiscreteLimit
    (F : CompleteDVF.{u, v} K) :
    AdicPrincipalUnits F ≃+ PrincipalUnitProdiscreteLimit F :=
  (AdicPrincipalUnits.addEquiv F).trans
    ((principalUnitAddEquivInverseLimitCarrier F).trans
      (PrincipalUnitProdiscreteLimit.addEquiv F).symm)

/--
The defining evaluation formula for `adicPrincipalUnitsHomeomorphProdiscreteLimit` is
`adicPrincipalUnitsHomeomorphProdiscreteLimit F x = adicPrincipalUnitsAddEquivProdiscreteLimit F
x`.
-/
@[simp] theorem adicPrincipalUnitsHomeomorphProdiscreteLimit_apply
    (F : CompleteDVF.{u, v} K) (x : AdicPrincipalUnits F) :
    adicPrincipalUnitsHomeomorphProdiscreteLimit F x =
      adicPrincipalUnitsAddEquivProdiscreteLimit F x :=
  (PrincipalUnitProdiscreteLimit.addEquiv F).injective (by
    rw [adicPrincipalUnitsHomeomorphProdiscreteLimit_to_addEquiv]
    change
      principalUnitAddEquivInverseLimitCarrier F
          (AdicPrincipalUnits.addEquiv F x) =
        PrincipalUnitProdiscreteLimit.addEquiv F
          ((PrincipalUnitProdiscreteLimit.addEquiv F).symm
            (principalUnitAddEquivInverseLimitCarrier F
              (AdicPrincipalUnits.addEquiv F x)))
    exact ((PrincipalUnitProdiscreteLimit.addEquiv F).apply_symm_apply _).symm)

/-- Additive topological form of
`adicPrincipalUnitsHomeomorphProdiscreteLimit`. -/
noncomputable def adicPrincipalUnitsContinuousAddEquivProdiscreteLimit
    (F : CompleteDVF.{u, v} K) :
    AdicPrincipalUnits F ≃ₜ+ PrincipalUnitProdiscreteLimit F :=
  ContinuousAddEquiv.mk'
    (adicPrincipalUnitsHomeomorphProdiscreteLimit F)
    (fun x y => by
      simpa only [adicPrincipalUnitsHomeomorphProdiscreteLimit_apply] using
        (adicPrincipalUnitsAddEquivProdiscreteLimit F).map_add x y)

/-- The topology on the type in `T2Space (AdicPrincipalUnits F)` is Hausdorff. -/
noncomputable instance adicPrincipalUnitsT2Space
    (F : CompleteDVF.{u, v} K) : T2Space (AdicPrincipalUnits F) :=
  (adicPrincipalUnitsHomeomorphProdiscreteLimit F).symm.t2Space

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField
