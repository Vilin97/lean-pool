/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.InverseLimitCore
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Topology.Models
/-!
# Type-level topology models for principal units

Adic principal units, discrete finite quotients, and the prodiscrete inverse limit are
represented by distinct wrapper types so that their topologies cannot be confused by instance
selection.
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

/-! ## Topology is part of the type

The algebraic quotient and inverse-limit types above deliberately carry no
preferred topology.  The following models distinguish the topologies used in
the p-adic action at the type level.  In particular, no theorem below can
silently reinterpret the same quotient as both a quotient-topological and a
discrete space.
-/

/-- The topology on additive first principal units induced by the maximal-
ideal adic topology on the valuation ring. -/
@[implicit_reducible]
noncomputable def principalUnitAdicTopology
    (F : CompleteDVF.{u, v} K) :
    TopologicalSpace
      (Additive
        ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)) := by
  letI : TopologicalSpace F.valuationSubring :=
    (uniformizerPowerIdeal (chosenPrincipalUnitPadicUniformizer F) 1).adicTopology
  exact inferInstance

/-- First principal units with their canonical adic topology fixed in the
type. -/
structure AdicPrincipalUnits (F : CompleteDVF.{u, v} K) where
  /-- The underlying additive principal unit. -/
  val : Additive
    ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)

namespace AdicPrincipalUnits

/-- The carrier equivalence of the adic model. -/
def equiv (F : CompleteDVF.{u, v} K) :
    AdicPrincipalUnits F ≃
      Additive
        ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) where
  toFun := AdicPrincipalUnits.val
  invFun := fun x => ⟨x⟩
  left_inv := fun x => by cases x; rfl
  right_inv := fun _ => rfl

/--
Equips the target with its canonical `TopologicalSpace` structure, namely `TopologicalSpace
(AdicPrincipalUnits F)`.
-/
noncomputable instance (F : CompleteDVF.{u, v} K) :
    TopologicalSpace (AdicPrincipalUnits F) :=
  (principalUnitAdicTopology F).induced AdicPrincipalUnits.val

/-- Forget the wrapper while retaining the topology recorded in its type. -/
noncomputable def homeomorph (F : CompleteDVF.{u, v} K) :
    AdicPrincipalUnits F ≃ₜ
      WithTopology
        (Additive
          ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1))
        (principalUnitAdicTopology F) where
  toEquiv := (equiv F).trans
    (WithTopology.equiv _ (principalUnitAdicTopology F)).symm
  continuous_toFun := by
    let : TopologicalSpace
        (Additive
          ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)) :=
      principalUnitAdicTopology F
    change Continuous fun x : AdicPrincipalUnits F =>
      WithTopology.toTopology (principalUnitAdicTopology F) x.val
    exact
      (WithTopology.continuous_toTopology (principalUnitAdicTopology F)).comp
        continuous_induced_dom
  continuous_invFun := by
    let : TopologicalSpace
        (Additive
          ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)) :=
      principalUnitAdicTopology F
    change Continuous fun x : WithTopology
        (Additive
          ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1))
        (principalUnitAdicTopology F) =>
      (⟨x.ofTopology⟩ : AdicPrincipalUnits F)
    exact
      continuous_induced_rng.2
        (WithTopology.continuous_ofTopology (principalUnitAdicTopology F))

/--
Equips the target with its canonical `AddCommGroup` structure, namely `AddCommGroup
(AdicPrincipalUnits F)`.
-/
instance (F : CompleteDVF.{u, v} K) : AddCommGroup (AdicPrincipalUnits F) :=
  (equiv F).addCommGroup

/-- Put a first principal unit into the canonical adic model. -/
def of (F : CompleteDVF.{u, v} K)
    (x : Additive
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)) :
    AdicPrincipalUnits F :=
  ⟨x⟩

/-- Establishes the identity `(of F x).val = x`. -/
@[simp] theorem val_of (F : CompleteDVF.{u, v} K)
    (x : Additive
      ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1)) :
    (of F x).val = x := rfl

/-- Establishes the identity `of F x.val = x`. -/
@[simp] theorem of_val (F : CompleteDVF.{u, v} K)
    (x : AdicPrincipalUnits F) : of F x.val = x := by
  cases x
  rfl

/-- The algebraic equivalence underlying the adic model. -/
def addEquiv (F : CompleteDVF.{u, v} K) :
    AdicPrincipalUnits F ≃+
      Additive
        ((LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F) 1) :=
  (equiv F).addEquiv

end AdicPrincipalUnits

/-- The `n`-th principal-unit quotient with its mathematically intended
discrete topology fixed in the type.  Its carrier is finite when `F` is a
`LocalField`, but not for an arbitrary `CompleteDVF`. -/
structure DiscretePrincipalUnitQuotient
    (F : CompleteDVF.{u, v} K) (n : ℕ) where
  /-- The underlying quotient class. -/
  val : Additive (Internal.principalUnitQuotientCarrier F n)

namespace DiscretePrincipalUnitQuotient

/-- Establishes the identity `x = y`. -/
@[ext]
theorem ext {F : CompleteDVF.{u, v} K} {n : ℕ}
    {x y : DiscretePrincipalUnitQuotient F n} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  cases h
  rfl

/-- The carrier equivalence of a discrete coordinate. -/
def equiv (F : CompleteDVF.{u, v} K) (n : ℕ) :
    DiscretePrincipalUnitQuotient F n ≃
      Additive (Internal.principalUnitQuotientCarrier F n) where
  toFun := DiscretePrincipalUnitQuotient.val
  invFun := fun x => ⟨x⟩
  left_inv := fun x => by cases x; rfl
  right_inv := fun _ => rfl

/--
Equips the target with its canonical `TopologicalSpace` structure, namely `TopologicalSpace
(DiscretePrincipalUnitQuotient F n)`.
-/
instance (F : CompleteDVF.{u, v} K) (n : ℕ) :
    TopologicalSpace (DiscretePrincipalUnitQuotient F n) := ⊥

/--
Equips the target with its canonical `DiscreteTopology` structure, namely `DiscreteTopology
(DiscretePrincipalUnitQuotient F n)`.
-/
instance (F : CompleteDVF.{u, v} K) (n : ℕ) :
    DiscreteTopology (DiscretePrincipalUnitQuotient F n) :=
  ⟨rfl⟩

/--
Equips the target with its canonical `AddCommGroup` structure, namely `AddCommGroup
(DiscretePrincipalUnitQuotient F n)`.
-/
instance (F : CompleteDVF.{u, v} K) (n : ℕ) :
    AddCommGroup (DiscretePrincipalUnitQuotient F n) :=
  (equiv F n).addCommGroup

/-- Algebraic equivalence forgetting the discrete coordinate wrapper. -/
def addEquiv (F : CompleteDVF.{u, v} K) (n : ℕ) :
    DiscretePrincipalUnitQuotient F n ≃+
      Additive (Internal.principalUnitQuotientCarrier F n) :=
  (equiv F n).addEquiv

/-- The defining evaluation formula for `addEquiv` is `addEquiv F n x = x.val`. -/
@[simp] theorem addEquiv_apply (F : CompleteDVF.{u, v} K) (n : ℕ)
    (x : DiscretePrincipalUnitQuotient F n) :
    addEquiv F n x = x.val :=
  rfl

/-- Put a quotient class into its discrete model. -/
def of (F : CompleteDVF.{u, v} K) (n : ℕ)
    (x : Additive (Internal.principalUnitQuotientCarrier F n)) :
    DiscretePrincipalUnitQuotient F n :=
  ⟨x⟩

/-- The defining evaluation formula for `addEquiv` is `(addEquiv F n).symm x = of F n x`. -/
@[simp] theorem addEquiv_symm_apply (F : CompleteDVF.{u, v} K) (n : ℕ)
    (x : Additive (Internal.principalUnitQuotientCarrier F n)) :
    (addEquiv F n).symm x = of F n x :=
  rfl

/-- Establishes the identity `(of F n x).val = x`. -/
@[simp] theorem val_of (F : CompleteDVF.{u, v} K) (n : ℕ)
    (x : Additive (Internal.principalUnitQuotientCarrier F n)) :
    (of F n x).val = x := rfl

/-- Establishes the identity `addEquiv F n (of F n x) = x`. -/
@[simp] theorem addEquiv_of (F : CompleteDVF.{u, v} K) (n : ℕ)
    (x : Additive (Internal.principalUnitQuotientCarrier F n)) :
    addEquiv F n (of F n x) = x := by
  rw [addEquiv_apply, val_of]

/-- Establishes the identity `of F n x.val = x`. -/
@[simp] theorem of_val (F : CompleteDVF.{u, v} K) (n : ℕ)
    (x : DiscretePrincipalUnitQuotient F n) :
    of F n x.val = x := by
  cases x
  rfl

end DiscretePrincipalUnitQuotient

/-- The product topology of the discrete coordinates on the additive
principal-unit inverse limit. -/
@[implicit_reducible]
noncomputable def principalUnitProdiscreteTopology
    (F : CompleteDVF.{u, v} K) :
    TopologicalSpace (Additive (Internal.principalUnitInverseLimitCarrier F)) := by
  letI : (n : ℕ) → TopologicalSpace (Internal.principalUnitQuotientCarrier F n) :=
    fun _ => ⊥
  exact inferInstance

/-- The principal-unit inverse limit with its prodiscrete topology fixed in
the type.  For a local field, the coordinate quotients are finite and this
specializes to the usual profinite topology. -/
structure PrincipalUnitProdiscreteLimit (F : CompleteDVF.{u, v} K) where
  /-- The underlying compatible family. -/
  val : Additive (Internal.principalUnitInverseLimitCarrier F)

namespace PrincipalUnitProdiscreteLimit

/-- The carrier equivalence of the prodiscrete inverse-limit model. -/
def equiv (F : CompleteDVF.{u, v} K) :
    PrincipalUnitProdiscreteLimit F ≃
      Additive (Internal.principalUnitInverseLimitCarrier F) where
  toFun := PrincipalUnitProdiscreteLimit.val
  invFun := fun x => ⟨x⟩
  left_inv := fun x => by cases x; rfl
  right_inv := fun _ => rfl

/--
Equips the target with its canonical `TopologicalSpace` structure, namely `TopologicalSpace
(PrincipalUnitProdiscreteLimit F)`.
-/
noncomputable instance (F : CompleteDVF.{u, v} K) :
    TopologicalSpace (PrincipalUnitProdiscreteLimit F) :=
  (principalUnitProdiscreteTopology F).induced PrincipalUnitProdiscreteLimit.val

/-- Forget the wrapper while retaining its fixed prodiscrete topology. -/
noncomputable def homeomorph (F : CompleteDVF.{u, v} K) :
    PrincipalUnitProdiscreteLimit F ≃ₜ
      WithTopology
        (Additive (Internal.principalUnitInverseLimitCarrier F))
        (principalUnitProdiscreteTopology F) where
  toEquiv := (equiv F).trans
    (WithTopology.equiv _ (principalUnitProdiscreteTopology F)).symm
  continuous_toFun := by
    let : TopologicalSpace
        (Additive (Internal.principalUnitInverseLimitCarrier F)) :=
      principalUnitProdiscreteTopology F
    change Continuous fun x : PrincipalUnitProdiscreteLimit F =>
      WithTopology.toTopology (principalUnitProdiscreteTopology F) x.val
    exact
      (WithTopology.continuous_toTopology (principalUnitProdiscreteTopology F)).comp
        continuous_induced_dom
  continuous_invFun := by
    let : TopologicalSpace
        (Additive (Internal.principalUnitInverseLimitCarrier F)) :=
      principalUnitProdiscreteTopology F
    change Continuous fun x : WithTopology
        (Additive (Internal.principalUnitInverseLimitCarrier F))
        (principalUnitProdiscreteTopology F) =>
      (⟨x.ofTopology⟩ : PrincipalUnitProdiscreteLimit F)
    exact
      continuous_induced_rng.2
        (WithTopology.continuous_ofTopology (principalUnitProdiscreteTopology F))

/--
Equips the target with its canonical `AddCommGroup` structure, namely `AddCommGroup
(PrincipalUnitProdiscreteLimit F)`.
-/
instance (F : CompleteDVF.{u, v} K) :
    AddCommGroup (PrincipalUnitProdiscreteLimit F) :=
  (equiv F).addCommGroup

/-- The algebraic equivalence forgetting the type-level prodiscrete model. -/
def addEquiv (F : CompleteDVF.{u, v} K) :
    PrincipalUnitProdiscreteLimit F ≃+
      Additive (Internal.principalUnitInverseLimitCarrier F) :=
  (equiv F).addEquiv

/-- The defining evaluation formula for `addEquiv` is `addEquiv F x = x.val`. -/
@[simp] theorem addEquiv_apply (F : CompleteDVF.{u, v} K)
    (x : PrincipalUnitProdiscreteLimit F) :
    addEquiv F x = x.val :=
  rfl

/-- Put a compatible family into its prodiscrete model. -/
def of (F : CompleteDVF.{u, v} K)
    (x : Additive (Internal.principalUnitInverseLimitCarrier F)) :
    PrincipalUnitProdiscreteLimit F :=
  ⟨x⟩

/-- The defining evaluation formula for `addEquiv` is `(addEquiv F).symm x = of F x`. -/
@[simp] theorem addEquiv_symm_apply (F : CompleteDVF.{u, v} K)
    (x : Additive (Internal.principalUnitInverseLimitCarrier F)) :
    (addEquiv F).symm x = of F x :=
  rfl

/-- Establishes the identity `(of F x).val = x`. -/
@[simp] theorem val_of (F : CompleteDVF.{u, v} K)
    (x : Additive (Internal.principalUnitInverseLimitCarrier F)) :
    (of F x).val = x := rfl

/-- Establishes the identity `of F x.val = x`. -/
@[simp] theorem of_val (F : CompleteDVF.{u, v} K)
    (x : PrincipalUnitProdiscreteLimit F) : of F x.val = x := by
  cases x
  rfl

/-- Evaluation at one discrete coordinate, as an additive homomorphism. -/
def coordinate (F : CompleteDVF.{u, v} K) (n : ℕ) :
    PrincipalUnitProdiscreteLimit F →+
      DiscretePrincipalUnitQuotient F n :=
  (DiscretePrincipalUnitQuotient.addEquiv F n).symm.toAddMonoidHom.comp
    ((MonoidHom.toAdditive
      (Internal.principalUnitInverseLimitCarrierEval F n)).comp
        (addEquiv F).toAddMonoidHom)

/--
The defining evaluation formula for `coordinate` is `coordinate F n x =
DiscretePrincipalUnitQuotient.of F n (Additive.ofMul
(Internal.principalUnitInverseLimitCarrierEval F n (Additive.toMul (addEquiv F x))))`.
-/
@[simp] theorem coordinate_apply (F : CompleteDVF.{u, v} K) (n : ℕ)
    (x : PrincipalUnitProdiscreteLimit F) :
    coordinate F n x = DiscretePrincipalUnitQuotient.of F n
      (Additive.ofMul
        (Internal.principalUnitInverseLimitCarrierEval F n
          (Additive.toMul (addEquiv F x)))) :=
  rfl

end PrincipalUnitProdiscreteLimit

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField
