/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.Algebra.Module.MinimalAxioms
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.FiniteQuotientPadicModule
/-!
# The p-adic module on the prodiscrete principal-unit limit

Coordinatewise scalar multiplication makes the prodiscrete inverse limit a topological
module over the p-adic integers.
-/

@[expose] public section

noncomputable
section

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

/-! ## The inverse-limit module and transport to `U^1` -/

/-- Coordinatewise p-adic scalar multiplication on the compatible inverse
limit. -/
noncomputable instance Internal.principalUnitInverseLimitCarrierPadicSMul
    (F : LocalField.{u, v} K) :
    SMul ℤ_[F.residueCharacteristic]
      (Additive (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF)) where
  smul a x := Additive.ofMul
    ⟨fun n => Additive.toMul
        (a • Additive.ofMul ((Additive.toMul x).1 n)), by
      intro m n hmn
      apply Additive.ofMul.injective
      change
        principalUnitQuotientCarrierTransitionAdd F.toCompleteDVF hmn
            (a • Additive.ofMul ((Additive.toMul x).1 n)) =
          a • Additive.ofMul ((Additive.toMul x).1 m)
      rw [principalUnitQuotientCarrierTransitionAdd_map_smul]
      change
        a • Additive.ofMul
            (principalUnitQuotientCarrierTransition F.toCompleteDVF hmn
              ((Additive.toMul x).1 n)) =
          a • Additive.ofMul ((Additive.toMul x).1 m)
      rw [(Additive.toMul x).2 hmn]⟩

/--
The defining evaluation formula for `Internal.principalUnitInverseLimitCarrierPadic_smul` is
`Additive.ofMul (Internal.principalUnitInverseLimitCarrierEval F.toCompleteDVF n (Additive.toMul
(a • x))) = a • Additive.ofMul (Internal.principalUnitInverseLimitCarrierEval F.toCompleteDVF n
(Additive.toMul x))`.
-/
theorem Internal.principalUnitInverseLimitCarrierPadic_smul_apply
    (F : LocalField.{u, v} K)
    (a : ℤ_[F.residueCharacteristic])
    (x : Additive (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF))
    (n : ℕ) :
    Additive.ofMul
        (Internal.principalUnitInverseLimitCarrierEval F.toCompleteDVF n
          (Additive.toMul (a • x))) =
      a • Additive.ofMul
        (Internal.principalUnitInverseLimitCarrierEval F.toCompleteDVF n
          (Additive.toMul x)) :=
  rfl

/--
Equips the target in `Module ℤ_[F.residueCharacteristic] (Additive
(Internal.principalUnitInverseLimitCarrier F.toCompleteDVF))` with the indicated module structure.
-/
noncomputable instance Internal.principalUnitInverseLimitCarrierPadicModule
    (F : LocalField.{u, v} K) :
    Module ℤ_[F.residueCharacteristic]
      (Additive (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF)) :=
  Module.ofMinimalAxioms
    (fun (a : ℤ_[F.residueCharacteristic])
        (x y : Additive
          (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF)) => by
      apply Additive.toMul.injective
      apply Subtype.ext
      funext n
      let : Module ℤ_[F.residueCharacteristic]
          (Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n)) :=
        principalUnitQuotientCarrierPadicModule F n
      apply Additive.ofMul.injective
      change
        a • (Additive.ofMul ((Additive.toMul x).1 n) +
          Additive.ofMul ((Additive.toMul y).1 n)) =
        a • Additive.ofMul ((Additive.toMul x).1 n) +
          a • Additive.ofMul ((Additive.toMul y).1 n)
      exact (principalUnitQuotientCarrierPadicModule F n).smul_add a
        (Additive.ofMul ((Additive.toMul x).1 n))
        (Additive.ofMul ((Additive.toMul y).1 n)))
    (fun (a b : ℤ_[F.residueCharacteristic])
        (x : Additive
          (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF)) => by
      apply Additive.toMul.injective
      apply Subtype.ext
      funext n
      let : Module ℤ_[F.residueCharacteristic]
          (Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n)) :=
        principalUnitQuotientCarrierPadicModule F n
      apply Additive.ofMul.injective
      change
        (a + b) • Additive.ofMul ((Additive.toMul x).1 n) =
          a • Additive.ofMul ((Additive.toMul x).1 n) +
            b • Additive.ofMul ((Additive.toMul x).1 n)
      exact (principalUnitQuotientCarrierPadicModule F n).add_smul a b
        (Additive.ofMul ((Additive.toMul x).1 n)))
    (fun (a b : ℤ_[F.residueCharacteristic])
        (x : Additive
          (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF)) => by
      apply Additive.toMul.injective
      apply Subtype.ext
      funext n
      let : Module ℤ_[F.residueCharacteristic]
          (Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n)) :=
        principalUnitQuotientCarrierPadicModule F n
      apply Additive.ofMul.injective
      change
        (a * b) • Additive.ofMul ((Additive.toMul x).1 n) =
          a • b • Additive.ofMul ((Additive.toMul x).1 n)
      exact (principalUnitQuotientCarrierPadicModule F n).mul_smul a b
        (Additive.ofMul ((Additive.toMul x).1 n)))
    (fun (x : Additive
        (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF)) => by
      apply Additive.toMul.injective
      apply Subtype.ext
      funext n
      let : Module ℤ_[F.residueCharacteristic]
          (Additive (Internal.principalUnitQuotientCarrier F.toCompleteDVF n)) :=
        principalUnitQuotientCarrierPadicModule F n
      apply Additive.ofMul.injective
      change
        (1 : ℤ_[F.residueCharacteristic]) •
            Additive.ofMul ((Additive.toMul x).1 n) =
          Additive.ofMul ((Additive.toMul x).1 n)
      exact (principalUnitQuotientCarrierPadicModule F n).one_smul
        (Additive.ofMul ((Additive.toMul x).1 n)))

/--
Equips the target in `Module ℤ_[F.residueCharacteristic] (PrincipalUnitProdiscreteLimit
F.toCompleteDVF)` with the indicated module structure.
-/
noncomputable instance principalUnitProdiscreteLimitPadicModule
    (F : LocalField.{u, v} K) :
    Module ℤ_[F.residueCharacteristic]
      (PrincipalUnitProdiscreteLimit F.toCompleteDVF) :=
  AddEquiv.module
    (β := Additive (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF))
    ℤ_[F.residueCharacteristic]
    (PrincipalUnitProdiscreteLimit.addEquiv F.toCompleteDVF)

/--
Establishes the identity `PrincipalUnitProdiscreteLimit.addEquiv F.toCompleteDVF (a • x) = a •
PrincipalUnitProdiscreteLimit.addEquiv F.toCompleteDVF x`.
-/
theorem PrincipalUnitProdiscreteLimit.addEquiv_map_smul
    (F : LocalField.{u, v} K) (a : ℤ_[F.residueCharacteristic])
    (x : PrincipalUnitProdiscreteLimit F.toCompleteDVF) :
    PrincipalUnitProdiscreteLimit.addEquiv F.toCompleteDVF (a • x) =
      a • PrincipalUnitProdiscreteLimit.addEquiv F.toCompleteDVF x :=
  rfl

/--
Establishes the identity `PrincipalUnitProdiscreteLimit.coordinate F.toCompleteDVF n (a • x) = a •
PrincipalUnitProdiscreteLimit.coordinate F.toCompleteDVF n x`.
-/
theorem PrincipalUnitProdiscreteLimit.coordinate_smul
    (F : LocalField.{u, v} K) (n : ℕ)
    (a : ℤ_[F.residueCharacteristic])
    (x : PrincipalUnitProdiscreteLimit F.toCompleteDVF) :
    PrincipalUnitProdiscreteLimit.coordinate F.toCompleteDVF n (a • x) =
      a • PrincipalUnitProdiscreteLimit.coordinate F.toCompleteDVF n x := by
  apply (DiscretePrincipalUnitQuotient.addEquiv F.toCompleteDVF n).injective
  rw [DiscretePrincipalUnitQuotient.addEquiv_map_smul,
    PrincipalUnitProdiscreteLimit.coordinate_apply,
    PrincipalUnitProdiscreteLimit.coordinate_apply,
    DiscretePrincipalUnitQuotient.addEquiv_of,
    DiscretePrincipalUnitQuotient.addEquiv_of,
    PrincipalUnitProdiscreteLimit.addEquiv_map_smul]
  exact Internal.principalUnitInverseLimitCarrierPadic_smul_apply F a
    (PrincipalUnitProdiscreteLimit.addEquiv F.toCompleteDVF x) n

/-- Evaluation at a wrapped coordinate as a `Z_p`-linear map. -/
noncomputable def PrincipalUnitProdiscreteLimit.coordinateLinear
    (F : LocalField.{u, v} K) (n : ℕ) :
    PrincipalUnitProdiscreteLimit F.toCompleteDVF →ₗ[
      ℤ_[F.residueCharacteristic]]
      DiscretePrincipalUnitQuotient F.toCompleteDVF n where
  toFun := PrincipalUnitProdiscreteLimit.coordinate F.toCompleteDVF n
  map_add' := fun x y =>
    (PrincipalUnitProdiscreteLimit.coordinate F.toCompleteDVF n).map_add x y
  map_smul' := PrincipalUnitProdiscreteLimit.coordinate_smul F n

/-- Joint continuity of the coordinatewise p-adic action on the inverse
limit of discrete finite quotients. -/
theorem Internal.continuous_principalUnitInverseLimitCarrierPadic_smul
    (F : LocalField.{u, v} K) :
    letI : (n : ℕ) → TopologicalSpace
        (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) := fun _ => ⊥
    Continuous fun z : ℤ_[F.residueCharacteristic] ×
        Additive (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF) =>
      z.1 • z.2 := by
  let : (n : ℕ) → TopologicalSpace
      (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) := fun _ => ⊥
  let : (n : ℕ) → DiscreteTopology
      (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) := fun _ => ⟨rfl⟩
  have hmul : Continuous fun z : ℤ_[F.residueCharacteristic] ×
      Additive (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF) =>
      Additive.toMul (z.1 • z.2) := by
    exact Continuous.subtype_mk
      (continuous_pi fun n => by
        have hlimval : Continuous fun x : Additive
            (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF) =>
            (Additive.toMul x).1 :=
          continuous_subtype_val
        have hcoord : Continuous fun z : ℤ_[F.residueCharacteristic] ×
            Additive (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF) =>
            Additive.ofMul ((Additive.toMul z.2).1 n) :=
          ((continuous_apply n).comp hlimval).comp continuous_snd
        have hs := (Internal.continuous_principalUnitQuotientCarrierPadicScalar F n).comp
          (continuous_fst.prodMk hcoord)
        change Continuous fun z : ℤ_[F.residueCharacteristic] ×
            Additive (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF) =>
          Additive.toMul
            (principalUnitQuotientCarrierPadicScalar F n z.1
              (Additive.ofMul ((Additive.toMul z.2).1 n)))
        exact hs)
      (fun z : ℤ_[F.residueCharacteristic] ×
          Additive (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF) => by
        intro i j hij
        exact (Additive.toMul (z.1 • z.2)).2 hij)
  exact hmul

/--
The specified map is continuous: `Continuous fun z : ℤ_[F.residueCharacteristic] ×
PrincipalUnitProdiscreteLimit F.toCompleteDVF => z.1 • z.2`.
-/
theorem continuous_principalUnitProdiscreteLimitPadic_smul
    (F : LocalField.{u, v} K) :
    Continuous fun z : ℤ_[F.residueCharacteristic] ×
        PrincipalUnitProdiscreteLimit F.toCompleteDVF =>
      z.1 • z.2 := by
  let : (n : ℕ) → TopologicalSpace
      (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) := fun _ => ⊥
  let e := (PrincipalUnitProdiscreteLimit.homeomorph F.toCompleteDVF).trans
    (WithTopology.homeomorph
      (α := Additive
        (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF))
      (topology := principalUnitProdiscreteTopology F.toCompleteDVF))
  have hpair : Continuous fun z : ℤ_[F.residueCharacteristic] ×
      PrincipalUnitProdiscreteLimit F.toCompleteDVF =>
      (z.1, e z.2) :=
    continuous_fst.prodMk (e.continuous.comp continuous_snd)
  have h := e.continuous_symm.comp
    ((Internal.continuous_principalUnitInverseLimitCarrierPadic_smul F).comp hpair)
  exact h

/--
The scalar action in `ContinuousSMul ℤ_[F.residueCharacteristic] (PrincipalUnitProdiscreteLimit
F.toCompleteDVF)` is continuous.
-/
noncomputable instance principalUnitProdiscreteLimitContinuousSMul
    (F : LocalField.{u, v} K) :
    ContinuousSMul ℤ_[F.residueCharacteristic]
      (PrincipalUnitProdiscreteLimit F.toCompleteDVF) :=
  ⟨continuous_principalUnitProdiscreteLimitPadic_smul F⟩

/-- Addition on the type-level prodiscrete principal-unit limit is
continuous. -/
noncomputable instance principalUnitProdiscreteLimitContinuousAdd
    (F : LocalField.{u, v} K) :
    ContinuousAdd (PrincipalUnitProdiscreteLimit F.toCompleteDVF) := by
  let : (n : ℕ) → TopologicalSpace
      (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) := fun _ => ⊥
  let : (n : ℕ) → DiscreteTopology
      (Internal.principalUnitQuotientCarrier F.toCompleteDVF n) := fun _ => ⟨rfl⟩
  let e := (PrincipalUnitProdiscreteLimit.homeomorph F.toCompleteDVF).trans
    (WithTopology.homeomorph
      (α := Additive
        (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF))
      (topology := principalUnitProdiscreteTopology F.toCompleteDVF))
  refine ⟨?_⟩
  have hlim : Continuous fun z :
      Additive (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF) ×
        Additive (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF) =>
      z.1 + z.2 := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro n
    have hx : Continuous fun z :
        Additive (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF) ×
          Additive (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF) =>
        (Additive.toMul z.1).1 n :=
      (continuous_apply n).comp
        (continuous_subtype_val.comp continuous_fst)
    have hy : Continuous fun z :
        Additive (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF) ×
          Additive (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF) =>
        (Additive.toMul z.2).1 n :=
      (continuous_apply n).comp
        (continuous_subtype_val.comp continuous_snd)
    exact (continuous_of_discreteTopology : Continuous fun z :
      Internal.principalUnitQuotientCarrier F.toCompleteDVF n ×
        Internal.principalUnitQuotientCarrier F.toCompleteDVF n => z.1 * z.2).comp
      (hx.prodMk hy)
  have hpair : Continuous fun z :
      PrincipalUnitProdiscreteLimit F.toCompleteDVF ×
        PrincipalUnitProdiscreteLimit F.toCompleteDVF =>
      (e z.1, e z.2) :=
    (e.continuous.comp continuous_fst).prodMk
      (e.continuous.comp continuous_snd)
  have htransport := e.continuous_symm.comp (hlim.comp hpair)
  exact htransport

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField
