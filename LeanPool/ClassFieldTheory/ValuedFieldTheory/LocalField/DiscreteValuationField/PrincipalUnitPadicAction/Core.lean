/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.InverseLimitCore
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.TopologyModelTypes
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.InverseLimitTopology
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.AdicProdiscreteComparison
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.FiniteQuotientPadicModule
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.ProdiscretePadicModule
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.AdicPadicModule
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.WithZeroValuationTopology
/-!
Assembles the inverse-limit and topological models used to define the `ℤ_[p]`-module structure on
principal units.
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

/-- Natural p-adic scalars act by the ordinary group powers. -/
theorem principalUnitPadic_natCast_smul
    (F : LocalField.{u, v} K) (n : ℕ)
    (x : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      F.toCompleteDVF) 1) :
    (n : ℤ_[F.residueCharacteristic]) • Additive.ofMul x =
      Additive.ofMul (x ^ n) := by
  calc
    (n : ℤ_[F.residueCharacteristic]) • Additive.ofMul x =
        n • Additive.ofMul x :=
      Nat.cast_smul_eq_nsmul ℤ_[F.residueCharacteristic] n (Additive.ofMul x)
    _ = Additive.ofMul (x ^ n) := rfl

/-- Equivalent multiplicative reading of
`principalUnitPadic_natCast_smul`. -/
theorem principalUnitPadic_nsmul_eq_pow
    (F : LocalField.{u, v} K) (n : ℕ)
    (x : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      F.toCompleteDVF) 1) :
    Additive.toMul
        ((n : ℤ_[F.residueCharacteristic]) • Additive.ofMul x) = x ^ n := by
  exact congrArg Additive.toMul
    (principalUnitPadic_natCast_smul F n x)

/-- Every `U^r`, for `r >= 1`, is stable under the canonical p-adic action
on `U^1`. -/
theorem principalUnitPadic_smul_mem_higher
    (F : LocalField.{u, v} K) {r : ℕ} (hr : 1 ≤ r)
    (a : ℤ_[F.residueCharacteristic])
    (x : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      F.toCompleteDVF) 1)
    (hx : (x : F.valuationSubringˣ) ∈
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        F.toCompleteDVF) r) :
    ((Additive.toMul (a • Additive.ofMul x) :
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
          F.toCompleteDVF) 1) :
      F.valuationSubringˣ) ∈
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
          F.toCompleteDVF) r := by
  let n := r - 1
  have hn : n + 1 = r := Nat.sub_add_cancel hr
  let y : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
    F.toCompleteDVF) 1 :=
    Additive.toMul (a • Additive.ofMul x)
  have hxq :
      (higherPrincipalUnitGroup.toPrincipalUnitFiltration
        F.toCompleteDVF).principalUnitSubquotientMk
        1 (n + 1) x = 1 := by
    exact ((higherPrincipalUnitGroup.toPrincipalUnitFiltration
      F.toCompleteDVF).principalUnitSubquotient_mk_eq_one_iff x).2
      (by
        change (x : F.valuationSubringˣ) ∈
          (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
            F.toCompleteDVF) (n + 1)
        rw [hn]
        exact hx)
  have hcoord :
      Additive.ofMul
          (principalUnitInverseLimitCarrierEval F.toCompleteDVF n
            (principalUnitMulEquivInverseLimitCarrier F.toCompleteDVF y)) =
        a • Additive.ofMul
          (principalUnitInverseLimitCarrierEval F.toCompleteDVF n
            (principalUnitMulEquivInverseLimitCarrier F.toCompleteDVF x)) := by
    have h := congrArg
      (fun z : Additive
          (Internal.principalUnitInverseLimitCarrier F.toCompleteDVF) =>
        Additive.ofMul
          (principalUnitInverseLimitCarrierEval F.toCompleteDVF n
            (Additive.toMul z)))
      (principalUnitAddEquivInverseLimitCarrier_map_smul
        F a (Additive.ofMul x))
    exact h
  have hyq :
      (higherPrincipalUnitGroup.toPrincipalUnitFiltration
        F.toCompleteDVF).principalUnitSubquotientMk
        1 (n + 1) y = 1 := by
    apply Additive.ofMul.injective
    calc
      Additive.ofMul
          ((higherPrincipalUnitGroup.toPrincipalUnitFiltration
            F.toCompleteDVF).principalUnitSubquotientMk
            1 (n + 1) y) =
          a • Additive.ofMul
            ((higherPrincipalUnitGroup.toPrincipalUnitFiltration
              F.toCompleteDVF).principalUnitSubquotientMk
              1 (n + 1) x) := by
        simpa only [principalUnitMulEquivInverseLimitCarrier_apply] using hcoord
      _ = a • Additive.ofMul (1 :
          Internal.principalUnitQuotientCarrier F.toCompleteDVF n) := by rw [hxq]
      _ = 0 := by
        rw [show Additive.ofMul
          (1 : Internal.principalUnitQuotientCarrier F.toCompleteDVF n) = 0 from rfl]
        exact (principalUnitQuotientCarrierPadicModule F n).smul_zero a
      _ = Additive.ofMul (1 :
          Internal.principalUnitQuotientCarrier F.toCompleteDVF n) := rfl
  change (y : F.valuationSubringˣ) ∈
    (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF) r
  rw [← hn]
  exact ((higherPrincipalUnitGroup.toPrincipalUnitFiltration
    F.toCompleteDVF).principalUnitSubquotient_mk_eq_one_iff y).1 hyq

/-- A p-adic scalar divisible by the residue characteristic kills the leading
graded class: on `U^r` it lands in `U^(r+1)`. -/
theorem principalUnitPadic_residueCharacteristic_mul_smul_mem_succ
    (F : LocalField.{u, v} K) {r : ℕ} (hr : 1 ≤ r)
    (b : ℤ_[F.residueCharacteristic])
    (x : (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      F.toCompleteDVF) 1)
    (hx : (x : F.valuationSubringˣ) ∈
      (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        F.toCompleteDVF) r) :
    ((Additive.toMul
        (((F.residueCharacteristic : ℤ_[F.residueCharacteristic]) * b) •
          Additive.ofMul x) :
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
          F.toCompleteDVF) 1) :
      F.valuationSubringˣ) ∈
        (LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
          F.toCompleteDVF) (r + 1) := by
  have hscalar :
      ((F.residueCharacteristic : ℤ_[F.residueCharacteristic]) * b) •
          Additive.ofMul x =
        b • Additive.ofMul (x ^ F.residueCharacteristic) := by
    rw [mul_comm, mul_smul, principalUnitPadic_natCast_smul]
  rw [hscalar]
  apply principalUnitPadic_smul_mem_higher F
    (Nat.succ_le_succ (Nat.zero_le r)) b (x ^ F.residueCharacteristic)
  exact higherPrincipalUnitGroup.pow_mem_succ_of_residue_ringChar_eq
    F.toCompleteDVF
    (residueCharacteristic_prime_and_card_eq_pow_residueDegree F).1 hr rfl hx

end higherPrincipalUnitGroup
end CompleteDVF
end LocalFieldTheory.DiscreteValuationField
