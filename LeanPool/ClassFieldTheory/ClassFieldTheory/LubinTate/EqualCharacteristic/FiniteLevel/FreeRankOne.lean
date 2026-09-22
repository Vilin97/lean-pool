/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.SetTheory.Cardinal.Finite
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.AmbientDivisionTorsion
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.FiniteParameters
import Mathlib.Algebra.Module.RingHom
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.FreeModule.Basic
/-!
# The primitive-division-module equivalence: equal-characteristic division points are free of
  rank one

For the standard equal-characteristic Lubin--Tate series, the points killed by
the `(n + 1)`-st iterate form a free rank-one module over
`κ⟦T⟧/(T^(n+1))`.  The shift is intentional: the existing division-tower
The primitive polynomial is indexed by `n`, while its roots lie at division
level `n + 1`.
-/

noncomputable section

open scoped PowerSeries LaurentSeries Polynomial

universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- All coefficients visible at division level `n + 1`.  In contrast with the
unit parameters used for the primitive roots in the uniformizer norm identity, the constant
coefficient is allowed to vanish; this is necessary to parametrize every
division point. -/
structure equalCharacteristicLubinTateParameter
    (F : LocalField.{u, v} K) (n : ℕ) where
  /-- The coefficients in degrees `0` through `n` of the represented truncated series. -/
  coeff : Fin (n + 1) → F.residueField

/-- A Lubin–Tate parameter evaluates to its finite coefficient function. -/
instance equalCharacteristicLubinTateParameterCoeFun
    (F : LocalField.{u, v} K) (n : ℕ) :
    CoeFun (equalCharacteristicLubinTateParameter F n)
      (fun _ => Fin (n + 1) → F.residueField) :=
  ⟨equalCharacteristicLubinTateParameter.coeff⟩

/-- Construct a finite parameter from its coefficient function. -/
def equalCharacteristicLubinTateParameterOfFunction
    (F : LocalField.{u, v} K) (n : ℕ)
    (coeff : Fin (n + 1) → F.residueField) :
    equalCharacteristicLubinTateParameter F n :=
  ⟨coeff⟩

/-- Comparison with the raw finite coefficient function. -/
def equalCharacteristicLubinTateParameterEquiv
    (F : LocalField.{u, v} K) (n : ℕ) :
    equalCharacteristicLubinTateParameter F n ≃
      (Fin (n + 1) → F.residueField) where
  toFun := equalCharacteristicLubinTateParameter.coeff
  invFun := equalCharacteristicLubinTateParameterOfFunction F n
  left_inv a := by cases a; rfl
  right_inv _ := rfl

/-- Lubin–Tate parameters are equal when all their coefficients agree. -/
@[ext]
theorem equalCharacteristicLubinTateParameter_ext
    (F : LocalField.{u, v} K) (n : ℕ)
    {a b : equalCharacteristicLubinTateParameter F n}
    (hcoeff : a.coeff = b.coeff) :
    a = b := by
  cases a
  cases b
  cases hcoeff
  rfl

/-- The finite coefficient parameter space is finite. -/
instance equalCharacteristicLubinTateParameter_finite
    (F : LocalField.{u, v} K) (n : ℕ) :
    Finite (equalCharacteristicLubinTateParameter F n) :=
  Finite.of_equiv (Fin (n + 1) → F.residueField)
    (equalCharacteristicLubinTateParameterEquiv F n).symm

/-- The canonical polynomial representative of a finite parameter. -/
noncomputable def equalCharacteristicLubinTateParameterSeries
    (F : LocalField.{u, v} K) (n : ℕ)
    (a : equalCharacteristicLubinTateParameter F n) :
    F.residueField⟦X⟧ :=
  PowerSeries.mk fun i =>
    if hi : i < n + 1 then a ⟨i, hi⟩ else 0

/-- The parameter power series recovers each stored finite coefficient. -/
@[simp]
theorem equalCharacteristicLubinTateParameterSeries_coeff
    (F : LocalField.{u, v} K) (n : ℕ)
    (a : equalCharacteristicLubinTateParameter F n)
    (i : Fin (n + 1)) :
    PowerSeries.coeff i
        (equalCharacteristicLubinTateParameterSeries F n a) = a i := by
  have hi : ¬ n < (i : ℕ) :=
    Nat.not_lt_of_ge (Nat.le_of_lt_succ i.isLt)
  simp [equalCharacteristicLubinTateParameterSeries, hi]

/-- Evaluation of a finite parameter at the chosen primitive division-level
`n + 1` point. -/
noncomputable def equalCharacteristicLubinTateParameterRoot
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : equalCharacteristicLubinTateParameter F n) :
    equalCharacteristicLubinTateAmbientTorsionAddSubgroup F
      (equalCharacteristicSeparableUniformizer F) (n + 1) :=
  ⟨equalCharacteristicLubinTateAmbientBracket F
      (equalCharacteristicSeparableCoefficientHom F)
      (equalCharacteristicSeparableUniformizer F) (n + 1)
      (equalCharacteristicLubinTateParameterSeries F n a)
      (chosenEqualCharacteristicLubinTatePrimitiveRoot F n),
    equalCharacteristicLubinTateAmbientBracket_torsion F
      (equalCharacteristicSeparableCoefficientHom F)
      (equalCharacteristicSeparableUniformizer F) (n + 1)
      (equalCharacteristicLubinTateParameterSeries F n a)
      (chosenEqualCharacteristicLubinTatePrimitiveRoot F n)
      (chosenEqualCharacteristicLubinTatePrimitiveRoot_torsion F n)⟩

/-- The primitive point detects every coefficient modulo `T^(n+1)`. -/
theorem equalCharacteristicLubinTateParameterRoot_injective
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    Function.Injective (equalCharacteristicLubinTateParameterRoot F n) := by
  intro a b hab
  apply equalCharacteristicLubinTateParameter_ext F n
  funext i
  have hvalue :
      (equalCharacteristicLubinTateParameterRoot F n a).1 =
        (equalCharacteristicLubinTateParameterRoot F n b).1 :=
    congrArg Subtype.val hab
  have hcoeff :=
    chosenEqualCharacteristicLubinTatePrimitiveRoot_bracket_eq_coeff F n
      (equalCharacteristicLubinTateParameterSeries F n a)
      (equalCharacteristicLubinTateParameterSeries F n b) hvalue
      i (Nat.le_of_lt_succ i.isLt)
  simpa using hcoeff

/-- The full finite parameter type has `q^(n+1)` elements. -/
theorem equalCharacteristicLubinTateParameter_natCard
    (F : LocalField.{u, v} K) (n : ℕ) :
    Nat.card (equalCharacteristicLubinTateParameter F n) =
      Nat.card F.residueField ^ (n + 1) := by
  rw [Nat.card_congr (equalCharacteristicLubinTateParameterEquiv F n),
    Nat.card_fun, Nat.card_fin]

/-- Level `n + 1` torsion is exactly the root set of the corresponding
division polynomial. -/
noncomputable def equalCharacteristicLubinTateTorsionEquivRootSet
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    equalCharacteristicLubinTateAmbientTorsionAddSubgroup F
        (equalCharacteristicSeparableUniformizer F) (n + 1) ≃
      (equalCharacteristicLubinTatePiPolynomialIterate F (n + 1)).rootSet
        (SeparableClosure F.residueField⸨X⸩) where
  toFun x := ⟨x.1, by
    have hP : equalCharacteristicLubinTatePiPolynomialIterate F (n + 1) ≠ 0 := by
      apply Polynomial.ne_zero_of_natDegree_gt
      rw [equalCharacteristicLubinTatePiPolynomialIterate_natDegree]
      exact Nat.pow_pos Nat.card_pos
    rw [Polynomial.mem_rootSet_of_ne hP, Polynomial.aeval_def,
      ← equalCharacteristicSeparableBaseHom_eq_algebraMap,
      equalCharacteristicLubinTatePiPolynomialIterate_eval₂]
    exact x.2⟩
  invFun x := ⟨x.1, by
    have hP : equalCharacteristicLubinTatePiPolynomialIterate F (n + 1) ≠ 0 := by
      apply Polynomial.ne_zero_of_natDegree_gt
      rw [equalCharacteristicLubinTatePiPolynomialIterate_natDegree]
      exact Nat.pow_pos Nat.card_pos
    have hx := (Polynomial.mem_rootSet_of_ne hP).mp x.2
    rw [Polynomial.aeval_def,
      ← equalCharacteristicSeparableBaseHom_eq_algebraMap,
      equalCharacteristicLubinTatePiPolynomialIterate_eval₂] at hx
    exact hx⟩
  left_inv x := rfl
  right_inv x := rfl

/-- The ambient Lubin–Tate torsion module at finite level is finite. -/
noncomputable instance equalCharacteristicLubinTateAmbientTorsion_finite
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    Finite
      (equalCharacteristicLubinTateAmbientTorsionAddSubgroup F
        (equalCharacteristicSeparableUniformizer F) (n + 1)) :=
  Finite.of_injective
    (equalCharacteristicLubinTateTorsionEquivRootSet F n)
    (equalCharacteristicLubinTateTorsionEquivRootSet F n).injective

/-- The level `n + 1` division group has `q^(n+1)` elements. -/
theorem equalCharacteristicLubinTateAmbientTorsion_natCard
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    Nat.card
        (equalCharacteristicLubinTateAmbientTorsionAddSubgroup F
          (equalCharacteristicSeparableUniformizer F) (n + 1)) =
      Nat.card F.residueField ^ (n + 1) := by
  rw [Nat.card_congr
      (equalCharacteristicLubinTateTorsionEquivRootSet F n),
    Nat.card_eq_fintype_card,
    Polynomial.card_rootSet_eq_natDegree
      (equalCharacteristicLubinTatePiPolynomialIterate_separable F (n + 1))
      (IsSepClosed.splits_codomain
        (equalCharacteristicLubinTatePiPolynomialIterate F (n + 1))
        (equalCharacteristicLubinTatePiPolynomialIterate_separable F (n + 1))),
    equalCharacteristicLubinTatePiPolynomialIterate_natDegree]

/-- Every division-level `n + 1` division point is obtained uniquely by applying
one truncated coefficient series to the chosen primitive point. -/
theorem equalCharacteristicLubinTateParameterRoot_bijective
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    Function.Bijective (equalCharacteristicLubinTateParameterRoot F n) := by
  let := Fintype.ofFinite (equalCharacteristicLubinTateParameter F n)
  let := Fintype.ofFinite
    (equalCharacteristicLubinTateAmbientTorsionAddSubgroup F
      (equalCharacteristicSeparableUniformizer F) (n + 1))
  apply (Fintype.bijective_iff_injective_and_card
    (equalCharacteristicLubinTateParameterRoot F n)).mpr
  refine ⟨equalCharacteristicLubinTateParameterRoot_injective F n, ?_⟩
  calc
    Fintype.card (equalCharacteristicLubinTateParameter F n) =
        Nat.card (equalCharacteristicLubinTateParameter F n) := by
      rw [Nat.card_eq_fintype_card]
    _ = Nat.card F.residueField ^ (n + 1) :=
      equalCharacteristicLubinTateParameter_natCard F n
    _ = Nat.card
        (equalCharacteristicLubinTateAmbientTorsionAddSubgroup F
          (equalCharacteristicSeparableUniformizer F) (n + 1)) :=
      (equalCharacteristicLubinTateAmbientTorsion_natCard F n).symm
    _ = Fintype.card
        (equalCharacteristicLubinTateAmbientTorsionAddSubgroup F
          (equalCharacteristicSeparableUniformizer F) (n + 1)) := by
      rw [Nat.card_eq_fintype_card]

/-- The coefficient ring at division level `n + 1`. -/
def equalCharacteristicLubinTateTruncatedRing
    (F : LocalField.{u, v} K) (n : ℕ) :=
  F.residueField⟦X⟧ ⧸
    Ideal.span ({PowerSeries.X ^ (n + 1)} : Set F.residueField⟦X⟧)

/-- The commutative ring structure on the named truncated coefficient
ring. -/
instance equalCharacteristicLubinTateTruncatedRingCommRing
    (F : LocalField.{u, v} K) (n : ℕ) :
    CommRing (equalCharacteristicLubinTateTruncatedRing F n) := by
  change CommRing
    (F.residueField⟦X⟧ ⧸
      Ideal.span ({PowerSeries.X ^ (n + 1)} : Set F.residueField⟦X⟧))
  infer_instance

/-- Comparison with the quotient-ring presentation used by the ring
library. -/
def equalCharacteristicLubinTateTruncatedRingEquiv
    (F : LocalField.{u, v} K) (n : ℕ) :
    equalCharacteristicLubinTateTruncatedRing F n ≃+*
      (F.residueField⟦X⟧ ⧸
        Ideal.span ({PowerSeries.X ^ (n + 1)} : Set F.residueField⟦X⟧)) :=
  RingEquiv.refl _

/-- The canonical projection to the named truncated coefficient ring. -/
def equalCharacteristicLubinTateTruncatedRingMk
    (F : LocalField.{u, v} K) (n : ℕ) :
    F.residueField⟦X⟧ →+* equalCharacteristicLubinTateTruncatedRing F n :=
  Ideal.Quotient.mk
    (Ideal.span ({PowerSeries.X ^ (n + 1)} : Set F.residueField⟦X⟧))

/-- Two truncated classes agree exactly when their difference is divisible by `X ^ (n + 1)`. -/
@[simp]
theorem equalCharacteristicLubinTateTruncatedRingMk_eq_iff
    (F : LocalField.{u, v} K) (n : ℕ) (a b : F.residueField⟦X⟧) :
    equalCharacteristicLubinTateTruncatedRingMk F n a =
        equalCharacteristicLubinTateTruncatedRingMk F n b ↔
      a - b ∈
        Ideal.span ({PowerSeries.X ^ (n + 1)} : Set F.residueField⟦X⟧) := by
  change
    Ideal.Quotient.mk
        (Ideal.span ({PowerSeries.X ^ (n + 1)} : Set F.residueField⟦X⟧)) a =
      Ideal.Quotient.mk
        (Ideal.span ({PowerSeries.X ^ (n + 1)} : Set F.residueField⟦X⟧)) b ↔ _
  exact Ideal.Quotient.mk_eq_mk_iff_sub_mem
    (I := Ideal.span
      ({PowerSeries.X ^ (n + 1)} : Set F.residueField⟦X⟧)) a b

/-- Every named truncated coefficient has a power-series representative. -/
theorem equalCharacteristicLubinTateTruncatedRingMk_surjective
    (F : LocalField.{u, v} K) (n : ℕ) :
    Function.Surjective (equalCharacteristicLubinTateTruncatedRingMk F n) := by
  change Function.Surjective
    (Ideal.Quotient.mk
      (Ideal.span ({PowerSeries.X ^ (n + 1)} : Set F.residueField⟦X⟧)))
  exact Ideal.Quotient.mk_surjective

/-- Eliminate two truncated coefficients simultaneously through canonical
representatives. -/
theorem equalCharacteristicLubinTateTruncatedRing_inductionOn₂
    (F : LocalField.{u, v} K) (n : ℕ)
    {motive : equalCharacteristicLubinTateTruncatedRing F n →
      equalCharacteristicLubinTateTruncatedRing F n → Prop}
    (q r : equalCharacteristicLubinTateTruncatedRing F n)
    (mk : ∀ a b : F.residueField⟦X⟧,
      motive (equalCharacteristicLubinTateTruncatedRingMk F n a)
        (equalCharacteristicLubinTateTruncatedRingMk F n b)) :
    motive q r := by
  exact Quotient.inductionOn₂' q r mk

/-- Descend a ring homomorphism through the named truncated coefficient
ring. -/
def equalCharacteristicLubinTateTruncatedRingLift
    {S : Type*} [Semiring S]
    (F : LocalField.{u, v} K) (n : ℕ)
    (f : F.residueField⟦X⟧ →+* S)
    (hf : ∀ a ∈
      Ideal.span ({PowerSeries.X ^ (n + 1)} : Set F.residueField⟦X⟧),
      f a = 0) :
    equalCharacteristicLubinTateTruncatedRing F n →+* S :=
  (Ideal.Quotient.lift
    (Ideal.span ({PowerSeries.X ^ (n + 1)} : Set F.residueField⟦X⟧))
    f hf).comp
      (equalCharacteristicLubinTateTruncatedRingEquiv F n).toRingHom

/-- A descended homomorphism evaluates a truncated representative by the original map. -/
@[simp]
theorem equalCharacteristicLubinTateTruncatedRingLift_mk
    {S : Type*} [Semiring S]
    (F : LocalField.{u, v} K) (n : ℕ)
    (f : F.residueField⟦X⟧ →+* S)
    (hf : ∀ a ∈
      Ideal.span ({PowerSeries.X ^ (n + 1)} : Set F.residueField⟦X⟧),
      f a = 0) (a : F.residueField⟦X⟧) :
    equalCharacteristicLubinTateTruncatedRingLift F n f hf
        (equalCharacteristicLubinTateTruncatedRingMk F n a) = f a :=
  rfl

/-- The canonical scalar multiplication of the truncated coefficient ring on
itself, named to prevent typeclass search from unfolding the quotient. -/
noncomputable local instance equalCharacteristicLubinTateTruncatedSelfSMul
    (F : LocalField.{u, v} K) (n : ℕ) :
    SMul (equalCharacteristicLubinTateTruncatedRing F n)
      (equalCharacteristicLubinTateTruncatedRing F n) where
  smul := (· * ·)

/-- The truncated Lubin–Tate coefficient ring acts on itself by multiplication. -/
noncomputable local instance equalCharacteristicLubinTateTruncatedSelfModule
    (F : LocalField.{u, v} K) (n : ℕ) :
    Module (equalCharacteristicLubinTateTruncatedRing F n)
      (equalCharacteristicLubinTateTruncatedRing F n) :=
  Semiring.toModule

/-- Genuine Lubin--Tate brackets give a ring action of the full power-series
ring on level `n + 1` torsion. -/
noncomputable def equalCharacteristicLubinTateTorsionEndRingHom
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    F.residueField⟦X⟧ →+*
      AddMonoid.End
        (equalCharacteristicLubinTateAmbientTorsionAddSubgroup F
          (equalCharacteristicSeparableUniformizer F) (n + 1)) where
  toFun a := equalCharacteristicLubinTateAmbientTorsionEnd F
    (equalCharacteristicSeparableCoefficientHom F)
    (equalCharacteristicSeparableUniformizer F) (n + 1) a
  map_zero' := by
    apply AddMonoidHom.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f : AddMonoid.End
        (SeparableClosure F.residueField⸨X⸩) =>
      f x.1) (equalCharacteristicLubinTateAmbientBracket_zero F
        (equalCharacteristicSeparableCoefficientHom F)
        (equalCharacteristicSeparableUniformizer F) (n + 1))
  map_one' := by
    apply AddMonoidHom.ext
    intro x
    apply Subtype.ext
    exact equalCharacteristicLubinTateAmbientBracket_one_apply_of_torsion F
      (equalCharacteristicSeparableCoefficientHom F)
      (equalCharacteristicSeparableUniformizer F) (n + 1) x.1 x.2
  map_add' a b := by
    apply AddMonoidHom.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f : AddMonoid.End
        (SeparableClosure F.residueField⸨X⸩) => f x.1)
      (equalCharacteristicLubinTateAmbientBracket_add F
        (equalCharacteristicSeparableCoefficientHom F)
        (equalCharacteristicSeparableUniformizer F) (n + 1) a b)
  map_mul' a b := by
    apply AddMonoidHom.ext
    intro x
    apply Subtype.ext
    exact equalCharacteristicLubinTateAmbientBracket_mul_apply_of_torsion F
      (equalCharacteristicSeparableCoefficientHom F)
      (equalCharacteristicSeparableUniformizer F) (n + 1) a b x.1 x.2

/-- `T^(n+1)` acts trivially on division-level `n + 1` division points. -/
theorem equalCharacteristicLubinTateTruncationIdeal_le_ker
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    Ideal.span ({PowerSeries.X ^ (n + 1)} : Set F.residueField⟦X⟧) ≤
      RingHom.ker (equalCharacteristicLubinTateTorsionEndRingHom F n) := by
  rw [Ideal.span_le]
  intro a ha
  rw [Set.mem_singleton_iff.mp ha]
  change equalCharacteristicLubinTateTorsionEndRingHom F n
      (PowerSeries.X ^ (n + 1)) = 0
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  change equalCharacteristicLubinTateAmbientBracket F
      (equalCharacteristicSeparableCoefficientHom F)
      (equalCharacteristicSeparableUniformizer F) (n + 1)
      (PowerSeries.X ^ (n + 1)) x.1 = 0
  rw [equalCharacteristicLubinTateAmbientBracket_apply]
  apply Finset.sum_eq_zero
  intro i hi
  rw [PowerSeries.coeff_X_pow,
    ite_eq_right (ne_of_lt (Finset.mem_range.mp hi)), map_zero, zero_mul]

/-- The resulting action of the actual quotient
`κ⟦T⟧/(T^(n+1))`. -/
noncomputable def equalCharacteristicLubinTateTruncatedScalarHom
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    equalCharacteristicLubinTateTruncatedRing F n →+*
      AddMonoid.End
        (equalCharacteristicLubinTateAmbientTorsionAddSubgroup F
          (equalCharacteristicSeparableUniformizer F) (n + 1)) :=
  equalCharacteristicLubinTateTruncatedRingLift F n
    (equalCharacteristicLubinTateTorsionEndRingHom F n)
    fun _ ha => RingHom.mem_ker.mp
      (equalCharacteristicLubinTateTruncationIdeal_le_ker F n ha)

/-- The quotient-ring scalar action underlying the truncated torsion module. -/
noncomputable instance equalCharacteristicLubinTateTruncatedSMul
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    SMul (equalCharacteristicLubinTateTruncatedRing F n)
      (equalCharacteristicLubinTateAmbientTorsionAddSubgroup F
        (equalCharacteristicSeparableUniformizer F) (n + 1)) :=
  SMul.comp
    (equalCharacteristicLubinTateAmbientTorsionAddSubgroup F
      (equalCharacteristicSeparableUniformizer F) (n + 1))
    (equalCharacteristicLubinTateTruncatedScalarHom F n)

/-- The canonical `κ⟦T⟧/(T^(n+1))`-module structure on division-level `n + 1`
division points. -/
noncomputable instance equalCharacteristicLubinTateTruncatedModule
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    Module (equalCharacteristicLubinTateTruncatedRing F n)
      (equalCharacteristicLubinTateAmbientTorsionAddSubgroup F
        (equalCharacteristicSeparableUniformizer F) (n + 1)) :=
  Module.compHom _ (equalCharacteristicLubinTateTruncatedScalarHom F n)

/-- The chosen primitive root, regarded as a division-level `n + 1` division
point. -/
noncomputable def equalCharacteristicLubinTatePrimitiveTorsionPoint
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    equalCharacteristicLubinTateAmbientTorsionAddSubgroup F
      (equalCharacteristicSeparableUniformizer F) (n + 1) :=
  ⟨chosenEqualCharacteristicLubinTatePrimitiveRoot F n,
    chosenEqualCharacteristicLubinTatePrimitiveRoot_torsion F n⟩

/-- Evaluation at the primitive point is linear for the quotient-ring
action. -/
noncomputable def equalCharacteristicLubinTatePrimitiveEvaluation
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    equalCharacteristicLubinTateTruncatedRing F n →ₗ[
      equalCharacteristicLubinTateTruncatedRing F n]
      equalCharacteristicLubinTateAmbientTorsionAddSubgroup F
        (equalCharacteristicSeparableUniformizer F) (n + 1) :=
  LinearMap.toSpanSingleton
    (equalCharacteristicLubinTateTruncatedRing F n)
    (equalCharacteristicLubinTateAmbientTorsionAddSubgroup F
      (equalCharacteristicSeparableUniformizer F) (n + 1))
    (equalCharacteristicLubinTatePrimitiveTorsionPoint F n)

/-- Primitive evaluation of a truncated class is bracket evaluation of its representative. -/
@[simp]
theorem equalCharacteristicLubinTatePrimitiveEvaluation_mk
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧) :
    equalCharacteristicLubinTatePrimitiveEvaluation F n
        (equalCharacteristicLubinTateTruncatedRingMk F n a) =
      equalCharacteristicLubinTateAmbientTorsionEnd F
        (equalCharacteristicSeparableCoefficientHom F)
        (equalCharacteristicSeparableUniformizer F) (n + 1) a
        (equalCharacteristicLubinTatePrimitiveTorsionPoint F n) := by
  rfl

/-- Evaluation at the primitive torsion point is injective on truncated coefficients. -/
theorem equalCharacteristicLubinTatePrimitiveEvaluation_injective
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    Function.Injective
      (equalCharacteristicLubinTatePrimitiveEvaluation F n) := by
  intro q r hqr
  revert hqr
  refine equalCharacteristicLubinTateTruncatedRing_inductionOn₂ F n
    (motive := fun q r =>
      equalCharacteristicLubinTatePrimitiveEvaluation F n q =
        equalCharacteristicLubinTatePrimitiveEvaluation F n r → q = r)
    q r ?_
  intro a b hab
  change equalCharacteristicLubinTatePrimitiveEvaluation F n
      (equalCharacteristicLubinTateTruncatedRingMk F n a) =
    equalCharacteristicLubinTatePrimitiveEvaluation F n
      (equalCharacteristicLubinTateTruncatedRingMk F n b) at hab
  rw [equalCharacteristicLubinTatePrimitiveEvaluation_mk,
    equalCharacteristicLubinTatePrimitiveEvaluation_mk] at hab
  apply (equalCharacteristicLubinTateTruncatedRingMk_eq_iff F n a b).2
  rw [Ideal.mem_span_singleton]
  apply PowerSeries.X_pow_dvd_iff.mpr
  intro i hi
  have hvalue :
      equalCharacteristicLubinTateAmbientBracket F
          (equalCharacteristicSeparableCoefficientHom F)
          (equalCharacteristicSeparableUniformizer F) (n + 1) a
          (chosenEqualCharacteristicLubinTatePrimitiveRoot F n) =
        equalCharacteristicLubinTateAmbientBracket F
          (equalCharacteristicSeparableCoefficientHom F)
          (equalCharacteristicSeparableUniformizer F) (n + 1) b
          (chosenEqualCharacteristicLubinTatePrimitiveRoot F n) := by
    exact congrArg Subtype.val hab
  have hcoeff :=
    chosenEqualCharacteristicLubinTatePrimitiveRoot_bracket_eq_coeff F n a b
      hvalue i (Nat.le_of_lt_succ hi)
  calc
    PowerSeries.coeff i (a - b) =
        PowerSeries.coeff i a - PowerSeries.coeff i b :=
      (PowerSeries.coeff i).map_sub a b
    _ = 0 := sub_eq_zero.mpr hcoeff

/-- Every ambient torsion point is obtained by primitive evaluation. -/
theorem equalCharacteristicLubinTatePrimitiveEvaluation_surjective
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    Function.Surjective
      (equalCharacteristicLubinTatePrimitiveEvaluation F n) := by
  intro x
  obtain ⟨a, ha⟩ :=
    (equalCharacteristicLubinTateParameterRoot_bijective F n).surjective x
  refine ⟨equalCharacteristicLubinTateTruncatedRingMk F n
      (equalCharacteristicLubinTateParameterSeries F n a), ?_⟩
  rw [equalCharacteristicLubinTatePrimitiveEvaluation_mk]
  calc
    equalCharacteristicLubinTateAmbientTorsionEnd F
        (equalCharacteristicSeparableCoefficientHom F)
        (equalCharacteristicSeparableUniformizer F) (n + 1)
        (equalCharacteristicLubinTateParameterSeries F n a)
        (equalCharacteristicLubinTatePrimitiveTorsionPoint F n) =
      equalCharacteristicLubinTateParameterRoot F n a := by
        rfl
    _ = x := ha

/-- The public the primitive-division-module equivalence equivalence: at positive division level
`n + 1`,
evaluation at a primitive division point identifies `κ⟦T⟧/(T^(n+1))`
with the entire division module. -/
noncomputable def equalCharacteristicLubinTateFreeRankOneEquiv
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    equalCharacteristicLubinTateTruncatedRing F n ≃ₗ[
      equalCharacteristicLubinTateTruncatedRing F n]
      equalCharacteristicLubinTateAmbientTorsionAddSubgroup F
        (equalCharacteristicSeparableUniformizer F) (n + 1) :=
  LinearEquiv.ofBijective
    (equalCharacteristicLubinTatePrimitiveEvaluation F n)
    ⟨equalCharacteristicLubinTatePrimitiveEvaluation_injective F n,
      equalCharacteristicLubinTatePrimitiveEvaluation_surjective F n⟩

/-- The free rank-one equivalence sends one to the primitive torsion point. -/
@[simp]
theorem equalCharacteristicLubinTateFreeRankOneEquiv_apply_one
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    equalCharacteristicLubinTateFreeRankOneEquiv F n 1 =
      equalCharacteristicLubinTatePrimitiveTorsionPoint F n := by
  change (1 : equalCharacteristicLubinTateTruncatedRing F n) •
      equalCharacteristicLubinTatePrimitiveTorsionPoint F n =
    equalCharacteristicLubinTatePrimitiveTorsionPoint F n
  exact one_smul _ _

/-- In particular the division module of the primitive-division-module equivalence is genuinely
free.  The
displayed linear equivalence above supplies its one-element basis. -/
noncomputable instance equalCharacteristicLubinTateDivisionModuleFree
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    Module.Free (equalCharacteristicLubinTateTruncatedRing F n)
      (equalCharacteristicLubinTateAmbientTorsionAddSubgroup F
        (equalCharacteristicSeparableUniformizer F) (n + 1)) :=
  Module.Free.of_equiv'
    (Module.Free.self (equalCharacteristicLubinTateTruncatedRing F n))
    (equalCharacteristicLubinTateFreeRankOneEquiv F n)

end EqualCharacteristic
end LubinTate
