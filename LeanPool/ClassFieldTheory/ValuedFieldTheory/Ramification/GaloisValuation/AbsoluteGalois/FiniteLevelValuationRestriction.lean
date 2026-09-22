/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.Complete
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.Core
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.Factorization.AdicLimits
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.Factorization.Assembly
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.Factorization.Basic
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.Factorization.CoefficientMinimum
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.Factorization.Complete
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.Factorization.DegreeBounds
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.Factorization.DivisionBounds
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.Factorization.ErrorPowers
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.Factorization.FiniteApproximation
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.Factorization.InfiniteApproximation
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.Factorization.Iteration
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.Factorization.PrincipalLimits
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.Factorization.Step
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.Factorization.Truncation
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.Factorization.WeakLimits
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.IrreduciblePolynomialBounds
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.IrreduciblePolynomialLifting
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.MonicFactorization
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.NonmonicReduction
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.PrimitiveFactorization
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.PrimitiveReduction
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.UniqueAlgebraicExtensions
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.UniqueExtensionPrimitive
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.UniqueExtensionReduction
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.ValuationExtensionCriterion
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.GaloisValuation.Ramification
import Mathlib.Algebra.Exact.Basic
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Sets.Opens

/-! # Finite Level Valuation Restriction -/
namespace RamificationTheory

open ValuationTheory
open ValuationTheory.DiscreteValuationField.HenselianDVF

/-!
# Finite-level valuation restriction for absolute Galois arguments

This file isolates the valuation-restriction and separable-power lemmas
used to pass from absolute Galois questions to finite intermediate fields.
-/

noncomputable section

universe u v w z

namespace ValuationSubring

variable {K : Type u} [Field K] (A : ValuationSubring K)

/-- Membership in a valuation subring is detected by any positive natural
power.

This is useful in absolute arguments: after moving an element into a finite
separable level only after taking a positive power, valuation-subring
membership can be pulled back to the original element. -/
theorem mem_iff_pow_mem (x : K) {n : ℕ} (hn : 0 < n) :
    x ∈ A ↔ x ^ n ∈ A := by
  constructor
  · intro hx
    exact A.toSubring.pow_mem hx n
  · intro hxpow
    induction n with
    | zero =>
        cases hn
    | succ n ih =>
        by_cases hn0 : n = 0
        · simpa [hn0] using hxpow
        · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
          by_cases hx0 : x = 0
          · simp [hx0]
          rcases A.mem_or_inv_mem x with hx | hxinv
          · exact hx
          · have hxpred : x ^ n ∈ A := by
              have hmul : x ^ (n + 1) * x⁻¹ ∈ A :=
                A.mul_mem _ _ hxpow hxinv
              have hpow : x ^ (n + 1) * x⁻¹ = x ^ n := by
                rw [pow_succ, mul_assoc, mul_inv_cancel₀, mul_one]
                exact hx0
              simpa [hpow] using hmul
            exact ih hnpos hxpred

/-- States the theorem `mem_of_pow_mem`. -/
theorem mem_of_pow_mem (x : K) {n : ℕ} (hn : 0 < n) (hx : x ^ n ∈ A) :
    x ∈ A :=
  (mem_iff_pow_mem A x hn).2 hx

/-- States the theorem `pow_mem_iff_mem`. -/
theorem pow_mem_iff_mem (x : K) {n : ℕ} (hn : 0 < n) :
    x ^ n ∈ A ↔ x ∈ A :=
  (mem_iff_pow_mem A x hn).symm

section RestrictIntermediateField

variable {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]

/-- Restrict a valuation subring of an ambient field to an intermediate field. -/
def restrictIntermediateField
    (A : ValuationSubring Ω) (E : IntermediateField K Ω) :
    ValuationSubring E :=
  A.comap (algebraMap E Ω)

/-- States the theorem `restrictIntermediateField_eq_comap`. -/
@[simp] theorem restrictIntermediateField_eq_comap
    (A : ValuationSubring Ω) (E : IntermediateField K Ω) :
    (restrictIntermediateField A E) = A.comap (algebraMap E Ω) :=
  rfl

/-- States the theorem `mem_restrictIntermediateField_iff`. -/
theorem mem_restrictIntermediateField_iff
    (A : ValuationSubring Ω) (E : IntermediateField K Ω) (x : E) :
    x ∈ (restrictIntermediateField A E) ↔ (x : Ω) ∈ A :=
  Iff.rfl

/-- States the theorem `restrictIntermediateField_hasExtension`. -/
theorem restrictIntermediateField_hasExtension
    {Γ : Type w} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (A : ValuationSubring Ω)
    [_root_.Valuation.HasExtension v A.valuation]
    (E : IntermediateField K Ω) :
    _root_.Valuation.HasExtension v ((restrictIntermediateField A E)).valuation := by
  apply _root_.Valuation.HasExtension.ofComapInteger
  ext x
  simp only [Subring.mem_comap, Valuation.mem_integer_iff,
    ValuationSubring.valuation_le_one_iff,
    mem_restrictIntermediateField_iff]
  change algebraMap E Ω (algebraMap K E x) ∈ A ↔ v x ≤ 1
  rw [← IsScalarTower.algebraMap_apply K E Ω x]
  rw [← A.valuation_le_one_iff (algebraMap K Ω x)]
  exact _root_.Valuation.HasExtension.val_map_le_one_iff
    (vR := v) (vA := A.valuation) x

open scoped Pointwise

/-- Membership in the inverse translate is the same as membership after
applying the automorphism. -/
theorem mem_inv_smul_iff_apply_mem
    (A : ValuationSubring Ω) (σ : Ω ≃ₐ[K] Ω) (z : Ω) :
    z ∈ σ⁻¹ • A ↔ σ z ∈ A := by
  simpa [AlgEquiv.smul_def] using
    (ValuationSubring.mem_inv_pointwise_smul_iff
      (g := σ) (S := A) (x := z))

/-- Membership in an automorphic translate is membership after applying the
inverse automorphism. -/
theorem mem_smul_valuationSubring_iff
    (A : ValuationSubring Ω) (σ : Ω ≃ₐ[K] Ω) (z : Ω) :
    z ∈ σ • A ↔ σ⁻¹ z ∈ A := by
  simpa [AlgEquiv.smul_def] using
    (ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem
      (g := σ) (S := A) (x := z))

/-- A `K`-algebra automorphic translate of an extension valuation subring is
again an extension of the base valuation. -/
theorem smul_hasExtension
    {Γ : Type w} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (A : ValuationSubring Ω)
    [_root_.Valuation.HasExtension v A.valuation]
    (σ : Ω ≃ₐ[K] Ω) :
    _root_.Valuation.HasExtension v (σ • A).valuation := by
  apply _root_.Valuation.HasExtension.ofComapInteger
  ext x
  simp only [ValuationSubring.integer_valuation, ValuationSubring.pointwise_smul_toSubring,
    Subring.mem_comap, Valuation.mem_integer_iff]
  rw [Subring.mem_pointwise_smul_iff_inv_smul_mem]
  have hcomm : (σ⁻¹) (algebraMap K Ω x) = algebraMap K Ω x :=
    (σ⁻¹).commutes x
  change (σ⁻¹) (algebraMap K Ω x) ∈ A.toSubring ↔ v x ≤ 1
  rw [hcomm]
  change (algebraMap K Ω x) ∈ A ↔ v x ≤ 1
  rw [← A.valuation_le_one_iff (algebraMap K Ω x)]
  exact _root_.Valuation.HasExtension.val_map_le_one_iff
    (vR := v) (vA := A.valuation) x

/-- Restricting an automorphic translate to an intermediate field preserves
the extension property over the base valuation. -/
theorem restrictIntermediateField_smul_hasExtension
    {Γ : Type w} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (A : ValuationSubring Ω)
    [_root_.Valuation.HasExtension v A.valuation]
    (σ : Ω ≃ₐ[K] Ω) (E : IntermediateField K Ω) :
    _root_.Valuation.HasExtension v ((restrictIntermediateField (σ • A) E)).valuation := by
  have hσ : _root_.Valuation.HasExtension v (σ • A).valuation :=
    smul_hasExtension v A σ
  exact restrictIntermediateField_hasExtension
    (v := v) (A := σ • A) E

/-- The inverse translate used in absolute Galois stabilization also restricts
to an extension of the base valuation. -/
theorem restrictIntermediateField_inv_smul_hasExtension
    {Γ : Type w} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (A : ValuationSubring Ω)
    [_root_.Valuation.HasExtension v A.valuation]
    (σ : Ω ≃ₐ[K] Ω) (E : IntermediateField K Ω) :
    _root_.Valuation.HasExtension v ((restrictIntermediateField (σ⁻¹ • A) E)).valuation :=
  restrictIntermediateField_smul_hasExtension v A σ⁻¹ E

/-- Under finite-level uniqueness, the restriction of `A` is equal to the
restriction of its inverse automorphic translate. -/
theorem restrictIntermediateField_eq_inv_smul_restrictIntermediateField_of_unique
    {Γ : Type w} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (A : ValuationSubring Ω)
    [_root_.Valuation.HasExtension v A.valuation]
    (E : IntermediateField K Ω)
    (huniq :
      ∀ (B : ValuationSubring E)
        [_root_.Valuation.HasExtension v B.valuation],
          (restrictIntermediateField A E) = B)
    (σ : Ω ≃ₐ[K] Ω) :
    (restrictIntermediateField A E) = (restrictIntermediateField (σ⁻¹ • A) E) := by
  have hC : _root_.Valuation.HasExtension v
      ((restrictIntermediateField (σ⁻¹ • A) E)).valuation :=
    restrictIntermediateField_inv_smul_hasExtension v A σ E
  exact huniq ((restrictIntermediateField (σ⁻¹ • A) E))

/-- If the restricted valuation on a finite level is the unique extension of
the base valuation, then every ambient `K`-automorphism preserves membership
in the ambient valuation subring on that level. -/
theorem mem_algEquiv_apply_iff_of_restrictIntermediateField_unique
    {Γ : Type w} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (A : ValuationSubring Ω)
    [_root_.Valuation.HasExtension v A.valuation]
    (E : IntermediateField K Ω)
    (huniq :
      ∀ (B : ValuationSubring E)
        [_root_.Valuation.HasExtension v B.valuation],
          (restrictIntermediateField A E) = B)
    (σ : Ω ≃ₐ[K] Ω) (x : E) :
    ((x : Ω) ∈ A) ↔ σ (x : Ω) ∈ A := by
  let B : ValuationSubring E := (restrictIntermediateField A E)
  let C : ValuationSubring E := (restrictIntermediateField (σ⁻¹ • A) E)
  have hBC : B = C := by
    simpa [B, C] using
      restrictIntermediateField_eq_inv_smul_restrictIntermediateField_of_unique
        v A E huniq σ
  constructor
  · intro hx
    have hxB : x ∈ B := by
      simpa [B] using hx
    have hxC : x ∈ C := by
      simpa [hBC] using hxB
    have hxInv : (x : Ω) ∈ σ⁻¹ • A := by
      simpa [C] using hxC
    exact (mem_inv_smul_iff_apply_mem A σ (x : Ω)).1 hxInv
  · intro hxσ
    have hxInv : (x : Ω) ∈ σ⁻¹ • A := by
      exact (mem_inv_smul_iff_apply_mem A σ (x : Ω)).2 hxσ
    have hxC : x ∈ C := by
      simpa [C] using hxInv
    have hxB : x ∈ B := by
      simpa [hBC] using hxC
    simpa [B] using hxB

/-- A Henselian-DVF unique-extension package on the finite level supplies the
membership preservation core needed for the absolute power route. -/
theorem mem_algEquiv_apply_iff_of_restrictIntermediateField_henselianUnique
    (base : ValuationTheory.DiscreteValuationField.HenselianDVF.{u, w} K)
    (A : ValuationSubring Ω)
    [_root_.Valuation.HasExtension base.valuation A.valuation]
    (E : IntermediateField K Ω)
    (target : ValuationTheory.DiscreteValuationField.HenselianDVF.{v, z} E)
    (hA : target.valuation.valuationSubring = (restrictIntermediateField A E))
    (huniq :
      HasUniqueValuationExtension.{u, w, v, z, v}
        base target)
    (σ : Ω ≃ₐ[K] Ω) (x : E) :
    ((x : Ω) ∈ A) ↔ σ (x : Ω) ∈ A := by
  refine
    mem_algEquiv_apply_iff_of_restrictIntermediateField_unique
      base.valuation A E ?_ σ x
  intro B hB
  have htarget :
      target.valuation.valuationSubring = B := by
    have hsub :=
      valuationSubring_eq_of_hasUniqueValuationExtension
          base target huniq B.valuation
    simpa [ValuationSubring.valuationSubring_valuation] using hsub
  exact hA.symm.trans htarget

end RestrictIntermediateField

end ValuationSubring

/-- A power of an algebraic element lies in a finite separable intermediate
field.

This packages the standard reduction through the separable closure: an
algebraic extension is purely inseparable over its separable closure, so a
positive power of the element lands in the separable closure, and adjoining
that power gives the finite separable level. -/
theorem exists_finite_separable_intermediate_pow_mem
    {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (z : Ω) :
    ∃ n : ℕ, ∃ E : IntermediateField K Ω,
      0 < n ∧ FiniteDimensional K E ∧ Algebra.IsSeparable K E ∧ z ^ n ∈ E := by
  let S : IntermediateField K Ω := separableClosure K Ω
  let q : ℕ := ringExpChar S
  have hq : 0 < q := by
    dsimp [q, ringExpChar]
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_right _ _)
  obtain ⟨m, y, hy⟩ := IsPurelyInseparable.pow_mem S q z
  refine ⟨q ^ m, IntermediateField.adjoin K ({z ^ (q ^ m)} : Set Ω),
    pow_pos hq m, ?_, ?_, ?_⟩
  · exact IntermediateField.adjoin.finiteDimensional
      (Algebra.IsIntegral.isIntegral (R := K) (z ^ (q ^ m)))
  · have hmem : z ^ (q ^ m) ∈ separableClosure K Ω := by
      have hmem' : algebraMap S Ω y ∈ separableClosure K Ω := by
        simp [S, y.2]
      simpa [hy] using hmem'
    exact (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable
      (F := K) (E := Ω)).2 (mem_separableClosure_iff.1 hmem)
  · exact IntermediateField.mem_adjoin_simple_self K (z ^ (q ^ m))

/-- A positive power of any algebraic element is separable over the base. -/
theorem exists_pow_isSeparable_of_isAlgebraic
    {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (z : Ω) :
    ∃ n : ℕ, 0 < n ∧ IsSeparable K (z ^ n) := by
  obtain ⟨n, E, hn, _hFin, hSep, hzE⟩ :=
    RamificationTheory.exists_finite_separable_intermediate_pow_mem (K := K) z
  let : Algebra.IsSeparable K E := hSep
  exact ⟨n, hn, (mem_separableClosure_iff).1 ((le_separableClosure K Ω E) hzE)⟩


end

end RamificationTheory
