/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalFieldTheory.Padic.Cyclotomic.Unramified.CanonicalExtension
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.InertiaRamificationCard
public import LeanPool.ClassFieldTheory.ClassFieldTheory.RamificationTheory.HilbertRamification.PadicCyclotomicRamificationIndexBound
public import LeanPool.ClassFieldTheory.ClassFieldTheory.RamificationTheory.RamificationIndexComparison
/-!
# Canonical p-adic inertia bounds

This file identifies the inertia cardinality of the canonical valuation on a
finite Galois extension of `ℚ_p` with the intrinsic value-group ramification
index, then applies the prime-power cyclotomic ramification bound.
-/

@[expose] public section

open _root_.RamificationTheory.HilbertRamification.CompleteDVF renaming
  natCard_decompositionInertiaSubgroup_eq_ramificationIndex →
    natCard_decompositionInertiaSubgroup_eq_ramificationIndex

open _root_.ValuationTheory.DiscreteValuationField.ValuedExtension renaming
  exists_integralClosure_standard_fundamental_identity →
    exists_integralClosure_standard_fundamental_identity

open _root_.ValuationTheory.DiscreteValuationField.ValuedExtension renaming
  moduleFinite_target_valuationSubring_of_finite_separable →
    moduleFinite_target_valuationSubring_of_finite_separable

open _root_.ValuationTheory.DiscreteValuationField.ValuedExtension renaming
  residueField_finiteDimensional_of_moduleFinite →
    residueField_finiteDimensional_of_moduleFinite


noncomputable
section

namespace HilbertRamification

open AlgebraicNumberTheory.Valuations

attribute [local instance] Ideal.Quotient.field

/-- For a finite Galois extension of `ℚ_p`, the inertia group of the
canonical norm-formula valuation has cardinality equal to the intrinsic ramification index. -/
theorem natCard_padicCanonicalInertia_eq_exponentialRamificationIndex
    (p : ℕ) [Fact p.Prime]
    (E : Type) [Field E] [Algebra ℚ_[p] E]
    [FiniteDimensional ℚ_[p] E] [IsGalois ℚ_[p] E] :
    Nat.card
        (RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup ℚ_[p]
          (absoluteValueValuationSubring
            (padicFiniteExtensionAbsoluteValue p E)
            (padicFiniteExtensionAbsoluteValue_nonarchimedean p E))) =
      exponentialRamificationIndex
        (padicFieldExponentialValuation p)
        (padicFiniteExtensionExponentialValuation p E) := by
  let base := LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF p
  obtain ⟨target, hExt, hTarget, _hFundamental⟩ :=
    exists_integralClosure_standard_fundamental_identity
      (K := ℚ_[p]) (L := E) base
  let : base.valuation.HasExtension target.valuation := hExt
  let : IsIntegralClosure target.valuationSubring base.valuationSubring E := hTarget
  let : IsScalarTower base.valuationSubring target.valuationSubring E := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  let : Module.Finite base.valuationSubring target.valuationSubring :=
    moduleFinite_target_valuationSubring_of_finite_separable
      base target
  let : FiniteDimensional
      (base.valuationSubring ⧸ base.maximalIdeal)
      (target.valuationSubring ⧸ target.maximalIdeal) :=
    residueField_finiteDimensional_of_moduleFinite
      base target
  let : Algebra.IsAlgebraic
      (base.valuationSubring ⧸ base.maximalIdeal)
      (target.valuationSubring ⧸ target.maximalIdeal) :=
    Algebra.IsAlgebraic.of_finite
      (base.valuationSubring ⧸ base.maximalIdeal)
      (target.valuationSubring ⧸ target.maximalIdeal)
  let : Finite (base.valuationSubring ⧸ base.maximalIdeal) := by
    change Finite base.residueField
    simpa only [base] using
      LocalFieldTheory.DiscreteValuationField.Examples.Qp.padicCompleteDVF_residueField_finite p
  let : PerfectField (base.valuationSubring ⧸ base.maximalIdeal) :=
    PerfectField.ofFinite
  let : Algebra.IsSeparable
      (base.valuationSubring ⧸ base.maximalIdeal)
      (target.valuationSubring ⧸ target.maximalIdeal) := by
    exact Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hCard :=
    natCard_decompositionInertiaSubgroup_eq_ramificationIndex
      (K := ℚ_[p]) (L := E) base target
  have hAssociated :
      LubinTate.Valuations.exponentialValuationSubringAsValuationSubring
          (padicFiniteExtensionExponentialValuation p E) =
        absoluteValueValuationSubring
          (padicFiniteExtensionAbsoluteValue p E)
          (padicFiniteExtensionAbsoluteValue_nonarchimedean p E) :=
    associatedAbsoluteValue_valuationSubring_eq
      (padicFiniteExtensionExponentialValuation p E)
      (Real.exp 1)
      (padicFiniteExtensionAbsoluteValue p E)
      (padicFiniteExtensionAbsoluteValue_nonarchimedean p E)
      (absoluteValueExponentialValuation_associated
        (padicFiniteExtensionAbsoluteValue p E)
        (padicFiniteExtensionAbsoluteValue_nonarchimedean p E))
  have hCanonical :=
    padicFiniteExtensionExponentialValuationSubring_eq_completeDVF
      p E target
  have hInertiaCardinality :=
    RamificationTheory.exponentialRamificationIndex_eq_ramificationIndex_of_valuationSubrings_eq
      (base := base) (target := target)
      (padicFieldExponentialValuation p)
      (padicFiniteExtensionExponentialValuation p E)
      (padicFiniteExtensionExponentialValuation_extends p E)
      (padicFieldExponentialValuationSubring_eq_completeDVF p)
      hCanonical
  have hAbsolute :
      absoluteValueValuationSubring
          (padicFiniteExtensionAbsoluteValue p E)
          (padicFiniteExtensionAbsoluteValue_nonarchimedean p E) =
        target.valuation.valuationSubring :=
    hAssociated.symm.trans hCanonical
  calc
    Nat.card
        (RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup ℚ_[p]
          (absoluteValueValuationSubring
            (padicFiniteExtensionAbsoluteValue p E)
            (padicFiniteExtensionAbsoluteValue_nonarchimedean p E))) =
        Nat.card (target.valuation.valuationSubring.inertiaSubgroup ℚ_[p]) := by
      rw [hAbsolute]
    _ = ValuationTheory.DiscreteValuationField.ValuedExtension.ramificationIndex
        base.toDVF target.toDVF := hCard
    _ = exponentialRamificationIndex
        (padicFieldExponentialValuation p)
        (padicFiniteExtensionExponentialValuation p E) := hInertiaCardinality.symm

/-- A cyclotomic embedding into order `r * p ^ n`, with `r` prime to `p`,
bounds the canonical inertia cardinality by `φ(p ^ n)`. -/
theorem natCard_padicCanonicalInertia_le_totient_primePow_of_coprimeEmbedding
    (p r n : ℕ) [Fact p.Prime] (hpr : p.Coprime r)
    (E : Type) [Field E] [Algebra ℚ_[p] E]
    [FiniteDimensional ℚ_[p] E] [IsGalois ℚ_[p] E]
    (i : E →ₐ[ℚ_[p]] CyclotomicField (r * p ^ n) ℚ_[p]) :
    Nat.card
        (RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup ℚ_[p]
          (absoluteValueValuationSubring
            (padicFiniteExtensionAbsoluteValue p E)
            (padicFiniteExtensionAbsoluteValue_nonarchimedean p E))) ≤
      Nat.totient (p ^ n) := by
  have hr : 0 < r := by
    exact Nat.pos_of_ne_zero (fun hr0 =>
      (Fact.out : Nat.Prime p).ne_one
        ((Nat.coprime_zero_right p).mp (hr0 ▸ hpr)))
  have hpPow : 0 < p ^ n := pow_pos (Fact.out : Nat.Prime p).pos n
  let : NeZero (r * p ^ n) := ⟨(mul_pos hr hpPow).ne'⟩
  let hDcyclo : IsCyclotomicExtension {r * p ^ n} ℚ_[p]
      (CyclotomicField (r * p ^ n) ℚ_[p]) :=
    CyclotomicField.isCyclotomicExtension (r * p ^ n) ℚ_[p]
  let : FiniteDimensional ℚ_[p]
      (CyclotomicField (r * p ^ n) ℚ_[p]) :=
    IsCyclotomicExtension.finiteDimensional {r * p ^ n} ℚ_[p]
      (CyclotomicField (r * p ^ n) ℚ_[p])
  calc
    Nat.card
        (RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup ℚ_[p]
          (absoluteValueValuationSubring
            (padicFiniteExtensionAbsoluteValue p E)
            (padicFiniteExtensionAbsoluteValue_nonarchimedean p E))) =
        exponentialRamificationIndex
          (padicFieldExponentialValuation p)
          (padicFiniteExtensionExponentialValuation p E) :=
      natCard_padicCanonicalInertia_eq_exponentialRamificationIndex p E
    _ ≤ exponentialRamificationIndex
          (padicFieldExponentialValuation p)
          (padicFiniteExtensionExponentialValuation p
            (CyclotomicField (r * p ^ n) ℚ_[p])) :=
      padicFiniteExtension_exponentialRamificationIndex_le_of_algHom p i
    _ ≤ Nat.totient (p ^ n) := by
      simpa using
        coprimeLocalCyclotomic_exponentialRamificationIndex_le_totient_primePow
          p r n hpr

end HilbertRamification

end
