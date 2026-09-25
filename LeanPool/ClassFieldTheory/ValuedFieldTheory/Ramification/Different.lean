/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Core
public import Mathlib.RingTheory.DedekindDomain.Different
/-!
# Different and codifferent for valued finite extensions

This file specializes mathlib's Dedekind-domain different ideal to complete
DVF valuation rings.  The ideal itself remains mathlib's `differentIdeal`; the
extra API here connects it to the chosen valuation rings, the codifferent, and
the local unramified criterion.
-/

@[expose] public section

noncomputable
section

universe u v w x

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace RamificationTheory
namespace DiscreteValuationField

open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

namespace ValuedExtension

variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L] [FiniteDimensional K L]
variable (base : CompleteDVF.{u, v} K) (target : CompleteDVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]

/-- The codifferent submodule of the valuation ring extension, i.e. the
trace-dual of the target valuation ring. -/
noncomputable def codifferentSubmodule
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    Submodule target.valuationSubring L :=
  Submodule.traceDual base.valuationSubring K
    (1 : Submodule target.valuationSubring L)

omit [FiniteDimensional K L] in
/-- Trace-dual membership written directly as a trace integrality condition. -/
theorem mem_codifferentSubmodule_iff_trace_mul_integral
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    {z : L} :
    z ∈ (RamificationTheory.DiscreteValuationField.ValuedExtension.codifferentSubmodule base
      target) ↔
      ∀ a ∈ (1 : Submodule target.valuationSubring L),
        IsIntegral base.valuationSubring (Algebra.trace K L (z * a)) := by
  change
    z ∈ Submodule.traceDual base.valuationSubring K
        (1 : Submodule target.valuationSubring L) ↔
      ∀ a ∈ (1 : Submodule target.valuationSubring L),
        IsIntegral base.valuationSubring (Algebra.trace K L (z * a))
  rw [Submodule.mem_traceDual_iff_isIntegral]
  simp [Algebra.traceForm_apply]

omit [FiniteDimensional K L] in
/-- The trace-dual operation is antitone.  This is the general filtration
transfer lemma used to move between ideal/submodule levels and trace bounds. -/
theorem traceDual_antitone
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    {I J : Submodule target.valuationSubring L} (hIJ : I ≤ J) :
    Submodule.traceDual base.valuationSubring K J ≤
      Submodule.traceDual base.valuationSubring K I := by
  intro z hz
  rw [Submodule.mem_traceDual] at hz ⊢
  intro a ha
  exact hz a (hIJ ha)

omit [FiniteDimensional K L] in
/-- Elements of the codifferent pair integrally with every integral element
under the trace form. -/
theorem trace_mul_mem_integer_range_of_mem_codifferent
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    {z a : L} (hz : z ∈
      (RamificationTheory.DiscreteValuationField.ValuedExtension.codifferentSubmodule base target))
    (ha : a ∈ (1 : Submodule target.valuationSubring L)) :
    Algebra.trace K L (z * a) ∈
      (algebraMap base.valuationSubring K).range := by
  change
    z ∈ Submodule.traceDual base.valuationSubring K
      (1 : Submodule target.valuationSubring L) at hz
  have htrace := (Submodule.mem_traceDual.mp hz) a ha
  simpa [Algebra.traceForm_apply] using htrace

/-- The different ideal with the torsion-free certificate supplied by finite
separability of complete-DVF extensions. -/
noncomputable def differentIdealOfFiniteSeparable
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    Ideal target.valuationSubring :=
  @differentIdeal base.valuationSubring target.valuationSubring
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (moduleIsTorsionFree_target_valuationSubring_of_finite_separable
      (K := K) (L := L) (base := base) (target := target))

/-- The finite-separable different ideal agrees with mathlib's `differentIdeal`
whenever a torsion-free instance is already in scope. -/
theorem differentIdealOfFiniteSeparable_eq_differentIdeal
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    [Module.IsTorsionFree base.valuationSubring target.valuationSubring] :
    (RamificationTheory.DiscreteValuationField.ValuedExtension.differentIdealOfFiniteSeparable
      base target) =
      differentIdeal base.valuationSubring target.valuationSubring := by
  simp [differentIdealOfFiniteSeparable]

/-- Finite-separable trace-dual membership written directly as a trace
integrality condition. -/
theorem mem_codifferentSubmodule_iff_trace_mul_integral_of_finite_separable
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    {z : L} :
    z ∈ (RamificationTheory.DiscreteValuationField.ValuedExtension.codifferentSubmodule base
      target) ↔
      ∀ a ∈ (1 : Submodule target.valuationSubring L),
        IsIntegral base.valuationSubring (Algebra.trace K L (z * a)) := by
  let : IsIntegralClosure target.valuationSubring base.valuationSubring L :=
    target_valuationSubring_isIntegralClosure_of_finite_separable base target
  exact
    (mem_codifferentSubmodule_iff_trace_mul_integral base target)

/-- The local different/codifferent relation in finite separable complete-DVF
extensions, using the finite-separable different ideal. -/
theorem coeSubmodule_differentIdealOfFiniteSeparable_eq_one_div_codifferent
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    IsLocalization.coeSubmodule L
      (RamificationTheory.DiscreteValuationField.ValuedExtension.differentIdealOfFiniteSeparable
      base target) =
      1 / (RamificationTheory.DiscreteValuationField.ValuedExtension.codifferentSubmodule base
        target) := by
  unfold differentIdealOfFiniteSeparable
  let : IsIntegralClosure target.valuationSubring base.valuationSubring L :=
    target_valuationSubring_isIntegralClosure_of_finite_separable base target
  let : Module.IsTorsionFree base.valuationSubring target.valuationSubring :=
    moduleIsTorsionFree_target_valuationSubring_of_finite_separable
      (K := K) (L := L) (base := base) (target := target)
  change
    IsLocalization.coeSubmodule L
        (differentIdeal base.valuationSubring target.valuationSubring) =
      1 / Submodule.traceDual base.valuationSubring K
        (1 : Submodule target.valuationSubring L)
  exact _root_.coeSubmodule_differentIdeal
    base.valuationSubring K target.valuationSubring

omit [FiniteDimensional K L] in
/-- The different ideal is nonzero for finite separable torsion-free valuation
ring extensions. -/
theorem differentIdeal_ne_bot
    [Module.IsTorsionFree base.valuationSubring target.valuationSubring]
    [Module.Finite base.valuationSubring target.valuationSubring]
    [Algebra.IsSeparable
      (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring)] :
    differentIdeal base.valuationSubring target.valuationSubring ≠ ⊥ := by
  exact _root_.differentIdeal_ne_bot

omit [FiniteDimensional K L] in
/-- The fraction-field extension attached to a finite separable complete-DVF
extension is separable.  This is kept private to prevent typeclass search from
trying the very general `FractionRing.liftAlgebra` instance globally. -/
private theorem fractionRing_isSeparable_of_finite_separable
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    [Module.IsTorsionFree base.valuationSubring target.valuationSubring] :
    letI : FaithfulSMul base.valuationSubring target.valuationSubring :=
      Module.IsTorsionFree.to_faithfulSMul
    letI : FaithfulSMul base.valuationSubring
        (FractionRing target.valuationSubring) := inferInstance
    letI : Algebra (FractionRing base.valuationSubring)
        (FractionRing target.valuationSubring) := FractionRing.liftAlgebra _ _
    Algebra.IsSeparable (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring) := by
  let : FaithfulSMul base.valuationSubring target.valuationSubring :=
    Module.IsTorsionFree.to_faithfulSMul
  let : FaithfulSMul base.valuationSubring
      (FractionRing target.valuationSubring) := inferInstance
  let fracAlgebra : Algebra (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring) := FractionRing.liftAlgebra _ _
  let : SMul (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring) :=
    @Algebra.toSMul _ _ _ _ fracAlgebra
  let : IsScalarTower base.valuationSubring
      (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring) :=
    FractionRing.isScalarTower_liftAlgebra _ _
  have H : RingHom.comp
      (algebraMap (FractionRing base.valuationSubring)
        (FractionRing target.valuationSubring))
      (FractionRing.algEquiv base.valuationSubring K).symm.toRingEquiv =
        RingHom.comp
          (FractionRing.algEquiv target.valuationSubring L).symm.toRingEquiv
          (algebraMap K L) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors base.valuationSubring)
    ext a
    simp only [RingHom.coe_comp, RingHom.coe_coe,
      AlgEquiv.coe_ringEquiv, Function.comp_apply,
      AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply
      base.valuationSubring target.valuationSubring L,
      AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  exact Algebra.IsSeparable.of_equiv_equiv _ _ H

/-- The finite-separable different ideal is nonzero without separately
providing the module-finiteness, torsion-free, or fraction-field separability
certificates. -/
theorem differentIdealOfFiniteSeparable_ne_bot
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    (RamificationTheory.DiscreteValuationField.ValuedExtension.differentIdealOfFiniteSeparable
      base target) ≠ ⊥ := by
  unfold differentIdealOfFiniteSeparable
  let : IsIntegralClosure target.valuationSubring base.valuationSubring L :=
    target_valuationSubring_isIntegralClosure_of_finite_separable base target
  let : Module.Finite base.valuationSubring target.valuationSubring :=
    moduleFinite_target_valuationSubring_of_finite_separable base target
  let : Module.IsTorsionFree base.valuationSubring target.valuationSubring :=
    moduleIsTorsionFree_target_valuationSubring_of_finite_separable base target
  let : Algebra (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring) := FractionRing.liftAlgebra _ _
  let : Algebra.IsSeparable (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring) :=
    (fractionRing_isSeparable_of_finite_separable base target)
  exact (RamificationTheory.DiscreteValuationField.ValuedExtension.differentIdeal_ne_bot base
    target)

/-- The local different/codifferent relation specialized to the valuation
rings. -/
theorem coeSubmodule_differentIdeal_eq_one_div_codifferent
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    [IsIntegralClosure target.valuationSubring base.valuationSubring L]
    [Module.IsTorsionFree base.valuationSubring target.valuationSubring] :
    IsLocalization.coeSubmodule L
        (differentIdeal base.valuationSubring target.valuationSubring) =
      1 / (RamificationTheory.DiscreteValuationField.ValuedExtension.codifferentSubmodule base
        target) := by
  change
    IsLocalization.coeSubmodule L
        (differentIdeal base.valuationSubring target.valuationSubring) =
      1 / Submodule.traceDual base.valuationSubring K
        (1 : Submodule target.valuationSubring L)
  exact _root_.coeSubmodule_differentIdeal
    base.valuationSubring K target.valuationSubring

/-- Discriminant control for the codifferent: if a `K`-basis of `L` is
integral over the base valuation ring, then multiplying an element of the
codifferent by the discriminant and an integral element gives an integral
element. -/
theorem isIntegral_discriminant_mul_of_mem_codifferent
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    [IsIntegralClosure target.valuationSubring base.valuationSubring L]
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    {b : Module.Basis ι K L} (hb : ∀ i, IsIntegral base.valuationSubring (b i))
    {a z : L} (ha : a ∈ (1 : Submodule target.valuationSubring L))
    (hz : z ∈ (RamificationTheory.DiscreteValuationField.ValuedExtension.codifferentSubmodule
      base target)) :
    IsIntegral base.valuationSubring
      (Algebra.discr K b • a * z) := by
  exact _root_.isIntegral_discr_mul_of_mem_traceDual
    (A := base.valuationSubring) (K := K)
    (B := target.valuationSubring) (I := (1 : Submodule target.valuationSubring L))
    hb ha hz

/-- Finite-separable discriminant control for the codifferent. -/
theorem isIntegral_discriminant_mul_of_mem_codifferent_of_finite_separable
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    {b : Module.Basis ι K L} (hb : ∀ i, IsIntegral base.valuationSubring (b i))
    {a z : L} (ha : a ∈ (1 : Submodule target.valuationSubring L))
    (hz : z ∈ (RamificationTheory.DiscreteValuationField.ValuedExtension.codifferentSubmodule
      base target)) :
    IsIntegral base.valuationSubring
      (Algebra.discr K b • a * z) := by
  let : IsIntegralClosure target.valuationSubring base.valuationSubring L :=
    target_valuationSubring_isIntegralClosure_of_finite_separable base target
  exact
    (isIntegral_discriminant_mul_of_mem_codifferent base target) hb ha hz

/-- Finite-separable version of the different/unramified criterion, using
`differentIdealOfFiniteSeparable` to avoid separate torsion-free and
fraction-field separability certificates. -/
theorem maximalIdeal_not_dvd_differentIdealOfFiniteSeparable_iff_isUnramifiedAt
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    ¬ target.maximalIdeal ∣
      (RamificationTheory.DiscreteValuationField.ValuedExtension.differentIdealOfFiniteSeparable
      base target) ↔
      Algebra.IsUnramifiedAt base.valuationSubring target.maximalIdeal := by
  unfold differentIdealOfFiniteSeparable
  let : IsIntegralClosure target.valuationSubring base.valuationSubring L :=
    target_valuationSubring_isIntegralClosure_of_finite_separable base target
  let : Module.Finite base.valuationSubring target.valuationSubring :=
    moduleFinite_target_valuationSubring_of_finite_separable base target
  let : Module.IsTorsionFree base.valuationSubring target.valuationSubring :=
    moduleIsTorsionFree_target_valuationSubring_of_finite_separable base target
  let : Algebra (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring) := FractionRing.liftAlgebra _ _
  let : Algebra.IsSeparable (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring) :=
    (fractionRing_isSeparable_of_finite_separable base target)
  exact _root_.not_dvd_differentIdeal_iff

/-- Finite-separable version of the ramified/different divisibility criterion,
using `differentIdealOfFiniteSeparable`. -/
theorem maximalIdeal_dvd_differentIdealOfFiniteSeparable_iff_not_isUnramifiedAt
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    target.maximalIdeal ∣
      (RamificationTheory.DiscreteValuationField.ValuedExtension.differentIdealOfFiniteSeparable
      base target) ↔
      ¬ Algebra.IsUnramifiedAt base.valuationSubring target.maximalIdeal := by
  unfold differentIdealOfFiniteSeparable
  let : IsIntegralClosure target.valuationSubring base.valuationSubring L :=
    target_valuationSubring_isIntegralClosure_of_finite_separable base target
  let : Module.Finite base.valuationSubring target.valuationSubring :=
    moduleFinite_target_valuationSubring_of_finite_separable base target
  let : Module.IsTorsionFree base.valuationSubring target.valuationSubring :=
    moduleIsTorsionFree_target_valuationSubring_of_finite_separable base target
  let : Algebra (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring) := FractionRing.liftAlgebra _ _
  let : Algebra.IsSeparable (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring) :=
    (fractionRing_isSeparable_of_finite_separable base target)
  exact _root_.dvd_differentIdeal_iff

omit [FiniteDimensional K L] in
/-- In a local valuation-ring extension, the different is a unit exactly when
the extension is unramified at the target maximal ideal. -/
theorem isUnit_differentIdeal_iff_isUnramifiedAt
    [Module.IsTorsionFree base.valuationSubring target.valuationSubring]
    [Module.Finite base.valuationSubring target.valuationSubring]
    [Algebra.IsSeparable
      (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring)] :
    IsUnit (differentIdeal base.valuationSubring target.valuationSubring) ↔
      Algebra.IsUnramifiedAt base.valuationSubring target.maximalIdeal := by
  constructor
  · intro hunit
    have htop :
        differentIdeal base.valuationSubring target.valuationSubring = ⊤ :=
      Ideal.isUnit_iff.mp hunit
    have hnot :
        ¬ target.maximalIdeal ∣
          differentIdeal base.valuationSubring target.valuationSubring := by
      intro hdvd
      have hle :
          differentIdeal base.valuationSubring target.valuationSubring ≤
            target.maximalIdeal :=
        Ideal.dvd_iff_le.mp hdvd
      rw [htop] at hle
      have hproper : target.maximalIdeal ≠ ⊤ :=
        (IsLocalRing.maximalIdeal.isMaximal target.valuationSubring).ne_top
      exact hproper (eq_top_iff.mpr hle)
    exact (_root_.not_dvd_differentIdeal_iff).1 hnot
  · intro hunram
    have hnot :
        ¬ target.maximalIdeal ∣
          differentIdeal base.valuationSubring target.valuationSubring :=
    (_root_.not_dvd_differentIdeal_iff).2 hunram
    rw [Ideal.isUnit_iff]
    by_contra hne
    have hle :
        differentIdeal base.valuationSubring target.valuationSubring ≤
          target.maximalIdeal :=
      IsLocalRing.le_maximalIdeal hne
    exact hnot (Ideal.dvd_iff_le.mpr hle)

/-- Finite-separable version of the local unit criterion for the different. -/
theorem isUnit_differentIdealOfFiniteSeparable_iff_isUnramifiedAt
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    IsUnit
      (RamificationTheory.DiscreteValuationField.ValuedExtension.differentIdealOfFiniteSeparable
      base target) ↔
      Algebra.IsUnramifiedAt base.valuationSubring target.maximalIdeal := by
  unfold differentIdealOfFiniteSeparable
  let : IsIntegralClosure target.valuationSubring base.valuationSubring L :=
    target_valuationSubring_isIntegralClosure_of_finite_separable base target
  let : Module.Finite base.valuationSubring target.valuationSubring :=
    moduleFinite_target_valuationSubring_of_finite_separable base target
  let : Module.IsTorsionFree base.valuationSubring target.valuationSubring :=
    moduleIsTorsionFree_target_valuationSubring_of_finite_separable base target
  let : Algebra (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring) := FractionRing.liftAlgebra _ _
  let : Algebra.IsSeparable (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring) :=
    (fractionRing_isSeparable_of_finite_separable base target)
  exact
    (isUnit_differentIdeal_iff_isUnramifiedAt base target)

omit [FiniteDimensional K L] in
/-- States the theorem `differentIdeal_eq_top_iff_isUnramifiedAt`. -/
theorem differentIdeal_eq_top_iff_isUnramifiedAt
    [Module.IsTorsionFree base.valuationSubring target.valuationSubring]
    [Module.Finite base.valuationSubring target.valuationSubring]
    [Algebra.IsSeparable
      (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring)] :
    differentIdeal base.valuationSubring target.valuationSubring = ⊤ ↔
      Algebra.IsUnramifiedAt base.valuationSubring target.maximalIdeal := by
  rw [← Ideal.isUnit_iff]
  exact
    (isUnit_differentIdeal_iff_isUnramifiedAt base target)

/-- Finite-separable version of the top/different criterion for
unramifiedness. -/
theorem differentIdealOfFiniteSeparable_eq_top_iff_isUnramifiedAt
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    (RamificationTheory.DiscreteValuationField.ValuedExtension.differentIdealOfFiniteSeparable
      base target) = ⊤ ↔
      Algebra.IsUnramifiedAt base.valuationSubring target.maximalIdeal := by
  unfold differentIdealOfFiniteSeparable
  let : IsIntegralClosure target.valuationSubring base.valuationSubring L :=
    target_valuationSubring_isIntegralClosure_of_finite_separable base target
  let : Module.Finite base.valuationSubring target.valuationSubring :=
    moduleFinite_target_valuationSubring_of_finite_separable base target
  let : Module.IsTorsionFree base.valuationSubring target.valuationSubring :=
    moduleIsTorsionFree_target_valuationSubring_of_finite_separable base target
  let : Algebra (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring) := FractionRing.liftAlgebra _ _
  let : Algebra.IsSeparable (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring) :=
    (fractionRing_isSeparable_of_finite_separable base target)
  exact
    (differentIdeal_eq_top_iff_isUnramifiedAt base target)

/-- The monogenic different formula: conductor times different is generated by
the derivative of the minimal polynomial.  This is the Dedekind-domain formula
used in Eisenstein computations. -/
theorem conductor_mul_differentIdeal_eq_span_derivative
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    [IsIntegralClosure target.valuationSubring base.valuationSubring L]
    [Module.IsTorsionFree base.valuationSubring target.valuationSubring]
    (z : target.valuationSubring)
    (hz : Algebra.adjoin K {(algebraMap target.valuationSubring L) z} = ⊤) :
    conductor base.valuationSubring z *
        differentIdeal base.valuationSubring target.valuationSubring =
      Ideal.span
        {Polynomial.aeval z
          (Polynomial.derivative (minpoly base.valuationSubring z))} := by
  exact _root_.conductor_mul_differentIdeal
    base.valuationSubring K L z hz

/-- In a monogenic finite separable extension, the derivative of the minimal
polynomial belongs to the different. -/
theorem aeval_derivative_mem_differentIdeal
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    [IsIntegralClosure target.valuationSubring base.valuationSubring L]
    [Module.IsTorsionFree base.valuationSubring target.valuationSubring]
    (z : target.valuationSubring)
    (hz : Algebra.adjoin K {(algebraMap target.valuationSubring L) z} = ⊤) :
    Polynomial.aeval z
        (Polynomial.derivative (minpoly base.valuationSubring z)) ∈
      differentIdeal base.valuationSubring target.valuationSubring := by
  exact _root_.aeval_derivative_mem_differentIdeal
    base.valuationSubring K L z hz

/-- Monogenic different formula in finite separable complete-DVF extensions,
using the finite-separable different ideal. -/
theorem conductor_mul_differentIdealOfFiniteSeparable_eq_span_derivative
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    (z : target.valuationSubring)
    (hz : Algebra.adjoin K {(algebraMap target.valuationSubring L) z} = ⊤) :
    conductor base.valuationSubring z *
      (RamificationTheory.DiscreteValuationField.ValuedExtension.differentIdealOfFiniteSeparable
      base target) =
      Ideal.span
        {Polynomial.aeval z
          (Polynomial.derivative (minpoly base.valuationSubring z))} := by
  unfold differentIdealOfFiniteSeparable
  let : IsIntegralClosure target.valuationSubring base.valuationSubring L :=
    target_valuationSubring_isIntegralClosure_of_finite_separable base target
  let : Module.IsTorsionFree base.valuationSubring target.valuationSubring :=
    moduleIsTorsionFree_target_valuationSubring_of_finite_separable
      (K := K) (L := L) (base := base) (target := target)
  exact
    (conductor_mul_differentIdeal_eq_span_derivative base target) z hz

/-- In a monogenic finite separable complete-DVF extension, the derivative of
the minimal polynomial belongs to the finite-separable different ideal. -/
theorem aeval_derivative_mem_differentIdealOfFiniteSeparable
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    (z : target.valuationSubring)
    (hz : Algebra.adjoin K {(algebraMap target.valuationSubring L) z} = ⊤) :
    Polynomial.aeval z
        (Polynomial.derivative (minpoly base.valuationSubring z)) ∈
      (RamificationTheory.DiscreteValuationField.ValuedExtension.differentIdealOfFiniteSeparable
        base target) := by
  unfold differentIdealOfFiniteSeparable
  let : IsIntegralClosure target.valuationSubring base.valuationSubring L :=
    target_valuationSubring_isIntegralClosure_of_finite_separable base target
  let : Module.IsTorsionFree base.valuationSubring target.valuationSubring :=
    moduleIsTorsionFree_target_valuationSubring_of_finite_separable
      (K := K) (L := L) (base := base) (target := target)
  exact
    (aeval_derivative_mem_differentIdeal base target) z hz

/-- A monogenic finite separable complete-DVF extension is unramified when
an integral equation for its generator has unit derivative.  The equation
need not be the minimal polynomial: integrally closed divisibility transfers
the unit condition to the derivative of the minimal polynomial, which then
generates the different. -/
theorem isUnramifiedAt_of_aeval_derivative_isUnit
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    (z : target.valuationSubring)
    (hz : Algebra.adjoin K {(algebraMap target.valuationSubring L) z} = ⊤)
    (P : Polynomial base.valuationSubring)
    (hP : Polynomial.aeval z P = 0)
    (hPderiv :
      IsUnit (Polynomial.aeval z (Polynomial.derivative P))) :
    Algebra.IsUnramifiedAt base.valuationSubring target.maximalIdeal := by
  let : IsIntegralClosure target.valuationSubring
      base.valuationSubring L :=
    target_valuationSubring_isIntegralClosure_of_finite_separable
      base target
  let : Module.IsTorsionFree base.valuationSubring
      target.valuationSubring :=
    moduleIsTorsionFree_target_valuationSubring_of_finite_separable
      (K := K) (L := L) (base := base) (target := target)
  obtain ⟨Q, hQ⟩ :=
    minpoly.isIntegrallyClosed_dvd
      (IsIntegralClosure.isIntegral base.valuationSubring L z) hP
  have hderiv :
      Polynomial.aeval z (Polynomial.derivative P) =
        Polynomial.aeval z
            (Polynomial.derivative
              (minpoly base.valuationSubring z)) *
          Polynomial.aeval z Q := by
    rw [hQ, Polynomial.derivative_mul]
    simp
  have hminpolyDeriv :
      IsUnit
        (Polynomial.aeval z
          (Polynomial.derivative
            (minpoly base.valuationSubring z))) := by
    apply isUnit_of_mul_isUnit_left
    rw [← hderiv]
    exact hPderiv
  apply
    (differentIdealOfFiniteSeparable_eq_top_iff_isUnramifiedAt
      base target).1
  apply
    (differentIdealOfFiniteSeparable base target).eq_top_of_isUnit_mem
      (aeval_derivative_mem_differentIdealOfFiniteSeparable
        base target z hz)
  exact hminpolyDeriv

omit [FiniteDimensional K L] in
/-- Dedekind's different lower bound: if the image of the base maximal ideal is
divisible by `P^e`, then `P^(e-1)` divides the different.  For Eisenstein
extensions this is the standard source of the derivative/different exponent
bound. -/
theorem maximalIdeal_pow_sub_one_dvd_differentIdeal
    [Module.IsTorsionFree base.valuationSubring target.valuationSubring]
    [Module.Finite base.valuationSubring target.valuationSubring]
    [Algebra.IsSeparable
      (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring)]
    (e : ℕ)
    (hpow :
      target.maximalIdeal ^ e ∣
        Ideal.map (algebraMap base.valuationSubring target.valuationSubring)
          base.maximalIdeal) :
    target.maximalIdeal ^ (e - 1) ∣
      differentIdeal base.valuationSubring target.valuationSubring := by
  exact _root_.pow_sub_one_dvd_differentIdeal
    (A := base.valuationSubring) (B := target.valuationSubring)
    (P := target.maximalIdeal) (e := e) base.maximalIdeal_ne_bot hpow

/-- Finite-separable different lower bound, using
`differentIdealOfFiniteSeparable`. -/
theorem maximalIdeal_pow_sub_one_dvd_differentIdealOfFiniteSeparable
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    (e : ℕ)
    (hpow :
      target.maximalIdeal ^ e ∣
        Ideal.map (algebraMap base.valuationSubring target.valuationSubring)
          base.maximalIdeal) :
    target.maximalIdeal ^ (e - 1) ∣
      (RamificationTheory.DiscreteValuationField.ValuedExtension.differentIdealOfFiniteSeparable
      base target) := by
  unfold differentIdealOfFiniteSeparable
  let : IsIntegralClosure target.valuationSubring base.valuationSubring L :=
    target_valuationSubring_isIntegralClosure_of_finite_separable base target
  let : Module.Finite base.valuationSubring target.valuationSubring :=
    moduleFinite_target_valuationSubring_of_finite_separable base target
  let : Module.IsTorsionFree base.valuationSubring target.valuationSubring :=
    moduleIsTorsionFree_target_valuationSubring_of_finite_separable base target
  let : Algebra (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring) := FractionRing.liftAlgebra _ _
  let : Algebra.IsSeparable (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring) :=
    (fractionRing_isSeparable_of_finite_separable base target)
  exact
    (maximalIdeal_pow_sub_one_dvd_differentIdeal base target) e hpow

/-- Finite-separable different lower bound at the canonical
ramification index: `P^(e - 1)` divides the finite-separable different.  This
uses mathlib's defining containment for `Ideal.ramificationIdx`, so callers do
not have to supply the divisibility hypothesis separately. -/
theorem maximalIdeal_pow_ramificationIndex_sub_one_dvd_differentIdealOfFiniteSeparable
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    target.maximalIdeal ^ (ramificationIndex base.toDVF target.toDVF - 1) ∣
      (RamificationTheory.DiscreteValuationField.ValuedExtension.differentIdealOfFiniteSeparable
        base target) := by
  refine
    (maximalIdeal_pow_sub_one_dvd_differentIdealOfFiniteSeparable base target)
      (ramificationIndex base.toDVF target.toDVF) ?_
  rw [ramificationIndex]
  exact Ideal.dvd_iff_le.mpr
    (Ideal.le_pow_ramificationIdx'
      (p := base.maximalIdeal) (P := target.maximalIdeal))

/-- If the canonical ramification index is nontrivial, the target
maximal ideal divides the finite-separable different. -/
theorem maximalIdeal_dvd_differentIdealOfFiniteSeparable_of_one_lt_ramificationIndex
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    (he : 1 < ramificationIndex base.toDVF target.toDVF) :
    target.maximalIdeal ∣
      (RamificationTheory.DiscreteValuationField.ValuedExtension.differentIdealOfFiniteSeparable
      base target) := by
  have hlower :
      target.maximalIdeal ^ (ramificationIndex base.toDVF target.toDVF - 1) ∣
        (differentIdealOfFiniteSeparable base target) :=
    (maximalIdeal_pow_ramificationIndex_sub_one_dvd_differentIdealOfFiniteSeparable base target)
  have hpos : 0 < ramificationIndex base.toDVF target.toDVF - 1 := Nat.sub_pos_of_lt he
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos) with ⟨n, hn⟩
  have hdivPow :
      target.maximalIdeal ∣
        target.maximalIdeal ^ (ramificationIndex base.toDVF target.toDVF - 1) := by
    rw [hn, pow_succ]
    exact dvd_mul_left target.maximalIdeal (target.maximalIdeal ^ n)
  exact dvd_trans hdivPow hlower

/-- A finite separable extension with nontrivial ramification index is
ramified at the target maximal ideal. -/
theorem not_isUnramifiedAt_of_one_lt_ramificationIndex_of_finite_separable
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring target.valuationSubring L]
    (he : 1 < ramificationIndex base.toDVF target.toDVF) :
    ¬ Algebra.IsUnramifiedAt base.valuationSubring target.maximalIdeal := by
  exact
    ((maximalIdeal_dvd_differentIdealOfFiniteSeparable_iff_not_isUnramifiedAt base target)).1
      ((maximalIdeal_dvd_differentIdealOfFiniteSeparable_of_one_lt_ramificationIndex
        base target) he)

section Tower

variable {M : Type*} [Field M]
variable [Algebra K M] [Algebra M L]
variable [FiniteDimensional K M] [FiniteDimensional M L]
variable {middle : CompleteDVF M}
variable [base.valuation.HasExtension middle.valuation]
variable [middle.valuation.HasExtension target.valuation]

omit [FiniteDimensional K L] [FiniteDimensional K M]
    [FiniteDimensional M L] in
/-- Transitivity of the different ideal in a tower of valuation-ring
extensions. -/
theorem differentIdeal_tower
    [IsScalarTower base.valuationSubring middle.valuationSubring target.valuationSubring]
    [Module.Finite base.valuationSubring middle.valuationSubring]
    [Module.Finite base.valuationSubring target.valuationSubring]
    [Module.Finite middle.valuationSubring target.valuationSubring]
    [Module.IsTorsionFree base.valuationSubring middle.valuationSubring]
    [Module.IsTorsionFree base.valuationSubring target.valuationSubring]
    [Module.IsTorsionFree middle.valuationSubring target.valuationSubring]
    [Algebra.IsSeparable
      (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring)] :
    differentIdeal base.valuationSubring target.valuationSubring =
      differentIdeal middle.valuationSubring target.valuationSubring *
        Ideal.map (algebraMap middle.valuationSubring target.valuationSubring)
          (differentIdeal base.valuationSubring middle.valuationSubring) := by
  exact _root_.differentIdeal_eq_differentIdeal_mul_differentIdeal
    base.valuationSubring middle.valuationSubring target.valuationSubring

/-- Finite-separable tower formula for the different, using the
finite-separable different ideals on all three steps. -/
theorem differentIdealOfFiniteSeparable_tower
    [Algebra.IsSeparable K M] [Algebra.IsSeparable M L]
    [Algebra.IsSeparable K L]
    [IsScalarTower base.valuationSubring middle.valuationSubring target.valuationSubring]
    [IsScalarTower base.valuationSubring middle.valuationSubring M]
    [IsScalarTower middle.valuationSubring target.valuationSubring L]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    (RamificationTheory.DiscreteValuationField.ValuedExtension.differentIdealOfFiniteSeparable
      base target) =
      (RamificationTheory.DiscreteValuationField.ValuedExtension.differentIdealOfFiniteSeparable
        middle target) *
        Ideal.map (algebraMap middle.valuationSubring target.valuationSubring)
          (differentIdealOfFiniteSeparable base middle) := by
  unfold differentIdealOfFiniteSeparable
  let : IsIntegralClosure middle.valuationSubring base.valuationSubring M :=
    target_valuationSubring_isIntegralClosure_of_finite_separable base middle
  let : IsIntegralClosure target.valuationSubring middle.valuationSubring L :=
    target_valuationSubring_isIntegralClosure_of_finite_separable middle target
  let : IsIntegralClosure target.valuationSubring base.valuationSubring L :=
    target_valuationSubring_isIntegralClosure_of_finite_separable base target
  let : Module.Finite base.valuationSubring middle.valuationSubring :=
    moduleFinite_target_valuationSubring_of_finite_separable base middle
  let : Module.Finite middle.valuationSubring target.valuationSubring :=
    moduleFinite_target_valuationSubring_of_finite_separable middle target
  let : Module.Finite base.valuationSubring target.valuationSubring :=
    moduleFinite_target_valuationSubring_of_finite_separable base target
  let : Module.IsTorsionFree base.valuationSubring middle.valuationSubring :=
    moduleIsTorsionFree_target_valuationSubring_of_finite_separable base middle
  let : Module.IsTorsionFree middle.valuationSubring target.valuationSubring :=
    moduleIsTorsionFree_target_valuationSubring_of_finite_separable middle target
  let : Module.IsTorsionFree base.valuationSubring target.valuationSubring :=
    moduleIsTorsionFree_target_valuationSubring_of_finite_separable base target
  let : Algebra (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring) := FractionRing.liftAlgebra _ _
  let : Algebra.IsSeparable (FractionRing base.valuationSubring)
      (FractionRing target.valuationSubring) :=
    (fractionRing_isSeparable_of_finite_separable base target)
  exact differentIdeal_tower base target

end Tower

end ValuedExtension
end DiscreteValuationField
end RamificationTheory

end
