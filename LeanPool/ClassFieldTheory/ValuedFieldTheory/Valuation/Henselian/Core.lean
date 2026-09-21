/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.HenselianFinite
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.HenselianValuationExtension
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.HenselLemma
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
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.IrreduciblePolynomialLifting
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.UniqueExtensionReduction

/-! # Core -/
namespace ValuationTheory

/-!
# Henselian discretely valued fields

The Henselian factorization condition and the residual linear-factor lemmas used in the
residual linear-factor criterion.
-/

noncomputable section

namespace DiscreteValuationField

universe u v

/-- The factorization form of Hensel's lemma used in the Henselian factorization condition.

Every primitive polynomial whose reduction is a product of coprime factors has
degree-controlled lifts with the prescribed reductions. -/
def HenselFactorizationProperty {K : Type u} [Field K]
    (V : ValuationSubring K) : Prop :=
  ∀ {f : Polynomial V}
      {gbar hbar : Polynomial (IsLocalRing.ResidueField V)},
    f.map (IsLocalRing.residue V) ≠ 0 →
      f.map (IsLocalRing.residue V) = gbar * hbar →
        IsCoprime gbar hbar →
          ∃ G H : Polynomial V,
            G.natDegree = gbar.natDegree ∧
              H.natDegree ≤ f.natDegree - gbar.natDegree ∧
                f = G * H ∧
                  G.map (IsLocalRing.residue V) = gbar ∧
                    H.map (IsLocalRing.residue V) = hbar

/-- The Henselian factorization condition: a valuation is Henselian when its valuation ring
satisfies Hensel's lemma in the factorization sense. -/
def HenselianValuationByFactorization {K : Type u} [Field K]
    {Γ : Type v} [LinearOrderedCommGroupWithZero Γ]
    (val : _root_.Valuation K Γ) : Prop :=
  HenselFactorizationProperty val.valuationSubring

/-- An approximate root becomes an actual root after reducing coefficients
modulo the ideal. -/
theorem eval_map_quotient_mk_eq_zero_of_eval_mem
    {S : Type*} [CommRing S] {J : Ideal S} {p : Polynomial S} {a₀ : S}
    (hroot : p.eval a₀ ∈ J) :
    (p.map (Ideal.Quotient.mk J)).eval (Ideal.Quotient.mk J a₀) = 0 := by
  let q : S →+* S ⧸ J := Ideal.Quotient.mk J
  have hq : q (p.eval a₀) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hroot
  simpa [q, Polynomial.eval_map] using hq

/-- Derivatives commute with coefficient reduction and evaluation at the
reduced approximate root. -/
theorem derivative_eval_map_quotient_mk
    {S : Type*} [CommRing S] (J : Ideal S) (p : Polynomial S) (a₀ : S) :
    (p.map (Ideal.Quotient.mk J)).derivative.eval (Ideal.Quotient.mk J a₀) =
      Ideal.Quotient.mk J (p.derivative.eval a₀) := by
  simp [Polynomial.derivative_map]

/-- The simple-root hypothesis is the derivative-unit condition for the
residual polynomial. -/
theorem derivative_isUnit_map_quotient_mk_of_simpleRoot_mod
    {S : Type*} [CommRing S] {J : Ideal S} {p : Polynomial S} {a₀ : S}
    (hsimple : IsUnit (Ideal.Quotient.mk J (p.derivative.eval a₀))) :
    IsUnit
      ((p.map (Ideal.Quotient.mk J)).derivative.eval
        (Ideal.Quotient.mk J a₀)) := by
  simpa [derivative_eval_map_quotient_mk (J := J) (p := p) (a₀ := a₀)]
    using hsimple

/-- A derivative unit makes the linear factor coprime to the cofactor obtained
by monic division. -/
theorem isCoprime_X_sub_C_divByMonic_of_derivative_isUnit
    {S : Type*} [CommRing S] (p : Polynomial S) (a : S)
    (hunit : IsUnit (p.derivative.eval a)) :
    IsCoprime (Polynomial.X - Polynomial.C a)
      (p /ₘ (Polynomial.X - Polynomial.C a)) := by
  apply HenselianDVF.isCoprime_X_sub_C_of_isUnit_eval
  simpa only [divByMonic_X_sub_C_eval_eq_derivative_eval] using hunit

/-- A residual approximate root supplies an actual linear factor after
coefficient reduction. -/
theorem residual_X_sub_C_mul_divByMonic_eq_map_of_eval_mem
    {S : Type*} [CommRing S] {J : Ideal S} {p : Polynomial S} {a₀ : S}
    (hroot : p.eval a₀ ∈ J) :
    (Polynomial.X - Polynomial.C (Ideal.Quotient.mk J a₀)) *
        ((p.map (Ideal.Quotient.mk J)) /ₘ
          (Polynomial.X - Polynomial.C (Ideal.Quotient.mk J a₀))) =
      p.map (Ideal.Quotient.mk J) := by
  rw [Polynomial.mul_divByMonic_eq_iff_isRoot]
  exact eval_map_quotient_mk_eq_zero_of_eval_mem hroot

/-- A residual simple root splits the residual polynomial into coprime linear
and complementary factors. -/
theorem isCoprime_residual_X_sub_C_divByMonic_of_simpleRoot_mod
    {S : Type*} [CommRing S] {J : Ideal S} {p : Polynomial S} {a₀ : S}
    (hsimple : IsUnit (Ideal.Quotient.mk J (p.derivative.eval a₀))) :
    IsCoprime
      (Polynomial.X - Polynomial.C (Ideal.Quotient.mk J a₀))
      ((p.map (Ideal.Quotient.mk J)) /ₘ
        (Polynomial.X - Polynomial.C (Ideal.Quotient.mk J a₀))) :=
  isCoprime_X_sub_C_divByMonic_of_derivative_isUnit
    (p := p.map (Ideal.Quotient.mk J))
    (a := Ideal.Quotient.mk J a₀)
    (derivative_isUnit_map_quotient_mk_of_simpleRoot_mod hsimple)

/-- Finite algebras over a Noetherian Henselian, precomplete base are
Henselian along the extended ideal. -/
theorem henselianRing_map_algebraMap_of_moduleFinite_of_base_isPrecomplete
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {I : Ideal R} [IsNoetherianRing R] [Module.Finite R S]
    [HenselianRing R I] [IsPrecomplete I R] :
    HenselianRing S (I.map (algebraMap R S)) := by
  have hHausdorff : IsHausdorff I R :=
    IsHausdorff.of_le_jacobson
      (R := R) (M := R) (I := I)
      (show I ≤ Ideal.jacobson (⊥ : Ideal R) from HenselianRing.jac)
  let : IsAdicComplete I R :=
    { toIsHausdorff := hHausdorff
      toIsPrecomplete := inferInstance }
  exact henselianRing_map_algebraMap_of_moduleFinite_of_isAdicComplete
    (R := R) (S := S) (I := I)

end DiscreteValuationField

end

end ValuationTheory
