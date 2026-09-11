/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
module

public import LeanPool.RiemannRochFunctionFields.LocalResidue
public import LeanPool.RiemannRochFunctionFields.PlaceEquiv

/-!
# Coordinate-free divisors and degree

This file transports the two-chart divisor group to intrinsic places and identifies the transported
degree with the residue-field weighted sum.

## Main definitions

* `FunctionField.Divisor`: divisors indexed by intrinsic places.
* `FunctionField.divisorEquivChart`: equivalence with the two-chart divisor group.
* `FunctionField.Divisor.deg`: intrinsic divisor degree.
* `FunctionField.principalDivisor`: coordinate-free principal divisors.
-/

@[expose] public section

open scoped nonZeroDivisors Polynomial RatFunc WithZero

noncomputable section

namespace FunctionField

open Chart

variable (k K : Type*) [Field k] [Field K]
  [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]

/-- Classical decidable equality for the coordinate rational function field. -/
local instance instDecidableEqRatFuncCoordinateFreeDivisor : DecidableEq k⟮X⟯ :=
  Classical.decEq _

namespace Place

/-- Constant-field algebra structure on a finite-place valuation subring. -/
noncomputable local instance finiteVspAlgebra
    (w : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    Algebra k (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K w) :=
  ((algebraMap (ringOfIntegers k K)
    (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K w)).comp
      (algebraMap k (ringOfIntegers k K))).toAlgebra

/-- Scalar-tower compatibility for a finite-place valuation subring. -/
local instance finiteVspTower
    (w : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    IsScalarTower k (ringOfIntegers k K)
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K w) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The finite-chart valuation subring is the valuation subring of the intrinsic place. -/
noncomputable def finiteValuationSubringAlgEquiv
    (w : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K w ≃ₐ[k]
      (Place.ofChart k K (Sum.inl w)).toValuationSubring := by
  let e : (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K w).toSubring ≃+*
      (Place.ofChart k K (Sum.inl w)).toValuationSubring.toSubring :=
    RingEquiv.subringCongr <| congrArg ValuationSubring.toSubring <|
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring
        (K := K) (v := w)).trans (Place.ofChart_toValuationSubring k K (Sum.inl w)).symm
  exact
    { __ := e
      commutes' := fun c => by
        apply Subtype.ext
        change algebraMap (ringOfIntegers k K) K
          (algebraMap k (ringOfIntegers k K) c) = algebraMap k K c
        exact (IsScalarTower.algebraMap_apply k (ringOfIntegers k K) K c).symm }

/-- The finite-chart residue field is the intrinsic residue field. -/
noncomputable def finiteResidueAlgEquiv
    (w : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    (ringOfIntegers k K ⧸ w.asIdeal) ≃ₐ[k]
      (Place.ofChart k K (Sum.inl w)).residueField := by
  let e₀ : (ringOfIntegers k K ⧸ w.asIdeal) ≃ₐ[k] w.asIdeal.ResidueField :=
    AlgEquiv.ofBijective
      (IsScalarTower.toAlgHom k (ringOfIntegers k K ⧸ w.asIdeal) w.asIdeal.ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField w.asIdeal)
  let e₁ : w.asIdeal.ResidueField ≃ₐ[k]
      IsLocalRing.ResidueField
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K w) :=
    IsLocalRing.ResidueField.mapAlgEquiv
      ((IsDedekindDomain.HeightOneSpectrum.localizationAlgEquiv (K := K) w).restrictScalars k)
  let e₂ : IsLocalRing.ResidueField
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K w) ≃ₐ[k]
      (Place.ofChart k K (Sum.inl w)).residueField :=
    IsLocalRing.ResidueField.mapAlgEquiv (finiteValuationSubringAlgEquiv k K w)
  exact e₀.trans (e₁.trans e₂)

theorem finite_degree_eq (w : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    (Place.ofChart k K (Sum.inl w)).degree = placeDegree k K (Sum.inl w) := by
  exact (finiteResidueAlgEquiv k K w).toLinearEquiv.finrank_eq.symm

/-- Constant-field algebra structure on an infinite-place valuation subring. -/
noncomputable local instance infiniteVspAlgebra
    (w : IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K)) :
    Algebra k (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K w) :=
  ((algebraMap (infiniteIntegers k K)
    (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K w)).comp
      (algebraMap k (infiniteIntegers k K))).toAlgebra

/-- Scalar-tower compatibility for an infinite-place valuation subring. -/
local instance infiniteVspTower
    (w : IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K)) :
    IsScalarTower k (infiniteIntegers k K)
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K w) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The infinite-chart valuation subring is the valuation subring of the intrinsic place. -/
noncomputable def infiniteValuationSubringAlgEquiv
    (w : IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K)) :
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K w ≃ₐ[k]
      (Place.ofChart k K (Sum.inr w)).toValuationSubring := by
  let e : (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K w).toSubring ≃+*
      (Place.ofChart k K (Sum.inr w)).toValuationSubring.toSubring :=
    RingEquiv.subringCongr <| congrArg ValuationSubring.toSubring <|
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring
        (K := K) (v := w)).trans (Place.ofChart_toValuationSubring k K (Sum.inr w)).symm
  exact
    { __ := e
      commutes' := fun c => by
        apply Subtype.ext
        change algebraMap (infiniteIntegers k K) K
          (algebraMap k (infiniteIntegers k K) c) = algebraMap k K c
        exact (IsScalarTower.algebraMap_apply k (infiniteIntegers k K) K c).symm }

/-- The infinite-chart residue field is the intrinsic residue field. -/
noncomputable def infiniteResidueAlgEquiv
    (w : IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K)) :
    (infiniteIntegers k K ⧸ w.asIdeal) ≃ₐ[k]
      (Place.ofChart k K (Sum.inr w)).residueField := by
  let e₀ : (infiniteIntegers k K ⧸ w.asIdeal) ≃ₐ[k] w.asIdeal.ResidueField :=
    AlgEquiv.ofBijective
      (IsScalarTower.toAlgHom k (infiniteIntegers k K ⧸ w.asIdeal) w.asIdeal.ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField w.asIdeal)
  let e₁ : w.asIdeal.ResidueField ≃ₐ[k]
      IsLocalRing.ResidueField
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K w) :=
    IsLocalRing.ResidueField.mapAlgEquiv
      ((IsDedekindDomain.HeightOneSpectrum.localizationAlgEquiv (K := K) w).restrictScalars k)
  let e₂ : IsLocalRing.ResidueField
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K w) ≃ₐ[k]
      (Place.ofChart k K (Sum.inr w)).residueField :=
    IsLocalRing.ResidueField.mapAlgEquiv (infiniteValuationSubringAlgEquiv k K w)
  exact e₀.trans (e₁.trans e₂)

theorem infinite_degree_eq (w : IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K)) :
    (Place.ofChart k K (Sum.inr w)).degree = placeDegree k K (Sum.inr w) := by
  exact (infiniteResidueAlgEquiv k K w).toLinearEquiv.finrank_eq.symm

end Place

/-- The chart degree agrees with the intrinsic residue-field degree. -/
theorem placeDegree_eq (w : PlaceA k K) :
    placeDegree k K w = (chartToPlace k K w).degree := by
  rcases w with w | w
  · exact (Place.finite_degree_eq k K w).symm
  · exact (Place.infinite_degree_eq k K w).symm

/-- Divisors indexed by coordinate-free places. -/
abbrev Divisor := Place k K →₀ ℤ

/-- Reindex a chart divisor by the chart/intrinsic place equivalence. -/
noncomputable def divisorEquivChart : DivisorA k K ≃+ Divisor k K :=
  Finsupp.domCongr (chartToPlace k K)

/-- The coordinate-free principal-divisor homomorphism. -/
noncomputable def principalDivisor : Additive Kˣ →+ Divisor k K :=
  (divisorEquivChart k K).toAddMonoidHom.comp (principalDivisorA k K)

namespace Divisor

/-- The intrinsic weighted degree of a divisor. -/
noncomputable def deg (D : Divisor k K) : ℤ :=
  D.sum fun v n => n * (v.degree : ℤ)

omit [Algebra k[X] K] [Algebra k⟮X⟯ K] [IsScalarTower k k[X] K]
    [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K]
    [Algebra.IsSeparable k⟮X⟯ K] in
/-- The degree is the intrinsic residue-degree weighted sum. -/
theorem deg_formula (D : Divisor k K) :
    deg k K D = D.sum fun v n => n * (v.degree : ℤ) := rfl

omit [Algebra k[X] K] [Algebra k⟮X⟯ K] [IsScalarTower k k[X] K]
    [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K]
    [Algebra.IsSeparable k⟮X⟯ K] in
theorem deg_add (D E : Divisor k K) : deg k K (D + E) = deg k K D + deg k K E := by
  classical
  simp [deg, Finsupp.sum_add_index, add_mul]

theorem deg_equivChart (D : DivisorA k K) :
    deg k K (divisorEquivChart k K D) = Chart.deg k K D := by
  classical
  induction D using Finsupp.induction with
  | zero => simp [deg, Chart.deg, divisorEquivChart]
  | single_add a b f ha hb ih =>
      rw [map_add, deg_add, Chart.deg_add, ih]
      congr 1
      simp [deg, Chart.deg, divisorEquivChart, Finsupp.domCongr_apply,
        Finsupp.equivMapDomain_single, placeDegree_eq]

/-- Principal divisors have degree zero. -/
theorem deg_principal_eq_zero (x : Kˣ) :
    deg k K (principalDivisor k K (Additive.ofMul x)) = 0 := by
  rw [principalDivisor]
  exact (deg_equivChart k K (principalDivisorA k K (Additive.ofMul x))).trans
    (deg_principalDivisorA_eq_zero k K x)

end Divisor

end FunctionField
