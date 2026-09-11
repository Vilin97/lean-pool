/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
module

public import LeanPool.RiemannRochFunctionFields.Place
public import LeanPool.RiemannRochFunctionFields.SeparableRelNorm
public import Mathlib.Data.Finsupp.Order
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-!
# Divisor degree and order on a function field

This file completes the coordinate divisor API needed for Riemann–Roch spaces and adeles:
place degrees, global degree, and the partial order on `DivisorA`.

## Main definitions

* `FunctionField.placeDegree`: residue field dimension of a coordinate place.
* `FunctionField.deg`: global degree of a divisor.

The partial order on `DivisorA` is the pointwise order on `Finsupp` from Mathlib
(`Finsupp.le_def`); no new order instance is introduced here.
-/

@[expose] public section

open scoped nonZeroDivisors Polynomial RatFunc

noncomputable section

namespace FunctionField.Chart

variable (k K : Type*) [Field k] [Field K]
  [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]

/-- The classical decidable equality on `k(X)` used by the coordinate places. -/
local instance instDecidableEqRatFuncDivisorFile : DecidableEq k⟮X⟯ := Classical.decEq _

/-- The degree of a coordinate place: the residue field dimension over `k`. -/
noncomputable def placeDegree (v : PlaceA k K) : ℕ :=
  match v with
  | Sum.inl w =>
    letI : Field (ringOfIntegers k K ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
    Module.finrank k (ringOfIntegers k K ⧸ w.asIdeal)
  | Sum.inr w =>
    letI : Field (infiniteIntegers k K ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
    Module.finrank k (infiniteIntegers k K ⧸ w.asIdeal)

/-- Every coordinate place has strictly positive degree. -/
theorem placeDegree_pos (v : PlaceA k K) : 0 < placeDegree k K v := by
  rcases v with v | v
  · change 0 < Module.finrank k (ringOfIntegers k K ⧸ v.asIdeal)
    exact Module.finrank_pos
  · change 0 < Module.finrank k (infiniteIntegers k K ⧸ v.asIdeal)
    exact Module.finrank_pos

omit [IsScalarTower k[X] k⟮X⟯ K] in
/-- At an infinite coordinate place, the place degree is its inertia degree over the unique
place at infinity of `k(X)`. -/
theorem placeDegree_infinite_eq_inertiaDeg
    (v : IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K)) :
    placeDegree k K (Sum.inr v) =
      (v.asIdeal.under (inftyValuationSubring k)).inertiaDeg' v.asIdeal := by
  let A := inftyValuationSubring k
  let S := infiniteIntegers k K
  let p : Ideal A := v.asIdeal.under A
  let : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  let : p.IsMaximal := Ideal.IsMaximal.under A v.asIdeal
  let : v.asIdeal.LiesOver p := ⟨rfl⟩
  let : Field (A ⧸ p) := Ideal.Quotient.field p
  let : Field (S ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  let : Algebra (A ⧸ p) (S ⧸ v.asIdeal) :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.over_def v.asIdeal p).ge
  have hp : p = IsLocalRing.maximalIdeal A := IsLocalRing.eq_maximalIdeal inferInstance
  let : FiniteDimensional k (A ⧸ p) := by
    rw [hp]
    exact inftyValuationSubring.finiteDimensionalResidueField k
  let : FiniteDimensional (A ⧸ p) (S ⧸ v.asIdeal) := by
    have hfin := Ideal.inertiaDeg'_pos p v.asIdeal
    rw [Ideal.inertiaDeg'_algebraMap] at hfin
    exact FiniteDimensional.of_finrank_pos hfin
  let : IsScalarTower k (A ⧸ p) (S ⧸ v.asIdeal) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  change Module.finrank k (S ⧸ v.asIdeal) = p.inertiaDeg' v.asIdeal
  rw [Ideal.inertiaDeg'_algebraMap]
  have htower := Module.finrank_mul_finrank k (A ⧸ p) (S ⧸ v.asIdeal)
  have hbase : Module.finrank k (A ⧸ p) = 1 := by
    rw [hp]
    exact inftyValuationSubring.finrank_residueField k
  rw [hbase, one_mul] at htower
  exact htower.symm

/-- At a finite coordinate place, the place degree is the degree of the prime below times its
inertia degree. -/
theorem placeDegree_finite_eq_base_mul_inertiaDeg
    (v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    placeDegree k K (Sum.inl v) =
      Module.finrank k (k[X] ⧸ v.asIdeal.under k[X]) *
        (v.asIdeal.under k[X]).inertiaDeg' v.asIdeal := by
  let S := ringOfIntegers k K
  let p : Ideal k[X] := v.asIdeal.under k[X]
  let : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  let : p.IsMaximal := Ideal.IsMaximal.under k[X] v.asIdeal
  let : v.asIdeal.LiesOver p := ⟨rfl⟩
  let : Field (k[X] ⧸ p) := Ideal.Quotient.field p
  let : Field (S ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  let : Algebra (k[X] ⧸ p) (S ⧸ v.asIdeal) :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.over_def v.asIdeal p).ge
  let : FiniteDimensional k (k[X] ⧸ p) :=
    finite_of_finite_type_of_isJacobsonRing k _
  let : FiniteDimensional (k[X] ⧸ p) (S ⧸ v.asIdeal) := by
    have hfin := Ideal.inertiaDeg'_pos p v.asIdeal
    rw [Ideal.inertiaDeg'_algebraMap] at hfin
    exact FiniteDimensional.of_finrank_pos hfin
  let : IsScalarTower k (k[X] ⧸ p) (S ⧸ v.asIdeal) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  change Module.finrank k (S ⧸ v.asIdeal) =
    Module.finrank k (k[X] ⧸ p) * p.inertiaDeg' v.asIdeal
  rw [Ideal.inertiaDeg'_algebraMap]
  exact (Module.finrank_mul_finrank k (k[X] ⧸ p) (S ⧸ v.asIdeal)).symm

/-- The relative ideal norm of a finite coordinate prime has exponent equal to its inertia
degree; unlike Mathlib's perfect-field version, this uses only the standing separability
hypothesis. -/
theorem relNorm_asIdeal_finite
    (v : IsDedekindDomain.HeightOneSpectrum (ringOfIntegers k K)) :
    Ideal.relNorm k[X] v.asIdeal =
      (v.asIdeal.under k[X]) ^ (v.asIdeal.under k[X]).inertiaDeg' v.asIdeal := by
  let S := ringOfIntegers k K
  let : Algebra k[X] (FractionRing S) := inferInstance
  let : FaithfulSMul k[X] (FractionRing S) := inferInstance
  let : Algebra (FractionRing k[X]) (FractionRing S) :=
    FractionRing.liftAlgebra k[X] (FractionRing S)
  let : IsScalarTower k[X] (FractionRing k[X]) (FractionRing S) :=
    FractionRing.isScalarTower_liftAlgebra k[X] (FractionRing S)
  let : Algebra.IsSeparable (FractionRing k[X]) (FractionRing S) := by
    refine Algebra.IsSeparable.of_equiv_equiv
      (FractionRing.algEquiv k[X] k⟮X⟯).symm.toRingEquiv
      (FractionRing.algEquiv S K).symm.toRingEquiv ?_
    ext x
    exact IsFractionRing.algEquiv_commutes
      (FractionRing.algEquiv k[X] k⟮X⟯).symm
      (FractionRing.algEquiv S K).symm x
  let : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  let : (v.asIdeal.under k[X]).IsMaximal := Ideal.IsMaximal.under k[X] v.asIdeal
  exact Ideal.relNorm_eq_pow_of_isMaximal_of_isSeparable
    v.asIdeal (v.asIdeal.under k[X])

omit [Algebra k[X] K] [IsScalarTower k[X] k⟮X⟯ K] in
/-- The corresponding relative-norm formula on the infinity chart. -/
theorem relNorm_asIdeal_infinite
    (v : IsDedekindDomain.HeightOneSpectrum (infiniteIntegers k K)) :
    Ideal.relNorm (inftyValuationSubring k) v.asIdeal =
      (v.asIdeal.under (inftyValuationSubring k)) ^
        (v.asIdeal.under (inftyValuationSubring k)).inertiaDeg' v.asIdeal := by
  let A := inftyValuationSubring k
  let S := infiniteIntegers k K
  let : Algebra A (FractionRing S) := inferInstance
  let : FaithfulSMul A (FractionRing S) := inferInstance
  let : Algebra (FractionRing A) (FractionRing S) :=
    FractionRing.liftAlgebra A (FractionRing S)
  let : IsScalarTower A (FractionRing A) (FractionRing S) :=
    FractionRing.isScalarTower_liftAlgebra A (FractionRing S)
  let : Algebra.IsSeparable (FractionRing A) (FractionRing S) := by
    refine Algebra.IsSeparable.of_equiv_equiv
      (FractionRing.algEquiv A k⟮X⟯).symm.toRingEquiv
      (FractionRing.algEquiv S K).symm.toRingEquiv ?_
    ext x
    exact IsFractionRing.algEquiv_commutes
      (FractionRing.algEquiv A k⟮X⟯).symm
      (FractionRing.algEquiv S K).symm x
  let : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  let : (v.asIdeal.under A).IsMaximal := Ideal.IsMaximal.under A v.asIdeal
  exact Ideal.relNorm_eq_pow_of_isMaximal_of_isSeparable
    v.asIdeal (v.asIdeal.under A)

/-- Weighted factor degree on the finite chart is preserved by relative ideal norm. -/
theorem finite_factorDegree_eq_relNorm (I : Ideal (ringOfIntegers k K)) (hI : I ≠ ⊥) :
    ((UniqueFactorizationMonoid.normalizedFactors I).map fun P =>
      Module.finrank k (k[X] ⧸ P.under k[X]) * (P.under k[X]).inertiaDeg' P).sum =
    ((UniqueFactorizationMonoid.normalizedFactors (Ideal.relNorm k[X] I)).map fun p =>
      Module.finrank k (k[X] ⧸ p)).sum := by
  let S := ringOfIntegers k K
  let : Algebra k[X] (FractionRing S) := inferInstance
  let : FaithfulSMul k[X] (FractionRing S) := inferInstance
  let : Algebra (FractionRing k[X]) (FractionRing S) :=
    FractionRing.liftAlgebra k[X] (FractionRing S)
  let : IsScalarTower k[X] (FractionRing k[X]) (FractionRing S) :=
    FractionRing.isScalarTower_liftAlgebra k[X] (FractionRing S)
  let : Algebra.IsSeparable (FractionRing k[X]) (FractionRing S) := by
    refine Algebra.IsSeparable.of_equiv_equiv
      (FractionRing.algEquiv k[X] k⟮X⟯).symm.toRingEquiv
      (FractionRing.algEquiv S K).symm.toRingEquiv ?_
    ext x
    exact IsFractionRing.algEquiv_commutes
      (FractionRing.algEquiv k[X] k⟮X⟯).symm
      (FractionRing.algEquiv S K).symm x
  symm
  simpa only [Nat.mul_comm] using
    Ideal.sum_normalizedFactors_relNorm_of_isSeparable I hI
      (fun p : Ideal k[X] => Module.finrank k (k[X] ⧸ p))

omit [Algebra k[X] K] [IsScalarTower k[X] k⟮X⟯ K] in
/-- The analogous relative-norm identity on the infinity chart. -/
theorem infinite_factorDegree_eq_relNorm
    (I : Ideal (infiniteIntegers k K)) (hI : I ≠ ⊥) :
    ((UniqueFactorizationMonoid.normalizedFactors I).map fun P =>
      (P.under (inftyValuationSubring k)).inertiaDeg' P).sum =
    ((UniqueFactorizationMonoid.normalizedFactors
      (Ideal.relNorm (inftyValuationSubring k) I)).map fun _ => 1).sum := by
  let A := inftyValuationSubring k
  let S := infiniteIntegers k K
  let : Algebra A (FractionRing S) := inferInstance
  let : FaithfulSMul A (FractionRing S) := inferInstance
  let : Algebra (FractionRing A) (FractionRing S) :=
    FractionRing.liftAlgebra A (FractionRing S)
  let : IsScalarTower A (FractionRing A) (FractionRing S) :=
    FractionRing.isScalarTower_liftAlgebra A (FractionRing S)
  let : Algebra.IsSeparable (FractionRing A) (FractionRing S) := by
    refine Algebra.IsSeparable.of_equiv_equiv
      (FractionRing.algEquiv A k⟮X⟯).symm.toRingEquiv
      (FractionRing.algEquiv S K).symm.toRingEquiv ?_
    ext x
    exact IsFractionRing.algEquiv_commutes
      (FractionRing.algEquiv A k⟮X⟯).symm
      (FractionRing.algEquiv S K).symm x
  symm
  simpa using Ideal.sum_normalizedFactors_relNorm_of_isSeparable I hI
    (fun _ : Ideal A => 1)

/-- Over the finite chart of `k(X)`, the weighted prime-factor degree of a principal polynomial
ideal is the polynomial degree. -/
theorem polynomial_factorDegree_span (p : k[X]) (hp : p ≠ 0) :
    ((UniqueFactorizationMonoid.normalizedFactors (Ideal.span {p})).map
      (fun P : Ideal k[X] => Module.finrank k (k[X] ⧸ P))).sum = p.natDegree := by
  classical
  rw [← UniqueFactorizationMonoid.factors_eq_normalizedFactors,
    Ideal.factors_span_eq, Multiset.map_map]
  simp_rw [Function.comp_apply, finrank_quotient_span_eq_natDegree]
  have hassoc := UniqueFactorizationMonoid.factors_prod hp
  have hprod : (UniqueFactorizationMonoid.factors p).prod ≠ 0 :=
    hassoc.ne_zero_iff.mpr hp
  have hzero : (0 : k[X]) ∉ UniqueFactorizationMonoid.factors p := by
    intro h
    exact hprod (Multiset.prod_eq_zero_iff.mpr h)
  rw [← Polynomial.natDegree_multiset_prod _ hzero]
  exact Polynomial.natDegree_eq_of_degree_eq
    (Polynomial.degree_eq_degree_of_associated hassoc)

/-- Over the infinity chart of `k(X)`, the number of prime factors of a nonzero principal ideal
is the negative rational-function degree of its generator. -/
theorem infinity_factorDegree_span (a : inftyValuationSubring k) (ha : a ≠ 0) :
    ((((UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})).map
      (fun _ : Ideal (inftyValuationSubring k) => (1 : ℕ))).sum : ℕ) : ℤ) =
        -RatFunc.intDegree (a : k⟮X⟯) := by
  classical
  let v := RatFunc.inftyValuation k
  let A := inftyValuationSubring k
  have hmem : (1 / RatFunc.X : k⟮X⟯) ∈ v.valuationSubring := by
    change v (1 / RatFunc.X) ≤ 1
    rw [RatFunc.inftyValuation.X_inv]
    simpa only [← WithZero.exp_zero, WithZero.exp_le_exp] using (show (-1 : ℤ) ≤ 0 by omega)
  let π : v.valuationSubring := ⟨1 / RatFunc.X, hmem⟩
  have hgen : (↑(Valuation.IsRankOneDiscrete.generator v) : WithZero (Multiplicative ℤ)) =
      WithZero.exp (-1 : ℤ) := by
    have h := Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range
      (v := v) (show WithZero.exp (-1 : ℤ) ∈ Set.range v from
        ⟨1 / RatFunc.X, RatFunc.inftyValuation.X_inv k⟩)
    exact congrArg Units.val h
  have hπval : v (π : k⟮X⟯) = WithZero.exp (-1 : ℤ) := by
    exact RatFunc.inftyValuation.X_inv k
  have hπ : v.IsUniformizer (π : k⟮X⟯) := by
    rw [Valuation.IsUniformizer.iff, hgen]
    exact hπval
  let πu : v.Uniformizer := ⟨π, hπ⟩
  obtain ⟨n, u, hau⟩ := Valuation.exists_pow_Uniformizer ha πu
  have hassocA : Associated a (π ^ n) := by
    have hauA : a = π ^ n * (u : v.valuationSubring) := by
      apply Subtype.ext
      exact hau
    rw [hauA]
    exact associated_mul_unit_left _ _ u.isUnit
  have hmaxpow : IsLocalRing.maximalIdeal A ^ n = Ideal.span {π ^ n} := by
    exact Valuation.pow_Uniformizer_is_pow_generator πu n
  have hideal : Ideal.span {a} = IsLocalRing.maximalIdeal A ^ n := by
    rw [hmaxpow]
    exact Ideal.span_singleton_eq_span_singleton.mpr hassocA
  have hmaxIrred : Irreducible (IsLocalRing.maximalIdeal A) := by
    exact (Ideal.prime_of_isPrime
      (IsDiscreteValuationRing.maximalIdeal A).ne_bot
      (IsLocalRing.maximalIdeal.isMaximal A).isPrime).irreducible
  have hfactor :
      UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a}) =
        Multiset.replicate n (IsLocalRing.maximalIdeal A) := by
    rw [hideal, UniqueFactorizationMonoid.normalizedFactors_pow,
      UniqueFactorizationMonoid.normalizedFactors_irreducible hmaxIrred,
      normalize_eq, Multiset.nsmul_singleton]
  have hleft :
      ((UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})).map
        (fun _ : Ideal A => 1)).sum = n := by
    rw [hfactor]
    simp
  have huval : v ((u : v.valuationSubring) : k⟮X⟯) = 1 := by
    exact (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.valuationSubring.integers v)).mp u.isUnit
  have haval : v (a : k⟮X⟯) = WithZero.exp (RatFunc.intDegree (a : k⟮X⟯)) := by
    rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero]
    simpa using ha
  have hvrepr := congrArg v hau
  have hexp : WithZero.exp (RatFunc.intDegree (a : k⟮X⟯)) =
      WithZero.exp (-(n : ℤ)) := by
    rw [← haval, hvrepr, map_mul]
    change v ((π : k⟮X⟯) ^ n) * v ((u : v.valuationSubring) : k⟮X⟯) = _
    rw [map_pow, hπval, huval, mul_one]
    calc
      WithZero.exp (-1 : ℤ) ^ n = WithZero.exp (n • (-1 : ℤ)) :=
        (WithZero.exp_nsmul n (-1 : ℤ)).symm
      _ = WithZero.exp (-(n : ℤ)) := by congr 1; simp
  have hint : RatFunc.intDegree (a : k⟮X⟯) = -(n : ℤ) :=
    WithZero.exp_injective hexp
  have hleftZ :
      ((((UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})).map
        (fun _ : Ideal A => (1 : ℕ))).sum : ℕ) : ℤ) = (n : ℤ) := by
    exact congrArg (fun m : ℕ => (m : ℤ)) hleft
  rw [hleftZ, hint]
  omega

/-- Compatibility of integral norm on the finite chart with the field norm after passing to
fraction fields. -/
theorem finite_intNorm_div_eq_norm (x : Kˣ) (n : ringOfIntegers k K)
    (d : nonZeroDivisors (ringOfIntegers k K))
    (hnd : IsLocalization.mk' K n d = (x : K)) :
    algebraMap k[X] k⟮X⟯ (Algebra.intNorm k[X] (ringOfIntegers k K) n) /
      algebraMap k[X] k⟮X⟯
        (Algebra.intNorm k[X] (ringOfIntegers k K) (d : ringOfIntegers k K)) =
      Algebra.norm k⟮X⟯ (x : K) := by
  have hn : algebraMap k[X] k⟮X⟯ (Algebra.intNorm k[X] (ringOfIntegers k K) n) =
      Algebra.intNorm k⟮X⟯ K (algebraMap (ringOfIntegers k K) K n) :=
    Algebra.intNorm_eq_of_isLocalization k[X]⁰ (Bₘ := K) n
  have hd : algebraMap k[X] k⟮X⟯
      (Algebra.intNorm k[X] (ringOfIntegers k K) (d : ringOfIntegers k K)) =
      Algebra.intNorm k⟮X⟯ K
        (algebraMap (ringOfIntegers k K) K (d : ringOfIntegers k K)) :=
    Algebra.intNorm_eq_of_isLocalization k[X]⁰ (Bₘ := K) (d : ringOfIntegers k K)
  rw [Algebra.intNorm_eq_norm k[X] (ringOfIntegers k K),
    Algebra.intNorm_eq_norm k⟮X⟯ K] at hn hd
  let N : K →*₀ k⟮X⟯ :=
    { Algebra.norm k⟮X⟯ with
      map_zero' := (Algebra.norm_eq_zero_iff (R := k⟮X⟯) (S := K)).mpr rfl }
  have hx := congrArg N hnd
  rw [IsFractionRing.mk'_eq_div, map_div₀] at hx
  change Algebra.norm k⟮X⟯ (algebraMap (ringOfIntegers k K) K n) /
    Algebra.norm k⟮X⟯
      (algebraMap (ringOfIntegers k K) K (d : ringOfIntegers k K)) =
      Algebra.norm k⟮X⟯ (x : K) at hx
  rw [← hn, ← hd] at hx
  simpa [Algebra.intNorm_eq_norm k[X] (ringOfIntegers k K)] using hx

omit [Algebra k[X] K] [IsScalarTower k[X] k⟮X⟯ K] in
/-- Compatibility of integral norm with field norm on the infinity chart. -/
theorem infinite_intNorm_div_eq_norm (x : Kˣ) (n : infiniteIntegers k K)
    (d : nonZeroDivisors (infiniteIntegers k K))
    (hnd : IsLocalization.mk' K n d = (x : K)) :
    algebraMap (inftyValuationSubring k) k⟮X⟯
        (Algebra.intNorm (inftyValuationSubring k) (infiniteIntegers k K) n) /
      algebraMap (inftyValuationSubring k) k⟮X⟯
        (Algebra.intNorm (inftyValuationSubring k) (infiniteIntegers k K)
          (d : infiniteIntegers k K)) =
      Algebra.norm k⟮X⟯ (x : K) := by
  let A := inftyValuationSubring k
  let S := infiniteIntegers k K
  have hn : algebraMap A k⟮X⟯ (Algebra.intNorm A S n) =
      Algebra.intNorm k⟮X⟯ K (algebraMap S K n) :=
    Algebra.intNorm_eq_of_isLocalization A⁰ (Bₘ := K) n
  have hd : algebraMap A k⟮X⟯ (Algebra.intNorm A S (d : S)) =
      Algebra.intNorm k⟮X⟯ K (algebraMap S K (d : S)) :=
    Algebra.intNorm_eq_of_isLocalization A⁰ (Bₘ := K) (d : S)
  rw [Algebra.intNorm_eq_norm A S, Algebra.intNorm_eq_norm k⟮X⟯ K] at hn hd
  let N : K →*₀ k⟮X⟯ :=
    { Algebra.norm k⟮X⟯ with
      map_zero' := (Algebra.norm_eq_zero_iff (R := k⟮X⟯) (S := K)).mpr rfl }
  have hx := congrArg N hnd
  rw [IsFractionRing.mk'_eq_div, map_div₀] at hx
  change Algebra.norm k⟮X⟯ (algebraMap S K n) /
    Algebra.norm k⟮X⟯ (algebraMap S K (d : S)) = Algebra.norm k⟮X⟯ (x : K) at hx
  rw [← hn, ← hd] at hx
  simpa [A, S, Algebra.intNorm_eq_norm A S] using hx

/-- The ideal-valued weight whose restriction to finite height-one primes is `placeDegree`. -/
noncomputable def finiteIdealWeight (P : Ideal (ringOfIntegers k K)) : ℕ :=
  Module.finrank k (k[X] ⧸ P.under k[X]) * (P.under k[X]).inertiaDeg' P

/-- The ideal-valued weight whose restriction to infinite height-one primes is `placeDegree`. -/
noncomputable def infiniteIdealWeight (P : Ideal (infiniteIntegers k K)) : ℕ :=
  (P.under (inftyValuationSubring k)).inertiaDeg' P

/-- The finite-chart contribution of a principal divisor is the degree at infinity of the field
norm. -/
theorem finitePrincipalDegree_eq_intDegree_norm (x : Kˣ) :
    (FractionalIdeal.principalDivisor
      (R := ringOfIntegers k K) (K := K) (Additive.ofMul x)).sum
        (fun v n => n * (placeDegree k K (Sum.inl v) : ℤ)) =
      RatFunc.intDegree (Algebra.norm k⟮X⟯ (x : K)) := by
  classical
  let S := ringOfIntegers k K
  obtain ⟨n, d, hnd⟩ := IsLocalization.exists_mk'_eq S⁰ (x : K)
  have hn : n ≠ 0 := by
    intro hn
    exact x.ne_zero (by simpa [hn] using hnd.symm)
  have hd : (d : S) ≠ 0 := by
    simpa only [mem_nonZeroDivisors_iff_ne_zero] using d.property
  have hdeg := FractionalIdeal.weightedDegree_principal_mk'
    (R := S) (K := K) (finiteIdealWeight k K) x n d hnd
  have hnormn := finite_factorDegree_eq_relNorm k K (Ideal.span {n})
    (Ideal.span_singleton_eq_bot.not.mpr hn)
  have hnormd := finite_factorDegree_eq_relNorm k K (Ideal.span {(d : S)})
    (Ideal.span_singleton_eq_bot.not.mpr hd)
  let pn : k[X] := Algebra.intNorm k[X] S n
  let pd : k[X] := Algebra.intNorm k[X] S (d : S)
  have hpn : pn ≠ 0 := by
    dsimp only [pn]
    rw [Algebra.intNorm_eq_norm]
    simpa only [ne_eq, Algebra.norm_eq_zero_iff] using hn
  have hpd : pd ≠ 0 := by
    dsimp only [pd]
    rw [Algebra.intNorm_eq_norm]
    simpa only [ne_eq, Algebra.norm_eq_zero_iff] using hd
  rw [Ideal.relNorm_singleton, polynomial_factorDegree_span k pn hpn] at hnormn
  rw [Ideal.relNorm_singleton, polynomial_factorDegree_span k pd hpd] at hnormd
  change
    (FractionalIdeal.principalDivisor
      (R := S) (K := K) (Additive.ofMul x)).sum
        (fun v m => m * (placeDegree k K (Sum.inl v) : ℤ)) = _
  have hchart :
      (FractionalIdeal.principalDivisor
        (R := S) (K := K) (Additive.ofMul x)).sum
          (fun v m => m * (placeDegree k K (Sum.inl v) : ℤ)) =
        (pn.natDegree : ℤ) - (pd.natDegree : ℤ) := by
    rw [← hnormn, ← hnormd]
    unfold finiteIdealWeight at hdeg
    simpa only [FractionalIdeal.weightedDegree_apply,
      placeDegree_finite_eq_base_mul_inertiaDeg] using hdeg
  have hratio := finite_intNorm_div_eq_norm k K x n d hnd
  change algebraMap k[X] k⟮X⟯ pn / algebraMap k[X] k⟮X⟯ pd =
    Algebra.norm k⟮X⟯ (x : K) at hratio
  have hpn' : algebraMap k[X] k⟮X⟯ pn ≠ 0 :=
    by simpa using (IsFractionRing.injective k[X] k⟮X⟯).ne hpn
  have hpd' : algebraMap k[X] k⟮X⟯ pd ≠ 0 :=
    by simpa using (IsFractionRing.injective k[X] k⟮X⟯).ne hpd
  have hint := congrArg RatFunc.intDegree hratio
  rw [RatFunc.intDegree_div hpn' hpd', RatFunc.intDegree_polynomial,
    RatFunc.intDegree_polynomial] at hint
  exact hchart.trans hint

omit [IsScalarTower k[X] k⟮X⟯ K] in
/-- The infinite-chart contribution of a principal divisor is the negative degree at infinity of
the field norm. -/
theorem infinitePrincipalDegree_eq_neg_intDegree_norm (x : Kˣ) :
    (FractionalIdeal.principalDivisor
      (R := infiniteIntegers k K) (K := K) (Additive.ofMul x)).sum
        (fun v n => n * (placeDegree k K (Sum.inr v) : ℤ)) =
      -RatFunc.intDegree (Algebra.norm k⟮X⟯ (x : K)) := by
  classical
  let A := inftyValuationSubring k
  let S := infiniteIntegers k K
  obtain ⟨n, d, hnd⟩ := IsLocalization.exists_mk'_eq S⁰ (x : K)
  have hn : n ≠ 0 := by
    intro hn
    exact x.ne_zero (by simpa [hn] using hnd.symm)
  have hd : (d : S) ≠ 0 := by
    simpa only [mem_nonZeroDivisors_iff_ne_zero] using d.property
  have hdeg := FractionalIdeal.weightedDegree_principal_mk'
    (R := S) (K := K) (infiniteIdealWeight k K) x n d hnd
  have hnormn := infinite_factorDegree_eq_relNorm k K (Ideal.span {n})
    (Ideal.span_singleton_eq_bot.not.mpr hn)
  have hnormd := infinite_factorDegree_eq_relNorm k K (Ideal.span {(d : S)})
    (Ideal.span_singleton_eq_bot.not.mpr hd)
  let qn : A := Algebra.intNorm A S n
  let qd : A := Algebra.intNorm A S (d : S)
  have hqn : qn ≠ 0 := by
    dsimp only [qn]
    rw [Algebra.intNorm_eq_norm]
    simpa only [ne_eq, Algebra.norm_eq_zero_iff] using hn
  have hqd : qd ≠ 0 := by
    dsimp only [qd]
    rw [Algebra.intNorm_eq_norm]
    simpa only [ne_eq, Algebra.norm_eq_zero_iff] using hd
  rw [Ideal.relNorm_singleton] at hnormn hnormd
  have hbaseqn := infinity_factorDegree_span k qn hqn
  have hbaseqd := infinity_factorDegree_span k qd hqd
  have hnormnZ := congrArg (fun m : ℕ => (m : ℤ)) hnormn
  have hnormdZ := congrArg (fun m : ℕ => (m : ℤ)) hnormd
  have hupn :
      ((((UniqueFactorizationMonoid.normalizedFactors (Ideal.span {n})).map
        (fun P => (P.under (inftyValuationSubring k)).inertiaDeg' P)).sum : ℕ) : ℤ) =
          -RatFunc.intDegree (qn : k⟮X⟯) :=
    hnormnZ.trans hbaseqn
  have hupd :
      ((((UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(d : S)})).map
        (fun P => (P.under (inftyValuationSubring k)).inertiaDeg' P)).sum : ℕ) : ℤ) =
          -RatFunc.intDegree (qd : k⟮X⟯) :=
    hnormdZ.trans hbaseqd
  change
    (FractionalIdeal.principalDivisor
      (R := S) (K := K) (Additive.ofMul x)).sum
        (fun v m => m * (placeDegree k K (Sum.inr v) : ℤ)) = _
  have hchart :
      (FractionalIdeal.principalDivisor
        (R := S) (K := K) (Additive.ofMul x)).sum
          (fun v m => m * (placeDegree k K (Sum.inr v) : ℤ)) =
        -RatFunc.intDegree (qn : k⟮X⟯) -
          (-RatFunc.intDegree (qd : k⟮X⟯)) := by
    have hdeg' := hdeg
    unfold infiniteIdealWeight at hdeg'
    simp only [FractionalIdeal.weightedDegree_apply] at hdeg'
    rw [hupn, hupd] at hdeg'
    simpa only [placeDegree_infinite_eq_inertiaDeg] using hdeg'
  have hratio := infinite_intNorm_div_eq_norm k K x n d hnd
  change (qn : k⟮X⟯) / (qd : k⟮X⟯) = Algebra.norm k⟮X⟯ (x : K) at hratio
  have hqn' : (qn : k⟮X⟯) ≠ 0 := by simpa using hqn
  have hqd' : (qd : k⟮X⟯) ≠ 0 := by simpa using hqd
  have hint := congrArg RatFunc.intDegree hratio
  rw [RatFunc.intDegree_div hqn' hqd'] at hint
  rw [hchart, ← hint]
  ring

/-- The valuation subring at a coordinate place. -/
noncomputable def placeValuationSubring (v : PlaceA k K) : ValuationSubring K :=
  (placeValuation k K v).valuationSubring

/-- The global degree of a divisor. -/
noncomputable def deg (D : DivisorA k K) : ℤ :=
  D.sum fun v n => (n : ℤ) * (placeDegree k K v : ℤ)

/-- Product formula: the global degree of a principal divisor is zero. -/
theorem deg_principalDivisorA_eq_zero (x : Kˣ) :
    deg k K (principalDivisorA k K (Additive.ofMul x)) = 0 := by
  let Dfin := FractionalIdeal.principalDivisor
    (R := ringOfIntegers k K) (K := K) (Additive.ofMul x)
  let Dinf := FractionalIdeal.principalDivisor
    (R := infiniteIntegers k K) (K := K) (Additive.ofMul x)
  have hdiv : principalDivisorA k K (Additive.ofMul x) = Dfin.sumElim Dinf := by
    rw [Finsupp.sumElim_eq_add]
    rfl
  rw [deg, hdiv, Finsupp.sum_sumElim]
  change
    Dfin.sum (fun v n => n * (placeDegree k K (Sum.inl v) : ℤ)) +
      Dinf.sum (fun v n => n * (placeDegree k K (Sum.inr v) : ℤ)) = 0
  rw [finitePrincipalDegree_eq_intDegree_norm k K x,
    infinitePrincipalDegree_eq_neg_intDegree_norm k K x]
  exact add_neg_cancel _

/-- The support of a divisor. -/
def support (D : DivisorA k K) : Finset (PlaceA k K) := D.support

/-- A divisor is effective when all coefficients are nonnegative. -/
def IsEffective (D : DivisorA k K) : Prop :=
  ∀ v, 0 ≤ D v

omit [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] in
theorem deg_zero : deg k K (0 : DivisorA k K) = 0 := by
  simp [deg, placeDegree]

omit [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] in
theorem deg_add (D₁ D₂ : DivisorA k K) :
    deg k K (D₁ + D₂) = deg k K D₁ + deg k K D₂ := by
  classical
  simp [deg, Finsupp.sum_add_index, add_mul]

omit [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] in
theorem deg_neg (D : DivisorA k K) : deg k K (-D) = -deg k K D := by
  classical
  simp [deg, Finsupp.sum_neg_index, neg_mul]

omit [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] in
theorem deg_sub (D D' : DivisorA k K) :
    deg k K (D - D') = deg k K D - deg k K D' := by
  simp [deg_add, deg_neg, sub_eq_add_neg]

omit [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] in
theorem deg_nsmul {D : DivisorA k K} (n : ℕ) :
    deg k K (n • D) = (n : ℤ) * deg k K D := by
  induction n with
  | zero => simp [deg_zero]
  | succ n ih =>
      rw [succ_nsmul, deg_add, ih]
      simp only [Nat.cast_add, Nat.cast_one, one_mul, add_mul, add_comm]

omit [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] in
theorem deg_nsmul_effective {D : DivisorA k K} (n : ℕ) (_hD : IsEffective k K D) :
    deg k K (n • D) = (n : ℤ) * deg k K D :=
  deg_nsmul (k := k) (K := K) (D := D) n

omit [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] in
/-- Effective divisors have nonnegative degree. -/
theorem deg_nonneg {D : DivisorA k K} (hD : IsEffective k K D) :
    0 ≤ deg k K D := by
  classical
  exact Finsupp.sum_nonneg fun v _ =>
    mul_nonneg (hD v) (Int.natCast_nonneg (placeDegree k K v))

/-- An effective divisor of degree zero is the zero divisor. -/
theorem eq_zero_of_effective_deg_zero {D : DivisorA k K} (hD : IsEffective k K D)
    (hdeg : deg k K D = 0) : D = 0 := by
  classical
  rw [deg, Finsupp.sum] at hdeg
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ =>
    mul_nonneg (hD v) (Int.natCast_nonneg (placeDegree k K v)))).1 hdeg
  apply Finsupp.ext
  intro v
  simp only [Finsupp.zero_apply]
  by_cases hv : v ∈ D.support
  · have hmul := hall v hv
    have hplace : (placeDegree k K v : ℤ) ≠ 0 := by
      exact_mod_cast (placeDegree_pos k K v).ne'
    exact (mul_eq_zero.mp hmul).resolve_right hplace
  · simpa only [Finsupp.mem_support_iff, not_not] using hv

omit [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] in
theorem deg_single (v : PlaceA k K) (n : ℤ) :
    deg k K (Finsupp.single v n) = n * placeDegree k K v := by
  simp [deg, Finsupp.sum_single_index]

omit [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] in
/-- The degree map is monotone for the pointwise order on divisors. -/
theorem deg_mono {D D' : DivisorA k K} (h : D ≤ D') :
    deg k K D ≤ deg k K D' := by
  rw [← sub_nonneg, ← deg_sub]
  apply deg_nonneg k K
  intro v
  exact sub_nonneg.mpr (h v)

omit [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] in
/-- A nonpositive divisor has nonpositive degree. -/
theorem deg_nonpos {D : DivisorA k K} (hD : D ≤ 0) : deg k K D ≤ 0 := by
  simpa only [deg_zero] using deg_mono k K hD

omit [IsScalarTower k[X] k⟮X⟯ K] [FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] in
theorem le_iff_sub_effective {D D' : DivisorA k K} :
    D ≤ D' ↔ IsEffective k K (D' - D) := by
  simp only [Finsupp.le_def, IsEffective, Finsupp.sub_apply, sub_nonneg]

end FunctionField.Chart
