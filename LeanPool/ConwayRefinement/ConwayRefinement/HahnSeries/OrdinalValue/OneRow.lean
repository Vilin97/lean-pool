/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Irreducibility
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.NonpositiveCoefficientMap

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Domain

/-!
# The one-row irreducibles

The series

`a = Σ n : ℕ, t ^ (-1 / (n + 1))`

has support order type `ω`, with supremum zero approached from below. Berarducci, Theorem 10.5
therefore proves that both `a` and `a + 1` are irreducible over every characteristic-zero
coefficient field. The second series is the signed Hahn-series form of Conway's one-row omnific
integer `1 + Σ n, ω ^ (1 / (n + 1))`, discussed in LM24, Example 9.2.8.

## References

* A. Berarducci, *Factorization in generalized power series*, Trans. Amer. Math. Soc. 352
  (2000), 553–577, cited as [Ber00].
* S. L'Innocente, V. Mantova, *A factorisation theory for generalised power series and omnific
  integers*, Adv. Math. 442 (2024) 109513, cited as [LM24].
-/

universe v w

open scoped HahnSeries

public noncomputable section

namespace Berarducci.OneRow

variable {K : Type v} [Field K]

/-- The `n`-th exponent in the one-row series approaching zero from below. -/
def exponent (n : ℕ) : ℝ :=
  -(1 / (n + 1 : ℝ))

@[simp]
theorem exponent_apply (n : ℕ) : exponent n = -(1 / (n + 1 : ℝ)) :=
  (rfl)

private theorem exponent_strictMono : StrictMono exponent :=
  strictMono_nat_of_lt_succ fun n ↦ by
    rw [exponent_apply, exponent_apply]
    apply neg_lt_neg
    apply one_div_lt_one_div_of_lt
    · positivity
    · norm_num

/-- The order embedding enumerating the support of the one-row series. -/
def exponentEmbedding : ℕ ↪o ℝ :=
  OrderEmbedding.ofStrictMono exponent exponent_strictMono

@[simp]
theorem exponentEmbedding_apply (n : ℕ) : exponentEmbedding n = exponent n :=
  (rfl)

private def coefficientOne : K⟦ℕ⟧ where
  coeff _ := 1
  isPWO_support' := by
    simpa [Function.support] using Set.IsPWO.of_linearOrder (Set.univ : Set ℕ)

private theorem coefficientOne_support : (coefficientOne (K := K)).support = Set.univ := by
  ext n
  simp [coefficientOne]

/-- The coefficient-one nonpositive Hahn series `Σ n, t ^ (-1 / (n + 1))`. -/
def withoutConstant : Series K :=
  ⟨HahnSeries.embDomain exponentEmbedding (coefficientOne (K := K)), by
    rw [HahnSeries.mem_nonpositiveSubring,
      HahnSeries.support_embDomain, coefficientOne_support, Set.image_univ]
    rintro _ ⟨n, rfl⟩
    rw [exponentEmbedding_apply, exponent_apply]
    exact neg_nonpos.mpr (show 0 ≤ 1 / (n + 1 : ℝ) by positivity)⟩

/-- Every exponent displayed in the one-row series has coefficient one. -/
theorem withoutConstant_coeff_exponent (n : ℕ) :
    (withoutConstant (K := K) : K⟦ℝ⟧).coeff (exponent n) = 1 := by
  rw [withoutConstant, ← exponentEmbedding_apply, HahnSeries.embDomain_coeff]
  rfl

/-- The support of the one-row series is exactly its displayed exponent sequence. -/
theorem withoutConstant_support :
    (withoutConstant (K := K) : K⟦ℝ⟧).support = Set.range exponentEmbedding := by
  rw [withoutConstant, HahnSeries.support_embDomain,
    coefficientOne_support, Set.image_univ]

/-- Coefficient extension preserves the coefficient-one row. -/
theorem nonpositiveCoefficientMap_withoutConstant
    {E : Type w} [Field E] (f : K →+* E) :
    HahnSeries.Nonpositive.nonpositiveCoefficientMap f
        (withoutConstant (K := K)) =
      withoutConstant (K := E) := by
  apply Subtype.ext
  apply HahnSeries.coeff_injective
  funext x
  by_cases hx : x ∈ Set.range exponentEmbedding
  · obtain ⟨n, rfl⟩ := hx
    rw [HahnSeries.Nonpositive.coe_nonpositiveCoefficientMap]
    simp only [exponentEmbedding_apply, withoutConstant_coeff_exponent, map_one]
  · have hK : (withoutConstant (K := K) : K⟦ℝ⟧).coeff x = 0 := by
      rw [← not_ne_iff, ← HahnSeries.mem_support, withoutConstant_support]
      exact hx
    have hE : (withoutConstant (K := E) : E⟦ℝ⟧).coeff x = 0 := by
      rw [← not_ne_iff, ← HahnSeries.mem_support, withoutConstant_support]
      exact hx
    rw [HahnSeries.Nonpositive.coe_nonpositiveCoefficientMap, hK, map_zero, hE]

@[simp]
theorem withoutConstant_coeff_zero :
    (withoutConstant (K := K) : K⟦ℝ⟧).coeff 0 = 0 := by
  rw [← not_ne_iff, ← HahnSeries.mem_support, withoutConstant_support]
  rintro ⟨n, hn⟩
  have hneg : exponentEmbedding n < 0 := by
    rw [exponentEmbedding_apply, exponent_apply]
    exact neg_lt_zero.mpr (by positivity)
  exact hneg.ne hn

/-- The support of the one-row series has order type `ω`. -/
theorem withoutConstant_supportOrderType :
    (withoutConstant (K := K) : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 := by
  rw [HahnSeries.supportOrderType_eq_setOrderType]
  have e : (withoutConstant (K := K) : K⟦ℝ⟧).support ≃o ℕ :=
    (OrderIso.setCongr _ (Set.range exponentEmbedding)
      (withoutConstant_support (K := K))).trans exponentEmbedding.orderIso.symm
  exact (withoutConstant (K := K) : K⟦ℝ⟧).isPWO_support
    |>.orderType_eq_typeLT_of_orderIso e |>.trans Ordinal.type_nat_lt

private theorem withoutConstant_isLUB :
    IsLUB (withoutConstant (K := K) : K⟦ℝ⟧).support 0 := by
  rw [withoutConstant_support]
  constructor
  · rintro _ ⟨n, rfl⟩
    rw [exponentEmbedding_apply, exponent_apply]
    exact neg_nonpos.mpr (by positivity)
  · intro a ha
    by_contra hnot
    have haNeg : a < 0 := lt_of_not_ge hnot
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (neg_pos.mpr haNeg)
    have hle := ha (Set.mem_range_self n)
    rw [exponentEmbedding_apply, exponent_apply] at hle
    linarith

/-- The support supremum is zero and is not attained. -/
theorem withoutConstant_supportSup :
    HahnSeries.Nonpositive.supportSup (withoutConstant (K := K)) = 0 := by
  apply HahnSeries.Nonpositive.supportSup_eq_coe_iff.mpr
  refine ⟨?_, withoutConstant_isLUB (K := K)⟩
  intro hzero
  have hcoeff := withoutConstant_coeff_exponent (K := K) 0
  rw [hzero] at hcoeff
  change (0 : K) = 1 at hcoeff
  exact zero_ne_one hcoeff

/-- No strictly negative monomial divides the one-row series. -/
theorem negative_single_not_dvd_withoutConstant
    (gamma : ℝ) (hgamma : gamma < 0) :
    ¬ HahnSeries.Nonpositive.single gamma (1 : K) hgamma.le ∣
      withoutConstant (K := K) := by
  have hnotJ : withoutConstant (K := K) ∉
      HahnSeries.Nonpositive.negativeMonomialIdeal K := by
    rw [HahnSeries.Nonpositive.mem_negativeMonomialIdeal_iff_supportSup_lt_zero,
      withoutConstant_supportSup]
    exact lt_irrefl 0
  intro hdvd
  obtain ⟨c, hc⟩ := hdvd
  apply hnotJ
  rw [hc]
  apply Ideal.mul_mem_right c
  rw [HahnSeries.Nonpositive.mem_negativeMonomialIdeal_iff_supportSup_lt_zero,
    HahnSeries.Nonpositive.supportSup_single one_ne_zero]
  exact_mod_cast hgamma

/-- The one-row series with its final constant coefficient one. -/
def withConstant : Series K :=
  withoutConstant (K := K) + 1

/-- Coefficient extension preserves the constant-capped coefficient-one row. -/
theorem nonpositiveCoefficientMap_withConstant
    {E : Type w} [Field E] (f : K →+* E) :
    HahnSeries.Nonpositive.nonpositiveCoefficientMap f
        (withConstant (K := K)) =
      withConstant (K := E) := by
  rw [withConstant, withConstant, map_add, map_one,
    nonpositiveCoefficientMap_withoutConstant]

theorem withConstant_coeff_exponent (n : ℕ) :
    (withConstant (K := K) : K⟦ℝ⟧).coeff (exponent n) = 1 := by
  rw [withConstant, Subring.coe_add, HahnSeries.coeff_add,
    withoutConstant_coeff_exponent, show ((1 : Series K) : K⟦ℝ⟧) = 1 from rfl]
  have hne : exponent n ≠ 0 := by
    rw [exponent_apply]
    exact (neg_lt_zero.mpr (by positivity)).ne
  rw [HahnSeries.coeff_one, ite_eq_right hne, add_zero]

@[simp]
theorem withConstant_coeff_zero :
    (withConstant (K := K) : K⟦ℝ⟧).coeff 0 = 1 := by
  rw [withConstant, Subring.coe_add, HahnSeries.coeff_add,
    withoutConstant_coeff_zero]
  simp

/-- The constant coefficient of the capped row is one. -/
theorem withConstant_constantCoeff :
    HahnSeries.Nonpositive.constantCoeff (withConstant (K := K)) = 1 := by
  rw [HahnSeries.Nonpositive.constantCoeff_apply, withConstant_coeff_zero]

/-- The support of the constant-capped series is the one-row sequence followed by zero. -/
theorem withConstant_support :
    (withConstant (K := K) : K⟦ℝ⟧).support = Set.range exponentEmbedding ∪ {0} := by
  ext x
  by_cases hx : x = 0
  · subst x
    simp [withConstant_coeff_zero]
  · have hone : (1 : K⟦ℝ⟧).coeff x = 0 := by
      rw [HahnSeries.coeff_one, ite_eq_right hx]
    rw [HahnSeries.mem_support, withConstant, Subring.coe_add,
      HahnSeries.coeff_add, show ((1 : Series K) : K⟦ℝ⟧) = 1 from rfl,
      hone, add_zero, ← HahnSeries.mem_support, withoutConstant_support]
    simp [hx]

private theorem withoutConstant_supportBelow_one :
    HahnSeries.SupportBelow (withoutConstant (K := K) : K⟦ℝ⟧) 1 := by
  rw [HahnSeries.supportBelow_iff]
  intro i hi j hj
  rw [withoutConstant_support] at hi
  obtain ⟨n, rfl⟩ := hi
  have hj0 : j = 0 := by
    simpa [HahnSeries.support_one] using hj
  subst j
  rw [exponentEmbedding_apply, exponent_apply]
  exact neg_lt_zero.mpr (by positivity)

/-- The support of the constant-capped one-row series has order type `ω + 1`. -/
theorem withConstant_supportOrderType :
    (withConstant (K := K) : K⟦ℝ⟧).supportOrderType = Ordinal.omega0 + 1 := by
  apply (HahnSeries.supportOrderType_eq_add_iff _ _ _).mpr
  refine ⟨(withoutConstant (K := K) : K⟦ℝ⟧), 1,
    withoutConstant_supportBelow_one (K := K),
    withoutConstant_supportOrderType (K := K), ?_, ?_⟩
  · change (HahnSeries.C (1 : K)).supportOrderType = 1
    rw [HahnSeries.C_apply, HahnSeries.supportOrderType_single one_ne_zero]
  · rfl

/-- Berarducci's theorem makes both the one-row series and its constant-capped form irreducible. -/
theorem irreducible_withoutConstant_and_withConstant [CharZero K] :
    Irreducible (withoutConstant (K := K)) ∧
      Irreducible (withConstant (K := K)) := by
  apply Berarducci.irreducible_and_add_one_of_supportOrderType
  · exact negative_single_not_dvd_withoutConstant
  · exact Or.inl withoutConstant_supportOrderType

end Berarducci.OneRow
