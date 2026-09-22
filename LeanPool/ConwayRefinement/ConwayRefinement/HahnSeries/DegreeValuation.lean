/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Valuation.MaxAddDegree
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Nonpositive
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrderType
public import Mathlib.Basic.Real.Basic

/-!
# The degree valuation on nonpositive real Hahn series

Hahn-series degree on `K((ℝ^{≤0}))` is a max-additive degree over every nontrivial coefficient
ring: the degree of a sum is at most the larger degree, and the degree of a product is at most
the Hessenberg sum of the degrees, because the support of a product lies in the sumset of the
supports and the order type of a sumset is at most the Hessenberg product of the order types
(`HahnSeries.degree_mul_le`, LM24, Corollary 3.1.2). The degree is separated: only `0` has
degree `⊥`.

Exact multiplicativity of the degree, LM24, Theorem D, holds over a field of characteristic zero;
it is recorded separately as an `IsMultiplicative` instance on `degreeValuation K` and is not
needed for the valuation itself.
-/

universe v

public noncomputable section

namespace HahnSeries.Nonpositive

variable (K : Type v) [CommRing K] [Nontrivial K]

/-- Hahn-series degree on `K((ℝ^{≤0}))` as a max-additive valuation: the value of `b` is the
leading Cantor exponent of the order type of its support, with `⊥` on `0`. -/
def degreeValuation : MaxAddDegree (Nonpositive ℝ K) NatOrdinal where
  toFun b := (b : K⟦ℝ⟧).degree
  map_zero' := by simp
  map_one_le_zero' := by
    change ((1 : Nonpositive ℝ K) : K⟦ℝ⟧).degree ≤ 0
    apply le_of_eq
    rw [HahnSeries.degree_eq_zero]
    exact ⟨one_ne_zero,
      Set.Finite.subset (Set.finite_singleton (0 : ℝ)) HahnSeries.support_single_subset⟩
  map_neg' b := HahnSeries.degree_neg (b : K⟦ℝ⟧)
  map_add_le_max' b c := HahnSeries.degree_add_le _ _
  map_mul_le_add' b c := HahnSeries.degree_mul_le _ _

variable {K}

/-- The degree valuation has Hahn-series degree as its value. -/
@[simp]
theorem degreeValuation_apply (b : Nonpositive ℝ K) :
    degreeValuation K b = (b : K⟦ℝ⟧).degree :=
  (rfl)

variable (K)

/-- The degree valuation is separated: only `0` has degree `⊥`. -/
theorem degreeValuation_isSeparated : (degreeValuation K).IsSeparated := by
  rw [MaxAddDegree.isSeparated_iff]
  intro b
  rw [degreeValuation_apply, HahnSeries.degree_eq_bot]
  simp

variable {K}

/-- A unit of the nonpositive Hahn-series ring has degree zero whenever degree is exactly
multiplicative. -/
theorem degree_eq_zero_of_isUnit
    (hmul : ∀ b c : Nonpositive ℝ K,
      ((b * c : Nonpositive ℝ K) : K⟦ℝ⟧).degree =
        (b : K⟦ℝ⟧).degree + (c : K⟦ℝ⟧).degree)
    {b : Nonpositive ℝ K} (hb : IsUnit b) :
    (b : K⟦ℝ⟧).degree = 0 := by
  let c : Nonpositive ℝ K := ↑hb.unit⁻¹
  have hc : c ≠ 0 := Units.ne_zero hb.unit⁻¹
  have hbDegreeNonneg : 0 ≤ (b : K⟦ℝ⟧).degree :=
    HahnSeries.zero_le_degree_of_ne_zero (by
      intro hzero
      exact hb.ne_zero (Subtype.ext hzero))
  have hcDegreeNonneg : 0 ≤ (c : K⟦ℝ⟧).degree :=
    HahnSeries.zero_le_degree_of_ne_zero (by
      intro hzero
      exact hc (Subtype.ext hzero))
  have hdegreeOne : (((1 : Nonpositive ℝ K) : K⟦ℝ⟧).degree) = 0 := by
    rw [HahnSeries.degree_eq_zero]
    exact ⟨one_ne_zero,
      Set.Finite.subset (Set.finite_singleton (0 : ℝ)) HahnSeries.support_single_subset⟩
  have hdegree := hmul b c
  have hproduct : b * c = 1 := hb.mul_val_inv
  rw [hproduct, hdegreeOne] at hdegree
  have hsum :
      (b : K⟦ℝ⟧).degree + (c : K⟦ℝ⟧).degree = 0 := hdegree.symm
  exact le_antisymm
    (calc
      (b : K⟦ℝ⟧).degree ≤
          (b : K⟦ℝ⟧).degree + (c : K⟦ℝ⟧).degree := by
        simpa using add_le_add_right hcDegreeNonneg (b : K⟦ℝ⟧).degree
      _ = 0 := hsum)
    hbDegreeNonneg

end HahnSeries.Nonpositive
