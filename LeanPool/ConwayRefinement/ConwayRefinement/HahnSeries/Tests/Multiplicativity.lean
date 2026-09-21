/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Multiplicativity

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Degree.Statements.Degree

/-!
# API checks for LM24 degree multiplicativity

The zero-factor certificate exposes the missing nonzero hypothesis in the printed first case of
LM24, Lemma 3.4.2: the empty support is strictly above every cutoff, but the claimed strict degree
inequality becomes `⊥ < ⊥`.

The nonzero monomial certificate exercises the repaired strict-support case at a genuinely
separated cutoff. A separate endpoint theorem shows that replacing `Set.Ioi` by `Set.Ici` would
incorrectly admit the monomial at its own exponent when its degree is zero.

The final two certificates exercise both the parameterized reduction in LM24, Proposition 3.4.3
and the characteristic-zero theorem on the same non-weakly-principal series.
-/

public noncomputable section

namespace Tests

open scoped HahnSeries

/-- The coefficient-one monomial at exponent `-1`, regarded as nonpositive. -/
def negativeOneMonomial : HahnSeries.Nonpositive ℝ ℚ :=
  HahnSeries.Nonpositive.single (-1) 1 (by norm_num)

@[simp]
theorem negativeOneMonomial_coe :
    (negativeOneMonomial : ℚ⟦ℝ⟧) = HahnSeries.single (-1) 1 :=
  by
    simpa only [negativeOneMonomial] using
      HahnSeries.Nonpositive.coe_single (-1 : ℝ) (1 : ℚ) (by norm_num)

theorem negativeOneMonomial_ne_zero : negativeOneMonomial ≠ 0 := by
  intro hzero
  have hcoeff := congrArg
    (fun x : HahnSeries.Nonpositive ℝ ℚ ↦ (x : ℚ⟦ℝ⟧).coeff (-1)) hzero
  norm_num [negativeOneMonomial] at hcoeff

/-- The monomial support lies strictly above the cutoff `-2`. -/
theorem negativeOneMonomial_support_subset_Ioi_neg_two :
    (negativeOneMonomial : ℚ⟦ℝ⟧).support ⊆ Set.Ioi (-2) := by
  intro i hi
  rw [negativeOneMonomial_coe] at hi
  have hi' : i = -1 := HahnSeries.eq_of_mem_support_single hi
  rw [hi']
  norm_num

/-- Repaired LM24, Lemma 3.4.2(1) applies to a nonzero separated monomial. -/
theorem strictSupport_truncation_degree_lt :
    (HahnSeries.truncLE (-2)
      (((1 : HahnSeries.Nonpositive ℝ ℚ) * negativeOneMonomial :
        HahnSeries.Nonpositive ℝ ℚ) : ℚ⟦ℝ⟧)).degree <
      ((1 : HahnSeries.Nonpositive ℝ ℚ) : ℚ⟦ℝ⟧).degree +
        (negativeOneMonomial : ℚ⟦ℝ⟧).degree := by
  exact HahnSeries.Nonpositive.degree_truncLE_mul_lt
    HahnSeries.Nonpositive.isPrincipal_one negativeOneMonomial_ne_zero
      (Or.inl negativeOneMonomial_support_subset_Ioi_neg_two)

/-- At its own exponent, the monomial support is weakly but not strictly above the cutoff. -/
theorem negativeOneMonomial_endpoint_separator :
    (negativeOneMonomial : ℚ⟦ℝ⟧).support ⊆ Set.Ici (-1) ∧
      ¬(negativeOneMonomial : ℚ⟦ℝ⟧).support ⊆ Set.Ioi (-1) := by
  constructor
  · intro i hi
    rw [negativeOneMonomial_coe] at hi
    rw [HahnSeries.eq_of_mem_support_single hi]
    exact (le_rfl : (-1 : ℝ) ≤ -1)
  · intro h
    have hmem :
        (-1 : ℝ) ∈ (negativeOneMonomial : ℚ⟦ℝ⟧).support := by
      rw [negativeOneMonomial_coe, HahnSeries.support_single_of_ne one_ne_zero]
      simp
    exact (lt_irrefl (-1 : ℝ)) (h hmem)

/-- Counterexample to the first case of the printed LM24, Lemma 3.4.2 when `c = 0`. -/
theorem printed_degree_truncLE_mul_lt_case_one_zero_counterexample (x : ℝ) :
    ((0 : HahnSeries.Nonpositive ℝ ℚ) : ℚ⟦ℝ⟧).support ⊆ Set.Ioi x ∧
      ¬(HahnSeries.truncLE x
        (((1 : HahnSeries.Nonpositive ℝ ℚ) * 0 :
          HahnSeries.Nonpositive ℝ ℚ) : ℚ⟦ℝ⟧)).degree <
        ((1 : HahnSeries.Nonpositive ℝ ℚ) : ℚ⟦ℝ⟧).degree +
          ((0 : HahnSeries.Nonpositive ℝ ℚ) : ℚ⟦ℝ⟧).degree := by
  constructor
  · simp
  · simp

/-- A two-term nonpositive series whose support order type is two. -/
def twoTermNonprincipal : HahnSeries.Nonpositive ℝ ℚ :=
  negativeOneMonomial + 1

private theorem twoTermNonprincipal_coe :
    (twoTermNonprincipal : ℚ⟦ℝ⟧) =
      HahnSeries.single (-1) 1 + HahnSeries.single 0 1 := by
  ext i
  simp [twoTermNonprincipal, negativeOneMonomial]

theorem twoTermNonprincipal_supportOrderType :
    (twoTermNonprincipal : ℚ⟦ℝ⟧).supportOrderType = 2 := by
  have hbelow :
      HahnSeries.SupportBelow
        (HahnSeries.single (-1 : ℝ) (1 : ℚ))
        (HahnSeries.single 0 (1 : ℚ)) := by
    rw [HahnSeries.supportBelow_iff]
    intro i hi j hj
    rw [HahnSeries.eq_of_mem_support_single hi,
      HahnSeries.eq_of_mem_support_single hj]
    norm_num
  rw [twoTermNonprincipal_coe]
  have htype := (HahnSeries.supportOrderType_eq_add_iff
    (HahnSeries.single (-1 : ℝ) (1 : ℚ) + HahnSeries.single 0 1)
      1 1).mpr
        ⟨HahnSeries.single (-1) 1, HahnSeries.single 0 1, hbelow,
          HahnSeries.supportOrderType_single one_ne_zero,
          HahnSeries.supportOrderType_single one_ne_zero,
          rfl⟩
  calc
    (HahnSeries.single (-1 : ℝ) (1 : ℚ) +
        HahnSeries.single 0 1).supportOrderType =
        (1 : Ordinal) + 1 := htype
    _ = 2 := by norm_num

/-- The two-term series is not weakly principal; support order type two is not a power of `ω`. -/
theorem twoTermNonprincipal_not_isWeaklyPrincipal :
    ¬HahnSeries.IsWeaklyPrincipal (twoTermNonprincipal : ℚ⟦ℝ⟧) := by
  intro hprincipal
  have hp :=
    (Ordinal.isAdditivelyPrincipal_iff_ne_zero_and_isPrincipal_add.mp
      (HahnSeries.isWeaklyPrincipal_iff.mp hprincipal)).2
  rw [twoTermNonprincipal_supportOrderType] at hp
  have hone : (1 : Ordinal) < 2 := by norm_num
  have hfalse := hp hone hone
  norm_num at hfalse

/-- The parameterized LM24, Proposition 3.4.3 applies beyond weakly principal factors. -/
theorem twoTermNonprincipal_square_degree_of_orderTypeMultiplicative
    (h :
      HahnSeries.Nonpositive.OrderTypeMultiplicativeOnWeaklyPrincipal ℚ) :
    ((twoTermNonprincipal * twoTermNonprincipal :
      HahnSeries.Nonpositive ℝ ℚ) : ℚ⟦ℝ⟧).degree =
      (twoTermNonprincipal : ℚ⟦ℝ⟧).degree +
        (twoTermNonprincipal : ℚ⟦ℝ⟧).degree :=
  HahnSeries.Nonpositive.degree_mul_of_orderTypeMultiplicativeOnWeaklyPrincipal
    h twoTermNonprincipal twoTermNonprincipal

/-- LM24, Theorem D applies beyond the weakly-principal input class used in its Berarducci
prerequisite. -/
theorem twoTermNonprincipal_square_degree :
    ((twoTermNonprincipal * twoTermNonprincipal :
      HahnSeries.Nonpositive ℝ ℚ) : ℚ⟦ℝ⟧).degree =
      (twoTermNonprincipal : ℚ⟦ℝ⟧).degree +
        (twoTermNonprincipal : ℚ⟦ℝ⟧).degree :=
  HahnSeries.Nonpositive.degree_mul _ _

end Tests
