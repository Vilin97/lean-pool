/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.NormalForm

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Domain

/-!
# A principal Hahn series approaching exponent zero

This module provides the shared nondegenerate fixture

```
∑ n : ℕ, t ^ (-1 / (n + 1)).
```

Its support has ordinary order type `ω`, is cofinal in zero, and does not contain zero. Thus its
support supremum is an unattained least upper bound, and the series is principal in the sense of
LM24. API-client modules use these proved properties to test normal forms, truncation bounds,
the negative-monomial ideal, and multiplicativity without duplicating the series.

This is shared example infrastructure for the checks, not part of the mathematical API.
-/

public noncomputable section

namespace Tests

open scoped HahnSeries NatOrdinal

/-- The coefficient-one Hahn series on `ℕ`. -/
def natOnes : ℚ⟦ℕ⟧ where
  coeff _ := 1
  isPWO_support' := by
    simpa [Function.support] using Set.IsPWO.of_linearOrder (Set.univ : Set ℕ)

/-- Every coefficient of `natOnes` is one. -/
@[simp]
theorem natOnes_coeff (n : ℕ) : natOnes.coeff n = 1 :=
  (rfl)

/-- The support of `natOnes` is all of `ℕ`. -/
@[simp]
theorem natOnes_support : natOnes.support = Set.univ := by
  ext n
  simp [HahnSeries.mem_support]

private theorem approachZero_strictMono :
    StrictMono (fun n : ℕ ↦ -(1 / (n + 1 : ℝ))) :=
  strictMono_nat_of_lt_succ fun n ↦ by
    apply neg_lt_neg
    apply one_div_lt_one_div_of_lt
    · positivity
    · norm_num

/-- The order embedding `n ↦ -1/(n+1)`. -/
def approachZeroEmbedding : ℕ ↪o ℝ :=
  OrderEmbedding.ofStrictMono _ approachZero_strictMono

/-- Evaluation of the exponent embedding used by `approachZero`. -/
@[simp]
theorem approachZeroEmbedding_apply (n : ℕ) :
    approachZeroEmbedding n = -(1 / (n + 1 : ℝ)) :=
  (rfl)

/-- The coefficient-one series on the support `{-1/(n+1) | n ∈ ℕ}`. -/
def approachZero : ℚ⟦ℝ⟧ :=
  HahnSeries.embDomain approachZeroEmbedding natOnes

/-- The coefficient at every embedded exponent is one. -/
theorem approachZero_coeff_embedding (n : ℕ) :
    approachZero.coeff (approachZeroEmbedding n) = 1 := by
  rw [approachZero, HahnSeries.embDomain_coeff, natOnes_coeff]

/-- The support of `approachZero` is exactly the range of its exponent embedding. -/
theorem approachZero_support :
    approachZero.support = Set.range approachZeroEmbedding := by
  rw [approachZero, HahnSeries.support_embDomain, natOnes_support,
    Set.image_univ]

/-- `approachZero` regarded as a nonpositive Hahn series. -/
def approachZeroNonpositive : HahnSeries.Nonpositive ℝ ℚ :=
  ⟨approachZero, by
    rw [HahnSeries.mem_nonpositiveSubring, approachZero_support]
    rintro _ ⟨n, rfl⟩
    exact neg_nonpos.mpr (by
      change 0 ≤ 1 / (n + 1 : ℝ)
      positivity)⟩

/-- Coercing `approachZeroNonpositive` recovers the underlying real Hahn series. -/
@[simp]
theorem coe_approachZeroNonpositive :
    (approachZeroNonpositive : ℚ⟦ℝ⟧) = approachZero :=
  (rfl)

/-- The nonpositive `approachZero` series is nonzero. -/
theorem approachZero_ne_zero : approachZeroNonpositive ≠ 0 := by
  intro hzero
  have hval := congrArg Subtype.val hzero
  change approachZero = (0 : ℚ⟦ℝ⟧) at hval
  have hmem : approachZeroEmbedding 0 ∈ approachZero.support := by
    rw [approachZero_support]
    exact Set.mem_range_self 0
  exact (HahnSeries.support_nonempty_iff.mp ⟨_, hmem⟩) hval

private theorem approachZero_isLUB : IsLUB approachZero.support 0 := by
  rw [approachZero_support]
  constructor
  · rintro _ ⟨n, rfl⟩
    exact neg_nonpos.mpr (by
      change 0 ≤ 1 / (n + 1 : ℝ)
      positivity)
  · intro a ha
    by_contra hnot
    have haNeg : a < 0 := lt_of_not_ge hnot
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (neg_pos.mpr haNeg)
    have hmem : approachZeroEmbedding n ∈ Set.range approachZeroEmbedding := ⟨n, rfl⟩
    have hle := ha hmem
    change -(1 / (n + 1 : ℝ)) ≤ a at hle
    linarith

/-- The support supremum of `approachZero` is zero, although zero is not in its support. -/
theorem approachZero_supportSup :
    HahnSeries.Nonpositive.supportSup approachZeroNonpositive = 0 := by
  apply HahnSeries.Nonpositive.supportSup_eq_coe_iff.mpr
  exact ⟨approachZero_ne_zero, approachZero_isLUB⟩

/-- The supremum zero of `approachZero` is not attained by its support. -/
theorem zero_not_mem_approachZero_support : 0 ∉ approachZero.support := by
  rw [approachZero_support]
  rintro ⟨n, hn⟩
  have hneg : approachZeroEmbedding n < 0 := by
    change -(1 / (n + 1 : ℝ)) < 0
    exact neg_lt_zero.mpr (by positivity)
  exact hneg.ne hn

/-- The support of `approachZero` has ordinary order type `ω`. -/
theorem approachZero_supportOrderType :
    approachZero.supportOrderType = Ordinal.omega0 := by
  rw [HahnSeries.supportOrderType_eq_setOrderType]
  have e : approachZero.support ≃o ℕ :=
    (Set.orderIsoOfEq approachZero.support (Set.range approachZeroEmbedding)
      approachZero_support).trans approachZeroEmbedding.orderIso.symm
  exact approachZero.isPWO_support.orderType_eq_typeLT_of_orderIso e |>.trans
    Ordinal.type_nat_lt

/-- The Hahn-series degree of `approachZero` is one. -/
theorem approachZero_degree_eq_one :
    (approachZeroNonpositive : ℚ⟦ℝ⟧).degree =
      (1 : WithBot NatOrdinal) := by
  rw [HahnSeries.degree_eq_cantorDegree, coe_approachZeroNonpositive,
    approachZero_supportOrderType, Ordinal.cantorDegree_omega]

/-- `approachZero` is a nonconstant principal series of support order type `ω`. -/
theorem approachZero_isPrincipal :
    HahnSeries.Nonpositive.IsPrincipal approachZeroNonpositive := by
  rw [HahnSeries.Nonpositive.isPrincipal_iff]
  constructor
  · rw [HahnSeries.isWeaklyPrincipal_iff, coe_approachZeroNonpositive,
      approachZero_supportOrderType]
    simpa using Ordinal.isAdditivelyPrincipal_omega0_opow 1
  · exact approachZero_supportSup

end Tests
