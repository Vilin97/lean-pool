/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.Entropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Transfer -/

open scoped BigOperators

namespace BeyondBethe

/-- Interior probability vector.  Both strict inequalities are recorded to
avoid repeatedly deriving the upper one from dimension assumptions. -/
def IsInteriorProbabilityVector
    {ι : Type*} [Fintype ι] (p : ι → ℝ) : Prop :=
  IsProbabilityVector p ∧ ∀ i, 0 < p i ∧ p i < 1

theorem IsInteriorProbabilityVector.strict
    {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : IsInteriorProbabilityVector p) :
    IsStrictProbabilityVector p :=
  ⟨hp.1, fun i ↦ (hp.2 i).1⟩

/-- Second moment of a finite probability vector. -/
noncomputable def secondMoment
    {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  ∑ i, (p i) ^ 2

theorem secondMoment_nonneg
    {ι : Type*} [Fintype ι] (p : ι → ℝ) :
    0 ≤ secondMoment p := by
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

theorem secondMoment_lt_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ι → ℝ} (hp : IsInteriorProbabilityVector p) :
    secondMoment p < 1 := by
  have huniv : (Finset.univ : Finset ι).Nonempty := by
    by_contra hempty
    have hsum0 : ∑ i, p i = 0 := by
      rw [Finset.not_nonempty_iff_eq_empty.mp hempty]
      simp
    linarith [hp.1.sum_eq_one]
  rw [← hp.1.sum_eq_one]
  apply Finset.sum_lt_sum
  · intro i _
    nlinarith [mul_nonneg (hp.1.nonnegative i)
      (sub_nonneg.mpr (hp.1.le_one i))]
  · obtain ⟨i, hi⟩ := huniv
    refine ⟨i, hi, ?_⟩
    nlinarith [hp.2 i |>.1, hp.2 i |>.2]

theorem coordinate_le_sqrt_secondMoment
    {ι : Type*} [Fintype ι]
    {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (i : ι) :
    p i ≤ Real.sqrt (secondMoment p) := by
  have hs2 : (p i) ^ 2 ≤ secondMoment p := by
    rw [secondMoment]
    exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (p j)) (Finset.mem_univ i)
  exact (Real.le_sqrt (hp i) (secondMoment_nonneg p)).2 hs2

/-- Finite-dimensional monotonicity of `ell_p` norms in the exact form used
in the proof of paper Lemma 15. -/
theorem sum_pow_le_sqrt_secondMoment_pow
    {ι : Type*} [Fintype ι]
    {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) {k : ℕ} (hk : 2 ≤ k) :
    ∑ i, (p i) ^ k ≤ (Real.sqrt (secondMoment p)) ^ k := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hcoord : ∀ i, p i ≤ Real.sqrt (secondMoment p) :=
    coordinate_le_sqrt_secondMoment hp
  calc
    ∑ i, (p i) ^ (2 + t)
        = ∑ i, (p i) ^ 2 * (p i) ^ t := by
          apply Finset.sum_congr rfl
          intro i _
          rw [pow_add]
    _ ≤ ∑ i, (p i) ^ 2 * (Real.sqrt (secondMoment p)) ^ t := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (hp i) (hcoord i) t) (sq_nonneg (p i))
    _ = secondMoment p * (Real.sqrt (secondMoment p)) ^ t := by
          rw [← Finset.sum_mul, secondMoment]
    _ = (Real.sqrt (secondMoment p)) ^ (2 + t) := by
          rw [pow_add, Real.sq_sqrt (secondMoment_nonneg p)]

/-- Product of the complementary coordinates of a row. -/
noncomputable def complementProduct
    {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  ∏ i, (1 - p i)

theorem complementProduct_pos
    {ι : Type*} [Fintype ι]
    {p : ι → ℝ} (hp : IsInteriorProbabilityVector p) :
    0 < complementProduct p := by
  rw [complementProduct]
  exact Finset.prod_pos fun i _ ↦ sub_pos.mpr (hp.2 i).2

/-- The logarithmic estimate at the heart of the row-sum bound in paper
Lemma 15. -/
theorem neg_log_complementProduct_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ι → ℝ} (hp : IsInteriorProbabilityVector p) :
    -Real.log (complementProduct p) ≤
      1 - Real.log (1 - secondMoment p) := by
  let a : ℝ := Real.sqrt (secondMoment p)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha_sq : a ^ 2 = secondMoment p := Real.sq_sqrt (secondMoment_nonneg p)
  have ha1 : a < 1 := by
    nlinarith [secondMoment_lt_one hp]
  have hpabs : ∀ i, |p i| < 1 := by
    intro i
    rw [abs_of_pos (hp.2 i).1]
    exact (hp.2 i).2
  have hleft : HasSum
      (fun n : ℕ => ∑ i, (p i) ^ (n + 1) / ((n : ℝ) + 1))
      (∑ i, -Real.log (1 - p i)) := by
    classical
    have hfinite : ∀ s : Finset ι, HasSum
        (fun n : ℕ => ∑ i ∈ s, (p i) ^ (n + 1) / ((n : ℝ) + 1))
        (∑ i ∈ s, -Real.log (1 - p i)) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih =>
          have hsingle := Real.hasSum_pow_div_log_of_abs_lt_one (hpabs i)
          simpa [Finset.sum_insert hi] using hsingle.add ih
    simpa using hfinite Finset.univ
  have haabs : |a| < 1 := by simpa [abs_of_nonneg ha0]
  have haSeries := Real.hasSum_pow_div_log_of_abs_lt_one haabs
  have hpoint := hasSum_ite_eq (0 : ℕ) (1 - a)
  have hright : HasSum
      (fun n : ℕ =>
        a ^ (n + 1) / ((n : ℝ) + 1) + if n = 0 then 1 - a else 0)
      (-Real.log (1 - a) + (1 - a)) := by
    exact haSeries.add hpoint
  have hterm : ∀ n : ℕ,
      (∑ i, (p i) ^ (n + 1) / ((n : ℝ) + 1)) ≤
        a ^ (n + 1) / ((n : ℝ) + 1) + if n = 0 then 1 - a else 0 := by
    intro n
    cases n with
    | zero => simp [hp.1.sum_eq_one]
    | succ n =>
        have hk : 2 ≤ n.succ + 1 := by omega
        have hpow := sum_pow_le_sqrt_secondMoment_pow hp.1.nonnegative hk
        change (∑ i, (p i) ^ (n.succ + 1) / ((n.succ : ℝ) + 1)) ≤ _
        rw [← Finset.sum_div]
        simp only [Nat.succ_ne_zero, ↓reduceIte, add_zero]
        exact div_le_div_of_nonneg_right (by simpa [a] using hpow)
          (by positivity)
  have hseriesBound := hleft.summable.tsum_le_tsum hterm hright.summable
  rw [hleft.tsum_eq, hright.tsum_eq] at hseriesBound
  have halog : Real.log (1 + a) ≤ a := by
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + a)
    linarith
  have honeSub : 0 < 1 - a := sub_pos.mpr ha1
  have honeAdd : 0 < 1 + a := by linarith
  have hlogFactor :
      Real.log (1 - secondMoment p) =
        Real.log (1 - a) + Real.log (1 + a) := by
    rw [← Real.log_mul honeSub.ne' honeAdd.ne']
    congr 1
    nlinarith [ha_sq]
  have hlogBound :
      -Real.log (1 - a) + (1 - a) ≤
        1 - Real.log (1 - secondMoment p) := by
    rw [hlogFactor]
    linarith
  have hsumLog :
      -Real.log (complementProduct p) =
        ∑ i, -Real.log (1 - p i) := by
    rw [complementProduct, Real.log_prod]
    · rw [Finset.sum_neg_distrib]
    · intro i _
      exact (sub_pos.mpr (hp.2 i).2).ne'
  rw [hsumLog]
  exact hseriesBound.trans hlogBound

/-- Exponentiating the preceding logarithmic estimate yields the product
bound used in paper Lemma 15. -/
theorem exp_neg_one_mul_one_sub_secondMoment_le_complementProduct
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ι → ℝ} (hp : IsInteriorProbabilityVector p) :
    Real.exp (-1) * (1 - secondMoment p) ≤ complementProduct p := by
  have hd : 0 < 1 - secondMoment p := sub_pos.mpr (secondMoment_lt_one hp)
  have hq : 0 < complementProduct p := complementProduct_pos hp
  have hlog := neg_log_complementProduct_le hp
  have hlog' : -1 + Real.log (1 - secondMoment p) ≤
      Real.log (complementProduct p) := by
    linarith
  have hexp := Real.exp_le_exp.mpr hlog'
  rw [Real.exp_add, Real.exp_log hd, Real.exp_log hq] at hexp
  exact hexp

/-- Elementary product inequality
`1 - ∑ x_i ≤ ∏ (1 - x_i)` for nonnegative numbers with sum at most one. -/
theorem one_sub_sum_le_prod_one_sub
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hsum : ∑ i ∈ s, x i ≤ 1) :
    1 - ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 - x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have ha0 : 0 ≤ x a := hx a (Finset.mem_insert_self a s)
      have hxs : ∀ i ∈ s, 0 ≤ x i :=
        fun i hi ↦ hx i (Finset.mem_insert_of_mem hi)
      have hs0 : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg hxs
      have hsle : ∑ i ∈ s, x i ≤ 1 := by
        rw [Finset.sum_insert ha] at hsum
        linarith
      have hale : x a ≤ 1 := by
        rw [Finset.sum_insert ha] at hsum
        linarith
      have hih := ih hxs hsle
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hmul := mul_le_mul_of_nonneg_left hih (sub_nonneg.mpr hale)
      nlinarith [mul_nonneg ha0 hs0]

/-- Product of all complementary coordinates except `j`. -/
noncomputable def productExcept
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (j : ι) : ℝ :=
  ∏ k ∈ Finset.univ.erase j, (1 - p k)

theorem self_le_productExcept
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ι → ℝ} (hp : IsProbabilityVector p) (j : ι) :
    p j ≤ productExcept p j := by
  have hsum : ∑ k ∈ Finset.univ.erase j, p k = 1 - p j := by
    have htotal := hp.sum_eq_one
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)] at htotal
    linarith
  have hprod := one_sub_sum_le_prod_one_sub
    (Finset.univ.erase j) p
    (fun k _ ↦ hp.nonnegative k)
    (by rw [hsum]; linarith [hp.nonnegative j])
  change 1 - ∑ k ∈ Finset.univ.erase j, p k ≤ productExcept p j at hprod
  rw [hsum] at hprod
  linarith

theorem productExcept_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ι → ℝ} (hp : IsInteriorProbabilityVector p) (j : ι) :
    0 < productExcept p j := by
  rw [productExcept]
  exact Finset.prod_pos fun k _ ↦ sub_pos.mpr (hp.2 k).2

theorem complementProduct_eq_mul_productExcept
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (j : ι) :
    complementProduct p = (1 - p j) * productExcept p j := by
  rw [complementProduct, productExcept]
  exact (Finset.mul_prod_erase Finset.univ (fun k ↦ 1 - p k)
    (Finset.mem_univ j)).symm

/-- Transfer coordinate `U_j` from paper (37). -/
noncomputable def transferU
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ℝ) (p : ι → ℝ) (j : ι) : ℝ :=
  (p j) ^ (1 + τ) / productExcept p j

theorem transferU_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {τ : ℝ} {p : ι → ℝ} (hp : IsInteriorProbabilityVector p) (j : ι) :
    0 < transferU τ p j := by
  exact div_pos (Real.rpow_pos_of_pos (hp.2 j).1 _) (productExcept_pos hp j)

theorem transferU_le_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {τ : ℝ} (hτ : 0 ≤ τ) {p : ι → ℝ}
    (hp : IsInteriorProbabilityVector p) (j : ι) :
    transferU τ p j ≤ 1 := by
  have hpow : (p j) ^ (1 + τ) ≤ p j := by
    have h := Real.rpow_le_rpow_of_exponent_ge'
      (hp.1.nonnegative j) (hp.2 j).2.le (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith : (1 : ℝ) ≤ 1 + τ)
    simpa using h
  have hnum : (p j) ^ (1 + τ) ≤ productExcept p j :=
    hpow.trans (self_le_productExcept hp.1 j)
  rw [transferU, div_le_one (productExcept_pos hp j)]
  exact hnum

theorem transferU_eq_div_complementProduct
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {τ : ℝ} {p : ι → ℝ} (hp : IsInteriorProbabilityVector p) (j : ι) :
    transferU τ p j =
      (p j) ^ (1 + τ) * (1 - p j) / complementProduct p := by
  rw [transferU, complementProduct_eq_mul_productExcept p j]
  field_simp [(sub_pos.mpr (hp.2 j).2).ne', (productExcept_pos hp j).ne']

/-- The full row-sum conclusion of paper Lemma 15. -/
theorem sum_transferU_le_exp_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {τ : ℝ} (hτ : 0 ≤ τ) {p : ι → ℝ}
    (hp : IsInteriorProbabilityVector p) :
    ∑ j, transferU τ p j ≤ Real.exp 1 := by
  have hq : 0 < complementProduct p := complementProduct_pos hp
  have hpoint : ∀ j,
      transferU τ p j ≤ p j * (1 - p j) / complementProduct p := by
    intro j
    rw [transferU_eq_div_complementProduct hp j]
    have hpow : (p j) ^ (1 + τ) ≤ p j := by
      have h := Real.rpow_le_rpow_of_exponent_ge'
        (hp.1.nonnegative j) (hp.2 j).2.le (by norm_num : (0 : ℝ) ≤ 1)
        (by linarith : (1 : ℝ) ≤ 1 + τ)
      simpa using h
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpow (sub_nonneg.mpr (hp.1.le_one j))) hq.le
  calc
    ∑ j, transferU τ p j
        ≤ ∑ j, p j * (1 - p j) / complementProduct p :=
          Finset.sum_le_sum fun j _ ↦ hpoint j
    _ = (1 - secondMoment p) / complementProduct p := by
          rw [← Finset.sum_div]
          simp_rw [mul_sub, mul_one]
          rw [Finset.sum_sub_distrib, hp.1.sum_eq_one, secondMoment]
          simp only [pow_two]
    _ ≤ Real.exp 1 := by
          rw [div_le_iff₀ hq]
          have hbase :=
            exp_neg_one_mul_one_sub_secondMoment_le_complementProduct hp
          have hexppos : 0 < Real.exp 1 := Real.exp_pos 1
          have hscaled := mul_le_mul_of_nonneg_left hbase hexppos.le
          have hexpinv : Real.exp 1 * Real.exp (-1) = 1 := by
            rw [← Real.exp_add]
            norm_num
          calc
            1 - secondMoment p =
                Real.exp 1 * (Real.exp (-1) * (1 - secondMoment p)) := by
                  rw [← mul_assoc, hexpinv, one_mul]
            _ ≤ Real.exp 1 * complementProduct p := hscaled

end BeyondBethe
