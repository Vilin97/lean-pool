/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import LeanPool.LeanModularForms.Modularforms.SummableLems

/-! # MultipliableLems -/


@[expose] public section

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open ArithmeticFunction


/-this is being PRd-/
lemma Complex.summable_nat_multipliable_one_add (f : ℕ → ℂ) (hf : Summable f) :
    Multipliable (fun n : ℕ => 1 + f n) := by
  apply Complex.multipliable_of_summable_log
  apply Complex.summable_log_one_add_of_summable hf


theorem term_ne_zero (z : ℍ) (n : ℕ) : 1 -cexp (2 * ↑π * Complex.I * (↑n + 1) * ↑z) ≠ 0 := by
  rw [@sub_ne_zero]
  intro h
  have := exp_upperHalfPlane_lt_one_nat z n
  rw [← h] at this
  simp only [norm_one, lt_self_iff_false] at *

theorem ball_pow_ne_1 (x : ℂ) (hx : x ∈ ball 0 1) (n : ℕ) : 1 + (fun n ↦ -x ^ (n + 1)) n ≠ 0 := by
  simp only [mem_ball, dist_zero_right] at *
  rw [← sub_eq_add_neg, sub_ne_zero]
  have hxn : ‖(x ^ (n + 1))‖ < 1 := by
    simp only [norm_pow]
    refine pow_lt_one₀ ?_ hx ?_
    · exact norm_nonneg x
    omega
  intro h
  rw [← h] at hxn
  simp only [norm_one, lt_self_iff_false] at hxn

theorem multipliable_lt_one (x : ℂ) (hx : x ∈ ball 0 1) :
  Multipliable fun i ↦ 1 - x ^ (i+ 1) := by
  have := Complex.summable_nat_multipliable_one_add (fun (n : ℕ) => (- x ^ (n + 1) )) ?_
  conv =>
    enter [1]
    ext n
    rw [sub_eq_add_neg]
  · exact this
  rw [@summable_neg_iff]
  rw [@summable_nat_add_iff]
  rw [@summable_geometric_iff_norm_lt_one]
  simpa using hx

lemma MultipliableEtaProductExpansion (z : ℍ) :
    Multipliable (fun (n : ℕ) => (1 - cexp (2 * π * Complex.I * (n + 1) * z)) ) := by
  have := Complex.summable_nat_multipliable_one_add (fun (n : ℕ) =>
    (-cexp (2 * π * Complex.I * (n + 1) * z)) ) ?_
  · apply this.congr
    intro n
    ring
  rw [←summable_norm_iff]
  simpa using summable_exp_pow z

lemma MultipliableEtaProductExpansion_pnat (z : ℍ) :
  Multipliable (fun (n : ℕ+) => (1 - cexp (2 * π * Complex.I * n * z))) := by
  conv =>
    enter [1]
    ext n
    rw [sub_eq_add_neg]
  let g := (fun (n : ℕ) => (1 - cexp (2 * π * Complex.I * n * z)) )
  have := MultipliableEtaProductExpansion z
  conv at this =>
    enter [1]
    ext n
    rw [show (n : ℂ) + 1 = (((n + 1) : ℕ) : ℂ) by simp]
  rw [ ← multipliable_pnat_iff_multipliable_succ (f := g)] at this
  apply this.congr
  intro b
  rfl



lemma tprod_ne_zero (x : ℍ) (f : ℕ → ℍ → ℂ) (hf : ∀ i x, 1 + f i x ≠ 0)
  (hu : ∀ x : ℍ, Summable fun n => f n x) : (∏' i : ℕ, (1 + f i) x) ≠ 0 := by
  have := Complex.cexp_tsum_eq_tprod (f := fun n => 1 + f n x) ?_
  · simp only [Pi.add_apply, Pi.one_apply, ne_eq]
    rw [← this]
    · simp only [exp_ne_zero, not_false_eq_true]
    apply Complex.summable_log_one_add_of_summable
    apply hu x
  intro n
  apply hf n x


lemma Multipliable_pow {ι : Type*} (f : ι → ℂ) (hf : Multipliable f) (n : ℕ) :
     Multipliable (fun i => f i ^ n) := by
  induction n with
  | zero =>
    simp
  | succ n hn =>
    conv =>
      enter [1]
      intro u
      rw [pow_succ]
    apply Multipliable.mul hn hf



lemma MultipliableDeltaProductExpansion_pnat (z : ℍ) :
  Multipliable (fun (n : ℕ+) => (1 - cexp (2 * π * Complex.I * n * z))^24) := by
  apply Multipliable_pow
  apply MultipliableEtaProductExpansion_pnat z


lemma tprod_pow (f : ℕ → ℂ) (hf : Multipliable f) (n : ℕ) : (∏' (i : ℕ), f i) ^ n = ∏' (i : ℕ),
    (f i) ^ n := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [pow_succ]
    rw [hn]
    rw [← Multipliable.tprod_mul]
    · congr
    · apply Multipliable_pow f hf n
    exact hf



variable {a a₁ a₂ : ℝ} {ι : Type*}

theorem hasProd_le_nonneg (f g : ι → ℝ) (h : ∀ i, f i ≤ g i) (h0 : ∀ i, 0 ≤ f i)
  (hf : HasProd f a₁) (hg : HasProd g a₂) : a₁ ≤ a₂ := by
  apply le_of_tendsto_of_tendsto' hf hg
  intro s
  apply Finset.prod_le_prod
  intros i hi
  · exact h0 i
  intros i hi
  exact h i

theorem HasProd.le_one_nonneg (g : ℕ → ℝ) (h : ∀ i, g i ≤ 1) (h0 : ∀ i, 0 ≤ g i)
    (ha : HasProd g a) : a ≤ 1 := by
  apply hasProd_le_nonneg (f := g) (g := fun _ => 1) h h0 ha hasProd_one

theorem one_le_tprod_nonneg (g : ℕ → ℝ) (h : ∀ i, g i ≤ 1) (h0 : ∀ i, 0 ≤ g i) : ∏' i, g i ≤ 1 := by
  by_cases hg : Multipliable g
  · apply hg.hasProd.le_one_nonneg g h h0
  · rw [tprod_eq_one_of_not_multipliable hg]
