/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Data.Int.Star
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.UniformConvergence

/-! # BigO -/


@[expose] public section

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat


lemma norm_symm (x y : ℤ) : ‖![x, y]‖ = ‖![y,x]‖ := by
  simp [EisensteinSeries.norm_eq_max_natAbs, max_comm]


lemma linear_bigO (m : ℤ) (z : ℍ) : (fun (n : ℤ) => ((m : ℂ) * z + n)⁻¹) =O[cofinite]
    fun n => (|(n : ℝ)|⁻¹) := by
  have h1 : (fun (n : ℤ) => ((m : ℂ) * z + n)⁻¹) =O[cofinite]
    (fun n : ℤ => ((r z * ‖![n, m]‖))⁻¹) := by
    rw [@Asymptotics.isBigO_iff']
    use 1
    simp only [gt_iff_lt, zero_lt_one, norm_inv, Nat.succ_eq_add_one, Nat.reduceAdd, mul_inv_rev,
      norm_mul, Real.norm_eq_abs, one_mul, Int.cofinite_eq, eventually_sup,
      eventually_atBot, eventually_atTop, true_and, abs_norm]
    constructor
    repeat{
    use 0
    intro n hn
    have := EisensteinSeries.summand_bound z (k := 1) (by norm_num) ![m, n]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, ge_iff_le] at *
    nth_rw 2 [mul_comm]
    simp_rw [Real.rpow_neg_one] at this
    have hr : (r z)⁻¹ = |r z|⁻¹ := by simp [abs_of_pos (r_pos z)]
    rw [← hr, _root_.norm_symm]
    exact this}
  apply Asymptotics.IsBigO.trans h1
  rw [@Asymptotics.isBigO_iff']
  use (r z)⁻¹
  refine ⟨by simp only [gt_iff_lt, inv_pos]; exact r_pos z, ?_⟩
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, mul_inv_rev, norm_mul, norm_inv,
    Real.norm_eq_abs, abs_abs, abs_norm, Int.cofinite_eq, eventually_sup, eventually_atBot,
    eventually_atTop]
  constructor
  · use min (-1) m
    intro n hn
    rw [mul_comm]
    gcongr
    · simp [(r_pos z).le]
    · exact r_pos z
    · exact le_abs_self (r z)
    · simp; omega
    · rw [EisensteinSeries.norm_eq_max_natAbs]
      simp
  use max 1 m
  intro b hb
  rw [EisensteinSeries.norm_eq_max_natAbs]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Nat.cast_max, Nat.cast_natAbs, Int.cast_abs]
  rw [mul_comm]
  gcongr
  · simp [(r_pos z).le]
  · exact r_pos z
  · exact le_abs_self (r z)
  · simp only [abs_pos, ne_eq, Int.cast_eq_zero]; omega
  · simp

lemma linear_bigO_pow (m : ℤ) (z : ℍ) (k : ℕ) : (fun (n : ℤ) => ((((m : ℂ) * z + n)) ^ k )⁻¹)
  =O[cofinite]
    fun n => ((|(n : ℝ)| ^ k)⁻¹) := by
  simp_rw [← inv_pow]
  apply Asymptotics.IsBigO.pow <| linear_bigO m z

lemma Asymptotics.IsBigO.zify {α β : Type*} [Norm α] [Norm β] {f : ℤ → α} {g : ℤ → β}
    (hf : f =O[cofinite] g) :
    (fun (n : ℕ) => f n) =O[cofinite] fun n => g n := by
  rw [@isBigO_iff] at *
  obtain ⟨C, hC⟩ := hf
  use C
  rw [Int.cofinite_eq] at hC
  rw [Nat.cofinite_eq_atTop]
  apply Filter.Eventually.natCast_atTop (p := fun n => ‖f n‖ ≤ C * ‖g n‖)
  simp_all only [eventually_sup, eventually_atBot, eventually_atTop]

lemma Asymptotics.IsBigO.of_neg {α β : Type*} [Norm α] [Norm β] {f : ℤ → α} {g : ℤ → β}
    (hf : f =O[cofinite] g) : (fun n => f (-n)) =O[cofinite] fun n => g (-n) := by
  rw [← Equiv.neg_apply]
  apply Asymptotics.IsBigO.comp_tendsto hf
  refine Injective.tendsto_cofinite (Equiv.injective (Equiv.neg ℤ))

lemma linear_bigO_nat (m : ℤ) (z : ℍ) : (fun (n : ℕ) => ((m : ℂ) * z + n)⁻¹) =O[cofinite]
    fun n => (|(n : ℝ)|⁻¹) :=
  (linear_bigO (m : ℤ) z).zify

lemma linear_bigO' (m : ℤ) (z : ℍ) : (fun (n : ℤ) => ((n : ℂ) * z + m)⁻¹) =O[cofinite]
    fun n => (|(n : ℝ)|⁻¹) := by
  have h1 : (fun (n : ℤ) => ((n : ℂ) * z + m)⁻¹) =O[cofinite]
    (fun n : ℤ => ((r z * ‖![m, n]‖))⁻¹) := by
    rw [@Asymptotics.isBigO_iff']
    use 1
    simp only [gt_iff_lt, zero_lt_one, norm_inv, Nat.succ_eq_add_one, Nat.reduceAdd, mul_inv_rev,
      norm_mul, Real.norm_eq_abs, one_mul, Int.cofinite_eq, eventually_sup,
      eventually_atBot, eventually_atTop, true_and, abs_norm]
    constructor
    repeat{
      use 0
      intro n hn
      have := EisensteinSeries.summand_bound z (k := 1) (by norm_num) ![n, m]
      simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, ge_iff_le] at *
      nth_rw 2 [mul_comm]
      simp_rw [Real.rpow_neg_one] at this
      have hr : (r z)⁻¹ = |r z|⁻¹ := by
        simp only [inv_inj]
        apply symm
        rw [abs_eq_self]
        exact (r_pos z).le
      rw [← hr, _root_.norm_symm]
      exact this}
  apply Asymptotics.IsBigO.trans h1
  rw [@Asymptotics.isBigO_iff']
  use (r z)⁻¹
  refine ⟨by simp only [gt_iff_lt, inv_pos]; exact r_pos z, ?_⟩
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, mul_inv_rev, norm_mul, norm_inv,
    Real.norm_eq_abs, abs_abs, abs_norm, Int.cofinite_eq, eventually_sup, eventually_atBot,
    eventually_atTop]
  constructor
  · use min (-1) m
    intro n hn
    rw [mul_comm]
    gcongr
    · simp [(r_pos z).le]
    · exact r_pos z
    · exact le_abs_self (r z)
    · simp; omega
    · simp [EisensteinSeries.norm_eq_max_natAbs]
  use max 1 m
  intro b hb
  rw [EisensteinSeries.norm_eq_max_natAbs]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Nat.cast_max, Nat.cast_natAbs, Int.cast_abs]
  rw [mul_comm]
  gcongr
  · simp [(r_pos z).le]
  · exact r_pos z
  · exact le_abs_self (r z)
  · simp; omega
  · simp
