/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/

import LeanPool.PentagonalNumberTheorem.Generic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.PiTopology

/-!

# Pentagonal number theorem for power series

This file proves the
[pentagonal number theorem](https://en.wikipedia.org/wiki/Pentagonal_number_theorem)
for power series.


-/

open PowerSeries Filter
open scoped PowerSeries.WithPiTopology


variable (R : Type*) [CommRing R]

namespace Pentagonal

theorem summable_gamma_powerSeries [TopologicalSpace R] (k : ℕ) :
    Summable (gamma k · (X : R⟦X⟧)) := by
  rw [PowerSeries.WithPiTopology.summable_iff_summable_coeff]
  refine fun n ↦ summable_of_hasFiniteSupport <| Set.Finite.subset (Set.finite_Iic n) ?_
  simp_rw [Function.support_subset_iff, Set.mem_Iic]
  intro i h
  contrapose! h
  unfold gamma
  have : ¬ (k + 1) * i ≤ n := by
    rw [not_le]
    exact h.trans_le <| Nat.le_mul_of_pos_left i (by simp)
  simp [PowerSeries.coeff_X_pow_mul', this]

theorem multipliable_pentagonalLhs_powerSeries' [Nontrivial R] [TopologicalSpace R] (k : ℕ) :
    Multipliable (fun n ↦ (1 : R⟦X⟧) - X ^ (n + k + 1)) := by
  simp_rw [sub_eq_add_neg]
  apply PowerSeries.WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr (fun n ↦ eventually_atTop.mpr ⟨n, ?_⟩)
  intro m hm
  rw [PowerSeries.order_neg]
  refine lt_of_lt_of_le ?_ (PowerSeries.le_order_pow _ _)
  rw [PowerSeries.order_X, nsmul_one]
  norm_cast
  linarith

end Pentagonal

open Pentagonal

theorem summable_pentagonalRhs_powerSeries
    [Nontrivial R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    Summable (fun (k : ℕ) ↦
    ((-1) ^ k * (X ^ (k * (3 * k + 1) / 2) - X ^ ((k + 1) * (3 * k + 2) / 2)) : R⟦X⟧)) := by
  apply PowerSeries.WithPiTopology.summable_of_tendsto_order_atTop_nhds_top
  rw [ENat.tendsto_nhds_top_iff_natCast_lt]
  refine fun n ↦ eventually_atTop.mpr ⟨n + 1, fun k hk ↦ ?_⟩
  rw [sub_eq_add_neg]
  apply lt_of_lt_of_le (lt_add_of_nonneg_of_lt (by simp) ?_) (PowerSeries.le_order_mul _ _)
  apply lt_of_lt_of_le ?_ (PowerSeries.min_order_le_order_add _ _)
  simp_rw [order_neg, order_X_pow]
  rw [min_eq_left (by gcongr <;> simp), Nat.cast_lt, ← Nat.add_one_le_iff,
    Nat.le_div_iff_mul_le (by simp)]
  exact Nat.mul_le_mul hk (by linarith)

/-- **Pentagonal number theorem** for formal power series, summation over natural numbers.

$$ \prod_{n = 0}^{\infty} 1 - x^{n + 1} =
\sum_{k=0}^{\infty} (-1)^k \left(x^{k(3k+1)/2} + x^{(k+1)(3k+2)/2}\right) $$ -/
theorem pentagonalNumberTheorem_powerSeries
    [Nontrivial R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    ∏' n, (1 - X ^ (n + 1) : R⟦X⟧) =
    ∑' k, (-1) ^ k * (X ^ (k * (3 * k + 1) / 2) - X ^ ((k + 1) * (3 * k + 2) / 2)) := by
  refine pentagonalNumberTheorem_generic ?_ ?_ ?_ ?_ ?_
  · rw [IsTopologicallyNilpotent, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
    refine fun d ↦ tendsto_atTop_of_eventually_const fun i (hi : i ≥ d + 1) ↦ ?_
    simp_rw [coeff_X_pow]
    aesop
  · apply summable_gamma_powerSeries
  · apply multipliable_pentagonalLhs_powerSeries'
  · apply summable_pentagonalRhs_powerSeries
  · rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
    refine fun n ↦ tendsto_atTop_of_eventually_const fun k (hk : k ≥ n) ↦ ?_
    rw [map_zero]
    apply PowerSeries.coeff_of_lt_order
    refine lt_of_lt_of_le (lt_add_of_lt_of_nonneg ?_ (by simp)) (PowerSeries.le_order_mul _ _)
    refine lt_of_lt_of_le (lt_add_of_nonneg_of_lt (by simp) ?_) (PowerSeries.le_order_mul _ _)
    rw [order_X_pow, Nat.cast_lt, ← Nat.add_one_le_iff, Nat.le_div_iff_mul_le (by simp)]
    apply Nat.mul_le_mul <;> linarith

theorem summable_pentagonalRhs_intNeg_powerSeries
    [Nontrivial R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    Summable (fun (k : ℤ) ↦ (Int.negOnePow k : R⟦X⟧) * X ^ (k * (3 * k + 1) / 2).toNat) := by
  apply Summable.of_add_one_of_neg_add_one
  all_goals
  apply PowerSeries.WithPiTopology.summable_of_tendsto_order_atTop_nhds_top
  rw [ENat.tendsto_nhds_top_iff_natCast_lt]
  refine fun n ↦ eventually_atTop.mpr ⟨n, fun k hk ↦ ?_⟩
  refine lt_of_lt_of_le (lt_add_of_nonneg_of_lt (by simp) ?_) (PowerSeries.le_order_mul _ _)
  rw [order_X_pow, Nat.cast_lt, Int.lt_toNat, ← Int.add_one_le_iff,
    Int.le_ediv_iff_mul_le (by simp)]
  nlinarith

/-- **Pentagonal number theorem** for formal power series, summation over integers, opposite order.

$$ \prod_{n = 0}^{\infty} 1 - x^{n + 1} = \sum_{k=-\infty}^{\infty} (-1)^k x^{k(3k + 1)/2} $$ -/
theorem pentagonalNumberTheorem_intNeg_powerSeries
    [Nontrivial R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    ∏' n, (1 - X ^ (n + 1)) =
    ∑' (k : ℤ), (Int.negOnePow k : R⟦X⟧) * X ^ (k * (3 * k + 1) / 2).toNat := by
  rw [← tsum_nat_add_neg_add_one (summable_pentagonalRhs_intNeg_powerSeries R),
    pentagonalNumberTheorem_powerSeries]
  refine tsum_congr fun k ↦ ?_
  rw [sub_eq_add_neg _ (X ^ _), mul_add, ← neg_mul_comm]
  congrm ($(by norm_cast) * X ^ $(by norm_cast) + ?_ * X ^ $(by norm_cast))
  trans (-1) ^ (k + 1)
  · ring
  · norm_cast

theorem summable_pentagonalRhs_intPos_powerSeries
    [Nontrivial R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    Summable (fun (k : ℤ) ↦ (Int.negOnePow k : R⟦X⟧) * X ^ (k * (3 * k - 1) / 2).toNat) := by
  rw [← neg_injective.summable_iff (by intro x hx; contrapose! hx; use -x; simp)]
  convert summable_pentagonalRhs_intNeg_powerSeries R
  rw [Function.comp_apply]
  exact congr($(by simp) * X ^ (Int.toNat ($(by ring_nf) / 2)))

/-- **Pentagonal number theorem** for formal power series, summation over integers, classic order.

$$ \prod_{n = 0}^{\infty} 1 - x^{n + 1} = \sum_{k=-\infty}^{\infty} (-1)^k x^{k(3k - 1)/2} $$ -/
theorem pentagonalNumberTheorem_intPos_powerSeries
    [Nontrivial R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    ∏' n, (1 - X ^ (n + 1)) =
    ∑' (k : ℤ), (Int.negOnePow k : R⟦X⟧) * X ^ (k * (3 * k - 1) / 2).toNat := by
  rw [pentagonalNumberTheorem_intNeg_powerSeries, ← neg_injective.tsum_eq (by simp)]
  exact tsum_congr fun k ↦ congr($(by simp) * X ^ (Int.toNat ($(by ring_nf) / 2)))
