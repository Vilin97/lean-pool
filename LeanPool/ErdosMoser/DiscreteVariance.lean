/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.ErdosMoser.Basic
import Mathlib.Data.Finset.Sort
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# A sharp variance bound for distinct natural numbers

The main result of this file minimizes the unnormalized empirical variance of
a finite set of natural numbers. The proof enumerates the set increasingly,
compares all pairwise differences with those of an initial interval, and
evaluates the resulting quadratic sum.
-/

namespace LeanPool.ErdosMoser

open Finset

/-- Closed form for the sum of squares over `Finset.range m`, stated over the
reals for use in the variance calculation. -/
lemma sumSquaresRange (m : ℕ) :
    6 * ∑ i ∈ Finset.range m, (i : ℝ) ^ 2 =
      (m : ℝ) * ((m : ℝ) - 1) * (2 * (m : ℝ) - 1) := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    push_cast
    ring_nf
    ring_nf at ih
    linarith [ih]

/-- Pairwise-difference form of the unnormalized variance of a function on a
finite set. -/
lemma twoMulCardSumSquaresSubSquareEqSumPairsDiffSquare
    {ι : Type*} (s : Finset ι) (g : ι → ℝ) :
    2 * ((s.card : ℝ) * (∑ i ∈ s, g i ^ 2) - (∑ i ∈ s, g i) ^ 2) =
      ∑ i ∈ s, ∑ j ∈ s, (g i - g j) ^ 2 := by
  have hInner : ∀ i ∈ s,
      ∑ j ∈ s, (g i - g j) ^ 2 =
        (s.card : ℝ) * g i ^ 2 - 2 * g i * (∑ j ∈ s, g j) +
          ∑ j ∈ s, g j ^ 2 := by
    intro i _
    have hExpand : ∀ j ∈ s,
        (g i - g j) ^ 2 = g i ^ 2 + g j ^ 2 - 2 * g i * g j := by
      intros
      ring
    rw [Finset.sum_congr rfl hExpand]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      nsmul_eq_mul]
    have hCross : ∑ j ∈ s, 2 * g i * g j = 2 * g i * ∑ j ∈ s, g j := by
      rw [← Finset.mul_sum]
    rw [hCross]
    ring
  rw [Finset.sum_congr rfl hInner]
  have hRearrange : ∀ i ∈ s,
      (s.card : ℝ) * g i ^ 2 - 2 * g i * (∑ j ∈ s, g j) +
          ∑ j ∈ s, g j ^ 2 =
        ((s.card : ℝ) * g i ^ 2 + ∑ j ∈ s, g j ^ 2) -
          2 * g i * (∑ j ∈ s, g j) := by
    intros
    ring
  rw [Finset.sum_congr rfl hRearrange]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hCrossOuter : ∑ i ∈ s, 2 * g i * (∑ j ∈ s, g j) =
      (2 * ∑ i ∈ s, g i) * ∑ j ∈ s, g j := by
    have hRewrite : ∀ i ∈ s,
        2 * g i * (∑ j ∈ s, g j) = (2 * ∑ j ∈ s, g j) * g i := by
      intros
      ring
    rw [Finset.sum_congr rfl hRewrite, ← Finset.mul_sum]
  rw [hCrossOuter]
  ring

/-- A strictly increasing natural-valued sequence grows by at least the
difference of its indices. -/
lemma strictMonoFinNatLeDiff {m : ℕ} {g : Fin m → ℕ} (hg : StrictMono g)
    {i j : Fin m} (h : i ≤ j) : (j : ℕ) - (i : ℕ) ≤ g j - g i := by
  suffices hGeneral : ∀ (d : ℕ) (i j : Fin m), (i : ℕ) + d = (j : ℕ) →
      d ≤ g j - g i by
    have hIndex : (i : ℕ) + ((j : ℕ) - (i : ℕ)) = (j : ℕ) := by
      have hValues : (i : ℕ) ≤ (j : ℕ) := h
      omega
    exact hGeneral ((j : ℕ) - (i : ℕ)) i j hIndex
  intro d
  induction d with
  | zero =>
    intro i j hEqual
    have hValues : (i : ℕ) = (j : ℕ) := by omega
    have hIndices : i = j := Fin.ext hValues
    subst hIndices
    omega
  | succ k ih =>
    intro i j hEqual
    have hIntermediateLt : (i : ℕ) + k < m := by
      omega
    let intermediate : Fin m := ⟨(i : ℕ) + k, hIntermediateLt⟩
    have hIntermediateValue : (intermediate : ℕ) = (i : ℕ) + k := rfl
    have hPrevious : k ≤ g intermediate - g i :=
      ih i intermediate hIntermediateValue.symm
    have hIntermediateLtJ : intermediate < j := by
      have : (intermediate : ℕ) < (j : ℕ) := by
        rw [hIntermediateValue]
        omega
      exact this
    have hStrict : g intermediate < g j := hg hIntermediateLtJ
    have hLower : g i ≤ g intermediate := by
      have hIndices : i ≤ intermediate := by
        have : (i : ℕ) ≤ (intermediate : ℕ) := by
          rw [hIntermediateValue]
          omega
        exact this
      exact hg.monotone hIndices
    omega

/-- Increasing a collection of distinct natural numbers can only increase
each squared pairwise difference from that of consecutive indices. -/
lemma strictMonoFinNatDiffSquareGe {m : ℕ} {g : Fin m → ℕ} (hg : StrictMono g)
    (i j : Fin m) :
    (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) ^ 2 ≤
      (((g i : ℕ) : ℝ) - ((g j : ℕ) : ℝ)) ^ 2 := by
  rcases le_total i j with hij | hji
  · have hDifference : (j : ℕ) - (i : ℕ) ≤ g j - g i :=
      strictMonoFinNatLeDiff hg hij
    have hImages : g i ≤ g j := hg.monotone hij
    have hIndices : (i : ℕ) ≤ (j : ℕ) := hij
    have hDifferenceReal :
        ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ) ≤
          ((g j : ℕ) : ℝ) - ((g i : ℕ) : ℝ) := by
      have hCast : (((j : ℕ) - (i : ℕ) : ℕ) : ℝ) ≤
          ((g j - g i : ℕ) : ℝ) := by
        exact_mod_cast hDifference
      rw [Nat.cast_sub hIndices, Nat.cast_sub hImages] at hCast
      exact hCast
    have hNonnegative :
        (0 : ℝ) ≤ ((j : ℕ) : ℝ) - ((i : ℕ) : ℝ) := by
      have : ((i : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by
        exact_mod_cast hIndices
      linarith
    have hLeft :
        (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) ^ 2 =
          (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) ^ 2 := by
      ring
    have hRight :
        (((g i : ℕ) : ℝ) - ((g j : ℕ) : ℝ)) ^ 2 =
          (((g j : ℕ) : ℝ) - ((g i : ℕ) : ℝ)) ^ 2 := by
      ring
    rw [hLeft, hRight]
    exact pow_le_pow_left₀ hNonnegative hDifferenceReal 2
  · have hDifference : (i : ℕ) - (j : ℕ) ≤ g i - g j :=
      strictMonoFinNatLeDiff hg hji
    have hImages : g j ≤ g i := hg.monotone hji
    have hIndices : (j : ℕ) ≤ (i : ℕ) := hji
    have hDifferenceReal :
        ((i : ℕ) : ℝ) - ((j : ℕ) : ℝ) ≤
          ((g i : ℕ) : ℝ) - ((g j : ℕ) : ℝ) := by
      have hCast : (((i : ℕ) - (j : ℕ) : ℕ) : ℝ) ≤
          ((g i - g j : ℕ) : ℝ) := by
        exact_mod_cast hDifference
      rw [Nat.cast_sub hIndices, Nat.cast_sub hImages] at hCast
      exact hCast
    have hNonnegative :
        (0 : ℝ) ≤ ((i : ℕ) : ℝ) - ((j : ℕ) : ℝ) := by
      have : ((j : ℕ) : ℝ) ≤ ((i : ℕ) : ℝ) := by
        exact_mod_cast hIndices
      linarith
    exact pow_le_pow_left₀ hNonnegative hDifferenceReal 2

/-- Among finite sets of natural numbers of a fixed cardinality, an initial
interval minimizes the unnormalized empirical variance. -/
theorem varianceLowerBoundFinsetNat (T : Finset ℕ) :
    (T.card : ℝ) ^ 2 * ((T.card : ℝ) ^ 2 - 1) / 12 ≤
      (T.card : ℝ) * (∑ t ∈ T, (t : ℝ) ^ 2) -
        (∑ t ∈ T, (t : ℝ)) ^ 2 := by
  set m := T.card with hCard
  let g : Fin m ↪o ℕ := T.orderEmbOfFin rfl
  have hStrict : StrictMono g := g.strictMono
  have hSum :
      ∑ t ∈ T, (t : ℝ) = ∑ i : Fin m, ((g i : ℕ) : ℝ) := by
    rw [← Finset.map_orderEmbOfFin_univ (s := T) rfl, Finset.sum_map]
    rfl
  have hSumSquares :
      ∑ t ∈ T, (t : ℝ) ^ 2 = ∑ i : Fin m, ((g i : ℕ) : ℝ) ^ 2 := by
    rw [← Finset.map_orderEmbOfFin_univ (s := T) rfl, Finset.sum_map]
    rfl
  rw [hSum, hSumSquares]
  have hCardUniv : (Finset.univ : Finset (Fin m)).card = m := by
    simp
  have hVarianceIdentity :
      2 * ((m : ℝ) * (∑ i : Fin m, ((g i : ℕ) : ℝ) ^ 2) -
            (∑ i : Fin m, ((g i : ℕ) : ℝ)) ^ 2) =
        ∑ i : Fin m, ∑ j : Fin m,
          (((g i : ℕ) : ℝ) - ((g j : ℕ) : ℝ)) ^ 2 := by
    have h := twoMulCardSumSquaresSubSquareEqSumPairsDiffSquare
      (Finset.univ : Finset (Fin m)) (fun i ↦ ((g i : ℕ) : ℝ))
    rw [hCardUniv] at h
    exact h
  have hPointwise : ∀ i : Fin m, ∀ j : Fin m,
      (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) ^ 2 ≤
        (((g i : ℕ) : ℝ) - ((g j : ℕ) : ℝ)) ^ 2 := by
    intro i j
    exact strictMonoFinNatDiffSquareGe hStrict i j
  have hSumLower :
      ∑ i : Fin m, ∑ j : Fin m,
          (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) ^ 2 ≤
        ∑ i : Fin m, ∑ j : Fin m,
          (((g i : ℕ) : ℝ) - ((g j : ℕ) : ℝ)) ^ 2 :=
    Finset.sum_le_sum (fun i _ ↦
      Finset.sum_le_sum (fun j _ ↦ hPointwise i j))
  have hRangeSum :
      ∑ i : Fin m, ∑ j : Fin m,
          (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) ^ 2 =
        (m : ℝ) ^ 2 * ((m : ℝ) ^ 2 - 1) / 6 := by
    have hIdentity :
        2 * ((m : ℝ) * (∑ i : Fin m, ((i : ℕ) : ℝ) ^ 2) -
              (∑ i : Fin m, ((i : ℕ) : ℝ)) ^ 2) =
          ∑ i : Fin m, ∑ j : Fin m,
            (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) ^ 2 := by
      have h := twoMulCardSumSquaresSubSquareEqSumPairsDiffSquare
        (Finset.univ : Finset (Fin m)) (fun i ↦ ((i : ℕ) : ℝ))
      rw [hCardUniv] at h
      exact h
    have hIndexSum :
        (∑ i : Fin m, ((i : ℕ) : ℝ)) =
          ∑ i ∈ Finset.range m, (i : ℝ) := by
      rw [Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ (i : ℝ))]
    have hIndexSquareSum :
        (∑ i : Fin m, ((i : ℕ) : ℝ) ^ 2) =
          ∑ i ∈ Finset.range m, (i : ℝ) ^ 2 := by
      rw [Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ (i : ℝ) ^ 2)]
    rw [hIndexSum, hIndexSquareSum] at hIdentity
    have hNatIndexSum :
        (∑ i ∈ Finset.range m, i) * 2 = m * (m - 1) :=
      Finset.sum_range_id_mul_two m
    have hRealIndexSum :
        (∑ i ∈ Finset.range m, (i : ℝ)) * 2 =
          (m : ℝ) * ((m : ℝ) - 1) := by
      have hCast : (((∑ i ∈ Finset.range m, i) * 2 : ℕ) : ℝ) =
          ((m * (m - 1) : ℕ) : ℝ) := by
        exact_mod_cast hNatIndexSum
      push_cast at hCast
      rcases Nat.eq_zero_or_pos m with hm | hm
      · simp [hm]
      · have hOneLe : 1 ≤ m := hm
        simpa [Nat.cast_sub hOneLe] using hCast
    have hSquareSum := sumSquaresRange m
    rw [hIdentity.symm]
    have hTarget :
        (m : ℝ) ^ 2 * ((m : ℝ) ^ 2 - 1) / 6 =
          2 * ((m : ℝ) * (∑ i ∈ Finset.range m, (i : ℝ) ^ 2) -
            (∑ i ∈ Finset.range m, (i : ℝ)) ^ 2) := by
      have hIndexSquare :
          (∑ i ∈ Finset.range m, (i : ℝ)) ^ 2 =
            ((m : ℝ) * ((m : ℝ) - 1)) ^ 2 / 4 := by
        have hSquare :
            ((∑ i ∈ Finset.range m, (i : ℝ)) * 2) ^ 2 =
              ((m : ℝ) * ((m : ℝ) - 1)) ^ 2 := by
          rw [hRealIndexSum]
        have hExpand :
            ((∑ i ∈ Finset.range m, (i : ℝ)) * 2) ^ 2 =
              4 * (∑ i ∈ Finset.range m, (i : ℝ)) ^ 2 := by
          ring
        linarith [hExpand ▸ hSquare]
      have hIndexSquareFour :
          4 * (∑ i ∈ Finset.range m, (i : ℝ)) ^ 2 =
            ((m : ℝ) * ((m : ℝ) - 1)) ^ 2 := by
        rw [hIndexSquare]
        ring
      have hTwelve :
          12 * ((m : ℝ) * (∑ i ∈ Finset.range m, (i : ℝ) ^ 2) -
            (∑ i ∈ Finset.range m, (i : ℝ)) ^ 2) =
              (m : ℝ) ^ 2 * ((m : ℝ) ^ 2 - 1) := by
        calc
          12 * ((m : ℝ) * (∑ i ∈ Finset.range m, (i : ℝ) ^ 2) -
              (∑ i ∈ Finset.range m, (i : ℝ)) ^ 2) =
              2 * (m : ℝ) * (6 * ∑ i ∈ Finset.range m, (i : ℝ) ^ 2) -
                3 * (4 * (∑ i ∈ Finset.range m, (i : ℝ)) ^ 2) := by ring
          _ = (m : ℝ) ^ 2 * ((m : ℝ) ^ 2 - 1) := by
            rw [hSquareSum, hIndexSquareFour]
            ring
      linarith
    linarith
  linarith [hVarianceIdentity, hSumLower, hRangeSum]

end LeanPool.ErdosMoser
