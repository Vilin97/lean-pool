/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.GlobalWronskianSummation
import Mathlib.Tactic

/-!
# Summing the four local Corvaja--Zannier Wronskian cases

This module proves the exact finite-support divisor summation used in
Corvaja--Zannier Proposition 2.  Its hypotheses are the four already proved
local lower bounds together with explicit principal-divisor, degree, and
canonical-divisor identities.  Thus it isolates the remaining geometric
boundary: constructing these data from the places of the plane-curve
function field.
-/

namespace BGS.CorvajaZannier

noncomputable section

/-- Finite-support form of the summation step in the proof of
Corvaja--Zannier Proposition 2. -/
theorem globalWronskianInequality_of_placewiseBounds
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι)
    (ordU ordV ordRho ordGrid ordW : ι → ℤ)
    (h k n sigma degreeU degreeV chi heightOutside : ℕ)
    (canonicalDegree : ℤ)
    (hUOutside : ∀ i, i ∉ S → ordU i = 0)
    (hGridOutside : ∀ i, i ∉ S → ordGrid i = 0)
    (hUSum : ∑ i, ordU i = 0)
    (hGridSum : ∑ i, ordGrid i = 0)
    (hDegreeV : ∑ i ∈ S.filter (fun i ↦ 0 < ordV i), ordV i = degreeV)
    (hOutsideHeight :
      ∑ i ∈ Finset.univ.filter (fun i ↦ i ∉ S ∧ ordRho i < 0), ordRho i =
        -(heightOutside : ℤ))
    (hCanonical : ∑ i, ordW i = (sigma : ℤ) * canonicalDegree)
    (hEuler : canonicalDegree + S.card ≤ (chi : ℤ))
    (hRhoSupport :
      -((degreeU : ℤ) + (degreeV : ℤ)) ≤ ∑ i ∈ S, ordRho i)
    (hCaseI : ∀ i, i ∉ S → ordRho i < 0 →
      (n : ℤ) * ordRho i ≤ ordW i)
    (hCaseII : ∀ i, i ∉ S → 0 ≤ ordRho i → 0 ≤ ordW i)
    (hCaseIII : ∀ i, i ∈ S → 0 < ordV i →
      ((k * (k - 1) / 2 : ℕ) : ℤ) * ordU i +
          ((h * k : ℕ) : ℤ) * ordV i + (k : ℤ) * ordRho i +
          ordGrid i - (sigma : ℤ) ≤ ordW i)
    (hCaseIV : ∀ i, i ∈ S → ordV i ≤ 0 →
      ((k * (k - 1) / 2 : ℕ) : ℤ) * ordU i +
          (k : ℤ) * ordRho i + ordGrid i - (sigma : ℤ) ≤ ordW i) :
    ((h * k : ℕ) : ℤ) * (degreeV : ℤ) -
        (k : ℤ) * ((degreeU : ℤ) + (degreeV : ℤ)) -
        (sigma : ℤ) * (chi : ℤ) ≤
      (n : ℤ) * (heightOutside : ℤ) := by
  let base : ι → ℤ := fun i ↦
    ((k * (k - 1) / 2 : ℕ) : ℤ) * ordU i +
      (k : ℤ) * ordRho i + ordGrid i - (sigma : ℤ)
  let lower : ι → ℤ := fun i ↦
    if i ∈ S then
      base i + if 0 < ordV i then ((h * k : ℕ) : ℤ) * ordV i else 0
    else if ordRho i < 0 then (n : ℤ) * ordRho i else 0
  have hPointwise (i : ι) : lower i ≤ ordW i := by
    by_cases hiS : i ∈ S
    · by_cases hvi : 0 < ordV i
      · have hLocal := hCaseIII i hiS hvi
        simp only [lower, hiS, ite_eq_left, hvi]
        dsimp [base]
        norm_num at hLocal ⊢
        linarith
      · have hvi' : ordV i ≤ 0 := le_of_not_gt hvi
        simpa [lower, base, hiS, hvi] using hCaseIV i hiS hvi'
    · by_cases hρi : ordRho i < 0
      · simpa [lower, hiS, hρi] using hCaseI i hiS hρi
      · have hρi' : 0 ≤ ordRho i := le_of_not_gt hρi
        simpa [lower, hiS, hρi] using hCaseII i hiS hρi'
  have hSumLower : ∑ i, lower i ≤ ∑ i, ordW i :=
    Finset.sum_le_sum fun i _ ↦ hPointwise i
  have hSumUOnS : ∑ i ∈ S, ordU i = 0 := by
    calc
      ∑ i ∈ S, ordU i = ∑ i, ordU i := by
        apply Finset.sum_subset (Finset.subset_univ S)
        intro i _ hiS
        exact hUOutside i hiS
      _ = 0 := hUSum
  have hSumGridOnS : ∑ i ∈ S, ordGrid i = 0 := by
    calc
      ∑ i ∈ S, ordGrid i = ∑ i, ordGrid i := by
        apply Finset.sum_subset (Finset.subset_univ S)
        intro i _ hiS
        exact hGridOutside i hiS
      _ = 0 := hGridSum
  have hPositiveVSum :
      ∑ i ∈ S, (if 0 < ordV i then ((h * k : ℕ) : ℤ) * ordV i else 0) =
        ((h * k : ℕ) : ℤ) * (degreeV : ℤ) := by
    calc
      _ = ∑ i ∈ S.filter (fun i ↦ 0 < ordV i),
          ((h * k : ℕ) : ℤ) * ordV i := by
            exact (Finset.sum_filter
              (s := S) (fun i ↦ 0 < ordV i)
              (fun i ↦ ((h * k : ℕ) : ℤ) * ordV i)).symm
      _ = ((h * k : ℕ) : ℤ) *
          (∑ i ∈ S.filter (fun i ↦ 0 < ordV i), ordV i) := by
            rw [Finset.mul_sum]
      _ = ((h * k : ℕ) : ℤ) * (degreeV : ℤ) := by rw [hDegreeV]
  have hOutsideRhoSum :
      ∑ i ∈ Finset.univ.filter (fun i ↦ i ∉ S),
          (if ordRho i < 0 then (n : ℤ) * ordRho i else 0) =
        -(n : ℤ) * (heightOutside : ℤ) := by
    calc
      _ = ∑ i ∈ (Finset.univ.filter (fun i ↦ i ∉ S)).filter
          (fun i ↦ ordRho i < 0), (n : ℤ) * ordRho i := by
            exact (Finset.sum_filter
              (s := Finset.univ.filter (fun i ↦ i ∉ S))
              (fun i ↦ ordRho i < 0)
              (fun i ↦ (n : ℤ) * ordRho i)).symm
      _ = ∑ i ∈ Finset.univ.filter (fun i ↦ i ∉ S ∧ ordRho i < 0),
          (n : ℤ) * ordRho i := by rw [Finset.filter_filter]
      _ = (n : ℤ) *
          (∑ i ∈ Finset.univ.filter (fun i ↦ i ∉ S ∧ ordRho i < 0),
            ordRho i) := by rw [Finset.mul_sum]
      _ = -(n : ℤ) * (heightOutside : ℤ) := by rw [hOutsideHeight]; ring
  have hBaseSum :
      ∑ i ∈ S, base i =
        (k : ℤ) * (∑ i ∈ S, ordRho i) - (sigma : ℤ) * S.card := by
    dsimp [base]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hSumUOnS, hSumGridOnS]
    simp
    ring
  have hLowerSum :
      ∑ i, lower i =
        (k : ℤ) * (∑ i ∈ S, ordRho i) - (sigma : ℤ) * S.card +
          ((h * k : ℕ) : ℤ) * (degreeV : ℤ) -
          (n : ℤ) * (heightOutside : ℤ) := by
    have hSplit := Finset.sum_filter_add_sum_filter_not
      Finset.univ (fun i ↦ i ∈ S) lower
    have hFilterS : Finset.univ.filter (fun i ↦ i ∈ S) = S := by
      ext i
      simp
    rw [hFilterS] at hSplit
    calc
      ∑ i, lower i =
          (∑ i ∈ S,
            (base i + if 0 < ordV i then ((h * k : ℕ) : ℤ) * ordV i else 0)) +
          ∑ i ∈ Finset.univ.filter (fun i ↦ i ∉ S),
            (if ordRho i < 0 then (n : ℤ) * ordRho i else 0) := by
              rw [← hSplit]
              congr 1
              · apply Finset.sum_congr rfl
                intro i hi
                simp only [lower, hi, ite_eq_left]
              · apply Finset.sum_congr rfl
                intro i hi
                have hiS : i ∉ S := (Finset.mem_filter.1 hi).2
                simp only [lower, hiS, ite_false]
      _ = (∑ i ∈ S, base i) +
          (∑ i ∈ S,
            (if 0 < ordV i then ((h * k : ℕ) : ℤ) * ordV i else 0)) +
          ∑ i ∈ Finset.univ.filter (fun i ↦ i ∉ S),
            (if ordRho i < 0 then (n : ℤ) * ordRho i else 0) := by
              rw [Finset.sum_add_distrib]
      _ = _ := by rw [hBaseSum, hPositiveVSum, hOutsideRhoSum]; ring
  rw [hLowerSum, hCanonical] at hSumLower
  have hRhoScaled :
      -(k : ℤ) * ((degreeU : ℤ) + (degreeV : ℤ)) ≤
        (k : ℤ) * (∑ i ∈ S, ordRho i) := by
    have hScaled :=
      mul_le_mul_of_nonneg_left hRhoSupport (Int.natCast_nonneg k)
    calc
      -(k : ℤ) * ((degreeU : ℤ) + (degreeV : ℤ)) =
          (k : ℤ) * (-((degreeU : ℤ) + (degreeV : ℤ))) := by ring
      _ ≤ (k : ℤ) * (∑ i ∈ S, ordRho i) := hScaled
  have hEulerScaled :
      (sigma : ℤ) * canonicalDegree + (sigma : ℤ) * S.card ≤
        (sigma : ℤ) * (chi : ℤ) := by
    have hScaled :=
      mul_le_mul_of_nonneg_left hEuler (Int.natCast_nonneg sigma)
    linarith
  linarith

end

end BGS.CorvajaZannier
