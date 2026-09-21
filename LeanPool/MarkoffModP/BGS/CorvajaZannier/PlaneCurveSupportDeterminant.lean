/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveFunctionField
import Mathlib.Tactic

/-!
# Rank-two support certificates for a plane curve

A diagonal stabilizer of a torus curve is controlled by the lattice generated
by differences of exponent vectors in its equation.  This file introduces the
two-dimensional determinant used for that lattice and proves the sharp box
bound `|det| ≤ 2 * degreeOf 0 f * degreeOf 1 f`.

The bound is characteristic-free.  In the high-characteristic range used by
the Corvaja--Zannier endpoint, every nonzero such determinant is automatically
nonzero modulo the characteristic.
-/

namespace BGS.CorvajaZannier

noncomputable section

/-- The oriented lattice area of the two support differences based at `r`. -/
def planeCurveSupportDifferenceDet
    (r s t : Fin 2 →₀ ℕ) : ℤ :=
  ((s 0 : ℤ) - (r 0 : ℤ)) * ((t 1 : ℤ) - (r 1 : ℤ)) -
    ((s 1 : ℤ) - (r 1 : ℤ)) * ((t 0 : ℤ) - (r 0 : ℤ))

/-- A polynomial has rank-two support when three of its monomials have
linearly independent exponent differences. -/
def PlaneCurveSupportHasRankTwo
    {K : Type*} [Field K] (f : MvPolynomial (Fin 2) K) : Prop :=
  ∃ r s t : Fin 2 →₀ ℕ,
    r ∈ f.support ∧ s ∈ f.support ∧ t ∈ f.support ∧
      planeCurveSupportDifferenceDet r s t ≠ 0

/-- Every support-lattice determinant is bounded by twice the area of the
coordinate-degree box.  This is the sharp uniform determinant estimate needed
for the diagonal-stabilizer route to the powered-image index bound. -/
theorem abs_planeCurveSupportDifferenceDet_le_twice_bidegree
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    {r s t : Fin 2 →₀ ℕ}
    (hr : r ∈ f.support) (hs : s ∈ f.support) (ht : t ∈ f.support) :
    |planeCurveSupportDifferenceDet r s t| ≤
      2 * (MvPolynomial.degreeOf 0 f : ℤ) *
        (MvPolynomial.degreeOf 1 f : ℤ) := by
  have hr0 := MvPolynomial.le_degreeOf_of_mem_support (p := f) 0 hr
  have hr1 := MvPolynomial.le_degreeOf_of_mem_support (p := f) 1 hr
  have hs0 := MvPolynomial.le_degreeOf_of_mem_support (p := f) 0 hs
  have hs1 := MvPolynomial.le_degreeOf_of_mem_support (p := f) 1 hs
  have ht0 := MvPolynomial.le_degreeOf_of_mem_support (p := f) 0 ht
  have ht1 := MvPolynomial.le_degreeOf_of_mem_support (p := f) 1 ht
  have hsr0 : |(s 0 : ℤ) - (r 0 : ℤ)| ≤
      (MvPolynomial.degreeOf 0 f : ℤ) := by
    rw [abs_le]
    constructor <;> omega
  have hsr1 : |(s 1 : ℤ) - (r 1 : ℤ)| ≤
      (MvPolynomial.degreeOf 1 f : ℤ) := by
    rw [abs_le]
    constructor <;> omega
  have htr0 : |(t 0 : ℤ) - (r 0 : ℤ)| ≤
      (MvPolynomial.degreeOf 0 f : ℤ) := by
    rw [abs_le]
    constructor <;> omega
  have htr1 : |(t 1 : ℤ) - (r 1 : ℤ)| ≤
      (MvPolynomial.degreeOf 1 f : ℤ) := by
    rw [abs_le]
    constructor <;> omega
  calc
    |planeCurveSupportDifferenceDet r s t| ≤
        |((s 0 : ℤ) - (r 0 : ℤ)) * ((t 1 : ℤ) - (r 1 : ℤ))| +
          |((s 1 : ℤ) - (r 1 : ℤ)) * ((t 0 : ℤ) - (r 0 : ℤ))| := by
      dsimp only [planeCurveSupportDifferenceDet]
      exact abs_sub _ _
    _ = |(s 0 : ℤ) - (r 0 : ℤ)| * |(t 1 : ℤ) - (r 1 : ℤ)| +
          |(s 1 : ℤ) - (r 1 : ℤ)| * |(t 0 : ℤ) - (r 0 : ℤ)| := by
      rw [abs_mul, abs_mul]
    _ ≤ (MvPolynomial.degreeOf 0 f : ℤ) *
          (MvPolynomial.degreeOf 1 f : ℤ) +
        (MvPolynomial.degreeOf 1 f : ℤ) *
          (MvPolynomial.degreeOf 0 f : ℤ) := by
      gcongr
    _ = 2 * (MvPolynomial.degreeOf 0 f : ℤ) *
          (MvPolynomial.degreeOf 1 f : ℤ) := by ring

/-- Natural-number form of the support determinant bound. -/
theorem natAbs_planeCurveSupportDifferenceDet_le_twice_bidegree
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    {r s t : Fin 2 →₀ ℕ}
    (hr : r ∈ f.support) (hs : s ∈ f.support) (ht : t ∈ f.support) :
    (planeCurveSupportDifferenceDet r s t).natAbs ≤
      2 * MvPolynomial.degreeOf 0 f * MvPolynomial.degreeOf 1 f := by
  have h := abs_planeCurveSupportDifferenceDet_le_twice_bidegree hr hs ht
  have hcast :
      ((planeCurveSupportDifferenceDet r s t).natAbs : ℤ) ≤
        (2 * MvPolynomial.degreeOf 0 f *
          MvPolynomial.degreeOf 1 f : ℕ) := by
    rw [Int.natCast_natAbs]
    exact h
  exact_mod_cast hcast

/-- A rank-two support certificate supplies a positive lattice index bounded
by the public Euler budget. -/
theorem exists_positive_supportDet_natAbs_le_twice_bidegree
    {K : Type*} [Field K] {f : MvPolynomial (Fin 2) K}
    (hrank : PlaneCurveSupportHasRankTwo f) :
    ∃ r s t : Fin 2 →₀ ℕ,
      r ∈ f.support ∧ s ∈ f.support ∧ t ∈ f.support ∧
        0 < (planeCurveSupportDifferenceDet r s t).natAbs ∧
        (planeCurveSupportDifferenceDet r s t).natAbs ≤
          2 * MvPolynomial.degreeOf 0 f * MvPolynomial.degreeOf 1 f := by
  obtain ⟨r, s, t, hr, hs, ht, hdet⟩ := hrank
  exact ⟨r, s, t, hr, hs, ht, Int.natAbs_pos.mpr hdet,
    natAbs_planeCurveSupportDifferenceDet_le_twice_bidegree hr hs ht⟩

end

end BGS.CorvajaZannier
