/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.RationalFeasibility
public import Mathlib.Tactic

/-! # Rational Linear Oracle -/

@[expose] public section

open scoped BigOperators

namespace BeyondBethe

/-!
# Exact rational linear-constraint cuts

The bounded Bethe epigraph has many rational linear inequalities.  This file
implements their scan and proves that every reported violation is a strict
central cut for every point satisfying the inequality.
-/

structure RationalHalfspace (d : ℕ) where
  normal : Fin d → ℚ
  offset : ℚ
  normal_ne_zero : normal ≠ 0

def RationalHalfspace.SatisfiedBy {d : ℕ}
    (h : RationalHalfspace d) (x : Fin d → ℝ) : Prop :=
  finiteDot (fun i ↦ (h.normal i : ℝ)) x ≤ (h.offset : ℝ)

def RationalHalfspace.satisfiedByRational {d : ℕ}
    (h : RationalHalfspace d) (x : Fin d → ℚ) : Prop :=
  finiteDot h.normal x ≤ h.offset

/-- First exactly violated inequality, in list order. -/
def firstViolatedHalfspace {d : ℕ} (x : Fin d → ℚ) :
    List (RationalHalfspace d) → Option (RationalHalfspace d)
  | [] => none
  | h :: hs =>
      if h.offset < finiteDot h.normal x then some h
      else firstViolatedHalfspace x hs

theorem firstViolatedHalfspace_mem {d : ℕ} {x : Fin d → ℚ}
    {hs : List (RationalHalfspace d)} {h : RationalHalfspace d}
    (hfind : firstViolatedHalfspace x hs = some h) : h ∈ hs := by
  induction hs with
  | nil => simp [firstViolatedHalfspace] at hfind
  | cons g hs ih =>
      rw [firstViolatedHalfspace] at hfind
      split at hfind
      · cases hfind
        simp
      · exact List.mem_cons_of_mem _ (ih hfind)

theorem firstViolatedHalfspace_is_violated {d : ℕ} {x : Fin d → ℚ}
    {hs : List (RationalHalfspace d)} {h : RationalHalfspace d}
    (hfind : firstViolatedHalfspace x hs = some h) :
    h.offset < finiteDot h.normal x := by
  induction hs with
  | nil => simp [firstViolatedHalfspace] at hfind
  | cons g hs ih =>
      rw [firstViolatedHalfspace] at hfind
      split at hfind <;> rename_i htest
      · cases hfind
        exact htest
      · exact ih hfind

theorem firstViolatedHalfspace_eq_none_iff {d : ℕ}
    (x : Fin d → ℚ) (hs : List (RationalHalfspace d)) :
    firstViolatedHalfspace x hs = none ↔
      ∀ h ∈ hs, h.satisfiedByRational x := by
  induction hs with
  | nil => simp [firstViolatedHalfspace]
  | cons g hs ih =>
      rw [firstViolatedHalfspace]
      split <;> rename_i htest
      · constructor
        · intro hnone
          contradiction
        · intro hall
          exact ((not_lt_of_ge (hall g (by simp))) htest).elim
      · rw [ih]
        have hg : g.satisfiedByRational x := not_lt.mp htest
        simp [hg]

theorem finiteDot_sub_right_ratCast {d : ℕ}
    (a : Fin d → ℚ) (x : Fin d → ℝ) (c : Fin d → ℚ) :
    finiteDot (fun i ↦ (a i : ℝ)) (fun i ↦ x i - (c i : ℝ)) =
      finiteDot (fun i ↦ (a i : ℝ)) x -
        (finiteDot a c : ℚ) := by
  rw [finiteDot, finiteDot, finiteDot]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, Rat.cast_sum]
  simp only [Rat.cast_mul]

/-- Every exact violation gives a strict physical central cut. -/
theorem firstViolatedHalfspace_valid_cut {d : ℕ}
    {x : Fin d → ℚ} {hs : List (RationalHalfspace d)}
    {h : RationalHalfspace d}
    (hfind : firstViolatedHalfspace x hs = some h)
    {z : Fin d → ℝ} (hz : h.SatisfiedBy z) :
    finiteDot (fun i ↦ (h.normal i : ℝ))
      (fun i ↦ z i - (x i : ℝ)) < 0 := by
  have hviolateQ := firstViolatedHalfspace_is_violated hfind
  have hviolate : (h.offset : ℝ) < (finiteDot h.normal x : ℚ) := by
    exact_mod_cast hviolateQ
  rw [finiteDot_sub_right_ratCast]
  exact sub_neg.mpr (hz.trans_lt hviolate)

/-- Add an exact scan of rational linear inequalities in front of any other
central oracle. -/
def withRationalLinearConstraints {d : ℕ}
    (constraints : List (RationalHalfspace d))
    (fallback : RationalCentralOracle d) : RationalCentralOracle d :=
  fun E ↦
    match firstViolatedHalfspace E.center constraints with
    | some h => .cut h.normal
    | none => fallback E

/-- If every target point satisfies every listed inequality and the fallback
oracle is valid, then the combined executable oracle is valid. -/
theorem withRationalLinearConstraints_valid {d : ℕ}
    {K : (Fin d → ℝ) → Prop}
    (constraints : List (RationalHalfspace d))
    (hconstraints : ∀ x, K x → ∀ h ∈ constraints, h.SatisfiedBy x)
    (fallback : RationalCentralOracle d)
    (hfallback : RationalCentralOracleValid K fallback) :
    RationalCentralOracleValid K
      (withRationalLinearConstraints constraints fallback) := by
  intro E a hresponse
  rw [withRationalLinearConstraints] at hresponse
  split at hresponse <;> rename_i hfind
  · rename_i h
    cases hresponse
    refine ⟨h.normal_ne_zero, ?_⟩
    intro x hx
    exact (firstViolatedHalfspace_valid_cut hfind
      (hconstraints x hx h (firstViolatedHalfspace_mem hfind))).le
  · exact hfallback E a hresponse

/-- Conditional form used for logarithmic oracles, whose correctness is only
needed after the exact positivity constraints have passed. -/
theorem withRationalLinearConstraints_valid_of_passed {d : ℕ}
    {K : (Fin d → ℝ) → Prop}
    (constraints : List (RationalHalfspace d))
    (hconstraints : ∀ x, K x → ∀ h ∈ constraints, h.SatisfiedBy x)
    (fallback : RationalCentralOracle d)
    (hfallback : ∀ E a,
      firstViolatedHalfspace E.center constraints = none →
      fallback E = .cut a →
      a ≠ 0 ∧ ∀ x, K x → finiteDot (fun i ↦ (a i : ℝ))
        (fun i ↦ x i - rationalCenterReal E i) ≤ 0) :
    RationalCentralOracleValid K
      (withRationalLinearConstraints constraints fallback) := by
  intro E a hresponse
  rw [withRationalLinearConstraints] at hresponse
  split at hresponse <;> rename_i hfind
  · rename_i h
    cases hresponse
    refine ⟨h.normal_ne_zero, ?_⟩
    intro x hx
    exact (firstViolatedHalfspace_valid_cut hfind
      (hconstraints x hx h (firstViolatedHalfspace_mem hfind))).le
  · exact hfallback E a hfind hresponse

/-- Acceptance by the combined oracle comes from the fallback after every
linear inequality has passed. -/
theorem withRationalLinearConstraints_acceptsOnly {d : ℕ}
    {Good : (Fin d → ℚ) → Prop}
    (constraints : List (RationalHalfspace d))
    (fallback : RationalCentralOracle d)
    (hfallback : RationalCentralOracleAcceptsOnly Good fallback) :
    RationalCentralOracleAcceptsOnly Good
      (withRationalLinearConstraints constraints fallback) := by
  intro E hresponse
  rw [withRationalLinearConstraints] at hresponse
  split at hresponse
  · contradiction
  · exact hfallback E hresponse

theorem withRationalLinearConstraints_acceptsOnly_of_passed {d : ℕ}
    {Good : (Fin d → ℚ) → Prop}
    (constraints : List (RationalHalfspace d))
    (fallback : RationalCentralOracle d)
    (hfallback : ∀ E,
      firstViolatedHalfspace E.center constraints = none →
      fallback E = .accept → Good E.center) :
    RationalCentralOracleAcceptsOnly Good
      (withRationalLinearConstraints constraints fallback) := by
  intro E hresponse
  rw [withRationalLinearConstraints] at hresponse
  split at hresponse <;> rename_i hfind
  · contradiction
  · exact hfallback E hfind hresponse

end BeyondBethe
