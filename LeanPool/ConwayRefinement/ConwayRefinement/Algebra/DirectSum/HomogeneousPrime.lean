/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.DirectSum.HomogeneousDivisibility
public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.DirectSum.LeadingGrade

import Mathlib.Tactic.Abel
import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Algebra.Prime.Defs

/-!
# Primality of a homogeneous element from its homogeneous divisibility property

In a graded direct sum whose homogeneous components multiply without cancellation, a
homogeneous element dividing one of the two factors of every homogeneous product it divides
does so for every product it divides. The induction is on the total number of nonzero
components, so it is uniform in the grading monoid and in the grade of the divisor.
-/

open scoped DirectSum

universe u v

public noncomputable section

namespace DirectSum

variable {ι : Type u} (A : ι → Type v)
  [LinearOrder ι] [AddCommMonoid ι] [IsOrderedCancelAddMonoid ι]
  [∀ i, AddCommGroup (A i)] [DirectSum.GCommRing A]

open scoped Classical in
omit [IsOrderedCancelAddMonoid ι] in
private theorem card_support_sub_lt {x : DirectSum ι A} {m : ι} (hm : x m ≠ 0) :
    (DFinsupp.support (x - DirectSum.of A m (x m))).card <
      (DFinsupp.support x).card := by
  classical
  refine Finset.card_lt_card ⟨fun j hj ↦ ?_, fun hsub ↦ ?_⟩
  · rw [DFinsupp.mem_support_iff] at hj ⊢
    intro hzero
    apply hj
    by_cases hjm : j = m
    · subst j
      simp [DirectSum.sub_apply]
    · simp [DirectSum.sub_apply, DirectSum.of_apply, Ne.symm hjm, hzero]
  · have hmem := hsub (DFinsupp.mem_support_iff.mpr hm)
    rw [DFinsupp.mem_support_iff] at hmem
    exact hmem (by simp [DirectSum.sub_apply])

theorem dvd_or_dvd_of_homogeneous_dvd_or_dvd
    {i : ι} (a : A i)
    (hhom : ∀ (j k : ι) (b : A j) (c : A k),
      DirectSum.of A i a ∣ DirectSum.of A j b * DirectSum.of A k c →
        DirectSum.of A i a ∣ DirectSum.of A j b ∨
        DirectSum.of A i a ∣ DirectSum.of A k c)
    (x y : DirectSum ι A) (hdvd : DirectSum.of A i a ∣ x * y) :
    DirectSum.of A i a ∣ x ∨ DirectSum.of A i a ∣ y := by
  classical
  generalize hcard : (DFinsupp.support x).card + (DFinsupp.support y).card = n
  induction n using Nat.strong_induction_on generalizing x y with
  | _ n ih =>
    by_cases hx : x = 0
    · exact Or.inl (hx ▸ ⟨0, (mul_zero _).symm⟩)
    by_cases hy : y = 0
    · exact Or.inr (hy ▸ ⟨0, (mul_zero _).symm⟩)
    obtain ⟨m, hmlead, hmne⟩ := exists_grade_eq_leadingGrade A hx
    obtain ⟨p, hplead, hpne⟩ := exists_grade_eq_leadingGrade A hy
    have htop : (x * y) (m + p) = GradedMonoid.GMul.mul (x m) (y p) :=
      mul_apply_add_eq_of_leadingGrade_eq A hmlead hplead
    have hsplit : DirectSum.of A i a ∣
        DirectSum.of A m (x m) * DirectSum.of A p (y p) := by
      have hcomp := (of_dvd_iff_dvd_components A a (x * y)).mp hdvd (m + p)
      rwa [htop, ← DirectSum.of_mul_of] at hcomp
    rcases hhom m p (x m) (y p) hsplit with hxm | hyp
    · have hrest : DirectSum.of A i a ∣ (x - DirectSum.of A m (x m)) * y := by
        rw [sub_mul]
        exact dvd_sub hdvd (dvd_mul_of_dvd_left hxm y)
      have hlt : (DFinsupp.support (x - DirectSum.of A m (x m))).card +
          (DFinsupp.support y).card < n := by
        rw [← hcard]
        exact Nat.add_lt_add_right (card_support_sub_lt A hmne) _
      rcases ih _ hlt _ _ hrest rfl with hrec | hrec
      · refine Or.inl ?_
        have hx' : x = (x - DirectSum.of A m (x m)) + DirectSum.of A m (x m) := by abel
        rw [hx']
        exact dvd_add hrec hxm
      · exact Or.inr hrec
    · have hrest : DirectSum.of A i a ∣ x * (y - DirectSum.of A p (y p)) := by
        rw [mul_sub]
        exact dvd_sub hdvd (dvd_mul_of_dvd_right hyp x)
      have hlt : (DFinsupp.support x).card +
          (DFinsupp.support (y - DirectSum.of A p (y p))).card < n := by
        rw [← hcard]
        exact Nat.add_lt_add_left (card_support_sub_lt A hpne) _
      rcases ih _ hlt _ _ hrest rfl with hrec | hrec
      · exact Or.inl hrec
      · refine Or.inr ?_
        have hy' : y = (y - DirectSum.of A p (y p)) + DirectSum.of A p (y p) := by abel
        rw [hy']
        exact dvd_add hrec hyp

theorem prime_of_homogeneous_dvd_or_dvd
    {i : ι} (a : A i)
    (hne : DirectSum.of A i a ≠ 0)
    (hunit : ¬ IsUnit (DirectSum.of A i a))
    (hhom : ∀ (j k : ι) (b : A j) (c : A k),
      DirectSum.of A i a ∣ DirectSum.of A j b * DirectSum.of A k c →
        DirectSum.of A i a ∣ DirectSum.of A j b ∨
        DirectSum.of A i a ∣ DirectSum.of A k c) :
    Prime (DirectSum.of A i a) :=
  ⟨hne, hunit, fun x y hdvd ↦
    dvd_or_dvd_of_homogeneous_dvd_or_dvd A a hhom x y hdvd⟩

theorem irreducible_of_homogeneous_of_grade_not_split {i : ι} (a : A i)
    (hmulne : ∀ {j k : ι} (u : A j) (v : A k), u ≠ 0 → v ≠ 0 →
      GradedMonoid.GMul.mul u v ≠ 0)
    (hbot : ∀ j : ι, 0 ≤ j)
    (hunitZero : ∀ u : A 0, u ≠ 0 → IsUnit (DirectSum.of A 0 u))
    (hsplit : ∀ j k : ι, j + k = i → j = 0 ∨ k = 0)
    (hne : DirectSum.of A i a ≠ 0)
    (hunit : ¬ IsUnit (DirectSum.of A i a)) :
    Irreducible (DirectSum.of A i a) := by
  classical
  have ha : a ≠ 0 := by
    intro h
    exact hne (by rw [h, map_zero])
  refine ⟨hunit, fun x y hxy ↦ ?_⟩
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, zero_mul] at hxy
    exact hne hxy
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, mul_zero] at hxy
    exact hne hxy
  obtain ⟨m, hm, hxm⟩ := exists_grade_eq_leadingGrade A hx0
  obtain ⟨n, hn, hyn⟩ := exists_grade_eq_leadingGrade A hy0
  have hlead : leadingGrade A x + leadingGrade A y = ((i : ι) : WithBot ι) := by
    rw [← leadingGrade_mul A hmulne x y, ← hxy, leadingGrade_of A ha]
  rw [hm, hn, ← WithBot.coe_add, WithBot.coe_eq_coe] at hlead
  have key : ∀ z : DirectSum ι A, z ≠ 0 → leadingGrade A z = ((0 : ι) : WithBot ι) →
      IsUnit z := by
    intro z hz hlz
    have hconc : z = DirectSum.of A 0 (z 0) := by
      refine DFinsupp.ext fun j ↦ ?_
      by_cases hj : j = 0
      · subst hj
        simp
      · have hzj : z j = 0 := by
          by_contra hjne
          have hle := grade_le_leadingGrade A hjne
          rw [hlz, WithBot.coe_le_coe] at hle
          exact hj (le_antisymm hle (hbot j))
        rw [hzj, DirectSum.of_apply, dif_neg (Ne.symm hj)]
    have hz0 : z 0 ≠ 0 := by
      intro h
      apply hz
      rw [hconc, h, map_zero]
    rw [hconc]
    exact hunitZero _ hz0
  rcases hsplit m n hlead with hm0 | hn0
  · exact Or.inl (key x hx0 (by rw [hm, hm0]))
  · exact Or.inr (key y hy0 (by rw [hn, hn0]))

end DirectSum

end
