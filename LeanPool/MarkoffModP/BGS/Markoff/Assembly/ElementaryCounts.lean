/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Core.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Elementary counts for the giant-orbit assembly

This file isolates the two elementary finite counts omitted from the paper's final assembly:

* fixing the first two coordinates of a Markoff point leaves at most two choices for the third;
* traces coming from elements of bounded order in a finite cyclic group have a deliberately crude
  quadratic cardinality bound.

The cyclicity hypothesis in the second count is essential: the analogous statement for arbitrary
finite groups is false (an elementary abelian `2`-group can have more than two elements of order
two).  The split and norm-one tori to which this count will eventually be applied are cyclic.
-/

namespace BGS.Markoff

open Polynomial

section ThirdCoordinateFiber

variable {F : Type*} [Field F]

/-- The monic quadratic obtained from the Markoff equation after fixing its first two
coordinates. -/
noncomputable def thirdCoordinatePolynomial (a b : F) : F[X] :=
  X ^ 2 - C (3 * a * b) * X + C (a ^ 2 + b ^ 2)

@[simp]
theorem thirdCoordinatePolynomial_eval (a b c : F) :
    (thirdCoordinatePolynomial a b).eval c = markoffPolynomial ⟨a, b, c⟩ := by
  simp [thirdCoordinatePolynomial, markoffPolynomial]
  ring

theorem thirdCoordinatePolynomial_monic (a b : F) :
    (thirdCoordinatePolynomial a b).Monic := by
  exact (isMonicOfDegree_sub_add_two (3 * a * b) (a ^ 2 + b ^ 2)).monic

@[simp]
theorem thirdCoordinatePolynomial_natDegree (a b : F) :
    (thirdCoordinatePolynomial a b).natDegree = 2 := by
  exact (isMonicOfDegree_sub_add_two (3 * a * b) (a ^ 2 + b ^ 2)).natDegree_eq

variable [Fintype F]

/-- The possible third coordinates of Markoff points whose first two coordinates are `a,b`. -/
noncomputable def thirdCoordinatesOnMarkoffSurface (a b : F) : Finset F := by
  classical
  exact Finset.univ.filter fun c => IsMarkoff ⟨a, b, c⟩

theorem thirdCoordinatesOnMarkoffSurface_card_le_two (a b : F) :
    (thirdCoordinatesOnMarkoffSurface a b).card ≤ 2 := by
  classical
  let f := thirdCoordinatePolynomial a b
  have hf : f ≠ 0 := (thirdCoordinatePolynomial_monic a b).ne_zero
  have hsubset : thirdCoordinatesOnMarkoffSurface a b ⊆ f.roots.toFinset := by
    intro c hc
    rw [thirdCoordinatesOnMarkoffSurface, Finset.mem_filter] at hc
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hf]
    simpa [f, IsMarkoff] using hc.2
  calc
    (thirdCoordinatesOnMarkoffSurface a b).card ≤ f.roots.toFinset.card :=
      Finset.card_mono hsubset
    _ ≤ f.roots.card := Multiset.toFinset_card_le _
    _ ≤ f.natDegree := Polynomial.card_roots' f
    _ = 2 := thirdCoordinatePolynomial_natDegree a b

/-- Markoff-surface points, represented in the project's ambient `Point` type, with prescribed
first and second coordinates. -/
noncomputable def markoffPointsWithFirstTwoCoordinates (a b : F) : Finset (Point F) := by
  classical
  exact (thirdCoordinatesOnMarkoffSurface a b).image fun c => ⟨a, b, c⟩

theorem mem_markoffPointsWithFirstTwoCoordinates_iff {a b : F} {x : Point F} :
    x ∈ markoffPointsWithFirstTwoCoordinates a b ↔
      IsMarkoff x ∧ x.x1 = a ∧ x.x2 = b := by
  classical
  constructor
  · intro hx
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx
    rw [thirdCoordinatesOnMarkoffSurface, Finset.mem_filter] at hc
    exact ⟨hc.2, rfl, rfl⟩
  · rintro ⟨hmarkoff, hx1, hx2⟩
    have hpoint : (⟨a, b, x.x3⟩ : Point F) = x := by
      ext <;> simp [hx1, hx2]
    apply Finset.mem_image.mpr
    refine ⟨x.x3, ?_, hpoint⟩
    · rw [thirdCoordinatesOnMarkoffSurface, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [hpoint]
      exact hmarkoff

theorem markoffPointsWithFirstTwoCoordinates_card_le_two (a b : F) :
    (markoffPointsWithFirstTwoCoordinates a b).card ≤ 2 := by
  classical
  exact Finset.card_image_le.trans (thirdCoordinatesOnMarkoffSurface_card_le_two a b)

end ThirdCoordinateFiber

section LowOrderTrace

variable {G T : Type*} [Group G] [Fintype G] [DecidableEq T]

/-- Elements of a finite group whose multiplicative order is strictly below `bound`. -/
noncomputable def elementsOfOrderLessThan
    (G : Type*) [Group G] [Fintype G] (bound : ℕ) : Finset G :=
  Finset.univ.filter fun g => orderOf g < bound

/-- Values of a trace-like map on group elements whose multiplicative order is below `bound`. -/
noncomputable def boundedOrderTraceSet (trace : G → T) (bound : ℕ) : Finset T :=
  (elementsOfOrderLessThan G bound).image trace

theorem elementsOfOrderLessThan_card_le_sum_range [IsCyclic G] (bound : ℕ) :
    (elementsOfOrderLessThan G bound).card ≤ ∑ d ∈ Finset.range bound, d := by
  classical
  rw [elementsOfOrderLessThan]
  rw [Finset.card_eq_sum_card_fiberwise
    (t := Finset.range bound) (f := orderOf) (by
      intro g hg
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hg).2)]
  apply Finset.sum_le_sum
  intro d hd
  rw [Finset.mem_range] at hd
  have hfiber :
      (Finset.univ.filter fun g : G => orderOf g < bound).filter (fun g => orderOf g = d) =
        Finset.univ.filter (fun g : G => orderOf g = d) := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨h ▸ hd, h⟩
  rw [hfiber]
  by_cases hdvd : d ∣ Fintype.card G
  · rw [IsCyclic.card_orderOf_eq_totient hdvd]
    exact Nat.totient_le d
  · have hempty : Finset.univ.filter (fun g : G => orderOf g = d) = ∅ := by
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false]
      intro horder
      apply hdvd
      rw [← horder]
      exact orderOf_dvd_card
    simp [hempty]

/-- A divisor-sensitive version of the bounded-order count.  Only orders dividing the group
cardinality can occur, and each such order contributes fewer than `bound` elements. -/
theorem elementsOfOrderLessThan_card_le_pred_mul_card_divisors [IsCyclic G] (bound : ℕ) :
    (elementsOfOrderLessThan G bound).card ≤
      (bound - 1) * (Fintype.card G).divisors.card := by
  classical
  have hcard : Fintype.card G ≠ 0 := Fintype.card_ne_zero
  rw [elementsOfOrderLessThan]
  rw [Finset.card_eq_sum_card_fiberwise
    (t := Finset.range bound) (f := orderOf) (by
      intro g hg
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hg).2)]
  calc
    (∑ d ∈ Finset.range bound,
        ((Finset.univ.filter fun g : G => orderOf g < bound).filter
          fun g => orderOf g = d).card) ≤
        ∑ d ∈ Finset.range bound,
          if d ∣ Fintype.card G then bound - 1 else 0 := by
      apply Finset.sum_le_sum
      intro d hd
      by_cases hdvd : d ∣ Fintype.card G
      · rw [if_pos hdvd]
        have hfiber :
            (Finset.univ.filter fun g : G => orderOf g < bound).filter
                (fun g => orderOf g = d) =
              Finset.univ.filter (fun g : G => orderOf g = d) := by
          ext g
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · exact fun h => h.2
          · intro h
            exact ⟨h ▸ Finset.mem_range.mp hd, h⟩
        rw [hfiber, IsCyclic.card_orderOf_eq_totient hdvd]
        exact (Nat.totient_le d).trans (Nat.le_sub_one_of_lt (Finset.mem_range.mp hd))
      · rw [if_neg hdvd]
        have hempty : Finset.univ.filter (fun g : G => orderOf g = d) = ∅ := by
          ext g
          simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.notMem_empty, iff_false]
          intro horder
          apply hdvd
          rw [← horder]
          exact orderOf_dvd_card
        have hfiber :
            (Finset.univ.filter fun g : G => orderOf g < bound).filter
                (fun g => orderOf g = d) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro g hg
          have hgOrder := (Finset.mem_filter.mp hg).2
          have : g ∈ Finset.univ.filter (fun g : G => orderOf g = d) := by
            simp [hgOrder]
          rw [hempty] at this
          exact (Finset.notMem_empty g) this
        simp [hfiber]
    _ = (bound - 1) * ((Finset.range bound).filter
        fun d => d ∣ Fintype.card G).card := by
      rw [← Finset.sum_filter]
      simp [mul_comm]
    _ ≤ (bound - 1) * (Fintype.card G).divisors.card := by
      gcongr
      intro d hd
      rw [Finset.mem_filter] at hd
      exact Nat.mem_divisors.mpr ⟨hd.2, hcard⟩

theorem elementsOfOrderLessThan_card_le_bound_mul_card_divisors [IsCyclic G] (bound : ℕ) :
    (elementsOfOrderLessThan G bound).card ≤
      bound * (Fintype.card G).divisors.card := by
  exact (elementsOfOrderLessThan_card_le_pred_mul_card_divisors bound).trans <| by
    gcongr
    omega

theorem boundedOrderTraceSet_card_le_sum_range [IsCyclic G]
    (trace : G → T) (bound : ℕ) :
    (boundedOrderTraceSet trace bound).card ≤ ∑ d ∈ Finset.range bound, d := by
  exact Finset.card_image_le.trans (elementsOfOrderLessThan_card_le_sum_range bound)

theorem boundedOrderTraceSet_card_le_bound_mul_card_divisors [IsCyclic G]
    (trace : G → T) (bound : ℕ) :
    (boundedOrderTraceSet trace bound).card ≤
      bound * (Fintype.card G).divisors.card := by
  exact Finset.card_image_le.trans
    (elementsOfOrderLessThan_card_le_bound_mul_card_divisors bound)

theorem boundedOrderTraceSet_card_le_pred_mul_card_divisors [IsCyclic G]
    (trace : G → T) (bound : ℕ) :
    (boundedOrderTraceSet trace bound).card ≤
      (bound - 1) * (Fintype.card G).divisors.card := by
  exact Finset.card_image_le.trans
    (elementsOfOrderLessThan_card_le_pred_mul_card_divisors bound)

theorem sum_orders_below_bound_le_bound_sq (bound : ℕ) :
    (∑ d ∈ Finset.range bound, d) ≤ bound ^ 2 := by
  calc
    (∑ d ∈ Finset.range bound, d) ≤
        ∑ _d ∈ Finset.range bound, bound := by
      gcongr with d hd
      exact Nat.le_of_lt (Finset.mem_range.mp hd)
    _ = bound * bound := by simp
    _ = bound ^ 2 := by ring

theorem boundedOrderTraceSet_card_le_bound_sq [IsCyclic G]
    (trace : G → T) (bound : ℕ) :
    (boundedOrderTraceSet trace bound).card ≤ bound ^ 2 :=
  (boundedOrderTraceSet_card_le_sum_range trace bound).trans
    (sum_orders_below_bound_le_bound_sq bound)

/-- The union of bounded-order trace values from the split and norm-one tori, together with a
finite set of exceptional (parabolic) trace values. -/
noncomputable def lowOrderTraceSet
    {Gsplit Gnonsplit T : Type*}
    [Group Gsplit] [Fintype Gsplit] [Group Gnonsplit] [Fintype Gnonsplit] [DecidableEq T]
    (parabolic : Finset T) (splitTrace : Gsplit → T) (nonsplitTrace : Gnonsplit → T)
    (bound : ℕ) : Finset T :=
  parabolic ∪ boundedOrderTraceSet splitTrace bound ∪ boundedOrderTraceSet nonsplitTrace bound

theorem lowOrderTraceSet_card_le
    {Gsplit Gnonsplit T : Type*}
    [Group Gsplit] [Fintype Gsplit] [IsCyclic Gsplit]
    [Group Gnonsplit] [Fintype Gnonsplit] [IsCyclic Gnonsplit]
    [DecidableEq T]
    (parabolic : Finset T) (splitTrace : Gsplit → T) (nonsplitTrace : Gnonsplit → T)
    (bound : ℕ) :
    (lowOrderTraceSet parabolic splitTrace nonsplitTrace bound).card ≤
      parabolic.card + 2 * ∑ d ∈ Finset.range bound, d := by
  unfold lowOrderTraceSet
  calc
    (parabolic ∪ boundedOrderTraceSet splitTrace bound ∪
        boundedOrderTraceSet nonsplitTrace bound).card ≤
        (parabolic ∪ boundedOrderTraceSet splitTrace bound).card +
          (boundedOrderTraceSet nonsplitTrace bound).card :=
      Finset.card_union_le
        (parabolic ∪ boundedOrderTraceSet splitTrace bound)
        (boundedOrderTraceSet nonsplitTrace bound)
    _ ≤ (parabolic.card + (boundedOrderTraceSet splitTrace bound).card) +
          (boundedOrderTraceSet nonsplitTrace bound).card := by
      gcongr
      exact Finset.card_union_le parabolic (boundedOrderTraceSet splitTrace bound)
    _ ≤ (parabolic.card + (∑ d ∈ Finset.range bound, d)) +
          (∑ d ∈ Finset.range bound, d) := by
      gcongr
      · exact boundedOrderTraceSet_card_le_sum_range splitTrace bound
      · exact boundedOrderTraceSet_card_le_sum_range nonsplitTrace bound
    _ = parabolic.card + 2 * ∑ d ∈ Finset.range bound, d := by omega

theorem lowOrderTraceSet_card_le_parabolic_add_two_mul_bound_sq
    {Gsplit Gnonsplit T : Type*}
    [Group Gsplit] [Fintype Gsplit] [IsCyclic Gsplit]
    [Group Gnonsplit] [Fintype Gnonsplit] [IsCyclic Gnonsplit]
    [DecidableEq T]
    (parabolic : Finset T) (splitTrace : Gsplit → T) (nonsplitTrace : Gnonsplit → T)
    (bound : ℕ) :
    (lowOrderTraceSet parabolic splitTrace nonsplitTrace bound).card ≤
      parabolic.card + 2 * bound ^ 2 := by
  exact (lowOrderTraceSet_card_le parabolic splitTrace nonsplitTrace bound).trans <| by
    gcongr
    exact sum_orders_below_bound_le_bound_sq bound

/-- A divisor-sensitive count for the union of the two bounded-order trace sets. -/
theorem lowOrderTraceSet_card_le_parabolic_add_pred_mul_divisor_cards
    {Gsplit Gnonsplit T : Type*}
    [Group Gsplit] [Fintype Gsplit] [IsCyclic Gsplit]
    [Group Gnonsplit] [Fintype Gnonsplit] [IsCyclic Gnonsplit]
    [DecidableEq T]
    (parabolic : Finset T) (splitTrace : Gsplit → T) (nonsplitTrace : Gnonsplit → T)
    (bound : ℕ) :
    (lowOrderTraceSet parabolic splitTrace nonsplitTrace bound).card ≤
      parabolic.card + (bound - 1) *
        ((Fintype.card Gsplit).divisors.card + (Fintype.card Gnonsplit).divisors.card) := by
  unfold lowOrderTraceSet
  calc
    (parabolic ∪ boundedOrderTraceSet splitTrace bound ∪
        boundedOrderTraceSet nonsplitTrace bound).card ≤
        (parabolic ∪ boundedOrderTraceSet splitTrace bound).card +
          (boundedOrderTraceSet nonsplitTrace bound).card :=
      Finset.card_union_le
        (parabolic ∪ boundedOrderTraceSet splitTrace bound)
        (boundedOrderTraceSet nonsplitTrace bound)
    _ ≤ (parabolic.card + (boundedOrderTraceSet splitTrace bound).card) +
          (boundedOrderTraceSet nonsplitTrace bound).card := by
      gcongr
      exact Finset.card_union_le parabolic (boundedOrderTraceSet splitTrace bound)
    _ ≤ (parabolic.card +
          (bound - 1) * (Fintype.card Gsplit).divisors.card) +
        (bound - 1) * (Fintype.card Gnonsplit).divisors.card := by
      gcongr
      · exact boundedOrderTraceSet_card_le_pred_mul_card_divisors splitTrace bound
      · exact boundedOrderTraceSet_card_le_pred_mul_card_divisors nonsplitTrace bound
    _ = parabolic.card + (bound - 1) *
        ((Fintype.card Gsplit).divisors.card +
          (Fintype.card Gnonsplit).divisors.card) := by
      rw [Nat.mul_add]
      omega

theorem lowOrderTraceSet_card_le_parabolic_add_bound_mul_divisor_cards
    {Gsplit Gnonsplit T : Type*}
    [Group Gsplit] [Fintype Gsplit] [IsCyclic Gsplit]
    [Group Gnonsplit] [Fintype Gnonsplit] [IsCyclic Gnonsplit]
    [DecidableEq T]
    (parabolic : Finset T) (splitTrace : Gsplit → T) (nonsplitTrace : Gnonsplit → T)
    (bound : ℕ) :
    (lowOrderTraceSet parabolic splitTrace nonsplitTrace bound).card ≤
      parabolic.card + bound *
        ((Fintype.card Gsplit).divisors.card + (Fintype.card Gnonsplit).divisors.card) := by
  exact (lowOrderTraceSet_card_le_parabolic_add_pred_mul_divisor_cards
    parabolic splitTrace nonsplitTrace bound).trans <| by
      gcongr
      omega

end LowOrderTrace

end BGS.Markoff
