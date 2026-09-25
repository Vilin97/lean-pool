/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.RightInversionPairing

/-!
# Finite unions of nonparabolic trace supports

The middle game only needs to exclude right traces coming from nonparabolic
coordinates: a parabolic target already lies above the endgame threshold.
This module packages that logical split before any numerical estimate is
inserted.  In particular, the inversion-pairing factor can be applied to each
right subgroup without counting its two fixed points.
-/

@[expose] public section

namespace BGS.Markoff

variable {E : Type*} [Field E] [Fintype E]

/-- Left elements meeting a nonparabolic point in one of a finite family of
right subgroups. -/
noncomputable def weightedNonparabolicBadOrderTraceSupport
    (alpha beta : E) (Hleft : Subgroup Eˣ) (orders : Finset ℕ)
    (rightSubgroup : ℕ → Subgroup Eˣ) : Finset Hleft := by
  classical
  exact orders.biUnion fun d ↦
    weightedTraceEquationNonparabolicLeftSupport
      alpha beta Hleft (rightSubgroup d)

@[simp]
theorem mem_weightedNonparabolicBadOrderTraceSupport_iff
    {alpha beta : E} {Hleft : Subgroup Eˣ} {orders : Finset ℕ}
    {rightSubgroup : ℕ → Subgroup Eˣ} {hleft : Hleft} :
    hleft ∈ weightedNonparabolicBadOrderTraceSupport
        alpha beta Hleft orders rightSubgroup ↔
      ∃ d ∈ orders, ∃ hright : rightSubgroup d,
        weightedSplitTorusTrace alpha beta hleft =
            splitTorusTrace hright ∧
          ((hright : Eˣ) ^ 2) ≠ 1 := by
  classical
  simp [weightedNonparabolicBadOrderTraceSupport]

/-- Bounds on the individual nonparabolic left supports sum over an arbitrary
finite family of candidate right subgroups. -/
theorem weightedNonparabolicBadOrderTraceSupport_card_cast_le_sum
    (alpha beta : E) (Hleft : Subgroup Eˣ) (orders : Finset ℕ)
    (rightSubgroup : ℕ → Subgroup Eˣ) (bound : ℕ → ℝ)
    (hbound : ∀ d ∈ orders,
      ((weightedTraceEquationNonparabolicLeftSupport
        alpha beta Hleft (rightSubgroup d)).card : ℝ) ≤ bound d) :
    ((weightedNonparabolicBadOrderTraceSupport
      alpha beta Hleft orders rightSubgroup).card : ℝ) ≤
        ∑ d ∈ orders, bound d := by
  classical
  calc
    ((weightedNonparabolicBadOrderTraceSupport
        alpha beta Hleft orders rightSubgroup).card : ℝ) ≤
        ∑ d ∈ orders,
          ((weightedTraceEquationNonparabolicLeftSupport
            alpha beta Hleft (rightSubgroup d)).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le :
        (weightedNonparabolicBadOrderTraceSupport
          alpha beta Hleft orders rightSubgroup).card ≤
            ∑ d ∈ orders,
              (weightedTraceEquationNonparabolicLeftSupport
                alpha beta Hleft (rightSubgroup d)).card)
    _ ≤ ∑ d ∈ orders, bound d := Finset.sum_le_sum hbound

/-- If the summed nonparabolic support bound is smaller than the left
subgroup, one left element avoids every nonparabolic candidate trace. -/
theorem exists_left_element_escaping_nonparabolic_orders_of_sum_bound
    (alpha beta : E) (Hleft : Subgroup Eˣ) (orders : Finset ℕ)
    (rightSubgroup : ℕ → Subgroup Eˣ) (bound : ℕ → ℝ)
    (hbound : ∀ d ∈ orders,
      ((weightedTraceEquationNonparabolicLeftSupport
        alpha beta Hleft (rightSubgroup d)).card : ℝ) ≤ bound d)
    (hsmall : (∑ d ∈ orders, bound d) < Nat.card Hleft) :
    ∃ hleft : Hleft, ∀ d ∈ orders, ∀ hright : rightSubgroup d,
      ((hright : Eˣ) ^ 2) ≠ 1 →
        weightedSplitTorusTrace alpha beta hleft ≠
          splitTorusTrace hright := by
  classical
  let bad :=
    weightedNonparabolicBadOrderTraceSupport
      alpha beta Hleft orders rightSubgroup
  have hbadReal : (bad.card : ℝ) < (Nat.card Hleft : ℝ) :=
    (weightedNonparabolicBadOrderTraceSupport_card_cast_le_sum
      alpha beta Hleft orders rightSubgroup bound hbound).trans_lt hsmall
  have hbad : bad.card < Nat.card Hleft := by
    exact_mod_cast hbadReal
  have hexists : ∃ hleft : Hleft, hleft ∉ bad := by
    by_contra hall
    push Not at hall
    have hle : (Finset.univ : Finset Hleft).card ≤ bad.card :=
      Finset.card_le_card fun hleft _ ↦ hall hleft
    rw [Finset.card_univ, Fintype.card_eq_nat_card] at hle
    exact (Nat.not_le_of_lt hbad) hle
  obtain ⟨hleft, hleftNotBad⟩ := hexists
  refine ⟨hleft, ?_⟩
  intro d hd hright hrightSq heq
  apply hleftNotBad
  exact mem_weightedNonparabolicBadOrderTraceSupport_iff.mpr
    ⟨d, hd, hright, heq, hrightSq⟩

end BGS.Markoff
