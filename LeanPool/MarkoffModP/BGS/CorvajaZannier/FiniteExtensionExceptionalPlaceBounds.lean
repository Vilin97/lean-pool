/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionExceptionalSupport
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.FiniteExtensionOneSubGcdHeight
public import Mathlib.Tactic

/-!
# Direct weighted bounds on exhaustive exceptional places

The family-place API is useful when several functions are indexed together.
The canonical global summation, however, is stated directly on the exhaustive
sum of finite and infinite places.  This file records the corresponding
subset lower bound and specializes it to the one-minus quotient used in
Proposition 2.
-/

@[expose] public section

namespace BGS.CorvajaZannier

noncomputable section

open scoped BigOperators

variable (K : Type*) [Field K] [DecidableEq K] [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

attribute [local instance] Classical.decEq

omit [DecidableEq K] in
/-- The first coordinate has order zero away from the direct Proposition 2
exceptional set. -/
theorem finiteExtensionPrincipalDivisor_u_eq_zero_outside_propositionTwoExceptionalPlaces
    (u v : L) (P : FiniteExtensionPlace K L)
    (hP : P ∉ propositionTwoExceptionalPlaces K L u v) :
    finiteExtensionPrincipalDivisor K L u P = 0 := by
  apply Finsupp.notMem_support_iff.mp
  intro hmem
  apply hP
  rw [propositionTwoExceptionalPlaces]
  exact Finset.mem_union_left _ hmem

omit [DecidableEq K] in
/-- The second coordinate has order zero away from the direct Proposition 2
exceptional set. -/
theorem finiteExtensionPrincipalDivisor_v_eq_zero_outside_propositionTwoExceptionalPlaces
    (u v : L) (P : FiniteExtensionPlace K L)
    (hP : P ∉ propositionTwoExceptionalPlaces K L u v) :
    finiteExtensionPrincipalDivisor K L v P = 0 := by
  apply Finsupp.notMem_support_iff.mp
  intro hmem
  apply hP
  rw [propositionTwoExceptionalPlaces]
  exact Finset.mem_union_right _ hmem

omit [DecidableEq K] in
/-- Every positive-order place of the second coordinate belongs to the direct
Proposition 2 exceptional set. -/
theorem mem_propositionTwoExceptionalPlaces_of_v_order_pos
    (u v : L) (P : FiniteExtensionPlace K L)
    (hP : 0 < finiteExtensionPrincipalDivisor K L v P) :
    P ∈ propositionTwoExceptionalPlaces K L u v := by
  rw [propositionTwoExceptionalPlaces]
  exact Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr (ne_of_gt hP))

/-- Every auxiliary grid product has order zero away from the direct
Proposition 2 exceptional set. -/
theorem finiteExtensionPrincipalDivisor_auxiliaryGridProduct_eq_zero_outside_propositionTwoExceptionalPlaces
    (u v : L) (hu : u ≠ 0) (hv : v ≠ 0)
    (h k : ℕ) (P : FiniteExtensionPlace K L)
    (hP : P ∉ propositionTwoExceptionalPlaces K L u v) :
    finiteExtensionPrincipalDivisor K L
      (finiteExtensionAuxiliaryGridProduct L u v h k) P = 0 := by
  rw [finiteExtensionPrincipalDivisor_auxiliaryGridProduct K L u v hu hv h k]
  have huP :=
    finiteExtensionPrincipalDivisor_u_eq_zero_outside_propositionTwoExceptionalPlaces
      K L u v P hP
  have hvP :=
    finiteExtensionPrincipalDivisor_v_eq_zero_outside_propositionTwoExceptionalPlaces
      K L u v P hP
  simp only [Finset.sum_apply', Finsupp.add_apply, Finsupp.smul_apply,
    huP, hvP, nsmul_zero, add_zero, Finset.sum_const_zero]

/-- On any finite set of exhaustive places, the weighted order sum of a
function is bounded below by minus its full pole height. -/
theorem finiteExtensionWeightedOrder_sum_ge_neg_height
    (x : L) (S : Finset (FiniteExtensionPlace K L)) :
    -((finiteExtensionHeight K L x : ℕ) : ℤ) ≤
      ∑ P ∈ S, finiteExtensionPrincipalDivisor K L x P *
        (finiteExtensionPlaceDegree K L P : ℤ) := by
  classical
  let D := finiteExtensionPrincipalDivisor K L x
  let N := D.support.filter (fun P => D P < 0)
  let T := S.filter (fun P => D P < 0)
  have hTN : T ⊆ N := by
    intro P hP
    have hneg : D P < 0 := (Finset.mem_filter.mp hP).2
    exact Finset.mem_filter.mpr
      ⟨Finsupp.mem_support_iff.mpr (ne_of_lt hneg), hneg⟩
  have hfilterTN : N.filter (fun P => P ∈ T) = T := by
    ext P
    simp only [Finset.mem_filter]
    constructor
    · exact fun hP => hP.2
    · exact fun hP => ⟨hTN hP, hP⟩
  have hMissingNonpos :
      ∑ P ∈ N.filter (fun P => P ∉ T),
          D P * (finiteExtensionPlaceDegree K L P : ℤ) ≤ 0 := by
    apply Finset.sum_nonpos
    intro P hP
    have hneg : D P < 0 :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hP).1).2
    exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt hneg) (by positivity)
  have hNegativeAllLeT :
      (∑ P ∈ N, D P * (finiteExtensionPlaceDegree K L P : ℤ)) ≤
        ∑ P ∈ T, D P * (finiteExtensionPlaceDegree K L P : ℤ) := by
    have hsplit := Finset.sum_filter_add_sum_filter_not N
      (fun P => P ∈ T)
      (fun P => D P * (finiteExtensionPlaceDegree K L P : ℤ))
    rw [hfilterTN] at hsplit
    linarith
  have hRemainingNonneg :
      0 ≤ ∑ P ∈ S.filter (fun P => ¬ D P < 0),
        D P * (finiteExtensionPlaceDegree K L P : ℤ) := by
    apply Finset.sum_nonneg
    intro P hP
    have hnonneg : 0 ≤ D P := le_of_not_gt (Finset.mem_filter.mp hP).2
    exact mul_nonneg hnonneg (by positivity)
  have hTLeS :
      (∑ P ∈ T, D P * (finiteExtensionPlaceDegree K L P : ℤ)) ≤
        ∑ P ∈ S, D P * (finiteExtensionPlaceDegree K L P : ℤ) := by
    have hsplit := Finset.sum_filter_add_sum_filter_not S
      (fun P => D P < 0)
      (fun P => D P * (finiteExtensionPlaceDegree K L P : ℤ))
    change
      (∑ P ∈ T, D P * (finiteExtensionPlaceDegree K L P : ℤ)) +
          ∑ P ∈ S.filter (fun P => ¬ D P < 0),
            D P * (finiteExtensionPlaceDegree K L P : ℤ) =
        ∑ P ∈ S, D P * (finiteExtensionPlaceDegree K L P : ℤ) at hsplit
    linarith
  have hNegativeAll := finiteExtensionHeight_negativeSum K L x
  change -((finiteExtensionHeight K L x : ℕ) : ℤ) =
    ∑ P ∈ N, D P * (finiteExtensionPlaceDegree K L P : ℤ) at hNegativeAll
  rw [hNegativeAll]
  exact hNegativeAllLeT.trans hTLeS

/-- The exceptional-set contribution of `(1-u)/(1-v)` is bounded below by
minus the sum of the two coordinate heights.  The assertion holds for every
finite set, and hence in particular for the zero-and-pole set of `u,v`. -/
theorem finiteExtensionOneSubU_div_oneSubV_weightedOrder_lower_bound
    (u v : L) (hu : u ≠ 0) (hv : v ≠ 0)
    (huone : u ≠ 1) (hvone : v ≠ 1)
    (S : Finset (FiniteExtensionPlace K L)) :
    -((finiteExtensionPositiveDegree K L u : ℕ) : ℤ) -
        (finiteExtensionPositiveDegree K L v : ℤ) ≤
      ∑ P ∈ S,
        finiteExtensionPrincipalDivisor K L ((1 - u) / (1 - v)) P *
          (finiteExtensionPlaceDegree K L P : ℤ) := by
  have hheight :
      finiteExtensionHeight K L ((1 - u) / (1 - v)) ≤
        finiteExtensionPositiveDegree K L u +
          finiteExtensionPositiveDegree K L v := by
    calc
      finiteExtensionHeight K L ((1 - u) / (1 - v)) ≤
          finiteExtensionHeight K L u + finiteExtensionHeight K L v :=
        by simpa only [add_comm] using
          finiteExtensionHeight_one_sub_div_one_sub_le K L
            v u hv hu hvone huone
      _ = finiteExtensionPositiveDegree K L u +
          finiteExtensionPositiveDegree K L v := by
        rw [finiteExtensionPositiveDegree_eq_height K L u hu,
          finiteExtensionPositiveDegree_eq_height K L v hv]
  have hheightInt :
      (finiteExtensionHeight K L ((1 - u) / (1 - v)) : ℤ) ≤
        (finiteExtensionPositiveDegree K L u : ℤ) +
          (finiteExtensionPositiveDegree K L v : ℤ) := by
    exact_mod_cast hheight
  have hsubset := finiteExtensionWeightedOrder_sum_ge_neg_height
    K L ((1 - u) / (1 - v)) S
  linarith

end

end BGS.CorvajaZannier
