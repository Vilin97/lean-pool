/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.QuantumParallelRepetition.Part06

/-! # Quantum parallel repetition, part 07 -/

noncomputable section

namespace QuantumParallelRepetition

/-- The local matrix norm instance used while elaborating part seven. -/
noncomputable local instance matrixComplexContinuousENormPartSeven
    {m n : Type*} [Fintype m] [Fintype n] :
    ContinuousENorm (Matrix m n ℂ) :=
  @SeminormedAddGroup.toContinuousENorm (Matrix m n ℂ)
    (Matrix.normedAddCommGroup.toSeminormedAddCommGroup.toSeminormedAddGroup)

open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

attribute [local instance] Classical.propDecidable

/--
The finite outcome encoding for DSV density rational heterogeneous actual common stop scheduled.
-/
def dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome
    {S N d L : ℕ} (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L) (i : Fin (L + 1)) :
    EuclideanSpace ℂ
      (DSVUniformDensityThresholdLocalIndex N d ×
       DSVUniformDensityThresholdLocalIndex N d) :=
  dSVDensityRationalCompleteStoppedOptionalOutcome
    (dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth
      width schedule i) N ξ ζ
    (dSVDensityRationalCompleteStoppedOptionalLocalSchedule
      L j.succ i)
    (dSVDensityRationalCompleteStoppedOptionalLocalSchedule
      L j.succ i)

theorem
    dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome_before
    {S N d L : ℕ} (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L) (i : Fin (L + 1))
    (before : i.val < j.val) :
    dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome
        width schedule ξ ζ j i =
      dSVDensityRationalCompleteProjectiveOutcome
        (width (schedule
          ⟨i.val, lt_trans before j.isLt⟩))
        N ξ ζ false false := by
  unfold dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome
  rw [dSVDensityRationalCompleteStoppedOptionalLocalSchedule_before
    j i before]
  rw [dSVDensityRationalCompleteStoppedOptionalOutcome_some_some]
  simp only [dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth,
    lt_trans before j.isLt, ↓reduceDIte]

theorem
    dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome_hit
    {S N d L : ℕ} (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (j : Fin L) :
    dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome
        width schedule ξ ζ j j.castSucc =
      dSVDensityRationalCompleteProjectiveOutcome
        (width (schedule j)) N ξ ζ true true := by
  unfold dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome
  rw [dSVDensityRationalCompleteStoppedOptionalLocalSchedule_hit]
  rw [dSVDensityRationalCompleteStoppedOptionalOutcome_some_some]
  simp only [dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth, Fin.val_castSucc,
    Fin.is_lt, ↓reduceDIte, Fin.eta]

theorem
    dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome_after
    {S N d L : ℕ} (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L) (i : Fin (L + 1))
    (after : j.val < i.val) :
    dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome
        width schedule ξ ζ j i =
      dSVUniformDensityThresholdSharedState N d := by
  unfold dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome
  rw [dSVDensityRationalCompleteStoppedOptionalLocalSchedule_after
    j i after]
  exact dSVDensityRationalCompleteStoppedOptionalOutcome_none_none
    (dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth
      width schedule i) N ξ ζ

theorem
    dSVDensityRationalHeterogeneousActualCommonStopPhysicalState_eq_outcomeProduct
    {S N d L : ℕ} (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (j : Fin L)
    (alice bob :
      DSVUniformDensityIndependentHistoryLocalIndex
        (L + 1) N d) :
    dSVDensityRationalHeterogeneousActualPhysicalState
        N width schedule ξ ζ
        (⟨j.succ, alice⟩, ⟨j.succ, bob⟩) =
      ∏ i : Fin (L + 1),
        dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome
          width schedule ξ ζ j i (alice i, bob i) := by
  exact
    dSVDensityRationalHeterogeneousActualPhysicalFlagBornState_allFlags
      width schedule ξ ζ j.succ j.succ alice bob

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder

private def dSVDensityRationalPureBaseExactFlagBornMass
    {A C : Type*} [Fintype A] [Fintype C] {L : ℕ}
    (alice : A → Fin (L + 1)) (bob : C → Fin (L + 1))
    (z : EuclideanSpace ℂ (A × C))
    (flagAlice flagBob : Fin (L + 1)) : ℝ :=
  ∑ a : A, ∑ c : C,
    ‖z (a, c)‖ ^ 2 *
      if alice a = flagAlice ∧ bob c = flagBob then 1 else 0

theorem dSVDensityRationalPureMatchedFlagIndicator_sum
    {L : ℕ} (a b : Fin (L + 1)) :
    (∑ flag : Fin (L + 1),
      if a = flag ∧ b = flag then (1 : ℝ) else 0) =
      if a = b then 1 else 0 := by
  classical
  by_cases same : a = b
  · subst b
    simp only [and_self, sum_ite_eq, mem_univ, ↓reduceIte]
  · have absent (flag : Fin (L + 1)) :
        ¬ (a = flag ∧ b = flag) := by
      rintro ⟨first, second⟩
      exact same (first.trans second.symm)
    simp only [absent, ↓reduceIte, sum_const_zero, same]

theorem dSVDensityRationalPureMatchedFlagBorn_sum_eq
    {A C : Type*} [Fintype A] [Fintype C]
    {L : ℕ} (alice : A → Fin (L + 1))
    (bob : C → Fin (L + 1))
    (z : EuclideanSpace ℂ (A × C)) :
    (∑ flag : Fin (L + 1),
      dSVDensityRationalPureBaseExactFlagBornMass
        alice bob z flag flag) =
      ∑ a : A, ∑ c : C,
        ‖z (a, c)‖ ^ 2 *
          if alice a = bob c then (1 : ℝ) else 0 := by
  classical
  unfold dSVDensityRationalPureBaseExactFlagBornMass
  calc
    (∑ flag : Fin (L + 1),
      ∑ a : A, ∑ c : C,
        ‖z (a, c)‖ ^ 2 *
          if alice a = flag ∧ bob c = flag then (1 : ℝ) else 0) =
      ∑ a : A, ∑ c : C, ∑ flag : Fin (L + 1),
        ‖z (a, c)‖ ^ 2 *
          if alice a = flag ∧ bob c = flag then (1 : ℝ) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ a : A, ∑ c : C,
      ‖z (a, c)‖ ^ 2 *
        if alice a = bob c then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro c _
      rw [← Finset.mul_sum,
        dSVDensityRationalPureMatchedFlagIndicator_sum]

theorem dSVDensityRationalPureFlagBorn_partition
    {A C : Type*} [Fintype A] [Fintype C]
    {L : ℕ} (alice : A → Fin (L + 1))
    (bob : C → Fin (L + 1))
    (z : EuclideanSpace ℂ (A × C)) :
    dSVDensityRationalPublicMultiscaleFirstHitPhysicalFlagMismatchMass
        alice bob z +
      (∑ flag : Fin (L + 1),
        dSVDensityRationalPureBaseExactFlagBornMass
          alice bob z flag flag) =
      ‖z‖ ^ 2 := by
  classical
  rw [dSVDensityRationalPureMatchedFlagBorn_sum_eq]
  unfold
    dSVDensityRationalPublicMultiscaleFirstHitPhysicalFlagMismatchMass
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> ring

theorem dSVDensityRationalPureMatchedFlagBorn_zero_succ
    {A C : Type*} [Fintype A] [Fintype C]
    {L : ℕ} (alice : A → Fin (L + 1))
    (bob : C → Fin (L + 1))
    (z : EuclideanSpace ℂ (A × C)) :
    (∑ flag : Fin (L + 1),
      dSVDensityRationalPureBaseExactFlagBornMass
        alice bob z flag flag) =
      dSVDensityRationalPureBaseExactFlagBornMass
          alice bob z 0 0 +
        ∑ j : Fin L,
          dSVDensityRationalPureBaseExactFlagBornMass
            alice bob z j.succ j.succ := by
  rw [Fin.sum_univ_succ]

theorem dSVDensityRationalPureFlagBorn_partition_zero_succ
    {A C : Type*} [Fintype A] [Fintype C]
    {L : ℕ} (alice : A → Fin (L + 1))
    (bob : C → Fin (L + 1))
    (z : EuclideanSpace ℂ (A × C)) :
    dSVDensityRationalPublicMultiscaleFirstHitPhysicalFlagMismatchMass
        alice bob z +
      dSVDensityRationalPureBaseExactFlagBornMass
          alice bob z 0 0 +
      (∑ j : Fin L,
        dSVDensityRationalPureBaseExactFlagBornMass
          alice bob z j.succ j.succ) =
      ‖z‖ ^ 2 := by
  have actual := dSVDensityRationalPureFlagBorn_partition
    alice bob z
  rw [dSVDensityRationalPureMatchedFlagBorn_zero_succ
    alice bob z] at actual
  linarith

theorem dSVDensityRationalPureFlagBorn_normalized_partition_zero_succ
    {A C : Type*} [Fintype A] [Fintype C]
    {L : ℕ} (alice : A → Fin (L + 1))
    (bob : C → Fin (L + 1))
    (z : EuclideanSpace ℂ (A × C)) (normalized : ‖z‖ = 1) :
    dSVDensityRationalPublicMultiscaleFirstHitPhysicalFlagMismatchMass
        alice bob z +
      dSVDensityRationalPureBaseExactFlagBornMass
          alice bob z 0 0 +
      (∑ j : Fin L,
        dSVDensityRationalPureBaseExactFlagBornMass
          alice bob z j.succ j.succ) = 1 := by
  simpa only [normalized, one_pow] using
    dSVDensityRationalPureFlagBorn_partition_zero_succ
      alice bob z

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder

attribute [local instance] Classical.propDecidable

theorem
    dSVDensityRationalHeterogeneousActualPhysicalFlagMass_eq_optionalProduct
    {S d N L : ℕ} (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (flagAlice flagBob : Fin (L + 1)) :
    dSVDensityRationalHeterogeneousActualPhysicalFlagMass
        N width schedule ξ ζ flagAlice flagBob =
      ∏ i : Fin (L + 1),
        ‖dSVDensityRationalCompleteStoppedOptionalOutcome
          (dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth
            width schedule i) N ξ ζ
          (dSVDensityRationalCompleteStoppedOptionalLocalSchedule
            L flagAlice i)
          (dSVDensityRationalCompleteStoppedOptionalLocalSchedule
            L flagBob i)‖ ^ 2 := by
  classical
  unfold dSVDensityRationalHeterogeneousActualPhysicalFlagMass
  simp_rw [dSVDensityRationalHeterogeneousActualPhysicalFlagBornState_allFlags,
    norm_prod, ← Finset.prod_pow]
  calc
    _ = ∏ i : Fin (L + 1),
          ∑ a : DSVUniformDensityThresholdLocalIndex N d,
            ∑ b : DSVUniformDensityThresholdLocalIndex N d,
              ‖dSVDensityRationalCompleteStoppedOptionalOutcome
                (dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth
                  width schedule i) N ξ ζ
                (dSVDensityRationalCompleteStoppedOptionalLocalSchedule
                  L flagAlice i)
                (dSVDensityRationalCompleteStoppedOptionalLocalSchedule
                  L flagBob i) (a, b)‖ ^ 2 :=
      dSVUniformDensityPhysicalAsync_doubleProductSum
        (fun i a b =>
          ‖dSVDensityRationalCompleteStoppedOptionalOutcome
            (dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth
              width schedule i) N ξ ζ
            (dSVDensityRationalCompleteStoppedOptionalLocalSchedule
              L flagAlice i)
            (dSVDensityRationalCompleteStoppedOptionalLocalSchedule
              L flagBob i) (a, b)‖ ^ 2)
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]

theorem
    dSVDensityRationalHeterogeneousActualPhysical_firstHitProduct
    {L : ℕ} (continuation : ℕ → ℝ) (success : ℝ) (j : Fin L) :
    (∏ i : Fin (L + 1),
      if i.val < j.val then continuation i.val
      else if i.val = j.val then success else 1) =
      dSVHeterogeneousRealPrefix continuation j.val * success := by
  classical
  let f : ℕ → ℝ := fun i =>
    if i < j.val then continuation i
    else if i = j.val then success else 1
  have length : L + 1 = (j.val + 1) + (L - j.val) := by
    omega
  calc
    _ = ∏ k ∈ Finset.range (L + 1), f k :=
      Fin.prod_univ_eq_prod_range f (L + 1)
    _ = (∏ k ∈ Finset.range (j.val + 1), f k) *
          (∏ k ∈ Finset.range (L - j.val), f (j.val + 1 + k)) := by
      rw [length, Finset.prod_range_add]
    _ = (∏ k ∈ Finset.range j.val, continuation k) * success := by
      rw [Finset.prod_range_succ]
      have prefixProduct :
          (∏ k ∈ Finset.range j.val, f k) =
            (∏ k ∈ Finset.range j.val, continuation k) := by
        apply Finset.prod_congr rfl
        intro k member
        have earlier : k < j.val := Finset.mem_range.mp member
        simp only [earlier, ↓reduceIte, f]
      have selected : f j.val = success := by
        simp only [lt_self_iff_false, ↓reduceIte, f]
      have tail :
          (∏ k ∈ Finset.range (L - j.val),
            f (j.val + 1 + k)) = 1 := by
        apply Finset.prod_eq_one
        intro k _
        have notEarlier : ¬ j.val + 1 + k < j.val := by omega
        have notEqual : j.val + 1 + k ≠ j.val := by omega
        simp only [notEarlier, ↓reduceIte, notEqual, f]
      rw [prefixProduct, selected, tail, mul_one]
    _ = _ := rfl

theorem
    dSVDensityRationalHeterogeneousActualPhysicalMatchedCopyBorn
    {S d N L : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L) (i : Fin (L + 1)) :
    ‖dSVDensityRationalCompleteStoppedOptionalOutcome
        (dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth
          width schedule i) N ξ ζ
        (dSVDensityRationalCompleteStoppedOptionalLocalSchedule
          L j.succ i)
        (dSVDensityRationalCompleteStoppedOptionalLocalSchedule
          L j.succ i)‖ ^ 2 =
      if i.val < j.val then
        dSVDensityRationalHeterogeneousPhysicalStageContinue
          N width schedule ξ ζ i.val
      else if i.val = j.val then
        dSVDensityRationalHeterogeneousPhysicalStageSuccess
          N width schedule ξ ζ j.val
      else 1 := by
  classical
  rcases lt_trichotomy i.val j.val with earlier | equal | later
  · rw [dSVDensityRationalCompleteStoppedOptionalLocalSchedule_before
      j i earlier,
      dSVDensityRationalCompleteStoppedOptionalOutcome_some_some]
    have active : i.val < L := lt_trans earlier j.isLt
    simp only [dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth, active,
      ↓reduceDIte, earlier, ↓reduceIte, dSVDensityRationalHeterogeneousPhysicalStageContinue,
      dSVDensityRationalHeterogeneousPhysicalStageOutcome]
  · have selected : i = j.castSucc := Fin.ext equal
    subst i
    rw [dSVDensityRationalCompleteStoppedOptionalLocalSchedule_hit,
      dSVDensityRationalCompleteStoppedOptionalOutcome_some_some]
    simp only [dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth, Fin.val_castSucc,
      j.isLt, ↓reduceDIte, Fin.eta, lt_self_iff_false, ↓reduceIte,
      dSVDensityRationalHeterogeneousPhysicalStageSuccess,
      dSVDensityRationalHeterogeneousPhysicalStageOutcome]
  · rw [dSVDensityRationalCompleteStoppedOptionalLocalSchedule_after
      j i later,
      dSVDensityRationalCompleteStoppedOptionalOutcome_none_none,
      dSVUniformDensityThresholdSharedState_norm grid dimension]
    simp only [one_pow, show ¬i.val < j.val by omega, ↓reduceIte, show i.val ≠ j.val by omega]

theorem
    dSVDensityRationalHeterogeneousActualPhysicalFlagMass_succ_succ_eq_stage
    {S d N L : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (j : Fin L) :
    dSVDensityRationalHeterogeneousActualPhysicalFlagMass
        N width schedule ξ ζ j.succ j.succ =
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ j.val *
        dSVDensityRationalHeterogeneousPhysicalStageSuccess
          N width schedule ξ ζ j.val := by
  rw [dSVDensityRationalHeterogeneousActualPhysicalFlagMass_eq_optionalProduct]
  simp_rw [dSVDensityRationalHeterogeneousActualPhysicalMatchedCopyBorn
    grid dimension width schedule ξ ζ j]
  exact dSVDensityRationalHeterogeneousActualPhysical_firstHitProduct
    (dSVDensityRationalHeterogeneousPhysicalStageContinue
      N width schedule ξ ζ)
    (dSVDensityRationalHeterogeneousPhysicalStageSuccess
      N width schedule ξ ζ j.val) j

theorem dSVDensityRationalHeterogeneousActualPhysicalNoHitCopyBorn
    {S d N L : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) (i : Fin (L + 1)) :
    ‖dSVDensityRationalCompleteStoppedOptionalOutcome
        (dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth
          width schedule i) N ξ ζ
        (dSVDensityRationalCompleteStoppedOptionalLocalSchedule
          L 0 i)
        (dSVDensityRationalCompleteStoppedOptionalLocalSchedule
          L 0 i)‖ ^ 2 =
      if i.val < L then
        dSVDensityRationalHeterogeneousPhysicalStageContinue
          N width schedule ξ ζ i.val
      else 1 := by
  classical
  rw [dSVDensityRationalCompleteStoppedOptionalLocalSchedule_zero]
  by_cases active : i.val < L
  · rw [ite_eq_left active,
      dSVDensityRationalCompleteStoppedOptionalOutcome_some_some]
    simp only [dSVDensityRationalHeterogeneousActualPhysicalFlagBornCopyWidth, active,
      ↓reduceDIte, ↓reduceIte, dSVDensityRationalHeterogeneousPhysicalStageContinue,
      dSVDensityRationalHeterogeneousPhysicalStageOutcome]
  · rw [ite_eq_right active,
      dSVDensityRationalCompleteStoppedOptionalOutcome_none_none,
      dSVUniformDensityThresholdSharedState_norm grid dimension]
    simp only [one_pow, active, ↓reduceIte]

theorem
    dSVDensityRationalHeterogeneousActualPhysicalFlagMass_zero_zero_eq_terminal
    {S d N L : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalHeterogeneousActualPhysicalFlagMass
        N width schedule ξ ζ 0 0 =
      dSVDensityRationalHeterogeneousPhysicalTerminalMass
        N width schedule ξ ζ := by
  rw [dSVDensityRationalHeterogeneousActualPhysicalFlagMass_eq_optionalProduct]
  simp_rw [dSVDensityRationalHeterogeneousActualPhysicalNoHitCopyBorn
    grid dimension width schedule ξ ζ]
  unfold dSVDensityRationalHeterogeneousPhysicalTerminalMass
    dSVDensityRationalHeterogeneousPhysicalSurvival
    dSVHeterogeneousRealPrefix
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, Fin.is_lt, ↓reduceIte,
    lt_self_iff_false, mul_one]
  exact Fin.prod_univ_eq_prod_range
    (dSVDensityRationalHeterogeneousPhysicalStageContinue
      N width schedule ξ ζ) L

theorem
    dSVDensityRationalHeterogeneousActualPhysicalBaseFlagBorn_eq_flagMass
    {S d N L : ℕ} (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (flagAlice flagBob : Fin (L + 1)) :
    dSVDensityRationalPureBaseExactFlagBornMass
        (fun q : DSVUniformDensityThresholdWholeHistoryLocalIndex
          N d L => q.1)
        (fun q : DSVUniformDensityThresholdWholeHistoryLocalIndex
          N d L => q.1)
        (dSVDensityRationalHeterogeneousActualPhysicalState
          N width schedule ξ ζ)
        flagAlice flagBob =
      dSVDensityRationalHeterogeneousActualPhysicalFlagMass
        N width schedule ξ ζ flagAlice flagBob := by
  classical
  unfold dSVDensityRationalPureBaseExactFlagBornMass
    dSVDensityRationalHeterogeneousActualPhysicalFlagMass
  simp only [Fintype.sum_sigma]
  simp only [ite_and, mul_ite, mul_one, mul_zero, sum_ite_irrel, sum_const_zero, sum_ite_eq',
    mem_univ, ↓reduceIte]

theorem
    dSVDensityRationalHeterogeneousActualPhysicalMatchedFlagMass_eq_stoppedSuccess
    {S d N L : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    (∑ j : Fin L,
      dSVDensityRationalHeterogeneousActualPhysicalFlagMass
        N width schedule ξ ζ j.succ j.succ) =
      dSVDensityRationalHeterogeneousPhysicalStoppedSuccessMass
        N width schedule ξ ζ := by
  simp_rw [dSVDensityRationalHeterogeneousActualPhysicalFlagMass_succ_succ_eq_stage
    grid dimension width schedule ξ ζ]
  unfold dSVDensityRationalHeterogeneousPhysicalStoppedSuccessMass
  exact Fin.sum_univ_eq_sum_range
    (fun k : ℕ =>
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ k *
        dSVDensityRationalHeterogeneousPhysicalStageSuccess
          N width schedule ξ ζ k) L

theorem
    dSVDensityRationalHeterogeneousActualPhysicalFlagBorn_mass_partition
    {S d N L : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalHeterogeneousActualAsynchronousFlagMass
        N width schedule ξ ζ +
      dSVDensityRationalHeterogeneousActualPhysicalFlagMass
          N width schedule ξ ζ 0 0 +
      (∑ j : Fin L,
        dSVDensityRationalHeterogeneousActualPhysicalFlagMass
          N width schedule ξ ζ j.succ j.succ) = 1 := by
  have actual :=
    dSVDensityRationalPureFlagBorn_normalized_partition_zero_succ
      (fun q : DSVUniformDensityThresholdWholeHistoryLocalIndex
        N d L => q.1)
      (fun q : DSVUniformDensityThresholdWholeHistoryLocalIndex
        N d L => q.1)
      (dSVDensityRationalHeterogeneousActualPhysicalState
        N width schedule ξ ζ)
      (dSVDensityRationalHeterogeneousActualPhysicalState_norm
        grid dimension width schedule ξ ζ)
  change
    dSVDensityRationalHeterogeneousActualAsynchronousFlagMass
        N width schedule ξ ζ +
      dSVDensityRationalPureBaseExactFlagBornMass
        (fun q : DSVUniformDensityThresholdWholeHistoryLocalIndex
          N d L => q.1)
        (fun q : DSVUniformDensityThresholdWholeHistoryLocalIndex
          N d L => q.1)
        (dSVDensityRationalHeterogeneousActualPhysicalState
          N width schedule ξ ζ) 0 0 +
      (∑ j : Fin L,
        dSVDensityRationalPureBaseExactFlagBornMass
          (fun q : DSVUniformDensityThresholdWholeHistoryLocalIndex
            N d L => q.1)
          (fun q : DSVUniformDensityThresholdWholeHistoryLocalIndex
            N d L => q.1)
          (dSVDensityRationalHeterogeneousActualPhysicalState
            N width schedule ξ ζ) j.succ j.succ) = 1 at actual
  simpa only
    [dSVDensityRationalHeterogeneousActualPhysicalBaseFlagBorn_eq_flagMass]
    using actual

theorem
    dSVDensityRationalHeterogeneousActualAsynchronousFlagMass_eq_stoppedAsynchronousMass
    {S d N L : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalHeterogeneousActualAsynchronousFlagMass
        N width schedule ξ ζ =
      dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
        N width schedule ξ ζ := by
  have physical :=
    dSVDensityRationalHeterogeneousActualPhysicalFlagBorn_mass_partition
      grid dimension width schedule ξ ζ
  rw [dSVDensityRationalHeterogeneousActualPhysicalFlagMass_zero_zero_eq_terminal
        grid dimension width schedule ξ ζ,
      dSVDensityRationalHeterogeneousActualPhysicalMatchedFlagMass_eq_stoppedSuccess
        grid dimension width schedule ξ ζ] at physical
  have stages :=
    dSVDensityRationalHeterogeneousPhysicalStopped_mass_partition
      grid dimension width schedule ξ ζ
  linarith

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

theorem
    dSVDensityRationalMixedCanonicalPrefixPhysicalLocalAction_real_smul
    {n : ℕ} (A B : Matrix.unitaryGroup (Fin n) ℂ)
    (r : ℝ) (z : EuclideanSpace ℂ (Fin n × Fin n)) :
    localUnitaryAction A B (r • z) =
      r • localUnitaryAction A B z := by
  change
    Matrix.toEuclideanLin
        ((A : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ
          (B : Matrix (Fin n) (Fin n) ℂ)) (r • z) =
      r • Matrix.toEuclideanLin
        ((A : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ
          (B : Matrix (Fin n) (Fin n) ℂ)) z
  exact (Matrix.toEuclideanLin
    ((A : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ
      (B : Matrix (Fin n) (Fin n) ℂ))).map_smul_of_tower r z

theorem
    dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor_real_smul
    {N : ℕ} (n : ℕ) (r : ℝ)
    (z : EuclideanSpace ℂ (Fin N × Fin N)) :
    dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
        n (r • z) =
      r • dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
        n z := by
  ext q
  change
    ((r : ℂ) * z ((finProdFinEquiv.symm q.1).1,
        (finProdFinEquiv.symm q.2).1)) *
      embezzlementState n
        ((finProdFinEquiv.symm q.1).2,
          (finProdFinEquiv.symm q.2).2) =
    (r : ℂ) *
      (z ((finProdFinEquiv.symm q.1).1,
          (finProdFinEquiv.symm q.2).1) *
        embezzlementState n
          ((finProdFinEquiv.symm q.1).2,
            (finProdFinEquiv.symm q.2).2))
  ring

theorem
    dSVDensityRationalMixedCanonicalPrefixPhysicalRawHarmonicTensor_eq
    {N : ℕ} (grid : 0 < N) (n : ℕ)
    (rank : Fin (N + 1)) :
    dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
        n (dSVCanonicalFailurePrefix rank) =
      Real.sqrt (rank.val : ℝ) •
        tensorEmbezzlementTarget (n := n)
          (dSVCanonicalFailureUnitRankFamily N grid rank) := by
  classical
  have raw : dSVCanonicalFailurePrefix rank =
      Real.sqrt (rank.val : ℝ) •
        (dSVCanonicalFailureUnitRankFamily N grid rank :
          EuclideanSpace ℂ (Fin N × Fin N)) := by
    by_cases zero : rank.val = 0
    · rw [dSVCanonicalFailurePrefix_eq_zero_of_rank_zero
        rank zero]
      simp only [zero, CharP.cast_eq_zero, Real.sqrt_zero, zero_smul]
    · have nonzero : dSVCanonicalFailurePrefix rank ≠ 0 := by
        intro vanished
        have mass := dSVCanonicalFailurePrefix_norm_sq rank
        rw [vanished] at mass
        have cast_zero : (rank.val : ℝ) = 0 := by
          simpa only [Nat.cast_eq_zero, Fin.val_eq_zero_iff, norm_zero, ne_eq,
            OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using mass.symm
        exact zero (by exact_mod_cast cast_zero)
      change dSVCanonicalFailurePrefix rank =
        Real.sqrt (rank.val : ℝ) •
          normalizeOrDefault
            (embezzlementState N)
            (dSVCanonicalFailurePrefix rank)
      rw [normalizeOrDefault, ite_eq_right nonzero,
        ← dSVCanonicalFailurePrefix_norm_eq_sqrt rank]
      exact (NormedSpace.norm_smul_normalize
        (dSVCanonicalFailurePrefix rank)).symm
  rw [raw,
    dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor_real_smul,
    dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor_unit]

theorem
    dSVDensityRationalMixedCanonicalPrefixPhysicalAcceptedSigmaState_apply
    {d N n : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N)
    (ξ ζ : BipartiteUnitVector d)
    (i j : Fin d) (k l : Fin N) (a b : Fin n) :
    dSVDensityRationalMixedCanonicalPrefixPhysicalAcceptedSigmaState
        (N := N) w n ξ ζ
        (⟨i, finProdFinEquiv (k, a)⟩,
          ⟨j, finProdFinEquiv (l, b)⟩) =
      dSVDensityRationalCanonicalPrefixSpectralOutcome
          w N ξ ζ (⟨k, i⟩, ⟨l, j⟩) *
        embezzlementState n (a, b) := by
  classical
  rw [dSVDensityRationalMixedCanonicalSpectralOutcome_eq]
  simp only [
    dSVDensityRationalMixedCanonicalPrefixPhysicalAcceptedSigmaState,
    dSVUniformDensityCorrectedMatchedSigmaWeightedResidual,
    dSVDensityRationalLocalSpectralPairHistory,
    dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor,
    dSVDensityRationalPhysicalMixedAcceptedPrefixWork,
    dSVCanonicalFailurePrefix,
    Equiv.symm_apply_apply]
  change
    (((‖sharedThresholdResourceRaw (d := Fin d)
        (fun _ : Fin N => (1 : ℝ))‖⁻¹ : ℝ) : ℂ) *
      dSVDensityRationalLocalSpectralPairBasisOverlap ξ ζ i j) *
      ((if k = l ∧
          k.val <
            (dSVDensityRationalPhysicalMixedAcceptedIntersectionRank
              w N ξ ζ i j).val
        then (1 : ℂ) else 0) *
        embezzlementState n (a, b)) =
      (((‖sharedThresholdResourceRaw (d := Fin d)
          (fun _ : Fin N => (1 : ℝ))‖⁻¹ : ℝ) : ℂ) *
        dSVDensityRationalMixedCanonicalRawSource
          w N ξ ζ (⟨k, i⟩, ⟨l, j⟩)) *
        embezzlementState n (a, b)
  rw [dSVDensityRationalMixedCanonicalRawSource_apply]
  by_cases same : k = l
  · subst l
    have accepted :=
      dSVDensityRationalPhysicalMixedAcceptedThreshold_iff
        width grid ξ ζ i j k
    by_cases below : k.val <
        (dSVDensityRationalPhysicalMixedAcceptedIntersectionRank
          w N ξ ζ i j).val
    · have both := accepted.mpr below
      simp only [ofReal_inv, below, and_self, ↓reduceIte, one_mul, mul_assoc, both.1, both.2]
    · have not_both :
        ¬ (dSVDensityRationalProjectiveThresholdBin w N k
            ((dSVSoftBobLeftReducedDensity_posSemidef
              ξ).isHermitian.eigenvalues i) = true ∧
          dSVDensityRationalProjectiveThresholdBin w N k
            ((dSVSoftBobLeftReducedDensity_posSemidef
              ζ).isHermitian.eigenvalues j) = true) :=
        fun both => below (accepted.mp both)
      simp only [ofReal_inv, below, and_false, ↓reduceIte, zero_mul, mul_zero, not_both]
  · simp only [ofReal_inv, same, false_and, ↓reduceIte, zero_mul, mul_zero]

theorem
    dSVDensityRationalMixedCanonicalPrefixPhysicalRankWeightedAtomError_eq
    {N n : ℕ} (grid : 0 < N)
    (rank : Fin (N + 1))
    (A B : Matrix.unitaryGroup (Fin (N * n)) ℂ) :
    ‖localUnitaryAction A B
          (dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
            n (dSVCanonicalFailurePrefix rank)) -
        Real.sqrt (rank.val : ℝ) •
          embezzlementState (N * n)‖ ^ 2 =
      (rank.val : ℝ) *
        ‖localUnitaryAction A B
            (tensorEmbezzlementTarget (n := n)
              (dSVCanonicalFailureUnitRankFamily
                N grid rank)) -
          embezzlementState (N * n)‖ ^ 2 := by
  rw [dSVDensityRationalMixedCanonicalPrefixPhysicalRawHarmonicTensor_eq
    grid n rank]
  rw [dSVDensityRationalMixedCanonicalPrefixPhysicalLocalAction_real_smul]
  rw [← smul_sub, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (by positivity : 0 ≤ (rank.val : ℝ))]

private def dSVDensityRationalPublicBucketPhysicalCommonRank
    {N : ℕ} (r s : Fin (N + 1)) : Fin (N + 1) :=
  ⟨min r.val s.val, by
    have left := r.isLt
    have right := s.isLt
    omega⟩

theorem dSVDensityRationalPublicBucketPhysicalCommonRank_eq
    {d N : ℕ} (w : ℝ)
    (ξ ζ : BipartiteUnitVector d)
    (i j : Fin d) :
    dSVDensityRationalPublicBucketPhysicalCommonRank
        (dSVDensityRationalPhysicalAcceptedRank w N ξ i)
        (dSVDensityRationalPhysicalAcceptedRank w N ζ j) =
      dSVDensityRationalPhysicalMixedAcceptedIntersectionRank
        w N ξ ζ i j := by
  rfl

theorem
    exists_proofDSVDensityRationalPublicBucketPhysicalRawRankCleanup_sq
    {Ω I : Type*} [DecidableEq I] {N : ℕ} (grid : 0 < N)
    (bucket : Ω → Fin (N + 1) → I)
    (representative : Ω → I → Fin (N + 1))
    (ε : ℝ) (precision : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧
      ∃ A B : Ω → I → Matrix.unitaryGroup (Fin (N * n)) ℂ,
        ∀ (phase : Ω) (r s : Fin (N + 1)),
          ‖localUnitaryAction
              (A phase (bucket phase r))
              (B phase (bucket phase s))
              (dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
                n (dSVCanonicalFailurePrefix r)) -
            Real.sqrt (r.val : ℝ) •
              embezzlementState (N * n)‖ ^ 2 ≤
            (r.val : ℝ) *
              (2 * ε ^ 2 +
                8 * |(r.val : ℝ) -
                  ((representative phase (bucket phase r)).val : ℝ)| /
                  (max 1
                    (min r.val
                      (representative phase (bucket phase r)).val) : ℕ) +
                4 * (if bucket phase r = bucket phase s
                  then (0 : ℝ) else 1)) := by
  obtain ⟨n, positive, A, B, accurate⟩ :=
    dSVDensityRationalPublicBucketCanonicalPrefixCleanup_sq
      grid bucket representative ε precision
  refine ⟨n, positive, A, B, ?_⟩
  intro phase r s
  rw [dSVDensityRationalMixedCanonicalPrefixPhysicalRankWeightedAtomError_eq
    grid r]
  exact mul_le_mul_of_nonneg_left
    (accurate phase r s) (Nat.cast_nonneg r.val)

theorem
    exists_proofDSVDensityRationalPublicBucketPhysicalMixedPrefixCleanup_sq
    {Ω I : Type*} [DecidableEq I] {N : ℕ} (grid : 0 < N)
    (bucket : Ω → Fin (N + 1) → I)
    (representative : Ω → I → Fin (N + 1))
    (ε : ℝ) (precision : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧
      ∃ A B : Ω → I → Matrix.unitaryGroup (Fin (N * n)) ℂ,
        ∀ (phase : Ω) (r s : Fin (N + 1)),
          ‖localUnitaryAction
              (A phase (bucket phase r))
              (B phase (bucket phase s))
              (dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
                n (dSVCanonicalFailurePrefix
                  (dSVDensityRationalPublicBucketPhysicalCommonRank
                    r s))) -
            Real.sqrt (r.val : ℝ) •
              embezzlementState (N * n)‖ ^ 2 ≤
            2 * |(r.val : ℝ) - (s.val : ℝ)| +
              2 * (r.val : ℝ) *
                (2 * ε ^ 2 +
                  8 * |(r.val : ℝ) -
                    ((representative phase (bucket phase r)).val : ℝ)| /
                    (max 1
                      (min r.val
                        (representative phase (bucket phase r)).val) : ℕ) +
                  4 * (if bucket phase r = bucket phase s
                    then (0 : ℝ) else 1)) := by
  obtain ⟨n, positive, A, B, accurate⟩ :=
    exists_proofDSVDensityRationalPublicBucketPhysicalRawRankCleanup_sq
      grid bucket representative ε precision
  refine ⟨n, positive, A, B, ?_⟩
  intro phase r s
  let U := A phase (bucket phase r)
  let V := B phase (bucket phase s)
  let common := dSVDensityRationalPublicBucketPhysicalCommonRank r s
  let mixed :=
    dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
      n (dSVCanonicalFailurePrefix common)
  let alice :=
    dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
      n (dSVCanonicalFailurePrefix r)
  let target := Real.sqrt (r.val : ℝ) •
    embezzlementState (N * n)
  have pure_distance :
      ‖localUnitaryAction U V mixed -
        localUnitaryAction U V alice‖ ^ 2 ≤
          |(r.val : ℝ) - (s.val : ℝ)| := by
    rw [← localUnitaryAction_sub,
      localUnitaryAction_norm]
    dsimp [mixed, alice]
    rw [dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor_prefix_sub_norm_sq
      positive]
    dsimp [common,
      dSVDensityRationalPublicBucketPhysicalCommonRank]
    rcases le_total r.val s.val with ordered | ordered
    · rw [min_eq_left ordered]
      simp only [sub_self, abs_zero, abs_nonneg]
    · rw [min_eq_right ordered]
      rw [abs_sub_comm]
  have cleanup := accurate phase r s
  change
    ‖localUnitaryAction U V mixed - target‖ ^ 2 ≤ _
  have triangle :
      ‖localUnitaryAction U V mixed - target‖ ≤
        ‖localUnitaryAction U V mixed -
          localUnitaryAction U V alice‖ +
        ‖localUnitaryAction U V alice - target‖ := by
    calc
      _ = ‖(localUnitaryAction U V mixed -
          localUnitaryAction U V alice) +
          (localUnitaryAction U V alice - target)‖ := by
            congr 1
            abel
      _ ≤ _ := norm_add_le _ _
  change
    ‖localUnitaryAction U V alice - target‖ ^ 2 ≤ _
    at cleanup
  nlinarith [
    norm_nonneg (localUnitaryAction U V mixed - target),
    norm_nonneg (localUnitaryAction U V mixed -
      localUnitaryAction U V alice),
    norm_nonneg (localUnitaryAction U V alice - target),
    sq_nonneg
      (‖localUnitaryAction U V mixed -
          localUnitaryAction U V alice‖ -
        ‖localUnitaryAction U V alice - target‖)]

private def dSVDensityRationalPublicBucketPhysicalPhaseWeightedMixedError
    {d N n B : ℕ} (Q : ℕ) (w : ℝ)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin B → Option ℕ →
      Matrix.unitaryGroup (Fin (N * n)) ℂ) : ℝ :=
  ∑ phase : Fin B,
    dSVDensityRationalPublicLogRankPhaseWeight B phase *
      ∑ i : Fin d, ∑ j : Fin d,
        (dSVDensityRationalPrefixHarmonicSpectralOverlap
          ξ ζ i j / ((d : ℝ) * (N : ℝ))) *
          ‖localUnitaryAction
              (A phase
                (dSVDensityRationalPublicLogRankBucket Q phase
                  (dSVDensityRationalPhysicalAcceptedRank
                    w N ξ i)))
              (C phase
                (dSVDensityRationalPublicLogRankBucket Q phase
                  (dSVDensityRationalPhysicalAcceptedRank
                    w N ζ j)))
              (dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
                n
                (dSVDensityRationalPhysicalMixedAcceptedPrefixWork
                  w N ξ ζ i j)) -
            Real.sqrt
                ((dSVDensityRationalPhysicalAcceptedRank
                  w N ξ i).val : ℝ) •
              embezzlementState (N * n)‖ ^ 2

/-- The quantum state representing DSV density rational public bucket physical coherent mixed. -/
def dSVDensityRationalPublicBucketPhysicalCoherentMixedState
    {d N B : ℕ} (w : ℝ) (n : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      ((Σ _ : Fin B × Fin d, Fin (N * n)) ×
       (Σ _ : Fin B × Fin d, Fin (N * n))) :=
  dSVDensityRationalPublicBucketCoherentPhaseSigmaState B
    (dSVDensityRationalLocalSpectralPairHistory N ξ ζ)
    (fun _ i j =>
      dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor n
        (dSVDensityRationalPhysicalMixedAcceptedPrefixWork
          w N ξ ζ i j))

/-- The quantum state representing DSV density rational public bucket physical coherent target. -/
def dSVDensityRationalPublicBucketPhysicalCoherentTargetState
    {d N B : ℕ} (w : ℝ) (n : ℕ)
    (ξ ζ : BipartiteUnitVector d) :
    EuclideanSpace ℂ
      ((Σ _ : Fin B × Fin d, Fin (N * n)) ×
       (Σ _ : Fin B × Fin d, Fin (N * n))) :=
  dSVDensityRationalPublicBucketCoherentPhaseSigmaState B
    (dSVDensityRationalLocalSpectralPairHistory N ξ ζ)
    (fun _ i _ =>
      Real.sqrt
          ((dSVDensityRationalPhysicalAcceptedRank
            w N ξ i).val : ℝ) •
        embezzlementState (N * n))

/--
The DSV density rational public bucket physical coherent local reset construction used in the
quantum parallel-repetition argument.
-/
def dSVDensityRationalPublicBucketPhysicalCoherentLocalReset
    {d N B n : ℕ} (Q : ℕ) (w : ℝ)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin B → Option ℕ →
      Matrix.unitaryGroup (Fin (N * n)) ℂ)
    (z : EuclideanSpace ℂ
      ((Σ _ : Fin B × Fin d, Fin (N * n)) ×
       (Σ _ : Fin B × Fin d, Fin (N * n)))) :
    EuclideanSpace ℂ
      ((Σ _ : Fin B × Fin d, Fin (N * n)) ×
       (Σ _ : Fin B × Fin d, Fin (N * n))) :=
  dSVUniformDensityPhysicalAsyncSigmaContinuation
    (fun q : Fin B × Fin d =>
      A q.1
        (dSVDensityRationalPublicLogRankBucket Q q.1
          (dSVDensityRationalPhysicalAcceptedRank
            w N ξ q.2)))
    (fun q : Fin B × Fin d =>
      C q.1
        (dSVDensityRationalPublicLogRankBucket Q q.1
          (dSVDensityRationalPhysicalAcceptedRank
            w N ζ q.2))) z

theorem
    dSVDensityRationalPublicBucketPhysicalCoherentMixedReset_distance_sq
    {d N B n : ℕ} (phases : 0 < B) (Q : ℕ) (w : ℝ)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin B → Option ℕ →
      Matrix.unitaryGroup (Fin (N * n)) ℂ) :
    ‖dSVDensityRationalPublicBucketPhysicalCoherentLocalReset
          Q w ξ ζ A C
          (dSVDensityRationalPublicBucketPhysicalCoherentMixedState
            (N := N) (B := B) w n ξ ζ) -
        dSVDensityRationalPublicBucketPhysicalCoherentTargetState
          (N := N) (B := B) w n ξ ζ‖ ^ 2 =
      dSVDensityRationalPublicBucketPhysicalPhaseWeightedMixedError
        Q w ξ ζ A C := by
  unfold
    dSVDensityRationalPublicBucketPhysicalCoherentLocalReset
    dSVDensityRationalPublicBucketPhysicalCoherentMixedState
    dSVDensityRationalPublicBucketPhysicalCoherentTargetState
  rw [dSVDensityRationalPublicBucketCoherentPhaseSigmaReset_distance_sq
    phases]
  simp_rw [
    dSVDensityRationalLocalSpectralPairHistory_apply_norm_sq]
  unfold
    dSVDensityRationalPublicBucketPhysicalPhaseWeightedMixedError
    dSVDensityRationalPublicLogRankPhaseWeight
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro phase _
  ring

end

section

open scoped BigOperators

theorem dSVDensityRationalPublicShiftedResidue_sum
    {B : ℕ} (positive : 0 < B) (a : ℕ) :
    (∑ phase : Fin B, (a + phase.val) % B) =
      ∑ phase : Fin B, phase.val := by
  let : NeZero B := ⟨Nat.ne_of_gt positive⟩
  let offset : Fin B := ⟨a % B, Nat.mod_lt a positive⟩
  calc
    (∑ phase : Fin B, (a + phase.val) % B) =
        ∑ phase : Fin B, (offset + phase).val := by
      apply Finset.sum_congr rfl
      intro phase _
      simp only [Nat.add_mod, dvd_refl, Nat.mod_mod_of_dvd, Fin.val_add, offset]
    _ = ∑ phase : Fin B, phase.val := by
      apply Fintype.sum_equiv (Equiv.addLeft offset)
      intro phase
      rfl

theorem dSVDensityRationalPublicShiftedQuotient_sum
    {B : ℕ} (positive : 0 < B) (a : ℕ) :
    (∑ phase : Fin B, (a + phase.val) / B) = a := by
  have decomposition :
      (∑ phase : Fin B, (a + phase.val) % B) +
          B * (∑ phase : Fin B, (a + phase.val) / B) =
        B * a + ∑ phase : Fin B, phase.val := by
    calc
      (∑ phase : Fin B, (a + phase.val) % B) +
            B * (∑ phase : Fin B, (a + phase.val) / B) =
          ∑ phase : Fin B,
            ((a + phase.val) % B + B * ((a + phase.val) / B)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = ∑ phase : Fin B, (a + phase.val) := by
        apply Finset.sum_congr rfl
        intro phase _
        exact Nat.mod_add_div (a + phase.val) B
      _ = B * a + ∑ phase : Fin B, phase.val := by
        simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  rw [dSVDensityRationalPublicShiftedResidue_sum
    positive a] at decomposition
  have cancelled :
      B * (∑ phase : Fin B, (a + phase.val) / B) = B * a := by
    apply Nat.add_left_cancel
    calc
      (∑ phase : Fin B, phase.val) +
          B * (∑ phase : Fin B, (a + phase.val) / B) =
        B * a + ∑ phase : Fin B, phase.val := decomposition
      _ = (∑ phase : Fin B, phase.val) + B * a := by
        omega
  exact Nat.mul_left_cancel positive cancelled

theorem dSVDensityRationalPublicShiftedQuotient_real_sum
    {B : ℕ} (positive : 0 < B) (a : ℕ) :
    (∑ phase : Fin B, (((a + phase.val) / B : ℕ) : ℝ)) =
      (a : ℝ) := by
  exact_mod_cast
    dSVDensityRationalPublicShiftedQuotient_sum positive a

theorem dSVDensityRationalPublicShiftedBucketMismatch_sum_le
    {B : ℕ} (positive : 0 < B) (a b : ℕ) :
    (∑ phase : Fin B,
      if (a + phase.val) / B = (b + phase.val) / B
      then (0 : ℝ) else 1) ≤
      |(a : ℝ) - (b : ℝ)| := by
  have ordered_bound :
      ∀ x y : ℕ, x ≤ y →
        (∑ phase : Fin B,
          if (x + phase.val) / B = (y + phase.val) / B
          then (0 : ℝ) else 1) ≤ (y : ℝ) - (x : ℝ) := by
    intro x y ordered
    calc
      (∑ phase : Fin B,
        if (x + phase.val) / B = (y + phase.val) / B
        then (0 : ℝ) else 1) ≤
          ∑ phase : Fin B,
            ((((y + phase.val) / B : ℕ) : ℝ) -
              (((x + phase.val) / B : ℕ) : ℝ)) := by
        apply Finset.sum_le_sum
        intro phase _
        have monotone :
            (x + phase.val) / B ≤ (y + phase.val) / B :=
          Nat.div_le_div_right (Nat.add_le_add_right ordered _)
        by_cases same :
            (x + phase.val) / B = (y + phase.val) / B
        · simp only [same, ↓reduceIte, sub_self, Std.le_refl]
        · simp only [same, ite_false]
          have strictly :
              (x + phase.val) / B < (y + phase.val) / B :=
            lt_of_le_of_ne monotone same
          have cast_bound :
              (((x + phase.val) / B : ℕ) : ℝ) + 1 ≤
                (((y + phase.val) / B : ℕ) : ℝ) := by
            exact_mod_cast Nat.succ_le_of_lt strictly
          linarith
      _ = (y : ℝ) - (x : ℝ) := by
        rw [Finset.sum_sub_distrib,
          dSVDensityRationalPublicShiftedQuotient_real_sum
            positive y,
          dSVDensityRationalPublicShiftedQuotient_real_sum
            positive x]
  rcases le_total a b with ordered | ordered
  · simpa only [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast ordered : (a : ℝ) ≤ b)), neg_sub,
      ge_iff_le] using
      ordered_bound a b ordered
  · have bound := ordered_bound b a ordered
    have same_sum :
        (∑ phase : Fin B,
          if (a + phase.val) / B = (b + phase.val) / B
          then (0 : ℝ) else 1) =
        ∑ phase : Fin B,
          if (b + phase.val) / B = (a + phase.val) / B
          then (0 : ℝ) else 1 := by
      apply Finset.sum_congr rfl
      intro phase _
      by_cases same :
          (a + phase.val) / B = (b + phase.val) / B
      · simp only [ite_eq_left same, ite_eq_left same.symm]
      · have reversed :
            (b + phase.val) / B ≠ (a + phase.val) / B :=
          Ne.symm same
        simp only [ite_eq_right same, ite_eq_right reversed]
    rw [same_sum]
    simpa only [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast ordered : (b : ℝ) ≤ a)),
      ge_iff_le] using bound

theorem dSVDensityRationalPublicShiftedBucketMismatch_average_le
    {B : ℕ} (positive : 0 < B) (a b : ℕ) :
    (∑ phase : Fin B,
      (1 / (B : ℝ)) *
        (if (a + phase.val) / B = (b + phase.val) / B
         then (0 : ℝ) else 1)) ≤
      |(a : ℝ) - (b : ℝ)| / (B : ℝ) := by
  rw [← Finset.mul_sum]
  have bound :=
    dSVDensityRationalPublicShiftedBucketMismatch_sum_le
      positive a b
  calc
    (1 / (B : ℝ)) *
        (∑ phase : Fin B,
          if (a + phase.val) / B = (b + phase.val) / B
          then (0 : ℝ) else 1) ≤
      (1 / (B : ℝ)) * |(a : ℝ) - (b : ℝ)| := by
        gcongr
    _ = |(a : ℝ) - (b : ℝ)| / (B : ℝ) := by
      ring

end

section

open scoped BigOperators ComplexOrder MatrixOrder

private def dSVDensityRationalPublicLogRankPhaseWeightedCrossing
    {N : ℕ} (Q B : ℕ) (r s : Fin (N + 1)) : ℝ :=
  ∑ phase : Fin B,
    dSVDensityRationalPublicLogRankPhaseWeight B phase *
      (if
        dSVDensityRationalPublicLogRankBucket Q phase r =
          dSVDensityRationalPublicLogRankBucket Q phase s
       then (0 : ℝ) else 1)

theorem dSVDensityRationalPublicLogRankPhaseWeightedCrossing_nonneg
    {N : ℕ} (Q B : ℕ) (r s : Fin (N + 1)) :
    0 ≤ dSVDensityRationalPublicLogRankPhaseWeightedCrossing
      Q B r s := by
  unfold dSVDensityRationalPublicLogRankPhaseWeightedCrossing
  apply Finset.sum_nonneg
  intro phase _
  unfold dSVDensityRationalPublicLogRankPhaseWeight
  split <;> positivity

theorem
    dSVDensityRationalPublicLogRankPhaseWeightedCrossing_le_fineLabel
    {N B : ℕ} (positive : 0 < B) (Q : ℕ)
    (r s : Fin (N + 1))
    (nonzero_r : r.val ≠ 0) (nonzero_s : s.val ≠ 0) :
    dSVDensityRationalPublicLogRankPhaseWeightedCrossing
        Q B r s ≤
      |(dSVDensityRationalPublicLogRankFineLabel Q r : ℝ) -
        (dSVDensityRationalPublicLogRankFineLabel Q s : ℝ)| /
          (B : ℝ) := by
  simpa only [dSVDensityRationalPublicLogRankPhaseWeightedCrossing,
    dSVDensityRationalPublicLogRankPhaseWeight, one_div, dSVDensityRationalPublicLogRankBucket,
    nonzero_r, ↓reduceIte, nonzero_s, Option.some.injEq, mul_ite, mul_zero, mul_one] using
      (dSVDensityRationalPublicShiftedBucketMismatch_average_le
        positive
        (dSVDensityRationalPublicLogRankFineLabel Q r)
        (dSVDensityRationalPublicLogRankFineLabel Q s))

theorem dSVDensityRationalPublicLogRankFineLabel_abs_sub_le
    {N : ℕ} (Q : ℕ) (r s : Fin (N + 1)) :
    |(dSVDensityRationalPublicLogRankFineLabel Q r : ℝ) -
      (dSVDensityRationalPublicLogRankFineLabel Q s : ℝ)| ≤
      (Q : ℝ) *
        |Real.log ((max 1 r.val : ℕ) : ℝ) -
          Real.log ((max 1 s.val : ℕ) : ℝ)| + 1 := by
  have first :=
    dSVDensityRationalPublicLogRankFineLabel_bounds Q r
  have second :=
    dSVDensityRationalPublicLogRankFineLabel_bounds Q s
  have scaled :
      |(Q : ℝ) * Real.log ((max 1 r.val : ℕ) : ℝ) -
        (Q : ℝ) * Real.log ((max 1 s.val : ℕ) : ℝ)| =
      (Q : ℝ) *
        |Real.log ((max 1 r.val : ℕ) : ℝ) -
          Real.log ((max 1 s.val : ℕ) : ℝ)| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg Q)]
  rw [← scaled]
  apply abs_le.mpr
  constructor
  · have lower := neg_le_abs
      ((Q : ℝ) * Real.log ((max 1 r.val : ℕ) : ℝ) -
        (Q : ℝ) * Real.log ((max 1 s.val : ℕ) : ℝ))
    linarith [first.2, second.1]
  · have upper := le_abs_self
      ((Q : ℝ) * Real.log ((max 1 r.val : ℕ) : ℝ) -
        (Q : ℝ) * Real.log ((max 1 s.val : ℕ) : ℝ))
    linarith [first.1, second.2]

theorem
    dSVDensityRationalPublicLogRankPhaseWeightedCrossing_min_le
    {N B : ℕ} (positive : 0 < B) (Q : ℕ)
    (r s : Fin (N + 1)) :
    min (r.val : ℝ) (s.val : ℝ) *
        dSVDensityRationalPublicLogRankPhaseWeightedCrossing
          Q B r s ≤
      (Q : ℝ) / (B : ℝ) * |(r.val : ℝ) - (s.val : ℝ)| +
        min (r.val : ℝ) (s.val : ℝ) / (B : ℝ) := by
  by_cases zero_r : r.val = 0
  · simp only [zero_r, CharP.cast_eq_zero, Nat.cast_nonneg, inf_of_le_left, zero_mul, zero_sub,
      abs_neg, Nat.abs_cast, zero_div, add_zero]
    positivity
  by_cases zero_s : s.val = 0
  · simp only [zero_s, CharP.cast_eq_zero, Nat.cast_nonneg, inf_of_le_right, zero_mul, sub_zero,
      Nat.abs_cast, zero_div, add_zero]
    positivity
  have positive_real : (0 : ℝ) < (B : ℝ) := by
    exact_mod_cast positive
  have common_nonnegative :
      0 ≤ min (r.val : ℝ) (s.val : ℝ) :=
    le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have finite_crossing :=
    dSVDensityRationalPublicLogRankPhaseWeightedCrossing_le_fineLabel
      positive Q r s zero_r zero_s
  have floor_error :=
    dSVDensityRationalPublicLogRankFineLabel_abs_sub_le Q r s
  have logarithmic :=
    dSVDensityRationalPublicLogRank_zeroSafe_fin_bound r s
  calc
    min (r.val : ℝ) (s.val : ℝ) *
        dSVDensityRationalPublicLogRankPhaseWeightedCrossing
          Q B r s ≤
      min (r.val : ℝ) (s.val : ℝ) *
        (|(dSVDensityRationalPublicLogRankFineLabel Q r : ℝ) -
          (dSVDensityRationalPublicLogRankFineLabel Q s : ℝ)| /
            (B : ℝ)) :=
      mul_le_mul_of_nonneg_left finite_crossing common_nonnegative
    _ ≤ min (r.val : ℝ) (s.val : ℝ) *
        (((Q : ℝ) *
          |Real.log ((max 1 r.val : ℕ) : ℝ) -
            Real.log ((max 1 s.val : ℕ) : ℝ)| + 1) / (B : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ common_nonnegative
      exact div_le_div_of_nonneg_right floor_error positive_real.le
    _ = (Q : ℝ) / (B : ℝ) *
          (min (r.val : ℝ) (s.val : ℝ) *
            |Real.log ((max 1 r.val : ℕ) : ℝ) -
              Real.log ((max 1 s.val : ℕ) : ℝ)|) +
          min (r.val : ℝ) (s.val : ℝ) / (B : ℝ) := by
      ring
    _ ≤ (Q : ℝ) / (B : ℝ) *
          |(r.val : ℝ) - (s.val : ℝ)| +
          min (r.val : ℝ) (s.val : ℝ) / (B : ℝ) := by
      have scaled := mul_le_mul_of_nonneg_left logarithmic
        (div_nonneg (Nat.cast_nonneg Q) positive_real.le)
      linarith

end

section

open scoped BigOperators Kronecker ComplexOrder MatrixOrder

theorem
    dSVDensityRationalPublicLogRankBucketRepresentative_val_pos
    {N B : ℕ} (Q : ℕ) (phase : Fin B)
    (r : Fin (N + 1)) (nonzero : r.val ≠ 0) :
    0 < (dSVDensityRationalPublicLogRankBucketRepresentative
      (N := N) Q phase
        (dSVDensityRationalPublicLogRankBucket
          Q phase r)).val := by
  exact Nat.pos_of_ne_zero
    (dSVDensityRationalPublicLogRankBucketRepresentative_same
      Q phase r nonzero).1

theorem
    dSVDensityRationalPublicLogRankBucketRepresentative_actual_log_sub_lt
    {N B : ℕ} {Q : ℕ} (positive_Q : 0 < Q)
    (phase : Fin B) (r : Fin (N + 1)) (nonzero : r.val ≠ 0) :
    |Real.log (r.val : ℝ) -
      Real.log
        ((dSVDensityRationalPublicLogRankBucketRepresentative
          (N := N) Q phase
            (dSVDensityRationalPublicLogRankBucket
              Q phase r)).val : ℝ)| <
      ((B : ℝ) + 1) / (Q : ℝ) := by
  have one_r : 1 ≤ r.val := Nat.one_le_iff_ne_zero.mpr nonzero
  have one_representative :
      1 ≤ (dSVDensityRationalPublicLogRankBucketRepresentative
        (N := N) Q phase
          (dSVDensityRationalPublicLogRankBucket
            Q phase r)).val :=
    dSVDensityRationalPublicLogRankBucketRepresentative_val_pos
      Q phase r nonzero
  simpa only [gt_iff_lt, max_eq_right one_r, max_eq_right one_representative] using
    (dSVDensityRationalPublicLogRankBucketRepresentative_log_sub_lt
      positive_Q phase r nonzero)

theorem
    dSVDensityRationalPublicLogRankBucketRepresentative_rank_ratio_lt
    {N B : ℕ} {Q : ℕ} (positive_Q : 0 < Q)
    (phase : Fin B) (r : Fin (N + 1)) (nonzero : r.val ≠ 0) :
    (r.val : ℝ) /
        ((dSVDensityRationalPublicLogRankBucketRepresentative
          (N := N) Q phase
            (dSVDensityRationalPublicLogRankBucket
              Q phase r)).val : ℝ) <
      Real.exp (((B : ℝ) + 1) / (Q : ℝ)) := by
  let representative : Fin (N + 1) :=
    dSVDensityRationalPublicLogRankBucketRepresentative
      (N := N) Q phase
        (dSVDensityRationalPublicLogRankBucket Q phase r)
  have positive_r : (0 : ℝ) < (r.val : ℝ) := by
    exact_mod_cast (Nat.pos_of_ne_zero nonzero)
  have positive_representative_nat : 0 < representative.val := by
    dsimp [representative]
    exact
      dSVDensityRationalPublicLogRankBucketRepresentative_val_pos
        Q phase r nonzero
  have positive_representative :
      (0 : ℝ) < (representative.val : ℝ) := by
    exact_mod_cast positive_representative_nat
  have diameter :=
    dSVDensityRationalPublicLogRankBucketRepresentative_actual_log_sub_lt
      positive_Q phase r nonzero
  change
    |Real.log (r.val : ℝ) - Real.log (representative.val : ℝ)| <
      ((B : ℝ) + 1) / (Q : ℝ) at diameter
  have logarithmic :
      Real.log (r.val : ℝ) - Real.log (representative.val : ℝ) <
        ((B : ℝ) + 1) / (Q : ℝ) :=
    lt_of_le_of_lt (le_abs_self _) diameter
  have exponential := (Real.exp_lt_exp).mpr logarithmic
  rw [← Real.log_div positive_r.ne' positive_representative.ne',
    Real.exp_log (div_pos positive_r positive_representative)] at exponential
  exact exponential

theorem
    dSVDensityRationalPublicLogRankBucketRepresentative_relative_sub_lt
    {N B : ℕ} {Q : ℕ} (positive_Q : 0 < Q)
    (phase : Fin B) (r : Fin (N + 1)) (nonzero : r.val ≠ 0) :
    ((r.val : ℝ) -
      ((dSVDensityRationalPublicLogRankBucketRepresentative
        (N := N) Q phase
          (dSVDensityRationalPublicLogRankBucket
            Q phase r)).val : ℝ)) /
      ((dSVDensityRationalPublicLogRankBucketRepresentative
        (N := N) Q phase
          (dSVDensityRationalPublicLogRankBucket
            Q phase r)).val : ℝ) <
      Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1 := by
  let representative : Fin (N + 1) :=
    dSVDensityRationalPublicLogRankBucketRepresentative
      (N := N) Q phase
        (dSVDensityRationalPublicLogRankBucket Q phase r)
  have positive_representative_nat : 0 < representative.val := by
    dsimp [representative]
    exact
      dSVDensityRationalPublicLogRankBucketRepresentative_val_pos
        Q phase r nonzero
  have positive_representative :
      (0 : ℝ) < (representative.val : ℝ) := by
    exact_mod_cast positive_representative_nat
  have ratio :=
    dSVDensityRationalPublicLogRankBucketRepresentative_rank_ratio_lt
      positive_Q phase r nonzero
  change
    (r.val : ℝ) / (representative.val : ℝ) <
      Real.exp (((B : ℝ) + 1) / (Q : ℝ)) at ratio
  change
    ((r.val : ℝ) - (representative.val : ℝ)) /
        (representative.val : ℝ) <
      Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1
  rw [sub_div, div_self positive_representative.ne']
  linarith

theorem
    dSVDensityRationalPublicLogRankBucketRepresentative_relative_abs_lt
    {N B : ℕ} {Q : ℕ} (positive_Q : 0 < Q)
    (phase : Fin B) (r : Fin (N + 1)) (nonzero : r.val ≠ 0) :
    |(r.val : ℝ) -
      ((dSVDensityRationalPublicLogRankBucketRepresentative
        (N := N) Q phase
          (dSVDensityRationalPublicLogRankBucket
            Q phase r)).val : ℝ)| /
      ((max 1
        (min r.val
          (dSVDensityRationalPublicLogRankBucketRepresentative
            (N := N) Q phase
              (dSVDensityRationalPublicLogRankBucket
                Q phase r)).val) : ℕ) : ℝ) <
      Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1 := by
  let representative : Fin (N + 1) :=
    dSVDensityRationalPublicLogRankBucketRepresentative
      (N := N) Q phase
        (dSVDensityRationalPublicLogRankBucket Q phase r)
  have ordered : representative.val ≤ r.val := by
    exact
      dSVDensityRationalPublicLogRankBucketRepresentative_le
        Q phase r nonzero
  have one_representative : 1 ≤ representative.val := by
    dsimp [representative]
    exact
      dSVDensityRationalPublicLogRankBucketRepresentative_val_pos
        Q phase r nonzero
  have real_ordered : (representative.val : ℝ) ≤ (r.val : ℝ) := by
    exact_mod_cast ordered
  have relative :=
    dSVDensityRationalPublicLogRankBucketRepresentative_relative_sub_lt
      positive_Q phase r nonzero
  change
    ((r.val : ℝ) - (representative.val : ℝ)) /
        (representative.val : ℝ) <
      Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1 at relative
  change
    |(r.val : ℝ) - (representative.val : ℝ)| /
        ((max 1 (min r.val representative.val) : ℕ) : ℝ) <
      Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1
  simpa only [abs_of_nonneg (sub_nonneg.mpr real_ordered), min_eq_right ordered,
    max_eq_right one_representative] using relative

end

section

open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

theorem dSVDensityRationalPublicLogRankPhaseWeightedCrossing_le_one
    {N B : ℕ} (positive : 0 < B) (Q : ℕ)
    (r s : Fin (N + 1)) :
    dSVDensityRationalPublicLogRankPhaseWeightedCrossing
        Q B r s ≤ 1 := by
  unfold dSVDensityRationalPublicLogRankPhaseWeightedCrossing
  calc
    _ ≤ ∑ phase : Fin B,
        dSVDensityRationalPublicLogRankPhaseWeight B phase := by
      apply Finset.sum_le_sum
      intro phase _
      split_ifs <;>
        simp [dSVDensityRationalPublicLogRankPhaseWeight]
    _ = 1 :=
      dSVDensityRationalPublicLogRankPhaseWeight_sum positive

theorem
    dSVDensityRationalPublicLogRankPhaseWeightedCrossing_alice_le
    {N B : ℕ} (positive : 0 < B) (Q : ℕ)
    (r s : Fin (N + 1)) :
    (r.val : ℝ) *
        dSVDensityRationalPublicLogRankPhaseWeightedCrossing
          Q B r s ≤
      ((Q : ℝ) / (B : ℝ) + 1) *
          |(r.val : ℝ) - (s.val : ℝ)| +
        min (r.val : ℝ) (s.val : ℝ) / (B : ℝ) := by
  let x :=
    dSVDensityRationalPublicLogRankPhaseWeightedCrossing
      Q B r s
  let m : ℝ := min (r.val : ℝ) (s.val : ℝ)
  let t : ℝ := |(r.val : ℝ) - (s.val : ℝ)|
  have nonnegative : 0 ≤ x :=
    dSVDensityRationalPublicLogRankPhaseWeightedCrossing_nonneg
      Q B r s
  have probability : x ≤ 1 :=
    dSVDensityRationalPublicLogRankPhaseWeightedCrossing_le_one
      positive Q r s
  have min_le : m ≤ (r.val : ℝ) := min_le_left _ _
  have difference : (r.val : ℝ) - m ≤ t := by
    dsimp [m, t]
    rcases le_total (r.val : ℝ) (s.val : ℝ) with ordered | ordered
    · rw [min_eq_left ordered]
      simp only [sub_self, abs_nonneg]
    · rw [min_eq_right ordered, abs_of_nonneg
        (sub_nonneg.mpr ordered)]
  have extra : ((r.val : ℝ) - m) * x ≤ t := by
    calc
      _ ≤ ((r.val : ℝ) - m) * 1 :=
        mul_le_mul_of_nonneg_left probability
          (sub_nonneg.mpr min_le)
      _ ≤ t := by simpa only [mul_one, tsub_le_iff_right] using difference
  have main :=
    dSVDensityRationalPublicLogRankPhaseWeightedCrossing_min_le
      positive Q r s
  change m * x ≤ (Q : ℝ) / (B : ℝ) * t + m / (B : ℝ)
    at main
  change (r.val : ℝ) * x ≤
    ((Q : ℝ) / (B : ℝ) + 1) * t + m / (B : ℝ)
  linarith

theorem
    exists_proofDSVDensityRationalPublicBucketPhysicalQuantitativeMixedPrefixCleanup_sq
    {N B : ℕ} (grid : 0 < N) (phases : 0 < B)
    {Q : ℕ} (fine : 0 < Q)
    (ε : ℝ) (precision : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧
      ∃ A C : Fin B → Option ℕ →
          Matrix.unitaryGroup (Fin (N * n)) ℂ,
        ∀ (r s : Fin (N + 1)),
          (∑ phase : Fin B,
            dSVDensityRationalPublicLogRankPhaseWeight B phase *
              ‖localUnitaryAction
                  (A phase
                    (dSVDensityRationalPublicLogRankBucket
                      Q phase r))
                  (C phase
                    (dSVDensityRationalPublicLogRankBucket
                      Q phase s))
                  (dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
                    n (dSVCanonicalFailurePrefix
                      (dSVDensityRationalPublicBucketPhysicalCommonRank
                        r s))) -
                Real.sqrt (r.val : ℝ) •
                  embezzlementState (N * n)‖ ^ 2) ≤
            2 * |(r.val : ℝ) - (s.val : ℝ)| +
            4 * (r.val : ℝ) * ε ^ 2 +
            16 * (r.val : ℝ) *
              (Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1) +
            8 * (((Q : ℝ) / (B : ℝ) + 1) *
              |(r.val : ℝ) - (s.val : ℝ)| +
              min (r.val : ℝ) (s.val : ℝ) / (B : ℝ)) := by
  let bucket : Fin B → Fin (N + 1) → Option ℕ :=
    dSVDensityRationalPublicLogRankBucket Q
  let representative : Fin B → Option ℕ → Fin (N + 1) :=
    dSVDensityRationalPublicLogRankBucketRepresentative Q
  obtain ⟨n, positive, A, C, accurate⟩ :=
    exists_proofDSVDensityRationalPublicBucketPhysicalMixedPrefixCleanup_sq
      grid bucket representative ε precision
  refine ⟨n, positive, A, C, ?_⟩
  intro r s
  let gap : ℝ := |(r.val : ℝ) - (s.val : ℝ)|
  let radius : ℝ :=
    Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1
  let base : ℝ :=
    2 * gap + 4 * (r.val : ℝ) * ε ^ 2 +
      16 * (r.val : ℝ) * radius
  have representative_bound (phase : Fin B) :
      (r.val : ℝ) *
          (|(r.val : ℝ) -
            ((representative phase (bucket phase r)).val : ℝ)| /
            ((max 1
              (min r.val
                (representative phase (bucket phase r)).val) : ℕ) : ℝ)) ≤
        (r.val : ℝ) * radius := by
    by_cases zero : r.val = 0
    · simp only [zero, CharP.cast_eq_zero, zero_sub, abs_neg, Nat.abs_cast, zero_le,
        inf_of_le_left, sup_of_le_left, Nat.cast_one, div_one, zero_mul, Std.le_refl]
    · have actual :=
        dSVDensityRationalPublicLogRankBucketRepresentative_relative_abs_lt
          fine phase r zero
      change
        |(r.val : ℝ) -
          ((representative phase (bucket phase r)).val : ℝ)| /
          ((max 1
            (min r.val
              (representative phase (bucket phase r)).val) : ℕ) : ℝ) <
          radius at actual
      exact mul_le_mul_of_nonneg_left actual.le (Nat.cast_nonneg r.val)
  have point (phase : Fin B) :
      ‖localUnitaryAction
          (A phase (bucket phase r))
          (C phase (bucket phase s))
          (dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
            n (dSVCanonicalFailurePrefix
              (dSVDensityRationalPublicBucketPhysicalCommonRank
                r s))) -
        Real.sqrt (r.val : ℝ) •
          embezzlementState (N * n)‖ ^ 2 ≤
        base + 8 * (r.val : ℝ) *
          (if bucket phase r = bucket phase s
            then (0 : ℝ) else 1) := by
    have actual := accurate phase r s
    have variation := representative_bound phase
    calc
      _ ≤ 2 * gap +
          2 * (r.val : ℝ) *
            (2 * ε ^ 2 +
              8 *
                |(r.val : ℝ) -
                  ((representative phase (bucket phase r)).val : ℝ)| /
                  ((max 1
                    (min r.val
                      (representative phase (bucket phase r)).val) : ℕ) : ℝ) +
              4 * (if bucket phase r = bucket phase s
                then (0 : ℝ) else 1)) := by
                simpa only [Nat.cast_max, Nat.cast_one, Nat.cast_min, mul_ite, mul_zero, mul_one,
                  gap] using actual
      _ = 2 * gap + 4 * (r.val : ℝ) * ε ^ 2 +
          16 * ((r.val : ℝ) *
            (|(r.val : ℝ) -
              ((representative phase (bucket phase r)).val : ℝ)| /
              ((max 1
                (min r.val
                  (representative phase (bucket phase r)).val) : ℕ) : ℝ))) +
          8 * (r.val : ℝ) *
            (if bucket phase r = bucket phase s
              then (0 : ℝ) else 1) := by ring
      _ ≤ base + 8 * (r.val : ℝ) *
            (if bucket phase r = bucket phase s
              then (0 : ℝ) else 1) := by
            dsimp [base]
            linarith
  have averaged :
      (∑ phase : Fin B,
        dSVDensityRationalPublicLogRankPhaseWeight B phase *
          ‖localUnitaryAction
              (A phase (bucket phase r))
              (C phase (bucket phase s))
              (dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
                n (dSVCanonicalFailurePrefix
                  (dSVDensityRationalPublicBucketPhysicalCommonRank
                    r s))) -
            Real.sqrt (r.val : ℝ) •
              embezzlementState (N * n)‖ ^ 2) ≤
        base + 8 * (r.val : ℝ) *
          dSVDensityRationalPublicLogRankPhaseWeightedCrossing
            Q B r s := by
    calc
      _ ≤ ∑ phase : Fin B,
          dSVDensityRationalPublicLogRankPhaseWeight B phase *
            (base + 8 * (r.val : ℝ) *
              (if bucket phase r = bucket phase s
                then (0 : ℝ) else 1)) := by
            apply Finset.sum_le_sum
            intro phase _
            exact mul_le_mul_of_nonneg_left (point phase)
              (by
                unfold dSVDensityRationalPublicLogRankPhaseWeight
                positivity)
      _ = base + 8 * (r.val : ℝ) *
          dSVDensityRationalPublicLogRankPhaseWeightedCrossing
            Q B r s := by
            unfold
              dSVDensityRationalPublicLogRankPhaseWeightedCrossing
            have total :=
              dSVDensityRationalPublicLogRankPhaseWeight_sum
                phases
            calc
              _ = base *
                    (∑ phase : Fin B,
                      dSVDensityRationalPublicLogRankPhaseWeight
                        B phase) +
                  8 * (r.val : ℝ) *
                    (∑ phase : Fin B,
                      dSVDensityRationalPublicLogRankPhaseWeight
                        B phase *
                        (if bucket phase r = bucket phase s
                          then (0 : ℝ) else 1)) := by
                    simp_rw [Finset.mul_sum]
                    rw [← Finset.sum_add_distrib]
                    apply Finset.sum_congr rfl
                    intro phase _
                    ring
              _ = _ := by rw [total]; simp only [mul_one, mul_ite, mul_zero, bucket]
  have crossing :=
    dSVDensityRationalPublicLogRankPhaseWeightedCrossing_alice_le
      phases Q r s
  change _ ≤ 2 * gap + 4 * (r.val : ℝ) * ε ^ 2 +
    16 * (r.val : ℝ) * radius +
    8 * (((Q : ℝ) / (B : ℝ) + 1) * gap +
      min (r.val : ℝ) (s.val : ℝ) / (B : ℝ))
  change
    (r.val : ℝ) *
        dSVDensityRationalPublicLogRankPhaseWeightedCrossing
          Q B r s ≤
      ((Q : ℝ) / (B : ℝ) + 1) * gap +
        min (r.val : ℝ) (s.val : ℝ) / (B : ℝ)
    at crossing
  dsimp [bucket] at averaged
  dsimp [base] at averaged
  linarith

private def dSVDensityRationalHeterogeneousCommonStopSpectralAtomWeight
    {d : ℕ} (N : ℕ)
    (ξ ζ : BipartiteUnitVector d)
    (i j : Fin d) : ℝ :=
  dSVDensityRationalPrefixHarmonicSpectralOverlap ξ ζ i j /
    ((d : ℝ) * (N : ℝ))

theorem
    dSVDensityRationalHeterogeneousCommonStopSpectralAtomWeight_nonneg
    {d : ℕ} (N : ℕ)
    (ξ ζ : BipartiteUnitVector d)
    (i j : Fin d) :
    0 ≤ dSVDensityRationalHeterogeneousCommonStopSpectralAtomWeight
      N ξ ζ i j := by
  exact div_nonneg
    (dSVDensityRationalPrefixHarmonicSpectralOverlap_nonneg
      ξ ζ i j)
    (mul_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg N))

private def dSVDensityRationalHeterogeneousCommonStopSpectralRankGap
    {d : ℕ} (N : ℕ) (w : ℝ)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d,
    dSVDensityRationalHeterogeneousCommonStopSpectralAtomWeight
      N ξ ζ i j *
      |((dSVDensityRationalPhysicalAcceptedRank w N ξ i).val : ℝ) -
        ((dSVDensityRationalPhysicalAcceptedRank w N ζ j).val : ℝ)|

theorem
    dSVDensityRationalHeterogeneousCommonStopSpectralRankGap_eq_hazard
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (w : ℝ) (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalHeterogeneousCommonStopSpectralRankGap
        N w ξ ζ =
      dSVDensityRationalPhysicalProjectorCrossHazard N w ξ ζ := by
  rw [← dSVDensityRationalPrefixRankMismatch_physicalHazard
    grid dimension w ξ ζ]
  unfold
    dSVDensityRationalHeterogeneousCommonStopSpectralRankGap
    dSVDensityRationalHeterogeneousCommonStopSpectralAtomWeight
    dSVDensityRationalPrefixRankMismatch
    dSVDensityRationalPrefixHarmonicSpectralOverlap
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
  rw [div_div, mul_comm (N : ℝ) (d : ℝ)]

private def dSVDensityRationalHeterogeneousCommonStopSpectralAliceMass
    {d : ℕ} (N : ℕ) (w : ℝ)
    (ξ ζ : BipartiteUnitVector d) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d,
    dSVDensityRationalHeterogeneousCommonStopSpectralAtomWeight
      N ξ ζ i j *
      ((dSVDensityRationalPhysicalAcceptedRank w N ξ i).val : ℝ)

theorem
    dSVDensityRationalHeterogeneousCommonStopSpectralAliceMass_eq_diagonalBorn
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (w : ℝ) (ξ ζ : BipartiteUnitVector d) :
    dSVDensityRationalHeterogeneousCommonStopSpectralAliceMass
        N w ξ ζ =
      dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension w ξ := by
  classical
  have row (i : Fin d) :
      (∑ j : Fin d,
        dSVDensityRationalPrefixHarmonicSpectralOverlap
          ξ ζ i j) = 1 := by
    unfold dSVDensityRationalPrefixHarmonicSpectralOverlap
    exact spectralAtomOverlap_sum_right
      (dSVSoftBobLeftReducedDensity ξ)
      (dSVSoftBobLeftReducedDensity ζ)
      (dSVSoftBobLeftReducedDensity_posSemidef ξ)
      (dSVSoftBobLeftReducedDensity_posSemidef ζ) i
  rw [dSVDensityRationalPhysicalDiagonalBornSuccess_eq
    grid dimension w ξ]
  unfold
    dSVDensityRationalHeterogeneousCommonStopSpectralAliceMass
    dSVDensityRationalHeterogeneousCommonStopSpectralAtomWeight
    dSVDensityRationalLeftProjectiveDiagonalMass
  simp_rw [dSVDensityRationalPhysicalAcceptedRank_gridPrefix]
  calc
    (∑ i : Fin d, ∑ j : Fin d,
      dSVDensityRationalPrefixHarmonicSpectralOverlap ξ ζ i j /
          ((d : ℝ) * (N : ℝ)) *
        ((dSVDensityRationalPhysicalAcceptedRank
          w N ξ i).val : ℝ)) =
      ∑ i : Fin d,
        (((dSVDensityRationalPhysicalAcceptedRank
          w N ξ i).val : ℝ) / ((d : ℝ) * (N : ℝ))) *
          (∑ j : Fin d,
            dSVDensityRationalPrefixHarmonicSpectralOverlap
              ξ ζ i j) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ = ∑ i : Fin d,
        ((dSVDensityRationalPhysicalAcceptedRank
          w N ξ i).val : ℝ) / ((d : ℝ) * (N : ℝ)) := by
      simp_rw [row, mul_one]
    _ = (∑ i : Fin d,
        ((dSVDensityRationalPhysicalAcceptedRank
          w N ξ i).val : ℝ)) /
          ((d : ℝ) * (N : ℝ)) := by
      rw [Finset.sum_div]
    _ = ((∑ i : Fin d,
        ((dSVDensityRationalPhysicalAcceptedRank
          w N ξ i).val : ℝ)) / (N : ℝ)) / (d : ℝ) := by
      rw [div_div, mul_comm (N : ℝ) (d : ℝ)]
    _ = (∑ i : Fin d,
        ((dSVDensityRationalPhysicalAcceptedRank
          w N ξ i).val : ℝ) / (N : ℝ)) / (d : ℝ) := by
      rw [Finset.sum_div]

private theorem finitePhaseWeightedDoubleSum_exchange
    {I J P : Type*} [Fintype I] [Fintype J] [Fintype P]
    (phaseWeight : P → ℝ) (coefficient : I → J → ℝ)
    (term : P → I → J → ℝ) :
    (∑ phase, phaseWeight phase *
        ∑ i, ∑ j, coefficient i j * term phase i j) =
      ∑ i, ∑ j, coefficient i j *
        ∑ phase, phaseWeight phase * term phase i j := by
  calc
    _ = ∑ phase, ∑ i, ∑ j,
        phaseWeight phase * (coefficient i j * term phase i j) := by
      simp_rw [Finset.mul_sum]
    _ = ∑ i, ∑ j, ∑ phase,
        phaseWeight phase * (coefficient i j * term phase i j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro phase _
      ring

private theorem finiteDoubleSum_mul_add
    {I J : Type*} [Fintype I] [Fintype J]
    (coefficient first second : I → J → ℝ) (left right : ℝ) :
    (∑ i, ∑ j, coefficient i j *
        (left * first i j + right * second i j)) =
      left * (∑ i, ∑ j, coefficient i j * first i j) +
        right * (∑ i, ∑ j, coefficient i j * second i j) := by
  simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem
    exists_proofDSVDensityRationalHeterogeneousCommonStopSpectralGaugeContinuity_sq
    {d N B : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (phases : 0 < B) {Q : ℕ} (fine : 0 < Q)
    (ε : ℝ) (precision : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧
      ∃ A C : Fin B → Option ℕ →
          Matrix.unitaryGroup (Fin (N * n)) ℂ,
        ∀ {S L : ℕ}
          (width : Fin S → ℝ) (schedule : Fin L → Fin S)
          (ξ ζ : BipartiteUnitVector d) (k : Fin L),
          ‖dSVDensityRationalPublicBucketPhysicalCoherentLocalReset
              Q (width (schedule k)) ξ ζ A C
              (dSVDensityRationalPublicBucketPhysicalCoherentMixedState
                (N := N) (B := B)
                (width (schedule k)) n ξ ζ) -
            dSVDensityRationalPublicBucketPhysicalCoherentTargetState
              (N := N) (B := B)
              (width (schedule k)) n ξ ζ‖ ^ 2 ≤
            (10 + 8 * ((Q : ℝ) / (B : ℝ))) *
                dSVDensityRationalPhysicalProjectorCrossHazard
                  N (width (schedule k)) ξ ζ +
              (4 * ε ^ 2 +
                16 * (Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1) +
                8 / (B : ℝ)) *
                dSVDensityRationalPhysicalDiagonalBornSuccess
                  grid dimension (width (schedule k)) ξ := by
  classical
  obtain ⟨n, harmonic, A, C, accurate⟩ :=
    exists_proofDSVDensityRationalPublicBucketPhysicalQuantitativeMixedPrefixCleanup_sq
      grid phases fine ε precision
  refine ⟨n, harmonic, A, C, ?_⟩
  intro S L width schedule ξ ζ k
  let w : ℝ := width (schedule k)
  let coefficient :=
    dSVDensityRationalHeterogeneousCommonStopSpectralAtomWeight N ξ ζ
  let gap : Fin d → Fin d → ℝ := fun i j =>
    |((dSVDensityRationalPhysicalAcceptedRank w N ξ i).val : ℝ) -
      ((dSVDensityRationalPhysicalAcceptedRank w N ζ j).val : ℝ)|
  let alice : Fin d → ℝ := fun i =>
    ((dSVDensityRationalPhysicalAcceptedRank w N ξ i).val : ℝ)
  let Kgap : ℝ := 10 + 8 * ((Q : ℝ) / (B : ℝ))
  let Kmass : ℝ := 4 * ε ^ 2 +
    16 * (Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1) + 8 / (B : ℝ)
  have point (i j : Fin d) :
      (∑ phase : Fin B,
        dSVDensityRationalPublicLogRankPhaseWeight B phase *
          ‖localUnitaryAction
              (A phase
                (dSVDensityRationalPublicLogRankBucket Q phase
                  (dSVDensityRationalPhysicalAcceptedRank
                    w N ξ i)))
              (C phase
                (dSVDensityRationalPublicLogRankBucket Q phase
                  (dSVDensityRationalPhysicalAcceptedRank
                    w N ζ j)))
              (dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
                n (dSVDensityRationalPhysicalMixedAcceptedPrefixWork
                  w N ξ ζ i j)) -
            Real.sqrt (alice i) •
              embezzlementState (N * n)‖ ^ 2) ≤
        Kgap * gap i j + Kmass * alice i := by
    have atom := accurate
      (dSVDensityRationalPhysicalAcceptedRank w N ξ i)
      (dSVDensityRationalPhysicalAcceptedRank w N ζ j)
    rw [dSVDensityRationalPublicBucketPhysicalCommonRank_eq
      w ξ ζ i j] at atom
    change
      (∑ phase : Fin B,
        dSVDensityRationalPublicLogRankPhaseWeight B phase *
          ‖localUnitaryAction
              (A phase
                (dSVDensityRationalPublicLogRankBucket Q phase
                  (dSVDensityRationalPhysicalAcceptedRank
                    w N ξ i)))
              (C phase
                (dSVDensityRationalPublicLogRankBucket Q phase
                  (dSVDensityRationalPhysicalAcceptedRank
                    w N ζ j)))
              (dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
                n (dSVDensityRationalPhysicalMixedAcceptedPrefixWork
                  w N ξ ζ i j)) -
            Real.sqrt (alice i) •
              embezzlementState (N * n)‖ ^ 2) ≤
        2 * gap i j + 4 * alice i * ε ^ 2 +
          16 * alice i *
            (Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1) +
          8 * (((Q : ℝ) / (B : ℝ) + 1) * gap i j +
            min (alice i)
              ((dSVDensityRationalPhysicalAcceptedRank
                w N ζ j).val : ℝ) / (B : ℝ)) at atom
    have min_bound :
        min (alice i)
            ((dSVDensityRationalPhysicalAcceptedRank
              w N ζ j).val : ℝ) / (B : ℝ) ≤
          alice i / (B : ℝ) :=
      div_le_div_of_nonneg_right (min_le_left _ _)
        (by exact_mod_cast phases.le)
    calc
      _ ≤ 2 * gap i j + 4 * alice i * ε ^ 2 +
          16 * alice i *
            (Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1) +
          8 * (((Q : ℝ) / (B : ℝ) + 1) * gap i j +
            min (alice i)
              ((dSVDensityRationalPhysicalAcceptedRank
                w N ζ j).val : ℝ) / (B : ℝ)) := atom
      _ = Kgap * gap i j +
          (4 * ε ^ 2 +
            16 * (Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1)) *
              alice i +
          8 * (min (alice i)
            ((dSVDensityRationalPhysicalAcceptedRank
              w N ζ j).val : ℝ) / (B : ℝ)) := by
        dsimp [Kgap]
        ring
      _ ≤ Kgap * gap i j +
          (4 * ε ^ 2 +
            16 * (Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1)) *
              alice i +
          8 * (alice i / (B : ℝ)) := by
        linarith [min_bound]
      _ = Kgap * gap i j + Kmass * alice i := by
        dsimp [Kmass]
        ring
  have exchange :
      dSVDensityRationalPublicBucketPhysicalPhaseWeightedMixedError
          Q w ξ ζ A C =
        ∑ i : Fin d, ∑ j : Fin d,
          coefficient i j *
            (∑ phase : Fin B,
              dSVDensityRationalPublicLogRankPhaseWeight B phase *
                ‖localUnitaryAction
                    (A phase
                      (dSVDensityRationalPublicLogRankBucket
                        Q phase
                        (dSVDensityRationalPhysicalAcceptedRank
                          w N ξ i)))
                    (C phase
                      (dSVDensityRationalPublicLogRankBucket
                        Q phase
                        (dSVDensityRationalPhysicalAcceptedRank
                          w N ζ j)))
                    (dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor
                      n
                      (dSVDensityRationalPhysicalMixedAcceptedPrefixWork
                        w N ξ ζ i j)) -
                  Real.sqrt (alice i) •
                    embezzlementState (N * n)‖ ^ 2) := by
    unfold dSVDensityRationalPublicBucketPhysicalPhaseWeightedMixedError
    exact finitePhaseWeightedDoubleSum_exchange
      (dSVDensityRationalPublicLogRankPhaseWeight B) coefficient
      (fun phase i j =>
        ‖localUnitaryAction
            (A phase
              (dSVDensityRationalPublicLogRankBucket Q phase
                (dSVDensityRationalPhysicalAcceptedRank w N ξ i)))
            (C phase
              (dSVDensityRationalPublicLogRankBucket Q phase
                (dSVDensityRationalPhysicalAcceptedRank w N ζ j)))
            (dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor n
              (dSVDensityRationalPhysicalMixedAcceptedPrefixWork
                w N ξ ζ i j)) -
          Real.sqrt (alice i) • embezzlementState (N * n)‖ ^ 2)
  rw [dSVDensityRationalPublicBucketPhysicalCoherentMixedReset_distance_sq
    phases Q w ξ ζ A C, exchange]
  calc
    _ ≤ ∑ i : Fin d, ∑ j : Fin d,
        coefficient i j * (Kgap * gap i j + Kmass * alice i) := by
      refine Finset.sum_le_sum fun i _ => ?_
      refine Finset.sum_le_sum fun j _ => ?_
      exact mul_le_mul_of_nonneg_left (point i j)
        (dSVDensityRationalHeterogeneousCommonStopSpectralAtomWeight_nonneg
          N ξ ζ i j)
    _ = Kgap *
          dSVDensityRationalHeterogeneousCommonStopSpectralRankGap
            N w ξ ζ +
        Kmass *
          dSVDensityRationalHeterogeneousCommonStopSpectralAliceMass
            N w ξ ζ := by
      simpa only [dSVDensityRationalHeterogeneousCommonStopSpectralRankGap,
        dSVDensityRationalHeterogeneousCommonStopSpectralAliceMass] using
          finiteDoubleSum_mul_add coefficient gap
            (fun i _ => alice i) Kgap Kmass
    _ = _ := by
      rw [dSVDensityRationalHeterogeneousCommonStopSpectralRankGap_eq_hazard
          grid dimension w ξ ζ,
        dSVDensityRationalHeterogeneousCommonStopSpectralAliceMass_eq_diagonalBorn
          grid dimension w ξ ζ]

end

section

open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder

/--
The DSV density rational heterogeneous common stop gauge stage error construction used in the
quantum parallel-repetition argument.
-/
def dSVDensityRationalHeterogeneousCommonStopGaugeStageError
    {d N B : ℕ} (Q : ℕ) (w : ℝ) (n : ℕ)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin B → Option ℕ →
      Matrix.unitaryGroup (Fin (N * n)) ℂ) : ℝ :=
  ‖dSVDensityRationalPublicBucketPhysicalCoherentLocalReset
        Q w ξ ζ A C
        (dSVDensityRationalPublicBucketPhysicalCoherentMixedState
          (N := N) (B := B) w n ξ ζ) -
      dSVDensityRationalPublicBucketPhysicalCoherentTargetState
        (N := N) (B := B) w n ξ ζ‖ ^ 2

private def dSVDensityRationalHeterogeneousStoppedCommonStopGaugeError
    {d N B S L : ℕ} (Q : ℕ) (n : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin B → Option ℕ →
      Matrix.unitaryGroup (Fin (N * n)) ℂ) : ℝ :=
  ∑ k : Fin L,
    dSVDensityRationalHeterogeneousPhysicalSurvival
        N width schedule ξ ζ k.val *
      dSVDensityRationalHeterogeneousCommonStopGaugeStageError
        Q (width (schedule k)) n ξ ζ A C

theorem
    dSVDensityRationalHeterogeneousPhysicalDiagonalSurvival_budget
    {d S L N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d) :
    (∑ k : Fin L,
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ k.val *
        dSVDensityRationalPhysicalDiagonalBornSuccess
          grid dimension (width (schedule k)) ξ) ≤ 1 := by
  calc
    _ ≤ ∑ k : Fin L,
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ k.val *
        (dSVDensityRationalHeterogeneousPhysicalStageSuccess
            N width schedule ξ ζ k.val +
          dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
            N width schedule ξ ζ k.val) := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left
        (dSVDensityRationalHeterogeneousPhysicalStage_escape_ge_diagonal
          grid dimension width schedule ξ ζ k)
        (dSVDensityRationalHeterogeneousPhysicalSurvival_nonneg
          N width schedule ξ ζ k.val)
    _ = ∑ k ∈ Finset.range L,
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ k *
        (dSVDensityRationalHeterogeneousPhysicalStageSuccess
            N width schedule ξ ζ k +
          dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
            N width schedule ξ ζ k) := by
      simpa only using
        (Fin.sum_univ_eq_sum_range
          (fun k : ℕ =>
            dSVDensityRationalHeterogeneousPhysicalSurvival
                N width schedule ξ ζ k *
              (dSVDensityRationalHeterogeneousPhysicalStageSuccess
                  N width schedule ξ ζ k +
                dSVDensityRationalHeterogeneousPhysicalStageAsynchronous
                  N width schedule ξ ζ k)) L)
    _ ≤ 1 :=
      dSVDensityRationalHeterogeneousPhysicalStoppedEscape_budget
        grid dimension width schedule ξ ζ

theorem
    exists_proofDSVDensityRationalHeterogeneousStoppedCommonStopGaugeErrorBound
    {d N B : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (phases : 0 < B) {Q : ℕ} (fine : 0 < Q)
    (ε : ℝ) (precision : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧
      ∃ A C : Fin B → Option ℕ →
          Matrix.unitaryGroup (Fin (N * n)) ℂ,
        ∀ {S L : ℕ}
          (width : Fin S → ℝ) (schedule : Fin L → Fin S)
          (ξ ζ : BipartiteUnitVector d),
          dSVDensityRationalHeterogeneousStoppedCommonStopGaugeError
              Q n width schedule ξ ζ A C ≤
            (10 + 8 * ((Q : ℝ) / (B : ℝ))) *
                dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
                  N width schedule ξ ζ +
              (4 * ε ^ 2 +
                16 * (Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1) +
                8 / (B : ℝ)) := by
  obtain ⟨n, harmonic, A, C, stage⟩ :=
    exists_proofDSVDensityRationalHeterogeneousCommonStopSpectralGaugeContinuity_sq
      grid dimension phases fine ε precision
  let Kgap : ℝ := 10 + 8 * ((Q : ℝ) / (B : ℝ))
  let Kmass : ℝ :=
    4 * ε ^ 2 +
      16 * (Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1) +
      8 / (B : ℝ)
  have exponent_nonnegative : 0 ≤ (((B : ℝ) + 1) / (Q : ℝ)) := by
    positivity
  have exponential_nonnegative :
      0 ≤ Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1 := by
    have exponential := Real.add_one_le_exp
      (((B : ℝ) + 1) / (Q : ℝ))
    linarith
  have Kmass_nonnegative : 0 ≤ Kmass := by
    dsimp [Kmass]
    positivity
  refine ⟨n, harmonic, A, C, ?_⟩
  intro S L width schedule ξ ζ
  have diagonal_budget :=
    dSVDensityRationalHeterogeneousPhysicalDiagonalSurvival_budget
      grid dimension width schedule ξ ζ
  unfold dSVDensityRationalHeterogeneousStoppedCommonStopGaugeError
  change
    (∑ k : Fin L,
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ k.val *
        dSVDensityRationalHeterogeneousCommonStopGaugeStageError
          Q (width (schedule k)) n ξ ζ A C) ≤
      Kgap *
          dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
            N width schedule ξ ζ + Kmass
  calc
    _ ≤ ∑ k : Fin L,
      dSVDensityRationalHeterogeneousPhysicalSurvival
          N width schedule ξ ζ k.val *
        (Kgap *
            dSVDensityRationalPhysicalProjectorCrossHazard
              N (width (schedule k)) ξ ζ +
          Kmass *
            dSVDensityRationalPhysicalDiagonalBornSuccess
              grid dimension (width (schedule k)) ξ) := by
      apply Finset.sum_le_sum
      intro k _
      have stage_bound := stage width schedule ξ ζ k
      change
        dSVDensityRationalHeterogeneousCommonStopGaugeStageError
            Q (width (schedule k)) n ξ ζ A C ≤
          Kgap *
              dSVDensityRationalPhysicalProjectorCrossHazard
                N (width (schedule k)) ξ ζ +
            Kmass *
              dSVDensityRationalPhysicalDiagonalBornSuccess
                grid dimension (width (schedule k)) ξ at stage_bound
      exact mul_le_mul_of_nonneg_left stage_bound
        (dSVDensityRationalHeterogeneousPhysicalSurvival_nonneg
          N width schedule ξ ζ k.val)
    _ =
      Kgap *
        (∑ k : Fin L,
          dSVDensityRationalHeterogeneousPhysicalSurvival
              N width schedule ξ ζ k.val *
            dSVDensityRationalPhysicalProjectorCrossHazard
              N (width (schedule k)) ξ ζ) +
      Kmass *
        (∑ k : Fin L,
          dSVDensityRationalHeterogeneousPhysicalSurvival
              N width schedule ξ ζ k.val *
            dSVDensityRationalPhysicalDiagonalBornSuccess
              grid dimension (width (schedule k)) ξ) := by
      simp_rw [Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = Kgap *
        dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
          N width schedule ξ ζ +
      Kmass *
        (∑ k : Fin L,
          dSVDensityRationalHeterogeneousPhysicalSurvival
              N width schedule ξ ζ k.val *
            dSVDensityRationalPhysicalDiagonalBornSuccess
              grid dimension (width (schedule k)) ξ) := by
      rw [
        dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass_eq_hazard]
    _ ≤ Kgap *
        dSVDensityRationalHeterogeneousPhysicalStoppedAsynchronousMass
          N width schedule ξ ζ + Kmass := by
      linarith [mul_nonneg Kmass_nonnegative
        (sub_nonneg.mpr diagonal_budget)]

private def dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureCopy
    {S N d L : ℕ} (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L) (i : Fin j.val) :
    EuclideanSpace ℂ
      (DSVUniformDensityThresholdLocalIndex N d ×
       DSVUniformDensityThresholdLocalIndex N d) :=
  dSVDensityRationalCompleteProjectiveOutcome
    (width (schedule ⟨i.val, lt_trans i.isLt j.isLt⟩))
    N ξ ζ false false

/--
The state vector representing DSV density rational heterogeneous stopped common prefix failure.
-/
def dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector
    {S N d L : ℕ} (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L) :
    EuclideanSpace ℂ
      (Fin j.val →
        (DSVUniformDensityThresholdLocalIndex N d ×
         DSVUniformDensityThresholdLocalIndex N d)) :=
  finiteTensorVector
    (dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureCopy
      width schedule ξ ζ j)

theorem
    dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureCopy_eq_actual
    {S N d L : ℕ} (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L) (i : Fin j.val) :
    dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureCopy
        (N := N) width schedule ξ ζ j i =
      dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome
        width schedule ξ ζ j
        ⟨i.val, by omega⟩ := by
  symm
  exact
    dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome_before
      width schedule ξ ζ j ⟨i.val, by omega⟩ i.isLt

theorem
    dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector_apply
    {S N d L : ℕ} (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L)
    (q : Fin j.val →
      (DSVUniformDensityThresholdLocalIndex N d ×
       DSVUniformDensityThresholdLocalIndex N d)) :
    dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector
        width schedule ξ ζ j q =
      ∏ i : Fin j.val,
        dSVDensityRationalHeterogeneousActualCommonStopScheduledOutcome
          width schedule ξ ζ j
          ⟨i.val, by omega⟩ (q i) := by
  change
    (∏ i : Fin j.val,
      dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureCopy
        width schedule ξ ζ j i (q i)) = _
  apply Finset.prod_congr rfl
  intro i _
  rw [dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureCopy_eq_actual]

theorem
    dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector_norm_sq
    {S N d L : ℕ} (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (j : Fin L) :
    ‖dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector
        (N := N) width schedule ξ ζ j‖ ^ 2 =
      dSVDensityRationalHeterogeneousPhysicalSurvival
        N width schedule ξ ζ j.val := by
  rw [dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector,
    finiteTensorVector_norm_sq]
  unfold dSVDensityRationalHeterogeneousPhysicalSurvival
    dSVHeterogeneousRealPrefix
  calc
    (∏ i : Fin j.val,
      ‖dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureCopy
        width schedule ξ ζ j i‖ ^ 2) =
        ∏ i : Fin j.val,
          dSVDensityRationalHeterogeneousPhysicalStageContinue
            N width schedule ξ ζ i.val := by
      apply Finset.prod_congr rfl
      intro i _
      simp only [dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureCopy,
        dSVDensityRationalHeterogeneousPhysicalStageContinue,
        dSVDensityRationalHeterogeneousPhysicalStageOutcome, lt_trans i.isLt j.isLt, ↓reduceDIte]
    _ = _ :=
      Fin.prod_univ_eq_prod_range
        (dSVDensityRationalHeterogeneousPhysicalStageContinue
          N width schedule ξ ζ) j.val

/--
The DSV density rational heterogeneous stopped common prefix hazard construction used in the
quantum parallel-repetition argument.
-/
def dSVDensityRationalHeterogeneousStoppedCommonPrefixHazard
    {d N B S L : ℕ} (Q n : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin B → Option ℕ →
      Matrix.unitaryGroup (Fin (N * n)) ℂ) : ℝ :=
  ∑ j : Fin L,
    ‖dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector
          (N := N) width schedule ξ ζ j‖ ^ 2 *
      dSVDensityRationalHeterogeneousCommonStopGaugeStageError
        Q (width (schedule j)) n ξ ζ A C

theorem
    dSVDensityRationalHeterogeneousStoppedCommonPrefixHazard_eq_gaugeError
    {d N B S L : ℕ} (Q n : ℕ)
    (width : Fin S → ℝ) (schedule : Fin L → Fin S)
    (ξ ζ : BipartiteUnitVector d)
    (A C : Fin B → Option ℕ →
      Matrix.unitaryGroup (Fin (N * n)) ℂ) :
    dSVDensityRationalHeterogeneousStoppedCommonPrefixHazard
        Q n width schedule ξ ζ A C =
      dSVDensityRationalHeterogeneousStoppedCommonStopGaugeError
        Q n width schedule ξ ζ A C := by
  unfold dSVDensityRationalHeterogeneousStoppedCommonPrefixHazard
    dSVDensityRationalHeterogeneousStoppedCommonStopGaugeError
  simp_rw [
    dSVDensityRationalHeterogeneousStoppedCommonPrefixFailureVector_norm_sq]

theorem
    exists_proofDSVDensityRationalHeterogeneousStoppedCommonPrefixHazardBound
    {d N B : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (phases : 0 < B) {Q : ℕ} (fine : 0 < Q)
    (ε : ℝ) (precision : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧
      ∃ A C : Fin B → Option ℕ →
          Matrix.unitaryGroup (Fin (N * n)) ℂ,
        ∀ {S L : ℕ}
          (width : Fin S → ℝ) (schedule : Fin L → Fin S)
          (ξ ζ : BipartiteUnitVector d),
          dSVDensityRationalHeterogeneousStoppedCommonPrefixHazard
              Q n width schedule ξ ζ A C ≤
            (10 + 8 * ((Q : ℝ) / (B : ℝ))) *
                dSVDensityRationalHeterogeneousActualAsynchronousFlagMass
                  N width schedule ξ ζ +
              (4 * ε ^ 2 +
                16 * (Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1) +
                8 / (B : ℝ)) := by
  obtain ⟨n, harmonic, A, C, bound⟩ :=
    exists_proofDSVDensityRationalHeterogeneousStoppedCommonStopGaugeErrorBound
      grid dimension phases fine ε precision
  refine ⟨n, harmonic, A, C, ?_⟩
  intro S L width schedule ξ ζ
  rw [dSVDensityRationalHeterogeneousStoppedCommonPrefixHazard_eq_gaugeError,
    dSVDensityRationalHeterogeneousActualAsynchronousFlagMass_eq_stoppedAsynchronousMass
      grid dimension width schedule ξ ζ]
  exact bound width schedule ξ ζ

end

section

theorem unconditionalPublicBucket_exp_sub_one_le
    {u : ℝ} (nonnegative : 0 ≤ u) (bounded : u ≤ 1) :
    Real.exp u - 1 ≤ (Real.exp 1 - 1) * u := by
  have chord := convexOn_exp.2
    (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    (sub_nonneg.mpr bounded) nonnegative
    (show (1 - u) + u = (1 : ℝ) by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, mul_one,
    Real.exp_zero] at chord
  linarith

private def unconditionalPublicBucketLoss
    (B Q : ℕ) (asynchronous precision : ℝ) : ℝ :=
  (10 + 8 * ((Q : ℝ) / (B : ℝ))) * asynchronous +
    (4 * precision ^ 2 +
      16 * (Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1) +
      8 / (B : ℝ))

theorem exists_proofUnconditionalPublicBucketBalance
    (t : ℝ) (positive : 0 < t) (bounded : t ≤ 1) :
    ∃ B Q : ℕ, 0 < B ∧ 0 < Q ∧
      (1 / (B : ℝ) ≤ t / 2) ∧
      ((Q : ℝ) / (B : ℝ) ≤ 3 / t) ∧
      (((B : ℝ) + 1) / (Q : ℝ) ≤ t) ∧
      (Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1 ≤
        (Real.exp 1 - 1) * t) ∧
      ∀ asynchronous precision : ℝ, 0 ≤ asynchronous →
        unconditionalPublicBucketLoss B Q asynchronous precision ≤
          (34 / t) * asynchronous + 4 * precision ^ 2 +
            (16 * (Real.exp 1 - 1) + 4) * t := by
  let B : ℕ := ⌈(2 : ℝ) / t⌉₊
  let Q : ℕ := B ^ 2
  have B_positive : 0 < B := by
    dsimp [B]
    exact Nat.ceil_pos.mpr (div_pos (by norm_num) positive)
  have B_real_positive : 0 < (B : ℝ) := by
    exact_mod_cast B_positive
  have Q_positive : 0 < Q := pow_pos B_positive 2
  have Q_real_positive : 0 < (Q : ℝ) := by
    exact_mod_cast Q_positive
  have lower : 2 / t ≤ (B : ℝ) := by
    exact Nat.le_ceil ((2 : ℝ) / t)
  have product_lower : (2 : ℝ) ≤ (B : ℝ) * t :=
    (div_le_iff₀ positive).mp lower
  have inverse_bound : 1 / (B : ℝ) ≤ t / 2 := by
    apply (div_le_iff₀ B_real_positive).mpr
    linarith
  have ceiling_upper : (B : ℝ) < 2 / t + 1 := by
    exact Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 2 / t)
  have product_upper : (B : ℝ) * t < 2 + t := by
    calc
      (B : ℝ) * t < (2 / t + 1) * t :=
        mul_lt_mul_of_pos_right ceiling_upper positive
      _ = 2 + t := by field_simp
  have B_upper : (B : ℝ) ≤ 3 / t := by
    apply (le_div_iff₀ positive).mpr
    linarith
  have ratio_eq : (Q : ℝ) / (B : ℝ) = (B : ℝ) := by
    dsimp [Q]
    push_cast
    field_simp
  have ratio_bound : (Q : ℝ) / (B : ℝ) ≤ 3 / t :=
    ratio_eq.trans_le B_upper
  have B_at_least_one : (1 : ℝ) ≤ (B : ℝ) := by
    exact_mod_cast B_positive
  have width_bound : ((B : ℝ) + 1) / (Q : ℝ) ≤ t := by
    apply (div_le_iff₀ Q_real_positive).mpr
    have multiply :=
      mul_le_mul_of_nonneg_right product_lower B_real_positive.le
    have Q_real : (Q : ℝ) = (B : ℝ) ^ 2 := by
      simp only [Nat.cast_pow, Q]
    rw [Q_real]
    linarith
  have width_nonnegative :
      0 ≤ ((B : ℝ) + 1) / (Q : ℝ) := by positivity
  have exponential_bound :
      Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1 ≤
        (Real.exp 1 - 1) * t := by
    calc
      Real.exp (((B : ℝ) + 1) / (Q : ℝ)) - 1 ≤
          (Real.exp 1 - 1) * (((B : ℝ) + 1) / (Q : ℝ)) :=
        unconditionalPublicBucket_exp_sub_one_le
          width_nonnegative (width_bound.trans bounded)
      _ ≤ (Real.exp 1 - 1) * t := by
        have coefficient : 0 ≤ Real.exp 1 - 1 := by
          linarith [Real.add_one_le_exp (1 : ℝ)]
        exact mul_le_mul_of_nonneg_left width_bound coefficient
  refine ⟨B, Q, B_positive, Q_positive, inverse_bound,
    ratio_bound, width_bound, exponential_bound, ?_⟩
  intro asynchronous precision asynchronous_nonnegative
  have reciprocal : 8 / (B : ℝ) ≤ 4 * t := by
    have scale := mul_le_mul_of_nonneg_left inverse_bound
      (by norm_num : (0 : ℝ) ≤ 8)
    calc
      8 / (B : ℝ) = 8 * (1 / (B : ℝ)) := by ring
      _ ≤ 8 * (t / 2) := scale
      _ = 4 * t := by ring
  have ratio_cost :
      (10 + 8 * ((Q : ℝ) / (B : ℝ))) * asynchronous ≤
        (34 / t) * asynchronous := by
    apply mul_le_mul_of_nonneg_right _ asynchronous_nonnegative
    have t_inverse : (1 : ℝ) ≤ 1 / t := by
      apply (le_div_iff₀ positive).mpr
      simpa only [one_mul] using bounded
    have ratio_scaled :=
      mul_le_mul_of_nonneg_left ratio_bound
        (by norm_num : (0 : ℝ) ≤ 8)
    have ten_scaled :=
      mul_le_mul_of_nonneg_left t_inverse
        (by norm_num : (0 : ℝ) ≤ 10)
    have ten_piece : (10 : ℝ) ≤ 10 / t := by
      calc
        (10 : ℝ) = 10 * 1 := by ring
        _ ≤ 10 * (1 / t) := ten_scaled
        _ = 10 / t := by ring
    have ratio_piece :
        8 * ((Q : ℝ) / (B : ℝ)) ≤ 24 / t := by
      calc
        8 * ((Q : ℝ) / (B : ℝ)) ≤ 8 * (3 / t) := ratio_scaled
        _ = 24 / t := by ring
    calc
      10 + 8 * ((Q : ℝ) / (B : ℝ)) ≤
          10 / t + 24 / t := add_le_add ten_piece ratio_piece
      _ = 34 / t := by ring
  have exponential_scaled :=
    mul_le_mul_of_nonneg_left exponential_bound
      (by norm_num : (0 : ℝ) ≤ 16)
  unfold unconditionalPublicBucketLoss
  linarith

theorem exists_proofUnconditionalStoppedCommonPrefixBalancedHazard
    {d N : ℕ} (grid : 0 < N) (dimension : 0 < d)
    (t : ℝ) (positive : 0 < t) (bounded : t ≤ 1)
    (precision : ℝ) (precision_positive : 0 < precision) :
    ∃ B Q n : ℕ, 0 < B ∧ 0 < Q ∧ 0 < n ∧
      ∃ A C : Fin B → Option ℕ →
          Matrix.unitaryGroup (Fin (N * n)) ℂ,
        ∀ {S L : ℕ}
          (width : Fin S → ℝ) (schedule : Fin L → Fin S)
          (ξ ζ : BipartiteUnitVector d),
          dSVDensityRationalHeterogeneousStoppedCommonPrefixHazard
              Q n width schedule ξ ζ A C ≤
            (34 / t) *
                dSVDensityRationalHeterogeneousActualAsynchronousFlagMass
                  N width schedule ξ ζ +
              4 * precision ^ 2 +
                (16 * (Real.exp 1 - 1) + 4) * t := by
  obtain ⟨B, Q, phases, fine, _, _, _, _, balance⟩ :=
    exists_proofUnconditionalPublicBucketBalance t positive bounded
  obtain ⟨n, harmonic, A, C, source⟩ :=
    exists_proofDSVDensityRationalHeterogeneousStoppedCommonPrefixHazardBound
      grid dimension phases fine precision precision_positive
  refine ⟨B, Q, n, phases, fine, harmonic, A, C, ?_⟩
  intro S L width schedule ξ ζ
  have actual := source width schedule ξ ζ
  have asynchronous_nonnegative :
      0 ≤ dSVDensityRationalHeterogeneousActualAsynchronousFlagMass
        N width schedule ξ ζ := by
    exact
      dSVDensityRationalHeterogeneousActualAsynchronousFlagMass_nonneg
        N width schedule ξ ζ
  exact actual.trans
    (balance
      (dSVDensityRationalHeterogeneousActualAsynchronousFlagMass
        N width schedule ξ ζ)
      precision asynchronous_nonnegative)

/--
The unconditional prefactor bucket coefficient construction used in the quantum parallel-
repetition argument.
-/
def unconditionalPrefactorBucketCoefficient : ℝ :=
  16 * (Real.exp 1 - 1) + 4

theorem unconditionalPrefactorBucketCoefficient_nonneg :
    0 ≤ unconditionalPrefactorBucketCoefficient := by
  have exponential := Real.add_one_le_exp (1 : ℝ)
  unfold unconditionalPrefactorBucketCoefficient
  linarith

theorem unconditionalPrefactor_fourthRoot_sq
    {a : ℝ} (nonnegative : 0 ≤ a) :
    (a ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt a := by
  calc
    (a ^ (1 / 4 : ℝ)) ^ 2 = a ^ ((1 / 4 : ℝ) * 2) :=
      (Real.rpow_mul_natCast nonnegative (1 / 4 : ℝ) 2).symm
    _ = a ^ (1 / 2 : ℝ) := by norm_num
    _ = Real.sqrt a := (Real.sqrt_eq_rpow a).symm

theorem unconditionalPrefactor_sixtyFour_fourthRoot_le :
    (64 : ℝ) ^ (1 / 4 : ℝ) ≤ 4 := by
  have monotone := Real.rpow_le_rpow
    (by norm_num : (0 : ℝ) ≤ 64)
    (by norm_num : (64 : ℝ) ≤ 256)
    (by norm_num : (0 : ℝ) ≤ (1 / 4 : ℝ))
  have fourth :
      (256 : ℝ) ^ (1 / 4 : ℝ) = 4 := by
    norm_num
  exact monotone.trans_eq fourth

theorem unconditionalPrefactor_fourthRoot_async_le
    {eta alpha : ℝ}
    (eta_nonnegative : 0 ≤ eta)
    (alpha_nonnegative : 0 ≤ alpha) :
    (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ)) ^ (1 / 4 : ℝ) ≤
      4 * eta ^ (1 / 8 : ℝ) + alpha ^ (1 / 12 : ℝ) := by
  have asynchronous_nonnegative : 0 ≤ (64 : ℝ) * Real.sqrt eta := by
    positivity
  have precision_nonnegative : 0 ≤ alpha ^ (1 / 3 : ℝ) :=
    Real.rpow_nonneg alpha_nonnegative _
  have split := Real.rpow_add_le_add_rpow
    asynchronous_nonnegative precision_nonnegative
    (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) ≤ 1)
  have eta_identity :
      (Real.sqrt eta) ^ (1 / 4 : ℝ) = eta ^ (1 / 8 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul eta_nonnegative]
    norm_num
  have alpha_identity :
      (alpha ^ (1 / 3 : ℝ)) ^ (1 / 4 : ℝ) =
        alpha ^ (1 / 12 : ℝ) := by
    rw [← Real.rpow_mul alpha_nonnegative]
    norm_num
  have numerical :=
    unconditionalPrefactor_sixtyFour_fourthRoot_le
  calc
    (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ)) ^ (1 / 4 : ℝ)
        ≤ (64 * Real.sqrt eta) ^ (1 / 4 : ℝ) +
          (alpha ^ (1 / 3 : ℝ)) ^ (1 / 4 : ℝ) := split
    _ = (64 : ℝ) ^ (1 / 4 : ℝ) * eta ^ (1 / 8 : ℝ) +
          alpha ^ (1 / 12 : ℝ) := by
          rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 64)
            (Real.sqrt_nonneg eta), eta_identity, alpha_identity]
    _ ≤ 4 * eta ^ (1 / 8 : ℝ) + alpha ^ (1 / 12 : ℝ) := by
          gcongr

theorem unconditionalPrefactor_fourthRoot_async_le_twelfth
    {eta alpha : ℝ}
    (eta_nonnegative : 0 ≤ eta)
    (eta_bounded : eta ≤ 1)
    (alpha_nonnegative : 0 ≤ alpha) :
    (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ)) ^ (1 / 4 : ℝ) ≤
      4 * eta ^ (1 / 12 : ℝ) + alpha ^ (1 / 12 : ℝ) := by
  have root_compare : eta ^ (1 / 8 : ℝ) ≤ eta ^ (1 / 12 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge'
      eta_nonnegative eta_bounded
      (by norm_num : (0 : ℝ) ≤ 1 / 12)
      (by norm_num : (1 / 12 : ℝ) ≤ 1 / 8)
  calc
    (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ)) ^ (1 / 4 : ℝ)
        ≤ 4 * eta ^ (1 / 8 : ℝ) + alpha ^ (1 / 12 : ℝ) :=
          unconditionalPrefactor_fourthRoot_async_le
            eta_nonnegative alpha_nonnegative
    _ ≤ 4 * eta ^ (1 / 12 : ℝ) + alpha ^ (1 / 12 : ℝ) := by
          gcongr

theorem unconditionalPrefactor_balancedHazard_sqrt_le
    {a rho : ℝ}
    (positive : 0 < a)
    (rho_nonnegative : 0 ≤ rho) :
    Real.sqrt
      ((34 / Real.sqrt a) * a + 4 * rho ^ 2 +
        unconditionalPrefactorBucketCoefficient * Real.sqrt a) ≤
      Real.sqrt (34 + unconditionalPrefactorBucketCoefficient) *
          a ^ (1 / 4 : ℝ) + 2 * rho := by
  have root_positive : 0 < Real.sqrt a := Real.sqrt_pos.2 positive
  have root_square : (Real.sqrt a) ^ 2 = a :=
    Real.sq_sqrt positive.le
  have coefficient_nonnegative :=
    unconditionalPrefactorBucketCoefficient_nonneg
  have coefficient_square :
      (Real.sqrt
        (34 + unconditionalPrefactorBucketCoefficient)) ^ 2 =
        34 + unconditionalPrefactorBucketCoefficient :=
    Real.sq_sqrt (by linarith)
  have fourth_square :=
    unconditionalPrefactor_fourthRoot_sq positive.le
  have product_square :
      (Real.sqrt (34 + unconditionalPrefactorBucketCoefficient) *
        a ^ (1 / 4 : ℝ)) ^ 2 =
        (34 + unconditionalPrefactorBucketCoefficient) *
          Real.sqrt a := by
    calc
      (Real.sqrt (34 + unconditionalPrefactorBucketCoefficient) *
        a ^ (1 / 4 : ℝ)) ^ 2 =
          (Real.sqrt (34 +
            unconditionalPrefactorBucketCoefficient)) ^ 2 *
            (a ^ (1 / 4 : ℝ)) ^ 2 := by ring
      _ = (34 + unconditionalPrefactorBucketCoefficient) *
          Real.sqrt a := by rw [coefficient_square, fourth_square]
  have quotient : (34 / Real.sqrt a) * a = 34 * Real.sqrt a := by
    field_simp [ne_of_gt root_positive]
    linarith [root_square]
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · rw [quotient]
    have cross_nonnegative :
        0 ≤ (Real.sqrt
          (34 + unconditionalPrefactorBucketCoefficient) *
          a ^ (1 / 4 : ℝ)) * rho :=
      mul_nonneg
        (mul_nonneg (Real.sqrt_nonneg _)
          (Real.rpow_nonneg positive.le _))
        rho_nonnegative
    linarith [product_square]

theorem unconditionalPrefactor_smallHazard_twelfthRoot_le
    {eta alpha : ℝ}
    (eta_nonnegative : 0 ≤ eta)
    (alpha_positive : 0 < alpha)
    (small : 64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ) ≤ 1) :
    Real.sqrt
      ((34 / Real.sqrt
          (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ))) *
          (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ)) +
        4 * (alpha ^ (1 / 12 : ℝ)) ^ 2 +
        unconditionalPrefactorBucketCoefficient *
          Real.sqrt
            (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ))) ≤
      (4 * Real.sqrt
          (34 + unconditionalPrefactorBucketCoefficient) + 2) *
        (eta ^ (1 / 12 : ℝ) + alpha ^ (1 / 12 : ℝ)) := by
  let a : ℝ := 64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ)
  let rho : ℝ := alpha ^ (1 / 12 : ℝ)
  have alpha_third_positive : 0 < alpha ^ (1 / 3 : ℝ) :=
    Real.rpow_pos_of_pos alpha_positive _
  have a_positive : 0 < a := by
    dsimp [a]
    have := Real.sqrt_nonneg eta
    linarith
  have eta_root_square : (Real.sqrt eta) ^ 2 = eta :=
    Real.sq_sqrt eta_nonnegative
  have eta_bounded : eta ≤ 1 := by
    have eta_root_bounded : Real.sqrt eta ≤ 1 := by
      linarith [Real.sqrt_nonneg eta, alpha_third_positive]
    nlinarith [Real.sqrt_nonneg eta]
  have rho_nonnegative : 0 ≤ rho := by
    dsimp [rho]
    exact Real.rpow_nonneg alpha_positive.le _
  have eta_twelfth_nonnegative : 0 ≤ eta ^ (1 / 12 : ℝ) :=
    Real.rpow_nonneg eta_nonnegative _
  have quarter :=
    unconditionalPrefactor_fourthRoot_async_le_twelfth
      eta_nonnegative eta_bounded alpha_positive.le
  have balanced :=
    unconditionalPrefactor_balancedHazard_sqrt_le
      a_positive rho_nonnegative
  have coefficient_root_nonnegative :
      0 ≤ Real.sqrt
        (34 + unconditionalPrefactorBucketCoefficient) :=
    Real.sqrt_nonneg _
  change
    Real.sqrt
      ((34 / Real.sqrt a) * a + 4 * rho ^ 2 +
        unconditionalPrefactorBucketCoefficient * Real.sqrt a) ≤
      (4 * Real.sqrt
          (34 + unconditionalPrefactorBucketCoefficient) + 2) *
        (eta ^ (1 / 12 : ℝ) + rho)
  change a ^ (1 / 4 : ℝ) ≤
    4 * eta ^ (1 / 12 : ℝ) + rho at quarter
  linarith [mul_nonneg coefficient_root_nonnegative
    (sub_nonneg.mpr quarter),
    mul_nonneg coefficient_root_nonnegative rho_nonnegative,
    mul_nonneg (show 0 ≤ (2 : ℝ) by norm_num)
      eta_twelfth_nonnegative]

theorem unconditionalPrefactor_largeVerifier_twelfthRoot_le
    {eta alpha : ℝ}
    (eta_nonnegative : 0 ≤ eta)
    (alpha_positive : 0 < alpha)
    (alpha_bounded : alpha ≤ 1)
    (large : 1 < 64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ)) :
    (2 : ℝ) ≤
      128 * (eta ^ (1 / 12 : ℝ) + alpha ^ (1 / 12 : ℝ)) := by
  have eta_root_nonnegative : 0 ≤ eta ^ (1 / 12 : ℝ) :=
    Real.rpow_nonneg eta_nonnegative _
  have alpha_root_nonnegative : 0 ≤ alpha ^ (1 / 12 : ℝ) :=
    Real.rpow_nonneg alpha_positive.le _
  by_cases eta_bounded : eta ≤ 1
  · have eta_root_compare :
        Real.sqrt eta ≤ eta ^ (1 / 12 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_ge'
        eta_nonnegative eta_bounded
        (by norm_num : (0 : ℝ) ≤ 1 / 12)
        (by norm_num : (1 / 12 : ℝ) ≤ 1 / 2)
    have alpha_root_compare :
        alpha ^ (1 / 3 : ℝ) ≤ alpha ^ (1 / 12 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge'
        alpha_positive.le alpha_bounded
        (by norm_num : (0 : ℝ) ≤ 1 / 12)
        (by norm_num : (1 / 12 : ℝ) ≤ 1 / 3)
    linarith
  · have eta_large : 1 ≤ eta := (lt_of_not_ge eta_bounded).le
    have eta_root_large : 1 ≤ eta ^ (1 / 12 : ℝ) :=
      Real.one_le_rpow eta_large (by norm_num : (0 : ℝ) ≤ 1 / 12)
    linarith

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

theorem unconditionalExactSourceScalarClipping
    (d : ℕ) (dimension : 0 < d)
    (alpha : ℝ) (alpha_positive : 0 < alpha)
    (alpha_bounded : alpha ≤ 1) :
    ∃ (w : ℝ) (N : ℕ),
      1 ≤ w ∧ 0 < N ∧
      2 * (w + 1) * ((d : ℝ) / N) ≤ alpha ^ (1 / 3 : ℝ) ∧
      (1 / w + (d : ℝ) * w / (N : ℝ) ≤
        3 * alpha ^ (1 / 3 : ℝ) / 2) ∧
      (∀ ξ : BipartiteUnitVector d,
        ‖ξ.val - dSVDensityRationalCanonicalAcceptedTarget
            w N ξ‖ ^ 2 ≤ 3 * alpha ^ (1 / 3 : ℝ) / 2) ∧
      (∀ ξ ζ : BipartiteUnitVector d,
        dSVDensityRationalLeftProjectiveThresholdAtomMismatch
            w N ξ ζ /
          dSVDensityRationalLeftProjectiveDiagonalMass w N ξ ≤
            8 * Real.sqrt 2 * ‖ξ.val - ζ.val‖ +
              alpha ^ (1 / 3 : ℝ)) := by
  have precision : 0 < alpha ^ (1 / 3 : ℝ) :=
    Real.rpow_pos_of_pos alpha_positive _
  have small : alpha ^ (1 / 3 : ℝ) ≤ 1 :=
    Real.rpow_le_one alpha_positive.le alpha_bounded (by norm_num)
  obtain ⟨w, N, width, grid, fine, rounding, _diagonal, mismatch⟩ :=
    dSVDensityRationalLargeWidth_exists_sourceUniformParameters
      d dimension (alpha ^ (1 / 3 : ℝ)) precision small
  have scalar :
      1 / w + (d : ℝ) * w / (N : ℝ) ≤
        3 * alpha ^ (1 / 3 : ℝ) / 2 := by
    calc
      1 / w + (d : ℝ) * w / (N : ℝ) =
          1 / w + w * ((d : ℝ) / N) := by ring
      _ ≤ 3 * alpha ^ (1 / 3 : ℝ) / 2 := rounding
  refine ⟨w, N, width, grid, fine, scalar, ?_, mismatch⟩
  intro ξ
  exact
    (dSVDensityRationalCanonicalAcceptedTarget_distance_sq_le
      (by linarith) grid ξ).trans scalar

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

private def exactLocalQuestionHistoryEquiv
    {n : ℕ} (D : Finset (Fin n)) :
    (LocalQuestionContext X Y D ×
      ExactHistoryFlag X Y A B D) ≃
      ExactLocallySampleableTuple X Y A B D where
  toFun t := (t.1.1, t.1.2.1, t.1.2.2, t.2)
  invFun t := ((t.1, t.2.1, t.2.2.1), t.2.2.2)
  left_inv t := by
    rcases t with ⟨⟨i, x, y⟩, r⟩
    rfl
  right_inv t := by
    rcases t with ⟨i, x, y, r⟩
    rfl

/--
The exact locally sampleable ja rounded construction used in the quantum parallel-repetition
argument.
-/
def exactLocallySampleableJARounded
    (G : Game X Y A B) (n : ℕ) (D : Finset (Fin n))
    (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (t : ExactLocallySampleableTuple X Y A B D) : ℝ :=
  G.questionWeight t.2.1 t.2.2.1 *
    ((numerator (.inl (t.1, t.2.1)) t.2.2.2 : ℝ) /
      denominator) /
    (Fintype.card (SourceRemainingCoordinate D) : ℝ)

/--
The exact locally sampleable jb rounded construction used in the quantum parallel-repetition
argument.
-/
def exactLocallySampleableJBRounded
    (G : Game X Y A B) (n : ℕ) (D : Finset (Fin n))
    (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (t : ExactLocallySampleableTuple X Y A B D) : ℝ :=
  G.questionWeight t.2.1 t.2.2.1 *
    ((numerator (.inr (t.1, t.2.2.1)) t.2.2.2 : ℝ) /
      denominator) /
    (Fintype.card (SourceRemainingCoordinate D) : ℝ)

theorem exactLocallySampleableJA_weightedConditional
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D) :
    (exactLocallySampleableJA G n S D base ∘
      exactLocalQuestionHistoryEquiv D) =
      weightedConditionalJoint
        (localQuestionWeight G n D)
        (fun c r => exactAliceLocalConditional D base
          (exactLocallySampleableLaw G n S D)
          c.1 c.2.1 r) := by
  funext t
  rcases t with ⟨⟨i, x, y⟩, r⟩
  change
    G.questionWeight x y *
      exactAliceLocalConditional D base
        (exactLocallySampleableLaw G n S D) i x r /
        (Fintype.card (SourceRemainingCoordinate D) : ℝ) =
      (G.questionWeight x y /
        (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        exactAliceLocalConditional D base
          (exactLocallySampleableLaw G n S D) i x r
  ring

theorem exactLocallySampleableJB_weightedConditional
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D) :
    (exactLocallySampleableJB G n S D base ∘
      exactLocalQuestionHistoryEquiv D) =
      weightedConditionalJoint
        (localQuestionWeight G n D)
        (fun c r => exactBobLocalConditional D base
          (exactLocallySampleableLaw G n S D)
          c.1 c.2.2 r) := by
  funext t
  rcases t with ⟨⟨i, x, y⟩, r⟩
  change
    G.questionWeight x y *
      exactBobLocalConditional D base
        (exactLocallySampleableLaw G n S D) i y r /
        (Fintype.card (SourceRemainingCoordinate D) : ℝ) =
      (G.questionWeight x y /
        (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        exactBobLocalConditional D base
          (exactLocallySampleableLaw G n S D) i y r
  ring

theorem exactLocallySampleableJARounded_weightedConditional
    (G : Game X Y A B) (n : ℕ) (D : Finset (Fin n))
    (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ) :
    (exactLocallySampleableJARounded
      G n D denominator numerator ∘
        exactLocalQuestionHistoryEquiv D) =
      weightedConditionalJoint
        (localQuestionWeight G n D)
        (fun c r =>
          (numerator (.inl (c.1, c.2.1)) r : ℝ) / denominator) := by
  funext t
  rcases t with ⟨⟨i, x, y⟩, r⟩
  change
    G.questionWeight x y *
      ((numerator (.inl (i, x)) r : ℝ) / denominator) /
        (Fintype.card (SourceRemainingCoordinate D) : ℝ) =
      (G.questionWeight x y /
        (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        ((numerator (.inl (i, x)) r : ℝ) / denominator)
  ring

theorem exactLocallySampleableJBRounded_weightedConditional
    (G : Game X Y A B) (n : ℕ) (D : Finset (Fin n))
    (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ) :
    (exactLocallySampleableJBRounded
      G n D denominator numerator ∘
        exactLocalQuestionHistoryEquiv D) =
      weightedConditionalJoint
        (localQuestionWeight G n D)
        (fun c r =>
          (numerator (.inr (c.1, c.2.2)) r : ℝ) / denominator) := by
  funext t
  rcases t with ⟨⟨i, x, y⟩, r⟩
  change
    G.questionWeight x y *
      ((numerator (.inr (i, y)) r : ℝ) / denominator) /
        (Fintype.card (SourceRemainingCoordinate D) : ℝ) =
      (G.questionWeight x y /
        (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        ((numerator (.inr (i, y)) r : ℝ) / denominator)
  ring

theorem exactLocallySampleableJA_rounded_totalVariation_le
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (base : ExactHistoryFlag X Y A B D)
    (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    {gamma : ℝ}
    (approximation : ∀ k, finiteTotalVariation
      (exactLocalConditionalFamily D base
        (exactLocallySampleableLaw G n S D) k)
      (fun r => (numerator k r : ℝ) / denominator) < gamma) :
    finiteTotalVariation
        (exactLocallySampleableJA G n S D base)
        (exactLocallySampleableJARounded
          G n D denominator numerator) ≤ gamma := by
  calc
    finiteTotalVariation
        (exactLocallySampleableJA G n S D base)
        (exactLocallySampleableJARounded
          G n D denominator numerator) =
      finiteTotalVariation
        (exactLocallySampleableJA G n S D base ∘
          exactLocalQuestionHistoryEquiv D)
        (exactLocallySampleableJARounded
          G n D denominator numerator ∘
          exactLocalQuestionHistoryEquiv D) :=
      (finiteTotalVariation_equiv
        (exactLocalQuestionHistoryEquiv D)
        (exactLocallySampleableJA G n S D base)
        (exactLocallySampleableJARounded
          G n D denominator numerator)).symm
    _ = ∑ c : LocalQuestionContext X Y D,
        localQuestionWeight G n D c *
          finiteTotalVariation
            (fun r => exactAliceLocalConditional D base
              (exactLocallySampleableLaw G n S D)
              c.1 c.2.1 r)
            (fun r =>
              (numerator (.inl (c.1, c.2.1)) r : ℝ) /
                denominator) := by
      rw [exactLocallySampleableJA_weightedConditional,
        exactLocallySampleableJARounded_weightedConditional,
        weightedConditionalJoint_totalVariation
          (localQuestionWeight G n D)
          (localQuestionWeight_nonneg G n D)]
    _ ≤ ∑ c : LocalQuestionContext X Y D,
        localQuestionWeight G n D c * gamma := by
      apply Finset.sum_le_sum
      intro c _
      apply mul_le_mul_of_nonneg_left _
        (localQuestionWeight_nonneg G n D c)
      exact (approximation (.inl (c.1, c.2.1))).le
    _ = gamma := by
      rw [← Finset.sum_mul,
        localQuestionWeight_sum G n D remaining]
      ring

theorem exactLocallySampleableJB_rounded_totalVariation_le
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (base : ExactHistoryFlag X Y A B D)
    (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    {gamma : ℝ}
    (approximation : ∀ k, finiteTotalVariation
      (exactLocalConditionalFamily D base
        (exactLocallySampleableLaw G n S D) k)
      (fun r => (numerator k r : ℝ) / denominator) < gamma) :
    finiteTotalVariation
        (exactLocallySampleableJB G n S D base)
        (exactLocallySampleableJBRounded
          G n D denominator numerator) ≤ gamma := by
  calc
    finiteTotalVariation
        (exactLocallySampleableJB G n S D base)
        (exactLocallySampleableJBRounded
          G n D denominator numerator) =
      finiteTotalVariation
        (exactLocallySampleableJB G n S D base ∘
          exactLocalQuestionHistoryEquiv D)
        (exactLocallySampleableJBRounded
          G n D denominator numerator ∘
          exactLocalQuestionHistoryEquiv D) :=
      (finiteTotalVariation_equiv
        (exactLocalQuestionHistoryEquiv D)
        (exactLocallySampleableJB G n S D base)
        (exactLocallySampleableJBRounded
          G n D denominator numerator)).symm
    _ = ∑ c : LocalQuestionContext X Y D,
        localQuestionWeight G n D c *
          finiteTotalVariation
            (fun r => exactBobLocalConditional D base
              (exactLocallySampleableLaw G n S D)
              c.1 c.2.2 r)
            (fun r =>
              (numerator (.inr (c.1, c.2.2)) r : ℝ) /
                denominator) := by
      rw [exactLocallySampleableJB_weightedConditional,
        exactLocallySampleableJBRounded_weightedConditional,
        weightedConditionalJoint_totalVariation
          (localQuestionWeight G n D)
          (localQuestionWeight_nonneg G n D)]
    _ ≤ ∑ c : LocalQuestionContext X Y D,
        localQuestionWeight G n D c * gamma := by
      apply Finset.sum_le_sum
      intro c _
      apply mul_le_mul_of_nonneg_left _
        (localQuestionWeight_nonneg G n D c)
      exact (approximation (.inr (c.1, c.2.2))).le
    _ = gamma := by
      rw [← Finset.sum_mul,
        localQuestionWeight_sum G n D remaining]
      ring

theorem exactLocallySampleableRounded_pair_totalVariation
    (G : Game X Y A B) (n : ℕ) (D : Finset (Fin n))
    (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ) :
    finiteTotalVariation
        (exactLocallySampleableJARounded
          G n D denominator numerator)
        (exactLocallySampleableJBRounded
          G n D denominator numerator) =
      ∑ c : LocalQuestionContext X Y D,
        localQuestionWeight G n D c *
          finiteTotalVariation
            (fun r =>
              (numerator (.inl (c.1, c.2.1)) r : ℝ) / denominator)
            (fun r =>
              (numerator (.inr (c.1, c.2.2)) r : ℝ) / denominator) := by
  calc
    finiteTotalVariation
        (exactLocallySampleableJARounded
          G n D denominator numerator)
        (exactLocallySampleableJBRounded
          G n D denominator numerator) =
      finiteTotalVariation
        (exactLocallySampleableJARounded
          G n D denominator numerator ∘
          exactLocalQuestionHistoryEquiv D)
        (exactLocallySampleableJBRounded
          G n D denominator numerator ∘
          exactLocalQuestionHistoryEquiv D) :=
      (finiteTotalVariation_equiv
        (exactLocalQuestionHistoryEquiv D)
        (exactLocallySampleableJARounded
          G n D denominator numerator)
        (exactLocallySampleableJBRounded
          G n D denominator numerator)).symm
    _ = _ := by
      rw [exactLocallySampleableJARounded_weightedConditional,
        exactLocallySampleableJBRounded_weightedConditional,
        weightedConditionalJoint_totalVariation
          (localQuestionWeight G n D)
          (localQuestionWeight_nonneg G n D)]

/--
The exact locally sampleable permutation mismatch construction used in the quantum parallel-
repetition argument.
-/
def exactLocallySampleablePermutationMismatch
    (G : Game X Y A B) (n : ℕ) (D : Finset (Fin n))
    (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ k,
      (rationalMarked denominator (numerator k)).Nonempty) : ℝ :=
  ∑ c : LocalQuestionContext X Y D,
    localQuestionWeight G n D c *
      uniformPermutationProbability
        (fun permutation :
          Equiv.Perm
            (ExactHistoryFlag X Y A B D × Fin denominator) =>
          rationalPermutationOutput denominator
              (numerator (.inl (c.1, c.2.1)))
              (nonempty (.inl (c.1, c.2.1))) permutation ≠
            rationalPermutationOutput denominator
              (numerator (.inr (c.1, c.2.2)))
              (nonempty (.inr (c.1, c.2.2))) permutation)

theorem exactLocallySampleablePermutationMismatch_le_two_tv
    (G : Game X Y A B) (n : ℕ) (D : Finset (Fin n))
    (denominator : ℕ) (positive : 0 < denominator)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (normalized : ∀ k, (∑ r, numerator k r) = denominator)
    (nonempty : ∀ k,
      (rationalMarked denominator (numerator k)).Nonempty) :
    exactLocallySampleablePermutationMismatch
        G n D denominator numerator nonempty ≤
      2 * finiteTotalVariation
        (exactLocallySampleableJARounded
          G n D denominator numerator)
        (exactLocallySampleableJBRounded
          G n D denominator numerator) := by
  unfold exactLocallySampleablePermutationMismatch
  calc
    (∑ c : LocalQuestionContext X Y D,
      localQuestionWeight G n D c *
        uniformPermutationProbability
          (fun permutation :
            Equiv.Perm
              (ExactHistoryFlag X Y A B D × Fin denominator) =>
            rationalPermutationOutput denominator
                (numerator (.inl (c.1, c.2.1)))
                (nonempty (.inl (c.1, c.2.1))) permutation ≠
              rationalPermutationOutput denominator
                (numerator (.inr (c.1, c.2.2)))
                (nonempty (.inr (c.1, c.2.2))) permutation)) ≤
      ∑ c : LocalQuestionContext X Y D,
        localQuestionWeight G n D c *
          (2 * finiteTotalVariation
            (fun r =>
              (numerator (.inl (c.1, c.2.1)) r : ℝ) / denominator)
            (fun r =>
              (numerator (.inr (c.1, c.2.2)) r : ℝ) / denominator)) := by
      apply Finset.sum_le_sum
      intro c _
      apply mul_le_mul_of_nonneg_left _
        (localQuestionWeight_nonneg G n D c)
      exact rationalPermutationOutput_disagreement_le_two_mul_finiteTotalVariation
        denominator positive
        (numerator (.inl (c.1, c.2.1)))
        (numerator (.inr (c.1, c.2.2)))
        (normalized (.inl (c.1, c.2.1)))
        (normalized (.inr (c.1, c.2.2)))
        (nonempty (.inl (c.1, c.2.1)))
        (nonempty (.inr (c.1, c.2.2)))
    _ = 2 *
      (∑ c : LocalQuestionContext X Y D,
        localQuestionWeight G n D c *
          finiteTotalVariation
            (fun r =>
              (numerator (.inl (c.1, c.2.1)) r : ℝ) / denominator)
            (fun r =>
              (numerator (.inr (c.1, c.2.2)) r : ℝ) / denominator)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ = 2 * finiteTotalVariation
        (exactLocallySampleableJARounded
          G n D denominator numerator)
        (exactLocallySampleableJBRounded
          G n D denominator numerator) := by
      rw [exactLocallySampleableRounded_pair_totalVariation]

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The type used to represent exact source shared flag in the exact sampling construction. -/
abbrev ExactSourceSharedFlag
    (X Y A B : Type)
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {n : ℕ} (D : Finset (Fin n)) (denominator : ℕ) :=
  SourceRemainingCoordinate D ×
    Equiv.Perm
      (ExactHistoryFlag X Y A B D × Fin denominator)

/-- The probability weight for exact source shared flag. -/
def exactSourceSharedFlagWeight
    {n : ℕ} (D : Finset (Fin n)) (denominator : ℕ)
    (_ : ExactSourceSharedFlag X Y A B D denominator) : ℝ :=
  (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
    (1 / (Fintype.card
      (Equiv.Perm
        (ExactHistoryFlag X Y A B D × Fin denominator)) : ℝ))

theorem exactSourceSharedFlagWeight_nonneg
    {n : ℕ} (D : Finset (Fin n)) (denominator : ℕ)
    (j : ExactSourceSharedFlag X Y A B D denominator) :
    0 ≤ exactSourceSharedFlagWeight D denominator j := by
  unfold exactSourceSharedFlagWeight
  positivity

theorem exactSourceSharedFlagWeight_sum
    {n : ℕ} (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (denominator : ℕ) :
    (∑ j : ExactSourceSharedFlag X Y A B D denominator,
      exactSourceSharedFlagWeight D denominator j) = 1 := by
  classical
  have coordinate_nonzero :
      (Fintype.card (SourceRemainingCoordinate D) : ℝ) ≠ 0 := by
    exact_mod_cast
      (Nat.ne_of_gt (exactRemainingCoordinate_card_pos
        D remaining))
  have permutation_nonzero :
      (Fintype.card
        (Equiv.Perm
          (ExactHistoryFlag X Y A B D × Fin denominator)) : ℝ)
        ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt
      (Fintype.card_pos_iff.mpr
        ⟨Equiv.refl
          (ExactHistoryFlag X Y A B D × Fin denominator)⟩))
  rw [Fintype.sum_prod_type]
  simp only [exactSourceSharedFlagWeight,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- The transcript representation for exact source alice permutation. -/
def exactSourceAlicePermutationHistory
    {n : ℕ} (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ k,
      (rationalMarked denominator (numerator k)).Nonempty)
    (j : ExactSourceSharedFlag X Y A B D denominator)
    (x : X) : ExactHistoryFlag X Y A B D :=
  rationalPermutationOutput denominator
    (numerator (.inl (j.1, x)))
    (nonempty (.inl (j.1, x))) j.2

/-- The transcript representation for exact source bob permutation. -/
def exactSourceBobPermutationHistory
    {n : ℕ} (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ k,
      (rationalMarked denominator (numerator k)).Nonempty)
    (j : ExactSourceSharedFlag X Y A B D denominator)
    (y : Y) : ExactHistoryFlag X Y A B D :=
  rationalPermutationOutput denominator
    (numerator (.inr (j.1, y)))
    (nonempty (.inr (j.1, y))) j.2

/--
The exact source permutation matched construction used in the quantum parallel-repetition
argument.
-/
def exactSourcePermutationMatched
    {n : ℕ} (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ k,
      (rationalMarked denominator (numerator k)).Nonempty)
    (ω : ExactSourceSharedFlag X Y A B D denominator ×
      (X × Y)) : Bool := by
  classical
  exact decide
    (exactSourceAlicePermutationHistory
      D denominator numerator nonempty ω.1 ω.2.1 =
      exactSourceBobPermutationHistory
        D denominator numerator nonempty ω.1 ω.2.2)

/-- The Boolean shared-permutation test reflects equality of the two decoded histories. -/
theorem exactSourcePermutationMatched_eq_true_iff
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ k,
      (rationalMarked denominator (numerator k)).Nonempty)
    (ω : ExactSourceSharedFlag X Y A B D denominator × (X × Y)) :
    exactSourcePermutationMatched D denominator numerator nonempty ω = true ↔
      exactSourceAlicePermutationHistory
          D denominator numerator nonempty ω.1 ω.2.1 =
        exactSourceBobPermutationHistory
          D denominator numerator nonempty ω.1 ω.2.2 := by
  classical
  simp only [exactSourcePermutationMatched, decide_eq_true_eq]

theorem exactUniformPermutationProbability_eq_indicator_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (event : Equiv.Perm ι → Prop) :
    uniformPermutationProbability event =
      (∑ permutation : Equiv.Perm ι,
        if event permutation then (1 : ℝ) else 0) /
        (Fintype.card (Equiv.Perm ι) : ℝ) := by
  classical
  unfold uniformPermutationProbability
  congr 1
  exact (Finset.sum_boole (R := ℝ) event
    (Finset.univ : Finset (Equiv.Perm ι))).symm

theorem exactSourceSharedFlag_mismatch_eq
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ k,
      (rationalMarked denominator (numerator k)).Nonempty) :
    (∑ ω :
      ExactSourceSharedFlag X Y A B D denominator × (X × Y),
      flaggedQuestionWeight G
        (exactSourceSharedFlagWeight D denominator) ω *
        if exactSourcePermutationMatched
            D denominator numerator nonempty ω then 0 else 1) =
      exactLocallySampleablePermutationMismatch
        G n D denominator numerator nonempty := by
  classical
  have point
      (i : SourceRemainingCoordinate D) (x : X) (y : Y) :
      (∑ permutation :
        Equiv.Perm
          (ExactHistoryFlag X Y A B D × Fin denominator),
        ((1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
          (1 / (Fintype.card
            (Equiv.Perm
              (ExactHistoryFlag X Y A B D ×
                Fin denominator)) : ℝ))) *
          G.questionWeight x y *
          if rationalPermutationOutput denominator
              (numerator (.inl (i, x)))
              (nonempty (.inl (i, x))) permutation =
            rationalPermutationOutput denominator
              (numerator (.inr (i, y)))
              (nonempty (.inr (i, y))) permutation
          then 0 else 1) =
        (G.questionWeight x y /
          (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
          uniformPermutationProbability
            (fun permutation :
              Equiv.Perm
                (ExactHistoryFlag X Y A B D ×
                  Fin denominator) =>
              rationalPermutationOutput denominator
                  (numerator (.inl (i, x)))
                  (nonempty (.inl (i, x))) permutation ≠
                rationalPermutationOutput denominator
                  (numerator (.inr (i, y)))
                  (nonempty (.inr (i, y))) permutation) := by
    have probability :=
      exactUniformPermutationProbability_eq_indicator_sum
        (ι := ExactHistoryFlag X Y A B D × Fin denominator)
        (fun permutation :
          Equiv.Perm
            (ExactHistoryFlag X Y A B D × Fin denominator) =>
          rationalPermutationOutput denominator
              (numerator (.inl (i, x)))
              (nonempty (.inl (i, x))) permutation ≠
            rationalPermutationOutput denominator
              (numerator (.inr (i, y)))
              (nonempty (.inr (i, y))) permutation)
    rw [probability, Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro permutation _
    by_cases matched :
      rationalPermutationOutput denominator
          (numerator (.inl (i, x)))
          (nonempty (.inl (i, x))) permutation =
        rationalPermutationOutput denominator
          (numerator (.inr (i, y)))
          (nonempty (.inr (i, y))) permutation
    · simp only [Fintype.card_coe, one_div, matched, ↓reduceIte, mul_zero, ne_eq,
        not_true_eq_false, zero_div]
    · simp only [Fintype.card_coe, one_div, matched, ↓reduceIte, mul_one, ne_eq,
        not_false_eq_true]
      ring
  unfold exactLocallySampleablePermutationMismatch
  simp only [flaggedQuestionWeight,
    exactSourceSharedFlagWeight,
    localQuestionWeight,
    exactSourcePermutationMatched_eq_true_iff,
    exactSourceAlicePermutationHistory,
    exactSourceBobPermutationHistory,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  exact point i x y

theorem exactSourceSharedFlag_mismatch_le
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ k,
      (rationalMarked denominator (numerator k)).Nonempty)
    {lam : ℝ}
    (mismatch :
      exactLocallySampleablePermutationMismatch
        G n D denominator numerator nonempty ≤ 4 * lam) :
    (∑ ω :
      ExactSourceSharedFlag X Y A B D denominator × (X × Y),
      flaggedQuestionWeight G
        (exactSourceSharedFlagWeight D denominator) ω *
        if exactSourcePermutationMatched
            D denominator numerator nonempty ω then 0 else 1) ≤
      4 * lam := by
  rw [exactSourceSharedFlag_mismatch_eq
    G n D denominator numerator nonempty]
  exact mismatch

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem reweightedSeed_reverse_source_prefix_information_budget
    {K V : Type*} [Fintype K] [Fintype V]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (seedLaw : Finset (SourceRemainingCoordinate D) →
      FiniteEventLaw K)
    (Ω : Finset (SourceRemainingCoordinate D) → Type*)
    [∀ side, Fintype (Ω side)]
    (projection : ∀ side : Finset (SourceRemainingCoordinate D),
      K × ExactOutcome X Y A B n →
        Ω side × (Fin side.card → V))
    (default : V) :
    (∑ side : Finset (SourceRemainingCoordinate D),
      reversePartitionWeight side *
        ((∑ k : Fin side.card,
          reweightedSeedPrefixEntropyIncrement
            (seedLaw side) G n S D
            (projection side) default k) /
          (side.card : ℝ))) ≤
      2 * (postselectionLogCost G n S D +
        answerLogCost (A := A) (B := B) D) /
        ((Finset.univ \ D).card : ℝ) := by
  have nonnegative_cost :
      0 ≤ postselectionLogCost G n S D +
        answerLogCost (A := A) (B := B) D := by
    have hempty := reweightedSeed_source_equation_twenty_six
      (seedLaw ∅) G n S D positive (projection ∅) default
    let : IsEmpty (Fin (∅ : Finset (SourceRemainingCoordinate D)).card) :=
      ⟨fun k => Nat.not_lt_zero k.val
        (by simpa only [Finset.card_empty] using k.isLt)⟩
    simpa only [Fintype.sum_empty] using hempty
  exact exactRemainingReverse_relativeEntropy_budget
    D remaining
    (fun side k => reweightedSeedPrefixEntropyIncrement
      (seedLaw side) G n S D (projection side) default k)
    nonnegative_cost
    (fun side => reweightedSeed_source_equation_twenty_six
      (seedLaw side) G n S D positive (projection side) default)

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

private def finiteIndependentProductWeight
    {ι V : Type*} [Fintype ι]
    (q : ι → V → ℝ) (x : ι → V) : ℝ :=
  ∏ i : ι, q i (x i)

private def finiteCoordinateMarginal
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : (ι → V) → ℝ) (i : ι) : V → ℝ := by
  classical
  exact groupedMass (fun x : ι → V => x i) p

theorem finiteIndependentProductWeight_nonneg
    {ι V : Type*} [Fintype ι]
    (q : ι → V → ℝ) (hq : ∀ i v, 0 ≤ q i v)
    (x : ι → V) :
    0 ≤ finiteIndependentProductWeight q x := by
  classical
  unfold finiteIndependentProductWeight
  exact Finset.prod_nonneg fun i _ => hq i (x i)

theorem finiteIndependentProductWeight_sum
    {ι V : Type*} [Fintype ι] [Fintype V]
    (q : ι → V → ℝ)
    (hq : ∀ i, (∑ v : V, q i v) = 1) :
    (∑ x : ι → V, finiteIndependentProductWeight q x) = 1 := by
  classical
  unfold finiteIndependentProductWeight
  calc
    (∑ x : ι → V, ∏ i : ι, q i (x i)) =
        ∏ i : ι, ∑ v : V, q i v :=
      (Fintype.prod_sum (fun i : ι => fun v : V => q i v)).symm
    _ = 1 := by simp only [hq, prod_const_one]

theorem finiteCoordinateMarginal_nonneg
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : (ι → V) → ℝ) (hp : ∀ x, 0 ≤ p x)
    (i : ι) (v : V) :
    0 ≤ finiteCoordinateMarginal p i v := by
  classical
  unfold finiteCoordinateMarginal
  exact groupedMass_nonneg (fun x : ι → V => x i) p hp v

theorem finiteCoordinateMarginal_sum
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : (ι → V) → ℝ) (i : ι) :
    (∑ v : V, finiteCoordinateMarginal p i v) =
      ∑ x : ι → V, p x := by
  classical
  unfold finiteCoordinateMarginal
  exact groupedMass_sum (fun x : ι → V => x i) p

theorem finiteJoint_le_coordinateMarginal
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : (ι → V) → ℝ) (hp : ∀ x, 0 ≤ p x)
    (x : ι → V) (i : ι) :
    p x ≤ finiteCoordinateMarginal p i (x i) := by
  classical
  unfold finiteCoordinateMarginal groupedMass
  exact Finset.single_le_sum
    (fun a _ => hp a)
    (by simp only [mem_filter, mem_univ, and_self])

theorem finiteCoordinateMarginal_absolute_continuity
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : (ι → V) → ℝ) (q : ι → V → ℝ)
    (hac : ∀ x, finiteIndependentProductWeight q x = 0 → p x = 0)
    (i : ι) (v : V) :
    q i v = 0 → finiteCoordinateMarginal p i v = 0 := by
  classical
  intro hz
  unfold finiteCoordinateMarginal groupedMass
  apply Finset.sum_eq_zero
  intro x hx
  have hxi : x i = v := (Finset.mem_filter.mp hx).2
  apply hac x
  unfold finiteIndependentProductWeight
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simpa only [hxi] using hz

theorem finiteJoint_absolute_continuous_product_marginals
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : (ι → V) → ℝ) (hp : ∀ x, 0 ≤ p x)
    (x : ι → V) :
    finiteIndependentProductWeight
        (finiteCoordinateMarginal p) x = 0 → p x = 0 := by
  classical
  intro hz
  by_contra hpx
  have hpositive : 0 < p x :=
    lt_of_le_of_ne (hp x) (Ne.symm hpx)
  have hmarginal (i : ι) :
      0 < finiteCoordinateMarginal p i (x i) :=
    lt_of_lt_of_le hpositive
      (finiteJoint_le_coordinateMarginal p hp x i)
  have hproduct :
      0 < finiteIndependentProductWeight
        (finiteCoordinateMarginal p) x := by
    unfold finiteIndependentProductWeight
    exact Finset.prod_pos fun i _ => hmarginal i
  exact hproduct.ne' hz

theorem finiteCoordinateMarginal_sum_mul
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : (ι → V) → ℝ) (i : ι) (f : V → ℝ) :
    (∑ x : ι → V, p x * f (x i)) =
      ∑ v : V, finiteCoordinateMarginal p i v * f v := by
  classical
  calc
    (∑ x : ι → V, p x * f (x i)) =
        ∑ v : V,
          groupedMass (fun x : ι → V => x i)
            (fun x => p x * f (x i)) v := by
      symm
      exact groupedMass_sum
        (fun x : ι → V => x i)
        (fun x => p x * f (x i))
    _ = ∑ v : V, finiteCoordinateMarginal p i v * f v := by
      apply Finset.sum_congr rfl
      intro v _
      unfold finiteCoordinateMarginal groupedMass
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      have hxi : x i = v := (Finset.mem_filter.mp hx).2
      simp only [hxi]

theorem finiteProductMarginal_relativeEntropy_le
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : (ι → V) → ℝ) (q : ι → V → ℝ)
    (hp : ∀ x, 0 ≤ p x)
    (hp_normalized : (∑ x : ι → V, p x) = 1)
    (hq : ∀ i v, 0 ≤ q i v)
    (hq_normalized : ∀ i, (∑ v : V, q i v) = 1)
    (absolute_continuity :
      ∀ x, finiteIndependentProductWeight q x = 0 → p x = 0) :
    (∑ i : ι,
      finiteRelativeEntropy (finiteCoordinateMarginal p i) (q i)) ≤
      finiteRelativeEntropy p (finiteIndependentProductWeight q) := by
  classical
  let marginal : ι → V → ℝ := finiteCoordinateMarginal p
  have hm_nonnegative (i : ι) (v : V) : 0 ≤ marginal i v :=
    finiteCoordinateMarginal_nonneg p hp i v
  have hm_normalized (i : ι) : (∑ v : V, marginal i v) = 1 := by
    change (∑ v : V, finiteCoordinateMarginal p i v) = 1
    rw [finiteCoordinateMarginal_sum, hp_normalized]
  have hm_absolute (x : ι → V) :
      finiteIndependentProductWeight marginal x = 0 → p x = 0 :=
    finiteJoint_absolute_continuous_product_marginals p hp x
  have hq_absolute (i : ι) (v : V) :
      q i v = 0 → marginal i v = 0 :=
    finiteCoordinateMarginal_absolute_continuity
      p q absolute_continuity i v
  have hpoint (x : ι → V) :
      p x * Real.log
        (p x / finiteIndependentProductWeight q x) =
        p x * Real.log
            (p x / finiteIndependentProductWeight marginal x) +
          ∑ i : ι,
            p x * Real.log (marginal i (x i) / q i (x i)) := by
    by_cases hpx : p x = 0
    · simp only [hpx, zero_div, Real.log_zero, mul_zero, zero_mul, sum_const_zero, add_zero]
    · have hp_positive : 0 < p x :=
        lt_of_le_of_ne (hp x) (Ne.symm hpx)
      have hq_product :
          finiteIndependentProductWeight q x ≠ 0 := by
        intro hz
        exact hpx (absolute_continuity x hz)
      have hm_product :
          finiteIndependentProductWeight marginal x ≠ 0 := by
        intro hz
        exact hpx (hm_absolute x hz)
      have hq_factor (i : ι) : q i (x i) ≠ 0 := by
        intro hz
        apply hq_product
        unfold finiteIndependentProductWeight
        exact Finset.prod_eq_zero (Finset.mem_univ i) hz
      have hm_factor (i : ι) : marginal i (x i) ≠ 0 := by
        have hm_positive : 0 < marginal i (x i) :=
          lt_of_lt_of_le hp_positive
            (finiteJoint_le_coordinateMarginal p hp x i)
        exact hm_positive.ne'
      have hlogq :
          Real.log (finiteIndependentProductWeight q x) =
            ∑ i : ι, Real.log (q i (x i)) := by
        unfold finiteIndependentProductWeight
        exact Real.log_prod (fun i _ => hq_factor i)
      have hlogm :
          Real.log (finiteIndependentProductWeight marginal x) =
            ∑ i : ι, Real.log (marginal i (x i)) := by
        unfold finiteIndependentProductWeight
        exact Real.log_prod (fun i _ => hm_factor i)
      rw [Real.log_div hpx hq_product,
        Real.log_div hpx hm_product, hlogq, hlogm]
      simp_rw [Real.log_div (hm_factor _) (hq_factor _)]
      rw [← Finset.mul_sum, Finset.sum_sub_distrib]
      ring
  have hidentity :
      finiteRelativeEntropy p (finiteIndependentProductWeight q) =
        finiteRelativeEntropy p
            (finiteIndependentProductWeight marginal) +
          ∑ i : ι, finiteRelativeEntropy (marginal i) (q i) := by
    rw [finiteRelativeEntropy_eq_log_sum_of_absolute_continuity
      p (finiteIndependentProductWeight q)
      (finiteIndependentProductWeight_nonneg q hq)
      absolute_continuity hp_normalized
      (finiteIndependentProductWeight_sum q hq_normalized)]
    rw [finiteRelativeEntropy_eq_log_sum_of_absolute_continuity
      p (finiteIndependentProductWeight marginal)
      (finiteIndependentProductWeight_nonneg marginal hm_nonnegative)
      hm_absolute hp_normalized
      (finiteIndependentProductWeight_sum marginal hm_normalized)]
    simp_rw [finiteRelativeEntropy_eq_log_sum_of_absolute_continuity
      (marginal _) (q _) (hq _) (hq_absolute _)
      (hm_normalized _) (hq_normalized _)]
    calc
      (∑ x : ι → V, p x *
          Real.log (p x / finiteIndependentProductWeight q x)) =
        ∑ x : ι → V,
          (p x * Real.log
            (p x / finiteIndependentProductWeight marginal x) +
            ∑ i : ι,
              p x * Real.log (marginal i (x i) / q i (x i))) := by
          apply Finset.sum_congr rfl
          intro x _
          exact hpoint x
      _ = (∑ x : ι → V, p x *
            Real.log
              (p x / finiteIndependentProductWeight marginal x)) +
          ∑ i : ι,
            ∑ x : ι → V,
              p x * Real.log (marginal i (x i) / q i (x i)) := by
          rw [Finset.sum_add_distrib, Finset.sum_comm]
      _ = (∑ x : ι → V, p x *
            Real.log
              (p x / finiteIndependentProductWeight marginal x)) +
          ∑ i : ι,
            ∑ v : V,
              marginal i v * Real.log (marginal i v / q i v) := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          exact finiteCoordinateMarginal_sum_mul
            p i (fun v => Real.log (marginal i v / q i v))
  rw [hidentity]
  have hnonnegative :
      0 ≤ finiteRelativeEntropy p
        (finiteIndependentProductWeight marginal) :=
    finiteRelativeEntropy_nonneg p
      (finiteIndependentProductWeight marginal)
      hp (finiteIndependentProductWeight_nonneg
        marginal hm_nonnegative)
  change (∑ i : ι, finiteRelativeEntropy (marginal i) (q i)) ≤ _
  linarith

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem exactIndependentCoordinateQuestion_marginal
    {M Ω V : Type*} [Fintype M] [DecidableEq M]
    [Fintype Ω]
    (outcome : Ω → ℝ) (question : Ω → M → V)
    (i : M) (v : V) :
    groupedMass
        (fun t : ExactForwardSeed M × Ω =>
          (t.1.coordinate, question t.2 t.1.coordinate))
        (fun t : ExactForwardSeed M × Ω =>
          exactSeedWeight t.1 * outcome t.2) (i, v) =
      (1 / (Fintype.card M : ℝ)) *
        groupedMass (fun ω : Ω => question ω i) outcome v := by
  classical
  let coordinateMass :=
    groupedMass (fun ω : Ω => question ω i) outcome v
  have hinner (seed : ExactForwardSeed M) :
      (∑ ω : Ω,
        if (seed.coordinate, question ω seed.coordinate) = (i, v)
        then exactSeedWeight seed * outcome ω
        else 0) =
      if seed.coordinate = i
      then exactSeedWeight seed * coordinateMass
      else 0 := by
    by_cases hc : seed.coordinate = i
    · subst i
      simp only [Prod.mk.injEq, true_and, ↓reduceIte]
      dsimp [coordinateMass]
      unfold groupedMass
      rw [Finset.sum_filter]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _
      split_ifs <;> simp_all
    · simp only [Prod.mk.injEq, hc, false_and, ↓reduceIte, sum_const_zero]
  unfold groupedMass
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp_rw [hinner]
  calc
    (∑ seed : ExactForwardSeed M,
      if seed.coordinate = i
      then exactSeedWeight seed * coordinateMass
      else 0) =
        (∑ seed : ExactForwardSeed M,
          if seed.coordinate = i
          then exactSeedWeight seed else 0) * coordinateMass := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro seed _
          split_ifs <;> simp
    _ = (1 / (Fintype.card M : ℝ)) * coordinateMass := by
      rw [exactSeedWeight_coordinate_marginal i]

theorem strategyAliceQuestionPrior_marginal
    (G : Game X Y A B) (S : Strategy G) (x : X) :
    groupedMass (fun ω : StrategyOutcome X Y A B => ω.1)
        (strategyEventLaw G S).weight x =
      G.marginalX x := by
  classical
  unfold groupedMass
  rw [Finset.sum_filter]
  simp only [Fintype.sum_prod_type]
  change
    (∑ x' : X, ∑ y : Y, ∑ a : A, ∑ b : B,
      if x' = x then
        G.questionWeight x' y * S.outcomeProbability x' y a b
      else 0) = G.marginalX x
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  unfold Game.marginalX
  apply Finset.sum_congr rfl
  intro y _
  simp_rw [← Finset.mul_sum]
  rw [S.outcomeProbability_normalized x y]
  ring

theorem strategyBobQuestionPrior_marginal
    (G : Game X Y A B) (S : Strategy G) (y : Y) :
    groupedMass (fun ω : StrategyOutcome X Y A B => ω.2.1)
        (strategyEventLaw G S).weight y =
      G.marginalY y := by
  classical
  unfold groupedMass
  rw [Finset.sum_filter]
  simp only [Fintype.sum_prod_type]
  change
    (∑ x : X, ∑ y' : Y, ∑ a : A, ∑ b : B,
      if y' = y then
        G.questionWeight x y' * S.outcomeProbability x y' a b
      else 0) = G.marginalY y
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  unfold Game.marginalY
  apply Finset.sum_congr rfl
  intro x _
  simp_rw [← Finset.mul_sum]
  rw [S.outcomeProbability_normalized x y]
  ring

theorem repeatedAliceQuestionPrior_product
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (xs : Fin n → X) :
    groupedMass
        (fun ω : ExactOutcome X Y A B n => ω.1)
        (strategyEventLaw (G.repeat n) S).weight xs =
      finiteIndependentProductWeight
        (fun _ : Fin n => G.marginalX) xs := by
  classical
  calc
    groupedMass
        (fun ω : ExactOutcome X Y A B n => ω.1)
        (strategyEventLaw (G.repeat n) S).weight xs =
      (G.repeat n).marginalX xs := by
        calc
          groupedMass
              (fun ω : ExactOutcome X Y A B n => ω.1)
              (strategyEventLaw (G.repeat n) S).weight xs =
            @groupedMass
              (ExactOutcome X Y A B n) inferInstance
              (Fin n → X)
              (fun a b => Classical.propDecidable (a = b))
              (fun ω : ExactOutcome X Y A B n => ω.1)
              (strategyEventLaw (G.repeat n) S).weight xs := by
                exact congrFun
                  (exactGroupedMass_decidableEq_irrel _ _
                    (fun ω : ExactOutcome X Y A B n => ω.1)
                    (strategyEventLaw (G.repeat n) S).weight) xs
          _ = (G.repeat n).marginalX xs :=
            strategyAliceQuestionPrior_marginal
              (G.repeat n) S xs
    _ = finiteIndependentProductWeight
        (fun _ : Fin n => G.marginalX) xs := by
      unfold Game.marginalX finiteIndependentProductWeight
      simp only [Game.repeat_questionWeight]
      exact (Fintype.prod_sum
        (fun i : Fin n => fun y : Y => G.questionWeight (xs i) y)).symm

theorem repeatedBobQuestionPrior_product
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (ys : Fin n → Y) :
    groupedMass
        (fun ω : ExactOutcome X Y A B n => ω.2.1)
        (strategyEventLaw (G.repeat n) S).weight ys =
      finiteIndependentProductWeight
        (fun _ : Fin n => G.marginalY) ys := by
  classical
  calc
    groupedMass
        (fun ω : ExactOutcome X Y A B n => ω.2.1)
        (strategyEventLaw (G.repeat n) S).weight ys =
      (G.repeat n).marginalY ys := by
        calc
          groupedMass
              (fun ω : ExactOutcome X Y A B n => ω.2.1)
              (strategyEventLaw (G.repeat n) S).weight ys =
            @groupedMass
              (ExactOutcome X Y A B n) inferInstance
              (Fin n → Y)
              (fun a b => Classical.propDecidable (a = b))
              (fun ω : ExactOutcome X Y A B n => ω.2.1)
              (strategyEventLaw (G.repeat n) S).weight ys := by
                exact congrFun
                  (exactGroupedMass_decidableEq_irrel _ _
                    (fun ω : ExactOutcome X Y A B n => ω.2.1)
                    (strategyEventLaw (G.repeat n) S).weight) ys
          _ = (G.repeat n).marginalY ys :=
            strategyBobQuestionPrior_marginal
              (G.repeat n) S ys
    _ = finiteIndependentProductWeight
        (fun _ : Fin n => G.marginalY) ys := by
      unfold Game.marginalY finiteIndependentProductWeight
      simp only [Game.repeat_questionWeight]
      exact (Fintype.prod_sum
        (fun i : Fin n => fun x : X => G.questionWeight x (ys i))).symm

private def repeatedAlicePostselectedQuestionLaw
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) : (Fin n → X) → ℝ := by
  classical
  exact groupedMass
    (fun ω : ExactOutcome X Y A B n => ω.1)
    (repeatedConditionedOutcomeLaw G n S D)

private def repeatedBobPostselectedQuestionLaw
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) : (Fin n → Y) → ℝ := by
  classical
  exact groupedMass
    (fun ω : ExactOutcome X Y A B n => ω.2.1)
    (repeatedConditionedOutcomeLaw G n S D)

theorem exactGroupedMass_equiv
    {Ω K V : Type*} [Fintype Ω] [Fintype K]
    (equiv : Ω ≃ K) (projection : Ω → V) (mass : Ω → ℝ)
    (v : V) :
    groupedMass (fun k : K => projection (equiv.symm k))
        (fun k : K => mass (equiv.symm k)) v =
      groupedMass projection mass v := by
  classical
  unfold groupedMass
  rw [Finset.sum_filter, Finset.sum_filter]
  exact equiv.symm.sum_comp
    (fun ω : Ω => if projection ω = v then mass ω else 0)

theorem exactAliceInformationPosterior_firstMarginal_pushforward
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (i : SourceRemainingCoordinate D) (x : X) :
    jointFirstMarginal
        (exactAliceInformationPosterior G n S D) (i, x) =
      groupedMass
        (fun t : ExactLocallySampleableTuple X Y A B D =>
          (t.1, t.2.1))
        (exactLocallySampleableLaw G n S D) (i, x) := by
  classical
  let equiv := exactAliceInformationEquiv
    (X := X) (Y := Y) (A := A) (B := B) D
  let projection :=
    fun t : ExactLocallySampleableTuple X Y A B D =>
      (t.1, t.2.1)
  let mass := exactLocallySampleableLaw G n S D
  have hfirst := congrFun
    (groupedMass_first
      (exactAliceInformationPosterior G n S D)) (i, x)
  have hreindex := exactGroupedMass_equiv
    equiv projection mass (i, x)
  have hprojection :
      (fun k :
        (SourceRemainingCoordinate D × X) ×
          (ExactHistoryFlag X Y A B D × Y) =>
        projection (equiv.symm k)) = Prod.fst := by
    funext k
    rcases k with ⟨⟨j, z⟩, r, w⟩
    rfl
  have hmass :
      (fun k :
        (SourceRemainingCoordinate D × X) ×
          (ExactHistoryFlag X Y A B D × Y) =>
        mass (equiv.symm k)) =
        exactAliceInformationPosterior G n S D := by
    funext k
    rfl
  rw [hprojection, hmass] at hreindex
  calc
    jointFirstMarginal
        (exactAliceInformationPosterior G n S D) (i, x) =
      groupedMass Prod.fst
        (exactAliceInformationPosterior G n S D) (i, x) := by
          exact hfirst.symm
    _ = groupedMass projection mass (i, x) := by
      have hchange :
          groupedMass Prod.fst
              (exactAliceInformationPosterior G n S D) (i, x) =
            @groupedMass
              ((SourceRemainingCoordinate D × X) ×
                (ExactHistoryFlag X Y A B D × Y))
              inferInstance (SourceRemainingCoordinate D × X)
              (fun a b => Classical.propDecidable (a = b))
              Prod.fst
              (exactAliceInformationPosterior G n S D) (i, x) := by
        exact congrFun
          (exactGroupedMass_decidableEq_irrel _ _ Prod.fst
            (exactAliceInformationPosterior G n S D)) (i, x)
      have hreindex' :
          @groupedMass
              ((SourceRemainingCoordinate D × X) ×
                (ExactHistoryFlag X Y A B D × Y))
              inferInstance (SourceRemainingCoordinate D × X)
              (fun a b => Classical.propDecidable (a = b))
              Prod.fst
              (exactAliceInformationPosterior G n S D) (i, x) =
            @groupedMass
              (ExactLocallySampleableTuple X Y A B D)
              inferInstance (SourceRemainingCoordinate D × X)
              (fun a b => Classical.propDecidable (a = b))
              projection mass (i, x) := by
        exact hreindex
      have hright :
          @groupedMass
              (ExactLocallySampleableTuple X Y A B D)
              inferInstance (SourceRemainingCoordinate D × X)
              (fun a b => Classical.propDecidable (a = b))
              projection mass (i, x) =
            groupedMass projection mass (i, x) := by
        exact congrFun
          (exactGroupedMass_decidableEq_irrel _ _
            projection mass) (i, x)
      exact hchange.trans (hreindex'.trans hright)

theorem exactBobInformationPosterior_firstMarginal_pushforward
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (i : SourceRemainingCoordinate D) (y : Y) :
    jointFirstMarginal
        (exactBobInformationPosterior G n S D) (i, y) =
      groupedMass
        (fun t : ExactLocallySampleableTuple X Y A B D =>
          (t.1, t.2.2.1))
        (exactLocallySampleableLaw G n S D) (i, y) := by
  classical
  let equiv := exactBobInformationEquiv
    (X := X) (Y := Y) (A := A) (B := B) D
  let projection :=
    fun t : ExactLocallySampleableTuple X Y A B D =>
      (t.1, t.2.2.1)
  let mass := exactLocallySampleableLaw G n S D
  have hfirst := congrFun
    (groupedMass_first
      (exactBobInformationPosterior G n S D)) (i, y)
  have hreindex := exactGroupedMass_equiv
    equiv projection mass (i, y)
  have hprojection :
      (fun k :
        (SourceRemainingCoordinate D × Y) ×
          (ExactHistoryFlag X Y A B D × X) =>
        projection (equiv.symm k)) = Prod.fst := by
    funext k
    rcases k with ⟨⟨j, z⟩, r, w⟩
    rfl
  have hmass :
      (fun k :
        (SourceRemainingCoordinate D × Y) ×
          (ExactHistoryFlag X Y A B D × X) =>
        mass (equiv.symm k)) =
        exactBobInformationPosterior G n S D := by
    funext k
    rfl
  rw [hprojection, hmass] at hreindex
  calc
    jointFirstMarginal
        (exactBobInformationPosterior G n S D) (i, y) =
      groupedMass Prod.fst
        (exactBobInformationPosterior G n S D) (i, y) := by
          exact hfirst.symm
    _ = groupedMass projection mass (i, y) := by
      have hchange :
          groupedMass Prod.fst
              (exactBobInformationPosterior G n S D) (i, y) =
            @groupedMass
              ((SourceRemainingCoordinate D × Y) ×
                (ExactHistoryFlag X Y A B D × X))
              inferInstance (SourceRemainingCoordinate D × Y)
              (fun a b => Classical.propDecidable (a = b))
              Prod.fst
              (exactBobInformationPosterior G n S D) (i, y) := by
        exact congrFun
          (exactGroupedMass_decidableEq_irrel _ _ Prod.fst
            (exactBobInformationPosterior G n S D)) (i, y)
      have hreindex' :
          @groupedMass
              ((SourceRemainingCoordinate D × Y) ×
                (ExactHistoryFlag X Y A B D × X))
              inferInstance (SourceRemainingCoordinate D × Y)
              (fun a b => Classical.propDecidable (a = b))
              Prod.fst
              (exactBobInformationPosterior G n S D) (i, y) =
            @groupedMass
              (ExactLocallySampleableTuple X Y A B D)
              inferInstance (SourceRemainingCoordinate D × Y)
              (fun a b => Classical.propDecidable (a = b))
              projection mass (i, y) := by
        exact hreindex
      have hright :
          @groupedMass
              (ExactLocallySampleableTuple X Y A B D)
              inferInstance (SourceRemainingCoordinate D × Y)
              (fun a b => Classical.propDecidable (a = b))
              projection mass (i, y) =
            groupedMass projection mass (i, y) := by
        exact congrFun
          (exactGroupedMass_decidableEq_irrel _ _
            projection mass) (i, y)
      exact hchange.trans (hreindex'.trans hright)

theorem exactAliceInformationPosterior_firstMarginal
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (i : SourceRemainingCoordinate D) (x : X) :
    jointFirstMarginal
        (exactAliceInformationPosterior G n S D) (i, x) =
      (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        groupedMass
          (fun ω : ExactOutcome X Y A B n => ω.1 i.val)
          (repeatedConditionedOutcomeLaw G n S D) x := by
  classical
  let code := exactLocallySampleableCode
    (X := X) (Y := Y) (A := A) (B := B) D
  let projection :=
    fun t : ExactLocallySampleableTuple X Y A B D =>
      (t.1, t.2.1)
  let joint := exactPostselectedJointLaw G n S D
  have hlaw :
      exactLocallySampleableLaw G n S D =
        groupedMass code joint := by
    unfold exactLocallySampleableLaw
      exactSourcePushforward
    exact exactGroupedMass_decidableEq_irrel _ _ _ _
  have hcomp := congrFun
    (groupedMass_comp code projection joint) (i, x)
  have hprojection :
      projection ∘ code =
        (fun q : ExactJointOutcome X Y A B D =>
          (q.1.coordinate, q.2.1 q.1.coordinate.val)) := by
    funext q
    rfl
  rw [hprojection] at hcomp
  calc
    jointFirstMarginal
        (exactAliceInformationPosterior G n S D) (i, x) =
      groupedMass projection
        (exactLocallySampleableLaw G n S D) (i, x) :=
      exactAliceInformationPosterior_firstMarginal_pushforward
        G n S D i x
    _ = groupedMass projection (groupedMass code joint) (i, x) := by
      rw [hlaw]
    _ = groupedMass
        (fun q : ExactJointOutcome X Y A B D =>
          (q.1.coordinate, q.2.1 q.1.coordinate.val)) joint (i, x) :=
      hcomp
    _ = (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        groupedMass
          (fun ω : ExactOutcome X Y A B n => ω.1 i.val)
          (repeatedConditionedOutcomeLaw G n S D) x := by
      exact exactIndependentCoordinateQuestion_marginal
        (repeatedConditionedOutcomeLaw G n S D)
        (fun ω : ExactOutcome X Y A B n =>
          fun j : SourceRemainingCoordinate D => ω.1 j.val) i x

theorem exactBobInformationPosterior_firstMarginal
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (i : SourceRemainingCoordinate D) (y : Y) :
    jointFirstMarginal
        (exactBobInformationPosterior G n S D) (i, y) =
      (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        groupedMass
          (fun ω : ExactOutcome X Y A B n => ω.2.1 i.val)
          (repeatedConditionedOutcomeLaw G n S D) y := by
  classical
  let code := exactLocallySampleableCode
    (X := X) (Y := Y) (A := A) (B := B) D
  let projection :=
    fun t : ExactLocallySampleableTuple X Y A B D =>
      (t.1, t.2.2.1)
  let joint := exactPostselectedJointLaw G n S D
  have hlaw :
      exactLocallySampleableLaw G n S D =
        groupedMass code joint := by
    unfold exactLocallySampleableLaw
      exactSourcePushforward
    exact exactGroupedMass_decidableEq_irrel _ _ _ _
  have hcomp := congrFun
    (groupedMass_comp code projection joint) (i, y)
  have hprojection :
      projection ∘ code =
        (fun q : ExactJointOutcome X Y A B D =>
          (q.1.coordinate, q.2.2.1 q.1.coordinate.val)) := by
    funext q
    rfl
  rw [hprojection] at hcomp
  calc
    jointFirstMarginal
        (exactBobInformationPosterior G n S D) (i, y) =
      groupedMass projection
        (exactLocallySampleableLaw G n S D) (i, y) :=
      exactBobInformationPosterior_firstMarginal_pushforward
        G n S D i y
    _ = groupedMass projection (groupedMass code joint) (i, y) := by
      rw [hlaw]
    _ = groupedMass
        (fun q : ExactJointOutcome X Y A B D =>
          (q.1.coordinate, q.2.2.1 q.1.coordinate.val)) joint (i, y) :=
      hcomp
    _ = (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        groupedMass
          (fun ω : ExactOutcome X Y A B n => ω.2.1 i.val)
          (repeatedConditionedOutcomeLaw G n S D) y := by
      exact exactIndependentCoordinateQuestion_marginal
        (repeatedConditionedOutcomeLaw G n S D)
        (fun ω : ExactOutcome X Y A B n =>
          fun j : SourceRemainingCoordinate D => ω.2.1 j.val) i y

theorem finiteProductMarginal_projection_relativeEntropy_le
    {Ω ι V : Type*} [Fintype Ω] [Fintype ι] [Fintype V]
    (posterior prior : Ω → ℝ) (projection : Ω → (ι → V))
    (q : ι → V → ℝ) (budget : ℝ)
    (posterior_nonnegative : ∀ ω, 0 ≤ posterior ω)
    (posterior_normalized : (∑ ω : Ω, posterior ω) = 1)
    (prior_nonnegative : ∀ ω, 0 ≤ prior ω)
    (absolute_continuity : ∀ ω, prior ω = 0 → posterior ω = 0)
    (coordinate_nonnegative : ∀ i v, 0 ≤ q i v)
    (coordinate_normalized : ∀ i, (∑ v : V, q i v) = 1)
    (actual_prior :
      groupedMass projection prior =
        finiteIndependentProductWeight q)
    (actual_budget : finiteRelativeEntropy posterior prior ≤ budget) :
    (∑ i : ι,
      finiteRelativeEntropy
        (finiteCoordinateMarginal
          (groupedMass projection posterior) i)
        (q i)) ≤ budget := by
  classical
  let projected := groupedMass projection posterior
  have hnonnegative (x : ι → V) : 0 ≤ projected x :=
    groupedMass_nonneg projection posterior
      posterior_nonnegative x
  have hnormalized : (∑ x : ι → V, projected x) = 1 := by
    dsimp [projected]
    rw [groupedMass_sum, posterior_normalized]
  have habsolute (x : ι → V) :
      finiteIndependentProductWeight q x = 0 → projected x = 0 := by
    intro hx
    have hprior : groupedMass projection prior x = 0 := by
      rw [actual_prior]
      exact hx
    exact groupedMass_absolute_continuity
      projection posterior prior prior_nonnegative
      absolute_continuity x hprior
  have htensor := finiteProductMarginal_relativeEntropy_le
    projected q hnonnegative hnormalized coordinate_nonnegative
    coordinate_normalized habsolute
  have hdpi := finite_relative_entropy_data_processing
    projection posterior prior posterior_nonnegative prior_nonnegative
    absolute_continuity
  rw [actual_prior] at hdpi
  exact htensor.trans (hdpi.trans actual_budget)

theorem repeatedAliceCoordinateInformation_sum_le
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D) :
    (∑ j : Fin n,
      finiteRelativeEntropy
        (finiteCoordinateMarginal
          (repeatedAlicePostselectedQuestionLaw G n S D) j)
        G.marginalX) ≤
      postselectionLogCost G n S D := by
  classical
  let posterior := repeatedConditionedOutcomeLaw G n S D
  let prior := (strategyEventLaw (G.repeat n) S).weight
  let projection :=
    fun ω : ExactOutcome X Y A B n => ω.1
  let q := fun _ : Fin n => G.marginalX
  have hposterior (ω : ExactOutcome X Y A B n) :
      0 ≤ posterior ω :=
    conditionedEventDistribution_nonneg
      (strategyEventLaw (G.repeat n) S)
      (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)
      positive ω
  have hnormalized :
      (∑ ω : ExactOutcome X Y A B n, posterior ω) = 1 :=
    conditionedEventDistribution_sum
      (strategyEventLaw (G.repeat n) S)
      (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)
      positive
  have hac (ω : ExactOutcome X Y A B n) :
      prior ω = 0 → posterior ω = 0 :=
    conditionedEventDistribution_absolute_continuity
      (strategyEventLaw (G.repeat n) S)
      (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D) ω
  have hprior :
      groupedMass projection prior =
        finiteIndependentProductWeight q := by
    funext xs
    exact repeatedAliceQuestionPrior_product G n S xs
  have hbudget :
      finiteRelativeEntropy posterior prior ≤
        postselectionLogCost G n S D := by
    exact le_of_eq
      (repeatedConditionedOutcomeLaw_relativeEntropy
        G n S D positive)
  have h := finiteProductMarginal_projection_relativeEntropy_le
    posterior prior projection q
    (postselectionLogCost G n S D)
    hposterior hnormalized
    (strategyEventLaw (G.repeat n) S).weight_nonneg hac
    (fun j x => G.marginalX_nonneg x)
    (fun j => G.marginalX_normalized)
    hprior hbudget
  have hprojected :
      groupedMass projection posterior =
        repeatedAlicePostselectedQuestionLaw G n S D := by
    unfold repeatedAlicePostselectedQuestionLaw
    exact exactGroupedMass_decidableEq_irrel _ _ _ _
  rw [hprojected] at h
  exact h

theorem repeatedBobCoordinateInformation_sum_le
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D) :
    (∑ j : Fin n,
      finiteRelativeEntropy
        (finiteCoordinateMarginal
          (repeatedBobPostselectedQuestionLaw G n S D) j)
        G.marginalY) ≤
      postselectionLogCost G n S D := by
  classical
  let posterior := repeatedConditionedOutcomeLaw G n S D
  let prior := (strategyEventLaw (G.repeat n) S).weight
  let projection :=
    fun ω : ExactOutcome X Y A B n => ω.2.1
  let q := fun _ : Fin n => G.marginalY
  have hposterior (ω : ExactOutcome X Y A B n) :
      0 ≤ posterior ω :=
    conditionedEventDistribution_nonneg
      (strategyEventLaw (G.repeat n) S)
      (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)
      positive ω
  have hnormalized :
      (∑ ω : ExactOutcome X Y A B n, posterior ω) = 1 :=
    conditionedEventDistribution_sum
      (strategyEventLaw (G.repeat n) S)
      (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)
      positive
  have hac (ω : ExactOutcome X Y A B n) :
      prior ω = 0 → posterior ω = 0 :=
    conditionedEventDistribution_absolute_continuity
      (strategyEventLaw (G.repeat n) S)
      (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D) ω
  have hprior :
      groupedMass projection prior =
        finiteIndependentProductWeight q := by
    funext ys
    exact repeatedBobQuestionPrior_product G n S ys
  have hbudget :
      finiteRelativeEntropy posterior prior ≤
        postselectionLogCost G n S D := by
    exact le_of_eq
      (repeatedConditionedOutcomeLaw_relativeEntropy
        G n S D positive)
  have h := finiteProductMarginal_projection_relativeEntropy_le
    posterior prior projection q
    (postselectionLogCost G n S D)
    hposterior hnormalized
    (strategyEventLaw (G.repeat n) S).weight_nonneg hac
    (fun j y => G.marginalY_nonneg y)
    (fun j => G.marginalY_normalized)
    hprior hbudget
  have hprojected :
      groupedMass projection posterior =
        repeatedBobPostselectedQuestionLaw G n S D := by
    unfold repeatedBobPostselectedQuestionLaw
    exact exactGroupedMass_decidableEq_irrel _ _ _ _
  rw [hprojected] at h
  exact h

theorem finiteCoordinateMarginal_groupedMass
    {Ω ι V : Type*} [Fintype Ω] [Fintype ι] [Fintype V]
    (projection : Ω → (ι → V)) (mass : Ω → ℝ)
    (i : ι) (v : V) :
    finiteCoordinateMarginal
        (groupedMass projection mass) i v =
      groupedMass (fun ω : Ω => projection ω i) mass v := by
  classical
  let eval : (ι → V) → V := fun x => x i
  have h := congrFun
    (groupedMass_comp projection eval mass) v
  unfold finiteCoordinateMarginal
  have hleft :
      groupedMass (fun x : ι → V => x i)
          (groupedMass projection mass) v =
        @groupedMass (ι → V) inferInstance V
          (fun a b => Classical.propDecidable (a = b))
          eval (groupedMass projection mass) v := by
    exact congrFun
      (exactGroupedMass_decidableEq_irrel _ _
        eval (groupedMass projection mass)) v
  have hright :
      @groupedMass Ω inferInstance V
          (fun a b => Classical.propDecidable (a = b))
          (eval ∘ projection) mass v =
        groupedMass (fun ω : Ω => projection ω i) mass v := by
    exact congrFun
      (exactGroupedMass_decidableEq_irrel _ _
        (fun ω : Ω => projection ω i) mass) v
  exact hleft.trans (h.trans hright)

theorem finiteUniformCoordinate_relativeEntropy
    {ι V : Type*} [Fintype ι] [Fintype V]
    (positive : 0 < Fintype.card ι)
    (posterior : ι → V → ℝ) (prior : V → ℝ) :
    finiteRelativeEntropy
        (fun t : ι × V =>
          (1 / (Fintype.card ι : ℝ)) * posterior t.1 t.2)
        (fun t : ι × V =>
          (1 / (Fintype.card ι : ℝ)) * prior t.2) =
      (1 / (Fintype.card ι : ℝ)) *
        ∑ i : ι, finiteRelativeEntropy (posterior i) prior := by
  classical
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt positive)
  have huniform : (1 / (Fintype.card ι : ℝ)) ≠ 0 :=
    one_div_ne_zero hcard
  unfold finiteRelativeEntropy
  rw [Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [mul_div_mul_left _ _ huniform]
  ring

theorem repeatedAlicePostselectedQuestionLaw_nonneg
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (xs : Fin n → X) :
    0 ≤ repeatedAlicePostselectedQuestionLaw G n S D xs := by
  classical
  unfold repeatedAlicePostselectedQuestionLaw
  apply groupedMass_nonneg
  intro ω
  exact conditionedEventDistribution_nonneg
    (strategyEventLaw (G.repeat n) S)
    (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)
    positive ω

theorem repeatedBobPostselectedQuestionLaw_nonneg
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (ys : Fin n → Y) :
    0 ≤ repeatedBobPostselectedQuestionLaw G n S D ys := by
  classical
  unfold repeatedBobPostselectedQuestionLaw
  apply groupedMass_nonneg
  intro ω
  exact conditionedEventDistribution_nonneg
    (strategyEventLaw (G.repeat n) S)
    (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)
    positive ω

theorem repeatedAlicePostselectedCoordinateMarginal
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (j : Fin n) (x : X) :
    finiteCoordinateMarginal
        (repeatedAlicePostselectedQuestionLaw G n S D) j x =
      groupedMass
        (fun ω : ExactOutcome X Y A B n => ω.1 j)
        (repeatedConditionedOutcomeLaw G n S D) x := by
  classical
  let projection :=
    fun ω : ExactOutcome X Y A B n => ω.1
  let posterior := repeatedConditionedOutcomeLaw G n S D
  have hlaw :
      repeatedAlicePostselectedQuestionLaw G n S D =
        groupedMass projection posterior := by
    unfold repeatedAlicePostselectedQuestionLaw
    exact exactGroupedMass_decidableEq_irrel _ _ _ _
  rw [hlaw]
  exact finiteCoordinateMarginal_groupedMass
    projection posterior j x

theorem repeatedBobPostselectedCoordinateMarginal
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (j : Fin n) (y : Y) :
    finiteCoordinateMarginal
        (repeatedBobPostselectedQuestionLaw G n S D) j y =
      groupedMass
        (fun ω : ExactOutcome X Y A B n => ω.2.1 j)
        (repeatedConditionedOutcomeLaw G n S D) y := by
  classical
  let projection :=
    fun ω : ExactOutcome X Y A B n => ω.2.1
  let posterior := repeatedConditionedOutcomeLaw G n S D
  have hlaw :
      repeatedBobPostselectedQuestionLaw G n S D =
        groupedMass projection posterior := by
    unfold repeatedBobPostselectedQuestionLaw
    exact exactGroupedMass_decidableEq_irrel _ _ _ _
  rw [hlaw]
  exact finiteCoordinateMarginal_groupedMass
    projection posterior j y

theorem exactAliceSourceMarginalInformation_eq
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (base : ExactHistoryFlag X Y A B D) :
    exactAliceSourceMarginalInformation G n S D base =
      (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        ∑ i : SourceRemainingCoordinate D,
          finiteRelativeEntropy
            (finiteCoordinateMarginal
              (repeatedAlicePostselectedQuestionLaw G n S D)
              i.val)
            G.marginalX := by
  classical
  let posterior := repeatedAlicePostselectedQuestionLaw G n S D
  have hposterior :
      jointFirstMarginal
          (exactAliceInformationPosterior G n S D) =
        (fun t : SourceRemainingCoordinate D × X =>
          (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
            finiteCoordinateMarginal posterior t.1.val t.2) := by
    funext t
    rcases t with ⟨i, x⟩
    rw [exactAliceInformationPosterior_firstMarginal]
    congr 1
    exact (repeatedAlicePostselectedCoordinateMarginal
      G n S D i.val x).symm
  have hreference :
      jointFirstMarginal
          (exactAliceInformationReference G n S D base) =
        (fun t : SourceRemainingCoordinate D × X =>
          (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
            G.marginalX t.2) := by
    funext t
    rcases t with ⟨i, x⟩
    rw [exactAliceInformationReference_firstMarginal]
    change G.marginalX x /
      (Fintype.card (SourceRemainingCoordinate D) : ℝ) = _
    ring
  unfold exactAliceSourceMarginalInformation
  rw [hposterior, hreference]
  exact finiteUniformCoordinate_relativeEntropy
    (exactRemainingCoordinate_card_pos D remaining)
    (fun i : SourceRemainingCoordinate D =>
      finiteCoordinateMarginal posterior i.val)
    G.marginalX

theorem exactBobSourceMarginalInformation_eq
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (base : ExactHistoryFlag X Y A B D) :
    exactBobSourceMarginalInformation G n S D base =
      (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        ∑ i : SourceRemainingCoordinate D,
          finiteRelativeEntropy
            (finiteCoordinateMarginal
              (repeatedBobPostselectedQuestionLaw G n S D)
              i.val)
            G.marginalY := by
  classical
  let posterior := repeatedBobPostselectedQuestionLaw G n S D
  have hposterior :
      jointFirstMarginal
          (exactBobInformationPosterior G n S D) =
        (fun t : SourceRemainingCoordinate D × Y =>
          (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
            finiteCoordinateMarginal posterior t.1.val t.2) := by
    funext t
    rcases t with ⟨i, y⟩
    rw [exactBobInformationPosterior_firstMarginal]
    congr 1
    exact (repeatedBobPostselectedCoordinateMarginal
      G n S D i.val y).symm
  have hreference :
      jointFirstMarginal
          (exactBobInformationReference G n S D base) =
        (fun t : SourceRemainingCoordinate D × Y =>
          (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
            G.marginalY t.2) := by
    funext t
    rcases t with ⟨i, y⟩
    rw [exactBobInformationReference_firstMarginal]
    change G.marginalY y /
      (Fintype.card (SourceRemainingCoordinate D) : ℝ) = _
    ring
  unfold exactBobSourceMarginalInformation
  rw [hposterior, hreference]
  exact finiteUniformCoordinate_relativeEntropy
    (exactRemainingCoordinate_card_pos D remaining)
    (fun i : SourceRemainingCoordinate D =>
      finiteCoordinateMarginal posterior i.val)
    G.marginalY

theorem sourceRemaining_nonnegative_sum_le
    {n : ℕ} (D : Finset (Fin n)) (f : Fin n → ℝ)
    (nonnegative : ∀ j, 0 ≤ f j) :
    (∑ i : SourceRemainingCoordinate D, f i.val) ≤
      ∑ j : Fin n, f j := by
  classical
  change
    (∑ i ∈ (Finset.univ \ D).attach, f i.val) ≤
      ∑ j : Fin n, f j
  rw [Finset.sum_attach]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ (Finset.univ \ D))
    (fun j _ _ => nonnegative j)

theorem exactAliceSourceMarginalInformation_le
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D) :
    exactAliceSourceMarginalInformation G n S D base ≤
      postselectionLogCost G n S D /
        ((Finset.univ \ D).card : ℝ) := by
  classical
  let posterior := repeatedAlicePostselectedQuestionLaw G n S D
  let coordinateInfo : Fin n → ℝ := fun j =>
    finiteRelativeEntropy
      (finiteCoordinateMarginal posterior j) G.marginalX
  have hnonnegative (j : Fin n) : 0 ≤ coordinateInfo j := by
    exact finiteRelativeEntropy_nonneg
      (finiteCoordinateMarginal posterior j) G.marginalX
      (fun x => finiteCoordinateMarginal_nonneg
        posterior
        (repeatedAlicePostselectedQuestionLaw_nonneg
          G n S D positive) j x)
      G.marginalX_nonneg
  have hremaining :
      (∑ i : SourceRemainingCoordinate D, coordinateInfo i.val) ≤
        postselectionLogCost G n S D := by
    exact
      (sourceRemaining_nonnegative_sum_le
        D coordinateInfo hnonnegative).trans
      (repeatedAliceCoordinateInformation_sum_le
        G n S D positive)
  have hcard :
      Fintype.card (SourceRemainingCoordinate D) =
        (Finset.univ \ D).card := by
    simp only [Fintype.card_coe]
  calc
    exactAliceSourceMarginalInformation G n S D base =
      (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        ∑ i : SourceRemainingCoordinate D, coordinateInfo i.val :=
      exactAliceSourceMarginalInformation_eq
        G n S D remaining base
    _ ≤ (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        postselectionLogCost G n S D := by
      exact mul_le_mul_of_nonneg_left hremaining
        (one_div_nonneg.mpr (Nat.cast_nonneg _))
    _ = postselectionLogCost G n S D /
        ((Finset.univ \ D).card : ℝ) := by
      rw [hcard]
      ring

theorem exactBobSourceMarginalInformation_le
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D) :
    exactBobSourceMarginalInformation G n S D base ≤
      postselectionLogCost G n S D /
        ((Finset.univ \ D).card : ℝ) := by
  classical
  let posterior := repeatedBobPostselectedQuestionLaw G n S D
  let coordinateInfo : Fin n → ℝ := fun j =>
    finiteRelativeEntropy
      (finiteCoordinateMarginal posterior j) G.marginalY
  have hnonnegative (j : Fin n) : 0 ≤ coordinateInfo j := by
    exact finiteRelativeEntropy_nonneg
      (finiteCoordinateMarginal posterior j) G.marginalY
      (fun y => finiteCoordinateMarginal_nonneg
        posterior
        (repeatedBobPostselectedQuestionLaw_nonneg
          G n S D positive) j y)
      G.marginalY_nonneg
  have hremaining :
      (∑ i : SourceRemainingCoordinate D, coordinateInfo i.val) ≤
        postselectionLogCost G n S D := by
    exact
      (sourceRemaining_nonnegative_sum_le
        D coordinateInfo hnonnegative).trans
      (repeatedBobCoordinateInformation_sum_le
        G n S D positive)
  have hcard :
      Fintype.card (SourceRemainingCoordinate D) =
        (Finset.univ \ D).card := by
    simp only [Fintype.card_coe]
  calc
    exactBobSourceMarginalInformation G n S D base =
      (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        ∑ i : SourceRemainingCoordinate D, coordinateInfo i.val :=
      exactBobSourceMarginalInformation_eq
        G n S D remaining base
    _ ≤ (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        postselectionLogCost G n S D := by
      exact mul_le_mul_of_nonneg_left hremaining
        (one_div_nonneg.mpr (Nat.cast_nonneg _))
    _ = postselectionLogCost G n S D /
        ((Finset.univ \ D).card : ℝ) := by
      rw [hcard]
      ring

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem exact_source_equation_twenty_three_of_conditioned_reverse_prefix
    {KA KB : Type*} [Fintype KA] [Fintype KB]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (seedLawA : Finset (SourceRemainingCoordinate D) →
      FiniteEventLaw KA)
    (seedLawB : Finset (SourceRemainingCoordinate D) →
      FiniteEventLaw KB)
    (ΩA ΩB : Finset (SourceRemainingCoordinate D) → Type*)
    [∀ side, Fintype (ΩA side)]
    [∀ side, Fintype (ΩB side)]
    (projectionA : ∀ side : Finset (SourceRemainingCoordinate D),
      KA × ExactOutcome X Y A B n →
        ΩA side × (Fin side.card → Y))
    (projectionB : ∀ side : Finset (SourceRemainingCoordinate D),
      KB × ExactOutcome X Y A B n →
        ΩB side × (Fin side.card → X))
    (defaultY : Y) (defaultX : X)
    (aliceConditionedReverseIdentification :
      exactAliceSourceConditionalInformation G n S D base =
        ∑ side : Finset (SourceRemainingCoordinate D),
          reversePartitionWeight side *
            ((∑ k : Fin side.card,
              reweightedSeedPrefixEntropyIncrement
                (seedLawA side) G n S D
                (projectionA side) defaultY k) /
              (side.card : ℝ)))
    (bobConditionedReverseIdentification :
      exactBobSourceConditionalInformation G n S D base =
        ∑ side : Finset (SourceRemainingCoordinate D),
          reversePartitionWeight side *
            ((∑ k : Fin side.card,
              reweightedSeedPrefixEntropyIncrement
                (seedLawB side) G n S D
                (projectionB side) defaultX k) /
              (side.card : ℝ))) :
    ExactSourceClassicalInformationBound G n S D base := by
  constructor
  · rw [exact_source_equation_twenty_four_alice
      G n S D remaining positive base]
    change
      exactAliceSourceMarginalInformation G n S D base +
          exactAliceSourceConditionalInformation G n S D base ≤
        exactSourceClassicalInformationRate G n S D
    calc
      exactAliceSourceMarginalInformation G n S D base +
          exactAliceSourceConditionalInformation G n S D base ≤
        postselectionLogCost G n S D /
            ((Finset.univ \ D).card : ℝ) +
          2 * (postselectionLogCost G n S D +
            answerLogCost (A := A) (B := B) D) /
              ((Finset.univ \ D).card : ℝ) := by
            apply add_le_add
            · exact exactAliceSourceMarginalInformation_le
                G n S D remaining positive base
            · rw [aliceConditionedReverseIdentification]
              exact
                reweightedSeed_reverse_source_prefix_information_budget
                  G n S D remaining positive
                  seedLawA ΩA projectionA defaultY
      _ = exactSourceClassicalInformationRate G n S D := by
        unfold exactSourceClassicalInformationRate
        ring
  · rw [exact_source_equation_twenty_four_bob
      G n S D remaining positive base]
    change
      exactBobSourceMarginalInformation G n S D base +
          exactBobSourceConditionalInformation G n S D base ≤
        exactSourceClassicalInformationRate G n S D
    calc
      exactBobSourceMarginalInformation G n S D base +
          exactBobSourceConditionalInformation G n S D base ≤
        postselectionLogCost G n S D /
            ((Finset.univ \ D).card : ℝ) +
          2 * (postselectionLogCost G n S D +
            answerLogCost (A := A) (B := B) D) /
              ((Finset.univ \ D).card : ℝ) := by
            apply add_le_add
            · exact exactBobSourceMarginalInformation_le
                G n S D remaining positive base
            · rw [bobConditionedReverseIdentification]
              exact
                reweightedSeed_reverse_source_prefix_information_budget
                  G n S D remaining positive
                  seedLawB ΩB projectionB defaultX
      _ = exactSourceClassicalInformationRate G n S D := by
        unfold exactSourceClassicalInformationRate
        ring

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The information increment contributed by exact conditioned reverse alice prefix entropy. -/
def exactConditionedReverseAlicePrefixEntropyIncrement
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (side : Finset (SourceRemainingCoordinate D))
    (default : Y) (k : Fin side.card) : ℝ :=
  reweightedSeedPrefixEntropyIncrement
    (exactReverseAliceConditionalSeedLaw
      (exactRemainingCoordinate_card_pos D remaining) side)
    G n S D
    (exactReverseAliceSourceProjection
      (X := X) (Y := Y) (A := A) (B := B) D side)
    default k

/-- The information increment contributed by exact conditioned reverse bob prefix entropy. -/
def exactConditionedReverseBobPrefixEntropyIncrement
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (side : Finset (SourceRemainingCoordinate D))
    (default : X) (k : Fin side.card) : ℝ :=
  reweightedSeedPrefixEntropyIncrement
    (exactReverseBobConditionalSeedLaw
      (exactRemainingCoordinate_card_pos D remaining) side)
    G n S D
    (exactReverseBobSourceProjection
      (X := X) (Y := Y) (A := A) (B := B) D side)
    default k

/--
The exact conditioned reverse alice prefix information construction used in the quantum
parallel-repetition argument.
-/
def exactConditionedReverseAlicePrefixInformation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (default : Y) : ℝ :=
  ∑ side : Finset (SourceRemainingCoordinate D),
    reversePartitionWeight side *
      ((∑ k : Fin side.card,
        exactConditionedReverseAlicePrefixEntropyIncrement
          G n S D remaining side default k) /
        (side.card : ℝ))

/--
The exact conditioned reverse bob prefix information construction used in the quantum parallel-
repetition argument.
-/
def exactConditionedReverseBobPrefixInformation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (default : X) : ℝ :=
  ∑ side : Finset (SourceRemainingCoordinate D),
    reversePartitionWeight side *
      ((∑ k : Fin side.card,
        exactConditionedReverseBobPrefixEntropyIncrement
          G n S D remaining side default k) /
        (side.card : ℝ))

/--
The exact reverse alice conditional history identification construction used in the quantum
parallel-repetition argument.
-/
def ExactReverseAliceConditionalHistoryIdentification
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (base : ExactHistoryFlag X Y A B D)
    (default : Y) : Prop :=
  exactAliceSourceConditionalInformation G n S D base =
    exactConditionedReverseAlicePrefixInformation
      G n S D remaining default

/--
The exact reverse bob conditional history identification construction used in the quantum
parallel-repetition argument.
-/
def ExactReverseBobConditionalHistoryIdentification
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (base : ExactHistoryFlag X Y A B D)
    (default : X) : Prop :=
  exactBobSourceConditionalInformation G n S D base =
    exactConditionedReverseBobPrefixInformation
      G n S D remaining default

theorem exact_source_equation_twenty_three_of_actual_conditioned_reindex
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (defaultY : Y) (defaultX : X)
    (alice : ExactReverseAliceConditionalHistoryIdentification
      G n S D remaining base defaultY)
    (bob : ExactReverseBobConditionalHistoryIdentification
      G n S D remaining base defaultX) :
    ExactSourceClassicalInformationBound G n S D base := by
  apply
    exact_source_equation_twenty_three_of_conditioned_reverse_prefix
      G n S D remaining positive base
      (exactReverseAliceConditionalSeedLaw
        (exactRemainingCoordinate_card_pos D remaining))
      (exactReverseBobConditionalSeedLaw
        (exactRemainingCoordinate_card_pos D remaining))
      (ExactReverseAliceFixedInformation X Y D)
      (ExactReverseBobFixedInformation X Y D)
      (exactReverseAliceSourceProjection
        (X := X) (Y := Y) (A := A) (B := B) D)
      (exactReverseBobSourceProjection
        (X := X) (Y := Y) (A := A) (B := B) D)
      defaultY defaultX
  · exact alice
  · exact bob

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

theorem finiteRelativeEntropy_self
    {I : Type*} [Fintype I] (mass : I → ℝ) :
    finiteRelativeEntropy mass mass = 0 := by
  unfold finiteRelativeEntropy
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : mass i = 0
  · simp only [hi, div_zero, zero_mul]
  · simp only [InformationTheory.klFun, ne_eq, hi, not_false_eq_true, div_self, Real.log_one,
      mul_zero, zero_add, sub_self]

theorem finiteConditionalHistoryRelativeEntropy_eq
    {I R V : Type*} [Fintype I] [Fintype R] [Fintype V]
    (p q : I × (R × V) → ℝ)
    (p_nonnegative : ∀ point, 0 ≤ p point)
    (q_nonnegative : ∀ point, 0 ≤ q point)
    (absolute_continuity : ∀ point, q point = 0 → p point = 0)
    (reference : I → R → V → ℝ)
    (same_history : ∀ i,
      jointFirstMarginal p i ≠ 0 →
        jointFirstMarginal (jointConditional p i) =
          jointFirstMarginal (jointConditional q i))
    (next_reference : ∀ i r,
      jointFirstMarginal p i ≠ 0 →
      jointFirstMarginal (jointConditional p i) r ≠ 0 →
        jointConditional (jointConditional q i) r = reference i r) :
    (∑ i : I,
      jointFirstMarginal p i *
        finiteRelativeEntropy
          (jointConditional p i)
          (jointConditional q i)) =
      ∑ i : I,
        jointFirstMarginal p i *
          (∑ r : R,
            jointFirstMarginal (jointConditional p i) r *
              finiteRelativeEntropy
                (jointConditional (jointConditional p i) r)
                (reference i r)) := by
  apply Finset.sum_congr rfl
  intro i _
  by_cases hpi : jointFirstMarginal p i = 0
  · simp only [hpi, zero_mul]
  · have hqi : jointFirstMarginal q i ≠ 0 := by
      intro hz
      exact hpi
        (jointFirstMarginal_absolute_continuity
          p q q_nonnegative absolute_continuity i hz)
    have hpconditional :
        ∀ t : R × V, 0 ≤ jointConditional p i t := by
      intro t
      exact div_nonneg (p_nonnegative (i, t))
        (jointFirstMarginal_nonneg p p_nonnegative i)
    have hqconditional :
        ∀ t : R × V, 0 ≤ jointConditional q i t := by
      intro t
      exact div_nonneg (q_nonnegative (i, t))
        (jointFirstMarginal_nonneg q q_nonnegative i)
    have hconditional_absolute :
        ∀ t : R × V,
          jointConditional q i t = 0 →
            jointConditional p i t = 0 := by
      intro t hz
      have hqzero : q (i, t) = 0 := by
        change q (i, t) / jointFirstMarginal q i = 0 at hz
        exact (div_eq_zero_iff.mp hz).resolve_right hqi
      simp only [jointConditional, absolute_continuity (i, t) hqzero, zero_div]
    have hchain := finite_relative_entropy_joint_chain_rule
      (jointConditional p i) (jointConditional q i)
      hpconditional hqconditional hconditional_absolute
      (jointConditional_sum p i hpi)
      (jointConditional_sum q i hqi)
    have hhistory_entropy :
        finiteRelativeEntropy
          (jointFirstMarginal (jointConditional p i))
          (jointFirstMarginal (jointConditional q i)) = 0 := by
      rw [← same_history i hpi]
      exact finiteRelativeEntropy_self _
    rw [hhistory_entropy, zero_add] at hchain
    rw [hchain]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    by_cases hr : jointFirstMarginal (jointConditional p i) r = 0
    · simp only [hr, zero_mul]
    · rw [next_reference i r hpi hr]

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

theorem finiteSupportedConditionalHistoryReferenceFirstMarginal_eq
    {I R V : Type*} [Fintype R] [Fintype V]
    (p q : I × (R × V) → ℝ)
    (q_nonnegative : ∀ point, 0 ≤ q point)
    (absolute_continuity : ∀ point, q point = 0 → p point = 0)
    (reference : I → R → V → ℝ)
    (reference_normalized : ∀ i,
      jointFirstMarginal p i ≠ 0 →
        ∀ r, (∑ v : V, reference i r v) = 1)
    (factor : ∀ i,
      jointFirstMarginal p i ≠ 0 →
        ∀ r v,
          q (i, (r, v)) =
            jointFirstMarginal q i *
              jointFirstMarginal (jointConditional p i) r *
              reference i r v)
    (i : I) (supported : jointFirstMarginal p i ≠ 0) :
    jointFirstMarginal (jointConditional q i) =
      jointFirstMarginal (jointConditional p i) := by
  have hqi : jointFirstMarginal q i ≠ 0 := by
    intro hz
    exact supported
      (jointFirstMarginal_absolute_continuity
        p q q_nonnegative absolute_continuity i hz)
  funext r
  change
    (∑ v : V,
      q (i, (r, v)) / jointFirstMarginal q i) =
      jointFirstMarginal (jointConditional p i) r
  simp_rw [factor i supported r]
  calc
    (∑ v : V,
      (jointFirstMarginal q i *
        jointFirstMarginal (jointConditional p i) r *
        reference i r v) / jointFirstMarginal q i) =
      ∑ v : V,
        jointFirstMarginal (jointConditional p i) r *
          reference i r v := by
        apply Finset.sum_congr rfl
        intro v _
        field_simp [hqi]
    _ = jointFirstMarginal (jointConditional p i) r := by
      rw [← Finset.mul_sum, reference_normalized i supported r]
      ring

theorem finiteSupportedConditionalHistoryReferenceConditional_eq
    {I R V : Type*} [Fintype R] [Fintype V]
    (p q : I × (R × V) → ℝ)
    (q_nonnegative : ∀ point, 0 ≤ q point)
    (absolute_continuity : ∀ point, q point = 0 → p point = 0)
    (reference : I → R → V → ℝ)
    (reference_normalized : ∀ i,
      jointFirstMarginal p i ≠ 0 →
        ∀ r, (∑ v : V, reference i r v) = 1)
    (factor : ∀ i,
      jointFirstMarginal p i ≠ 0 →
        ∀ r v,
          q (i, (r, v)) =
            jointFirstMarginal q i *
              jointFirstMarginal (jointConditional p i) r *
              reference i r v)
    (i : I) (r : R)
    (supported : jointFirstMarginal p i ≠ 0)
    (history_supported :
      jointFirstMarginal (jointConditional p i) r ≠ 0) :
    jointConditional (jointConditional q i) r = reference i r := by
  have hqi : jointFirstMarginal q i ≠ 0 := by
    intro hz
    exact supported
      (jointFirstMarginal_absolute_continuity
        p q q_nonnegative absolute_continuity i hz)
  have hhistory :=
    finiteSupportedConditionalHistoryReferenceFirstMarginal_eq
      p q q_nonnegative absolute_continuity
      reference reference_normalized factor i supported
  funext v
  change
    (q (i, (r, v)) / jointFirstMarginal q i) /
        jointFirstMarginal (jointConditional q i) r =
      reference i r v
  rw [factor i supported r v, congrFun hhistory r]
  field_simp [hqi, history_supported]

theorem finiteSupportedConditionalHistoryRelativeEntropy_eq_of_factor
    {I R V : Type*} [Fintype I] [Fintype R] [Fintype V]
    (p q : I × (R × V) → ℝ)
    (p_nonnegative : ∀ point, 0 ≤ p point)
    (q_nonnegative : ∀ point, 0 ≤ q point)
    (absolute_continuity : ∀ point, q point = 0 → p point = 0)
    (reference : I → R → V → ℝ)
    (reference_normalized : ∀ i,
      jointFirstMarginal p i ≠ 0 →
        ∀ r, (∑ v : V, reference i r v) = 1)
    (factor : ∀ i,
      jointFirstMarginal p i ≠ 0 →
        ∀ r v,
          q (i, (r, v)) =
            jointFirstMarginal q i *
              jointFirstMarginal (jointConditional p i) r *
              reference i r v) :
    (∑ i : I,
      jointFirstMarginal p i *
        finiteRelativeEntropy
          (jointConditional p i)
          (jointConditional q i)) =
      ∑ i : I,
        jointFirstMarginal p i *
          (∑ r : R,
            jointFirstMarginal (jointConditional p i) r *
              finiteRelativeEntropy
                (jointConditional (jointConditional p i) r)
                (reference i r)) := by
  apply finiteConditionalHistoryRelativeEntropy_eq
    p q p_nonnegative q_nonnegative absolute_continuity reference
  · intro i hi
    exact
      (finiteSupportedConditionalHistoryReferenceFirstMarginal_eq
        p q q_nonnegative absolute_continuity
        reference reference_normalized factor i hi).symm
  · intro i r hi hr
    exact
      finiteSupportedConditionalHistoryReferenceConditional_eq
        p q q_nonnegative absolute_continuity
        reference reference_normalized factor i r hi hr

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem exactAliceInformationPosterior_firstMarginal_eq_localMass
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (i : SourceRemainingCoordinate D) (x : X) :
    jointFirstMarginal
        (exactAliceInformationPosterior G n S D) (i, x) =
      exactAliceLocalMass D
        (exactLocallySampleableLaw G n S D) i x := by
  unfold jointFirstMarginal
  rw [Fintype.sum_prod_type]
  rfl

theorem exactBobInformationPosterior_firstMarginal_eq_localMass
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (i : SourceRemainingCoordinate D) (y : Y) :
    jointFirstMarginal
        (exactBobInformationPosterior G n S D) (i, y) =
      exactBobLocalMass D
        (exactLocallySampleableLaw G n S D) i y := by
  unfold jointFirstMarginal
  rw [Fintype.sum_prod_type]
  rfl

theorem exactAliceSupportedQuestion_marginal_pos
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (i : SourceRemainingCoordinate D) (x : X)
    (supported : jointFirstMarginal
      (exactAliceInformationPosterior G n S D) (i, x) ≠ 0) :
    0 < G.marginalX x := by
  let p := exactAliceInformationPosterior G n S D
  let q := exactAliceInformationReference G n S D base
  have hqnonnegative : ∀ t, 0 ≤ q t := by
    intro t
    exact exactLocallySampleableJA_nonneg
      G n S D positive base
      ((exactAliceInformationEquiv
        (X := X) (Y := Y) (A := A) (B := B) D).symm t)
  have hac : ∀ t, q t = 0 → p t = 0 := by
    intro t hz
    exact exactLocallySampleableLaw_absolute_continuous_JA
      G n S D remaining positive base
      ((exactAliceInformationEquiv
        (X := X) (Y := Y) (A := A) (B := B) D).symm t) hz
  have hqmass : jointFirstMarginal q (i, x) ≠ 0 := by
    intro hz
    exact supported
      (jointFirstMarginal_absolute_continuity
        p q hqnonnegative hac (i, x) hz)
  rw [exactAliceInformationReference_firstMarginal
    G n S D base i x] at hqmass
  have hx : G.marginalX x ≠ 0 := by
    intro hz
    apply hqmass
    change G.marginalX x /
      (Fintype.card (SourceRemainingCoordinate D) : ℝ) = 0
    rw [hz]
    simp only [Fintype.card_coe, zero_div]
  exact lt_of_le_of_ne (G.marginalX_nonneg x) (Ne.symm hx)

theorem exactBobSupportedQuestion_marginal_pos
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (i : SourceRemainingCoordinate D) (y : Y)
    (supported : jointFirstMarginal
      (exactBobInformationPosterior G n S D) (i, y) ≠ 0) :
    0 < G.marginalY y := by
  let p := exactBobInformationPosterior G n S D
  let q := exactBobInformationReference G n S D base
  have hqnonnegative : ∀ t, 0 ≤ q t := by
    intro t
    exact exactLocallySampleableJB_nonneg
      G n S D positive base
      ((exactBobInformationEquiv
        (X := X) (Y := Y) (A := A) (B := B) D).symm t)
  have hac : ∀ t, q t = 0 → p t = 0 := by
    intro t hz
    exact exactLocallySampleableLaw_absolute_continuous_JB
      G n S D remaining positive base
      ((exactBobInformationEquiv
        (X := X) (Y := Y) (A := A) (B := B) D).symm t) hz
  have hqmass : jointFirstMarginal q (i, y) ≠ 0 := by
    intro hz
    exact supported
      (jointFirstMarginal_absolute_continuity
        p q hqnonnegative hac (i, y) hz)
  rw [exactBobInformationReference_firstMarginal
    G n S D base i y] at hqmass
  have hy : G.marginalY y ≠ 0 := by
    intro hz
    apply hqmass
    change G.marginalY y /
      (Fintype.card (SourceRemainingCoordinate D) : ℝ) = 0
    rw [hz]
    simp only [Fintype.card_coe, zero_div]
  exact lt_of_le_of_ne (G.marginalY_nonneg y) (Ne.symm hy)

theorem exactAliceInformationPosterior_historyMarginal
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D)
    (i : SourceRemainingCoordinate D) (x : X)
    (supported : jointFirstMarginal
      (exactAliceInformationPosterior G n S D) (i, x) ≠ 0)
    (r : ExactHistoryFlag X Y A B D) :
    jointFirstMarginal
        (jointConditional
          (exactAliceInformationPosterior G n S D) (i, x)) r =
      exactAliceLocalConditional D base
        (exactLocallySampleableLaw G n S D) i x r := by
  have hmass :=
    exactAliceInformationPosterior_firstMarginal_eq_localMass
      G n S D i x
  have hlocal :
      exactAliceLocalMass D
        (exactLocallySampleableLaw G n S D) i x ≠ 0 := by
    rw [← hmass]
    exact supported
  unfold jointFirstMarginal jointConditional
  change
    (∑ y : Y,
      exactLocallySampleableLaw G n S D (i, x, y, r) /
        jointFirstMarginal
          (exactAliceInformationPosterior G n S D) (i, x)) =
      exactAliceLocalConditional D base
        (exactLocallySampleableLaw G n S D) i x r
  rw [← Finset.sum_div, hmass]
  simp only [exactAliceLocalConditional, hlocal, ↓reduceIte]

theorem exactBobInformationPosterior_historyMarginal
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D)
    (i : SourceRemainingCoordinate D) (y : Y)
    (supported : jointFirstMarginal
      (exactBobInformationPosterior G n S D) (i, y) ≠ 0)
    (r : ExactHistoryFlag X Y A B D) :
    jointFirstMarginal
        (jointConditional
          (exactBobInformationPosterior G n S D) (i, y)) r =
      exactBobLocalConditional D base
        (exactLocallySampleableLaw G n S D) i y r := by
  have hmass :=
    exactBobInformationPosterior_firstMarginal_eq_localMass
      G n S D i y
  have hlocal :
      exactBobLocalMass D
        (exactLocallySampleableLaw G n S D) i y ≠ 0 := by
    rw [← hmass]
    exact supported
  unfold jointFirstMarginal jointConditional
  change
    (∑ x : X,
      exactLocallySampleableLaw G n S D (i, x, y, r) /
        jointFirstMarginal
          (exactBobInformationPosterior G n S D) (i, y)) =
      exactBobLocalConditional D base
        (exactLocallySampleableLaw G n S D) i y r
  rw [← Finset.sum_div, hmass]
  simp only [exactBobLocalConditional, hlocal, ↓reduceIte]

theorem exactAliceInformationReference_supported_factor
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D)
    (i : SourceRemainingCoordinate D) (x : X)
    (supported : jointFirstMarginal
      (exactAliceInformationPosterior G n S D) (i, x) ≠ 0)
    (r : ExactHistoryFlag X Y A B D) (y : Y) :
    exactAliceInformationReference G n S D base
        ((i, x), (r, y)) =
      jointFirstMarginal
          (exactAliceInformationReference G n S D base) (i, x) *
        jointFirstMarginal
          (jointConditional
            (exactAliceInformationPosterior G n S D) (i, x)) r *
        G.conditionalYGivenX x y := by
  rw [exactAliceInformationReference_firstMarginal
    G n S D base i x,
    exactAliceInformationPosterior_historyMarginal
      G n S D base i x supported r]
  change
    G.questionWeight x y *
        exactAliceLocalConditional D base
          (exactLocallySampleableLaw G n S D) i x r /
          (Fintype.card (SourceRemainingCoordinate D) : ℝ) =
      (G.marginalX x /
        (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        exactAliceLocalConditional D base
          (exactLocallySampleableLaw G n S D) i x r *
        G.conditionalYGivenX x y
  rw [← G.marginalX_mul_conditionalYGivenX x y]
  ring

theorem exactBobInformationReference_supported_factor
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D)
    (i : SourceRemainingCoordinate D) (y : Y)
    (supported : jointFirstMarginal
      (exactBobInformationPosterior G n S D) (i, y) ≠ 0)
    (r : ExactHistoryFlag X Y A B D) (x : X) :
    exactBobInformationReference G n S D base
        ((i, y), (r, x)) =
      jointFirstMarginal
          (exactBobInformationReference G n S D base) (i, y) *
        jointFirstMarginal
          (jointConditional
            (exactBobInformationPosterior G n S D) (i, y)) r *
        G.conditionalXGivenY y x := by
  rw [exactBobInformationReference_firstMarginal
    G n S D base i y,
    exactBobInformationPosterior_historyMarginal
      G n S D base i y supported r]
  change
    G.questionWeight x y *
        exactBobLocalConditional D base
          (exactLocallySampleableLaw G n S D) i y r /
          (Fintype.card (SourceRemainingCoordinate D) : ℝ) =
      (G.marginalY y /
        (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        exactBobLocalConditional D base
          (exactLocallySampleableLaw G n S D) i y r *
        G.conditionalXGivenY y x
  rw [← G.marginalY_mul_conditionalXGivenY x y]
  ring

theorem exactAliceSourceConditionalInformation_eq_question
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D) :
    exactAliceSourceConditionalInformation G n S D base =
      ∑ ix : SourceRemainingCoordinate D × X,
        jointFirstMarginal
          (exactAliceInformationPosterior G n S D) ix *
          (∑ r : ExactHistoryFlag X Y A B D,
            jointFirstMarginal
                (jointConditional
                  (exactAliceInformationPosterior G n S D) ix) r *
              finiteRelativeEntropy
                (jointConditional
                  (jointConditional
                    (exactAliceInformationPosterior G n S D) ix) r)
                (G.conditionalYGivenX ix.2)) := by
  let p := exactAliceInformationPosterior G n S D
  let q := exactAliceInformationReference G n S D base
  have hp : ∀ t, 0 ≤ p t := by
    intro t
    exact exactLocallySampleableLaw_nonneg
      G n S D positive
      ((exactAliceInformationEquiv
        (X := X) (Y := Y) (A := A) (B := B) D).symm t)
  have hq : ∀ t, 0 ≤ q t := by
    intro t
    exact exactLocallySampleableJA_nonneg
      G n S D positive base
      ((exactAliceInformationEquiv
        (X := X) (Y := Y) (A := A) (B := B) D).symm t)
  have hac : ∀ t, q t = 0 → p t = 0 := by
    intro t hz
    exact exactLocallySampleableLaw_absolute_continuous_JA
      G n S D remaining positive base
      ((exactAliceInformationEquiv
        (X := X) (Y := Y) (A := A) (B := B) D).symm t) hz
  unfold exactAliceSourceConditionalInformation
  apply finiteSupportedConditionalHistoryRelativeEntropy_eq_of_factor
    p q hp hq hac
    (fun ix _ => G.conditionalYGivenX ix.2)
  · intro ix hix r
    exact G.conditionalYGivenX_sum ix.2
      (exactAliceSupportedQuestion_marginal_pos
        G n S D remaining positive base ix.1 ix.2 hix)
  · intro ix hix r y
    exact exactAliceInformationReference_supported_factor
      G n S D base ix.1 ix.2 hix r y

theorem exactBobSourceConditionalInformation_eq_question
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D) :
    exactBobSourceConditionalInformation G n S D base =
      ∑ iy : SourceRemainingCoordinate D × Y,
        jointFirstMarginal
          (exactBobInformationPosterior G n S D) iy *
          (∑ r : ExactHistoryFlag X Y A B D,
            jointFirstMarginal
                (jointConditional
                  (exactBobInformationPosterior G n S D) iy) r *
              finiteRelativeEntropy
                (jointConditional
                  (jointConditional
                    (exactBobInformationPosterior G n S D) iy) r)
                (G.conditionalXGivenY iy.2)) := by
  let p := exactBobInformationPosterior G n S D
  let q := exactBobInformationReference G n S D base
  have hp : ∀ t, 0 ≤ p t := by
    intro t
    exact exactLocallySampleableLaw_nonneg
      G n S D positive
      ((exactBobInformationEquiv
        (X := X) (Y := Y) (A := A) (B := B) D).symm t)
  have hq : ∀ t, 0 ≤ q t := by
    intro t
    exact exactLocallySampleableJB_nonneg
      G n S D positive base
      ((exactBobInformationEquiv
        (X := X) (Y := Y) (A := A) (B := B) D).symm t)
  have hac : ∀ t, q t = 0 → p t = 0 := by
    intro t hz
    exact exactLocallySampleableLaw_absolute_continuous_JB
      G n S D remaining positive base
      ((exactBobInformationEquiv
        (X := X) (Y := Y) (A := A) (B := B) D).symm t) hz
  unfold exactBobSourceConditionalInformation
  apply finiteSupportedConditionalHistoryRelativeEntropy_eq_of_factor
    p q hp hq hac
    (fun iy _ => G.conditionalXGivenY iy.2)
  · intro iy hiy r
    exact G.conditionalXGivenY_sum iy.2
      (exactBobSupportedQuestion_marginal_pos
        G n S D remaining positive base iy.1 iy.2 hiy)
  · intro iy hiy r x
    exact exactBobInformationReference_supported_factor
      G n S D base iy.1 iy.2 hiy r x

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/--
The type used to represent exact reverse alice next context in the exact sampling construction.
-/
abbrev ExactReverseAliceNextContext
    (X Y A B : Type*)
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D)) :=
  (ExactReverseAliceFixedInformation X Y D side ×
    ConditionedAnswerFlag A B D) ×
    (Fin side.card → Y)

/-- The type used to represent exact reverse bob next context in the exact sampling construction. -/
abbrev ExactReverseBobNextContext
    (X Y A B : Type*)
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D)) :=
  (ExactReverseBobFixedInformation X Y D side ×
    ConditionedAnswerFlag A B D) ×
    (Fin side.card → X)

/--
The exact conditioned reverse alice next joint construction used in the quantum parallel-
repetition argument.
-/
def exactConditionedReverseAliceNextJoint
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (side : Finset (SourceRemainingCoordinate D)) :
    ExactReverseAliceNextContext X Y A B D side → ℝ :=
  reweightedSeedPrefixJoint
    (exactReverseAliceConditionalSeedLaw
      (exactRemainingCoordinate_card_pos D remaining) side)
    G n S D
    (exactReverseAliceSourceProjection
      (X := X) (Y := Y) (A := A) (B := B) D side)

/--
The exact conditioned reverse alice next prior construction used in the quantum parallel-
repetition argument.
-/
def exactConditionedReverseAliceNextPrior
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (side : Finset (SourceRemainingCoordinate D)) :
    ExactReverseAliceNextContext X Y A B D side → ℝ :=
  reweightedSeedPrefixPrior
    (exactReverseAliceConditionalSeedLaw
      (exactRemainingCoordinate_card_pos D remaining) side)
    G n S D
    (exactReverseAliceSourceProjection
      (X := X) (Y := Y) (A := A) (B := B) D side)

/--
The exact conditioned reverse bob next joint construction used in the quantum parallel-
repetition argument.
-/
def exactConditionedReverseBobNextJoint
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (side : Finset (SourceRemainingCoordinate D)) :
    ExactReverseBobNextContext X Y A B D side → ℝ :=
  reweightedSeedPrefixJoint
    (exactReverseBobConditionalSeedLaw
      (exactRemainingCoordinate_card_pos D remaining) side)
    G n S D
    (exactReverseBobSourceProjection
      (X := X) (Y := Y) (A := A) (B := B) D side)

/--
The exact conditioned reverse bob next prior construction used in the quantum parallel-
repetition argument.
-/
def exactConditionedReverseBobNextPrior
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (side : Finset (SourceRemainingCoordinate D)) :
    ExactReverseBobNextContext X Y A B D side → ℝ :=
  reweightedSeedPrefixPrior
    (exactReverseBobConditionalSeedLaw
      (exactRemainingCoordinate_card_pos D remaining) side)
    G n S D
    (exactReverseBobSourceProjection
      (X := X) (Y := Y) (A := A) (B := B) D side)

theorem exactReverseAliceMaskedProjection_eq_of_history
    {n : ℕ} (D : Finset (Fin n))
    (default : Y)
    (q q' : ExactJointOutcome X Y A B D)
    (same_history :
      exactHistoryCode D q =
        exactHistoryCode D q')
    (same_question :
      q.2.1 q.1.coordinate.val =
        q'.2.1 q'.1.coordinate.val) :
    finitePrefixMask
      default
      ((exactReverseAliceContext q.1).sideRank
        ⟨q.1.coordinate,
          exactReverseLeftSide_coordinate_mem q.1⟩).castSucc
      (exactReverseAliceSourceProjection
        (X := X) (Y := Y) (A := A) (B := B)
        D (exactReverseLeftSide q.1) q) =
    finitePrefixMask
      default
      ((exactReverseAliceContext q.1).sideRank
        ⟨q.1.coordinate,
          exactReverseLeftSide_coordinate_mem q.1⟩).castSucc
      (exactReverseAliceSourceProjection
        (X := X) (Y := Y) (A := A) (B := B)
        D (exactReverseLeftSide q.1) q') := by
  rcases q with ⟨seed, outcome⟩
  rcases q' with ⟨seed', outcome'⟩
  have hseed : seed = seed' :=
    congrArg (fun r : ExactHistoryFlag X Y A B D => r.seed)
      same_history
  subst seed'
  have htuple := congrArg
    (exactHistoryFlagEquiv
      (X := X) (Y := Y) (A := A) (B := B) D)
    same_history
  change
    (⟨seed,
       (exactRevealCode D seed
         (outcome.1, outcome.2.1),
        (fun j : {j : Fin n // j ∈ D} => outcome.2.2.1 j.val),
        (fun j : {j : Fin n // j ∈ D} => outcome.2.2.2 j.val))⟩ :
      ExactHistoryFlagTuple X Y A B D) =
    (⟨seed,
       (exactRevealCode D seed
         (outcome'.1, outcome'.2.1),
        (fun j : {j : Fin n // j ∈ D} => outcome'.2.2.1 j.val),
        (fun j : {j : Fin n // j ∈ D} => outcome'.2.2.2 j.val))⟩ :
      ExactHistoryFlagTuple X Y A B D) at htuple
  have hpair := eq_of_heq (Sigma.mk.inj htuple).2
  have hreveal :
      exactRevealCode D seed
          (outcome.1, outcome.2.1) =
        exactRevealCode D seed
          (outcome'.1, outcome'.2.1) :=
    congrArg Prod.fst hpair
  have hac := congrArg
    (fun r : ExactRevealHistory X Y D seed =>
      r.aliceConditioned) hreveal
  have hbc := congrArg
    (fun r : ExactRevealHistory X Y D seed =>
      r.bobConditioned) hreveal
  have hal := congrArg
    (fun r : ExactRevealHistory X Y D seed =>
      r.aliceLeft) hreveal
  have hbr := congrArg
    (fun r : ExactRevealHistory X Y D seed =>
      r.bobRight) hreveal
  have hbl := congrArg
    (fun r : ExactRevealHistory X Y D seed =>
      r.bobLeftPrefix) hreveal
  have har := congrArg
    (fun r : ExactRevealHistory X Y D seed =>
      r.aliceRightPrefix) hreveal
  let side := exactReverseLeftSide seed
  let context := exactReverseAliceContext seed
  let marker : Fin side.card :=
    context.sideRank
      ⟨seed.coordinate,
        exactReverseLeftSide_coordinate_mem seed⟩
  have hmarker : marker.val = seed.leftCut.val := by
    exact exactReverseAliceContext_marked_rank seed
  have hfixed :
      (exactReverseAliceSourceProjection
        (X := X) (Y := Y) (A := A) (B := B)
        D side (seed, outcome)).1 =
      (exactReverseAliceSourceProjection
        (X := X) (Y := Y) (A := A) (B := B)
        D side (seed, outcome')).1 := by
    simp only [side, exactReverseAliceSourceProjection,
      exactReverseAliceContextAt_actual]
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Prod.ext
      · exact hac
      apply Prod.ext
      · exact hbc
      apply Prod.ext
      · funext j
        by_cases hj : j.val = seed.coordinate
        · have hval : j.val.val = seed.coordinate.val :=
            congrArg Subtype.val hj
          simpa only [hval] using same_question
        · have hleft :
              j.val ∈ exactLeft
                seed.coordinate seed.partition := by
            have hmem :
                j.val ∈ insert seed.coordinate
                  (exactLeft seed.coordinate seed.partition) :=
              j.property
            exact (Finset.mem_insert.mp hmem).resolve_left hj
          exact congrFun hal ⟨j.val, hleft⟩
      apply Prod.ext
      · funext j
        have hj :
            j.val ∈ exactRight
              seed.coordinate seed.partition := by
          simpa only [exactReverseAliceContextAt_actual,
            exactReverseAliceContext] using j.property
        exact congrFun hbr ⟨j.val, hj⟩
      funext j
      have hj : j.val ∈ exactRightPrefix seed := by
        have hprefix :
            exactReverseContextOtherPrefix
              (exactReverseAliceContextAt
                (exactReverseLeftSide seed) seed) =
              exactRightPrefix seed := by
          rw [exactReverseAliceContextAt_actual,
            exactReverseAliceContext_otherPrefix]
        exact (Finset.ext_iff.mp hprefix j.val).mp j.property
      exact congrFun har ⟨j.val, hj⟩
  apply Prod.ext
  · exact hfixed
  · funext k
    by_cases hk : k.val < marker.val
    · have hbefore :
          (context.sideRank.symm k).val ∈
            exactLeftPrefix seed := by
        rw [← exactReverseAliceContext_prefix_before_marked seed]
        apply (exactOrderedSidePrefix_mem_iff
          side context.sideRank marker.castSucc
          (context.sideRank.symm k).val).mpr
        refine ⟨(context.sideRank.symm k).property, ?_⟩
        change
          (context.sideRank (context.sideRank.symm k)).val <
            marker.val
        rw [Equiv.apply_symm_apply]
        exact hk
      have hy := congrFun hbl
        ⟨(context.sideRank.symm k).val, hbefore⟩
      change
        outcome.2.1 (context.sideRank.symm k).val.val =
          outcome'.2.1 (context.sideRank.symm k).val.val at hy
      have hkcut : k.val < seed.leftCut.val := by
        rw [← hmarker]
        exact hk
      simpa only [finitePrefixMask, exactReverseAliceSourceProjection, exactReverseAliceContextAt,
        dite_eq_ite, ↓reduceDIte, Fin.val_castSucc, exactReverseAliceContext_marked_rank, hkcut,
        ↓reduceIte] using hy
    · have hkcut : ¬ k.val < seed.leftCut.val := by
        rw [← hmarker]
        exact hk
      simp only [finitePrefixMask, exactReverseAliceSourceProjection, exactReverseAliceContextAt,
        dite_eq_ite, ↓reduceDIte, Fin.val_castSucc, exactReverseAliceContext_marked_rank, hkcut,
        ↓reduceIte]

theorem exactReverseBobMaskedProjection_eq_of_history
    {n : ℕ} (D : Finset (Fin n))
    (default : X)
    (q q' : ExactJointOutcome X Y A B D)
    (same_history :
      exactHistoryCode D q =
        exactHistoryCode D q')
    (same_question :
      q.2.2.1 q.1.coordinate.val =
        q'.2.2.1 q'.1.coordinate.val) :
    finitePrefixMask
      default
      ((exactReverseBobContext q.1).sideRank
        ⟨q.1.coordinate,
          exactReverseRightSide_coordinate_mem q.1⟩).castSucc
      (exactReverseBobSourceProjection
        (X := X) (Y := Y) (A := A) (B := B)
        D (exactReverseRightSide q.1) q) =
    finitePrefixMask
      default
      ((exactReverseBobContext q.1).sideRank
        ⟨q.1.coordinate,
          exactReverseRightSide_coordinate_mem q.1⟩).castSucc
      (exactReverseBobSourceProjection
        (X := X) (Y := Y) (A := A) (B := B)
        D (exactReverseRightSide q.1) q') := by
  rcases q with ⟨seed, outcome⟩
  rcases q' with ⟨seed', outcome'⟩
  have hseed : seed = seed' :=
    congrArg (fun r : ExactHistoryFlag X Y A B D => r.seed)
      same_history
  subst seed'
  have htuple := congrArg
    (exactHistoryFlagEquiv
      (X := X) (Y := Y) (A := A) (B := B) D)
    same_history
  change
    (⟨seed,
       (exactRevealCode D seed
         (outcome.1, outcome.2.1),
        (fun j : {j : Fin n // j ∈ D} => outcome.2.2.1 j.val),
        (fun j : {j : Fin n // j ∈ D} => outcome.2.2.2 j.val))⟩ :
      ExactHistoryFlagTuple X Y A B D) =
    (⟨seed,
       (exactRevealCode D seed
         (outcome'.1, outcome'.2.1),
        (fun j : {j : Fin n // j ∈ D} => outcome'.2.2.1 j.val),
        (fun j : {j : Fin n // j ∈ D} => outcome'.2.2.2 j.val))⟩ :
      ExactHistoryFlagTuple X Y A B D) at htuple
  have hpair := eq_of_heq (Sigma.mk.inj htuple).2
  have hreveal :
      exactRevealCode D seed
          (outcome.1, outcome.2.1) =
        exactRevealCode D seed
          (outcome'.1, outcome'.2.1) :=
    congrArg Prod.fst hpair
  have hac := congrArg
    (fun r : ExactRevealHistory X Y D seed =>
      r.aliceConditioned) hreveal
  have hbc := congrArg
    (fun r : ExactRevealHistory X Y D seed =>
      r.bobConditioned) hreveal
  have hal := congrArg
    (fun r : ExactRevealHistory X Y D seed =>
      r.aliceLeft) hreveal
  have hbr := congrArg
    (fun r : ExactRevealHistory X Y D seed =>
      r.bobRight) hreveal
  have hbl := congrArg
    (fun r : ExactRevealHistory X Y D seed =>
      r.bobLeftPrefix) hreveal
  have har := congrArg
    (fun r : ExactRevealHistory X Y D seed =>
      r.aliceRightPrefix) hreveal
  let side := exactReverseRightSide seed
  let context := exactReverseBobContext seed
  let marker : Fin side.card :=
    context.sideRank
      ⟨seed.coordinate,
        exactReverseRightSide_coordinate_mem seed⟩
  have hmarker : marker.val = seed.rightCut.val := by
    exact exactReverseBobContext_marked_rank seed
  have hfixed :
      (exactReverseBobSourceProjection
        (X := X) (Y := Y) (A := A) (B := B)
        D side (seed, outcome)).1 =
      (exactReverseBobSourceProjection
        (X := X) (Y := Y) (A := A) (B := B)
        D side (seed, outcome')).1 := by
    simp only [side, exactReverseBobSourceProjection,
      exactReverseBobContextAt_actual]
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Prod.ext
      · exact hac
      apply Prod.ext
      · exact hbc
      apply Prod.ext
      · funext j
        by_cases hj : j.val = seed.coordinate
        · have hval : j.val.val = seed.coordinate.val :=
            congrArg Subtype.val hj
          simpa only [hval] using same_question
        · have hright :
              j.val ∈ exactRight
                seed.coordinate seed.partition := by
            have hmem :
                j.val ∈ insert seed.coordinate
                  (exactRight seed.coordinate seed.partition) :=
              j.property
            exact (Finset.mem_insert.mp hmem).resolve_left hj
          exact congrFun hbr ⟨j.val, hright⟩
      apply Prod.ext
      · funext j
        have hj :
            j.val ∈ exactLeft
              seed.coordinate seed.partition := by
          simpa only [exactReverseBobContextAt_actual,
            exactReverseBobContext] using j.property
        exact congrFun hal ⟨j.val, hj⟩
      funext j
      have hj : j.val ∈ exactLeftPrefix seed := by
        have hprefix :
            exactReverseContextOtherPrefix
              (exactReverseBobContextAt
                (exactReverseRightSide seed) seed) =
              exactLeftPrefix seed := by
          rw [exactReverseBobContextAt_actual,
            exactReverseBobContext_otherPrefix]
        exact (Finset.ext_iff.mp hprefix j.val).mp j.property
      exact congrFun hbl ⟨j.val, hj⟩
  apply Prod.ext
  · exact hfixed
  · funext k
    by_cases hk : k.val < marker.val
    · have hbefore :
          (context.sideRank.symm k).val ∈
            exactRightPrefix seed := by
        rw [← exactReverseBobContext_prefix_before_marked seed]
        apply (exactOrderedSidePrefix_mem_iff
          side context.sideRank marker.castSucc
          (context.sideRank.symm k).val).mpr
        refine ⟨(context.sideRank.symm k).property, ?_⟩
        change
          (context.sideRank (context.sideRank.symm k)).val <
            marker.val
        rw [Equiv.apply_symm_apply]
        exact hk
      have hx := congrFun har
        ⟨(context.sideRank.symm k).val, hbefore⟩
      change
        outcome.1 (context.sideRank.symm k).val.val =
          outcome'.1 (context.sideRank.symm k).val.val at hx
      have hkcut : k.val < seed.rightCut.val := by
        rw [← hmarker]
        exact hk
      simpa only [finitePrefixMask, exactReverseBobSourceProjection, exactReverseBobContextAt,
        dite_eq_ite, ↓reduceDIte, Fin.val_castSucc, exactReverseBobContext_marked_rank, hkcut,
        ↓reduceIte] using hx
    · have hkcut : ¬ k.val < seed.rightCut.val := by
        rw [← hmarker]
        exact hk
      simp only [finitePrefixMask, exactReverseBobSourceProjection, exactReverseBobContextAt,
        dite_eq_ite, ↓reduceDIte, Fin.val_castSucc, exactReverseBobContext_marked_rank, hkcut,
        ↓reduceIte]

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

theorem groupedMass_product_injective_seed
    {K Ω C T : Type*}
    [Fintype K] [Fintype Ω]
    [DecidableEq C] [DecidableEq T]
    (code : K → C) (injective : Function.Injective code)
    (projection : K → Ω → T)
    (seedWeight : K → ℝ) (outcomeWeight : Ω → ℝ)
    (seed : K) (target : T) :
    groupedMass
        (fun q : K × Ω => (code q.1, projection q.1 q.2))
        (fun q : K × Ω => seedWeight q.1 * outcomeWeight q.2)
        (code seed, target) =
      seedWeight seed *
        groupedMass (projection seed) outcomeWeight target := by
  classical
  unfold groupedMass
  rw [Finset.sum_filter, Fintype.sum_prod_type,
    Finset.sum_filter, Finset.mul_sum]
  simp only [Prod.mk.injEq, injective.eq_iff, mul_ite, mul_zero]
  rw [Finset.sum_eq_single seed]
  · simp only [true_and]
  · intro other _ different
    simp only [different, false_and, ↓reduceIte, sum_const_zero]
  · simp only [mem_univ, not_true_eq_false, true_and, IsEmpty.forall_iff]

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

theorem jointConditional_groupedMass_eq_of_fiber
    {Ω C D V : Type*}
    [Fintype Ω] [Fintype V]
    [DecidableEq (C × V)] [DecidableEq (D × V)]
    (mass : Ω → ℝ)
    (left : Ω → C) (right : Ω → D) (next : Ω → V)
    (leftTarget : C) (rightTarget : D)
    (same_fiber : ∀ outcome : Ω,
      left outcome = leftTarget ↔ right outcome = rightTarget) :
    jointConditional
        (groupedMass (fun outcome => (left outcome, next outcome)) mass)
        leftTarget =
      jointConditional
        (groupedMass (fun outcome => (right outcome, next outcome)) mass)
        rightTarget := by
  classical
  have hatom (value : V) :
      groupedMass
          (fun outcome => (left outcome, next outcome)) mass
          (leftTarget, value) =
        groupedMass
          (fun outcome => (right outcome, next outcome)) mass
          (rightTarget, value) := by
    unfold groupedMass
    apply Finset.sum_congr
    · ext outcome
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Prod.mk.injEq]
      exact and_congr_left (fun _ => same_fiber outcome)
    · intro outcome _
      rfl
  have hmarginal :
      jointFirstMarginal
          (groupedMass
            (fun outcome => (left outcome, next outcome)) mass)
          leftTarget =
        jointFirstMarginal
          (groupedMass
            (fun outcome => (right outcome, next outcome)) mass)
          rightTarget := by
    unfold jointFirstMarginal
    apply Finset.sum_congr rfl
    intro value _
    exact hatom value
  funext value
  unfold jointConditional
  rw [hatom value, hmarginal]

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The data context recording exact reverse alice marked history. -/
def exactReverseAliceMarkedHistoryContext
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (default : Y)
    (seed : ExactRemainingSeed D)
    (outcome : ExactOutcome X Y A B n) :
    ExactReverseAliceNextContext X Y A B D
      (exactReverseLeftSide seed) :=
  let side := exactReverseLeftSide seed
  let marker :=
    (exactReverseAliceContext seed).sideRank
      ⟨seed.coordinate,
        exactReverseLeftSide_coordinate_mem seed⟩
  let projection :=
    exactReverseAliceSourceProjection
      (X := X) (Y := Y) (A := A) (B := B)
      D side (seed, outcome)
  finitePrefixMask default marker.castSucc
    ((projection.1,
      repeatedConditionedAnswerFlag G n S D outcome),
      projection.2)

/-- The data context recording exact reverse bob marked history. -/
def exactReverseBobMarkedHistoryContext
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (default : X)
    (seed : ExactRemainingSeed D)
    (outcome : ExactOutcome X Y A B n) :
    ExactReverseBobNextContext X Y A B D
      (exactReverseRightSide seed) :=
  let side := exactReverseRightSide seed
  let marker :=
    (exactReverseBobContext seed).sideRank
      ⟨seed.coordinate,
        exactReverseRightSide_coordinate_mem seed⟩
  let projection :=
    exactReverseBobSourceProjection
      (X := X) (Y := Y) (A := A) (B := B)
      D side (seed, outcome)
  finitePrefixMask default marker.castSucc
    ((projection.1,
      repeatedConditionedAnswerFlag G n S D outcome),
      projection.2)

theorem exactConditionedAnswerFlag_eq_of_history
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (q q' : ExactJointOutcome X Y A B D)
    (same_history :
      exactHistoryCode D q =
        exactHistoryCode D q') :
    repeatedConditionedAnswerFlag G n S D q.2 =
      repeatedConditionedAnswerFlag G n S D q'.2 := by
  apply Prod.ext
  · exact congrArg
      (fun r : ExactHistoryFlag X Y A B D => r.aliceAnswer)
      same_history
  · exact congrArg
      (fun r : ExactHistoryFlag X Y A B D => r.bobAnswer)
      same_history

theorem exactReverseAliceMarkedHistoryContext_eq_of_history
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (default : Y)
    (seed : ExactRemainingSeed D)
    (outcome outcome' : ExactOutcome X Y A B n)
    (same_history :
      exactHistoryCode D (seed, outcome) =
        exactHistoryCode D (seed, outcome'))
    (same_question :
      outcome.1 seed.coordinate.val =
        outcome'.1 seed.coordinate.val) :
    exactReverseAliceMarkedHistoryContext
        G n S D default seed outcome =
      exactReverseAliceMarkedHistoryContext
        G n S D default seed outcome' := by
  have hmask := exactReverseAliceMaskedProjection_eq_of_history
    (X := X) (Y := Y) (A := A) (B := B)
    D default (seed, outcome) (seed, outcome')
    same_history same_question
  have hflag := exactConditionedAnswerFlag_eq_of_history
    G n S D (seed, outcome) (seed, outcome') same_history
  have hfixed :
      (exactReverseAliceSourceProjection
        (X := X) (Y := Y) (A := A) (B := B)
        D (exactReverseLeftSide seed) (seed, outcome)).1 =
      (exactReverseAliceSourceProjection
        (X := X) (Y := Y) (A := A) (B := B)
        D (exactReverseLeftSide seed) (seed, outcome')).1 := by
    have h := congrArg
      (fun t :
        ExactReverseAliceFixedInformation X Y D
          (exactReverseLeftSide seed) ×
            (Fin (exactReverseLeftSide seed).card → Y) =>
        t.1) hmask
    simpa only [finitePrefixMask] using h
  have hprefix :
      (finitePrefixMask default
        ((exactReverseAliceContext seed).sideRank
          ⟨seed.coordinate,
            exactReverseLeftSide_coordinate_mem seed⟩).castSucc
        (exactReverseAliceSourceProjection
          (X := X) (Y := Y) (A := A) (B := B)
          D (exactReverseLeftSide seed) (seed, outcome))).2 =
      (finitePrefixMask default
        ((exactReverseAliceContext seed).sideRank
          ⟨seed.coordinate,
            exactReverseLeftSide_coordinate_mem seed⟩).castSucc
        (exactReverseAliceSourceProjection
          (X := X) (Y := Y) (A := A) (B := B)
          D (exactReverseLeftSide seed) (seed, outcome'))).2 := by
    exact congrArg
      (fun t :
        ExactReverseAliceFixedInformation X Y D
          (exactReverseLeftSide seed) ×
            (Fin (exactReverseLeftSide seed).card → Y) =>
        t.2) hmask
  unfold exactReverseAliceMarkedHistoryContext
  dsimp
  apply Prod.ext
  · apply Prod.ext
    · exact hfixed
    · exact hflag
  · exact hprefix

theorem exactReverseBobMarkedHistoryContext_eq_of_history
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (default : X)
    (seed : ExactRemainingSeed D)
    (outcome outcome' : ExactOutcome X Y A B n)
    (same_history :
      exactHistoryCode D (seed, outcome) =
        exactHistoryCode D (seed, outcome'))
    (same_question :
      outcome.2.1 seed.coordinate.val =
        outcome'.2.1 seed.coordinate.val) :
    exactReverseBobMarkedHistoryContext
        G n S D default seed outcome =
      exactReverseBobMarkedHistoryContext
        G n S D default seed outcome' := by
  have hmask := exactReverseBobMaskedProjection_eq_of_history
    (X := X) (Y := Y) (A := A) (B := B)
    D default (seed, outcome) (seed, outcome')
    same_history same_question
  have hflag := exactConditionedAnswerFlag_eq_of_history
    G n S D (seed, outcome) (seed, outcome') same_history
  have hfixed :
      (exactReverseBobSourceProjection
        (X := X) (Y := Y) (A := A) (B := B)
        D (exactReverseRightSide seed) (seed, outcome)).1 =
      (exactReverseBobSourceProjection
        (X := X) (Y := Y) (A := A) (B := B)
        D (exactReverseRightSide seed) (seed, outcome')).1 := by
    have h := congrArg
      (fun t :
        ExactReverseBobFixedInformation X Y D
          (exactReverseRightSide seed) ×
            (Fin (exactReverseRightSide seed).card → X) =>
        t.1) hmask
    simpa only [finitePrefixMask] using h
  have hprefix :
      (finitePrefixMask default
        ((exactReverseBobContext seed).sideRank
          ⟨seed.coordinate,
            exactReverseRightSide_coordinate_mem seed⟩).castSucc
        (exactReverseBobSourceProjection
          (X := X) (Y := Y) (A := A) (B := B)
          D (exactReverseRightSide seed) (seed, outcome))).2 =
      (finitePrefixMask default
        ((exactReverseBobContext seed).sideRank
          ⟨seed.coordinate,
            exactReverseRightSide_coordinate_mem seed⟩).castSucc
        (exactReverseBobSourceProjection
          (X := X) (Y := Y) (A := A) (B := B)
          D (exactReverseRightSide seed) (seed, outcome'))).2 := by
    exact congrArg
      (fun t :
        ExactReverseBobFixedInformation X Y D
          (exactReverseRightSide seed) ×
            (Fin (exactReverseRightSide seed).card → X) =>
        t.2) hmask
  unfold exactReverseBobMarkedHistoryContext
  dsimp
  apply Prod.ext
  · apply Prod.ext
    · exact hfixed
    · exact hflag
  · exact hprefix

theorem exactReverseAlice_history_of_marked_context
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (default : Y)
    (seed : ExactRemainingSeed D)
    (outcome outcome' : ExactOutcome X Y A B n)
    (same_context :
      exactReverseAliceMarkedHistoryContext
          G n S D default seed outcome =
        exactReverseAliceMarkedHistoryContext
          G n S D default seed outcome') :
    outcome.1 seed.coordinate.val =
        outcome'.1 seed.coordinate.val ∧
      exactHistoryCode D (seed, outcome) =
        exactHistoryCode D (seed, outcome') := by
  let side := exactReverseLeftSide seed
  let context := exactReverseAliceContext seed
  let marker : Fin side.card :=
    context.sideRank
      ⟨seed.coordinate,
        exactReverseLeftSide_coordinate_mem seed⟩
  have hfixed :
      (exactReverseAliceSourceProjection
        (X := X) (Y := Y) (A := A) (B := B)
        D side (seed, outcome)).1 =
      (exactReverseAliceSourceProjection
        (X := X) (Y := Y) (A := A) (B := B)
        D side (seed, outcome')).1 := by
    have h := congrArg
      (fun t : ExactReverseAliceNextContext
        X Y A B D (exactReverseLeftSide seed) => t.1.1)
      same_context
    simpa only [exactReverseAliceMarkedHistoryContext,
      finitePrefixMask, side] using h
  have hflag :
      repeatedConditionedAnswerFlag G n S D outcome =
        repeatedConditionedAnswerFlag G n S D outcome' := by
    have h := congrArg
      (fun t : ExactReverseAliceNextContext
        X Y A B D (exactReverseLeftSide seed) => t.1.2)
      same_context
    simpa only [exactReverseAliceMarkedHistoryContext,
      finitePrefixMask] using h
  have hprefix :
      (finitePrefixMask default marker.castSucc
        (exactReverseAliceSourceProjection
          (X := X) (Y := Y) (A := A) (B := B)
          D side (seed, outcome))).2 =
      (finitePrefixMask default marker.castSucc
        (exactReverseAliceSourceProjection
          (X := X) (Y := Y) (A := A) (B := B)
          D side (seed, outcome'))).2 := by
    have h := congrArg
      (fun t : ExactReverseAliceNextContext
        X Y A B D (exactReverseLeftSide seed) => t.2)
      same_context
    simpa only [exactReverseAliceMarkedHistoryContext,
      finitePrefixMask, side, context, marker] using h
  have hfields := eq_of_heq (Sigma.mk.inj hfixed).2
  have hac := congrArg (fun t => t.1) hfields
  have hbc := congrArg (fun t => t.2.1) hfields
  have hside := congrArg (fun t => t.2.2.1) hfields
  have hother := congrArg (fun t => t.2.2.2.1) hfields
  have hoppositePrefix := congrArg (fun t => t.2.2.2.2) hfields
  have hquestion :
      outcome.1 seed.coordinate.val =
        outcome'.1 seed.coordinate.val := by
    have h := congrFun hside
      ⟨seed.coordinate,
        exactReverseLeftSide_coordinate_mem seed⟩
    exact h
  have hreveal :
      exactRevealCode D seed
          (outcome.1, outcome.2.1) =
        exactRevealCode D seed
          (outcome'.1, outcome'.2.1) := by
    apply (exactRevealHistoryEquiv
      (X := X) (Y := Y) D seed).injective
    apply Prod.ext
    · exact hac
    apply Prod.ext
    · exact hbc
    apply Prod.ext
    · funext j
      have hj : j.val ∈ side := by
        change j.val ∈ insert seed.coordinate
          (exactLeft seed.coordinate seed.partition)
        exact Finset.mem_insert_of_mem j.property
      exact congrFun hside ⟨j.val, hj⟩
    apply Prod.ext
    · funext j
      have hotherSide :
          (exactReverseAliceContextAt side seed).otherSide =
            exactRight seed.coordinate seed.partition := by
        change
          (exactReverseAliceContextAt
            (exactReverseLeftSide seed) seed).otherSide = _
        rw [exactReverseAliceContextAt_actual]
        rfl
      have hj :
          j.val ∈
            (exactReverseAliceContextAt side seed).otherSide :=
        (Finset.ext_iff.mp hotherSide j.val).mpr j.property
      exact congrFun hother ⟨j.val, hj⟩
    apply Prod.ext
    · funext j
      have hbefore :
          j.val ∈ exactReverseContextPrefixBefore
            context marker := by
        change
          j.val ∈ exactReverseContextPrefixBefore
            (exactReverseAliceContext seed)
            ((exactReverseAliceContext seed).sideRank
              ⟨seed.coordinate,
                exactReverseLeftSide_coordinate_mem seed⟩)
        rw [exactReverseAliceContext_prefix_before_marked]
        exact j.property
      have hparts :=
        (exactOrderedSidePrefix_mem_iff
          side context.sideRank marker.castSucc j.val).mp
          hbefore
      let position : Fin side.card :=
        context.sideRank ⟨j.val, hparts.1⟩
      have hlt : position.val < marker.val := by
        simpa only [Fin.val_fin_lt, Fin.val_castSucc] using hparts.2
      have hltCut : position.val < seed.leftCut.val := by
        calc
          position.val < marker.val := hlt
          _ = seed.leftCut.val := by
            exact exactReverseAliceContext_marked_rank seed
      have h := congrFun hprefix position
      change outcome.2.1 j.val.val = outcome'.2.1 j.val.val
      simpa [finitePrefixMask,
        exactReverseAliceSourceProjection,
        exactReverseAliceContextAt, side,
        context, marker, position, hlt, hltCut] using h
    · funext j
      have hotherPrefix :
          exactReverseContextOtherPrefix
              (exactReverseAliceContextAt side seed) =
            exactRightPrefix seed := by
        change
          exactReverseContextOtherPrefix
            (exactReverseAliceContextAt
              (exactReverseLeftSide seed) seed) = _
        rw [exactReverseAliceContextAt_actual,
          exactReverseAliceContext_otherPrefix]
      have hj :
          j.val ∈ exactReverseContextOtherPrefix
            (exactReverseAliceContextAt side seed) :=
        (Finset.ext_iff.mp hotherPrefix j.val).mpr j.property
      exact congrFun hoppositePrefix ⟨j.val, hj⟩
  refine ⟨hquestion, ?_⟩
  apply (exactHistoryFlagEquiv
    (X := X) (Y := Y) (A := A) (B := B) D).injective
  change
    (⟨seed,
       (exactRevealCode D seed (outcome.1, outcome.2.1),
        (fun j : {j : Fin n // j ∈ D} => outcome.2.2.1 j.val),
        (fun j : {j : Fin n // j ∈ D} => outcome.2.2.2 j.val))⟩ :
      ExactHistoryFlagTuple X Y A B D) =
    (⟨seed,
       (exactRevealCode D seed (outcome'.1, outcome'.2.1),
        (fun j : {j : Fin n // j ∈ D} => outcome'.2.2.1 j.val),
        (fun j : {j : Fin n // j ∈ D} => outcome'.2.2.2 j.val))⟩ :
      ExactHistoryFlagTuple X Y A B D)
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Prod.ext
    · exact hreveal
    apply Prod.ext
    · exact congrArg Prod.fst hflag
    · exact congrArg Prod.snd hflag

theorem exactReverseBob_history_of_marked_context
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (default : X)
    (seed : ExactRemainingSeed D)
    (outcome outcome' : ExactOutcome X Y A B n)
    (same_context :
      exactReverseBobMarkedHistoryContext
          G n S D default seed outcome =
        exactReverseBobMarkedHistoryContext
          G n S D default seed outcome') :
    outcome.2.1 seed.coordinate.val =
        outcome'.2.1 seed.coordinate.val ∧
      exactHistoryCode D (seed, outcome) =
        exactHistoryCode D (seed, outcome') := by
  let side := exactReverseRightSide seed
  let context := exactReverseBobContext seed
  let marker : Fin side.card :=
    context.sideRank
      ⟨seed.coordinate,
        exactReverseRightSide_coordinate_mem seed⟩
  have hfixed :
      (exactReverseBobSourceProjection
        (X := X) (Y := Y) (A := A) (B := B)
        D side (seed, outcome)).1 =
      (exactReverseBobSourceProjection
        (X := X) (Y := Y) (A := A) (B := B)
        D side (seed, outcome')).1 := by
    have h := congrArg
      (fun t : ExactReverseBobNextContext
        X Y A B D (exactReverseRightSide seed) => t.1.1)
      same_context
    simpa only [exactReverseBobMarkedHistoryContext,
      finitePrefixMask, side] using h
  have hflag :
      repeatedConditionedAnswerFlag G n S D outcome =
        repeatedConditionedAnswerFlag G n S D outcome' := by
    have h := congrArg
      (fun t : ExactReverseBobNextContext
        X Y A B D (exactReverseRightSide seed) => t.1.2)
      same_context
    simpa only [exactReverseBobMarkedHistoryContext,
      finitePrefixMask] using h
  have hprefix :
      (finitePrefixMask default marker.castSucc
        (exactReverseBobSourceProjection
          (X := X) (Y := Y) (A := A) (B := B)
          D side (seed, outcome))).2 =
      (finitePrefixMask default marker.castSucc
        (exactReverseBobSourceProjection
          (X := X) (Y := Y) (A := A) (B := B)
          D side (seed, outcome'))).2 := by
    have h := congrArg
      (fun t : ExactReverseBobNextContext
        X Y A B D (exactReverseRightSide seed) => t.2)
      same_context
    simpa only [exactReverseBobMarkedHistoryContext,
      finitePrefixMask, side, context, marker] using h
  have hfields := eq_of_heq (Sigma.mk.inj hfixed).2
  have hac := congrArg (fun t => t.1) hfields
  have hbc := congrArg (fun t => t.2.1) hfields
  have hside := congrArg (fun t => t.2.2.1) hfields
  have hother := congrArg (fun t => t.2.2.2.1) hfields
  have hoppositePrefix := congrArg (fun t => t.2.2.2.2) hfields
  have hquestion :
      outcome.2.1 seed.coordinate.val =
        outcome'.2.1 seed.coordinate.val := by
    have h := congrFun hside
      ⟨seed.coordinate,
        exactReverseRightSide_coordinate_mem seed⟩
    exact h
  have hreveal :
      exactRevealCode D seed
          (outcome.1, outcome.2.1) =
        exactRevealCode D seed
          (outcome'.1, outcome'.2.1) := by
    apply (exactRevealHistoryEquiv
      (X := X) (Y := Y) D seed).injective
    apply Prod.ext
    · exact hac
    apply Prod.ext
    · exact hbc
    apply Prod.ext
    · funext j
      have hotherSide :
          (exactReverseBobContextAt side seed).otherSide =
            exactLeft seed.coordinate seed.partition := by
        change
          (exactReverseBobContextAt
            (exactReverseRightSide seed) seed).otherSide = _
        rw [exactReverseBobContextAt_actual]
        rfl
      have hj :
          j.val ∈
            (exactReverseBobContextAt side seed).otherSide :=
        (Finset.ext_iff.mp hotherSide j.val).mpr j.property
      exact congrFun hother ⟨j.val, hj⟩
    apply Prod.ext
    · funext j
      have hj : j.val ∈ side := by
        change j.val ∈ insert seed.coordinate
          (exactRight seed.coordinate seed.partition)
        exact Finset.mem_insert_of_mem j.property
      exact congrFun hside ⟨j.val, hj⟩
    apply Prod.ext
    · funext j
      have hotherPrefix :
          exactReverseContextOtherPrefix
              (exactReverseBobContextAt side seed) =
            exactLeftPrefix seed := by
        change
          exactReverseContextOtherPrefix
            (exactReverseBobContextAt
              (exactReverseRightSide seed) seed) = _
        rw [exactReverseBobContextAt_actual,
          exactReverseBobContext_otherPrefix]
      have hj :
          j.val ∈ exactReverseContextOtherPrefix
            (exactReverseBobContextAt side seed) :=
        (Finset.ext_iff.mp hotherPrefix j.val).mpr j.property
      exact congrFun hoppositePrefix ⟨j.val, hj⟩
    · funext j
      have hbefore :
          j.val ∈ exactReverseContextPrefixBefore
            context marker := by
        change
          j.val ∈ exactReverseContextPrefixBefore
            (exactReverseBobContext seed)
            ((exactReverseBobContext seed).sideRank
              ⟨seed.coordinate,
                exactReverseRightSide_coordinate_mem seed⟩)
        rw [exactReverseBobContext_prefix_before_marked]
        exact j.property
      have hparts :=
        (exactOrderedSidePrefix_mem_iff
          side context.sideRank marker.castSucc j.val).mp
          hbefore
      let position : Fin side.card :=
        context.sideRank ⟨j.val, hparts.1⟩
      have hlt : position.val < marker.val := by
        simpa only [Fin.val_fin_lt, Fin.val_castSucc] using hparts.2
      have hltCut : position.val < seed.rightCut.val := by
        calc
          position.val < marker.val := hlt
          _ = seed.rightCut.val := by
            exact exactReverseBobContext_marked_rank seed
      have h := congrFun hprefix position
      change outcome.1 j.val.val = outcome'.1 j.val.val
      simpa [finitePrefixMask,
        exactReverseBobSourceProjection,
        exactReverseBobContextAt, side,
        context, marker, position, hlt, hltCut] using h
  refine ⟨hquestion, ?_⟩
  apply (exactHistoryFlagEquiv
    (X := X) (Y := Y) (A := A) (B := B) D).injective
  change
    (⟨seed,
       (exactRevealCode D seed (outcome.1, outcome.2.1),
        (fun j : {j : Fin n // j ∈ D} => outcome.2.2.1 j.val),
        (fun j : {j : Fin n // j ∈ D} => outcome.2.2.2 j.val))⟩ :
      ExactHistoryFlagTuple X Y A B D) =
    (⟨seed,
       (exactRevealCode D seed (outcome'.1, outcome'.2.1),
        (fun j : {j : Fin n // j ∈ D} => outcome'.2.2.1 j.val),
        (fun j : {j : Fin n // j ∈ D} => outcome'.2.2.2 j.val))⟩ :
      ExactHistoryFlagTuple X Y A B D)
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Prod.ext
    · exact hreveal
    apply Prod.ext
    · exact congrArg Prod.fst hflag
    · exact congrArg Prod.snd hflag

theorem exactReverseAliceMarkedHistoryContext_fiber_iff
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (default : Y)
    (seed : ExactRemainingSeed D)
    (outcome reference : ExactOutcome X Y A B n) :
    (exactReverseAliceMarkedHistoryContext
        G n S D default seed outcome =
      exactReverseAliceMarkedHistoryContext
        G n S D default seed reference) ↔
      (outcome.1 seed.coordinate.val,
        exactHistoryCode D (seed, outcome)) =
      (reference.1 seed.coordinate.val,
        exactHistoryCode D (seed, reference)) := by
  constructor
  · intro same
    obtain ⟨hquestion, hhistory⟩ :=
      exactReverseAlice_history_of_marked_context
        G n S D default seed outcome reference same
    exact Prod.ext hquestion hhistory
  · intro same
    apply exactReverseAliceMarkedHistoryContext_eq_of_history
      G n S D default seed outcome reference
    · exact congrArg Prod.snd same
    · exact congrArg Prod.fst same

theorem exactReverseBobMarkedHistoryContext_fiber_iff
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (default : X)
    (seed : ExactRemainingSeed D)
    (outcome reference : ExactOutcome X Y A B n) :
    (exactReverseBobMarkedHistoryContext
        G n S D default seed outcome =
      exactReverseBobMarkedHistoryContext
        G n S D default seed reference) ↔
      (outcome.2.1 seed.coordinate.val,
        exactHistoryCode D (seed, outcome)) =
      (reference.2.1 seed.coordinate.val,
        exactHistoryCode D (seed, reference)) := by
  constructor
  · intro same
    obtain ⟨hquestion, hhistory⟩ :=
      exactReverseBob_history_of_marked_context
        G n S D default seed outcome reference same
    exact Prod.ext hquestion hhistory
  · intro same
    apply exactReverseBobMarkedHistoryContext_eq_of_history
      G n S D default seed outcome reference
    · exact congrArg Prod.snd same
    · exact congrArg Prod.fst same

theorem exactReverseAliceMarkedPosteriorConditional_eq_sourceFiber
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (default : Y)
    (seed : ExactRemainingSeed D)
    (reference : ExactOutcome X Y A B n) :
    jointConditional
        (groupedMass
          (fun outcome : ExactOutcome X Y A B n =>
            (exactReverseAliceMarkedHistoryContext
              G n S D default seed outcome,
              outcome.2.1 seed.coordinate.val))
          (repeatedConditionedOutcomeLaw G n S D))
        (exactReverseAliceMarkedHistoryContext
          G n S D default seed reference) =
      jointConditional
        (groupedMass
          (fun outcome : ExactOutcome X Y A B n =>
            ((outcome.1 seed.coordinate.val,
              exactHistoryCode D (seed, outcome)),
              outcome.2.1 seed.coordinate.val))
          (repeatedConditionedOutcomeLaw G n S D))
        (reference.1 seed.coordinate.val,
          exactHistoryCode D (seed, reference)) := by
  apply jointConditional_groupedMass_eq_of_fiber
    (repeatedConditionedOutcomeLaw G n S D)
    (fun outcome : ExactOutcome X Y A B n =>
      exactReverseAliceMarkedHistoryContext
        G n S D default seed outcome)
    (fun outcome : ExactOutcome X Y A B n =>
      (outcome.1 seed.coordinate.val,
        exactHistoryCode D (seed, outcome)))
    (fun outcome : ExactOutcome X Y A B n =>
      outcome.2.1 seed.coordinate.val)
    (exactReverseAliceMarkedHistoryContext
      G n S D default seed reference)
    (reference.1 seed.coordinate.val,
      exactHistoryCode D (seed, reference))
  intro outcome
  exact exactReverseAliceMarkedHistoryContext_fiber_iff
    G n S D default seed outcome reference

theorem exactReverseBobMarkedPosteriorConditional_eq_sourceFiber
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (default : X)
    (seed : ExactRemainingSeed D)
    (reference : ExactOutcome X Y A B n) :
    jointConditional
        (groupedMass
          (fun outcome : ExactOutcome X Y A B n =>
            (exactReverseBobMarkedHistoryContext
              G n S D default seed outcome,
              outcome.1 seed.coordinate.val))
          (repeatedConditionedOutcomeLaw G n S D))
        (exactReverseBobMarkedHistoryContext
          G n S D default seed reference) =
      jointConditional
        (groupedMass
          (fun outcome : ExactOutcome X Y A B n =>
            ((outcome.2.1 seed.coordinate.val,
              exactHistoryCode D (seed, outcome)),
              outcome.1 seed.coordinate.val))
          (repeatedConditionedOutcomeLaw G n S D))
        (reference.2.1 seed.coordinate.val,
          exactHistoryCode D (seed, reference)) := by
  apply jointConditional_groupedMass_eq_of_fiber
    (repeatedConditionedOutcomeLaw G n S D)
    (fun outcome : ExactOutcome X Y A B n =>
      exactReverseBobMarkedHistoryContext
        G n S D default seed outcome)
    (fun outcome : ExactOutcome X Y A B n =>
      (outcome.2.1 seed.coordinate.val,
        exactHistoryCode D (seed, outcome)))
    (fun outcome : ExactOutcome X Y A B n =>
      outcome.1 seed.coordinate.val)
    (exactReverseBobMarkedHistoryContext
      G n S D default seed reference)
    (reference.2.1 seed.coordinate.val,
      exactHistoryCode D (seed, reference))
  intro outcome
  exact exactReverseBobMarkedHistoryContext_fiber_iff
    G n S D default seed outcome reference

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem reweightedSeedPrefixPrior_as_flagged_pushforward
    {K Ω V : Type*} [Fintype K]
    {h : ℕ}
    (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (projection : K × ExactOutcome X Y A B n →
      Ω × (Fin h → V))
    (t : (Ω × ConditionedAnswerFlag A B D) ×
      (Fin h → V)) :
    reweightedSeedPrefixPrior
        seedLaw G n S D projection t =
      groupedMass
        (fun q : ConditionedAnswerFlag A B D ×
            (K × ExactOutcome X Y A B n) =>
          (((projection q.2).1, q.1), (projection q.2).2))
        (fun q : ConditionedAnswerFlag A B D ×
            (K × ExactOutcome X Y A B n) =>
          finiteUniformWeight
              (ConditionedAnswerFlag A B D) *
            (reweightedSeedPriorEventLaw
              seedLaw G n S).weight q.2)
        t := by
  classical
  change
    groupedMass projection
        (reweightedSeedPriorEventLaw seedLaw G n S).weight
        (t.1.1, t.2) *
      finiteUniformWeight
        (ConditionedAnswerFlag A B D) = _
  calc
    groupedMass projection
        (reweightedSeedPriorEventLaw seedLaw G n S).weight
        (t.1.1, t.2) *
      finiteUniformWeight
        (ConditionedAnswerFlag A B D) =
      finiteUniformWeight
        (ConditionedAnswerFlag A B D) *
        groupedMass projection
          (reweightedSeedPriorEventLaw seedLaw G n S).weight
          (t.1.1, t.2) := by
            ring
    _ = groupedMass
        (fun q : ConditionedAnswerFlag A B D ×
            (K × ExactOutcome X Y A B n) =>
          (q.1, projection q.2))
        (fun q : ConditionedAnswerFlag A B D ×
            (K × ExactOutcome X Y A B n) =>
          finiteUniformWeight
              (ConditionedAnswerFlag A B D) *
            (reweightedSeedPriorEventLaw
              seedLaw G n S).weight q.2)
        (t.1.2, (t.1.1, t.2)) := by
          symm
          exact groupedMass_product_injective_seed
            (fun z : ConditionedAnswerFlag A B D => z)
            (fun _ _ same => same)
            (fun (_ : ConditionedAnswerFlag A B D) q =>
              projection q)
            (fun _ : ConditionedAnswerFlag A B D =>
              finiteUniformWeight
                (ConditionedAnswerFlag A B D))
            (reweightedSeedPriorEventLaw seedLaw G n S).weight
            t.1.2 (t.1.1, t.2)
    _ = groupedMass
        (fun q : ConditionedAnswerFlag A B D ×
            (K × ExactOutcome X Y A B n) =>
          (((projection q.2).1, q.1), (projection q.2).2))
        (fun q : ConditionedAnswerFlag A B D ×
            (K × ExactOutcome X Y A B n) =>
          finiteUniformWeight
              (ConditionedAnswerFlag A B D) *
            (reweightedSeedPriorEventLaw
              seedLaw G n S).weight q.2)
        t := by
          unfold groupedMass
          congr 1
          ext q
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro same
            have hflag : q.1 = t.1.2 :=
              congrArg Prod.fst same
            have hprojection : projection q.2 = (t.1.1, t.2) :=
              congrArg Prod.snd same
            apply Prod.ext
            · apply Prod.ext
              · exact congrArg
                  (fun u : Ω × (Fin h → V) => u.1) hprojection
              · exact hflag
            · exact congrArg
                (fun u : Ω × (Fin h → V) => u.2) hprojection
          · intro same
            have hfixed :
                ((projection q.2).1, q.1) = t.1 :=
              congrArg Prod.fst same
            have hsequence : (projection q.2).2 = t.2 :=
              congrArg Prod.snd same
            apply Prod.ext
            · exact congrArg
                (fun u : Ω × ConditionedAnswerFlag A B D => u.2)
                hfixed
            · apply Prod.ext
              · exact congrArg
                  (fun u : Ω × ConditionedAnswerFlag A B D =>
                    u.1) hfixed
              · exact hsequence

theorem reweightedSeedPrefixPrior_next_flagged_pushforward
    {K Ω V : Type*} [Fintype K] [Fintype Ω] [Fintype V]
    {h : ℕ}
    (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (projection : K × ExactOutcome X Y A B n →
      Ω × (Fin h → V))
    (default : V) (k : Fin h)
    (target :
      ((Ω × ConditionedAnswerFlag A B D) ×
        (Fin h → V)) × V) :
    groupedMass (exactPrefixNextCode default k)
        (reweightedSeedPrefixPrior
          seedLaw G n S D projection) target =
      groupedMass
        (fun q : ConditionedAnswerFlag A B D ×
            (K × ExactOutcome X Y A B n) =>
          exactPrefixNextCode default k
            (((projection q.2).1, q.1), (projection q.2).2))
        (fun q : ConditionedAnswerFlag A B D ×
            (K × ExactOutcome X Y A B n) =>
          finiteUniformWeight
              (ConditionedAnswerFlag A B D) *
            (reweightedSeedPriorEventLaw
              seedLaw G n S).weight q.2)
        target := by
  classical
  let augmented :
      ConditionedAnswerFlag A B D ×
        (K × ExactOutcome X Y A B n) →
          (Ω × ConditionedAnswerFlag A B D) ×
            (Fin h → V) :=
    fun q => (((projection q.2).1, q.1), (projection q.2).2)
  let weight :
      ConditionedAnswerFlag A B D ×
        (K × ExactOutcome X Y A B n) → ℝ :=
    fun q =>
      finiteUniformWeight
          (ConditionedAnswerFlag A B D) *
        (reweightedSeedPriorEventLaw
          seedLaw G n S).weight q.2
  have hprior :
      reweightedSeedPrefixPrior
          seedLaw G n S D projection =
        groupedMass augmented weight := by
    funext t
    exact reweightedSeedPrefixPrior_as_flagged_pushforward
      seedLaw G n S D projection t
  rw [hprior]
  exact congrFun
    (groupedMass_comp augmented
      (exactPrefixNextCode default k) weight) target

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

theorem finiteGroupedExpectation_eq_atom_sum
    {Ω C : Type*} [Fintype Ω] [Fintype C] [DecidableEq C]
    (code : Ω → C) (mass : Ω → ℝ) (value : C → ℝ) :
    (∑ target : C, groupedMass code mass target * value target) =
      ∑ outcome : Ω, mass outcome * value (code outcome) := by
  classical
  unfold groupedMass
  calc
    (∑ target : C,
      (∑ outcome ∈
        (Finset.univ.filter fun outcome : Ω =>
          code outcome = target), mass outcome) * value target) =
      ∑ target : C,
        ∑ outcome ∈
          (Finset.univ.filter fun outcome : Ω =>
            code outcome = target),
          mass outcome * value (code outcome) := by
        apply Finset.sum_congr rfl
        intro target _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro outcome houtcome
        have hcode : code outcome = target :=
          (Finset.mem_filter.mp houtcome).2
        rw [hcode]
    _ = ∑ outcome : Ω, mass outcome * value (code outcome) :=
      Finset.sum_fiberwise Finset.univ code
        (fun outcome => mass outcome * value (code outcome))

theorem jointFirstMarginal_groupedContextNext
    {Ω C V : Type*} [Fintype Ω] [Fintype V]
    [DecidableEq C] [DecidableEq (C × V)]
    (context : Ω → C) (next : Ω → V)
    (mass : Ω → ℝ) (target : C) :
    jointFirstMarginal
        (groupedMass
          (fun outcome => (context outcome, next outcome)) mass)
        target =
      groupedMass context mass target := by
  classical
  unfold jointFirstMarginal groupedMass
  calc
    (∑ value : V,
      ∑ outcome ∈
        (Finset.univ.filter fun outcome : Ω =>
          (context outcome, next outcome) = (target, value)),
        mass outcome) =
      ∑ value : V,
        ∑ outcome ∈
          ((Finset.univ.filter fun outcome : Ω =>
            context outcome = target).filter
              fun outcome => next outcome = value),
          mass outcome := by
        apply Finset.sum_congr rfl
        intro value _
        congr 1
        ext outcome
        simp only [Prod.mk.injEq, mem_filter, mem_univ, true_and]
    _ = ∑ outcome ∈
        (Finset.univ.filter fun outcome : Ω =>
          context outcome = target), mass outcome :=
      Finset.sum_fiberwise
        (Finset.univ.filter fun outcome : Ω =>
          context outcome = target)
        next mass

theorem finiteNextInformation_eq_atom_sum
    {Ω C V : Type*} [Fintype Ω] [Fintype C] [Fintype V]
    [DecidableEq (C × V)]
    (context : Ω → C) (next : Ω → V)
    (mass : Ω → ℝ) (reference : C → V → ℝ) :
    (∑ target : C,
      jointFirstMarginal
          (groupedMass
            (fun outcome => (context outcome, next outcome)) mass)
          target *
        finiteRelativeEntropy
          (jointConditional
            (groupedMass
              (fun outcome => (context outcome, next outcome)) mass)
            target)
          (reference target)) =
      ∑ outcome : Ω,
        mass outcome *
          finiteRelativeEntropy
            (jointConditional
              (groupedMass
                (fun source => (context source, next source)) mass)
              (context outcome))
            (reference (context outcome)) := by
  simp_rw [jointFirstMarginal_groupedContextNext
    context next mass]
  exact finiteGroupedExpectation_eq_atom_sum
    context mass
    (fun target =>
      finiteRelativeEntropy
        (jointConditional
          (groupedMass
            (fun outcome => (context outcome, next outcome)) mass)
          target)
        (reference target))

theorem jointAtom_eq_zero_of_firstMarginal_zero
    {I V : Type*} [Fintype V]
    (mass : I × V → ℝ)
    (nonnegative : ∀ point, 0 ≤ mass point)
    (index : I)
    (zero : jointFirstMarginal mass index = 0)
    (value : V) :
    mass (index, value) = 0 := by
  unfold jointFirstMarginal at zero
  exact
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun value _ => nonnegative (index, value))).mp
      zero value (Finset.mem_univ value)

theorem nestedFirstMarginal_mul_conditional
    {I R V : Type*} [Fintype R] [Fintype V]
    (mass : I × (R × V) → ℝ)
    (nonnegative : ∀ point, 0 ≤ mass point)
    (index : I) (history : R) :
    jointFirstMarginal mass index *
        jointFirstMarginal (jointConditional mass index) history =
    jointFirstMarginal
        (fun point : (I × R) × V =>
          mass (point.1.1, (point.1.2, point.2)))
        (index, history) := by
  unfold jointFirstMarginal jointConditional
  change
    (∑ point : R × V, mass (index, point)) *
        (∑ value : V,
          mass (index, (history, value)) /
            (∑ point : R × V, mass (index, point))) =
      ∑ value : V, mass (index, (history, value))
  rw [← Finset.sum_div]
  by_cases houter : (∑ point : R × V, mass (index, point)) = 0
  · have hinner : (∑ value : V, mass (index, (history, value))) = 0 := by
      apply Finset.sum_eq_zero
      intro value _
      exact jointAtom_eq_zero_of_firstMarginal_zero
        mass nonnegative index houter (history, value)
    simp only [houter, hinner, div_zero, mul_zero]
  · field_simp [houter]

theorem nestedConditional_eq_flat
    {I R V : Type*} [Fintype R] [Fintype V]
    (mass : I × (R × V) → ℝ)
    (nonnegative : ∀ point, 0 ≤ mass point)
    (index : I) (history : R) :
    jointConditional (jointConditional mass index) history =
      jointConditional
        (fun point : (I × R) × V =>
          mass (point.1.1, (point.1.2, point.2)))
        (index, history) := by
  funext value
  unfold jointConditional jointFirstMarginal
  rw [← Finset.sum_div]
  by_cases houter : (∑ point : R × V, mass (index, point)) = 0
  · have hatom : mass (index, (history, value)) = 0 :=
      jointAtom_eq_zero_of_firstMarginal_zero
        mass nonnegative index houter (history, value)
    simp only [hatom, houter, div_zero, zero_div]
  · by_cases hhistory : (∑ v : V, mass (index, (history, v))) = 0
    · have hatom : mass (index, (history, value)) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun v _ => nonnegative (index, (history, v)))).mp
          hhistory value (Finset.mem_univ value)
      simp only [hatom, zero_div, hhistory, div_zero]
    · field_simp [houter, hhistory]

theorem finiteNestedNextInformation_eq_atom_sum
    {I R V : Type*} [Fintype I] [Fintype R] [Fintype V]
    (mass : I × (R × V) → ℝ)
    (nonnegative : ∀ point, 0 ≤ mass point)
    (reference : I → V → ℝ) :
    (∑ index : I,
      jointFirstMarginal mass index *
        (∑ history : R,
          jointFirstMarginal
              (jointConditional mass index) history *
            finiteRelativeEntropy
              (jointConditional
                (jointConditional mass index) history)
              (reference index))) =
      ∑ point : I × (R × V),
        mass point *
          finiteRelativeEntropy
            (jointConditional
              (fun atom : (I × R) × V =>
                mass (atom.1.1, (atom.1.2, atom.2)))
              (point.1, point.2.1))
            (reference point.1) := by
  classical
  simp_rw [Finset.mul_sum]
  simp_rw [← mul_assoc,
    nestedFirstMarginal_mul_conditional mass nonnegative,
    nestedConditional_eq_flat mass nonnegative]
  let flat : (I × R) × V → ℝ :=
    fun atom => mass (atom.1.1, (atom.1.2, atom.2))
  let score : I × R → ℝ :=
    fun target =>
      finiteRelativeEntropy
        (jointConditional flat target)
        (reference target.1)
  have h := finiteGroupedExpectation_eq_atom_sum
    (fun atom : (I × R) × V => atom.1) flat score
  have hfirst (target : I × R) :
      groupedMass
          (fun atom : (I × R) × V => atom.1)
          flat target =
        jointFirstMarginal flat target := by
    exact congrFun (groupedMass_first flat) target
  simp_rw [hfirst] at h
  change
    (∑ index : I, ∑ history : R,
      jointFirstMarginal flat (index, history) *
        score (index, history)) = _
  calc
    (∑ index : I, ∑ history : R,
      jointFirstMarginal flat (index, history) *
        score (index, history)) =
      ∑ target : I × R,
        jointFirstMarginal flat target * score target := by
          rw [Fintype.sum_prod_type]
    _ = ∑ atom : (I × R) × V,
        flat atom * score atom.1 := h
    _ = ∑ point : I × (R × V),
        mass point *
          finiteRelativeEntropy
            (jointConditional
              (fun atom : (I × R) × V =>
                mass (atom.1.1, (atom.1.2, atom.2)))
              (point.1, point.2.1))
            (reference point.1) := by
          simp only [flat, score, Fintype.sum_prod_type]

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem reweightedSeedPrefixJoint_as_actual_flagged_pushforward
    {K Ω V : Type*} [Fintype K]
    {h : ℕ}
    (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (projection : K × ExactOutcome X Y A B n →
      Ω × (Fin h → V))
    (target : (Ω × ConditionedAnswerFlag A B D) ×
      (Fin h → V)) :
    reweightedSeedPrefixJoint
        seedLaw G n S D projection target =
      groupedMass
        (fun point : K × ExactOutcome X Y A B n =>
          (((projection point).1,
            repeatedConditionedAnswerFlag G n S D point.2),
            (projection point).2))
        (reweightedSeedPosterior seedLaw G n S D)
        target := by
  classical
  let source := K × ExactOutcome X Y A B n
  let leftTarget := (Ω × (Fin h → V)) × ConditionedAnswerFlag A B D
  let rightTarget := (Ω × ConditionedAnswerFlag A B D) × (Fin h → V)
  let equivalence : leftTarget ≃ rightTarget := exactSourcePrefixFlagEquiv
  let mass : source → ℝ := reweightedSeedPosterior seedLaw G n S D
  let leftProjection : source → leftTarget := fun point =>
    (projection point, repeatedConditionedAnswerFlag G n S D point.2)
  let rightProjection : source → rightTarget := fun point =>
    (((projection point).1,
      repeatedConditionedAnswerFlag G n S D point.2),
      (projection point).2)
  have leftNormalization :
      reweightedSeedPrefixJoint seedLaw G n S D projection target =
        @groupedMass source inferInstance leftTarget
          (fun a b => Classical.propDecidable (a = b))
          leftProjection mass (equivalence.symm target) := by
    unfold reweightedSeedPrefixJoint reweightedSeedFlaggedProjectionLaw
    exact congrFun
      (exactGroupedMass_decidableEq_irrel _ _ leftProjection mass)
      (equivalence.symm target)
  have rightNormalization :
      @groupedMass source inferInstance rightTarget
          (fun a b => Classical.propDecidable (a = b))
          rightProjection mass target =
        groupedMass rightProjection mass target := by
    exact congrFun
      (exactGroupedMass_decidableEq_irrel _ _ rightProjection mass) target
  calc
    reweightedSeedPrefixJoint seedLaw G n S D projection target =
        @groupedMass source inferInstance leftTarget
          (fun a b => Classical.propDecidable (a = b))
          leftProjection mass (equivalence.symm target) := leftNormalization
    _ = ∑ point,
          @ite ℝ (leftProjection point = equivalence.symm target)
            (Classical.propDecidable _) (mass point) 0 :=
      @groupedMass_eq_sum_ite source inferInstance
        leftTarget (fun a b => Classical.propDecidable (a = b))
        leftProjection mass (equivalence.symm target)
    _ = ∑ point,
          @ite ℝ (rightProjection point = target)
            (Classical.propDecidable _) (mass point) 0 := by
      apply Finset.sum_congr rfl
      intro point _
      have hfiber :
          leftProjection point = equivalence.symm target ↔
            rightProjection point = target := by
        change
          leftProjection point = equivalence.symm target ↔
            equivalence (leftProjection point) = target
        constructor
        · intro same
          rw [same, equivalence.apply_symm_apply]
        · intro same
          exact equivalence.eq_symm_apply.mpr same
      by_cases hleft : leftProjection point = equivalence.symm target
      · rw [ite_eq_left hleft, ite_eq_left (hfiber.mp hleft)]
      · have hright : ¬ rightProjection point = target :=
          fun h => hleft (hfiber.mpr h)
        rw [ite_eq_right hleft, ite_eq_right hright]
    _ = @groupedMass source inferInstance rightTarget
          (fun a b => Classical.propDecidable (a = b))
          rightProjection mass target :=
      (@groupedMass_eq_sum_ite source inferInstance
        rightTarget (fun a b => Classical.propDecidable (a = b))
        rightProjection mass target).symm
    _ = groupedMass rightProjection mass target := rightNormalization

theorem exactAliceSourceConditionalInformation_eq_atom_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D) :
    exactAliceSourceConditionalInformation G n S D base =
      ∑ point : (SourceRemainingCoordinate D × X) ×
          (ExactHistoryFlag X Y A B D × Y),
        exactAliceInformationPosterior G n S D point *
          finiteRelativeEntropy
            (jointConditional
              (fun atom :
                ((SourceRemainingCoordinate D × X) ×
                    ExactHistoryFlag X Y A B D) × Y =>
                exactAliceInformationPosterior G n S D
                  (atom.1.1, (atom.1.2, atom.2)))
              (point.1, point.2.1))
            (G.conditionalYGivenX point.1.2) := by
  have hnonnegative :
      ∀ point,
        0 ≤ exactAliceInformationPosterior
          G n S D point := by
    intro point
    exact exactLocallySampleableLaw_nonneg
      G n S D positive
      ((exactAliceInformationEquiv
        (X := X) (Y := Y) (A := A) (B := B) D).symm point)
  calc
    exactAliceSourceConditionalInformation G n S D base =
      ∑ index : SourceRemainingCoordinate D × X,
        jointFirstMarginal
          (exactAliceInformationPosterior G n S D) index *
          (∑ history : ExactHistoryFlag X Y A B D,
            jointFirstMarginal
                (jointConditional
                  (exactAliceInformationPosterior G n S D)
                  index) history *
              finiteRelativeEntropy
                (jointConditional
                  (jointConditional
                    (exactAliceInformationPosterior G n S D)
                    index) history)
                (G.conditionalYGivenX index.2)) :=
      exactAliceSourceConditionalInformation_eq_question
        G n S D remaining positive base
    _ = _ :=
      finiteNestedNextInformation_eq_atom_sum
        (exactAliceInformationPosterior G n S D)
        hnonnegative
        (fun index : SourceRemainingCoordinate D × X =>
          G.conditionalYGivenX index.2)

theorem exactBobSourceConditionalInformation_eq_atom_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D) :
    exactBobSourceConditionalInformation G n S D base =
      ∑ point : (SourceRemainingCoordinate D × Y) ×
          (ExactHistoryFlag X Y A B D × X),
        exactBobInformationPosterior G n S D point *
          finiteRelativeEntropy
            (jointConditional
              (fun atom :
                ((SourceRemainingCoordinate D × Y) ×
                    ExactHistoryFlag X Y A B D) × X =>
                exactBobInformationPosterior G n S D
                  (atom.1.1, (atom.1.2, atom.2)))
              (point.1, point.2.1))
            (G.conditionalXGivenY point.1.2) := by
  have hnonnegative :
      ∀ point,
        0 ≤ exactBobInformationPosterior
          G n S D point := by
    intro point
    exact exactLocallySampleableLaw_nonneg
      G n S D positive
      ((exactBobInformationEquiv
        (X := X) (Y := Y) (A := A) (B := B) D).symm point)
  calc
    exactBobSourceConditionalInformation G n S D base =
      ∑ index : SourceRemainingCoordinate D × Y,
        jointFirstMarginal
          (exactBobInformationPosterior G n S D) index *
          (∑ history : ExactHistoryFlag X Y A B D,
            jointFirstMarginal
                (jointConditional
                  (exactBobInformationPosterior G n S D)
                  index) history *
              finiteRelativeEntropy
                (jointConditional
                  (jointConditional
                    (exactBobInformationPosterior G n S D)
                    index) history)
                (G.conditionalXGivenY index.2)) :=
      exactBobSourceConditionalInformation_eq_question
        G n S D remaining positive base
    _ = _ :=
      finiteNestedNextInformation_eq_atom_sum
        (exactBobInformationPosterior G n S D)
        hnonnegative
        (fun index : SourceRemainingCoordinate D × Y =>
          G.conditionalXGivenY index.2)

end

end QuantumParallelRepetition

end
