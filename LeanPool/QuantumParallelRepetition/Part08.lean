/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.QuantumParallelRepetition.Part07

/-! # Quantum parallel repetition, part 08 -/

noncomputable section

namespace QuantumParallelRepetition

open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem exactPermutationOutputUniformPushforward
    {R : Type*} [Fintype R] [DecidableEq R]
    (denominator : ℕ) (numerator : R → ℕ)
    (normalized : (∑ r, numerator r) = denominator)
    (nonempty : (rationalMarked denominator numerator).Nonempty)
    (letter : R) :
    groupedMass
        (rationalPermutationOutput denominator numerator nonempty)
        (fun _ : Equiv.Perm (R × Fin denominator) =>
          (1 : ℝ) / (Fintype.card
            (Equiv.Perm (R × Fin denominator)) : ℝ)) letter =
      (numerator letter : ℝ) / denominator := by
  classical
  calc
    groupedMass
        (rationalPermutationOutput denominator numerator nonempty)
        (fun _ : Equiv.Perm (R × Fin denominator) =>
          (1 : ℝ) / (Fintype.card
            (Equiv.Perm (R × Fin denominator)) : ℝ)) letter =
      uniformPermutationProbability
        (fun permutation : Equiv.Perm (R × Fin denominator) =>
          rationalPermutationOutput denominator numerator nonempty
            permutation = letter) := by
        rw [exactUniformPermutationProbability_eq_indicator_sum]
        unfold groupedMass
        rw [Finset.sum_filter, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro permutation _
        by_cases selected :
          rationalPermutationOutput denominator numerator nonempty
            permutation = letter
        · simp only [selected, ↓reduceIte, one_div]
        · simp only [selected, ↓reduceIte, zero_div]
    _ = (numerator letter : ℝ) / denominator :=
      rationalPermutationOutput_probability denominator numerator
        normalized nonempty letter

theorem exactPermutationOutputUniformExpectation
    {R : Type*} [Fintype R] [DecidableEq R]
    (denominator : ℕ) (numerator : R → ℕ)
    (normalized : (∑ r, numerator r) = denominator)
    (nonempty : (rationalMarked denominator numerator).Nonempty)
    (value : R → ℝ) :
    (∑ permutation : Equiv.Perm (R × Fin denominator),
      ((1 : ℝ) /
        (Fintype.card (Equiv.Perm (R × Fin denominator)) : ℝ)) *
          value (rationalPermutationOutput denominator numerator
            nonempty permutation)) =
      ∑ letter : R, ((numerator letter : ℝ) / denominator) *
        value letter := by
  calc
    (∑ permutation : Equiv.Perm (R × Fin denominator),
      ((1 : ℝ) /
        (Fintype.card (Equiv.Perm (R × Fin denominator)) : ℝ)) *
          value (rationalPermutationOutput denominator numerator
            nonempty permutation)) =
      ∑ letter : R,
        groupedMass
          (rationalPermutationOutput denominator numerator nonempty)
          (fun _ : Equiv.Perm (R × Fin denominator) =>
            (1 : ℝ) /
              (Fintype.card (Equiv.Perm
                (R × Fin denominator)) : ℝ)) letter * value letter :=
        (finiteGroupedExpectation_eq_atom_sum
          (rationalPermutationOutput denominator numerator nonempty)
          (fun _ : Equiv.Perm (R × Fin denominator) =>
            (1 : ℝ) /
              (Fintype.card (Equiv.Perm
                (R × Fin denominator)) : ℝ)) value).symm
    _ = ∑ letter : R,
      ((numerator letter : ℝ) / denominator) * value letter := by
        simp_rw [exactPermutationOutputUniformPushforward
          denominator numerator normalized nonempty]

/-- The product encoding of exact source alice sample. -/
def exactSourceAliceSampleTuple
    {n : ℕ} (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ k,
      (rationalMarked denominator (numerator k)).Nonempty)
    (outcome :
      ExactSourceSharedFlag X Y A B D denominator × (X × Y)) :
    ExactLocallySampleableTuple X Y A B D :=
  (outcome.1.1, outcome.2.1, outcome.2.2,
    exactSourceAlicePermutationHistory
      D denominator numerator nonempty outcome.1 outcome.2.1)

theorem exactSourceAliceSampleTuple_expectation
    (G : Game X Y A B) (n : ℕ) (D : Finset (Fin n))
    (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (normalized : ∀ k, (∑ r, numerator k r) = denominator)
    (nonempty : ∀ k,
      (rationalMarked denominator (numerator k)).Nonempty)
    (value : ExactLocallySampleableTuple X Y A B D → ℝ) :
    (∑ outcome :
      ExactSourceSharedFlag X Y A B D denominator × (X × Y),
      flaggedQuestionWeight G
        (exactSourceSharedFlagWeight D denominator) outcome *
          value (exactSourceAliceSampleTuple
            D denominator numerator nonempty outcome)) =
      ∑ history : ExactLocallySampleableTuple X Y A B D,
        exactLocallySampleableJARounded
          G n D denominator numerator history * value history := by
  classical
  have point (coordinate : SourceRemainingCoordinate D)
      (x : X) (y : Y) :
      (∑ permutation :
        Equiv.Perm
          (ExactHistoryFlag X Y A B D × Fin denominator),
        ((1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
          (1 / (Fintype.card
            (Equiv.Perm
              (ExactHistoryFlag X Y A B D ×
                Fin denominator)) : ℝ))) *
          G.questionWeight x y *
          value (coordinate, x, y,
            rationalPermutationOutput denominator
              (numerator (.inl (coordinate, x)))
              (nonempty (.inl (coordinate, x))) permutation)) =
        ∑ history : ExactHistoryFlag X Y A B D,
          (G.questionWeight x y *
            ((numerator (.inl (coordinate, x)) history : ℝ) /
              denominator) /
              (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
            value (coordinate, x, y, history) := by
    have output := exactPermutationOutputUniformExpectation
      denominator (numerator (.inl (coordinate, x)))
      (normalized (.inl (coordinate, x)))
      (nonempty (.inl (coordinate, x)))
      (fun history : ExactHistoryFlag X Y A B D =>
        value (coordinate, x, y, history))
    calc
      (∑ permutation :
        Equiv.Perm
          (ExactHistoryFlag X Y A B D × Fin denominator),
        ((1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
          (1 / (Fintype.card
            (Equiv.Perm
              (ExactHistoryFlag X Y A B D ×
                Fin denominator)) : ℝ))) *
          G.questionWeight x y *
          value (coordinate, x, y,
            rationalPermutationOutput denominator
              (numerator (.inl (coordinate, x)))
              (nonempty (.inl (coordinate, x))) permutation)) =
        (G.questionWeight x y /
          (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
          (∑ permutation :
            Equiv.Perm
              (ExactHistoryFlag X Y A B D × Fin denominator),
            ((1 : ℝ) /
              (Fintype.card
                (Equiv.Perm
                  (ExactHistoryFlag X Y A B D ×
                    Fin denominator)) : ℝ)) *
              value (coordinate, x, y,
                rationalPermutationOutput denominator
                  (numerator (.inl (coordinate, x)))
                  (nonempty (.inl (coordinate, x))) permutation)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro permutation _
            ring
      _ = (G.questionWeight x y /
          (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
          (∑ history : ExactHistoryFlag X Y A B D,
            ((numerator (.inl (coordinate, x)) history : ℝ) /
              denominator) * value (coordinate, x, y, history)) := by
            rw [output]
      _ = ∑ history : ExactHistoryFlag X Y A B D,
          (G.questionWeight x y *
            ((numerator (.inl (coordinate, x)) history : ℝ) /
              denominator) /
              (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
            value (coordinate, x, y, history) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro history _
            ring
  simp only [flaggedQuestionWeight,
    exactSourceSharedFlagWeight,
    exactSourceAliceSampleTuple,
    exactSourceAlicePermutationHistory,
    exactLocallySampleableJARounded,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro coordinate _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  exact point coordinate x y

theorem exactSourceAliceSampleTuple_groupedMass
    (G : Game X Y A B) (n : ℕ) (D : Finset (Fin n))
    (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (normalized : ∀ k, (∑ r, numerator k r) = denominator)
    (nonempty : ∀ k,
      (rationalMarked denominator (numerator k)).Nonempty)
    (history : ExactLocallySampleableTuple X Y A B D) :
    groupedMass
      (exactSourceAliceSampleTuple
        D denominator numerator nonempty)
      (flaggedQuestionWeight G
        (exactSourceSharedFlagWeight D denominator)) history =
      exactLocallySampleableJARounded
        G n D denominator numerator history := by
  classical
  have expectation := exactSourceAliceSampleTuple_expectation
    G n D denominator numerator normalized nonempty
    (fun candidate => if candidate = history then (1 : ℝ) else 0)
  simpa only [groupedMass, sum_filter, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ,
    ↓reduceIte] using expectation

end

section

open scoped BigOperators

open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {Ω T : Type*} [Fintype Ω] [Fintype T] [DecidableEq T]

private def exactFiniteFiberLift
    (projection : Ω → T) (original : Ω → ℝ) (target : T → ℝ)
    (outcome : Ω) : ℝ :=
  target (projection outcome) * original outcome /
    groupedMass projection original (projection outcome)

omit [Fintype T] in
theorem exactFiniteFiberLift_groupedMass
    (projection : Ω → T) (original : Ω → ℝ) (target : T → ℝ)
    (supported : ∀ point,
      groupedMass projection original point = 0 → target point = 0)
    (point : T) :
    groupedMass projection
      (exactFiniteFiberLift projection original target) point =
        target point := by
  classical
  change
    (∑ outcome ∈
      (Finset.univ.filter fun outcome : Ω =>
        projection outcome = point),
      exactFiniteFiberLift projection original target outcome) =
        target point
  calc
    (∑ outcome ∈
      (Finset.univ.filter fun outcome : Ω =>
        projection outcome = point),
      exactFiniteFiberLift projection original target outcome) =
      ∑ outcome ∈
        (Finset.univ.filter fun outcome : Ω =>
          projection outcome = point),
        target point * original outcome /
          groupedMass projection original point := by
          apply Finset.sum_congr rfl
          intro outcome member
          have same : projection outcome = point :=
            (Finset.mem_filter.mp member).2
          simp only [exactFiniteFiberLift, same]
    _ = target point * groupedMass projection original point /
          groupedMass projection original point := by
          rw [← Finset.sum_div, ← Finset.mul_sum]
          rfl
    _ = target point := by
          by_cases empty : groupedMass projection original point = 0
          · simp only [supported point empty, empty, mul_zero, div_zero]
          · field_simp

theorem exactFiniteFiberLift_expectation
    (projection : Ω → T) (original : Ω → ℝ) (target : T → ℝ)
    (supported : ∀ point,
      groupedMass projection original point = 0 → target point = 0)
    (value : T → ℝ) :
    (∑ outcome : Ω,
      exactFiniteFiberLift projection original target outcome *
        value (projection outcome)) =
      ∑ point : T, target point * value point := by
  calc
    (∑ outcome : Ω,
      exactFiniteFiberLift projection original target outcome *
        value (projection outcome)) =
      ∑ point : T,
        groupedMass projection
          (exactFiniteFiberLift projection original target) point *
            value point :=
      (finiteGroupedExpectation_eq_atom_sum projection
        (exactFiniteFiberLift projection original target)
        value).symm
    _ = ∑ point : T, target point * value point := by
      simp_rw [exactFiniteFiberLift_groupedMass
        projection original target supported]

omit [Fintype T] in
theorem exactFiniteFiberLift_absolute_groupedMass
    (projection : Ω → T) (original : Ω → ℝ) (target : T → ℝ)
    (original_nonnegative : ∀ outcome, 0 ≤ original outcome)
    (supported : ∀ point,
      groupedMass projection original point = 0 → target point = 0)
    (point : T) :
    groupedMass projection
      (fun outcome =>
        |original outcome -
          exactFiniteFiberLift projection original target outcome|)
      point =
        |groupedMass projection original point - target point| := by
  classical
  by_cases empty : groupedMass projection original point = 0
  · have vanishes : ∀ outcome,
        outcome ∈ (Finset.univ.filter fun outcome : Ω =>
          projection outcome = point) → original outcome = 0 := by
      intro outcome member
      exact
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun outcome _ => original_nonnegative outcome)).mp
          (show
            (∑ outcome ∈
              (Finset.univ.filter fun outcome : Ω =>
                projection outcome = point),
              original outcome) = 0 from empty)
          outcome member
    unfold groupedMass
    rw [Finset.sum_eq_zero (fun outcome member => by
      have zero := vanishes outcome member
      simp only [zero, exactFiniteFiberLift, mul_zero, zero_div, sub_self, abs_zero])]
    simpa only [supported point empty, sub_zero, abs_zero, groupedMass] using
      (congrArg abs empty).symm
  · have pointwise (outcome : Ω)
        (member : outcome ∈
          (Finset.univ.filter fun outcome : Ω =>
            projection outcome = point)) :
        |original outcome -
          exactFiniteFiberLift projection original target outcome| =
          original outcome *
            |groupedMass projection original point - target point| /
              groupedMass projection original point := by
      have same : projection outcome = point :=
        (Finset.mem_filter.mp member).2
      have mass_nonnegative :
          0 ≤ groupedMass projection original point := by
        unfold groupedMass
        exact Finset.sum_nonneg
          (fun outcome _ => original_nonnegative outcome)
      have mass_positive :
          0 < groupedMass projection original point :=
        lt_of_le_of_ne mass_nonnegative (Ne.symm empty)
      rw [exactFiniteFiberLift, same]
      rw [show original outcome -
          target point * original outcome /
            groupedMass projection original point =
          original outcome *
            (groupedMass projection original point - target point) /
              groupedMass projection original point by
            field_simp]
      rw [abs_div, abs_mul,
        abs_of_nonneg (original_nonnegative outcome),
        abs_of_pos mass_positive]
    change
      (∑ outcome ∈
        (Finset.univ.filter fun outcome : Ω =>
          projection outcome = point),
        |original outcome -
          exactFiniteFiberLift projection original target outcome|) =
        |groupedMass projection original point - target point|
    calc
      (∑ outcome ∈
        (Finset.univ.filter fun outcome : Ω =>
          projection outcome = point),
        |original outcome -
          exactFiniteFiberLift projection original target outcome|) =
        ∑ outcome ∈
          (Finset.univ.filter fun outcome : Ω =>
            projection outcome = point),
          original outcome *
            |groupedMass projection original point - target point| /
              groupedMass projection original point := by
          apply Finset.sum_congr rfl
          exact pointwise
      _ = groupedMass projection original point *
          |groupedMass projection original point - target point| /
            groupedMass projection original point := by
          rw [← Finset.sum_div, ← Finset.sum_mul]
          rfl
      _ = |groupedMass projection original point - target point| := by
          field_simp

theorem exactFiniteFiberLift_totalVariation
    (projection : Ω → T) (original : Ω → ℝ) (target : T → ℝ)
    (original_nonnegative : ∀ outcome, 0 ≤ original outcome)
    (supported : ∀ point,
      groupedMass projection original point = 0 → target point = 0) :
    finiteTotalVariation original
      (exactFiniteFiberLift projection original target) =
        finiteTotalVariation (groupedMass projection original) target := by
  unfold finiteTotalVariation
  congr 1
  calc
    (∑ outcome : Ω,
      |original outcome -
        exactFiniteFiberLift projection original target outcome|) =
      ∑ point : T,
        groupedMass projection
          (fun outcome =>
            |original outcome -
              exactFiniteFiberLift projection original target outcome|)
          point := by
        simpa only [mul_one] using
          (finiteGroupedExpectation_eq_atom_sum projection
            (fun outcome =>
              |original outcome -
                exactFiniteFiberLift
                  projection original target outcome|)
            (fun _ => (1 : ℝ))).symm
    _ = ∑ point : T,
      |groupedMass projection original point - target point| := by
        simp_rw [exactFiniteFiberLift_absolute_groupedMass
          projection original target original_nonnegative supported]

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

theorem existsCommonSupportPreservingRationalApproximations
    {I K : Type*} [Fintype I] [Finite K]
    (base : I) (probability : K → I → ℝ)
    (nonnegative : ∀ index letter, 0 ≤ probability index letter)
    (normalized : ∀ index, (∑ letter, probability index letter) = 1)
    {gamma : ℝ} (gamma_positive : 0 < gamma) :
    ∃ denominator : ℕ, 0 < denominator ∧
      ∃ numerator : K → I → ℕ,
        (∀ index, (∑ letter, numerator index letter) = denominator) ∧
        (∀ index, finiteTotalVariation
          (probability index)
          (fun letter => (numerator index letter : ℝ) / denominator) <
            gamma) ∧
        (∀ index letter,
          0 < probability index letter → 0 < numerator index letter) := by
  classical
  let _ := Fintype.ofFinite K
  let supportCost : ℝ :=
    ∑ index : K, ∑ letter : I,
      if 0 < probability index letter then
        1 / probability index letter
      else 0
  have cost_nonnegative : 0 ≤ supportCost := by
    dsimp [supportCost]
    apply Finset.sum_nonneg
    intro index _
    apply Finset.sum_nonneg
    intro letter _
    split_ifs with positive
    · exact (one_div_pos.mpr positive).le
    · exact le_rfl
  have cardinal_positive : 0 < (Fintype.card I : ℝ) := by
    exact_mod_cast
      (Fintype.card_pos_iff.mpr ⟨base⟩ : 0 < Fintype.card I)
  have ratio_positive :
      0 < (Fintype.card I : ℝ) / gamma :=
    div_pos cardinal_positive gamma_positive
  obtain ⟨denominator, denominator_large⟩ :=
    exists_nat_gt ((Fintype.card I : ℝ) / gamma + supportCost)
  have denominator_real_positive : 0 < (denominator : ℝ) :=
    lt_of_lt_of_le
      (lt_of_lt_of_le ratio_positive
        (le_add_of_nonneg_right cost_nonnegative))
      denominator_large.le
  have denominator_positive : 0 < denominator := by
    exact_mod_cast denominator_real_positive
  have approximation_budget :
      (Fintype.card I : ℝ) / denominator < gamma := by
    apply (div_lt_iff₀ denominator_real_positive).mpr
    have reciprocal_bound :
        (Fintype.card I : ℝ) / gamma < (denominator : ℝ) :=
      lt_of_le_of_lt
        (le_add_of_nonneg_right cost_nonnegative)
        denominator_large
    have crossed :=
      (div_lt_iff₀ gamma_positive).mp reciprocal_bound
    linarith
  refine ⟨denominator, denominator_positive,
    fun index => distributionRoundedNumerator
      base denominator (probability index), ?_, ?_, ?_⟩
  · intro index
    exact distributionRoundedNumerator_sum
      base denominator (probability index)
      (nonnegative index) (normalized index)
  · intro index
    change finiteTotalVariation
      (probability index)
      (distributionRoundedProbability
        base denominator (probability index)) < gamma
    exact (distributionRoundedProbability_totalVariation_le
      base denominator denominator_positive
      (probability index) (nonnegative index)
      (normalized index)).trans_lt approximation_budget
  · intro index letter genuinely_positive
    have letter_le_inner :
        1 / probability index letter ≤
          ∑ candidate : I,
            if 0 < probability index candidate then
              1 / probability index candidate
            else 0 := by
      have single := Finset.single_le_sum
        (s := (Finset.univ : Finset I))
        (f := fun candidate : I =>
          if 0 < probability index candidate then
            1 / probability index candidate
          else 0)
        (fun candidate _ => by
          split_ifs with positive
          · exact (one_div_pos.mpr positive).le
          · exact le_rfl)
        (Finset.mem_univ letter)
      simpa only [one_div, ge_iff_le, genuinely_positive, ↓reduceIte] using single
    have inner_le_cost :
        (∑ candidate : I,
          if 0 < probability index candidate then
            1 / probability index candidate
          else 0) ≤ supportCost := by
      dsimp [supportCost]
      exact Finset.single_le_sum
        (s := (Finset.univ : Finset K))
        (f := fun current : K =>
          ∑ candidate : I,
            if 0 < probability current candidate then
              1 / probability current candidate
            else 0)
        (fun current _ => by
          apply Finset.sum_nonneg
          intro candidate _
          split_ifs with positive
          · exact (one_div_pos.mpr positive).le
          · exact le_rfl)
        (Finset.mem_univ index)
    have reciprocal_lt_denominator :
        1 / probability index letter < (denominator : ℝ) :=
      lt_of_le_of_lt (letter_le_inner.trans inner_le_cost)
        (lt_of_le_of_lt
          (le_add_of_nonneg_left ratio_positive.le)
          denominator_large)
    have mass_exceeds_one :
        (1 : ℝ) ≤ probability index letter * (denominator : ℝ) := by
      have crossed :=
        (div_lt_iff₀ genuinely_positive).mp
          reciprocal_lt_denominator
      linarith
    have positive_floor :
        0 < distributionFloorNumerator
          denominator (probability index) letter := by
      unfold distributionFloorNumerator
      exact Nat.floor_pos.mpr mass_exceeds_one
    change
      0 < distributionFloorNumerator denominator
        (probability index) letter +
          if letter = base then
            distributionFloorResidual denominator (probability index)
          else 0
    exact lt_of_lt_of_le positive_floor
      (Nat.le_add_right _ _)

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem exactLocallySampleableLaw_absolute_continuous_roundedJA
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (denominator : ℕ) (denominator_positive : 0 < denominator)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (preserves : ∀ index history,
      0 < exactLocalConditionalFamily D base
          (exactLocallySampleableLaw G n S D) index history →
        0 < numerator index history)
    (history : ExactLocallySampleableTuple X Y A B D) :
    exactLocallySampleableJARounded
      G n D denominator numerator history = 0 →
        exactLocallySampleableLaw G n S D history = 0 := by
  classical
  intro rounded_zero
  apply exactLocallySampleableLaw_absolute_continuous_JA
    G n S D remaining positive base history
  rcases history with ⟨coordinate, x, y, flag⟩
  have card_nonzero :
      (Fintype.card (SourceRemainingCoordinate D) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt
      (exactRemainingCoordinate_card_pos D remaining))
  have denominator_nonzero : (denominator : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt denominator_positive)
  change
    G.questionWeight x y *
      ((numerator (.inl (coordinate, x)) flag : ℝ) /
        denominator) /
      (Fintype.card (SourceRemainingCoordinate D) : ℝ) = 0
    at rounded_zero
  have product_zero :
      G.questionWeight x y *
        ((numerator (.inl (coordinate, x)) flag : ℝ) /
          denominator) = 0 :=
    (div_eq_zero_iff.mp rounded_zero).resolve_right card_nonzero
  rcases mul_eq_zero.mp product_zero with question_zero | numerator_zero
  · change
      G.questionWeight x y *
        exactAliceLocalConditional D base
          (exactLocallySampleableLaw G n S D)
          coordinate x flag /
          (Fintype.card (SourceRemainingCoordinate D) : ℝ) = 0
    simp only [question_zero, zero_mul, Fintype.card_coe, zero_div]
  · have cast_zero :
        (numerator (.inl (coordinate, x)) flag : ℝ) = 0 :=
      (div_eq_zero_iff.mp numerator_zero).resolve_right
        denominator_nonzero
    have natural_zero : numerator (.inl (coordinate, x)) flag = 0 := by
      exact_mod_cast cast_zero
    have conditional_nonnegative :
        0 ≤ exactAliceLocalConditional D base
          (exactLocallySampleableLaw G n S D)
          coordinate x flag :=
      exactAliceLocalConditional_nonneg D base
        (exactLocallySampleableLaw G n S D)
        (exactLocallySampleableLaw_nonneg G n S D positive)
        coordinate x flag
    have conditional_zero :
        exactAliceLocalConditional D base
          (exactLocallySampleableLaw G n S D)
          coordinate x flag = 0 := by
      by_contra nonzero
      have strictly_positive :=
        lt_of_le_of_ne conditional_nonnegative (Ne.symm nonzero)
      have retained := preserves (.inl (coordinate, x)) flag
        strictly_positive
      omega
    change
      G.questionWeight x y *
        exactAliceLocalConditional D base
          (exactLocallySampleableLaw G n S D)
          coordinate x flag /
          (Fintype.card (SourceRemainingCoordinate D) : ℝ) = 0
    simp only [conditional_zero, mul_zero, Fintype.card_coe, zero_div]

theorem exact_exists_support_preserving_local_shared_permutation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    {gamma : ℝ} (gamma_positive : 0 < gamma) :
    ∃ denominator : ℕ, 0 < denominator ∧
      ∃ numerator : ExactLocalSamplerIndex X Y D →
        ExactHistoryFlag X Y A B D → ℕ,
        (∀ index, (∑ history, numerator index history) = denominator) ∧
        (∀ index, finiteTotalVariation
          (exactLocalConditionalFamily D base
            (exactLocallySampleableLaw G n S D) index)
          (fun history =>
            (numerator index history : ℝ) / denominator) < gamma) ∧
        (∀ index history,
          0 < exactLocalConditionalFamily D base
              (exactLocallySampleableLaw G n S D)
              index history →
            0 < numerator index history) ∧
        ∃ nonempty : ∀ index,
          (rationalMarked denominator (numerator index)).Nonempty,
          (∀ index history,
            uniformPermutationProbability
              (fun permutation : Equiv.Perm
                (ExactHistoryFlag X Y A B D × Fin denominator) =>
                rationalPermutationOutput denominator (numerator index)
                  (nonempty index) permutation = history) =
                (numerator index history : ℝ) / denominator) ∧
          (∀ left right,
            uniformPermutationProbability
              (fun permutation : Equiv.Perm
                (ExactHistoryFlag X Y A B D × Fin denominator) =>
                rationalPermutationOutput denominator (numerator left)
                  (nonempty left) permutation ≠
                rationalPermutationOutput denominator (numerator right)
                  (nonempty right) permutation) ≤
              2 * finiteTotalVariation
                (fun history =>
                  (numerator left history : ℝ) / denominator)
                (fun history =>
                  (numerator right history : ℝ) / denominator)) := by
  obtain ⟨denominator, denominator_positive, numerator,
      normalized, approximation, preserves⟩ :=
    existsCommonSupportPreservingRationalApproximations
      base
      (exactLocalConditionalFamily D base
        (exactLocallySampleableLaw G n S D))
      (exactLocalConditionalFamily_nonneg D base
        (exactLocallySampleableLaw G n S D)
        (exactLocallySampleableLaw_nonneg G n S D positive))
      (exactLocalConditionalFamily_sum D base
        (exactLocallySampleableLaw G n S D))
      gamma_positive
  refine ⟨denominator, denominator_positive, numerator,
    normalized, approximation, preserves,
    fun index => rationalMarked_nonempty denominator
      (numerator index) (normalized index) denominator_positive,
    ?_, ?_⟩
  · intro index history
    exact rationalPermutationOutput_probability
      denominator (numerator index) (normalized index) _ history
  · intro left right
    exact rationalPermutationOutput_disagreement_le_two_mul_finiteTotalVariation
      denominator denominator_positive
      (numerator left) (numerator right)
      (normalized left) (normalized right) _ _

end

section

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace


attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

private def exactSourceAliceRefinedPOVM
    [DecidableEq A]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (x : X) :
    POVM A (ExactAliceLocalIndex G n S D r) := by
  classical
  exact purificationAlicePOVM
    (exactAliceRefinedPOVM G n S D r a₀ x)

private def exactSourceBobRefinedPOVM
    [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (b₀ : B) (y : Y) :
    POVM B (ExactBobLocalIndex G n S D r) :=
  exactBobRefinedPOVM G n S D r b₀ y

private def exactSourceJointEffect
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (b₀ : B) (x : X) (y : Y) (a : A) (b : B) :
    Matrix
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r)
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r) ℂ :=
  (exactSourceAliceRefinedPOVM G n S D r a₀ x).effect a ⊗ₖ
    (exactSourceBobRefinedPOVM G n S D r b₀ y).effect b

private def exactSourceWinningEffect
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (b₀ : B) (x : X) (y : Y) :
    Matrix
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r)
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r) ℂ :=
  ∑ a : A, ∑ b : B,
    if G.predicate x y a b = true
    then exactSourceJointEffect G n S D r a₀ b₀ x y a b
    else 0

/-- The continuous linear map implementing exact source winning effect. -/
def exactSourceWinningEffectCLM
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (b₀ : B) (x : X) (y : Y) :
    EuclideanSpace ℂ
        (ExactAliceLocalIndex G n S D r ×
          ExactBobLocalIndex G n S D r) →L[ℂ]
      EuclideanSpace ℂ
        (ExactAliceLocalIndex G n S D r ×
          ExactBobLocalIndex G n S D r) := by
  classical
  exact Matrix.toEuclideanCLM
    (n := ExactAliceLocalIndex G n S D r ×
      ExactBobLocalIndex G n S D r) (𝕜 := ℂ)
    (exactSourceWinningEffect G n S D r a₀ b₀ x y)

theorem exactSourceJointEffect_quadratic
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (b₀ : B) (x : X) (y : Y) (a : A) (b : B) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := ExactAliceLocalIndex G n S D r ×
          ExactBobLocalIndex G n S D r) (𝕜 := ℂ)
        (exactSourceJointEffect G n S D r a₀ b₀ x y a b))
      (exactUnnormalizedPsi G n S D r x y) =
      bornTracePairing S.state.matrix
        (exactAliceCoordinateFilter
          G n S D r.seed r.history r.aliceAnswer x a)
        (exactBobCoordinateFilter
          G n S D r.seed r.history r.bobAnswer y b) := by
  classical
  simpa only [exactSourceJointEffect, exactSourceAliceRefinedPOVM, purificationAlicePOVM,
    exactSourceBobRefinedPOVM] using
    (exactRefinedPOVM_quadratic
      G n S D r a₀ b₀ x y a b)

theorem exactSourceWinningEffect_quadratic
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (b₀ : B) (x : X) (y : Y) :
    quadraticExpectation
      (exactSourceWinningEffectCLM
        G n S D r a₀ b₀ x y)
      (exactUnnormalizedPsi G n S D r x y) =
      ∑ a : A, ∑ b : B,
        if G.predicate x y a b = true then
          bornTracePairing S.state.matrix
            (exactAliceCoordinateFilter
              G n S D r.seed r.history r.aliceAnswer x a)
            (exactBobCoordinateFilter
              G n S D r.seed r.history r.bobAnswer y b)
        else 0 := by
  classical
  unfold exactSourceWinningEffectCLM
    exactSourceWinningEffect
  rw [sourceHistoryQuadraticExpectation_matrix_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [sourceHistoryQuadraticExpectation_matrix_sum]
  apply Finset.sum_congr rfl
  intro b _
  split_ifs
  · exact exactSourceJointEffect_quadratic
      G n S D r a₀ b₀ x y a b
  · simp only [quadraticExpectation, map_zero, _root_.zero_apply, inner_zero_right, zero_re]

theorem exactSourceWinningEffect_quadratic_eq_conditional
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (b₀ : B) (x : X) (y : Y)
    (supported : exactFiberQuestionMass
      G n D r.seed r.history x y ≠ 0) :
    quadraticExpectation
      (exactSourceWinningEffectCLM
        G n S D r a₀ b₀ x y)
      (exactUnnormalizedPsi G n S D r x y) =
      exactJointConditionalWinningMass
        G n S D r.seed r.history r.aliceAnswer r.bobAnswer x y := by
  rw [exactSourceWinningEffect_quadratic]
  unfold exactJointConditionalWinningMass
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs
  · rw [exactAliceCoordinateFilter_eq_joint
      G n S D r.seed r.history r.aliceAnswer x y a supported,
      exactBobCoordinateFilter_eq_joint
        G n S D r.seed r.history r.bobAnswer x y b supported]
  · rfl

theorem exactSourceNormalizedWinningEffect_eq_conditional
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (b₀ : B) (x : X) (y : Y)
    (supported : exactFiberQuestionMass
      G n D r.seed r.history x y ≠ 0) :
    quadraticExpectation
      (exactSourceWinningEffectCLM
        G n S D r a₀ b₀ x y)
      (normalizedPureVector
        (exactUnnormalizedPsi G n S D r x y)) =
      exactJointConditionalWinningMass
        G n S D r.seed r.history r.aliceAnswer r.bobAnswer x y /
        bornTracePairing S.state.matrix
          (exactAliceQuestionFilter
            G n S D r.seed r.history r.aliceAnswer x)
          (exactBobQuestionFilter
            G n S D r.seed r.history r.bobAnswer y) := by
  rw [quadraticExpectation_normalizedPureVector,
    exactSourceWinningEffect_quadratic_eq_conditional
      G n S D r a₀ b₀ x y supported,
    exactUnnormalizedPsi_norm_sq]

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace


open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

private def exactSourceAcceptedCoordinateMass
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (t : ExactLocallySampleableTuple X Y A B D) : ℝ :=
  ∑ q : ExactJointOutcome X Y A B D,
    if exactLocallySampleableCode D q = t ∧
      repeatedCoordinateWin G n q.1.coordinate.val q.2 = true then
      exactPostselectedJointLaw G n S D q
    else 0

theorem exactSourceAcceptedCoordinateMass_nonneg
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (t : ExactLocallySampleableTuple X Y A B D) :
    0 ≤ exactSourceAcceptedCoordinateMass G n S D t := by
  unfold exactSourceAcceptedCoordinateMass
  apply Finset.sum_nonneg
  intro q _
  split
  · exact exactPostselectedJointLaw_nonneg
      G n S D positive q
  · exact le_rfl

theorem exactSourceAcceptedCoordinateMass_le_law
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (t : ExactLocallySampleableTuple X Y A B D) :
    exactSourceAcceptedCoordinateMass G n S D t ≤
      exactLocallySampleableLaw G n S D t := by
  classical
  unfold exactSourceAcceptedCoordinateMass
    exactLocallySampleableLaw exactSourcePushforward
    groupedMass
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro q _
  by_cases history : exactLocallySampleableCode D q = t
  · by_cases winning :
      repeatedCoordinateWin G n q.1.coordinate.val q.2 = true
    · simp only [history, winning, and_self, ↓reduceIte, Std.le_refl]
    · simp only [history, winning, Bool.false_eq_true, and_false, ↓reduceIte,
        exactPostselectedJointLaw_nonneg G n S D positive q]
  · simp only [history, false_and, ↓reduceIte, Std.le_refl]

/-- The probability of exact source conditional winning. -/
def exactSourceConditionalWinningProbability
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (t : ExactLocallySampleableTuple X Y A B D) : ℝ :=
  exactSourceAcceptedCoordinateMass G n S D t /
    exactLocallySampleableLaw G n S D t

theorem exactSourceConditionalWinningProbability_bounds
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (t : ExactLocallySampleableTuple X Y A B D) :
    0 ≤ exactSourceConditionalWinningProbability
      G n S D t ∧
    exactSourceConditionalWinningProbability
      G n S D t ≤ 1 := by
  have mass_nonnegative :=
    exactSourceAcceptedCoordinateMass_nonneg
      G n S D positive t
  have mass_le := exactSourceAcceptedCoordinateMass_le_law
    G n S D positive t
  have law_nonnegative := exactLocallySampleableLaw_nonneg
    G n S D positive t
  unfold exactSourceConditionalWinningProbability
  constructor
  · exact div_nonneg mass_nonnegative law_nonnegative
  · by_cases zero : exactLocallySampleableLaw G n S D t = 0
    · simp only [zero, div_zero, zero_le_one]
    · exact (div_le_one
        (lt_of_le_of_ne law_nonnegative (Ne.symm zero))).mpr mass_le

theorem exactSourceConditionalWinningProbability_mul_law
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (t : ExactLocallySampleableTuple X Y A B D) :
    exactLocallySampleableLaw G n S D t *
        exactSourceConditionalWinningProbability G n S D t =
      exactSourceAcceptedCoordinateMass G n S D t := by
  by_cases zero : exactLocallySampleableLaw G n S D t = 0
  · have nonnegative := exactSourceAcceptedCoordinateMass_nonneg
      G n S D positive t
    have bounded := exactSourceAcceptedCoordinateMass_le_law
      G n S D positive t
    rw [zero] at bounded
    have accepted_zero :
        exactSourceAcceptedCoordinateMass G n S D t = 0 := by
      linarith
    simp only [zero, zero_mul, accepted_zero]
  · unfold exactSourceConditionalWinningProbability
    field_simp [zero]

theorem exactSourceAcceptedCoordinateMass_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :
    (∑ t : ExactLocallySampleableTuple X Y A B D,
      exactSourceAcceptedCoordinateMass G n S D t) =
      ∑ q : ExactJointOutcome X Y A B D,
        if repeatedCoordinateWin G n q.1.coordinate.val q.2 = true
        then exactPostselectedJointLaw G n S D q
        else 0 := by
  classical
  unfold exactSourceAcceptedCoordinateMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  by_cases winning :
      repeatedCoordinateWin G n q.1.coordinate.val q.2 = true
  · simp only [winning, and_true, sum_ite_eq, mem_univ, ↓reduceIte]
  · simp only [winning, Bool.false_eq_true, and_false, ↓reduceIte, sum_const_zero]

theorem exactSourceConditionalWinningProbability_expectation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D) :
    (∑ t : ExactLocallySampleableTuple X Y A B D,
      exactLocallySampleableLaw G n S D t *
        exactSourceConditionalWinningProbability G n S D t) =
      ∑ q : ExactJointOutcome X Y A B D,
        if repeatedCoordinateWin G n q.1.coordinate.val q.2 = true
        then exactPostselectedJointLaw G n S D q
        else 0 := by
  simp_rw [exactSourceConditionalWinningProbability_mul_law
    G n S D positive]
  exact exactSourceAcceptedCoordinateMass_sum G n S D

theorem exactRepeatedConditionedCoordinateWin
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (i : Fin n) :
    (∑ outcome : ExactOutcome X Y A B n,
      if repeatedCoordinateWin G n i outcome = true then
        repeatedConditionedOutcomeLaw G n S D outcome
      else 0) =
    (strategyEventLaw (G.repeat n) S).eventMass
        (FiniteEventLaw.winEvent
          (repeatedCoordinateWin G n) (insert i D)) /
        repeatedPostselectionMass G n S D := by
  classical
  have accepted_as_indicator :
      (strategyEventLaw (G.repeat n) S).eventMass
          (FiniteEventLaw.winEvent
            (repeatedCoordinateWin G n) (insert i D)) =
        ∑ outcome : ExactOutcome X Y A B n,
          if outcome ∈ FiniteEventLaw.winEvent
              (repeatedCoordinateWin G n) (insert i D) then
            (strategyEventLaw (G.repeat n) S).weight outcome
          else 0 := by
    simp only [FiniteEventLaw.eventMass, sum_ite_mem, univ_inter]
  rw [accepted_as_indicator]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases winning : repeatedCoordinateWin G n i outcome = true
  · simp only [winning, ↓reduceIte, repeatedConditionedOutcomeLaw, conditionedEventDistribution,
      FiniteEventLaw.winEvent, mem_filter, mem_univ, true_and, mem_insert, forall_eq_or_imp,
      repeatedPostselectionMass, postselectionMass, ite_div, zero_div]
  · simp only [winning, Bool.false_eq_true, ↓reduceIte, FiniteEventLaw.winEvent, mem_insert,
      forall_eq_or_imp, mem_filter, mem_univ, false_and, and_false, zero_div]

theorem exactSourceAcceptedCoordinateMass_sum_eq_remaining_average
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :
    (∑ t : ExactLocallySampleableTuple X Y A B D,
      exactSourceAcceptedCoordinateMass G n S D t) =
      (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        (∑ i : SourceRemainingCoordinate D,
          (strategyEventLaw (G.repeat n) S).eventMass
            (FiniteEventLaw.winEvent
              (repeatedCoordinateWin G n) (insert i.val D)) /
            repeatedPostselectionMass G n S D) := by
  classical
  rw [exactSourceAcceptedCoordinateMass_sum]
  unfold exactPostselectedJointLaw
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  calc
    (∑ outcome : ExactOutcome X Y A B n,
      ∑ seed : ExactRemainingSeed D,
        if repeatedCoordinateWin G n seed.coordinate.val outcome = true
        then exactSeedWeight seed *
          repeatedConditionedOutcomeLaw G n S D outcome
        else 0) =
      ∑ outcome : ExactOutcome X Y A B n,
        ∑ seed : ExactRemainingSeed D,
          exactSeedWeight seed *
            (if repeatedCoordinateWin G n seed.coordinate.val outcome = true
             then repeatedConditionedOutcomeLaw G n S D outcome
             else 0) := by
          apply Finset.sum_congr rfl
          intro outcome _
          apply Finset.sum_congr rfl
          intro seed _
          split <;> simp
    _ = ∑ outcome : ExactOutcome X Y A B n,
        ∑ i : SourceRemainingCoordinate D,
          (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
            (if repeatedCoordinateWin G n i.val outcome = true
             then repeatedConditionedOutcomeLaw G n S D outcome
             else 0) := by
          apply Finset.sum_congr rfl
          intro outcome _
          exact exactSeedWeight_coordinate_sum
            (M := SourceRemainingCoordinate D)
            (fun i =>
              if repeatedCoordinateWin G n i.val outcome = true
              then repeatedConditionedOutcomeLaw G n S D outcome
              else 0)
    _ = (1 / (Fintype.card (SourceRemainingCoordinate D) : ℝ)) *
        (∑ i : SourceRemainingCoordinate D,
          ∑ outcome : ExactOutcome X Y A B n,
            if repeatedCoordinateWin G n i.val outcome = true
            then repeatedConditionedOutcomeLaw G n S D outcome
            else 0) := by
          rw [Finset.sum_comm, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact exactRepeatedConditionedCoordinateWin
        G n S D i.val

theorem exactSourceConditionalWinningProbability_eq_accepted_average
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D) :
    (∑ t : ExactLocallySampleableTuple X Y A B D,
      exactLocallySampleableLaw G n S D t *
        exactSourceConditionalWinningProbability G n S D t) =
      sourceHistoryAcceptedMass G n S D /
        repeatedPostselectionMass G n S D := by
  rw [exactSourceConditionalWinningProbability_expectation
    G n S D positive,
    ← exactSourceAcceptedCoordinateMass_sum,
    exactSourceAcceptedCoordinateMass_sum_eq_remaining_average,
    sourceHistoryAcceptedMass_eq_remaining_average]
  have cardinality :
      Fintype.card (SourceRemainingCoordinate D) =
        (Finset.univ \ D).card := by
    simpa only [Fintype.card_fin] using Fintype.card_congr
      (Finset.equivFin (Finset.univ \ D))
  push_cast [cardinality]
  rw [← Finset.sum_div]
  ring

theorem exactSource_failure_sum_lt_of_uniform
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    {δ : ℝ}
    (failure : uniformRemainingFailure
      (strategyEventLaw (G.repeat n) S)
      (repeatedCoordinateWin G n) D < δ) :
    (∑ i ∈ Finset.univ \ D,
      FiniteEventLaw.failureMass
        (strategyEventLaw (G.repeat n) S)
        (repeatedCoordinateWin G n) D i) <
      ((Finset.univ \ D).card : ℝ) *
        (δ * repeatedPostselectionMass G n S D) := by
  have cardinality : 0 < ((Finset.univ \ D).card : ℝ) := by
    exact_mod_cast remaining
  unfold uniformRemainingFailure conditionalCoordinateFailure at failure
  change
    (∑ i ∈ Finset.univ \ D,
      FiniteEventLaw.failureMass
        (strategyEventLaw (G.repeat n) S)
        (repeatedCoordinateWin G n) D i /
        repeatedPostselectionMass G n S D) /
      ((Finset.univ \ D).card : ℝ) < δ at failure
  rw [← Finset.sum_div] at failure
  have first := (div_lt_iff₀ cardinality).mp failure
  have second := (div_lt_iff₀ positive).mp first
  linarith

theorem exactSourceConditionalWinningProbability_gt_of_uniform_failure
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    {δ : ℝ}
    (failure : uniformRemainingFailure
      (strategyEventLaw (G.repeat n) S)
      (repeatedCoordinateWin G n) D < δ) :
    1 - δ <
      ∑ t : ExactLocallySampleableTuple X Y A B D,
        exactLocallySampleableLaw G n S D t *
          exactSourceConditionalWinningProbability G n S D t := by
  rw [exactSourceConditionalWinningProbability_eq_accepted_average
    G n S D positive]
  have numerator := exactSource_failure_sum_lt_of_uniform
    G n S D remaining positive failure
  have accepted := sourceHistoryAcceptedMass_gt_of_greedy
    G n S D remaining numerator
  apply (lt_div_iff₀ positive).mpr
  exact accepted

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B dA dB : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype dA] [Fintype dB] [DecidableEq dA] [DecidableEq dB]

/--
The exact source alice flag coupling construction used in the quantum parallel-repetition
argument.
-/
def exactSourceAliceFlagCoupling
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty) :
    ExactSourceSharedFlag X Y A B D denominator × (X × Y) → ℝ :=
  exactFiniteFiberLift
    (exactSourceAliceSampleTuple
      D denominator numerator nonempty)
    (flaggedQuestionWeight G
      (exactSourceSharedFlagWeight D denominator))
    (exactLocallySampleableLaw G n S D)

theorem exactSourceAliceFlagCoupling_supported
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (denominator : ℕ) (denominator_positive : 0 < denominator)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (normalized : ∀ index,
      (∑ history, numerator index history) = denominator)
    (preserves : ∀ index history,
      0 < exactLocalConditionalFamily D base
          (exactLocallySampleableLaw G n S D) index history →
        0 < numerator index history)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (history : ExactLocallySampleableTuple X Y A B D) :
    groupedMass
        (exactSourceAliceSampleTuple
          D denominator numerator nonempty)
        (flaggedQuestionWeight G
          (exactSourceSharedFlagWeight D denominator)) history = 0 →
      exactLocallySampleableLaw G n S D history = 0 := by
  rw [exactSourceAliceSampleTuple_groupedMass
    G n D denominator numerator normalized nonempty]
  exact exactLocallySampleableLaw_absolute_continuous_roundedJA
    G n S D remaining positive base denominator denominator_positive
    numerator preserves history

theorem exactSourceAliceFlagCoupling_expectation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (denominator : ℕ) (denominator_positive : 0 < denominator)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (normalized : ∀ index,
      (∑ history, numerator index history) = denominator)
    (preserves : ∀ index history,
      0 < exactLocalConditionalFamily D base
          (exactLocallySampleableLaw G n S D) index history →
        0 < numerator index history)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (value : ExactLocallySampleableTuple X Y A B D → ℝ) :
    (∑ outcome :
      ExactSourceSharedFlag X Y A B D denominator × (X × Y),
      exactSourceAliceFlagCoupling
        G n S D denominator numerator nonempty outcome *
        value (exactSourceAliceSampleTuple
          D denominator numerator nonempty outcome)) =
      ∑ history : ExactLocallySampleableTuple X Y A B D,
        exactLocallySampleableLaw G n S D history *
          value history := by
  exact exactFiniteFiberLift_expectation
    (exactSourceAliceSampleTuple
      D denominator numerator nonempty)
    (flaggedQuestionWeight G
      (exactSourceSharedFlagWeight D denominator))
    (exactLocallySampleableLaw G n S D)
    (exactSourceAliceFlagCoupling_supported
      G n S D remaining positive base denominator denominator_positive
      numerator normalized preserves nonempty)
    value

theorem exactSourceAliceFlagCoupling_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (denominator : ℕ) (denominator_positive : 0 < denominator)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (normalized : ∀ index,
      (∑ history, numerator index history) = denominator)
    (preserves : ∀ index history,
      0 < exactLocalConditionalFamily D base
          (exactLocallySampleableLaw G n S D) index history →
        0 < numerator index history)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty) :
    (∑ outcome :
      ExactSourceSharedFlag X Y A B D denominator × (X × Y),
      exactSourceAliceFlagCoupling
        G n S D denominator numerator nonempty outcome) = 1 := by
  have expectation := exactSourceAliceFlagCoupling_expectation
    G n S D remaining positive base denominator denominator_positive
    numerator normalized preserves nonempty (fun _ => (1 : ℝ))
  simpa only [mul_one, exactLocallySampleableLaw_sum G n S D remaining positive] using expectation

theorem exactSourceAliceFlagCoupling_totalVariation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (denominator : ℕ) (denominator_positive : 0 < denominator)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (normalized : ∀ index,
      (∑ history, numerator index history) = denominator)
    (preserves : ∀ index history,
      0 < exactLocalConditionalFamily D base
          (exactLocallySampleableLaw G n S D) index history →
        0 < numerator index history)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty) :
    finiteTotalVariation
      (flaggedQuestionWeight G
        (exactSourceSharedFlagWeight D denominator))
      (exactSourceAliceFlagCoupling
        G n S D denominator numerator nonempty) =
      finiteTotalVariation
        (exactLocallySampleableJARounded
          G n D denominator numerator)
        (exactLocallySampleableLaw G n S D) := by
  change
    finiteTotalVariation
      (flaggedQuestionWeight G
        (exactSourceSharedFlagWeight D denominator))
      (exactFiniteFiberLift
        (exactSourceAliceSampleTuple
          D denominator numerator nonempty)
        (flaggedQuestionWeight G
          (exactSourceSharedFlagWeight D denominator))
        (exactLocallySampleableLaw G n S D)) = _
  rw [exactFiniteFiberLift_totalVariation
    (exactSourceAliceSampleTuple
      D denominator numerator nonempty)
    (flaggedQuestionWeight G
      (exactSourceSharedFlagWeight D denominator))
    (exactLocallySampleableLaw G n S D)
    (flaggedQuestionWeight_nonneg G
      (exactSourceSharedFlagWeight D denominator)
      (exactSourceSharedFlagWeight_nonneg D denominator))
    (exactSourceAliceFlagCoupling_supported
      G n S D remaining positive base denominator denominator_positive
      numerator normalized preserves nonempty)]
  congr 1
  funext history
  exact exactSourceAliceSampleTuple_groupedMass
    G n D denominator numerator normalized nonempty history

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace


open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

private def exactFairWinningOutcomeBornMass
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (history : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) : ℝ :=
  ∑ outcome : ExactOutcome X Y A B n,
    if exactLocallySampleableCode D (history.seed, outcome) =
        (history.seed.coordinate, x, y, history) ∧
      repeatedCoordinateWin G n history.seed.coordinate.val outcome = true
    then (strategyEventLaw (G.repeat n) S).weight outcome
    else 0

theorem exactSourceAcceptedCoordinateMass_eq_seeded_fair_born
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (history : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) :
    exactSourceAcceptedCoordinateMass G n S D
        (history.seed.coordinate, x, y, history) =
      if exactHistoryAccepted G n D history then
        (exactSeedWeight history.seed *
          exactFairWinningOutcomeBornMass
            G n S D history x y) /
          repeatedPostselectionMass G n S D
      else 0 := by
  classical
  by_cases accepted : exactHistoryAccepted G n D history
  · rw [ite_eq_left accepted]
    unfold exactSourceAcceptedCoordinateMass
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single history.seed]
    · unfold exactFairWinningOutcomeBornMass
      rw [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro outcome _
      by_cases code :
          exactLocallySampleableCode D
            (history.seed, outcome) =
              (history.seed.coordinate, x, y, history)
      · by_cases winning :
          repeatedCoordinateWin G n history.seed.coordinate.val
            outcome = true
        · have same_history :
              exactHistoryCode D (history.seed, outcome) =
                history :=
            congrArg
              (fun t : ExactLocallySampleableTuple
                X Y A B D => t.2.2.2) code
          have conditioned :
              outcome ∈ FiniteEventLaw.winEvent
                (repeatedCoordinateWin G n) D := by
            apply (exactHistoryCode_accepted_iff
              G n D (history.seed, outcome)).mp
            rw [same_history]
            exact accepted
          simp only [code, winning, and_self, ↓reduceIte, exactPostselectedJointLaw,
            repeatedConditionedOutcomeLaw, conditionedEventDistribution, conditioned,
            repeatedPostselectionMass, postselectionMass]
          ring
        · simp only [code, winning, Bool.false_eq_true, and_false, ↓reduceIte, mul_zero, zero_div]
      · simp only [code, false_and, ↓reduceIte, mul_zero, zero_div]
    · intro seed _ distinct
      apply Finset.sum_eq_zero
      intro outcome _
      have not_code :
          exactLocallySampleableCode D (seed, outcome) ≠
            (history.seed.coordinate, x, y, history) := by
        intro code
        have same := congrArg
          (fun t : ExactLocallySampleableTuple X Y A B D =>
            t.2.2.2.seed) code
        exact distinct same
      simp only [not_code, false_and, ↓reduceIte]
    · simp only [mem_univ, not_true_eq_false, IsEmpty.forall_iff]
  · rw [ite_eq_right accepted]
    have law_zero :=
      exactLocallySampleableLaw_zero_of_not_accepted
        G n S D history.seed.coordinate x y history accepted
    exact le_antisymm
      (by
        simpa only [law_zero] using
          exactSourceAcceptedCoordinateMass_le_law
            G n S D positive
            (history.seed.coordinate, x, y, history))
      (exactSourceAcceptedCoordinateMass_nonneg
        G n S D positive
        (history.seed.coordinate, x, y, history))

theorem exactSourceConditionalWinningProbability_eq_fine_born_ratio
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (history : ExactHistoryFlag X Y A B D)
    (accepted : exactHistoryAccepted G n D history)
    (x : X) (y : Y) :
    exactSourceConditionalWinningProbability G n S D
        (history.seed.coordinate, x, y, history) =
      exactFairWinningOutcomeBornMass G n S D history x y /
        exactFairFullOutcomeBornMass G n S D history x y := by
  have seed_positive : 0 < exactSeedWeight history.seed := by
    unfold exactSeedWeight
    have coordinate_positive :
        0 < Fintype.card (SourceRemainingCoordinate D) :=
      Fintype.card_pos_iff.mpr ⟨history.seed.coordinate⟩
    positivity
  have posterior :
      exactLocallySampleableLaw G n S D
        (history.seed.coordinate, x, y, history) =
        (exactSeedWeight history.seed *
          exactFairFullOutcomeBornMass
            G n S D history x y) /
          repeatedPostselectionMass G n S D := by
    rw [exactLocallySampleableLaw_eq_fair_born,
      ite_eq_left accepted,
      exactFairFullOutcomeBornMass_eq_reveal_question_norm]
    ring
  unfold exactSourceConditionalWinningProbability
  rw [exactSourceAcceptedCoordinateMass_eq_seeded_fair_born
    G n S D positive history x y, ite_eq_left accepted, posterior]
  by_cases mass_zero :
      exactFairFullOutcomeBornMass G n S D history x y = 0
  · simp only [mass_zero, mul_zero, zero_div, div_zero]
  · field_simp [positive.ne', seed_positive.ne', mass_zero]

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace


attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem exactFineCoordinateWinningBorn_collapse
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (aliceAnswer : {j : Fin n // j ∈ D} → A)
    (bobAnswer : {j : Fin n // j ∈ D} → B)
    (xs : Fin n → X) (ys : Fin n → Y)
    (coordinate : Fin n) (x : X) (y : Y) :
    (∑ a : A, ∑ b : B,
      if G.predicate x y a b = true then
        bornTracePairing S.state.matrix
          (conditionedAliceCoordinateEffect
            G n S D aliceAnswer xs coordinate a)
          (conditionedBobCoordinateEffect
            G n S D bobAnswer ys coordinate b)
      else 0) =
    ∑ aa : Fin n → A, ∑ bb : Fin n → B,
      if
        (∀ (j : Fin n) (member : j ∈ D),
          aa j = aliceAnswer ⟨j, member⟩) ∧
        (∀ (j : Fin n) (member : j ∈ D),
          bb j = bobAnswer ⟨j, member⟩) ∧
        G.predicate x y (aa coordinate) (bb coordinate) = true
      then S.outcomeProbability xs ys aa bb
      else 0 := by
  classical
  simp_rw [conditionedCoordinateEffects_born_expansion G n S D]
  let f : A → B → (Fin n → A) → (Fin n → B) → ℝ :=
    fun a b aa bb =>
      if G.predicate x y a b = true then
        if
          (∀ (j : Fin n) (member : j ∈ D),
            aa j = aliceAnswer ⟨j, member⟩) ∧ aa coordinate = a
        then
          if
            (∀ (j : Fin n) (member : j ∈ D),
              bb j = bobAnswer ⟨j, member⟩) ∧ bb coordinate = b
          then S.outcomeProbability xs ys aa bb
          else 0
        else 0
      else 0
  calc
    (∑ a : A, ∑ b : B,
      if G.predicate x y a b = true then
        ∑ aa : Fin n → A, ∑ bb : Fin n → B,
          if
            (∀ (j : Fin n) (member : j ∈ D),
              aa j = aliceAnswer ⟨j, member⟩) ∧ aa coordinate = a
          then
            if
              (∀ (j : Fin n) (member : j ∈ D),
                bb j = bobAnswer ⟨j, member⟩) ∧ bb coordinate = b
            then S.outcomeProbability xs ys aa bb
            else 0
          else 0
      else 0) =
      ∑ a : A, ∑ b : B,
        ∑ aa : Fin n → A, ∑ bb : Fin n → B, f a b aa bb := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          by_cases wins : G.predicate x y a b = true
          · simp only [wins, ↓reduceIte, sum_ite_irrel, sum_const_zero, f]
          · simp only [wins, Bool.false_eq_true, ↓reduceIte, sum_const_zero, f]
    _ = ∑ aa : Fin n → A, ∑ bb : Fin n → B,
      ∑ a : A, ∑ b : B, f a b aa bb :=
        finite_sum_four_swap f
    _ = ∑ aa : Fin n → A, ∑ bb : Fin n → B,
      if
        (∀ (j : Fin n) (member : j ∈ D),
          aa j = aliceAnswer ⟨j, member⟩) ∧
        (∀ (j : Fin n) (member : j ∈ D),
          bb j = bobAnswer ⟨j, member⟩) ∧
        G.predicate x y (aa coordinate) (bb coordinate) = true
      then S.outcomeProbability xs ys aa bb
      else 0 := by
        apply Finset.sum_congr rfl
        intro aa _
        apply Finset.sum_congr rfl
        intro bb _
        by_cases alice_matches :
          ∀ (j : Fin n) (member : j ∈ D),
            aa j = aliceAnswer ⟨j, member⟩
        · by_cases bob_matches :
            ∀ (j : Fin n) (member : j ∈ D),
              bb j = bobAnswer ⟨j, member⟩
          · rw [Finset.sum_eq_single (aa coordinate)]
            · rw [Finset.sum_eq_single (bb coordinate)]
              · dsimp only [f]
                by_cases wins :
                  G.predicate x y (aa coordinate) (bb coordinate) = true
                · rw [ite_eq_left wins,
                    ite_eq_left ⟨alice_matches, rfl⟩,
                    ite_eq_left ⟨bob_matches, rfl⟩,
                    ite_eq_left ⟨alice_matches, bob_matches, wins⟩]
                · rw [ite_eq_right wins,
                    ite_eq_right (fun h => wins h.2.2)]
              · intro b _ different
                simp only [and_true, Ne.symm different, and_false, ↓reduceIte, ite_self, f]
              · simp only [mem_univ, not_true_eq_false, IsEmpty.forall_iff]
            · intro a _ different
              simp only [Ne.symm different, and_false, ↓reduceIte, ite_self, sum_const_zero, f]
            · simp only [mem_univ, not_true_eq_false, IsEmpty.forall_iff]
          · simp only [bob_matches, false_and, ↓reduceIte, ite_self, sum_const_zero, and_false, f]
        · simp only [alice_matches, false_and, ↓reduceIte, ite_self, sum_const_zero, f]

private def exactFairCoordinateRefinedWinningBornMass
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (history : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) : ℝ :=
  ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
    exactFiberQuestionWeight
        G n D history.seed history.history x y xs ys *
      (∑ a : A, ∑ b : B,
        if G.predicate x y a b = true then
          bornTracePairing S.state.matrix
            (conditionedAliceCoordinateEffect G n S D
              history.aliceAnswer xs history.seed.coordinate.val a)
            (conditionedBobCoordinateEffect G n S D
              history.bobAnswer ys history.seed.coordinate.val b)
        else 0)

theorem exactFairWinningOutcomeBornMass_eq_refined
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (history : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) :
    exactFairWinningOutcomeBornMass
      G n S D history x y =
        exactFairCoordinateRefinedWinningBornMass
          G n S D history x y := by
  classical
  unfold exactFairWinningOutcomeBornMass
    exactFairCoordinateRefinedWinningBornMass
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro xs _
  apply Finset.sum_congr rfl
  intro ys _
  have compatibility :
      (exactAliceQuestionCompatible
        D history.seed history.history x xs ∧
       exactBobQuestionCompatible
        D history.seed history.history y ys) ↔
      exactRevealCode D history.seed (xs, ys) = history.history ∧
        xs history.seed.coordinate.val = x ∧
        ys history.seed.coordinate.val = y :=
    (exactRevealCode_compatible_iff
      D history.seed history.history x y xs ys).symm
  by_cases compatible :
      exactAliceQuestionCompatible
        D history.seed history.history x xs ∧
      exactBobQuestionCompatible
        D history.seed history.history y ys
  · have actual := compatibility.mp compatible
    rw [exactFiberQuestionWeight, ite_eq_left compatible,
      exactFineCoordinateWinningBorn_collapse
        G n S D history.aliceAnswer history.bobAnswer xs ys
        history.seed.coordinate.val x y]
    calc
      (∑ aa : Fin n → A, ∑ bb : Fin n → B,
        if exactLocallySampleableCode D
            (history.seed, (xs, ys, aa, bb)) =
            (history.seed.coordinate, x, y, history) ∧
          repeatedCoordinateWin G n history.seed.coordinate.val
            (xs, ys, aa, bb) = true
        then (strategyEventLaw (G.repeat n) S).weight
          (xs, ys, aa, bb)
        else 0) =
        ∑ aa : Fin n → A, ∑ bb : Fin n → B,
          (G.repeat n).questionWeight xs ys *
            if
              (∀ (j : Fin n) (member : j ∈ D),
                aa j = history.aliceAnswer ⟨j, member⟩) ∧
              (∀ (j : Fin n) (member : j ∈ D),
                bb j = history.bobAnswer ⟨j, member⟩) ∧
              G.predicate x y
                (aa history.seed.coordinate.val)
                (bb history.seed.coordinate.val) = true
            then S.outcomeProbability xs ys aa bb
            else 0 := by
          apply Finset.sum_congr rfl
          intro aa _
          apply Finset.sum_congr rfl
          intro bb _
          have fiber :=
            exactLocallySampleableCode_fixedSeed_fiber_iff
              D history x y (xs, ys, aa, bb)
          have event :
              (exactLocallySampleableCode D
                  (history.seed, (xs, ys, aa, bb)) =
                    (history.seed.coordinate, x, y, history) ∧
                repeatedCoordinateWin G n history.seed.coordinate.val
                  (xs, ys, aa, bb) = true) ↔
              ((∀ (j : Fin n) (member : j ∈ D),
                aa j = history.aliceAnswer ⟨j, member⟩) ∧
               (∀ (j : Fin n) (member : j ∈ D),
                bb j = history.bobAnswer ⟨j, member⟩) ∧
               G.predicate x y
                (aa history.seed.coordinate.val)
                (bb history.seed.coordinate.val) = true) := by
            rw [fiber]
            simp only [actual.1, actual.2.1, actual.2.2, Subtype.forall, true_and,
              repeatedCoordinateWin, and_assoc]
          by_cases wins :
              (∀ (j : Fin n) (member : j ∈ D),
                aa j = history.aliceAnswer ⟨j, member⟩) ∧
              (∀ (j : Fin n) (member : j ∈ D),
                bb j = history.bobAnswer ⟨j, member⟩) ∧
              G.predicate x y
                (aa history.seed.coordinate.val)
                (bb history.seed.coordinate.val) = true
          · have selected := event.mpr wins
            rw [ite_eq_left selected, ite_eq_left wins]
            rfl
          · have rejected :
              ¬ (exactLocallySampleableCode D
                    (history.seed, (xs, ys, aa, bb)) =
                  (history.seed.coordinate, x, y, history) ∧
                repeatedCoordinateWin G n history.seed.coordinate.val
                  (xs, ys, aa, bb) = true) := by
              intro selected
              exact wins (event.mp selected)
            rw [ite_eq_right rejected, ite_eq_right wins]
            simp only [Game.repeat_questionWeight, mul_zero]
      _ = (G.repeat n).questionWeight xs ys *
        (∑ aa : Fin n → A, ∑ bb : Fin n → B,
          if
            (∀ (j : Fin n) (member : j ∈ D),
              aa j = history.aliceAnswer ⟨j, member⟩) ∧
            (∀ (j : Fin n) (member : j ∈ D),
              bb j = history.bobAnswer ⟨j, member⟩) ∧
            G.predicate x y
              (aa history.seed.coordinate.val)
              (bb history.seed.coordinate.val) = true
          then S.outcomeProbability xs ys aa bb
          else 0) := by
          simp only [Finset.mul_sum]
  · rw [exactFiberQuestionWeight, ite_eq_right compatible,
      zero_mul]
    apply Finset.sum_eq_zero
    intro aa _
    apply Finset.sum_eq_zero
    intro bb _
    have no_code :
        exactLocallySampleableCode D
          (history.seed, (xs, ys, aa, bb)) ≠
            (history.seed.coordinate, x, y, history) := by
      intro code
      have conditions :=
        (exactLocallySampleableCode_fixedSeed_fiber_iff
          D history x y (xs, ys, aa, bb)).mp code
      exact compatible
        (compatibility.mpr
          ⟨conditions.1, conditions.2.1, conditions.2.2.1⟩)
    simp only [no_code, false_and, ↓reduceIte]

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace


attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem exactFairWinningOutcomeBornMass_eq_fiber_conditional
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (history : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y)
    (supported : exactFiberQuestionMass
      G n D history.seed history.history x y ≠ 0) :
    exactFairWinningOutcomeBornMass G n S D history x y =
      exactFiberQuestionMass
          G n D history.seed history.history x y *
        exactJointConditionalWinningMass
          G n S D history.seed history.history
          history.aliceAnswer history.bobAnswer x y := by
  classical
  rw [exactFairWinningOutcomeBornMass_eq_refined,
    exactJointConditionalWinningMass_born
      G n S D history.seed history.history
      history.aliceAnswer history.bobAnswer x y supported]
  unfold exactFairCoordinateRefinedWinningBornMass
  let summand : (Fin n → X) → (Fin n → Y) → A → B → ℝ :=
    fun xs ys a b =>
      if G.predicate x y a b = true then
        exactFiberQuestionWeight
            G n D history.seed history.history x y xs ys *
          bornTracePairing S.state.matrix
            (conditionedAliceCoordinateEffect
              G n S D history.aliceAnswer xs
              history.seed.coordinate.val a)
            (conditionedBobCoordinateEffect
              G n S D history.bobAnswer ys
              history.seed.coordinate.val b)
      else 0
  calc
    (∑ xs : Fin n → X, ∑ ys : Fin n → Y,
      exactFiberQuestionWeight
          G n D history.seed history.history x y xs ys *
        (∑ a : A, ∑ b : B,
          if G.predicate x y a b = true then
            bornTracePairing S.state.matrix
              (conditionedAliceCoordinateEffect
                G n S D history.aliceAnswer xs
                history.seed.coordinate.val a)
              (conditionedBobCoordinateEffect
                G n S D history.bobAnswer ys
                history.seed.coordinate.val b)
          else 0)) =
        ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
          ∑ a : A, ∑ b : B, summand xs ys a b := by
            simp only [summand, Finset.mul_sum, mul_ite, mul_zero]
    _ = ∑ a : A, ∑ b : B,
          ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
            summand xs ys a b :=
      finite_sum_four_swap summand
    _ = exactFiberQuestionMass
          G n D history.seed history.history x y *
        (∑ a : A, ∑ b : B,
          if G.predicate x y a b = true then
            ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
              exactConditionalQuestionWeight
                  G n D history.seed history.history x y xs ys *
                bornTracePairing S.state.matrix
                  (conditionedAliceCoordinateEffect
                    G n S D history.aliceAnswer xs
                    history.seed.coordinate.val a)
                  (conditionedBobCoordinateEffect
                    G n S D history.bobAnswer ys
                    history.seed.coordinate.val b)
          else 0) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b _
            by_cases wins : G.predicate x y a b = true
            · simp only [ite_eq_left wins]
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro xs _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro ys _
              dsimp only [summand]
              rw [ite_eq_left wins]
              unfold exactConditionalQuestionWeight
              field_simp [supported]
            · simp only [wins, Bool.false_eq_true, ↓reduceIte, sum_const_zero, mul_zero, summand]

theorem exactSourceConditionalWinningProbability_eq_normalized_verifier
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (history : ExactHistoryFlag X Y A B D)
    (accepted : exactHistoryAccepted G n D history)
    (a₀ : A) (b₀ : B) (x : X) (y : Y)
    (supported : exactFiberQuestionMass
      G n D history.seed history.history x y ≠ 0) :
    exactSourceConditionalWinningProbability G n S D
        (history.seed.coordinate, x, y, history) =
      quadraticExpectation
        (exactSourceWinningEffectCLM
          G n S D history a₀ b₀ x y)
        (normalizedPureVector
          (exactUnnormalizedPsi G n S D history x y)) := by
  rw [exactSourceConditionalWinningProbability_eq_fine_born_ratio
    G n S D positive history accepted x y,
    exactFairWinningOutcomeBornMass_eq_fiber_conditional
      G n S D history x y supported,
    exactFairFullOutcomeBornMass_eq_conditioned,
    exactFairConditionedAnswerBornMass_eq_fiber_norm,
    exactSourceNormalizedWinningEffect_eq_conditional
      G n S D history a₀ b₀ x y supported,
    exactUnnormalizedPsi_norm_sq]
  exact mul_div_mul_left _ _ supported

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
open QuantumParallelRepetition.ClassicalSampling

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem exactLocallySampleableLaw_coordinate_eq_of_ne_zero
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (t : ExactLocallySampleableTuple X Y A B D)
    (supported : exactLocallySampleableLaw G n S D t ≠ 0) :
    t.1 = t.2.2.2.seed.coordinate := by
  classical
  by_contra different
  apply supported
  unfold exactLocallySampleableLaw
    exactSourcePushforward groupedMass
  apply Finset.sum_eq_zero
  intro q member
  have code :
      exactLocallySampleableCode D q = t := by
    exact ((@Finset.mem_filter
      (ExactJointOutcome X Y A B D)
      (fun a => exactLocallySampleableCode D a = t)
      (fun _ => Classical.propDecidable _)
      Finset.univ q).mp member).2
  have coordinate :=
    congrArg
      (fun u : ExactLocallySampleableTuple X Y A B D =>
        u.1)
      code
  have history_coordinate :=
    congrArg
      (fun u : ExactLocallySampleableTuple X Y A B D =>
        u.2.2.2.seed.coordinate)
      code
  exact False.elim
    (different (coordinate.symm.trans history_coordinate))

theorem exactLocallySampleableLaw_accepted_of_ne_zero
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (t : ExactLocallySampleableTuple X Y A B D)
    (supported : exactLocallySampleableLaw G n S D t ≠ 0) :
    exactHistoryAccepted G n D t.2.2.2 := by
  classical
  by_contra rejected
  exact supported
    (exactLocallySampleableLaw_zero_of_not_accepted
      G n S D t.1 t.2.1 t.2.2.1 t.2.2.2 rejected)

theorem exactLocallySampleableLaw_fiber_ne_zero_of_ne_zero
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (t : ExactLocallySampleableTuple X Y A B D)
    (supported : exactLocallySampleableLaw G n S D t ≠ 0) :
    exactFiberQuestionMass
      G n D t.2.2.2.seed t.2.2.2.history
      t.2.1 t.2.2.1 ≠ 0 := by
  classical
  have coordinate := exactLocallySampleableLaw_coordinate_eq_of_ne_zero G n S D t supported
  have accepted := exactLocallySampleableLaw_accepted_of_ne_zero G n S D t supported
  intro zero
  have reveal_zero :
      exactRevealMass G n D
          t.2.2.2.seed t.2.2.2.history *
        G.questionWeight t.2.1 t.2.2.1 = 0 := by
    simpa only [mul_eq_zero, exactFiberQuestionMass_eq_jointQuestionMass,
      exactJointQuestionMass_eq_reveal_mul_question] using zero
  apply supported
  have source := exactLocallySampleableLaw_eq_fair_born G n S D t.2.2.2 t.2.1 t.2.2.1
  have tuple :
      t =
        (t.2.2.2.seed.coordinate, t.2.1, t.2.2.1, t.2.2.2) := by
    rcases t with ⟨i, x, y, r⟩
    simpa only [Prod.mk.injEq, and_true] using coordinate
  rw [tuple, source, ite_eq_left accepted]
  rw [show
    exactSeedWeight t.2.2.2.seed *
        exactRevealMass G n D
          t.2.2.2.seed t.2.2.2.history *
        G.questionWeight t.2.1 t.2.2.1 =
      exactSeedWeight t.2.2.2.seed *
        (exactRevealMass G n D
          t.2.2.2.seed t.2.2.2.history *
          G.questionWeight t.2.1 t.2.2.1) by ring]
  simp only [reveal_zero, mul_zero, zero_mul, zero_div]

theorem exactLocallySampleableLaw_psi_ne_zero_of_ne_zero
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (t : ExactLocallySampleableTuple X Y A B D)
    (supported : exactLocallySampleableLaw G n S D t ≠ 0) :
    exactUnnormalizedPsi
      G n S D t.2.2.2 t.2.1 t.2.2.1 ≠ 0 := by
  classical
  have coordinate := exactLocallySampleableLaw_coordinate_eq_of_ne_zero
    G n S D t supported
  have accepted := exactLocallySampleableLaw_accepted_of_ne_zero
    G n S D t supported
  intro zero
  apply supported
  have source := exactLocallySampleableLaw_eq_fair_born
    G n S D t.2.2.2 t.2.1 t.2.2.1
  have tuple : t =
        (t.2.2.2.seed.coordinate, t.2.1, t.2.2.1, t.2.2.2) := by
    rcases t with ⟨i, x, y, r⟩
    simpa only [Prod.mk.injEq, and_true] using coordinate
  rw [tuple, source, ite_eq_left accepted, zero]
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    zero_div]

/-- The positive operator-valued measurement implementing dependent block. -/
def dependentBlockPOVM
    {R C : Type*} [Fintype R] [DecidableEq R] [Fintype C]
    {ι : R → Type*}
    [∀ r, Fintype (ι r)] [∀ r, DecidableEq (ι r)]
    (P : (r : R) → POVM C (ι r)) :
    POVM C (Σ r : R, ι r) where
  effect c := Matrix.blockDiagonal' fun r => (P r).effect c
  positive c := by
    apply posSemidef_blockDiagonal'
    intro r
    exact (P r).positive c
  complete := by
    classical
    ext ⟨r, u⟩ ⟨s, v⟩
    by_cases same : r = s
    · subst s
      have completed := congrArg
        (fun M : Matrix (ι r) (ι r) ℂ => M u v)
        (P r).complete
      simpa only [Matrix.sum_apply, blockDiagonal'_apply, ↓reduceDIte, cast_eq, Matrix.one_apply,
        Sigma.mk.injEq, heq_eq_eq, true_and] using completed
    · simp only [Matrix.sum_apply, blockDiagonal'_apply, same, ↓reduceDIte, sum_const_zero, ne_eq,
        Sigma.mk.injEq, false_and, not_false_eq_true, one_apply_ne]

/-- The positive operator-valued measurement implementing reindexed. -/
def reindexedPOVM
    {C d e : Type*} [Fintype C]
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (basis : d ≃ e) (P : POVM C d) : POVM C e where
  effect c := (P.effect c).submatrix basis.symm basis.symm
  positive c := (P.positive c).submatrix basis.symm
  complete := by
    classical
    ext i j
    have completed := congrArg
      (fun M : Matrix d d ℂ => M (basis.symm i) (basis.symm j))
      P.complete
    simpa only [Matrix.sum_apply, submatrix_apply, Matrix.one_apply,
      EmbeddingLike.apply_eq_iff_eq] using completed

private def twoBlockPOVM
    {C d e : Type} [Fintype C]
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (P : POVM C d) (Q : POVM C e) :
    POVM C (d ⊕ e) := by
  classical
  letI : (b : Bool) → Fintype (bif b then e else d)
    | false => inferInstanceAs (Fintype d)
    | true => inferInstanceAs (Fintype e)
  letI : (b : Bool) → DecidableEq (bif b then e else d)
    | false => inferInstanceAs (DecidableEq d)
    | true => inferInstanceAs (DecidableEq e)
  let blocks : (b : Bool) → POVM C (bif b then e else d)
    | false => P
    | true => Q
  exact reindexedPOVM
    (Equiv.sumEquivSigmaBool d e).symm
    (dependentBlockPOVM blocks)

/-- The positive operator-valued measurement implementing deterministic outcome. -/
def deterministicOutcomePOVM
    {C d : Type*} [Fintype C] [DecidableEq C]
    [Fintype d] [DecidableEq d] (default : C) : POVM C d where
  effect c := if c = default then 1 else 0
  positive c := by
    split_ifs
    · exact Matrix.PosSemidef.one
    · exact Matrix.PosSemidef.zero
  complete := by
    classical
    simp only [sum_ite_eq', mem_univ, ↓reduceIte]

private def pOVMChangeDecidableEq
    {C d : Type*} [Fintype C] [Fintype d]
    (source target : DecidableEq d)
    (P : @POVM C d inferInstance inferInstance source) :
    @POVM C d inferInstance inferInstance target where
  effect c := @POVM.effect C d inferInstance inferInstance source P c
  positive c := @POVM.positive C d
    inferInstance inferInstance source P c
  complete := by
    classical
    ext i j
    have completed := congrArg
      (fun M : Matrix d d ℂ => M i j)
      (@POVM.complete C d inferInstance inferInstance source P)
    simp only [Matrix.sum_apply, Matrix.one_apply] at completed ⊢
    by_cases same : i = j
    · subst j
      simpa only [↓reduceIte] using completed
    · simpa only [same, ↓reduceIte] using completed

private def exactSourceAlicePaddedPOVM
    [DecidableEq A]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (x : X) :
    POVM A (ExactPaddedLocalIndex G n S D r) := by
  classical
  exact twoBlockPOVM
    (deterministicOutcomePOVM (d := PUnit) a₀)
    (twoBlockPOVM
      (exactSourceAliceRefinedPOVM G n S D r a₀ x)
      (deterministicOutcomePOVM
        (d := ExactBobLocalIndex G n S D r) a₀))

private def exactSourceBobPaddedPOVM
    [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (b₀ : B) (y : Y) :
    POVM B (ExactPaddedLocalIndex G n S D r) := by
  classical
  exact twoBlockPOVM
    (deterministicOutcomePOVM (d := PUnit) b₀)
    (twoBlockPOVM
      (deterministicOutcomePOVM
        (d := ExactAliceLocalIndex G n S D r) b₀)
      (exactSourceBobRefinedPOVM G n S D r b₀ y))

/-- The positive operator-valued measurement implementing exact source global alice. -/
def exactSourceGlobalAlicePOVM
    [DecidableEq A]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A) (x : X) :
    POVM A (ExactGlobalHistoryLocalIndex G n S D) := by
  classical
  let actual := twoBlockPOVM
    (deterministicOutcomePOVM (d := PUnit) a₀)
    (dependentBlockPOVM
      (fun r : ExactHistoryFlag X Y A B D =>
        exactSourceAlicePaddedPOVM G n S D r a₀ x))
  exact pOVMChangeDecidableEq
    (@instDecidableEqSum PUnit
      (Σ r : ExactHistoryFlag X Y A B D,
        ExactPaddedLocalIndex G n S D r)
      inferInstance inferInstance)
    (Classical.decEq
      (ExactGlobalHistoryLocalIndex G n S D))
    actual

/-- The positive operator-valued measurement implementing exact source global bob. -/
def exactSourceGlobalBobPOVM
    [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (b₀ : B) (y : Y) :
    POVM B (ExactGlobalHistoryLocalIndex G n S D) := by
  classical
  let actual := twoBlockPOVM
    (deterministicOutcomePOVM (d := PUnit) b₀)
    (dependentBlockPOVM
      (fun r : ExactHistoryFlag X Y A B D =>
        exactSourceBobPaddedPOVM G n S D r b₀ y))
  exact pOVMChangeDecidableEq
    (@instDecidableEqSum PUnit
      (Σ r : ExactHistoryFlag X Y A B D,
        ExactPaddedLocalIndex G n S D r)
      inferInstance inferInstance)
    (Classical.decEq
      (ExactGlobalHistoryLocalIndex G n S D))
    actual

/-- The positive operator-valued measurement implementing exact source global catalyst alice. -/
def exactSourceGlobalCatalystAlicePOVM
    [DecidableEq A]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (e : ℕ) (a₀ : A) (x : X) :
    POVM A
      (Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e)) := by
  classical
  exact reindexedPOVM finProdFinEquiv
    (purificationAlicePOVM (k := Fin e)
      (reindexedPOVM
        (Fintype.equivFin
          (ExactGlobalHistoryLocalIndex G n S D))
        (exactSourceGlobalAlicePOVM G n S D a₀ x)))

/-- The positive operator-valued measurement implementing exact source global catalyst bob. -/
def exactSourceGlobalCatalystBobPOVM
    [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (e : ℕ) (b₀ : B) (y : Y) :
    POVM B
      (Fin (Fintype.card
        (ExactGlobalHistoryLocalIndex G n S D) * e)) := by
  classical
  exact reindexedPOVM finProdFinEquiv
    (purificationAlicePOVM (k := Fin e)
      (reindexedPOVM
        (Fintype.equivFin
          (ExactGlobalHistoryLocalIndex G n S D))
        (exactSourceGlobalBobPOVM G n S D b₀ y)))

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace


attribute [local instance] Classical.propDecidable

@[simp] theorem twoBlockPOVM_effect_inl
    {C d e : Type} [Fintype C]
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (P : POVM C d) (Q : POVM C e)
    (c : C) (i j : d) :
    (twoBlockPOVM P Q).effect c
      (.inl i) (.inl j) = P.effect c i j := by
  classical
  simp only [twoBlockPOVM, reindexedPOVM, dependentBlockPOVM,
    Equiv.sumEquivSigmaBool, Bool.cond_false, Bool.cond_true,
    Equiv.symm_mk, Equiv.coe_fn_mk, submatrix_apply, Sum.elim_inl,
    blockDiagonal'_apply, ↓reduceDIte, cast_eq]

@[simp] theorem twoBlockPOVM_effect_inr
    {C d e : Type} [Fintype C]
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (P : POVM C d) (Q : POVM C e)
    (c : C) (i j : e) :
    (twoBlockPOVM P Q).effect c
      (.inr i) (.inr j) = Q.effect c i j := by
  classical
  simp only [twoBlockPOVM, reindexedPOVM, dependentBlockPOVM,
    Equiv.sumEquivSigmaBool, Bool.cond_false, Bool.cond_true,
    Equiv.symm_mk, Equiv.coe_fn_mk, submatrix_apply, Sum.elim_inr,
    blockDiagonal'_apply, ↓reduceDIte, cast_eq]

@[simp] theorem dependentBlockPOVM_effect_same
    {R C : Type*} [Fintype R] [DecidableEq R] [Fintype C]
    {ι : R → Type*}
    [∀ r, Fintype (ι r)] [∀ r, DecidableEq (ι r)]
    (P : (r : R) → POVM C (ι r))
    (r : R) (c : C) (i j : ι r) :
    (dependentBlockPOVM P).effect c
      ⟨r, i⟩ ⟨r, j⟩ = (P r).effect c i j := by
  classical
  simp only [dependentBlockPOVM, blockDiagonal'_apply, ↓reduceDIte, cast_eq]

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

@[simp] theorem exactSourceGlobalAlicePOVM_effect
    [DecidableEq A]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ a : A) (x : X)
    (i j : ExactAliceLocalIndex G n S D r) :
    (exactSourceGlobalAlicePOVM G n S D a₀ x).effect a
      (.inr ⟨r, .inr (.inl i)⟩)
      (.inr ⟨r, .inr (.inl j)⟩) =
      (exactSourceAliceRefinedPOVM G n S D r a₀ x).effect a i j := by
  classical
  simp only [exactSourceGlobalAlicePOVM, pOVMChangeDecidableEq, exactSourceAlicePaddedPOVM,
    twoBlockPOVM_effect_inr, dependentBlockPOVM_effect_same, twoBlockPOVM_effect_inl]

@[simp] theorem exactSourceGlobalBobPOVM_effect
    [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (b₀ b : B) (y : Y)
    (i j : ExactBobLocalIndex G n S D r) :
    (exactSourceGlobalBobPOVM G n S D b₀ y).effect b
      (.inr ⟨r, .inr (.inr i)⟩)
      (.inr ⟨r, .inr (.inr j)⟩) =
      (exactSourceBobRefinedPOVM G n S D r b₀ y).effect b i j := by
  classical
  simp only [exactSourceGlobalBobPOVM, pOVMChangeDecidableEq, exactSourceBobPaddedPOVM,
    twoBlockPOVM_effect_inr, dependentBlockPOVM_effect_same]

theorem matrixQuadraticExpectation_expand
    {d : Type*} [Fintype d] [DecidableEq d]
    (M : Matrix d d ℂ) (z : EuclideanSpace ℂ d) :
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) M) z =
      (∑ i : d, (∑ j : d, M i j * z j) * star (z i)).re := by
  simp only [quadraticExpectation, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    ofLp_toEuclideanCLM, mulVec, Pi.star_apply, RCLike.star_def, re_sum, mul_re, sum_sub_distrib,
    conj_re, im_sum, mul_im, conj_im, mul_neg, sub_neg_eq_add]

theorem finiteSum_injective_support
    {d e K : Type*} [Fintype d] [Fintype e] [AddCommMonoid K]
    (f : d → e) (injective : Function.Injective f)
    (g : e → K)
    (supported : ∀ j : e, (∀ i : d, f i ≠ j) → g j = 0) :
    (∑ j : e, g j) = ∑ i : d, g (f i) := by
  classical
  calc
    (∑ j : e, g j) = ∑ j ∈ Finset.univ.image f, g j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ outside
      apply supported j
      intro i same
      exact outside
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, same⟩)
    _ = ∑ i : d, g (f i) := by
      rw [Finset.sum_image]
      intro i _ j _ same
      exact injective same

theorem matrixQuadraticExpectation_injective
    {d e : Type*}
    [Fintype d] [Fintype e] [DecidableEq d] [DecidableEq e]
    (f : d → e) (injective : Function.Injective f)
    (M : Matrix e e ℂ) (N : Matrix d d ℂ)
    (v : EuclideanSpace ℂ e) (z : EuclideanSpace ℂ d)
    (included : ∀ i : d, v (f i) = z i)
    (supported : ∀ j : e, (∀ i : d, f i ≠ j) → v j = 0)
    (compressed : ∀ i j : d, M (f i) (f j) = N i j) :
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := e) (𝕜 := ℂ) M) v =
    quadraticExpectation
      (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) N) z := by
  classical
  rw [matrixQuadraticExpectation_expand,
    matrixQuadraticExpectation_expand]
  congr 1
  rw [finiteSum_injective_support f injective
    (fun i : e => (∑ j : e, M i j * v j) * star (v i))
    (by
      intro i outside
      simp only [supported i outside, star_zero, mul_zero])]
  apply Finset.sum_congr rfl
  intro i _
  rw [included i]
  congr 1
  rw [finiteSum_injective_support f injective
    (fun j : e => M (f i) j * v j)
    (by
      intro j outside
      simp only [supported j outside, mul_zero])]
  apply Finset.sum_congr rfl
  intro j _
  rw [compressed i j, included j]

private def exactSourceGlobalJointBasis
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :
    (ExactAliceLocalIndex G n S D r ×
      ExactBobLocalIndex G n S D r) →
      (ExactGlobalHistoryLocalIndex G n S D ×
        ExactGlobalHistoryLocalIndex G n S D)
  | (i, j) =>
    (.inr ⟨r, .inr (.inl i)⟩, .inr ⟨r, .inr (.inr j)⟩)

theorem exactSourceGlobalJointBasis_injective
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :
    Function.Injective (exactSourceGlobalJointBasis G n S D r) := by
  intro i j same
  rcases i with ⟨ia, ib⟩
  rcases j with ⟨ja, jb⟩
  have alice := congrArg Prod.fst same
  have bob := congrArg Prod.snd same
  change
    (Sum.inr ⟨r, .inr (.inl ia)⟩ :
      ExactGlobalHistoryLocalIndex G n S D) =
      Sum.inr ⟨r, .inr (.inl ja)⟩ at alice
  change
    (Sum.inr ⟨r, .inr (.inr ib)⟩ :
      ExactGlobalHistoryLocalIndex G n S D) =
      Sum.inr ⟨r, .inr (.inr jb)⟩ at bob
  have alice_block :
      (Sum.inr (.inl ia) : ExactPaddedLocalIndex G n S D r) =
        Sum.inr (.inl ja) :=
    eq_of_heq (Sigma.mk.inj (Sum.inr.inj alice)).2
  have bob_block :
      (Sum.inr (.inr ib) : ExactPaddedLocalIndex G n S D r) =
        Sum.inr (.inr jb) :=
    eq_of_heq (Sigma.mk.inj (Sum.inr.inj bob)).2
  have alice' : ia = ja :=
    Sum.inl.inj (Sum.inr.inj alice_block)
  have bob' : ib = jb :=
    Sum.inr.inj (Sum.inr.inj bob_block)
  exact Prod.ext alice' bob'

theorem exactSourceGlobalJointBasis_vector
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (z : EuclideanSpace ℂ
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r))
    (i : ExactAliceLocalIndex G n S D r ×
      ExactBobLocalIndex G n S D r) :
    exactGlobalHistoryVector G n S D r
        (exactPaddedVector G n S D r z)
        (exactSourceGlobalJointBasis G n S D r i) =
      z i := by
  rcases i with ⟨ia, ib⟩
  change
    (if ha : r = r then
      if hb : r = r then
        exactPaddedVector G n S D r z
          (ha ▸ Sum.inr (Sum.inl ia),
            hb ▸ Sum.inr (Sum.inr ib))
      else 0
    else 0) = z (ia, ib)
  simp only [exactPaddedVector, dite_true]

theorem exactSourceGlobalJointBasis_support
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (z : EuclideanSpace ℂ
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r))
    (j : ExactGlobalHistoryLocalIndex G n S D ×
      ExactGlobalHistoryLocalIndex G n S D)
    (outside : ∀ i, exactSourceGlobalJointBasis
      G n S D r i ≠ j) :
    exactGlobalHistoryVector G n S D r
      (exactPaddedVector G n S D r z) j = 0 := by
  classical
  rcases j with ⟨u, v⟩
  rcases u with u | ⟨ru, u⟩
  · rfl
  rcases v with v | ⟨rv, v⟩
  · rfl
  change
    (if ha : ru = r then
      if hb : rv = r then
        exactPaddedVector G n S D r z
          (ha ▸ u, hb ▸ v)
      else 0
    else 0) = 0
  by_cases hu : ru = r
  · subst ru
    by_cases hv : rv = r
    · subst rv
      simp only [dite_true]
      rcases u with u | (u | u)
      · rfl
      · rcases v with v | (v | v)
        · rfl
        · rfl
        · exact False.elim
            (outside (u, v)
              (by rfl))
      · rfl
    · simp only [dite_eq_right hv, dite_true]
  · simp only [dite_eq_right hu]

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace


open QuantumParallelRepetition.ClassicalSampling

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The measurement effect for exact source global winning. -/
def exactSourceGlobalWinningEffect
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (a₀ : A) (b₀ : B) (x : X) (y : Y) :
    Matrix
      (ExactGlobalHistoryLocalIndex G n S D ×
        ExactGlobalHistoryLocalIndex G n S D)
      (ExactGlobalHistoryLocalIndex G n S D ×
        ExactGlobalHistoryLocalIndex G n S D) ℂ :=
  ∑ a : A, ∑ b : B,
    if G.predicate x y a b = true then
      (exactSourceGlobalAlicePOVM G n S D a₀ x).effect a ⊗ₖ
        (exactSourceGlobalBobPOVM G n S D b₀ y).effect b
    else 0

theorem exactSourceGlobalWinningEffect_compression
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (b₀ : B) (x : X) (y : Y)
    (i j : ExactAliceLocalIndex G n S D r ×
      ExactBobLocalIndex G n S D r) :
    exactSourceGlobalWinningEffect G n S D a₀ b₀ x y
      (exactSourceGlobalJointBasis G n S D r i)
      (exactSourceGlobalJointBasis G n S D r j) =
      exactSourceWinningEffect G n S D r a₀ b₀ x y i j := by
  classical
  rcases i with ⟨ia, ib⟩
  rcases j with ⟨ja, jb⟩
  simp only [exactSourceGlobalWinningEffect,
    exactSourceWinningEffect, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs
  · simp only [exactSourceGlobalJointBasis,
      exactSourceJointEffect, Matrix.kroneckerMap_apply,
      exactSourceGlobalAlicePOVM_effect,
      exactSourceGlobalBobPOVM_effect]
  · rfl

theorem exactSourceGlobalWinningEffect_quadratic
    [DecidableEq A] [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (r : ExactHistoryFlag X Y A B D)
    (a₀ : A) (b₀ : B) (x : X) (y : Y)
    (z : EuclideanSpace ℂ
      (ExactAliceLocalIndex G n S D r ×
        ExactBobLocalIndex G n S D r)) :
    quadraticExpectation
      (Matrix.toEuclideanCLM
        (n := ExactGlobalHistoryLocalIndex G n S D ×
          ExactGlobalHistoryLocalIndex G n S D)
        (𝕜 := ℂ)
        (exactSourceGlobalWinningEffect G n S D a₀ b₀ x y))
      (exactGlobalHistoryVector G n S D r
        (exactPaddedVector G n S D r z)) =
      quadraticExpectation
        (exactSourceWinningEffectCLM G n S D r a₀ b₀ x y)
        z := by
  classical
  unfold exactSourceWinningEffectCLM
  apply matrixQuadraticExpectation_injective
    (exactSourceGlobalJointBasis G n S D r)
    (exactSourceGlobalJointBasis_injective G n S D r)
  · exact exactSourceGlobalJointBasis_vector G n S D r z
  · exact exactSourceGlobalJointBasis_support G n S D r z
  · exact exactSourceGlobalWinningEffect_compression
      G n S D r a₀ b₀ x y

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder


attribute [local instance] Classical.propDecidable

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

@[simp] theorem reindexedCatalystPOVM_effect
    {C d : Type*} [Fintype C] [Fintype d] [DecidableEq d]
    (P : POVM C d) (e : ℕ) (c : C)
    (i j : d) (k l : Fin e) :
    (reindexedPOVM finProdFinEquiv
      (purificationAlicePOVM (k := Fin e)
        (reindexedPOVM (Fintype.equivFin d) P))).effect c
      (finProdFinEquiv ((Fintype.equivFin d) i, k))
      (finProdFinEquiv ((Fintype.equivFin d) j, l)) =
      P.effect c i j * (if k = l then 1 else 0) := by
  classical
  simp only [reindexedPOVM, purificationAlicePOVM, submatrix_apply, Equiv.symm_apply_apply,
    kroneckerMap_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero]

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

@[simp] theorem exactSourceGlobalCatalystBobPOVM_effect
    [DecidableEq B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (e : ℕ) (b₀ b : B) (y : Y)
    (i j : ExactGlobalHistoryLocalIndex G n S D)
    (k l : Fin e) :
    (exactSourceGlobalCatalystBobPOVM G n S D e b₀ y).effect b
      (finProdFinEquiv
        (Fintype.equivFin
          (ExactGlobalHistoryLocalIndex G n S D) i, k))
      (finProdFinEquiv
        (Fintype.equivFin
          (ExactGlobalHistoryLocalIndex G n S D) j, l)) =
      (exactSourceGlobalBobPOVM G n S D b₀ y).effect b i j *
        (if k = l then 1 else 0) := by
  classical
  simp only [exactSourceGlobalCatalystBobPOVM, reindexedPOVM, purificationAlicePOVM,
    submatrix_apply, Equiv.symm_apply_apply, kroneckerMap_apply, Matrix.one_apply, mul_ite,
    mul_one, mul_zero]

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem reweightedSeedPrefixEntropyIncrement_eq_actual_atom_sum
    {K Ω V : Type*} [Fintype K] [Fintype Ω] [Fintype V]
    {h : ℕ}
    (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (projection : K × ExactOutcome X Y A B n →
      Ω × (Fin h → V))
    (default : V) (k : Fin h) :
    reweightedSeedPrefixEntropyIncrement
        seedLaw G n S D projection default k =
      ∑ point : K × ExactOutcome X Y A B n,
        reweightedSeedPosterior seedLaw G n S D point *
          finiteRelativeEntropy
            (jointConditional
              (groupedMass (exactPrefixNextCode default k)
                (reweightedSeedPrefixJoint
                  seedLaw G n S D projection))
              (finitePrefixMask default k.castSucc
                (((projection point).1,
                  repeatedConditionedAnswerFlag
                    G n S D point.2),
                  (projection point).2)))
            (jointConditional
              (groupedMass (exactPrefixNextCode default k)
                (reweightedSeedPrefixPrior
                  seedLaw G n S D projection))
              (finitePrefixMask default k.castSucc
                (((projection point).1,
                  repeatedConditionedAnswerFlag
                    G n S D point.2),
                  (projection point).2))) := by
  classical
  let joint := reweightedSeedPrefixJoint
    seedLaw G n S D projection
  let prior := reweightedSeedPrefixPrior
    seedLaw G n S D projection
  let posterior := reweightedSeedPosterior
    seedLaw G n S D
  let augmented :
      K × ExactOutcome X Y A B n →
        (Ω × ConditionedAnswerFlag A B D) ×
          (Fin h → V) :=
    fun point =>
      (((projection point).1,
        repeatedConditionedAnswerFlag G n S D point.2),
        (projection point).2)
  let posteriorNext :=
    groupedMass (exactPrefixNextCode default k) joint
  let priorNext :=
    groupedMass (exactPrefixNextCode default k) prior
  let score :
      (Ω × ConditionedAnswerFlag A B D) ×
        (Fin h → V) → ℝ :=
    fun context =>
      finiteRelativeEntropy
        (jointConditional posteriorNext
          (finitePrefixMask default k.castSucc context))
        (jointConditional priorNext
          (finitePrefixMask default k.castSucc context))
  have hjoint : joint = groupedMass augmented posterior := by
    funext target
    exact reweightedSeedPrefixJoint_as_actual_flagged_pushforward
      seedLaw G n S D projection target
  calc
    reweightedSeedPrefixEntropyIncrement
        seedLaw G n S D projection default k =
      ∑ context :
        (Ω × ConditionedAnswerFlag A B D) ×
          (Fin h → V),
        groupedMass
            (finitePrefixMask default k.castSucc)
            joint context *
          finiteRelativeEntropy
            (jointConditional posteriorNext context)
            (jointConditional priorNext context) :=
      reweightedSeedPrefixEntropyIncrement_eq_conditional
        seedLaw G n S D positive projection default k
    _ = ∑ context :
        (Ω × ConditionedAnswerFlag A B D) ×
          (Fin h → V),
        jointFirstMarginal posteriorNext context *
          finiteRelativeEntropy
            (jointConditional posteriorNext context)
            (jointConditional priorNext context) := by
      apply Finset.sum_congr rfl
      intro context _
      congr 1
      convert (congrFun
        (exactPrefixNext_firstMarginal joint default k)
        context).symm using 1
      · exact congrFun
          (exactGroupedMass_decidableEq_irrel _ _
            (finitePrefixMask default k.castSucc) joint)
          context
      · exact congrArg
          (fun law => jointFirstMarginal law context)
          (exactGroupedMass_decidableEq_irrel _ _
            (exactPrefixNextCode default k) joint)
    _ = ∑ target :
        (Ω × ConditionedAnswerFlag A B D) ×
          (Fin h → V),
        joint target * score target := by
      exact finiteNextInformation_eq_atom_sum
        (finitePrefixMask default k.castSucc)
        (fun target :
          (Ω × ConditionedAnswerFlag A B D) ×
            (Fin h → V) => target.2 k)
        joint
        (fun context => jointConditional priorNext context)
    _ = ∑ point : K × ExactOutcome X Y A B n,
        posterior point * score (augmented point) := by
      rw [hjoint]
      exact finiteGroupedExpectation_eq_atom_sum
        augmented posterior score
    _ = _ := rfl

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem exactStrategyQuestionCodeGroupedMass
    {C : Type*} [DecidableEq C]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (code : (Fin n → X) → (Fin n → Y) → C)
    (target : C) :
    groupedMass
        (fun outcome : ExactOutcome X Y A B n =>
          code outcome.1 outcome.2.1)
        (strategyEventLaw (G.repeat n) S).weight target =
      ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
        if code xs ys = target then
          (G.repeat n).questionWeight xs ys
        else 0 := by
  classical
  unfold groupedMass
  rw [Finset.sum_filter]
  simp only [Fintype.sum_prod_type]
  change
    (∑ xs : Fin n → X, ∑ ys : Fin n → Y,
      ∑ answersA : Fin n → A, ∑ answersB : Fin n → B,
        if code xs ys = target then
          (G.repeat n).questionWeight xs ys *
            S.outcomeProbability xs ys answersA answersB
        else 0) = _
  apply Finset.sum_congr rfl
  intro xs _
  apply Finset.sum_congr rfl
  intro ys _
  by_cases compatible : code xs ys = target
  · simp only [ite_eq_left compatible]
    calc
      (∑ answersA : Fin n → A, ∑ answersB : Fin n → B,
        (G.repeat n).questionWeight xs ys *
          S.outcomeProbability xs ys answersA answersB) =
        (G.repeat n).questionWeight xs ys *
          (∑ answersA : Fin n → A, ∑ answersB : Fin n → B,
            S.outcomeProbability xs ys answersA answersB) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro answersA _
              rw [Finset.mul_sum]
      _ = (G.repeat n).questionWeight xs ys := by
        rw [S.outcomeProbability_normalized xs ys]
        ring
  · simp only [compatible, ↓reduceIte, sum_const_zero]

theorem exactRepeatedQuestionWeight_splitAt_bob
    (G : Game X Y A B) (n : ℕ)
    (i : Fin n) (xs : Fin n → X)
    (y : Y) (tail : {j : Fin n // j ≠ i} → Y) :
    (G.repeat n).questionWeight xs
        ((Equiv.funSplitAt i Y).symm (y, tail)) =
      G.questionWeight (xs i) y *
        ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
          G.questionWeight (xs j)
            ((Equiv.funSplitAt i Y).symm (y, tail) j) := by
  classical
  rw [Game.repeat_questionWeight]
  rw [← Finset.mul_prod_erase
    (Finset.univ : Finset (Fin n))
    (fun j : Fin n =>
      G.questionWeight (xs j)
        ((Equiv.funSplitAt i Y).symm (y, tail) j))
    (Finset.mem_univ i)]
  simp only [ne_eq, Equiv.funSplitAt, Equiv.piSplitAt, eq_rec_constant, Equiv.symm_mk,
    Equiv.coe_fn_mk, ↓reduceDIte]

theorem exactRepeatedQuestionTail_splitAt_bob
    (G : Game X Y A B) (n : ℕ)
    (i : Fin n) (xs : Fin n → X)
    (y y' : Y) (tail : {j : Fin n // j ≠ i} → Y) :
    (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
      G.questionWeight (xs j)
        ((Equiv.funSplitAt i Y).symm (y, tail) j)) =
    (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i,
      G.questionWeight (xs j)
        ((Equiv.funSplitAt i Y).symm (y', tail) j)) := by
  classical
  apply Finset.prod_congr rfl
  intro j hj
  have different : j ≠ i := (Finset.mem_erase.mp hj).1
  simp only [ne_eq, Equiv.funSplitAt, Equiv.piSplitAt, eq_rec_constant, Equiv.symm_mk,
    Equiv.coe_fn_mk, different, ↓reduceDIte]

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem exactStrategyStableBobQuestionCode_joint_factor
    {C : Type*} [DecidableEq C]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (coordinate : Fin n)
    (code : (Fin n → X) → (Fin n → Y) → C)
    (target : C) (question : X) (next : Y)
    (stable : ∀ (xs : Fin n → X)
      (tail : {j : Fin n // j ≠ coordinate} → Y)
      (y y' : Y),
      code xs ((Equiv.funSplitAt coordinate Y).symm (y, tail)) =
        code xs ((Equiv.funSplitAt coordinate Y).symm (y', tail)))
    (determines : ∀ (xs : Fin n → X) (ys : Fin n → Y),
      code xs ys = target → xs coordinate = question) :
    groupedMass
        (fun outcome : ExactOutcome X Y A B n =>
          (code outcome.1 outcome.2.1,
            outcome.2.1 coordinate))
        (strategyEventLaw (G.repeat n) S).weight
        (target, next) =
      G.conditionalYGivenX question next *
        groupedMass
          (fun outcome : ExactOutcome X Y A B n =>
            code outcome.1 outcome.2.1)
          (strategyEventLaw (G.repeat n) S).weight target := by
  classical
  rw [exactStrategyQuestionCodeGroupedMass
    G n S (fun xs ys => (code xs ys, ys coordinate))
    (target, next),
    exactStrategyQuestionCodeGroupedMass G n S code target]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro xs _
  let split := Equiv.funSplitAt coordinate Y
  have hsplit (f : (Fin n → Y) → ℝ) :
      (∑ ys : Fin n → Y, f ys) =
        ∑ pair : Y × ({j : Fin n // j ≠ coordinate} → Y),
          f (split.symm pair) :=
    (split.symm.sum_comp f).symm
  rw [hsplit
    (fun ys => if (code xs ys, ys coordinate) = (target, next)
      then (G.repeat n).questionWeight xs ys else 0),
    hsplit
      (fun ys => if code xs ys = target
        then (G.repeat n).questionWeight xs ys else 0)]
  simp only [Fintype.sum_prod_type]
  conv_lhs =>
    rw [Finset.sum_comm]
  conv_rhs =>
    arg 2
    rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro tail _
  have same_code (y : Y) :
      code xs (split.symm (y, tail)) =
        code xs (split.symm (next, tail)) :=
    stable xs tail y next
  have same_tail (y : Y) :
      (∏ j ∈ (Finset.univ : Finset (Fin n)).erase coordinate,
        G.questionWeight (xs j)
          (split.symm (y, tail) j)) =
      ∏ j ∈ (Finset.univ : Finset (Fin n)).erase coordinate,
        G.questionWeight (xs j)
          (split.symm (next, tail) j) :=
    exactRepeatedQuestionTail_splitAt_bob
      G n coordinate xs y next tail
  by_cases compatible :
      code xs (split.symm (next, tail)) = target
  · have hx : xs coordinate = question :=
      determines xs (split.symm (next, tail)) compatible
    have marked (y : Y) : split.symm (y, tail) coordinate = y := by
      simp only [ne_eq, Equiv.funSplitAt, Equiv.piSplitAt, eq_rec_constant, Equiv.symm_mk,
        Equiv.coe_fn_mk, ↓reduceDIte, split]
    simp_rw [same_code, marked]
    simp only [compatible, Prod.mk.injEq, true_and, ↓reduceIte]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    have hweight (y : Y) :
        (G.repeat n).questionWeight xs (split.symm (y, tail)) =
          G.questionWeight (xs coordinate) y *
            (∏ j ∈ (Finset.univ : Finset (Fin n)).erase coordinate,
              G.questionWeight (xs j)
                (split.symm (next, tail) j)) := by
      calc
        (G.repeat n).questionWeight xs (split.symm (y, tail)) =
          G.questionWeight (xs coordinate) y *
            (∏ j ∈ (Finset.univ : Finset (Fin n)).erase coordinate,
              G.questionWeight (xs j)
                (split.symm (y, tail) j)) := by
            exact exactRepeatedQuestionWeight_splitAt_bob
              G n coordinate xs y tail
        _ = _ := by rw [same_tail y]
    simp_rw [hweight]
    rw [← Finset.sum_mul]
    change
      G.questionWeight (xs coordinate) next * _ =
        G.conditionalYGivenX question next *
          (G.marginalX (xs coordinate) * _)
    rw [hx]
    rw [← G.marginalX_mul_conditionalYGivenX question next]
    ring
  · simp_rw [same_code]
    simp only [ne_eq, Prod.mk.injEq, compatible, false_and, ↓reduceIte, sum_const_zero, mul_zero]

theorem exactRepeatedQuestionWeight_splitAt_alice
    (G : Game X Y A B) (n : ℕ)
    (coordinate : Fin n) (ys : Fin n → Y)
    (x : X) (tail : {j : Fin n // j ≠ coordinate} → X) :
    (G.repeat n).questionWeight
        ((Equiv.funSplitAt coordinate X).symm (x, tail)) ys =
      G.questionWeight x (ys coordinate) *
        ∏ j ∈ (Finset.univ : Finset (Fin n)).erase coordinate,
          G.questionWeight
            ((Equiv.funSplitAt coordinate X).symm (x, tail) j)
            (ys j) := by
  classical
  rw [Game.repeat_questionWeight]
  rw [← Finset.mul_prod_erase
    (Finset.univ : Finset (Fin n))
    (fun j : Fin n =>
      G.questionWeight
        ((Equiv.funSplitAt coordinate X).symm (x, tail) j)
        (ys j))
    (Finset.mem_univ coordinate)]
  simp only [ne_eq, Equiv.funSplitAt, Equiv.piSplitAt, eq_rec_constant, Equiv.symm_mk,
    Equiv.coe_fn_mk, ↓reduceDIte]

theorem exactRepeatedQuestionTail_splitAt_alice
    (G : Game X Y A B) (n : ℕ)
    (coordinate : Fin n) (ys : Fin n → Y)
    (x x' : X) (tail : {j : Fin n // j ≠ coordinate} → X) :
    (∏ j ∈ (Finset.univ : Finset (Fin n)).erase coordinate,
      G.questionWeight
        ((Equiv.funSplitAt coordinate X).symm (x, tail) j)
        (ys j)) =
    ∏ j ∈ (Finset.univ : Finset (Fin n)).erase coordinate,
      G.questionWeight
        ((Equiv.funSplitAt coordinate X).symm (x', tail) j)
        (ys j) := by
  classical
  apply Finset.prod_congr rfl
  intro j hj
  have different : j ≠ coordinate := (Finset.mem_erase.mp hj).1
  simp only [ne_eq, Equiv.funSplitAt, Equiv.piSplitAt, eq_rec_constant, Equiv.symm_mk,
    Equiv.coe_fn_mk, different, ↓reduceDIte]

theorem exactStrategyStableAliceQuestionCode_joint_factor
    {C : Type*} [DecidableEq C]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (coordinate : Fin n)
    (code : (Fin n → X) → (Fin n → Y) → C)
    (target : C) (question : Y) (next : X)
    (stable : ∀ (ys : Fin n → Y)
      (tail : {j : Fin n // j ≠ coordinate} → X)
      (x x' : X),
      code ((Equiv.funSplitAt coordinate X).symm (x, tail)) ys =
        code ((Equiv.funSplitAt coordinate X).symm (x', tail)) ys)
    (determines : ∀ (xs : Fin n → X) (ys : Fin n → Y),
      code xs ys = target → ys coordinate = question) :
    groupedMass
        (fun outcome : ExactOutcome X Y A B n =>
          (code outcome.1 outcome.2.1,
            outcome.1 coordinate))
        (strategyEventLaw (G.repeat n) S).weight
        (target, next) =
      G.conditionalXGivenY question next *
        groupedMass
          (fun outcome : ExactOutcome X Y A B n =>
            code outcome.1 outcome.2.1)
          (strategyEventLaw (G.repeat n) S).weight target := by
  classical
  rw [exactStrategyQuestionCodeGroupedMass
    G n S (fun xs ys => (code xs ys, xs coordinate))
    (target, next),
    exactStrategyQuestionCodeGroupedMass G n S code target]
  conv_lhs =>
    rw [Finset.sum_comm]
  conv_rhs =>
    arg 2
    rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ys _
  let split := Equiv.funSplitAt coordinate X
  have hsplit (f : (Fin n → X) → ℝ) :
      (∑ xs : Fin n → X, f xs) =
        ∑ pair : X × ({j : Fin n // j ≠ coordinate} → X),
          f (split.symm pair) :=
    (split.symm.sum_comp f).symm
  rw [hsplit
    (fun xs => if (code xs ys, xs coordinate) = (target, next)
      then (G.repeat n).questionWeight xs ys else 0),
    hsplit
      (fun xs => if code xs ys = target
        then (G.repeat n).questionWeight xs ys else 0)]
  simp only [Fintype.sum_prod_type]
  conv_lhs =>
    rw [Finset.sum_comm]
  conv_rhs =>
    arg 2
    rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro tail _
  have same_code (x : X) :
      code (split.symm (x, tail)) ys =
        code (split.symm (next, tail)) ys :=
    stable ys tail x next
  have same_tail (x : X) :
      (∏ j ∈ (Finset.univ : Finset (Fin n)).erase coordinate,
        G.questionWeight
          (split.symm (x, tail) j) (ys j)) =
      ∏ j ∈ (Finset.univ : Finset (Fin n)).erase coordinate,
        G.questionWeight
          (split.symm (next, tail) j) (ys j) :=
    exactRepeatedQuestionTail_splitAt_alice
      G n coordinate ys x next tail
  by_cases compatible :
      code (split.symm (next, tail)) ys = target
  · have hy : ys coordinate = question :=
      determines (split.symm (next, tail)) ys compatible
    have marked (x : X) : split.symm (x, tail) coordinate = x := by
      simp only [ne_eq, Equiv.funSplitAt, Equiv.piSplitAt, eq_rec_constant, Equiv.symm_mk,
        Equiv.coe_fn_mk, ↓reduceDIte, split]
    simp_rw [same_code, marked]
    simp only [compatible, Prod.mk.injEq, true_and, ↓reduceIte]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    have hweight (x : X) :
        (G.repeat n).questionWeight (split.symm (x, tail)) ys =
          G.questionWeight x (ys coordinate) *
            (∏ j ∈ (Finset.univ : Finset (Fin n)).erase coordinate,
              G.questionWeight
                (split.symm (next, tail) j) (ys j)) := by
      calc
        (G.repeat n).questionWeight (split.symm (x, tail)) ys =
          G.questionWeight x (ys coordinate) *
            (∏ j ∈ (Finset.univ : Finset (Fin n)).erase coordinate,
              G.questionWeight
                (split.symm (x, tail) j) (ys j)) := by
            exact exactRepeatedQuestionWeight_splitAt_alice
              G n coordinate ys x tail
        _ = _ := by rw [same_tail x]
    simp_rw [hweight]
    rw [← Finset.sum_mul]
    change
      G.questionWeight next (ys coordinate) * _ =
        G.conditionalXGivenY question next *
          (G.marginalY (ys coordinate) * _)
    rw [hy]
    rw [← G.marginalY_mul_conditionalXGivenY next question]
    ring
  · simp_rw [same_code]
    simp only [ne_eq, Prod.mk.injEq, compatible, false_and, ↓reduceIte, sum_const_zero, mul_zero]

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

private def exactAliceSourceAtomCode
    {n : ℕ} (D : Finset (Fin n)) :
    ExactJointOutcome X Y A B D →
      (SourceRemainingCoordinate D × X) ×
        (ExactHistoryFlag X Y A B D × Y) :=
  fun point =>
    ((point.1.coordinate, point.2.1 point.1.coordinate.val),
      (exactHistoryCode D point,
        point.2.2.1 point.1.coordinate.val))

private def exactBobSourceAtomCode
    {n : ℕ} (D : Finset (Fin n)) :
    ExactJointOutcome X Y A B D →
      (SourceRemainingCoordinate D × Y) ×
        (ExactHistoryFlag X Y A B D × X) :=
  fun point =>
    ((point.1.coordinate, point.2.2.1 point.1.coordinate.val),
      (exactHistoryCode D point,
        point.2.1 point.1.coordinate.val))

theorem exactAliceInformationPosterior_eq_jointPushforward
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :
    exactAliceInformationPosterior G n S D =
      groupedMass
        (exactAliceSourceAtomCode
          (X := X) (Y := Y) (A := A) (B := B) D)
        (exactPostselectedJointLaw G n S D) := by
  classical
  funext target
  unfold exactAliceInformationPosterior
    exactLocallySampleableLaw
    exactSourcePushforward groupedMass
  apply Finset.sum_congr
  · ext point
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change
      (exactLocallySampleableCode D point =
        (exactAliceInformationEquiv
          (X := X) (Y := Y) (A := A) (B := B) D).symm target) ↔
      (exactAliceInformationEquiv
        (X := X) (Y := Y) (A := A) (B := B) D)
          (exactLocallySampleableCode D point) = target
    exact (exactAliceInformationEquiv
      (X := X) (Y := Y) (A := A) (B := B) D).eq_symm_apply
  · intro point _
    rfl

theorem exactBobInformationPosterior_eq_jointPushforward
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :
    exactBobInformationPosterior G n S D =
      groupedMass
        (exactBobSourceAtomCode
          (X := X) (Y := Y) (A := A) (B := B) D)
        (exactPostselectedJointLaw G n S D) := by
  classical
  funext target
  unfold exactBobInformationPosterior
    exactLocallySampleableLaw
    exactSourcePushforward groupedMass
  apply Finset.sum_congr
  · ext point
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change
      (exactLocallySampleableCode D point =
        (exactBobInformationEquiv
          (X := X) (Y := Y) (A := A) (B := B) D).symm target) ↔
      (exactBobInformationEquiv
        (X := X) (Y := Y) (A := A) (B := B) D)
          (exactLocallySampleableCode D point) = target
    exact (exactBobInformationEquiv
      (X := X) (Y := Y) (A := A) (B := B) D).eq_symm_apply
  · intro point _
    rfl

theorem exactAliceSourceConditionalInformation_eq_joint_atom_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D) :
    exactAliceSourceConditionalInformation G n S D base =
      ∑ point : ExactJointOutcome X Y A B D,
        exactPostselectedJointLaw G n S D point *
          finiteRelativeEntropy
            (jointConditional
              (fun atom :
                ((SourceRemainingCoordinate D × X) ×
                  ExactHistoryFlag X Y A B D) × Y =>
                exactAliceInformationPosterior G n S D
                  (atom.1.1, (atom.1.2, atom.2)))
              ((point.1.coordinate,
                point.2.1 point.1.coordinate.val),
                exactHistoryCode D point))
            (G.conditionalYGivenX
              (point.2.1 point.1.coordinate.val)) := by
  classical
  let posterior := exactAliceInformationPosterior G n S D
  let code := exactAliceSourceAtomCode
    (X := X) (Y := Y) (A := A) (B := B) D
  let joint := exactPostselectedJointLaw G n S D
  let score : (SourceRemainingCoordinate D × X) ×
      (ExactHistoryFlag X Y A B D × Y) → ℝ :=
    fun point =>
      finiteRelativeEntropy
        (jointConditional
          (fun atom :
            ((SourceRemainingCoordinate D × X) ×
              ExactHistoryFlag X Y A B D) × Y =>
            posterior (atom.1.1, (atom.1.2, atom.2)))
          (point.1, point.2.1))
        (G.conditionalYGivenX point.1.2)
  have hsource := exactAliceSourceConditionalInformation_eq_atom_sum
    G n S D remaining positive base
  change
    exactAliceSourceConditionalInformation G n S D base =
      ∑ point, posterior point * score point at hsource
  have hposterior : posterior = groupedMass code joint :=
    exactAliceInformationPosterior_eq_jointPushforward
      G n S D
  calc
    exactAliceSourceConditionalInformation G n S D base =
      ∑ point, posterior point * score point := hsource
    _ = ∑ point : ExactJointOutcome X Y A B D,
        joint point * score (code point) := by
          rw [hposterior]
          exact finiteGroupedExpectation_eq_atom_sum
            code joint score
    _ = _ := rfl

theorem exactBobSourceConditionalInformation_eq_joint_atom_sum
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D) :
    exactBobSourceConditionalInformation G n S D base =
      ∑ point : ExactJointOutcome X Y A B D,
        exactPostselectedJointLaw G n S D point *
          finiteRelativeEntropy
            (jointConditional
              (fun atom :
                ((SourceRemainingCoordinate D × Y) ×
                  ExactHistoryFlag X Y A B D) × X =>
                exactBobInformationPosterior G n S D
                  (atom.1.1, (atom.1.2, atom.2)))
              ((point.1.coordinate,
                point.2.2.1 point.1.coordinate.val),
                exactHistoryCode D point))
            (G.conditionalXGivenY
              (point.2.2.1 point.1.coordinate.val)) := by
  classical
  let posterior := exactBobInformationPosterior G n S D
  let code := exactBobSourceAtomCode
    (X := X) (Y := Y) (A := A) (B := B) D
  let joint := exactPostselectedJointLaw G n S D
  let score : (SourceRemainingCoordinate D × Y) ×
      (ExactHistoryFlag X Y A B D × X) → ℝ :=
    fun point =>
      finiteRelativeEntropy
        (jointConditional
          (fun atom :
            ((SourceRemainingCoordinate D × Y) ×
              ExactHistoryFlag X Y A B D) × X =>
            posterior (atom.1.1, (atom.1.2, atom.2)))
          (point.1, point.2.1))
        (G.conditionalXGivenY point.1.2)
  have hsource := exactBobSourceConditionalInformation_eq_atom_sum
    G n S D remaining positive base
  change
    exactBobSourceConditionalInformation G n S D base =
      ∑ point, posterior point * score point at hsource
  have hposterior : posterior = groupedMass code joint :=
    exactBobInformationPosterior_eq_jointPushforward
      G n S D
  calc
    exactBobSourceConditionalInformation G n S D base =
      ∑ point, posterior point * score point := hsource
    _ = ∑ point : ExactJointOutcome X Y A B D,
        joint point * score (code point) := by
          rw [hposterior]
          exact finiteGroupedExpectation_eq_atom_sum
            code joint score
    _ = _ := rfl

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

theorem exactSeedWeight_pos_of_seed
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    0 < exactSeedWeight seed := by
  have nonempty : 0 < Fintype.card M :=
    Fintype.card_pos_iff.mpr ⟨seed.coordinate⟩
  have bits : 0 < Fintype.card (M → Bool) :=
    Fintype.card_pos_iff.mpr ⟨fun _ => false⟩
  have left :
      0 < Fintype.card
        (Equiv.Perm
          {j : M // j ∈
            exactLeft seed.coordinate seed.partition}) :=
    Fintype.card_pos_iff.mpr ⟨Equiv.refl _⟩
  have right :
      0 < Fintype.card
        (Equiv.Perm
          {j : M // j ∈
            exactRight seed.coordinate seed.partition}) :=
    Fintype.card_pos_iff.mpr ⟨Equiv.refl _⟩
  unfold exactSeedWeight
  positivity

theorem jointConditional_product_context_seed
    {K Ω C V : Type*}
    [Fintype K] [Fintype Ω] [Fintype V]
    (context : K → Ω → C)
    (next : K → Ω → V)
    (seedWeight : K → ℝ)
    (outcomeWeight : Ω → ℝ)
    (seed : K) (target : C)
    (nonzero : seedWeight seed ≠ 0) :
    jointConditional
        (groupedMass
          (fun q : K × Ω =>
            ((q.1, context q.1 q.2), next q.1 q.2))
          (fun q : K × Ω =>
            seedWeight q.1 * outcomeWeight q.2))
        (seed, target) =
      jointConditional
        (groupedMass
          (fun outcome : Ω =>
            (context seed outcome, next seed outcome))
          outcomeWeight)
        target := by
  classical
  have atom (value : V) :
      groupedMass
          (fun q : K × Ω =>
            ((q.1, context q.1 q.2), next q.1 q.2))
          (fun q : K × Ω =>
            seedWeight q.1 * outcomeWeight q.2)
          ((seed, target), value) =
        seedWeight seed *
          groupedMass
            (fun outcome : Ω =>
              (context seed outcome, next seed outcome))
            outcomeWeight (target, value) := by
    calc
      groupedMass
          (fun q : K × Ω =>
            ((q.1, context q.1 q.2), next q.1 q.2))
          (fun q : K × Ω =>
            seedWeight q.1 * outcomeWeight q.2)
          ((seed, target), value) =
        groupedMass
          (fun q : K × Ω =>
            (q.1, (context q.1 q.2, next q.1 q.2)))
          (fun q : K × Ω =>
            seedWeight q.1 * outcomeWeight q.2)
          (seed, (target, value)) := by
            unfold groupedMass
            apply Finset.sum_congr
            · ext q
              simp only [Prod.mk.injEq, and_assoc, mem_filter, mem_univ, true_and]
            · intro q _
              rfl
      _ = seedWeight seed *
          groupedMass
            (fun outcome : Ω =>
              (context seed outcome, next seed outcome))
            outcomeWeight (target, value) := by
            exact groupedMass_product_injective_seed
              (fun k : K => k) (fun _ _ equal => equal)
              (fun k outcome =>
                (context k outcome, next k outcome))
              seedWeight outcomeWeight seed (target, value)
  funext value
  unfold jointConditional jointFirstMarginal
  simp_rw [atom]
  rw [← Finset.mul_sum]
  exact mul_div_mul_left _ _ nonzero

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem exactAliceSourceContextNextPosterior_eq_groupedMass
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :
    (fun atom :
      ((SourceRemainingCoordinate D × X) ×
        ExactHistoryFlag X Y A B D) × Y =>
      exactAliceInformationPosterior G n S D
        (atom.1.1, (atom.1.2, atom.2))) =
      groupedMass
        (fun point : ExactJointOutcome X Y A B D =>
          (((point.1.coordinate,
              point.2.1 point.1.coordinate.val),
            exactHistoryCode D point),
            point.2.2.1 point.1.coordinate.val))
        (exactPostselectedJointLaw G n S D) := by
  classical
  funext atom
  rcases atom with ⟨⟨⟨coordinate, question⟩, history⟩, next⟩
  rw [exactAliceInformationPosterior_eq_jointPushforward]
  unfold groupedMass
  apply Finset.sum_congr
  · ext point
    simp only [exactAliceSourceAtomCode, Prod.mk.injEq, and_assoc, mem_filter, mem_univ, true_and]
  · intro point _
    rfl

theorem exactBobSourceContextNextPosterior_eq_groupedMass
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :
    (fun atom :
      ((SourceRemainingCoordinate D × Y) ×
        ExactHistoryFlag X Y A B D) × X =>
      exactBobInformationPosterior G n S D
        (atom.1.1, (atom.1.2, atom.2))) =
      groupedMass
        (fun point : ExactJointOutcome X Y A B D =>
          (((point.1.coordinate,
              point.2.2.1 point.1.coordinate.val),
            exactHistoryCode D point),
            point.2.1 point.1.coordinate.val))
        (exactPostselectedJointLaw G n S D) := by
  classical
  funext atom
  rcases atom with ⟨⟨⟨coordinate, question⟩, history⟩, next⟩
  rw [exactBobInformationPosterior_eq_jointPushforward]
  unfold groupedMass
  apply Finset.sum_congr
  · ext point
    simp only [exactBobSourceAtomCode, Prod.mk.injEq, and_assoc, mem_filter, mem_univ, true_and]
  · intro point _
    rfl

theorem exactAliceSourcePosteriorConditional_eq_fixedSeedFiber
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (reference : ExactOutcome X Y A B n) :
    jointConditional
        (fun atom :
          ((SourceRemainingCoordinate D × X) ×
            ExactHistoryFlag X Y A B D) × Y =>
          exactAliceInformationPosterior G n S D
            (atom.1.1, (atom.1.2, atom.2)))
        ((seed.coordinate, reference.1 seed.coordinate.val),
          exactHistoryCode D (seed, reference)) =
      jointConditional
        (groupedMass
          (fun outcome : ExactOutcome X Y A B n =>
            ((outcome.1 seed.coordinate.val,
              exactHistoryCode D (seed, outcome)),
              outcome.2.1 seed.coordinate.val))
          (repeatedConditionedOutcomeLaw G n S D))
        (reference.1 seed.coordinate.val,
          exactHistoryCode D (seed, reference)) := by
  classical
  rw [exactAliceSourceContextNextPosterior_eq_groupedMass]
  have fiber :
      jointConditional
          (groupedMass
            (fun point : ExactJointOutcome X Y A B D =>
              (((point.1.coordinate,
                  point.2.1 point.1.coordinate.val),
                exactHistoryCode D point),
                point.2.2.1 point.1.coordinate.val))
            (exactPostselectedJointLaw G n S D))
          ((seed.coordinate, reference.1 seed.coordinate.val),
            exactHistoryCode D (seed, reference)) =
        jointConditional
          (groupedMass
            (fun point : ExactJointOutcome X Y A B D =>
              ((point.1,
                (point.2.1 point.1.coordinate.val,
                  exactHistoryCode D point)),
                point.2.2.1 point.1.coordinate.val))
            (exactPostselectedJointLaw G n S D))
          (seed,
            (reference.1 seed.coordinate.val,
              exactHistoryCode D (seed, reference))) := by
    apply jointConditional_groupedMass_eq_of_fiber
      (exactPostselectedJointLaw G n S D)
      (fun point : ExactJointOutcome X Y A B D =>
        ((point.1.coordinate,
          point.2.1 point.1.coordinate.val),
          exactHistoryCode D point))
      (fun point : ExactJointOutcome X Y A B D =>
        (point.1,
          (point.2.1 point.1.coordinate.val,
            exactHistoryCode D point)))
      (fun point : ExactJointOutcome X Y A B D =>
        point.2.2.1 point.1.coordinate.val)
      ((seed.coordinate, reference.1 seed.coordinate.val),
        exactHistoryCode D (seed, reference))
      (seed,
        (reference.1 seed.coordinate.val,
          exactHistoryCode D (seed, reference)))
    intro point
    constructor
    · intro same
      have history :
          exactHistoryCode D point =
            exactHistoryCode D (seed, reference) :=
        congrArg Prod.snd same
      have seed_eq : point.1 = seed := by
        simpa only [exactHistoryCode] using
          congrArg
            (fun r : ExactHistoryFlag X Y A B D => r.seed)
            history
      have question :
          point.2.1 point.1.coordinate.val =
            reference.1 seed.coordinate.val :=
        congrArg
          (fun t :
            (SourceRemainingCoordinate D × X) ×
              ExactHistoryFlag X Y A B D => t.1.2)
          same
      exact Prod.ext seed_eq (Prod.ext question history)
    · intro same
      have seed_eq : point.1 = seed := congrArg Prod.fst same
      have question :
          point.2.1 point.1.coordinate.val =
            reference.1 seed.coordinate.val :=
        congrArg
          (fun t : ExactRemainingSeed D ×
            (X × ExactHistoryFlag X Y A B D) => t.2.1)
          same
      have history :
          exactHistoryCode D point =
            exactHistoryCode D (seed, reference) :=
        congrArg
          (fun t : ExactRemainingSeed D ×
            (X × ExactHistoryFlag X Y A B D) => t.2.2)
          same
      apply Prod.ext
      · exact Prod.ext
          (congrArg
            (fun s : ExactRemainingSeed D => s.coordinate)
            seed_eq)
          question
      · exact history
  calc
    _ = jointConditional
          (groupedMass
            (fun point : ExactJointOutcome X Y A B D =>
              ((point.1,
                (point.2.1 point.1.coordinate.val,
                  exactHistoryCode D point)),
                point.2.2.1 point.1.coordinate.val))
            (exactPostselectedJointLaw G n S D))
          (seed,
            (reference.1 seed.coordinate.val,
              exactHistoryCode D (seed, reference))) := fiber
    _ = _ := by
      unfold exactPostselectedJointLaw
      convert (jointConditional_product_context_seed
          (fun (source : ExactRemainingSeed D)
            (outcome : ExactOutcome X Y A B n) =>
            (outcome.1 source.coordinate.val,
              exactHistoryCode D (source, outcome)))
          (fun (source : ExactRemainingSeed D)
            (outcome : ExactOutcome X Y A B n) =>
            outcome.2.1 source.coordinate.val)
          exactSeedWeight
          (repeatedConditionedOutcomeLaw G n S D)
          seed
          (reference.1 seed.coordinate.val,
            exactHistoryCode D (seed, reference))
          (ne_of_gt (exactSeedWeight_pos_of_seed seed))) using 1
      · congr 1
        exact exactGroupedMass_decidableEq_irrel _ _ _ _
      · congr 1
        exact exactGroupedMass_decidableEq_irrel _ _ _ _

theorem exactBobSourcePosteriorConditional_eq_fixedSeedFiber
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (reference : ExactOutcome X Y A B n) :
    jointConditional
        (fun atom :
          ((SourceRemainingCoordinate D × Y) ×
            ExactHistoryFlag X Y A B D) × X =>
          exactBobInformationPosterior G n S D
            (atom.1.1, (atom.1.2, atom.2)))
        ((seed.coordinate, reference.2.1 seed.coordinate.val),
          exactHistoryCode D (seed, reference)) =
      jointConditional
        (groupedMass
          (fun outcome : ExactOutcome X Y A B n =>
            ((outcome.2.1 seed.coordinate.val,
              exactHistoryCode D (seed, outcome)),
              outcome.1 seed.coordinate.val))
          (repeatedConditionedOutcomeLaw G n S D))
        (reference.2.1 seed.coordinate.val,
          exactHistoryCode D (seed, reference)) := by
  classical
  rw [exactBobSourceContextNextPosterior_eq_groupedMass]
  have fiber :
      jointConditional
          (groupedMass
            (fun point : ExactJointOutcome X Y A B D =>
              (((point.1.coordinate,
                  point.2.2.1 point.1.coordinate.val),
                exactHistoryCode D point),
                point.2.1 point.1.coordinate.val))
            (exactPostselectedJointLaw G n S D))
          ((seed.coordinate, reference.2.1 seed.coordinate.val),
            exactHistoryCode D (seed, reference)) =
        jointConditional
          (groupedMass
            (fun point : ExactJointOutcome X Y A B D =>
              ((point.1,
                (point.2.2.1 point.1.coordinate.val,
                  exactHistoryCode D point)),
                point.2.1 point.1.coordinate.val))
            (exactPostselectedJointLaw G n S D))
          (seed,
            (reference.2.1 seed.coordinate.val,
              exactHistoryCode D (seed, reference))) := by
    apply jointConditional_groupedMass_eq_of_fiber
      (exactPostselectedJointLaw G n S D)
      (fun point : ExactJointOutcome X Y A B D =>
        ((point.1.coordinate,
          point.2.2.1 point.1.coordinate.val),
          exactHistoryCode D point))
      (fun point : ExactJointOutcome X Y A B D =>
        (point.1,
          (point.2.2.1 point.1.coordinate.val,
            exactHistoryCode D point)))
      (fun point : ExactJointOutcome X Y A B D =>
        point.2.1 point.1.coordinate.val)
      ((seed.coordinate, reference.2.1 seed.coordinate.val),
        exactHistoryCode D (seed, reference))
      (seed,
        (reference.2.1 seed.coordinate.val,
          exactHistoryCode D (seed, reference)))
    intro point
    constructor
    · intro same
      have history :
          exactHistoryCode D point =
            exactHistoryCode D (seed, reference) :=
        congrArg Prod.snd same
      have seed_eq : point.1 = seed := by
        simpa only [exactHistoryCode] using
          congrArg
            (fun r : ExactHistoryFlag X Y A B D => r.seed)
            history
      have question :
          point.2.2.1 point.1.coordinate.val =
            reference.2.1 seed.coordinate.val :=
        congrArg
          (fun t :
            (SourceRemainingCoordinate D × Y) ×
              ExactHistoryFlag X Y A B D => t.1.2)
          same
      exact Prod.ext seed_eq (Prod.ext question history)
    · intro same
      have seed_eq : point.1 = seed := congrArg Prod.fst same
      have question :
          point.2.2.1 point.1.coordinate.val =
            reference.2.1 seed.coordinate.val :=
        congrArg
          (fun t : ExactRemainingSeed D ×
            (Y × ExactHistoryFlag X Y A B D) => t.2.1)
          same
      have history :
          exactHistoryCode D point =
            exactHistoryCode D (seed, reference) :=
        congrArg
          (fun t : ExactRemainingSeed D ×
            (Y × ExactHistoryFlag X Y A B D) => t.2.2)
          same
      apply Prod.ext
      · exact Prod.ext
          (congrArg
            (fun s : ExactRemainingSeed D => s.coordinate)
            seed_eq)
          question
      · exact history
  calc
    _ = jointConditional
          (groupedMass
            (fun point : ExactJointOutcome X Y A B D =>
              ((point.1,
                (point.2.2.1 point.1.coordinate.val,
                  exactHistoryCode D point)),
                point.2.1 point.1.coordinate.val))
            (exactPostselectedJointLaw G n S D))
          (seed,
            (reference.2.1 seed.coordinate.val,
              exactHistoryCode D (seed, reference))) := fiber
    _ = _ := by
      unfold exactPostselectedJointLaw
      convert (jointConditional_product_context_seed
          (fun (source : ExactRemainingSeed D)
            (outcome : ExactOutcome X Y A B n) =>
            (outcome.2.1 source.coordinate.val,
              exactHistoryCode D (source, outcome)))
          (fun (source : ExactRemainingSeed D)
            (outcome : ExactOutcome X Y A B n) =>
            outcome.1 source.coordinate.val)
          exactSeedWeight
          (repeatedConditionedOutcomeLaw G n S D)
          seed
          (reference.2.1 seed.coordinate.val,
            exactHistoryCode D (seed, reference))
          (ne_of_gt (exactSeedWeight_pos_of_seed seed))) using 1
      · congr 1
        exact exactGroupedMass_decidableEq_irrel _ _ _ _
      · congr 1
        exact exactGroupedMass_decidableEq_irrel _ _ _ _

theorem exactReverseAliceMarkedPosteriorConditional_eq_sourcePosterior
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
        (fun atom :
          ((SourceRemainingCoordinate D × X) ×
            ExactHistoryFlag X Y A B D) × Y =>
          exactAliceInformationPosterior G n S D
            (atom.1.1, (atom.1.2, atom.2)))
        ((seed.coordinate, reference.1 seed.coordinate.val),
          exactHistoryCode D (seed, reference)) := by
  exact
    (exactReverseAliceMarkedPosteriorConditional_eq_sourceFiber
      G n S D default seed reference).trans
      (exactAliceSourcePosteriorConditional_eq_fixedSeedFiber
        G n S D seed reference).symm

theorem exactReverseBobMarkedPosteriorConditional_eq_sourcePosterior
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
        (fun atom :
          ((SourceRemainingCoordinate D × Y) ×
            ExactHistoryFlag X Y A B D) × X =>
          exactBobInformationPosterior G n S D
            (atom.1.1, (atom.1.2, atom.2)))
        ((seed.coordinate, reference.2.1 seed.coordinate.val),
          exactHistoryCode D (seed, reference)) := by
  exact
    (exactReverseBobMarkedPosteriorConditional_eq_sourceFiber
      G n S D default seed reference).trans
      (exactBobSourcePosteriorConditional_eq_fixedSeedFiber
        G n S D seed reference).symm

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

theorem exactReverseAliceSideWeightedPrefix_sum
    {M : Type*} [Fintype M] [DecidableEq M]
    (nonempty : 0 < Fintype.card M)
    (score : (side : Finset M) →
      ExactForwardSeed M → Fin side.card → ℝ) :
    (∑ side : Finset M,
      reversePartitionWeight side *
        ((∑ marker : Fin side.card,
          ∑ seed : ExactForwardSeed M,
            (exactReverseAliceConditionalSeedLaw
              nonempty side).weight seed *
              score side seed marker) /
          (side.card : ℝ))) =
      ∑ seed : ExactForwardSeed M,
        exactSeedWeight seed *
          ((∑ marker : Fin (exactReverseLeftSide seed).card,
            score (exactReverseLeftSide seed) seed marker) /
            ((exactReverseLeftSide seed).card : ℝ)) := by
  classical
  calc
    (∑ side : Finset M,
      reversePartitionWeight side *
        ((∑ marker : Fin side.card,
          ∑ seed : ExactForwardSeed M,
            (exactReverseAliceConditionalSeedLaw
              nonempty side).weight seed *
              score side seed marker) /
          (side.card : ℝ))) =
      ∑ side : Finset M,
        ∑ seed : ExactForwardSeed M,
          (reversePartitionWeight side *
            (exactReverseAliceConditionalSeedLaw
              nonempty side).weight seed) *
            ((∑ marker : Fin side.card,
              score side seed marker) / (side.card : ℝ)) := by
        apply Finset.sum_congr rfl
        intro side _
        rw [Finset.sum_comm]
        simp_rw [← Finset.mul_sum]
        rw [Finset.sum_div, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro seed _
        ring
    _ = ∑ side : Finset M,
        ∑ seed : ExactForwardSeed M,
          (if exactReverseLeftSide seed = side
           then exactSeedWeight seed else 0) *
            ((∑ marker : Fin side.card,
              score side seed marker) / (side.card : ℝ)) := by
        simp_rw [exactReverseAliceConditionalSeedLaw_weight_cancel
          nonempty]
    _ = ∑ seed : ExactForwardSeed M,
        exactSeedWeight seed *
          ((∑ marker : Fin (exactReverseLeftSide seed).card,
            score (exactReverseLeftSide seed) seed marker) /
            ((exactReverseLeftSide seed).card : ℝ)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro seed _
        simp only [ite_mul, zero_mul, sum_ite_eq, mem_univ, ↓reduceIte]

theorem exactReverseBobSideWeightedPrefix_sum
    {M : Type*} [Fintype M] [DecidableEq M]
    (nonempty : 0 < Fintype.card M)
    (score : (side : Finset M) →
      ExactForwardSeed M → Fin side.card → ℝ) :
    (∑ side : Finset M,
      reversePartitionWeight side *
        ((∑ marker : Fin side.card,
          ∑ seed : ExactForwardSeed M,
            (exactReverseBobConditionalSeedLaw
              nonempty side).weight seed *
              score side seed marker) /
          (side.card : ℝ))) =
      ∑ seed : ExactForwardSeed M,
        exactSeedWeight seed *
          ((∑ marker : Fin (exactReverseRightSide seed).card,
            score (exactReverseRightSide seed) seed marker) /
            ((exactReverseRightSide seed).card : ℝ)) := by
  classical
  calc
    (∑ side : Finset M,
      reversePartitionWeight side *
        ((∑ marker : Fin side.card,
          ∑ seed : ExactForwardSeed M,
            (exactReverseBobConditionalSeedLaw
              nonempty side).weight seed *
              score side seed marker) /
          (side.card : ℝ))) =
      ∑ side : Finset M,
        ∑ seed : ExactForwardSeed M,
          (reversePartitionWeight side *
            (exactReverseBobConditionalSeedLaw
              nonempty side).weight seed) *
            ((∑ marker : Fin side.card,
              score side seed marker) / (side.card : ℝ)) := by
        apply Finset.sum_congr rfl
        intro side _
        rw [Finset.sum_comm]
        simp_rw [← Finset.mul_sum]
        rw [Finset.sum_div, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro seed _
        ring
    _ = ∑ side : Finset M,
        ∑ seed : ExactForwardSeed M,
          (if exactReverseRightSide seed = side
           then exactSeedWeight seed else 0) *
            ((∑ marker : Fin side.card,
              score side seed marker) / (side.card : ℝ)) := by
        simp_rw [exactReverseBobConditionalSeedLaw_weight_cancel
          nonempty]
    _ = ∑ seed : ExactForwardSeed M,
        exactSeedWeight seed *
          ((∑ marker : Fin (exactReverseRightSide seed).card,
            score (exactReverseRightSide seed) seed marker) /
            ((exactReverseRightSide seed).card : ℝ)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro seed _
        simp only [ite_mul, zero_mul, sum_ite_eq, mem_univ, ↓reduceIte]

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

theorem groupedMass_product_stable_context_fiber
    {K Ω I C V : Type*}
    [Fintype K] [Fintype Ω]
    (index : K → I)
    (context : I → Ω → C)
    (next : I → Ω → V)
    (extract : C → I)
    (extract_context : ∀ (i : I) (outcome : Ω),
      extract (context i outcome) = i)
    (seedWeight : K → ℝ)
    (outcomeWeight : Ω → ℝ)
    (target : C) (value : V) :
    groupedMass
        (fun point : K × Ω =>
          (context (index point.1) point.2,
            next (index point.1) point.2))
        (fun point : K × Ω =>
          seedWeight point.1 * outcomeWeight point.2)
        (target, value) =
      groupedMass index seedWeight (extract target) *
        groupedMass
          (fun outcome : Ω =>
            (context (extract target) outcome,
              next (extract target) outcome))
          outcomeWeight (target, value) := by
  classical
  unfold groupedMass
  simp only [Finset.sum_filter, Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro seed _
  by_cases same : index seed = extract target
  · simp only [same, Prod.mk.injEq, ↓reduceIte, mul_sum, mul_ite, mul_zero]
  · have different (outcome : Ω) :
        context (index seed) outcome ≠ target := by
        intro equal
        apply same
        calc
          index seed = extract (context (index seed) outcome) :=
            (extract_context (index seed) outcome).symm
          _ = extract target := congrArg extract equal
    simp only [Prod.mk.injEq, different, false_and, ↓reduceIte, sum_const_zero, same, zero_mul]

theorem jointConditional_product_stable_context_seed
    {K Ω I C V : Type*}
    [Fintype K] [Fintype Ω] [Fintype V]
    (index : K → I)
    (context : I → Ω → C)
    (next : I → Ω → V)
    (extract : C → I)
    (extract_context : ∀ (i : I) (outcome : Ω),
      extract (context i outcome) = i)
    (seedWeight : K → ℝ)
    (outcomeWeight : Ω → ℝ)
    (seed : K) (target : C)
    (target_index : extract target = index seed)
    (nonzero : groupedMass index seedWeight (index seed) ≠ 0) :
    jointConditional
        (groupedMass
          (fun point : K × Ω =>
            (context (index point.1) point.2,
              next (index point.1) point.2))
          (fun point : K × Ω =>
            seedWeight point.1 * outcomeWeight point.2))
        target =
      jointConditional
        (groupedMass
          (fun outcome : Ω =>
            (context (index seed) outcome,
              next (index seed) outcome))
          outcomeWeight)
        target := by
  classical
  have atom (value : V) :
      groupedMass
          (fun point : K × Ω =>
            (context (index point.1) point.2,
              next (index point.1) point.2))
          (fun point : K × Ω =>
            seedWeight point.1 * outcomeWeight point.2)
          (target, value) =
        groupedMass index seedWeight (index seed) *
          groupedMass
            (fun outcome : Ω =>
              (context (index seed) outcome,
                next (index seed) outcome))
            outcomeWeight (target, value) := by
    simpa only [target_index] using
      groupedMass_product_stable_context_fiber
        index context next extract extract_context
        seedWeight outcomeWeight target value
  funext value
  unfold jointConditional jointFirstMarginal
  simp_rw [atom]
  rw [← Finset.mul_sum]
  exact mul_div_mul_left _ _ nonzero

theorem groupedMass_pos_of_supported_atom
    {K I : Type*} [Fintype K] [DecidableEq I]
    (code : K → I) (weight : K → ℝ)
    (nonnegative : ∀ seed : K, 0 ≤ weight seed)
    (seed : K) (positive : 0 < weight seed) :
    0 < groupedMass code weight (code seed) := by
  unfold groupedMass
  apply lt_of_lt_of_le positive
  apply Finset.single_le_sum
  · intro other _
    exact nonnegative other
  · exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ seed, rfl⟩

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

private def exactReverseAliceContextOutcomeProjection
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (outcome : ExactOutcome X Y A B n) :
    ExactReverseAliceFixedInformation X Y D side ×
      (Fin side.card → Y) :=
  (⟨context,
     (fun j => outcome.1 j.val),
     (fun j => outcome.2.1 j.val),
     (fun j => outcome.1 j.val.val),
     (fun j => outcome.2.1 j.val.val),
     (fun j => outcome.1 j.val.val)⟩,
    fun marker =>
      outcome.2.1 (context.sideRank.symm marker).val.val)

private def exactReverseBobContextOutcomeProjection
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (outcome : ExactOutcome X Y A B n) :
    ExactReverseBobFixedInformation X Y D side ×
      (Fin side.card → X) :=
  (⟨context,
     (fun j => outcome.1 j.val),
     (fun j => outcome.2.1 j.val),
     (fun j => outcome.2.1 j.val.val),
     (fun j => outcome.1 j.val.val),
     (fun j => outcome.2.1 j.val.val)⟩,
    fun marker =>
      outcome.1 (context.sideRank.symm marker).val.val)

theorem reweightedSeedPrefixNextJoint_as_actual_pushforward
    {K Ω V : Type*} [Fintype K] [Fintype Ω] [Fintype V]
    {h : ℕ}
    (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (projection : K × ExactOutcome X Y A B n →
      Ω × (Fin h → V))
    (default : V) (marker : Fin h) :
    groupedMass (exactPrefixNextCode default marker)
        (reweightedSeedPrefixJoint
          seedLaw G n S D projection) =
      groupedMass
        (fun point : K × ExactOutcome X Y A B n =>
          exactPrefixNextCode default marker
            (((projection point).1,
              repeatedConditionedAnswerFlag
                G n S D point.2),
              (projection point).2))
        (reweightedSeedPosterior seedLaw G n S D) := by
  classical
  let augmented :
      K × ExactOutcome X Y A B n →
        (Ω × ConditionedAnswerFlag A B D) ×
          (Fin h → V) :=
    fun point =>
      (((projection point).1,
        repeatedConditionedAnswerFlag G n S D point.2),
        (projection point).2)
  have actual :
      reweightedSeedPrefixJoint
          seedLaw G n S D projection =
        groupedMass augmented
          (reweightedSeedPosterior seedLaw G n S D) := by
    funext target
    exact reweightedSeedPrefixJoint_as_actual_flagged_pushforward
      seedLaw G n S D projection target
  rw [actual]
  exact groupedMass_comp augmented
    (exactPrefixNextCode default marker)
    (reweightedSeedPosterior seedLaw G n S D)

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

theorem groupedMass_productCode_weighted_sum
    {K Ω C : Type*} [Fintype K] [Fintype Ω]
    [DecidableEq C]
    (code : K → Ω → C)
    (weight : K → ℝ) (mass : Ω → ℝ) (target : C) :
    groupedMass (fun point : K × Ω => code point.1 point.2)
        (fun point : K × Ω => weight point.1 * mass point.2)
        target =
      ∑ index : K, weight index * groupedMass (code index) mass target := by
  classical
  unfold groupedMass
  simp only [Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro index _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro outcome _
  split <;> simp_all

theorem groupedMass_flagSeedOutcome_reassoc
    {F K Ω C : Type*}
    [Fintype F] [Fintype K] [Fintype Ω]
    [DecidableEq C]
    (code : F → K → Ω → C)
    (flagWeight : F → ℝ) (seedWeight : K → ℝ)
    (outcomeWeight : Ω → ℝ) (target : C) :
    groupedMass
        (fun point : F × (K × Ω) =>
          code point.1 point.2.1 point.2.2)
        (fun point : F × (K × Ω) =>
          flagWeight point.1 *
            (seedWeight point.2.1 * outcomeWeight point.2.2))
        target =
      groupedMass
        (fun point : (F × K) × Ω =>
          code point.1.1 point.1.2 point.2)
        (fun point : (F × K) × Ω =>
          (flagWeight point.1.1 * seedWeight point.1.2) *
            outcomeWeight point.2)
        target := by
  classical
  unfold groupedMass
  simp only [Finset.sum_filter]
  symm
  apply Fintype.sum_equiv (Equiv.prodAssoc F K Ω)
  intro point
  change
    (if code point.1.1 point.1.2 point.2 = target then
      (flagWeight point.1.1 * seedWeight point.1.2) *
        outcomeWeight point.2 else 0) =
    (if code point.1.1 point.1.2 point.2 = target then
      flagWeight point.1.1 *
        (seedWeight point.1.2 * outcomeWeight point.2) else 0)
  split <;> simp [mul_assoc]

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem mixedStableBobQuestionCode_joint_factor
    {K C : Type*} [Fintype K] [DecidableEq C]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (weight : K → ℝ)
    (coordinate : K → Fin n)
    (code : K → (Fin n → X) → (Fin n → Y) → C)
    (target : C) (question : X) (next : Y)
    (stable : ∀ (index : K) (xs : Fin n → X)
      (tail : {j : Fin n // j ≠ coordinate index} → Y)
      (y y' : Y),
      code index xs
          ((Equiv.funSplitAt (coordinate index) Y).symm (y, tail)) =
        code index xs
          ((Equiv.funSplitAt (coordinate index) Y).symm (y', tail)))
    (determines : ∀ (index : K)
      (xs : Fin n → X) (ys : Fin n → Y),
      code index xs ys = target → xs (coordinate index) = question) :
    groupedMass
        (fun point : K × ExactOutcome X Y A B n =>
          (code point.1 point.2.1 point.2.2.1,
            point.2.2.1 (coordinate point.1)))
        (fun point : K × ExactOutcome X Y A B n =>
          weight point.1 *
            (strategyEventLaw (G.repeat n) S).weight point.2)
        (target, next) =
      G.conditionalYGivenX question next *
        groupedMass
          (fun point : K × ExactOutcome X Y A B n =>
            code point.1 point.2.1 point.2.2.1)
          (fun point : K × ExactOutcome X Y A B n =>
            weight point.1 *
              (strategyEventLaw (G.repeat n) S).weight point.2)
          target := by
  classical
  calc
    groupedMass
        (fun point : K × ExactOutcome X Y A B n =>
          (code point.1 point.2.1 point.2.2.1,
            point.2.2.1 (coordinate point.1)))
        (fun point : K × ExactOutcome X Y A B n =>
          weight point.1 *
            (strategyEventLaw (G.repeat n) S).weight point.2)
        (target, next) =
      ∑ index : K, weight index *
        groupedMass
          (fun outcome : ExactOutcome X Y A B n =>
            (code index outcome.1 outcome.2.1,
              outcome.2.1 (coordinate index)))
          (strategyEventLaw (G.repeat n) S).weight
          (target, next) :=
      groupedMass_productCode_weighted_sum
        (fun index (outcome : ExactOutcome X Y A B n) =>
          (code index outcome.1 outcome.2.1,
            outcome.2.1 (coordinate index)))
        weight (strategyEventLaw (G.repeat n) S).weight (target, next)
    _ = ∑ index : K, weight index *
        (G.conditionalYGivenX question next *
          groupedMass
            (fun outcome : ExactOutcome X Y A B n =>
              code index outcome.1 outcome.2.1)
            (strategyEventLaw (G.repeat n) S).weight target) := by
      apply Finset.sum_congr rfl
      intro index _
      congr 1
      exact exactStrategyStableBobQuestionCode_joint_factor
        G n S (coordinate index) (code index) target question next
        (stable index) (determines index)
    _ = G.conditionalYGivenX question next *
          (∑ index : K, weight index *
            groupedMass
              (fun outcome : ExactOutcome X Y A B n =>
                code index outcome.1 outcome.2.1)
              (strategyEventLaw (G.repeat n) S).weight target) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro index _
      ring
    _ = G.conditionalYGivenX question next *
        groupedMass
          (fun point : K × ExactOutcome X Y A B n =>
            code point.1 point.2.1 point.2.2.1)
          (fun point : K × ExactOutcome X Y A B n =>
            weight point.1 *
              (strategyEventLaw (G.repeat n) S).weight point.2)
          target := by
      congr 1
      exact (groupedMass_productCode_weighted_sum
        (fun index (outcome : ExactOutcome X Y A B n) =>
          code index outcome.1 outcome.2.1)
        weight (strategyEventLaw (G.repeat n) S).weight target).symm

theorem mixedStableAliceQuestionCode_joint_factor
    {K C : Type*} [Fintype K] [DecidableEq C]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (weight : K → ℝ)
    (coordinate : K → Fin n)
    (code : K → (Fin n → X) → (Fin n → Y) → C)
    (target : C) (question : Y) (next : X)
    (stable : ∀ (index : K) (ys : Fin n → Y)
      (tail : {j : Fin n // j ≠ coordinate index} → X)
      (x x' : X),
      code index
          ((Equiv.funSplitAt (coordinate index) X).symm (x, tail)) ys =
        code index
          ((Equiv.funSplitAt (coordinate index) X).symm (x', tail)) ys)
    (determines : ∀ (index : K)
      (xs : Fin n → X) (ys : Fin n → Y),
      code index xs ys = target → ys (coordinate index) = question) :
    groupedMass
        (fun point : K × ExactOutcome X Y A B n =>
          (code point.1 point.2.1 point.2.2.1,
            point.2.1 (coordinate point.1)))
        (fun point : K × ExactOutcome X Y A B n =>
          weight point.1 *
            (strategyEventLaw (G.repeat n) S).weight point.2)
        (target, next) =
      G.conditionalXGivenY question next *
        groupedMass
          (fun point : K × ExactOutcome X Y A B n =>
            code point.1 point.2.1 point.2.2.1)
          (fun point : K × ExactOutcome X Y A B n =>
            weight point.1 *
              (strategyEventLaw (G.repeat n) S).weight point.2)
          target := by
  classical
  calc
    groupedMass
        (fun point : K × ExactOutcome X Y A B n =>
          (code point.1 point.2.1 point.2.2.1,
            point.2.1 (coordinate point.1)))
        (fun point : K × ExactOutcome X Y A B n =>
          weight point.1 *
            (strategyEventLaw (G.repeat n) S).weight point.2)
        (target, next) =
      ∑ index : K, weight index *
        groupedMass
          (fun outcome : ExactOutcome X Y A B n =>
            (code index outcome.1 outcome.2.1,
              outcome.1 (coordinate index)))
          (strategyEventLaw (G.repeat n) S).weight
          (target, next) :=
      groupedMass_productCode_weighted_sum
        (fun index (outcome : ExactOutcome X Y A B n) =>
          (code index outcome.1 outcome.2.1,
            outcome.1 (coordinate index)))
        weight (strategyEventLaw (G.repeat n) S).weight (target, next)
    _ = ∑ index : K, weight index *
        (G.conditionalXGivenY question next *
          groupedMass
            (fun outcome : ExactOutcome X Y A B n =>
              code index outcome.1 outcome.2.1)
            (strategyEventLaw (G.repeat n) S).weight target) := by
      apply Finset.sum_congr rfl
      intro index _
      congr 1
      exact exactStrategyStableAliceQuestionCode_joint_factor
        G n S (coordinate index) (code index) target question next
        (stable index) (determines index)
    _ = G.conditionalXGivenY question next *
          (∑ index : K, weight index *
            groupedMass
              (fun outcome : ExactOutcome X Y A B n =>
                code index outcome.1 outcome.2.1)
              (strategyEventLaw (G.repeat n) S).weight target) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro index _
      ring
    _ = G.conditionalXGivenY question next *
        groupedMass
          (fun point : K × ExactOutcome X Y A B n =>
            code point.1 point.2.1 point.2.2.1)
          (fun point : K × ExactOutcome X Y A B n =>
            weight point.1 *
              (strategyEventLaw (G.repeat n) S).weight point.2)
          target := by
      congr 1
      exact (groupedMass_productCode_weighted_sum
        (fun index (outcome : ExactOutcome X Y A B n) =>
          code index outcome.1 outcome.2.1)
        weight (strategyEventLaw (G.repeat n) S).weight target).symm

private def exactReverseAliceMaskedQuestionRegister
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (default : Y) (marker : Fin side.card)
    (flag : ConditionedAnswerFlag A B D)
    (seed : ExactRemainingSeed D)
    (xs : Fin n → X) (ys : Fin n → Y) :
    ExactReverseAliceNextContext X Y A B D side :=
  let context := exactReverseAliceContextAt side seed
  let fixed : ExactReverseAliceFixedInformation X Y D side :=
    ⟨context,
      (fun j => xs j.val),
      (fun j => ys j.val),
      (fun j => xs j.val.val),
      (fun j => ys j.val.val),
      (fun j => xs j.val.val)⟩
  finitePrefixMask default marker.castSucc
    ((fixed, flag),
      fun position => ys (context.sideRank.symm position).val.val)

private def exactReverseBobMaskedQuestionRegister
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (default : X) (marker : Fin side.card)
    (flag : ConditionedAnswerFlag A B D)
    (seed : ExactRemainingSeed D)
    (xs : Fin n → X) (ys : Fin n → Y) :
    ExactReverseBobNextContext X Y A B D side :=
  let context := exactReverseBobContextAt side seed
  let fixed : ExactReverseBobFixedInformation X Y D side :=
    ⟨context,
      (fun j => xs j.val),
      (fun j => ys j.val),
      (fun j => ys j.val.val),
      (fun j => xs j.val.val),
      (fun j => ys j.val.val)⟩
  finitePrefixMask default marker.castSucc
    ((fixed, flag),
      fun position => xs (context.sideRank.symm position).val.val)

omit [Fintype X] [Fintype Y] [Fintype A] [Fintype B] in
theorem exactReverseAliceMaskedQuestionRegister_stable
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (default : Y) (marker : Fin side.card)
    (flag : ConditionedAnswerFlag A B D)
    (seed : ExactRemainingSeed D)
    (xs : Fin n → X)
    (tail : {j : Fin n //
      j ≠ ((exactReverseAliceContextAt side seed).sideRank.symm
        marker).val.val} → Y)
    (y y' : Y) :
    exactReverseAliceMaskedQuestionRegister
        D side default marker flag seed xs
        ((Equiv.funSplitAt
          ((exactReverseAliceContextAt side seed).sideRank.symm
            marker).val.val Y).symm (y, tail)) =
      exactReverseAliceMaskedQuestionRegister
        D side default marker flag seed xs
        ((Equiv.funSplitAt
          ((exactReverseAliceContextAt side seed).sideRank.symm
            marker).val.val Y).symm (y', tail)) := by
  classical
  let context := exactReverseAliceContextAt side seed
  let marked : SourceRemainingCoordinate D :=
    (context.sideRank.symm marker).val
  let coordinate : Fin n := marked.val
  have outsideD : coordinate ∉ D := by
    exact (Finset.mem_sdiff.mp marked.property).2
  have outsideOther : marked ∉ context.otherSide := by
    rw [context.otherSide_eq_complement]
    simp only [univ_eq_attach, mem_sdiff, mem_attach, (context.sideRank.symm marker).property,
      not_true_eq_false, and_false, not_false_eq_true, marked]
  change
    exactReverseAliceMaskedQuestionRegister
        D side default marker flag seed xs
        ((Equiv.funSplitAt coordinate Y).symm (y, tail)) =
      exactReverseAliceMaskedQuestionRegister
        D side default marker flag seed xs
        ((Equiv.funSplitAt coordinate Y).symm (y', tail))
  unfold exactReverseAliceMaskedQuestionRegister
    finitePrefixMask
  apply Prod.ext
  · apply Prod.ext
    · apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Prod.ext
        · rfl
        apply Prod.ext
        · funext j
          have different : j.val ≠ coordinate := by
            intro same
            exact outsideD (same ▸ j.property)
          simp only [ne_eq, Equiv.funSplitAt, Equiv.piSplitAt, eq_rec_constant, Equiv.symm_mk,
            Equiv.coe_fn_mk, different, ↓reduceDIte]
        apply Prod.ext
        · rfl
        apply Prod.ext
        · funext j
          have different : j.val.val ≠ coordinate := by
            intro same
            apply outsideOther
            have actual : j.val = marked := by
              apply Subtype.ext
              exact same
            exact actual ▸ j.property
          simp only [ne_eq, Equiv.funSplitAt, Equiv.piSplitAt, eq_rec_constant, Equiv.symm_mk,
            Equiv.coe_fn_mk, different, ↓reduceDIte]
        · rfl
    · rfl
  · funext position
    by_cases before : position.val < marker.val
    · have different :
          ((context.sideRank.symm position).val.val) ≠ coordinate := by
        intro same
        have sameMarked :
            context.sideRank.symm position =
              context.sideRank.symm marker := by
          apply Subtype.ext
          apply Subtype.ext
          exact same
        have samePosition :=
          context.sideRank.symm.injective sameMarked
        exact (Nat.ne_of_lt before)
          (congrArg Fin.val samePosition)
      simp only [Fin.val_castSucc, before, ↓reduceIte, ne_eq, Equiv.funSplitAt, Equiv.piSplitAt,
        eq_rec_constant, Equiv.symm_mk, Equiv.coe_fn_mk, different, ↓reduceDIte, context]
    · simp only [Fin.val_castSucc, before, ↓reduceIte]

theorem exactConditionedReverseAliceNextPrior_flagged_mixture
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (side : Finset (SourceRemainingCoordinate D))
    (default : Y) (marker : Fin side.card) :
    groupedMass (exactPrefixNextCode default marker)
        (exactConditionedReverseAliceNextPrior
          G n S D remaining side) =
      groupedMass
        (fun point :
          (ConditionedAnswerFlag A B D ×
            ExactRemainingSeed D) ×
              ExactOutcome X Y A B n =>
          (exactReverseAliceMaskedQuestionRegister
            D side default marker point.1.1 point.1.2
            point.2.1 point.2.2.1,
            point.2.2.1
              (((exactReverseAliceContextAt
                side point.1.2).sideRank.symm marker).val.val)))
        (fun point :
          (ConditionedAnswerFlag A B D ×
            ExactRemainingSeed D) ×
              ExactOutcome X Y A B n =>
          (finiteUniformWeight
              (ConditionedAnswerFlag A B D) *
            (exactReverseAliceConditionalSeedLaw
              (exactRemainingCoordinate_card_pos
                D remaining) side).weight point.1.2) *
            (strategyEventLaw (G.repeat n) S).weight point.2) := by
  classical
  funext target
  let seedLaw := exactReverseAliceConditionalSeedLaw
    (exactRemainingCoordinate_card_pos D remaining) side
  let projection := exactReverseAliceSourceProjection
    (X := X) (Y := Y) (A := A) (B := B) D side
  change
    groupedMass (exactPrefixNextCode default marker)
        (reweightedSeedPrefixPrior
          seedLaw G n S D projection) target = _
  calc
    groupedMass (exactPrefixNextCode default marker)
        (reweightedSeedPrefixPrior
          seedLaw G n S D projection) target =
      groupedMass
        (fun point : ConditionedAnswerFlag A B D ×
          (ExactRemainingSeed D ×
            ExactOutcome X Y A B n) =>
          exactPrefixNextCode default marker
            (((projection point.2).1, point.1),
              (projection point.2).2))
        (fun point : ConditionedAnswerFlag A B D ×
          (ExactRemainingSeed D ×
            ExactOutcome X Y A B n) =>
          finiteUniformWeight
              (ConditionedAnswerFlag A B D) *
            (reweightedSeedPriorEventLaw
              seedLaw G n S).weight point.2)
        target :=
      reweightedSeedPrefixPrior_next_flagged_pushforward
        seedLaw G n S D projection default marker target
    _ = _ := by
      change
        groupedMass
          (fun point : ConditionedAnswerFlag A B D ×
            (ExactRemainingSeed D ×
              ExactOutcome X Y A B n) =>
            (exactReverseAliceMaskedQuestionRegister
              D side default marker point.1 point.2.1
              point.2.2.1 point.2.2.2.1,
              point.2.2.2.1
                (((exactReverseAliceContextAt
                  side point.2.1).sideRank.symm marker).val.val)))
          (fun point : ConditionedAnswerFlag A B D ×
            (ExactRemainingSeed D ×
              ExactOutcome X Y A B n) =>
            finiteUniformWeight
                (ConditionedAnswerFlag A B D) *
              (seedLaw.weight point.2.1 *
                (strategyEventLaw (G.repeat n) S).weight point.2.2))
          target = _
      exact groupedMass_flagSeedOutcome_reassoc
        (F := ConditionedAnswerFlag A B D)
        (K := ExactRemainingSeed D)
        (Ω := ExactOutcome X Y A B n)
        (fun flag seed (outcome : ExactOutcome X Y A B n) =>
          (exactReverseAliceMaskedQuestionRegister
            D side default marker flag seed outcome.1 outcome.2.1,
            outcome.2.1
              (((exactReverseAliceContextAt
                side seed).sideRank.symm marker).val.val)))
        (fun _ : ConditionedAnswerFlag A B D =>
          finiteUniformWeight
            (ConditionedAnswerFlag A B D))
        seedLaw.weight
        (strategyEventLaw (G.repeat n) S).weight target

omit [Fintype X] [Fintype Y] [Fintype A] [Fintype B] in
theorem exactReverseAliceMaskedQuestionRegister_determines
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (default : Y) (marker : Fin side.card)
    (flag : ConditionedAnswerFlag A B D)
    (seed : ExactRemainingSeed D)
    (xs : Fin n → X) (ys : Fin n → Y)
    (target : ExactReverseAliceNextContext X Y A B D side)
    (same :
      exactReverseAliceMaskedQuestionRegister
        D side default marker flag seed xs ys = target) :
    xs (((exactReverseAliceContextAt
        side seed).sideRank.symm marker).val.val) =
      target.1.1.2.2.2.1
        (target.1.1.1.sideRank.symm marker) := by
  have actual := congrArg
    (fun context : ExactReverseAliceNextContext
      X Y A B D side =>
      context.1.1.2.2.2.1
        (context.1.1.1.sideRank.symm marker)) same
  exact actual

theorem exactConditionedReverseAliceNextPrior_marked_joint_factor
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (side : Finset (SourceRemainingCoordinate D))
    (default : Y) (marker : Fin side.card)
    (target : ExactReverseAliceNextContext X Y A B D side)
    (next : Y) :
    groupedMass
        (exactPrefixNextCode default marker)
        (exactConditionedReverseAliceNextPrior
          G n S D remaining side)
        (target, next) =
      G.conditionalYGivenX
          (target.1.1.2.2.2.1
            (target.1.1.1.sideRank.symm marker)) next *
        jointFirstMarginal
          (groupedMass
            (exactPrefixNextCode default marker)
            (exactConditionedReverseAliceNextPrior
              G n S D remaining side))
          target := by
  classical
  let seedLaw := exactReverseAliceConditionalSeedLaw
    (exactRemainingCoordinate_card_pos D remaining) side
  let mixedWeight :
      ConditionedAnswerFlag A B D ×
        ExactRemainingSeed D → ℝ :=
    fun index =>
      finiteUniformWeight
        (ConditionedAnswerFlag A B D) *
        seedLaw.weight index.2
  let coordinate :
      ConditionedAnswerFlag A B D ×
        ExactRemainingSeed D → Fin n :=
    fun index =>
      ((exactReverseAliceContextAt
        side index.2).sideRank.symm marker).val.val
  let code :
      (ConditionedAnswerFlag A B D ×
        ExactRemainingSeed D) →
          (Fin n → X) → (Fin n → Y) →
            ExactReverseAliceNextContext X Y A B D side :=
    fun index xs ys =>
      exactReverseAliceMaskedQuestionRegister
        D side default marker index.1 index.2 xs ys
  let question : X :=
    target.1.1.2.2.2.1
      (target.1.1.1.sideRank.symm marker)
  have stable :
      ∀ (index : ConditionedAnswerFlag A B D ×
          ExactRemainingSeed D)
        (xs : Fin n → X)
        (tail : {j : Fin n // j ≠ coordinate index} → Y)
        (y y' : Y),
        code index xs
            ((Equiv.funSplitAt (coordinate index) Y).symm (y, tail)) =
          code index xs
            ((Equiv.funSplitAt (coordinate index) Y).symm (y', tail)) := by
    intro index xs tail y y'
    exact exactReverseAliceMaskedQuestionRegister_stable
      D side default marker index.1 index.2 xs tail y y'
  have determines :
      ∀ (index : ConditionedAnswerFlag A B D ×
          ExactRemainingSeed D)
        (xs : Fin n → X) (ys : Fin n → Y),
        code index xs ys = target →
          xs (coordinate index) = question := by
    intro index xs ys same
    exact exactReverseAliceMaskedQuestionRegister_determines
      D side default marker index.1 index.2 xs ys target same
  have mixed := mixedStableBobQuestionCode_joint_factor
    G n S mixedWeight coordinate code target question next
    stable determines
  rw [exactConditionedReverseAliceNextPrior_flagged_mixture
    G n S D remaining side default marker]
  change
    groupedMass
        (fun point :
          (ConditionedAnswerFlag A B D ×
            ExactRemainingSeed D) ×
              ExactOutcome X Y A B n =>
          (code point.1 point.2.1 point.2.2.1,
            point.2.2.1 (coordinate point.1)))
        (fun point :
          (ConditionedAnswerFlag A B D ×
            ExactRemainingSeed D) ×
              ExactOutcome X Y A B n =>
          mixedWeight point.1 *
            (strategyEventLaw (G.repeat n) S).weight point.2)
        (target, next) =
      G.conditionalYGivenX question next *
        jointFirstMarginal
          (groupedMass
            (fun point :
              (ConditionedAnswerFlag A B D ×
                ExactRemainingSeed D) ×
                  ExactOutcome X Y A B n =>
              (code point.1 point.2.1 point.2.2.1,
                point.2.2.1 (coordinate point.1)))
            (fun point :
              (ConditionedAnswerFlag A B D ×
                ExactRemainingSeed D) ×
                  ExactOutcome X Y A B n =>
              mixedWeight point.1 *
                (strategyEventLaw (G.repeat n) S).weight point.2))
          target
  rw [jointFirstMarginal_groupedContextNext]
  convert mixed using 1
  exact congrFun (exactGroupedMass_decidableEq_irrel
    _ _ _ _) (target, next)

theorem exactConditionedReverseAliceNextPrior_marked_conditional
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (side : Finset (SourceRemainingCoordinate D))
    (default : Y) (marker : Fin side.card)
    (target : ExactReverseAliceNextContext X Y A B D side)
    (supported :
      jointFirstMarginal
        (groupedMass
          (exactPrefixNextCode default marker)
          (exactConditionedReverseAliceNextPrior
            G n S D remaining side))
        target ≠ 0) :
    jointConditional
        (groupedMass
          (exactPrefixNextCode default marker)
          (exactConditionedReverseAliceNextPrior
            G n S D remaining side))
        target =
      G.conditionalYGivenX
        (target.1.1.2.2.2.1
          (target.1.1.1.sideRank.symm marker)) := by
  funext next
  unfold jointConditional
  rw [exactConditionedReverseAliceNextPrior_marked_joint_factor
    G n S D remaining side default marker target next]
  exact mul_div_cancel_right₀ _ supported

theorem exactReverseAliceMarkedPriorConditional_eq_game
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (default : Y)
    (seed : ExactRemainingSeed D)
    (reference : ExactOutcome X Y A B n)
    (supported :
      jointFirstMarginal
        (groupedMass
          (exactPrefixNextCode default
            ((exactReverseAliceContext seed).sideRank
              ⟨seed.coordinate,
                exactReverseLeftSide_coordinate_mem seed⟩))
          (exactConditionedReverseAliceNextPrior
            G n S D remaining
            (exactReverseLeftSide seed)))
        (exactReverseAliceMarkedHistoryContext
          G n S D default seed reference) ≠ 0) :
    jointConditional
        (groupedMass
          (exactPrefixNextCode default
            ((exactReverseAliceContext seed).sideRank
              ⟨seed.coordinate,
                exactReverseLeftSide_coordinate_mem seed⟩))
          (exactConditionedReverseAliceNextPrior
            G n S D remaining
            (exactReverseLeftSide seed)))
        (exactReverseAliceMarkedHistoryContext
          G n S D default seed reference) =
      G.conditionalYGivenX
        (reference.1 seed.coordinate.val) := by
  have actual := exactConditionedReverseAliceNextPrior_marked_conditional
    G n S D remaining
    (exactReverseLeftSide seed) default
    ((exactReverseAliceContext seed).sideRank
      ⟨seed.coordinate,
        exactReverseLeftSide_coordinate_mem seed⟩)
    (exactReverseAliceMarkedHistoryContext
      G n S D default seed reference) supported
  simpa only [exactReverseAliceMarkedHistoryContext, finitePrefixMask,
    exactReverseAliceSourceProjection, exactReverseAliceContextAt_actual, Fin.val_castSucc,
    exactReverseAliceContext_marked_rank, Equiv.symm_apply_apply] using actual

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

private def exactReverseAliceMaskedOutcomeContext
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (default : Y) (marker : Fin side.card)
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (outcome : ExactOutcome X Y A B n) :
    ExactReverseAliceNextContext X Y A B D side :=
  let projection :=
    exactReverseAliceContextOutcomeProjection
      (X := X) (Y := Y) (A := A) (B := B)
      D side context outcome
  finitePrefixMask default marker.castSucc
    ((projection.1,
      repeatedConditionedAnswerFlag G n S D outcome),
      projection.2)

theorem exactReverseAliceMaskedOutcomeContext_extract
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (default : Y) (marker : Fin side.card)
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (outcome : ExactOutcome X Y A B n) :
    (exactReverseAliceMaskedOutcomeContext
      G n S D side default marker context outcome).1.1.1 =
      context := by
  rfl

theorem exactConditionedReverseAliceNextJoint_marked_mixture
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (side : Finset (SourceRemainingCoordinate D))
    (default : Y) (marker : Fin side.card) :
    groupedMass (exactPrefixNextCode default marker)
        (exactConditionedReverseAliceNextJoint
          G n S D remaining side) =
      groupedMass
        (fun point : ExactJointOutcome X Y A B D =>
          (exactReverseAliceMaskedOutcomeContext
            G n S D side default marker
            (exactReverseAliceContextAt side point.1)
            point.2,
            point.2.2.1
              (((exactReverseAliceContextAt
                side point.1).sideRank.symm marker).val.val)))
        (fun point : ExactJointOutcome X Y A B D =>
          (exactReverseAliceConditionalSeedLaw
            (exactRemainingCoordinate_card_pos
              D remaining) side).weight point.1 *
            repeatedConditionedOutcomeLaw G n S D point.2) := by
  classical
  let law := exactReverseAliceConditionalSeedLaw
    (exactRemainingCoordinate_card_pos D remaining) side
  let projection := exactReverseAliceSourceProjection
    (X := X) (Y := Y) (A := A) (B := B) D side
  change
    groupedMass (exactPrefixNextCode default marker)
        (reweightedSeedPrefixJoint
          law G n S D projection) = _
  rw [reweightedSeedPrefixNextJoint_as_actual_pushforward]
  apply exactGroupedMass_congr
  · funext point
    rfl
  · funext point
    exact reweightedSeedPosterior_eq_product law G n S D point

theorem exactReverseAliceActualConditionalSeedWeight_pos
    {n : ℕ} (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (seed : ExactRemainingSeed D) :
    0 <
      (exactReverseAliceConditionalSeedLaw
        (exactRemainingCoordinate_card_pos D remaining)
        (exactReverseLeftSide seed)).weight seed := by
  have side :
      (exactReverseLeftSide seed).Nonempty :=
    ⟨seed.coordinate,
      exactReverseLeftSide_coordinate_mem seed⟩
  rw [exactReverseAliceConditionalSeedLaw_weight
    (exactRemainingCoordinate_card_pos D remaining)
    (exactReverseLeftSide seed) side seed]
  unfold exactReverseAliceConditionalSeedWeight
  simp only [↓reduceIte]
  exact div_pos
    (exactSeedWeight_pos_of_seed seed)
    ((reversePartitionWeight_pos_iff
      (exactRemainingCoordinate_card_pos D remaining)
      (exactReverseLeftSide seed)).mpr side)

theorem exactReverseAliceMaskedOutcomeContext_actual
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (default : Y)
    (seed : ExactRemainingSeed D)
    (outcome : ExactOutcome X Y A B n) :
    exactReverseAliceMaskedOutcomeContext
        G n S D (exactReverseLeftSide seed) default
        ((exactReverseAliceContext seed).sideRank
          ⟨seed.coordinate,
            exactReverseLeftSide_coordinate_mem seed⟩)
        (exactReverseAliceContextAt
          (exactReverseLeftSide seed) seed)
        outcome =
      exactReverseAliceMarkedHistoryContext
        G n S D default seed outcome := by
  simp only [exactReverseAliceMaskedOutcomeContext, exactReverseAliceContextOutcomeProjection,
    exactReverseAliceContextAt_actual, exactReverseAliceMarkedHistoryContext,
    exactReverseAliceSourceProjection]

theorem exactReverseAliceSideMarkedPosteriorConditional_eq_fixedSeedFiber
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (default : Y)
    (seed : ExactRemainingSeed D)
    (reference : ExactOutcome X Y A B n) :
    jointConditional
        (groupedMass
          (exactPrefixNextCode default
            ((exactReverseAliceContext seed).sideRank
              ⟨seed.coordinate,
                exactReverseLeftSide_coordinate_mem seed⟩))
          (exactConditionedReverseAliceNextJoint
            G n S D remaining (exactReverseLeftSide seed)))
        (exactReverseAliceMarkedHistoryContext
          G n S D default seed reference) =
      jointConditional
        (groupedMass
          (fun outcome : ExactOutcome X Y A B n =>
            (exactReverseAliceMarkedHistoryContext
              G n S D default seed outcome,
              outcome.2.1 seed.coordinate.val))
          (repeatedConditionedOutcomeLaw G n S D))
        (exactReverseAliceMarkedHistoryContext
          G n S D default seed reference) := by
  classical
  let side := exactReverseLeftSide seed
  let marker : Fin side.card :=
    (exactReverseAliceContext seed).sideRank
      ⟨seed.coordinate,
        exactReverseLeftSide_coordinate_mem seed⟩
  let law := exactReverseAliceConditionalSeedLaw
    (exactRemainingCoordinate_card_pos D remaining) side
  let index : ExactRemainingSeed D →
      ExactReverseSideContext
        (SourceRemainingCoordinate D) side :=
    exactReverseAliceContextAt side
  let context :
      ExactReverseSideContext
        (SourceRemainingCoordinate D) side →
          ExactOutcome X Y A B n →
            ExactReverseAliceNextContext X Y A B D side :=
    exactReverseAliceMaskedOutcomeContext
      G n S D side default marker
  let next :
      ExactReverseSideContext
        (SourceRemainingCoordinate D) side →
          ExactOutcome X Y A B n → Y :=
    fun current outcome =>
      outcome.2.1 (current.sideRank.symm marker).val.val
  let extract :
      ExactReverseAliceNextContext X Y A B D side →
        ExactReverseSideContext
          (SourceRemainingCoordinate D) side :=
    fun current => current.1.1.1
  let target := exactReverseAliceMarkedHistoryContext
    G n S D default seed reference
  have extracts : ∀ current outcome,
      extract (context current outcome) = current := by
    intro current outcome
    exact exactReverseAliceMaskedOutcomeContext_extract
      G n S D side default marker current outcome
  have target_index : extract target = index seed := by
    rfl
  have positive :
      0 < groupedMass index law.weight (index seed) := by
    apply groupedMass_pos_of_supported_atom
      index law.weight law.weight_nonneg seed
    exact exactReverseAliceActualConditionalSeedWeight_pos
      D remaining seed
  have stable :=
    jointConditional_product_stable_context_seed
      index context next extract extracts law.weight
      (repeatedConditionedOutcomeLaw G n S D)
      seed target target_index (ne_of_gt positive)
  rw [exactConditionedReverseAliceNextJoint_marked_mixture
    G n S D remaining side default marker]
  change
    jointConditional
        (groupedMass
          (fun point : ExactJointOutcome X Y A B D =>
            (context (index point.1) point.2,
              next (index point.1) point.2))
          (fun point : ExactJointOutcome X Y A B D =>
            law.weight point.1 *
              repeatedConditionedOutcomeLaw
                G n S D point.2))
        target =
      jointConditional
        (groupedMass
          (fun outcome : ExactOutcome X Y A B n =>
            (exactReverseAliceMarkedHistoryContext
              G n S D default seed outcome,
              outcome.2.1 seed.coordinate.val))
          (repeatedConditionedOutcomeLaw G n S D))
        target
  calc
    jointConditional
        (groupedMass
          (fun point : ExactJointOutcome X Y A B D =>
            (context (index point.1) point.2,
              next (index point.1) point.2))
          (fun point : ExactJointOutcome X Y A B D =>
            law.weight point.1 *
              repeatedConditionedOutcomeLaw
                G n S D point.2))
        target =
      jointConditional
        (groupedMass
          (fun outcome : ExactOutcome X Y A B n =>
            (context (index seed) outcome,
              next (index seed) outcome))
          (repeatedConditionedOutcomeLaw G n S D))
        target := by
          convert stable using 1
          · congr 1
            exact exactGroupedMass_decidableEq_irrel
              _ _ _ _
          · congr 1
            exact exactGroupedMass_decidableEq_irrel
              _ _ _ _
    _ = jointConditional
        (groupedMass
          (fun outcome : ExactOutcome X Y A B n =>
            (exactReverseAliceMarkedHistoryContext
              G n S D default seed outcome,
              outcome.2.1 seed.coordinate.val))
          (repeatedConditionedOutcomeLaw G n S D))
        target := by
          refine congrArg (fun j => jointConditional j target) ?_
          apply congrArg
            (fun code =>
              groupedMass code
                (repeatedConditionedOutcomeLaw G n S D))
          funext outcome
          apply Prod.ext
          · exact exactReverseAliceMaskedOutcomeContext_actual
              G n S D default seed outcome
          · simp only [exactReverseAliceContextAt_actual, Equiv.symm_apply_apply, next, side,
              marker, index]

theorem exactReverseAliceSideMarkedPosteriorConditional_eq_sourcePosterior
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (default : Y)
    (seed : ExactRemainingSeed D)
    (reference : ExactOutcome X Y A B n) :
    jointConditional
        (groupedMass
          (exactPrefixNextCode default
            ((exactReverseAliceContext seed).sideRank
              ⟨seed.coordinate,
                exactReverseLeftSide_coordinate_mem seed⟩))
          (exactConditionedReverseAliceNextJoint
            G n S D remaining (exactReverseLeftSide seed)))
        (exactReverseAliceMarkedHistoryContext
          G n S D default seed reference) =
      jointConditional
        (fun atom :
          ((SourceRemainingCoordinate D × X) ×
            ExactHistoryFlag X Y A B D) × Y =>
          exactAliceInformationPosterior G n S D
            (atom.1.1, (atom.1.2, atom.2)))
        ((seed.coordinate, reference.1 seed.coordinate.val),
          exactHistoryCode D (seed, reference)) := by
  exact
    (exactReverseAliceSideMarkedPosteriorConditional_eq_fixedSeedFiber
      G n S D remaining default seed reference).trans
      (exactReverseAliceMarkedPosteriorConditional_eq_sourcePosterior
        G n S D default seed reference)

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem reweightedSeedPrefixPriorMarginal_ne_zero_of_positive_atom
    {K Ω V : Type*} [Fintype K] [Fintype Ω] [Fintype V]
    {h : ℕ}
    (law : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (projection : K × ExactOutcome X Y A B n →
      Ω × (Fin h → V))
    (default : V) (marker : Fin h)
    (point : K × ExactOutcome X Y A B n)
    (atom_positive :
      0 < reweightedSeedPosterior law G n S D point) :
    jointFirstMarginal
        (groupedMass (exactPrefixNextCode default marker)
          (reweightedSeedPrefixPrior
            law G n S D projection))
        (finitePrefixMask default marker.castSucc
          (((projection point).1,
            repeatedConditionedAnswerFlag
              G n S D point.2),
            (projection point).2)) ≠ 0 := by
  classical
  let augmented :
      K × ExactOutcome X Y A B n →
        (Ω × ConditionedAnswerFlag A B D) ×
          (Fin h → V) :=
    fun source =>
      (((projection source).1,
        repeatedConditionedAnswerFlag
          G n S D source.2),
        (projection source).2)
  let target :=
    finitePrefixMask default marker.castSucc
      (augmented point)
  let posterior := reweightedSeedPosterior law G n S D
  let joint := reweightedSeedPrefixJoint
    law G n S D projection
  let prior := reweightedSeedPrefixPrior
    law G n S D projection
  have joint_pushforward : joint = groupedMass augmented posterior := by
    funext outcome
    exact reweightedSeedPrefixJoint_as_actual_flagged_pushforward
      law G n S D projection outcome
  have posterior_nonnegative : ∀ source, 0 ≤ posterior source := by
    intro source
    unfold posterior reweightedSeedPosterior
    apply conditionedEventDistribution_nonneg
    rw [reweightedSeedWinEventMass]
    exact positive
  have masked_posterior_positive :
      0 < groupedMass
        (finitePrefixMask default marker.castSucc)
        joint target := by
    rw [joint_pushforward, groupedMass_comp]
    exact groupedMass_pos_of_supported_atom
      (finitePrefixMask default marker.castSucc ∘ augmented)
      posterior posterior_nonnegative point atom_positive
  intro zero
  have masked_prior_zero :
      groupedMass
        (finitePrefixMask default marker.castSucc)
        prior target = 0 := by
    have first := congrFun
      (exactPrefixNext_firstMarginal
        prior default marker) target
    calc
      groupedMass
          (finitePrefixMask default marker.castSucc)
          prior target =
        jointFirstMarginal
          (groupedMass (exactPrefixNextCode default marker)
            prior) target := by
          convert first.symm using 1
          · exact congrFun
              (exactGroupedMass_decidableEq_irrel
                _ _ (finitePrefixMask
                  default marker.castSucc) prior)
              target
          · exact congrArg
              (fun mass => jointFirstMarginal mass target)
              (exactGroupedMass_decidableEq_irrel
                _ _ (exactPrefixNextCode
                  default marker) prior)
      _ = 0 := zero
  have masked_posterior_zero :
      groupedMass
        (finitePrefixMask default marker.castSucc)
        joint target = 0 :=
    groupedMass_absolute_continuity
      (finitePrefixMask default marker.castSucc)
      joint prior
      (reweightedSeedPrefixPrior_nonneg
        law G n S D positive projection)
      (reweightedSeedPrefix_absolute_continuity
        law G n S D positive projection)
      target masked_prior_zero
  exact (ne_of_gt masked_posterior_positive)
    masked_posterior_zero

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

private def exactReverseAliceContextMarkerInformation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (default : Y)
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) : ℝ :=
  ∑ outcome : ExactOutcome X Y A B n,
    repeatedConditionedOutcomeLaw G n S D outcome *
      finiteRelativeEntropy
        (jointConditional
          (groupedMass
            (exactPrefixNextCode default marker)
            (exactConditionedReverseAliceNextJoint
              G n S D remaining side))
          (exactReverseAliceMaskedOutcomeContext
            G n S D side default marker context outcome))
        (jointConditional
          (groupedMass
            (exactPrefixNextCode default marker)
            (exactConditionedReverseAliceNextPrior
              G n S D remaining side))
          (exactReverseAliceMaskedOutcomeContext
            G n S D side default marker context outcome))

theorem exactReverseAlicePrefixIncrement_eq_contextMarkerInformation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (side : Finset (SourceRemainingCoordinate D))
    (default : Y) (marker : Fin side.card) :
    exactConditionedReverseAlicePrefixEntropyIncrement
        G n S D remaining side default marker =
      ∑ seed : ExactRemainingSeed D,
        (exactReverseAliceConditionalSeedLaw
          (exactRemainingCoordinate_card_pos
            D remaining) side).weight seed *
          exactReverseAliceContextMarkerInformation
            G n S D remaining default side
            (exactReverseAliceContextAt side seed) marker := by
  classical
  let law := exactReverseAliceConditionalSeedLaw
    (exactRemainingCoordinate_card_pos D remaining) side
  let projection := exactReverseAliceSourceProjection
    (X := X) (Y := Y) (A := A) (B := B) D side
  have actual :=
    reweightedSeedPrefixEntropyIncrement_eq_actual_atom_sum
      law G n S D positive projection default marker
  have actual_joint :
      reweightedSeedPrefixJoint
          law G n S D projection =
        exactConditionedReverseAliceNextJoint
          G n S D remaining side := by
    rfl
  have actual_prior :
      reweightedSeedPrefixPrior
          law G n S D projection =
        exactConditionedReverseAliceNextPrior
          G n S D remaining side := by
    rfl
  rw [actual_joint, actual_prior] at actual
  change
    reweightedSeedPrefixEntropyIncrement
        law G n S D projection default marker = _
  rw [actual, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro seed _
  unfold exactReverseAliceContextMarkerInformation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro outcome _
  rw [reweightedSeedPosterior_eq_product]
  have same_context :
      finitePrefixMask default marker.castSucc
          (((projection (seed, outcome)).1,
            repeatedConditionedAnswerFlag
              G n S D outcome),
            (projection (seed, outcome)).2) =
        exactReverseAliceMaskedOutcomeContext
          G n S D side default marker
          (exactReverseAliceContextAt side seed)
          outcome := by
    rfl
  rw [same_context]
  change
    (law.weight seed *
      repeatedConditionedOutcomeLaw G n S D outcome) * _ =
      law.weight seed *
        (repeatedConditionedOutcomeLaw G n S D outcome * _)
  ring

theorem exactReverseAlicePrefixInformation_eq_seedMarkerAverage
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (default : Y) :
    exactConditionedReverseAlicePrefixInformation
        G n S D remaining default =
      ∑ seed : ExactRemainingSeed D,
        exactSeedWeight seed *
          ((∑ marker : Fin (exactReverseLeftSide seed).card,
            exactReverseAliceContextMarkerInformation
              G n S D remaining default
              (exactReverseLeftSide seed)
              (exactReverseAliceContextAt
                (exactReverseLeftSide seed) seed)
              marker) /
            ((exactReverseLeftSide seed).card : ℝ)) := by
  classical
  calc
    exactConditionedReverseAlicePrefixInformation
        G n S D remaining default =
      ∑ side : Finset (SourceRemainingCoordinate D),
        reversePartitionWeight side *
          ((∑ marker : Fin side.card,
            ∑ seed : ExactRemainingSeed D,
              (exactReverseAliceConditionalSeedLaw
                (exactRemainingCoordinate_card_pos
                  D remaining) side).weight seed *
                exactReverseAliceContextMarkerInformation
                  G n S D remaining default side
                  (exactReverseAliceContextAt side seed)
                  marker) / (side.card : ℝ)) := by
      unfold exactConditionedReverseAlicePrefixInformation
      apply Finset.sum_congr rfl
      intro side _
      congr 1
      apply congrArg (fun total : ℝ => total / (side.card : ℝ))
      apply Finset.sum_congr rfl
      intro marker _
      exact exactReverseAlicePrefixIncrement_eq_contextMarkerInformation
        G n S D remaining positive side default marker
    _ = _ := by
      exact exactReverseAliceSideWeightedPrefix_sum
        (exactRemainingCoordinate_card_pos D remaining)
        (fun side seed marker =>
          exactReverseAliceContextMarkerInformation
            G n S D remaining default side
            (exactReverseAliceContextAt side seed) marker)

theorem exactReverseAlicePrefixInformation_eq_markedSeedAverage
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (default : Y) :
    exactConditionedReverseAlicePrefixInformation
        G n S D remaining default =
      ∑ seed : ExactRemainingSeed D,
        exactSeedWeight seed *
          exactReverseAliceContextMarkerInformation
            G n S D remaining default
            (exactReverseLeftSide seed)
            (exactReverseAliceContext seed)
            ((exactReverseAliceContext seed).sideRank
              ⟨seed.coordinate,
                exactReverseLeftSide_coordinate_mem seed⟩) := by
  classical
  calc
    exactConditionedReverseAlicePrefixInformation
        G n S D remaining default =
      ∑ seed : ExactRemainingSeed D,
        exactSeedWeight seed *
          ((∑ marker : Fin (exactReverseLeftSide seed).card,
            exactReverseAliceContextMarkerInformation
              G n S D remaining default
              (exactReverseLeftSide seed)
              (exactReverseAliceContextAt
                (exactReverseLeftSide seed) seed)
              marker) /
            ((exactReverseLeftSide seed).card : ℝ)) :=
      exactReverseAlicePrefixInformation_eq_seedMarkerAverage
        G n S D remaining positive default
    _ = ∑ seed : ExactRemainingSeed D,
        exactSeedWeight seed *
          ((∑ marker : Fin (exactReverseLeftSide seed).card,
            exactReverseAliceContextMarkerInformation
              G n S D remaining default
              (exactReverseLeftSide seed)
              (exactReverseAliceContext seed)
              marker) /
            ((exactReverseLeftSide seed).card : ℝ)) := by
        simp_rw [exactReverseAliceContextAt_actual]
    _ = _ :=
      exactReverseAliceUniformMarkedSeed_sum
        (exactRemainingCoordinate_card_pos D remaining)
        (fun side context marker =>
          exactReverseAliceContextMarkerInformation
            G n S D remaining default side context marker)

theorem repeatedConditionedOutcomeLaw_pos_of_ne_zero
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (outcome : ExactOutcome X Y A B n)
    (nonzero : repeatedConditionedOutcomeLaw
      G n S D outcome ≠ 0) :
    0 < repeatedConditionedOutcomeLaw G n S D outcome := by
  have nonnegative :
      0 ≤ repeatedConditionedOutcomeLaw
        G n S D outcome := by
    exact conditionedEventDistribution_nonneg
      (strategyEventLaw (G.repeat n) S)
      (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)
      positive outcome
  exact lt_of_le_of_ne nonnegative nonzero.symm

theorem exactReverseAliceMarkedPriorMarginal_ne_zero_of_outcome
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (default : Y)
    (seed : ExactRemainingSeed D)
    (outcome : ExactOutcome X Y A B n)
    (outcome_nonzero :
      repeatedConditionedOutcomeLaw G n S D outcome ≠ 0) :
    jointFirstMarginal
        (groupedMass
          (exactPrefixNextCode default
            ((exactReverseAliceContext seed).sideRank
              ⟨seed.coordinate,
                exactReverseLeftSide_coordinate_mem seed⟩))
          (exactConditionedReverseAliceNextPrior
            G n S D remaining
            (exactReverseLeftSide seed)))
        (exactReverseAliceMarkedHistoryContext
          G n S D default seed outcome) ≠ 0 := by
  classical
  let side := exactReverseLeftSide seed
  let marker : Fin side.card :=
    (exactReverseAliceContext seed).sideRank
      ⟨seed.coordinate,
        exactReverseLeftSide_coordinate_mem seed⟩
  let law := exactReverseAliceConditionalSeedLaw
    (exactRemainingCoordinate_card_pos D remaining) side
  let projection := exactReverseAliceSourceProjection
    (X := X) (Y := Y) (A := A) (B := B) D side
  have atom_positive :
      0 < reweightedSeedPosterior
        law G n S D (seed, outcome) := by
    rw [reweightedSeedPosterior_eq_product]
    exact mul_pos
      (exactReverseAliceActualConditionalSeedWeight_pos
        D remaining seed)
      (repeatedConditionedOutcomeLaw_pos_of_ne_zero
        G n S D positive outcome outcome_nonzero)
  have supported :=
    reweightedSeedPrefixPriorMarginal_ne_zero_of_positive_atom
      law G n S D positive projection default marker
      (seed, outcome) atom_positive
  simpa [law, projection, side, marker,
    exactConditionedReverseAliceNextPrior,
    exactReverseAliceMarkedHistoryContext,
    exactReverseAliceSourceProjection] using supported

private def exactAliceSourceSeedBornInformation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D) : ℝ :=
  ∑ outcome : ExactOutcome X Y A B n,
    repeatedConditionedOutcomeLaw G n S D outcome *
      finiteRelativeEntropy
        (jointConditional
          (fun atom :
            ((SourceRemainingCoordinate D × X) ×
              ExactHistoryFlag X Y A B D) × Y =>
            exactAliceInformationPosterior G n S D
              (atom.1.1, (atom.1.2, atom.2)))
          ((seed.coordinate, outcome.1 seed.coordinate.val),
            exactHistoryCode D (seed, outcome)))
        (G.conditionalYGivenX
          (outcome.1 seed.coordinate.val))

theorem exactReverseAliceMarkedContextInformation_eq_source
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (default : Y)
    (seed : ExactRemainingSeed D) :
    exactReverseAliceContextMarkerInformation
        G n S D remaining default
        (exactReverseLeftSide seed)
        (exactReverseAliceContext seed)
        ((exactReverseAliceContext seed).sideRank
          ⟨seed.coordinate,
            exactReverseLeftSide_coordinate_mem seed⟩) =
      exactAliceSourceSeedBornInformation
        G n S D seed := by
  classical
  unfold exactReverseAliceContextMarkerInformation
    exactAliceSourceSeedBornInformation
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases zero :
      repeatedConditionedOutcomeLaw G n S D outcome = 0
  · simp only [zero, zero_mul]
  · have actual_context :
        exactReverseAliceMaskedOutcomeContext
            G n S D (exactReverseLeftSide seed) default
            ((exactReverseAliceContext seed).sideRank
              ⟨seed.coordinate,
                exactReverseLeftSide_coordinate_mem seed⟩)
            (exactReverseAliceContext seed) outcome =
          exactReverseAliceMarkedHistoryContext
            G n S D default seed outcome := by
        simpa only [exactReverseAliceContextAt_actual] using
          exactReverseAliceMaskedOutcomeContext_actual
            G n S D default seed outcome
    rw [actual_context]
    congr 1
    exact congrArg₂ finiteRelativeEntropy
      (exactReverseAliceSideMarkedPosteriorConditional_eq_sourcePosterior
        G n S D remaining default seed outcome)
      (exactReverseAliceMarkedPriorConditional_eq_game
        G n S D remaining default seed outcome
        (exactReverseAliceMarkedPriorMarginal_ne_zero_of_outcome
          G n S D remaining positive default seed outcome zero))

theorem exactAliceSourceConditionalInformation_eq_seedBornAverage
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D) :
    exactAliceSourceConditionalInformation G n S D base =
      ∑ seed : ExactRemainingSeed D,
        exactSeedWeight seed *
          exactAliceSourceSeedBornInformation G n S D seed := by
  classical
  rw [exactAliceSourceConditionalInformation_eq_joint_atom_sum
    G n S D remaining positive base, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro seed _
  unfold exactAliceSourceSeedBornInformation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro outcome _
  unfold exactPostselectedJointLaw
  ring

theorem exactReverseAliceConditionalHistoryIdentification_proved
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (default : Y) :
    ExactReverseAliceConditionalHistoryIdentification
      G n S D remaining base default := by
  unfold ExactReverseAliceConditionalHistoryIdentification
  rw [exactAliceSourceConditionalInformation_eq_seedBornAverage
    G n S D remaining positive base,
    exactReverseAlicePrefixInformation_eq_markedSeedAverage
      G n S D remaining positive default]
  apply Finset.sum_congr rfl
  intro seed _
  refine congrArg₂ (· * ·) rfl ?_
  exact
    (exactReverseAliceMarkedContextInformation_eq_source
      G n S D remaining positive default seed).symm

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

omit [Fintype X] [Fintype Y] [Fintype A] [Fintype B] in
theorem exactReverseBobMaskedQuestionRegister_stable
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (default : X) (marker : Fin side.card)
    (flag : ConditionedAnswerFlag A B D)
    (seed : ExactRemainingSeed D)
    (ys : Fin n → Y)
    (tail : {j : Fin n //
      j ≠ ((exactReverseBobContextAt side seed).sideRank.symm
        marker).val.val} → X)
    (x x' : X) :
    exactReverseBobMaskedQuestionRegister
        D side default marker flag seed
        ((Equiv.funSplitAt
          ((exactReverseBobContextAt side seed).sideRank.symm
            marker).val.val X).symm (x, tail)) ys =
      exactReverseBobMaskedQuestionRegister
        D side default marker flag seed
        ((Equiv.funSplitAt
          ((exactReverseBobContextAt side seed).sideRank.symm
            marker).val.val X).symm (x', tail)) ys := by
  classical
  let context := exactReverseBobContextAt side seed
  let marked : SourceRemainingCoordinate D :=
    (context.sideRank.symm marker).val
  let coordinate : Fin n := marked.val
  have outsideD : coordinate ∉ D := by
    exact (Finset.mem_sdiff.mp marked.property).2
  have outsideOther : marked ∉ context.otherSide := by
    rw [context.otherSide_eq_complement]
    simp only [univ_eq_attach, mem_sdiff, mem_attach, (context.sideRank.symm marker).property,
      not_true_eq_false, and_false, not_false_eq_true, marked]
  change
    exactReverseBobMaskedQuestionRegister
        D side default marker flag seed
        ((Equiv.funSplitAt coordinate X).symm (x, tail)) ys =
      exactReverseBobMaskedQuestionRegister
        D side default marker flag seed
        ((Equiv.funSplitAt coordinate X).symm (x', tail)) ys
  unfold exactReverseBobMaskedQuestionRegister
    finitePrefixMask
  apply Prod.ext
  · apply Prod.ext
    · apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Prod.ext
        · funext j
          have different : j.val ≠ coordinate := by
            intro same
            exact outsideD (same ▸ j.property)
          simp only [ne_eq, Equiv.funSplitAt, Equiv.piSplitAt, eq_rec_constant, Equiv.symm_mk,
            Equiv.coe_fn_mk, different, ↓reduceDIte]
        apply Prod.ext
        · rfl
        apply Prod.ext
        · rfl
        apply Prod.ext
        · funext j
          have different : j.val.val ≠ coordinate := by
            intro same
            apply outsideOther
            have actual : j.val = marked := by
              apply Subtype.ext
              exact same
            exact actual ▸ j.property
          simp only [ne_eq, Equiv.funSplitAt, Equiv.piSplitAt, eq_rec_constant, Equiv.symm_mk,
            Equiv.coe_fn_mk, different, ↓reduceDIte]
        · rfl
    · rfl
  · funext position
    by_cases before : position.val < marker.val
    · have different :
          ((context.sideRank.symm position).val.val) ≠ coordinate := by
        intro same
        have sameMarked :
            context.sideRank.symm position =
              context.sideRank.symm marker := by
          apply Subtype.ext
          apply Subtype.ext
          exact same
        have samePosition :=
          context.sideRank.symm.injective sameMarked
        exact (Nat.ne_of_lt before)
          (congrArg Fin.val samePosition)
      simp only [Fin.val_castSucc, before, ↓reduceIte, ne_eq, Equiv.funSplitAt, Equiv.piSplitAt,
        eq_rec_constant, Equiv.symm_mk, Equiv.coe_fn_mk, different, ↓reduceDIte, context]
    · simp only [Fin.val_castSucc, before, ↓reduceIte]

theorem exactConditionedReverseBobNextPrior_flagged_mixture
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (side : Finset (SourceRemainingCoordinate D))
    (default : X) (marker : Fin side.card) :
    groupedMass (exactPrefixNextCode default marker)
        (exactConditionedReverseBobNextPrior
          G n S D remaining side) =
      groupedMass
        (fun point :
          (ConditionedAnswerFlag A B D ×
            ExactRemainingSeed D) ×
              ExactOutcome X Y A B n =>
          (exactReverseBobMaskedQuestionRegister
            D side default marker point.1.1 point.1.2
            point.2.1 point.2.2.1,
            point.2.1
              (((exactReverseBobContextAt
                side point.1.2).sideRank.symm marker).val.val)))
        (fun point :
          (ConditionedAnswerFlag A B D ×
            ExactRemainingSeed D) ×
              ExactOutcome X Y A B n =>
          (finiteUniformWeight
              (ConditionedAnswerFlag A B D) *
            (exactReverseBobConditionalSeedLaw
              (exactRemainingCoordinate_card_pos
                D remaining) side).weight point.1.2) *
            (strategyEventLaw (G.repeat n) S).weight point.2) := by
  classical
  funext target
  let seedLaw := exactReverseBobConditionalSeedLaw
    (exactRemainingCoordinate_card_pos D remaining) side
  let projection := exactReverseBobSourceProjection
    (X := X) (Y := Y) (A := A) (B := B) D side
  change
    groupedMass (exactPrefixNextCode default marker)
        (reweightedSeedPrefixPrior
          seedLaw G n S D projection) target = _
  calc
    groupedMass (exactPrefixNextCode default marker)
        (reweightedSeedPrefixPrior
          seedLaw G n S D projection) target =
      groupedMass
        (fun point : ConditionedAnswerFlag A B D ×
          (ExactRemainingSeed D ×
            ExactOutcome X Y A B n) =>
          exactPrefixNextCode default marker
            (((projection point.2).1, point.1),
              (projection point.2).2))
        (fun point : ConditionedAnswerFlag A B D ×
          (ExactRemainingSeed D ×
            ExactOutcome X Y A B n) =>
          finiteUniformWeight
              (ConditionedAnswerFlag A B D) *
            (reweightedSeedPriorEventLaw
              seedLaw G n S).weight point.2)
        target :=
      reweightedSeedPrefixPrior_next_flagged_pushforward
        seedLaw G n S D projection default marker target
    _ = _ := by
      change
        groupedMass
          (fun point : ConditionedAnswerFlag A B D ×
            (ExactRemainingSeed D ×
              ExactOutcome X Y A B n) =>
            (exactReverseBobMaskedQuestionRegister
              D side default marker point.1 point.2.1
              point.2.2.1 point.2.2.2.1,
              point.2.2.1
                (((exactReverseBobContextAt
                  side point.2.1).sideRank.symm marker).val.val)))
          (fun point : ConditionedAnswerFlag A B D ×
            (ExactRemainingSeed D ×
              ExactOutcome X Y A B n) =>
            finiteUniformWeight
                (ConditionedAnswerFlag A B D) *
              (seedLaw.weight point.2.1 *
                (strategyEventLaw (G.repeat n) S).weight point.2.2))
          target = _
      exact groupedMass_flagSeedOutcome_reassoc
        (F := ConditionedAnswerFlag A B D)
        (K := ExactRemainingSeed D)
        (Ω := ExactOutcome X Y A B n)
        (fun flag seed (outcome : ExactOutcome X Y A B n) =>
          (exactReverseBobMaskedQuestionRegister
            D side default marker flag seed outcome.1 outcome.2.1,
            outcome.1
              (((exactReverseBobContextAt
                side seed).sideRank.symm marker).val.val)))
        (fun _ : ConditionedAnswerFlag A B D =>
          finiteUniformWeight
            (ConditionedAnswerFlag A B D))
        seedLaw.weight
        (strategyEventLaw (G.repeat n) S).weight target

omit [Fintype X] [Fintype Y] [Fintype A] [Fintype B] in
theorem exactReverseBobMaskedQuestionRegister_determines
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (default : X) (marker : Fin side.card)
    (flag : ConditionedAnswerFlag A B D)
    (seed : ExactRemainingSeed D)
    (xs : Fin n → X) (ys : Fin n → Y)
    (target : ExactReverseBobNextContext X Y A B D side)
    (same :
      exactReverseBobMaskedQuestionRegister
        D side default marker flag seed xs ys = target) :
    ys (((exactReverseBobContextAt
        side seed).sideRank.symm marker).val.val) =
      target.1.1.2.2.2.1
        (target.1.1.1.sideRank.symm marker) := by
  have actual := congrArg
    (fun context : ExactReverseBobNextContext
      X Y A B D side =>
      context.1.1.2.2.2.1
        (context.1.1.1.sideRank.symm marker)) same
  exact actual

theorem exactConditionedReverseBobNextPrior_marked_joint_factor
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (side : Finset (SourceRemainingCoordinate D))
    (default : X) (marker : Fin side.card)
    (target : ExactReverseBobNextContext X Y A B D side)
    (next : X) :
    groupedMass
        (exactPrefixNextCode default marker)
        (exactConditionedReverseBobNextPrior
          G n S D remaining side)
        (target, next) =
      G.conditionalXGivenY
          (target.1.1.2.2.2.1
            (target.1.1.1.sideRank.symm marker)) next *
        jointFirstMarginal
          (groupedMass
            (exactPrefixNextCode default marker)
            (exactConditionedReverseBobNextPrior
              G n S D remaining side))
          target := by
  classical
  let seedLaw := exactReverseBobConditionalSeedLaw
    (exactRemainingCoordinate_card_pos D remaining) side
  let mixedWeight :
      ConditionedAnswerFlag A B D ×
        ExactRemainingSeed D → ℝ :=
    fun index =>
      finiteUniformWeight
        (ConditionedAnswerFlag A B D) *
        seedLaw.weight index.2
  let coordinate :
      ConditionedAnswerFlag A B D ×
        ExactRemainingSeed D → Fin n :=
    fun index =>
      ((exactReverseBobContextAt
        side index.2).sideRank.symm marker).val.val
  let code :
      (ConditionedAnswerFlag A B D ×
        ExactRemainingSeed D) →
          (Fin n → X) → (Fin n → Y) →
            ExactReverseBobNextContext X Y A B D side :=
    fun index xs ys =>
      exactReverseBobMaskedQuestionRegister
        D side default marker index.1 index.2 xs ys
  let question : Y :=
    target.1.1.2.2.2.1
      (target.1.1.1.sideRank.symm marker)
  have stable :
      ∀ (index : ConditionedAnswerFlag A B D ×
          ExactRemainingSeed D)
        (ys : Fin n → Y)
        (tail : {j : Fin n // j ≠ coordinate index} → X)
        (x x' : X),
        code index
            ((Equiv.funSplitAt (coordinate index) X).symm (x, tail)) ys =
          code index
            ((Equiv.funSplitAt (coordinate index) X).symm (x', tail)) ys := by
    intro index ys tail x x'
    exact exactReverseBobMaskedQuestionRegister_stable
      D side default marker index.1 index.2 ys tail x x'
  have determines :
      ∀ (index : ConditionedAnswerFlag A B D ×
          ExactRemainingSeed D)
        (xs : Fin n → X) (ys : Fin n → Y),
        code index xs ys = target →
          ys (coordinate index) = question := by
    intro index xs ys same
    exact exactReverseBobMaskedQuestionRegister_determines
      D side default marker index.1 index.2 xs ys target same
  have mixed := mixedStableAliceQuestionCode_joint_factor
    G n S mixedWeight coordinate code target question next
    stable determines
  rw [exactConditionedReverseBobNextPrior_flagged_mixture
    G n S D remaining side default marker]
  change
    groupedMass
        (fun point :
          (ConditionedAnswerFlag A B D ×
            ExactRemainingSeed D) ×
              ExactOutcome X Y A B n =>
          (code point.1 point.2.1 point.2.2.1,
            point.2.1 (coordinate point.1)))
        (fun point :
          (ConditionedAnswerFlag A B D ×
            ExactRemainingSeed D) ×
              ExactOutcome X Y A B n =>
          mixedWeight point.1 *
            (strategyEventLaw (G.repeat n) S).weight point.2)
        (target, next) =
      G.conditionalXGivenY question next *
        jointFirstMarginal
          (groupedMass
            (fun point :
              (ConditionedAnswerFlag A B D ×
                ExactRemainingSeed D) ×
                  ExactOutcome X Y A B n =>
              (code point.1 point.2.1 point.2.2.1,
                point.2.1 (coordinate point.1)))
            (fun point :
              (ConditionedAnswerFlag A B D ×
                ExactRemainingSeed D) ×
                  ExactOutcome X Y A B n =>
              mixedWeight point.1 *
                (strategyEventLaw (G.repeat n) S).weight point.2))
          target
  rw [jointFirstMarginal_groupedContextNext]
  convert mixed using 1
  exact congrFun (exactGroupedMass_decidableEq_irrel
    _ _ _ _) (target, next)

theorem exactConditionedReverseBobNextPrior_marked_conditional
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (side : Finset (SourceRemainingCoordinate D))
    (default : X) (marker : Fin side.card)
    (target : ExactReverseBobNextContext X Y A B D side)
    (supported :
      jointFirstMarginal
        (groupedMass
          (exactPrefixNextCode default marker)
          (exactConditionedReverseBobNextPrior
            G n S D remaining side))
        target ≠ 0) :
    jointConditional
        (groupedMass
          (exactPrefixNextCode default marker)
          (exactConditionedReverseBobNextPrior
            G n S D remaining side))
        target =
      G.conditionalXGivenY
        (target.1.1.2.2.2.1
          (target.1.1.1.sideRank.symm marker)) := by
  funext next
  unfold jointConditional
  rw [exactConditionedReverseBobNextPrior_marked_joint_factor
    G n S D remaining side default marker target next]
  exact mul_div_cancel_right₀ _ supported

theorem exactReverseBobMarkedPriorConditional_eq_game
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (default : X)
    (seed : ExactRemainingSeed D)
    (reference : ExactOutcome X Y A B n)
    (supported :
      jointFirstMarginal
        (groupedMass
          (exactPrefixNextCode default
            ((exactReverseBobContext seed).sideRank
              ⟨seed.coordinate,
                exactReverseRightSide_coordinate_mem seed⟩))
          (exactConditionedReverseBobNextPrior
            G n S D remaining
            (exactReverseRightSide seed)))
        (exactReverseBobMarkedHistoryContext
          G n S D default seed reference) ≠ 0) :
    jointConditional
        (groupedMass
          (exactPrefixNextCode default
            ((exactReverseBobContext seed).sideRank
              ⟨seed.coordinate,
                exactReverseRightSide_coordinate_mem seed⟩))
          (exactConditionedReverseBobNextPrior
            G n S D remaining
            (exactReverseRightSide seed)))
        (exactReverseBobMarkedHistoryContext
          G n S D default seed reference) =
      G.conditionalXGivenY
        (reference.2.1 seed.coordinate.val) := by
  have actual := exactConditionedReverseBobNextPrior_marked_conditional
    G n S D remaining
    (exactReverseRightSide seed) default
    ((exactReverseBobContext seed).sideRank
      ⟨seed.coordinate,
        exactReverseRightSide_coordinate_mem seed⟩)
    (exactReverseBobMarkedHistoryContext
      G n S D default seed reference) supported
  simpa only [exactReverseBobMarkedHistoryContext, finitePrefixMask,
    exactReverseBobSourceProjection, exactReverseBobContextAt_actual, Fin.val_castSucc,
    exactReverseBobContext_marked_rank, Equiv.symm_apply_apply] using actual

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

private def exactReverseBobMaskedOutcomeContext
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (default : X) (marker : Fin side.card)
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (outcome : ExactOutcome X Y A B n) :
    ExactReverseBobNextContext X Y A B D side :=
  let projection :=
    exactReverseBobContextOutcomeProjection
      (X := X) (Y := Y) (A := A) (B := B)
      D side context outcome
  finitePrefixMask default marker.castSucc
    ((projection.1,
      repeatedConditionedAnswerFlag G n S D outcome),
      projection.2)

theorem exactReverseBobMaskedOutcomeContext_extract
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (default : X) (marker : Fin side.card)
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (outcome : ExactOutcome X Y A B n) :
    (exactReverseBobMaskedOutcomeContext
      G n S D side default marker context outcome).1.1.1 =
      context := by
  rfl

theorem exactConditionedReverseBobNextJoint_marked_mixture
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (side : Finset (SourceRemainingCoordinate D))
    (default : X) (marker : Fin side.card) :
    groupedMass (exactPrefixNextCode default marker)
        (exactConditionedReverseBobNextJoint
          G n S D remaining side) =
      groupedMass
        (fun point : ExactJointOutcome X Y A B D =>
          (exactReverseBobMaskedOutcomeContext
            G n S D side default marker
            (exactReverseBobContextAt side point.1)
            point.2,
            point.2.1
              (((exactReverseBobContextAt
                side point.1).sideRank.symm marker).val.val)))
        (fun point : ExactJointOutcome X Y A B D =>
          (exactReverseBobConditionalSeedLaw
            (exactRemainingCoordinate_card_pos
              D remaining) side).weight point.1 *
            repeatedConditionedOutcomeLaw G n S D point.2) := by
  classical
  let law := exactReverseBobConditionalSeedLaw
    (exactRemainingCoordinate_card_pos D remaining) side
  let projection := exactReverseBobSourceProjection
    (X := X) (Y := Y) (A := A) (B := B) D side
  change
    groupedMass (exactPrefixNextCode default marker)
        (reweightedSeedPrefixJoint
          law G n S D projection) = _
  rw [reweightedSeedPrefixNextJoint_as_actual_pushforward]
  apply exactGroupedMass_congr
  · funext point
    rfl
  · funext point
    exact reweightedSeedPosterior_eq_product law G n S D point

theorem exactReverseBobConditionalSeedLaw_actual_pos
    {M : Type*} [Fintype M] [DecidableEq M]
    (nonempty : 0 < Fintype.card M)
    (seed : ExactForwardSeed M) :
    0 < (exactReverseBobConditionalSeedLaw
      nonempty (exactReverseRightSide seed)).weight seed := by
  have sideNonempty :
      (exactReverseRightSide seed).Nonempty :=
    ⟨seed.coordinate,
      exactReverseRightSide_coordinate_mem seed⟩
  rw [exactReverseBobConditionalSeedLaw_weight
    nonempty (exactReverseRightSide seed)
    sideNonempty seed]
  unfold exactReverseBobConditionalSeedWeight
  rw [ite_eq_left rfl]
  exact div_pos
    (exactSeedWeight_pos_of_seed seed)
    ((reversePartitionWeight_pos_iff nonempty
      (exactReverseRightSide seed)).mpr sideNonempty)

theorem exactReverseBobMaskedOutcomeContext_actual
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (default : X)
    (seed : ExactRemainingSeed D)
    (outcome : ExactOutcome X Y A B n) :
    exactReverseBobMaskedOutcomeContext
        G n S D (exactReverseRightSide seed) default
        ((exactReverseBobContext seed).sideRank
          ⟨seed.coordinate,
            exactReverseRightSide_coordinate_mem seed⟩)
        (exactReverseBobContextAt
          (exactReverseRightSide seed) seed)
        outcome =
      exactReverseBobMarkedHistoryContext
        G n S D default seed outcome := by
  simp only [exactReverseBobMaskedOutcomeContext, exactReverseBobContextOutcomeProjection,
    exactReverseBobContextAt_actual, exactReverseBobMarkedHistoryContext,
    exactReverseBobSourceProjection]

theorem exactConditionedReverseBobNextJoint_marked_conditional_eq_fixedOutcome
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (default : X)
    (seed : ExactRemainingSeed D)
    (reference : ExactOutcome X Y A B n) :
    jointConditional
        (groupedMass
          (exactPrefixNextCode default
            ((exactReverseBobContext seed).sideRank
              ⟨seed.coordinate,
                exactReverseRightSide_coordinate_mem seed⟩))
          (exactConditionedReverseBobNextJoint
            G n S D remaining
            (exactReverseRightSide seed)))
        (exactReverseBobMarkedHistoryContext
          G n S D default seed reference) =
      jointConditional
        (groupedMass
          (fun outcome : ExactOutcome X Y A B n =>
            (exactReverseBobMarkedHistoryContext
              G n S D default seed outcome,
              outcome.1 seed.coordinate.val))
          (repeatedConditionedOutcomeLaw G n S D))
        (exactReverseBobMarkedHistoryContext
          G n S D default seed reference) := by
  classical
  let side := exactReverseRightSide seed
  let marker : Fin side.card :=
    (exactReverseBobContext seed).sideRank
      ⟨seed.coordinate,
        exactReverseRightSide_coordinate_mem seed⟩
  let law := exactReverseBobConditionalSeedLaw
    (exactRemainingCoordinate_card_pos D remaining) side
  let index : ExactRemainingSeed D →
      ExactReverseSideContext
        (SourceRemainingCoordinate D) side :=
    exactReverseBobContextAt side
  let context :
      ExactReverseSideContext
        (SourceRemainingCoordinate D) side →
          ExactOutcome X Y A B n →
            ExactReverseBobNextContext X Y A B D side :=
    exactReverseBobMaskedOutcomeContext
      G n S D side default marker
  let next :
      ExactReverseSideContext
        (SourceRemainingCoordinate D) side →
          ExactOutcome X Y A B n → X :=
    fun reverseContext outcome =>
      outcome.1
        ((reverseContext.sideRank.symm marker).val.val)
  let extract :
      ExactReverseBobNextContext X Y A B D side →
        ExactReverseSideContext
          (SourceRemainingCoordinate D) side :=
    fun target => target.1.1.1
  let target :=
    exactReverseBobMarkedHistoryContext
      G n S D default seed reference
  have extract_context :
      ∀ (reverseContext : ExactReverseSideContext
          (SourceRemainingCoordinate D) side)
        (outcome : ExactOutcome X Y A B n),
        extract (context reverseContext outcome) = reverseContext := by
    intro reverseContext outcome
    exact exactReverseBobMaskedOutcomeContext_extract
      G n S D side default marker reverseContext outcome
  have target_index : extract target = index seed := by
    rfl
  have positive :
      0 < groupedMass index law.weight (index seed) := by
    apply groupedMass_pos_of_supported_atom
      index law.weight law.weight_nonneg seed
    exact exactReverseBobConditionalSeedLaw_actual_pos
      (exactRemainingCoordinate_card_pos D remaining) seed
  have stable := jointConditional_product_stable_context_seed
    index context next extract extract_context
    law.weight (repeatedConditionedOutcomeLaw G n S D)
    seed target target_index (ne_of_gt positive)
  rw [exactConditionedReverseBobNextJoint_marked_mixture
    G n S D remaining side default marker]
  change
    jointConditional
        (groupedMass
          (fun point : ExactJointOutcome X Y A B D =>
            (context (index point.1) point.2,
              next (index point.1) point.2))
          (fun point : ExactJointOutcome X Y A B D =>
            law.weight point.1 *
              repeatedConditionedOutcomeLaw
                G n S D point.2))
        target =
      jointConditional
        (groupedMass
          (fun outcome : ExactOutcome X Y A B n =>
            (exactReverseBobMarkedHistoryContext
              G n S D default seed outcome,
              outcome.1 seed.coordinate.val))
          (repeatedConditionedOutcomeLaw G n S D))
        target
  calc
    jointConditional
        (groupedMass
          (fun point : ExactJointOutcome X Y A B D =>
            (context (index point.1) point.2,
              next (index point.1) point.2))
          (fun point : ExactJointOutcome X Y A B D =>
            law.weight point.1 *
              repeatedConditionedOutcomeLaw
                G n S D point.2))
        target =
      jointConditional
        (groupedMass
          (fun outcome : ExactOutcome X Y A B n =>
            (context (index seed) outcome,
              next (index seed) outcome))
          (repeatedConditionedOutcomeLaw G n S D))
        target := by
          convert stable using 1
          · congr 1
            exact exactGroupedMass_decidableEq_irrel
              _ _ _ _
          · congr 1
            exact exactGroupedMass_decidableEq_irrel
              _ _ _ _
    _ = jointConditional
        (groupedMass
          (fun outcome : ExactOutcome X Y A B n =>
            (exactReverseBobMarkedHistoryContext
              G n S D default seed outcome,
              outcome.1 seed.coordinate.val))
          (repeatedConditionedOutcomeLaw G n S D))
        target := by
          refine congrArg (fun j => jointConditional j target) ?_
          apply congrArg
            (fun code =>
              groupedMass code
                (repeatedConditionedOutcomeLaw G n S D))
          funext outcome
          apply Prod.ext
          · exact exactReverseBobMaskedOutcomeContext_actual
              G n S D default seed outcome
          · simp only [exactReverseBobContextAt_actual, Equiv.symm_apply_apply, next, side,
              marker, index]

theorem exactConditionedReverseBobNextJoint_marked_conditional_eq_sourcePosterior
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (default : X)
    (seed : ExactRemainingSeed D)
    (reference : ExactOutcome X Y A B n) :
    jointConditional
        (groupedMass
          (exactPrefixNextCode default
            ((exactReverseBobContext seed).sideRank
              ⟨seed.coordinate,
                exactReverseRightSide_coordinate_mem seed⟩))
          (exactConditionedReverseBobNextJoint
            G n S D remaining
            (exactReverseRightSide seed)))
        (exactReverseBobMarkedHistoryContext
          G n S D default seed reference) =
      jointConditional
        (fun atom :
          ((SourceRemainingCoordinate D × Y) ×
            ExactHistoryFlag X Y A B D) × X =>
          exactBobInformationPosterior G n S D
            (atom.1.1, (atom.1.2, atom.2)))
        ((seed.coordinate, reference.2.1 seed.coordinate.val),
          exactHistoryCode D (seed, reference)) := by
  exact
    (exactConditionedReverseBobNextJoint_marked_conditional_eq_fixedOutcome
      G n S D remaining default seed reference).trans
      (exactReverseBobMarkedPosteriorConditional_eq_sourcePosterior
        G n S D default seed reference)

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

private def exactReverseBobContextMarkedEntropyScore
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (default : X)
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card)
    (outcome : ExactOutcome X Y A B n) : ℝ :=
  let target :=
    exactReverseBobMaskedOutcomeContext
      G n S D side default marker context outcome
  finiteRelativeEntropy
    (jointConditional
      (groupedMass
        (exactPrefixNextCode default marker)
        (exactConditionedReverseBobNextJoint
          G n S D remaining side))
      target)
    (jointConditional
      (groupedMass
        (exactPrefixNextCode default marker)
        (exactConditionedReverseBobNextPrior
          G n S D remaining side))
      target)

private def exactReverseBobActualMarkedEntropyScore
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (default : X)
    (side : Finset (SourceRemainingCoordinate D))
    (seed : ExactRemainingSeed D)
    (marker : Fin side.card)
    (outcome : ExactOutcome X Y A B n) : ℝ :=
  let target :=
    exactReverseBobMaskedOutcomeContext
      G n S D side default marker
      (exactReverseBobContextAt side seed)
      outcome
  finiteRelativeEntropy
    (jointConditional
      (groupedMass
        (exactPrefixNextCode default marker)
        (exactConditionedReverseBobNextJoint
          G n S D remaining side))
      target)
    (jointConditional
      (groupedMass
        (exactPrefixNextCode default marker)
        (exactConditionedReverseBobNextPrior
          G n S D remaining side))
      target)

theorem exactReverseBobActualMarkedEntropyScore_eq_context
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (default : X)
    (side : Finset (SourceRemainingCoordinate D))
    (seed : ExactRemainingSeed D)
    (marker : Fin side.card)
    (outcome : ExactOutcome X Y A B n) :
    exactReverseBobActualMarkedEntropyScore
        G n S D remaining default side seed marker outcome =
      exactReverseBobContextMarkedEntropyScore
        G n S D remaining default side
        (exactReverseBobContextAt side seed)
        marker outcome := by
  rfl

theorem exactConditionedReverseBobPrefixEntropyIncrement_eq_markedOutcomeScore
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (side : Finset (SourceRemainingCoordinate D))
    (default : X)
    (marker : Fin side.card) :
    exactConditionedReverseBobPrefixEntropyIncrement
        G n S D remaining side default marker =
      ∑ seed : ExactRemainingSeed D,
        (exactReverseBobConditionalSeedLaw
          (exactRemainingCoordinate_card_pos
            D remaining) side).weight seed *
          ∑ outcome : ExactOutcome X Y A B n,
            repeatedConditionedOutcomeLaw G n S D outcome *
              exactReverseBobActualMarkedEntropyScore
                G n S D remaining default side seed marker outcome := by
  classical
  let law := exactReverseBobConditionalSeedLaw
    (exactRemainingCoordinate_card_pos D remaining) side
  let projection := exactReverseBobSourceProjection
    (X := X) (Y := Y) (A := A) (B := B) D side
  change
    reweightedSeedPrefixEntropyIncrement
        law G n S D projection default marker = _
  rw [reweightedSeedPrefixEntropyIncrement_eq_actual_atom_sum
    law G n S D positive projection default marker]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro seed _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro outcome _
  rw [reweightedSeedPosterior_eq_product]
  change
    (law.weight seed *
      repeatedConditionedOutcomeLaw G n S D outcome) *
        exactReverseBobActualMarkedEntropyScore
          G n S D remaining default side seed marker outcome =
      law.weight seed *
        (repeatedConditionedOutcomeLaw G n S D outcome *
          exactReverseBobActualMarkedEntropyScore
            G n S D remaining default side seed marker outcome)
  ring

theorem exactConditionedReverseBobPrefixInformation_eq_sourceMarkerAverage
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (default : X) :
    exactConditionedReverseBobPrefixInformation
        G n S D remaining default =
      ∑ seed : ExactRemainingSeed D,
        exactSeedWeight seed *
          ((∑ marker : Fin (exactReverseRightSide seed).card,
            ∑ outcome : ExactOutcome X Y A B n,
              repeatedConditionedOutcomeLaw G n S D outcome *
                exactReverseBobActualMarkedEntropyScore
                  G n S D remaining default
                  (exactReverseRightSide seed)
                  seed marker outcome) /
            ((exactReverseRightSide seed).card : ℝ)) := by
  classical
  unfold exactConditionedReverseBobPrefixInformation
  simp_rw [
    exactConditionedReverseBobPrefixEntropyIncrement_eq_markedOutcomeScore
      G n S D remaining positive]
  exact exactReverseBobSideWeightedPrefix_sum
    (exactRemainingCoordinate_card_pos D remaining)
    (fun side seed marker =>
      ∑ outcome : ExactOutcome X Y A B n,
        repeatedConditionedOutcomeLaw G n S D outcome *
          exactReverseBobActualMarkedEntropyScore
            G n S D remaining default side seed marker outcome)

theorem exactConditionedReverseBobPrefixInformation_eq_sourceMarkedOutcomeScore
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (default : X) :
    exactConditionedReverseBobPrefixInformation
        G n S D remaining default =
      ∑ seed : ExactRemainingSeed D,
        exactSeedWeight seed *
          ∑ outcome : ExactOutcome X Y A B n,
            repeatedConditionedOutcomeLaw G n S D outcome *
              exactReverseBobContextMarkedEntropyScore
                G n S D remaining default
                (exactReverseRightSide seed)
                (exactReverseBobContext seed)
                ((exactReverseBobContext seed).sideRank
                  ⟨seed.coordinate,
                    exactReverseRightSide_coordinate_mem seed⟩)
                outcome := by
  calc
    exactConditionedReverseBobPrefixInformation
        G n S D remaining default =
      ∑ seed : ExactRemainingSeed D,
        exactSeedWeight seed *
          ((∑ marker : Fin (exactReverseRightSide seed).card,
            ∑ outcome : ExactOutcome X Y A B n,
              repeatedConditionedOutcomeLaw G n S D outcome *
                exactReverseBobActualMarkedEntropyScore
                  G n S D remaining default
                  (exactReverseRightSide seed)
                  seed marker outcome) /
            ((exactReverseRightSide seed).card : ℝ)) :=
      exactConditionedReverseBobPrefixInformation_eq_sourceMarkerAverage
        G n S D remaining positive default
    _ = _ := by
      simpa only [
        exactReverseBobActualMarkedEntropyScore_eq_context,
        exactReverseBobContextAt_actual] using
        (exactReverseBobUniformMarkedSeed_sum
          (exactRemainingCoordinate_card_pos D remaining)
          (fun side context marker =>
            ∑ outcome : ExactOutcome X Y A B n,
              repeatedConditionedOutcomeLaw G n S D outcome *
                exactReverseBobContextMarkedEntropyScore
                  G n S D remaining default side context marker outcome))

theorem exactReverseBobMarkedPriorMarginal_ne_zero_of_outcome
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (default : X)
    (seed : ExactRemainingSeed D)
    (outcome : ExactOutcome X Y A B n)
    (supported :
      repeatedConditionedOutcomeLaw G n S D outcome ≠ 0) :
    jointFirstMarginal
        (groupedMass
          (exactPrefixNextCode default
            ((exactReverseBobContext seed).sideRank
              ⟨seed.coordinate,
                exactReverseRightSide_coordinate_mem seed⟩))
          (exactConditionedReverseBobNextPrior
            G n S D remaining
            (exactReverseRightSide seed)))
        (exactReverseBobMarkedHistoryContext
          G n S D default seed outcome) ≠ 0 := by
  let side := exactReverseRightSide seed
  let marker : Fin side.card :=
    (exactReverseBobContext seed).sideRank
      ⟨seed.coordinate,
        exactReverseRightSide_coordinate_mem seed⟩
  let law := exactReverseBobConditionalSeedLaw
    (exactRemainingCoordinate_card_pos D remaining) side
  let projection := exactReverseBobSourceProjection
    (X := X) (Y := Y) (A := A) (B := B) D side
  have outcome_nonnegative :
      0 ≤ repeatedConditionedOutcomeLaw
        G n S D outcome :=
    conditionedEventDistribution_nonneg
      (strategyEventLaw (G.repeat n) S)
      (FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D)
      positive outcome
  have outcome_positive :
      0 < repeatedConditionedOutcomeLaw
        G n S D outcome :=
    lt_of_le_of_ne outcome_nonnegative (Ne.symm supported)
  have seed_positive :
      0 < law.weight seed :=
    exactReverseBobConditionalSeedLaw_actual_pos
      (exactRemainingCoordinate_card_pos D remaining) seed
  have atom_positive :
      0 < reweightedSeedPosterior
        law G n S D (seed, outcome) := by
    rw [reweightedSeedPosterior_eq_product]
    exact mul_pos seed_positive outcome_positive
  have actual := reweightedSeedPrefixPriorMarginal_ne_zero_of_positive_atom
    law G n S D positive projection default marker
    (seed, outcome) atom_positive
  exact actual

theorem exactReverseBobActualMarkedEntropy_eq_source
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (default : X)
    (seed : ExactRemainingSeed D)
    (outcome : ExactOutcome X Y A B n)
    (supported :
      repeatedConditionedOutcomeLaw G n S D outcome ≠ 0) :
    exactReverseBobContextMarkedEntropyScore
        G n S D remaining default
        (exactReverseRightSide seed)
        (exactReverseBobContext seed)
        ((exactReverseBobContext seed).sideRank
          ⟨seed.coordinate,
            exactReverseRightSide_coordinate_mem seed⟩)
        outcome =
      finiteRelativeEntropy
        (jointConditional
          (fun atom :
            ((SourceRemainingCoordinate D × Y) ×
              ExactHistoryFlag X Y A B D) × X =>
            exactBobInformationPosterior G n S D
              (atom.1.1, (atom.1.2, atom.2)))
          ((seed.coordinate, outcome.2.1 seed.coordinate.val),
            exactHistoryCode D (seed, outcome)))
        (G.conditionalXGivenY
          (outcome.2.1 seed.coordinate.val)) := by
  have history :
      exactReverseBobMaskedOutcomeContext
        G n S D (exactReverseRightSide seed) default
        ((exactReverseBobContext seed).sideRank
          ⟨seed.coordinate,
            exactReverseRightSide_coordinate_mem seed⟩)
        (exactReverseBobContext seed) outcome =
      exactReverseBobMarkedHistoryContext
        G n S D default seed outcome := by
    simpa only [exactReverseBobContextAt_actual] using
      (exactReverseBobMaskedOutcomeContext_actual
        G n S D default seed outcome)
  have prior_supported :=
    exactReverseBobMarkedPriorMarginal_ne_zero_of_outcome
      G n S D remaining positive default seed outcome supported
  unfold exactReverseBobContextMarkedEntropyScore
  dsimp only
  rw [history]
  rw [exactConditionedReverseBobNextJoint_marked_conditional_eq_sourcePosterior
    G n S D remaining default seed outcome]
  rw [exactReverseBobMarkedPriorConditional_eq_game
    G n S D remaining default seed outcome prior_supported]

theorem exactReverseBobConditionalHistoryIdentification_proved
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (default : X) :
    ExactReverseBobConditionalHistoryIdentification
      G n S D remaining base default := by
  classical
  unfold ExactReverseBobConditionalHistoryIdentification
  rw [exactBobSourceConditionalInformation_eq_joint_atom_sum
    G n S D remaining positive base]
  rw [exactConditionedReverseBobPrefixInformation_eq_sourceMarkedOutcomeScore
    G n S D remaining positive default]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro seed _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases zero :
      repeatedConditionedOutcomeLaw
        G n S D outcome = 0
  · simp only [exactPostselectedJointLaw, zero, mul_zero, zero_mul]
  · rw [exactReverseBobActualMarkedEntropy_eq_source
      G n S D remaining positive default seed outcome zero]
    unfold exactPostselectedJointLaw
    ring

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem exact_source_equation_twenty_three_unconditional
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (defaultY : Y) (defaultX : X) :
    ExactSourceClassicalInformationBound G n S D base := by
  exact exact_source_equation_twenty_three_of_actual_conditioned_reindex
    G n S D remaining positive base defaultY defaultX
    (exactReverseAliceConditionalHistoryIdentification_proved
      G n S D remaining positive base defaultY)
    (exactReverseBobConditionalHistoryIdentification_proved
      G n S D remaining positive base defaultX)

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/--
The exact source support preserving classical sampler construction used in the quantum parallel-
repetition argument.
-/
def ExactSourceSupportPreservingClassicalSampler
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D)
    (kappa gamma : ℝ) : Prop :=
  ∃ denominator : ℕ, 0 < denominator ∧
    ∃ numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ,
      (∀ index, (∑ history, numerator index history) = denominator) ∧
      (∀ index, finiteTotalVariation
        (exactLocalConditionalFamily D base
          (exactLocallySampleableLaw G n S D) index)
        (fun history =>
          (numerator index history : ℝ) / denominator) < gamma) ∧
      (∀ index history,
        0 < exactLocalConditionalFamily D base
            (exactLocallySampleableLaw G n S D)
            index history →
          0 < numerator index history) ∧
      ∃ nonempty : ∀ index,
        (rationalMarked denominator (numerator index)).Nonempty,
        finiteTotalVariation
            (exactLocallySampleableLaw G n S D)
            (exactLocallySampleableJARounded
              G n D denominator numerator) ≤ kappa + gamma ∧
        finiteTotalVariation
            (exactLocallySampleableLaw G n S D)
            (exactLocallySampleableJBRounded
              G n D denominator numerator) ≤ kappa + gamma ∧
        exactLocallySampleablePermutationMismatch
            G n D denominator numerator nonempty ≤
          4 * (kappa + gamma)

theorem exact_source_equation_twenty_seven_support_preserving
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    {kappa gamma : ℝ} (gamma_positive : 0 < gamma)
    (alice : finiteTotalVariation
      (exactLocallySampleableLaw G n S D)
      (exactLocallySampleableJA G n S D base) ≤ kappa)
    (bob : finiteTotalVariation
      (exactLocallySampleableLaw G n S D)
      (exactLocallySampleableJB G n S D base) ≤ kappa) :
    ExactSourceSupportPreservingClassicalSampler
      G n S D base kappa gamma := by
  obtain ⟨denominator, denominator_positive, numerator,
      normalized, approximation, preserves, nonempty, _, _⟩ :=
    exact_exists_support_preserving_local_shared_permutation
      G n S D positive base gamma_positive
  have rounded_alice :
      finiteTotalVariation
          (exactLocallySampleableLaw G n S D)
          (exactLocallySampleableJARounded
            G n D denominator numerator) ≤ kappa + gamma := by
    calc
      finiteTotalVariation
          (exactLocallySampleableLaw G n S D)
          (exactLocallySampleableJARounded
            G n D denominator numerator) ≤
        finiteTotalVariation
          (exactLocallySampleableLaw G n S D)
          (exactLocallySampleableJA G n S D base) +
        finiteTotalVariation
          (exactLocallySampleableJA G n S D base)
          (exactLocallySampleableJARounded
            G n D denominator numerator) :=
          finiteTotalVariation_triangle _ _ _
      _ ≤ kappa + gamma :=
        add_le_add alice
          (exactLocallySampleableJA_rounded_totalVariation_le
            G n S D remaining base denominator numerator approximation)
  have rounded_bob :
      finiteTotalVariation
          (exactLocallySampleableLaw G n S D)
          (exactLocallySampleableJBRounded
            G n D denominator numerator) ≤ kappa + gamma := by
    calc
      finiteTotalVariation
          (exactLocallySampleableLaw G n S D)
          (exactLocallySampleableJBRounded
            G n D denominator numerator) ≤
        finiteTotalVariation
          (exactLocallySampleableLaw G n S D)
          (exactLocallySampleableJB G n S D base) +
        finiteTotalVariation
          (exactLocallySampleableJB G n S D base)
          (exactLocallySampleableJBRounded
            G n D denominator numerator) :=
          finiteTotalVariation_triangle _ _ _
      _ ≤ kappa + gamma :=
        add_le_add bob
          (exactLocallySampleableJB_rounded_totalVariation_le
            G n S D remaining base denominator numerator approximation)
  refine ⟨denominator, denominator_positive, numerator,
    normalized, approximation, preserves, nonempty,
    rounded_alice, rounded_bob, ?_⟩
  calc
    exactLocallySampleablePermutationMismatch
        G n D denominator numerator nonempty ≤
      2 * finiteTotalVariation
        (exactLocallySampleableJARounded
          G n D denominator numerator)
        (exactLocallySampleableJBRounded
          G n D denominator numerator) :=
        exactLocallySampleablePermutationMismatch_le_two_tv
          G n D denominator denominator_positive
          numerator normalized nonempty
    _ ≤ 2 *
        (finiteTotalVariation
          (exactLocallySampleableJARounded
            G n D denominator numerator)
          (exactLocallySampleableLaw G n S D) +
         finiteTotalVariation
          (exactLocallySampleableLaw G n S D)
          (exactLocallySampleableJBRounded
            G n D denominator numerator)) := by
      gcongr
      exact finiteTotalVariation_triangle _ _ _
    _ = 2 *
        (finiteTotalVariation
          (exactLocallySampleableLaw G n S D)
          (exactLocallySampleableJARounded
            G n D denominator numerator) +
         finiteTotalVariation
          (exactLocallySampleableLaw G n S D)
          (exactLocallySampleableJBRounded
            G n D denominator numerator)) := by
      rw [finiteTotalVariation_comm
        (exactLocallySampleableJARounded
          G n D denominator numerator)
        (exactLocallySampleableLaw G n S D)]
    _ ≤ 4 * (kappa + gamma) := by
      linarith

theorem
    exact_source_equation_twenty_seven_support_preserving_of_information
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (information : ExactSourceClassicalInformationBound
      G n S D base)
    {gamma : ℝ} (gamma_positive : 0 < gamma) :
    ExactSourceSupportPreservingClassicalSampler
      G n S D base (exactSourcePinskerRate G n S D) gamma := by
  exact exact_source_equation_twenty_seven_support_preserving
    G n S D remaining positive base gamma_positive
    (exact_source_alice_pinsker_of_classical_information
      G n S D remaining positive base information)
    (exact_source_bob_pinsker_of_classical_information
      G n S D remaining positive base information)

end

end QuantumParallelRepetition

end
