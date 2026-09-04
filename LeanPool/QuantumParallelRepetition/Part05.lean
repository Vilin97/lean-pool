/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.QuantumParallelRepetition.Part04

/-! # Quantum parallel repetition, part 05 -/

noncomputable section

namespace QuantumParallelRepetition

/-- The local matrix norm instance used while elaborating part five. -/
noncomputable local instance matrixComplexContinuousENormPartFive
    {m n : Type*} [Fintype m] [Fintype n] :
    ContinuousENorm (Matrix m n ℂ) :=
  @SeminormedAddGroup.toContinuousENorm (Matrix m n ℂ)
    (Matrix.normedAddCommGroup.toSeminormedAddCommGroup.toSeminormedAddGroup)

open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset

section

open scoped BigOperators


attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The total probability mass of exact fixed bob question. -/
def exactFixedBobQuestionMass
    (G : Game X Y A B) (n : ℕ)
    (fixed : Finset (Fin n))
    (xs : Fin n → X) (known : Fin n → Y) : ℝ :=
  ∑ ys : Fin n → Y,
    if ∀ j : Fin n, j ∈ fixed → ys j = known j then
      (G.repeat n).questionWeight xs ys
    else 0

/-- The total probability mass of exact fixed alice question. -/
def exactFixedAliceQuestionMass
    (G : Game X Y A B) (n : ℕ)
    (fixed : Finset (Fin n))
    (known : Fin n → X) (ys : Fin n → Y) : ℝ :=
  ∑ xs : Fin n → X,
    if ∀ j : Fin n, j ∈ fixed → xs j = known j then
      (G.repeat n).questionWeight xs ys
    else 0

theorem exactFixedBobQuestionMass_eq_product
    (G : Game X Y A B) (n : ℕ)
    (fixed : Finset (Fin n))
    (xs : Fin n → X) (known : Fin n → Y) :
    exactFixedBobQuestionMass G n fixed xs known =
      ∏ j : Fin n,
        if j ∈ fixed then G.questionWeight (xs j) (known j)
        else G.marginalX (xs j) := by
  classical
  unfold exactFixedBobQuestionMass
  simp only [Game.repeat_questionWeight]
  calc
    (∑ ys : Fin n → Y,
      if ∀ j : Fin n, j ∈ fixed → ys j = known j then
        ∏ j : Fin n, G.questionWeight (xs j) (ys j)
      else 0) =
      ∑ ys : Fin n → Y,
        ∏ j : Fin n,
          if j ∈ fixed then
            if ys j = known j then
              G.questionWeight (xs j) (ys j)
            else 0
          else G.questionWeight (xs j) (ys j) := by
            apply Finset.sum_congr rfl
            intro ys _
            calc
              (if ∀ j : Fin n,
                  j ∈ fixed → ys j = known j then
                  ∏ j : Fin n,
                    G.questionWeight (xs j) (ys j)
                else 0) =
                ∏ j : Fin n,
                  if j ∈ fixed → ys j = known j then
                    G.questionWeight (xs j) (ys j)
                  else 0 :=
                  by
                    simp only [Fintype.prod_ite_zero]
                    split <;> simp_all
              _ = _ := by
                apply Finset.prod_congr rfl
                intro j _
                by_cases hj : j ∈ fixed <;>
                  by_cases he : ys j = known j <;>
                    simp [hj, he]
    _ = ∏ j : Fin n,
        ∑ y : Y,
          if j ∈ fixed then
            if y = known j then G.questionWeight (xs j) y else 0
          else G.questionWeight (xs j) y :=
      (Fintype.prod_sum
        (fun (j : Fin n) (y : Y) =>
          if j ∈ fixed then
            if y = known j then G.questionWeight (xs j) y else 0
          else G.questionWeight (xs j) y)).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro j _
      by_cases hj : j ∈ fixed
      · simp only [hj, ↓reduceIte, sum_ite_eq', mem_univ]
      · simp only [hj, ↓reduceIte, Game.marginalX]

theorem exactFixedAliceQuestionMass_eq_product
    (G : Game X Y A B) (n : ℕ)
    (fixed : Finset (Fin n))
    (known : Fin n → X) (ys : Fin n → Y) :
    exactFixedAliceQuestionMass G n fixed known ys =
      ∏ j : Fin n,
        if j ∈ fixed then G.questionWeight (known j) (ys j)
        else G.marginalY (ys j) := by
  classical
  unfold exactFixedAliceQuestionMass
  simp only [Game.repeat_questionWeight]
  calc
    (∑ xs : Fin n → X,
      if ∀ j : Fin n, j ∈ fixed → xs j = known j then
        ∏ j : Fin n, G.questionWeight (xs j) (ys j)
      else 0) =
      ∑ xs : Fin n → X,
        ∏ j : Fin n,
          if j ∈ fixed then
            if xs j = known j then
              G.questionWeight (xs j) (ys j)
            else 0
          else G.questionWeight (xs j) (ys j) := by
            apply Finset.sum_congr rfl
            intro xs _
            calc
              (if ∀ j : Fin n,
                  j ∈ fixed → xs j = known j then
                  ∏ j : Fin n,
                    G.questionWeight (xs j) (ys j)
                else 0) =
                ∏ j : Fin n,
                  if j ∈ fixed → xs j = known j then
                    G.questionWeight (xs j) (ys j)
                  else 0 :=
                  by
                    simp only [Fintype.prod_ite_zero]
                    split <;> simp_all
              _ = _ := by
                apply Finset.prod_congr rfl
                intro j _
                by_cases hj : j ∈ fixed <;>
                  by_cases he : xs j = known j <;>
                    simp [hj, he]
    _ = ∏ j : Fin n,
        ∑ x : X,
          if j ∈ fixed then
            if x = known j then G.questionWeight x (ys j) else 0
          else G.questionWeight x (ys j) :=
      (Fintype.prod_sum
        (fun (j : Fin n) (x : X) =>
          if j ∈ fixed then
            if x = known j then G.questionWeight x (ys j) else 0
          else G.questionWeight x (ys j))).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro j _
      by_cases hj : j ∈ fixed
      · simp only [hj, ↓reduceIte, sum_ite_eq', mem_univ]
      · simp only [hj, ↓reduceIte, Game.marginalY]

theorem exactFixedBobQuestionMass_insert
    (G : Game X Y A B) (n : ℕ)
    (fixed : Finset (Fin n)) (j : Fin n) (fresh : j ∉ fixed)
    (xs : Fin n → X) (known : Fin n → Y) (y : Y) :
    exactFixedBobQuestionMass
        G n (insert j fixed) xs (Function.update known j y) =
      G.conditionalYGivenX (xs j) y *
        exactFixedBobQuestionMass G n fixed xs known := by
  classical
  rw [exactFixedBobQuestionMass_eq_product,
    exactFixedBobQuestionMass_eq_product]
  have tails :
      (∏ k ∈ (Finset.univ : Finset (Fin n)).erase j,
        if k ∈ insert j fixed then
          G.questionWeight (xs k)
            (Function.update known j y k)
        else G.marginalX (xs k)) =
      ∏ k ∈ (Finset.univ : Finset (Fin n)).erase j,
        if k ∈ fixed then
          G.questionWeight (xs k) (known k)
        else G.marginalX (xs k) := by
    apply Finset.prod_congr rfl
    intro k hk
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    simp only [mem_insert, hkj, false_or, ne_eq, not_false_eq_true, Function.update_of_ne]
  rw [← Finset.mul_prod_erase Finset.univ
        (fun k : Fin n =>
          if k ∈ insert j fixed then
            G.questionWeight (xs k)
              (Function.update known j y k)
          else G.marginalX (xs k)) (Finset.mem_univ j),
      ← Finset.mul_prod_erase Finset.univ
        (fun k : Fin n =>
          if k ∈ fixed then
            G.questionWeight (xs k) (known k)
          else G.marginalX (xs k)) (Finset.mem_univ j),
      tails]
  simp only [Finset.mem_insert_self, ↓reduceIte,
    Function.update_self, fresh]
  rw [← G.marginalX_mul_conditionalYGivenX (xs j) y]
  ring

theorem exactFixedAliceQuestionMass_insert
    (G : Game X Y A B) (n : ℕ)
    (fixed : Finset (Fin n)) (j : Fin n) (fresh : j ∉ fixed)
    (known : Fin n → X) (ys : Fin n → Y) (x : X) :
    exactFixedAliceQuestionMass
        G n (insert j fixed) (Function.update known j x) ys =
      G.conditionalXGivenY (ys j) x *
        exactFixedAliceQuestionMass G n fixed known ys := by
  classical
  rw [exactFixedAliceQuestionMass_eq_product,
    exactFixedAliceQuestionMass_eq_product]
  have tails :
      (∏ k ∈ (Finset.univ : Finset (Fin n)).erase j,
        if k ∈ insert j fixed then
          G.questionWeight
            (Function.update known j x k) (ys k)
        else G.marginalY (ys k)) =
      ∏ k ∈ (Finset.univ : Finset (Fin n)).erase j,
        if k ∈ fixed then
          G.questionWeight (known k) (ys k)
        else G.marginalY (ys k) := by
    apply Finset.prod_congr rfl
    intro k hk
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    simp only [mem_insert, hkj, false_or, ne_eq, not_false_eq_true, Function.update_of_ne]
  rw [← Finset.mul_prod_erase Finset.univ
        (fun k : Fin n =>
          if k ∈ insert j fixed then
            G.questionWeight
              (Function.update known j x k) (ys k)
          else G.marginalY (ys k)) (Finset.mem_univ j),
      ← Finset.mul_prod_erase Finset.univ
        (fun k : Fin n =>
          if k ∈ fixed then
            G.questionWeight (known k) (ys k)
          else G.marginalY (ys k)) (Finset.mem_univ j),
      tails]
  simp only [Finset.mem_insert_self, ↓reduceIte,
    Function.update_self, fresh]
  rw [← G.marginalY_mul_conditionalXGivenY x (ys j)]
  ring

end

section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- The exact reverse left side construction used in the quantum parallel-repetition argument. -/
def exactReverseLeftSide
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) : Finset M :=
  insert seed.coordinate
    (exactLeft seed.coordinate seed.partition)

/-- The exact reverse right side construction used in the quantum parallel-repetition argument. -/
def exactReverseRightSide
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) : Finset M :=
  insert seed.coordinate
    (exactRight seed.coordinate seed.partition)

@[simp] theorem exactReverseLeftSide_coordinate_mem
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    seed.coordinate ∈ exactReverseLeftSide seed := by
  simp only [exactReverseLeftSide, mem_insert, true_or]

@[simp] theorem exactReverseRightSide_coordinate_mem
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    seed.coordinate ∈ exactReverseRightSide seed := by
  simp only [exactReverseRightSide, mem_insert, true_or]

theorem exactReverseLeftSide_card
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    (exactReverseLeftSide seed).card =
      (exactLeft seed.coordinate seed.partition).card + 1 := by
  simp only [exactReverseLeftSide, exactLeft_coordinate_not_mem, not_false_eq_true,
    card_insert_of_notMem, Nat.add_comm]

theorem exactReverseRightSide_card
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    (exactReverseRightSide seed).card =
      (exactRight seed.coordinate seed.partition).card + 1 := by
  simp only [exactReverseRightSide, exactRight_coordinate_not_mem, not_false_eq_true,
    card_insert_of_notMem, Nat.add_comm]

theorem exactReverseLeftSide_markedWeight
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    reverseMarkedPartitionWeight
        (exactReverseLeftSide seed) seed.coordinate =
      forwardMarkedPartitionWeight M :=
  reverseMarkedPartitionWeight_eq_forward
    (exactReverseLeftSide_coordinate_mem seed)

theorem exactReverseRightSide_markedWeight
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    reverseMarkedPartitionWeight
        (exactReverseRightSide seed) seed.coordinate =
      forwardMarkedPartitionWeight M :=
  reverseMarkedPartitionWeight_eq_forward
    (exactReverseRightSide_coordinate_mem seed)

theorem exactRemainingReverse_relativeEntropy_budget
    {n : ℕ} (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (increment :
      (s : Finset (SourceRemainingCoordinate D)) → Fin s.card → ℝ)
    {cost : ℝ} (nonnegative_cost : 0 ≤ cost)
    (budget : ∀ s : Finset (SourceRemainingCoordinate D),
      (∑ k : Fin s.card, increment s k) ≤ cost) :
    (∑ s : Finset (SourceRemainingCoordinate D),
      reversePartitionWeight s *
        ((∑ k : Fin s.card, increment s k) /
          (s.card : ℝ))) ≤
      2 * cost / ((Finset.univ \ D).card : ℝ) := by
  have hcard : 0 < Fintype.card (SourceRemainingCoordinate D) := by
    simpa only [Fintype.card_coe, card_pos] using remaining
  simpa only [ge_iff_le, Fintype.card_coe] using
    (reversePartition_relativeEntropy_budget
      hcard increment nonnegative_cost budget)

end

section

open scoped BigOperators


open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

private def exactReverseLeftSeedWeight
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) : ℝ :=
  (1 / (2 : ℝ)) *
    reverseMarkedPartitionWeight
      (exactReverseLeftSide seed) seed.coordinate *
    (1 / (Fintype.card
      (Equiv.Perm
        {j : M // j ∈ exactReverseLeftSide seed}) : ℝ)) *
    (1 / (Fintype.card
      (Equiv.Perm
        {j : M // j ∈
          exactRight seed.coordinate seed.partition}) : ℝ)) *
    (1 /
      ((exactRight
        seed.coordinate seed.partition).card + 1 : ℝ))

private def exactReverseRightSeedWeight
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) : ℝ :=
  (1 / (2 : ℝ)) *
    reverseMarkedPartitionWeight
      (exactReverseRightSide seed) seed.coordinate *
    (1 / (Fintype.card
      (Equiv.Perm
        {j : M // j ∈ exactReverseRightSide seed}) : ℝ)) *
    (1 / (Fintype.card
      (Equiv.Perm
        {j : M // j ∈
          exactLeft seed.coordinate seed.partition}) : ℝ)) *
    (1 /
      ((exactLeft
        seed.coordinate seed.partition).card + 1 : ℝ))

theorem exactReverseLeftPermutation_card
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    Fintype.card
        (Equiv.Perm
          {j : M // j ∈ exactReverseLeftSide seed}) =
      Fintype.card
          (Equiv.Perm
            {j : M // j ∈
              exactLeft seed.coordinate seed.partition}) *
        ((exactLeft
          seed.coordinate seed.partition).card + 1) := by
  rw [Fintype.card_perm, Fintype.card_perm]
  simp only [Fintype.card_coe, exactReverseLeftSide_card, Nat.factorial_succ, Nat.mul_comm]

theorem exactReverseRightPermutation_card
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    Fintype.card
        (Equiv.Perm
          {j : M // j ∈ exactReverseRightSide seed}) =
      Fintype.card
          (Equiv.Perm
            {j : M // j ∈
              exactRight seed.coordinate seed.partition}) *
        ((exactRight
          seed.coordinate seed.partition).card + 1) := by
  rw [Fintype.card_perm, Fintype.card_perm]
  simp only [Fintype.card_coe, exactReverseRightSide_card, Nat.factorial_succ, Nat.mul_comm]

theorem exactReverseLeftSeedWeight_eq_forward
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    exactReverseLeftSeedWeight seed =
      exactSeedWeight seed := by
  rw [exactReverseLeftSeedWeight,
    exactReverseLeftSide_markedWeight,
    exactReverseLeftPermutation_card]
  simp only [exactSeedWeight,
    forwardMarkedPartitionWeight,
    fairPartitionWeight,
    Fintype.card_fun, Fintype.card_bool,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Nat.cast_pow]
  field_simp
  ring

theorem exactReverseRightSeedWeight_eq_forward
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    exactReverseRightSeedWeight seed =
      exactSeedWeight seed := by
  rw [exactReverseRightSeedWeight,
    exactReverseRightSide_markedWeight,
    exactReverseRightPermutation_card]
  simp only [exactSeedWeight,
    forwardMarkedPartitionWeight,
    fairPartitionWeight,
    Fintype.card_fun, Fintype.card_bool,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Nat.cast_pow]
  field_simp
  ring

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The exact history accepted construction used in the quantum parallel-repetition argument. -/
def exactHistoryAccepted
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) : Prop :=
  ∀ j : {j : Fin n // j ∈ D},
    G.predicate
      (r.history.aliceConditioned j)
      (r.history.bobConditioned j)
      (r.aliceAnswer j)
      (r.bobAnswer j) = true

theorem exactHistoryCode_accepted_iff
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (q : ExactJointOutcome X Y A B D) :
    exactHistoryAccepted G n D
        (exactHistoryCode D q) ↔
      q.2 ∈ FiniteEventLaw.winEvent
        (repeatedCoordinateWin G n) D := by
  classical
  unfold exactHistoryAccepted
  simp only [exactHistoryCode, exactRevealCode]
  rw [FiniteEventLaw.mem_winEvent_iff]
  constructor
  · intro h j hj
    simpa only [repeatedCoordinateWin] using h ⟨j, hj⟩
  · intro h j
    have hw := h j.val j.property
    simpa only [repeatedCoordinateWin] using hw

theorem exactLocallySampleableLaw_zero_of_not_accepted
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (i : SourceRemainingCoordinate D) (x : X) (y : Y)
    (r : ExactHistoryFlag X Y A B D)
    (not_accepted : ¬ exactHistoryAccepted G n D r) :
    exactLocallySampleableLaw G n S D (i, x, y, r) = 0 := by
  classical
  unfold exactLocallySampleableLaw
    exactSourcePushforward
    groupedMass
  apply Finset.sum_eq_zero
  intro q hq
  have hcode :
      exactLocallySampleableCode D q = (i, x, y, r) := by
    exact ((@Finset.mem_filter
      (ExactJointOutcome X Y A B D)
      (fun a => exactLocallySampleableCode D a = (i, x, y, r))
      (fun _ => Classical.propDecidable _)
      Finset.univ q).mp hq).2
  have hhistory : exactHistoryCode D q = r :=
    congrArg
      (fun t : ExactLocallySampleableTuple X Y A B D =>
        t.2.2.2) hcode
  have hnot :
      q.2 ∉ FiniteEventLaw.winEvent
        (repeatedCoordinateWin G n) D := by
    intro hw
    apply not_accepted
    rw [← hhistory]
    exact (exactHistoryCode_accepted_iff
      G n D q).mpr hw
  simp only [exactPostselectedJointLaw, repeatedConditionedOutcomeLaw,
    conditionedEventDistribution, hnot, ↓reduceIte, mul_zero]

end

section

open scoped BigOperators Kronecker ComplexOrder MatrixOrder


attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/--
The type used to represent exact global history local index in the exact sampling construction.
-/
abbrev ExactGlobalHistoryLocalIndex
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :=
  PUnit.{1} ⊕
    (Σ r : ExactHistoryFlag X Y A B D,
      ExactPaddedLocalIndex G n S D r)

/-- The state vector representing exact global history. -/
def exactGlobalHistoryVector
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (z : EuclideanSpace ℂ
      (ExactPaddedLocalIndex G n S D r ×
        ExactPaddedLocalIndex G n S D r)) :
    EuclideanSpace ℂ
      (ExactGlobalHistoryLocalIndex G n S D ×
        ExactGlobalHistoryLocalIndex G n S D) :=
  taggedTensorVector r z

theorem exactGlobalHistoryVector_norm
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (z : EuclideanSpace ℂ
      (ExactPaddedLocalIndex G n S D r ×
        ExactPaddedLocalIndex G n S D r)) :
    ‖exactGlobalHistoryVector G n S D r z‖ = ‖z‖ :=
  taggedTensorVector_norm r z

theorem exactGlobalHistoryVector_sub
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (u v : EuclideanSpace ℂ
      (ExactPaddedLocalIndex G n S D r ×
        ExactPaddedLocalIndex G n S D r)) :
    exactGlobalHistoryVector G n S D r (u - v) =
      exactGlobalHistoryVector G n S D r u -
        exactGlobalHistoryVector G n S D r v :=
  taggedTensorVector_sub r u v

theorem exactGlobalHistoryLocalIndex_card_pos
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :
    0 < Fintype.card (ExactGlobalHistoryLocalIndex G n S D) := by
  exact Fintype.card_pos_iff.mpr ⟨Sum.inl PUnit.unit⟩

/--
The exact global history fin reindex construction used in the quantum parallel-repetition
argument.
-/
def exactGlobalHistoryFinReindex
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :
    EuclideanSpace ℂ
      (ExactGlobalHistoryLocalIndex G n S D ×
        ExactGlobalHistoryLocalIndex G n S D) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ
        (Fin (Fintype.card
          (ExactGlobalHistoryLocalIndex G n S D)) ×
         Fin (Fintype.card
          (ExactGlobalHistoryLocalIndex G n S D))) := by
  classical
  exact LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (Equiv.prodCongr
      (Fintype.equivFin (ExactGlobalHistoryLocalIndex G n S D))
      (Fintype.equivFin (ExactGlobalHistoryLocalIndex G n S D)))

/--
The exact global history fin gamma construction used in the quantum parallel-repetition
argument.
-/
def exactGlobalHistoryFinGamma
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) (x : X) :
    BipartiteUnitVector
      (Fintype.card (ExactGlobalHistoryLocalIndex G n S D)) :=
  ⟨exactGlobalHistoryFinReindex G n S D
      (exactGlobalHistoryVector G n S D r
        (exactGamma G n S D r x)), by
      rw [LinearIsometryEquiv.norm_map,
        exactGlobalHistoryVector_norm]
      exact normalizeOrDefault_norm _ _
        (exactPaddedDefault_norm G n S D r)⟩

/--
The exact global history fin phi construction used in the quantum parallel-repetition argument.
-/
def exactGlobalHistoryFinPhi
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) (y : Y) :
    BipartiteUnitVector
      (Fintype.card (ExactGlobalHistoryLocalIndex G n S D)) :=
  ⟨exactGlobalHistoryFinReindex G n S D
      (exactGlobalHistoryVector G n S D r
        (exactPhi G n S D r y)), by
      rw [LinearIsometryEquiv.norm_map,
        exactGlobalHistoryVector_norm]
      exact normalizeOrDefault_norm _ _
        (exactPaddedDefault_norm G n S D r)⟩

/--
The exact global history fin psi construction used in the quantum parallel-repetition argument.
-/
def exactGlobalHistoryFinPsi
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) :
    BipartiteUnitVector
      (Fintype.card (ExactGlobalHistoryLocalIndex G n S D)) :=
  ⟨exactGlobalHistoryFinReindex G n S D
      (exactGlobalHistoryVector G n S D r
        (exactPsi G n S D r x y)), by
      rw [LinearIsometryEquiv.norm_map,
        exactGlobalHistoryVector_norm]
      exact normalizeOrDefault_norm _ _
        (exactPaddedDefault_norm G n S D r)⟩

theorem exactGlobalHistoryFinGamma_sub_Psi_norm
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) :
    ‖(exactGlobalHistoryFinGamma G n S D r x).val -
      (exactGlobalHistoryFinPsi G n S D r x y).val‖ =
      ‖exactGamma G n S D r x -
        exactPsi G n S D r x y‖ := by
  change
    ‖exactGlobalHistoryFinReindex G n S D
        (exactGlobalHistoryVector G n S D r
          (exactGamma G n S D r x)) -
      exactGlobalHistoryFinReindex G n S D
        (exactGlobalHistoryVector G n S D r
          (exactPsi G n S D r x y))‖ = _
  rw [← map_sub, ← exactGlobalHistoryVector_sub,
    LinearIsometryEquiv.norm_map,
    exactGlobalHistoryVector_norm]

end

section

open scoped BigOperators


attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The type used to represent exact source global state in the exact sampling construction. -/
abbrev ExactSourceGlobalState
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :=
  EuclideanSpace ℂ
    (Fin (Fintype.card (ExactGlobalHistoryLocalIndex G n S D)) ×
      Fin (Fintype.card (ExactGlobalHistoryLocalIndex G n S D)))

/-- The exact source tuple psi construction used in the quantum parallel-repetition argument. -/
def exactSourceTuplePsi
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (t : ExactLocallySampleableTuple X Y A B D) :
    ExactSourceGlobalState G n S D :=
  (exactGlobalHistoryFinPsi
    G n S D t.2.2.2 t.2.1 t.2.2.1).val

/-- The exact source tuple gamma construction used in the quantum parallel-repetition argument. -/
def exactSourceTupleGamma
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (t : ExactLocallySampleableTuple X Y A B D) :
    ExactSourceGlobalState G n S D :=
  (exactGlobalHistoryFinGamma
    G n S D t.2.2.2 t.2.1).val

/-- The exact source tuple phi construction used in the quantum parallel-repetition argument. -/
def exactSourceTuplePhi
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (t : ExactLocallySampleableTuple X Y A B D) :
    ExactSourceGlobalState G n S D :=
  (exactGlobalHistoryFinPhi
    G n S D t.2.2.2 t.2.2.1).val

theorem exactSourceTuplePsi_norm
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (t : ExactLocallySampleableTuple X Y A B D) :
    ‖exactSourceTuplePsi G n S D t‖ = 1 :=
  (exactGlobalHistoryFinPsi
    G n S D t.2.2.2 t.2.1 t.2.2.1).property

theorem exactSourceTupleGamma_norm
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (t : ExactLocallySampleableTuple X Y A B D) :
    ‖exactSourceTupleGamma G n S D t‖ = 1 :=
  (exactGlobalHistoryFinGamma
    G n S D t.2.2.2 t.2.1).property

/-- The numerical bound for exact source state distance. -/
def ExactSourceStateDistanceBound
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (η : ℝ) : Prop :=
  (∑ t : ExactLocallySampleableTuple X Y A B D,
    exactLocallySampleableLaw G n S D t *
      ‖exactSourceTupleGamma G n S D t -
        exactSourceTuplePsi G n S D t‖ ^ 2) ≤ 8 * η ∧
  (∑ t : ExactLocallySampleableTuple X Y A B D,
    exactLocallySampleableLaw G n S D t *
      ‖exactSourceTuplePsi G n S D t -
        exactSourceTuplePhi G n S D t‖ ^ 2) ≤ 8 * η

theorem exactPsiPhi_BornWeighted_normalized_distance
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) :
    ‖exactUnnormalizedPsi G n S D r x y‖ ^ 2 *
      ‖exactPsi G n S D r x y -
        exactPhi G n S D r y‖ ^ 2 ≤
      4 * ‖exactUnnormalizedPsi G n S D r x y -
        exactUnnormalizedPhi G n S D r y‖ ^ 2 := by
  let fallback := exactPaddedDefault G n S D r
  let u := exactUnnormalizedPsi G n S D r x y
  let v := exactUnnormalizedPhi G n S D r y
  have h := bornWeighted_normalized_distance fallback
    (exactPaddedVector G n S D r u)
    (exactPaddedVector G n S D r v)
    (exactPaddedDefault_norm G n S D r)
  rw [exactPaddedVector_norm,
    ← exactPaddedVector_sub,
    exactPaddedVector_norm] at h
  exact h

theorem exactGammaPsi_BornWeighted_normalized_distance
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) :
    ‖exactUnnormalizedPsi G n S D r x y‖ ^ 2 *
      ‖exactGamma G n S D r x -
        exactPsi G n S D r x y‖ ^ 2 ≤
      4 * ‖exactUnnormalizedGamma G n S D r x -
        exactUnnormalizedPsi G n S D r x y‖ ^ 2 := by
  let fallback := exactPaddedDefault G n S D r
  let u := exactUnnormalizedPsi G n S D r x y
  let v := exactUnnormalizedGamma G n S D r x
  have h := bornWeighted_normalized_distance fallback
    (exactPaddedVector G n S D r u)
    (exactPaddedVector G n S D r v)
    (exactPaddedDefault_norm G n S D r)
  rw [exactPaddedVector_norm,
    ← exactPaddedVector_sub,
    exactPaddedVector_norm] at h
  have hforward :
      ‖exactUnnormalizedPsi G n S D r x y‖ ^ 2 *
        ‖exactPsi G n S D r x y -
          exactGamma G n S D r x‖ ^ 2 ≤
        4 * ‖exactUnnormalizedPsi G n S D r x y -
          exactUnnormalizedGamma G n S D r x‖ ^ 2 := by
    exact h
  calc
    ‖exactUnnormalizedPsi G n S D r x y‖ ^ 2 *
        ‖exactGamma G n S D r x -
          exactPsi G n S D r x y‖ ^ 2 =
      ‖exactUnnormalizedPsi G n S D r x y‖ ^ 2 *
        ‖exactPsi G n S D r x y -
          exactGamma G n S D r x‖ ^ 2 := by
        rw [norm_sub_rev]
    _ ≤ 4 * ‖exactUnnormalizedPsi G n S D r x y -
          exactUnnormalizedGamma G n S D r x‖ ^ 2 := hforward
    _ = 4 * ‖exactUnnormalizedGamma G n S D r x -
          exactUnnormalizedPsi G n S D r x y‖ ^ 2 := by
        rw [norm_sub_rev]

theorem exactSourceEquationTwentyOne_of_fifteen
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (η : ℝ)
    (distance : ExactSourceStateDistanceBound G n S D η) :
    (∑ t : ExactLocallySampleableTuple X Y A B D,
      exactLocallySampleableLaw G n S D t *
        ‖exactSourceTupleGamma G n S D t -
          exactSourceTuplePhi G n S D t‖ ^ 2) ≤ 32 * η := by
  exact source_equation_twenty_one
    (exactLocallySampleableLaw G n S D)
    (exactLocallySampleableLaw_nonneg G n S D positive)
    (exactSourceTupleGamma G n S D)
    (exactSourceTuplePsi G n S D)
    (exactSourceTuplePhi G n S D)
    η distance.1 distance.2

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace


attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

private def exactFairAliceQuestionEntropyIncrement
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) (y : Y) : ℝ :=
  bornTracePairing S.state.matrix
    ((∑ x : X, G.conditionalXGivenY y x •
      cfc (fun z : ℝ => z * Real.log z)
        (exactAliceQuestionFilter
          G n S D r.seed r.history r.aliceAnswer x)) -
      cfc (fun z : ℝ => z * Real.log z)
        (exactAliceMeanFilter
          G n S D r.seed r.history r.aliceAnswer y))
    (exactBobQuestionFilter
      G n S D r.seed r.history r.bobAnswer y)

private def exactFairBobQuestionEntropyIncrement
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) (x : X) : ℝ :=
  bornTracePairing S.state.matrix
    (exactAliceQuestionFilter
      G n S D r.seed r.history r.aliceAnswer x)
    ((∑ y : Y, G.conditionalYGivenX x y •
      cfc (fun z : ℝ => z * Real.log z)
        (exactBobQuestionFilter
          G n S D r.seed r.history r.bobAnswer y)) -
      cfc (fun z : ℝ => z * Real.log z)
        (exactBobMeanFilter
          G n S D r.seed r.history r.bobAnswer x))

theorem exactFairAlice_conditional_variation_le
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) (y : Y)
    (hy : 0 < G.marginalY y) :
    (∑ x : X, G.conditionalXGivenY y x *
      ‖exactUnnormalizedPsi G n S D r x y -
        exactUnnormalizedPhi G n S D r y‖ ^ 2) ≤
      exactFairAliceQuestionEntropyIncrement G n S D r y := by
  let F := exactAlicePurificationFamily
    G n S D r.seed r.history r.aliceAnswer
  let hF := exactAlicePurificationFamily_posSemidef
    G n S D r.seed r.history r.aliceAnswer
  have hmean :
      (∑ x : X, G.conditionalXGivenY y x • F (.inl x)) =
        F (.inr y) := by
    exact rfl
  have h := commonFinitePurification_weighted_left_variation_le
    S (G.conditionalXGivenY y) F 0 hF Matrix.PosSemidef.zero
    (fun x : X => Sum.inl x) (Sum.inr y)
    (fun x => G.conditionalXGivenY_nonneg y x)
    (G.conditionalXGivenY_sum y hy) hmean
    (exactBobPurificationMatrix
      G n S D r.seed r.history r.bobAnswer (.inl y))
  rw [exactBobPurificationMatrix_gram] at h
  exact h

theorem exactFairBob_conditional_variation_le
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) (x : X)
    (hx : 0 < G.marginalX x) :
    (∑ y : Y, G.conditionalYGivenX x y *
      ‖exactUnnormalizedPsi G n S D r x y -
        exactUnnormalizedGamma G n S D r x‖ ^ 2) ≤
      exactFairBobQuestionEntropyIncrement G n S D r x := by
  let F := exactBobPurificationFamily
    G n S D r.seed r.history r.bobAnswer
  let hF := exactBobPurificationFamily_posSemidef
    G n S D r.seed r.history r.bobAnswer
  have hmean :
      (∑ y : Y, G.conditionalYGivenX x y • F (.inl y)) =
        F (.inr x) := by
    exact rfl
  have h := commonFinitePurification_weighted_right_variation_le
    S (G.conditionalYGivenX x) F 0 hF Matrix.PosSemidef.zero
    (fun y : Y => Sum.inl y) (Sum.inr x)
    (fun y => G.conditionalYGivenX_nonneg x y)
    (G.conditionalYGivenX_sum x hx) hmean
    (exactAlicePurificationMatrix
      G n S D r.seed r.history r.aliceAnswer (.inl x))
  rw [exactAlicePurificationMatrix_gram] at h
  exact h

private def exactFairAliceHistoryVariation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) : ℝ :=
  ∑ y : Y, ∑ x : X, G.questionWeight x y *
    ‖exactUnnormalizedPsi G n S D r x y -
      exactUnnormalizedPhi G n S D r y‖ ^ 2

private def exactFairBobHistoryVariation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) : ℝ :=
  ∑ x : X, ∑ y : Y, G.questionWeight x y *
    ‖exactUnnormalizedPsi G n S D r x y -
      exactUnnormalizedGamma G n S D r x‖ ^ 2

/-- The information increment contributed by exact fair alice history entropy. -/
def exactFairAliceHistoryEntropyIncrement
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) : ℝ :=
  ∑ y : Y, G.marginalY y *
    exactFairAliceQuestionEntropyIncrement G n S D r y

/-- The information increment contributed by exact fair bob history entropy. -/
def exactFairBobHistoryEntropyIncrement
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) : ℝ :=
  ∑ x : X, G.marginalX x *
    exactFairBobQuestionEntropyIncrement G n S D r x

theorem exactFairAliceHistoryVariation_le_entropy
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :
    exactFairAliceHistoryVariation G n S D r ≤
      exactFairAliceHistoryEntropyIncrement G n S D r := by
  unfold exactFairAliceHistoryVariation
    exactFairAliceHistoryEntropyIncrement
  apply Finset.sum_le_sum
  intro y _
  by_cases hy : G.marginalY y = 0
  · have hzero (x : X) : G.questionWeight x y = 0 := by
      have hle := G.questionWeight_le_marginalY x y
      have hnonneg := G.weight_nonneg x y
      rw [hy] at hle
      linarith
    simp only [hzero, zero_mul, sum_const_zero, hy, Std.le_refl]
  · have hypos : 0 < G.marginalY y :=
      lt_of_le_of_ne (G.marginalY_nonneg y) (Ne.symm hy)
    have hlocal := exactFairAlice_conditional_variation_le
      G n S D r y hypos
    calc
      (∑ x : X, G.questionWeight x y *
        ‖exactUnnormalizedPsi G n S D r x y -
          exactUnnormalizedPhi G n S D r y‖ ^ 2) =
        G.marginalY y *
          (∑ x : X, G.conditionalXGivenY y x *
            ‖exactUnnormalizedPsi G n S D r x y -
              exactUnnormalizedPhi G n S D r y‖ ^ 2) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro x _
                rw [← G.marginalY_mul_conditionalXGivenY x y]
                ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlocal (G.marginalY_nonneg y)

theorem exactFairBobHistoryVariation_le_entropy
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :
    exactFairBobHistoryVariation G n S D r ≤
      exactFairBobHistoryEntropyIncrement G n S D r := by
  unfold exactFairBobHistoryVariation
    exactFairBobHistoryEntropyIncrement
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : G.marginalX x = 0
  · have hzero (y : Y) : G.questionWeight x y = 0 := by
      have hle := G.questionWeight_le_marginalX x y
      have hnonneg := G.weight_nonneg x y
      rw [hx] at hle
      linarith
    simp only [hzero, zero_mul, sum_const_zero, hx, Std.le_refl]
  · have hxpos : 0 < G.marginalX x :=
      lt_of_le_of_ne (G.marginalX_nonneg x) (Ne.symm hx)
    have hlocal := exactFairBob_conditional_variation_le
      G n S D r x hxpos
    calc
      (∑ y : Y, G.questionWeight x y *
        ‖exactUnnormalizedPsi G n S D r x y -
          exactUnnormalizedGamma G n S D r x‖ ^ 2) =
        G.marginalX x *
          (∑ y : Y, G.conditionalYGivenX x y *
            ‖exactUnnormalizedPsi G n S D r x y -
              exactUnnormalizedGamma G n S D r x‖ ^ 2) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro y _
                rw [← G.marginalX_mul_conditionalYGivenX x y]
                ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlocal (G.marginalX_nonneg x)

/-- The probability weight for exact fair history prior. -/
def exactFairHistoryPriorWeight
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) : ℝ :=
  exactSeedWeight r.seed *
    exactRevealMass G n D r.seed r.history

theorem exactFairHistoryPriorWeight_nonneg
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :
    0 ≤ exactFairHistoryPriorWeight G n D r := by
  exact mul_nonneg (exactSeedWeight_nonneg r.seed)
    (exactRevealMass_nonneg G n D r.seed r.history)

theorem exactAcceptedFairAliceVariation_le_entropy
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :
    (∑ r : ExactHistoryFlag X Y A B D,
      if exactHistoryAccepted G n D r then
        exactFairHistoryPriorWeight G n D r *
          exactFairAliceHistoryVariation G n S D r
      else 0) ≤
    (∑ r : ExactHistoryFlag X Y A B D,
      if exactHistoryAccepted G n D r then
        exactFairHistoryPriorWeight G n D r *
          exactFairAliceHistoryEntropyIncrement G n S D r
      else 0) := by
  apply Finset.sum_le_sum
  intro r _
  split
  · exact mul_le_mul_of_nonneg_left
      (exactFairAliceHistoryVariation_le_entropy G n S D r)
      (exactFairHistoryPriorWeight_nonneg G n D r)
  · exact le_rfl

theorem exactAcceptedFairBobVariation_le_entropy
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :
    (∑ r : ExactHistoryFlag X Y A B D,
      if exactHistoryAccepted G n D r then
        exactFairHistoryPriorWeight G n D r *
          exactFairBobHistoryVariation G n S D r
      else 0) ≤
    (∑ r : ExactHistoryFlag X Y A B D,
      if exactHistoryAccepted G n D r then
        exactFairHistoryPriorWeight G n D r *
          exactFairBobHistoryEntropyIncrement G n S D r
      else 0) := by
  apply Finset.sum_le_sum
  intro r _
  split
  · exact mul_le_mul_of_nonneg_left
      (exactFairBobHistoryVariation_le_entropy G n S D r)
      (exactFairHistoryPriorWeight_nonneg G n D r)
  · exact le_rfl

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The error rate associated with exact source classical information. -/
def exactSourceClassicalInformationRate
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) : ℝ :=
  (3 * postselectionLogCost G n S D +
      2 * answerLogCost (A := A) (B := B) D) /
    ((Finset.univ \ D).card : ℝ)

/-- The numerical bound for exact source classical information. -/
def ExactSourceClassicalInformationBound
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D) : Prop :=
  finiteRelativeEntropy
      (exactLocallySampleableLaw G n S D)
      (exactLocallySampleableJA G n S D base) ≤
        exactSourceClassicalInformationRate G n S D ∧
    finiteRelativeEntropy
      (exactLocallySampleableLaw G n S D)
      (exactLocallySampleableJB G n S D base) ≤
        exactSourceClassicalInformationRate G n S D

theorem exactFiniteRelativeEntropy_equiv
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (p q : ι → ℝ) :
    finiteRelativeEntropy
        (fun k : κ => p (e.symm k))
        (fun k : κ => q (e.symm k)) =
      finiteRelativeEntropy p q := by
  unfold finiteRelativeEntropy
  exact e.symm.sum_comp
    (fun i => q i * InformationTheory.klFun (p i / q i))

/-- The finite equivalence encoding exact alice information. -/
def exactAliceInformationEquiv
    {n : ℕ} (D : Finset (Fin n)) :
    ExactLocallySampleableTuple X Y A B D ≃
      (SourceRemainingCoordinate D × X) ×
        (ExactHistoryFlag X Y A B D × Y) where
  toFun t := ((t.1, t.2.1), (t.2.2.2, t.2.2.1))
  invFun t := (t.1.1, t.1.2, t.2.2, t.2.1)
  left_inv t := by
    rcases t with ⟨i, x, y, r⟩
    rfl
  right_inv t := by
    rcases t with ⟨⟨i, x⟩, ⟨r, y⟩⟩
    rfl

/-- The finite equivalence encoding exact bob information. -/
def exactBobInformationEquiv
    {n : ℕ} (D : Finset (Fin n)) :
    ExactLocallySampleableTuple X Y A B D ≃
      (SourceRemainingCoordinate D × Y) ×
        (ExactHistoryFlag X Y A B D × X) where
  toFun t := ((t.1, t.2.2.1), (t.2.2.2, t.2.1))
  invFun t := (t.1.1, t.2.2, t.1.2, t.2.1)
  left_inv t := by
    rcases t with ⟨i, x, y, r⟩
    rfl
  right_inv t := by
    rcases t with ⟨⟨i, y⟩, ⟨r, x⟩⟩
    rfl

/--
The exact alice information posterior construction used in the quantum parallel-repetition
argument.
-/
def exactAliceInformationPosterior
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :
    (SourceRemainingCoordinate D × X) ×
      (ExactHistoryFlag X Y A B D × Y) → ℝ :=
  fun t => exactLocallySampleableLaw G n S D
    ((exactAliceInformationEquiv
      (X := X) (Y := Y) (A := A) (B := B) D).symm t)

/--
The exact alice information reference construction used in the quantum parallel-repetition
argument.
-/
def exactAliceInformationReference
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D) :
    (SourceRemainingCoordinate D × X) ×
      (ExactHistoryFlag X Y A B D × Y) → ℝ :=
  fun t => exactLocallySampleableJA G n S D base
    ((exactAliceInformationEquiv
      (X := X) (Y := Y) (A := A) (B := B) D).symm t)

/--
The exact bob information posterior construction used in the quantum parallel-repetition
argument.
-/
def exactBobInformationPosterior
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :
    (SourceRemainingCoordinate D × Y) ×
      (ExactHistoryFlag X Y A B D × X) → ℝ :=
  fun t => exactLocallySampleableLaw G n S D
    ((exactBobInformationEquiv
      (X := X) (Y := Y) (A := A) (B := B) D).symm t)

/--
The exact bob information reference construction used in the quantum parallel-repetition
argument.
-/
def exactBobInformationReference
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D) :
    (SourceRemainingCoordinate D × Y) ×
      (ExactHistoryFlag X Y A B D × X) → ℝ :=
  fun t => exactLocallySampleableJB G n S D base
    ((exactBobInformationEquiv
      (X := X) (Y := Y) (A := A) (B := B) D).symm t)

theorem exact_source_equation_twenty_four_alice
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D) :
    finiteRelativeEntropy
        (exactLocallySampleableLaw G n S D)
        (exactLocallySampleableJA G n S D base) =
      finiteRelativeEntropy
          (jointFirstMarginal
            (exactAliceInformationPosterior G n S D))
          (jointFirstMarginal
            (exactAliceInformationReference G n S D base)) +
        ∑ ix : SourceRemainingCoordinate D × X,
          jointFirstMarginal
              (exactAliceInformationPosterior G n S D) ix *
            finiteRelativeEntropy
              (jointConditional
                (exactAliceInformationPosterior G n S D) ix)
              (jointConditional
                (exactAliceInformationReference G n S D base) ix) := by
  let e := exactAliceInformationEquiv
    (X := X) (Y := Y) (A := A) (B := B) D
  let p := exactAliceInformationPosterior G n S D
  let q := exactAliceInformationReference G n S D base
  have hp : ∀ t, 0 ≤ p t := by
    intro t
    exact exactLocallySampleableLaw_nonneg
      G n S D positive (e.symm t)
  have hq : ∀ t, 0 ≤ q t := by
    intro t
    exact exactLocallySampleableJA_nonneg
      G n S D positive base (e.symm t)
  have hac : ∀ t, q t = 0 → p t = 0 := by
    intro t ht
    exact exactLocallySampleableLaw_absolute_continuous_JA
      G n S D remaining positive base (e.symm t) ht
  have hpnorm : (∑ t, p t) = 1 := by
    change (∑ t, exactLocallySampleableLaw
      G n S D (e.symm t)) = 1
    rw [e.symm.sum_comp]
    exact exactLocallySampleableLaw_sum
      G n S D remaining positive
  have hqnorm : (∑ t, q t) = 1 := by
    change (∑ t, exactLocallySampleableJA
      G n S D base (e.symm t)) = 1
    rw [e.symm.sum_comp]
    exact exactLocallySampleableJA_sum
      G n S D remaining base
  calc
    finiteRelativeEntropy
        (exactLocallySampleableLaw G n S D)
        (exactLocallySampleableJA G n S D base) =
      finiteRelativeEntropy p q := by
        exact (exactFiniteRelativeEntropy_equiv e
          (exactLocallySampleableLaw G n S D)
          (exactLocallySampleableJA G n S D base)).symm
    _ = _ := finite_relative_entropy_joint_chain_rule
      p q hp hq hac hpnorm hqnorm

theorem exact_source_equation_twenty_four_bob
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D) :
    finiteRelativeEntropy
        (exactLocallySampleableLaw G n S D)
        (exactLocallySampleableJB G n S D base) =
      finiteRelativeEntropy
          (jointFirstMarginal
            (exactBobInformationPosterior G n S D))
          (jointFirstMarginal
            (exactBobInformationReference G n S D base)) +
        ∑ iy : SourceRemainingCoordinate D × Y,
          jointFirstMarginal
              (exactBobInformationPosterior G n S D) iy *
            finiteRelativeEntropy
              (jointConditional
                (exactBobInformationPosterior G n S D) iy)
              (jointConditional
                (exactBobInformationReference G n S D base) iy) := by
  let e := exactBobInformationEquiv
    (X := X) (Y := Y) (A := A) (B := B) D
  let p := exactBobInformationPosterior G n S D
  let q := exactBobInformationReference G n S D base
  have hp : ∀ t, 0 ≤ p t := by
    intro t
    exact exactLocallySampleableLaw_nonneg
      G n S D positive (e.symm t)
  have hq : ∀ t, 0 ≤ q t := by
    intro t
    exact exactLocallySampleableJB_nonneg
      G n S D positive base (e.symm t)
  have hac : ∀ t, q t = 0 → p t = 0 := by
    intro t ht
    exact exactLocallySampleableLaw_absolute_continuous_JB
      G n S D remaining positive base (e.symm t) ht
  have hpnorm : (∑ t, p t) = 1 := by
    change (∑ t, exactLocallySampleableLaw
      G n S D (e.symm t)) = 1
    rw [e.symm.sum_comp]
    exact exactLocallySampleableLaw_sum
      G n S D remaining positive
  have hqnorm : (∑ t, q t) = 1 := by
    change (∑ t, exactLocallySampleableJB
      G n S D base (e.symm t)) = 1
    rw [e.symm.sum_comp]
    exact exactLocallySampleableJB_sum
      G n S D remaining base
  calc
    finiteRelativeEntropy
        (exactLocallySampleableLaw G n S D)
        (exactLocallySampleableJB G n S D base) =
      finiteRelativeEntropy p q := by
        exact (exactFiniteRelativeEntropy_equiv e
          (exactLocallySampleableLaw G n S D)
          (exactLocallySampleableJB G n S D base)).symm
    _ = _ := finite_relative_entropy_joint_chain_rule
      p q hp hq hac hpnorm hqnorm

/-- The error rate associated with exact source pinsker. -/
def exactSourcePinskerRate
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) : ℝ :=
  Real.sqrt (exactSourceClassicalInformationRate G n S D / 2)

theorem exact_source_alice_pinsker_of_classical_information
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (information :
      ExactSourceClassicalInformationBound G n S D base) :
    finiteTotalVariation
        (exactLocallySampleableLaw G n S D)
        (exactLocallySampleableJA G n S D base) ≤
      exactSourcePinskerRate G n S D := by
  calc
    _ ≤ Real.sqrt
      (finiteRelativeEntropy
        (exactLocallySampleableLaw G n S D)
        (exactLocallySampleableJA G n S D base) / 2) :=
      exactLocallySampleableJA_pinsker
        G n S D remaining positive base
    _ ≤ exactSourcePinskerRate G n S D := by
      unfold exactSourcePinskerRate
      apply Real.sqrt_le_sqrt
      exact div_le_div_of_nonneg_right information.1 (by norm_num)

theorem exact_source_bob_pinsker_of_classical_information
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (base : ExactHistoryFlag X Y A B D)
    (information :
      ExactSourceClassicalInformationBound G n S D base) :
    finiteTotalVariation
        (exactLocallySampleableLaw G n S D)
        (exactLocallySampleableJB G n S D base) ≤
      exactSourcePinskerRate G n S D := by
  calc
    _ ≤ Real.sqrt
      (finiteRelativeEntropy
        (exactLocallySampleableLaw G n S D)
        (exactLocallySampleableJB G n S D base) / 2) :=
      exactLocallySampleableJB_pinsker
        G n S D remaining positive base
    _ ≤ exactSourcePinskerRate G n S D := by
      unfold exactSourcePinskerRate
      apply Real.sqrt_le_sqrt
      exact div_le_div_of_nonneg_right information.2 (by norm_num)

end

section

open scoped BigOperators


attribute [local instance] Classical.propDecidable

theorem exactSeedCoordinateFiber_sum
    {M : Type*} [Fintype M] [DecidableEq M]
    (coordinate : M) :
    (∑ partition : M → Bool,
      ∑ leftOrder : Equiv.Perm
        {j : M // j ∈ exactLeft coordinate partition},
      ∑ rightOrder : Equiv.Perm
        {j : M // j ∈ exactRight coordinate partition},
      ∑ leftCut : Fin
        ((exactLeft coordinate partition).card + 1),
      ∑ rightCut : Fin
        ((exactRight coordinate partition).card + 1),
        exactSeedWeight
          ⟨coordinate, partition, leftOrder,
            rightOrder, leftCut, rightCut⟩) =
      1 / (Fintype.card M : ℝ) := by
  classical
  have hbits : 0 < Fintype.card (M → Bool) :=
    Fintype.card_pos_iff.mpr ⟨fun _ => false⟩
  conv_rhs =>
    rw [← exactUniform_sum_mul hbits
      (1 / (Fintype.card M : ℝ))]
  apply Finset.sum_congr (by ext; simp only [mem_univ])
  intro partition _
  let : DecidableEq
      {j : M // j ∈ exactLeft coordinate partition} :=
    fun a b => Classical.propDecidable (a = b)
  let : DecidableEq
      {j : M // j ∈ exactRight coordinate partition} :=
    fun a b => Classical.propDecidable (a = b)
  conv_rhs =>
    rw [← exactPermutationUniform_sum_mul
      (T := {j : M // j ∈ exactLeft coordinate partition})
      ((1 / (Fintype.card M : ℝ)) *
        (1 / (Fintype.card (M → Bool) : ℝ)))]
  apply Finset.sum_congr (by ext; simp only [mem_univ])
  intro leftOrder _
  conv_rhs =>
    rw [← exactPermutationUniform_sum_mul
      (T := {j : M // j ∈ exactRight coordinate partition})
      ((1 / (Fintype.card M : ℝ)) *
        (1 / (Fintype.card (M → Bool) : ℝ)) *
        (1 / (Fintype.card
          (Equiv.Perm
            {j : M // j ∈ exactLeft coordinate partition}) : ℝ)))]
  apply Finset.sum_congr (by ext; simp only [mem_univ])
  intro rightOrder _
  conv_rhs =>
    rw [← exactPrefixUniform_sum_mul
      (exactLeft coordinate partition).card
      ((1 / (Fintype.card M : ℝ)) *
        (1 / (Fintype.card (M → Bool) : ℝ)) *
        (1 / (Fintype.card
          (Equiv.Perm
            {j : M // j ∈ exactLeft coordinate partition}) : ℝ)) *
        (1 / (Fintype.card
          (Equiv.Perm
            {j : M // j ∈ exactRight coordinate partition}) : ℝ)))]
  apply Finset.sum_congr (by ext; simp only [mem_univ])
  intro leftCut _
  conv_rhs =>
    rw [← exactPrefixUniform_sum_mul
      (exactRight coordinate partition).card
      ((1 / (Fintype.card M : ℝ)) *
        (1 / (Fintype.card (M → Bool) : ℝ)) *
        (1 / (Fintype.card
          (Equiv.Perm
            {j : M // j ∈ exactLeft coordinate partition}) : ℝ)) *
        (1 / (Fintype.card
          (Equiv.Perm
            {j : M // j ∈ exactRight coordinate partition}) : ℝ)) *
        (1 / ((exactLeft coordinate partition).card + 1 : ℝ)))]
  apply Finset.sum_congr (by ext; simp only [mem_univ])
  intro rightCut _
  simp only [exactSeedWeight]
  refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·)
    (congrArg₂ (· * ·) rfl ?_) ?_) rfl) rfl
  · exact congrArg (fun k : ℕ => 1 / (k : ℝ)) (exactFintypeCard_eq _ _)
  · exact congrArg (fun k : ℕ => 1 / (k : ℝ)) (exactFintypeCard_eq _ _)

theorem exactSeedWeight_coordinate_sum
    {M : Type*} [Fintype M] [DecidableEq M]
    (f : M → ℝ) :
    (∑ seed : ExactForwardSeed M,
      exactSeedWeight seed * f seed.coordinate) =
      ∑ i : M, (1 / (Fintype.card M : ℝ)) * f i := by
  classical
  rw [exactForwardSeed_sum]
  apply Finset.sum_congr (by ext; simp only [mem_univ])
  intro i _
  simp_rw [← Finset.sum_mul]
  rw [exactSeedCoordinateFiber_sum i]

theorem exactSeedWeight_coordinate_marginal
    {M : Type*} [Fintype M] [DecidableEq M]
    (i : M) :
    (∑ seed : ExactForwardSeed M,
      if seed.coordinate = i then exactSeedWeight seed else 0) =
      1 / (Fintype.card M : ℝ) := by
  have h := exactSeedWeight_coordinate_sum
    (M := M) (fun j => if j = i then (1 : ℝ) else 0)
  simpa only [mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] using h

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The finite equivalence encoding exact source prefix flag. -/
def exactSourcePrefixFlagEquiv
    {Ω V Z : Type*} {h : ℕ} :
    ((Ω × (Fin h → V)) × Z) ≃
      ((Ω × Z) × (Fin h → V)) where
  toFun t := ((t.1.1, t.2), t.1.2)
  invFun t := ((t.1.1, t.2), t.1.2)
  left_inv t := by
    rcases t with ⟨⟨u, values⟩, z⟩
    rfl
  right_inv t := by
    rcases t with ⟨⟨u, z⟩, values⟩
    rfl

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The marginal distribution of exact alice question prior. -/
def exactAliceQuestionPriorMarginal
    (G : Game X Y A B) (x : X) : ℝ :=
  ∑ y : Y, G.questionWeight x y

/-- The marginal distribution of exact bob question prior. -/
def exactBobQuestionPriorMarginal
    (G : Game X Y A B) (y : Y) : ℝ :=
  ∑ x : X, G.questionWeight x y

theorem exactAliceInformationReference_firstMarginal
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D)
    (i : SourceRemainingCoordinate D) (x : X) :
    jointFirstMarginal
        (exactAliceInformationReference G n S D base)
        (i, x) =
      exactAliceQuestionPriorMarginal G x /
        (Fintype.card (SourceRemainingCoordinate D) : ℝ) := by
  unfold jointFirstMarginal
  rw [Fintype.sum_prod_type]
  change
    (∑ r : ExactHistoryFlag X Y A B D,
      ∑ y : Y,
        G.questionWeight x y *
          exactAliceLocalConditional D base
            (exactLocallySampleableLaw G n S D) i x r /
          (Fintype.card (SourceRemainingCoordinate D) : ℝ)) =
      (∑ y : Y, G.questionWeight x y) /
        (Fintype.card (SourceRemainingCoordinate D) : ℝ)
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_div, ← Finset.mul_sum,
    exactAliceLocalConditional_sum, mul_one]

theorem exactBobInformationReference_firstMarginal
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D)
    (i : SourceRemainingCoordinate D) (y : Y) :
    jointFirstMarginal
        (exactBobInformationReference G n S D base)
        (i, y) =
      exactBobQuestionPriorMarginal G y /
        (Fintype.card (SourceRemainingCoordinate D) : ℝ) := by
  unfold jointFirstMarginal
  rw [Fintype.sum_prod_type]
  change
    (∑ r : ExactHistoryFlag X Y A B D,
      ∑ x : X,
        G.questionWeight x y *
          exactBobLocalConditional D base
            (exactLocallySampleableLaw G n S D) i y r /
          (Fintype.card (SourceRemainingCoordinate D) : ℝ)) =
      (∑ x : X, G.questionWeight x y) /
        (Fintype.card (SourceRemainingCoordinate D) : ℝ)
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_div, ← Finset.mul_sum,
    exactBobLocalConditional_sum, mul_one]

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem exactGroupedMass_decidableEq_irrel
    {Ω κ : Type*} [Fintype Ω]
    (first second : DecidableEq κ)
    (projection : Ω → κ) (mass : Ω → ℝ) :
    @groupedMass Ω _ κ first projection mass =
      @groupedMass Ω _ κ second projection mass := by
  have h : first = second := Subsingleton.elim first second
  subst second
  rfl

/-- Grouped masses agree when their projections and source weights agree, independently of
the chosen decidable-equality implementations on the target. -/
theorem exactGroupedMass_congr
    {Ω κ : Type*} [Fintype Ω]
    (first second : DecidableEq κ)
    (projection₁ projection₂ : Ω → κ) (mass₁ mass₂ : Ω → ℝ)
    (projection_eq : projection₁ = projection₂)
    (mass_eq : mass₁ = mass₂) :
    @groupedMass Ω _ κ first projection₁ mass₁ =
      @groupedMass Ω _ κ second projection₂ mass₂ := by
  subst projection₂
  subst mass₂
  exact exactGroupedMass_decidableEq_irrel first second projection₁ mass₁

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/--
The exact alice source marginal information construction used in the quantum parallel-repetition
argument.
-/
def exactAliceSourceMarginalInformation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D) : ℝ :=
  finiteRelativeEntropy
    (jointFirstMarginal
      (exactAliceInformationPosterior G n S D))
    (jointFirstMarginal
      (exactAliceInformationReference G n S D base))

/--
The exact bob source marginal information construction used in the quantum parallel-repetition
argument.
-/
def exactBobSourceMarginalInformation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D) : ℝ :=
  finiteRelativeEntropy
    (jointFirstMarginal
      (exactBobInformationPosterior G n S D))
    (jointFirstMarginal
      (exactBobInformationReference G n S D base))

/--
The exact alice source conditional information construction used in the quantum parallel-
repetition argument.
-/
def exactAliceSourceConditionalInformation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D) : ℝ :=
  ∑ ix : SourceRemainingCoordinate D × X,
    jointFirstMarginal
        (exactAliceInformationPosterior G n S D) ix *
      finiteRelativeEntropy
        (jointConditional
          (exactAliceInformationPosterior G n S D) ix)
        (jointConditional
          (exactAliceInformationReference G n S D base) ix)

/--
The exact bob source conditional information construction used in the quantum parallel-
repetition argument.
-/
def exactBobSourceConditionalInformation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (base : ExactHistoryFlag X Y A B D) : ℝ :=
  ∑ iy : SourceRemainingCoordinate D × Y,
    jointFirstMarginal
        (exactBobInformationPosterior G n S D) iy *
      finiteRelativeEntropy
        (jointConditional
          (exactBobInformationPosterior G n S D) iy)
        (jointConditional
          (exactBobInformationReference G n S D base) iy)

end

section

open scoped BigOperators


attribute [local instance] Classical.propDecidable

private def exactInsertedRank
    {M : Type*} [DecidableEq M]
    (i : M) (side : Finset M) (not_mem : i ∉ side)
    (rank : {j : M // j ∈ side} ≃ Fin side.card)
    (cut : Fin (side.card + 1)) :
    {j : M // j ∈ insert i side} ≃ Fin (side.card + 1) :=
  (Finset.subtypeInsertEquivOption not_mem).trans
    ((Equiv.optionCongr rank).trans (finSuccEquiv' cut).symm)

@[simp] theorem exactInsertedRank_marker
    {M : Type*} [DecidableEq M]
    (i : M) (side : Finset M) (not_mem : i ∉ side)
    (rank : {j : M // j ∈ side} ≃ Fin side.card)
    (cut : Fin (side.card + 1)) :
    exactInsertedRank i side not_mem rank cut
      ⟨i, Finset.mem_insert_self i side⟩ = cut := by
  simp only [exactInsertedRank, subtypeInsertEquivOption, Equiv.trans_apply, Equiv.coe_fn_mk,
    ↓reduceDIte, Equiv.optionCongr_apply, Option.map_none, finSuccEquiv'_symm_none]

theorem exactInsertedRank_old
    {M : Type*} [DecidableEq M]
    (i : M) (side : Finset M) (not_mem : i ∉ side)
    (rank : {j : M // j ∈ side} ≃ Fin side.card)
    (cut : Fin (side.card + 1))
    (j : {j : M // j ∈ side}) :
    exactInsertedRank i side not_mem rank cut
      ⟨j.val, Finset.mem_insert_of_mem j.property⟩ =
      cut.succAbove (rank j) := by
  have hne : j.val ≠ i := by
    intro h
    exact not_mem (h ▸ j.property)
  simp only [exactInsertedRank, subtypeInsertEquivOption, Equiv.trans_apply, Equiv.coe_fn_mk, hne,
    ↓reduceDIte, Subtype.coe_eta, Equiv.optionCongr_apply, Option.map_some,
    finSuccEquiv'_symm_some]

/-- The rank map for exact reverse left. -/
def exactReverseLeftRank
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    {j : M // j ∈ exactReverseLeftSide seed} ≃
      Fin ((exactLeft seed.coordinate seed.partition).card + 1) :=
  exactInsertedRank seed.coordinate
    (exactLeft seed.coordinate seed.partition)
    (exactLeft_coordinate_not_mem seed.coordinate seed.partition)
    (exactLeftRank seed) seed.leftCut

/-- The rank map for exact reverse right. -/
def exactReverseRightRank
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    {j : M // j ∈ exactReverseRightSide seed} ≃
      Fin ((exactRight seed.coordinate seed.partition).card + 1) :=
  exactInsertedRank seed.coordinate
    (exactRight seed.coordinate seed.partition)
    (exactRight_coordinate_not_mem seed.coordinate seed.partition)
    (exactRightRank seed) seed.rightCut

@[simp] theorem exactReverseLeftRank_coordinate
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    exactReverseLeftRank seed
      ⟨seed.coordinate,
        exactReverseLeftSide_coordinate_mem seed⟩ =
      seed.leftCut := by
  exact exactInsertedRank_marker
    seed.coordinate
    (exactLeft seed.coordinate seed.partition)
    (exactLeft_coordinate_not_mem
      seed.coordinate seed.partition)
    (exactLeftRank seed) seed.leftCut

@[simp] theorem exactReverseRightRank_coordinate
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    exactReverseRightRank seed
      ⟨seed.coordinate,
        exactReverseRightSide_coordinate_mem seed⟩ =
      seed.rightCut := by
  exact exactInsertedRank_marker
    seed.coordinate
    (exactRight seed.coordinate seed.partition)
    (exactRight_coordinate_not_mem
      seed.coordinate seed.partition)
    (exactRightRank seed) seed.rightCut

theorem exactReverseLeftRank_old
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M)
    (j : {j : M //
      j ∈ exactLeft seed.coordinate seed.partition}) :
    exactReverseLeftRank seed
      ⟨j.val, Finset.mem_insert_of_mem j.property⟩ =
      seed.leftCut.succAbove (exactLeftRank seed j) := by
  exact exactInsertedRank_old
    seed.coordinate
    (exactLeft seed.coordinate seed.partition)
    (exactLeft_coordinate_not_mem
      seed.coordinate seed.partition)
    (exactLeftRank seed) seed.leftCut j

theorem exactReverseRightRank_old
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M)
    (j : {j : M //
      j ∈ exactRight seed.coordinate seed.partition}) :
    exactReverseRightRank seed
      ⟨j.val, Finset.mem_insert_of_mem j.property⟩ =
      seed.rightCut.succAbove (exactRightRank seed j) := by
  exact exactInsertedRank_old
    seed.coordinate
    (exactRight seed.coordinate seed.partition)
    (exactRight_coordinate_not_mem
      seed.coordinate seed.partition)
    (exactRightRank seed) seed.rightCut j

private def exactInsertedPrefixBefore
    {M : Type*} [DecidableEq M]
    (i : M) (side : Finset M) (not_mem : i ∉ side)
    (rank : {j : M // j ∈ side} ≃ Fin side.card)
    (cut : Fin (side.card + 1)) : Finset M :=
  (Finset.univ.filter
    (fun j : {j : M // j ∈ insert i side} =>
      (exactInsertedRank i side not_mem rank cut j).val <
        cut.val)).image Subtype.val

theorem exactInsertedPrefixBefore_marker_eq
    {M : Type*} [DecidableEq M]
    (i : M) (side : Finset M) (not_mem : i ∉ side)
    (rank : {j : M // j ∈ side} ≃ Fin side.card)
    (cut : Fin (side.card + 1)) :
    exactInsertedPrefixBefore i side not_mem rank cut =
      (Finset.univ.filter
        (fun j : {j : M // j ∈ side} =>
          (rank j).val < cut.val)).image Subtype.val := by
  ext j
  constructor
  · intro hj
    obtain ⟨a, ha, haval⟩ := Finset.mem_image.mp hj
    have hlt :
        (exactInsertedRank i side not_mem rank cut a).val <
          cut.val := (Finset.mem_filter.mp ha).2
    have hne : a.val ≠ i := by
      intro heq
      have hsub : a = ⟨i, Finset.mem_insert_self i side⟩ :=
        Subtype.ext heq
      rw [hsub, exactInsertedRank_marker] at hlt
      exact (Nat.lt_irrefl cut.val) hlt
    have hside : a.val ∈ side :=
      (Finset.mem_insert.mp a.property).resolve_left hne
    let b : {j : M // j ∈ side} := ⟨a.val, hside⟩
    refine Finset.mem_image.mpr ⟨b, ?_, haval⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ b, ?_⟩
    have hbefore :
        cut.succAbove (rank b) < cut := by
      change (cut.succAbove (rank b)).val < cut.val
      rw [← exactInsertedRank_old
        i side not_mem rank cut b]
      exact hlt
    have hcast : (rank b).castSucc < cut :=
      (Fin.succAbove_lt_iff_castSucc_lt cut (rank b)).mp hbefore
    exact hcast
  · intro hj
    obtain ⟨b, hb, hbval⟩ := Finset.mem_image.mp hj
    have hlt : (rank b).val < cut.val :=
      (Finset.mem_filter.mp hb).2
    let a : {j : M // j ∈ insert i side} :=
      ⟨b.val, Finset.mem_insert_of_mem b.property⟩
    refine Finset.mem_image.mpr ⟨a, ?_, hbval⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ a, ?_⟩
    have hcast : (rank b).castSucc < cut := hlt
    have hbefore : cut.succAbove (rank b) < cut :=
      (Fin.succAbove_lt_iff_castSucc_lt cut (rank b)).mpr hcast
    rw [exactInsertedRank_old
      i side not_mem rank cut b]
    exact hbefore

private def exactReverseLeftPrefixBeforeMarked
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) : Finset M :=
  exactInsertedPrefixBefore seed.coordinate
    (exactLeft seed.coordinate seed.partition)
    (exactLeft_coordinate_not_mem
      seed.coordinate seed.partition)
    (exactLeftRank seed) seed.leftCut

private def exactReverseRightPrefixBeforeMarked
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) : Finset M :=
  exactInsertedPrefixBefore seed.coordinate
    (exactRight seed.coordinate seed.partition)
    (exactRight_coordinate_not_mem
      seed.coordinate seed.partition)
    (exactRightRank seed) seed.rightCut

theorem exactReverseLeftPrefixBeforeMarked_eq
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    exactReverseLeftPrefixBeforeMarked seed =
      exactLeftPrefix seed := by
  exact exactInsertedPrefixBefore_marker_eq
    seed.coordinate
    (exactLeft seed.coordinate seed.partition)
    (exactLeft_coordinate_not_mem
      seed.coordinate seed.partition)
    (exactLeftRank seed) seed.leftCut

theorem exactReverseRightPrefixBeforeMarked_eq
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    exactReverseRightPrefixBeforeMarked seed =
      exactRightPrefix seed := by
  exact exactInsertedPrefixBefore_marker_eq
    seed.coordinate
    (exactRight seed.coordinate seed.partition)
    (exactRight_coordinate_not_mem
      seed.coordinate seed.partition)
    (exactRightRank seed) seed.rightCut

end

section

open scoped BigOperators


attribute [local instance] Classical.propDecidable

/-- The exact ordered side prefix construction used in the quantum parallel-repetition argument. -/
def exactOrderedSidePrefix
    {M : Type*} [DecidableEq M]
    (side : Finset M)
    (rank : {j : M // j ∈ side} ≃ Fin side.card)
    (cut : Fin (side.card + 1)) : Finset M :=
  (Finset.univ.filter
    (fun j : {j : M // j ∈ side} =>
      (rank j).val < cut.val)).image Subtype.val

theorem exactOrderedSidePrefix_mem_iff
    {M : Type*} [DecidableEq M]
    (side : Finset M)
    (rank : {j : M // j ∈ side} ≃ Fin side.card)
    (cut : Fin (side.card + 1)) (j : M) :
    j ∈ exactOrderedSidePrefix side rank cut ↔
      ∃ hj : j ∈ side, (rank ⟨j, hj⟩).val < cut.val := by
  constructor
  · intro hj
    obtain ⟨a, ha, haval⟩ := Finset.mem_image.mp hj
    have hside : j ∈ side := haval ▸ a.property
    refine ⟨hside, ?_⟩
    have hsub : (⟨j, hside⟩ : {j : M // j ∈ side}) = a :=
      Subtype.ext haval.symm
    rw [hsub]
    exact (Finset.mem_filter.mp ha).2
  · rintro ⟨hj, hlt⟩
    exact Finset.mem_image.mpr
      ⟨⟨j, hj⟩, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hlt⟩, rfl⟩

theorem exactInsertedPrefixBefore_mem_iff
    {M : Type*} [DecidableEq M]
    (i : M) (side : Finset M) (not_mem : i ∉ side)
    (rank : {j : M // j ∈ side} ≃ Fin side.card)
    (cut : Fin (side.card + 1)) (j : M) :
    j ∈ exactInsertedPrefixBefore i side not_mem rank cut ↔
      ∃ hj : j ∈ insert i side,
        (exactInsertedRank i side not_mem rank cut
          ⟨j, hj⟩).val < cut.val := by
  constructor
  · intro hj
    obtain ⟨a, ha, haval⟩ := Finset.mem_image.mp hj
    have hside : j ∈ insert i side := haval ▸ a.property
    refine ⟨hside, ?_⟩
    have hsub : (⟨j, hside⟩ : {j : M // j ∈ insert i side}) = a :=
      Subtype.ext haval.symm
    rw [hsub]
    exact (Finset.mem_filter.mp ha).2
  · rintro ⟨hj, hlt⟩
    exact Finset.mem_image.mpr
      ⟨⟨j, hj⟩, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hlt⟩, rfl⟩

/-- The information retained when decoding one side of a reverse seed. -/
structure ExactReverseSideContext
    (M : Type*) [Fintype M] [DecidableEq M]
    (side : Finset M) where
  /-- The coordinates on the opposite side of the partition. -/
  otherSide : Finset M
  /-- The rank equivalence for the decoded side. -/
  sideRank : {j : M // j ∈ side} ≃ Fin side.card
  /-- The rank equivalence for the opposite side. -/
  otherRank : {j : M // j ∈ otherSide} ≃ Fin otherSide.card
  /-- The reveal cut on the opposite side. -/
  otherCut : Fin (otherSide.card + 1)
  /-- The partition bit omitted by the reverse encoding. -/
  ignoredBit : Bool
  otherSide_eq_complement : otherSide = Finset.univ \ side
  deriving Fintype

/--
The exact reverse context other prefix construction used in the quantum parallel-repetition
argument.
-/
def exactReverseContextOtherPrefix
    {M : Type*} [Fintype M] [DecidableEq M]
    {side : Finset M}
    (context : ExactReverseSideContext M side) : Finset M :=
  exactOrderedSidePrefix
    context.otherSide context.otherRank context.otherCut

theorem exactReverseLeftSide_complement
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    exactRight seed.coordinate seed.partition =
      Finset.univ \ exactReverseLeftSide seed := by
  ext j
  by_cases hcoordinate : j = seed.coordinate
  · subst j
    simp only [exactRight, ne_eq, mem_filter, mem_univ, not_true_eq_false, false_and, and_false,
      exactReverseLeftSide, mem_sdiff, mem_insert, true_or]
  · cases hbit : seed.partition j <;>
      simp [exactRight, exactLeft,
        exactReverseLeftSide, hcoordinate, hbit]

theorem exactReverseRightSide_complement
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    exactLeft seed.coordinate seed.partition =
      Finset.univ \ exactReverseRightSide seed := by
  ext j
  by_cases hcoordinate : j = seed.coordinate
  · subst j
    simp only [exactLeft, ne_eq, mem_filter, mem_univ, not_true_eq_false, false_and, and_false,
      exactReverseRightSide, mem_sdiff, mem_insert, true_or]
  · cases hbit : seed.partition j <;>
      simp [exactRight, exactLeft,
        exactReverseRightSide, hcoordinate, hbit]

/-- The data context recording exact reverse alice. -/
def exactReverseAliceContext
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    ExactReverseSideContext M
      (exactReverseLeftSide seed) where
  otherSide := exactRight seed.coordinate seed.partition
  sideRank := (exactReverseLeftRank seed).trans
    (finCongr (exactReverseLeftSide_card seed).symm)
  otherRank := exactRightRank seed
  otherCut := seed.rightCut
  ignoredBit := seed.partition seed.coordinate
  otherSide_eq_complement := exactReverseLeftSide_complement seed

/-- The data context recording exact reverse bob. -/
def exactReverseBobContext
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    ExactReverseSideContext M
      (exactReverseRightSide seed) where
  otherSide := exactLeft seed.coordinate seed.partition
  sideRank := (exactReverseRightRank seed).trans
    (finCongr (exactReverseRightSide_card seed).symm)
  otherRank := exactLeftRank seed
  otherCut := seed.leftCut
  ignoredBit := seed.partition seed.coordinate
  otherSide_eq_complement := exactReverseRightSide_complement seed

/-- The data context recording exact default reverse side. -/
def exactDefaultReverseSideContext
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) : ExactReverseSideContext M side where
  otherSide := Finset.univ \ side
  sideRank := Finset.equivFin side
  otherRank := Finset.equivFin (Finset.univ \ side)
  otherCut := 0
  ignoredBit := false
  otherSide_eq_complement := rfl

/--
The exact reverse alice context at construction used in the quantum parallel-repetition
argument.
-/
def exactReverseAliceContextAt
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (seed : ExactForwardSeed M) :
    ExactReverseSideContext M side :=
  if h : exactReverseLeftSide seed = side then
    h ▸ exactReverseAliceContext seed
  else
    exactDefaultReverseSideContext side

/--
The exact reverse bob context at construction used in the quantum parallel-repetition argument.
-/
def exactReverseBobContextAt
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (seed : ExactForwardSeed M) :
    ExactReverseSideContext M side :=
  if h : exactReverseRightSide seed = side then
    h ▸ exactReverseBobContext seed
  else
    exactDefaultReverseSideContext side

@[simp] theorem exactReverseAliceContextAt_actual
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    exactReverseAliceContextAt
        (exactReverseLeftSide seed) seed =
      exactReverseAliceContext seed := by
  simp only [exactReverseAliceContextAt, ↓reduceDIte]

@[simp] theorem exactReverseBobContextAt_actual
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    exactReverseBobContextAt
        (exactReverseRightSide seed) seed =
      exactReverseBobContext seed := by
  simp only [exactReverseBobContextAt, ↓reduceDIte]

@[simp] theorem exactReverseAliceContext_otherPrefix
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    exactReverseContextOtherPrefix
        (exactReverseAliceContext seed) =
      exactRightPrefix seed := by
  rfl

@[simp] theorem exactReverseBobContext_otherPrefix
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    exactReverseContextOtherPrefix
        (exactReverseBobContext seed) =
      exactLeftPrefix seed := by
  rfl

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/--
The type used to represent exact reverse alice fixed information in the exact sampling
construction.
-/
abbrev ExactReverseAliceFixedInformation
    (X Y : Type*)
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D)) :=
  Σ context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side,
    ({j : Fin n // j ∈ D} → X) ×
    ({j : Fin n // j ∈ D} → Y) ×
    ({j : SourceRemainingCoordinate D // j ∈ side} → X) ×
    ({j : SourceRemainingCoordinate D // j ∈ context.otherSide} → Y) ×
    ({j : SourceRemainingCoordinate D //
        j ∈ exactReverseContextOtherPrefix context} → X)

/--
The type used to represent exact reverse bob fixed information in the exact sampling
construction.
-/
abbrev ExactReverseBobFixedInformation
    (X Y : Type*)
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D)) :=
  Σ context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side,
    ({j : Fin n // j ∈ D} → X) ×
    ({j : Fin n // j ∈ D} → Y) ×
    ({j : SourceRemainingCoordinate D // j ∈ side} → Y) ×
    ({j : SourceRemainingCoordinate D // j ∈ context.otherSide} → X) ×
    ({j : SourceRemainingCoordinate D //
        j ∈ exactReverseContextOtherPrefix context} → Y)

/-- The projection associated with exact reverse alice source. -/
def exactReverseAliceSourceProjection
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D)) :
    ExactJointOutcome X Y A B D →
      ExactReverseAliceFixedInformation X Y D side ×
        (Fin side.card → Y) :=
  fun q =>
    let context := exactReverseAliceContextAt side q.1
    (⟨context,
       (fun j => q.2.1 j.val),
       (fun j => q.2.2.1 j.val),
       (fun j => q.2.1 j.val.val),
       (fun j => q.2.2.1 j.val.val),
       (fun j => q.2.1 j.val.val)⟩,
      fun k => q.2.2.1 (context.sideRank.symm k).val.val)

/-- The projection associated with exact reverse bob source. -/
def exactReverseBobSourceProjection
    {n : ℕ} (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D)) :
    ExactJointOutcome X Y A B D →
      ExactReverseBobFixedInformation X Y D side ×
        (Fin side.card → X) :=
  fun q =>
    let context := exactReverseBobContextAt side q.1
    (⟨context,
       (fun j => q.2.1 j.val),
       (fun j => q.2.2.1 j.val),
       (fun j => q.2.2.1 j.val.val),
       (fun j => q.2.1 j.val.val),
       (fun j => q.2.2.1 j.val.val)⟩,
      fun k => q.2.1 (context.sideRank.symm k).val.val)

@[simp] theorem exactReverseAliceContext_marked_rank
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    ((exactReverseAliceContext seed).sideRank
      ⟨seed.coordinate,
        exactReverseLeftSide_coordinate_mem seed⟩).val =
      seed.leftCut.val := by
  simp only [exactReverseAliceContext, Equiv.trans_apply, exactReverseLeftRank_coordinate,
    finCongr_apply, Fin.val_cast]

@[simp] theorem exactReverseBobContext_marked_rank
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    ((exactReverseBobContext seed).sideRank
      ⟨seed.coordinate,
        exactReverseRightSide_coordinate_mem seed⟩).val =
      seed.rightCut.val := by
  simp only [exactReverseBobContext, Equiv.trans_apply, exactReverseRightRank_coordinate,
    finCongr_apply, Fin.val_cast]

/--
The exact reverse context prefix before construction used in the quantum parallel-repetition
argument.
-/
def exactReverseContextPrefixBefore
    {M : Type*} [Fintype M] [DecidableEq M]
    {side : Finset M}
    (context : ExactReverseSideContext M side)
    (position : Fin side.card) : Finset M :=
  exactOrderedSidePrefix
    side context.sideRank position.castSucc

theorem exactReverseAliceContext_prefix_before_marked
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    exactReverseContextPrefixBefore
        (exactReverseAliceContext seed)
        ((exactReverseAliceContext seed).sideRank
          ⟨seed.coordinate,
            exactReverseLeftSide_coordinate_mem seed⟩) =
      exactLeftPrefix seed := by
  calc
    exactReverseContextPrefixBefore
        (exactReverseAliceContext seed)
        ((exactReverseAliceContext seed).sideRank
          ⟨seed.coordinate,
            exactReverseLeftSide_coordinate_mem seed⟩) =
        exactReverseLeftPrefixBeforeMarked seed := by
      change
        exactOrderedSidePrefix
          (exactReverseLeftSide seed)
          (exactReverseAliceContext seed).sideRank
          ((exactReverseAliceContext seed).sideRank
            ⟨seed.coordinate,
              exactReverseLeftSide_coordinate_mem seed⟩).castSucc =
        exactInsertedPrefixBefore seed.coordinate
          (exactLeft seed.coordinate seed.partition)
          (exactLeft_coordinate_not_mem
            seed.coordinate seed.partition)
          (exactLeftRank seed) seed.leftCut
      ext j
      simp only [exactOrderedSidePrefix_mem_iff,
        exactInsertedPrefixBefore_mem_iff]
      constructor
      · rintro ⟨hj, hlt⟩
        change j ∈ insert seed.coordinate
          (exactLeft seed.coordinate seed.partition) at hj
        refine ⟨hj, ?_⟩
        have hlt' :
            ((exactReverseAliceContext seed).sideRank
              ⟨j, hj⟩).val < seed.leftCut.val := by
          simpa only [Fin.val_castSucc,
            exactReverseAliceContext_marked_rank] using hlt
        convert hlt' using 1 ;
          simp only [exactReverseAliceContext, exactReverseLeftRank] ;
          congr 2
      · rintro ⟨hj, hlt⟩
        change j ∈ exactReverseLeftSide seed at hj
        refine ⟨hj, ?_⟩
        have hrankValue :
            ((exactReverseAliceContext seed).sideRank
              ⟨j, hj⟩).val =
              (exactReverseLeftRank seed ⟨j, hj⟩).val := by
          simp only [exactReverseAliceContext, Equiv.trans_apply,
            finCongr_apply, Fin.val_cast]
        have hlt' :
            ((exactReverseAliceContext seed).sideRank
              ⟨j, hj⟩).val < seed.leftCut.val := by
          rw [hrankValue]
          exact hlt
        simpa only [Fin.val_castSucc,
          exactReverseAliceContext_marked_rank] using hlt'
    _ = exactLeftPrefix seed :=
      exactReverseLeftPrefixBeforeMarked_eq seed

theorem exactReverseBobContext_prefix_before_marked
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    exactReverseContextPrefixBefore
        (exactReverseBobContext seed)
        ((exactReverseBobContext seed).sideRank
          ⟨seed.coordinate,
            exactReverseRightSide_coordinate_mem seed⟩) =
      exactRightPrefix seed := by
  calc
    exactReverseContextPrefixBefore
        (exactReverseBobContext seed)
        ((exactReverseBobContext seed).sideRank
          ⟨seed.coordinate,
            exactReverseRightSide_coordinate_mem seed⟩) =
        exactReverseRightPrefixBeforeMarked seed := by
      change
        exactOrderedSidePrefix
          (exactReverseRightSide seed)
          (exactReverseBobContext seed).sideRank
          ((exactReverseBobContext seed).sideRank
            ⟨seed.coordinate,
              exactReverseRightSide_coordinate_mem seed⟩).castSucc =
        exactInsertedPrefixBefore seed.coordinate
          (exactRight seed.coordinate seed.partition)
          (exactRight_coordinate_not_mem
            seed.coordinate seed.partition)
          (exactRightRank seed) seed.rightCut
      ext j
      simp only [exactOrderedSidePrefix_mem_iff,
        exactInsertedPrefixBefore_mem_iff]
      constructor
      · rintro ⟨hj, hlt⟩
        change j ∈ insert seed.coordinate
          (exactRight seed.coordinate seed.partition) at hj
        refine ⟨hj, ?_⟩
        have hlt' :
            ((exactReverseBobContext seed).sideRank
              ⟨j, hj⟩).val < seed.rightCut.val := by
          simpa only [Fin.val_castSucc,
            exactReverseBobContext_marked_rank] using hlt
        convert hlt' using 1 ;
          simp only [exactReverseBobContext, exactReverseRightRank] ;
          congr 2
      · rintro ⟨hj, hlt⟩
        change j ∈ exactReverseRightSide seed at hj
        refine ⟨hj, ?_⟩
        have hrankValue :
            ((exactReverseBobContext seed).sideRank
              ⟨j, hj⟩).val =
              (exactReverseRightRank seed ⟨j, hj⟩).val := by
          simp only [exactReverseBobContext, Equiv.trans_apply,
            finCongr_apply, Fin.val_cast]
        have hlt' :
            ((exactReverseBobContext seed).sideRank
              ⟨j, hj⟩).val < seed.rightCut.val := by
          rw [hrankValue]
          exact hlt
        simpa only [Fin.val_castSucc,
          exactReverseBobContext_marked_rank] using hlt'
    _ = exactRightPrefix seed :=
      exactReverseRightPrefixBeforeMarked_eq seed

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

/-- The finite encoding of exact prefix next. -/
def exactPrefixNextCode
    {Ω V : Type*} {h : ℕ}
    (default : V) (k : Fin h) :
    (Ω × (Fin h → V)) → ((Ω × (Fin h → V)) × V) :=
  fun t => (finitePrefixMask default k.castSucc t, t.2 k)

private def exactPrefixNextDecode
    {Ω V : Type*} {h : ℕ}
    (k : Fin h) :
    ((Ω × (Fin h → V)) × V) → (Ω × (Fin h → V)) :=
  fun t => (t.1.1, Function.update t.1.2 k t.2)

theorem exactPrefixNextDecode_comp
    {Ω V : Type*} {h : ℕ}
    (default : V) (k : Fin h) :
    exactPrefixNextDecode (Ω := Ω) (V := V) k ∘
        exactPrefixNextCode default k =
      finitePrefixMask default k.succ := by
  funext t
  apply Prod.ext
  · rfl
  · funext j
    by_cases heq : j = k
    · subst j
      simp only [Function.comp_apply, exactPrefixNextDecode, exactPrefixNextCode,
        finitePrefixMask, Fin.val_castSucc, Fin.val_fin_lt, Function.update_self, Fin.val_succ,
        Order.lt_add_one_iff, Fin.val_fin_le, Std.le_refl, ↓reduceIte]
    · by_cases hlt : j.val < k.val
      · have hfin : j < k := hlt
        have hnotgt : ¬ k < j := not_lt_of_ge (le_of_lt hfin)
        simp only [Function.comp_apply, exactPrefixNextDecode, exactPrefixNextCode,
          finitePrefixMask, Fin.val_castSucc, Fin.val_fin_lt, Function.update_of_ne heq, hfin,
          ↓reduceIte, Fin.val_succ, Order.lt_add_one_iff, Fin.val_fin_le, left_eq_ite_iff, not_le,
          hnotgt, IsEmpty.forall_iff]
      · have hfin : ¬ j < k := hlt
        have hnotle : ¬ j ≤ k := by
          intro hle
          have heqval : j.val = k.val := by omega
          exact heq (Fin.ext heqval)
        simp only [Function.comp_apply, exactPrefixNextDecode, exactPrefixNextCode,
          finitePrefixMask, Fin.val_castSucc, Fin.val_fin_lt, Function.update_of_ne heq, hfin,
          ↓reduceIte, Fin.val_succ, Order.lt_add_one_iff, Fin.val_fin_le, hnotle]

theorem exactPrefixNextCode_comp
    {Ω V : Type*} {h : ℕ}
    (default : V) (k : Fin h) :
    exactPrefixNextCode default k ∘
        finitePrefixMask (Ω := Ω) default k.succ =
      exactPrefixNextCode default k := by
  funext t
  apply Prod.ext
  · exact congrFun
      (finitePrefixMask_comp (Ω := Ω) default k) t
  · simp only [Function.comp_apply, exactPrefixNextCode, finitePrefixMask, Fin.val_succ,
      Order.lt_add_one_iff, Fin.val_fin_le, Fin.val_castSucc, Fin.val_fin_lt, Std.le_refl,
      ↓reduceIte]

theorem exactPrefixNext_relativeEntropy_eq
    {Ω V : Type*} [Fintype Ω] [Fintype V] {h : ℕ}
    (joint prior : Ω × (Fin h → V) → ℝ)
    (joint_nonnegative : ∀ t, 0 ≤ joint t)
    (prior_nonnegative : ∀ t, 0 ≤ prior t)
    (absolute_continuity : ∀ t, prior t = 0 → joint t = 0)
    (default : V) (k : Fin h) :
    finiteRelativeEntropy
        (groupedMass (exactPrefixNextCode default k) joint)
        (groupedMass (exactPrefixNextCode default k) prior) =
      finitePrefixRelativeEntropy joint prior default k.succ := by
  change
    finiteRelativeEntropy
        (groupedMass (exactPrefixNextCode default k) joint)
        (groupedMass (exactPrefixNextCode default k) prior) =
      finiteRelativeEntropy
        (groupedMass
          (finitePrefixMask default k.succ) joint)
        (groupedMass
          (finitePrefixMask default k.succ) prior)
  apply le_antisymm
  · have hdp := finite_relative_entropy_data_processing
      (exactPrefixNextCode default k)
      (groupedMass (finitePrefixMask default k.succ) joint)
      (groupedMass (finitePrefixMask default k.succ) prior)
      (groupedMass_nonneg
        (finitePrefixMask default k.succ)
        joint joint_nonnegative)
      (groupedMass_nonneg
        (finitePrefixMask default k.succ)
        prior prior_nonnegative)
      (groupedMass_absolute_continuity
        (finitePrefixMask default k.succ)
        joint prior prior_nonnegative absolute_continuity)
    rw [groupedMass_comp,
      exactPrefixNextCode_comp,
      groupedMass_comp,
      exactPrefixNextCode_comp] at hdp
    exact hdp
  · have hdp := finite_relative_entropy_data_processing
      (exactPrefixNextDecode (Ω := Ω) (V := V) k)
      (groupedMass (exactPrefixNextCode default k) joint)
      (groupedMass (exactPrefixNextCode default k) prior)
      (groupedMass_nonneg
        (exactPrefixNextCode default k)
        joint joint_nonnegative)
      (groupedMass_nonneg
        (exactPrefixNextCode default k)
        prior prior_nonnegative)
      (groupedMass_absolute_continuity
        (exactPrefixNextCode default k)
        joint prior prior_nonnegative absolute_continuity)
    rw [groupedMass_comp,
      exactPrefixNextDecode_comp,
      groupedMass_comp,
      exactPrefixNextDecode_comp] at hdp
    exact hdp

theorem exactPrefixNext_firstMarginal
    {Ω V : Type*} [Fintype Ω] [Fintype V] {h : ℕ}
    (mass : Ω × (Fin h → V) → ℝ)
    (default : V) (k : Fin h) :
    jointFirstMarginal
        (groupedMass (exactPrefixNextCode default k) mass) =
      groupedMass (finitePrefixMask default k.castSucc) mass := by
  calc
    jointFirstMarginal
        (groupedMass (exactPrefixNextCode default k) mass) =
      groupedMass Prod.fst
        (groupedMass (exactPrefixNextCode default k) mass) :=
        (groupedMass_first
          (groupedMass (exactPrefixNextCode default k) mass)).symm
    _ = groupedMass
        (Prod.fst ∘ exactPrefixNextCode default k) mass :=
        groupedMass_comp
          (exactPrefixNextCode default k) Prod.fst mass
    _ = groupedMass
        (finitePrefixMask default k.castSucc) mass := by
        rfl

theorem exactPrefixEntropyIncrement_eq_conditional
    {Ω V : Type*} [Fintype Ω] [Fintype V] {h : ℕ}
    (joint prior : Ω × (Fin h → V) → ℝ)
    (joint_nonnegative : ∀ t, 0 ≤ joint t)
    (prior_nonnegative : ∀ t, 0 ≤ prior t)
    (absolute_continuity : ∀ t, prior t = 0 → joint t = 0)
    (joint_normalized : (∑ t, joint t) = 1)
    (prior_normalized : (∑ t, prior t) = 1)
    (default : V) (k : Fin h) :
    finitePrefixRelativeEntropy
        joint prior default k.succ -
      finitePrefixRelativeEntropy
        joint prior default k.castSucc =
      ∑ context : Ω × (Fin h → V),
        groupedMass
            (finitePrefixMask default k.castSucc)
            joint context *
          finiteRelativeEntropy
            (jointConditional
              (groupedMass
                (exactPrefixNextCode default k) joint)
              context)
            (jointConditional
              (groupedMass
                (exactPrefixNextCode default k) prior)
              context) := by
  let next := exactPrefixNextCode (Ω := Ω) (V := V) default k
  let nextJoint := groupedMass next joint
  let nextPrior := groupedMass next prior
  have hnext_joint : ∀ t, 0 ≤ nextJoint t :=
    groupedMass_nonneg next joint joint_nonnegative
  have hnext_prior : ∀ t, 0 ≤ nextPrior t :=
    groupedMass_nonneg next prior prior_nonnegative
  have hnext_absolute :
      ∀ t, nextPrior t = 0 → nextJoint t = 0 :=
    groupedMass_absolute_continuity
      next joint prior prior_nonnegative absolute_continuity
  have hnext_joint_normalized : (∑ t, nextJoint t) = 1 := by
    rw [groupedMass_sum]
    exact joint_normalized
  have hnext_prior_normalized : (∑ t, nextPrior t) = 1 := by
    rw [groupedMass_sum]
    exact prior_normalized
  have hchain := finite_relative_entropy_joint_chain_rule
    nextJoint nextPrior hnext_joint hnext_prior hnext_absolute
    hnext_joint_normalized hnext_prior_normalized
  have hnext_entropy := exactPrefixNext_relativeEntropy_eq
    joint prior joint_nonnegative prior_nonnegative absolute_continuity
    default k
  change
    finitePrefixRelativeEntropy
        joint prior default k.succ -
      finitePrefixRelativeEntropy
        joint prior default k.castSucc = _
  change
    finiteRelativeEntropy nextJoint nextPrior =
      finitePrefixRelativeEntropy
        joint prior default k.succ at hnext_entropy
  change
    finiteRelativeEntropy nextJoint nextPrior =
      finiteRelativeEntropy
          (jointFirstMarginal nextJoint)
          (jointFirstMarginal nextPrior) +
        ∑ context : Ω × (Fin h → V),
          jointFirstMarginal nextJoint context *
            finiteRelativeEntropy
              (jointConditional nextJoint context)
              (jointConditional nextPrior context) at hchain
  have hfirst_joint :
      jointFirstMarginal nextJoint =
        groupedMass
          (finitePrefixMask default k.castSucc) joint :=
    exactPrefixNext_firstMarginal joint default k
  have hfirst_prior :
      jointFirstMarginal nextPrior =
        groupedMass
          (finitePrefixMask default k.castSucc) prior :=
    exactPrefixNext_firstMarginal prior default k
  rw [hfirst_joint, hfirst_prior] at hchain
  change
    finitePrefixRelativeEntropy
        joint prior default k.succ -
      finitePrefixRelativeEntropy
        joint prior default k.castSucc =
      ∑ context : Ω × (Fin h → V),
        groupedMass
            (finitePrefixMask default k.castSucc)
            joint context *
          finiteRelativeEntropy
            (jointConditional nextJoint context)
            (jointConditional nextPrior context)
  change
    finiteRelativeEntropy nextJoint nextPrior =
      finitePrefixRelativeEntropy
        joint prior default k.castSucc +
        ∑ context : Ω × (Fin h → V),
          groupedMass
              (finitePrefixMask default k.castSucc)
              joint context *
            finiteRelativeEntropy
              (jointConditional nextJoint context)
              (jointConditional nextPrior context) at hchain
  linarith

end

section

open scoped BigOperators


open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

private def exactReverseAliceCanonicalPartition
    {M : Type*} [DecidableEq M]
    (side : Finset M) (coordinate : M) (ignored : Bool) : M → Bool :=
  fun j => if j = coordinate then ignored
    else if j ∈ side then false else true

theorem exactReverseAliceCanonicalPartition_side
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) (ignored : Bool) :
    insert coordinate
        (exactLeft coordinate
          (exactReverseAliceCanonicalPartition
            side coordinate ignored)) = side := by
  ext j
  by_cases hj : j = coordinate
  · subst j
    simp only [mem_insert, true_or, member]
  · by_cases hs : j ∈ side <;>
      simp [exactLeft,
        exactReverseAliceCanonicalPartition,
        hj, hs]

theorem exactReverseAliceCanonicalPartition_unique
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (partition : M → Bool)
    (fiber : insert coordinate
      (exactLeft coordinate partition) = side) :
    partition = exactReverseAliceCanonicalPartition
      side coordinate (partition coordinate) := by
  funext j
  by_cases hj : j = coordinate
  · subst j
    simp only [exactReverseAliceCanonicalPartition, ↓reduceIte]
  · cases hb : partition j
    · have hs : j ∈ side := by
        rw [← fiber]
        simp only [exactLeft, ne_eq, mem_insert, hj, mem_filter, mem_univ, not_false_eq_true, hb,
          and_self, or_true]
      simp only [exactReverseAliceCanonicalPartition, hj, ↓reduceIte, hs]
    · have hs : j ∉ side := by
        rw [← fiber]
        simp only [exactLeft, ne_eq, mem_insert, hj, mem_filter, mem_univ, not_false_eq_true, hb,
          Bool.true_eq_false, and_false, or_self]
      simp only [exactReverseAliceCanonicalPartition, hj, ↓reduceIte, hs]

private def exactReverseAlicePartitionFiberEquiv
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) :
    {partition : M → Bool //
      insert coordinate (exactLeft coordinate partition) = side} ≃
        Bool where
  toFun partition := partition.val coordinate
  invFun ignored :=
    ⟨exactReverseAliceCanonicalPartition side coordinate ignored,
      exactReverseAliceCanonicalPartition_side
        side coordinate member ignored⟩
  left_inv partition := by
    apply Subtype.ext
    exact (exactReverseAliceCanonicalPartition_unique
      side coordinate partition.val partition.property).symm
  right_inv ignored := by
    simp only [exactReverseAliceCanonicalPartition, ↓reduceIte]

private def exactReverseBobCanonicalPartition
    {M : Type*} [DecidableEq M]
    (side : Finset M) (coordinate : M) (ignored : Bool) : M → Bool :=
  fun j => if j = coordinate then ignored
    else if j ∈ side then true else false

theorem exactReverseBobCanonicalPartition_side
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) (ignored : Bool) :
    insert coordinate
        (exactRight coordinate
          (exactReverseBobCanonicalPartition
            side coordinate ignored)) = side := by
  ext j
  by_cases hj : j = coordinate
  · subst j
    simp only [mem_insert, true_or, member]
  · by_cases hs : j ∈ side <;>
      simp [exactRight,
        exactReverseBobCanonicalPartition,
        hj, hs]

theorem exactReverseBobCanonicalPartition_unique
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (partition : M → Bool)
    (fiber : insert coordinate
      (exactRight coordinate partition) = side) :
    partition = exactReverseBobCanonicalPartition
      side coordinate (partition coordinate) := by
  funext j
  by_cases hj : j = coordinate
  · subst j
    simp only [exactReverseBobCanonicalPartition, ↓reduceIte]
  · cases hb : partition j
    · have hs : j ∉ side := by
        rw [← fiber]
        simp only [exactRight, ne_eq, mem_insert, hj, mem_filter, mem_univ, not_false_eq_true, hb,
          Bool.false_eq_true, and_false, or_self]
      simp only [exactReverseBobCanonicalPartition, hj, ↓reduceIte, hs]
    · have hs : j ∈ side := by
        rw [← fiber]
        simp only [exactRight, ne_eq, mem_insert, hj, mem_filter, mem_univ, not_false_eq_true, hb,
          and_self, or_true]
      simp only [exactReverseBobCanonicalPartition, hj, ↓reduceIte, hs]

private def exactReverseBobPartitionFiberEquiv
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) :
    {partition : M → Bool //
      insert coordinate (exactRight coordinate partition) = side} ≃
        Bool where
  toFun partition := partition.val coordinate
  invFun ignored :=
    ⟨exactReverseBobCanonicalPartition side coordinate ignored,
      exactReverseBobCanonicalPartition_side
        side coordinate member ignored⟩
  left_inv partition := by
    apply Subtype.ext
    exact (exactReverseBobCanonicalPartition_unique
      side coordinate partition.val partition.property).symm
  right_inv ignored := by
    simp only [exactReverseBobCanonicalPartition, ↓reduceIte]

theorem exactReverseAlicePartitionFiber_card
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) :
    Fintype.card
      {partition : M → Bool //
        insert coordinate
          (exactLeft coordinate partition) = side} = 2 := by
  simpa only [Fintype.card_bool] using Fintype.card_congr
    (exactReverseAlicePartitionFiberEquiv
      side coordinate member)

theorem exactReverseBobPartitionFiber_card
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) :
    Fintype.card
      {partition : M → Bool //
        insert coordinate
          (exactRight coordinate partition) = side} = 2 := by
  simpa only [Fintype.card_bool] using Fintype.card_congr
    (exactReverseBobPartitionFiberEquiv
      side coordinate member)

theorem exactFiniteIndicator_sum
    {T : Type*} [Fintype T]
    (predicate : T → Prop) [DecidablePred predicate]
    (weight : ℝ) :
    (∑ t : T, if predicate t then weight else 0) =
      (Fintype.card {t : T // predicate t} : ℝ) * weight := by
  classical
  calc
    (∑ t : T, if predicate t then weight else 0) =
        (∑ t : T, if predicate t then (1 : ℝ) else 0) * weight := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro t _
          split_ifs <;> simp
    _ = (Fintype.card {t : T // predicate t} : ℝ) * weight := by
      simp only [sum_boole, Fintype.card_subtype]

theorem exactReverseAlicePartitionFiber_sum
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) (weight : ℝ) :
    (∑ partition : M → Bool,
      if insert coordinate
          (exactLeft coordinate partition) = side
      then weight else 0) = 2 * weight := by
  rw [exactFiniteIndicator_sum]
  rw [exactReverseAlicePartitionFiber_card
    side coordinate member]
  norm_num

theorem exactReverseBobPartitionFiber_sum
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) (weight : ℝ) :
    (∑ partition : M → Bool,
      if insert coordinate
          (exactRight coordinate partition) = side
      then weight else 0) = 2 * weight := by
  rw [exactFiniteIndicator_sum]
  rw [exactReverseBobPartitionFiber_card
    side coordinate member]
  norm_num

theorem exactReversePartition_orderCut_sum
    {M : Type*} [Fintype M] [DecidableEq M]
    (coordinate : M) (partition : M → Bool) :
    (∑ leftOrder : Equiv.Perm
        {j : M // j ∈ exactLeft coordinate partition},
      ∑ rightOrder : Equiv.Perm
        {j : M // j ∈ exactRight coordinate partition},
      ∑ leftCut : Fin
        ((exactLeft coordinate partition).card + 1),
      ∑ rightCut : Fin
        ((exactRight coordinate partition).card + 1),
        exactSeedWeight
          ⟨coordinate, partition,
            leftOrder, rightOrder, leftCut, rightCut⟩) =
      (1 / (Fintype.card M : ℝ)) *
        (1 / (Fintype.card (M → Bool) : ℝ)) := by
  simp only [exactSeedWeight,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_perm, Fintype.card_coe,
    Fintype.card_fin, Nat.cast_add, Nat.cast_one]
  have hleft :
      (0 : ℝ) < ((exactLeft coordinate partition).card + 1) := by
    exact_mod_cast Nat.zero_lt_succ _
  have hright :
      (0 : ℝ) < ((exactRight coordinate partition).card + 1) := by
    exact_mod_cast Nat.zero_lt_succ _
  have hleft_factorial :
      (0 : ℝ) <
        ((exactLeft coordinate partition).card.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have hright_factorial :
      (0 : ℝ) <
        ((exactRight coordinate partition).card.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  field_simp [hleft.ne', hright.ne',
    hleft_factorial.ne', hright_factorial.ne']

theorem exactReverseAlicePartition_orderCut_fiber_sum
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M) (partition : M → Bool) :
    (∑ leftOrder : Equiv.Perm
        {j : M // j ∈ exactLeft coordinate partition},
      ∑ rightOrder : Equiv.Perm
        {j : M // j ∈ exactRight coordinate partition},
      ∑ leftCut : Fin
        ((exactLeft coordinate partition).card + 1),
      ∑ rightCut : Fin
        ((exactRight coordinate partition).card + 1),
        if exactReverseLeftSide
              (⟨coordinate, partition,
                leftOrder, rightOrder, leftCut, rightCut⟩ :
                  ExactForwardSeed M) = side
        then exactSeedWeight
          ⟨coordinate, partition,
            leftOrder, rightOrder, leftCut, rightCut⟩
        else 0) =
      if insert coordinate
          (exactLeft coordinate partition) = side
      then (1 / (Fintype.card M : ℝ)) *
        (1 / (Fintype.card (M → Bool) : ℝ))
      else 0 := by
  by_cases hside :
      insert coordinate
        (exactLeft coordinate partition) = side
  · simpa only [exactReverseLeftSide, hside, ↓reduceIte, one_div, Fintype.card_pi,
      Fintype.card_bool, prod_const, card_univ, Nat.cast_pow, Nat.cast_ofNat] using
      exactReversePartition_orderCut_sum coordinate partition
  · simp only [exactReverseLeftSide, hside, ↓reduceIte, sum_const_zero]

theorem exactReverseBobPartition_orderCut_fiber_sum
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M) (partition : M → Bool) :
    (∑ leftOrder : Equiv.Perm
        {j : M // j ∈ exactLeft coordinate partition},
      ∑ rightOrder : Equiv.Perm
        {j : M // j ∈ exactRight coordinate partition},
      ∑ leftCut : Fin
        ((exactLeft coordinate partition).card + 1),
      ∑ rightCut : Fin
        ((exactRight coordinate partition).card + 1),
        if exactReverseRightSide
              (⟨coordinate, partition,
                leftOrder, rightOrder, leftCut, rightCut⟩ :
                  ExactForwardSeed M) = side
        then exactSeedWeight
          ⟨coordinate, partition,
            leftOrder, rightOrder, leftCut, rightCut⟩
        else 0) =
      if insert coordinate
          (exactRight coordinate partition) = side
      then (1 / (Fintype.card M : ℝ)) *
        (1 / (Fintype.card (M → Bool) : ℝ))
      else 0 := by
  by_cases hside :
      insert coordinate
        (exactRight coordinate partition) = side
  · simpa only [exactReverseRightSide, hside, ↓reduceIte, one_div, Fintype.card_pi,
      Fintype.card_bool, prod_const, card_univ, Nat.cast_pow, Nat.cast_ofNat] using
      exactReversePartition_orderCut_sum coordinate partition
  · simp only [exactReverseRightSide, hside, ↓reduceIte, sum_const_zero]

theorem exactReverseAliceSide_marginal
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) :
    groupedMass exactReverseLeftSide
        exactSeedWeight side =
      reversePartitionWeight side := by
  classical
  unfold groupedMass
  rw [Finset.sum_filter, exactForwardSeed_sum]
  simp_rw [exactReverseAlicePartition_orderCut_fiber_sum]
  have hcoordinate (coordinate : M) :
      (∑ partition : M → Bool,
        if insert coordinate
            (exactLeft coordinate partition) = side
        then (1 / (Fintype.card M : ℝ)) *
          (1 / (Fintype.card (M → Bool) : ℝ))
        else 0) =
      if coordinate ∈ side
      then 2 * ((1 / (Fintype.card M : ℝ)) *
        (1 / (Fintype.card (M → Bool) : ℝ)))
      else 0 := by
    by_cases hmember : coordinate ∈ side
    · simp only [hmember, ↓reduceIte]
      exact exactReverseAlicePartitionFiber_sum
        side coordinate hmember
        ((1 / (Fintype.card M : ℝ)) *
          (1 / (Fintype.card (M → Bool) : ℝ)))
    · simp only [hmember, ↓reduceIte]
      apply Finset.sum_eq_zero
      intro partition _
      have hnot :
          insert coordinate
            (exactLeft coordinate partition) ≠ side := by
        intro h
        apply hmember
        rw [← h]
        exact Finset.mem_insert_self _ _
      simp only [hnot, ↓reduceIte]
  simp_rw [hcoordinate]
  rw [exactFiniteIndicator_sum]
  simp only [Fintype.card_coe, Fintype.card_fun,
    Fintype.card_bool, reversePartitionWeight,
    fairPartitionWeight, Nat.cast_pow]
  ring

theorem exactReverseBobSide_marginal
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) :
    groupedMass exactReverseRightSide
        exactSeedWeight side =
      reversePartitionWeight side := by
  classical
  unfold groupedMass
  rw [Finset.sum_filter, exactForwardSeed_sum]
  simp_rw [exactReverseBobPartition_orderCut_fiber_sum]
  have hcoordinate (coordinate : M) :
      (∑ partition : M → Bool,
        if insert coordinate
            (exactRight coordinate partition) = side
        then (1 / (Fintype.card M : ℝ)) *
          (1 / (Fintype.card (M → Bool) : ℝ))
        else 0) =
      if coordinate ∈ side
      then 2 * ((1 / (Fintype.card M : ℝ)) *
        (1 / (Fintype.card (M → Bool) : ℝ)))
      else 0 := by
    by_cases hmember : coordinate ∈ side
    · simp only [hmember, ↓reduceIte]
      exact exactReverseBobPartitionFiber_sum
        side coordinate hmember
        ((1 / (Fintype.card M : ℝ)) *
          (1 / (Fintype.card (M → Bool) : ℝ)))
    · simp only [hmember, ↓reduceIte]
      apply Finset.sum_eq_zero
      intro partition _
      have hnot :
          insert coordinate
            (exactRight coordinate partition) ≠ side := by
        intro h
        apply hmember
        rw [← h]
        exact Finset.mem_insert_self _ _
      simp only [hnot, ↓reduceIte]
  simp_rw [hcoordinate]
  rw [exactFiniteIndicator_sum]
  simp only [Fintype.card_coe, Fintype.card_fun,
    Fintype.card_bool, reversePartitionWeight,
    fairPartitionWeight, Nat.cast_pow]
  ring

/-- The probability weight for exact reverse alice conditional seed. -/
def exactReverseAliceConditionalSeedWeight
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (seed : ExactForwardSeed M) : ℝ :=
  if exactReverseLeftSide seed = side then
    exactSeedWeight seed / reversePartitionWeight side
  else 0

/-- The probability weight for exact reverse bob conditional seed. -/
def exactReverseBobConditionalSeedWeight
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (seed : ExactForwardSeed M) : ℝ :=
  if exactReverseRightSide seed = side then
    exactSeedWeight seed / reversePartitionWeight side
  else 0

theorem exactReverseAliceConditionalSeedWeight_nonneg
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (seed : ExactForwardSeed M) :
    0 ≤ exactReverseAliceConditionalSeedWeight side seed := by
  unfold exactReverseAliceConditionalSeedWeight
  split_ifs
  · exact div_nonneg (exactSeedWeight_nonneg seed)
      (reversePartitionWeight_nonneg side)
  · exact le_rfl

theorem exactReverseBobConditionalSeedWeight_nonneg
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (seed : ExactForwardSeed M) :
    0 ≤ exactReverseBobConditionalSeedWeight side seed := by
  unfold exactReverseBobConditionalSeedWeight
  split_ifs
  · exact div_nonneg (exactSeedWeight_nonneg seed)
      (reversePartitionWeight_nonneg side)
  · exact le_rfl

theorem exactReverseAliceConditionalSeedWeight_cancel
    {M : Type*} [Fintype M] [DecidableEq M]
    (nonempty : 0 < Fintype.card M)
    (side : Finset M) (seed : ExactForwardSeed M) :
    reversePartitionWeight side *
        exactReverseAliceConditionalSeedWeight side seed =
      if exactReverseLeftSide seed = side
      then exactSeedWeight seed else 0 := by
  by_cases hs : exactReverseLeftSide seed = side
  · subst side
    have hpositive :
        0 < reversePartitionWeight
          (exactReverseLeftSide seed) :=
      (reversePartitionWeight_pos_iff nonempty
        (exactReverseLeftSide seed)).mpr
          ⟨seed.coordinate,
            exactReverseLeftSide_coordinate_mem seed⟩
    simp only [exactReverseAliceConditionalSeedWeight,
      ↓reduceIte]
    field_simp [hpositive.ne']
  · simp only [exactReverseAliceConditionalSeedWeight, hs, ↓reduceIte, mul_zero]

theorem exactReverseBobConditionalSeedWeight_cancel
    {M : Type*} [Fintype M] [DecidableEq M]
    (nonempty : 0 < Fintype.card M)
    (side : Finset M) (seed : ExactForwardSeed M) :
    reversePartitionWeight side *
        exactReverseBobConditionalSeedWeight side seed =
      if exactReverseRightSide seed = side
      then exactSeedWeight seed else 0 := by
  by_cases hs : exactReverseRightSide seed = side
  · subst side
    have hpositive :
        0 < reversePartitionWeight
          (exactReverseRightSide seed) :=
      (reversePartitionWeight_pos_iff nonempty
        (exactReverseRightSide seed)).mpr
          ⟨seed.coordinate,
            exactReverseRightSide_coordinate_mem seed⟩
    simp only [exactReverseBobConditionalSeedWeight,
      ↓reduceIte]
    field_simp [hpositive.ne']
  · simp only [exactReverseBobConditionalSeedWeight, hs, ↓reduceIte, mul_zero]

theorem exactReverseAliceConditionalSeedWeight_sum
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (nonempty : side.Nonempty) :
    (∑ seed : ExactForwardSeed M,
      exactReverseAliceConditionalSeedWeight side seed) = 1 := by
  have hM : 0 < Fintype.card M :=
    Fintype.card_pos_iff.mpr ⟨nonempty.choose⟩
  have hside : 0 < reversePartitionWeight side :=
    (reversePartitionWeight_pos_iff hM side).mpr nonempty
  calc
    (∑ seed : ExactForwardSeed M,
        exactReverseAliceConditionalSeedWeight side seed) =
      (∑ seed : ExactForwardSeed M,
        if exactReverseLeftSide seed = side
        then exactSeedWeight seed else 0) /
          reversePartitionWeight side := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro seed _
            unfold exactReverseAliceConditionalSeedWeight
            split_ifs <;> simp
    _ = groupedMass exactReverseLeftSide
        exactSeedWeight side /
          reversePartitionWeight side := by
            unfold groupedMass
            rw [Finset.sum_filter]
    _ = 1 := by
      rw [exactReverseAliceSide_marginal]
      exact div_self hside.ne'

theorem exactReverseBobConditionalSeedWeight_sum
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (nonempty : side.Nonempty) :
    (∑ seed : ExactForwardSeed M,
      exactReverseBobConditionalSeedWeight side seed) = 1 := by
  have hM : 0 < Fintype.card M :=
    Fintype.card_pos_iff.mpr ⟨nonempty.choose⟩
  have hside : 0 < reversePartitionWeight side :=
    (reversePartitionWeight_pos_iff hM side).mpr nonempty
  calc
    (∑ seed : ExactForwardSeed M,
        exactReverseBobConditionalSeedWeight side seed) =
      (∑ seed : ExactForwardSeed M,
        if exactReverseRightSide seed = side
        then exactSeedWeight seed else 0) /
          reversePartitionWeight side := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro seed _
            unfold exactReverseBobConditionalSeedWeight
            split_ifs <;> simp
    _ = groupedMass exactReverseRightSide
        exactSeedWeight side /
          reversePartitionWeight side := by
            unfold groupedMass
            rw [Finset.sum_filter]
    _ = 1 := by
      rw [exactReverseBobSide_marginal]
      exact div_self hside.ne'

private def exactForwardSeedLaw
    {M : Type*} [Fintype M] [DecidableEq M]
    (nonempty : 0 < Fintype.card M) :
    FiniteEventLaw (ExactForwardSeed M) where
  weight := exactSeedWeight
  weight_nonneg := exactSeedWeight_nonneg
  weight_sum := exactSeedWeight_sum nonempty

/-- The finite probability law for exact reverse alice conditional seed. -/
def exactReverseAliceConditionalSeedLaw
    {M : Type*} [Fintype M] [DecidableEq M]
    (nonempty : 0 < Fintype.card M)
    (side : Finset M) :
    FiniteEventLaw (ExactForwardSeed M) :=
  if hside : side.Nonempty then
    { weight := exactReverseAliceConditionalSeedWeight side
      weight_nonneg :=
        exactReverseAliceConditionalSeedWeight_nonneg side
      weight_sum :=
        exactReverseAliceConditionalSeedWeight_sum side hside }
  else exactForwardSeedLaw nonempty

/-- The finite probability law for exact reverse bob conditional seed. -/
def exactReverseBobConditionalSeedLaw
    {M : Type*} [Fintype M] [DecidableEq M]
    (nonempty : 0 < Fintype.card M)
    (side : Finset M) :
    FiniteEventLaw (ExactForwardSeed M) :=
  if hside : side.Nonempty then
    { weight := exactReverseBobConditionalSeedWeight side
      weight_nonneg :=
        exactReverseBobConditionalSeedWeight_nonneg side
      weight_sum :=
        exactReverseBobConditionalSeedWeight_sum side hside }
  else exactForwardSeedLaw nonempty

@[simp] theorem exactReverseAliceConditionalSeedLaw_weight
    {M : Type*} [Fintype M] [DecidableEq M]
    (nonempty : 0 < Fintype.card M)
    (side : Finset M) (hside : side.Nonempty)
    (seed : ExactForwardSeed M) :
    (exactReverseAliceConditionalSeedLaw
      nonempty side).weight seed =
      exactReverseAliceConditionalSeedWeight side seed := by
  simp only [exactReverseAliceConditionalSeedLaw, hside, ↓reduceDIte]

@[simp] theorem exactReverseBobConditionalSeedLaw_weight
    {M : Type*} [Fintype M] [DecidableEq M]
    (nonempty : 0 < Fintype.card M)
    (side : Finset M) (hside : side.Nonempty)
    (seed : ExactForwardSeed M) :
    (exactReverseBobConditionalSeedLaw
      nonempty side).weight seed =
      exactReverseBobConditionalSeedWeight side seed := by
  simp only [exactReverseBobConditionalSeedLaw, hside, ↓reduceDIte]

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The finite probability law for reweighted seed prior event. -/
def reweightedSeedPriorEventLaw
    {K : Type*} [Fintype K]
    (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n)) :
    FiniteEventLaw (K × ExactOutcome X Y A B n) where
  weight q := seedLaw.weight q.1 *
    (strategyEventLaw (G.repeat n) S).weight q.2
  weight_nonneg q := mul_nonneg
    (seedLaw.weight_nonneg q.1)
    ((strategyEventLaw (G.repeat n) S).weight_nonneg q.2)
  weight_sum := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum,
      (strategyEventLaw (G.repeat n) S).weight_sum, mul_one]
    exact seedLaw.weight_sum

/-- The reweighted seed win event construction used in the quantum parallel-repetition argument. -/
def reweightedSeedWinEvent
    {K : Type*} [Fintype K]
    (G : Game X Y A B) (n : ℕ) (D : Finset (Fin n)) :
    Finset (K × ExactOutcome X Y A B n) :=
  Finset.univ.filter
    (fun q : K × ExactOutcome X Y A B n =>
      q.2 ∈ FiniteEventLaw.winEvent
        (repeatedCoordinateWin G n) D)

theorem reweightedSeedWinEventMass
    {K : Type*} [Fintype K]
    (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :
    (reweightedSeedPriorEventLaw seedLaw G n S).eventMass
        (reweightedSeedWinEvent (K := K) G n D) =
      repeatedPostselectionMass G n S D := by
  classical
  let event := FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D
  let original := strategyEventLaw (G.repeat n) S
  change
    (∑ q ∈ (Finset.univ.filter
      (fun q : K × ExactOutcome X Y A B n => q.2 ∈ event)),
        seedLaw.weight q.1 * original.weight q.2) =
      ∑ outcome ∈ event, original.weight outcome
  simp only [Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  have hinner (k : K) :
      (∑ outcome : ExactOutcome X Y A B n,
        if outcome ∈ event
        then seedLaw.weight k * original.weight outcome
        else 0) =
      seedLaw.weight k *
        (∑ outcome : ExactOutcome X Y A B n,
          if outcome ∈ event then original.weight outcome else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro outcome _
    split_ifs <;> simp
  simp_rw [hinner]
  rw [← Finset.sum_mul, seedLaw.weight_sum]
  simp only [sum_ite_mem, univ_inter, one_mul]

/-- The reweighted seed posterior construction used in the quantum parallel-repetition argument. -/
def reweightedSeedPosterior
    {K : Type*} [Fintype K]
    (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) :
    K × ExactOutcome X Y A B n → ℝ :=
  conditionedEventDistribution
    (reweightedSeedPriorEventLaw seedLaw G n S)
    (reweightedSeedWinEvent (K := K) G n D)

theorem reweightedSeedPosterior_eq_product
    {K : Type*} [Fintype K]
    (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (q : K × ExactOutcome X Y A B n) :
    reweightedSeedPosterior seedLaw G n S D q =
      seedLaw.weight q.1 *
        repeatedConditionedOutcomeLaw G n S D q.2 := by
  classical
  let event := FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D
  have hmass := reweightedSeedWinEventMass
    seedLaw G n S D
  by_cases hq : q.2 ∈ event
  · have hlift :
        q ∈ reweightedSeedWinEvent (K := K) G n D := by
      simpa only [reweightedSeedWinEvent, mem_filter, mem_univ, true_and] using hq
    unfold reweightedSeedPosterior
      repeatedConditionedOutcomeLaw
      conditionedEventDistribution
    rw [ite_eq_left hlift, ite_eq_left hq]
    change
      (seedLaw.weight q.1 *
        (strategyEventLaw (G.repeat n) S).weight q.2) /
          (reweightedSeedPriorEventLaw seedLaw G n S).eventMass
            (reweightedSeedWinEvent (K := K) G n D) =
        seedLaw.weight q.1 *
          ((strategyEventLaw (G.repeat n) S).weight q.2 /
            repeatedPostselectionMass G n S D)
    rw [hmass]
    ring
  · have hlift :
        q ∉ reweightedSeedWinEvent (K := K) G n D := by
      simpa only [reweightedSeedWinEvent, mem_filter, mem_univ, true_and] using hq
    change q.2 ∉
      FiniteEventLaw.winEvent (repeatedCoordinateWin G n) D at hq
    simp only [reweightedSeedPosterior, conditionedEventDistribution, hlift, ↓reduceIte,
      repeatedConditionedOutcomeLaw, hq, mul_zero]

theorem reweightedSeedProjection_relativeEntropy_le
    {K U : Type*} [Fintype K] [Fintype U]
    (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (projection : K × ExactOutcome X Y A B n → U) :
    finiteRelativeEntropy
        (groupedMass projection
          (reweightedSeedPosterior seedLaw G n S D))
        (groupedMass projection
          (reweightedSeedPriorEventLaw seedLaw G n S).weight) ≤
      postselectionLogCost G n S D := by
  let law := reweightedSeedPriorEventLaw seedLaw G n S
  let event := reweightedSeedWinEvent (K := K) G n D
  have hpositive : 0 < law.eventMass event := by
    change
      0 < (reweightedSeedPriorEventLaw seedLaw G n S).eventMass
        (reweightedSeedWinEvent (K := K) G n D)
    rw [reweightedSeedWinEventMass]
    exact positive
  change
    finiteRelativeEntropy
      (groupedMass projection
        (conditionedEventDistribution law event))
      (groupedMass projection law.weight) ≤ _
  calc
    finiteRelativeEntropy
        (groupedMass projection
          (conditionedEventDistribution law event))
        (groupedMass projection law.weight) ≤
      Real.log (1 / law.eventMass event) :=
      conditionedEventDistribution_projection_relativeEntropy_le
        law event hpositive projection
    _ = postselectionLogCost G n S D := by
      change
        Real.log
          (1 / (reweightedSeedPriorEventLaw
            seedLaw G n S).eventMass
            (reweightedSeedWinEvent (K := K) G n D)) = _
      rw [reweightedSeedWinEventMass]
      rfl

/-- The finite probability law for reweighted seed flagged projection. -/
def reweightedSeedFlaggedProjectionLaw
    {K U Z : Type*} [Fintype K]
    (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (projection : K × ExactOutcome X Y A B n → U)
    (flag : K × ExactOutcome X Y A B n → Z) :
    U × Z → ℝ :=
  groupedMass (fun q => (projection q, flag q))
    (reweightedSeedPosterior seedLaw G n S D)

theorem reweightedSeedFlaggedProjectionLaw_firstMarginal
    {K U Z : Type*} [Fintype K] [Finite U] [Fintype Z]
    (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (projection : K × ExactOutcome X Y A B n → U)
    (flag : K × ExactOutcome X Y A B n → Z) :
    jointFirstMarginal
      (reweightedSeedFlaggedProjectionLaw
        seedLaw G n S D projection flag) =
      groupedMass projection
        (reweightedSeedPosterior seedLaw G n S D) := by
  let _ := Fintype.ofFinite U
  rw [← groupedMass_first]
  unfold reweightedSeedFlaggedProjectionLaw
  rw [groupedMass_comp]
  rfl

theorem reweightedSeed_flagged_projection_relativeEntropy_le
    {K U Z : Type*} [Fintype K] [Fintype U] [Fintype Z]
    (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (flag_positive : 0 < Fintype.card Z)
    (projection : K × ExactOutcome X Y A B n → U)
    (flag : K × ExactOutcome X Y A B n → Z) :
    finiteRelativeEntropy
        (reweightedSeedFlaggedProjectionLaw
          seedLaw G n S D projection flag)
        (uniformFlagReference (Z := Z)
          (groupedMass projection
            (reweightedSeedPriorEventLaw seedLaw G n S).weight)) ≤
      postselectionLogCost G n S D +
        Real.log (Fintype.card Z : ℝ) := by
  let law := reweightedSeedPriorEventLaw seedLaw G n S
  let event := reweightedSeedWinEvent (K := K) G n D
  let posterior := reweightedSeedPosterior seedLaw G n S D
  let joint := reweightedSeedFlaggedProjectionLaw
    seedLaw G n S D projection flag
  let projectedPrior := groupedMass projection law.weight
  have hevent : 0 < law.eventMass event := by
    change
      0 < (reweightedSeedPriorEventLaw seedLaw G n S).eventMass
        (reweightedSeedWinEvent (K := K) G n D)
    rw [reweightedSeedWinEventMass]
    exact positive
  have hposterior : ∀ q, 0 ≤ posterior q :=
    conditionedEventDistribution_nonneg law event hevent
  have hjoint : ∀ t, 0 ≤ joint t :=
    groupedMass_nonneg
      (fun q => (projection q, flag q)) posterior hposterior
  have hprojectedPrior : ∀ u, 0 ≤ projectedPrior u :=
    groupedMass_nonneg projection law.weight law.weight_nonneg
  have hjointnorm : (∑ t, joint t) = 1 := by
    change
      (∑ t,
        groupedMass (fun q => (projection q, flag q))
          (conditionedEventDistribution law event) t) = 1
    rw [groupedMass_sum]
    exact conditionedEventDistribution_sum law event hevent
  have hpriornorm : (∑ u, projectedPrior u) = 1 := by
    change (∑ u, groupedMass projection law.weight u) = 1
    rw [groupedMass_sum]
    exact law.weight_sum
  have hac :
      ∀ u, projectedPrior u = 0 →
        jointFirstMarginal joint u = 0 := by
    intro u hzero
    change
      jointFirstMarginal
        (reweightedSeedFlaggedProjectionLaw
          seedLaw G n S D projection flag) u = 0
    rw [reweightedSeedFlaggedProjectionLaw_firstMarginal]
    exact groupedMass_absolute_continuity
      projection
      (conditionedEventDistribution law event)
      law.weight law.weight_nonneg
      (conditionedEventDistribution_absolute_continuity
        law event) u hzero
  calc
    finiteRelativeEntropy
        (reweightedSeedFlaggedProjectionLaw
          seedLaw G n S D projection flag)
        (uniformFlagReference (Z := Z)
          (groupedMass projection
            (reweightedSeedPriorEventLaw seedLaw G n S).weight)) ≤
      finiteRelativeEntropy
        (jointFirstMarginal joint) projectedPrior +
          Real.log (Fintype.card Z : ℝ) :=
      uniformFlagRelativeEntropy_le
        joint projectedPrior hjoint hprojectedPrior
        hjointnorm hpriornorm hac flag_positive
    _ = finiteRelativeEntropy
        (groupedMass projection
          (reweightedSeedPosterior seedLaw G n S D))
        (groupedMass projection
          (reweightedSeedPriorEventLaw seedLaw G n S).weight) +
          Real.log (Fintype.card Z : ℝ) := by
      rw [reweightedSeedFlaggedProjectionLaw_firstMarginal]
    _ ≤ postselectionLogCost G n S D +
          Real.log (Fintype.card Z : ℝ) := by
      gcongr
      exact reweightedSeedProjection_relativeEntropy_le
        seedLaw G n S D positive projection

theorem reweightedSeed_source_equation_twenty_five
    {K U : Type*} [Fintype K] [Fintype U]
    (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (projection : K × ExactOutcome X Y A B n → U) :
    finiteRelativeEntropy
        (reweightedSeedFlaggedProjectionLaw
          seedLaw G n S D projection
          (fun q =>
            repeatedConditionedAnswerFlag G n S D q.2))
        (uniformFlagReference
          (Z := ConditionedAnswerFlag A B D)
          (groupedMass projection
            (reweightedSeedPriorEventLaw seedLaw G n S).weight)) ≤
      postselectionLogCost G n S D +
        answerLogCost (A := A) (B := B) D := by
  have h := reweightedSeed_flagged_projection_relativeEntropy_le
    seedLaw G n S D positive
    (conditionedAnswerFlag_card_pos G n S D positive)
    projection
    (fun q => repeatedConditionedAnswerFlag G n S D q.2)
  rw [conditionedAnswerFlag_log_card
    G n S D positive] at h
  exact h

/--
The reweighted seed prefix joint construction used in the quantum parallel-repetition argument.
-/
def reweightedSeedPrefixJoint
    {K Ω V : Type*} [Fintype K]
    {h : ℕ} (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (projection : K × ExactOutcome X Y A B n →
      Ω × (Fin h → V)) :
    ((Ω × ConditionedAnswerFlag A B D) ×
      (Fin h → V)) → ℝ :=
  fun t => reweightedSeedFlaggedProjectionLaw
    seedLaw G n S D projection
    (fun q => repeatedConditionedAnswerFlag G n S D q.2)
    ((exactSourcePrefixFlagEquiv
      (Ω := Ω) (V := V)
      (Z := ConditionedAnswerFlag A B D)).symm t)

/--
The reweighted seed prefix prior construction used in the quantum parallel-repetition argument.
-/
def reweightedSeedPrefixPrior
    {K Ω V : Type*} [Fintype K]
    {h : ℕ} (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (projection : K × ExactOutcome X Y A B n →
      Ω × (Fin h → V)) :
    ((Ω × ConditionedAnswerFlag A B D) ×
      (Fin h → V)) → ℝ :=
  fun t => uniformFlagReference
    (Z := ConditionedAnswerFlag A B D)
    (groupedMass projection
      (reweightedSeedPriorEventLaw seedLaw G n S).weight)
    ((exactSourcePrefixFlagEquiv
      (Ω := Ω) (V := V)
      (Z := ConditionedAnswerFlag A B D)).symm t)

theorem reweightedSeedPrefixJoint_nonneg
    {K Ω V : Type*} [Fintype K]
    {h : ℕ} (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (projection : K × ExactOutcome X Y A B n →
      Ω × (Fin h → V))
    (t : (Ω × ConditionedAnswerFlag A B D) ×
      (Fin h → V)) :
    0 ≤ reweightedSeedPrefixJoint
      seedLaw G n S D projection t := by
  unfold reweightedSeedPrefixJoint
    reweightedSeedFlaggedProjectionLaw groupedMass
  apply Finset.sum_nonneg
  intro q _
  unfold reweightedSeedPosterior
  apply conditionedEventDistribution_nonneg
  rw [reweightedSeedWinEventMass]
  exact positive

theorem reweightedSeedPrefixPrior_nonneg
    {K Ω V : Type*} [Fintype K]
    {h : ℕ} (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (projection : K × ExactOutcome X Y A B n →
      Ω × (Fin h → V))
    (t : (Ω × ConditionedAnswerFlag A B D) ×
      (Fin h → V)) :
    0 ≤ reweightedSeedPrefixPrior
      seedLaw G n S D projection t := by
  unfold reweightedSeedPrefixPrior
  apply uniformFlagReference_nonneg
  · exact groupedMass_nonneg projection
      (reweightedSeedPriorEventLaw seedLaw G n S).weight
      (reweightedSeedPriorEventLaw seedLaw G n S).weight_nonneg
  · exact conditionedAnswerFlag_card_pos G n S D positive

/-- The information increment contributed by reweighted seed prefix entropy. -/
def reweightedSeedPrefixEntropyIncrement
    {K Ω V : Type*} [Fintype K] [Fintype Ω] [Fintype V]
    {h : ℕ} (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (projection : K × ExactOutcome X Y A B n →
      Ω × (Fin h → V))
    (default : V) (k : Fin h) : ℝ :=
  finitePrefixRelativeEntropy
      (reweightedSeedPrefixJoint
        seedLaw G n S D projection)
      (reweightedSeedPrefixPrior
        seedLaw G n S D projection)
      default k.succ -
    finitePrefixRelativeEntropy
      (reweightedSeedPrefixJoint
        seedLaw G n S D projection)
      (reweightedSeedPrefixPrior
        seedLaw G n S D projection)
      default k.castSucc

theorem reweightedSeed_source_equation_twenty_six
    {K Ω V : Type*} [Fintype K] [Fintype Ω] [Fintype V]
    {h : ℕ} (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (projection : K × ExactOutcome X Y A B n →
      Ω × (Fin h → V))
    (default : V) :
    (∑ k : Fin h,
      reweightedSeedPrefixEntropyIncrement
        seedLaw G n S D projection default k) ≤
      postselectionLogCost G n S D +
        answerLogCost (A := A) (B := B) D := by
  let e := exactSourcePrefixFlagEquiv
    (Ω := Ω) (V := V) (h := h)
    (Z := ConditionedAnswerFlag A B D)
  let joint := reweightedSeedPrefixJoint
    seedLaw G n S D projection
  let prior := reweightedSeedPrefixPrior
    seedLaw G n S D projection
  calc
    (∑ k : Fin h,
      reweightedSeedPrefixEntropyIncrement
        seedLaw G n S D projection default k) ≤
      finiteRelativeEntropy joint prior := by
        exact finitePrefixRelativeEntropy_budget joint prior
          (reweightedSeedPrefixJoint_nonneg
            seedLaw G n S D positive projection)
          (reweightedSeedPrefixPrior_nonneg
            seedLaw G n S D positive projection)
          default
    _ = finiteRelativeEntropy
      (reweightedSeedFlaggedProjectionLaw
        seedLaw G n S D projection
        (fun q =>
          repeatedConditionedAnswerFlag G n S D q.2))
      (uniformFlagReference
        (Z := ConditionedAnswerFlag A B D)
        (groupedMass projection
          (reweightedSeedPriorEventLaw seedLaw G n S).weight)) := by
        exact exactFiniteRelativeEntropy_equiv e
          (reweightedSeedFlaggedProjectionLaw
            seedLaw G n S D projection
            (fun q =>
              repeatedConditionedAnswerFlag G n S D q.2))
          (uniformFlagReference
            (Z := ConditionedAnswerFlag A B D)
            (groupedMass projection
              (reweightedSeedPriorEventLaw seedLaw G n S).weight))
    _ ≤ postselectionLogCost G n S D +
        answerLogCost (A := A) (B := B) D := by
      convert reweightedSeed_source_equation_twenty_five
        seedLaw G n S D positive projection using 1
      congr 1
      congr 1
      exact exactGroupedMass_decidableEq_irrel _ _
        projection
        (reweightedSeedPriorEventLaw seedLaw G n S).weight

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem reweightedSeedPrefixJoint_sum
    {K Ω V : Type*} [Fintype K] [Fintype Ω] [Fintype V]
    {h : ℕ} (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (projection : K × ExactOutcome X Y A B n →
      Ω × (Fin h → V)) :
    (∑ t,
      reweightedSeedPrefixJoint
        seedLaw G n S D projection t) = 1 := by
  let e := exactSourcePrefixFlagEquiv
    (Ω := Ω) (V := V) (h := h)
    (Z := ConditionedAnswerFlag A B D)
  let law := reweightedSeedPriorEventLaw seedLaw G n S
  let event := reweightedSeedWinEvent (K := K) G n D
  have hevent : 0 < law.eventMass event := by
    change
      0 < (reweightedSeedPriorEventLaw seedLaw G n S).eventMass
        (reweightedSeedWinEvent (K := K) G n D)
    rw [reweightedSeedWinEventMass]
    exact positive
  change
    (∑ t,
      reweightedSeedFlaggedProjectionLaw
        seedLaw G n S D projection
        (fun q => repeatedConditionedAnswerFlag G n S D q.2)
        (e.symm t)) = 1
  rw [e.symm.sum_comp]
  unfold reweightedSeedFlaggedProjectionLaw
  convert
    (groupedMass_sum
      (fun q : K × ExactOutcome X Y A B n =>
        (projection q,
          repeatedConditionedAnswerFlag G n S D q.2))
      (conditionedEventDistribution law event)).trans
      (conditionedEventDistribution_sum law event hevent) using 1
  apply Finset.sum_congr (by ext; simp only [mem_univ])
  intro t _
  exact congrFun
    (exactGroupedMass_decidableEq_irrel _ _
      (fun q : K × ExactOutcome X Y A B n =>
        (projection q,
          repeatedConditionedAnswerFlag G n S D q.2))
      (conditionedEventDistribution law event)) t

theorem reweightedSeedPrefixPrior_sum
    {K Ω V : Type*} [Fintype K] [Fintype Ω] [Fintype V]
    {h : ℕ} (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (projection : K × ExactOutcome X Y A B n →
      Ω × (Fin h → V)) :
    (∑ t,
      reweightedSeedPrefixPrior
        seedLaw G n S D projection t) = 1 := by
  let e := exactSourcePrefixFlagEquiv
    (Ω := Ω) (V := V) (h := h)
    (Z := ConditionedAnswerFlag A B D)
  let law := reweightedSeedPriorEventLaw seedLaw G n S
  change
    (∑ t,
      uniformFlagReference
        (Z := ConditionedAnswerFlag A B D)
        (groupedMass projection law.weight)
        (e.symm t)) = 1
  rw [e.symm.sum_comp]
  apply uniformFlagReference_sum
  · rw [groupedMass_sum]
    exact law.weight_sum
  · exact conditionedAnswerFlag_card_pos G n S D positive

theorem reweightedSeedPrefix_absolute_continuity
    {K Ω V : Type*} [Fintype K] [Finite Ω] [Finite V]
    {h : ℕ} (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (projection : K × ExactOutcome X Y A B n →
      Ω × (Fin h → V))
    (t : (Ω × ConditionedAnswerFlag A B D) ×
      (Fin h → V)) :
    reweightedSeedPrefixPrior
        seedLaw G n S D projection t = 0 →
      reweightedSeedPrefixJoint
        seedLaw G n S D projection t = 0 := by
  let _ := Fintype.ofFinite Ω
  let _ := Fintype.ofFinite V
  let e := exactSourcePrefixFlagEquiv
    (Ω := Ω) (V := V) (h := h)
    (Z := ConditionedAnswerFlag A B D)
  let law := reweightedSeedPriorEventLaw seedLaw G n S
  let event := reweightedSeedWinEvent (K := K) G n D
  have hevent : 0 < law.eventMass event := by
    change
      0 < (reweightedSeedPriorEventLaw seedLaw G n S).eventMass
        (reweightedSeedWinEvent (K := K) G n D)
    rw [reweightedSeedWinEventMass]
    exact positive
  change
    uniformFlagReference
        (Z := ConditionedAnswerFlag A B D)
        (groupedMass projection law.weight)
        (e.symm t) = 0 →
      reweightedSeedFlaggedProjectionLaw
        seedLaw G n S D projection
        (fun q => repeatedConditionedAnswerFlag G n S D q.2)
        (e.symm t) = 0
  apply uniformFlagReference_absolute_continuity
    (reweightedSeedFlaggedProjectionLaw
      seedLaw G n S D projection
      (fun q => repeatedConditionedAnswerFlag G n S D q.2))
    (groupedMass projection law.weight)
  · intro a
    unfold reweightedSeedFlaggedProjectionLaw groupedMass
    apply Finset.sum_nonneg
    intro q _
    exact conditionedEventDistribution_nonneg
      law event hevent q
  · intro u hzero
    rw [reweightedSeedFlaggedProjectionLaw_firstMarginal]
    convert groupedMass_absolute_continuity
      projection (conditionedEventDistribution law event)
      law.weight law.weight_nonneg
      (conditionedEventDistribution_absolute_continuity
        law event) u hzero using 1
    exact congrFun
      (exactGroupedMass_decidableEq_irrel _ _
        projection
        (conditionedEventDistribution law event)) u
  · exact conditionedAnswerFlag_card_pos G n S D positive

theorem reweightedSeedPrefixEntropyIncrement_eq_conditional
    {K Ω V : Type*} [Fintype K] [Fintype Ω] [Fintype V]
    {h : ℕ} (seedLaw : FiniteEventLaw K)
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (projection : K × ExactOutcome X Y A B n →
      Ω × (Fin h → V))
    (default : V) (k : Fin h) :
    reweightedSeedPrefixEntropyIncrement
        seedLaw G n S D projection default k =
      ∑ context :
        (Ω × ConditionedAnswerFlag A B D) × (Fin h → V),
        groupedMass
            (finitePrefixMask default k.castSucc)
            (reweightedSeedPrefixJoint
              seedLaw G n S D projection)
            context *
          finiteRelativeEntropy
            (jointConditional
              (groupedMass
                (exactPrefixNextCode default k)
                (reweightedSeedPrefixJoint
                  seedLaw G n S D projection))
              context)
            (jointConditional
              (groupedMass
                (exactPrefixNextCode default k)
                (reweightedSeedPrefixPrior
                  seedLaw G n S D projection))
              context) := by
  change
    finitePrefixRelativeEntropy
        (reweightedSeedPrefixJoint
          seedLaw G n S D projection)
        (reweightedSeedPrefixPrior
          seedLaw G n S D projection)
        default k.succ -
      finitePrefixRelativeEntropy
        (reweightedSeedPrefixJoint
          seedLaw G n S D projection)
        (reweightedSeedPrefixPrior
          seedLaw G n S D projection)
        default k.castSucc = _
  convert exactPrefixEntropyIncrement_eq_conditional
    (reweightedSeedPrefixJoint
      seedLaw G n S D projection)
    (reweightedSeedPrefixPrior
      seedLaw G n S D projection)
    (reweightedSeedPrefixJoint_nonneg
      seedLaw G n S D positive projection)
    (reweightedSeedPrefixPrior_nonneg
      seedLaw G n S D positive projection)
    (reweightedSeedPrefix_absolute_continuity
      seedLaw G n S D positive projection)
    (reweightedSeedPrefixJoint_sum
      seedLaw G n S D positive projection)
    (reweightedSeedPrefixPrior_sum
      seedLaw G n S D positive projection)
    default k using 1
  apply Finset.sum_congr rfl
  intro context _
  congr 1
  · exact congrFun
      (exactGroupedMass_decidableEq_irrel _ _
        (finitePrefixMask default k.castSucc)
        (reweightedSeedPrefixJoint
          seedLaw G n S D projection)) context
  · congr 1
    · congr 1
      exact exactGroupedMass_decidableEq_irrel _ _
        (exactPrefixNextCode default k)
        (reweightedSeedPrefixJoint
          seedLaw G n S D projection)
    · congr 1
      exact exactGroupedMass_decidableEq_irrel _ _
        (exactPrefixNextCode default k)
        (reweightedSeedPrefixPrior
          seedLaw G n S D projection)

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

theorem exactReverseAliceConditionalSeedLaw_weight_cancel
    {M : Type*} [Fintype M] [DecidableEq M]
    (nonempty : 0 < Fintype.card M)
    (side : Finset M) (seed : ExactForwardSeed M) :
    reversePartitionWeight side *
        (exactReverseAliceConditionalSeedLaw
          nonempty side).weight seed =
      if exactReverseLeftSide seed = side
      then exactSeedWeight seed else 0 := by
  by_cases hside : side.Nonempty
  · rw [exactReverseAliceConditionalSeedLaw_weight
      nonempty side hside seed]
    exact exactReverseAliceConditionalSeedWeight_cancel
      nonempty side seed
  · have hempty : side = ∅ := Finset.not_nonempty_iff_eq_empty.mp hside
    subst side
    simp only [reversePartitionWeight_empty, exactReverseAliceConditionalSeedLaw,
      Finset.not_nonempty_empty, ↓reduceDIte, zero_mul, exactReverseLeftSide, insert_ne_empty,
      ↓reduceIte]

theorem exactReverseBobConditionalSeedLaw_weight_cancel
    {M : Type*} [Fintype M] [DecidableEq M]
    (nonempty : 0 < Fintype.card M)
    (side : Finset M) (seed : ExactForwardSeed M) :
    reversePartitionWeight side *
        (exactReverseBobConditionalSeedLaw
          nonempty side).weight seed =
      if exactReverseRightSide seed = side
      then exactSeedWeight seed else 0 := by
  by_cases hside : side.Nonempty
  · rw [exactReverseBobConditionalSeedLaw_weight
      nonempty side hside seed]
    exact exactReverseBobConditionalSeedWeight_cancel
      nonempty side seed
  · have hempty : side = ∅ := Finset.not_nonempty_iff_eq_empty.mp hside
    subst side
    simp only [reversePartitionWeight_empty, exactReverseBobConditionalSeedLaw,
      Finset.not_nonempty_empty, ↓reduceDIte, zero_mul, exactReverseRightSide, insert_ne_empty,
      ↓reduceIte]

private def exactReverseSideContextWeight
    {M : Type*} [Fintype M] [DecidableEq M]
    {side : Finset M}
    (context : ExactReverseSideContext M side) : ℝ :=
  (1 / (2 : ℝ)) *
    (1 / (Fintype.card
      (Equiv.Perm {j : M // j ∈ side}) : ℝ)) *
    (1 / (Fintype.card
      (Equiv.Perm {j : M // j ∈ context.otherSide}) : ℝ)) *
    (1 / (context.otherSide.card + 1 : ℝ))

theorem exactReverseAliceConditionalSeedWeight_eq_context_div_card
    {M : Type*} [Fintype M] [DecidableEq M]
    (nonempty : 0 < Fintype.card M)
    (seed : ExactForwardSeed M) :
    exactReverseAliceConditionalSeedWeight
        (exactReverseLeftSide seed) seed =
      exactReverseSideContextWeight
        (exactReverseAliceContext seed) /
        ((exactReverseLeftSide seed).card : ℝ) := by
  have hside :
      0 < reversePartitionWeight
        (exactReverseLeftSide seed) :=
    (reversePartitionWeight_pos_iff nonempty
      (exactReverseLeftSide seed)).mpr
      ⟨seed.coordinate,
        exactReverseLeftSide_coordinate_mem seed⟩
  unfold exactReverseAliceConditionalSeedWeight
  rw [ite_eq_left rfl]
  rw [← exactReverseLeftSeedWeight_eq_forward seed]
  unfold exactReverseLeftSeedWeight
    exactReverseSideContextWeight
    exactReverseAliceContext
    reverseMarkedPartitionWeight
  rw [ite_eq_left (exactReverseLeftSide_coordinate_mem seed)]
  field_simp [hside.ne']

theorem exactReverseBobConditionalSeedWeight_eq_context_div_card
    {M : Type*} [Fintype M] [DecidableEq M]
    (nonempty : 0 < Fintype.card M)
    (seed : ExactForwardSeed M) :
    exactReverseBobConditionalSeedWeight
        (exactReverseRightSide seed) seed =
      exactReverseSideContextWeight
        (exactReverseBobContext seed) /
        ((exactReverseRightSide seed).card : ℝ) := by
  have hside :
      0 < reversePartitionWeight
        (exactReverseRightSide seed) :=
    (reversePartitionWeight_pos_iff nonempty
      (exactReverseRightSide seed)).mpr
      ⟨seed.coordinate,
        exactReverseRightSide_coordinate_mem seed⟩
  unfold exactReverseBobConditionalSeedWeight
  rw [ite_eq_left rfl]
  rw [← exactReverseRightSeedWeight_eq_forward seed]
  unfold exactReverseRightSeedWeight
    exactReverseSideContextWeight
    exactReverseBobContext
    reverseMarkedPartitionWeight
  rw [ite_eq_left (exactReverseRightSide_coordinate_mem seed)]
  field_simp [hside.ne']

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

/-- The finite encoding of exact reverse alice marker. -/
def exactReverseAliceMarkerCode
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    Σ side : Finset M,
      ExactReverseSideContext M side × Fin side.card :=
  ⟨exactReverseLeftSide seed,
    exactReverseAliceContext seed,
    (exactReverseAliceContext seed).sideRank
      ⟨seed.coordinate,
        exactReverseLeftSide_coordinate_mem seed⟩⟩

/-- The finite encoding of exact reverse bob marker. -/
def exactReverseBobMarkerCode
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    Σ side : Finset M,
      ExactReverseSideContext M side × Fin side.card :=
  ⟨exactReverseRightSide seed,
    exactReverseBobContext seed,
    (exactReverseBobContext seed).sideRank
      ⟨seed.coordinate,
        exactReverseRightSide_coordinate_mem seed⟩⟩

@[simp] theorem exactReverseAliceMarkerCode_coordinate
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    (((exactReverseAliceMarkerCode seed).2.1.sideRank).symm
      (exactReverseAliceMarkerCode seed).2.2).val =
      seed.coordinate := by
  change
    ((exactReverseAliceContext seed).sideRank.symm
      ((exactReverseAliceContext seed).sideRank
        ⟨seed.coordinate, exactReverseLeftSide_coordinate_mem seed⟩)).val =
      seed.coordinate
  exact congrArg Subtype.val
    ((exactReverseAliceContext seed).sideRank.symm_apply_apply
      ⟨seed.coordinate, exactReverseLeftSide_coordinate_mem seed⟩)

@[simp] theorem exactReverseBobMarkerCode_coordinate
    {M : Type*} [Fintype M] [DecidableEq M]
    (seed : ExactForwardSeed M) :
    (((exactReverseBobMarkerCode seed).2.1.sideRank).symm
      (exactReverseBobMarkerCode seed).2.2).val =
      seed.coordinate := by
  change
    ((exactReverseBobContext seed).sideRank.symm
      ((exactReverseBobContext seed).sideRank
        ⟨seed.coordinate, exactReverseRightSide_coordinate_mem seed⟩)).val =
      seed.coordinate
  exact congrArg Subtype.val
    ((exactReverseBobContext seed).sideRank.symm_apply_apply
      ⟨seed.coordinate, exactReverseRightSide_coordinate_mem seed⟩)

theorem exactReverseAliceMarkerCode_coordinate_injective
    {M : Type*} [Fintype M] [DecidableEq M]
    {a b : ExactForwardSeed M}
    (same : exactReverseAliceMarkerCode a =
      exactReverseAliceMarkerCode b) :
    a.coordinate = b.coordinate := by
  have h := congrArg
    (fun t : Σ side : Finset M,
      ExactReverseSideContext M side × Fin side.card =>
      (t.2.1.sideRank.symm t.2.2).val) same
  simpa only [exactReverseAliceMarkerCode_coordinate] using h

theorem exactReverseBobMarkerCode_coordinate_injective
    {M : Type*} [Fintype M] [DecidableEq M]
    {a b : ExactForwardSeed M}
    (same : exactReverseBobMarkerCode a =
      exactReverseBobMarkerCode b) :
    a.coordinate = b.coordinate := by
  have h := congrArg
    (fun t : Σ side : Finset M,
      ExactReverseSideContext M side × Fin side.card =>
      (t.2.1.sideRank.symm t.2.2).val) same
  simpa only [exactReverseBobMarkerCode_coordinate] using h

theorem exactReverseAliceMarkerCode_partition_injective
    {M : Type*} [Fintype M] [DecidableEq M]
    {a b : ExactForwardSeed M}
    (same : exactReverseAliceMarkerCode a =
      exactReverseAliceMarkerCode b) :
    a.partition = b.partition := by
  have hcoordinate :=
    exactReverseAliceMarkerCode_coordinate_injective same
  have hside :
      exactReverseLeftSide a =
        exactReverseLeftSide b :=
    congrArg Sigma.fst same
  have hbit : a.partition a.coordinate = b.partition b.coordinate := by
    have h := congrArg
      (fun t : Σ side : Finset M,
        ExactReverseSideContext M side × Fin side.card =>
        t.2.1.ignoredBit) same
    exact h
  funext j
  by_cases hj : j = a.coordinate
  · subst j
    simpa only [hcoordinate] using hbit
  · have hbj : j ≠ b.coordinate := by
      simpa only [ne_eq, hcoordinate] using hj
    have hm :
        (a.partition j = false) ↔ (b.partition j = false) := by
      have := Finset.ext_iff.mp hside j
      simpa only [Bool.coe_false_iff_false, Bool.not_eq_eq_eq_not, Bool.not_not,
        exactReverseLeftSide, exactLeft, ne_eq, mem_insert, hj, mem_filter, mem_univ,
        not_false_eq_true, true_and, false_or, hbj] using this
    cases ha : a.partition j <;>
      cases hb : b.partition j <;>
      simp_all

theorem exactReverseBobMarkerCode_partition_injective
    {M : Type*} [Fintype M] [DecidableEq M]
    {a b : ExactForwardSeed M}
    (same : exactReverseBobMarkerCode a =
      exactReverseBobMarkerCode b) :
    a.partition = b.partition := by
  have hcoordinate :=
    exactReverseBobMarkerCode_coordinate_injective same
  have hside :
      exactReverseRightSide a =
        exactReverseRightSide b :=
    congrArg Sigma.fst same
  have hbit : a.partition a.coordinate = b.partition b.coordinate := by
    have h := congrArg
      (fun t : Σ side : Finset M,
        ExactReverseSideContext M side × Fin side.card =>
        t.2.1.ignoredBit) same
    exact h
  funext j
  by_cases hj : j = a.coordinate
  · subst j
    simpa only [hcoordinate] using hbit
  · have hbj : j ≠ b.coordinate := by
      simpa only [ne_eq, hcoordinate] using hj
    have hm :
        (a.partition j = true) ↔ (b.partition j = true) := by
      have := Finset.ext_iff.mp hside j
      simpa only [Bool.coe_iff_coe, exactReverseRightSide, exactRight, ne_eq, mem_insert, hj,
        mem_filter, mem_univ, not_false_eq_true, true_and, false_or, hbj] using this
    cases ha : a.partition j <;>
      cases hb : b.partition j <;>
      simp_all

theorem exactReverseAliceMarkerCode_injective
    {M : Type*} [Fintype M] [DecidableEq M] :
    Function.Injective (exactReverseAliceMarkerCode (M := M)) := by
  intro a b same
  have hcoordinate :=
    exactReverseAliceMarkerCode_coordinate_injective same
  have hpartition :=
    exactReverseAliceMarkerCode_partition_injective same
  rcases a with ⟨i, p, l, r, lc, rc⟩
  rcases b with ⟨j, q, l', r', lc', rc'⟩
  dsimp at hcoordinate hpartition
  subst j
  subst q
  simp only [exactReverseAliceMarkerCode, Sigma.mk.inj_iff] at same
  have hpair := eq_of_heq same.2
  have hctx := congrArg Prod.fst hpair
  have hmarked := congrArg Prod.snd hpair
  have hleftCut : lc = lc' := by
    apply Fin.ext
    have hv := congrArg Fin.val hmarked
    exact
      (exactReverseAliceContext_marked_rank
        ({ coordinate := i, partition := p, leftOrder := l,
           rightOrder := r, leftCut := lc, rightCut := rc } :
          ExactForwardSeed M)).symm.trans
        (hv.trans
          (exactReverseAliceContext_marked_rank
            ({ coordinate := i, partition := p, leftOrder := l',
               rightOrder := r', leftCut := lc', rightCut := rc' } :
              ExactForwardSeed M)))
  have hrightCut : rc = rc' := by
    apply Fin.ext
    have hv := congrArg
      (fun c : ExactReverseSideContext M
        (exactReverseLeftSide
          ({ coordinate := i, partition := p, leftOrder := l,
             rightOrder := r, leftCut := lc, rightCut := rc } :
            ExactForwardSeed M)) => c.otherCut.val) hctx
    exact hv
  subst lc'
  subst rc'
  change
    exactReverseAliceContext
        ({ coordinate := i, partition := p, leftOrder := l,
           rightOrder := r, leftCut := lc, rightCut := rc } :
          ExactForwardSeed M) =
      exactReverseAliceContext
        ({ coordinate := i, partition := p, leftOrder := l',
           rightOrder := r', leftCut := lc, rightCut := rc } :
          ExactForwardSeed M) at hctx
  have hsideRank := congrArg
    (fun c : ExactReverseSideContext M
      (exactReverseLeftSide
        ({ coordinate := i, partition := p, leftOrder := l,
           rightOrder := r, leftCut := lc, rightCut := rc } :
          ExactForwardSeed M)) => c.sideRank) hctx
  have hotherRankSigma := congrArg
    (fun c : ExactReverseSideContext M
      (exactReverseLeftSide
        ({ coordinate := i, partition := p, leftOrder := l,
           rightOrder := r, leftCut := lc, rightCut := rc } :
          ExactForwardSeed M)) =>
      (⟨c.otherSide, c.otherRank⟩ :
        Σ other : Finset M,
          ({j : M // j ∈ other} ≃ Fin other.card))) hctx
  simp only [exactReverseAliceContext,
    Sigma.mk.inj_iff] at hotherRankSigma
  have hotherRank := eq_of_heq hotherRankSigma.2
  have hrightSymm : r.symm = r'.symm := by
    have h := congrArg
      (fun e :
        ({j : M // j ∈ exactRight i p} ≃
          Fin (exactRight i p).card) =>
        e.trans (Finset.equivFin (exactRight i p)).symm)
      hotherRank
    simpa only [exactRightRank, Equiv.trans_assoc, Equiv.self_trans_symm,
      Equiv.trans_refl] using h
  have hright : r = r' := Equiv.symm_bijective.injective hrightSymm
  subst r'
  have hreverseLeftRank :
      exactReverseLeftRank
          ({ coordinate := i, partition := p, leftOrder := l,
             rightOrder := r, leftCut := lc, rightCut := rc } :
            ExactForwardSeed M) =
        exactReverseLeftRank
          ({ coordinate := i, partition := p, leftOrder := l',
             rightOrder := r, leftCut := lc, rightCut := rc } :
            ExactForwardSeed M) := by
    apply Equiv.ext
    intro j
    apply Fin.ext
    have hsideVal
        (seed : ExactForwardSeed M)
        (k : {k : M // k ∈ exactReverseLeftSide seed}) :
        ((exactReverseAliceContext seed).sideRank k).val =
          (exactReverseLeftRank seed k).val := by
      simp only [exactReverseAliceContext, Equiv.trans_apply,
        finCongr_apply, Fin.val_cast]
    have h := congrArg
      (fun e => (e j).val) hsideRank
    exact
      (hsideVal
        ({ coordinate := i, partition := p, leftOrder := l,
           rightOrder := r, leftCut := lc, rightCut := rc } :
          ExactForwardSeed M) j).symm.trans
        (h.trans
          (hsideVal
            ({ coordinate := i, partition := p, leftOrder := l',
               rightOrder := r, leftCut := lc, rightCut := rc } :
              ExactForwardSeed M) j))
  have hleftRank :
      exactLeftRank
          ({ coordinate := i, partition := p, leftOrder := l,
             rightOrder := r, leftCut := lc, rightCut := rc } :
            ExactForwardSeed M) =
        exactLeftRank
          ({ coordinate := i, partition := p, leftOrder := l',
             rightOrder := r, leftCut := lc, rightCut := rc } :
            ExactForwardSeed M) := by
    apply Equiv.ext
    intro j
    let j' :
        {j : M //
          j ∈ exactLeft i p} := ⟨j.val, j.property⟩
    have h := congrArg
      (fun e => e
        ⟨j.val, Finset.mem_insert_of_mem j.property⟩)
      hreverseLeftRank
    apply Fin.succAbove_right_injective
    exact
      (exactReverseLeftRank_old
        ({ coordinate := i, partition := p, leftOrder := l,
           rightOrder := r, leftCut := lc, rightCut := rc } :
          ExactForwardSeed M) j).symm.trans
        (h.trans
          (exactReverseLeftRank_old
            ({ coordinate := i, partition := p, leftOrder := l',
               rightOrder := r, leftCut := lc, rightCut := rc } :
              ExactForwardSeed M) j'))
  have hleftSymm : l.symm = l'.symm := by
    have h := congrArg
      (fun e :
        ({j : M // j ∈ exactLeft i p} ≃
          Fin (exactLeft i p).card) =>
        e.trans (Finset.equivFin (exactLeft i p)).symm)
      hleftRank
    simpa only [exactLeftRank, Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.trans_refl] using h
  have hleft : l = l' := Equiv.symm_bijective.injective hleftSymm
  subst l'
  rfl

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

theorem exactReverseBobMarkerCode_injective
    {M : Type*} [Fintype M] [DecidableEq M] :
    Function.Injective (exactReverseBobMarkerCode (M := M)) := by
  intro a b same
  have hcoordinate :=
    exactReverseBobMarkerCode_coordinate_injective same
  have hpartition :=
    exactReverseBobMarkerCode_partition_injective same
  rcases a with ⟨i, p, l, r, lc, rc⟩
  rcases b with ⟨j, q, l', r', lc', rc'⟩
  dsimp at hcoordinate hpartition
  subst j
  subst q
  simp only [exactReverseBobMarkerCode, Sigma.mk.inj_iff] at same
  have hpair := eq_of_heq same.2
  have hctx := congrArg Prod.fst hpair
  have hmarked := congrArg Prod.snd hpair
  have hrightCut : rc = rc' := by
    apply Fin.ext
    have hv := congrArg Fin.val hmarked
    exact
      (exactReverseBobContext_marked_rank
        ({ coordinate := i, partition := p, leftOrder := l,
           rightOrder := r, leftCut := lc, rightCut := rc } :
          ExactForwardSeed M)).symm.trans
        (hv.trans
          (exactReverseBobContext_marked_rank
            ({ coordinate := i, partition := p, leftOrder := l',
               rightOrder := r', leftCut := lc', rightCut := rc' } :
              ExactForwardSeed M)))
  have hleftCut : lc = lc' := by
    apply Fin.ext
    have hv := congrArg
      (fun c : ExactReverseSideContext M
        (exactReverseRightSide
          ({ coordinate := i, partition := p, leftOrder := l,
             rightOrder := r, leftCut := lc, rightCut := rc } :
            ExactForwardSeed M)) => c.otherCut.val) hctx
    exact hv
  subst rc'
  subst lc'
  change
    exactReverseBobContext
        ({ coordinate := i, partition := p, leftOrder := l,
           rightOrder := r, leftCut := lc, rightCut := rc } :
          ExactForwardSeed M) =
      exactReverseBobContext
        ({ coordinate := i, partition := p, leftOrder := l',
           rightOrder := r', leftCut := lc, rightCut := rc } :
          ExactForwardSeed M) at hctx
  have hsideRank := congrArg
    (fun c : ExactReverseSideContext M
      (exactReverseRightSide
        ({ coordinate := i, partition := p, leftOrder := l,
           rightOrder := r, leftCut := lc, rightCut := rc } :
          ExactForwardSeed M)) => c.sideRank) hctx
  have hotherRankSigma := congrArg
    (fun c : ExactReverseSideContext M
      (exactReverseRightSide
        ({ coordinate := i, partition := p, leftOrder := l,
           rightOrder := r, leftCut := lc, rightCut := rc } :
          ExactForwardSeed M)) =>
      (⟨c.otherSide, c.otherRank⟩ :
        Σ other : Finset M,
          ({j : M // j ∈ other} ≃ Fin other.card))) hctx
  simp only [exactReverseBobContext,
    Sigma.mk.inj_iff] at hotherRankSigma
  have hotherRank := eq_of_heq hotherRankSigma.2
  have hleftSymm : l.symm = l'.symm := by
    have h := congrArg
      (fun e :
        ({j : M // j ∈ exactLeft i p} ≃
          Fin (exactLeft i p).card) =>
        e.trans (Finset.equivFin (exactLeft i p)).symm)
      hotherRank
    simpa only [exactLeftRank, Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.trans_refl] using h
  have hleft : l = l' := Equiv.symm_bijective.injective hleftSymm
  subst l'
  have hreverseRightRank :
      exactReverseRightRank
          ({ coordinate := i, partition := p, leftOrder := l,
             rightOrder := r, leftCut := lc, rightCut := rc } :
            ExactForwardSeed M) =
        exactReverseRightRank
          ({ coordinate := i, partition := p, leftOrder := l,
             rightOrder := r', leftCut := lc, rightCut := rc } :
            ExactForwardSeed M) := by
    apply Equiv.ext
    intro j
    apply Fin.ext
    have hsideVal
        (seed : ExactForwardSeed M)
        (k : {k : M // k ∈ exactReverseRightSide seed}) :
        ((exactReverseBobContext seed).sideRank k).val =
          (exactReverseRightRank seed k).val := by
      simp only [exactReverseBobContext, Equiv.trans_apply,
        finCongr_apply, Fin.val_cast]
    have h := congrArg
      (fun e => (e j).val) hsideRank
    exact
      (hsideVal
        ({ coordinate := i, partition := p, leftOrder := l,
           rightOrder := r, leftCut := lc, rightCut := rc } :
          ExactForwardSeed M) j).symm.trans
        (h.trans
          (hsideVal
            ({ coordinate := i, partition := p, leftOrder := l,
               rightOrder := r', leftCut := lc, rightCut := rc } :
              ExactForwardSeed M) j))
  have hrightRank :
      exactRightRank
          ({ coordinate := i, partition := p, leftOrder := l,
             rightOrder := r, leftCut := lc, rightCut := rc } :
            ExactForwardSeed M) =
        exactRightRank
          ({ coordinate := i, partition := p, leftOrder := l,
             rightOrder := r', leftCut := lc, rightCut := rc } :
            ExactForwardSeed M) := by
    apply Equiv.ext
    intro j
    let j' :
        {j : M //
          j ∈ exactRight i p} := ⟨j.val, j.property⟩
    have h := congrArg
      (fun e => e
        ⟨j.val, Finset.mem_insert_of_mem j.property⟩)
      hreverseRightRank
    apply Fin.succAbove_right_injective
    exact
      (exactReverseRightRank_old
        ({ coordinate := i, partition := p, leftOrder := l,
           rightOrder := r, leftCut := lc, rightCut := rc } :
          ExactForwardSeed M) j).symm.trans
        (h.trans
          (exactReverseRightRank_old
            ({ coordinate := i, partition := p, leftOrder := l,
               rightOrder := r', leftCut := lc, rightCut := rc } :
              ExactForwardSeed M) j'))
  have hrightSymm : r.symm = r'.symm := by
    have h := congrArg
      (fun e :
        ({j : M // j ∈ exactRight i p} ≃
          Fin (exactRight i p).card) =>
        e.trans (Finset.equivFin (exactRight i p)).symm)
      hrightRank
    simpa only [exactRightRank, Equiv.trans_assoc, Equiv.self_trans_symm,
      Equiv.trans_refl] using h
  have hright : r = r' := Equiv.symm_bijective.injective hrightSymm
  subst r'
  rfl

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

private def exactInsertedOldSubtypeEquiv
    {M : Type*} [DecidableEq M]
    (i : M) (side : Finset M) (not_mem : i ∉ side) :
    {j : M // j ∈ side} ≃
      {j : {j : M // j ∈ insert i side} // j.val ≠ i} where
  toFun j :=
    ⟨⟨j.val, Finset.mem_insert_of_mem j.property⟩,
      fun same => not_mem (same ▸ j.property)⟩
  invFun j :=
    ⟨j.val.val, (Finset.mem_insert.mp j.val.property).resolve_left
      j.property⟩
  left_inv j := by
    apply Subtype.ext
    rfl
  right_inv j := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

private def exactDeleteMarkedRank
    {M : Type*} [DecidableEq M]
    (i : M) (side : Finset M) (not_mem : i ∉ side)
    (rank : {j : M // j ∈ insert i side} ≃
      Fin (side.card + 1))
    (cut : Fin (side.card + 1))
    (marked :
      rank ⟨i, Finset.mem_insert_self i side⟩ = cut) :
    {j : M // j ∈ side} ≃ Fin side.card :=
  (exactInsertedOldSubtypeEquiv i side not_mem).trans
    ((rank.subtypeEquiv (p := fun j => j.val ≠ i)
      (q := fun k => k ≠ cut)
      (by
        intro j
        constructor
        · intro distinct same
          apply distinct
          have hrank :
              rank j =
                rank ⟨i, Finset.mem_insert_self i side⟩ := by
            rw [marked]
            exact same
          exact congrArg Subtype.val (rank.injective hrank)
        · intro distinct same
          apply distinct
          have hj : j = ⟨i, Finset.mem_insert_self i side⟩ :=
            Subtype.ext same
          rw [hj, marked])).trans (finSuccAboveEquiv cut).symm)

theorem exactInsertedRank_deleteMarked
    {M : Type*} [DecidableEq M]
    (i : M) (side : Finset M) (not_mem : i ∉ side)
    (rank : {j : M // j ∈ insert i side} ≃
      Fin (side.card + 1))
    (cut : Fin (side.card + 1))
    (marked :
      rank ⟨i, Finset.mem_insert_self i side⟩ = cut) :
    exactInsertedRank i side not_mem
        (exactDeleteMarkedRank
          i side not_mem rank cut marked) cut = rank := by
  apply Equiv.ext
  intro j
  by_cases is_marker : j.val = i
  · have hj : j = ⟨i, Finset.mem_insert_self i side⟩ :=
      Subtype.ext is_marker
    rw [hj, exactInsertedRank_marker, marked]
  · have old_member : j.val ∈ side :=
      (Finset.mem_insert.mp j.property).resolve_left is_marker
    let old : {j : M // j ∈ side} := ⟨j.val, old_member⟩
    have hj :
        (⟨old.val, Finset.mem_insert_of_mem old.property⟩ :
          {j : M // j ∈ insert i side}) = j := by
      apply Subtype.ext
      rfl
    rw [← hj, exactInsertedRank_old]
    have distinct :
        rank ⟨old.val, Finset.mem_insert_of_mem old.property⟩ ≠ cut := by
      intro same
      apply is_marker
      have hrank :
          rank ⟨old.val, Finset.mem_insert_of_mem old.property⟩ =
            rank ⟨i, Finset.mem_insert_self i side⟩ := by
        rw [marked]
        exact same
      exact congrArg Subtype.val (rank.injective hrank)
    let deleted : {k : Fin (side.card + 1) // k ≠ cut} :=
      ⟨rank ⟨old.val, Finset.mem_insert_of_mem old.property⟩,
        distinct⟩
    have hdelete :
        exactDeleteMarkedRank
            i side not_mem rank cut marked old =
          (finSuccAboveEquiv cut).symm deleted := by
      rfl
    rw [hdelete]
    have h := (finSuccAboveEquiv cut).apply_symm_apply deleted
    exact congrArg Subtype.val h

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

private def exactPermutationOfSideRank
    {M : Type*}
    (side : Finset M)
    (rank : {j : M // j ∈ side} ≃ Fin side.card) :
    Equiv.Perm {j : M // j ∈ side} :=
  (rank.trans (Finset.equivFin side).symm).symm

theorem exactPermutationOfSideRank_rank
    {M : Type*}
    (side : Finset M)
    (rank : {j : M // j ∈ side} ≃ Fin side.card) :
    (exactPermutationOfSideRank side rank).symm.trans
      (Finset.equivFin side) = rank := by
  apply Equiv.ext
  intro j
  simp only [exactPermutationOfSideRank, Equiv.symm_trans, Equiv.symm_symm, Equiv.trans_apply,
    Equiv.apply_symm_apply]

theorem exactReverseAliceCanonicalPartition_otherSide
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) (ignored : Bool) :
    exactRight coordinate
        (exactReverseAliceCanonicalPartition
          side coordinate ignored) =
      Finset.univ \ side := by
  ext j
  by_cases marked : j = coordinate
  · subst j
    simp only [exactRight, ne_eq, mem_filter, mem_univ, not_true_eq_false, false_and, and_false,
      mem_sdiff, member]
  · by_cases belongs : j ∈ side <;>
      simp [exactRight,
        exactReverseAliceCanonicalPartition,
        marked, belongs]

theorem exactReverseBobCanonicalPartition_otherSide
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) (ignored : Bool) :
    exactLeft coordinate
        (exactReverseBobCanonicalPartition
          side coordinate ignored) =
      Finset.univ \ side := by
  ext j
  by_cases marked : j = coordinate
  · subst j
    simp only [exactLeft, ne_eq, mem_filter, mem_univ, not_true_eq_false, false_and, and_false,
      mem_sdiff, member]
  · by_cases belongs : j ∈ side <;>
      simp [exactLeft,
        exactReverseBobCanonicalPartition,
        marked, belongs]

theorem exactReverseAliceCanonicalPartition_card
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) (ignored : Bool) :
    (exactLeft coordinate
      (exactReverseAliceCanonicalPartition
        side coordinate ignored)).card + 1 = side.card := by
  have h := congrArg Finset.card
    (exactReverseAliceCanonicalPartition_side
      side coordinate member ignored)
  simpa only [exactLeft_coordinate_not_mem, not_false_eq_true, card_insert_of_notMem] using h

theorem exactReverseBobCanonicalPartition_card
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M) (coordinate : M)
    (member : coordinate ∈ side) (ignored : Bool) :
    (exactRight coordinate
      (exactReverseBobCanonicalPartition
        side coordinate ignored)).card + 1 = side.card := by
  have h := congrArg Finset.card
    (exactReverseBobCanonicalPartition_side
      side coordinate member ignored)
  simpa only [exactRight_coordinate_not_mem, not_false_eq_true, card_insert_of_notMem] using h

/--
The exact reverse alice marker decode construction used in the quantum parallel-repetition
argument.
-/
def exactReverseAliceMarkerDecode
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    ExactForwardSeed M := by
  classical
  let coordinate : M := (context.sideRank.symm marker).val
  have member : coordinate ∈ side :=
    (context.sideRank.symm marker).property
  let partition : M → Bool :=
    exactReverseAliceCanonicalPartition
      side coordinate context.ignoredBit
  have hside :
      insert coordinate (exactLeft coordinate partition) = side :=
    exactReverseAliceCanonicalPartition_side
      side coordinate member context.ignoredBit
  have hcard :
      (exactLeft coordinate partition).card + 1 = side.card :=
    exactReverseAliceCanonicalPartition_card
      side coordinate member context.ignoredBit
  let transportedSide :
      {j : M //
        j ∈ insert coordinate (exactLeft coordinate partition)} ≃
      {j : M // j ∈ side} :=
    Equiv.subtypeEquivRight (fun j => by rw [hside])
  let insertedRank :
      {j : M //
        j ∈ insert coordinate (exactLeft coordinate partition)} ≃
      Fin ((exactLeft coordinate partition).card + 1) :=
    transportedSide.trans
      (context.sideRank.trans (finCongr hcard.symm))
  let leftCut : Fin ((exactLeft coordinate partition).card + 1) :=
    (finCongr hcard.symm) marker
  have marked :
      insertedRank
          ⟨coordinate, Finset.mem_insert_self coordinate
            (exactLeft coordinate partition)⟩ = leftCut := by
    have transported :
        transportedSide
            ⟨coordinate, Finset.mem_insert_self coordinate
              (exactLeft coordinate partition)⟩ =
          context.sideRank.symm marker := by
      apply Subtype.ext
      rfl
    change
      (finCongr hcard.symm)
          (context.sideRank
            (transportedSide
              ⟨coordinate, Finset.mem_insert_self coordinate
                (exactLeft coordinate partition)⟩)) =
        (finCongr hcard.symm) marker
    rw [transported, Equiv.apply_symm_apply]
  let leftRank :
      {j : M // j ∈ exactLeft coordinate partition} ≃
        Fin (exactLeft coordinate partition).card :=
    exactDeleteMarkedRank coordinate
      (exactLeft coordinate partition)
      (exactLeft_coordinate_not_mem coordinate partition)
      insertedRank leftCut marked
  have hother :
      exactRight coordinate partition = context.otherSide := by
    calc
      exactRight coordinate partition =
          Finset.univ \ side :=
        exactReverseAliceCanonicalPartition_otherSide
          side coordinate member context.ignoredBit
      _ = context.otherSide := context.otherSide_eq_complement.symm
  let transportedOther :
      {j : M // j ∈ exactRight coordinate partition} ≃
        {j : M // j ∈ context.otherSide} :=
    Equiv.subtypeEquivRight (fun j => by rw [hother])
  let rightRank :
      {j : M // j ∈ exactRight coordinate partition} ≃
        Fin (exactRight coordinate partition).card :=
    transportedOther.trans
      (context.otherRank.trans
        (finCongr (congrArg Finset.card hother).symm))
  exact
    { coordinate := coordinate
      partition := partition
      leftOrder := exactPermutationOfSideRank
        (exactLeft coordinate partition) leftRank
      rightOrder := exactPermutationOfSideRank
        (exactRight coordinate partition) rightRank
      leftCut := leftCut
      rightCut :=
        (finCongr
          (congrArg (fun s : Finset M => s.card + 1) hother).symm)
          context.otherCut }

/--
The exact reverse bob marker decode construction used in the quantum parallel-repetition
argument.
-/
def exactReverseBobMarkerDecode
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    ExactForwardSeed M := by
  classical
  let coordinate : M := (context.sideRank.symm marker).val
  have member : coordinate ∈ side :=
    (context.sideRank.symm marker).property
  let partition : M → Bool :=
    exactReverseBobCanonicalPartition
      side coordinate context.ignoredBit
  have hside :
      insert coordinate (exactRight coordinate partition) = side :=
    exactReverseBobCanonicalPartition_side
      side coordinate member context.ignoredBit
  have hcard :
      (exactRight coordinate partition).card + 1 = side.card :=
    exactReverseBobCanonicalPartition_card
      side coordinate member context.ignoredBit
  let transportedSide :
      {j : M //
        j ∈ insert coordinate (exactRight coordinate partition)} ≃
      {j : M // j ∈ side} :=
    Equiv.subtypeEquivRight (fun j => by rw [hside])
  let insertedRank :
      {j : M //
        j ∈ insert coordinate (exactRight coordinate partition)} ≃
      Fin ((exactRight coordinate partition).card + 1) :=
    transportedSide.trans
      (context.sideRank.trans (finCongr hcard.symm))
  let rightCut : Fin ((exactRight coordinate partition).card + 1) :=
    (finCongr hcard.symm) marker
  have marked :
      insertedRank
          ⟨coordinate, Finset.mem_insert_self coordinate
            (exactRight coordinate partition)⟩ = rightCut := by
    have transported :
        transportedSide
            ⟨coordinate, Finset.mem_insert_self coordinate
              (exactRight coordinate partition)⟩ =
          context.sideRank.symm marker := by
      apply Subtype.ext
      rfl
    change
      (finCongr hcard.symm)
          (context.sideRank
            (transportedSide
              ⟨coordinate, Finset.mem_insert_self coordinate
                (exactRight coordinate partition)⟩)) =
        (finCongr hcard.symm) marker
    rw [transported, Equiv.apply_symm_apply]
  let rightRank :
      {j : M // j ∈ exactRight coordinate partition} ≃
        Fin (exactRight coordinate partition).card :=
    exactDeleteMarkedRank coordinate
      (exactRight coordinate partition)
      (exactRight_coordinate_not_mem coordinate partition)
      insertedRank rightCut marked
  have hother :
      exactLeft coordinate partition = context.otherSide := by
    calc
      exactLeft coordinate partition =
          Finset.univ \ side :=
        exactReverseBobCanonicalPartition_otherSide
          side coordinate member context.ignoredBit
      _ = context.otherSide := context.otherSide_eq_complement.symm
  let transportedOther :
      {j : M // j ∈ exactLeft coordinate partition} ≃
        {j : M // j ∈ context.otherSide} :=
    Equiv.subtypeEquivRight (fun j => by rw [hother])
  let leftRank :
      {j : M // j ∈ exactLeft coordinate partition} ≃
        Fin (exactLeft coordinate partition).card :=
    transportedOther.trans
      (context.otherRank.trans
        (finCongr (congrArg Finset.card hother).symm))
  exact
    { coordinate := coordinate
      partition := partition
      leftOrder := exactPermutationOfSideRank
        (exactLeft coordinate partition) leftRank
      rightOrder := exactPermutationOfSideRank
        (exactRight coordinate partition) rightRank
      leftCut :=
        (finCongr
          (congrArg (fun s : Finset M => s.card + 1) hother).symm)
          context.otherCut
      rightCut := rightCut }

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

@[simp] theorem exactReverseAliceMarkerDecode_coordinate
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    (exactReverseAliceMarkerDecode
      side context marker).coordinate =
      (context.sideRank.symm marker).val := by
  rfl

@[simp] theorem exactReverseBobMarkerDecode_coordinate
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    (exactReverseBobMarkerDecode
      side context marker).coordinate =
      (context.sideRank.symm marker).val := by
  rfl

@[simp] theorem exactReverseAliceMarkerDecode_side
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    exactReverseLeftSide
        (exactReverseAliceMarkerDecode
          side context marker) = side := by
  change
    insert (context.sideRank.symm marker).val
      (exactLeft (context.sideRank.symm marker).val
        (exactReverseAliceCanonicalPartition
          side (context.sideRank.symm marker).val
          context.ignoredBit)) = side
  exact exactReverseAliceCanonicalPartition_side
    side (context.sideRank.symm marker).val
    (context.sideRank.symm marker).property context.ignoredBit

@[simp] theorem exactReverseBobMarkerDecode_side
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    exactReverseRightSide
        (exactReverseBobMarkerDecode
          side context marker) = side := by
  change
    insert (context.sideRank.symm marker).val
      (exactRight (context.sideRank.symm marker).val
        (exactReverseBobCanonicalPartition
          side (context.sideRank.symm marker).val
          context.ignoredBit)) = side
  exact exactReverseBobCanonicalPartition_side
    side (context.sideRank.symm marker).val
    (context.sideRank.symm marker).property context.ignoredBit

@[simp] theorem exactReverseAliceMarkerDecode_ignoredBit
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    (exactReverseAliceMarkerDecode
      side context marker).partition
      (context.sideRank.symm marker).val = context.ignoredBit := by
  simp only [exactReverseAliceMarkerDecode, finCongr_apply, exactReverseAliceCanonicalPartition,
    ↓reduceIte]

@[simp] theorem exactReverseBobMarkerDecode_ignoredBit
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    (exactReverseBobMarkerDecode
      side context marker).partition
      (context.sideRank.symm marker).val = context.ignoredBit := by
  simp only [exactReverseBobMarkerDecode, finCongr_apply, exactReverseBobCanonicalPartition,
    ↓reduceIte]

theorem exactSigmaFinCutTransport
    {M : Type*}
    (source target : Finset M) (same : source = target)
    (cut : Fin (target.card + 1)) :
    (⟨source,
        (finCongr
          (congrArg (fun side : Finset M => side.card + 1) same).symm)
          cut⟩ : Σ side : Finset M, Fin (side.card + 1)) =
      ⟨target, cut⟩ := by
  subst target
  simp only [finCongr_refl, Equiv.refl_apply]

theorem exactSigmaSideRankTransport
    {M : Type*}
    (source target : Finset M) (same : source = target)
    (rank : {j : M // j ∈ target} ≃ Fin target.card) :
    (⟨source,
        (Equiv.subtypeEquivRight (fun j => by rw [same])).trans
          (rank.trans (finCongr (congrArg Finset.card same).symm))⟩ :
        Σ side : Finset M, ({j : M // j ∈ side} ≃ Fin side.card)) =
      ⟨target, rank⟩ := by
  subst target
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Equiv.ext
    intro j
    simp only [finCongr_refl, Equiv.trans_refl, Equiv.trans_apply, EmbeddingLike.apply_eq_iff_eq]
    apply Subtype.ext
    rfl

theorem exactReverseAliceMarkerDecode_otherRank
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    (⟨exactRight
        (exactReverseAliceMarkerDecode
          side context marker).coordinate
        (exactReverseAliceMarkerDecode
          side context marker).partition,
      exactRightRank
        (exactReverseAliceMarkerDecode
          side context marker)⟩ :
        Σ other : Finset M,
          ({j : M // j ∈ other} ≃ Fin other.card)) =
      ⟨context.otherSide, context.otherRank⟩ := by
  classical
  let coordinate := (context.sideRank.symm marker).val
  let partition :=
    exactReverseAliceCanonicalPartition
      side coordinate context.ignoredBit
  have other : exactRight coordinate partition =
      context.otherSide := by
    exact (exactReverseAliceCanonicalPartition_otherSide
      side coordinate (context.sideRank.symm marker).property
      context.ignoredBit).trans
        context.otherSide_eq_complement.symm
  have transported := exactSigmaSideRankTransport
    (exactRight coordinate partition)
    context.otherSide other context.otherRank
  simpa only [exactReverseAliceMarkerDecode,
    exactRightRank,
    exactPermutationOfSideRank_rank] using transported

theorem exactReverseAliceMarkerDecode_otherCut
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    (⟨exactRight
        (exactReverseAliceMarkerDecode
          side context marker).coordinate
        (exactReverseAliceMarkerDecode
          side context marker).partition,
      (exactReverseAliceMarkerDecode
        side context marker).rightCut⟩ :
        Σ other : Finset M, Fin (other.card + 1)) =
      ⟨context.otherSide, context.otherCut⟩ := by
  classical
  let coordinate := (context.sideRank.symm marker).val
  let partition :=
    exactReverseAliceCanonicalPartition
      side coordinate context.ignoredBit
  have other : exactRight coordinate partition =
      context.otherSide := by
    exact (exactReverseAliceCanonicalPartition_otherSide
      side coordinate (context.sideRank.symm marker).property
      context.ignoredBit).trans
        context.otherSide_eq_complement.symm
  have transported := exactSigmaFinCutTransport
    (exactRight coordinate partition)
    context.otherSide other context.otherCut
  simpa only [exactReverseAliceMarkerDecode] using transported

theorem exactReverseAliceMarkerDecode_sideRank
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    (⟨exactReverseLeftSide
        (exactReverseAliceMarkerDecode
          side context marker),
      (exactReverseAliceContext
        (exactReverseAliceMarkerDecode
          side context marker)).sideRank⟩ :
        Σ actualSide : Finset M,
          ({j : M // j ∈ actualSide} ≃ Fin actualSide.card)) =
      ⟨side, context.sideRank⟩ := by
  classical
  let coordinate := (context.sideRank.symm marker).val
  let partition :=
    exactReverseAliceCanonicalPartition
      side coordinate context.ignoredBit
  have actual : insert coordinate
      (exactLeft coordinate partition) = side :=
    exactReverseAliceCanonicalPartition_side
      side coordinate (context.sideRank.symm marker).property
      context.ignoredBit
  let transportedRank :
      {j : M //
        j ∈ insert coordinate (exactLeft coordinate partition)} ≃
        Fin (insert coordinate (exactLeft coordinate partition)).card :=
    (Equiv.subtypeEquivRight (fun j => by rw [actual])).trans
      (context.sideRank.trans
        (finCongr (congrArg Finset.card actual).symm))
  have transported :
      (⟨insert coordinate (exactLeft coordinate partition),
        transportedRank⟩ :
          Σ actualSide : Finset M,
            ({j : M // j ∈ actualSide} ≃ Fin actualSide.card)) =
        ⟨side, context.sideRank⟩ :=
    exactSigmaSideRankTransport
      (insert coordinate (exactLeft coordinate partition))
      side actual context.sideRank
  calc
    (⟨exactReverseLeftSide
        (exactReverseAliceMarkerDecode side context marker),
      (exactReverseAliceContext
        (exactReverseAliceMarkerDecode
          side context marker)).sideRank⟩ :
        Σ actualSide : Finset M,
          ({j : M // j ∈ actualSide} ≃ Fin actualSide.card)) =
        ⟨insert coordinate (exactLeft coordinate partition),
          transportedRank⟩ := by
            apply Sigma.ext
            · change
                insert (context.sideRank.symm marker).val
                    (exactLeft (context.sideRank.symm marker).val
                      (exactReverseAliceCanonicalPartition
                        side (context.sideRank.symm marker).val
                        context.ignoredBit)) =
                  insert coordinate (exactLeft coordinate partition)
              rfl
            · apply heq_of_eq
              dsimp only [exactReverseAliceMarkerDecode]
              simp only [exactReverseLeftSide,
                exactReverseAliceContext, exactReverseLeftRank, exactLeftRank,
                exactPermutationOfSideRank_rank]
              rw [exactInsertedRank_deleteMarked]
              apply Equiv.ext
              intro j
              apply Fin.ext
              simp only [finCongr_apply, Equiv.trans_apply, Fin.val_cast,
                transportedRank, coordinate, partition]
              rfl
    _ = ⟨side, context.sideRank⟩ := transported

theorem exactReverseAliceMarkerDecode_rightInverse
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    exactReverseAliceMarkerCode
        (exactReverseAliceMarkerDecode
          side context marker) =
      ⟨side, context, marker⟩ := by
  classical
  generalize decoded :
    exactReverseAliceMarkerDecode side context marker = seed
  have sameSide : exactReverseLeftSide seed = side := by
    rw [← decoded]
    exact exactReverseAliceMarkerDecode_side
      side context marker
  subst side
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    change
      (exactReverseAliceContext seed,
        (exactReverseAliceContext seed).sideRank
          ⟨seed.coordinate,
            exactReverseLeftSide_coordinate_mem seed⟩) =
        (context, marker)
    have sameContext : exactReverseAliceContext seed = context := by
      cases context with
      | mk otherSide sideRank otherRank otherCut ignored complement =>
        simp only [exactReverseAliceContext,
          ExactReverseSideContext.mk.injEq]
        let reverseContext : ExactReverseSideContext M
            (exactReverseLeftSide seed) :=
          { otherSide := otherSide
            sideRank := sideRank
            otherRank := otherRank
            otherCut := otherCut
            ignoredBit := ignored
            otherSide_eq_complement := complement }
        have exactSideRank :=
          exactReverseAliceMarkerDecode_sideRank
            (exactReverseLeftSide seed)
            reverseContext marker
        have exactOtherRank :=
          exactReverseAliceMarkerDecode_otherRank
            (exactReverseLeftSide seed)
            reverseContext marker
        have exactOtherCut :=
          exactReverseAliceMarkerDecode_otherCut
            (exactReverseLeftSide seed)
            reverseContext marker
        change
          exactReverseAliceMarkerDecode
              (exactReverseLeftSide seed)
              reverseContext marker = seed at decoded
        rw [decoded] at exactSideRank exactOtherRank exactOtherCut
        refine ⟨(exactReverseLeftSide_complement seed).trans
            complement.symm, ?_, ?_, ?_, ?_⟩
        · exact eq_of_heq (Sigma.mk.inj exactSideRank).2
        · exact (Sigma.mk.inj exactOtherRank).2
        · exact (Sigma.mk.inj exactOtherCut).2
        · have exactIgnored := congrArg
            (fun original : ExactForwardSeed M =>
              original.partition original.coordinate) decoded
          simpa only
            [exactReverseAliceMarkerDecode_coordinate,
              exactReverseAliceMarkerDecode_ignoredBit]
              using exactIgnored.symm
    apply Prod.ext
    · exact sameContext
    · rw [sameContext]
      apply context.sideRank.symm.injective
      change
        context.sideRank.symm
            (context.sideRank ⟨seed.coordinate, _⟩) =
          context.sideRank.symm marker
      rw [Equiv.symm_apply_apply]
      apply Subtype.ext
      have coordinate := congrArg
        (fun original : ExactForwardSeed M => original.coordinate)
        decoded
      simpa only [exactReverseAliceMarkerDecode_coordinate]
        using coordinate.symm

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

theorem exactReverseBobMarkerDecode_otherRank
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    (⟨exactLeft
        (exactReverseBobMarkerDecode
          side context marker).coordinate
        (exactReverseBobMarkerDecode
          side context marker).partition,
      exactLeftRank
        (exactReverseBobMarkerDecode
          side context marker)⟩ :
        Σ other : Finset M,
          ({j : M // j ∈ other} ≃ Fin other.card)) =
      ⟨context.otherSide, context.otherRank⟩ := by
  classical
  let coordinate := (context.sideRank.symm marker).val
  let partition :=
    exactReverseBobCanonicalPartition
      side coordinate context.ignoredBit
  have other : exactLeft coordinate partition =
      context.otherSide := by
    exact (exactReverseBobCanonicalPartition_otherSide
      side coordinate (context.sideRank.symm marker).property
      context.ignoredBit).trans
        context.otherSide_eq_complement.symm
  have transported := exactSigmaSideRankTransport
    (exactLeft coordinate partition)
    context.otherSide other context.otherRank
  simpa only [exactReverseBobMarkerDecode,
    exactLeftRank,
    exactPermutationOfSideRank_rank] using transported

theorem exactReverseBobMarkerDecode_otherCut
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    (⟨exactLeft
        (exactReverseBobMarkerDecode
          side context marker).coordinate
        (exactReverseBobMarkerDecode
          side context marker).partition,
      (exactReverseBobMarkerDecode
        side context marker).leftCut⟩ :
        Σ other : Finset M, Fin (other.card + 1)) =
      ⟨context.otherSide, context.otherCut⟩ := by
  classical
  let coordinate := (context.sideRank.symm marker).val
  let partition :=
    exactReverseBobCanonicalPartition
      side coordinate context.ignoredBit
  have other : exactLeft coordinate partition =
      context.otherSide := by
    exact (exactReverseBobCanonicalPartition_otherSide
      side coordinate (context.sideRank.symm marker).property
      context.ignoredBit).trans
        context.otherSide_eq_complement.symm
  have transported := exactSigmaFinCutTransport
    (exactLeft coordinate partition)
    context.otherSide other context.otherCut
  simpa only [exactReverseBobMarkerDecode] using transported

theorem exactReverseBobMarkerDecode_sideRank
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    (⟨exactReverseRightSide
        (exactReverseBobMarkerDecode
          side context marker),
      (exactReverseBobContext
        (exactReverseBobMarkerDecode
          side context marker)).sideRank⟩ :
        Σ actualSide : Finset M,
          ({j : M // j ∈ actualSide} ≃ Fin actualSide.card)) =
      ⟨side, context.sideRank⟩ := by
  classical
  let coordinate := (context.sideRank.symm marker).val
  let partition :=
    exactReverseBobCanonicalPartition
      side coordinate context.ignoredBit
  have actual : insert coordinate
      (exactRight coordinate partition) = side :=
    exactReverseBobCanonicalPartition_side
      side coordinate (context.sideRank.symm marker).property
      context.ignoredBit
  let transportedRank :
      {j : M //
        j ∈ insert coordinate (exactRight coordinate partition)} ≃
        Fin (insert coordinate (exactRight coordinate partition)).card :=
    (Equiv.subtypeEquivRight (fun j => by rw [actual])).trans
      (context.sideRank.trans
        (finCongr (congrArg Finset.card actual).symm))
  have transported :
      (⟨insert coordinate (exactRight coordinate partition),
        transportedRank⟩ :
          Σ actualSide : Finset M,
            ({j : M // j ∈ actualSide} ≃ Fin actualSide.card)) =
        ⟨side, context.sideRank⟩ :=
    exactSigmaSideRankTransport
      (insert coordinate (exactRight coordinate partition))
      side actual context.sideRank
  calc
    (⟨exactReverseRightSide
        (exactReverseBobMarkerDecode side context marker),
      (exactReverseBobContext
        (exactReverseBobMarkerDecode
          side context marker)).sideRank⟩ :
        Σ actualSide : Finset M,
          ({j : M // j ∈ actualSide} ≃ Fin actualSide.card)) =
        ⟨insert coordinate (exactRight coordinate partition),
          transportedRank⟩ := by
            apply Sigma.ext
            · change
                insert (context.sideRank.symm marker).val
                    (exactRight (context.sideRank.symm marker).val
                      (exactReverseBobCanonicalPartition
                        side (context.sideRank.symm marker).val
                        context.ignoredBit)) =
                  insert coordinate (exactRight coordinate partition)
              rfl
            · apply heq_of_eq
              dsimp only [exactReverseBobMarkerDecode]
              simp only [exactReverseRightSide,
                exactReverseBobContext, exactReverseRightRank, exactRightRank,
                exactPermutationOfSideRank_rank]
              rw [exactInsertedRank_deleteMarked]
              apply Equiv.ext
              intro j
              apply Fin.ext
              simp only [finCongr_apply, Equiv.trans_apply, Fin.val_cast,
                transportedRank, coordinate, partition]
              rfl
    _ = ⟨side, context.sideRank⟩ := transported

theorem exactReverseBobMarkerDecode_rightInverse
    {M : Type*} [Fintype M] [DecidableEq M]
    (side : Finset M)
    (context : ExactReverseSideContext M side)
    (marker : Fin side.card) :
    exactReverseBobMarkerCode
        (exactReverseBobMarkerDecode
          side context marker) =
      ⟨side, context, marker⟩ := by
  classical
  generalize decoded :
    exactReverseBobMarkerDecode side context marker = seed
  have sameSide : exactReverseRightSide seed = side := by
    rw [← decoded]
    exact exactReverseBobMarkerDecode_side
      side context marker
  subst side
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    change
      (exactReverseBobContext seed,
        (exactReverseBobContext seed).sideRank
          ⟨seed.coordinate,
            exactReverseRightSide_coordinate_mem seed⟩) =
        (context, marker)
    have sameContext : exactReverseBobContext seed = context := by
      cases context with
      | mk otherSide sideRank otherRank otherCut ignored complement =>
        simp only [exactReverseBobContext,
          ExactReverseSideContext.mk.injEq]
        let reverseContext : ExactReverseSideContext M
            (exactReverseRightSide seed) :=
          { otherSide := otherSide
            sideRank := sideRank
            otherRank := otherRank
            otherCut := otherCut
            ignoredBit := ignored
            otherSide_eq_complement := complement }
        have exactSideRank :=
          exactReverseBobMarkerDecode_sideRank
            (exactReverseRightSide seed)
            reverseContext marker
        have exactOtherRank :=
          exactReverseBobMarkerDecode_otherRank
            (exactReverseRightSide seed)
            reverseContext marker
        have exactOtherCut :=
          exactReverseBobMarkerDecode_otherCut
            (exactReverseRightSide seed)
            reverseContext marker
        change
          exactReverseBobMarkerDecode
              (exactReverseRightSide seed)
              reverseContext marker = seed at decoded
        rw [decoded] at exactSideRank exactOtherRank exactOtherCut
        refine ⟨(exactReverseRightSide_complement seed).trans
            complement.symm, ?_, ?_, ?_, ?_⟩
        · exact eq_of_heq (Sigma.mk.inj exactSideRank).2
        · exact (Sigma.mk.inj exactOtherRank).2
        · exact (Sigma.mk.inj exactOtherCut).2
        · have exactIgnored := congrArg
            (fun original : ExactForwardSeed M =>
              original.partition original.coordinate) decoded
          simpa only
            [exactReverseBobMarkerDecode_coordinate,
              exactReverseBobMarkerDecode_ignoredBit]
              using exactIgnored.symm
    apply Prod.ext
    · exact sameContext
    · rw [sameContext]
      apply context.sideRank.symm.injective
      change
        context.sideRank.symm
            (context.sideRank ⟨seed.coordinate, _⟩) =
          context.sideRank.symm marker
      rw [Equiv.symm_apply_apply]
      apply Subtype.ext
      have coordinate := congrArg
        (fun original : ExactForwardSeed M => original.coordinate)
        decoded
      simpa only [exactReverseBobMarkerDecode_coordinate]
        using coordinate.symm

end

section

open scoped BigOperators


open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

/-- The finite equivalence encoding exact reverse alice weighted marker. -/
def exactReverseAliceWeightedMarkerEquiv
    {M : Type*} [Fintype M] [DecidableEq M] :
    ExactForwardSeed M ≃
      (Σ side : Finset M,
        ExactReverseSideContext M side × Fin side.card) where
  toFun := exactReverseAliceMarkerCode
  invFun marker :=
    exactReverseAliceMarkerDecode
      marker.1 marker.2.1 marker.2.2
  left_inv seed := by
    apply exactReverseAliceMarkerCode_injective
    exact exactReverseAliceMarkerDecode_rightInverse
      (exactReverseAliceMarkerCode seed).1
      (exactReverseAliceMarkerCode seed).2.1
      (exactReverseAliceMarkerCode seed).2.2
  right_inv marker := by
    rcases marker with ⟨side, context, position⟩
    exact exactReverseAliceMarkerDecode_rightInverse
      side context position

/-- The finite equivalence encoding exact reverse bob weighted marker. -/
def exactReverseBobWeightedMarkerEquiv
    {M : Type*} [Fintype M] [DecidableEq M] :
    ExactForwardSeed M ≃
      (Σ side : Finset M,
        ExactReverseSideContext M side × Fin side.card) where
  toFun := exactReverseBobMarkerCode
  invFun marker :=
    exactReverseBobMarkerDecode
      marker.1 marker.2.1 marker.2.2
  left_inv seed := by
    apply exactReverseBobMarkerCode_injective
    exact exactReverseBobMarkerDecode_rightInverse
      (exactReverseBobMarkerCode seed).1
      (exactReverseBobMarkerCode seed).2.1
      (exactReverseBobMarkerCode seed).2.2
  right_inv marker := by
    rcases marker with ⟨side, context, position⟩
    exact exactReverseBobMarkerDecode_rightInverse
      side context position

theorem exactReverseAliceOriginalSeedWeight_factor
    {M : Type*} [Fintype M] [DecidableEq M]
    (nonempty : 0 < Fintype.card M)
    (seed : ExactForwardSeed M) :
    exactSeedWeight seed =
      reversePartitionWeight (exactReverseLeftSide seed) *
        (exactReverseSideContextWeight
          (exactReverseAliceContext seed) /
            ((exactReverseLeftSide seed).card : ℝ)) := by
  calc
    exactSeedWeight seed =
        reversePartitionWeight (exactReverseLeftSide seed) *
          exactReverseAliceConditionalSeedWeight
            (exactReverseLeftSide seed) seed := by
      symm
      simpa only [↓reduceIte] using
        (exactReverseAliceConditionalSeedWeight_cancel
          nonempty (exactReverseLeftSide seed) seed)
    _ = _ := by
      rw [exactReverseAliceConditionalSeedWeight_eq_context_div_card
        nonempty seed]

theorem exactReverseBobOriginalSeedWeight_factor
    {M : Type*} [Fintype M] [DecidableEq M]
    (nonempty : 0 < Fintype.card M)
    (seed : ExactForwardSeed M) :
    exactSeedWeight seed =
      reversePartitionWeight (exactReverseRightSide seed) *
        (exactReverseSideContextWeight
          (exactReverseBobContext seed) /
            ((exactReverseRightSide seed).card : ℝ)) := by
  calc
    exactSeedWeight seed =
        reversePartitionWeight (exactReverseRightSide seed) *
          exactReverseBobConditionalSeedWeight
            (exactReverseRightSide seed) seed := by
      symm
      simpa only [↓reduceIte] using
        (exactReverseBobConditionalSeedWeight_cancel
          nonempty (exactReverseRightSide seed) seed)
    _ = _ := by
      rw [exactReverseBobConditionalSeedWeight_eq_context_div_card
        nonempty seed]

theorem exactUniformFiniteMarkedAverage_sum
    (n : ℕ) (weight : ℝ) (statistic : Fin n → ℝ) :
    (∑ _marker : Fin n,
      weight * ((∑ position : Fin n, statistic position) / (n : ℝ))) =
      ∑ marker : Fin n, weight * statistic marker := by
  by_cases empty : n = 0
  · subst n
    simp only [univ_eq_empty, sum_empty, CharP.cast_eq_zero, div_zero, mul_zero, sum_const_zero]
  · have nonzero : (n : ℝ) ≠ 0 := by
      exact_mod_cast empty
    simp only [div_eq_mul_inv, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_left_comm, ne_eq, nonzero, not_false_eq_true, mul_inv_cancel₀, mul_one, mul_sum]

theorem exactReverseAliceUniformMarkedSeed_sum
    {M : Type*} [Fintype M] [DecidableEq M]
    (nonempty : 0 < Fintype.card M)
    (statistic : (side : Finset M) →
      ExactReverseSideContext M side → Fin side.card → ℝ) :
    (∑ seed : ExactForwardSeed M,
      exactSeedWeight seed *
        ((∑ marker : Fin (exactReverseLeftSide seed).card,
          statistic (exactReverseLeftSide seed)
            (exactReverseAliceContext seed) marker) /
          ((exactReverseLeftSide seed).card : ℝ))) =
      ∑ seed : ExactForwardSeed M,
        exactSeedWeight seed *
          statistic (exactReverseLeftSide seed)
            (exactReverseAliceContext seed)
            ((exactReverseAliceContext seed).sideRank
              ⟨seed.coordinate,
                exactReverseLeftSide_coordinate_mem seed⟩) := by
  classical
  let markerWeight :
      (Σ side : Finset M,
        ExactReverseSideContext M side × Fin side.card) → ℝ :=
    fun marker =>
      reversePartitionWeight marker.1 *
        (exactReverseSideContextWeight marker.2.1 /
          (marker.1.card : ℝ))
  let markerAverage :
      (Σ side : Finset M,
        ExactReverseSideContext M side × Fin side.card) → ℝ :=
    fun marker =>
      (∑ position : Fin marker.1.card,
        statistic marker.1 marker.2.1 position) /
        (marker.1.card : ℝ)
  let markerValue :
      (Σ side : Finset M,
        ExactReverseSideContext M side × Fin side.card) → ℝ :=
    fun marker => statistic marker.1 marker.2.1 marker.2.2
  calc
    (∑ seed : ExactForwardSeed M,
      exactSeedWeight seed *
        ((∑ marker : Fin (exactReverseLeftSide seed).card,
          statistic (exactReverseLeftSide seed)
            (exactReverseAliceContext seed) marker) /
          ((exactReverseLeftSide seed).card : ℝ))) =
        ∑ marker : Σ side : Finset M,
          ExactReverseSideContext M side × Fin side.card,
            markerWeight marker * markerAverage marker := by
      apply Fintype.sum_equiv
        (exactReverseAliceWeightedMarkerEquiv (M := M))
      intro seed
      change
        exactSeedWeight seed *
          ((∑ marker : Fin (exactReverseLeftSide seed).card,
            statistic (exactReverseLeftSide seed)
              (exactReverseAliceContext seed) marker) /
            ((exactReverseLeftSide seed).card : ℝ)) =
          (reversePartitionWeight (exactReverseLeftSide seed) *
            (exactReverseSideContextWeight
              (exactReverseAliceContext seed) /
                ((exactReverseLeftSide seed).card : ℝ))) *
            ((∑ marker : Fin (exactReverseLeftSide seed).card,
              statistic (exactReverseLeftSide seed)
                (exactReverseAliceContext seed) marker) /
              ((exactReverseLeftSide seed).card : ℝ))
      rw [exactReverseAliceOriginalSeedWeight_factor nonempty]
    _ = ∑ marker : Σ side : Finset M,
          ExactReverseSideContext M side × Fin side.card,
            markerWeight marker * markerValue marker := by
      simp only [Fintype.sum_sigma, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro side _
      apply Finset.sum_congr rfl
      intro context _
      exact exactUniformFiniteMarkedAverage_sum
        side.card
        (reversePartitionWeight side *
          (exactReverseSideContextWeight context /
            (side.card : ℝ)))
        (statistic side context)
    _ = ∑ seed : ExactForwardSeed M,
        exactSeedWeight seed *
          statistic (exactReverseLeftSide seed)
            (exactReverseAliceContext seed)
            ((exactReverseAliceContext seed).sideRank
              ⟨seed.coordinate,
                exactReverseLeftSide_coordinate_mem seed⟩) := by
      symm
      apply Fintype.sum_equiv
        (exactReverseAliceWeightedMarkerEquiv (M := M))
      intro seed
      change
        exactSeedWeight seed *
          statistic (exactReverseLeftSide seed)
            (exactReverseAliceContext seed)
            ((exactReverseAliceContext seed).sideRank
              ⟨seed.coordinate,
                exactReverseLeftSide_coordinate_mem seed⟩) =
          (reversePartitionWeight (exactReverseLeftSide seed) *
            (exactReverseSideContextWeight
              (exactReverseAliceContext seed) /
                ((exactReverseLeftSide seed).card : ℝ))) *
            statistic (exactReverseLeftSide seed)
              (exactReverseAliceContext seed)
              ((exactReverseAliceContext seed).sideRank
                ⟨seed.coordinate,
                  exactReverseLeftSide_coordinate_mem seed⟩)
      rw [exactReverseAliceOriginalSeedWeight_factor nonempty]

theorem exactReverseBobUniformMarkedSeed_sum
    {M : Type*} [Fintype M] [DecidableEq M]
    (nonempty : 0 < Fintype.card M)
    (statistic : (side : Finset M) →
      ExactReverseSideContext M side → Fin side.card → ℝ) :
    (∑ seed : ExactForwardSeed M,
      exactSeedWeight seed *
        ((∑ marker : Fin (exactReverseRightSide seed).card,
          statistic (exactReverseRightSide seed)
            (exactReverseBobContext seed) marker) /
          ((exactReverseRightSide seed).card : ℝ))) =
      ∑ seed : ExactForwardSeed M,
        exactSeedWeight seed *
          statistic (exactReverseRightSide seed)
            (exactReverseBobContext seed)
            ((exactReverseBobContext seed).sideRank
              ⟨seed.coordinate,
                exactReverseRightSide_coordinate_mem seed⟩) := by
  classical
  let markerWeight :
      (Σ side : Finset M,
        ExactReverseSideContext M side × Fin side.card) → ℝ :=
    fun marker =>
      reversePartitionWeight marker.1 *
        (exactReverseSideContextWeight marker.2.1 /
          (marker.1.card : ℝ))
  let markerAverage :
      (Σ side : Finset M,
        ExactReverseSideContext M side × Fin side.card) → ℝ :=
    fun marker =>
      (∑ position : Fin marker.1.card,
        statistic marker.1 marker.2.1 position) /
        (marker.1.card : ℝ)
  let markerValue :
      (Σ side : Finset M,
        ExactReverseSideContext M side × Fin side.card) → ℝ :=
    fun marker => statistic marker.1 marker.2.1 marker.2.2
  calc
    (∑ seed : ExactForwardSeed M,
      exactSeedWeight seed *
        ((∑ marker : Fin (exactReverseRightSide seed).card,
          statistic (exactReverseRightSide seed)
            (exactReverseBobContext seed) marker) /
          ((exactReverseRightSide seed).card : ℝ))) =
        ∑ marker : Σ side : Finset M,
          ExactReverseSideContext M side × Fin side.card,
            markerWeight marker * markerAverage marker := by
      apply Fintype.sum_equiv
        (exactReverseBobWeightedMarkerEquiv (M := M))
      intro seed
      change
        exactSeedWeight seed *
          ((∑ marker : Fin (exactReverseRightSide seed).card,
            statistic (exactReverseRightSide seed)
              (exactReverseBobContext seed) marker) /
            ((exactReverseRightSide seed).card : ℝ)) =
          (reversePartitionWeight (exactReverseRightSide seed) *
            (exactReverseSideContextWeight
              (exactReverseBobContext seed) /
                ((exactReverseRightSide seed).card : ℝ))) *
            ((∑ marker : Fin (exactReverseRightSide seed).card,
              statistic (exactReverseRightSide seed)
                (exactReverseBobContext seed) marker) /
              ((exactReverseRightSide seed).card : ℝ))
      rw [exactReverseBobOriginalSeedWeight_factor nonempty]
    _ = ∑ marker : Σ side : Finset M,
          ExactReverseSideContext M side × Fin side.card,
            markerWeight marker * markerValue marker := by
      simp only [Fintype.sum_sigma, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro side _
      apply Finset.sum_congr rfl
      intro context _
      exact exactUniformFiniteMarkedAverage_sum
        side.card
        (reversePartitionWeight side *
          (exactReverseSideContextWeight context /
            (side.card : ℝ)))
        (statistic side context)
    _ = ∑ seed : ExactForwardSeed M,
        exactSeedWeight seed *
          statistic (exactReverseRightSide seed)
            (exactReverseBobContext seed)
            ((exactReverseBobContext seed).sideRank
              ⟨seed.coordinate,
                exactReverseRightSide_coordinate_mem seed⟩) := by
      symm
      apply Fintype.sum_equiv
        (exactReverseBobWeightedMarkerEquiv (M := M))
      intro seed
      change
        exactSeedWeight seed *
          statistic (exactReverseRightSide seed)
            (exactReverseBobContext seed)
            ((exactReverseBobContext seed).sideRank
              ⟨seed.coordinate,
                exactReverseRightSide_coordinate_mem seed⟩) =
          (reversePartitionWeight (exactReverseRightSide seed) *
            (exactReverseSideContextWeight
              (exactReverseBobContext seed) /
                ((exactReverseRightSide seed).card : ℝ))) *
            statistic (exactReverseRightSide seed)
              (exactReverseBobContext seed)
              ((exactReverseBobContext seed).sideRank
                ⟨seed.coordinate,
                  exactReverseRightSide_coordinate_mem seed⟩)
      rw [exactReverseBobOriginalSeedWeight_factor nonempty]

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace


attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The entropy quantity for exact reverse alice filter operator marker. -/
def exactReverseAliceFilterOperatorMarkerEntropy
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) : ℝ :=
  let seed := exactReverseBobMarkerDecode side context marker
  ∑ history : ExactRevealHistory X Y D seed,
  ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
  ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
    if exactHistoryAccepted G n D
        ⟨seed, history, aliceAnswer, bobAnswer⟩ then
      exactRevealMass G n D seed history *
        exactFairAliceHistoryEntropyIncrement G n S D
          ⟨seed, history, aliceAnswer, bobAnswer⟩
    else 0

/-- The entropy quantity for exact reverse bob filter operator marker. -/
def exactReverseBobFilterOperatorMarkerEntropy
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) : ℝ :=
  let seed := exactReverseAliceMarkerDecode side context marker
  ∑ history : ExactRevealHistory X Y D seed,
  ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
  ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
    if exactHistoryAccepted G n D
        ⟨seed, history, aliceAnswer, bobAnswer⟩ then
      exactRevealMass G n D seed history *
        exactFairBobHistoryEntropyIncrement G n S D
          ⟨seed, history, aliceAnswer, bobAnswer⟩
    else 0

theorem exactFairAliceOperatorEntropy_reverse_marked_average
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < Fintype.card (SourceRemainingCoordinate D)) :
    (∑ r : ExactHistoryFlag X Y A B D,
      if exactHistoryAccepted G n D r then
        exactFairHistoryPriorWeight G n D r *
          exactFairAliceHistoryEntropyIncrement G n S D r
      else 0) =
    ∑ seed : ExactRemainingSeed D,
      exactSeedWeight seed *
        ((∑ marker : Fin (exactReverseRightSide seed).card,
          exactReverseAliceFilterOperatorMarkerEntropy
            G n S D
            (exactReverseRightSide seed)
            (exactReverseBobContext seed) marker) /
          ((exactReverseRightSide seed).card : ℝ)) := by
  classical
  have uniform := exactReverseBobUniformMarkedSeed_sum
    remaining
    (exactReverseAliceFilterOperatorMarkerEntropy G n S D)
  symm
  calc
    (∑ seed : ExactRemainingSeed D,
      exactSeedWeight seed *
        ((∑ marker : Fin (exactReverseRightSide seed).card,
          exactReverseAliceFilterOperatorMarkerEntropy
            G n S D
            (exactReverseRightSide seed)
            (exactReverseBobContext seed) marker) /
          ((exactReverseRightSide seed).card : ℝ))) =
      ∑ seed : ExactRemainingSeed D,
        exactSeedWeight seed *
          exactReverseAliceFilterOperatorMarkerEntropy
            G n S D
            (exactReverseRightSide seed)
            (exactReverseBobContext seed)
            ((exactReverseBobContext seed).sideRank
              ⟨seed.coordinate,
                exactReverseRightSide_coordinate_mem seed⟩) :=
        uniform
    _ = _ := by
      rw [exactHistoryFlag_sum]
      apply Finset.sum_congr rfl
      intro seed _
      have decode :=
        (exactReverseBobWeightedMarkerEquiv
          (M := SourceRemainingCoordinate D)).left_inv seed
      change
        exactReverseBobMarkerDecode
          (exactReverseRightSide seed)
          (exactReverseBobContext seed)
          ((exactReverseBobContext seed).sideRank
            ⟨seed.coordinate,
              exactReverseRightSide_coordinate_mem seed⟩) =
          seed at decode
      unfold exactReverseAliceFilterOperatorMarkerEntropy
      rw [decode]
      simp only [exactFairHistoryPriorWeight,
        Finset.mul_sum, mul_ite, mul_zero, mul_assoc]

theorem exactFairBobOperatorEntropy_reverse_marked_average
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (remaining : 0 < Fintype.card (SourceRemainingCoordinate D)) :
    (∑ r : ExactHistoryFlag X Y A B D,
      if exactHistoryAccepted G n D r then
        exactFairHistoryPriorWeight G n D r *
          exactFairBobHistoryEntropyIncrement G n S D r
      else 0) =
    ∑ seed : ExactRemainingSeed D,
      exactSeedWeight seed *
        ((∑ marker : Fin (exactReverseLeftSide seed).card,
          exactReverseBobFilterOperatorMarkerEntropy
            G n S D
            (exactReverseLeftSide seed)
            (exactReverseAliceContext seed) marker) /
          ((exactReverseLeftSide seed).card : ℝ)) := by
  classical
  have uniform := exactReverseAliceUniformMarkedSeed_sum
    remaining
    (exactReverseBobFilterOperatorMarkerEntropy G n S D)
  symm
  calc
    (∑ seed : ExactRemainingSeed D,
      exactSeedWeight seed *
        ((∑ marker : Fin (exactReverseLeftSide seed).card,
          exactReverseBobFilterOperatorMarkerEntropy
            G n S D
            (exactReverseLeftSide seed)
            (exactReverseAliceContext seed) marker) /
          ((exactReverseLeftSide seed).card : ℝ))) =
      ∑ seed : ExactRemainingSeed D,
        exactSeedWeight seed *
          exactReverseBobFilterOperatorMarkerEntropy
            G n S D
            (exactReverseLeftSide seed)
            (exactReverseAliceContext seed)
            ((exactReverseAliceContext seed).sideRank
              ⟨seed.coordinate,
                exactReverseLeftSide_coordinate_mem seed⟩) :=
        uniform
    _ = _ := by
      rw [exactHistoryFlag_sum]
      apply Finset.sum_congr rfl
      intro seed _
      have decode :=
        (exactReverseAliceWeightedMarkerEquiv
          (M := SourceRemainingCoordinate D)).left_inv seed
      change
        exactReverseAliceMarkerDecode
          (exactReverseLeftSide seed)
          (exactReverseAliceContext seed)
          ((exactReverseAliceContext seed).sideRank
            ⟨seed.coordinate,
              exactReverseLeftSide_coordinate_mem seed⟩) =
          seed at decode
      unfold exactReverseBobFilterOperatorMarkerEntropy
      rw [decode]
      simp only [exactFairHistoryPriorWeight,
        Finset.mul_sum, mul_ite, mul_zero, mul_assoc]

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace


attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The potential function controlling exact fair alice history high operator. -/
def exactFairAliceHistoryHighOperatorPotential
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) : ℝ :=
  ∑ y : Y, G.marginalY y *
    bornTracePairing S.state.matrix
      (∑ x : X, G.conditionalXGivenY y x •
        cfc (fun z : ℝ => z * Real.log z)
          (exactAliceQuestionFilter
            G n S D r.seed r.history r.aliceAnswer x))
      (exactBobQuestionFilter
        G n S D r.seed r.history r.bobAnswer y)

/-- The potential function controlling exact fair alice history low operator. -/
def exactFairAliceHistoryLowOperatorPotential
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) : ℝ :=
  ∑ y : Y, G.marginalY y *
    bornTracePairing S.state.matrix
      (cfc (fun z : ℝ => z * Real.log z)
        (exactAliceMeanFilter
          G n S D r.seed r.history r.aliceAnswer y))
      (exactBobQuestionFilter
        G n S D r.seed r.history r.bobAnswer y)

/-- The potential function controlling exact fair bob history high operator. -/
def exactFairBobHistoryHighOperatorPotential
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) : ℝ :=
  ∑ x : X, G.marginalX x *
    bornTracePairing S.state.matrix
      (exactAliceQuestionFilter
        G n S D r.seed r.history r.aliceAnswer x)
      (∑ y : Y, G.conditionalYGivenX x y •
        cfc (fun z : ℝ => z * Real.log z)
          (exactBobQuestionFilter
            G n S D r.seed r.history r.bobAnswer y))

/-- The potential function controlling exact fair bob history low operator. -/
def exactFairBobHistoryLowOperatorPotential
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) : ℝ :=
  ∑ x : X, G.marginalX x *
    bornTracePairing S.state.matrix
      (exactAliceQuestionFilter
        G n S D r.seed r.history r.aliceAnswer x)
      (cfc (fun z : ℝ => z * Real.log z)
        (exactBobMeanFilter
          G n S D r.seed r.history r.bobAnswer x))

theorem exactFairAliceHistoryEntropy_eq_operatorPotential_sub
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :
    exactFairAliceHistoryEntropyIncrement G n S D r =
      exactFairAliceHistoryHighOperatorPotential G n S D r -
      exactFairAliceHistoryLowOperatorPotential G n S D r := by
  unfold exactFairAliceHistoryEntropyIncrement
    exactFairAliceQuestionEntropyIncrement
    exactFairAliceHistoryHighOperatorPotential
    exactFairAliceHistoryLowOperatorPotential
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro y _
  rw [← mul_sub, map_sub]
  rfl

theorem exactFairBobHistoryEntropy_eq_operatorPotential_sub
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D) :
    exactFairBobHistoryEntropyIncrement G n S D r =
      exactFairBobHistoryHighOperatorPotential G n S D r -
      exactFairBobHistoryLowOperatorPotential G n S D r := by
  unfold exactFairBobHistoryEntropyIncrement
    exactFairBobQuestionEntropyIncrement
    exactFairBobHistoryHighOperatorPotential
    exactFairBobHistoryLowOperatorPotential
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [← mul_sub, map_sub]

/-- The potential function controlling exact reverse alice filter high operator. -/
def exactReverseAliceFilterHighOperatorPotential
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) : ℝ :=
  let seed := exactReverseBobMarkerDecode side context marker
  ∑ history : ExactRevealHistory X Y D seed,
  ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
  ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
    if exactHistoryAccepted G n D
        ⟨seed, history, aliceAnswer, bobAnswer⟩ then
      exactRevealMass G n D seed history *
        exactFairAliceHistoryHighOperatorPotential G n S D
          ⟨seed, history, aliceAnswer, bobAnswer⟩
    else 0

/-- The potential function controlling exact reverse alice filter low operator. -/
def exactReverseAliceFilterLowOperatorPotential
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) : ℝ :=
  let seed := exactReverseBobMarkerDecode side context marker
  ∑ history : ExactRevealHistory X Y D seed,
  ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
  ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
    if exactHistoryAccepted G n D
        ⟨seed, history, aliceAnswer, bobAnswer⟩ then
      exactRevealMass G n D seed history *
        exactFairAliceHistoryLowOperatorPotential G n S D
          ⟨seed, history, aliceAnswer, bobAnswer⟩
    else 0

/-- The potential function controlling exact reverse bob filter high operator. -/
def exactReverseBobFilterHighOperatorPotential
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) : ℝ :=
  let seed := exactReverseAliceMarkerDecode side context marker
  ∑ history : ExactRevealHistory X Y D seed,
  ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
  ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
    if exactHistoryAccepted G n D
        ⟨seed, history, aliceAnswer, bobAnswer⟩ then
      exactRevealMass G n D seed history *
        exactFairBobHistoryHighOperatorPotential G n S D
          ⟨seed, history, aliceAnswer, bobAnswer⟩
    else 0

/-- The potential function controlling exact reverse bob filter low operator. -/
def exactReverseBobFilterLowOperatorPotential
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) : ℝ :=
  let seed := exactReverseAliceMarkerDecode side context marker
  ∑ history : ExactRevealHistory X Y D seed,
  ∑ aliceAnswer : {j : Fin n // j ∈ D} → A,
  ∑ bobAnswer : {j : Fin n // j ∈ D} → B,
    if exactHistoryAccepted G n D
        ⟨seed, history, aliceAnswer, bobAnswer⟩ then
      exactRevealMass G n D seed history *
        exactFairBobHistoryLowOperatorPotential G n S D
          ⟨seed, history, aliceAnswer, bobAnswer⟩
    else 0

theorem exactReverseAliceFilterOperatorMarkerEntropy_eq_sub
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) :
    exactReverseAliceFilterOperatorMarkerEntropy
        G n S D side context marker =
      exactReverseAliceFilterHighOperatorPotential
          G n S D side context marker -
        exactReverseAliceFilterLowOperatorPotential
          G n S D side context marker := by
  unfold exactReverseAliceFilterOperatorMarkerEntropy
    exactReverseAliceFilterHighOperatorPotential
    exactReverseAliceFilterLowOperatorPotential
  simp only [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro history _
  apply Finset.sum_congr rfl
  intro aliceAnswer _
  apply Finset.sum_congr rfl
  intro bobAnswer _
  by_cases accepted : exactHistoryAccepted G n D
    ⟨exactReverseBobMarkerDecode side context marker,
      history, aliceAnswer, bobAnswer⟩
  · simp only [ite_eq_left accepted]
    rw [exactFairAliceHistoryEntropy_eq_operatorPotential_sub]
    ring
  · simp only [accepted, ↓reduceIte, sub_self]

theorem exactReverseBobFilterOperatorMarkerEntropy_eq_sub
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (side : Finset (SourceRemainingCoordinate D))
    (context : ExactReverseSideContext
      (SourceRemainingCoordinate D) side)
    (marker : Fin side.card) :
    exactReverseBobFilterOperatorMarkerEntropy
        G n S D side context marker =
      exactReverseBobFilterHighOperatorPotential
          G n S D side context marker -
        exactReverseBobFilterLowOperatorPotential
          G n S D side context marker := by
  unfold exactReverseBobFilterOperatorMarkerEntropy
    exactReverseBobFilterHighOperatorPotential
    exactReverseBobFilterLowOperatorPotential
  simp only [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro history _
  apply Finset.sum_congr rfl
  intro aliceAnswer _
  apply Finset.sum_congr rfl
  intro bobAnswer _
  by_cases accepted : exactHistoryAccepted G n D
    ⟨exactReverseAliceMarkerDecode side context marker,
      history, aliceAnswer, bobAnswer⟩
  · simp only [ite_eq_left accepted]
    rw [exactFairBobHistoryEntropy_eq_operatorPotential_sub]
    ring
  · simp only [accepted, ↓reduceIte, sub_self]

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace


attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem exactFixedQuestionPrefix_insert_iff
    {T : Type*}
    {n : ℕ} (fixed : Finset (Fin n)) (j : Fin n)
    (fresh : j ∉ fixed)
    (candidate known : Fin n → T) (value : T) :
    (∀ k : Fin n, k ∈ insert j fixed →
      candidate k = (Function.update known j value) k) ↔
      candidate j = value ∧
        ∀ k : Fin n, k ∈ fixed → candidate k = known k := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa only [Function.update_self] using h j (Finset.mem_insert_self j fixed)
    · intro k hk
      have different : k ≠ j := by
        intro same
        exact fresh (same ▸ hk)
      simpa only [Function.update_of_ne different] using
        h k (Finset.mem_insert_of_mem hk)
  · rintro ⟨hvalue, hfixed⟩ k hk
    rcases Finset.mem_insert.mp hk with same | hk
    · subst k
      simpa only [Function.update_self] using hvalue
    · have different : k ≠ j := by
        intro same
        exact fresh (same ▸ hk)
      simpa only [Function.update_of_ne different] using hfixed k hk

end

section

open scoped BigOperators


attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem exactRevealCode_splitAt_independent
    {n : ℕ} (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (x x' : X) (y y' : Y)
    (tailX : {j : Fin n // j ≠ seed.coordinate.val} → X)
    (tailY : {j : Fin n // j ≠ seed.coordinate.val} → Y) :
    exactRevealCode D seed
      ((Equiv.funSplitAt seed.coordinate.val X).symm (x, tailX),
       (Equiv.funSplitAt seed.coordinate.val Y).symm (y, tailY)) =
    exactRevealCode D seed
      ((Equiv.funSplitAt seed.coordinate.val X).symm (x', tailX),
       (Equiv.funSplitAt seed.coordinate.val Y).symm (y', tailY)) := by
  unfold exactRevealCode
  congr 1
  · funext j
    have hiD : seed.coordinate.val ∉ D :=
      (Finset.mem_sdiff.mp seed.coordinate.property).2
    have different : j.val ≠ seed.coordinate.val := by
      intro h
      exact hiD (h ▸ j.property)
    simp only [ne_eq, Equiv.funSplitAt, Equiv.piSplitAt, eq_rec_constant, Equiv.symm_mk,
      Equiv.coe_fn_mk, different, ↓reduceDIte]
  · funext j
    have hiD : seed.coordinate.val ∉ D :=
      (Finset.mem_sdiff.mp seed.coordinate.property).2
    have different : j.val ≠ seed.coordinate.val := by
      intro h
      exact hiD (h ▸ j.property)
    simp only [ne_eq, Equiv.funSplitAt, Equiv.piSplitAt, eq_rec_constant, Equiv.symm_mk,
      Equiv.coe_fn_mk, different, ↓reduceDIte]
  · funext j
    have different : j.val.val ≠ seed.coordinate.val := by
      intro h
      have same : j.val = seed.coordinate := Subtype.ext h
      have mem : seed.coordinate ∈
          exactLeft seed.coordinate seed.partition := by
        simpa only [same] using j.property
      exact exactLeft_coordinate_not_mem
        seed.coordinate seed.partition mem
    simp only [ne_eq, Equiv.funSplitAt, Equiv.piSplitAt, eq_rec_constant, Equiv.symm_mk,
      Equiv.coe_fn_mk, different, ↓reduceDIte]
  · funext j
    have different : j.val.val ≠ seed.coordinate.val := by
      intro h
      have same : j.val = seed.coordinate := Subtype.ext h
      have mem : seed.coordinate ∈
          exactRight seed.coordinate seed.partition := by
        simpa only [same] using j.property
      exact exactRight_coordinate_not_mem
        seed.coordinate seed.partition mem
    simp only [ne_eq, Equiv.funSplitAt, Equiv.piSplitAt, eq_rec_constant, Equiv.symm_mk,
      Equiv.coe_fn_mk, different, ↓reduceDIte]
  · funext j
    have different : j.val.val ≠ seed.coordinate.val := by
      intro h
      have same : j.val = seed.coordinate := Subtype.ext h
      have hleft := exactLeftPrefix_subset seed j.property
      exact exactLeft_coordinate_not_mem
        seed.coordinate seed.partition (same ▸ hleft)
    simp only [ne_eq, Equiv.funSplitAt, Equiv.piSplitAt, eq_rec_constant, Equiv.symm_mk,
      Equiv.coe_fn_mk, different, ↓reduceDIte]
  · funext j
    have different : j.val.val ≠ seed.coordinate.val := by
      intro h
      have same : j.val = seed.coordinate := Subtype.ext h
      have hright := exactRightPrefix_subset seed j.property
      exact exactRight_coordinate_not_mem
        seed.coordinate seed.partition (same ▸ hright)
    simp only [ne_eq, Equiv.funSplitAt, Equiv.piSplitAt, eq_rec_constant, Equiv.symm_mk,
      Equiv.coe_fn_mk, different, ↓reduceDIte]

theorem exactRepeatedQuestionWeight_splitAt_joint
    (G : Game X Y A B) (n : ℕ) (i : Fin n)
    (x : X) (y : Y)
    (tailX : {j : Fin n // j ≠ i} → X)
    (tailY : {j : Fin n // j ≠ i} → Y) :
    (G.repeat n).questionWeight
        ((Equiv.funSplitAt i X).symm (x, tailX))
        ((Equiv.funSplitAt i Y).symm (y, tailY)) =
      G.questionWeight x y *
        ∏ j : {j : Fin n // j ≠ i},
          G.questionWeight (tailX j) (tailY j) := by
  classical
  rw [Game.repeat_questionWeight]
  rw [← Finset.mul_prod_erase
    (Finset.univ : Finset (Fin n))
    (fun j : Fin n => G.questionWeight
      ((Equiv.funSplitAt i X).symm (x, tailX) j)
      ((Equiv.funSplitAt i Y).symm (y, tailY) j))
    (Finset.mem_univ i)]
  simp only [Equiv.funSplitAt, Equiv.piSplitAt,
    Equiv.coe_fn_symm_mk, dite_true]
  congr 1
  let e : {j : Fin n // j ∈ (Finset.univ : Finset (Fin n)).erase i} ≃
      {j : Fin n // j ≠ i} :=
    { toFun := fun j => ⟨j.val, (Finset.mem_erase.mp j.property).1⟩
      invFun := fun j => ⟨j.val,
        Finset.mem_erase.mpr ⟨j.property, Finset.mem_univ _⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Finset.prod_coe_sort, ← e.prod_comp]
  apply Finset.prod_congr rfl
  intro j _
  have different : j.val ≠ i := (Finset.mem_erase.mp j.property).1
  simp only [different, ↓reduceDIte, ne_eq, Equiv.coe_fn_mk, e]

private def exactFairQuestionTailWeight
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y) : ℝ :=
  ∑ tailX : {j : Fin n // j ≠ seed.coordinate.val} → X,
  ∑ tailY : {j : Fin n // j ≠ seed.coordinate.val} → Y,
    if exactRevealCode D seed
       ((Equiv.funSplitAt seed.coordinate.val X).symm (x, tailX),
        (Equiv.funSplitAt seed.coordinate.val Y).symm (y, tailY)) =
          history
    then ∏ j : {j : Fin n // j ≠ seed.coordinate.val},
      G.questionWeight (tailX j) (tailY j)
    else 0

theorem exactFairQuestionTailWeight_independent
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x x' : X) (y y' : Y) :
    exactFairQuestionTailWeight
        G n D seed history x y =
      exactFairQuestionTailWeight
        G n D seed history x' y' := by
  unfold exactFairQuestionTailWeight
  apply Finset.sum_congr rfl
  intro tailX _
  apply Finset.sum_congr rfl
  intro tailY _
  rw [exactRevealCode_splitAt_independent
    D seed x x' y y' tailX tailY]

theorem exactJointQuestionMass_eq_question_mul_tail
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y) :
    exactJointQuestionMass G n D seed history x y =
      G.questionWeight x y *
        exactFairQuestionTailWeight
          G n D seed history x y := by
  classical
  let e := Equiv.prodCongr
    (Equiv.funSplitAt seed.coordinate.val X)
    (Equiv.funSplitAt seed.coordinate.val Y)
  calc
    exactJointQuestionMass G n D seed history x y =
      ∑ t : (X × ({j : Fin n // j ≠ seed.coordinate.val} → X)) ×
          (Y × ({j : Fin n // j ≠ seed.coordinate.val} → Y)),
        if exactRevealCode D seed (e.symm t) = history ∧
          (e.symm t).1 seed.coordinate.val = x ∧
          (e.symm t).2 seed.coordinate.val = y
        then exactPriorQuestionWeight G n (e.symm t)
        else 0 := by
          unfold exactJointQuestionMass
          exact (e.symm.sum_comp (fun q =>
            if exactRevealCode D seed q = history ∧
              q.1 seed.coordinate.val = x ∧
              q.2 seed.coordinate.val = y
            then exactPriorQuestionWeight G n q
            else 0)).symm
    _ = ∑ tailX : {j : Fin n // j ≠ seed.coordinate.val} → X,
        ∑ tailY : {j : Fin n // j ≠ seed.coordinate.val} → Y,
          if exactRevealCode D seed
             ((Equiv.funSplitAt seed.coordinate.val X).symm (x, tailX),
              (Equiv.funSplitAt seed.coordinate.val Y).symm (y, tailY)) =
                history
          then exactPriorQuestionWeight G n
             ((Equiv.funSplitAt seed.coordinate.val X).symm (x, tailX),
              (Equiv.funSplitAt seed.coordinate.val Y).symm (y, tailY))
          else 0 := by
            simp only [Fintype.sum_prod_type, e, Equiv.prodCongr,
              Equiv.coe_fn_symm_mk, Prod.map, Equiv.funSplitAt,
              Equiv.piSplitAt, dite_true]
            change
              (∑ xx : X,
                ∑ tailX : {j : Fin n // j ≠ seed.coordinate.val} → X,
                ∑ yy : Y,
                ∑ tailY : {j : Fin n // j ≠ seed.coordinate.val} → Y,
                  if exactRevealCode D seed
                      ((Equiv.funSplitAt seed.coordinate.val X).symm
                         (xx, tailX),
                       (Equiv.funSplitAt seed.coordinate.val Y).symm
                         (yy, tailY)) = history ∧
                    xx = x ∧ yy = y then
                    exactPriorQuestionWeight G n
                      ((Equiv.funSplitAt seed.coordinate.val X).symm
                         (xx, tailX),
                       (Equiv.funSplitAt seed.coordinate.val Y).symm
                         (yy, tailY))
                  else 0) = _
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro tailX _
            calc
              (∑ xx : X,
                ∑ yy : Y,
                ∑ tailY : {j : Fin n // j ≠ seed.coordinate.val} → Y,
                  if exactRevealCode D seed
                      ((Equiv.funSplitAt seed.coordinate.val X).symm
                         (xx, tailX),
                       (Equiv.funSplitAt seed.coordinate.val Y).symm
                         (yy, tailY)) = history ∧
                    xx = x ∧ yy = y then
                    exactPriorQuestionWeight G n
                      ((Equiv.funSplitAt seed.coordinate.val X).symm
                         (xx, tailX),
                       (Equiv.funSplitAt seed.coordinate.val Y).symm
                         (yy, tailY))
                  else 0) =
                ∑ xx : X,
                ∑ tailY : {j : Fin n // j ≠ seed.coordinate.val} → Y,
                ∑ yy : Y,
                  if exactRevealCode D seed
                      ((Equiv.funSplitAt seed.coordinate.val X).symm
                         (xx, tailX),
                       (Equiv.funSplitAt seed.coordinate.val Y).symm
                         (yy, tailY)) = history ∧
                    xx = x ∧ yy = y then
                    exactPriorQuestionWeight G n
                      ((Equiv.funSplitAt seed.coordinate.val X).symm
                         (xx, tailX),
                       (Equiv.funSplitAt seed.coordinate.val Y).symm
                         (yy, tailY))
                  else 0 := by
                    apply Finset.sum_congr rfl
                    intro xx _
                    rw [Finset.sum_comm]
              _ = ∑ tailY : {j : Fin n // j ≠ seed.coordinate.val} → Y,
                  ∑ xx : X, ∑ yy : Y,
                    if exactRevealCode D seed
                        ((Equiv.funSplitAt seed.coordinate.val X).symm
                           (xx, tailX),
                         (Equiv.funSplitAt seed.coordinate.val Y).symm
                           (yy, tailY)) = history ∧
                      xx = x ∧ yy = y then
                      exactPriorQuestionWeight G n
                        ((Equiv.funSplitAt seed.coordinate.val X).symm
                           (xx, tailX),
                         (Equiv.funSplitAt seed.coordinate.val Y).symm
                           (yy, tailY))
                    else 0 := by
                      rw [Finset.sum_comm]
              _ = _ := by
                    apply Finset.sum_congr rfl
                    intro tailY _
                    have hcondition (xx : X) (yy : Y) :
                        (exactRevealCode D seed
                            ((Equiv.funSplitAt seed.coordinate.val X).symm
                               (xx, tailX),
                             (Equiv.funSplitAt seed.coordinate.val Y).symm
                               (yy, tailY)) = history ∧
                          xx = x ∧ yy = y) =
                        (xx = x ∧ yy = y ∧
                          exactRevealCode D seed
                            ((Equiv.funSplitAt seed.coordinate.val X).symm
                               (xx, tailX),
                             (Equiv.funSplitAt seed.coordinate.val Y).symm
                               (yy, tailY)) = history) := by
                          apply propext
                          tauto
                    simp_rw [hcondition, ite_and]
                    simp only [ne_eq, Equiv.funSplitAt, Equiv.piSplitAt, eq_rec_constant,
                      Equiv.symm_mk, Equiv.coe_fn_mk, sum_ite_irrel, sum_ite_eq', mem_univ,
                      ↓reduceIte, sum_const_zero]
    _ = G.questionWeight x y *
        exactFairQuestionTailWeight G n D seed history x y := by
          unfold exactFairQuestionTailWeight
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro tailX _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro tailY _
          by_cases h : exactRevealCode D seed
              ((Equiv.funSplitAt seed.coordinate.val X).symm (x, tailX),
               (Equiv.funSplitAt seed.coordinate.val Y).symm (y, tailY)) =
                history
          · rw [ite_eq_left h, ite_eq_left h]
            exact exactRepeatedQuestionWeight_splitAt_joint
              G n seed.coordinate.val x y tailX tailY
          · simp only [ne_eq, h, ↓reduceIte, mul_zero]

theorem exactJointQuestionMass_sum
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed) :
    (∑ x : X, ∑ y : Y,
      exactJointQuestionMass G n D seed history x y) =
      exactRevealMass G n D seed history := by
  classical
  unfold exactJointQuestionMass exactRevealMass
  calc
    (∑ x : X, ∑ y : Y,
      ∑ q : ExactFullQuestion X Y n,
        if exactRevealCode D seed q = history ∧
          q.1 seed.coordinate.val = x ∧
          q.2 seed.coordinate.val = y
        then exactPriorQuestionWeight G n q
        else 0) =
      ∑ q : ExactFullQuestion X Y n,
        ∑ x : X, ∑ y : Y,
          if exactRevealCode D seed q = history ∧
            q.1 seed.coordinate.val = x ∧
            q.2 seed.coordinate.val = y
          then exactPriorQuestionWeight G n q
          else 0 := by
            calc
              (∑ x : X, ∑ y : Y,
                ∑ q : ExactFullQuestion X Y n,
                  if exactRevealCode D seed q = history ∧
                    q.1 seed.coordinate.val = x ∧
                    q.2 seed.coordinate.val = y
                  then exactPriorQuestionWeight G n q
                  else 0) =
                ∑ y : Y, ∑ q : ExactFullQuestion X Y n,
                ∑ x : X,
                  if exactRevealCode D seed q = history ∧
                    q.1 seed.coordinate.val = x ∧
                    q.2 seed.coordinate.val = y
                  then exactPriorQuestionWeight G n q
                  else 0 :=
                    fullCoordinate_three_sum_rotate _
              _ = _ := fullCoordinate_three_sum_rotate _
    _ = ∑ q : ExactFullQuestion X Y n,
        if exactRevealCode D seed q = history
        then exactPriorQuestionWeight G n q
        else 0 := by
          apply Finset.sum_congr rfl
          intro q _
          by_cases h : exactRevealCode D seed q = history
          · have hsum :
                (∑ xx : X, ∑ yy : Y,
                  if q.1 seed.coordinate.val = xx ∧
                    q.2 seed.coordinate.val = yy
                  then exactPriorQuestionWeight G n q
                  else 0) = exactPriorQuestionWeight G n q := by
                  calc
                    (∑ xx : X, ∑ yy : Y,
                      if q.1 seed.coordinate.val = xx ∧
                        q.2 seed.coordinate.val = yy
                      then exactPriorQuestionWeight G n q
                      else 0) =
                      ∑ xx : X,
                        if q.1 seed.coordinate.val = xx
                        then exactPriorQuestionWeight G n q
                        else 0 := by
                          apply Finset.sum_congr rfl
                          intro xx _
                          by_cases hx : q.1 seed.coordinate.val = xx
                          · simp only [hx, true_and, sum_ite_eq, mem_univ, ↓reduceIte]
                          · simp only [hx, false_and, ↓reduceIte, sum_const_zero]
                    _ = _ := by simp only [sum_ite_eq, mem_univ, ↓reduceIte]
            simpa only [h, true_and, ↓reduceIte] using hsum
          · simp only [h, false_and, ↓reduceIte, sum_const_zero]

theorem exactJointQuestionMass_eq_reveal_mul_question
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y) :
    exactJointQuestionMass G n D seed history x y =
      exactRevealMass G n D seed history *
        G.questionWeight x y := by
  have htotal := exactJointQuestionMass_sum
    G n D seed history
  have htail :
      exactRevealMass G n D seed history =
        exactFairQuestionTailWeight
          G n D seed history x y := by
    calc
      exactRevealMass G n D seed history =
        ∑ xx : X, ∑ yy : Y,
          exactJointQuestionMass
            G n D seed history xx yy := htotal.symm
      _ = ∑ xx : X, ∑ yy : Y,
          G.questionWeight xx yy *
            exactFairQuestionTailWeight
              G n D seed history x y := by
            apply Finset.sum_congr rfl
            intro xx _
            apply Finset.sum_congr rfl
            intro yy _
            rw [exactJointQuestionMass_eq_question_mul_tail]
            rw [exactFairQuestionTailWeight_independent
              G n D seed history xx x yy y]
      _ = (∑ xx : X, ∑ yy : Y,
          G.questionWeight xx yy) *
            exactFairQuestionTailWeight
              G n D seed history x y := by
            simp only [sum_mul]
      _ = exactFairQuestionTailWeight
          G n D seed history x y := by
            rw [G.weight_normalized]
            simp only [one_mul]
  rw [exactJointQuestionMass_eq_question_mul_tail,
    ← htail]
  ring

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace


attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

/-- The total probability mass of exact fair conditioned answer born. -/
def exactFairConditionedAnswerBornMass
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) : ℝ :=
  ∑ xs : Fin n → X, ∑ ys : Fin n → Y,
    exactFiberQuestionWeight
      G n D r.seed r.history x y xs ys *
      bornTracePairing S.state.matrix
        (conditionedAliceEffect G n S D r.aliceAnswer xs)
        (conditionedBobEffect G n S D r.bobAnswer ys)

theorem exactFiberQuestionWeight_eq_zero_of_mass_zero
    (G : Game X Y A B) (n : ℕ)
    (D : Finset (Fin n))
    (seed : ExactRemainingSeed D)
    (history : ExactRevealHistory X Y D seed)
    (x : X) (y : Y)
    (zero : exactFiberQuestionMass
      G n D seed history x y = 0)
    (xs : Fin n → X) (ys : Fin n → Y) :
    exactFiberQuestionWeight
      G n D seed history x y xs ys = 0 := by
  have rows :
      (∑ xx : Fin n → X,
        ∑ yy : Fin n → Y,
          exactFiberQuestionWeight
            G n D seed history x y xx yy) = 0 := by
    exact zero
  have row_zero :
      (∑ yy : Fin n → Y,
        exactFiberQuestionWeight
          G n D seed history x y xs yy) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun xx _ => Finset.sum_nonneg fun yy _ =>
        exactFiberQuestionWeight_nonneg
          G n D seed history x y xx yy)).mp rows xs
      (Finset.mem_univ xs)
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun yy _ => exactFiberQuestionWeight_nonneg
      G n D seed history x y xs yy)).mp row_zero ys
    (Finset.mem_univ ys)

theorem exactFairConditionedAnswerBornMass_eq_fiber_norm
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) :
    exactFairConditionedAnswerBornMass G n S D r x y =
      exactFiberQuestionMass
          G n D r.seed r.history x y *
        ‖exactUnnormalizedPsi G n S D r x y‖ ^ 2 := by
  classical
  by_cases hmass :
      exactFiberQuestionMass
        G n D r.seed r.history x y = 0
  · have hz (xs : Fin n → X) (ys : Fin n → Y) :=
      exactFiberQuestionWeight_eq_zero_of_mass_zero
        G n D r.seed r.history x y hmass xs ys
    simp only [exactFairConditionedAnswerBornMass, hz, zero_mul, sum_const_zero, hmass]
  · rw [exactUnnormalizedPsi_norm_sq]
    have hborn := exactSourceEquationTen
      G n S D r.seed r.history r.aliceAnswer r.bobAnswer
      x y hmass
    unfold exactFairConditionedAnswerBornMass
    rw [hborn, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro xs _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ys _
    unfold exactConditionalQuestionWeight
    field_simp [hmass]

theorem exactFairConditionedAnswerBornMass_eq_reveal_question_norm
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) :
    exactFairConditionedAnswerBornMass G n S D r x y =
      exactRevealMass G n D r.seed r.history *
        G.questionWeight x y *
        ‖exactUnnormalizedPsi G n S D r x y‖ ^ 2 := by
  rw [exactFairConditionedAnswerBornMass_eq_fiber_norm,
    exactFiberQuestionMass_eq_jointQuestionMass,
    exactJointQuestionMass_eq_reveal_mul_question]

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace


open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem exactLocallySampleableCode_fixedSeed_fiber_iff
    {n : ℕ} (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y)
    (o : ExactOutcome X Y A B n) :
    exactLocallySampleableCode D (r.seed, o) =
        (r.seed.coordinate, x, y, r) ↔
      exactRevealCode D r.seed (o.1, o.2.1) = r.history ∧
      o.1 r.seed.coordinate.val = x ∧
      o.2.1 r.seed.coordinate.val = y ∧
      (∀ j : {j : Fin n // j ∈ D},
        o.2.2.1 j.val = r.aliceAnswer j) ∧
      (∀ j : {j : Fin n // j ∈ D},
        o.2.2.2 j.val = r.bobAnswer j) := by
  constructor
  · intro h
    have hx := congrArg
      (fun t : ExactLocallySampleableTuple X Y A B D => t.2.1) h
    have hy := congrArg
      (fun t : ExactLocallySampleableTuple X Y A B D => t.2.2.1) h
    have hr := congrArg
      (fun t : ExactLocallySampleableTuple X Y A B D => t.2.2.2) h
    have hh0 := congrArg
      (fun z : ExactHistoryFlag X Y A B D =>
        if hs : z.seed = r.seed then hs ▸ z.history else r.history) hr
    have hh :
        exactRevealCode D r.seed (o.1, o.2.1) = r.history := by
      simpa only [exactLocallySampleableCode, exactHistoryCode, ↓reduceDIte] using hh0
    refine ⟨hh, hx, hy, ?_, ?_⟩
    · have ha := congrArg ExactHistoryFlag.aliceAnswer hr
      intro j
      exact congrFun ha j
    · have hb := congrArg ExactHistoryFlag.bobAnswer hr
      intro j
      exact congrFun hb j
  · rintro ⟨hh, hx, hy, ha, hb⟩
    have hr : exactHistoryCode D (r.seed, o) = r := by
      apply ExactHistoryFlag.ext
      · rfl
      · exact heq_of_eq hh
      · funext j
        exact ha j
      · funext j
        exact hb j
    change
      (r.seed.coordinate,
        o.1 r.seed.coordinate.val,
        o.2.1 r.seed.coordinate.val,
        exactHistoryCode D (r.seed, o)) =
      (r.seed.coordinate, x, y, r)
    rw [hx, hy, hr]

/-- The total probability mass of exact fair full outcome born. -/
def exactFairFullOutcomeBornMass
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) : ℝ :=
  ∑ o : ExactOutcome X Y A B n,
    if exactLocallySampleableCode D (r.seed, o) =
      (r.seed.coordinate, x, y, r)
    then (strategyEventLaw (G.repeat n) S).weight o
    else 0

theorem exactFairFullOutcomeBornMass_eq_conditioned
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) :
    exactFairFullOutcomeBornMass G n S D r x y =
      exactFairConditionedAnswerBornMass G n S D r x y := by
  classical
  unfold exactFairFullOutcomeBornMass
    exactFairConditionedAnswerBornMass
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro xs _
  apply Finset.sum_congr rfl
  intro ys _
  have hq :
      (exactAliceQuestionCompatible
        D r.seed r.history x xs ∧
        exactBobQuestionCompatible
          D r.seed r.history y ys) ↔
        exactRevealCode D r.seed (xs, ys) = r.history ∧
        xs r.seed.coordinate.val = x ∧
        ys r.seed.coordinate.val = y :=
    (exactRevealCode_compatible_iff
      D r.seed r.history x y xs ys).symm
  by_cases compatible :
      exactAliceQuestionCompatible
        D r.seed r.history x xs ∧
      exactBobQuestionCompatible
        D r.seed r.history y ys
  · have hc := hq.mp compatible
    rw [exactFiberQuestionWeight]
    simp only [ite_eq_left compatible]
    rw [conditionedEffects_born_expansion]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro aa _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro bb _
    have hf := exactLocallySampleableCode_fixedSeed_fiber_iff
      D r x y (xs, ys, aa, bb)
    have ha :
        (∀ (j : Fin n) (hj : j ∈ D),
          aa j = r.aliceAnswer ⟨j, hj⟩) ↔
        (∀ j : {j : Fin n // j ∈ D},
          aa j.val = r.aliceAnswer j) := by
      constructor
      · intro h j
        exact h j.val j.property
      · intro h j hj
        exact h ⟨j, hj⟩
    have hb :
        (∀ (j : Fin n) (hj : j ∈ D),
          bb j = r.bobAnswer ⟨j, hj⟩) ↔
        (∀ j : {j : Fin n // j ∈ D},
          bb j.val = r.bobAnswer j) := by
      constructor
      · intro h j
        exact h j.val j.property
      · intro h j hj
        exact h ⟨j, hj⟩
    by_cases aok : ∀ (j : Fin n) (hj : j ∈ D),
      aa j = r.aliceAnswer ⟨j, hj⟩
    · by_cases bok : ∀ (j : Fin n) (hj : j ∈ D),
          bb j = r.bobAnswer ⟨j, hj⟩
      · have code :
            exactLocallySampleableCode D
              (r.seed, (xs, ys, aa, bb)) =
                (r.seed.coordinate, x, y, r) :=
          hf.mpr ⟨hc.1, hc.2.1, hc.2.2,
            ha.mp aok, hb.mp bok⟩
        simp only [ite_eq_left code, ite_eq_left aok, ite_eq_left bok]
        rfl
      · have notcode :
            exactLocallySampleableCode D
              (r.seed, (xs, ys, aa, bb)) ≠
                (r.seed.coordinate, x, y, r) := by
          intro code
          exact bok (hb.mpr (hf.mp code).2.2.2.2)
        simp only [notcode, ↓reduceIte, Game.repeat_questionWeight, bok, ite_self, mul_zero]
    · have notcode :
          exactLocallySampleableCode D
            (r.seed, (xs, ys, aa, bb)) ≠
              (r.seed.coordinate, x, y, r) := by
        intro code
        exact aok (ha.mpr (hf.mp code).2.2.2.1)
      simp only [notcode, ↓reduceIte, Game.repeat_questionWeight, aok, mul_zero]
  · have notfiber :
        ¬ (exactRevealCode D r.seed (xs, ys) = r.history ∧
          xs r.seed.coordinate.val = x ∧
          ys r.seed.coordinate.val = y) := by
      intro h
      exact compatible (hq.mpr h)
    rw [exactFiberQuestionWeight]
    simp only [ite_eq_right compatible, zero_mul]
    apply Finset.sum_eq_zero
    intro aa _
    apply Finset.sum_eq_zero
    intro bb _
    have notcode :
        exactLocallySampleableCode D
          (r.seed, (xs, ys, aa, bb)) ≠
            (r.seed.coordinate, x, y, r) := by
      intro code
      have h := (exactLocallySampleableCode_fixedSeed_fiber_iff
        D r x y (xs, ys, aa, bb)).mp code
      exact notfiber ⟨h.1, h.2.1, h.2.2.1⟩
    simp only [notcode, ↓reduceIte]

theorem exactFairFullOutcomeBornMass_eq_reveal_question_norm
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) :
    exactFairFullOutcomeBornMass G n S D r x y =
      exactRevealMass G n D r.seed r.history *
        G.questionWeight x y *
        ‖exactUnnormalizedPsi G n S D r x y‖ ^ 2 := by
  rw [exactFairFullOutcomeBornMass_eq_conditioned,
    exactFairConditionedAnswerBornMass_eq_reveal_question_norm]

theorem exactLocallySampleableLaw_eq_fair_born
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) :
    exactLocallySampleableLaw G n S D
        (r.seed.coordinate, x, y, r) =
      if exactHistoryAccepted G n D r then
        (exactSeedWeight r.seed *
          exactRevealMass G n D r.seed r.history *
          G.questionWeight x y *
          ‖exactUnnormalizedPsi G n S D r x y‖ ^ 2) /
          repeatedPostselectionMass G n S D
      else 0 := by
  classical
  by_cases accepted : exactHistoryAccepted G n D r
  · rw [ite_eq_left accepted]
    unfold exactLocallySampleableLaw
      exactSourcePushforward groupedMass
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single r.seed]
    · have hcalc :
          (∑ o : ExactOutcome X Y A B n,
            if exactLocallySampleableCode D (r.seed, o) =
                (r.seed.coordinate, x, y, r) then
              exactPostselectedJointLaw G n S D (r.seed, o)
            else 0) =
          (exactSeedWeight r.seed *
            exactRevealMass G n D r.seed r.history *
            G.questionWeight x y *
            ‖exactUnnormalizedPsi G n S D r x y‖ ^ 2) /
              repeatedPostselectionMass G n S D := by
        calc
          (∑ o : ExactOutcome X Y A B n,
          if exactLocallySampleableCode D (r.seed, o) =
              (r.seed.coordinate, x, y, r) then
            exactPostselectedJointLaw G n S D (r.seed, o)
          else 0) =
          (exactSeedWeight r.seed *
            exactFairFullOutcomeBornMass G n S D r x y) /
              repeatedPostselectionMass G n S D := by
            unfold exactFairFullOutcomeBornMass
            rw [Finset.mul_sum, Finset.sum_div]
            apply Finset.sum_congr rfl
            intro o _
            by_cases code :
                exactLocallySampleableCode D (r.seed, o) =
                  (r.seed.coordinate, x, y, r)
            · have same_history :
                  exactHistoryCode D (r.seed, o) = r :=
                congrArg
                  (fun t : ExactLocallySampleableTuple
                    X Y A B D => t.2.2.2) code
              have won :
                  o ∈ FiniteEventLaw.winEvent
                    (repeatedCoordinateWin G n) D := by
                apply (exactHistoryCode_accepted_iff
                  G n D (r.seed, o)).mp
                rw [same_history]
                exact accepted
              simp only [code, ↓reduceIte, exactPostselectedJointLaw,
                repeatedConditionedOutcomeLaw, conditionedEventDistribution, won,
                repeatedPostselectionMass, postselectionMass]
              ring
            · simp only [code, ↓reduceIte, mul_zero, zero_div]
          _ = _ := by
            rw [exactFairFullOutcomeBornMass_eq_reveal_question_norm]
            ring
      convert hcalc using 1
      apply Finset.sum_congr rfl
      intro o _
      split <;> rfl
    · intro seed _ different
      apply Finset.sum_eq_zero
      intro o _
      have notcode :
          exactLocallySampleableCode D (seed, o) ≠
            (r.seed.coordinate, x, y, r) := by
        intro code
        have same := congrArg
          (fun t : ExactLocallySampleableTuple X Y A B D =>
            t.2.2.2.seed) code
        exact different same
      simp only [notcode, ↓reduceIte]
    · simp only [mem_univ, not_true_eq_false, IsEmpty.forall_iff]
  · rw [ite_eq_right accepted]
    exact exactLocallySampleableLaw_zero_of_not_accepted
      G n S D r.seed.coordinate x y r accepted

end

section

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace


open QuantumParallelRepetition.ClassicalInformation

attribute [local instance] Classical.propDecidable

variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]

theorem exactGlobalHistoryFinPsi_sub_Phi_norm
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (r : ExactHistoryFlag X Y A B D)
    (x : X) (y : Y) :
    ‖(exactGlobalHistoryFinPsi G n S D r x y).val -
      (exactGlobalHistoryFinPhi G n S D r y).val‖ =
      ‖exactPsi G n S D r x y -
        exactPhi G n S D r y‖ := by
  change
    ‖exactGlobalHistoryFinReindex G n S D
        (exactGlobalHistoryVector G n S D r
          (exactPsi G n S D r x y)) -
      exactGlobalHistoryFinReindex G n S D
        (exactGlobalHistoryVector G n S D r
          (exactPhi G n S D r y))‖ = _
  rw [← map_sub, ← exactGlobalHistoryVector_sub,
    LinearIsometryEquiv.norm_map,
    exactGlobalHistoryVector_norm]

theorem exactLocallySampleableLaw_zero_of_coordinate_mismatch
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (i : SourceRemainingCoordinate D) (x : X) (y : Y)
    (r : ExactHistoryFlag X Y A B D)
    (different : i ≠ r.seed.coordinate) :
    exactLocallySampleableLaw G n S D (i, x, y, r) = 0 := by
  classical
  unfold exactLocallySampleableLaw
    exactSourcePushforward groupedMass
  apply Finset.sum_eq_zero
  intro q hq
  have code :
      exactLocallySampleableCode D q = (i, x, y, r) :=
    ((@Finset.mem_filter
      (ExactJointOutcome X Y A B D)
      (fun a => exactLocallySampleableCode D a =
        (i, x, y, r))
      (fun _ => Classical.propDecidable _)
      Finset.univ q).mp hq).2
  have coordinate : q.1.coordinate = i := congrArg
    (fun t : ExactLocallySampleableTuple X Y A B D => t.1) code
  have history : exactHistoryCode D q = r := congrArg
    (fun t : ExactLocallySampleableTuple X Y A B D =>
      t.2.2.2) code
  have seed : q.1 = r.seed := congrArg
    ExactHistoryFlag.seed history
  exact (different
    (coordinate.symm.trans (congrArg ExactForwardSeed.coordinate seed))).elim

theorem exactFairPosteriorExpectation_reindex
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (f : ExactLocallySampleableTuple X Y A B D → ℝ) :
    (∑ t : ExactLocallySampleableTuple X Y A B D,
      exactLocallySampleableLaw G n S D t * f t) =
      ∑ r : ExactHistoryFlag X Y A B D,
      ∑ y : Y, ∑ x : X,
        exactLocallySampleableLaw G n S D
          (r.seed.coordinate, x, y, r) *
        f (r.seed.coordinate, x, y, r) := by
  classical
  calc
    (∑ t : ExactLocallySampleableTuple X Y A B D,
      exactLocallySampleableLaw G n S D t * f t) =
      ∑ i : SourceRemainingCoordinate D,
      ∑ x : X, ∑ y : Y,
      ∑ r : ExactHistoryFlag X Y A B D,
        exactLocallySampleableLaw G n S D (i, x, y, r) *
          f (i, x, y, r) := by
            simp only [Fintype.sum_prod_type, univ_eq_attach]
    _ = ∑ y : Y,
        ∑ r : ExactHistoryFlag X Y A B D,
        ∑ i : SourceRemainingCoordinate D,
        ∑ x : X,
          exactLocallySampleableLaw G n S D (i, x, y, r) *
            f (i, x, y, r) := finite_sum_four_swap _
    _ = ∑ r : ExactHistoryFlag X Y A B D,
        ∑ y : Y,
        ∑ i : SourceRemainingCoordinate D,
        ∑ x : X,
          exactLocallySampleableLaw G n S D (i, x, y, r) *
            f (i, x, y, r) := by
              rw [Finset.sum_comm]
    _ = ∑ r : ExactHistoryFlag X Y A B D,
        ∑ y : Y, ∑ x : X,
        ∑ i : SourceRemainingCoordinate D,
          exactLocallySampleableLaw G n S D (i, x, y, r) *
            f (i, x, y, r) := by
              apply Finset.sum_congr rfl
              intro r _
              apply Finset.sum_congr rfl
              intro y _
              rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_eq_single r.seed.coordinate]
      · intro i _ different
        simp only [exactLocallySampleableLaw_zero_of_coordinate_mismatch G n S D i x y r different,
          zero_mul]
      · simp only [univ_eq_attach, mem_attach, not_true_eq_false, mul_eq_zero, IsEmpty.forall_iff]

/-- The entropy quantity for exact fair accepted alice. -/
def exactFairAcceptedAliceEntropy
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) : ℝ :=
  ∑ r : ExactHistoryFlag X Y A B D,
    if exactHistoryAccepted G n D r then
      exactFairHistoryPriorWeight G n D r *
        exactFairAliceHistoryEntropyIncrement G n S D r
    else 0

/-- The entropy quantity for exact fair accepted bob. -/
def exactFairAcceptedBobEntropy
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) : ℝ :=
  ∑ r : ExactHistoryFlag X Y A B D,
    if exactHistoryAccepted G n D r then
      exactFairHistoryPriorWeight G n D r *
        exactFairBobHistoryEntropyIncrement G n S D r
    else 0

private def exactFairAcceptedAliceVariation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) : ℝ :=
  ∑ r : ExactHistoryFlag X Y A B D,
    if exactHistoryAccepted G n D r then
      exactFairHistoryPriorWeight G n D r *
        exactFairAliceHistoryVariation G n S D r
    else 0

private def exactFairAcceptedBobVariation
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) : ℝ :=
  ∑ r : ExactHistoryFlag X Y A B D,
    if exactHistoryAccepted G n D r then
      exactFairHistoryPriorWeight G n D r *
        exactFairBobHistoryVariation G n S D r
    else 0

theorem exactFairPsiPhiDistance_mul_postselection_le
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D) :
    (∑ t : ExactLocallySampleableTuple X Y A B D,
      exactLocallySampleableLaw G n S D t *
        ‖exactSourceTuplePsi G n S D t -
          exactSourceTuplePhi G n S D t‖ ^ 2) *
        repeatedPostselectionMass G n S D ≤
      4 * exactFairAcceptedAliceVariation G n S D := by
  classical
  rw [exactFairPosteriorExpectation_reindex]
  simp_rw [Finset.sum_mul]
  calc
    (∑ r : ExactHistoryFlag X Y A B D,
      ∑ y : Y, ∑ x : X,
        (exactLocallySampleableLaw G n S D
          (r.seed.coordinate, x, y, r) *
          ‖exactSourceTuplePsi G n S D
              (r.seed.coordinate, x, y, r) -
            exactSourceTuplePhi G n S D
              (r.seed.coordinate, x, y, r)‖ ^ 2) *
          repeatedPostselectionMass G n S D) ≤
      ∑ r : ExactHistoryFlag X Y A B D,
      ∑ y : Y, ∑ x : X,
        if exactHistoryAccepted G n D r then
          4 * (exactFairHistoryPriorWeight G n D r *
            G.questionWeight x y *
            ‖exactUnnormalizedPsi G n S D r x y -
              exactUnnormalizedPhi G n S D r y‖ ^ 2)
        else 0 := by
          apply Finset.sum_le_sum
          intro r _
          apply Finset.sum_le_sum
          intro y _
          apply Finset.sum_le_sum
          intro x _
          by_cases accepted : exactHistoryAccepted G n D r
          · rw [ite_eq_left accepted,
              exactLocallySampleableLaw_eq_fair_born,
              ite_eq_left accepted]
            change
              ((_ / repeatedPostselectionMass G n S D) *
                ‖(exactGlobalHistoryFinPsi
                    G n S D r x y).val -
                  (exactGlobalHistoryFinPhi
                    G n S D r y).val‖ ^ 2) *
                  repeatedPostselectionMass G n S D ≤ _
            rw [exactGlobalHistoryFinPsi_sub_Phi_norm]
            have hnorm :=
              exactPsiPhi_BornWeighted_normalized_distance
                G n S D r x y
            have hw :
                0 ≤ exactFairHistoryPriorWeight G n D r *
                  G.questionWeight x y :=
              mul_nonneg
                (exactFairHistoryPriorWeight_nonneg G n D r)
                (G.weight_nonneg x y)
            have hscaled := mul_le_mul_of_nonneg_left hnorm hw
            unfold exactFairHistoryPriorWeight at hscaled ⊢
            field_simp [positive.ne']
            linarith
          · rw [ite_eq_right accepted,
              exactLocallySampleableLaw_eq_fair_born,
              ite_eq_right accepted]
            simp only [zero_mul, Std.le_refl]
    _ = 4 * exactFairAcceptedAliceVariation G n S D := by
      unfold exactFairAcceptedAliceVariation
        exactFairAliceHistoryVariation
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      by_cases accepted : exactHistoryAccepted G n D r
      · simp only [ite_eq_left accepted, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        apply Finset.sum_congr rfl
        intro x _
        ring
      · simp only [accepted, ↓reduceIte, sum_const_zero, mul_zero]

theorem exactFairGammaPsiDistance_mul_postselection_le
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D) :
    (∑ t : ExactLocallySampleableTuple X Y A B D,
      exactLocallySampleableLaw G n S D t *
        ‖exactSourceTupleGamma G n S D t -
          exactSourceTuplePsi G n S D t‖ ^ 2) *
        repeatedPostselectionMass G n S D ≤
      4 * exactFairAcceptedBobVariation G n S D := by
  classical
  rw [exactFairPosteriorExpectation_reindex]
  simp_rw [Finset.sum_mul]
  calc
    (∑ r : ExactHistoryFlag X Y A B D,
      ∑ y : Y, ∑ x : X,
        (exactLocallySampleableLaw G n S D
          (r.seed.coordinate, x, y, r) *
          ‖exactSourceTupleGamma G n S D
              (r.seed.coordinate, x, y, r) -
            exactSourceTuplePsi G n S D
              (r.seed.coordinate, x, y, r)‖ ^ 2) *
          repeatedPostselectionMass G n S D) ≤
      ∑ r : ExactHistoryFlag X Y A B D,
      ∑ y : Y, ∑ x : X,
        if exactHistoryAccepted G n D r then
          4 * (exactFairHistoryPriorWeight G n D r *
            G.questionWeight x y *
            ‖exactUnnormalizedGamma G n S D r x -
              exactUnnormalizedPsi G n S D r x y‖ ^ 2)
        else 0 := by
          apply Finset.sum_le_sum
          intro r _
          apply Finset.sum_le_sum
          intro y _
          apply Finset.sum_le_sum
          intro x _
          by_cases accepted : exactHistoryAccepted G n D r
          · rw [ite_eq_left accepted,
              exactLocallySampleableLaw_eq_fair_born,
              ite_eq_left accepted]
            change
              ((_ / repeatedPostselectionMass G n S D) *
                ‖(exactGlobalHistoryFinGamma
                    G n S D r x).val -
                  (exactGlobalHistoryFinPsi
                    G n S D r x y).val‖ ^ 2) *
                  repeatedPostselectionMass G n S D ≤ _
            rw [exactGlobalHistoryFinGamma_sub_Psi_norm]
            have hnorm :=
              exactGammaPsi_BornWeighted_normalized_distance
                G n S D r x y
            have hw :
                0 ≤ exactFairHistoryPriorWeight G n D r *
                  G.questionWeight x y :=
              mul_nonneg
                (exactFairHistoryPriorWeight_nonneg G n D r)
                (G.weight_nonneg x y)
            have hscaled := mul_le_mul_of_nonneg_left hnorm hw
            unfold exactFairHistoryPriorWeight at hscaled ⊢
            field_simp [positive.ne']
            linarith
          · rw [ite_eq_right accepted,
              exactLocallySampleableLaw_eq_fair_born,
              ite_eq_right accepted]
            simp only [zero_mul, Std.le_refl]
    _ = 4 * exactFairAcceptedBobVariation G n S D := by
      unfold exactFairAcceptedBobVariation
        exactFairBobHistoryVariation
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      by_cases accepted : exactHistoryAccepted G n D r
      · simp only [ite_eq_left accepted, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        rw [norm_sub_rev]
        ring
      · simp only [accepted, ↓reduceIte, sum_const_zero, mul_zero]

/-- The numerical bound for exact fair operator entropy. -/
def ExactFairOperatorEntropyBound
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (η : ℝ) : Prop :=
  exactFairAcceptedAliceEntropy G n S D ≤
      2 * (repeatedPostselectionMass G n S D * η) ∧
  exactFairAcceptedBobEntropy G n S D ≤
      2 * (repeatedPostselectionMass G n S D * η)

theorem exactSourceStateDistanceBound_of_fair_operator_entropy
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (η : ℝ)
    (positive : 0 < repeatedPostselectionMass G n S D)
    (entropy : ExactFairOperatorEntropyBound
      G n S D η) :
    ExactSourceStateDistanceBound G n S D η := by
  constructor
  · have hv := exactFairGammaPsiDistance_mul_postselection_le
      G n S D positive
    have hj := exactAcceptedFairBobVariation_le_entropy
      G n S D
    change exactFairAcceptedBobVariation G n S D ≤
      exactFairAcceptedBobEntropy G n S D at hj
    have hb := entropy.2
    have hscaled := mul_le_mul_of_nonneg_left hj (by norm_num : (0 : ℝ) ≤ 4)
    have hbudget := mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 4)
    change
      (∑ t : ExactLocallySampleableTuple X Y A B D,
        exactLocallySampleableLaw G n S D t *
          ‖exactSourceTupleGamma G n S D t -
            exactSourceTuplePsi G n S D t‖ ^ 2) ≤ 8 * η
    nlinarith
  · have hv := exactFairPsiPhiDistance_mul_postselection_le
      G n S D positive
    have hj := exactAcceptedFairAliceVariation_le_entropy
      G n S D
    change exactFairAcceptedAliceVariation G n S D ≤
      exactFairAcceptedAliceEntropy G n S D at hj
    have ha := entropy.1
    have hscaled := mul_le_mul_of_nonneg_left hj (by norm_num : (0 : ℝ) ≤ 4)
    have hbudget := mul_le_mul_of_nonneg_left ha (by norm_num : (0 : ℝ) ≤ 4)
    change
      (∑ t : ExactLocallySampleableTuple X Y A B D,
        exactLocallySampleableLaw G n S D t *
          ‖exactSourceTuplePsi G n S D t -
            exactSourceTuplePhi G n S D t‖ ^ 2) ≤ 8 * η
    nlinarith

end

end QuantumParallelRepetition

end
