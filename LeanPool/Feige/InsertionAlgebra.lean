/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.ChainCalibration
import LeanPool.Feige.TransferAlgebra

/-!
# Algebraic bookkeeping for chain insertion

This file isolates the finite mass calculations in the chain-insertion
proof of Theorem 2.1.  The analytic content of the exponential transfer
step is kept separate: once that step supplies the sign of `η`, the results below identify the new
chain mixture as an upward transfer inside each pair `{Cⱼ, Hⱼ}`.
-/

namespace Feige

section PairMasses

variable {A B F w θ : ℕ → ℝ} {p : ℝ}

/-- The insertion-position weight. -/
def insertionWeight (θ : ℕ → ℝ) (j : ℕ) : ℝ :=
  chainMass θ j

/-- Averaged mass placed at the lower state `Cⱼ`. -/
def insertedLowerMass (B w θ : ℕ → ℝ) (j : ℕ) : ℝ :=
  θ (j + 1) * (B j - B (j + 1)) + insertionWeight θ j * w j

/-- Averaged mass placed at the upper state `Hⱼ`. -/
def insertedUpperMass (A θ : ℕ → ℝ) (j : ℕ) : ℝ :=
  (1 - θ (j + 1)) * (A j - A (j + 1))

/-- Mass at `Cⱼ` before replacing the independent Bernoulli reveal. -/
def independentLowerMass (F : ℕ → ℝ) (p : ℝ) (j : ℕ) : ℝ :=
  (1 - p) * (F j - F (j + 1))

/-- Mass at `Hⱼ` before replacing the independent Bernoulli reveal. -/
def independentUpperMass (F : ℕ → ℝ) (p : ℝ) (j : ℕ) : ℝ :=
  p * (F j - F (j + 1))

/-- Mass assigned to `Cⱼ` by the chain whose insertion rank is `J`.
The state is absent for `J < j`, has the bridge mass `wⱼ` for `J = j`,
and has the ordinary `B`-chain mass for `j < J`. -/
def lowerMassForInsertion (B w : ℕ → ℝ) (J j : ℕ) : ℝ :=
  if J = j then w j else if j < J then B j - B (j + 1) else 0

/-- Mass assigned to `Hⱼ` by the chain whose insertion rank is `J`.
This state occurs exactly for `J ≤ j`. -/
def upperMassForInsertion (A : ℕ → ℝ) (J j : ℕ) : ℝ :=
  if J ≤ j then A j - A (j + 1) else 0

/-- Pairwise expansion of the expectation for the chain whose insertion
rank is `J`. -/
noncomputable def insertionPairScore
    (A B w gLower gUpper : ℕ → ℝ) (k J : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k,
    (lowerMassForInsertion B w J j * gLower j +
      upperMassForInsertion A J j * gUpper j)

/-- The same inserted-chain score indexed by its consecutive chain level:
levels through `J` are lower states and later levels are upper states. -/
noncomputable def insertionLevelScore
    (A B w gLower gUpper : ℕ → ℝ) (J r : ℕ) : ℝ :=
  if r ≤ J then
    lowerMassForInsertion B w J r * gLower r
  else
    upperMassForInsertion A J (r - 1) * gUpper (r - 1)

/-- The pairwise and consecutive-level expansions of one inserted-chain
expectation agree. -/
theorem insertionPairScore_eq_levelScore
    {A B w gLower gUpper : ℕ → ℝ} {k J : ℕ} (hJk : J < k) :
    insertionPairScore A B w gLower gUpper k J =
      ∑ r ∈ Finset.range (k + 1),
        insertionLevelScore A B w gLower gUpper J r := by
  classical
  have hrange : Finset.range (J + 1) ⊆ Finset.range k := by
    intro r hr
    simp only [Finset.mem_range] at hr ⊢
    omega
  have hlower :
      (∑ j ∈ Finset.range k,
          lowerMassForInsertion B w J j * gLower j) =
        ∑ j ∈ Finset.range (J + 1),
          lowerMassForInsertion B w J j * gLower j := by
    symm
    apply Finset.sum_subset hrange
    intro j hjk hjnot
    have hjgt : J < j := by
      simp only [Finset.mem_range, not_lt] at hjnot
      omega
    simp [lowerMassForInsertion, ne_of_lt hjgt, not_lt_of_ge hjgt.le]
  have hIco : Finset.Ico J k ⊆ Finset.range k := by
    intro r hr
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hr).2
  have hupper :
      (∑ j ∈ Finset.range k,
          upperMassForInsertion A J j * gUpper j) =
        ∑ j ∈ Finset.Ico J k,
          upperMassForInsertion A J j * gUpper j := by
    symm
    apply Finset.sum_subset hIco
    intro j hjk hjnot
    have hjlt : j < J := by
      simp only [Finset.mem_Ico, not_and_or, not_lt] at hjnot
      rcases hjnot with hjlt | hkj
      · exact Nat.lt_of_not_ge hjlt
      · exact False.elim ((not_le_of_gt (Finset.mem_range.mp hjk)) hkj)
    simp [upperMassForInsertion, not_le_of_gt hjlt]
  unfold insertionPairScore
  rw [Finset.sum_add_distrib, hlower, hupper]
  rw [← Finset.sum_Ico_add_right_sub_eq J k 1
    (f := fun r ↦ upperMassForInsertion A J r * gUpper r)]
  rw [← Finset.sum_range_add_sum_Ico
    (insertionLevelScore A B w gLower gUpper J)
    (by omega : J + 1 ≤ k + 1)]
  refine congrArg₂ (· + ·) ?_ ?_
  · apply Finset.sum_congr rfl
    intro r hr
    simp only [insertionLevelScore]
    rw [ite_eq_left (by
      have := Finset.mem_range.mp hr
      omega : r ≤ J)]
  · apply Finset.sum_congr rfl
    intro r hr
    simp only [insertionLevelScore]
    rw [ite_eq_right (by
      have := (Finset.mem_Ico.mp hr).1
      omega : ¬r ≤ J)]

/-- Statistic sequence along the chain with insertion rank `J`: the
pre-insertion levels use `B`, and the post-insertion levels use `A` with
their index shifted by one. -/
def insertionStatisticSequence (A B : ℕ → ℝ) (J r : ℕ) : ℝ :=
  if r ≤ J then B r else A (r - 1)

/-- At a lower state `Cⱼ` which is present in the rank-`J` chain, the
adjacent-difference chain mass is exactly the corresponding lower
contribution. -/
theorem chainMass_insertionStatisticSequence_lower
    {A B w : ℕ → ℝ} {J j : ℕ} (hjJ : j ≤ J)
    (hbridge : B j - A j = w j) :
    chainMass (insertionStatisticSequence A B J) j =
      lowerMassForInsertion B w J j := by
  by_cases hEq : J = j
  · subst J
    simp [chainMass, insertionStatisticSequence, lowerMassForInsertion,
      hbridge]
  · have hjlt : j < J := lt_of_le_of_ne hjJ (Ne.symm hEq)
    simp [chainMass, insertionStatisticSequence, lowerMassForInsertion,
      hEq, hjlt, hjJ]

/-- At an upper state `Hⱼ`, present exactly for `J ≤ j`, the
adjacent-difference chain mass is its upper contribution. -/
theorem chainMass_insertionStatisticSequence_upper
    {A B : ℕ → ℝ} {J j : ℕ} (hJj : J ≤ j) :
    chainMass (insertionStatisticSequence A B J) (j + 1) =
      upperMassForInsertion A J j := by
  simp only [chainMass, insertionStatisticSequence, upperMassForInsertion,
    ite_eq_left hJj]
  rw [ite_eq_right (by omega : ¬j + 1 ≤ J), ite_eq_right (by omega : ¬j + 1 + 1 ≤ J)]
  congr 1

/-- The upward mass-transfer coefficient. -/
def insertionTransfer (A F θ : ℕ → ℝ) (p : ℝ) (j : ℕ) : ℝ :=
  insertedUpperMass A θ j - independentUpperMass F p j

/-- The lower and upper mass formulas preserve the total mass of each pair
`{Cⱼ, Hⱼ}`. -/
theorem inserted_pair_total (j : ℕ)
    (hB : ∀ r, B r = A r + w r)
    (hF : ∀ r, F r = A r + θ r * w r) :
    insertedLowerMass B w θ j + insertedUpperMass A θ j =
      F j - F (j + 1) := by
  simp only [insertedLowerMass, insertedUpperMass, insertionWeight, chainMass]
  rw [hB j, hB (j + 1), hF j, hF (j + 1)]
  ring

theorem independent_pair_total (F : ℕ → ℝ) (p : ℝ) (j : ℕ) :
    independentLowerMass F p j + independentUpperMass F p j =
      F j - F (j + 1) := by
  simp [independentLowerMass, independentUpperMass]
  ring

/-- Equal pair totals force the difference to be a within-pair transfer:
the lower state loses exactly the mass gained by the upper state. -/
theorem lower_difference_eq_neg_transfer (j : ℕ)
    (hB : ∀ r, B r = A r + w r)
    (hF : ∀ r, F r = A r + θ r * w r) :
    insertedLowerMass B w θ j - independentLowerMass F p j =
      -insertionTransfer A F θ p j := by
  have hnew := inserted_pair_total (A := A) (B := B) (F := F)
    (w := w) (θ := θ) j hB hF
  have hold := independent_pair_total F p j
  simp only [insertionTransfer] at *
  linarith

/-- A nonnegative transfer improves every increasing payoff on the pair. -/
theorem upward_transfer_improves
    {newLower newUpper oldLower oldUpper η gLower gUpper : ℝ}
    (hlower : newLower - oldLower = -η)
    (hupper : newUpper - oldUpper = η)
    (hη : 0 ≤ η) (hg : gLower ≤ gUpper) :
    oldLower * gLower + oldUpper * gUpper ≤
      newLower * gLower + newUpper * gUpper := by
  have hnewLower : newLower = oldLower - η := by linarith
  have hnewUpper : newUpper = oldUpper + η := by linarith
  have hdiff :
      (newLower * gLower + newUpper * gUpper) -
          (oldLower * gLower + oldUpper * gUpper) =
        η * (gUpper - gLower) := by
    rw [hnewLower, hnewUpper]
    ring
  rw [← sub_nonneg, hdiff]
  exact mul_nonneg hη (sub_nonneg.mpr hg)

/-- Summing the pairwise upward transfers proves the expectation
comparison. -/
theorem sum_upward_transfers_improve
    {k : ℕ}
    {newLower newUpper oldLower oldUpper η gLower gUpper : ℕ → ℝ}
    (hlower : ∀ j < k, newLower j - oldLower j = -η j)
    (hupper : ∀ j < k, newUpper j - oldUpper j = η j)
    (hη : ∀ j < k, 0 ≤ η j)
    (hg : ∀ j < k, gLower j ≤ gUpper j) :
    (∑ j ∈ Finset.range k,
        (oldLower j * gLower j + oldUpper j * gUpper j)) ≤
      ∑ j ∈ Finset.range k,
        (newLower j * gLower j + newUpper j * gUpper j) := by
  apply Finset.sum_le_sum
  intro j hj
  have hjk := Finset.mem_range.mp hj
  exact upward_transfer_improves (hlower j hjk) (hupper j hjk)
    (hη j hjk) (hg j hjk)

end PairMasses

section Weights

/-- The insertion-position weights are nonnegative when `θ` decreases. -/
theorem insertionWeight_nonneg {θ : ℕ → ℝ} (hθ : Antitone θ) (j : ℕ) :
    0 ≤ insertionWeight θ j := by
  simpa only [insertionWeight, chainMass] using
    sub_nonneg.mpr (hθ (Nat.le_succ j))

/-- The insertion-position weights telescope from `θ 0` to `θ k`. -/
theorem sum_insertionWeight (θ : ℕ → ℝ) (k : ℕ) :
    (∑ j ∈ Finset.range k, insertionWeight θ j) = θ 0 - θ k := by
  change (∑ j ∈ Finset.range k, chainMass θ j) = θ 0 - θ k
  simpa using CalibratedChain.sum_chainMass_shift θ 0 k

/-- Under the endpoint conditions `θ 0 = 1` and `θ k = 0`, the insertion
weights sum to one. -/
theorem sum_insertionWeight_eq_one {θ : ℕ → ℝ} {k : ℕ}
    (hzero : θ 0 = 1) (hend : θ k = 0) :
    (∑ j ∈ Finset.range k, insertionWeight θ j) = 1 := by
  rw [sum_insertionWeight, hzero, hend, sub_zero]

private theorem lowerMassForInsertion_split (B w : ℕ → ℝ) (J j : ℕ) :
    lowerMassForInsertion B w J j =
      (if J = j then w j else 0) +
        (if j < J then B j - B (j + 1) else 0) := by
  unfold lowerMassForInsertion
  by_cases hEq : J = j
  · subst J
    simp
  · by_cases hlt : j < J <;> simp [hEq, hlt]

/-- Averaging the actual `Cⱼ` mass over all insertion ranks separates into
the single bridge rank and the strictly later ranks. -/
theorem sum_lowerMassForInsertion
    {B w θ : ℕ → ℝ} {j k : ℕ} (hjk : j < k) :
    (∑ J ∈ Finset.range k,
        insertionWeight θ J * lowerMassForInsertion B w J j) =
      (∑ J ∈ Finset.Ico (j + 1) k, insertionWeight θ J) *
          (B j - B (j + 1)) +
        insertionWeight θ j * w j := by
  classical
  simp_rw [lowerMassForInsertion_split, mul_add]
  rw [Finset.sum_add_distrib]
  have heq :
      (Finset.range k).filter (fun J ↦ j < J) =
        Finset.Ico (j + 1) k := by
    ext J
    simp
    omega
  calc
    (∑ J ∈ Finset.range k,
        insertionWeight θ J * (if J = j then w j else 0)) +
        ∑ J ∈ Finset.range k,
          insertionWeight θ J *
            (if j < J then B j - B (j + 1) else 0) =
      insertionWeight θ j * w j +
        ∑ J ∈ (Finset.range k).filter (fun J ↦ j < J),
          insertionWeight θ J * (B j - B (j + 1)) := by
            congr 1
            · simp [hjk]
            · rw [Finset.sum_filter]
              apply Finset.sum_congr rfl
              intro J hJ
              by_cases hlt : j < J <;> simp [hlt]
    _ = insertionWeight θ j * w j +
        (∑ J ∈ Finset.Ico (j + 1) k, insertionWeight θ J) *
          (B j - B (j + 1)) := by
      rw [heq, Finset.sum_mul]
    _ = _ := by ring

/-- Averaging the actual `Hⱼ` mass over all insertion ranks keeps exactly
the ranks through `j`. -/
theorem sum_upperMassForInsertion
    {A θ : ℕ → ℝ} {j k : ℕ} (hjk : j < k) :
    (∑ J ∈ Finset.range k,
        insertionWeight θ J * upperMassForInsertion A J j) =
      (∑ J ∈ Finset.range (j + 1), insertionWeight θ J) *
        (A j - A (j + 1)) := by
  classical
  have heq :
      (Finset.range k).filter (fun J ↦ J ≤ j) =
        Finset.range (j + 1) := by
    ext J
    simp
    omega
  unfold upperMassForInsertion
  calc
    (∑ J ∈ Finset.range k,
        insertionWeight θ J *
          (if J ≤ j then A j - A (j + 1) else 0)) =
      ∑ J ∈ (Finset.range k).filter (fun J ↦ J ≤ j),
        insertionWeight θ J * (A j - A (j + 1)) := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro J hJ
          by_cases hle : J ≤ j <;> simp [hle]
    _ = (∑ J ∈ Finset.range (j + 1), insertionWeight θ J) *
        (A j - A (j + 1)) := by
      rw [heq, Finset.sum_mul]

/-- The total insertion weight strictly after rank `j`.  This is the
coefficient of `Bⱼ - Bⱼ₊₁` in the averaged mass at `Cⱼ`. -/
theorem sum_insertionWeight_after {θ : ℕ → ℝ} {j k : ℕ}
    (hjk : j < k) (hend : θ k = 0) :
    (∑ J ∈ Finset.Ico (j + 1) k, insertionWeight θ J) = θ (j + 1) := by
  have htel :
      (∑ J ∈ Finset.Ico (j + 1) k, chainMass θ J) =
        θ (j + 1) - θ k :=
    CalibratedChain.sum_chainMass_Ico θ (Nat.succ_le_iff.mpr hjk)
  simpa only [insertionWeight, chainMass, hend, sub_zero] using htel

/-- The total insertion weight through rank `j`.  This is the coefficient
of `Aⱼ - Aⱼ₊₁` in the averaged mass at `Hⱼ`. -/
theorem sum_insertionWeight_through {θ : ℕ → ℝ} (j : ℕ)
    (hzero : θ 0 = 1) :
    (∑ J ∈ Finset.range (j + 1), insertionWeight θ J) =
      1 - θ (j + 1) := by
  rw [sum_insertionWeight, hzero]

/-- The averaged lower-mass formula obtained by separating the insertion
rank `J = j` from all later ranks. -/
theorem averaged_lower_mass_eq_insertedLowerMass
    {B w θ : ℕ → ℝ} {j k : ℕ} (hjk : j < k) (hend : θ k = 0) :
    (∑ J ∈ Finset.Ico (j + 1) k, insertionWeight θ J) *
          (B j - B (j + 1)) +
        insertionWeight θ j * w j =
      insertedLowerMass B w θ j := by
  rw [sum_insertionWeight_after hjk hend]
  rfl

/-- The averaged upper-mass formula obtained by summing over all insertion
ranks `J ≤ j`. -/
theorem averaged_upper_mass_eq_insertedUpperMass
    {A θ : ℕ → ℝ} (j : ℕ) (hzero : θ 0 = 1) :
    (∑ J ∈ Finset.range (j + 1), insertionWeight θ J) *
        (A j - A (j + 1)) =
      insertedUpperMass A θ j := by
  rw [sum_insertionWeight_through j hzero]
  rfl

/-- The full weighted rank average gives the lower-mass formula. -/
theorem weighted_lowerMassForInsertion_eq
    {B w θ : ℕ → ℝ} {j k : ℕ}
    (hjk : j < k) (hend : θ k = 0) :
    (∑ J ∈ Finset.range k,
        insertionWeight θ J * lowerMassForInsertion B w J j) =
      insertedLowerMass B w θ j := by
  rw [sum_lowerMassForInsertion hjk,
    averaged_lower_mass_eq_insertedLowerMass hjk hend]

/-- The full weighted rank average gives the upper-mass formula. -/
theorem weighted_upperMassForInsertion_eq
    {A θ : ℕ → ℝ} {j k : ℕ}
    (hjk : j < k) (hzero : θ 0 = 1) :
    (∑ J ∈ Finset.range k,
        insertionWeight θ J * upperMassForInsertion A J j) =
      insertedUpperMass A θ j := by
  rw [sum_upperMassForInsertion hjk,
    averaged_upper_mass_eq_insertedUpperMass j hzero]

/-- Averaging the complete pairwise scores over insertion ranks gives the
averaged lower and upper masses. -/
theorem weighted_insertionPairScore_eq
    {A B w θ gLower gUpper : ℕ → ℝ} {k : ℕ}
    (hθ0 : θ 0 = 1) (hθk : θ k = 0) :
    (∑ J ∈ Finset.range k,
        insertionWeight θ J *
          insertionPairScore A B w gLower gUpper k J) =
      ∑ j ∈ Finset.range k,
        (insertedLowerMass B w θ j * gLower j +
          insertedUpperMass A θ j * gUpper j) := by
  unfold insertionPairScore
  simp only [Finset.mul_sum, mul_add]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk := Finset.mem_range.mp hj
  rw [Finset.sum_add_distrib]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  rw [weighted_lowerMassForInsertion_eq hjk hθk,
    weighted_upperMassForInsertion_eq hjk hθ0]

/-- A convex average cannot exceed all of its entries.  This is the final
finite step selecting one insertion position from the averaged chain
comparison. -/
theorem exists_score_ge_of_le_convex_average
    {k : ℕ} (hk : 0 < k) {weight score : ℕ → ℝ} {old : ℝ}
    (hweight : ∀ j < k, 0 ≤ weight j)
    (hsum : (∑ j ∈ Finset.range k, weight j) = 1)
    (hold : old ≤ ∑ j ∈ Finset.range k, weight j * score j) :
    ∃ j < k, old ≤ score j := by
  have hne : (Finset.range k).Nonempty := by
    exact ⟨0, Finset.mem_range.mpr hk⟩
  obtain ⟨j, hj, hjmax⟩ :=
    Finset.exists_max_image (Finset.range k) score hne
  refine ⟨j, Finset.mem_range.mp hj, hold.trans ?_⟩
  calc
    (∑ r ∈ Finset.range k, weight r * score r) ≤
        ∑ r ∈ Finset.range k, weight r * score j := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_left (hjmax r hr)
        (hweight r (Finset.mem_range.mp hr))
    _ = (∑ r ∈ Finset.range k, weight r) * score j := by
      rw [Finset.sum_mul]
    _ = score j := by rw [hsum, one_mul]

end Weights

section TransferSign

/-- The local transfer identity identifies the insertion coefficient `η`;
positivity of its four factors gives the upward transfer direction. -/
theorem insertionTransfer_nonneg_of_identity
    {η a c d w thetaPlus thetaMinus : ℝ}
    (hid :
      η = ((a - c) / (c + d)) * w * (thetaPlus - thetaMinus))
    (hac : c ≤ a) (hcd : 0 < c + d) (hw : 0 ≤ w)
    (hθ : thetaMinus ≤ thetaPlus) :
    0 ≤ η := by
  rw [hid]
  positivity

end TransferSign

section LocalInsertionConclusion

open scoped BigOperators

/-- The finite mass-transport conclusion of the chain-insertion step.

Once the exponential transfer identity has supplied the required factorized
transfer on every edge, the independently revealed coordinate is dominated
by the averaged inserted-chain law for every payoff which is increasing on
each pair `Cⱼ ⊆ Hⱼ`.  All remaining hypotheses are the corresponding
analytic and probabilistic identities. -/
theorem localInsertion_average_pair_payoff_le
    {k : ℕ} {A B F w θ a : ℕ → ℝ} {p c d : ℝ}
    {gLower gUpper : ℕ → ℝ}
    (hB : ∀ r, B r = A r + w r)
    (hF : ∀ r, F r = A r + θ r * w r)
    (hθ : Antitone θ)
    (hac : ∀ j < k, c ≤ a j)
    (hcd : 0 < c + d)
    (hw : ∀ j < k, 0 ≤ w j)
    (htransfer : ∀ j < k,
      insertionTransfer A F θ p j =
        ((a j - c) / (c + d)) * w j * (θ j - θ (j + 1)))
    (hg : ∀ j < k, gLower j ≤ gUpper j) :
    (∑ j ∈ Finset.range k,
        (independentLowerMass F p j * gLower j +
          independentUpperMass F p j * gUpper j)) ≤
      ∑ j ∈ Finset.range k,
        (insertedLowerMass B w θ j * gLower j +
          insertedUpperMass A θ j * gUpper j) := by
  apply sum_upward_transfers_improve
      (η := fun j ↦ insertionTransfer A F θ p j)
  · intro j hj
    exact lower_difference_eq_neg_transfer j hB hF
  · intro j hj
    rfl
  · intro j hj
    exact insertionTransfer_nonneg_of_identity
      (htransfer j hj) (hac j hj) hcd (hw j hj)
      (hθ (Nat.le_succ j))
  · exact hg

/-- Full finite selection step in the chain-insertion argument.

The two equalities `hold` and `haverage` are precisely the expansions of
the old hybrid expectation and of the convex average of inserted-chain
expectations.  The theorem first applies the upward-transport comparison
and then selects one insertion rank from that convex average. -/
theorem exists_localInsertion_score_of_transfer
    {k : ℕ} (hk : 0 < k)
    {A B F w θ a : ℕ → ℝ} {p c d old : ℝ}
    {gLower gUpper score : ℕ → ℝ}
    (hB : ∀ r, B r = A r + w r)
    (hF : ∀ r, F r = A r + θ r * w r)
    (hθ : Antitone θ)
    (hθ0 : θ 0 = 1) (hθk : θ k = 0)
    (hac : ∀ j < k, c ≤ a j)
    (hcd : 0 < c + d)
    (hw : ∀ j < k, 0 ≤ w j)
    (htransfer : ∀ j < k,
      insertionTransfer A F θ p j =
        ((a j - c) / (c + d)) * w j * (θ j - θ (j + 1)))
    (hg : ∀ j < k, gLower j ≤ gUpper j)
    (hold : old =
      ∑ j ∈ Finset.range k,
        (independentLowerMass F p j * gLower j +
          independentUpperMass F p j * gUpper j))
    (haverage :
      (∑ j ∈ Finset.range k,
          insertionWeight θ j * score j) =
        ∑ j ∈ Finset.range k,
          (insertedLowerMass B w θ j * gLower j +
            insertedUpperMass A θ j * gUpper j)) :
    ∃ j < k, old ≤ score j := by
  have htransport :
      old ≤ ∑ j ∈ Finset.range k, insertionWeight θ j * score j := by
    rw [hold, haverage]
    exact localInsertion_average_pair_payoff_le hB hF hθ hac hcd hw
      htransfer hg
  exact exists_score_ge_of_le_convex_average hk
    (fun j hj ↦ insertionWeight_nonneg hθ j)
    (sum_insertionWeight_eq_one hθ0 hθk) htransport

/-- The finite chain-insertion conclusion with the inserted-chain score
expanded canonically into its `Cⱼ/Hⱼ` pairs.  Unlike
`exists_localInsertion_score_of_transfer`, this theorem no longer asks for
the averaged-score identity as an external hypothesis. -/
theorem exists_insertionPairScore_of_transfer
    {k : ℕ} (hk : 0 < k)
    {A B F w θ a : ℕ → ℝ} {p c d old : ℝ}
    {gLower gUpper : ℕ → ℝ}
    (hB : ∀ r, B r = A r + w r)
    (hF : ∀ r, F r = A r + θ r * w r)
    (hθ : Antitone θ)
    (hθ0 : θ 0 = 1) (hθk : θ k = 0)
    (hac : ∀ j < k, c ≤ a j)
    (hcd : 0 < c + d)
    (hw : ∀ j < k, 0 ≤ w j)
    (htransfer : ∀ j < k,
      insertionTransfer A F θ p j =
        ((a j - c) / (c + d)) * w j * (θ j - θ (j + 1)))
    (hg : ∀ j < k, gLower j ≤ gUpper j)
    (hold : old =
      ∑ j ∈ Finset.range k,
        (independentLowerMass F p j * gLower j +
          independentUpperMass F p j * gUpper j)) :
    ∃ j < k,
      old ≤ insertionPairScore A B w gLower gUpper k j := by
  apply exists_localInsertion_score_of_transfer hk hB hF hθ hθ0 hθk
    hac hcd hw htransfer hg hold
  exact weighted_insertionPairScore_eq hθ0 hθk

end LocalInsertionConclusion

end Feige
