/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.RobustCycle
import LeanPool.BeyondBethe.BeyondBethe.Optimizer
import LeanPool.BeyondBethe.BeyondBethe.ExcursionTransfer
import Mathlib.Tactic

/-! # Cycle Transfer -/

open scoped BigOperators

namespace BeyondBethe

/-- Columns outside the two core edges at a row. -/
noncomputable def coreOutside
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι) : Finset ι :=
  Finset.univ.filter fun j ↦ a ≠ j ∧ b ≠ j

theorem massOn_coreOutside_of_ne
    {n : ℕ} {p : Fin n → ℝ} (hp : IsProbabilityVector p)
    {a b : Fin n} (hab : a ≠ b) :
    massOn (coreOutside a b) p = 1 - p a - p b := by
  rw [massOn, coreOutside, Finset.sum_filter]
  exact sum_away_from_two hp hab

theorem massOn_coreOutside_same
    {n : ℕ} {p : Fin n → ℝ} (hp : IsProbabilityVector p) (a : Fin n) :
    massOn (coreOutside a a) p = 1 - p a := by
  rw [massOn, coreOutside, Finset.sum_filter]
  have haway := sum_ite_ne_eq_sum_sub p a
  rw [hp.sum_eq_one] at haway
  have hsame : (∑ j, if a ≠ j ∧ a ≠ j then p j else 0) =
      ∑ j, if j ≠ a then p j else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hja : j = a
    · subst j
      simp
    · simp [hja, Ne.symm hja]
  rw [hsame, haway]

theorem coreOutside_comm
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι) :
    coreOutside a b = coreOutside b a := by
  ext j
  simp only [coreOutside, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨haj, hbj⟩
    exact ⟨hbj, haj⟩
  · rintro ⟨hbj, haj⟩
    exact ⟨haj, hbj⟩

/-- If two distinct coordinates both belong to another two-element core,
then the two cores, and hence their complements, agree. -/
theorem coreOutside_eq_of_pair_membership
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b c d : ι} (hab : a ≠ b)
    (ha : a = c ∨ a = d) (hb : b = c ∨ b = d) :
    coreOutside c d = coreOutside a b := by
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact False.elim (hab (ha.trans hb.symm))
  · rw [ha, hb]
  · rw [ha, hb, coreOutside_comm]
  · exact False.elim (hab (ha.trans hb.symm))

theorem sum_negMulLog_coreOutside
    {n : ℕ} (p : Fin n → ℝ) (a b : Fin n) :
    (∑ j ∈ coreOutside a b, Real.negMulLog (p j)) =
      ∑ j, if a ≠ j ∧ b ≠ j then Real.negMulLog (p j) else 0 := by
  rw [coreOutside, Finset.sum_filter]

/-- The row coordinate of the cycle encoding is exactly the coarsening used
in the excursion-transfer argument. -/
theorem coreOutcome_entropy_eq_coarsenedRowEntropy
    {n : ℕ} {p : Fin n → ℝ} (hp : IsStrictProbabilityVector p)
    (a b : Fin n) :
    shannonEntropy (pushforwardMass p (coreOutcome a b)) =
      coarsenedRowEntropy (coreOutside a b) p := by
  by_cases hab : a = b
  · subst b
    rw [coreOutcome_entropy_same p a, coarsenedRowEntropy,
      scaledConditionalEntropyOn, binaryEntropy,
      massOn_coreOutside_same hp.probability,
      sum_negMulLog_coreOutside]
    have hout := sum_ite_ne_eq_sum_sub
      (fun j ↦ Real.negMulLog (p j)) a
    have hsame :
        (∑ j, if a ≠ j ∧ a ≠ j then Real.negMulLog (p j) else 0) =
          ∑ j, if j ≠ a then Real.negMulLog (p j) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hja : j = a
      · subst j
        simp
      · simp [hja, Ne.symm hja]
    rw [hsame, hout, shannonEntropy, Real.negMulLog_def]
    ring
  · rw [coreOutcome_entropy_eq_twoCoreCoarsenedEntropy p hab,
      twoCoreCoarsenedEntropy, coarsenedRowEntropy,
      scaledConditionalEntropyOn, binaryEntropy,
      massOn_coreOutside_of_ne hp.probability hab,
      sum_negMulLog_coreOutside]
    have hmass : 1 - (1 - p a - p b) = p a + p b := by ring
    rw [hmass, Real.negMulLog_def]
    ring

/-- Rowwise form of the preceding bridge for the actual completed graph. -/
theorem coordinateEncoding_entropy_eq_coarsenedRowEntropy
    {n : ℕ} {μ : Equiv.Perm (Fin n) → ℝ}
    {P : Matrix (Fin n) (Fin n) ℝ}
    (hmarg : HasAssignmentMarginals μ P)
    (hP : ∀ i, IsStrictProbabilityVector (P i))
    (f g : Equiv.Perm (Fin n)) (i : Fin n) :
    shannonEntropy (pushforwardMass (rowOrientedMass μ)
        (fun σ ↦ twoMatchingEncoding f g σ i)) =
      coarsenedRowEntropy (coreOutside (f i) (g i)) (P i) := by
  rw [coordinateEncoding_mass hmarg f g i]
  exact coreOutcome_entropy_eq_coarsenedRowEntropy (hP i) (f i) (g i)

theorem two_mul_cycleFactors_card_le
    {n : ℕ} (h : Equiv.Perm (Fin n)) :
    2 * h.cycleFactorsFinset.card ≤ n := by
  have htwo : 2 * h.cycleFactorsFinset.card ≤
      ∑ c : h.cycleFactorsFinset,
        (c : Equiv.Perm (Fin n)).support.card := by
    calc
      2 * h.cycleFactorsFinset.card =
          ∑ _c : h.cycleFactorsFinset, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ c : h.cycleFactorsFinset,
          (c : Equiv.Perm (Fin n)).support.card := by
        apply Finset.sum_le_sum
        intro c _
        exact (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.property).1.two_le_card_support
  have hsupport :
      (∑ c : h.cycleFactorsFinset,
        (c : Equiv.Perm (Fin n)).support.card) ≤ n := by
    have hle := sum_cycleSupport_inter_card_le h Finset.univ
    simpa using hle
  omega

/-- Paper Lemma 9 in the exact coarsened-row form needed for equation (39). -/
theorem twoMatching_entropy_le_halfBits_add_coarsenedRows
    {n : ℕ} {μ : Equiv.Perm (Fin n) → ℝ}
    {P : Matrix (Fin n) (Fin n) ℝ}
    (hμ : IsProbabilityVector μ)
    (hmarg : HasAssignmentMarginals μ P)
    (hP : ∀ i, IsStrictProbabilityVector (P i))
    (f g : Equiv.Perm (Fin n)) :
    shannonEntropy μ ≤ n * (Real.log 2 / 2) +
      ∑ i, coarsenedRowEntropy (coreOutside (f i) (g i)) (P i) := by
  have hcore := twoMatching_coreEncoding_sum_coordinates hμ f g
  simp_rw [coordinateEncoding_entropy_eq_coarsenedRowEntropy
    hmarg hP f g] at hcore
  have hcountNat := two_mul_cycleFactors_card_le (alternatingRowPerm f g)
  have hcount :
      ((alternatingRowPerm f g).cycleFactorsFinset.card : ℝ) *
          Real.log 2 ≤ n * (Real.log 2 / 2) := by
    have hcountR :
        2 * ((alternatingRowPerm f g).cycleFactorsFinset.card : ℝ) ≤ n := by
      exact_mod_cast hcountNat
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_right hcountR hlog]
  linarith

/-- End-to-end form of the excursion-transfer estimate for a completed
two-matching graph.  This theorem closes the informal identification of a
good row's two heavy coordinates with its two graph edges: consequently the
mass outside the encoded core is at most `η`. -/
theorem twoMatching_coreTransferCost_normalized_le
    {n : ℕ} (hn : 0 < n)
    {μ : Equiv.Perm (Fin n) → ℝ}
    {P X : Matrix (Fin n) (Fin n) ℝ}
    (hμ : IsProbabilityVector μ)
    (hmarg : HasAssignmentMarginals μ P)
    (hP : ∀ i, IsStrictProbabilityVector (P i))
    {τ B η : ℝ} (hτ : 0 ≤ τ)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    (hη : η ∈ Set.Icc (0 : ℝ) (2 : ℝ)⁻¹)
    (f g : Equiv.Perm (Fin n))
    (hheavy : ∀ i j, j ∈ heavyCoordinates η (P i) →
      j = f i ∨ j = g i)
    (hglobal : matrixTransferCost P
        (fun i j ↦ transferU τ (X i) j) ≤
      B + shannonEntropy μ - n * (Real.log 2 / 2)) :
    coreTransferCost (fun i ↦ coreOutside (f i) (g i)) P
          (fun i j ↦ transferU τ (X i) j) / n ≤
      B / n + binaryEntropy η + η +
        (1 + Real.log 2) * ((badRows η P).card : ℝ) / n := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hencoding := twoMatching_entropy_le_halfBits_add_coarsenedRows
    hμ hmarg hP f g
  have hbefore : matrixTransferCost P
        (fun i j ↦ transferU τ (X i) j) ≤
      B + ∑ i, coarsenedRowEntropy (coreOutside (f i) (g i)) (P i) := by
    linarith
  have hρ : ∀ i,
      massOn (coreOutside (f i) (g i)) (P i) ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    constructor
    · rw [massOn]
      exact Finset.sum_nonneg fun j _ ↦ (hP i).probability.nonnegative j
    · exact (massOn_le_sum_univ _
        (fun j ↦ (hP i).probability.nonnegative j)).trans_eq
          (hP i).probability.sum_eq_one
  have hgood : ∀ i ∈ goodRows η P,
      massOn (coreOutside (f i) (g i)) (P i) ≤ η := by
    intro i hi
    have hi' : IsGoodRow η (P i) := by
      simpa [goodRows] using hi
    obtain ⟨a, b, hab, hdist⟩ := hi'
    have hcore := goodRow_witness_mem_heavyCoordinates
      (hP i).probability hab hdist
    have ha := hheavy i a hcore.1
    have hb := hheavy i b hcore.2
    have houtside : coreOutside (f i) (g i) = coreOutside a b :=
      coreOutside_eq_of_pair_membership hab ha hb
    rw [houtside, massOn_coreOutside_of_ne (hP i).probability hab]
    rw [halfHalfL1Distance_eq (hP i).probability hab] at hdist
    linarith [abs_nonneg (P i a - 1 / 2), abs_nonneg (P i b - 1 / 2)]
  have hnormalized := coreTransferCost_normalized_le_for_transferU
    (fun i ↦ coreOutside (f i) (g i)) (goodRows η P)
    hτ (fun i j ↦ (hP i).positive j) hXint hbefore hη hρ hgood
  have hbad : (Finset.univ \ goodRows η P) = badRows η P := by
    ext i
    simp [goodRows, badRows]
  rw [hbad] at hnormalized
  simpa [Fintype.card_fin] using hnormalized

/-- The preceding transfer estimate with every probabilistic, slack, and
optimization quantity instantiated for the Gibbs distribution of a positive
matrix.  Apart from the logarithmic KKT equations, all inputs to paper
Lemmas 16 and 17 are discharged here. -/
theorem gibbs_twoMatching_coreTransferCost_normalized_le
    {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : Matrix.Positive A)
    {τ ξ η : ℝ} (hτ : 0 ≤ τ)
    (hbudget : τ * (n * Real.log n) ≤ ξ * n)
    (hη : η ∈ Set.Icc (0 : ℝ) (2 : ℝ)⁻¹)
    (f g : Equiv.Perm (Fin n))
    (hheavy : ∀ i j, j ∈ heavyCoordinates η (assignmentMarginal A i) →
      j = f i ∨ j = g i)
    {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : IsDoublyStochastic X)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    {r c : Fin n → ℝ} (hKKT : HasLogKKT τ A X r c) :
    coreTransferCost (fun i ↦ coreOutside (f i) (g i))
          (assignmentMarginal A) (fun i j ↦ transferU τ (X i) j) / n ≤
      betheSlack n (betheLogValue A) (Real.log (Matrix.permanent A)) / n +
        2 * ξ + binaryEntropy η + η +
        (1 + Real.log 2) *
          ((badRows η (assignmentMarginal A)).card : ℝ) / n := by
  let P := assignmentMarginal A
  let μ := gibbsProbability A
  let D := gibbsSequentialDivergence A
  let E := betheSuboptimality (betheLogValue A) (betheObjective A P)
  let S := betheSlack n (betheLogValue A)
    (Real.log (Matrix.permanent A))
  have hper : 0 < Matrix.permanent A := permanent_pos_of_positive A hA
  have hPds : IsDoublyStochastic P :=
    assignmentMarginal_doublyStochastic A
      (fun i j ↦ (hA i j).le) hper.ne'
  have hPstrict : ∀ i, IsStrictProbabilityVector (P i) :=
    assignmentMarginal_strictProbabilityVector A hA
  have hEτ : regularizedBetheObjective τ A X -
        regularizedBetheObjective τ A P ≤ E + ξ * n := by
    exact regularizedDifference_le_betheSuboptimality_add_budget
      hn hτ hbudget hA hX hPds
  have hregularizer : τ * totalRowEntropy P ≤ ξ * n := by
    have hentropy : totalRowEntropy P ≤ n * Real.log n := by
      letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
      simpa using totalRowEntropy_le hPds
    exact (mul_le_mul_of_nonneg_left hentropy hτ).trans hbudget
  have hdivergence : D = -shannonEntropy μ + ∑ i, rowScore (P i) := by
    exact gibbsSequentialDivergence_eq_entropy A hA
  have hseq : Real.log (Matrix.permanent A) =
      betheObjective A P + (∑ i, rowCorrection (P i)) - D := by
    exact gibbs_exact_sequential_identity A hA
  have hslack : S = E + (∑ i, rowDeficit (P i)) + D := by
    exact slack_decomposition_rowDeficit P hseq
  have hglobal : matrixTransferCost P
        (fun i j ↦ transferU τ (X i) j) ≤
      S + 2 * ξ * n + shannonEntropy μ -
        n * (Real.log 2 / 2) := by
    exact global_transfer_upper_of_logKKT_and_slack
      hX hPds hXint hKKT hEτ hregularizer hdivergence hslack
  have hcore := twoMatching_coreTransferCost_normalized_le
    hn (gibbsProbability_isProbabilityVector A hA)
    (gibbs_hasAssignmentMarginals A) hPstrict hτ hXint hη f g hheavy
    (B := S + 2 * ξ * n) hglobal
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  dsimp only [P, μ, S] at hcore ⊢
  convert hcore using 1 <;> field_simp [hnR] <;> ring

end BeyondBethe
