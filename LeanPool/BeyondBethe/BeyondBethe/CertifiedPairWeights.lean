/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.DirectedPairCost
import LeanPool.BeyondBethe.BeyondBethe.GreedyRowMatching
import Mathlib.Tactic

/-! # Certified Pair Weights -/

namespace BeyondBethe

/-!
# Executable constant-gain row-pair certificates

A row pair is retained when some two distinct columns pass the directed
four-core-cost test.  Every retained pair receives the same rational gain.
This avoids both numerical pair-capacity optimization and numerical
maximum-weight matching.
-/

/-- Finite, decidable eligibility test for a row pair. -/
def HasCertifiedCorePair {n : ℕ}
    (τ : ℚ) (X : Matrix (Fin n) (Fin n) ℚ)
    (κ : ℚ) (p : ℕ) (q : RowPair n) : Prop :=
  ∃ a b : Fin n, a ≠ b ∧
    directedFourCoreCostUpper τ X
      (rowPairRow q 0) (rowPairRow q 1) a b p ≤ κ

instance {n : ℕ} (τ : ℚ) (X : Matrix (Fin n) (Fin n) ℚ)
    (κ : ℚ) (p : ℕ) (q : RowPair n) :
    Decidable (HasCertifiedCorePair τ X κ p q) := by
  unfold HasCertifiedCorePair
  infer_instance

/-- The executable row-pair weight: either the fixed certified gain or zero. -/
def certifiedConstantRowWeight {n : ℕ}
    (τ : ℚ) (X : Matrix (Fin n) (Fin n) ℚ)
    (κ γ : ℚ) (p : ℕ) (q : RowPair n) : ℚ :=
  if HasCertifiedCorePair τ X κ p q then γ else 0

theorem certifiedConstantRowWeight_nonneg {n : ℕ}
    (τ : ℚ) (X : Matrix (Fin n) (Fin n) ℚ)
    (κ γ : ℚ) (p : ℕ) (q : RowPair n) (hγ : 0 ≤ γ) :
    0 ≤ certifiedConstantRowWeight τ X κ γ p q := by
  rw [certifiedConstantRowWeight]
  split_ifs
  · exact hγ
  · exact le_rfl

theorem certifiedConstantRowWeight_eq_gamma_iff {n : ℕ}
    (τ : ℚ) (X : Matrix (Fin n) (Fin n) ℚ)
    (κ γ : ℚ) (p : ℕ) (q : RowPair n) (hγ : γ ≠ 0) :
    certifiedConstantRowWeight τ X κ γ p q = γ ↔
      HasCertifiedCorePair τ X κ p q := by
  by_cases h : HasCertifiedCorePair τ X κ p q
  · simp [certifiedConstantRowWeight, h]
  · rw [certifiedConstantRowWeight, ite_eq_right h]
    exact iff_of_false (fun he ↦ hγ he.symm) h

theorem certifiedConstantRowWeight_eq_gamma_of_threshold {n : ℕ}
    (τ : ℚ) (X : Matrix (Fin n) (Fin n) ℚ)
    (κ γ : ℚ) (p : ℕ) (q : RowPair n) (hγ : 0 < γ)
    (hthreshold : γ ≤ certifiedConstantRowWeight τ X κ γ p q) :
    certifiedConstantRowWeight τ X κ γ p q = γ := by
  by_cases h : HasCertifiedCorePair τ X κ p q
  · simp [certifiedConstantRowWeight, h]
  · simp [certifiedConstantRowWeight, h] at hthreshold
    linarith

/-- Passing the rational test proves the fixed weight is a lower bound on the
true logarithmic pair gain for an exact KKT matrix. -/
theorem certifiedConstantRowWeight_le_log_pairGain
    {n : ℕ} {κ ξ₀ γ ell ξ : ℝ} {τ : ℚ}
    (hgain : CleanPairGainGuarantee κ ξ₀ γ)
    (hell : 1 ≤ ell) (hlogn : Real.log n ≤ ell * Real.log 2)
    (hξ : 0 < ξ) (hξ₀ : ξ ≤ ξ₀)
    (hτscale : (τ : ℝ) = ξ / (4 * ell))
    {A : Matrix (Fin n) (Fin n) ℝ}
    {X : Matrix (Fin n) (Fin n) ℚ}
    (hA : Matrix.Positive A)
    (hXds : IsDoublyStochastic (fun i j ↦ ((X i j : ℚ) : ℝ)))
    (hXint : ∀ i, IsInteriorProbabilityVector
      (fun j ↦ ((X i j : ℚ) : ℝ)))
    {R C : Fin n → ℝ}
    (hKKT : HasLogKKT (τ : ℝ) A
      (fun i j ↦ ((X i j : ℚ) : ℝ)) R C)
    {κq γq : ℚ} (hκ : (κq : ℝ) ≤ κ) (hγq : (γq : ℝ) ≤ γ)
    (p : ℕ) (q : RowPair n)
    (heligible : HasCertifiedCorePair τ X κq p q) :
    (γq : ℝ) ≤ Real.log (pairGain A
      (fun i j ↦ ((X i j : ℚ) : ℝ))
      (rowPairRow q 0) (rowPairRow q 1)) := by
  obtain ⟨a, b, hab, hcostQ⟩ := heligible
  have hτlower : (-1 : ℚ) ≤ τ := by
    have hτpos : (0 : ℝ) < (τ : ℝ) := by rw [hτscale]; positivity
    have hτposQ : (0 : ℚ) < τ := by exact_mod_cast hτpos
    linarith
  have hcostUpper := fourCoreTransferCost_le_directedFourCoreCostUpper
    hτlower hXint (rowPairRow q 0) (rowPairRow q 1) a b p
  have hcostCast :
      (directedFourCoreCostUpper τ X
        (rowPairRow q 0) (rowPairRow q 1) a b p : ℝ) ≤ (κq : ℝ) := by
    exact_mod_cast hcostQ
  have hcost : fourCoreTransferCost (τ : ℝ)
      (fun i j ↦ ((X i j : ℚ) : ℝ))
      (rowPairRow q 0) (rowPairRow q 1) a b ≤ κ :=
    hcostUpper.trans (hcostCast.trans hκ)
  let rscale : Fin n → ℝ := fun i ↦ Real.exp (R i)
  let cscale : Fin n → ℝ := fun j ↦ Real.exp (C j)
  have hmult : HasMultiplicativeKKT (τ : ℝ) A
      (fun i j ↦ ((X i j : ℚ) : ℝ)) rscale cscale :=
    hasMultiplicativeKKT_of_logKKT hA hXint hKKT
  exact hγq.trans (hgain hell hlogn hξ hξ₀ hτscale hA hXds hXint
    (fun i ↦ Real.exp_pos _) (fun j ↦ Real.exp_pos _) hmult
    (rowPairRow_ne q) hab hcost)

/-- A true clean pair whose cost has the stated numerical margin passes the
directed test and therefore receives the fixed gain. -/
theorem successfulCleanCycle_certifiedConstantRowWeight
    {n : ℕ} {κstruct η : ℝ} {τ κgain γ : ℚ}
    {P : Matrix (Fin n) (Fin n) ℝ}
    {X : Matrix (Fin n) (Fin n) ℚ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hXint : ∀ i, IsInteriorProbabilityVector
      (fun j ↦ ((X i j : ℚ) : ℝ)))
    (p : ℕ)
    (hmargin : 4 * (n + 3 : ℝ) * ((1 / 2 : ℚ) ^ p : ℚ) ≤
      (κgain : ℝ) - κstruct)
    (f g : Equiv.Perm (Fin n))
    (c : cleanCycleFactors η P (alternatingRowPerm f g))
    (hc : c ∈ successfulCleanCycles κstruct (τ : ℝ) η P
      (fun i j ↦ ((X i j : ℚ) : ℝ)) f g) :
    certifiedConstantRowWeight τ X κgain γ p (cleanCycleRowPair c) = γ := by
  have hcost : fourCoreTransferCost (τ : ℝ)
      (fun i j ↦ ((X i j : ℚ) : ℝ))
      (cleanCycleRow c 0) (cleanCycleRow c 1)
      (f (cleanCycleRow c 0)) (g (cleanCycleRow c 0)) ≤ κstruct := by
    have hnot : ¬ κstruct < fourCoreTransferCost (τ : ℝ)
        (fun i j ↦ ((X i j : ℚ) : ℝ))
        (cleanCycleRow c 0) (cleanCycleRow c 1)
        (f (cleanCycleRow c 0)) (g (cleanCycleRow c 0)) := by
      simpa [successfulCleanCycles, failedCleanCycles] using hc
    exact le_of_not_gt hnot
  have hu := directedFourCoreCostUpper_le_add_error hτ0 hτ1 hXint
    (cleanCycleRow c 0) (cleanCycleRow c 1)
    (f (cleanCycleRow c 0)) (g (cleanCycleRow c 0)) p
  have huκ : (directedFourCoreCostUpper τ X
      (cleanCycleRow c 0) (cleanCycleRow c 1)
      (f (cleanCycleRow c 0)) (g (cleanCycleRow c 0)) p : ℝ) ≤
      (κgain : ℝ) := by linarith
  have huκq : directedFourCoreCostUpper τ X
      (cleanCycleRow c 0) (cleanCycleRow c 1)
      (f (cleanCycleRow c 0)) (g (cleanCycleRow c 0)) p ≤ κgain := by
    exact_mod_cast huκ
  have hcols := cleanCycle_core_columns c
  rw [certifiedConstantRowWeight]
  split_ifs with h
  · rfl
  · exfalso
    apply h
    refine ⟨f (cleanCycleRow c 0), g (cleanCycleRow c 0), hcols.2.1, ?_⟩
    simpa only [rowPairRow_cleanCycleRowPair] using huκq

/-- The disjoint successful clean cycles force a large executable greedy
gain once the directed cost test has enough precision. -/
theorem greedyCertifiedMatchingGain_ge_successful_of_costMargin
    {n : ℕ} {κstruct η : ℝ} {τ κgain γ : ℚ}
    {P : Matrix (Fin n) (Fin n) ℝ}
    {X : Matrix (Fin n) (Fin n) ℚ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hXint : ∀ i, IsInteriorProbabilityVector
      (fun j ↦ ((X i j : ℚ) : ℝ)))
    (p : ℕ) (hγ : 0 ≤ γ)
    (hmargin : 4 * (n + 3 : ℝ) * ((1 / 2 : ℚ) ^ p : ℚ) ≤
      (κgain : ℝ) - κstruct)
    (f g : Equiv.Perm (Fin n)) :
    (((successfulCleanCycles κstruct (τ : ℝ) η P
        (fun i j ↦ ((X i j : ℚ) : ℝ)) f g).card : ℝ) * (γ : ℝ)) / 2 ≤
      (greedyCertifiedMatchingGain
        (certifiedConstantRowWeight τ X κgain γ p) γ : ℝ) := by
  exact greedyCertifiedMatchingGain_ge_successfulCleanCycles f g
    (certifiedConstantRowWeight τ X κgain γ p) hγ
    (fun c hc ↦ le_of_eq (successfulCleanCycle_certifiedConstantRowWeight
      hτ0 hτ1 hXint p hmargin f g c hc).symm)

/-- Full near-case conclusion for the executable threshold-greedy
certificate.  The structural threshold `κstruct` is allowed to be smaller
than the certified gain threshold `κgain`; their difference is exactly the
directed-evaluation margin. -/
theorem nearCase_greedyCertifiedMatchingGain_ge_threeSixteenths
    (hrowInequality : AnariRezaeiRowInequality)
    {n : ℕ} (hn : 2 ≤ n)
    {κstruct ell ξ η δ : ℝ} {τ κgain γ : ℚ}
    (hκstruct : 0 < κstruct)
    (hell : 1 ≤ ell) (hlogn : Real.log n ≤ ell * Real.log 2)
    (hξ : 0 < ξ) (hτscale : (τ : ℝ) = ξ / (4 * ell))
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hγ : 0 ≤ γ)
    (hη : 0 < η) (hηtenth : η ≤ 1 / 10)
    (hrowSmall : δ / (η / 3074) ^ 4 ≤ 1 / 128)
    (hcycleSmall : 6 / Real.log 2 *
      (δ + (1 + Real.log 2 / 2) * (δ / (η / 3074) ^ 4) +
        goodRowOmega η) ≤ 1 / 16)
    (htransferSmall :
      δ + 2 * ξ + binaryEntropy η + η +
          (1 + Real.log 2) * (δ / (η / 3074) ^ 4) ≤
        (1 / 16) * ((1 / 2 - η) * κstruct))
    {A : Matrix (Fin n) (Fin n) ℝ}
    {X : Matrix (Fin n) (Fin n) ℚ}
    (hA : Matrix.Positive A)
    (hX : IsDoublyStochastic (fun i j ↦ ((X i j : ℚ) : ℝ)))
    (hXint : ∀ i, IsInteriorProbabilityVector
      (fun j ↦ ((X i j : ℚ) : ℝ)))
    {R C : Fin n → ℝ}
    (hKKT : HasLogKKT (τ : ℝ) A
      (fun i j ↦ ((X i j : ℚ) : ℝ)) R C)
    (hnear : betheSlack n (betheLogValue A)
      (Real.log (Matrix.permanent A)) < δ * n)
    (p : ℕ)
    (hmargin : 4 * (n + 3 : ℝ) * ((1 / 2 : ℚ) ^ p : ℚ) ≤
      (κgain : ℝ) - κstruct) :
    3 * (γ : ℝ) / 16 * n ≤
      (greedyCertifiedMatchingGain
        (certifiedConstantRowWeight τ X κgain γ p) γ : ℝ) := by
  obtain ⟨f, g, hsuccess⟩ :=
    nearCase_successfulCleanCycles_count_ge_threeEighths hrowInequality hn
      hκstruct hell hlogn hξ hτscale hη hηtenth hrowSmall hcycleSmall
      htransferSmall hA hX hXint hKKT hnear
  have hgreedy := greedyCertifiedMatchingGain_ge_successful_of_costMargin
    (P := assignmentMarginal A) (η := η)
    hτ0 hτ1 hXint p hγ hmargin f g
  have hγR : (0 : ℝ) ≤ (γ : ℝ) := by exact_mod_cast hγ
  have hscaled := mul_le_mul_of_nonneg_right hsuccess hγR
  calc
    3 * (γ : ℝ) / 16 * n = ((3 * (n : ℝ) / 8) * (γ : ℝ)) / 2 := by ring
    _ ≤ (((successfulCleanCycles κstruct (τ : ℝ) η
        (assignmentMarginal A) (fun i j ↦ ((X i j : ℚ) : ℝ)) f g).card : ℝ) *
          (γ : ℝ)) / 2 := by linarith
    _ ≤ _ := hgreedy

/-- The matching test uses the same fixed precision as the final certificate
evaluation.  The generous additive constant keeps the executable matcher and
its analytic correctness theorem literally aligned. -/
def directedPairCostPrecision (n : ℕ) : ℕ := n + 400

theorem n_add_three_le_four_mul_two_pow (n : ℕ) :
    n + 3 ≤ 4 * 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      calc
        n + 1 + 3 ≤ 2 * (n + 3) := by omega
        _ ≤ 2 * (4 * 2 ^ n) := Nat.mul_le_mul_left 2 ih
        _ = 4 * 2 ^ (n + 1) := by rw [pow_succ]; ring

theorem directedPairCostPrecision_error_le (n : ℕ) :
    4 * (n + 3 : ℝ) *
        ((1 / 2 : ℚ) ^ directedPairCostPrecision n : ℚ) ≤
      (((1 / 10000 : ℚ) : ℚ) : ℝ) := by
  have hn : (n + 3 : ℝ) ≤ 4 * (2 : ℝ) ^ n := by
    exact_mod_cast n_add_three_le_four_mul_two_pow n
  rw [directedPairCostPrecision, show n + 400 = n + 400 by rfl, pow_add]
  norm_num only [Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_one,
    Rat.cast_ofNat]
  have hpowpos : 0 < (2 : ℝ) ^ n := by positivity
  calc
    4 * (n + 3 : ℝ) * ((1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ 400) ≤
        4 * (n + 3 : ℝ) *
          ((1 / 2 : ℝ) ^ n * (1 / 1048576 : ℝ)) := by
      gcongr
        norm_num
    _ ≤
        4 * (4 * (2 : ℝ) ^ n) *
          ((1 / 2 : ℝ) ^ n * (1 / 1048576 : ℝ)) := by gcongr
    _ = 1 / 65536 := by
      have hcancel : (2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n = 1 := by
        rw [← mul_pow]
        norm_num
      calc
        4 * (4 * (2 : ℝ) ^ n) *
              ((1 / 2 : ℝ) ^ n * (1 / 1048576 : ℝ)) =
            (16 / 1048576 : ℝ) *
              ((2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n) := by ring
        _ = 16 / 1048576 := by rw [hcancel, mul_one]
        _ = 1 / 65536 := by norm_num
    _ ≤ 1 / 10000 := by norm_num

end BeyondBethe
