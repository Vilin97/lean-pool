/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.Permanent
public import LeanPool.BeyondBethe.BeyondBethe.Slack
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Completion -/

@[expose] public section

namespace BeyondBethe

/-- The improvement in the positive-matrix dichotomy (paper (46)). -/
noncomputable def epsilonPlus (δ ξ γ : ℝ) : ℝ :=
  min (δ - ξ) (3 * γ / 8 - ξ)

theorem epsilonPlus_pos {δ ξ γ : ℝ}
    (hδ : ξ < δ) (hγ : ξ < 3 * γ / 8) :
    0 < epsilonPlus δ ξ γ := by
  rw [epsilonPlus, lt_min_iff]
  exact ⟨sub_pos.mpr hδ, sub_pos.mpr hγ⟩

/-- The two cases in Proposition 20 combine to the exponent in (45). -/
theorem positiveDichotomy_exponent
    {n : ℕ} {r δ ξ γ : ℝ}
    (h : r ≤ (Real.log 2 / 2 - δ + ξ) * n ∨
      r ≤ (Real.log 2 / 2 + ξ - 3 * γ / 8) * n) :
    r ≤ (Real.log 2 / 2 - epsilonPlus δ ξ γ) * n := by
  rcases h with hfar | hnear
  · refine hfar.trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg n))
    rw [epsilonPlus]
    have hmin : min (δ - ξ) (3 * γ / 8 - ξ) ≤ δ - ξ := min_le_left _ _
    linarith
  · refine hnear.trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg n))
    rw [epsilonPlus]
    have hmin : min (δ - ξ) (3 * γ / 8 - ξ) ≤ 3 * γ / 8 - ξ := min_le_right _ _
    linarith

/-- Paper (65): in the far case, Bethe slack pays for the logarithmic gap;
the paired gain can only help. -/
theorem farCase_logGap
    {n : ℕ} {logPermanent logBethe objective gain δ ξ : ℝ}
    (hslack : δ * n ≤ betheSlack n logBethe logPermanent)
    (hobjective : logBethe - ξ * n ≤ objective)
    (hgain : 0 ≤ gain) :
    logPermanent - (objective + gain) ≤
      (Real.log 2 / 2 - δ + ξ) * n := by
  rw [betheSlack] at hslack
  nlinarith

/-- Paper (69): in the near case, the matching gain subtracts directly from
the upper half of the Bethe sandwich. -/
theorem nearCase_logGap
    {n : ℕ} {logPermanent logBethe objective gain γ ξ : ℝ}
    (hupper : logPermanent ≤ logBethe + n * (Real.log 2 / 2))
    (hobjective : logBethe - ξ * n ≤ objective)
    (hgain : 3 * γ / 8 * n ≤ gain) :
    logPermanent - (objective + gain) ≤
      (Real.log 2 / 2 + ξ - 3 * γ / 8) * n := by
  nlinarith

/-- The proof's far/near split with the structural part of the near case
isolated in one explicit implication. -/
theorem completionCaseDisjunction
    {n : ℕ}
    {logPermanent logBethe objective gain δ ξ γ : ℝ}
    (hobjective : logBethe - ξ * n ≤ objective)
    (hgainNonneg : 0 ≤ gain)
    (hupper : logPermanent ≤ logBethe + n * (Real.log 2 / 2))
    (hnearGain : betheSlack n logBethe logPermanent < δ * n →
      3 * γ / 8 * n ≤ gain) :
    logPermanent - (objective + gain) ≤
        (Real.log 2 / 2 - δ + ξ) * n ∨
      logPermanent - (objective + gain) ≤
        (Real.log 2 / 2 + ξ - 3 * γ / 8) * n := by
  by_cases hfar : δ * n ≤ betheSlack n logBethe logPermanent
  · exact Or.inl (farCase_logGap hfar hobjective hgainNonneg)
  · exact Or.inr (nearCase_logGap hupper hobjective
      (hnearGain (lt_of_not_ge hfar)))

/-- Quantitative count used in the near case: the row and long-component
losses leave at least `59 n / 128` clean pairs. -/
theorem cleanPair_count_ge_fiftyNine
    {n bad long clean : ℝ}
    (hbad : bad ≤ n / 128) (hlong : long ≤ n / 16)
    (hclean : n - 2 * bad - long ≤ 2 * clean) :
    59 * n / 128 ≤ clean := by
  linarith

/-- After discarding at most `n/16` expensive pairs, the remaining disjoint
clean pairs number at least `3n/8`. -/
theorem successfulCleanPair_count_ge_threeEighths
    {n clean failed successful : ℝ}
    (hn : 0 ≤ n) (hclean : 59 * n / 128 ≤ clean)
    (hfailed : failed ≤ n / 16)
    (hsuccess : clean - failed ≤ successful) :
    3 * n / 8 ≤ successful := by
  linarith

/-- Multiplying the successful-pair count by the uniform gain gives paper
(68). -/
theorem matchingGain_ge_threeEighths
    {n successful γ matchingGain : ℝ}
    (hγ : 0 ≤ γ) (hsuccess : 3 * n / 8 ≤ successful)
    (hmatching : successful * γ ≤ matchingGain) :
    3 * γ / 8 * n ≤ matchingGain := by
  nlinarith

/-- Rearrangement of the robust cycle-information inequality used in (66).
The displayed definition of `cycleError` is kept as a hypothesis so this
lemma remains the exact scalar accounting step. -/
theorem longRow_count_le_cycleError
    {n D N bad δ rowError ω cycleError : ℝ}
    (hn : 0 ≤ n)
    (hlogD : D ≤ δ * n)
    (hbad : bad ≤ rowError * n)
    (hrobust : Real.log 2 / 6 * N -
        (1 + Real.log 2 / 2) * bad - n * ω ≤ D)
    (hcycle : cycleError = 6 / Real.log 2 *
      (δ + (1 + Real.log 2 / 2) * rowError + ω)) :
    N ≤ cycleError * n := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hscale : Real.log 2 / 6 * cycleError =
      δ + (1 + Real.log 2 / 2) * rowError + ω := by
    rw [hcycle]
    field_simp [hlog.ne']
  have hscaled : Real.log 2 / 6 * N ≤
      Real.log 2 / 6 * (cycleError * n) := by
    nlinarith [mul_le_mul_of_nonneg_left hbad
      (show 0 ≤ 1 + Real.log 2 / 2 by positivity)]
  exact le_of_mul_le_mul_left hscaled
    (div_pos hlog (by norm_num : (0 : ℝ) < 6))

/-- The Markov step for expensive clean pairs after (67), abstracted from
the graph indexing: cancel their common positive minimum cost. -/
theorem failedPair_count_le_transferError
    {failed transferError n minCost totalCost : ℝ}
    (hmin : 0 < minCost)
    (hfailed : failed * minCost ≤ totalCost)
    (htotal : totalCost ≤ transferError * n * minCost) :
    failed ≤ transferError * n := by
  exact le_of_mul_le_mul_right (hfailed.trans htotal) hmin

/-- Exponentiating the logarithmic bound uses exactly the base appearing in
paper Proposition 20. -/
theorem exp_logTwoHalf_sub (ε : ℝ) :
    Real.exp (Real.log 2 / 2 - ε) =
      Real.sqrt 2 * Real.exp (-ε) := by
  rw [sub_eq_add_neg, Real.exp_add]
  congr 1
  rw [← Real.exp_log (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))]
  congr 1
  rw [Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem logGap_implies_positive_approximation
    {n : ℕ} {L per ε : ℝ}
    (hL : 0 < L) (hper : 0 < per)
    (hlog : Real.log per - Real.log L ≤
      (Real.log 2 / 2 - ε) * n) :
    per ≤ (Real.sqrt 2 * Real.exp (-ε)) ^ n * L := by
  have hexp := Real.exp_le_exp.mpr hlog
  have hleft : Real.exp (Real.log per - Real.log L) = per / L := by
    rw [Real.exp_sub, Real.exp_log hper, Real.exp_log hL]
  have hright : Real.exp ((Real.log 2 / 2 - ε) * n) =
      (Real.sqrt 2 * Real.exp (-ε)) ^ n := by
    rw [Real.exp_mul, Real.rpow_natCast, exp_logTwoHalf_sub]
  rw [hleft, hright] at hexp
  exact (div_le_iff₀ hL).mp hexp

/-- Exact scalar assembly of paper Proposition 20.  The disjunction consists
of the far-slack and near-tight estimates proved in the two structural cases. -/
theorem positiveDichotomy_approximation
    {n : ℕ} {L per δ ξ γ : ℝ}
    (hL : 0 < L) (hper : 0 < per)
    (hcases :
      Real.log per - Real.log L ≤
          (Real.log 2 / 2 - δ + ξ) * n ∨
        Real.log per - Real.log L ≤
          (Real.log 2 / 2 + ξ - 3 * γ / 8) * n) :
    per ≤
      (Real.sqrt 2 * Real.exp (-epsilonPlus δ ξ γ)) ^ n * L := by
  apply logGap_implies_positive_approximation hL hper
  exact positiveDichotomy_exponent hcases

/-- Two-sided form of the positive-matrix conclusion, conditional on the
paired certificate lower bound and the two case estimates. -/
theorem positiveDichotomy_twoSided
    {n : ℕ} {L per δ ξ γ : ℝ}
    (hL : 0 < L) (hper : 0 < per) (hlower : L ≤ per)
    (hcases :
      Real.log per - Real.log L ≤
          (Real.log 2 / 2 - δ + ξ) * n ∨
        Real.log per - Real.log L ≤
          (Real.log 2 / 2 + ξ - 3 * γ / 8) * n) :
    L ≤ per ∧
      per ≤ (Real.sqrt 2 * Real.exp (-epsilonPlus δ ξ γ)) ^ n * L :=
  ⟨hlower, positiveDichotomy_approximation hL hper hcases⟩

/-- Positive-matrix proposition with its remaining structural obligation
shown explicitly as `hnearGain`.  This is the exact boundary between the
already checked analytic assembly and the good-row/cycle/transfer counting
argument. -/
theorem positiveMatrix_twoSided_of_nearGain
    {n : ℕ} {L per logBethe objective gain δ ξ γ : ℝ}
    (hL : 0 < L) (hper : 0 < per) (hlower : L ≤ per)
    (hlogL : Real.log L = objective + gain)
    (hobjective : logBethe - ξ * n ≤ objective)
    (hgainNonneg : 0 ≤ gain)
    (hupper : Real.log per ≤ logBethe + n * (Real.log 2 / 2))
    (hnearGain : betheSlack n logBethe (Real.log per) < δ * n →
      3 * γ / 8 * n ≤ gain) :
    L ≤ per ∧
      per ≤ (Real.sqrt 2 * Real.exp (-epsilonPlus δ ξ γ)) ^ n * L := by
  apply positiveDichotomy_twoSided hL hper hlower
  rw [hlogL]
  exact completionCaseDisjunction hobjective hgainNonneg hupper hnearGain

/-- The numerical and smoothing losses in the appendix consume at most half
of the positive-matrix logarithmic improvement. -/
theorem numerical_smoothing_loss
    {ε numericalLoss smoothingLoss : ℝ}
    (hnum : numericalLoss ≤ ε / 4)
    (hsmooth : smoothingLoss ≤ ε / 4) :
    -ε + numericalLoss + smoothingLoss ≤ -ε / 2 := by
  linarith

/-- The purely numerical conclusion of Theorem 1, separated from its
bit-complexity assertion. -/
def ApproximationGuarantee
    (alg : ∀ n, Matrix (Fin n) (Fin n) ℚ → ℚ) (c : ℝ) : Prop :=
  0 < c ∧ c < Real.sqrt 2 ∧
    ∀ n (A : Matrix (Fin n) (Fin n) ℚ),
      Matrix.Nonnegative A →
      ((alg n A : ℚ) : ℝ) ≤ ((Matrix.permanent A : ℚ) : ℝ) ∧
        ((Matrix.permanent A : ℚ) : ℝ) ≤ c ^ n * ((alg n A : ℚ) : ℝ)

/-- The last scalar step in the paper: any positive logarithmic improvement
produces a base strictly below `sqrt 2`. -/
theorem improvedBase_lt_sqrtTwo {ε : ℝ} (hε : 0 < ε) :
    Real.sqrt 2 * Real.exp (-ε) < Real.sqrt 2 := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hexp : Real.exp (-ε) < 1 := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (neg_neg_of_pos hε)
  nlinarith [mul_lt_mul_of_pos_left hexp hsqrt]

/-- The final base (paper (59)). -/
noncomputable def finalBase (ε : ℝ) : ℝ :=
  Real.sqrt 2 * Real.exp (-ε / 2)

theorem finalBase_lt_sqrtTwo {ε : ℝ} (hε : 0 < ε) :
    finalBase ε < Real.sqrt 2 := by
  rw [finalBase]
  have hhalf : 0 < ε / 2 := by linarith
  simpa only [neg_div] using improvedBase_lt_sqrtTwo hhalf

theorem finalBase_pos (ε : ℝ) : 0 < finalBase ε := by
  exact mul_pos (Real.sqrt_pos.2 (by norm_num)) (Real.exp_pos _)

/-- The base available before paying for smoothing and directed numerical
rounding.  The certified computation is allowed to spend one quarter of the
positive-matrix improvement. -/
noncomputable def preSmoothingBase (ε : ℝ) : ℝ :=
  Real.sqrt 2 * Real.exp (-ε + ε / 4)

theorem preSmoothingBase_pos (ε : ℝ) : 0 < preSmoothingBase ε := by
  exact mul_pos (Real.sqrt_pos.2 (by norm_num)) (Real.exp_pos _)

theorem preSmoothingBase_mul_exp_quarter (ε : ℝ) :
    preSmoothingBase ε * Real.exp (ε / 4) = finalBase ε := by
  rw [preSmoothingBase, finalBase]
  rw [mul_assoc, ← Real.exp_add]
  congr 1
  ring

/-- The scalar completion of the smoothing argument.  This theorem is the
exact non-algorithmic content of the last paragraph of the paper: a certified
positive-matrix lower bound that has spent at most one quarter of `ε` on
numerics can spend another quarter on smoothing and retain improvement
`ε / 2`. -/
theorem assemble_smoothing_and_numerics
    {n : ℕ} {per perSmooth lower χ ε : ℝ}
    (_hε : 0 < ε) (hχ : 0 ≤ χ) (hχsmall : χ ≤ ε / 2)
    (hlowerPos : 0 < lower)
    (hsmoothLower : per ≤ perSmooth)
    (hsmoothUpper : perSmooth ≤ (1 + χ * n / 2) * per)
    (hcertLower : lower ≤ perSmooth)
    (hcertUpper : perSmooth ≤ (preSmoothingBase ε) ^ n * lower) :
    lower / (1 + χ * n / 2) ≤ per ∧
      per ≤ (finalBase ε) ^ n * (lower / (1 + χ * n / 2)) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hfactorPos : 0 < 1 + χ * n / 2 := by positivity
  have hlower : lower / (1 + χ * n / 2) ≤ per := by
    rw [div_le_iff₀ hfactorPos]
    simpa [mul_comm] using hcertLower.trans hsmoothUpper
  have hfactorExp :
      1 + χ * n / 2 ≤ Real.exp (ε / 4) ^ n := by
    calc
      1 + χ * n / 2 ≤ Real.exp (χ * n / 2) := by
        simpa [add_comm] using Real.add_one_le_exp (χ * n / 2)
      _ ≤ Real.exp ((ε / 4) * n) := by
        apply Real.exp_le_exp.mpr
        have hmul := mul_le_mul_of_nonneg_right hχsmall
          (show 0 ≤ (n : ℝ) / 2 by positivity)
        nlinarith
      _ = Real.exp (ε / 4) ^ n := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hbase :
      (1 + χ * n / 2) * (preSmoothingBase ε) ^ n ≤
        (finalBase ε) ^ n := by
    calc
      (1 + χ * n / 2) * (preSmoothingBase ε) ^ n
          ≤ Real.exp (ε / 4) ^ n * (preSmoothingBase ε) ^ n :=
        mul_le_mul_of_nonneg_right hfactorExp
          (pow_nonneg (preSmoothingBase_pos ε).le n)
      _ = (finalBase ε) ^ n := by
        rw [← mul_pow, mul_comm, preSmoothingBase_mul_exp_quarter]
  have hper : per ≤ (preSmoothingBase ε) ^ n * lower :=
    hsmoothLower.trans hcertUpper
  have hupper :
      per ≤ (finalBase ε) ^ n * (lower / (1 + χ * n / 2)) := by
    rw [show (finalBase ε) ^ n * (lower / (1 + χ * n / 2)) =
        ((finalBase ε) ^ n * lower) / (1 + χ * n / 2) by ring]
    rw [le_div_iff₀ hfactorPos]
    calc
      per * (1 + χ * n / 2)
          ≤ ((preSmoothingBase ε) ^ n * lower) *
              (1 + χ * n / 2) :=
        mul_le_mul_of_nonneg_right hper hfactorPos.le
      _ = ((1 + χ * n / 2) * (preSmoothingBase ε) ^ n) * lower := by ring
      _ ≤ (finalBase ε) ^ n * lower :=
        mul_le_mul_of_nonneg_right hbase hlowerPos.le
  exact ⟨hlower, hupper⟩

end BeyondBethe
