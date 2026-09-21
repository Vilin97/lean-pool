/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.NearCase
import Mathlib.Algebra.Order.Archimedean.Basic

/-! # Numerical Scales -/

namespace BeyondBethe

/-!
# Rational structural scales for the numerical algorithm

The qualitative completion theorem chooses its hierarchy of constants in
`ℝ`.  That is sufficient for the mathematical approximation theorem, but an
algorithm cannot use an unspecified real regularization parameter.  This file
repeats the choice with rational points at every open step.  The resulting
constants can be hard-coded in a Turing machine and the regularization scale
`ξ / (4n)` is rational on every input dimension.
-/

/-- Rational data satisfying exactly the scale inequalities consumed by the
positive-matrix dichotomy.  Analytic expressions are compared after casting
the rational constants to `ℝ`. -/
structure RationalCompletionScales (κ₀ ξ₀ γ₀ : ℚ) where
  η : ℚ
  δ : ℚ
  ξ : ℚ
  η_pos : 0 < η
  η_le_tenth : (η : ℝ) ≤ 1 / 10
  δ_pos : 0 < δ
  ξ_pos : 0 < ξ
  ξ_le_source : ξ ≤ ξ₀
  row_small :
    (δ : ℝ) / ((η : ℝ) / 3074) ^ 4 ≤ 1 / 128
  cycle_small :
    6 / Real.log 2 *
      ((δ : ℝ) + (1 + Real.log 2 / 2) *
          ((δ : ℝ) / ((η : ℝ) / 3074) ^ 4) +
        goodRowOmega (η : ℝ)) ≤ 1 / 16
  transfer_small :
    (δ : ℝ) + 2 * (ξ : ℝ) + binaryEntropy (η : ℝ) + (η : ℝ) +
        (1 + Real.log 2) *
          ((δ : ℝ) / ((η : ℝ) / 3074) ^ 4) ≤
      (1 / 16) * ((1 / 2 - (η : ℝ)) * (κ₀ : ℝ))
  ξ_lt_δ : ξ < δ
  ξ_lt_gain : ξ < 3 * γ₀ / 8

/-- The completion hierarchy may be chosen rationally.  The proof uses
rational density only inside strict margins, so no numerical approximation is
smuggled into the theorem. -/
theorem exists_rational_completion_scales
    {κ₀ ξ₀ γ₀ : ℚ} (hκ₀ : 0 < κ₀) (hξ₀ : 0 < ξ₀) (hγ₀ : 0 < γ₀) :
    Nonempty (RationalCompletionScales κ₀ ξ₀ γ₀) := by
  have hκ₀r : 0 < (κ₀ : ℝ) := by exact_mod_cast hκ₀
  have hξ₀r : 0 < (ξ₀ : ℝ) := by exact_mod_cast hξ₀
  have hγ₀r : 0 < (γ₀ : ℝ) := by exact_mod_cast hγ₀
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hωtarget : 0 < Real.log 2 / 384 := div_pos hlog (by norm_num)
  have hωevent : {x : ℝ | goodRowOmega x < Real.log 2 / 384} ∈ nhds 0 :=
    tendsto_goodRowOmega_zero (isOpen_Iio.mem_nhds hωtarget)
  have hHcont : ContinuousAt (fun x : ℝ ↦ binaryEntropy x + x) 0 :=
    continuous_binaryEntropy.continuousAt.add continuousAt_id
  have hHtarget : 0 < (κ₀ : ℝ) / 256 := div_pos hκ₀r (by norm_num)
  have hHevent :
      {x : ℝ | binaryEntropy x + x < (κ₀ : ℝ) / 256} ∈ nhds 0 := by
    exact hHcont.eventually (isOpen_Iio.mem_nhds (by
      simpa [binaryEntropy] using hHtarget))
  have hevent := Filter.inter_mem hωevent hHevent
  rw [Metric.mem_nhds_iff] at hevent
  obtain ⟨a, ha, hball⟩ := hevent
  have hηbound : 0 < min a (1 / 20 : ℝ) := lt_min ha (by norm_num)
  obtain ⟨ηq, hηq0r, hηqbound⟩ := exists_pos_rat_lt hηbound
  have hηq0 : 0 < ηq := hηq0r
  let η : ℝ := (ηq : ℝ)
  have hη : 0 < η := by
    simpa only [η, Rat.cast_pos] using hηq0r
  have hηtwenty : η < 1 / 20 :=
    hηqbound.trans_le (min_le_right _ _)
  have hηa : η < a := hηqbound.trans_le (min_le_left _ _)
  have hηmem := hball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hη]
    exact hηa)
  have hωsmall : goodRowOmega η < Real.log 2 / 384 := hηmem.1
  have hHsmall : binaryEntropy η + η < (κ₀ : ℝ) / 256 := hηmem.2
  have hηtenth : η ≤ 1 / 10 := hηtwenty.le.trans (by norm_num)
  have hcycleBase : 6 / Real.log 2 * goodRowOmega η < 1 / 64 := by
    have hcoef : 0 < 6 / Real.log 2 := div_pos (by norm_num) hlog
    calc
      6 / Real.log 2 * goodRowOmega η <
          6 / Real.log 2 * (Real.log 2 / 384) :=
        mul_lt_mul_of_pos_left hωsmall hcoef
      _ = 1 / 64 := by field_simp [hlog.ne'] <;> norm_num
  have hηκ : η * (κ₀ : ℝ) ≤ (1 / 20) * (κ₀ : ℝ) :=
    mul_le_mul_of_nonneg_right hηtwenty.le hκ₀r.le
  have htransferBase : binaryEntropy η + η <
      (1 / 16) * ((1 / 2 - η) * (κ₀ : ℝ)) := by
    nlinarith
  let cycleMargin : ℝ := 1 / 16 - 6 / Real.log 2 * goodRowOmega η
  let transferMargin : ℝ :=
    (1 / 16) * ((1 / 2 - η) * (κ₀ : ℝ)) - (binaryEntropy η + η)
  have hcycleMargin : 0 < cycleMargin := by
    dsimp only [cycleMargin]
    linarith
  have htransferMargin : 0 < transferMargin := by
    dsimp only [transferMargin]
    linarith
  let d₀q : ℚ := (ηq / 3074) ^ 4
  let d₀ : ℝ := (d₀q : ℚ)
  have hd₀_cast : d₀ = (η / 3074) ^ 4 := by
    simp [d₀, d₀q, η]
  have hd₀ : 0 < d₀ := by
    rw [hd₀_cast]
    positivity
  let cycleCoefficient : ℝ :=
    6 / Real.log 2 * (d₀ + (1 + Real.log 2 / 2))
  have hcycleCoefficient : 0 < cycleCoefficient := by
    dsimp only [cycleCoefficient]
    have hc : 0 < d₀ + (1 + Real.log 2 / 2) := by positivity
    exact mul_pos (div_pos (by norm_num) hlog) hc
  let transferCoefficient : ℝ := d₀ + (1 + Real.log 2)
  have htransferCoefficient : 0 < transferCoefficient := by
    dsimp only [transferCoefficient]
    positivity
  let rBound : ℝ := min (1 / 128)
    (min (cycleMargin / (2 * cycleCoefficient))
      (transferMargin / (2 * transferCoefficient)))
  have hrBound : 0 < rBound := by
    dsimp only [rBound]
    exact lt_min (by norm_num) (lt_min
      (div_pos hcycleMargin (mul_pos (by norm_num) hcycleCoefficient))
      (div_pos htransferMargin (mul_pos (by norm_num) htransferCoefficient)))
  obtain ⟨rq, hrq0r, hrqBound⟩ := exists_pos_rat_lt hrBound
  have hrq0 : 0 < rq := hrq0r
  let r : ℝ := (rq : ℝ)
  have hr : 0 < r := by
    simpa only [r, Rat.cast_pos] using hrq0r
  have hr128 : r ≤ 1 / 128 :=
    hrqBound.le.trans (min_le_left _ _)
  have hrcycle : r ≤ cycleMargin / (2 * cycleCoefficient) :=
    hrqBound.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrtransfer : r ≤ transferMargin / (2 * transferCoefficient) :=
    hrqBound.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hcycleExtra : cycleCoefficient * r ≤ cycleMargin / 2 := by
    calc
      cycleCoefficient * r ≤
          cycleCoefficient * (cycleMargin / (2 * cycleCoefficient)) :=
        mul_le_mul_of_nonneg_left hrcycle hcycleCoefficient.le
      _ = cycleMargin / 2 := by field_simp [hcycleCoefficient.ne']
  have htransferExtra : transferCoefficient * r ≤ transferMargin / 2 := by
    calc
      transferCoefficient * r ≤
          transferCoefficient * (transferMargin / (2 * transferCoefficient)) :=
        mul_le_mul_of_nonneg_left hrtransfer htransferCoefficient.le
      _ = transferMargin / 2 := by field_simp [htransferCoefficient.ne']
  let δq : ℚ := d₀q * rq
  let δ : ℝ := (δq : ℚ)
  have hδ_cast : δ = d₀ * r := by simp [δ, δq, d₀, r]
  have hδ : 0 < δ := by rw [hδ_cast]; exact mul_pos hd₀ hr
  have hδq : 0 < δq := by
    dsimp only [δq, d₀q]
    positivity
  have hratio : δ / (η / 3074) ^ 4 = r := by
    rw [← hd₀_cast, hδ_cast]
    exact mul_div_cancel_left₀ r hd₀.ne'
  have hcycle : 6 / Real.log 2 *
      (δ + (1 + Real.log 2 / 2) * (δ / (η / 3074) ^ 4) +
        goodRowOmega η) < 1 / 16 := by
    rw [hratio]
    have hid : 6 / Real.log 2 *
        (δ + (1 + Real.log 2 / 2) * r + goodRowOmega η) =
        6 / Real.log 2 * goodRowOmega η + cycleCoefficient * r := by
      rw [hδ_cast]
      dsimp only [cycleCoefficient]
      ring
    rw [hid]
    dsimp only [cycleMargin] at hcycleExtra
    linarith
  have htransferZero :
      δ + binaryEntropy η + η +
          (1 + Real.log 2) * (δ / (η / 3074) ^ 4) <
        (1 / 16) * ((1 / 2 - η) * (κ₀ : ℝ)) := by
    rw [hratio]
    have hid : δ + binaryEntropy η + η + (1 + Real.log 2) * r =
        (binaryEntropy η + η) + transferCoefficient * r := by
      rw [hδ_cast]
      dsimp only [transferCoefficient]
      ring
    rw [hid]
    dsimp only [transferMargin] at htransferExtra
    linarith
  let remaining : ℝ := (1 / 16) * ((1 / 2 - η) * (κ₀ : ℝ)) -
    (δ + binaryEntropy η + η +
      (1 + Real.log 2) * (δ / (η / 3074) ^ 4))
  have hremaining : 0 < remaining := by
    dsimp only [remaining]
    linarith
  let ξBound : ℝ := min (ξ₀ : ℝ)
    (min δ (min (3 * (γ₀ : ℝ) / 8) (remaining / 4)))
  have hξBound : 0 < ξBound := by
    dsimp only [ξBound]
    exact lt_min hξ₀r (lt_min hδ (lt_min
      (div_pos (mul_pos (by norm_num) hγ₀r) (by norm_num))
      (div_pos hremaining (by norm_num))))
  obtain ⟨ξq, hξq0r, hξqBound⟩ := exists_pos_rat_lt hξBound
  have hξq0 : 0 < ξq := by exact_mod_cast hξq0r
  let ξ : ℝ := (ξq : ℝ)
  have hξξ₀r : ξ < (ξ₀ : ℝ) :=
    hξqBound.trans_le (min_le_left _ _)
  have hξξ₀ : ξq ≤ ξ₀ := by
    have hcast : (ξq : ℝ) ≤ (ξ₀ : ℝ) := by
      simpa only [ξ] using hξξ₀r.le
    exact_mod_cast hcast
  have hξδr : ξ < δ :=
    hξqBound.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hξδ : ξq < δq := by
    change (ξq : ℝ) < (δq : ℝ) at hξδr
    exact_mod_cast hξδr
  have hξγ : ξ < 3 * (γ₀ : ℝ) / 8 :=
    hξqBound.trans_le ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hξremaining : ξ ≤ remaining / 4 :=
    hξqBound.le.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  have htransfer :
      δ + 2 * ξ + binaryEntropy η + η +
          (1 + Real.log 2) * (δ / (η / 3074) ^ 4) ≤
        (1 / 16) * ((1 / 2 - η) * (κ₀ : ℝ)) := by
    dsimp only [remaining] at hξremaining
    nlinarith
  exact ⟨{
    η := ηq
    δ := δq
    ξ := ξq
    η_pos := hηq0
    η_le_tenth := by simpa only [η] using hηtenth
    δ_pos := hδq
    ξ_pos := hξq0
    ξ_le_source := hξξ₀
    row_small := by
      change δ / (η / 3074) ^ 4 ≤ 1 / 128
      rw [hratio]
      exact hr128
    cycle_small := by simpa only [δ, η] using hcycle.le
    transfer_small := by simpa only [δ, ξ, η] using htransfer
    ξ_lt_δ := hξδ
    ξ_lt_gain := by
      have hcast : (ξq : ℝ) < ((3 * γ₀ / 8 : ℚ) : ℝ) := by
        norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat]
        simpa only [ξ] using hξγ
      exact_mod_cast hcast }⟩

/-- A rational version of the improvement left after the far/near dichotomy. -/
def rationalEpsilonPlus
    {κ₀ ξ₀ γ₀ : ℚ} (s : RationalCompletionScales κ₀ ξ₀ γ₀) : ℚ :=
  min (s.δ - s.ξ) (3 * γ₀ / 8 - s.ξ)

theorem rationalEpsilonPlus_pos
    {κ₀ ξ₀ γ₀ : ℚ} (s : RationalCompletionScales κ₀ ξ₀ γ₀) :
    0 < rationalEpsilonPlus s := by
  rw [rationalEpsilonPlus, lt_min_iff]
  exact ⟨sub_pos.mpr s.ξ_lt_δ, sub_pos.mpr s.ξ_lt_gain⟩

theorem cast_rationalEpsilonPlus
    {κ₀ ξ₀ γ₀ : ℚ} (s : RationalCompletionScales κ₀ ξ₀ γ₀) :
    ((rationalEpsilonPlus s : ℚ) : ℝ) =
      epsilonPlus (s.δ : ℝ) (s.ξ : ℝ) (γ₀ : ℝ) := by
  simp [rationalEpsilonPlus, epsilonPlus, Rat.cast_min]

/-- The elementary dimension bound that permits the algorithm to use the
rational scale `ell = n`, instead of the nonrational expression
`max 1 (log n / log 2)`. -/
theorem log_natCast_le_natCast_mul_log_two
    {n : ℕ} (hn : 1 ≤ n) :
    Real.log n ≤ (n : ℝ) * Real.log 2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hpowpos : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  have hnat : n ≤ 2 ^ n := n.lt_two_pow_self.le
  have hcast : (n : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hnat
  have hlog := Real.strictMonoOn_log.monotoneOn hnpos hpowpos hcast
  rw [Real.log_pow] at hlog
  simpa only [Nat.cast_ofNat] using hlog

/-- All absolute constants needed by the structural argument, now retained
as rational data instead of being erased into an existential real constant. -/
structure RationalStructuralScales where
  κ₀ : ℚ
  ξ₀ : ℚ
  γ₀ : ℚ
  κ₀_pos : 0 < κ₀
  ξ₀_pos : 0 < ξ₀
  γ₀_pos : 0 < γ₀
  cleanGain : CleanPairGainGuarantee (κ₀ : ℝ) (ξ₀ : ℝ) (γ₀ : ℝ)
  completion : RationalCompletionScales κ₀ ξ₀ γ₀

theorem exists_rational_structuralScales :
    Nonempty RationalStructuralScales := by
  obtain ⟨κ₀, ξ₀, γ₀, hκ₀, hξ₀, hγ₀, hgain⟩ :=
    exists_rational_cleanPairGain_constants
  obtain ⟨s⟩ := exists_rational_completion_scales hκ₀ hξ₀ hγ₀
  exact ⟨{
    κ₀ := κ₀
    ξ₀ := ξ₀
    γ₀ := γ₀
    κ₀_pos := hκ₀
    ξ₀_pos := hξ₀
    γ₀_pos := hγ₀
    cleanGain := hgain
    completion := s }⟩

/-- The rational regularization parameter used in dimension `n`. -/
def rationalRegularizationScale (s : RationalStructuralScales) (n : ℕ) : ℚ :=
  s.completion.ξ / (4 * n)

theorem cast_rationalRegularizationScale
    (s : RationalStructuralScales) (n : ℕ) :
    ((rationalRegularizationScale s n : ℚ) : ℝ) =
      (s.completion.ξ : ℝ) / (4 * (n : ℝ)) := by
  simp [rationalRegularizationScale]

theorem rationalRegularizationScale_pos
    (s : RationalStructuralScales) {n : ℕ} (hn : 0 < n) :
    0 < rationalRegularizationScale s n := by
  rw [rationalRegularizationScale]
  exact div_pos s.completion.ξ_pos (by positivity)

/-- The structural certificate applies to any exact optimizer at the rational
scale.  This is the form needed after the numerical routine replaces its
approximate optimizer by a nearby matrix for which the KKT equations are
exact. -/
theorem rationalScales_certificate_of_optimizer
    (stableCoefficient : AnariOveisGharanStableCoefficient.{0})
    (s : RationalStructuralScales)
    {n : ℕ} (hn : 2 ≤ n)
    {A X : Matrix (Fin n) (Fin n) ℝ}
    (hA : Matrix.Positive A)
    (hX : IsDoublyStochastic X)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    (hmax : ∀ Y, IsDoublyStochastic Y →
      regularizedBetheObjective
          ((rationalRegularizationScale s n : ℚ) : ℝ) A Y ≤
        regularizedBetheObjective
          ((rationalRegularizationScale s n : ℚ) : ℝ) A X)
    (hKKT : ∃ r c : Fin n → ℝ,
      HasLogKKT ((rationalRegularizationScale s n : ℚ) : ℝ) A X r c) :
    Real.exp (betheObjective A X + maximumMatchingGain A X) ≤
        Matrix.permanent A ∧
      Real.log (Matrix.permanent A) -
          (betheObjective A X + maximumMatchingGain A X) ≤
        (Real.log 2 / 2 -
          ((rationalEpsilonPlus s.completion : ℚ) : ℝ)) * n := by
  let η : ℝ := (s.completion.η : ℝ)
  let δ : ℝ := (s.completion.δ : ℝ)
  let ξ : ℝ := (s.completion.ξ : ℝ)
  let τ : ℝ := ((rationalRegularizationScale s n : ℚ) : ℝ)
  obtain ⟨rscale, cscale, hKKT⟩ := hKKT
  have hκ : 0 < (s.κ₀ : ℝ) := by exact_mod_cast s.κ₀_pos
  have hγ : 0 < (s.γ₀ : ℝ) := by exact_mod_cast s.γ₀_pos
  have hξ : 0 < ξ := by
    simpa only [ξ, Rat.cast_pos] using s.completion.ξ_pos
  have hξξ₀ : ξ ≤ (s.ξ₀ : ℝ) := by
    have hcast : (s.completion.ξ : ℝ) ≤ (s.ξ₀ : ℝ) := by
      exact_mod_cast s.completion.ξ_le_source
    simpa only [ξ] using hcast
  have hτscale : τ = ξ / (4 * (n : ℝ)) := by
    exact cast_rationalRegularizationScale s n
  have hobjective :
      Real.log (bethePermanent A) - ξ * n ≤ betheObjective A X := by
    have hbudget := regularization_budget_of_paper_scale
      (show (0 : ℝ) < n by positivity)
      (log_natCast_le_natCast_mul_log_two (show 1 ≤ n by omega))
      hξ hτscale
    have hvalue := betheLogValue_le_regularizedMaximizer
      (show 1 < n by omega)
      (le_of_lt (by
        change 0 < ((rationalRegularizationScale s n : ℚ) : ℝ)
        exact_mod_cast rationalRegularizationScale_pos s (show 0 < n by omega)))
      hA hX hmax
    have hmatch := positiveMatrix_hasPerfectMatching hA
    have hlogBethe : Real.log (bethePermanent A) = betheLogValue A := by
      rw [bethePermanent, if_pos hmatch, Real.log_exp]
    rw [hlogBethe]
    linarith
  have hmatch := positiveMatrix_hasPerfectMatching hA
  have hlogBethe : Real.log (bethePermanent A) = betheLogValue A := by
    rw [bethePermanent, if_pos hmatch, Real.log_exp]
  have hupper : Real.log (Matrix.permanent A) ≤
      Real.log (bethePermanent A) + n * (Real.log 2 / 2) := by
    rw [hlogBethe]
    exact log_permanent_le_betheLogValue_add_log_two_half hn A hA
  have hcertificate :=
    exp_betheObjective_add_maximumMatchingGain_le_permanent
      stableCoefficient hn hA hX (fun i j ↦ (hXint i).2 j |>.1)
  have hnearGain : betheSlack n (Real.log (bethePermanent A))
      (Real.log (Matrix.permanent A)) < δ * n →
      3 * (s.γ₀ : ℝ) / 8 * n ≤ maximumMatchingGain A X := by
    intro hnear
    rw [hlogBethe] at hnear
    exact nearCase_maximumMatchingGain_ge_threeEighths
      anariRezaeiRowInequality hn
      s.cleanGain hκ hγ.le
      (show (1 : ℝ) ≤ n by exact_mod_cast (show 1 ≤ n by omega))
      (log_natCast_le_natCast_mul_log_two (show 1 ≤ n by omega))
      hξ hξξ₀ hτscale
      (by exact_mod_cast s.completion.η_pos)
      s.completion.η_le_tenth
      s.completion.row_small s.completion.cycle_small
      s.completion.transfer_small hA hX hXint hKKT hnear
  have hcases := completionCaseDisjunction
    (logPermanent := Real.log (Matrix.permanent A))
    (logBethe := Real.log (bethePermanent A))
    (objective := betheObjective A X)
    (gain := maximumMatchingGain A X)
    (δ := δ) (ξ := ξ) (γ := (s.γ₀ : ℝ))
    hobjective (maximumMatchingGain_nonneg A X) hupper hnearGain
  have hgap := positiveDichotomy_exponent hcases
  have hεcast := cast_rationalEpsilonPlus s.completion
  constructor
  · exact hcertificate
  · simpa only [η, δ, ξ, hεcast] using hgap

/-- The positive-matrix certificate with a rational improvement fixedValue and
an explicitly rational regularization scale. -/
theorem rationalScales_exactPositiveCertificate
    (stableCoefficient : AnariOveisGharanStableCoefficient.{0})
    (s : RationalStructuralScales) :
    ExactPositiveCertificate
      ((rationalEpsilonPlus s.completion : ℚ) : ℝ) := by
  intro n hn A hA
  let τ : ℝ := ((rationalRegularizationScale s n : ℚ) : ℝ)
  have hξ : 0 < (s.completion.ξ : ℝ) := by
    exact_mod_cast s.completion.ξ_pos
  have hτscale : τ = (s.completion.ξ : ℝ) / (4 * (n : ℝ)) := by
    exact cast_rationalRegularizationScale s n
  obtain ⟨X, hX, hXint, hmax, hKKT, _hobjective⟩ :=
    exists_regularizedOptimizer_at_paper_scale
      (show 1 < n by omega)
      (show (0 : ℝ) < n by positivity)
      (log_natCast_le_natCast_mul_log_two (show 1 ≤ n by omega))
      hξ hτscale A hA
  obtain ⟨hlower, hgap⟩ := rationalScales_certificate_of_optimizer
    stableCoefficient s hn hA hX hXint hmax hKKT
  exact ⟨X, hX, hlower, hgap⟩

theorem exists_rational_exactPositiveCertificate
    (stableCoefficient : AnariOveisGharanStableCoefficient.{0}) :
    ∃ ε : ℚ, 0 < ε ∧ ExactPositiveCertificate (ε : ℝ) := by
  obtain ⟨s⟩ := exists_rational_structuralScales
  exact ⟨rationalEpsilonPlus s.completion,
    rationalEpsilonPlus_pos s.completion,
    rationalScales_exactPositiveCertificate stableCoefficient s⟩

end BeyondBethe
