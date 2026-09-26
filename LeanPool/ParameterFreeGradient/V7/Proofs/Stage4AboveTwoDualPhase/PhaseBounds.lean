/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage4AboveTwoDualPhase.DualEnergy

/-!
The prescribed primal and dual horizons imply objective-gap and terminal-gradient bounds.
-/

@[expose] public section

namespace V7.Stage4AboveTwoDualPhase

/-- The scaled quadratic weight sequence held constant from the terminal index onward. -/
noncomputable def plateauU (p eta : ℝ) (n : ℕ) : ScalarSeq :=
  fun k ↦ if k < n then
    aboveGamma p eta n * ((k : ℝ) + 1) ^ (2 : ℕ)
  else aboveGamma p eta n * (n : ℝ) ^ (2 : ℕ)

/-- The increments of the scaled quadratic weight sequence with terminal plateau. -/
noncomputable def plateauDw (p eta : ℝ) (n : ℕ) : ScalarSeq :=
  fun k ↦ plateauU p eta n k -
    (if k = 0 then 0 else plateauU p eta n (k - 1))

theorem conjugate_budget_identity {p : ℝ} (hp : 2 < p) :
    conjugateExponent p * (1 + aboveBudgetExponent p) = 2 := by
  change O3.conjugateExponent p * (1 + (p - 2) / p) = 2
  rw [O3.conjugateExponent_eq]
  field_simp [show p ≠ 0 by linarith, show p - 1 ≠ 0 by linarith]
  ring

private lemma aboveH_unit_le {p : ℝ} (hp : 2 < p) (z : Point d)
    (hz : lpNorm p z ≤ 1) :
    aboveH p z ≤ 1 / p := by
  have hnorm : 0 ≤ lpNorm p z := O3.lpNorm_nonneg _ _
  have hpow := Real.rpow_le_rpow hnorm hz (by linarith : 0 ≤ p)
  rw [Real.one_rpow] at hpow
  unfold aboveH
  exact mul_le_of_le_one_right (by positivity : 0 ≤ 1 / p) hpow

theorem phaseOnePowerBound (p : ℝ) (hp : 2 < p) (n : ℕ) (hn : 1 ≤ n)
    (data : AbovePrimalPhaseData p d n)
    (hass : AbovePrimalPhaseAssumptions data) (z : Point d)
    (hzstar : data.oracle.value z = data.fstar)
    (hznorm : lpNorm p z ≤ 1)
    (hu : data.u = plateauU p (1 / p) n)
    (hdw : data.dw = plateauDw p (1 / p) n) :
    data.oracle.value (data.x n) - data.fstar ≤
      aboveHp p / (n : ℝ) ^ ((p + 2) / p) := by
  have hp0 : 0 < p := by linarith
  have heta : 0 < (1 / p : ℝ) := one_div_pos.mpr hp0
  have hbal := V7.aboveWeightErrorBalance p hp n hn (1 / p) heta
  change
    aboveErrorSum p n (plateauU p (1 / p) n) (plateauDw p (1 / p) n) ≤
        (1 / p) / 2 ∧
      plateauU p (1 / p) n n =
        aboveGrowthConstant p * (1 / p) ^ aboveBudgetExponent p *
          (n : ℝ) ^ ((p + 2) / p) at hbal
  have hgap := V7.abovePrimalTerminalGap p hp d n data hass z hzstar
  rw [hu, hdw] at hgap
  have hh := aboveH_unit_le hp z hznorm
  have hnum : aboveH p z +
      aboveErrorSum p n (plateauU p (1 / p) n) (plateauDw p (1 / p) n) ≤
      3 / (2 * p) := by
    have := add_le_add hh hbal.1
    field_simp [hp0.ne'] at this ⊢
    linarith
  have hc := Stage4AboveTwo.growthConstant_pos hp
  have ha : 0 < (1 / p) ^ aboveBudgetExponent p :=
    Real.rpow_pos_of_pos heta _
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hr : 0 < (p + 2) / p := div_pos (by linarith) hp0
  have hnpow : 0 < (n : ℝ) ^ ((p + 2) / p) :=
    Real.rpow_pos_of_pos hnpos _
  have hden : 0 < plateauU p (1 / p) n n := by
    rw [hbal.2]
    positivity
  have hquot :
      (aboveH p z +
        aboveErrorSum p n (plateauU p (1 / p) n) (plateauDw p (1 / p) n)) /
          plateauU p (1 / p) n n ≤
      (3 / (2 * p)) /
        (aboveGrowthConstant p * (1 / p) ^ aboveBudgetExponent p *
          (n : ℝ) ^ ((p + 2) / p)) := by
    rw [hbal.2]
    exact div_le_div_of_nonneg_right hnum (by positivity)
  have honepow : (1 / p) ^ aboveBudgetExponent p =
      1 / p ^ aboveBudgetExponent p := by
    rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1) hp0.le, Real.one_rpow]
  have hid :
      (3 / (2 * p)) /
        (aboveGrowthConstant p * (1 / p) ^ aboveBudgetExponent p *
          (n : ℝ) ^ ((p + 2) / p)) =
      aboveHp p / (n : ℝ) ^ ((p + 2) / p) := by
    rw [honepow]
    unfold aboveHp
    field_simp [hp0.ne', hc.ne',
      (Real.rpow_pos_of_pos hp0 _).ne', hnpow.ne']
  rw [hid] at hquot
  exact le_trans hgap hquot

private theorem horizon_power_bound {H delta beta rho : ℝ}
    (hH : 0 < H) (hdelta : 0 < delta)
    (_hbeta : 0 < beta) (hrho : 0 < rho) (hprod : beta * rho = 1) :
    let n := Nat.ceil ((H / delta) ^ beta)
    1 ≤ n ∧ H / (n : ℝ) ^ rho ≤ delta := by
  dsimp only
  let x : ℝ := (H / delta) ^ beta
  have hx : 0 < x := Real.rpow_pos_of_pos (div_pos hH hdelta) _
  have hn : 1 ≤ Nat.ceil x := Nat.ceil_pos.mpr hx
  have hceil : x ≤ (Nat.ceil x : ℝ) := Nat.le_ceil x
  have hnreal : 0 < (Nat.ceil x : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hpow := Real.rpow_le_rpow hx.le hceil hrho.le
  have hxpow : x ^ rho = H / delta := by
    dsimp [x]
    rw [← Real.rpow_mul (div_pos hH hdelta).le, hprod, Real.rpow_one]
  rw [hxpow] at hpow
  have hnpow : 0 < (Nat.ceil x : ℝ) ^ rho :=
    Real.rpow_pos_of_pos hnreal _
  constructor
  · exact hn
  · rw [div_le_iff₀ hnpow]
    have := mul_le_mul_of_nonneg_right hpow hdelta.le
    field_simp [hdelta.ne'] at this
    nlinarith

theorem phaseOneHorizonBound (p : ℝ) (hp : 2 < p) (delta : ℝ)
    (hdelta : 0 < delta)
    (n : ℕ)
    (hn : n = Nat.ceil ((aboveHp p / delta) ^ (p / (p + 2))))
    (data : AbovePrimalPhaseData p d n)
    (hass : AbovePrimalPhaseAssumptions data) (z : Point d)
    (hzstar : data.oracle.value z = data.fstar)
    (hznorm : lpNorm p z ≤ 1)
    (hu : data.u = plateauU p (1 / p) n)
    (hdw : data.dw = plateauDw p (1 / p) n) :
    data.oracle.value (data.x n) - data.fstar ≤ delta := by
  have hp0 : 0 < p := by linarith
  have hp2 : 0 < p + 2 := by linarith
  have hhor := horizon_power_bound
    (Stage4AboveTwo.hpConstant_pos hp) hdelta
    (div_pos hp0 hp2) (div_pos hp2 hp0)
    (by field_simp [hp0.ne', hp2.ne'])
  rw [← hn] at hhor
  have hpower := phaseOnePowerBound p hp n hhor.1 data hass z
    hzstar hznorm hu hdw
  exact le_trans hpower hhor.2

theorem phaseTwoEnergyBound (p : ℝ) (hp : 2 < p) (n : ℕ) (hn : 1 ≤ n)
    (delta : ℝ) (hdelta : 0 < delta)
    (data : AboveDualPhaseData p d n)
    (hass : AboveDualPhaseAssumptions data)
    (hgap0 : data.oracle.value (data.q 0) -
      sInf (Set.range data.oracle.value) ≤ delta)
    (hu : data.u = plateauU p
      (delta ^ (conjugateExponent p) / conjugateExponent p) n)
    (hdw : data.dw = plateauDw p
      (delta ^ (conjugateExponent p) / conjugateExponent p) n) :
    aboveHstar p (data.oracle.gradient (data.q n)) ≤
      delta /
        (aboveGrowthConstant p *
          (delta ^ (conjugateExponent p) / conjugateExponent p) ^
            (aboveBudgetExponent p) *
          (n : ℝ) ^ ((p + 2) / p)) +
      (delta ^ (conjugateExponent p) / conjugateExponent p) / 2 := by
  have hp0 : 0 < p := by linarith
  have hq : 0 < conjugateExponent p := Stage4AboveTwo.conjugate_pos hp
  let eta := delta ^ (conjugateExponent p) / conjugateExponent p
  have heta : 0 < eta := div_pos (Real.rpow_pos_of_pos hdelta _) hq
  have hbal := V7.aboveWeightErrorBalance p hp n hn eta heta
  change
    aboveErrorSum p n (plateauU p eta n) (plateauDw p eta n) ≤ eta / 2 ∧
      plateauU p eta n n =
        aboveGrowthConstant p * eta ^ aboveBudgetExponent p *
          (n : ℝ) ^ ((p + 2) / p) at hbal
  have hdual := V7.aboveDualTerminalEnergy p hp n data hass
  rw [hu, hdw] at hdual
  have hden : 0 < plateauU p eta n n := by
    rw [hbal.2]
    have hc := Stage4AboveTwo.growthConstant_pos hp
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
    positivity
  have hfirst :
      (data.oracle.value (data.q 0) - sInf (Set.range data.oracle.value)) /
          plateauU p eta n n ≤ delta / plateauU p eta n n :=
    div_le_div_of_nonneg_right hgap0 hden.le
  have hsum := add_le_add hfirst hbal.1
  calc
    aboveHstar p (data.oracle.gradient (data.q n)) ≤
        (data.oracle.value (data.q 0) - sInf (Set.range data.oracle.value)) /
            plateauU p eta n n +
          aboveErrorSum p n (plateauU p eta n) (plateauDw p eta n) := hdual
    _ ≤ delta / plateauU p eta n n + eta / 2 := hsum
    _ = delta /
          (aboveGrowthConstant p * eta ^ aboveBudgetExponent p *
            (n : ℝ) ^ ((p + 2) / p)) + eta / 2 := by rw [hbal.2]
    _ = _ := by rfl

private lemma eta_power_identity (p : ℝ) (hp : 2 < p) (delta : ℝ)
    (hdelta : 0 < delta) :
    (delta ^ (conjugateExponent p) / conjugateExponent p) ^
        (1 + aboveBudgetExponent p) =
      delta ^ (2 : ℝ) /
        (conjugateExponent p) ^ (1 + aboveBudgetExponent p) := by
  have hq : 0 < conjugateExponent p := Stage4AboveTwo.conjugate_pos hp
  rw [Real.div_rpow (Real.rpow_nonneg hdelta.le _) hq.le]
  rw [← Real.rpow_mul hdelta.le, conjugate_budget_identity hp]

theorem phaseTwoHorizonBound (p : ℝ) (hp : 2 < p) (delta : ℝ)
    (hdelta : 0 < delta)
    (n : ℕ)
    (hn : n = Nat.ceil ((aboveJp p / delta) ^ (p / (p + 2))))
    (data : AboveDualPhaseData p d n)
    (hass : AboveDualPhaseAssumptions data)
    (hgap0 : data.oracle.value (data.q 0) -
      sInf (Set.range data.oracle.value) ≤ delta)
    (hu : data.u = plateauU p
      (delta ^ (conjugateExponent p) / conjugateExponent p) n)
    (hdw : data.dw = plateauDw p
      (delta ^ (conjugateExponent p) / conjugateExponent p) n) :
    aboveHstar p (data.oracle.gradient (data.q n)) ≤
        delta ^ (conjugateExponent p) / conjugateExponent p ∧
      lpNorm (conjugateExponent p)
        (data.oracle.gradient (data.q n)) ≤ delta := by
  have hp0 : 0 < p := by linarith
  have hp2 : 0 < p + 2 := by linarith
  have hq : 0 < conjugateExponent p := Stage4AboveTwo.conjugate_pos hp
  let eta := delta ^ (conjugateExponent p) / conjugateExponent p
  have heta : 0 < eta := div_pos (Real.rpow_pos_of_pos hdelta _) hq
  have hc := Stage4AboveTwo.growthConstant_pos hp
  have ha : 0 < eta ^ aboveBudgetExponent p :=
    Real.rpow_pos_of_pos heta _
  have hhor := horizon_power_bound
    (Stage4AboveTwo.jpConstant_pos hp) hdelta
    (div_pos hp0 hp2) (div_pos hp2 hp0)
    (by field_simp [hp0.ne', hp2.ne'])
  rw [← hn] at hhor
  dsimp only at hhor
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hhor.1)
  have hnpow : 0 < (n : ℝ) ^ ((p + 2) / p) :=
    Real.rpow_pos_of_pos hnpos _
  have henergy := phaseTwoEnergyBound p hp n hhor.1 delta hdelta
    data hass hgap0 hu hdw
  have hetaPower := eta_power_identity p hp delta hdelta
  change eta ^ (1 + aboveBudgetExponent p) =
      delta ^ (2 : ℝ) /
        (conjugateExponent p) ^ (1 + aboveBudgetExponent p) at hetaPower
  have hJ : aboveJp p ≤ delta * (n : ℝ) ^ ((p + 2) / p) := by
    exact (div_le_iff₀ hnpow).mp hhor.2
  have htwodelta :
      2 * delta ≤
        aboveGrowthConstant p * eta ^ (1 + aboveBudgetExponent p) *
          (n : ℝ) ^ ((p + 2) / p) := by
    have hmul := mul_le_mul_of_nonneg_left hJ
      (show 0 ≤ aboveGrowthConstant p * eta ^
        (1 + aboveBudgetExponent p) / delta by positivity)
    have hident :
        (aboveGrowthConstant p * eta ^ (1 + aboveBudgetExponent p) / delta) *
            aboveJp p = 2 * delta := by
      rw [hetaPower]
      unfold aboveJp
      field_simp [hdelta.ne', hc.ne',
        (Real.rpow_pos_of_pos hq _).ne']
      rw [show delta ^ (2 : ℝ) = delta ^ (2 : ℕ) by norm_num]
    rw [hident] at hmul
    calc
      2 * delta ≤
          (aboveGrowthConstant p * eta ^ (1 + aboveBudgetExponent p) / delta) *
            (delta * (n : ℝ) ^ ((p + 2) / p)) := hmul
      _ = aboveGrowthConstant p * eta ^ (1 + aboveBudgetExponent p) *
            (n : ℝ) ^ ((p + 2) / p) := by field_simp [hdelta.ne']
  have hfirst :
      delta /
        (aboveGrowthConstant p * eta ^ aboveBudgetExponent p *
          (n : ℝ) ^ ((p + 2) / p)) ≤ eta / 2 := by
    have hden : 0 < aboveGrowthConstant p * eta ^ aboveBudgetExponent p *
        (n : ℝ) ^ ((p + 2) / p) := by positivity
    rw [div_le_iff₀ hden]
    have hetaSplit : eta ^ (1 + aboveBudgetExponent p) =
        eta * eta ^ aboveBudgetExponent p := by
      rw [Real.rpow_add heta]
      simp
    rw [hetaSplit] at htwodelta
    nlinarith
  have hestar : aboveHstar p (data.oracle.gradient (data.q n)) ≤ eta := by
    refine le_trans henergy ?_
    change delta /
        (aboveGrowthConstant p * eta ^ aboveBudgetExponent p *
          (n : ℝ) ^ ((p + 2) / p)) + eta / 2 ≤ eta
    linarith
  constructor
  · simpa [eta] using hestar
  · have hnorm : 0 ≤ lpNorm (conjugateExponent p)
        (data.oracle.gradient (data.q n)) := O3.lpNorm_nonneg _ _
    have hrpow :
        (lpNorm (conjugateExponent p)
          (data.oracle.gradient (data.q n))) ^ (conjugateExponent p) ≤
          delta ^ (conjugateExponent p) := by
      unfold aboveHstar at hestar
      dsimp [eta] at hestar
      have := mul_le_mul_of_nonneg_left hestar hq.le
      field_simp [hq.ne'] at this
      exact this
    exact (Real.rpow_le_rpow_iff hnorm hdelta.le hq).mp hrpow

end V7.Stage4AboveTwoDualPhase

namespace V7

theorem abovePhaseOneGapBound (p : ℝ) (hp : 2 < p) (n : ℕ) (hn : 1 ≤ n)
    (data : AbovePrimalPhaseData p d n)
    (hass : AbovePrimalPhaseAssumptions data) (z : Point d)
    (hzstar : data.oracle.value z = data.fstar)
    (hznorm : lpNorm p z ≤ 1)
    (hu : data.u = Stage4AboveTwoDualPhase.plateauU p (1 / p) n)
    (hdw : data.dw = Stage4AboveTwoDualPhase.plateauDw p (1 / p) n) :
    data.oracle.value (data.x n) - data.fstar ≤
      aboveHp p / (n : ℝ) ^ ((p + 2) / p) :=
  Stage4AboveTwoDualPhase.phaseOnePowerBound p hp n hn data hass z hzstar
    hznorm hu hdw

theorem abovePhaseOneHorizonBound (p : ℝ) (hp : 2 < p) (delta : ℝ)
    (hdelta : 0 < delta)
    (n : ℕ)
    (hn : n = Nat.ceil ((aboveHp p / delta) ^ (p / (p + 2))))
    (data : AbovePrimalPhaseData p d n)
    (hass : AbovePrimalPhaseAssumptions data) (z : Point d)
    (hzstar : data.oracle.value z = data.fstar)
    (hznorm : lpNorm p z ≤ 1)
    (hu : data.u = Stage4AboveTwoDualPhase.plateauU p (1 / p) n)
    (hdw : data.dw = Stage4AboveTwoDualPhase.plateauDw p (1 / p) n) :
    data.oracle.value (data.x n) - data.fstar ≤ delta :=
  Stage4AboveTwoDualPhase.phaseOneHorizonBound p hp delta hdelta n hn data
    hass z hzstar hznorm hu hdw

theorem abovePhaseTwoEnergyBound (p : ℝ) (hp : 2 < p)
    (n : ℕ) (hn : 1 ≤ n) (delta : ℝ) (hdelta : 0 < delta)
    (data : AboveDualPhaseData p d n)
    (hass : AboveDualPhaseAssumptions data)
    (hgap0 : data.oracle.value (data.q 0) -
      sInf (Set.range data.oracle.value) ≤ delta)
    (hu : data.u = Stage4AboveTwoDualPhase.plateauU p
      (delta ^ (conjugateExponent p) / conjugateExponent p) n)
    (hdw : data.dw = Stage4AboveTwoDualPhase.plateauDw p
      (delta ^ (conjugateExponent p) / conjugateExponent p) n) :
    aboveHstar p (data.oracle.gradient (data.q n)) ≤
      delta /
        (aboveGrowthConstant p *
          (delta ^ (conjugateExponent p) / conjugateExponent p) ^
            aboveBudgetExponent p *
          (n : ℝ) ^ ((p + 2) / p)) +
      (delta ^ (conjugateExponent p) / conjugateExponent p) / 2 :=
  Stage4AboveTwoDualPhase.phaseTwoEnergyBound p hp n hn delta hdelta data hass
    hgap0 hu hdw

theorem abovePhaseTwoTerminalGradientBound (p : ℝ) (hp : 2 < p)
    (delta : ℝ) (hdelta : 0 < delta)
    (n : ℕ)
    (hn : n = Nat.ceil ((aboveJp p / delta) ^ (p / (p + 2))))
    (data : AboveDualPhaseData p d n)
    (hass : AboveDualPhaseAssumptions data)
    (hgap0 : data.oracle.value (data.q 0) -
      sInf (Set.range data.oracle.value) ≤ delta)
    (hu : data.u = Stage4AboveTwoDualPhase.plateauU p
      (delta ^ (conjugateExponent p) / conjugateExponent p) n)
    (hdw : data.dw = Stage4AboveTwoDualPhase.plateauDw p
      (delta ^ (conjugateExponent p) / conjugateExponent p) n) :
    aboveHstar p (data.oracle.gradient (data.q n)) ≤
        delta ^ (conjugateExponent p) / conjugateExponent p ∧
      lpNorm (conjugateExponent p)
        (data.oracle.gradient (data.q n)) ≤ delta :=
  Stage4AboveTwoDualPhase.phaseTwoHorizonBound p hp delta hdelta n hn
    data hass hgap0 hu hdw

end V7
