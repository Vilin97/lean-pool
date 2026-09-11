/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.OutgoingEntranceCone

/-!
# Actual shaped-hold errors with constants uniform in the small slope

The angular lag is solved exactly from its incoming value at `holdStart`.
The two decaying modes are kept separate, so no inverse small-slope constant
appears in the error estimate.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ShapedWaitBounds

open Set Filter MeasureTheory
open scoped Topology ContDiff
open OutgoingSchedule OutgoingTail NaturalAxisData OutgoingEntranceCone

theorem linearLag_neg (r b : ℝ → ℝ) (q₀ y : ℝ) :
    linearLag r (fun t => -b t) (-q₀) y = -linearLag r b q₀ y := by
  unfold linearLag OutgoingSchedule.primitive
  simp only [mul_neg, intervalIntegral.integral_neg]
  ring

theorem linearLag_le_constant {r b : ℝ → ℝ} (hr : Continuous r) (hb : Continuous b)
    {q₀ B y : ℝ} (hy : 0 ≤ y) (hq : q₀ ≤ B)
    (hs : ∀ t ∈ Icc (0 : ℝ) y, b t ≤ r t * B) : linearLag r b q₀ y ≤ B := by
  have h := linearLag_lower_barrier hr hb.fun_neg (q₀ := -q₀) (β := -B) (κ := 0) hy
    (by linarith) (fun t ht => by have := hs t ht; linarith)
  rw [linearLag_neg] at h
  linarith

theorem linearLag_abs_le {r b : ℝ → ℝ} (hr : Continuous r) (hb : Continuous b)
    {q₀ B y : ℝ} (hy : 0 ≤ y) (hq : |q₀| ≤ B)
    (hs : ∀ t ∈ Icc (0 : ℝ) y, |b t| ≤ r t * B) : |linearLag r b q₀ y| ≤ B := by
  apply abs_le.mpr
  refine ⟨?_, linearLag_le_constant hr hb hy ((le_abs_self _).trans hq)
    (fun t ht => (le_abs_self _).trans (hs t ht))⟩
  have h := linearLag_lower_barrier hr hb (β := -B) (κ := 0) hy
    (by have := (abs_le.mp hq).1; linarith) (fun t ht => by
      have := (abs_le.mp (hs t ht)).1
      linarith)
  linarith

theorem angularSource_abs_bound (c : Parameters) {h y η : ℝ} (hh : 0 ≤ h)
    (hh1 : h ≤ 1 / 100) (hy : 0 ≤ y) (hη : |η| ≤ 1) :
    |angularSource c h η y| ≤ 8 := by
  have hr := angularRate_bounds c y
  have hl : |slope c.dropLength c.lam y| ≤ 1 := by
    unfold angularRate at hr
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hW : |transportW c h y η| ≤ 3 :=
    abs_le.mpr ⟨(transportW_bounds c hh hh1 hy hη).1,
      (transportW_bounds c hh hh1 hy hη).2.trans (by norm_num)⟩
  have hk := dropCoefficient_bounds c.m y
  have hsq := parameter_square_le_one hη
  have hd : 0 ≤ d η ∧ d η ≤ 1 := by unfold d; constructor <;> linarith [sq_nonneg η]
  have hD : 0 ≤ D h ∧ D h ≤ 1 / 2 := by unfold D; constructor <;> linarith
  have hJ := eta_shapeGradient_bounds hη
  have hcoef : |1 - 2 * dropCoefficient c.m y * η ^ 2| ≤ 9 := by
    have hp := mul_le_mul hk.2 hsq (sq_nonneg η) (by norm_num : (0 : ℝ) ≤ 4)
    apply abs_le.mpr
    constructor <;> linarith [mul_nonneg hk.1 (sq_nonneg η)]
  have hfirst : |-slope c.dropLength c.lam y * transportW c h y η| ≤ 3 := by
    rw [abs_mul, abs_neg]
    exact (mul_le_mul hl hW (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (by ring)
  have hsecond : |h * (1 - 2 * dropCoefficient c.m y * η ^ 2)| ≤ 9 / 100 := by
    rw [abs_mul, abs_of_nonneg hh]
    have hb := mul_le_mul hh1 hcoef (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 100)
    linarith
  have hbase : 0 ≤ D h + d η * dropCoefficient c.m y ∧ D h + d η * dropCoefficient c.m y ≤ 9 / 2 :=
      by
    have hb := mul_le_mul hd.2 hk.2 hk.1 (by norm_num : (0 : ℝ) ≤ 1)
    constructor <;> linarith [mul_nonneg hd.1 hk.1]
  have hthird : |(D h + d η * dropCoefficient c.m y) * η * shapeGradient η| ≤ 9 / 2 := by
    rw [mul_assoc, abs_mul, abs_of_nonneg hbase.1, abs_of_nonneg (by
        linarith [sq_nonneg η] : 0 ≤ η * shapeGradient η)]
    exact (mul_le_mul hbase.2 hJ.2 (by
        linarith [sq_nonneg η]) (by norm_num : (0 : ℝ) ≤ 9 / 2)).trans_eq (by ring)
  unfold angularSource
  have hs : |-slope c.dropLength c.lam y * transportW c h y η -
      h * (1 - 2 * dropCoefficient c.m y * η ^ 2) +
        (D h + d η * dropCoefficient c.m y) * η * shapeGradient η| ≤
      |-slope c.dropLength c.lam y * transportW c h y η| +
        |h * (1 - 2 * dropCoefficient c.m y * η ^ 2)| +
          |(D h + d η * dropCoefficient c.m y) * η * shapeGradient η| :=
    (abs_add_le _ _).trans (add_le_add_left (abs_sub _ _) _)
  linarith

theorem angularLag_abs_bound (c : Parameters) {h y η : ℝ} (hh : 0 ≤ h)
    (hh1 : h ≤ 1 / 100) (hy : 0 ≤ y) (hη : |η| ≤ 1) :
    |angularLag c h η y| ≤ 10 := by
  have hi := angularSource_abs_bound c hh hh1 (show (0 : ℝ) ≤ 0 by rfl) hη
  rw [angularSource_ideal c h η le_rfl] at hi
  have hinit : |idealAngularLag h η| ≤ 10 := by
    unfold idealAngularLag
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 8 / 5)]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 8 / 5)).mpr
    linarith
  apply linearLag_abs_le (angularRate_contDiff c).continuous
    (angularSource_contDiff c h η).continuous hy hinit
  intro t ht
  have hs := angularSource_abs_bound c hh hh1 ht.1 hη
  have hr := (angularRate_bounds c t).1
  linarith

/-- Equilibrium, given by `(c.lam - h + D h * η * shapeGradient η) / (1 - c.lam)`. -/
noncomputable def equilibrium (c : Parameters) (h η : ℝ) : ℝ :=
  (c.lam - h + D h * η * shapeGradient η) / (1 - c.lam)

/-- Hold coefficient, given by `L h η * averagedDrop c c.holdStart`. -/
noncomputable def holdCoefficient (c : Parameters) (h η : ℝ) : ℝ :=
  L h η * averagedDrop c c.holdStart

/-- Hold source, given by `c.lam - h + D h * η * shapeGradient η - c.lam * holdCoefficient c h η
* Real.exp (-t)`. -/
noncomputable def holdSource (c : Parameters) (h η t : ℝ) : ℝ :=
  c.lam - h + D h * η * shapeGradient η - c.lam * holdCoefficient c h η * Real.exp (-t)

/-- Hold formula, constructed using `equilibrium`. -/
noncomputable def holdFormula (c : Parameters) (h η t : ℝ) : ℝ :=
  equilibrium c h η +
    (angularLag c h η c.holdStart - equilibrium c h η - holdCoefficient c h η) *
      Real.exp (-(1 - c.lam) * t) + holdCoefficient c h η * Real.exp (-t)

theorem hold_rate_pos (c : Parameters) : 0 < 1 - c.lam := by linarith [c.lam_lt]

theorem dropCoefficient_hold (c : Parameters) {t : ℝ} (ht : 0 ≤ t) :
    dropCoefficient c.m (c.holdStart + t) = 0 := by
  apply dropCoefficient_late c.m_pos
  dsimp [Parameters.holdStart, Parameters.dropLength]
  linarith

theorem averagedDrop_hold (c : Parameters) {t : ℝ} (ht : 0 ≤ t) :
    averagedDrop c (c.holdStart + t) = Real.exp (-t) * averagedDrop c c.holdStart := by
  have hl := historyAverage_late (dropCoefficient_contDiff c.m_pos).continuous
    (b₀ := (4 : ℝ)) (a := c.holdStart) (y := c.holdStart + t) (by linarith)
    (fun u hu => by
      apply dropCoefficient_late c.m_pos
      dsimp [Parameters.holdStart, Parameters.dropLength] at hu
      linarith)
  simpa only [averagedDrop, add_sub_cancel_left] using hl

theorem angularRate_hold (c : Parameters) {t : ℝ} (ht : 0 ≤ t) :
    angularRate c (c.holdStart + t) = 1 - c.lam := by
  unfold angularRate
  rw [slope_hold c.dropLength_pos.le (by dsimp [Parameters.holdStart]; linarith)]
  ring

theorem angularSource_hold (c : Parameters) (h η : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    angularSource c h η (c.holdStart + t) = holdSource c h η t := by
  unfold angularSource transportW holdSource holdCoefficient
  rw [dropCoefficient_hold c ht, averagedDrop_hold c ht,
    slope_hold c.dropLength_pos.le (by dsimp [Parameters.holdStart]; linarith)]
  ring

theorem decay_hasDerivAt (r t : ℝ) : HasDerivAt (fun t => Real.exp (-r * t))
    (-r * Real.exp (-r * t)) t := by
  convert! ((hasDerivAt_id t).const_mul (-r)).exp using 1
  simp only [id_eq]
  ring

theorem holdFormula_hasDerivAt (c : Parameters) (h η t : ℝ) :
    HasDerivAt (holdFormula c h η)
      (holdSource c h η t - (1 - c.lam) * holdFormula c h η t) t := by
  have hd := ((decay_hasDerivAt (1 - c.lam) t).const_mul
    (angularLag c h η c.holdStart - equilibrium c h η - holdCoefficient c h η)).const_add
      (equilibrium c h η)
  have hd' := hd.fun_add (((hasDerivAt_id t).fun_neg.exp).const_mul (holdCoefficient c h η))
  convert! hd' using 1
  unfold holdSource holdFormula equilibrium
  simp only [id_eq]
  field_simp [(hold_rate_pos c).ne']; ring

/-- Exact integration of the shaped-hold equation, with no division by `λ`. -/
theorem angularLag_hold_formula (c : Parameters) (h η : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    angularLag c h η (c.holdStart + t) = holdFormula c h η t := by
  have hb : Continuous (holdSource c h η) :=
    continuous_const.sub (continuous_const.mul (Real.continuous_exp.comp continuous_neg))
  have ha := linearLag_eq_of_solution (r := fun _ => 1 - c.lam) (b := holdSource c h η)
    (f := fun u => angularLag c h η (c.holdStart + u)) continuous_const hb
    (by simp : angularLag c h η (c.holdStart + 0) = angularLag c h η c.holdStart) (fun u hu => by
      have hu0 := (uIcc_of_le ht ▸ hu).1
      have hd := (angularLag_hasDerivAt c h η (c.holdStart + u)).comp u ((hasDerivAt_id
          u).const_add c.holdStart)
      simp only [Function.comp_def, mul_one, angularSource_hold c h η hu0,
        angularRate_hold c hu0] at hd
      exact hd)
  have hf := linearLag_eq_of_solution (r := fun _ => 1 - c.lam) (b := holdSource c h η)
    (f := holdFormula c h η) continuous_const hb
    (show holdFormula c h η 0 = angularLag c h η c.holdStart by
      simp only [holdFormula, mul_zero, neg_zero, Real.exp_zero, mul_one]
      ring)
    (fun u _ => holdFormula_hasDerivAt c h η u) (y := t)
  exact ha.trans hf.symm

theorem equilibrium_bounds (v : TailData) {η : ℝ} (hh1 : v.h ≤ 1 / 100) (hη : |η| ≤ 1) :
    0 ≤ equilibrium v.core v.h η ∧ equilibrium v.core v.h η ≤ 1 := by
  have hr := hold_rate_pos v.core
  have hj := eta_shapeGradient_bounds hη
  have hD : 0 ≤ D v.h ∧ D v.h ≤ 1 / 2 := by unfold D; constructor <;> linarith [v.h_pos]
  have hprod := mul_le_mul hD.2 hj.2 (by linarith [sq_nonneg η]) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hprod0 := mul_nonneg hD.1 (show 0 ≤ η * shapeGradient η by linarith [sq_nonneg η])
  unfold equilibrium
  constructor
  · exact div_nonneg (by linarith [v.h_small, v.h_pos]) hr.le
  · apply (div_le_iff₀ hr).mpr
    linarith [v.core.lam_lt, v.h_pos]

theorem holdCoefficient_bounds (c : Parameters) {h η : ℝ} (hh : 0 ≤ h)
    (hh1 : h ≤ 1 / 100) (hη : |η| ≤ 1) : 0 ≤ holdCoefficient c h η ∧ holdCoefficient c h η ≤ 4 := by
  have hL := natural_L_bounds hh hh1 hη
  have hk := averagedDrop_bounds c c.holdStart_pos.le
  unfold holdCoefficient
  refine ⟨mul_nonneg (by linarith) hk.1, ?_⟩
  exact (mul_le_mul hL.2 hk.2 hk.1 (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (by ring)

theorem angularLag_hold_error (v : TailData) {η t : ℝ} (hh1 : v.h ≤ 1 / 100)
    (hη : |η| ≤ 1) (ht : 0 ≤ t) :
    |angularLag v.core v.h η (v.core.holdStart + t) - equilibrium v.core v.h η| ≤
      19 * Real.exp (-(1 - v.core.lam) * t) := by
  have hq := angularLag_abs_bound v.core v.h_pos.le hh1 v.core.holdStart_pos.le hη
  have heq := equilibrium_bounds v hh1 hη
  have hc := holdCoefficient_bounds v.core v.h_pos.le hh1 hη
  have hcabs : |holdCoefficient v.core v.h η| ≤ 4 := by simpa only [abs_of_nonneg hc.1] using hc.2
  have heqabs : |equilibrium v.core v.h η| ≤ 1 := by simpa only [abs_of_nonneg heq.1] using heq.2
  have hcoef : |angularLag v.core v.h η v.core.holdStart - equilibrium v.core v.h η -
      holdCoefficient v.core v.h η| ≤ 15 := by
    have hb := (abs_sub (angularLag v.core v.h η v.core.holdStart - equilibrium v.core v.h η)
      (holdCoefficient v.core v.h η)).trans (add_le_add_left (abs_sub _ _) _)
    linarith
  have hex : Real.exp (-t) ≤ Real.exp (-(1 - v.core.lam) * t) :=
    Real.exp_le_exp.mpr (by linarith [mul_nonneg v.core.lam_pos.le ht])
  rw [angularLag_hold_formula v.core v.h η ht]
  have hf : holdFormula v.core v.h η t - equilibrium v.core v.h η =
      (angularLag v.core v.h η v.core.holdStart - equilibrium v.core v.h η - holdCoefficient v.core
          v.h η) *
        Real.exp (-(1 - v.core.lam) * t) + holdCoefficient v.core v.h η * Real.exp (-t) := by
    unfold holdFormula
    ring
  rw [hf]
  calc
    _ ≤ |(angularLag v.core v.h η v.core.holdStart - equilibrium v.core v.h η - holdCoefficient
        v.core v.h η) *
        Real.exp (-(1 - v.core.lam) * t)| + |holdCoefficient v.core v.h η * Real.exp (-t)| :=
            abs_add_le _ _
    _ ≤ 15 * Real.exp (-(1 - v.core.lam) * t) + 4 * Real.exp (-(1 - v.core.lam) * t) := by
      simp only [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact add_le_add (mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le)
        (mul_le_mul hcabs hex (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 4))
    _ = _ := by ring

theorem canonical_Qs_pulseStart_error {v : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness v K) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp)
    (hh1 : v.h ≤ 1 / 100) {η : ℝ} (hη : |η| ≤ 1) :
    |OutgoingHistories.Qs w Amp (v.core.pulseStart, η) - equilibrium v.core v.h η| ≤
      19 * Real.exp (-(1 - v.core.lam) * v.core.wait) := by
  rw [canonical_Qs_before w ha v.core.pulseStart_pos.le le_rfl]
  exact angularLag_hold_error v hh1 hη (by linarith [v.core.wait_gt])

/-- Wait for power, given by `-(n : ℝ) * Real.log c.lam / (1 - c.lam)`. -/
noncomputable def waitForPower (c : Parameters) (n : ℕ) : ℝ :=
  -(n : ℝ) * Real.log c.lam / (1 - c.lam)

theorem decay_le_power (c : Parameters) (n : ℕ) (ht : waitForPower c n ≤ c.wait) :
    Real.exp (-(1 - c.lam) * c.wait) ≤ c.lam ^ n := by
  have hmul := (div_le_iff₀ (hold_rate_pos c)).mp ht
  calc
    _ ≤ Real.exp ((n : ℝ) * Real.log c.lam) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [Real.exp_nat_mul, Real.exp_log c.lam_pos]

theorem canonical_Qs_pulseStart_power_error {v : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness v K) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp)
    (hh1 : v.h ≤ 1 / 100) {η : ℝ} (hη : |η| ≤ 1) (n : ℕ)
    (hwait : waitForPower v.core n ≤ v.core.wait) :
    |OutgoingHistories.Qs w Amp (v.core.pulseStart, η) - equilibrium v.core v.h η| ≤
      19 * v.core.lam ^ n :=
  (canonical_Qs_pulseStart_error w ha hh1 hη).trans
    (mul_le_mul_of_nonneg_left (decay_le_power v.core n hwait) (by norm_num))

/-! ## The positive shaped-hold floor -/

/-- Hold floor, given by `min (coneFloor * Real.exp (-entranceTime m) / 4) (1 / 16)`. -/
noncomputable def holdFloor (m : ℝ) : ℝ :=
  min (coneFloor * Real.exp (-entranceTime m) / 4) (1 / 16)

theorem holdFloor_pos (m : ℝ) : 0 < holdFloor m := by
  unfold holdFloor
  exact lt_min (by have := coneFloor_pos; positivity) (by norm_num)

theorem holdFloor_bounds (m : ℝ) : holdFloor m ≤ coneFloor ∧ holdFloor m ≤ 1 / 16 ∧
    4 * holdFloor m ≤ coneFloor * Real.exp (-entranceTime m) := by
  have hb : holdFloor m ≤ coneFloor * Real.exp (-entranceTime m) / 4 := min_le_left _ _
  have he : Real.exp (-entranceTime m) ≤ 1 := Real.exp_le_one_iff.mpr (by
    unfold entranceTime
    have := Real.exp_pos m
    linarith)
  have hc := coneFloor_pos
  refine ⟨?_, min_le_right _ _, by linarith⟩
  linarith [mul_le_mul_of_nonneg_left he hc.le]

theorem holdSource_lower (v : TailData) {η t : ℝ} (hh1 : v.h ≤ 1 / 100)
    (hhlam : v.h ≤ v.core.lam / 4) (hη : |η| ≤ 1) (ht : 0 ≤ t) :
    v.core.lam / 4 + (49 / 100) * η ^ 2 ≤ holdSource v.core v.h η t := by
  have hy : v.core.dropLength + 2 ≤ v.core.holdStart + t := by
    dsimp [Parameters.holdStart]
    linarith
  have hW := transportW_second_ramp v.core v.h_pos.le hh1 (y := v.core.holdStart + t) (by
      linarith) hη
  have hD : 49 / 100 ≤ D v.h := by unfold D; linarith
  have hJ := (eta_shapeGradient_bounds hη).1
  have hprod := mul_le_mul hD hJ (sq_nonneg η) (by linarith : 0 ≤ D v.h)
  rw [← angularSource_hold v.core v.h η ht, angularSource,
    slope_hold v.core.dropLength_pos.le hy, dropCoefficient_hold v.core ht]
  simp only [mul_zero, add_zero, neg_neg]
  linarith [mul_le_mul_of_nonneg_left hW v.core.lam_pos.le]

theorem holdFormula_eq_linearLag (c : Parameters) (h η t : ℝ) :
    holdFormula c h η t =
      linearLag (fun _ => 1 - c.lam) (holdSource c h η) (angularLag c h η c.holdStart) t := by
  apply linearLag_eq_of_solution continuous_const
    (continuous_const.sub (continuous_const.mul (Real.continuous_exp.comp continuous_neg)))
  · simp only [holdFormula, mul_zero, neg_zero, Real.exp_zero, mul_one]
    ring
  · intro u _
    exact holdFormula_hasDerivAt c h η u

theorem angularLag_hold_lower (v : TailData) {η t : ℝ} (hh1 : v.h ≤ 1 / 100)
    (hhlam : v.h ≤ v.core.lam / 4)
    (hhT : v.h ≤ Real.exp (-(v.core.holdStart + 3 / 5)) / 8)
    (hη : |η| ≤ 1) (ht : 0 ≤ t) :
    holdFloor v.core.m * (η ^ 2 + v.core.lam + Real.exp (-(1 - v.core.lam) * t)) ≤
      angularLag v.core v.h η (v.core.holdStart + t) := by
  have hc := holdFloor_pos v.core.m
  have hb := holdFloor_bounds v.core.m
  have hi := angularLag_lower v.core v.h_pos.le hh1 v.core.holdStart_pos.le le_rfl hη hhT
  have htime : 4 * holdFloor v.core.m ≤ coneFloor * Real.exp (-v.core.holdStart) := by
    simpa only [holdStart_eq_entranceTime] using hb.2.2
  have hinit : holdFloor v.core.m * (η ^ 2 + v.core.lam) + holdFloor v.core.m ≤
      angularLag v.core v.h η v.core.holdStart := by
    have hs := mul_le_mul_of_nonneg_right hb.1 (sq_nonneg η)
    have hl := mul_le_mul_of_nonneg_left v.core.lam_lt.le hc.le
    linarith
  have hsource : ∀ u ∈ Icc (0 : ℝ) t,
      (1 - v.core.lam) * (holdFloor v.core.m * (η ^ 2 + v.core.lam)) ≤ holdSource v.core v.h η u :=
          by
    intro u hu
    have hs := holdSource_lower v hh1 hhlam hη hu.1
    have hbase : holdFloor v.core.m * (η ^ 2 + v.core.lam) ≤
        v.core.lam / 4 + (49 / 100) * η ^ 2 := by
      have hbη := mul_le_mul_of_nonneg_right hb.2.1 (sq_nonneg η)
      have hbLam := mul_le_mul_of_nonneg_right hb.2.1 v.core.lam_pos.le
      linarith [sq_nonneg η, v.core.lam_pos]
    have hn : 0 ≤ holdFloor v.core.m * (η ^ 2 + v.core.lam) :=
      mul_nonneg hc.le (add_nonneg (sq_nonneg η) v.core.lam_pos.le)
    linarith [mul_nonneg v.core.lam_pos.le hn]
  have hlo := linearLag_lower_barrier continuous_const
    (continuous_const.sub (continuous_const.mul (Real.continuous_exp.comp continuous_neg)))
    ht hinit hsource
  rw [angularLag_hold_formula v.core v.h η ht, holdFormula_eq_linearLag]
  have hp : -OutgoingSchedule.primitive (fun _ : ℝ => 1 - v.core.lam) t = -(1 - v.core.lam) * t :=
      by
    simp only [OutgoingSchedule.primitive, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    ring
  rw [hp] at hlo
  convert! hlo using 1
  ring

/-! ## The axial source and its actual convolution on the hold -/

theorem pressureClock_contDiff (c : Parameters) : ContDiff ℝ ∞ (pressureClock c) :=
  contDiff_const.add (contDiff_const.mul (primitive_contDiff (clockEnergy_contDiff c)))

theorem entrancePressure_contDiff (v : TailData) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => entrancePressure v p.1 p.2) := by
  exact ((SchedulePressure.axisPressure_contDiff v).comp contDiff_snd).add
    (((shape_contDiff.comp contDiff_snd).pow 2).mul ((pressureClock_contDiff v.core).comp
        contDiff_fst))

theorem pressureGradient_contDiff (v : TailData) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => pressureGradient v p.1 p.2) := by
  exact ((contDiff_infty_iff_deriv.mp (SchedulePressure.axisPressure_contDiff v)).2.comp
      contDiff_snd).sub
    (((contDiff_const.mul (shapeGradient_contDiff.comp contDiff_snd)).mul
      ((shape_contDiff.comp contDiff_snd).pow 2)).mul ((pressureClock_contDiff v.core).comp
          contDiff_fst))

theorem pressureAxialSource_contDiff (v : TailData) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => pressureAxialSource v p.1 p.2) := by
  have hd : ContDiff ℝ ∞ (fun p : ℝ × ℝ => d p.2) := contDiff_const.sub (contDiff_snd.pow 2)
  exact ((hd.neg.mul (pressureGradient_contDiff v)).add
    (((contDiff_const.mul contDiff_snd).mul (entrancePressure_contDiff v)))).add
      (contDiff_snd.mul ((angular_contDiff v.core.P v.core.dropLength v.core.lam).pow 2))

theorem geometricAxialSource_hold (c : Parameters) (h η : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    geometricAxialSource c h (c.holdStart + t) η = 0 := by
  have hl : Real.exp c.m < c.holdStart + t := by
    dsimp [Parameters.holdStart, Parameters.dropLength]
    linarith
  simp [geometricAxialSource, dropCoefficient_hold c ht, dropCoefficient_deriv_late c.m_pos hl]

theorem axialLag_hold_history (v : TailData) (η : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    axialLag v (v.core.holdStart + t) η =
      historyAverage (fun u => pressureAxialSource v (v.core.holdStart + u) η)
        (axialLag v v.core.holdStart η) t := by
  unfold historyAverage
  apply linearLag_eq_of_solution (r := fun _ => 1)
    (f := fun u => axialLag v (v.core.holdStart + u) η) continuous_const
    ((pressureAxialSource_contDiff v).continuous.comp
      ((continuous_const.add continuous_id).prodMk continuous_const))
  · simp
  · intro u hu
    have hu0 := (uIcc_of_le ht ▸ hu).1
    have hd := (axialLag_hasDerivAt v (v.core.holdStart + u) η).comp u
      ((hasDerivAt_id u).const_add v.core.holdStart)
    simp only [Function.comp_def, mul_one, one_mul, axialSource,
      geometricAxialSource_hold v.core v.h η hu0, zero_add] at hd ⊢
    exact hd

theorem historyAverage_abs_bound {b : ℝ → ℝ} {b₀ A B t : ℝ} (ht : 0 ≤ t)
    (hb₀ : |b₀| ≤ A) (hb : ∀ u ∈ Icc (0 : ℝ) t, |Real.exp u * b u| ≤ B) :
    |historyAverage b b₀ t| ≤ Real.exp (-t) * (A + t * B) := by
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := t)
    (f := fun u => Real.exp u * b u) (C := B) (fun u hu => by
      rw [Real.norm_eq_abs]
      have hu' : u ∈ Icc (0 : ℝ) t := ⟨(show 0 < u from (uIoc_of_le ht ▸ hu).1).le,
        (uIoc_of_le ht ▸ hu).2⟩
      exact hb u hu')
  simp only [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht] at hi
  rw [historyAverage_formula, abs_mul, abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  exact (abs_add_le _ _).trans (by linarith)

theorem angular_hold (c : Parameters) (η : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    angular c.P c.dropLength c.lam (c.holdStart + t, η) =
      angular c.P c.dropLength c.lam (c.holdStart, η) * Real.exp (-(1 / 2 + c.lam) * t) := by
  unfold angular
  rw [radialAmplitude_hold c.dropLength_pos.le (show c.dropLength + 2 ≤ c.holdStart by rfl)
    (show c.holdStart ≤ c.holdStart + t by linarith)]
  simp only [add_sub_cancel_left]
  ring

theorem weighted_angular_square_hold (c : Parameters) (η : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp t * angular c.P c.dropLength c.lam (c.holdStart + t, η) ^ 2 =
      angular c.P c.dropLength c.lam (c.holdStart, η) ^ 2 * Real.exp (-2 * c.lam * t) := by
  rw [angular_hold c η ht, mul_pow, ← Real.exp_nat_mul]
  have he : -2 * c.lam * t = t + 2 * (-(1 / 2 + c.lam) * t) := by ring
  rw [he, Real.exp_add]
  norm_num
  ring

/-- Initial energy lower, given by `P * Real.exp (-entranceTime m) / 2`. -/
noncomputable def initialEnergyLower (P m : ℝ) : ℝ := P * Real.exp (-entranceTime m) / 2
/-- Initial energy upper, given by `P * Real.exp (entranceTime m)`. -/
noncomputable def initialEnergyUpper (P m : ℝ) : ℝ := P * Real.exp (entranceTime m)
/-- Initial axial bound, given by `64 + (3 + 4 * pressureBound) * energyEnvelope P (entranceTime
m)`. -/
noncomputable def initialAxialBound (P m : ℝ) : ℝ :=
  64 + (3 + 4 * pressureBound) * energyEnvelope P (entranceTime m)
/-- Axial wait constant, given by `initialAxialBound P m / initialEnergyLower P m +
pressureSourceBound * initialEnergyUpper P m`. -/
noncomputable def axialWaitConstant (P m : ℝ) : ℝ :=
  initialAxialBound P m / initialEnergyLower P m + pressureSourceBound * initialEnergyUpper P m

theorem initialEnergyLower_pos {P : ℝ} (hP : 0 < P) (m : ℝ) : 0 < initialEnergyLower P m := by
  unfold initialEnergyLower
  positivity

theorem initialEnergyUpper_pos {P : ℝ} (hP : 0 < P) (m : ℝ) : 0 < initialEnergyUpper P m := by
  unfold initialEnergyUpper
  positivity

theorem initialAxialBound_pos (P m : ℝ) : 0 < initialAxialBound P m := by
  unfold initialAxialBound energyEnvelope
  have := pressureBound_pos
  positivity

theorem axialWaitConstant_pos {P : ℝ} (hP : 0 < P) (m : ℝ) : 0 < axialWaitConstant P m := by
  unfold axialWaitConstant
  exact add_pos (div_pos (initialAxialBound_pos _ _) (initialEnergyLower_pos hP _))
    (mul_pos pressureSourceBound_pos (initialEnergyUpper_pos hP _))

theorem angular_hold_start_bounds (c : Parameters) {η : ℝ} (hη : |η| ≤ 1) :
    initialEnergyLower c.P c.m ≤ angular c.P c.dropLength c.lam (c.holdStart, η) ∧
      angular c.P c.dropLength c.lam (c.holdStart, η) ≤ initialEnergyUpper c.P c.m := by
  have hlo := angular_lower_envelope c c.holdStart_pos.le le_rfl hη
  refine ⟨?_, ?_⟩
  · simpa only [initialEnergyLower, holdStart_eq_entranceTime] using hlo
  · have hi := (OutgoingPulseBounds.radialAmplitude_bounds c c.holdStart_pos.le).2
    have hs := (shape_interval hη).2
    have hp := mul_le_mul hi hs (shape_pos η).le (mul_pos c.P_pos (Real.exp_pos _)).le
    simpa only [angular, initialEnergyUpper, holdStart_eq_entranceTime, mul_one] using hp

theorem axialLag_hold_start_bound (v : TailData) {η : ℝ} (hh1 : v.h ≤ 1 / 100) (hη : |η| ≤ 1) :
    |axialLag v v.core.holdStart η| ≤ initialAxialBound v.core.P v.core.m * |η| := by
  have hend : v.core.holdStart ≤ v.core.endpoint := by
    have := v.core.pulseStart_ge_hold
    dsimp [Parameters.endpoint]
    linarith [v.core.pulseLength_pos]
  have hg := geometricAxialLag_bound v.core v.h_pos.le hh1 v.core.holdStart_pos.le hη
  have hp := pressureAxialLag_le_envelope v hh1 v.core.holdStart_pos.le le_rfl hend hη
  unfold axialLag
  have hs := (abs_add_le (geometricAxialLag v.core v.h v.core.holdStart η)
    (pressureAxialLag v v.core.holdStart η)).trans (add_le_add hg hp)
  convert! hs using 1
  unfold initialAxialBound
  rw [holdStart_eq_entranceTime]
  ring

theorem weighted_pressure_source_bound (v : TailData) {η t : ℝ}
    (hh1 : v.h ≤ 1 / 100) (hη : |η| ≤ 1) (ht : 0 ≤ t) (htw : t ≤ v.core.wait) :
    |Real.exp t * pressureAxialSource v (v.core.holdStart + t) η| ≤
      pressureSourceBound * |η| * angular v.core.P v.core.dropLength v.core.lam (v.core.holdStart,
          η) ^ 2 := by
  have hy : 0 ≤ v.core.holdStart + t := by linarith [v.core.holdStart_pos]
  have hend : v.core.holdStart + t ≤ v.core.endpoint := by
    dsimp [Parameters.endpoint, Parameters.pulseStart]
    linarith [v.core.pulseLength_pos]
  have hb := pressureAxialSource_bound v hh1 hy hend hη
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp t * (pressureSourceBound * |η| *
        angular v.core.P v.core.dropLength v.core.lam (v.core.holdStart + t, η) ^ 2) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = (pressureSourceBound * |η|) *
        (Real.exp t * angular v.core.P v.core.dropLength v.core.lam (v.core.holdStart + t, η) ^ 2)
            := by
            ring
    _ = _ * (angular v.core.P v.core.dropLength v.core.lam (v.core.holdStart, η) ^ 2 *
        Real.exp (-2 * v.core.lam * t)) := by rw [weighted_angular_square_hold v.core η ht]
    _ ≤ _ := by
      have he : Real.exp (-2 * v.core.lam * t) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by linarith [mul_nonneg v.core.lam_pos.le ht])
      have hp := mul_le_mul_of_nonneg_left he
        (show 0 ≤ pressureSourceBound * |η| * angular v.core.P v.core.dropLength v.core.lam
            (v.core.holdStart, η) ^ 2 by
          have := pressureSourceBound_pos
          positivity)
      linarith

theorem axialLag_hold_bound (v : TailData) {η t : ℝ}
    (hh1 : v.h ≤ 1 / 100) (hη : |η| ≤ 1) (ht : 0 ≤ t) (htw : t ≤ v.core.wait) :
    |axialLag v (v.core.holdStart + t) η| ≤ Real.exp (-t) *
      (initialAxialBound v.core.P v.core.m * |η| + t *
        (pressureSourceBound * |η| * angular v.core.P v.core.dropLength v.core.lam
            (v.core.holdStart, η) ^ 2)) := by
  rw [axialLag_hold_history v η ht]
  apply historyAverage_abs_bound ht (axialLag_hold_start_bound v hh1 hη)
  intro u hu
  exact weighted_pressure_source_bound v hh1 hη hu.1 (hu.2.trans htw)

theorem axialLag_hold_ratio_bound (v : TailData) {η t : ℝ}
    (hh1 : v.h ≤ 1 / 100) (hη : |η| ≤ 1) (ht : 0 ≤ t) (htw : t ≤ v.core.wait) :
    |axialLag v (v.core.holdStart + t) η /
      angular v.core.P v.core.dropLength v.core.lam (v.core.holdStart + t, η)| ≤
      axialWaitConstant v.core.P v.core.m * |η| * (1 + t) * Real.exp (-(1 / 2 - v.core.lam) * t) :=
          by
  let E₀ := angular v.core.P v.core.dropLength v.core.lam (v.core.holdStart, η)
  have hE₀ : 0 < E₀ := angular_pos v.core.P_pos _ _ _
  have hE := angular_hold_start_bounds v.core hη
  have hEmin := initialEnergyLower_pos v.core.P_pos v.core.m
  have hA := initialAxialBound_pos v.core.P v.core.m
  have hC := pressureSourceBound_pos
  have hCb := axialWaitConstant_pos v.core.P_pos v.core.m
  have hfirst : initialAxialBound v.core.P v.core.m ≤
      (initialAxialBound v.core.P v.core.m / initialEnergyLower v.core.P v.core.m) * E₀ := by
    have hp := mul_le_mul_of_nonneg_left hE.1 (div_pos hA hEmin).le
    simpa only [div_mul_cancel₀ _ hEmin.ne'] using hp
  have hsecond : pressureSourceBound * E₀ ^ 2 ≤
      (pressureSourceBound * initialEnergyUpper v.core.P v.core.m) * E₀ := by
    have hp := mul_le_mul_of_nonneg_right hE.2 (mul_pos hC hE₀).le
    linarith
  have hinside : initialAxialBound v.core.P v.core.m + t * (pressureSourceBound * E₀ ^ 2) ≤
      axialWaitConstant v.core.P v.core.m * (1 + t) * E₀ := by
    have hm := mul_le_mul_of_nonneg_left hsecond ht
    have hc1 := div_pos hA hEmin
    have hc2 := mul_pos hC (initialEnergyUpper_pos v.core.P_pos v.core.m)
    unfold axialWaitConstant
    nlinarith [mul_nonneg ht hc1.le, mul_nonneg ht hc2.le, mul_pos hc2 hE₀]
  have hN := axialLag_hold_bound v hh1 hη ht htw
  have hex : Real.exp (-(1 / 2 - v.core.lam) * t) * Real.exp (-(1 / 2 + v.core.lam) * t) =
      Real.exp (-t) := by rw [← Real.exp_add]; congr 1; ring
  rw [abs_div, abs_of_pos (angular_pos v.core.P_pos _ _ _)]
  apply (div_le_iff₀ (angular_pos v.core.P_pos _ _ _)).mpr
  apply hN.trans
  rw [angular_hold v.core η ht]
  change Real.exp (-t) * (_ + _) ≤
    axialWaitConstant v.core.P v.core.m * |η| * (1 + t) *
      Real.exp (-(1 / 2 - v.core.lam) * t) * (E₀ * Real.exp (-(1 / 2 + v.core.lam) * t))
  have hm := mul_le_mul_of_nonneg_left hinside (mul_nonneg (Real.exp_pos (-t)).le (abs_nonneg η))
  calc
    _ ≤ Real.exp (-t) * |η| * (axialWaitConstant v.core.P v.core.m * (1 + t) * E₀) := by
      convert! hm using 1
      ring
    _ = _ := by rw [← hex]; ring

theorem canonical_Ns_hold_ratio_bound {v : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness v K) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp)
    {η t : ℝ} (hh1 : v.h ≤ 1 / 100) (hη : |η| ≤ 1) (ht : 0 ≤ t) (htw : t ≤ v.core.wait) :
    |OutgoingHistories.Ns w Amp (v.core.holdStart + t, η) /
      OutgoingHistories.E w (v.core.holdStart + t, η)| ≤
      axialWaitConstant v.core.P v.core.m * |η| * (1 + t) * Real.exp (-(1 / 2 - v.core.lam) * t) :=
          by
  have hpulse : v.core.holdStart + t ≤ v.core.pulseStart := by
    dsimp [Parameters.pulseStart]
    linarith
  have hend : v.core.holdStart + t ≤ v.core.endpoint := by
    dsimp [Parameters.endpoint]
    linarith [v.core.pulseLength_pos]
  rw [canonical_Ns_before w ha hpulse, OutgoingHistories.E_before w η hend]
  exact axialLag_hold_ratio_bound v hh1 hη ht htw

/-! ## Differentiating the genuine parameter-dependent histories -/

theorem linearLag_hasDerivAt_parameter {r : ℝ → ℝ} {b : ℝ × ℝ → ℝ}
    (hr : ContDiff ℝ ∞ r) (hb : ContDiff ℝ ∞ b) {q₀ : ℝ → ℝ} {q₀' η : ℝ}
    (hq : HasDerivAt q₀ q₀' η) (y : ℝ) :
    HasDerivAt (fun θ => linearLag r (fun t => b (t, θ)) (q₀ θ) y)
      (linearLag r (fun t => OutgoingHistories.dEta b (t, η)) q₀' y) η := by
  let F : ℝ × ℝ → ℝ := fun p => Real.exp (OutgoingSchedule.primitive r p.1) * b p
  have hF : ContDiff ℝ ∞ F :=
    (((primitive_contDiff hr).comp contDiff_fst).exp).mul hb
  have hFI : ContDiff ℝ ∞ (ProfileHistories.primitive F) :=
    contDiffOn_univ.mp (ProfileHistories.primitive_smooth OutgoingHistories.logDomain hF.contDiffOn)
  have hi := OutgoingHistories.dEta_hasDerivAt hFI (y, η)
  change HasDerivAt (fun θ => ProfileHistories.primitive F (y, θ))
    (ProfileHistories.parameterPartial (ProfileHistories.primitive F) (y, η)) η at hi
  rw [ProfileHistories.parameterPartial_primitive OutgoingHistories.logDomain hF.contDiffOn
      (mem_univ _)] at hi
  have hFd (t : ℝ) : OutgoingHistories.dEta F (t, η) =
      Real.exp (OutgoingSchedule.primitive r t) * OutgoingHistories.dEta b (t, η) := by
    exact (OutgoingHistories.dEta_hasDerivAt hF (t, η)).unique
      ((OutgoingHistories.dEta_hasDerivAt hb (t, η)).const_mul (Real.exp
          (OutgoingSchedule.primitive r t)))
  have hI : ProfileHistories.primitive (ProfileHistories.parameterPartial F) (y, η) =
      ∫ t in (0 : ℝ)..y, Real.exp (OutgoingSchedule.primitive r t) * OutgoingHistories.dEta b (t,
          η) := by
    exact intervalIntegral.integral_congr (fun t _ => hFd t)
  rw [hI] at hi
  simpa only [linearLag, OutgoingSchedule.primitive, ProfileHistories.primitive, F] using
    (hq.fun_add hi).const_mul (Real.exp (-OutgoingSchedule.primitive r y))

theorem shapeGradient_hasDerivAt (η : ℝ) :
    HasDerivAt shapeGradient (2 * (1 - η ^ 2) / (1 + η ^ 2) ^ 2) η := by
  have hn : 1 + η ^ 2 ≠ 0 := by positivity
  convert! ((hasDerivAt_id η).const_mul 2).div
    ((hasDerivAt_const η (1 : ℝ)).fun_add ((hasDerivAt_id η).fun_pow 2)) hn using 1
  simp only [id_eq]
  ring

theorem shapeGradient_deriv_bound {η : ℝ} (hη : |η| ≤ 1) : |deriv shapeGradient η| ≤ 2 := by
  rw [(shapeGradient_hasDerivAt η).deriv]
  have hsq := parameter_square_le_one hη
  have hd : 0 < (1 + η ^ 2) ^ 2 := by positivity
  rw [abs_of_nonneg (div_nonneg (by linarith) hd.le)]
  apply (div_le_iff₀ hd).mpr
  linarith [sq_nonneg η, sq_nonneg (η ^ 2)]

/-- Angular source eta as an element of `ℝ`. -/
noncomputable def angularSourceEta (c : Parameters) (h η y : ℝ) : ℝ :=
  -4 * h * slope c.dropLength c.lam y * η * averagedDrop c y +
    4 * h * dropCoefficient c.m y * η -
      2 * dropCoefficient c.m y * η ^ 2 * shapeGradient η +
        (D h + d η * dropCoefficient c.m y) * (shapeGradient η + η * deriv shapeGradient η)

theorem angularSource_hasDerivAt_eta (c : Parameters) (h y η : ℝ) :
    HasDerivAt (fun θ => angularSource c h θ y) (angularSourceEta c h η y) η := by
  have hd : HasDerivAt d (-2 * η) η := by
    convert! (hasDerivAt_const η (1 : ℝ)).fun_sub ((hasDerivAt_id η).fun_pow 2) using 1
    simp []
  have hW : HasDerivAt (fun θ => transportW c h y θ) (4 * h * η * averagedDrop c y) η := by
    convert! ((((hasDerivAt_id η).fun_pow 2).const_mul (2 * h)).const_sub 1).mul_const
      (averagedDrop c y) |>.const_sub 1 using 1
    simp only [id_eq]
    ring
  have hJ := (shapeGradient_contDiff.differentiable (by simp) η).hasDerivAt
  have hmiddle := (((hasDerivAt_id η).fun_pow 2).const_mul (2 * dropCoefficient c.m y)).const_sub 1
  have hlast := ((((hd.mul_const (dropCoefficient c.m y)).const_add (D h)).fun_mul (hasDerivAt_id
      η)).fun_mul hJ)
  convert! (((hW.const_mul (-slope c.dropLength c.lam y)).fun_sub (hmiddle.const_mul h)).fun_add
      hlast) using 1
  simp only [angularSourceEta, id_eq]
  ring

theorem angularSource_joint_contDiff (c : Parameters) (h : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => angularSource c h p.2 p.1) := by
  have hk := (dropCoefficient_contDiff c.m_pos).comp (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : ℝ × ℝ
      → ℝ))
  have hkbar := (averagedDrop_contDiff c).comp (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : ℝ × ℝ → ℝ))
  have hL : ContDiff ℝ ∞ (fun p : ℝ × ℝ => L h p.2) := contDiff_const.sub (contDiff_const.mul
      (contDiff_snd.pow 2))
  have hd : ContDiff ℝ ∞ (fun p : ℝ × ℝ => d p.2) := contDiff_const.sub (contDiff_snd.pow 2)
  have hW : ContDiff ℝ ∞ (fun p : ℝ × ℝ => transportW c h p.1 p.2) :=
    contDiff_const.sub (hL.mul hkbar)
  exact ((((slope_contDiff c.dropLength c.lam).comp contDiff_fst).neg.mul hW).sub
    (contDiff_const.mul (contDiff_const.sub ((contDiff_const.mul hk).mul (contDiff_snd.pow
        2))))).add
      ((((contDiff_const.add (hd.mul hk)).mul contDiff_snd).mul (shapeGradient_contDiff.comp
          contDiff_snd)))

theorem angularSourceEta_eq_dEta (c : Parameters) (h y η : ℝ) :
    OutgoingHistories.dEta (fun p => angularSource c h p.2 p.1) (y, η) = angularSourceEta c h η y :=
  (OutgoingHistories.dEta_hasDerivAt (angularSource_joint_contDiff c h) (y, η)).unique
    (angularSource_hasDerivAt_eta c h y η)

theorem angularSourceEta_abs_bound (c : Parameters) {h y η : ℝ} (hh : 0 ≤ h)
    (hh1 : h ≤ 1 / 100) (hy : 0 ≤ y) (hη : |η| ≤ 1) : |angularSourceEta c h η y| ≤ 100 := by
  have hr := angularRate_bounds c y
  have hl : |slope c.dropLength c.lam y| ≤ 1 := by
    unfold angularRate at hr
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hhabs : |h| ≤ 1 := by rw [abs_of_nonneg hh]; linarith
  have hk := dropCoefficient_bounds c.m y
  have hkabs : |dropCoefficient c.m y| ≤ 4 := by simpa only [abs_of_nonneg hk.1] using hk.2
  have hb := averagedDrop_bounds c hy
  have hbabs : |averagedDrop c y| ≤ 4 := by simpa only [abs_of_nonneg hb.1] using hb.2
  have hsq := parameter_square_le_one hη
  have hJ : |shapeGradient η| ≤ 2 := (abs_shapeGradient_le η).trans (by linarith)
  have hJ' := shapeGradient_deriv_bound hη
  have hd : 0 ≤ d η ∧ d η ≤ 1 := by unfold d; constructor <;> linarith [sq_nonneg η]
  have hbase : |D h + d η * dropCoefficient c.m y| ≤ 5 := by
    have hmul := mul_le_mul hd.2 hk.2 hk.1 (by norm_num : (0 : ℝ) ≤ 1)
    have hn := mul_nonneg hd.1 hk.1
    unfold D
    apply abs_le.mpr
    constructor <;> linarith
  have hfirst : |-4 * h * slope c.dropLength c.lam y * η * averagedDrop c y| ≤ 16 := by
    calc
      _ = 4 * |h| * |slope c.dropLength c.lam y| * |η| * |averagedDrop c y| := by
          simp only [abs_mul]; norm_num
      _ ≤ 4 * 1 * 1 * 1 * 4 := by gcongr
      _ = _ := by norm_num
  have hsecond : |4 * h * dropCoefficient c.m y * η| ≤ 16 := by
    calc
      _ = 4 * |h| * |dropCoefficient c.m y| * |η| := by simp only [abs_mul]; norm_num
      _ ≤ 4 * 1 * 4 * 1 := by gcongr
      _ = _ := by norm_num
  have hthird : |2 * dropCoefficient c.m y * η ^ 2 * shapeGradient η| ≤ 16 := by
    calc
      _ = 2 * |dropCoefficient c.m y| * η ^ 2 * |shapeGradient η| := by
          simp only [abs_mul, abs_pow, sq_abs]; norm_num
      _ ≤ 2 * 4 * 1 * 2 := by gcongr
      _ = _ := by norm_num
  have hjoint : |shapeGradient η + η * deriv shapeGradient η| ≤ 4 := by
    have hm : |η * deriv shapeGradient η| ≤ 2 := by
      rw [abs_mul]
      exact (mul_le_mul hη hJ' (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (by ring)
    exact (abs_add_le _ _).trans (by linarith)
  have hfourth : |(D h + d η * dropCoefficient c.m y) * (shapeGradient η + η * deriv shapeGradient
      η)| ≤ 20 := by
    rw [abs_mul]
    exact (mul_le_mul hbase hjoint (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 5)).trans_eq (by ring)
  unfold angularSourceEta
  have hs : |-4 * h * slope c.dropLength c.lam y * η * averagedDrop c y +
      4 * h * dropCoefficient c.m y * η - 2 * dropCoefficient c.m y * η ^ 2 * shapeGradient η +
        (D h + d η * dropCoefficient c.m y) * (shapeGradient η + η * deriv shapeGradient η)| ≤
      |-4 * h * slope c.dropLength c.lam y * η * averagedDrop c y| +
        |4 * h * dropCoefficient c.m y * η| + |2 * dropCoefficient c.m y * η ^ 2 * shapeGradient η|
            +
          |(D h + d η * dropCoefficient c.m y) * (shapeGradient η + η * deriv shapeGradient η)| :=
    (abs_add_le _ _).trans (add_le_add_left ((abs_sub _ _).trans (add_le_add_left (abs_add_le _ _)
        _)) _)
  linarith

theorem idealAngularLag_hasDerivAt (c : Parameters) (h η : ℝ) :
    HasDerivAt (idealAngularLag h) (angularSourceEta c h η 0 / (8 / 5)) η := by
  have he : idealAngularLag h = fun θ => angularSource c h θ 0 / (8 / 5) := by
    funext θ
    rw [angularSource_ideal c h θ le_rfl]
    rfl
  rw [he]
  exact (angularSource_hasDerivAt_eta c h 0 η).div_const (8 / 5)

theorem angularLag_hasDerivAt_eta (c : Parameters) (h η y : ℝ) :
    HasDerivAt (fun θ => angularLag c h θ y)
      (linearLag (angularRate c) (angularSourceEta c h η) (angularSourceEta c h η 0 / (8 / 5)) y) η
          := by
  have hd := linearLag_hasDerivAt_parameter (angularRate_contDiff c) (angularSource_joint_contDiff
      c h)
    (idealAngularLag_hasDerivAt c h η) y
  simp_rw [angularSourceEta_eq_dEta] at hd
  exact hd

theorem angularLag_deriv_eta_bound (c : Parameters) {h y η : ℝ} (hh : 0 ≤ h)
    (hh1 : h ≤ 1 / 100) (hy : 0 ≤ y) (hη : |η| ≤ 1) :
    |deriv (fun θ => angularLag c h θ y) η| ≤ 200 := by
  rw [(angularLag_hasDerivAt_eta c h η y).deriv]
  have hc : Continuous (angularSourceEta c h η) := by
    have hcont : Continuous (fun t => OutgoingHistories.dEta (fun p => angularSource c h p.2 p.1)
        (t, η)) :=
      (OutgoingHistories.dEta_smooth (angularSource_joint_contDiff c h)).continuous.comp
      (continuous_id.prodMk continuous_const)
    exact hcont.congr (fun t => angularSourceEta_eq_dEta c h t η)
  apply linearLag_abs_le (angularRate_contDiff c).continuous hc hy
  · have hi := angularSourceEta_abs_bound c hh hh1 (show (0 : ℝ) ≤ 0 by rfl) hη
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 8 / 5)]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 8 / 5)).mpr
    linarith
  · intro t ht
    have hs := angularSourceEta_abs_bound c hh hh1 ht.1 hη
    have hr := (angularRate_bounds c t).1
    linarith

theorem equilibrium_hasDerivAt (c : Parameters) (h η : ℝ) :
    HasDerivAt (equilibrium c h)
      (D h * (shapeGradient η + η * deriv shapeGradient η) / (1 - c.lam)) η := by
  have hj := (shapeGradient_contDiff.differentiable (by simp) η).hasDerivAt
  convert! ((((hasDerivAt_id η).const_mul (D h)).mul hj).const_add (c.lam - h)).div_const (1 -
      c.lam) using 1
  simp only [id_eq]
  ring

theorem equilibrium_deriv_bound (v : TailData) {η : ℝ} (hh1 : v.h ≤ 1 / 100) (hη : |η| ≤ 1) :
    |deriv (equilibrium v.core v.h) η| ≤ 4 := by
  rw [(equilibrium_hasDerivAt v.core v.h η).deriv, abs_div,
    abs_of_pos (hold_rate_pos v.core), abs_mul]
  have hD : |D v.h| ≤ 1 / 2 := by
    unfold D
    apply abs_le.mpr
    constructor <;> linarith [v.h_pos]
  have hJ : |shapeGradient η| ≤ 2 := (abs_shapeGradient_le η).trans (by linarith)
  have hJ' := shapeGradient_deriv_bound hη
  have hm := mul_le_mul hη hJ' (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hsum : |shapeGradient η + η * deriv shapeGradient η| ≤ 4 := by
    have htri := abs_add_le (shapeGradient η) (η * deriv shapeGradient η)
    rw [abs_mul] at htri
    linarith
  have hprod := mul_le_mul hD hsum (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  apply (div_le_iff₀ (hold_rate_pos v.core)).mpr
  linarith [v.core.lam_lt]

theorem holdCoefficient_hasDerivAt (c : Parameters) (h η : ℝ) :
    HasDerivAt (holdCoefficient c h) (-4 * h * η * averagedDrop c c.holdStart) η := by
  convert! ((((hasDerivAt_id η).pow 2).const_mul (2 * h)).const_sub 1).mul_const
    (averagedDrop c c.holdStart) using 1
  simp only [id_eq]
  ring

theorem holdCoefficient_deriv_bound (c : Parameters) {h η : ℝ} (hh : 0 ≤ h)
    (hh1 : h ≤ 1 / 100) (hη : |η| ≤ 1) : |deriv (holdCoefficient c h) η| ≤ 1 := by
  rw [(holdCoefficient_hasDerivAt c h η).deriv]
  have hb := averagedDrop_bounds c c.holdStart_pos.le
  have hb₀ := hb.1
  have hb₁ := hb.2
  calc
    _ = 4 * h * |η| * averagedDrop c c.holdStart := by
      simp only [abs_mul, abs_of_nonneg hh, abs_of_nonneg hb.1]
      norm_num
    _ ≤ 4 * (1 / 100) * 1 * 4 := by gcongr
    _ ≤ _ := by norm_num

theorem angularLag_hold_deriv_error (v : TailData) {η t : ℝ}
    (hh1 : v.h ≤ 1 / 100) (hη : |η| ≤ 1) (ht : 0 ≤ t) :
    |deriv (fun θ => angularLag v.core v.h θ (v.core.holdStart + t) - equilibrium v.core v.h θ) η| ≤
      206 * Real.exp (-(1 - v.core.lam) * t) := by
  have hq := angularLag_deriv_eta_bound v.core v.h_pos.le hh1 v.core.holdStart_pos.le hη
  have heq := equilibrium_deriv_bound v hh1 hη
  have hc := holdCoefficient_deriv_bound v.core v.h_pos.le hh1 hη
  have hf : (fun θ => angularLag v.core v.h θ (v.core.holdStart + t) - equilibrium v.core v.h θ) =
      fun θ => (angularLag v.core v.h θ v.core.holdStart - equilibrium v.core v.h θ -
          holdCoefficient v.core v.h θ) *
        Real.exp (-(1 - v.core.lam) * t) + holdCoefficient v.core v.h θ * Real.exp (-t) := by
    funext θ
    rw [angularLag_hold_formula v.core v.h θ ht]
    unfold holdFormula
    ring
  have hdq := (angularLag_hasDerivAt_eta v.core v.h η v.core.holdStart).differentiableAt.hasDerivAt
  have hde := (equilibrium_hasDerivAt v.core v.h η).differentiableAt.hasDerivAt
  have hdc := (holdCoefficient_hasDerivAt v.core v.h η).differentiableAt.hasDerivAt
  have hd := ((((hdq.fun_sub hde).fun_sub hdc).mul_const (Real.exp (-(1 - v.core.lam) * t))).fun_add
    (hdc.mul_const (Real.exp (-t))))
  rw [hf, hd.deriv]
  have hb : |deriv (fun θ => angularLag v.core v.h θ v.core.holdStart) η -
      deriv (equilibrium v.core v.h) η - deriv (holdCoefficient v.core v.h) η| ≤ 205 := by
    have htri := (abs_sub (deriv (fun θ => angularLag v.core v.h θ v.core.holdStart) η -
      deriv (equilibrium v.core v.h) η) (deriv (holdCoefficient v.core v.h) η)).trans
      (add_le_add_left (abs_sub _ _) _)
    linarith
  have hex : Real.exp (-t) ≤ Real.exp (-(1 - v.core.lam) * t) :=
    Real.exp_le_exp.mpr (by linarith [mul_nonneg v.core.lam_pos.le ht])
  have htri := abs_add_le
    ((deriv (fun θ => angularLag v.core v.h θ v.core.holdStart) η - deriv (equilibrium v.core v.h)
        η -
      deriv (holdCoefficient v.core v.h) η) * Real.exp (-(1 - v.core.lam) * t))
    (deriv (holdCoefficient v.core v.h) η * Real.exp (-t))
  simp only [abs_mul, abs_of_pos (Real.exp_pos _)] at htri
  have hfirst := mul_le_mul_of_nonneg_right hb (Real.exp_pos (-(1 - v.core.lam) * t)).le
  have hsecond := mul_le_mul hc hex (Real.exp_pos (-t)).le (by norm_num : (0 : ℝ) ≤ 1)
  linarith

/-! ## The axial parameter derivative at the beginning of the hold -/

/-- Initial axial derivative as an element of `ℝ`. -/
noncomputable def initialAxialDerivative (v : TailData) (η : ℝ) : ℝ :=
  (12 * v.h * η ^ 2 + 6 * η ^ 2 - 2) * averagedDropSquare v.core v.core.holdStart -
    (2 * v.h - 2 * η * shapeGradient η + d η * deriv shapeGradient η) * averagedEnergy v.core
        v.core.holdStart η +
      2 * (2 * v.h * η + d η * shapeGradient η) * shapeGradient η * averagedEnergy v.core
          v.core.holdStart η +
        4 * A v.h * entrancePressure v v.core.holdStart η +
          (4 * A v.h + 2) * η * pressureGradient v v.core.holdStart η -
            d η * deriv (pressureGradient v v.core.holdStart) η

/-- Initial axial derivative bound, given by `256 + (32 + 16 * pressureBound) * energyEnvelope P
(entranceTime m)`. -/
noncomputable def initialAxialDerivativeBound (P m : ℝ) : ℝ :=
  256 + (32 + 16 * pressureBound) * energyEnvelope P (entranceTime m)

theorem initialAxialDerivativeBound_pos (P m : ℝ) : 0 < initialAxialDerivativeBound P m := by
  unfold initialAxialDerivativeBound energyEnvelope
  have := pressureBound_pos
  positivity

theorem initialAxial_hasDerivAt (v : TailData) (η : ℝ) :
    HasDerivAt (fun θ => axialLag v v.core.holdStart θ) (initialAxialDerivative v η) η := by
  have hk : dropCoefficient v.core.m v.core.holdStart = 0 := by
    simpa only [add_zero] using dropCoefficient_hold v.core (t := 0) le_rfl
  have hf : (fun θ => axialLag v v.core.holdStart θ) = fun θ =>
      (4 * v.h * θ ^ 3 - 2 * d θ * θ) * averagedDropSquare v.core v.core.holdStart -
        (2 * v.h * θ + d θ * shapeGradient θ) * averagedEnergy v.core v.core.holdStart θ +
          4 * A v.h * θ * entrancePressure v v.core.holdStart θ -
            d θ * pressureGradient v v.core.holdStart θ := by
    funext θ
    simp only [axialLag, geometricAxialLag, pressureAxialLag, hk, mul_zero, zero_mul, zero_add]
    ring
  have hd : HasDerivAt d (-2 * η) η := by
    convert! (hasDerivAt_const η (1 : ℝ)).fun_sub ((hasDerivAt_id η).fun_pow 2) using 1
    simp []
  have hj := (shapeGradient_contDiff.differentiable (by simp) η).hasDerivAt
  have hcoef := ((hasDerivAt_id η).const_mul (2 * v.h)).fun_add (hd.fun_mul hj)
  have hg := ((((hasDerivAt_id η).fun_pow 3).const_mul (4 * v.h)).fun_sub
    ((hd.fun_mul (hasDerivAt_id η)).const_mul 2)).mul_const (averagedDropSquare v.core
        v.core.holdStart)
  have hgrad := ((pressureGradient_contDiff_eta v v.core.holdStart).differentiable (by
      simp) η).hasDerivAt
  rw [hf]
  convert! (((hg.fun_sub (hcoef.fun_mul (averagedEnergy_hasDerivAt_eta v.core v.core.holdStart
      η))).fun_add
    (((hasDerivAt_id η).const_mul (4 * A v.h)).fun_mul (entrancePressure_hasDerivAt_eta v
        v.core.holdStart η))).fun_sub
      (hd.fun_mul hgrad)) using 1
  · funext θ
    simp only [id_eq]
    ring
  · simp only [initialAxialDerivative, id_eq, d]
    norm_num
    ring

theorem initialAxialDerivative_bound (v : TailData) {η : ℝ}
    (hh1 : v.h ≤ 1 / 100) (hη : |η| ≤ 1) :
    |initialAxialDerivative v η| ≤ initialAxialDerivativeBound v.core.P v.core.m := by
  have htime := v.core.holdStart_pos.le
  have hend : v.core.holdStart ≤ v.core.endpoint := by
    have := v.core.pulseStart_ge_hold
    dsimp [Parameters.endpoint]
    linarith [v.core.pulseLength_pos]
  have hP := actual_pressure_bounds v htime hend hη
  have hE := angular_square_le_envelope v.core htime le_rfl hη
  have hbar := averagedEnergy_le_envelope v.core htime le_rfl hη
  have hbar0 : 0 ≤ averagedEnergy v.core v.core.holdStart η :=
    mul_nonneg (sq_nonneg _) (averagedClockEnergy_nonneg v.core htime)
  have hK := averagedDropSquare_bounds v.core htime
  have hEnv : 0 ≤ energyEnvelope v.core.P v.core.holdStart := by unfold energyEnvelope; positivity
  have hp0 : |entrancePressure v v.core.holdStart η| ≤ pressureBound * energyEnvelope v.core.P
      v.core.holdStart :=
    hP.1.trans (mul_le_mul_of_nonneg_left hE pressureBound_pos.le)
  have hp1 : |pressureGradient v v.core.holdStart η| ≤ pressureBound * energyEnvelope v.core.P
      v.core.holdStart := by
    have he := mul_le_mul_of_nonneg_left hE (mul_nonneg pressureBound_pos.le (abs_nonneg η))
    have hh := mul_le_mul_of_nonneg_left hη (mul_nonneg pressureBound_pos.le hEnv)
    linarith [hP.2.1]
  have hp2 : |deriv (pressureGradient v v.core.holdStart) η| ≤ pressureBound * energyEnvelope
      v.core.P v.core.holdStart :=
    hP.2.2.trans (mul_le_mul_of_nonneg_left hE pressureBound_pos.le)
  have hsq := parameter_square_le_one hη
  have hd : 0 ≤ d η ∧ d η ≤ 1 := by unfold d; constructor <;> linarith [sq_nonneg η]
  have hA : 0 ≤ 4 * A v.h ∧ 4 * A v.h ≤ 3 := by unfold A; constructor <;> linarith [v.h_pos]
  have hJ : |shapeGradient η| ≤ 2 := (abs_shapeGradient_le η).trans (by linarith)
  have hJ' := shapeGradient_deriv_bound hη
  have hC : |2 * v.h * η + d η * shapeGradient η| ≤ 3 :=
    (pressure_coefficient_bound v.h_pos.le hh1 hη).trans (by linarith)
  have hCp : |2 * v.h - 2 * η * shapeGradient η + d η * deriv shapeGradient η| ≤ 10 := by
    have hfirst : |2 * v.h| ≤ 2 := by
        rw [abs_of_nonneg (by linarith [v.h_pos] : 0 ≤ 2 * v.h)]; linarith
    have hsecond : |2 * η * shapeGradient η| ≤ 4 := by
      calc
        _ = 2 * |η| * |shapeGradient η| := by simp only [abs_mul]; norm_num
        _ ≤ 2 * 1 * 2 := by gcongr
        _ = _ := by norm_num
    have hthird : |d η * deriv shapeGradient η| ≤ 2 := by
      rw [abs_mul, abs_of_nonneg hd.1]
      exact (mul_le_mul hd.2 hJ' (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (by ring)
    have htri := (abs_add_le (2 * v.h - 2 * η * shapeGradient η) (d η * deriv shapeGradient
        η)).trans
      (add_le_add_left (abs_sub _ _) _)
    linarith
  have hg : |(12 * v.h * η ^ 2 + 6 * η ^ 2 - 2) * averagedDropSquare v.core v.core.holdStart| ≤ 256
      := by
    have hc : |12 * v.h * η ^ 2 + 6 * η ^ 2 - 2| ≤ 16 := by
      have hh := mul_le_mul hh1 hsq (sq_nonneg η) (by norm_num : (0 : ℝ) ≤ 1 / 100)
      have hh0 := mul_nonneg v.h_pos.le (sq_nonneg η)
      apply abs_le.mpr
      constructor <;> linarith [sq_nonneg η]
    rw [abs_mul, abs_of_nonneg hK.1]
    exact (mul_le_mul hc hK.2 hK.1 (by norm_num : (0 : ℝ) ≤ 16)).trans_eq (by norm_num)
  have h1 : |(2 * v.h - 2 * η * shapeGradient η + d η * deriv shapeGradient η) *
      averagedEnergy v.core v.core.holdStart η| ≤ 10 * energyEnvelope v.core.P v.core.holdStart :=
          by
    rw [abs_mul, abs_of_nonneg hbar0]
    exact mul_le_mul hCp hbar hbar0 (by norm_num)
  have h2 : |2 * (2 * v.h * η + d η * shapeGradient η) * shapeGradient η *
      averagedEnergy v.core v.core.holdStart η| ≤ 12 * energyEnvelope v.core.P v.core.holdStart :=
          by
    rw [abs_mul, abs_of_nonneg hbar0]
    have hc : |2 * (2 * v.h * η + d η * shapeGradient η) * shapeGradient η| ≤ 12 := by
      calc
        _ = 2 * |2 * v.h * η + d η * shapeGradient η| * |shapeGradient η| := by
            simp only [abs_mul]; norm_num
        _ ≤ 2 * 3 * 2 := by gcongr
        _ = _ := by norm_num
    exact mul_le_mul hc hbar hbar0 (by norm_num)
  have h3 : |4 * A v.h * entrancePressure v v.core.holdStart η| ≤
      3 * pressureBound * energyEnvelope v.core.P v.core.holdStart := by
    rw [abs_mul, abs_of_nonneg hA.1]
    have hm := mul_le_mul hA.2 hp0 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 3)
    linarith
  have h4 : |(4 * A v.h + 2) * η * pressureGradient v v.core.holdStart η| ≤
      5 * pressureBound * energyEnvelope v.core.P v.core.holdStart := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 4 * A v.h + 2)]
    have hc : (4 * A v.h + 2) * |η| ≤ 5 := by
      have hm := mul_le_mul_of_nonneg_left hη (by linarith : 0 ≤ 4 * A v.h + 2)
      linarith
    have hm := mul_le_mul hc hp1 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 5)
    linarith
  have h5 : |d η * deriv (pressureGradient v v.core.holdStart) η| ≤
      pressureBound * energyEnvelope v.core.P v.core.holdStart := by
    rw [abs_mul, abs_of_nonneg hd.1]
    exact (mul_le_mul hd.2 hp2 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul _)
  have hsum : |initialAxialDerivative v η| ≤
      |(12 * v.h * η ^ 2 + 6 * η ^ 2 - 2) * averagedDropSquare v.core v.core.holdStart| +
        |(2 * v.h - 2 * η * shapeGradient η + d η * deriv shapeGradient η) * averagedEnergy v.core
            v.core.holdStart η| +
          |2 * (2 * v.h * η + d η * shapeGradient η) * shapeGradient η * averagedEnergy v.core
              v.core.holdStart η| +
            |4 * A v.h * entrancePressure v v.core.holdStart η| +
              |(4 * A v.h + 2) * η * pressureGradient v v.core.holdStart η| +
                |d η * deriv (pressureGradient v v.core.holdStart) η| := by
    exact (abs_sub _ _).trans (add_le_add_left ((abs_add_le _ _).trans (add_le_add_left
      ((abs_add_le _ _).trans (add_le_add_left ((abs_add_le _ _).trans (add_le_add_left (abs_sub _
          _) _)) _)) _)) _)
  unfold initialAxialDerivativeBound
  rw [← holdStart_eq_entranceTime v.core]
  linarith [mul_nonneg pressureBound_pos.le hEnv]

theorem weighted_bound_of_angular_square (c : Parameters) (η : ℝ) {t B z : ℝ}
    (ht : 0 ≤ t) (hB : 0 ≤ B)
    (hz : |z| ≤ B * angular c.P c.dropLength c.lam (c.holdStart + t, η) ^ 2) :
    |Real.exp t * z| ≤ B * angular c.P c.dropLength c.lam (c.holdStart, η) ^ 2 := by
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have he : Real.exp (-2 * c.lam * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith [mul_nonneg c.lam_pos.le ht])
  calc
    _ ≤ B * (Real.exp t * angular c.P c.dropLength c.lam (c.holdStart + t, η) ^ 2) := by
      linarith [mul_le_mul_of_nonneg_left hz (Real.exp_pos t).le]
    _ = B * (angular c.P c.dropLength c.lam (c.holdStart, η) ^ 2 * Real.exp (-2 * c.lam * t)) := by
      rw [weighted_angular_square_hold c η ht]
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_left he
        (mul_nonneg hB (sq_nonneg (angular c.P c.dropLength c.lam (c.holdStart, η))))
      linarith

theorem axialLag_hold_hasDerivAt_eta (v : TailData) (η : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun θ => axialLag v (v.core.holdStart + t) θ)
      (historyAverage (fun u => deriv (pressureAxialSource v (v.core.holdStart + u)) η)
        (initialAxialDerivative v η) t) η := by
  let b : ℝ × ℝ → ℝ := fun p => pressureAxialSource v (v.core.holdStart + p.1) p.2
  have hb : ContDiff ℝ ∞ b := (pressureAxialSource_contDiff v).comp
    ((contDiff_const.add contDiff_fst).prodMk contDiff_snd)
  have hd := linearLag_hasDerivAt_parameter (r := fun _ => (1 : ℝ)) contDiff_const hb
    (initialAxial_hasDerivAt v η) t
  have hg : (fun u => OutgoingHistories.dEta b (u, η)) =
      fun u => deriv (pressureAxialSource v (v.core.holdStart + u)) η := by
    funext u
    exact OutgoingHistories.dEta_eq_deriv hb (u, η)
  rw [hg] at hd
  have hf : (fun θ => axialLag v (v.core.holdStart + t) θ) =
      fun θ => linearLag (fun _ => (1 : ℝ)) (fun u => b (u, θ)) (axialLag v v.core.holdStart θ) t
          := by
    funext θ
    exact axialLag_hold_history v θ ht
  rw [hf]
  exact hd

theorem axialLag_hold_deriv_bound (v : TailData) {η t : ℝ}
    (hh1 : v.h ≤ 1 / 100) (hη : |η| ≤ 1) (ht : 0 ≤ t) (htw : t ≤ v.core.wait) :
    |deriv (fun θ => axialLag v (v.core.holdStart + t) θ) η| ≤ Real.exp (-t) *
      (initialAxialDerivativeBound v.core.P v.core.m + t *
        (pressureSourceBound * angular v.core.P v.core.dropLength v.core.lam (v.core.holdStart, η)
            ^ 2)) := by
  rw [(axialLag_hold_hasDerivAt_eta v η ht).deriv]
  apply historyAverage_abs_bound ht (initialAxialDerivative_bound v hh1 hη)
  intro u hu
  apply weighted_bound_of_angular_square v.core η hu.1 pressureSourceBound_pos.le
  apply pressureAxialSource_deriv_bound v hh1 _ _ hη
  · linarith [v.core.holdStart_pos, hu.1]
  · dsimp [Parameters.endpoint, Parameters.pulseStart]
    linarith [v.core.pulseLength_pos, hu.2]

theorem normalize_hold_bound (c : Parameters) {η t A z : ℝ} (hη : |η| ≤ 1)
    (ht : 0 ≤ t) (hA : 0 ≤ A)
    (hz : |z| ≤ Real.exp (-t) * (A + t *
      (pressureSourceBound * angular c.P c.dropLength c.lam (c.holdStart, η) ^ 2))) :
    |z / angular c.P c.dropLength c.lam (c.holdStart + t, η)| ≤
      (A / initialEnergyLower c.P c.m + pressureSourceBound * initialEnergyUpper c.P c.m) *
        (1 + t) * Real.exp (-(1 / 2 - c.lam) * t) := by
  let E₀ := angular c.P c.dropLength c.lam (c.holdStart, η)
  have hE₀ : 0 < E₀ := angular_pos c.P_pos _ _ _
  have hE := angular_hold_start_bounds c hη
  have hEmin := initialEnergyLower_pos c.P_pos c.m
  have hC := pressureSourceBound_pos
  have hfirst : A ≤ (A / initialEnergyLower c.P c.m) * E₀ := by
    have hp := mul_le_mul_of_nonneg_left hE.1 (div_nonneg hA hEmin.le)
    simpa only [div_mul_cancel₀ _ hEmin.ne'] using hp
  have hsecond : pressureSourceBound * E₀ ^ 2 ≤
      (pressureSourceBound * initialEnergyUpper c.P c.m) * E₀ := by
    have hp := mul_le_mul_of_nonneg_right hE.2 (mul_pos hC hE₀).le
    linarith
  have hinside : A + t * (pressureSourceBound * E₀ ^ 2) ≤
      (A / initialEnergyLower c.P c.m + pressureSourceBound * initialEnergyUpper c.P c.m) * (1 + t)
          * E₀ := by
    have hm := mul_le_mul_of_nonneg_left hsecond ht
    have hc1 := div_nonneg hA hEmin.le
    have hc2 := mul_pos hC (initialEnergyUpper_pos c.P_pos c.m)
    linarith [mul_nonneg (mul_nonneg ht hc1) hE₀.le, mul_pos hc2 hE₀]
  have hex : Real.exp (-(1 / 2 - c.lam) * t) * Real.exp (-(1 / 2 + c.lam) * t) = Real.exp (-t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [abs_div, abs_of_pos (angular_pos c.P_pos _ _ _)]
  apply (div_le_iff₀ (angular_pos c.P_pos _ _ _)).mpr
  apply hz.trans
  rw [angular_hold c η ht]
  have hm := mul_le_mul_of_nonneg_left hinside (Real.exp_pos (-t)).le
  change Real.exp (-t) * (A + t * (pressureSourceBound * E₀ ^ 2)) ≤ _ at hm
  calc
    _ ≤ Real.exp (-t) *
        ((A / initialEnergyLower c.P c.m + pressureSourceBound * initialEnergyUpper c.P c.m) * (1 +
            t) * E₀) := hm
    _ = _ := by rw [← hex]; ring

/-- Axial derivative wait constant, given by `initialAxialDerivativeBound P m /
initialEnergyLower P m + pressureSourceBound * initialEnergyUpper P m`. -/
noncomputable def axialDerivativeWaitConstant (P m : ℝ) : ℝ :=
  initialAxialDerivativeBound P m / initialEnergyLower P m + pressureSourceBound *
      initialEnergyUpper P m

/-- Axial ratio derivative wait constant, given by `axialDerivativeWaitConstant P m + 2 *
axialWaitConstant P m`. -/
noncomputable def axialRatioDerivativeWaitConstant (P m : ℝ) : ℝ :=
  axialDerivativeWaitConstant P m + 2 * axialWaitConstant P m

theorem axialDerivativeWaitConstant_pos {P : ℝ} (hP : 0 < P) (m : ℝ) :
    0 < axialDerivativeWaitConstant P m := by
  exact add_pos (div_pos (initialAxialDerivativeBound_pos _ _) (initialEnergyLower_pos hP _))
    (mul_pos pressureSourceBound_pos (initialEnergyUpper_pos hP _))

theorem axialRatioDerivativeWaitConstant_pos {P : ℝ} (hP : 0 < P) (m : ℝ) :
    0 < axialRatioDerivativeWaitConstant P m := by
  exact add_pos (axialDerivativeWaitConstant_pos hP _)
    (mul_pos (by norm_num) (axialWaitConstant_pos hP _))

theorem axialLag_hold_deriv_ratio_bound (v : TailData) {η t : ℝ}
    (hh1 : v.h ≤ 1 / 100) (hη : |η| ≤ 1) (ht : 0 ≤ t) (htw : t ≤ v.core.wait) :
    |deriv (fun θ => axialLag v (v.core.holdStart + t) θ) η /
      angular v.core.P v.core.dropLength v.core.lam (v.core.holdStart + t, η)| ≤
      axialDerivativeWaitConstant v.core.P v.core.m * (1 + t) * Real.exp (-(1 / 2 - v.core.lam) *
          t) :=
  normalize_hold_bound v.core hη ht (initialAxialDerivativeBound_pos _ _).le
    (axialLag_hold_deriv_bound v hh1 hη ht htw)

theorem normalizedAxial_hasDerivAt (v : TailData) (η : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun θ => axialLag v (v.core.holdStart + t) θ /
      angular v.core.P v.core.dropLength v.core.lam (v.core.holdStart + t, θ))
      (deriv (fun θ => axialLag v (v.core.holdStart + t) θ) η /
        angular v.core.P v.core.dropLength v.core.lam (v.core.holdStart + t, η) +
          shapeGradient η * (axialLag v (v.core.holdStart + t) η /
            angular v.core.P v.core.dropLength v.core.lam (v.core.holdStart + t, η))) η := by
  have hN := (axialLag_hold_hasDerivAt_eta v η ht).differentiableAt.hasDerivAt
  have hE : HasDerivAt (fun θ => angular v.core.P v.core.dropLength v.core.lam (v.core.holdStart +
      t, θ))
      (-shapeGradient η * angular v.core.P v.core.dropLength v.core.lam (v.core.holdStart + t, η))
          η := by
    convert! (OutgoingEntranceCone.shape_hasDerivAt η).const_mul
      (radialAmplitude v.core.P v.core.dropLength v.core.lam (v.core.holdStart + t)) using 1
    simp only [angular]
    ring
  have hpos := angular_pos v.core.P_pos v.core.dropLength v.core.lam (v.core.holdStart + t, η)
  convert! hN.div hE hpos.ne' using 1
  field_simp [hpos.ne']; ring

theorem axialLag_hold_ratio_deriv_bound (v : TailData) {η t : ℝ}
    (hh1 : v.h ≤ 1 / 100) (hη : |η| ≤ 1) (ht : 0 ≤ t) (htw : t ≤ v.core.wait) :
    |deriv (fun θ => axialLag v (v.core.holdStart + t) θ /
      angular v.core.P v.core.dropLength v.core.lam (v.core.holdStart + t, θ)) η| ≤
      axialRatioDerivativeWaitConstant v.core.P v.core.m * (1 + t) * Real.exp (-(1 / 2 -
          v.core.lam) * t) := by
  rw [(normalizedAxial_hasDerivAt v η ht).deriv]
  have hD := axialLag_hold_deriv_ratio_bound v hh1 hη ht htw
  have hN := axialLag_hold_ratio_bound v hh1 hη ht htw
  have hC := axialWaitConstant_pos v.core.P_pos v.core.m
  have hpol : 0 ≤ (1 + t) * Real.exp (-(1 / 2 - v.core.lam) * t) := by positivity
  have hN' : |axialLag v (v.core.holdStart + t) η /
      angular v.core.P v.core.dropLength v.core.lam (v.core.holdStart + t, η)| ≤
      axialWaitConstant v.core.P v.core.m * (1 + t) * Real.exp (-(1 / 2 - v.core.lam) * t) := by
    have hm := mul_le_mul_of_nonneg_left hη (mul_nonneg hC.le hpol)
    linarith
  have hJ : |shapeGradient η| ≤ 2 := (abs_shapeGradient_le η).trans (by linarith)
  have hm := mul_le_mul hJ hN' (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  have htri := abs_add_le
    (deriv (fun θ => axialLag v (v.core.holdStart + t) θ) η /
      angular v.core.P v.core.dropLength v.core.lam (v.core.holdStart + t, η))
    (shapeGradient η * (axialLag v (v.core.holdStart + t) η /
      angular v.core.P v.core.dropLength v.core.lam (v.core.holdStart + t, η)))
  rw [abs_mul] at htri
  unfold axialRatioDerivativeWaitConstant
  linarith

theorem canonical_Ns_hold_ratio_deriv_bound {v : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness v K) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp)
    {η t : ℝ} (hh1 : v.h ≤ 1 / 100) (hη : |η| ≤ 1) (ht : 0 ≤ t) (htw : t ≤ v.core.wait) :
    |deriv (fun θ => OutgoingHistories.Ns w Amp (v.core.holdStart + t, θ) /
      OutgoingHistories.E w (v.core.holdStart + t, θ)) η| ≤
      axialRatioDerivativeWaitConstant v.core.P v.core.m * (1 + t) * Real.exp (-(1 / 2 -
          v.core.lam) * t) := by
  have hpulse : v.core.holdStart + t ≤ v.core.pulseStart := by
    dsimp [Parameters.pulseStart]
    linarith
  have hend : v.core.holdStart + t ≤ v.core.endpoint := by
    dsimp [Parameters.endpoint]
    linarith [v.core.pulseLength_pos]
  have hf : (fun θ => OutgoingHistories.Ns w Amp (v.core.holdStart + t, θ) /
      OutgoingHistories.E w (v.core.holdStart + t, θ)) =
      fun θ => axialLag v (v.core.holdStart + t) θ /
        angular v.core.P v.core.dropLength v.core.lam (v.core.holdStart + t, θ) := by
    funext θ
    rw [canonical_Ns_before w ha hpulse, OutgoingHistories.E_before w θ hend]
  rw [hf]
  exact axialLag_hold_ratio_deriv_bound v hh1 hη ht htw

/-! ## Canonical combined statements and pulse-entry powers -/

theorem canonical_Qs_hold_lower {v : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness v K) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp)
    {η t : ℝ} (hh1 : v.h ≤ 1 / 100) (hhlam : v.h ≤ v.core.lam / 4)
    (hhT : v.h ≤ Real.exp (-(v.core.holdStart + 3 / 5)) / 8)
    (hη : |η| ≤ 1) (ht : 0 ≤ t) (htw : t ≤ v.core.wait) :
    holdFloor v.core.m * (η ^ 2 + v.core.lam + Real.exp (-(1 - v.core.lam) * t)) ≤
      OutgoingHistories.Qs w Amp (v.core.holdStart + t, η) := by
  have hpulse : v.core.holdStart + t ≤ v.core.pulseStart := by
    dsimp [Parameters.pulseStart]
    linarith
  rw [canonical_Qs_before w ha (by linarith [v.core.holdStart_pos]) hpulse]
  exact angularLag_hold_lower v hh1 hhlam hhT hη ht

theorem canonical_Qs_hold_error {v : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness v K) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp)
    {η t : ℝ} (hh1 : v.h ≤ 1 / 100) (hη : |η| ≤ 1) (ht : 0 ≤ t) (htw : t ≤ v.core.wait) :
    |OutgoingHistories.Qs w Amp (v.core.holdStart + t, η) - equilibrium v.core v.h η| ≤
      19 * Real.exp (-(1 - v.core.lam) * t) := by
  have hpulse : v.core.holdStart + t ≤ v.core.pulseStart := by
    dsimp [Parameters.pulseStart]
    linarith
  rw [canonical_Qs_before w ha (by linarith [v.core.holdStart_pos]) hpulse]
  exact angularLag_hold_error v hh1 hη ht

theorem canonical_Qs_hold_deriv_error {v : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness v K) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp)
    {η t : ℝ} (hh1 : v.h ≤ 1 / 100) (hη : |η| ≤ 1) (ht : 0 ≤ t) (htw : t ≤ v.core.wait) :
    |deriv (fun θ =>
        OutgoingHistories.Qs w Amp (v.core.holdStart + t, θ) - equilibrium v.core v.h θ) η| ≤
      206 * Real.exp (-(1 - v.core.lam) * t) := by
  have hpulse : v.core.holdStart + t ≤ v.core.pulseStart := by
    dsimp [Parameters.pulseStart]
    linarith
  have hf : (fun θ => OutgoingHistories.Qs w Amp (v.core.holdStart + t, θ) - equilibrium v.core v.h
      θ) =
      fun θ => angularLag v.core v.h θ (v.core.holdStart + t) - equilibrium v.core v.h θ := by
    funext θ
    rw [canonical_Qs_before w ha (by linarith [v.core.holdStart_pos]) hpulse]
  rw [hf]
  exact angularLag_hold_deriv_error v hh1 hη ht

/-- Hold constant, given by `206 + axialWaitConstant P m + axialRatioDerivativeWaitConstant P
m`. -/
noncomputable def holdConstant (P m : ℝ) : ℝ :=
  206 + axialWaitConstant P m + axialRatioDerivativeWaitConstant P m

theorem holdConstant_bounds {P : ℝ} (hP : 0 < P) (m : ℝ) :
    0 < holdConstant P m ∧ 206 ≤ holdConstant P m ∧
      axialWaitConstant P m ≤ holdConstant P m ∧ axialRatioDerivativeWaitConstant P m ≤
          holdConstant P m := by
  have h1 := axialWaitConstant_pos hP m
  have h2 := axialRatioDerivativeWaitConstant_pos hP m
  unfold holdConstant
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- The complete estimates (16), including the actual first parameter
derivatives, with one displayed constant depending only on the earlier `P,m`. -/
theorem canonical_hold_estimates {v : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness v K) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp)
    {η t : ℝ} (hh1 : v.h ≤ 1 / 100) (hhlam : v.h ≤ v.core.lam / 4)
    (hhT : v.h ≤ Real.exp (-(v.core.holdStart + 3 / 5)) / 8)
    (hη : |η| ≤ 1) (ht : 0 ≤ t) (htw : t ≤ v.core.wait) :
    holdFloor v.core.m * (η ^ 2 + v.core.lam + Real.exp (-(1 - v.core.lam) * t)) ≤
        OutgoingHistories.Qs w Amp (v.core.holdStart + t, η) ∧
      |OutgoingHistories.Qs w Amp (v.core.holdStart + t, η) - equilibrium v.core v.h η| ≤
        holdConstant v.core.P v.core.m * (1 + t) * Real.exp (-(1 - v.core.lam) * t) ∧
      |deriv (fun θ =>
          OutgoingHistories.Qs w Amp (v.core.holdStart + t, θ) - equilibrium v.core v.h θ) η| ≤
        holdConstant v.core.P v.core.m * (1 + t) * Real.exp (-(1 - v.core.lam) * t) ∧
      |OutgoingHistories.Ns w Amp (v.core.holdStart + t, η) / OutgoingHistories.E w
          (v.core.holdStart + t, η)| ≤
        holdConstant v.core.P v.core.m * |η| * (1 + t) * Real.exp (-(1 / 2 - v.core.lam) * t) ∧
      |deriv (fun θ => OutgoingHistories.Ns w Amp (v.core.holdStart + t, θ) /
        OutgoingHistories.E w (v.core.holdStart + t, θ)) η| ≤
          holdConstant v.core.P v.core.m * (1 + t) * Real.exp (-(1 / 2 - v.core.lam) * t) := by
  have hc := holdConstant_bounds v.core.P_pos v.core.m
  have hprod : 206 ≤ holdConstant v.core.P v.core.m * (1 + t) := by
    linarith [mul_nonneg hc.1.le ht]
  refine ⟨canonical_Qs_hold_lower w ha hh1 hhlam hhT hη ht htw, ?_, ?_, ?_, ?_⟩
  · exact (canonical_Qs_hold_error w ha hh1 hη ht htw).trans
      (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)
  · exact (canonical_Qs_hold_deriv_error w ha hh1 hη ht htw).trans
      (mul_le_mul_of_nonneg_right hprod (Real.exp_pos _).le)
  · apply (canonical_Ns_hold_ratio_bound w ha hh1 hη ht htw).trans
    gcongr
    exact hc.2.2.1
  · apply (canonical_Ns_hold_ratio_deriv_bound w ha hh1 hη ht htw).trans
    gcongr
    exact hc.2.2.2

theorem canonical_Qs_pulseStart_deriv_power_error {v : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness v K) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp)
    (hh1 : v.h ≤ 1 / 100) {η : ℝ} (hη : |η| ≤ 1) (n : ℕ)
    (hwait : waitForPower v.core n ≤ v.core.wait) :
    |deriv (fun θ =>
        OutgoingHistories.Qs w Amp (v.core.pulseStart, θ) - equilibrium v.core v.h θ) η| ≤
      206 * v.core.lam ^ n := by
  have ht : 0 ≤ v.core.wait := by linarith [v.core.wait_gt]
  exact (canonical_Qs_hold_deriv_error w ha hh1 hη ht le_rfl).trans
    (mul_le_mul_of_nonneg_left (decay_le_power v.core n hwait) (by norm_num))

/-- A logarithmic wait gives the claimed polynomial smallness of the axial
history, including its harmless linear factor, with no hidden `λ` constant. -/
theorem polynomial_decay_le_power (c : Parameters) (hlam : c.lam ≤ 1 / 120)
    (hwait : -60 * Real.log c.lam ≤ c.wait) :
    (1 + c.wait) * Real.exp (-(1 / 2 - c.lam) * c.wait) ≤ 120 * c.lam ^ 29 := by
  have ht : 0 ≤ c.wait := by linarith [c.wait_gt]
  have hlin : 1 + c.wait ≤ 120 * Real.exp (c.wait / 120) := by
    have he := Real.add_one_le_exp (c.wait / 120)
    linarith
  have hl := mul_le_mul_of_nonneg_right hlam ht
  have harg : c.wait / 120 + -(1 / 2 - c.lam) * c.wait ≤ 29 * Real.log c.lam := by
    linarith
  calc
    _ ≤ (120 * Real.exp (c.wait / 120)) * Real.exp (-(1 / 2 - c.lam) * c.wait) :=
      mul_le_mul_of_nonneg_right hlin (Real.exp_pos _).le
    _ = 120 * Real.exp (c.wait / 120 + -(1 / 2 - c.lam) * c.wait) := by rw [Real.exp_add]; ring
    _ ≤ 120 * Real.exp (29 * Real.log c.lam) := by gcongr
    _ = _ := by
      change 120 * Real.exp (((29 : ℕ) : ℝ) * Real.log c.lam) = 120 * c.lam ^ 29
      rw [Real.exp_nat_mul, Real.exp_log c.lam_pos]

theorem canonical_Ns_pulseStart_power_bounds {v : TailData} {K : ℝ}
    (w : UniformAngularReset.ResetWitness v K) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp)
    (hh1 : v.h ≤ 1 / 100) (hlam : v.core.lam ≤ 1 / 120)
    (hwait : -60 * Real.log v.core.lam ≤ v.core.wait) {η : ℝ} (hη : |η| ≤ 1) :
    |OutgoingHistories.Ns w Amp (v.core.pulseStart, η) / OutgoingHistories.E w (v.core.pulseStart,
        η)| ≤
        120 * axialWaitConstant v.core.P v.core.m * |η| * v.core.lam ^ 29 ∧
      |deriv (fun θ => OutgoingHistories.Ns w Amp (v.core.pulseStart, θ) /
        OutgoingHistories.E w (v.core.pulseStart, θ)) η| ≤
          120 * axialRatioDerivativeWaitConstant v.core.P v.core.m * v.core.lam ^ 29 := by
  have ht : 0 ≤ v.core.wait := by linarith [v.core.wait_gt]
  have hd := polynomial_decay_le_power v.core hlam hwait
  have hval := canonical_Ns_hold_ratio_bound w ha hh1 hη ht le_rfl
  have hder := canonical_Ns_hold_ratio_deriv_bound w ha hh1 hη ht le_rfl
  have hc := axialWaitConstant_pos v.core.P_pos v.core.m
  have hc' := axialRatioDerivativeWaitConstant_pos v.core.P_pos v.core.m
  constructor
  · have hm := mul_le_mul_of_nonneg_left hd (mul_nonneg hc.le (abs_nonneg η))
    change |OutgoingHistories.Ns w Amp (v.core.holdStart + v.core.wait, η) /
      OutgoingHistories.E w (v.core.holdStart + v.core.wait, η)| ≤ _
    linarith
  · have hm := mul_le_mul_of_nonneg_left hd hc'.le
    change |deriv (fun θ => OutgoingHistories.Ns w Amp (v.core.holdStart + v.core.wait, θ) /
      OutgoingHistories.E w (v.core.holdStart + v.core.wait, θ)) η| ≤ _
    linarith

end NavierStokes.ShapedWaitBounds
