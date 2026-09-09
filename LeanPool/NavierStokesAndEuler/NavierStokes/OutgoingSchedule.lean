/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.LocalizedMomentRepair
public import LeanPool.NavierStokesAndEuler.NavierStokes.FlatCutoff
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import LeanPool.NavierStokesAndEuler.NavierStokes.FlatPrimitive
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Constructed outgoing profiles through the axial pulse

The clock is the global logarithmic radius, with the first ramp starting at zero.
All functions below are actual formulas.  Stage inequalities are hypotheses on
real parameters, not assumptions that suitable profiles or corrections exist.
-/

@[expose] public section


noncomputable section

open Set Filter Function MeasureTheory
open scoped Topology ContDiff BigOperators

namespace NavierStokes.OutgoingSchedule

/-! ## The manuscript's smooth step -/

/-- Sigma, given by `FlatCutoff.edge 1 x / (FlatCutoff.edge 1 x + FlatCutoff.edge 1 (1 - x))`. -/
def sigma (x : ℝ) : ℝ :=
  FlatCutoff.edge 1 x / (FlatCutoff.edge 1 x + FlatCutoff.edge 1 (1 - x))

theorem sigma_denom_pos (x : ℝ) :
    0 < FlatCutoff.edge 1 x + FlatCutoff.edge 1 (1 - x) := by
  by_cases hx : 0 < x
  · exact add_pos_of_pos_of_nonneg (FlatCutoff.edge_pos 1 hx)
      (FlatCutoff.edge_nonneg 1 _)
  · exact add_pos_of_nonneg_of_pos (FlatCutoff.edge_nonneg 1 _)
      (FlatCutoff.edge_pos 1 (by linarith))

theorem sigma_contDiff : ContDiff ℝ ∞ sigma :=
  (FlatCutoff.edge_contDiff (by norm_num : (0 : ℝ) < 1)).div
    ((FlatCutoff.edge_contDiff (by norm_num : (0 : ℝ) < 1)).add
      ((FlatCutoff.edge_contDiff (by norm_num : (0 : ℝ) < 1)).comp
        (contDiff_const.sub contDiff_id)))
    (fun x => (sigma_denom_pos x).ne')

theorem sigma_zero {x : ℝ} (hx : x ≤ 0) : sigma x = 0 := by
  simp [sigma, FlatCutoff.edge_of_nonpos 1 hx]

theorem sigma_one {x : ℝ} (hx : 1 ≤ x) : sigma x = 1 := by
  unfold sigma
  rw [FlatCutoff.edge_of_nonpos 1 (by linarith : 1 - x ≤ 0), add_zero]
  exact div_self (FlatCutoff.edge_pos 1 (by linarith)).ne'

theorem sigma_nonneg (x : ℝ) : 0 ≤ sigma x :=
  div_nonneg (FlatCutoff.edge_nonneg 1 x) (sigma_denom_pos x).le

theorem sigma_le_one (x : ℝ) : sigma x ≤ 1 := by
  apply (div_le_one (sigma_denom_pos x)).mpr
  exact le_add_of_nonneg_right (FlatCutoff.edge_nonneg 1 _)

theorem edge_monotone : Monotone (FlatCutoff.edge 1) := by
  apply monotone_of_deriv_nonneg
    ((FlatCutoff.edge_contDiff (by norm_num : (0 : ℝ) < 1) :
      ContDiff ℝ ∞ _).differentiable (by simp))
  intro x
  rw [(FlatPrimitive.edge_hasDerivAt (by norm_num : (0 : ℝ) < 1) x).deriv]
  by_cases hx : 0 < x
  · exact div_nonneg (mul_nonneg (by norm_num) (FlatCutoff.edge_nonneg 1 x))
      (pow_nonneg hx.le 3)
  · simp [FlatCutoff.edge_of_nonpos 1 (le_of_not_gt hx)]

theorem sigma_monotone : Monotone sigma := by
  intro x y hxy
  apply (div_le_div_iff₀ (sigma_denom_pos x) (sigma_denom_pos y)).mpr
  have ha := edge_monotone hxy
  have hb := edge_monotone (show 1 - y ≤ 1 - x by linarith)
  have hcross := mul_le_mul ha hb (FlatCutoff.edge_nonneg 1 _) (FlatCutoff.edge_nonneg 1 _)
  nlinarith

/-! ## Smooth primitives and the single global slope -/

/-- Primitive, given by `∫ t in (0 : ℝ)..y, g t`. -/
def primitive (g : ℝ → ℝ) (y : ℝ) : ℝ := ∫ t in (0 : ℝ)..y, g t

theorem primitive_hasDerivAt {g : ℝ → ℝ} (hg : Continuous g) (y : ℝ) :
    HasDerivAt (primitive g) (g y) y :=
  intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 y)
    hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt

theorem primitive_contDiff {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (primitive g) := by
  apply contDiff_infty_iff_deriv.mpr
  constructor
  · exact fun y => (primitive_hasDerivAt hg.continuous y).differentiableAt
  · have hd : deriv (primitive g) = g := by
      funext y
      exact (primitive_hasDerivAt hg.continuous y).deriv
    rwa [hd]

theorem primitive_increment {g : ℝ → ℝ} (hg : Continuous g) (a b c : ℝ)
    (hc : ∀ t ∈ uIcc a b, g t = c) :
    primitive g b = primitive g a + (b - a) * c := by
  have hi : (∫ t in a..b, g t) = (b - a) * c := by
    calc
      _ = ∫ _t in a..b, c := intervalIntegral.integral_congr hc
      _ = _ := by simp
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hg.intervalIntegrable 0 a) (hg.intervalIntegrable a b)
  simpa only [primitive, hi] using h.symm

/-- Slope, given by `(3 / 5) * (1 - sigma y) - lam * sigma (y - (dropLength + 1))`. -/
def slope (dropLength lam y : ℝ) : ℝ :=
  (3 / 5) * (1 - sigma y) - lam * sigma (y - (dropLength + 1))

theorem slope_contDiff (dropLength lam : ℝ) : ContDiff ℝ ∞ (slope dropLength lam) :=
  (contDiff_const.mul (contDiff_const.sub sigma_contDiff)).sub
    (contDiff_const.mul (sigma_contDiff.comp (contDiff_id.sub contDiff_const)))

theorem slope_ideal {dropLength lam y : ℝ} (hd : 0 ≤ dropLength) (hy : y ≤ 0) :
    slope dropLength lam y = 3 / 5 := by
  simp [slope, sigma_zero hy, sigma_zero (by linarith : y - (dropLength + 1) ≤ 0)]

theorem slope_drop {dropLength lam y : ℝ} (hy : 1 ≤ y) (hy' : y ≤ dropLength + 1) :
    slope dropLength lam y = 0 := by
  simp [slope, sigma_one hy, sigma_zero (by linarith : y - (dropLength + 1) ≤ 0)]

theorem slope_hold {dropLength lam y : ℝ} (hd : 0 ≤ dropLength)
    (hy : dropLength + 2 ≤ y) : slope dropLength lam y = -lam := by
  simp [slope, sigma_one (by linarith : 1 ≤ y),
    sigma_one (by linarith : 1 ≤ y - (dropLength + 1))]

/-- Log amplitude, given by `primitive (fun y => slope dropLength lam y - 1 / 2)`. -/
def logAmplitude (dropLength lam : ℝ) : ℝ → ℝ :=
  primitive (fun y => slope dropLength lam y - 1 / 2)

/-- Radial amplitude, given by `P * Real.exp (logAmplitude dropLength lam y)`. -/
def radialAmplitude (P dropLength lam y : ℝ) : ℝ :=
  P * Real.exp (logAmplitude dropLength lam y)

/-- Shape, given by `(1 + eta ^ 2)⁻¹`. -/
def shape (eta : ℝ) : ℝ := (1 + eta ^ 2)⁻¹

/-- Angular, given by `radialAmplitude P dropLength lam p.1 * shape p.2`. -/
def angular (P dropLength lam : ℝ) (p : ℝ × ℝ) : ℝ :=
  radialAmplitude P dropLength lam p.1 * shape p.2

theorem logAmplitude_contDiff (dropLength lam : ℝ) :
    ContDiff ℝ ∞ (logAmplitude dropLength lam) :=
  primitive_contDiff ((slope_contDiff dropLength lam).sub contDiff_const)

theorem radialAmplitude_contDiff (P dropLength lam : ℝ) :
    ContDiff ℝ ∞ (radialAmplitude P dropLength lam) :=
  contDiff_const.mul (logAmplitude_contDiff dropLength lam).exp

theorem shape_pos (eta : ℝ) : 0 < shape eta := by
  unfold shape
  positivity

theorem shape_contDiff : ContDiff ℝ ∞ shape :=
  (contDiff_const.add (contDiff_id.pow 2)).inv (fun eta => by positivity)

theorem angular_contDiff (P dropLength lam : ℝ) :
    ContDiff ℝ ∞ (angular P dropLength lam) :=
  ((radialAmplitude_contDiff P dropLength lam).comp contDiff_fst).mul
    (shape_contDiff.comp contDiff_snd)

theorem angular_pos {P : ℝ} (hP : 0 < P) (dropLength lam : ℝ) (p : ℝ × ℝ) :
    0 < angular P dropLength lam p :=
  mul_pos (mul_pos hP (Real.exp_pos _)) (shape_pos _)

theorem radialAmplitude_hasDerivAt (P dropLength lam y : ℝ) :
    HasDerivAt (radialAmplitude P dropLength lam)
      (radialAmplitude P dropLength lam y * (slope dropLength lam y - 1 / 2)) y := by
  have h := ((primitive_hasDerivAt
    (g := fun y => slope dropLength lam y - 1 / 2)
    ((slope_contDiff dropLength lam).continuous.sub continuous_const) y).exp).const_mul P
  unfold radialAmplitude logAmplitude
  simpa only [mul_assoc] using h

theorem logAmplitude_ideal {dropLength lam y : ℝ} (hd : 0 ≤ dropLength) (hy : y ≤ 0) :
    logAmplitude dropLength lam y = y / 10 := by
  have h := primitive_increment
    (g := fun y => slope dropLength lam y - 1 / 2)
    ((slope_contDiff dropLength lam).continuous.sub continuous_const) 0 y (1 / 10) ?_
  · simpa [logAmplitude, primitive, div_eq_mul_inv] using h
  · intro t ht
    have ht0 : t ≤ 0 := (uIcc_of_ge hy ▸ ht).2
    rw [slope_ideal hd ht0]
    norm_num

theorem angular_ideal {dropLength lam y eta P : ℝ} (hd : 0 ≤ dropLength) (hy : y ≤ 0) :
    angular P dropLength lam (y, eta) = P * shape eta * Real.exp (y / 10) := by
  simp only [angular, radialAmplitude, logAmplitude_ideal hd hy]
  ring

theorem radialAmplitude_hold {dropLength lam a y P : ℝ} (hd : 0 ≤ dropLength)
    (ha : dropLength + 2 ≤ a) (hay : a ≤ y) :
    radialAmplitude P dropLength lam y =
      radialAmplitude P dropLength lam a * Real.exp (-(1 / 2 + lam) * (y - a)) := by
  have h := primitive_increment
    (g := fun y => slope dropLength lam y - 1 / 2)
    ((slope_contDiff dropLength lam).continuous.sub continuous_const) a y (-(1 / 2 + lam)) ?_
  · have he : logAmplitude dropLength lam y =
        logAmplitude dropLength lam a + -(1 / 2 + lam) * (y - a) := by
      simpa only [logAmplitude, mul_comm (y - a)] using h
    rw [radialAmplitude, he, Real.exp_add]
    simp only [radialAmplitude, mul_assoc]
  · intro t ht
    have hat : a ≤ t := (uIcc_of_le hay ▸ ht).1
    rw [slope_hold hd (ha.trans hat)]
    ring

/-! ## The logarithmically slow axial drop -/

/-- Drop coefficient, with branches according to `y ≤ 1`. -/
def dropCoefficient (m y : ℝ) : ℝ :=
  if y ≤ 1 then 4 else 4 * (1 - sigma (Real.log y / m))

theorem dropCoefficient_early (m : ℝ) {y : ℝ} (hy : y ≤ 1) :
    dropCoefficient m y = 4 := by simp [dropCoefficient, hy]

theorem dropCoefficient_eq {m y : ℝ} (hm : 0 < m) (hy : 0 < y) :
    dropCoefficient m y = 4 * (1 - sigma (Real.log y / m)) := by
  by_cases hy1 : y ≤ 1
  · have hs := sigma_zero (div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos hy.le hy1) hm.le)
    simp [dropCoefficient, hy1, hs]
  · simp [dropCoefficient, hy1]

theorem dropCoefficient_contDiff {m : ℝ} (hm : 0 < m) :
    ContDiff ℝ ∞ (dropCoefficient m) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y < 1
  · apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : ℝ => (4 : ℝ)) y).congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds hy] with t ht
    exact dropCoefficient_early m ht.le
  · have hy0 : 0 < y := by linarith
    have hf : ContDiffAt ℝ ∞ (fun t : ℝ => 4 * (1 - sigma (Real.log t / m))) y :=
      contDiffAt_const.mul (contDiffAt_const.sub
        (sigma_contDiff.contDiffAt.comp y ((Real.contDiffAt_log.mpr hy0.ne').div_const m)))
    apply hf.congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds hy0] with t ht
    exact dropCoefficient_eq hm ht

theorem dropCoefficient_late {m y : ℝ} (hm : 0 < m) (hy : Real.exp m ≤ y) :
    dropCoefficient m y = 0 := by
  have hy0 : 0 < y := (Real.exp_pos m).trans_le hy
  have hlog : m ≤ Real.log y := (Real.le_log_iff_exp_le hy0).mpr hy
  rw [dropCoefficient_eq hm hy0, sigma_one ((le_div_iff₀ hm).mpr (by simpa using hlog))]
  ring

theorem dropCoefficient_bounds (m y : ℝ) :
    0 ≤ dropCoefficient m y ∧ dropCoefficient m y ≤ 4 := by
  by_cases hy : y ≤ 1
  · simp [dropCoefficient, hy]
  · have hlo := sigma_nonneg (Real.log y / m)
    have hhi := sigma_le_one (Real.log y / m)
    simp only [dropCoefficient, ite_eq_right hy]
    constructor <;> linarith

/-- Initial axial, given by `dropCoefficient m p.1 * p.2`. -/
def initialAxial (m : ℝ) (p : ℝ × ℝ) : ℝ := dropCoefficient m p.1 * p.2

theorem initialAxial_contDiff {m : ℝ} (hm : 0 < m) :
    ContDiff ℝ ∞ (initialAxial m) :=
  ((dropCoefficient_contDiff hm).comp contDiff_fst).mul contDiff_snd

/-! ## The main pulse and fixed, separated repair intervals -/

/-- Pulse ramp, given by `primitive (fun z => sigma (50 * z))`. -/
def pulseRamp : ℝ → ℝ := primitive (fun z => sigma (50 * z))

/-- Main pulse, given by `pulseRamp z * (1 - sigma (z - 10))`. -/
def mainPulse (z : ℝ) : ℝ := pulseRamp z * (1 - sigma (z - 10))

theorem pulseRamp_contDiff : ContDiff ℝ ∞ pulseRamp :=
  primitive_contDiff (sigma_contDiff.comp (contDiff_const.mul contDiff_id))

theorem mainPulse_contDiff : ContDiff ℝ ∞ mainPulse :=
  pulseRamp_contDiff.mul (contDiff_const.sub
    (sigma_contDiff.comp (contDiff_id.sub contDiff_const)))

theorem pulseRamp_zero {z : ℝ} (hz : z ≤ 0) : pulseRamp z = 0 := by
  unfold pulseRamp primitive
  calc
    _ = ∫ _t in (0 : ℝ)..z, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      apply sigma_zero
      have ht0 : t ≤ 0 := (uIcc_of_ge hz ▸ ht).2
      linarith
    _ = 0 := by simp

theorem mainPulse_zero_left {z : ℝ} (hz : z ≤ 0) : mainPulse z = 0 := by
  simp [mainPulse, pulseRamp_zero hz]

theorem mainPulse_zero_right {z : ℝ} (hz : 11 ≤ z) : mainPulse z = 0 := by
  simp [mainPulse, sigma_one (by linarith : 1 ≤ z - 10)]

/-- Only finite real parameters and their elementary inequalities are input. -/
structure Parameters where
  /-- P of `Parameters`, of type `ℝ`. -/
  P : ℝ
  /-- M of `Parameters`, of type `ℝ`. -/
  m : ℝ
  /-- Lam of `Parameters`, of type `ℝ`. -/
  lam : ℝ
  /-- Wait of `Parameters`, of type `ℝ`. -/
  wait : ℝ
  P_pos : 0 < P
  m_pos : 0 < m
  lam_pos : 0 < lam
  lam_lt : lam < 1 / 10
  wait_gt : 25 < wait

namespace Parameters

/-- Drop length, given by `Real.exp c.m + 10`. -/
def dropLength (c : Parameters) : ℝ := Real.exp c.m + 10
/-- Hold start, given by `c.dropLength + 2`. -/
def holdStart (c : Parameters) : ℝ := c.dropLength + 2
/-- Pulse start, given by `c.holdStart + c.wait`. -/
def pulseStart (c : Parameters) : ℝ := c.holdStart + c.wait
/-- Pulse length, given by `13 / c.lam`. -/
def pulseLength (c : Parameters) : ℝ := 13 / c.lam
/-- Endpoint, given by `c.pulseStart + c.pulseLength`. -/
def endpoint (c : Parameters) : ℝ := c.pulseStart + c.pulseLength

theorem dropLength_pos (c : Parameters) : 0 < c.dropLength := by
  dsimp [dropLength]
  positivity

theorem holdStart_pos (c : Parameters) : 0 < c.holdStart := by
  dsimp [holdStart]
  linarith [c.dropLength_pos]

theorem pulseStart_ge_hold (c : Parameters) : c.holdStart ≤ c.pulseStart := by
  dsimp [pulseStart]
  linarith [c.wait_gt]

theorem pulseStart_pos (c : Parameters) : 0 < c.pulseStart :=
  c.holdStart_pos.trans_le c.pulseStart_ge_hold

theorem pulseLength_pos (c : Parameters) : 0 < c.pulseLength :=
  div_pos (by norm_num) c.lam_pos

/-- Exponents, with branches according to `i = 0`. -/
def exponents (c : Parameters) (i : Fin 2) : ℝ :=
  if i = 0 then -(1 / 2 + c.lam) else -(1 / 2 + 2 * c.lam)

/-- The log supports lie inside `(L-3.15,L-2.85)` and `(L-1.15,L-.85)`. -/
def lower (c : Parameters) (i : Fin 2) : ℝ :=
  Real.exp (c.pulseLength - if i = 0 then 63 / 20 else 23 / 20)

/-- Upper, given by `Real.exp (c.pulseLength - if i = 0 then 57 / 20 else 17 / 20)`. -/
def upper (c : Parameters) (i : Fin 2) : ℝ :=
  Real.exp (c.pulseLength - if i = 0 then 57 / 20 else 17 / 20)

theorem exponents_injective (c : Parameters) : Injective c.exponents := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [exponents] at hij ⊢
  all_goals linarith [c.lam_pos]

theorem lower_pos (c : Parameters) (i : Fin 2) : 0 < c.lower i := Real.exp_pos _

theorem lower_lt_upper (c : Parameters) (i : Fin 2) : c.lower i < c.upper i := by
  apply Real.exp_lt_exp.mpr
  fin_cases i <;> norm_num [lower, upper]

theorem intervals_separated (c : Parameters) (i j : Fin 2) (hij : i < j) :
    c.upper i ≤ c.lower j := by
  fin_cases i <;> fin_cases j <;> norm_num at hij
  apply Real.exp_le_exp.mpr
  norm_num [upper, lower]
  linarith

theorem one_lt_lower (c : Parameters) (i : Fin 2) : 1 < c.lower i := by
  have hL : 4 < c.pulseLength := by
    apply (lt_div_iff₀ c.lam_pos).mpr
    nlinarith [c.lam_lt]
  change 1 < Real.exp _
  rw [← Real.exp_zero]
  apply Real.exp_lt_exp.mpr
  fin_cases i <;> norm_num <;> linarith

theorem upper_lt_end (c : Parameters) (i : Fin 2) :
    c.upper i < Real.exp c.pulseLength := by
  apply Real.exp_lt_exp.mpr
  fin_cases i <;> norm_num [upper]

theorem main_end_lt_lower (c : Parameters) (i : Fin 2) :
    Real.exp (11 / c.lam) < c.lower i := by
  apply Real.exp_lt_exp.mpr
  have hgap : (63 / 20 : ℝ) * c.lam < 2 := by nlinarith [c.lam_lt]
  have hgap' := (lt_div_iff₀ c.lam_pos).mpr hgap
  have hid : 13 / c.lam - 11 / c.lam = 2 / c.lam := by ring
  dsimp [lower, pulseLength]
  fin_cases i <;> norm_num <;> linarith

end Parameters

/-! ## Explicit smooth debts and constructed corrections -/

/-- Prefix M, given by `4 + ∫ y in (0 : ℝ)..c.pulseStart, Real.exp y * dropCoefficient c.m y`. -/
def prefixM (c : Parameters) : ℝ :=
  4 + ∫ y in (0 : ℝ)..c.pulseStart, Real.exp y * dropCoefficient c.m y

/-- Prefix J as an element of `ℝ`. -/
def prefixJ (c : Parameters) : ℝ :=
  (5 / 2) * Real.sqrt 2 * c.P +
    ∫ y in (0 : ℝ)..c.pulseStart,
      Real.sqrt 2 * Real.exp (3 * y / 2) *
        radialAmplitude c.P c.dropLength c.lam y * dropCoefficient c.m y

/-- Pulse amplitude, given by `radialAmplitude c.P c.dropLength c.lam c.pulseStart`. -/
def pulseAmplitude (c : Parameters) : ℝ :=
  radialAmplitude c.P c.dropLength c.lam c.pulseStart

/-- Moment scale, with branches according to `i = 0`. -/
def momentScale (c : Parameters) (i : Fin 2) : ℝ :=
  if i = 0 then Real.exp c.pulseStart * pulseAmplitude c
  else Real.sqrt 2 * Real.exp (3 * c.pulseStart / 2) * pulseAmplitude c ^ 2

theorem pulseAmplitude_pos (c : Parameters) : 0 < pulseAmplitude c :=
  mul_pos c.P_pos (Real.exp_pos _)

theorem momentScale_pos (c : Parameters) (i : Fin 2) : 0 < momentScale c i := by
  unfold momentScale
  split_ifs
  · exact mul_pos (Real.exp_pos _) (pulseAmplitude_pos c)
  · exact mul_pos (mul_pos (Real.sqrt_pos.mpr (by norm_num)) (Real.exp_pos _))
      (sq_pos_of_pos (pulseAmplitude_pos c))

/-- Prefix coefficient, given by `(if i = 0 then prefixM c else prefixJ c) / momentScale c i`. -/
def prefixCoefficient (c : Parameters) (i : Fin 2) : ℝ :=
  (if i = 0 then prefixM c else prefixJ c) / momentScale c i

/-- Main moment, given by `∫ x in (1 : ℝ)..Real.exp c.pulseLength, x ^ c.exponents i * mainPulse
(c.lam * Real.log x)`. -/
def mainMoment (c : Parameters) (i : Fin 2) : ℝ :=
  ∫ x in (1 : ℝ)..Real.exp c.pulseLength,
    x ^ c.exponents i * mainPulse (c.lam * Real.log x)

/-- Debt, given by `-(prefixCoefficient c i * eta * (1 + eta ^ 2) + amp eta * mainMoment c i)`. -/
def debt (c : Parameters) (amp : ℝ → ℝ) (eta : ℝ) (i : Fin 2) : ℝ :=
  -(prefixCoefficient c i * eta * (1 + eta ^ 2) + amp eta * mainMoment c i)

theorem debt_contDiff (c : Parameters) {amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ amp)
    (i : Fin 2) : ContDiff ℝ ∞ (fun eta => debt c amp eta i) :=
  ((contDiff_const.mul contDiff_id).mul (contDiff_const.add (contDiff_id.pow 2)) |>.add
    (ha.mul contDiff_const)).neg

/-- Correction, given by `LocalizedMomentRepair.repair c.exponents c.lower c.upper (debt c amp
eta) x`. -/
def correction (c : Parameters) (amp : ℝ → ℝ) (eta x : ℝ) : ℝ :=
  LocalizedMomentRepair.repair c.exponents c.lower c.upper (debt c amp eta) x

theorem correction_exact (c : Parameters) (amp : ℝ → ℝ) (eta : ℝ) (i : Fin 2) :
    (∫ x, x ^ c.exponents i * correction c amp eta x) = debt c amp eta i :=
  LocalizedMomentRepair.repair_exact c.exponents c.lower c.upper (debt c amp eta)
    c.exponents_injective c.lower_pos c.lower_lt_upper c.intervals_separated i

theorem correction_contDiff_joint (c : Parameters) {amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ amp) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => correction c amp p.2 (Real.exp p.1)) := by
  have heq : (fun p : ℝ × ℝ => correction c amp p.2 (Real.exp p.1)) =
      (fun p : ℝ × ℝ => ∑ i : Fin 2, debt c amp p.2 i *
        LocalizedMomentRepair.repair c.exponents c.lower c.upper (Pi.single i 1)
          (Real.exp p.1)) := by
    funext p
    exact congrFun (LocalizedMomentRepair.repair_eq_sum_coordinate
      c.exponents c.lower c.upper (debt c amp p.2)) (Real.exp p.1)
  rw [heq]
  apply ContDiff.sum
  intro i _
  exact ((debt_contDiff c ha i).comp contDiff_snd).mul
    ((LocalizedMomentRepair.repair_contDiff c.exponents c.lower c.upper (Pi.single i 1)).comp
      contDiff_fst.exp)

theorem correction_zero_of_outside (c : Parameters) (amp : ℝ → ℝ) (eta x : ℝ)
    (hx : ∀ i : Fin 2, x ∉ Ioo (c.lower i) (c.upper i)) :
    correction c amp eta x = 0 := by
  by_contra h
  have hs := (LocalizedMomentRepair.repair_tsupport_subset_open
    c.exponents c.lower c.upper (debt c amp eta) c.lower_lt_upper)
    (subset_tsupport _ h)
  obtain ⟨i, hi⟩ := mem_iUnion.mp hs
  exact hx i hi

theorem correction_zero_early (c : Parameters) (amp : ℝ → ℝ) (eta : ℝ) {y : ℝ}
    (hy : y ≤ 0) : correction c amp eta (Real.exp y) = 0 := by
  apply correction_zero_of_outside
  intro i hi
  have hey : Real.exp y ≤ 1 := by simpa using Real.exp_le_exp.mpr hy
  linarith [c.one_lt_lower i, hi.1]

theorem correction_zero_late (c : Parameters) (amp : ℝ → ℝ) (eta : ℝ) {y : ℝ}
    (hy : c.pulseLength ≤ y) : correction c amp eta (Real.exp y) = 0 := by
  apply correction_zero_of_outside
  intro i hi
  have hey := Real.exp_le_exp.mpr hy
  linarith [c.upper_lt_end i, hi.2]

/-- Pulse ratio, given by `amp p.2 * mainPulse (c.lam * p.1) + correction c amp p.2 (Real.exp
p.1)`. -/
def pulseRatio (c : Parameters) (amp : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  amp p.2 * mainPulse (c.lam * p.1) + correction c amp p.2 (Real.exp p.1)

theorem pulseRatio_contDiff (c : Parameters) {amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ amp) : ContDiff ℝ ∞ (pulseRatio c amp) :=
  ((ha.comp contDiff_snd).mul
    (mainPulse_contDiff.comp (contDiff_const.mul contDiff_fst))).add
    (correction_contDiff_joint c ha)

theorem pulseRatio_zero_early (c : Parameters) (amp : ℝ → ℝ) (eta : ℝ) {y : ℝ}
    (hy : y ≤ 0) : pulseRatio c amp (y, eta) = 0 := by
  simp only [pulseRatio]
  rw [mainPulse_zero_left (mul_nonpos_of_nonneg_of_nonpos c.lam_pos.le hy),
    correction_zero_early c amp eta hy]
  ring

theorem pulseRatio_zero_late (c : Parameters) (amp : ℝ → ℝ) (eta : ℝ) {y : ℝ}
    (hy : c.pulseLength ≤ y) : pulseRatio c amp (y, eta) = 0 := by
  have h13 : 13 ≤ c.lam * y := by
    have h := (div_le_iff₀ c.lam_pos).mp hy
    nlinarith
  simp only [pulseRatio]
  rw [mainPulse_zero_right (by linarith : 11 ≤ c.lam * y),
    correction_zero_late c amp eta hy]
  ring

/-- Axial, given by `initialAxial c.m p + angular c.P c.dropLength c.lam p * pulseRatio c amp
(p.1 - c.pulseStart, p.2)`. -/
def axial (c : Parameters) (amp : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  initialAxial c.m p + angular c.P c.dropLength c.lam p *
    pulseRatio c amp (p.1 - c.pulseStart, p.2)

theorem axial_contDiff (c : Parameters) {amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ amp) : ContDiff ℝ ∞ (axial c amp) :=
  (initialAxial_contDiff c.m_pos).add ((angular_contDiff c.P c.dropLength c.lam).mul
    ((pulseRatio_contDiff c ha).comp
      ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd)))

theorem axial_before_pulse (c : Parameters) (amp : ℝ → ℝ) (eta : ℝ) {y : ℝ}
    (hy : y ≤ c.pulseStart) : axial c amp (y, eta) = dropCoefficient c.m y * eta := by
  simp [axial, initialAxial, pulseRatio_zero_early c amp eta (by linarith : y - c.pulseStart ≤ 0)]

theorem axial_shaped_wait (c : Parameters) (amp : ℝ → ℝ) (eta : ℝ) {y : ℝ}
    (hy : c.holdStart ≤ y) (hy' : y ≤ c.pulseStart) : axial c amp (y, eta) = 0 := by
  rw [axial_before_pulse c amp eta hy', dropCoefficient_late c.m_pos]
  · ring
  · dsimp [Parameters.holdStart, Parameters.dropLength]
      at hy
    linarith

theorem axial_after_pulse (c : Parameters) (amp : ℝ → ℝ) (eta : ℝ) {y : ℝ}
    (hy : c.endpoint ≤ y) : axial c amp (y, eta) = 0 := by
  have hlate : c.pulseLength ≤ y - c.pulseStart := by
    dsimp [Parameters.endpoint] at hy
    linarith
  have hdrop : Real.exp c.m ≤ y := by
    have hB := c.pulseStart_ge_hold
    have hL := c.pulseLength_pos
    dsimp [Parameters.endpoint] at hy
    dsimp [Parameters.holdStart, Parameters.dropLength] at hB
    linarith
  simp [axial, initialAxial, pulseRatio_zero_late c amp eta hlate,
    dropCoefficient_late c.m_pos hdrop]

theorem angular_shaped_wait (c : Parameters) (eta : ℝ) {y : ℝ}
    (hy : c.holdStart ≤ y) :
    angular c.P c.dropLength c.lam (y, eta) =
      radialAmplitude c.P c.dropLength c.lam c.holdStart * shape eta *
        Real.exp (-(1 / 2 + c.lam) * (y - c.holdStart)) := by
  unfold angular
  rw [radialAmplitude_hold c.dropLength_pos.le (by rfl) hy]
  ring

/-! ## Exact finite radial moments of the pulse -/

/-- Radial pulse, given by `amp eta * mainPulse (c.lam * Real.log x) + correction c amp eta x`. -/
def radialPulse (c : Parameters) (amp : ℝ → ℝ) (eta x : ℝ) : ℝ :=
  amp eta * mainPulse (c.lam * Real.log x) + correction c amp eta x

theorem radialPulse_exp (c : Parameters) (amp : ℝ → ℝ) (eta y : ℝ) :
    radialPulse c amp eta (Real.exp y) = pulseRatio c amp (y, eta) := by
  simp [radialPulse, pulseRatio]

theorem radialPulse_continuousOn (c : Parameters) (amp : ℝ → ℝ) (eta : ℝ) :
    ContinuousOn (radialPulse c amp eta) (Ioi 0) := by
  have hlog : ContinuousOn Real.log (Ioi (0 : ℝ)) :=
    continuousOn_id.log (fun _ hx => ne_of_gt hx)
  exact (continuousOn_const.mul
    (mainPulse_contDiff.continuous.comp_continuousOn (continuousOn_const.mul hlog))).add
    ((LocalizedMomentRepair.repair_contDiff c.exponents c.lower c.upper
      (debt c amp eta)).continuous.continuousOn)

theorem correction_interval_exact (c : Parameters) (amp : ℝ → ℝ) (eta : ℝ) (i : Fin 2) :
    (∫ x in (1 : ℝ)..Real.exp c.pulseLength,
      x ^ c.exponents i * correction c amp eta x) = debt c amp eta i := by
  rw [intervalIntegral.integral_eq_integral_of_support_subset]
  · exact correction_exact c amp eta i
  · intro x hx
    have hc : correction c amp eta x ≠ 0 := by
      intro hzero
      exact hx (by simp [hzero])
    have hs := (LocalizedMomentRepair.repair_tsupport_subset_open
      c.exponents c.lower c.upper (debt c amp eta) c.lower_lt_upper)
      (subset_tsupport _ hc)
    obtain ⟨j, hj⟩ := mem_iUnion.mp hs
    exact ⟨(c.one_lt_lower j).trans hj.1, hj.2.le.trans (c.upper_lt_end j).le⟩

theorem pulse_moment_exact (c : Parameters) (amp : ℝ → ℝ) (eta : ℝ) (i : Fin 2) :
    (∫ x in (1 : ℝ)..Real.exp c.pulseLength,
      x ^ c.exponents i * radialPulse c amp eta x) =
        -(prefixCoefficient c i * eta * (1 + eta ^ 2)) := by
  have hle : 1 ≤ Real.exp c.pulseLength := by
    simpa using Real.exp_le_exp.mpr c.pulseLength_pos.le
  have hpos : ∀ x ∈ Icc (1 : ℝ) (Real.exp c.pulseLength), x ≠ 0 := by
    intro x hx
    linarith [hx.1]
  have hpow : ContinuousOn (fun x : ℝ => x ^ c.exponents i)
      (Icc 1 (Real.exp c.pulseLength)) :=
    continuousOn_id.rpow_const (fun x hx => Or.inl (hpos x hx))
  have hlog : ContinuousOn Real.log (Icc (1 : ℝ) (Real.exp c.pulseLength)) :=
    continuousOn_id.log hpos
  have hmain : IntervalIntegrable
      (fun x : ℝ => x ^ c.exponents i * (amp eta * mainPulse (c.lam * Real.log x)))
      volume 1 (Real.exp c.pulseLength) :=
    ContinuousOn.intervalIntegrable_of_Icc hle
      (hpow.mul (continuousOn_const.mul
        (mainPulse_contDiff.continuous.comp_continuousOn (continuousOn_const.mul hlog))))
  have hcorr : IntervalIntegrable
      (fun x : ℝ => x ^ c.exponents i * correction c amp eta x)
      volume 1 (Real.exp c.pulseLength) :=
    ContinuousOn.intervalIntegrable_of_Icc hle
      (hpow.mul ((LocalizedMomentRepair.repair_contDiff
        c.exponents c.lower c.upper (debt c amp eta)).continuous.continuousOn))
  calc
    _ = (∫ x in (1 : ℝ)..Real.exp c.pulseLength,
          x ^ c.exponents i * (amp eta * mainPulse (c.lam * Real.log x))) +
        (∫ x in (1 : ℝ)..Real.exp c.pulseLength,
          x ^ c.exponents i * correction c amp eta x) := by
      simp only [radialPulse, mul_add]
      exact intervalIntegral.integral_add hmain hcorr
    _ = amp eta * mainMoment c i + debt c amp eta i := by
      rw [correction_interval_exact]
      congr 1
      unfold mainMoment
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x _
      ring
    _ = _ := by unfold debt; ring

/-- Reattaching the actual prefix gives zero total mass and angular moments.
The two components have physical factors `shape η` and `(shape η)^2`. -/
theorem pulse_closes_prefix (c : Parameters) (amp : ℝ → ℝ) (eta : ℝ) :
    prefixM c * eta + momentScale c 0 * shape eta *
      (∫ x in (1 : ℝ)..Real.exp c.pulseLength,
        x ^ c.exponents 0 * radialPulse c amp eta x) = 0 ∧
    prefixJ c * eta * shape eta + momentScale c 1 * (shape eta)^2 *
      (∫ x in (1 : ℝ)..Real.exp c.pulseLength,
        x ^ c.exponents 1 * radialPulse c amp eta x) = 0 := by
  rw [pulse_moment_exact, pulse_moment_exact]
  have hs : 1 + eta ^ 2 ≠ 0 := by positivity
  have hM := (momentScale_pos c 0).ne'
  have hJ := (momentScale_pos c 1).ne'
  simp only [prefixCoefficient, shape, Fin.isValue, reduceIte, one_ne_zero]
  constructor <;> field_simp <;> ring

/-! ## The moments of the combined log-radius profile -/

theorem exp_weight_substitution {R : ℝ → ℝ} (hR : ContinuousOn R (Ioi 0))
    (a B L : ℝ) :
    (∫ y in B..B + L, Real.exp ((a + 1) * (y - B)) * R (Real.exp (y - B))) =
      ∫ x in (1 : ℝ)..Real.exp L, x ^ a * R x := by
  have hpos : ∀ x ∈ (fun y : ℝ => Real.exp (y - B)) '' uIcc B (B + L), 0 < x := by
    rintro x ⟨y, hy, rfl⟩
    exact Real.exp_pos _
  have hpow : ContinuousOn (fun x : ℝ => x ^ a)
      ((fun y : ℝ => Real.exp (y - B)) '' uIcc B (B + L)) :=
    continuousOn_id.rpow_const (fun x hx => Or.inl (hpos x hx).ne')
  have hsub := intervalIntegral.integral_comp_mul_deriv'
    (a := B) (b := B + L) (f := fun y : ℝ => Real.exp (y - B))
    (f' := fun y : ℝ => Real.exp (y - B)) (g := fun x : ℝ => x ^ a * R x)
    (fun y _ => by simpa using ((hasDerivAt_id y).sub_const B).exp)
    ((Real.continuous_exp.comp (continuous_id.sub continuous_const)).continuousOn)
    (hpow.mul (hR.mono (fun x hx => hpos x hx)))
  calc
    _ = ∫ y in B..B + L,
        ((fun x : ℝ => x ^ a * R x) ∘ (fun y : ℝ => Real.exp (y - B))) y *
          Real.exp (y - B) := by
      apply intervalIntegral.integral_congr
      intro y _
      simp only [Function.comp_apply, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      rw [show (a + 1) * (y - B) = (y - B) * a + (y - B) by ring, Real.exp_add]
      ring
    _ = _ := by simpa using hsub

theorem axial_radial_contDiff (c : Parameters) (amp : ℝ → ℝ) (eta : ℝ) :
    ContDiff ℝ ∞ (fun y => axial c amp (y, eta)) := by
  have he : ContDiff ℝ ∞ (fun y => angular c.P c.dropLength c.lam (y, eta)) :=
    (angular_contDiff c.P c.dropLength c.lam).comp (contDiff_id.prodMk contDiff_const)
  have hr : ContDiff ℝ ∞ (fun y => pulseRatio c amp (y - c.pulseStart, eta)) :=
    by
      change ContDiff ℝ ∞ (fun y => amp eta * mainPulse (c.lam * (y - c.pulseStart)) +
        LocalizedMomentRepair.repair c.exponents c.lower c.upper (debt c amp eta)
          (Real.exp (y - c.pulseStart)))
      exact (contDiff_const.mul (mainPulse_contDiff.comp
        (contDiff_const.mul (contDiff_id.sub contDiff_const)))).add
        ((LocalizedMomentRepair.repair_contDiff c.exponents c.lower c.upper (debt c amp eta)).comp
          (contDiff_id.sub contDiff_const).exp)
  exact ((dropCoefficient_contDiff c.m_pos).mul contDiff_const).add (he.mul hr)

theorem angular_pulse (c : Parameters) (eta : ℝ) {y : ℝ} (hy : c.pulseStart ≤ y) :
    angular c.P c.dropLength c.lam (y, eta) =
      pulseAmplitude c * shape eta * Real.exp (-(1 / 2 + c.lam) * (y - c.pulseStart)) := by
  unfold angular
  rw [radialAmplitude_hold c.dropLength_pos.le c.pulseStart_ge_hold hy]
  unfold pulseAmplitude
  ring

theorem axial_pulse (c : Parameters) (amp : ℝ → ℝ) (eta : ℝ) {y : ℝ}
    (hy : c.pulseStart ≤ y) :
    axial c amp (y, eta) = angular c.P c.dropLength c.lam (y, eta) *
      radialPulse c amp eta (Real.exp (y - c.pulseStart)) := by
  have hdrop : Real.exp c.m ≤ y := by
    have hb := c.pulseStart_ge_hold
    dsimp [Parameters.holdStart, Parameters.dropLength] at hb
    linarith
  simp [axial, initialAxial, dropCoefficient_late c.m_pos hdrop, radialPulse_exp]

theorem mass_integrand_pulse (c : Parameters) (amp : ℝ → ℝ) (eta : ℝ) {y : ℝ}
    (hy : c.pulseStart ≤ y) :
    Real.exp y * axial c amp (y, eta) =
      (momentScale c 0 * shape eta) *
        (Real.exp ((c.exponents 0 + 1) * (y - c.pulseStart)) *
          radialPulse c amp eta (Real.exp (y - c.pulseStart))) := by
  rw [axial_pulse c amp eta hy, angular_pulse c eta hy]
  have he : Real.exp y * Real.exp (-(1 / 2 + c.lam) * (y - c.pulseStart)) =
      Real.exp c.pulseStart * Real.exp ((c.exponents 0 + 1) * (y - c.pulseStart)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    norm_num [Parameters.exponents]
    ring
  norm_num [momentScale]
  calc
    _ = (pulseAmplitude c * shape eta) *
        (Real.exp y * Real.exp (-(1 / 2 + c.lam) * (y - c.pulseStart))) *
          radialPulse c amp eta (Real.exp (y - c.pulseStart)) := by ring_nf
    _ = _ := by rw [he]; ring

theorem angular_integrand_pulse (c : Parameters) (amp : ℝ → ℝ) (eta : ℝ) {y : ℝ}
    (hy : c.pulseStart ≤ y) :
    Real.sqrt 2 * Real.exp (3 * y / 2) * angular c.P c.dropLength c.lam (y, eta) *
        axial c amp (y, eta) =
      (momentScale c 1 * (shape eta)^2) *
        (Real.exp ((c.exponents 1 + 1) * (y - c.pulseStart)) *
          radialPulse c amp eta (Real.exp (y - c.pulseStart))) := by
  rw [axial_pulse c amp eta hy, angular_pulse c eta hy]
  have he : Real.exp (3 * y / 2) *
      Real.exp (-(1 / 2 + c.lam) * (y - c.pulseStart)) ^ 2 =
      Real.exp (3 * c.pulseStart / 2) *
        Real.exp ((c.exponents 1 + 1) * (y - c.pulseStart)) := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    norm_num [Parameters.exponents]
    ring
  norm_num [momentScale]
  calc
    _ = (Real.sqrt 2 * pulseAmplitude c ^ 2 * shape eta ^ 2) *
        (Real.exp (3 * y / 2) * Real.exp (-(1 / 2 + c.lam) * (y - c.pulseStart)) ^ 2) *
          radialPulse c amp eta (Real.exp (y - c.pulseStart)) := by ring_nf
    _ = _ := by rw [he]; ring

/-- `X=e^y`; the first term is the exact mass of the ideal prefix `0<X≤1`. -/
def massMoment (c : Parameters) (amp : ℝ → ℝ) (eta y : ℝ) : ℝ :=
  4 * eta + ∫ t in (0 : ℝ)..y, Real.exp t * axial c amp (t, eta)

/-- The first term integrates `U H` over the ideal prefix `0<X≤1`. -/
def angularMoment (c : Parameters) (amp : ℝ → ℝ) (eta y : ℝ) : ℝ :=
  (5 / 2) * Real.sqrt 2 * c.P * eta * shape eta +
    ∫ t in (0 : ℝ)..y,
      Real.sqrt 2 * Real.exp (3 * t / 2) * angular c.P c.dropLength c.lam (t, eta) *
        axial c amp (t, eta)

theorem massMoment_at_pulseStart (c : Parameters) (amp : ℝ → ℝ) (eta : ℝ) :
    massMoment c amp eta c.pulseStart = prefixM c * eta := by
  have hI : (∫ t in (0 : ℝ)..c.pulseStart, Real.exp t * axial c amp (t, eta)) =
      (∫ t in (0 : ℝ)..c.pulseStart, Real.exp t * dropCoefficient c.m t) * eta := by
    rw [← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [axial_before_pulse c amp eta ((uIcc_of_le c.pulseStart_pos.le ▸ ht).2)]
    ring
  unfold massMoment prefixM
  rw [hI]
  ring

theorem angularMoment_at_pulseStart (c : Parameters) (amp : ℝ → ℝ) (eta : ℝ) :
    angularMoment c amp eta c.pulseStart = prefixJ c * eta * shape eta := by
  have hI : (∫ t in (0 : ℝ)..c.pulseStart,
      Real.sqrt 2 * Real.exp (3 * t / 2) * angular c.P c.dropLength c.lam (t, eta) *
        axial c amp (t, eta)) =
      (∫ t in (0 : ℝ)..c.pulseStart,
        Real.sqrt 2 * Real.exp (3 * t / 2) *
          radialAmplitude c.P c.dropLength c.lam t * dropCoefficient c.m t) *
          (eta * shape eta) := by
    rw [← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [axial_before_pulse c amp eta ((uIcc_of_le c.pulseStart_pos.le ▸ ht).2)]
    unfold angular
    ring
  unfold angularMoment prefixJ
  rw [hI]
  ring

theorem axial_reserved_band (c : Parameters) (amp : ℝ → ℝ) (eta y : ℝ)
    (hy : c.pulseStart - 25 ≤ y) (hy' : y ≤ c.pulseStart - 3) :
    axial c amp (y, eta) = 0 := by
  apply axial_shaped_wait c amp eta
  · dsimp [Parameters.pulseStart] at hy
    linarith [c.wait_gt]
  · linarith

theorem correction_zero_on_main_pulse (c : Parameters) (amp : ℝ → ℝ) (eta : ℝ)
    {y : ℝ} (hy : y ≤ 11 / c.lam) : correction c amp eta (Real.exp y) = 0 := by
  apply correction_zero_of_outside
  intro i hi
  have hey := Real.exp_le_exp.mpr hy
  linarith [c.main_end_lt_lower i, hi.1]

theorem pulseRatio_on_main_pulse (c : Parameters) (amp : ℝ → ℝ) (eta : ℝ)
    {y : ℝ} (hy : y ≤ 11 / c.lam) :
    pulseRatio c amp (y, eta) = amp eta * mainPulse (c.lam * y) := by
  simp [pulseRatio, correction_zero_on_main_pulse c amp eta hy]

theorem axial_ideal (c : Parameters) (amp : ℝ → ℝ) (eta : ℝ) {y : ℝ} (hy : y ≤ 0) :
    axial c amp (y, eta) = 4 * eta := by
  rw [axial_before_pulse c amp eta (hy.trans c.pulseStart_pos.le),
    dropCoefficient_early c.m (by linarith)]

theorem axial_drop (c : Parameters) (amp : ℝ → ℝ) (eta : ℝ) {t : ℝ}
    (ht : 0 ≤ t) (ht' : t ≤ c.dropLength) :
    axial c amp (1 + t, eta) =
      4 * (1 - sigma (Real.log (1 + t) / c.m)) * eta := by
  have hB := c.pulseStart_ge_hold
  have hy : 1 + t ≤ c.pulseStart := by
    dsimp [Parameters.holdStart] at hB
    linarith
  rw [axial_before_pulse c amp eta hy, dropCoefficient_eq c.m_pos (by linarith)]

theorem radialAmplitude_drop {dropLength lam y P : ℝ}
    (hy : 1 ≤ y) (hy' : y ≤ dropLength + 1) :
    radialAmplitude P dropLength lam y =
      radialAmplitude P dropLength lam 1 * Real.exp (-(y - 1) / 2) := by
  have h := primitive_increment (g := fun t => slope dropLength lam t - 1 / 2)
    ((slope_contDiff dropLength lam).continuous.sub continuous_const) 1 y (-1 / 2) ?_
  · have he : logAmplitude dropLength lam y =
        logAmplitude dropLength lam 1 + -(y - 1) / 2 := by
      unfold logAmplitude
      rw [h]
      ring
    simp only [radialAmplitude, he, Real.exp_add, mul_assoc]
  · intro t ht
    have ht' := uIcc_of_le hy ▸ ht
    rw [slope_drop ht'.1 (ht'.2.trans hy')]
    ring

theorem ideal_mass_prefix_integral (eta : ℝ) :
    (∫ _x in (0 : ℝ)..1, 4 * eta) = 4 * eta := by simp

theorem ideal_angular_prefix_integral (P eta : ℝ) :
    (∫ x in (0 : ℝ)..1, (4 * eta * Real.sqrt 2 * P * shape eta) * x ^ (3 / 5 : ℝ)) =
      (5 / 2) * Real.sqrt 2 * P * eta * shape eta := by
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num))]
  norm_num
  ring

/-- Both moments are the actual log-coordinate integrals of the combined fields. -/
theorem massMoment_endpoint (c : Parameters) (amp : ℝ → ℝ) (eta : ℝ) :
    massMoment c amp eta c.endpoint = 0 := by
  have hF : Continuous (fun t => Real.exp t * axial c amp (t, eta)) :=
    Real.continuous_exp.mul (axial_radial_contDiff c amp eta).continuous
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hF.intervalIntegrable 0 c.pulseStart) (hF.intervalIntegrable c.pulseStart c.endpoint)
  have hI : (∫ t in c.pulseStart..c.endpoint, Real.exp t * axial c amp (t, eta)) =
      (momentScale c 0 * shape eta) *
        (∫ x in (1 : ℝ)..Real.exp c.pulseLength,
          x ^ c.exponents 0 * radialPulse c amp eta x) := by
    calc
      _ = ∫ t in c.pulseStart..c.pulseStart + c.pulseLength,
          (momentScale c 0 * shape eta) *
            (Real.exp ((c.exponents 0 + 1) * (t - c.pulseStart)) *
              radialPulse c amp eta (Real.exp (t - c.pulseStart))) := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp only
        apply mass_integrand_pulse c amp eta
        exact (uIcc_of_le (show c.pulseStart ≤ c.endpoint by
          dsimp [Parameters.endpoint]; linarith [c.pulseLength_pos]) ▸ ht).1
      _ = _ := by
        rw [intervalIntegral.integral_const_mul,
          exp_weight_substitution (radialPulse_continuousOn c amp eta)]
  calc
    massMoment c amp eta c.endpoint = massMoment c amp eta c.pulseStart +
        (∫ t in c.pulseStart..c.endpoint, Real.exp t * axial c amp (t, eta)) := by
      unfold massMoment
      rw [← hsplit]
      ring
    _ = 0 := by
      rw [massMoment_at_pulseStart, hI]
      exact (pulse_closes_prefix c amp eta).1

theorem angularMoment_endpoint (c : Parameters) (amp : ℝ → ℝ) (eta : ℝ) :
    angularMoment c amp eta c.endpoint = 0 := by
  have hE : Continuous (fun t => angular c.P c.dropLength c.lam (t, eta)) :=
    ((angular_contDiff c.P c.dropLength c.lam).comp
      (contDiff_id.prodMk contDiff_const)).continuous
  have hF : Continuous (fun t => Real.sqrt 2 * Real.exp (3 * t / 2) *
      angular c.P c.dropLength c.lam (t, eta) * axial c amp (t, eta)) :=
    ((continuous_const.mul (Real.continuous_exp.comp
      ((continuous_const.mul continuous_id).div_const 2))).mul hE).mul
      (axial_radial_contDiff c amp eta).continuous
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hF.intervalIntegrable 0 c.pulseStart) (hF.intervalIntegrable c.pulseStart c.endpoint)
  have hI : (∫ t in c.pulseStart..c.endpoint,
      Real.sqrt 2 * Real.exp (3 * t / 2) * angular c.P c.dropLength c.lam (t, eta) *
        axial c amp (t, eta)) =
      (momentScale c 1 * shape eta ^ 2) *
        (∫ x in (1 : ℝ)..Real.exp c.pulseLength,
          x ^ c.exponents 1 * radialPulse c amp eta x) := by
    calc
      _ = ∫ t in c.pulseStart..c.pulseStart + c.pulseLength,
          (momentScale c 1 * shape eta ^ 2) *
            (Real.exp ((c.exponents 1 + 1) * (t - c.pulseStart)) *
              radialPulse c amp eta (Real.exp (t - c.pulseStart))) := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp only
        apply angular_integrand_pulse c amp eta
        exact (uIcc_of_le (show c.pulseStart ≤ c.endpoint by
          dsimp [Parameters.endpoint]; linarith [c.pulseLength_pos]) ▸ ht).1
      _ = _ := by
        rw [intervalIntegral.integral_const_mul,
          exp_weight_substitution (radialPulse_continuousOn c amp eta)]
  calc
    angularMoment c amp eta c.endpoint = angularMoment c amp eta c.pulseStart +
        (∫ t in c.pulseStart..c.endpoint,
          Real.sqrt 2 * Real.exp (3 * t / 2) * angular c.P c.dropLength c.lam (t, eta) *
            axial c amp (t, eta)) := by
      unfold angularMoment
      rw [← hsplit]
      ring
    _ = 0 := by
      rw [angularMoment_at_pulseStart, hI]
      exact (pulse_closes_prefix c amp eta).2

/-- The constructed profiles satisfy both endpoint equations for every parameter value. -/
theorem exact_axial_moments (c : Parameters) (amp : ℝ → ℝ) (eta : ℝ) :
    massMoment c amp eta c.endpoint = 0 ∧ angularMoment c amp eta c.endpoint = 0 :=
  ⟨massMoment_endpoint c amp eta, angularMoment_endpoint c amp eta⟩

theorem massMoment_after_pulse (c : Parameters) (amp : ℝ → ℝ) (eta : ℝ) {y : ℝ}
    (hy : c.endpoint ≤ y) : massMoment c amp eta y = 0 := by
  have hF : Continuous (fun t => Real.exp t * axial c amp (t, eta)) :=
    Real.continuous_exp.mul (axial_radial_contDiff c amp eta).continuous
  have hI : (∫ t in c.endpoint..y, Real.exp t * axial c amp (t, eta)) = 0 := by
    calc
      _ = ∫ _t in c.endpoint..y, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp only
        rw [axial_after_pulse c amp eta ((uIcc_of_le hy ▸ ht).1), mul_zero]
      _ = 0 := by simp
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hF.intervalIntegrable 0 c.endpoint) (hF.intervalIntegrable c.endpoint y)
  calc
    massMoment c amp eta y = massMoment c amp eta c.endpoint := by
      unfold massMoment
      rw [← hsplit, hI, add_zero]
    _ = 0 := massMoment_endpoint c amp eta

theorem angularMoment_after_pulse (c : Parameters) (amp : ℝ → ℝ) (eta : ℝ) {y : ℝ}
    (hy : c.endpoint ≤ y) : angularMoment c amp eta y = 0 := by
  have hE : Continuous (fun t => angular c.P c.dropLength c.lam (t, eta)) :=
    ((angular_contDiff c.P c.dropLength c.lam).comp
      (contDiff_id.prodMk contDiff_const)).continuous
  have hF : Continuous (fun t => Real.sqrt 2 * Real.exp (3 * t / 2) *
      angular c.P c.dropLength c.lam (t, eta) * axial c amp (t, eta)) :=
    ((continuous_const.mul (Real.continuous_exp.comp
      ((continuous_const.mul continuous_id).div_const 2))).mul hE).mul
      (axial_radial_contDiff c amp eta).continuous
  have hI : (∫ t in c.endpoint..y,
      Real.sqrt 2 * Real.exp (3 * t / 2) * angular c.P c.dropLength c.lam (t, eta) *
        axial c amp (t, eta)) = 0 := by
    calc
      _ = ∫ _t in c.endpoint..y, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp only
        rw [axial_after_pulse c amp eta ((uIcc_of_le hy ▸ ht).1), mul_zero]
      _ = 0 := by simp
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hF.intervalIntegrable 0 c.endpoint) (hF.intervalIntegrable c.endpoint y)
  calc
    angularMoment c amp eta y = angularMoment c amp eta c.endpoint := by
      unfold angularMoment
      rw [← hsplit, hI, add_zero]
    _ = 0 := angularMoment_endpoint c amp eta

/-- The manuscript's precise shaped-wait duration is a valid instance. -/
def paperParameters (P m lam : ℝ) (hP : 0 < P) (hm : 0 < m)
    (hlam : 0 < lam) (hlam' : lam < 1 / 10) : Parameters where
  P := P
  m := m
  lam := lam
  wait := 60 * Real.log (1 / lam)
  P_pos := hP
  m_pos := hm
  lam_pos := hlam
  lam_lt := hlam'
  wait_gt := by
    have h := Real.one_sub_inv_le_log_of_pos (one_div_pos.mpr hlam)
    simp only [one_div, inv_inv] at h ⊢
    nlinarith

/-- A compact interface for using the constructed profiles in later stages. -/
theorem constructed_core (c : Parameters) {amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ amp) :
    ContDiff ℝ ∞ (angular c.P c.dropLength c.lam) ∧
    ContDiff ℝ ∞ (axial c amp) ∧
    (∀ p, 0 < angular c.P c.dropLength c.lam p) ∧
    (∀ eta y, c.endpoint ≤ y →
      axial c amp (y, eta) = 0 ∧ massMoment c amp eta y = 0 ∧
        angularMoment c amp eta y = 0) ∧
    (∀ eta y, c.holdStart ≤ y → y ≤ c.pulseStart →
      axial c amp (y, eta) = 0 ∧
      angular c.P c.dropLength c.lam (y, eta) =
        radialAmplitude c.P c.dropLength c.lam c.holdStart * shape eta *
          Real.exp (-(1 / 2 + c.lam) * (y - c.holdStart))) := by
  refine ⟨angular_contDiff _ _ _, axial_contDiff c ha, angular_pos c.P_pos _ _, ?_, ?_⟩
  · intro eta y hy
    exact ⟨axial_after_pulse c amp eta hy, massMoment_after_pulse c amp eta hy,
      angularMoment_after_pulse c amp eta hy⟩
  · intro eta y hy hy'
    exact ⟨axial_shaped_wait c amp eta hy hy', angular_shaped_wait c eta hy⟩

end NavierStokes.OutgoingSchedule
