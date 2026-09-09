/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActivationStocks
public import LeanPool.NavierStokesAndEuler.NavierStokes.ReferenceJetBounds
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

@[expose] public section

/-!
# The stock-driven ACT continuation and its final two ramps

The controls below integrate the actual reference lag stocks.  The axial
control is turned off first; the angular control is then interpolated to
`4 / 5`.  All profile values are defined by integrals, including at the
joins.  No cone inequality is assumed here.
-/

noncomputable section

namespace NavierStokes.TransitionRamp

open Set Filter MeasureTheory ProfileHistories StressActivation
open scoped Topology ContDiff


/-- A translated copy of the manuscript's flat step. -/
noncomputable def step (b w y : ℝ) : ℝ := OutgoingSchedule.sigma ((y - b) / w)

theorem step_smooth (b w : ℝ) : ContDiff ℝ ∞ (step b w) :=
  OutgoingSchedule.sigma_contDiff.comp ((contDiff_id.sub contDiff_const).div_const w)

theorem step_mem (b w y : ℝ) : step b w y ∈ Icc (0 : ℝ) 1 :=
  ⟨OutgoingSchedule.sigma_nonneg _, OutgoingSchedule.sigma_le_one _⟩

theorem step_zero {b w y : ℝ} (hw : 0 < w) (hy : y ≤ b) : step b w y = 0 :=
  OutgoingSchedule.sigma_zero (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hy) hw.le)

theorem step_one {b w y : ℝ} (hw : 0 < w) (hy : b + w ≤ y) : step b w y = 1 :=
  OutgoingSchedule.sigma_one ((le_div_iff₀ hw).mpr (by linarith))

theorem damping_eq_constant {T : ℝ} (hT : 0 < T) (κ : ℝ) {y : ℝ} (hy : T ≤ y) :
    damping T κ y = κ := by
  rw [damping, activation, OutgoingSchedule.sigma_one ((le_div_iff₀ hT).mpr (by simpa))]
  ring

theorem damping_mem (T : ℝ) {κ : ℝ} (hκ : κ ∈ Icc (0 : ℝ) 1) (y : ℝ) :
    damping T κ y ∈ Icc (0 : ℝ) 1 := by
  have h0 := activation_nonneg T κ y hκ.2
  have h1 := activation_le_one T κ y hκ
  constructor <;> dsimp only [damping] <;> linarith

/-- A literal primitive, with an independently specified value at the axis
of the logarithmic clock. -/
noncomputable def integrate (initial : ℝ → ℝ) (slope : Field) : Field :=
  fun p => initial p.2 + primitive slope p

theorem integrate_smooth {J : Set ℝ} (hJ : IsOpen J) {initial : ℝ → ℝ} {slope : Field}
    (hi : ContDiffOn ℝ ∞ initial J)
    (hs : ContDiffOn ℝ ∞ slope (logDomain J hJ).carrier) :
    ContDiffOn ℝ ∞ (integrate initial slope) (logDomain J hJ).carrier :=
  (hi.comp contDiffOn_snd (fun _ hp => hp.2)).add (primitive_smooth (logDomain J hJ) hs)

theorem integrate_hasDerivAt {J : Set ℝ} (hJ : IsOpen J) (initial : ℝ → ℝ) {slope : Field}
    (hs : ContDiffOn ℝ ∞ slope (logDomain J hJ).carrier) (y : ℝ) {η : ℝ} (hη : η ∈ J) :
    HasDerivAt (fun x => integrate initial slope (x, η)) (slope (y, η)) y := by
  simpa only [integrate, zero_add] using (hasDerivAt_const y (initial η)).fun_add
    (primitive_hasDerivAt (logDomain J hJ) hs (p := (y, η)) ⟨mem_univ _, hη⟩)

@[simp] theorem integrate_initial (initial : ℝ → ℝ) (slope : Field) (η : ℝ) :
    integrate initial slope (0, η) = initial η := by simp [integrate, primitive]

theorem integrate_congr (initial : ℝ → ℝ) (slope₁ slope₂ : Field) (p : Point)
    (he : ∀ t ∈ uIcc (0 : ℝ) p.1, slope₁ (t, p.2) = slope₂ (t, p.2)) :
    integrate initial slope₁ p = integrate initial slope₂ p := by
  unfold integrate primitive
  congr 1
  exact intervalIntegral.integral_congr he

/-- The ordinary ACT control continues to multiply the REF lag stock,
even when the REF derivative has already become zero. -/
noncomputable def baseSlope (T κ : ℝ) (stock : Field) : Field :=
  fun p => -(damping T κ p.1 * stock p) / 2

noncomputable def angularSlope (T κ b w₁ w₂ : ℝ) (stock : Field) : Field :=
  fun p => (1 - step (b + w₁) w₂ p.1) * baseSlope T κ stock p -
    (2 / 5 : ℝ) * step (b + w₁) w₂ p.1

noncomputable def axialSlope (T κ b w₁ : ℝ) (stock : Field) : Field :=
  fun p => (1 - step b w₁ p.1) * baseSlope T κ stock p

theorem baseSlope_smooth (T κ : ℝ) {J : Set ℝ} (hJ : IsOpen J) {stock : Field}
    (hs : ContDiffOn ℝ ∞ stock (logDomain J hJ).carrier) :
    ContDiffOn ℝ ∞ (baseSlope T κ stock) (logDomain J hJ).carrier :=
  ((((damping_smooth T κ).comp contDiff_fst).contDiffOn.mul hs).neg).div_const 2

theorem angularSlope_smooth (T κ b w₁ w₂ : ℝ) {J : Set ℝ} (hJ : IsOpen J) {stock : Field}
    (hs : ContDiffOn ℝ ∞ stock (logDomain J hJ).carrier) :
    ContDiffOn ℝ ∞ (angularSlope T κ b w₁ w₂ stock) (logDomain J hJ).carrier :=
  (contDiffOn_const.sub ((step_smooth (b + w₁) w₂).comp contDiff_fst).contDiffOn).mul
    (baseSlope_smooth T κ hJ hs) |>.sub
      (contDiffOn_const.mul ((step_smooth (b + w₁) w₂).comp contDiff_fst).contDiffOn)

theorem axialSlope_smooth (T κ b w₁ : ℝ) {J : Set ℝ} (hJ : IsOpen J) {stock : Field}
    (hs : ContDiffOn ℝ ∞ stock (logDomain J hJ).carrier) :
    ContDiffOn ℝ ∞ (axialSlope T κ b w₁ stock) (logDomain J hJ).carrier :=
  (contDiffOn_const.sub ((step_smooth b w₁).comp contDiff_fst).contDiffOn).mul
    (baseSlope_smooth T κ hJ hs)

theorem angularSlope_before {T κ b w₁ w₂ : ℝ} (hw₂ : 0 < w₂) (stock : Field)
    {p : Point} (hp : p.1 ≤ b + w₁) :
    angularSlope T κ b w₁ w₂ stock p = baseSlope T κ stock p := by
  simp only [angularSlope, step_zero hw₂ hp, sub_zero, one_mul, mul_zero]

theorem axialSlope_before {T κ b w₁ : ℝ} (hw₁ : 0 < w₁) (stock : Field)
    {p : Point} (hp : p.1 ≤ b) :
    axialSlope T κ b w₁ stock p = baseSlope T κ stock p := by
  simp only [axialSlope, step_zero hw₁ hp, sub_zero, one_mul]

theorem angularSlope_after {T κ b w₁ w₂ : ℝ} (hw₂ : 0 < w₂) (stock : Field)
    {p : Point} (hp : b + w₁ + w₂ ≤ p.1) :
    angularSlope T κ b w₁ w₂ stock p = -(2 / 5 : ℝ) := by
  simp only [angularSlope, step_one hw₂ hp, sub_self, zero_mul, mul_one, zero_sub]

theorem axialSlope_after {T κ b w₁ : ℝ} (hw₁ : 0 < w₁) (stock : Field)
    {p : Point} (hp : b + w₁ ≤ p.1) : axialSlope T κ b w₁ stock p = 0 := by
  simp only [axialSlope, step_one hw₁ hp, sub_self, zero_mul]

/-- The actual logarithm of the angular amplitude. -/
noncomputable def logField (T κ b w₁ w₂ : ℝ) (initial : ℝ → ℝ) (stock : Field) : Field :=
  integrate initial (angularSlope T κ b w₁ w₂ stock)

/-- The actual axial velocity after the first, axial, shutoff. -/
noncomputable def axialField (T κ b w₁ : ℝ) (initial : ℝ → ℝ) (stock : Field) : Field :=
  integrate initial (axialSlope T κ b w₁ stock)

theorem logField_smooth (T κ b w₁ w₂ : ℝ) {J : Set ℝ} (hJ : IsOpen J)
    {initial : ℝ → ℝ} {stock : Field} (hi : ContDiffOn ℝ ∞ initial J)
    (hs : ContDiffOn ℝ ∞ stock (logDomain J hJ).carrier) :
    ContDiffOn ℝ ∞ (logField T κ b w₁ w₂ initial stock) (logDomain J hJ).carrier :=
  integrate_smooth hJ hi (angularSlope_smooth T κ b w₁ w₂ hJ hs)

theorem axialField_smooth (T κ b w₁ : ℝ) {J : Set ℝ} (hJ : IsOpen J)
    {initial : ℝ → ℝ} {stock : Field} (hi : ContDiffOn ℝ ∞ initial J)
    (hs : ContDiffOn ℝ ∞ stock (logDomain J hJ).carrier) :
    ContDiffOn ℝ ∞ (axialField T κ b w₁ initial stock) (logDomain J hJ).carrier :=
  integrate_smooth hJ hi (axialSlope_smooth T κ b w₁ hJ hs)

theorem logField_before {T κ b w₁ w₂ : ℝ} (hb : 0 ≤ b + w₁) (hw₂ : 0 < w₂)
    (initial : ℝ → ℝ) (stock : Field) {p : Point} (hp : p.1 ≤ b + w₁) :
    logField T κ b w₁ w₂ initial stock p = integrate initial (baseSlope T κ stock) p := by
  apply integrate_congr
  intro t ht
  apply angularSlope_before hw₂
  exact (mem_uIcc.mp ht).elim (fun h => h.2.trans hp) (fun h => h.2.trans hb)

theorem axialField_before {T κ b w₁ : ℝ} (hb : 0 ≤ b) (hw₁ : 0 < w₁)
    (initial : ℝ → ℝ) (stock : Field) {p : Point} (hp : p.1 ≤ b) :
    axialField T κ b w₁ initial stock p = integrate initial (baseSlope T κ stock) p := by
  apply integrate_congr
  intro t ht
  apply axialSlope_before hw₁
  exact (mem_uIcc.mp ht).elim (fun h => h.2.trans hp) (fun h => h.2.trans hb)

theorem integrate_affine_after {J : Set ℝ} (hJ : IsOpen J) (initial : ℝ → ℝ) {slope : Field}
    (hs : ContDiffOn ℝ ∞ slope (logDomain J hJ).carrier) {a y c η : ℝ}
    (hay : a ≤ y) (hη : η ∈ J) (hc : ∀ t, a ≤ t → slope (t, η) = c) :
    integrate initial slope (y, η) = integrate initial slope (a, η) + (y - a) * c := by
  have hd : ∀ t ∈ uIcc a y, HasDerivAt (fun x => integrate initial slope (x, η)) c t := by
    intro t ht
    rw [← hc t ((uIcc_of_le hay ▸ ht).1)]
    exact integrate_hasDerivAt hJ initial hs t hη
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => c) volume a y)
  rw [intervalIntegral.integral_const] at hi
  simp only [smul_eq_mul] at hi
  linarith

theorem logField_hold {T κ b w₁ w₂ : ℝ} (hw₂ : 0 < w₂) {J : Set ℝ} (hJ : IsOpen J)
    (initial : ℝ → ℝ) {stock : Field} (hs : ContDiffOn ℝ ∞ stock (logDomain J hJ).carrier)
    {a y η : ℝ} (ha : b + w₁ + w₂ ≤ a) (hay : a ≤ y) (hη : η ∈ J) :
    logField T κ b w₁ w₂ initial stock (y, η) =
      logField T κ b w₁ w₂ initial stock (a, η) - (2 / 5 : ℝ) * (y - a) := by
  unfold logField
  convert! integrate_affine_after hJ initial (angularSlope_smooth T κ b w₁ w₂ hJ hs)
    hay hη (fun t ht => angularSlope_after hw₂ stock (ha.trans ht)) using 1
  ring

theorem axialField_hold {T κ b w₁ : ℝ} (hw₁ : 0 < w₁) {J : Set ℝ} (hJ : IsOpen J)
    (initial : ℝ → ℝ) {stock : Field} (hs : ContDiffOn ℝ ∞ stock (logDomain J hJ).carrier)
    {a y η : ℝ} (ha : b + w₁ ≤ a) (hay : a ≤ y) (hη : η ∈ J) :
    axialField T κ b w₁ initial stock (y, η) = axialField T κ b w₁ initial stock (a, η) := by
  unfold axialField
  simpa only [mul_zero, add_zero] using integrate_affine_after hJ initial
    (axialSlope_smooth T κ b w₁ hJ hs) hay hη
    (fun t ht => axialSlope_after hw₁ stock (ha.trans ht))

/-- Genuine reference profiles, with their positive-radius logarithmic
chart.  The two controls below are defined from their actual lag integrals. -/
structure StockReference (J : Set ℝ) where
  exponent : ℝ
  radius0 : ℝ
  radius0_pos : 0 < radius0
  domain : RadialDomain
  profiles : Profiles domain
  log_mem : ∀ y η, η ∈ J → (radius radius0 y, η) ∈ domain.carrier
  f_pos : ∀ y η, η ∈ J → 0 < profiles.f (radius radius0 y, η)
  L_ne_zero : ∀ η ∈ J, NaturalAxisData.L exponent η ≠ 0

namespace StockReference

variable {J : Set ℝ} (R : StockReference J)

noncomputable def chart (p : Point) : Point := (radius R.radius0 p.1, p.2)

theorem chart_smooth : ContDiff ℝ ∞ R.chart :=
  ((radius_smooth R.radius0).comp contDiff_fst).prodMk contDiff_snd

theorem chart_radius_pos (p : Point) : 0 < (R.chart p).1 :=
  mul_pos R.radius0_pos (Real.exp_pos _)

noncomputable def angularStock : Field := fun p =>
  ActivationStocks.profileStockOne R.profiles R.exponent (R.chart p)

/-- This is `X * ns_REF`, including the radial factor in the axial ODE. -/
noncomputable def axialStock : Field := fun p =>
  (R.chart p).1 * R.profiles.axialLag R.exponent (R.chart p) /
    NaturalAxisData.L R.exponent p.2

noncomputable def initialLog (η : ℝ) : ℝ := Real.log (R.profiles.f (R.radius0, η))
noncomputable def initialU (η : ℝ) : ℝ := R.profiles.U (R.radius0, η)

theorem angularStock_smooth (hJ : IsOpen J) :
    ContDiffOn ℝ ∞ R.angularStock (logDomain J hJ).carrier := by
  intro p hp
  have hm := R.log_mem p.1 p.2 hp.2
  have hf := R.f_pos p.1 p.2 hp.2
  have hx := R.chart_radius_pos p
  have hlag := (R.profiles.angularLag_smoothAt R.exponent hm hx.ne'
    (R.profiles.H_ne_zero hx.ne' hf.ne')).comp p R.chart_smooth.contDiffAt
  have hL : ContDiffAt ℝ ∞ (fun q : Point => NaturalAxisData.L R.exponent q.2) p := by
    unfold NaturalAxisData.L
    exact contDiffAt_const.sub (contDiffAt_const.mul (contDiffAt_snd.pow 2))
  exact ((R.chart_smooth.contDiffAt.fst.mul hlag).div hL
    (R.L_ne_zero p.2 hp.2)).contDiffWithinAt

theorem axialStock_smooth (hJ : IsOpen J) :
    ContDiffOn ℝ ∞ R.axialStock (logDomain J hJ).carrier := by
  intro p hp
  have hlag := (R.profiles.axialLag_smoothAt R.exponent (R.log_mem p.1 p.2 hp.2)
    (R.chart_radius_pos p).ne').comp p R.chart_smooth.contDiffAt
  have hL : ContDiffAt ℝ ∞ (fun q : Point => NaturalAxisData.L R.exponent q.2) p := by
    unfold NaturalAxisData.L
    exact contDiffAt_const.sub (contDiffAt_const.mul (contDiffAt_snd.pow 2))
  exact ((R.chart_smooth.contDiffAt.fst.mul hlag).div hL
    (R.L_ne_zero p.2 hp.2)).contDiffWithinAt

theorem initialLog_smooth (_hJ : IsOpen J) : ContDiffOn ℝ ∞ R.initialLog J := by
  intro η hη
  have hm : (R.radius0, η) ∈ R.domain.carrier := by
    simpa only [radius, Real.exp_zero, mul_one] using R.log_mem 0 η hη
  have hf : 0 < R.profiles.f (R.radius0, η) := by
    simpa only [radius, Real.exp_zero, mul_one] using R.f_pos 0 η hη
  exact (((R.profiles.f_smooth.contDiffAt (R.domain.isOpen.mem_nhds hm)).comp η
    (contDiffAt_const.prodMk contDiffAt_id)).log hf.ne').contDiffWithinAt

theorem initialU_smooth (_hJ : IsOpen J) : ContDiffOn ℝ ∞ R.initialU J := by
  intro η hη
  have hm : (R.radius0, η) ∈ R.domain.carrier := by
    simpa only [radius, Real.exp_zero, mul_one] using R.log_mem 0 η hη
  exact ((R.profiles.U_smooth.contDiffAt (R.domain.isOpen.mem_nhds hm)).comp η
    (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt

noncomputable def bigTime : ℝ := Real.log (100 / R.radius0)
noncomputable def finalTime : ℝ := Real.log (110 / R.radius0)

noncomputable def logAmplitude (T κ w₁ w₂ : ℝ) : Field :=
  logField T κ R.bigTime w₁ w₂ R.initialLog R.angularStock

noncomputable def axialVelocity (T κ w₁ : ℝ) : Field :=
  axialField T κ R.bigTime w₁ R.initialU R.axialStock

theorem logAmplitude_smooth (hJ : IsOpen J) (T κ w₁ w₂ : ℝ) :
    ContDiffOn ℝ ∞ (R.logAmplitude T κ w₁ w₂) (logDomain J hJ).carrier :=
  logField_smooth T κ R.bigTime w₁ w₂ hJ (R.initialLog_smooth hJ) (R.angularStock_smooth hJ)

theorem axialVelocity_smooth (hJ : IsOpen J) (T κ w₁ : ℝ) :
    ContDiffOn ℝ ∞ (R.axialVelocity T κ w₁) (logDomain J hJ).carrier :=
  axialField_smooth T κ R.bigTime w₁ hJ (R.initialU_smooth hJ) (R.axialStock_smooth hJ)

theorem logAmplitude_hasDerivAt (hJ : IsOpen J) (T κ w₁ w₂ y : ℝ) {η : ℝ} (hη : η ∈ J) :
    HasDerivAt (fun x => R.logAmplitude T κ w₁ w₂ (x, η))
      (angularSlope T κ R.bigTime w₁ w₂ R.angularStock (y, η)) y :=
  integrate_hasDerivAt hJ R.initialLog (angularSlope_smooth T κ R.bigTime w₁ w₂ hJ
    (R.angularStock_smooth hJ)) y hη

theorem axialVelocity_hasDerivAt (hJ : IsOpen J) (T κ w₁ y : ℝ) {η : ℝ} (hη : η ∈ J) :
    HasDerivAt (fun x => R.axialVelocity T κ w₁ (x, η))
      (axialSlope T κ R.bigTime w₁ R.axialStock (y, η)) y :=
  integrate_hasDerivAt hJ R.initialU (axialSlope_smooth T κ R.bigTime w₁ hJ
    (R.axialStock_smooth hJ)) y hη

theorem prescribed_angular_control (hJ : IsOpen J) (T κ w₁ w₂ y : ℝ)
    {η : ℝ} (hη : η ∈ J) :
    -2 * deriv (fun x => R.logAmplitude T κ w₁ w₂ (x, η)) y =
      (1 - step (R.bigTime + w₁) w₂ y) * damping T κ y * R.angularStock (y, η) +
        (4 / 5 : ℝ) * step (R.bigTime + w₁) w₂ y := by
  rw [(R.logAmplitude_hasDerivAt hJ T κ w₁ w₂ y hη).deriv]
  unfold angularSlope baseSlope
  ring

theorem prescribed_axial_control (hJ : IsOpen J) (T κ w₁ y : ℝ)
    {η : ℝ} (hη : η ∈ J) :
    deriv (fun x => R.axialVelocity T κ w₁ (x, η)) y =
      -(1 - step R.bigTime w₁ y) * damping T κ y * R.axialStock (y, η) / 2 := by
  rw [(R.axialVelocity_hasDerivAt hJ T κ w₁ y hη).deriv]
  unfold axialSlope baseSlope
  ring

/-- On the final hold the physical logarithmic slope `l` is exactly `3/5`. -/
theorem final_logarithmic_slope (hJ : IsOpen J) {T κ w₁ w₂ y η : ℝ}
    (hw₂ : 0 < w₂) (hy : R.bigTime + w₁ + w₂ ≤ y) (hη : η ∈ J) :
    1 + deriv (fun x => R.logAmplitude T κ w₁ w₂ (x, η)) y = (3 / 5 : ℝ) := by
  rw [(R.logAmplitude_hasDerivAt hJ T κ w₁ w₂ y hη).deriv,
    angularSlope_after hw₂ R.angularStock hy]
  norm_num

end StockReference

/-! ## Actual parameter jets of the integral controls -/

noncomputable def parameterJet : ℕ → Field → Field
  | 0, F => F
  | n + 1, F => parameterPartial (parameterJet n F)

theorem parameterJet_smooth {J : Set ℝ} (hJ : IsOpen J) {F : Field}
    (hF : ContDiffOn ℝ ∞ F (logDomain J hJ).carrier) (n : ℕ) :
    ContDiffOn ℝ ∞ (parameterJet n F) (logDomain J hJ).carrier := by
  induction n with
  | zero => exact hF
  | succ n ih => exact parameterPartial_smooth (logDomain J hJ) ih

theorem parameterJet_eq_iteratedDeriv {J : Set ℝ} (hJ : IsOpen J) {F : Field}
    (hF : ContDiffOn ℝ ∞ F (logDomain J hJ).carrier) (n : ℕ) {p : Point} (hp : p.2 ∈ J) :
    parameterJet n F p = iteratedDeriv n (fun η => F (p.1, η)) p.2 := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    have he : (fun η => parameterJet n F (p.1, η)) =ᶠ[𝓝 p.2]
        iteratedDeriv n (fun η => F (p.1, η)) := by
      filter_upwards [hJ.mem_nhds hp] with η hη
      exact ih hη
    rw [parameterJet, iteratedDeriv_succ]
    exact (parameterPartial_hasDerivAt (logDomain J hJ) (parameterJet_smooth hJ hF n)
      (p := p) ⟨mem_univ _, hp⟩).deriv.symm.trans he.deriv_eq

theorem parameterPartial_congr {J : Set ℝ} (hJ : IsOpen J) {F G : Field}
    (he : ∀ p, p.2 ∈ J → F p = G p) {p : Point} (hp : p.2 ∈ J) :
    parameterPartial F p = parameterPartial G p := by
  have hev : F =ᶠ[𝓝 p] G := by
    filter_upwards [continuousAt_snd.eventually (hJ.mem_nhds hp)] with q hq
    exact he q hq
  exact congrArg (fun A : Point →L[ℝ] ℝ => A (0, 1)) hev.fderiv_eq

theorem parameterJet_primitive {J : Set ℝ} (hJ : IsOpen J) {F : Field}
    (hF : ContDiffOn ℝ ∞ F (logDomain J hJ).carrier) (n : ℕ) {p : Point} (hp : p.2 ∈ J) :
    parameterJet n (primitive F) p = primitive (parameterJet n F) p := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    rw [parameterJet,
      parameterPartial_congr hJ (fun q hq => ih hq) hp,
      parameterPartial_primitive (logDomain J hJ) (parameterJet_smooth hJ hF n)
        (p := p) ⟨mem_univ _, hp⟩]
    rfl

theorem parameterJet_mul_radial {J : Set ℝ} (hJ : IsOpen J) {F : Field}
    (hF : ContDiffOn ℝ ∞ F (logDomain J hJ).carrier) {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (n : ℕ)
    {p : Point} (hp : p.2 ∈ J) :
    parameterJet n (fun q => g q.1 * F q) p = g p.1 * parameterJet n F p := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    rw [parameterJet, parameterPartial_congr hJ
      (fun q hq => ih hq) hp]
    have hd := (parameterPartial_hasDerivAt (logDomain J hJ) (parameterJet_smooth hJ hF n)
      (p := p) ⟨mem_univ _, hp⟩).const_mul (g p.1)
    exact (parameterPartial_hasDerivAt (logDomain J hJ)
      ((hg.comp contDiff_fst).contDiffOn.mul (parameterJet_smooth hJ hF n))
        (p := p) ⟨mem_univ _, hp⟩).unique hd

theorem parameterJet_congr {J : Set ℝ} (hJ : IsOpen J) {F G : Field}
    (he : ∀ p, p.2 ∈ J → F p = G p) (n : ℕ) {p : Point} (hp : p.2 ∈ J) :
    parameterJet n F p = parameterJet n G p := by
  induction n generalizing p with
  | zero => exact he p hp
  | succ n ih => exact parameterPartial_congr hJ (fun _ hq => ih hq) hp

theorem parameterJet_sub {J : Set ℝ} (hJ : IsOpen J) {F G : Field}
    (hF : ContDiffOn ℝ ∞ F (logDomain J hJ).carrier)
    (hG : ContDiffOn ℝ ∞ G (logDomain J hJ).carrier) (n : ℕ)
    {p : Point} (hp : p.2 ∈ J) :
    parameterJet n (fun q => F q - G q) p = parameterJet n F p - parameterJet n G p := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    rw [parameterJet, parameterPartial_congr hJ (fun q hq => ih hq) hp]
    exact (parameterPartial_hasDerivAt (logDomain J hJ)
      ((parameterJet_smooth hJ hF n).sub (parameterJet_smooth hJ hG n))
        (p := p) ⟨mem_univ _, hp⟩).unique
      ((parameterPartial_hasDerivAt (logDomain J hJ) (parameterJet_smooth hJ hF n)
        (p := p) ⟨mem_univ _, hp⟩).sub
        (parameterPartial_hasDerivAt (logDomain J hJ) (parameterJet_smooth hJ hG n)
          (p := p) ⟨mem_univ _, hp⟩))

theorem parameterJet_radial {J : Set ℝ} (hJ : IsOpen J) {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (n : ℕ) {p : Point} (hp : p.2 ∈ J) :
    parameterJet n (fun q => g q.1) p = if n = 0 then g p.1 else 0 := by
  rw [parameterJet_eq_iteratedDeriv hJ (F := fun q => g q.1)
    (hg.comp contDiff_fst).contDiffOn n hp]
  cases n with
  | zero => rfl
  | succ n =>
    simp only [Nat.succ_ne_zero, ↓reduceIte, iteratedDeriv_succ']
    rw [show deriv (fun _ : ℝ => g p.1) = (fun _ => 0) by funext x; exact deriv_const x _]
    exact congrFun (ReferencePath.Input.iteratedDeriv_zero_function n) p.2

theorem integral_norm_bound {F : ℝ → ℝ} {a b M : ℝ} (hab : a ≤ b)
    (hb : ∀ t ∈ Icc a b, |F t| ≤ M) : |∫ t in a..b, F t| ≤ M * (b - a) := by
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := M) (f := F) (fun t ht => by
      rw [Real.norm_eq_abs]
      exact hb t ⟨(uIoc_of_le hab ▸ ht).1.le, (uIoc_of_le hab ▸ ht).2⟩)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] using hi

/-- An initial layer contributes only its width, even at later radii. -/
theorem initial_layer_bound {F : ℝ → ℝ} (hF : Continuous F) {T y M : ℝ}
    (hT : 0 ≤ T) (hy : 0 ≤ y) (hM : 0 ≤ M)
    (hb : ∀ t ∈ Icc (0 : ℝ) y, |F t| ≤ M)
    (hz : ∀ t ∈ Icc T y, F t = 0) :
    |∫ t in (0 : ℝ)..y, F t| ≤ M * T := by
  by_cases hyt : y ≤ T
  · have hi : |∫ t in (0 : ℝ)..y, F t| ≤ M * y := by
      simpa only [sub_zero] using integral_norm_bound hy hb
    exact hi.trans (mul_le_mul_of_nonneg_left hyt hM)
  · have hTy : T ≤ y := (lt_of_not_ge hyt).le
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hF.intervalIntegrable 0 T) (hF.intervalIntegrable T y)
    have hzero : (∫ t in T..y, F t) = 0 := by
      calc
        _ = ∫ _t in T..y, (0 : ℝ) :=
          intervalIntegral.integral_congr (fun t ht => hz t (uIcc_of_le hTy ▸ ht))
        _ = 0 := by simp
    rw [hzero, add_zero] at hsplit
    rw [← hsplit]
    simpa only [sub_zero] using integral_norm_bound hT
      (fun t ht => hb t ⟨ht.1, ht.2.trans hTy⟩)

/-- A modification supported after `a` contributes only the traversed
width; the estimate applies before, during, and at the end of its ramp. -/
theorem late_layer_bound {F : ℝ → ℝ} (hF : Continuous F) {a y w M : ℝ}
    (ha : 0 ≤ a) (hy : 0 ≤ y) (hyw : y ≤ a + w) (hw : 0 ≤ w) (hM : 0 ≤ M)
    (hb : ∀ t ∈ Icc (0 : ℝ) y, |F t| ≤ M)
    (hz : ∀ t ∈ Icc (0 : ℝ) a, F t = 0) :
    |∫ t in (0 : ℝ)..y, F t| ≤ M * w := by
  by_cases hya : y ≤ a
  · have hi : (∫ t in (0 : ℝ)..y, F t) = 0 := by
      calc
        _ = ∫ _t in (0 : ℝ)..y, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [uIcc_of_le hy] at ht
          exact hz t ⟨ht.1, ht.2.trans hya⟩
        _ = 0 := by simp
    rw [hi, abs_zero]
    exact mul_nonneg hM hw
  · have hay : a ≤ y := (lt_of_not_ge hya).le
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hF.intervalIntegrable 0 a) (hF.intervalIntegrable a y)
    have hzero : (∫ t in (0 : ℝ)..a, F t) = 0 := by
      calc
        _ = ∫ _t in (0 : ℝ)..a, (0 : ℝ) :=
          intervalIntegral.integral_congr (fun t ht => hz t (uIcc_of_le ha ▸ ht))
        _ = 0 := by simp
    rw [hzero, zero_add] at hsplit
    rw [← hsplit]
    exact (integral_norm_bound hay (fun t ht => hb t ⟨ha.trans ht.1, ht.2⟩)).trans
      (mul_le_mul_of_nonneg_left (by linarith) hM)

theorem parameterJet_baseSlope {J : Set ℝ} (hJ : IsOpen J) {stock : Field}
    (hs : ContDiffOn ℝ ∞ stock (logDomain J hJ).carrier) (T κ : ℝ) (n : ℕ)
    {p : Point} (hp : p.2 ∈ J) :
    parameterJet n (baseSlope T κ stock) p = -(damping T κ p.1 * parameterJet n stock p) / 2 := by
  have he : baseSlope T κ stock = fun q => (-(damping T κ q.1) / 2) * stock q := by
    funext q
    unfold baseSlope
    ring
  rw [he, parameterJet_mul_radial hJ hs ((damping_smooth T κ).neg.div_const 2) n hp]
  ring

theorem parameterJet_axialSlope {J : Set ℝ} (hJ : IsOpen J) {stock : Field}
    (hs : ContDiffOn ℝ ∞ stock (logDomain J hJ).carrier) (T κ b w : ℝ) (n : ℕ)
    {p : Point} (hp : p.2 ∈ J) :
    parameterJet n (axialSlope T κ b w stock) p =
      (1 - step b w p.1) * (-(damping T κ p.1 * parameterJet n stock p) / 2) := by
  unfold axialSlope
  rw [parameterJet_mul_radial hJ (baseSlope_smooth T κ hJ hs)
    (contDiff_const.sub (step_smooth b w)) n hp, parameterJet_baseSlope hJ hs T κ n hp]

theorem parameterJet_angularSlope {J : Set ℝ} (hJ : IsOpen J) {stock : Field}
    (hs : ContDiffOn ℝ ∞ stock (logDomain J hJ).carrier) (T κ b w₁ w₂ : ℝ) (n : ℕ)
    {p : Point} (hp : p.2 ∈ J) :
    parameterJet n (angularSlope T κ b w₁ w₂ stock) p =
      (1 - step (b + w₁) w₂ p.1) * (-(damping T κ p.1 * parameterJet n stock p) / 2) -
        if n = 0 then (2 / 5 : ℝ) * step (b + w₁) w₂ p.1 else 0 := by
  have hc : ContDiff ℝ ∞ (fun y => (2 / 5 : ℝ) * step (b + w₁) w₂ y) :=
    contDiff_const.mul (step_smooth (b + w₁) w₂)
  unfold angularSlope
  rw [parameterJet_sub hJ
    (F := fun p => (1 - step (b + w₁) w₂ p.1) * baseSlope T κ stock p)
    (G := fun p => (2 / 5 : ℝ) * step (b + w₁) w₂ p.1)
    ((contDiffOn_const.sub ((step_smooth (b + w₁) w₂).comp contDiff_fst).contDiffOn).mul
      (baseSlope_smooth T κ hJ hs)) (hc.comp contDiff_fst).contDiffOn n hp,
    parameterJet_mul_radial hJ (baseSlope_smooth T κ hJ hs)
      (contDiff_const.sub (step_smooth (b + w₁) w₂)) n hp,
    parameterJet_baseSlope hJ hs T κ n hp,
    parameterJet_radial hJ hc n hp]

theorem integrate_error_jet {J : Set ℝ} (hJ : IsOpen J) (initial : ℝ → ℝ) {slope : Field}
    (hs : ContDiffOn ℝ ∞ slope (logDomain J hJ).carrier) (n : ℕ) (y : ℝ)
    {η : ℝ} (hη : η ∈ J) :
    iteratedDeriv n (fun ξ => integrate initial slope (y, ξ) - initial ξ) η =
      ∫ t in (0 : ℝ)..y, parameterJet n slope (t, η) := by
  have he : (fun ξ => integrate initial slope (y, ξ) - initial ξ) =
      fun ξ => primitive slope (y, ξ) := by
    funext ξ
    simp only [integrate, add_sub_cancel_left]
  rw [he, ← parameterJet_eq_iteratedDeriv hJ (primitive_smooth (logDomain J hJ) hs) n
      (p := (y, η)) hη,
    parameterJet_primitive hJ hs n hη]
  rfl

/-- Integrating the actual damping gives a bound proportional to the
activation width plus the retained constant control. -/
theorem damped_integral_bound {F : ℝ → ℝ} (hF : Continuous F) {T κ y M : ℝ}
    (hT : 0 < T) (hκ : κ ∈ Icc (0 : ℝ) 1) (hy : 0 ≤ y) (hM : 0 ≤ M)
    (hb : ∀ t ∈ Icc (0 : ℝ) y, |F t| ≤ damping T κ t * M) :
    |∫ t in (0 : ℝ)..y, F t| ≤ M * (T + κ * y) := by
  have hbM (t : ℝ) (ht : t ∈ Icc (0 : ℝ) y) : |F t| ≤ M :=
    (hb t ht).trans (mul_le_of_le_one_left hM (damping_mem T hκ t).2)
  by_cases hyt : y ≤ T
  · have hi : |∫ t in (0 : ℝ)..y, F t| ≤ M * y := by
      simpa only [sub_zero] using integral_norm_bound hy hbM
    exact hi.trans (mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hκ.1 hy]) hM)
  · have hTy : T ≤ y := (lt_of_not_ge hyt).le
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hF.intervalIntegrable 0 T) (hF.intervalIntegrable T y)
    rw [← hsplit]
    have hfirst : |∫ t in (0 : ℝ)..T, F t| ≤ M * T := by
      simpa only [sub_zero] using integral_norm_bound hT.le
        (fun t ht => hbM t ⟨ht.1, ht.2.trans hTy⟩)
    have hlast : |∫ t in T..y, F t| ≤ (κ * M) * (y - T) := by
      apply integral_norm_bound hTy
      intro t ht
      simpa only [damping_eq_constant hT κ ht.1] using hb t ⟨hT.le.trans ht.1, ht.2⟩
    calc
      _ ≤ |∫ t in (0 : ℝ)..T, F t| + |∫ t in T..y, F t| := abs_add_le _ _
      _ ≤ M * T + (κ * M) * (y - T) := add_le_add hfirst hlast
      _ ≤ M * (T + κ * y) := by nlinarith [mul_nonneg (mul_nonneg hκ.1 hM) hT.le]

theorem jet_slice_continuous {J : Set ℝ} (hJ : IsOpen J) {F : Field}
    (hF : ContDiffOn ℝ ∞ F (logDomain J hJ).carrier) (n : ℕ) {η : ℝ} (hη : η ∈ J) :
    Continuous (fun t => parameterJet n F (t, η)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact ((parameterJet_smooth hJ hF n).contDiffAt
    ((logDomain J hJ).isOpen.mem_nhds ⟨mem_univ _, hη⟩)).continuousAt.comp
      (continuousAt_id.prodMk continuousAt_const)

theorem compact_stock_jet_bound {J K : Set ℝ} (hJ : IsOpen J) (hK : IsCompact K)
    (hKJ : K ⊆ J) {stock : Field}
    (hs : ContDiffOn ℝ ∞ stock (logDomain J hJ).carrier) (R : ℝ) (N : ℕ) :
    ∃ M ≥ 0, ∀ n ≤ N, ∀ t ∈ Icc (0 : ℝ) R, ∀ η ∈ K,
      |parameterJet n stock (t, η)| ≤ M := by
  have hex (n : ℕ) : ∃ M ≥ 0, ∀ t ∈ Icc (0 : ℝ) R, ∀ η ∈ K,
      |parameterJet n stock (t, η)| ≤ M := by
    obtain ⟨M, hM⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
      ((parameterJet_smooth hJ hs n).continuousOn.mono (fun _ hp => ⟨mem_univ _, hKJ hp.2⟩))
    refine ⟨max M 0, le_max_right _ _, ?_⟩
    intro t ht η hη
    have hm : |parameterJet n stock (t, η)| ≤ M := by
      simpa only [Real.norm_eq_abs] using hM (t, η) ⟨ht, hη⟩
    exact hm.trans (le_max_left _ _)
  induction N with
  | zero =>
    obtain ⟨M, hM, hb⟩ := hex 0
    exact ⟨M, hM, fun n hn => by have : n = 0 := Nat.eq_zero_of_le_zero hn; subst n; exact hb⟩
  | succ N ih =>
    obtain ⟨M, hM, hb⟩ := ih
    obtain ⟨M', hM', hb'⟩ := hex (N + 1)
    refine ⟨max M M', hM.trans (le_max_left _ _), ?_⟩
    intro n hn t ht η hη
    rcases Nat.eq_or_lt_of_le hn with he | hn'
    · subst n
      exact (hb' t ht η hη).trans (le_max_right _ _)
    · exact (hb n (Nat.le_of_lt_succ hn') t ht η hη).trans (le_max_left _ _)

theorem controlled_product_bound {a d z M : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hd : 0 ≤ d) (hM : 0 ≤ M) (hz : |z| ≤ M) : |a * (-(d * z) / 2)| ≤ d * M := by
  rw [abs_mul, abs_of_nonneg ha.1, abs_div, abs_neg, abs_mul, abs_of_nonneg hd]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hza : a * |z| ≤ M :=
    (mul_le_mul_of_nonneg_left hz ha.1).trans (mul_le_of_le_one_left hM ha.2)
  nlinarith [mul_le_mul_of_nonneg_left hza hd, mul_nonneg hd hM]

theorem axialField_jet_error_bound {J : Set ℝ} (hJ : IsOpen J) {stock : Field}
    (hs : ContDiffOn ℝ ∞ stock (logDomain J hJ).carrier) (initial : ℝ → ℝ)
    {T κ b w y η M : ℝ} (hT : 0 < T) (hκ : κ ∈ Icc (0 : ℝ) 1)
    (hy : 0 ≤ y) (hη : η ∈ J) (hM : 0 ≤ M) (n : ℕ)
    (hb : ∀ t ∈ Icc (0 : ℝ) y, |parameterJet n stock (t, η)| ≤ M) :
    |iteratedDeriv n (fun ξ => axialField T κ b w initial stock (y, ξ) - initial ξ) η| ≤
      M * (T + κ * y) := by
  rw [axialField, integrate_error_jet hJ initial (axialSlope_smooth T κ b w hJ hs) n y hη]
  apply damped_integral_bound (jet_slice_continuous hJ (axialSlope_smooth T κ b w hJ hs) n hη)
    hT hκ hy hM
  intro t ht
  rw [parameterJet_axialSlope hJ hs T κ b w n hη]
  apply controlled_product_bound _ (damping_mem T hκ t).1 hM (hb t ht)
  have hstep := step_mem b w t
  constructor <;> linarith [hstep.1, hstep.2]

theorem logField_positive_jet_error_bound {J : Set ℝ} (hJ : IsOpen J) {stock : Field}
    (hs : ContDiffOn ℝ ∞ stock (logDomain J hJ).carrier) (initial : ℝ → ℝ)
    {T κ b w₁ w₂ y η M : ℝ} (hT : 0 < T) (hκ : κ ∈ Icc (0 : ℝ) 1)
    (hy : 0 ≤ y) (hη : η ∈ J) (hM : 0 ≤ M) {n : ℕ} (hn : n ≠ 0)
    (hb : ∀ t ∈ Icc (0 : ℝ) y, |parameterJet n stock (t, η)| ≤ M) :
    |iteratedDeriv n (fun ξ => logField T κ b w₁ w₂ initial stock (y, ξ) - initial ξ) η| ≤
      M * (T + κ * y) := by
  rw [logField, integrate_error_jet hJ initial (angularSlope_smooth T κ b w₁ w₂ hJ hs) n y hη]
  apply damped_integral_bound
    (jet_slice_continuous hJ (angularSlope_smooth T κ b w₁ w₂ hJ hs) n hη) hT hκ hy hM
  intro t ht
  rw [parameterJet_angularSlope hJ hs T κ b w₁ w₂ n hη, ite_eq_right hn, sub_zero]
  apply controlled_product_bound _ (damping_mem T hκ t).1 hM (hb t ht)
  have hstep := step_mem (b + w₁) w₂ t
  constructor <;> linarith [hstep.1, hstep.2]

theorem logField_value_error_bound {J : Set ℝ} (hJ : IsOpen J) {stock : Field}
    (hs : ContDiffOn ℝ ∞ stock (logDomain J hJ).carrier) (initial : ℝ → ℝ)
    {T κ b w₁ w₂ y η M : ℝ} (hT : 0 < T) (hκ : κ ∈ Icc (0 : ℝ) 1)
    (hb0 : 0 ≤ b) (hw₁ : 0 ≤ w₁) (hw₂ : 0 < w₂)
    (hy : 0 ≤ y) (hyend : y ≤ b + w₁ + w₂) (hη : η ∈ J) (hM : 0 ≤ M)
    (hb : ∀ t ∈ Icc (0 : ℝ) y, |stock (t, η)| ≤ M) :
    |logField T κ b w₁ w₂ initial stock (y, η) - initial η| ≤
      M * (T + κ * y) + (2 / 5 : ℝ) * (w₁ + w₂) := by
  let A : ℝ → ℝ := fun t => (1 - step (b + w₁) w₂ t) * baseSlope T κ stock (t, η)
  let B : ℝ → ℝ := fun t => (2 / 5 : ℝ) * step (b + w₁) w₂ t
  have hA : Continuous A := ((continuous_const.sub (step_smooth (b + w₁) w₂).continuous).mul
    (jet_slice_continuous hJ (baseSlope_smooth T κ hJ hs) 0 hη))
  have hB : Continuous B := continuous_const.mul (step_smooth (b + w₁) w₂).continuous
  have hAbound : |∫ t in (0 : ℝ)..y, A t| ≤ M * (T + κ * y) := by
    apply damped_integral_bound hA hT hκ hy hM
    intro t ht
    apply controlled_product_bound _ (damping_mem T hκ t).1 hM (hb t ht)
    have hstep := step_mem (b + w₁) w₂ t
    constructor <;> linarith [hstep.1, hstep.2]
  have hBbound : |∫ t in (0 : ℝ)..y, B t| ≤ (2 / 5 : ℝ) * (w₁ + w₂) := by
    apply late_layer_bound hB hb0 hy (by linarith) (by linarith) (by norm_num)
    · intro t _
      dsimp [B]
      rw [abs_mul, abs_of_nonneg (step_mem (b + w₁) w₂ t).1,
        abs_of_pos (by norm_num : (0 : ℝ) < 2 / 5)]
      nlinarith [(step_mem (b + w₁) w₂ t).2]
    · intro t ht
      dsimp [B]
      rw [step_zero hw₂ (show t ≤ b + w₁ by linarith [ht.2]), mul_zero]
  have he : logField T κ b w₁ w₂ initial stock (y, η) - initial η =
      (∫ t in (0 : ℝ)..y, A t) - ∫ t in (0 : ℝ)..y, B t := by
    simp only [logField, integrate, add_sub_cancel_left, primitive, angularSlope]
    exact intervalIntegral.integral_sub (hA.intervalIntegrable 0 y) (hB.intervalIntegrable 0 y)
  rw [he]
  exact (abs_sub _ _).trans (add_le_add hAbound hBbound)

/-! ## Instantiation by the constructed natural profiles -/

namespace StockReference

variable {J : Set ℝ} (R : StockReference J)

noncomputable def logTime (X : ℝ) : ℝ := Real.log (X / R.radius0)
noncomputable def logPoint (p : Point) : Point := (R.logTime p.1, p.2)

theorem logPoint_smoothAt {p : Point} (hX : 0 < p.1) : ContDiffAt ℝ ∞ R.logPoint p :=
  ((contDiffAt_fst.div_const R.radius0).log (div_ne_zero hX.ne' R.radius0_pos.ne')).prodMk
    contDiffAt_snd

theorem logTime_chart (y : ℝ) : R.logTime (radius R.radius0 y) = y := by
  simp only [logTime, radius, mul_div_cancel_left₀ _ R.radius0_pos.ne', Real.log_exp]

theorem chart_logTime {X η : ℝ} (hX : 0 < X) : R.chart (R.logTime X, η) = (X, η) := by
  ext
  · dsimp only [chart, radius, logTime]
    rw [Real.exp_log (div_pos hX R.radius0_pos), mul_div_cancel₀ _ R.radius0_pos.ne']
  · rfl

noncomputable def physicalF (T κ w₁ w₂ : ℝ) : Field := fun p =>
  if p.1 ≤ R.radius0 then R.profiles.f p else Real.exp (R.logAmplitude T κ w₁ w₂ (R.logPoint p))

noncomputable def physicalU (T κ w₁ : ℝ) : Field := fun p =>
  if p.1 ≤ R.radius0 then R.profiles.U p else R.axialVelocity T κ w₁ (R.logPoint p)

theorem physicalF_before (T κ w₁ w₂ : ℝ) {p : Point} (hp : p.1 ≤ R.radius0) :
    R.physicalF T κ w₁ w₂ p = R.profiles.f p := ite_eq_left hp

theorem physicalU_before (T κ w₁ : ℝ) {p : Point} (hp : p.1 ≤ R.radius0) :
    R.physicalU T κ w₁ p = R.profiles.U p := ite_eq_left hp

noncomputable def endpointU (T κ w₁ : ℝ) (η : ℝ) : ℝ :=
  R.axialVelocity T κ w₁ (R.finalTime, η)

noncomputable def endpointLog (T κ w₁ w₂ C : ℝ) (η : ℝ) : ℝ :=
  Real.log C + Real.log 220 / 2 + R.logAmplitude T κ w₁ w₂ (R.finalTime, η)

theorem endpointU_smooth (hJ : IsOpen J) (T κ w₁ : ℝ) :
    ContDiffOn ℝ ∞ (R.endpointU T κ w₁) J :=
  (R.axialVelocity_smooth hJ T κ w₁).comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun _ hη => ⟨mem_univ _, hη⟩)

theorem endpointLog_smooth (hJ : IsOpen J) (T κ w₁ w₂ C : ℝ) :
    ContDiffOn ℝ ∞ (R.endpointLog T κ w₁ w₂ C) J :=
  contDiffOn_const.add ((R.logAmplitude_smooth hJ T κ w₁ w₂).comp
    (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hη => ⟨mem_univ _, hη⟩))

end StockReference

section Natural

open NaturalProfile NaturalAxisBridge ReferencePath

variable {h j σ Λ C : ℝ} {P0 : ℝ → ℝ} {d : NaturalAxisCoefficients.AnalyticInputs h j σ P0}
    (F : ProfileFamily d Λ C) (hΛ : 0 < Λ) (hsmall : NaturalAxisData.SmallParameters h j)
    {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit) (hP0 : ContDiff ℝ ∞ P0)

theorem L_pos_parameterInterval {h j η : ℝ} (hs : NaturalAxisData.SmallParameters h j)
    (hη : η ∈ parameterInterval) : 0 < NaturalAxisData.L h η := by
  have hη' : -(11 / 10 : ℝ) < η ∧ η < 11 / 10 := by
    simpa only [parameterInterval, NaturalAxisCoefficients.window, mem_Ioo, neg_div] using hη
  have hsquare : η ^ 2 ≤ (121 / 100 : ℝ) := by
    nlinarith [mul_nonneg (show 0 ≤ η + 11 / 10 by linarith [hη'.1])
      (show 0 ≤ 11 / 10 - η by linarith [hη'.2])]
  have hm := mul_le_mul hs.h_le hsquare (sq_nonneg η) (by norm_num : (0 : ℝ) ≤ 1 / 1000)
  unfold NaturalAxisData.L
  nlinarith

/-- No stock or differential equation is postulated in this constructor:
the underlying profiles and all five histories are the completed REF path. -/
noncomputable def ofNatural : StockReference parameterInterval where
  exponent := h
  radius0 := (Input.ofNatural hΛ F).endpoint
  radius0_pos := (Input.ofNatural hΛ F).endpoint_pos
  domain := (Input.ofNatural hΛ F).radialDomain
  profiles := (Input.ofNatural hΛ F).histories hδ hδT P0 hP0
  log_mem := fun y _η hη => StressActivation.FromReference.log_radius_mem (Input.ofNatural hΛ F) y
    hη
  f_pos := fun y _η hη => (Input.ofNatural hΛ F).refF_pos δ
    (StressActivation.FromReference.log_radius_mem (Input.ofNatural hΛ F) y hη)
    (mul_pos (Input.ofNatural hΛ F).endpoint_pos (Real.exp_pos _)).le
  L_ne_zero := fun _ hη => (L_pos_parameterInterval hsmall hη).ne'

include hsmall in
theorem natural_stock_identity (y : ℝ) (hy : y ≤ δ) {η : ℝ} (hη : η ∈ parameterInterval) :
    let N := Input.ofNatural hΛ F
    let p := N.fromLog (y, η)
    ActivationStocks.profileStockOne (N.histories hδ hδT P0 hP0) h p = NaturalEntrance.p1 F.f p ∧
      ActivationStocks.profileStockTwo (N.histories hδ hδT P0 hP0) h p = NaturalEntrance.p2 F.f F.U
        p := by
  let N := Input.ofNatural hΛ F
  let P := N.histories hδ hδT P0 hP0
  let Q := ActivationStocks.naturalHistories F hΛ hP0
  let p := N.fromLog (y, η)
  change ActivationStocks.profileStockOne P h p = NaturalEntrance.p1 F.f p ∧
    ActivationStocks.profileStockTwo P h p = NaturalEntrance.p2 F.f F.U p
  have hyT : y < rampLimit := by linarith
  have hp : p ∈ domain Λ := N.fromLog_mem ⟨hyT, hη⟩
  have hpN : p ∈ N.radialDomain.carrier := StressActivation.FromReference.log_radius_mem N y hη
  have hX : 0 < p.1 := mul_pos N.endpoint_pos (Real.exp_pos _)
  have hupper : p.1 ≤ N.endpoint * Real.exp δ :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hy) N.endpoint_pos.le
  have hfp : 0 < Q.f p := N.fromLog_f_pos ⟨hyT, hη⟩
  have hfields : P.f p = Q.f p := N.refF_eq_natural hδ hδT hη hupper
  have hUfields : P.U p = Q.U p := N.refU_eq_natural hδ hδT hη hupper
  have hrows : ∀ r ξ, ξ ∈ parameterInterval →
      profileHistory P r (p.1, ξ) = profileHistory Q r (p.1, ξ) := by
    intro r ξ hξ
    apply ActivationStocks.profileHistory_congr_across P Q r hX.le
    · cases r <;> rfl
    · intro x hx
      exact N.refF_eq_natural hδ hδT hξ (hx.2.trans hupper)
    · intro x hx
      exact N.refU_eq_natural hδ hδT hξ (hx.2.trans hupper)
  have hagree := ActivationStocks.profiles_stocks_congr P Q h parameterInterval_open hη
    hpN hp hX hfields hfp.ne' hUfields hrows
  have hY : Λ * p.1 ≤ 41 / 10 := by
    have he : Real.exp y < 41 / 40 := by
      simpa only [rampLimit, Real.exp_log (by norm_num : (0 : ℝ) < 41 / 40)] using
        Real.exp_lt_exp.mpr hyT
    rw [show Λ * p.1 = 4 * Real.exp y from N.fromLog_scaled (y, η)]
    linarith
  have hf : ∀ x ∈ uIcc (0 : ℝ) p.1, F.f (x, p.2) ≠ 0 := by
    intro x hx
    have hx' : x ∈ Icc (0 : ℝ) p.1 := by simpa only [uIcc_of_le hX.le] using hx
    exact (F.positive (x, p.2) (domain_segment hΛ hp hx) (mul_nonneg hΛ.le hx'.1)
      ((mul_le_mul_of_nonneg_left hx'.2 hΛ.le).trans hY)).ne'
  have hnat := ActivationStocks.naturalHistories_stocks F hΛ hP0 hp hX
    (L_pos_parameterInterval hsmall hη).ne' hf
  exact ⟨hagree.1.trans hnat.1, hagree.2.trans hnat.2⟩

theorem refLog_radial_natural (N : Input) {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    {p : Point} (hp : p.2 ∈ parameterInterval) (hy : p.1 ≤ δ) :
    radialPartial (StressActivation.FromReference.refLog N δ) p = radialPartial N.logF p := by
  have hd := continuation_hasDerivAt rampLimit_pos hδ hδT parameterInterval_open N.logF_smooth hp
  rw [slopeCutoff_one hδ hy, one_mul] at hd
  exact (radialPartial_hasDerivAt (logDomain parameterInterval parameterInterval_open)
    (StressActivation.FromReference.refLog_smooth N hδ hδT) (p := p) ⟨mem_univ _, hp⟩).unique hd

theorem refAxial_radial_natural (N : Input) {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    {p : Point} (hp : p.2 ∈ parameterInterval) (hy : p.1 ≤ δ) :
    radialPartial (StressActivation.FromReference.refAxial N δ) p = radialPartial N.logU p := by
  have hd := continuation_hasDerivAt rampLimit_pos hδ hδT parameterInterval_open N.logU_smooth hp
  rw [slopeCutoff_one hδ hy, one_mul] at hd
  exact (radialPartial_hasDerivAt (logDomain parameterInterval parameterInterval_open)
    (StressActivation.FromReference.refAxial_smooth N hδ hδT) (p := p) ⟨mem_univ _, hp⟩).unique hd

theorem ofNatural_stock_slopes (y : ℝ) (hy : y ≤ δ) {η : ℝ} (hη : η ∈ parameterInterval) :
    let R := ofNatural F hΛ hsmall hδ hδT hP0
    let N := Input.ofNatural hΛ F
    R.angularStock (y, η) = -2 * radialPartial (StressActivation.FromReference.refLog N δ) (y, η) ∧
      R.axialStock (y, η) = -2 * radialPartial (StressActivation.FromReference.refAxial N δ) (y, η)
        := by
  let N := Input.ofNatural hΛ F
  let R := ofNatural F hΛ hsmall hδ hδT hP0
  let p := N.fromLog (y, η)
  have hyT : y < rampLimit := by linarith
  have hp : p ∈ domain Λ := N.fromLog_mem ⟨hyT, hη⟩
  have hids := natural_stock_identity F hΛ hsmall hδ hδT hP0 y hy hη
  change ActivationStocks.profileStockOne (N.histories hδ hδT P0 hP0) h p = NaturalEntrance.p1 F.f
    p ∧
    ActivationStocks.profileStockTwo (N.histories hδ hδT P0 hP0) h p = NaturalEntrance.p2 F.f F.U p
      at hids
  have hxf := N.radialPartial_logF (p := (y, η)) ⟨hyT, hη⟩
  change radialPartial N.logF (y, η) = p.1 * radialPartial F.f p / F.f p at hxf
  have hxu := N.radialPartial_logU (p := (y, η)) ⟨hyT, hη⟩
  change radialPartial N.logU (y, η) = p.1 * radialPartial F.U p at hxu
  change R.angularStock (y, η) = -2 * radialPartial _ (y, η) ∧
    R.axialStock (y, η) = -2 * radialPartial _ (y, η)
  rw [refLog_radial_natural N hδ hδT hη hy, refAxial_radial_natural N hδ hδT hη hy]
  constructor
  · change ActivationStocks.profileStockOne (N.histories hδ hδT P0 hP0) h p = _
    rw [hids.1, hxf, ActivationStocks.radialPartial_natural_field hΛ (G := F.f) F.natural.f_smooth
      hp]
    unfold NaturalEntrance.p1
    ring
  · have hX : 0 < p.1 := mul_pos N.endpoint_pos (Real.exp_pos _)
    have hf : 0 < F.f p := N.fromLog_f_pos ⟨hyT, hη⟩
    have hupper : p.1 ≤ N.endpoint * Real.exp δ :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hy) N.endpoint_pos.le
    have he : (N.histories hδ hδT P0 hP0).E p = Real.sqrt (2 * p.1) * F.f p := by
      change Real.sqrt (2 * p.1) * N.refF δ p = _
      rw [N.refF_eq_natural hδ hδT hη hupper]
      rfl
    have hEn : Real.sqrt (2 * p.1) * F.f p ≠ 0 :=
      mul_ne_zero (Real.sqrt_pos.2 (by linarith)).ne' hf.ne'
    have hsecond := hids.2
    dsimp only [ActivationStocks.profileStockTwo, NaturalEntrance.p2,
      NaturalEntrance.angularVelocity] at hsecond
    rw [he] at hsecond
    change p.1 * (N.histories hδ hδT P0 hP0).axialLag h p / NaturalAxisData.L h η = _
    rw [hxu, ActivationStocks.radialPartial_natural_field hΛ (G := F.U) F.natural.U_smooth hp]
    have hsecond' : (p.1 * (N.histories hδ hδT P0 hP0).axialLag h p / NaturalAxisData.L h η) /
        (Real.sqrt (2 * p.1) * F.f p) = p.1 * NaturalEntrance.ns F.U p /
          (Real.sqrt (2 * p.1) * F.f p) := by
      have hh := hsecond
      simp only [div_div] at hh ⊢
      exact hh
    have hc := congrArg (fun z => z * (Real.sqrt (2 * p.1) * F.f p)) hsecond'
    rw [div_mul_cancel₀ _ hEn, div_mul_cancel₀ _ hEn] at hc
    rw [hc]
    unfold NaturalEntrance.ns
    ring

theorem ofNatural_initialLog {η : ℝ} (hη : η ∈ parameterInterval) :
    (ofNatural F hΛ hsmall hδ hδT hP0).initialLog η =
      StressActivation.FromReference.refLog (Input.ofNatural hΛ F) δ (0, η) := by
  let N := Input.ofNatural hΛ F
  change Real.log (N.refF δ (N.endpoint, η)) = StressActivation.FromReference.refLog N δ (0, η)
  rw [N.refF_eq_logtime hδ hδT hη N.endpoint_pos, Real.log_exp]
  have ht : N.logTime N.endpoint = 0 := by
    simp only [Input.logTime, div_self N.endpoint_pos.ne', Real.log_one]
  rw [ht]
  rfl

theorem ofNatural_initialU {η : ℝ} (hη : η ∈ parameterInterval) :
    (ofNatural F hΛ hsmall hδ hδT hP0).initialU η =
      StressActivation.FromReference.refAxial (Input.ofNatural hΛ F) δ (0, η) := by
  let N := Input.ofNatural hΛ F
  change N.refU δ (N.endpoint, η) = StressActivation.FromReference.refAxial N δ (0, η)
  rw [N.refU_eq_logtime hδ hδT hη N.endpoint_pos]
  have ht : N.logTime N.endpoint = 0 := by
    simp only [Input.logTime, div_self N.endpoint_pos.ne', Real.log_one]
  rw [ht]
  rfl

theorem base_integrals_eq_activation (T κ y : ℝ) (hy : y ≤ δ)
    {η : ℝ} (hη : η ∈ parameterInterval) :
    let R := ofNatural F hΛ hsmall hδ hδT hP0
    let N := Input.ofNatural hΛ F
    integrate R.initialLog (baseSlope T κ R.angularStock) (y, η) =
      controlled T κ (StressActivation.FromReference.refLog N δ) (y, η) ∧
    integrate R.initialU (baseSlope T κ R.axialStock) (y, η) =
      controlled T κ (StressActivation.FromReference.refAxial N δ) (y, η) := by
  let R := ofNatural F hΛ hsmall hδ hδT hP0
  let N := Input.ofNatural hΛ F
  have hiL := ofNatural_initialLog F hΛ hsmall hδ hδT hP0 hη
  have hiU := ofNatural_initialU F hΛ hsmall hδ hδT hP0 hη
  change integrate R.initialLog _ (y, η) = controlled T κ _ (y, η) ∧
    integrate R.initialU _ (y, η) = controlled T κ _ (y, η)
  constructor
  · unfold integrate controlled
    rw [hiL]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    have htδ := (mem_uIcc.mp ht).elim (fun h => h.2.trans hy) (fun h => h.2.trans hδ.le)
    have hstock := (ofNatural_stock_slopes F hΛ hsmall hδ hδT hP0 t htδ hη).1
    change -(damping T κ t * R.angularStock (t, η)) / 2 = _
    rw [hstock]
    ring
  · unfold integrate controlled
    rw [hiU]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    have htδ := (mem_uIcc.mp ht).elim (fun h => h.2.trans hy) (fun h => h.2.trans hδ.le)
    have hstock := (ofNatural_stock_slopes F hΛ hsmall hδ hδT hP0 t htδ hη).2
    change -(damping T κ t * R.axialStock (t, η)) / 2 = _
    rw [hstock]
    ring

theorem log_fields_eq_activation {T κ w₁ w₂ y : ℝ}
    (hb : δ ≤ (ofNatural F hΛ hsmall hδ hδT hP0).bigTime)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hy : y ≤ δ)
    {η : ℝ} (hη : η ∈ parameterInterval) :
    let R := ofNatural F hΛ hsmall hδ hδT hP0
    let N := Input.ofNatural hΛ F
    R.logAmplitude T κ w₁ w₂ (y, η) = controlled T κ (StressActivation.FromReference.refLog N δ)
      (y, η) ∧
    R.axialVelocity T κ w₁ (y, η) = controlled T κ (StressActivation.FromReference.refAxial N δ)
      (y, η) := by
  let R := ofNatural F hΛ hsmall hδ hδT hP0
  have hbase := base_integrals_eq_activation F hΛ hsmall hδ hδT hP0 T κ y hy hη
  change R.logAmplitude T κ w₁ w₂ (y, η) = _ ∧ R.axialVelocity T κ w₁ (y, η) = _
  constructor
  · change logField T κ R.bigTime w₁ w₂ R.initialLog R.angularStock (y, η) = _
    rw [logField_before (by linarith : 0 ≤ R.bigTime + w₁) hw₂ R.initialLog R.angularStock
      (by dsimp only; linarith : (y, η).1 ≤ R.bigTime + w₁)]
    exact hbase.1
  · change axialField T κ R.bigTime w₁ R.initialU R.axialStock (y, η) = _
    rw [axialField_before (hδ.le.trans hb) hw₁ R.initialU R.axialStock (hy.trans hb)]
    exact hbase.2

theorem physicalF_eq_log {T κ w₁ w₂ : ℝ} (hT : 0 < T)
    (hb : δ ≤ (ofNatural F hΛ hsmall hδ hδT hP0).bigTime)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) {p : Point}
    (hη : p.2 ∈ parameterInterval) (hX : 0 < p.1) :
    let R := ofNatural F hΛ hsmall hδ hδT hP0
    R.physicalF T κ w₁ w₂ p = Real.exp (R.logAmplitude T κ w₁ w₂ (R.logPoint p)) := by
  let N := Input.ofNatural hΛ F
  let R := ofNatural F hΛ hsmall hδ hδT hP0
  change R.physicalF T κ w₁ w₂ p = Real.exp (R.logAmplitude T κ w₁ w₂ (N.logTime p.1, p.2))
  by_cases hx : p.1 ≤ R.radius0
  · rw [R.physicalF_before T κ w₁ w₂ hx]
    have ht : N.logTime p.1 ≤ 0 := (N.logTime_le_iff hX).mpr
      (by simp only [Real.exp_zero, mul_one]; exact hx)
    rw [(log_fields_eq_activation F hΛ hsmall hδ hδT hP0 hb hw₁ hw₂
      (ht.trans hδ.le) hη).1]
    rw [controlled_eq_reference_before hT κ parameterInterval_open
      (StressActivation.FromReference.refLog_smooth N hδ hδT) ht hη]
    exact N.refF_eq_logtime hδ hδT hη hX
  · exact ite_eq_right hx

theorem physicalU_eq_log {T κ w₁ w₂ : ℝ} (hT : 0 < T)
    (hb : δ ≤ (ofNatural F hΛ hsmall hδ hδT hP0).bigTime)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) {p : Point}
    (hη : p.2 ∈ parameterInterval) (hX : 0 < p.1) :
    let R := ofNatural F hΛ hsmall hδ hδT hP0
    R.physicalU T κ w₁ p = R.axialVelocity T κ w₁ (R.logPoint p) := by
  let N := Input.ofNatural hΛ F
  let R := ofNatural F hΛ hsmall hδ hδT hP0
  change R.physicalU T κ w₁ p = R.axialVelocity T κ w₁ (N.logTime p.1, p.2)
  by_cases hx : p.1 ≤ R.radius0
  · rw [R.physicalU_before T κ w₁ hx]
    have ht : N.logTime p.1 ≤ 0 := (N.logTime_le_iff hX).mpr
      (by simp only [Real.exp_zero, mul_one]; exact hx)
    rw [(log_fields_eq_activation F hΛ hsmall hδ hδT hP0 hb hw₁ hw₂
      (ht.trans hδ.le) hη).2]
    rw [controlled_eq_reference_before hT κ parameterInterval_open
      (StressActivation.FromReference.refAxial_smooth N hδ hδT) ht hη]
    exact N.refU_eq_logtime hδ hδT hη hX
  · exact ite_eq_right hx

theorem physicalF_smooth {T κ w₁ w₂ : ℝ} (hT : 0 < T)
    (hb : δ ≤ (ofNatural F hΛ hsmall hδ hδT hP0).bigTime)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) :
    ContDiffOn ℝ ∞ ((ofNatural F hΛ hsmall hδ hδT hP0).physicalF T κ w₁ w₂)
      (Input.ofNatural hΛ F).radialDomain.carrier := by
  let R := ofNatural F hΛ hsmall hδ hδT hP0
  let N := Input.ofNatural hΛ F
  intro p hp
  by_cases hX : 0 < p.1
  · have hs := (((R.logAmplitude_smooth parameterInterval_open T κ w₁ w₂).contDiffAt
      ((logDomain parameterInterval parameterInterval_open).isOpen.mem_nhds
        (show R.logPoint p ∈ (logDomain parameterInterval parameterInterval_open).carrier from
          ⟨mem_univ _, hp.2⟩))).exp).comp p (R.logPoint_smoothAt hX)
    have he : R.physicalF T κ w₁ w₂ =ᶠ[𝓝 p]
        (fun q => Real.exp (R.logAmplitude T κ w₁ w₂ (R.logPoint q))) := by
      filter_upwards [continuousAt_fst.eventually (Ioi_mem_nhds hX),
        continuousAt_snd.eventually (parameterInterval_open.mem_nhds hp.2)] with q hqX hqη
      exact physicalF_eq_log F hΛ hsmall hδ hδT hP0 hT hb hw₁ hw₂ hqη hqX
    exact (hs.congr_of_eventuallyEq he).contDiffWithinAt
  · have hbefore : p.1 < R.radius0 := (le_of_not_gt hX).trans_lt R.radius0_pos
    have he : R.physicalF T κ w₁ w₂ =ᶠ[𝓝 p] R.profiles.f := by
      filter_upwards [continuousAt_fst.eventually (Iio_mem_nhds hbefore)] with q hq
      exact R.physicalF_before T κ w₁ w₂ hq.le
    exact ((R.profiles.f_smooth.contDiffAt (N.radialDomain.isOpen.mem_nhds
      hp)).congr_of_eventuallyEq he).contDiffWithinAt

theorem physicalU_smooth {T κ w₁ w₂ : ℝ} (hT : 0 < T)
    (hb : δ ≤ (ofNatural F hΛ hsmall hδ hδT hP0).bigTime)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) :
    ContDiffOn ℝ ∞ ((ofNatural F hΛ hsmall hδ hδT hP0).physicalU T κ w₁)
      (Input.ofNatural hΛ F).radialDomain.carrier := by
  let R := ofNatural F hΛ hsmall hδ hδT hP0
  let N := Input.ofNatural hΛ F
  intro p hp
  by_cases hX : 0 < p.1
  · have hs := ((R.axialVelocity_smooth parameterInterval_open T κ w₁).contDiffAt
      ((logDomain parameterInterval parameterInterval_open).isOpen.mem_nhds
        (show R.logPoint p ∈ (logDomain parameterInterval parameterInterval_open).carrier from
          ⟨mem_univ _, hp.2⟩))).comp p (R.logPoint_smoothAt hX)
    have he : R.physicalU T κ w₁ =ᶠ[𝓝 p]
        (fun q => R.axialVelocity T κ w₁ (R.logPoint q)) := by
      filter_upwards [continuousAt_fst.eventually (Ioi_mem_nhds hX),
        continuousAt_snd.eventually (parameterInterval_open.mem_nhds hp.2)] with q hqX hqη
      exact physicalU_eq_log F hΛ hsmall hδ hδT hP0 hT hb hw₁ hw₂ hqη hqX
    exact (hs.congr_of_eventuallyEq he).contDiffWithinAt
  · have hbefore : p.1 < R.radius0 := (le_of_not_gt hX).trans_lt R.radius0_pos
    have he : R.physicalU T κ w₁ =ᶠ[𝓝 p] R.profiles.U := by
      filter_upwards [continuousAt_fst.eventually (Iio_mem_nhds hbefore)] with q hq
      exact R.physicalU_before T κ w₁ hq.le
    exact ((R.profiles.U_smooth.contDiffAt (N.radialDomain.isOpen.mem_nhds
      hp)).congr_of_eventuallyEq he).contDiffWithinAt

theorem physicalF_positive (T κ w₁ w₂ : ℝ) {p : Point}
    (hp : p ∈ (Input.ofNatural hΛ F).radialDomain.carrier) (hX : 0 ≤ p.1) :
    0 < (ofNatural F hΛ hsmall hδ hδT hP0).physicalF T κ w₁ w₂ p := by
  let R := ofNatural F hΛ hsmall hδ hδT hP0
  by_cases hx : p.1 ≤ R.radius0
  · rw [R.physicalF_before T κ w₁ w₂ hx]
    exact (Input.ofNatural hΛ F).refF_pos δ hp hX
  · change 0 < (if p.1 ≤ R.radius0 then _ else _)
    rw [ite_eq_right hx]
    exact Real.exp_pos _

/-- The pressure and all moments are recomputed from these exact physical
fields.  This is the object used by the later cone and matching modules. -/
noncomputable def physicalProfiles {T κ w₁ w₂ : ℝ} (hT : 0 < T)
    (hb : δ ≤ (ofNatural F hΛ hsmall hδ hδT hP0).bigTime)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) : Profiles (Input.ofNatural hΛ F).radialDomain where
  f := (ofNatural F hΛ hsmall hδ hδT hP0).physicalF T κ w₁ w₂
  U := (ofNatural F hΛ hsmall hδ hδT hP0).physicalU T κ w₁
  f_smooth := physicalF_smooth F hΛ hsmall hδ hδT hP0 hT hb hw₁ hw₂
  U_smooth := physicalU_smooth F hΛ hsmall hδ hδT hP0 hT hb hw₁ hw₂
  pressure0 := P0
  pressure0_smooth := fun _ _ => hP0.contDiffAt

theorem physical_fields_natural (T κ w₁ w₂ : ℝ) {p : Point}
    (hp : p.1 ≤ (Input.ofNatural hΛ F).endpoint) :
    (ofNatural F hΛ hsmall hδ hδT hP0).physicalF T κ w₁ w₂ p = F.f p ∧
      (ofNatural F hΛ hsmall hδ hδT hP0).physicalU T κ w₁ p = F.U p := by
  let R := ofNatural F hΛ hsmall hδ hδT hP0
  rw [R.physicalF_before T κ w₁ w₂ hp, R.physicalU_before T κ w₁ hp]
  exact ⟨(Input.ofNatural hΛ F).refF_eq_natural_initial δ hp,
    (Input.ofNatural hΛ F).refU_eq_natural_initial δ hp⟩

theorem physical_fields_eq_activation {T κ w₁ w₂ : ℝ} (hT : 0 < T)
    (hb : δ ≤ (ofNatural F hΛ hsmall hδ hδT hP0).bigTime)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) {p : Point} (hη : p.2 ∈ parameterInterval)
    (hX : p.1 ≤ (Input.ofNatural hΛ F).endpoint * Real.exp δ) :
    let R := ofNatural F hΛ hsmall hδ hδT hP0
    let N := Input.ofNatural hΛ F
    R.physicalF T κ w₁ w₂ p = StressActivation.FromReference.f N T κ δ p ∧
      R.physicalU T κ w₁ p = StressActivation.FromReference.U N T κ δ p := by
  let R := ofNatural F hΛ hsmall hδ hδT hP0
  let N := Input.ofNatural hΛ F
  by_cases hx : p.1 ≤ R.radius0
  · exact ⟨(R.physicalF_before T κ w₁ w₂ hx).trans
      (StressActivation.FromReference.f_eq_reference N T κ δ hx).symm,
      (R.physicalU_before T κ w₁ hx).trans
      (StressActivation.FromReference.U_eq_reference N T κ δ hx).symm⟩
  · have hpos := R.radius0_pos.trans (lt_of_not_ge hx)
    have ht : N.logTime p.1 ≤ δ := (N.logTime_le_iff hpos).mpr hX
    have heq := log_fields_eq_activation F hΛ hsmall hδ hδT hP0 (T := T) (κ := κ) hb hw₁ hw₂ ht hη
    constructor
    · rw [physicalF_eq_log F hΛ hsmall hδ hδT hP0 hT hb hw₁ hw₂ hη hpos,
        StressActivation.FromReference.f_eq_logtime N hT hδ hδT κ hη hpos]
      exact congrArg Real.exp heq.1
    · rw [physicalU_eq_log F hΛ hsmall hδ hδT hP0 hT hb hw₁ hw₂ hη hpos,
        StressActivation.FromReference.U_eq_logtime N hT hδ hδT κ hη hpos]
      exact heq.2

theorem physicalF_hasDerivAt {T κ w₁ w₂ : ℝ} (hT : 0 < T)
    (hb : δ ≤ (ofNatural F hΛ hsmall hδ hδT hP0).bigTime)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) {p : Point}
    (hη : p.2 ∈ parameterInterval) (hX : 0 < p.1) :
    let R := ofNatural F hΛ hsmall hδ hδT hP0
    HasDerivAt (fun X => R.physicalF T κ w₁ w₂ (X, p.2))
      (R.physicalF T κ w₁ w₂ p * angularSlope T κ R.bigTime w₁ w₂ R.angularStock (R.logPoint p) /
        p.1) p.1 := by
  let N := Input.ofNatural hΛ F
  let R := ofNatural F hΛ hsmall hδ hδT hP0
  have hd := ((R.logAmplitude_hasDerivAt parameterInterval_open T κ w₁ w₂
    (N.logTime p.1) hη).comp p.1 (N.logTime_hasDerivAt hX)).exp
  have hd' : HasDerivAt (fun X => Real.exp (R.logAmplitude T κ w₁ w₂ (N.logTime X, p.2)))
      (R.physicalF T κ w₁ w₂ p * angularSlope T κ R.bigTime w₁ w₂ R.angularStock (R.logPoint p) /
        p.1) p.1 := by
    rw [physicalF_eq_log F hΛ hsmall hδ hδT hP0 hT hb hw₁ hw₂ hη hX]
    change HasDerivAt _ (Real.exp (R.logAmplitude T κ w₁ w₂ (N.logTime p.1, p.2)) *
      angularSlope T κ R.bigTime w₁ w₂ R.angularStock (N.logTime p.1, p.2) / p.1) p.1
    convert! hd using 1
    simp only [Function.comp_apply]
    ring
  apply hd'.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hX] with X hX'
  exact physicalF_eq_log F hΛ hsmall hδ hδT hP0 hT hb hw₁ hw₂ hη hX'

theorem physicalU_hasDerivAt {T κ w₁ w₂ : ℝ} (hT : 0 < T)
    (hb : δ ≤ (ofNatural F hΛ hsmall hδ hδT hP0).bigTime)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) {p : Point}
    (hη : p.2 ∈ parameterInterval) (hX : 0 < p.1) :
    let R := ofNatural F hΛ hsmall hδ hδT hP0
    HasDerivAt (fun X => R.physicalU T κ w₁ (X, p.2))
      (axialSlope T κ R.bigTime w₁ R.axialStock (R.logPoint p) / p.1) p.1 := by
  let N := Input.ofNatural hΛ F
  let R := ofNatural F hΛ hsmall hδ hδT hP0
  have hd := (R.axialVelocity_hasDerivAt parameterInterval_open T κ w₁
    (N.logTime p.1) hη).comp p.1 (N.logTime_hasDerivAt hX)
  have hd' : HasDerivAt (fun X => R.axialVelocity T κ w₁ (N.logTime X, p.2))
      (axialSlope T κ R.bigTime w₁ R.axialStock (R.logPoint p) / p.1) p.1 := by
    change HasDerivAt _ (axialSlope T κ R.bigTime w₁ R.axialStock (N.logTime p.1, p.2) / p.1) p.1
    convert! hd using 1
    ring
  apply hd'.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hX] with X hX'
  exact physicalU_eq_log F hΛ hsmall hδ hδT hP0 hT hb hw₁ hw₂ hη hX'

/-- The actual physical radial derivatives satisfy the prescribed log-clock
equations.  The controls use the REF stocks after REF freezes. -/
theorem physical_radial_equations {T κ w₁ w₂ : ℝ} (hT : 0 < T)
    (hb : δ ≤ (ofNatural F hΛ hsmall hδ hδT hP0).bigTime)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) {p : Point}
    (hη : p.2 ∈ parameterInterval) (hX : 0 < p.1) :
    let R := ofNatural F hΛ hsmall hδ hδT hP0
    p.1 * radialPartial (R.physicalF T κ w₁ w₂) p / R.physicalF T κ w₁ w₂ p =
      angularSlope T κ R.bigTime w₁ w₂ R.angularStock (R.logPoint p) ∧
    p.1 * radialPartial (R.physicalU T κ w₁) p =
      axialSlope T κ R.bigTime w₁ R.axialStock (R.logPoint p) := by
  let N := Input.ofNatural hΛ F
  let R := ofNatural F hΛ hsmall hδ hδT hP0
  have hp : p ∈ N.radialDomain.carrier := by
    exact ⟨lt_of_lt_of_le (by norm_num) (mul_nonneg hΛ.le hX.le), hη⟩
  have hfp := physicalF_positive F hΛ hsmall hδ hδT hP0 T κ w₁ w₂ hp hX.le
  have hf := (radialPartial_hasDerivAt N.radialDomain
    (physicalF_smooth F hΛ hsmall hδ hδT hP0 (κ := κ) hT hb hw₁ hw₂) hp).unique
      (physicalF_hasDerivAt F hΛ hsmall hδ hδT hP0 hT hb hw₁ hw₂ hη hX)
  have hu := (radialPartial_hasDerivAt N.radialDomain
    (physicalU_smooth F hΛ hsmall hδ hδT hP0 (κ := κ) hT hb hw₁ hw₂) hp).unique
      (physicalU_hasDerivAt F hΛ hsmall hδ hδT hP0 hT hb hw₁ hw₂ hη hX)
  change p.1 * radialPartial (R.physicalF T κ w₁ w₂) p / R.physicalF T κ w₁ w₂ p = _ ∧
    p.1 * radialPartial (R.physicalU T κ w₁) p = _
  rw [hf, hu]
  constructor
  · field_simp [hX.ne', hfp.ne']
    exact mul_div_cancel_left₀ _ hfp.ne'
  · field_simp [hX.ne']

end Natural

namespace StockReference

variable {J : Set ℝ} (R : StockReference J)

theorem finalTime_sub_bigTime : R.finalTime - R.bigTime = Real.log (11 / 10 : ℝ) := by
  unfold finalTime bigTime
  rw [Real.log_div (by norm_num) R.radius0_pos.ne', Real.log_div (by norm_num) R.radius0_pos.ne']
  calc
    _ = Real.log 110 - Real.log 100 := by ring
    _ = Real.log (110 / 100 : ℝ) := (Real.log_div (by norm_num) (by norm_num)).symm
    _ = _ := by norm_num

theorem finalTime_gt_bigTime : R.bigTime < R.finalTime := by
  have hp : 0 < Real.log (11 / 10 : ℝ) := Real.log_pos (by norm_num)
  linarith [R.finalTime_sub_bigTime]

theorem radius0_lt_100 (hb : 0 < R.bigTime) : R.radius0 < 100 := by
  have he := Real.exp_lt_exp.mpr hb
  rw [Real.exp_zero, bigTime, Real.exp_log (div_pos (by norm_num) R.radius0_pos)] at he
  simpa only [one_mul] using (lt_div_iff₀ R.radius0_pos).mp he

theorem logTime_sub_finalTime {X : ℝ} (hX : 0 < X) :
    R.logTime X - R.finalTime = Real.log (X / 110) := by
  unfold logTime finalTime
  rw [Real.log_div hX.ne' R.radius0_pos.ne', Real.log_div (by norm_num) R.radius0_pos.ne',
    Real.log_div hX.ne' (by norm_num)]
  ring

theorem finalTime_le_logTime {X : ℝ} (hX : 110 ≤ X) : R.finalTime ≤ R.logTime X := by
  exact Real.log_le_log (div_pos (by norm_num) R.radius0_pos)
    (div_le_div_of_nonneg_right hX R.radius0_pos.le)

theorem physicalU_held (hJ : IsOpen J) {T κ w₁ X η : ℝ}
    (hw₁ : 0 < w₁) (hstart : R.bigTime + w₁ ≤ R.finalTime)
    (hR : R.radius0 < 110) (hX : 110 ≤ X) (hη : η ∈ J) :
    R.physicalU T κ w₁ (X, η) = R.endpointU T κ w₁ η := by
  rw [physicalU, ite_eq_right (not_le.mpr (hR.trans_le hX))]
  exact axialField_hold hw₁ hJ R.initialU (R.axialStock_smooth hJ)
    hstart (R.finalTime_le_logTime hX) hη

theorem physicalF_held_log (hJ : IsOpen J) {T κ w₁ w₂ X η : ℝ}
    (hw₂ : 0 < w₂) (hstart : R.bigTime + w₁ + w₂ ≤ R.finalTime)
    (hR : R.radius0 < 110) (hX : 110 ≤ X) (hη : η ∈ J) :
    R.physicalF T κ w₁ w₂ (X, η) =
      Real.exp (R.logAmplitude T κ w₁ w₂ (R.finalTime, η) - (2 / 5 : ℝ) * Real.log (X / 110)) := by
  rw [physicalF, ite_eq_right (not_le.mpr (hR.trans_le hX))]
  have hh := logField_hold (T := T) (κ := κ) hw₂ hJ R.initialLog (R.angularStock_smooth hJ)
    hstart (R.finalTime_le_logTime hX) hη
  change Real.exp (logField T κ R.bigTime w₁ w₂ R.initialLog R.angularStock (R.logTime X, η)) = _
  rw [hh, R.logTime_sub_finalTime (lt_of_lt_of_le (by norm_num) hX)]
  rfl

theorem physicalF_held (hJ : IsOpen J) {T κ w₁ w₂ C X η : ℝ}
    (hw₂ : 0 < w₂) (hstart : R.bigTime + w₁ + w₂ ≤ R.finalTime)
    (hR : R.radius0 < 110) (hC : 0 < C) (hX : 110 ≤ X) (hη : η ∈ J) :
    R.physicalF T κ w₁ w₂ (X, η) =
      C⁻¹ * Real.exp (Real.log (X / 110) / 10 + R.endpointLog T κ w₁ w₂ C η) / Real.sqrt (2 * X) :=
        by
  have hXp : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hs : 0 < Real.sqrt (2 * X) := Real.sqrt_pos.2 (by positivity)
  have hlog : Real.log C + Real.log (Real.sqrt (2 * X)) +
      (R.logAmplitude T κ w₁ w₂ (R.finalTime, η) - (2 / 5 : ℝ) * Real.log (X / 110)) =
      Real.log (X / 110) / 10 + R.endpointLog T κ w₁ w₂ C η := by
    rw [Real.log_sqrt (by positivity : 0 ≤ 2 * X), Real.log_mul (by norm_num) hXp.ne',
      Real.log_div hXp.ne' (by norm_num)]
    unfold endpointLog
    rw [show (220 : ℝ) = 2 * 110 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  have hv : C * Real.sqrt (2 * X) * R.physicalF T κ w₁ w₂ (X, η) =
      Real.exp (Real.log (X / 110) / 10 + R.endpointLog T κ w₁ w₂ C η) := by
    calc
      _ = Real.exp (Real.log C) * Real.exp (Real.log (Real.sqrt (2 * X))) *
          Real.exp (R.logAmplitude T κ w₁ w₂ (R.finalTime, η) - (2 / 5 : ℝ) * Real.log (X / 110))
            := by
        rw [Real.exp_log hC, Real.exp_log hs, R.physicalF_held_log hJ hw₂ hstart hR hX hη]
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add, hlog]
  apply (eq_div_iff hs.ne').mpr
  rw [← hv]
  field_simp

theorem endpointLog_eq_actual (hJ : IsOpen J) {T κ w₁ w₂ C η : ℝ}
    (hw₂ : 0 < w₂) (hstart : R.bigTime + w₁ + w₂ ≤ R.finalTime)
    (hR : R.radius0 < 110) (hC : 0 < C) (hη : η ∈ J) :
    R.endpointLog T κ w₁ w₂ C η =
      Real.log (C * (Real.sqrt (2 * (110 : ℝ)) * R.physicalF T κ w₁ w₂ (110, η))) := by
  rw [R.physicalF_held_log hJ hw₂ hstart hR le_rfl hη]
  norm_num only [div_self (by norm_num : (110 : ℝ) ≠ 0), Real.log_one, mul_zero, sub_zero]
  rw [Real.log_mul hC.ne' (mul_ne_zero (Real.sqrt_pos.2 (by norm_num)).ne' (Real.exp_pos _).ne'),
    Real.log_mul (Real.sqrt_pos.2 (by norm_num)).ne' (Real.exp_pos _).ne',
    Real.log_exp, Real.log_sqrt (by norm_num)]
  unfold endpointLog
  ring

/-- Quantitative conclusions for the actual integral fields.  The theorem
below constructs one common set of parameter thresholds for all these jets. -/
structure SmallLogControl (K : Set ℝ) (N : ℕ) (ε T κ w₁ w₂ : ℝ) : Prop where
  finish_before : R.bigTime + w₁ + w₂ < R.finalTime
  axial_jets : ∀ y ∈ Icc (0 : ℝ) R.finalTime, ∀ η ∈ K, ∀ n ≤ N,
    |iteratedDeriv n (fun ξ => R.axialVelocity T κ w₁ (y, ξ) - R.initialU ξ) η| < ε
  positive_log_jets : ∀ y ∈ Icc (0 : ℝ) R.finalTime, ∀ η ∈ K, ∀ n ≤ N, 0 < n →
    |iteratedDeriv n (fun ξ => R.logAmplitude T κ w₁ w₂ (y, ξ) - R.initialLog ξ) η| < ε
  log_value : ∀ y ∈ Icc (0 : ℝ) (R.bigTime + w₁ + w₂), ∀ η ∈ K,
    |R.logAmplitude T κ w₁ w₂ (y, η) - R.initialLog η| < ε

/-- The compact constants are computed from the genuine REF stocks after
the reference path is fixed.  Then the activation width, retained control,
and both final widths can be chosen independently below positive bounds. -/
theorem exists_small_log_control (hJ : IsOpen J) {K : Set ℝ} (hK : IsCompact K)
    (hKJ : K ⊆ J) (N : ℕ) (hb : 0 ≤ R.bigTime) {Tmax ε : ℝ}
    (hTmax : 0 < Tmax) (hε : 0 < ε) :
    ∃ T0 > 0, ∃ κ0 > 0, ∃ w0 > 0, T0 ≤ Tmax ∧ κ0 < 1 ∧
      2 * w0 < R.finalTime - R.bigTime ∧
      ∀ T ∈ Ioo (0 : ℝ) T0, ∀ κ ∈ Ico (0 : ℝ) κ0,
      ∀ w₁ ∈ Ioo (0 : ℝ) w0, ∀ w₂ ∈ Ioo (0 : ℝ) w0,
        R.SmallLogControl K N ε T κ w₁ w₂ := by
  obtain ⟨Ma, hMa, ha⟩ := compact_stock_jet_bound hJ hK hKJ (R.angularStock_smooth hJ) R.finalTime N
  obtain ⟨Mu, hMu, hu⟩ := compact_stock_jet_bound hJ hK hKJ (R.axialStock_smooth hJ) R.finalTime N
  let M := Ma + Mu + 1
  have hM : 0 < M := by dsimp [M]; linarith
  have haM : Ma ≤ M := by dsimp [M]; linarith
  have huM : Mu ≤ M := by dsimp [M]; linarith
  have hf : 0 < R.finalTime := lt_of_le_of_lt hb R.finalTime_gt_bigTime
  let s := ε / (4 * M * (1 + R.finalTime))
  have hs : 0 < s := div_pos hε (by positivity)
  let T0 := min Tmax s
  let κ0 := min (1 / 2 : ℝ) s
  let w0 := min ((R.finalTime - R.bigTime) / 4) (ε / 4)
  have hw0 : 0 < w0 := lt_min (div_pos (sub_pos.mpr R.finalTime_gt_bigTime) (by norm_num))
    (div_pos hε (by norm_num))
  refine ⟨T0, lt_min hTmax hs, κ0, lt_min (by norm_num) hs, w0, hw0,
    min_le_left _ _, lt_of_le_of_lt (min_le_left _ _) (by norm_num), ?_, ?_⟩
  · have hw := min_le_left ((R.finalTime - R.bigTime) / 4) (ε / 4)
    dsimp only [w0]
    linarith [R.finalTime_gt_bigTime]
  intro T hT κ hκ w₁ hw₁ w₂ hw₂
  have hTs : T < s := hT.2.trans_le (min_le_right _ _)
  have hκs : κ < s := hκ.2.trans_le (min_le_right _ _)
  have hκ1 : κ ∈ Icc (0 : ℝ) 1 :=
    ⟨hκ.1, hκ.2.le.trans ((min_le_left _ _).trans (by norm_num))⟩
  have hws : w₁ + w₂ < R.finalTime - R.bigTime := by
    have hw : w0 ≤ (R.finalTime - R.bigTime) / 4 := min_le_left _ _
    linarith [hw₁.2, hw₂.2, R.finalTime_gt_bigTime]
  have hwe : w₁ + w₂ < ε / 2 := by
    have hw : w0 ≤ ε / 4 := min_le_right _ _
    linarith [hw₁.2, hw₂.2]
  have hcontrol (y : ℝ) (hy : y ∈ Icc (0 : ℝ) R.finalTime) : M * (T + κ * y) < ε / 4 := by
    have hky : κ * y ≤ s * R.finalTime := mul_le_mul hκs.le hy.2 hy.1 hs.le
    have hsum : T + κ * y < s * (1 + R.finalTime) := by nlinarith
    have hm := mul_lt_mul_of_pos_left hsum hM
    have he : M * (s * (1 + R.finalTime)) = ε / 4 := by
      dsimp [s]
      field_simp
    rwa [he] at hm
  refine ⟨by linarith, ?_, ?_, ?_⟩
  · intro y hy η hη n hn
    have hv := axialField_jet_error_bound hJ (R.axialStock_smooth hJ) R.initialU
      (b := R.bigTime) (w := w₁) hT.1 hκ1 hy.1 (hKJ hη) hM.le n
      (fun t ht => (hu n hn t ⟨ht.1, ht.2.trans hy.2⟩ η hη).trans huM)
    exact hv.trans_lt ((hcontrol y hy).trans (by linarith))
  · intro y hy η hη n hn hn0
    have hv := logField_positive_jet_error_bound hJ (R.angularStock_smooth hJ) R.initialLog
      (b := R.bigTime) (w₁ := w₁) (w₂ := w₂) hT.1 hκ1 hy.1 (hKJ hη) hM.le (Nat.ne_of_gt hn0)
      (fun t ht => (ha n hn t ⟨ht.1, ht.2.trans hy.2⟩ η hη).trans haM)
    exact hv.trans_lt ((hcontrol y hy).trans (by linarith))
  · intro y hy η hη
    have hyf : y ∈ Icc (0 : ℝ) R.finalTime := ⟨hy.1, hy.2.trans (by linarith)⟩
    have hv := logField_value_error_bound hJ (R.angularStock_smooth hJ) R.initialLog
      hT.1 hκ1 hb hw₁.1.le hw₂.1 hy.1 hy.2 (hKJ hη) hM.le
      (fun t ht => (ha 0 (Nat.zero_le N) t ⟨ht.1, ht.2.trans hyf.2⟩ η hη).trans haM)
    exact hv.trans_lt (by nlinarith [hcontrol y hyf])

/-- The same estimates stated directly for the actual physical fields. -/
structure SmallPhysicalControl (K : Set ℝ) (N : ℕ) (ε T κ w₁ w₂ : ℝ) : Prop where
  finish_before : R.bigTime + w₁ + w₂ < R.finalTime
  axial_jets : ∀ X ∈ Icc R.radius0 (110 : ℝ), ∀ η ∈ K, ∀ n ≤ N,
    |iteratedDeriv n (fun ξ => R.physicalU T κ w₁ (X, ξ) - R.initialU ξ) η| < ε
  positive_log_jets : ∀ X ∈ Icc R.radius0 (110 : ℝ), ∀ η ∈ K, ∀ n ≤ N, 0 < n →
    |iteratedDeriv n (fun ξ => Real.log (R.physicalF T κ w₁ w₂ (X, ξ)) - R.initialLog ξ) η| < ε
  log_value : ∀ X ∈ Icc R.radius0 (radius R.radius0 (R.bigTime + w₁ + w₂)), ∀ η ∈ K,
    |Real.log (R.physicalF T κ w₁ w₂ (X, η)) - R.initialLog η| < ε

end StockReference

section PhysicalEstimates

open NaturalProfile ReferencePath

variable {h j σ Λ C : ℝ} {P0 : ℝ → ℝ} {d : NaturalAxisCoefficients.AnalyticInputs h j σ P0}
    (F : ProfileFamily d Λ C) (hΛ : 0 < Λ) (hsmall : NaturalAxisData.SmallParameters h j)
    {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit) (hP0 : ContDiff ℝ ∞ P0)

theorem small_physical_of_log_control {K : Set ℝ} (hKJ : K ⊆ parameterInterval)
    {N : ℕ} {ε T κ w₁ w₂ : ℝ} (hT : 0 < T)
    (hb : δ ≤ (ofNatural F hΛ hsmall hδ hδT hP0).bigTime)
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (hc : (ofNatural F hΛ hsmall hδ hδT hP0).SmallLogControl K N ε T κ w₁ w₂) :
    (ofNatural F hΛ hsmall hδ hδT hP0).SmallPhysicalControl K N ε T κ w₁ w₂ := by
  let R := ofNatural F hΛ hsmall hδ hδT hP0
  let A := Input.ofNatural hΛ F
  have hclock (X : ℝ) (hX : X ∈ Icc R.radius0 (110 : ℝ)) :
      R.logTime X ∈ Icc (0 : ℝ) R.finalTime := by
    have hp : 0 < X := R.radius0_pos.trans_le hX.1
    refine ⟨?_, ?_⟩
    · change 0 ≤ A.logTime X
      exact (A.le_logTime_iff hp).mpr (by simp only [Real.exp_zero, mul_one]; exact hX.1)
    · exact Real.log_le_log (div_pos hp R.radius0_pos)
        (div_le_div_of_nonneg_right hX.2 R.radius0_pos.le)
  have hUeq (X η : ℝ) (hX : 0 < X) (hη : η ∈ K) :
      (fun ξ => R.physicalU T κ w₁ (X, ξ) - R.initialU ξ) =ᶠ[𝓝 η]
        (fun ξ => R.axialVelocity T κ w₁ (R.logTime X, ξ) - R.initialU ξ) := by
    filter_upwards [parameterInterval_open.mem_nhds (hKJ hη)] with ξ hξ
    exact congrArg (fun z => z - R.initialU ξ)
      (physicalU_eq_log F hΛ hsmall hδ hδT hP0 hT hb hw₁ hw₂ hξ hX)
  have hLeq (X η : ℝ) (hX : 0 < X) (hη : η ∈ K) :
      (fun ξ => Real.log (R.physicalF T κ w₁ w₂ (X, ξ)) - R.initialLog ξ) =ᶠ[𝓝 η]
        (fun ξ => R.logAmplitude T κ w₁ w₂ (R.logTime X, ξ) - R.initialLog ξ) := by
    filter_upwards [parameterInterval_open.mem_nhds (hKJ hη)] with ξ hξ
    rw [physicalF_eq_log F hΛ hsmall hδ hδT hP0 hT hb hw₁ hw₂ hξ hX, Real.log_exp]
    rfl
  refine ⟨hc.finish_before, ?_, ?_, ?_⟩
  · intro X hX η hη n hn
    rw [(hUeq X η (R.radius0_pos.trans_le hX.1) hη).iteratedDeriv_eq n]
    exact hc.axial_jets (R.logTime X) (hclock X hX) η hη n hn
  · intro X hX η hη n hn hn0
    rw [(hLeq X η (R.radius0_pos.trans_le hX.1) hη).iteratedDeriv_eq n]
    exact hc.positive_log_jets (R.logTime X) (hclock X hX) η hη n hn hn0
  · intro X hX η hη
    have hp : 0 < X := R.radius0_pos.trans_le hX.1
    have hy0 : 0 ≤ R.logTime X := (A.le_logTime_iff hp).mpr
      (by simp only [Real.exp_zero, mul_one]; exact hX.1)
    have hyend : R.logTime X ≤ R.bigTime + w₁ + w₂ := (A.logTime_le_iff hp).mpr hX.2
    rw [physicalF_eq_log F hΛ hsmall hδ hδT hP0 hT hb hw₁ hw₂ (hKJ hη) hp, Real.log_exp]
    exact hc.log_value (R.logTime X) ⟨hy0, hyend⟩ η hη

/-- Direct physical error thresholds, with the reference cutoff already
fixed.  Setting `N = 1` supplies the value and first-parameter estimates
needed for all five histories and both lag stocks. -/
theorem exists_small_physical_control {K : Set ℝ} (hK : IsCompact K)
    (hKJ : K ⊆ parameterInterval) (N : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hb : δ ≤ (ofNatural F hΛ hsmall hδ hδT hP0).bigTime) :
    let R := ofNatural F hΛ hsmall hδ hδT hP0
    ∃ T0 > 0, ∃ κ0 > 0, ∃ w0 > 0, T0 ≤ δ ∧ κ0 < 1 ∧
      2 * w0 < R.finalTime - R.bigTime ∧
      ∀ T ∈ Ioo (0 : ℝ) T0, ∀ κ ∈ Ico (0 : ℝ) κ0,
      ∀ w₁ ∈ Ioo (0 : ℝ) w0, ∀ w₂ ∈ Ioo (0 : ℝ) w0,
        R.SmallPhysicalControl K N ε T κ w₁ w₂ := by
  let R := ofNatural F hΛ hsmall hδ hδT hP0
  obtain ⟨T0, hT0, κ0, hκ0, w0, hw0, hTδ, hκ1, hwgap, hcontrol⟩ :=
    R.exists_small_log_control parameterInterval_open hK hKJ N (hδ.le.trans hb) hδ hε
  refine ⟨T0, hT0, κ0, hκ0, w0, hw0, hTδ, hκ1, hwgap, ?_⟩
  intro T hT κ hκ w₁ hw₁ w₂ hw₂
  exact small_physical_of_log_control F hΛ hsmall hδ hδT hP0 hKJ hT.1 hb hw₁.1 hw₂.1
    (hcontrol T hT κ hκ w₁ hw₁ w₂ hw₂)

theorem exists_joint_small_control {K : Set ℝ} (hK : IsCompact K)
    (hKJ : K ⊆ parameterInterval) (N : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hb : δ ≤ (ofNatural F hΛ hsmall hδ hδT hP0).bigTime) :
    let R := ofNatural F hΛ hsmall hδ hδT hP0
    ∃ T0 > 0, ∃ κ0 > 0, ∃ w0 > 0, T0 ≤ δ ∧ κ0 < 1 ∧
      2 * w0 < R.finalTime - R.bigTime ∧
      ∀ T ∈ Ioo (0 : ℝ) T0, ∀ κ ∈ Ico (0 : ℝ) κ0,
      ∀ w₁ ∈ Ioo (0 : ℝ) w0, ∀ w₂ ∈ Ioo (0 : ℝ) w0,
        R.SmallLogControl K N ε T κ w₁ w₂ ∧ R.SmallPhysicalControl K N ε T κ w₁ w₂ := by
  let R := ofNatural F hΛ hsmall hδ hδT hP0
  obtain ⟨T0, hT0, κ0, hκ0, w0, hw0, hTδ, hκ1, hwgap, hcontrol⟩ :=
    R.exists_small_log_control parameterInterval_open hK hKJ N (hδ.le.trans hb) hδ hε
  refine ⟨T0, hT0, κ0, hκ0, w0, hw0, hTδ, hκ1, hwgap, ?_⟩
  intro T hT κ hκ w₁ hw₁ w₂ hw₂
  have hc := hcontrol T hT κ hκ w₁ hw₁ w₂ hw₂
  exact ⟨hc, small_physical_of_log_control F hΛ hsmall hδ hδT hP0 hKJ hT.1 hb hw₁.1 hw₂.1 hc⟩

end PhysicalEstimates

section EndpointEstimates

open NaturalProfile NaturalAxisCoefficients ReferencePath

variable {h j σ Λ C : ℝ} {P0 : ℝ → ℝ} {d : AnalyticInputs h j σ P0}
    (F : ProfileFamily d Λ C) (hΛ : 0 < Λ) (hsmall : NaturalAxisData.SmallParameters h j)
    {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit) (hP0 : ContDiff ℝ ∞ P0)

theorem initialLog_natural (η : ℝ) :
    (ofNatural F hΛ hsmall hδ hδT hP0).initialLog η =
      Real.log (F.f ((Input.ofNatural hΛ F).endpoint, η)) := by
  change Real.log ((Input.ofNatural hΛ F).refF δ ((Input.ofNatural hΛ F).endpoint, η)) = _
  rw [(Input.ofNatural hΛ F).refF_eq_natural_initial δ le_rfl]
  rfl

theorem initialU_natural (η : ℝ) :
    (ofNatural F hΛ hsmall hδ hδT hP0).initialU η =
      F.U ((Input.ofNatural hΛ F).endpoint, η) := by
  exact (Input.ofNatural hΛ F).refU_eq_natural_initial δ le_rfl

theorem endpoint_rescale (η : ℝ) :
    NaturalProfile.rescalePoint Λ ((Input.ofNatural hΛ F).endpoint, η) = (4, η) := by
  exact Prod.ext ((Input.ofNatural hΛ F).scale_endpoint) rfl

omit F in
theorem exists_phase_bound (d : AnalyticInputs h j σ P0) :
    ∃ B > 0, ∀ η ∈ Icc (-1 : ℝ) 1, |realPhase h j σ η| ≤ B := by
  have hc : ContinuousOn (realPhase h j σ) (Icc (-1 : ℝ) 1) := by
    intro η hη
    have hw := original_interval_interior hη
    exact (d.realPhase_hasDerivAt ⟨hw.1.le, hw.2.le⟩).continuousAt.continuousWithinAt
  obtain ⟨B, hb⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨1 + |B|, by positivity, ?_⟩
  intro η hη
  have he := hb η hη
  rw [Real.norm_eq_abs] at he
  linarith [le_abs_self B]

omit F in
theorem normalized_initialLog_formula (E : NaturalEntrance.CoefficientProfile d Λ C)
    (hC : 0 < C) {η : ℝ}
    (hφ : AxisEvaluation.profile window d.coefficients.epsilon E.coefficients.1 (4, η) ≠ 0) :
    Real.log C + (ofNatural E.family hΛ hsmall hδ hδT hP0).initialLog η =
      Λ * realPhase h j σ η + Real.log (AxisEvaluation.profile window d.coefficients.epsilon
        E.coefficients.1 (4, η)) := by
  rw [initialLog_natural E.family hΛ hsmall hδ hδT hP0 η, E.f_eq]
  change Real.log C + Real.log (realAmplitude h j σ Λ C η *
    AxisEvaluation.profile window d.coefficients.epsilon E.coefficients.1
      (NaturalProfile.rescalePoint Λ ((Input.ofNatural hΛ E.family).endpoint, η))) = _
  rw [endpoint_rescale E.family hΛ η,
    Real.log_mul (realAmplitude_pos h j σ Λ hC η).ne' hφ]
  unfold realAmplitude
  rw [Real.log_div (Real.exp_pos _).ne' hC.ne', Real.log_exp]
  ring

omit F C hδ hδT in
/-- The bound precedes the choice of normalization `C`.  Its only profile
input is the uniform coefficient-space ball and the proved `Phi > 1/8`. -/
theorem exists_uniform_initialLog_bound (hσ : 0 < σ)
    (hscale : AxisReference.stabilityScale d.coefficients.epsilon (profileErrorConstant d) ≤ Λ) :
    ∃ B > 0, ∀ C, 0 < C → ∀ E : NaturalEntrance.CoefficientProfile d Λ C,
      ∀ δ, ∀ hδ : 0 < δ, ∀ hδT : 2 * δ < rampLimit, ∀ η ∈ Icc (-1 : ℝ) 1,
        |Real.log C + (ofNatural E.family hΛ hsmall hδ hδT hP0).initialLog η| ≤ B := by
  obtain ⟨A, hA, ha⟩ := exists_phase_bound d
  let J0 := ReferenceJetBounds.jetConstant d.coefficients 0 0
  have hJ0 : 0 ≤ J0 := ReferenceJetBounds.jetConstant_nonneg d.coefficients 0 0
  let B := 1 + Λ * A + |Real.log (1 / 8 : ℝ)| + |Real.log (1 + J0)|
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro C hC E δ hδ hδT η hη
  have hηJ := original_interval_interior hη
  have hphi := NaturalEntrance.coefficient_phi_lower d.coefficients hσ
    (NaturalEntrance.profileErrorConstant_nonneg d) hscale E.coefficients E.norm_error
    (by norm_num : (0 : ℝ) ≤ 4) (by norm_num : (4 : ℝ) ≤ 41 / 10) hηJ
  let φ := AxisEvaluation.profile window d.coefficients.epsilon E.coefficients.1 (4, η)
  have hφ : 0 < φ := lt_trans (by norm_num) hphi
  have hupper : φ ≤ 1 + J0 := by
    have he := (ReferenceJetBounds.coefficient_jet_bound d.coefficients E.coefficients E.norm_ball
      0 0 (p := (4, η)) (by norm_num)).1
    rw [AxisEvaluation.mixedSeries_zero] at he
    exact (le_abs_self φ).trans (he.trans (by dsimp [J0]; linarith))
  have hlo : Real.log (1 / 8 : ℝ) ≤ Real.log φ := Real.log_le_log (by norm_num) hphi.le
  have hhi : Real.log φ ≤ Real.log (1 + J0) := Real.log_le_log hφ hupper
  have hlog : |Real.log φ| ≤ |Real.log (1 / 8 : ℝ)| + |Real.log (1 + J0)| := by
    apply abs_le.mpr
    constructor
    · linarith [neg_abs_le (Real.log (1 / 8 : ℝ)), abs_nonneg (Real.log (1 + J0))]
    · linarith [le_abs_self (Real.log (1 + J0)), abs_nonneg (Real.log (1 / 8 : ℝ))]
  rw [normalized_initialLog_formula hΛ hsmall hδ hδT hP0 E hC hφ.ne']
  calc
    _ ≤ |Λ * realPhase h j σ η| + |Real.log φ| := abs_add_le _ _
    _ ≤ Λ * A + (|Real.log (1 / 8 : ℝ)| + |Real.log (1 + J0)|) := by
      rw [abs_mul, abs_of_pos hΛ]
      exact add_le_add (mul_le_mul_of_nonneg_left (ha η hη) hΛ.le) hlog
    _ ≤ B := by dsimp [B]; linarith

omit F in
theorem initialU_error_jet (E : NaturalEntrance.CoefficientProfile d Λ C) (n : ℕ)
    {η : ℝ} (hη : η ∈ parameterInterval) :
    iteratedDeriv n (fun ξ => (ofNatural E.family hΛ hsmall hδ hδT hP0).initialU ξ -
      NaturalAxisData.U j ξ) η =
        (1 / Λ) * AxisEvaluation.mixedSeries window d.coefficients.epsilon E.coefficients.2 0 n (4,
          η) := by
  have he : (fun ξ => (ofNatural E.family hΛ hsmall hδ hδT hP0).initialU ξ - NaturalAxisData.U j ξ)
    =
      fun ξ => (1 / Λ) * AxisEvaluation.profile window d.coefficients.epsilon E.coefficients.2 (4,
        ξ) := by
    funext ξ
    rw [initialU_natural E.family hΛ hsmall hδ hδT hP0 ξ, E.U_eq]
    change NaturalAxisData.U j ξ + (1 / Λ) * AxisEvaluation.profile window d.coefficients.epsilon
      E.coefficients.2 (NaturalProfile.rescalePoint Λ ((Input.ofNatural hΛ E.family).endpoint, ξ))
        - _ = _
    rw [endpoint_rescale E.family hΛ ξ]
    ring
  have hs : ContDiffAt ℝ ∞ (fun ξ => AxisEvaluation.profile window d.coefficients.epsilon
    E.coefficients.2 (4, ξ)) η :=
    ((AxisEvaluation.profile_smooth window d.coefficients.epsilon_pos E.coefficients.2).contDiffAt
      ((AxisEvaluation.strip_isOpen window 20).mem_nhds
        (show (4, η) ∈ AxisEvaluation.strip window 20 from ⟨by norm_num, hη⟩))).comp η
        (contDiffAt_const.prodMk contDiffAt_id)
  rw [he, iteratedDeriv_const_mul (1 / Λ) (hs.of_le
    (WithTop.coe_le_coe.mpr (show (n : ℕ∞) ≤ ⊤ from le_top)))]
  congr 1
  simpa only [AxisEvaluation.mixedSeries_zero, Nat.zero_add] using
    AxisEvaluation.iteratedDeriv_eta window d.coefficients.epsilon_pos E.coefficients.2 0 0 n
      (by norm_num : (4 : ℝ) ∈ Ioo (-20 : ℝ) 20) hη

omit F in
theorem initialU_error_jet_bound (E : NaturalEntrance.CoefficientProfile d Λ C) (n : ℕ)
    {η : ℝ} (hη : η ∈ parameterInterval) :
    |iteratedDeriv n (fun ξ => (ofNatural E.family hΛ hsmall hδ hδT hP0).initialU ξ -
      NaturalAxisData.U j ξ) η| ≤ ReferenceJetBounds.jetConstant d.coefficients 0 n / Λ := by
  rw [initialU_error_jet hΛ hsmall hδ hδT hP0 E n hη, abs_mul,
    abs_of_pos (one_div_pos.mpr hΛ)]
  have hb := (ReferenceJetBounds.coefficient_jet_bound d.coefficients E.coefficients E.norm_ball
    0 n (p := (4, η)) (by norm_num)).2
  convert! mul_le_mul_of_nonneg_left hb (one_div_nonneg.mpr hΛ.le) using 1
  ring

end EndpointEstimates

/-! ## Uniform higher jets before choosing the normalization -/

theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.mpr (show (n : ℕ∞) ≤ ⊤ from le_top)

theorem compact_scalar_jets {J K : Set ℝ} (hJ : IsOpen J) (hK : IsCompact K)
    (hKJ : K ⊆ J) {g : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g J) (N : ℕ) :
    ∃ M ≥ 0, ∀ n ≤ N, ∀ η ∈ K, |iteratedDeriv n g η| ≤ M := by
  have hfield : ContDiffOn ℝ ∞ (fun p : Point => g p.2) (logDomain J hJ).carrier :=
    hg.comp contDiffOn_snd (fun _ hp => hp.2)
  obtain ⟨M, hM, hb⟩ := compact_stock_jet_bound hJ hK hKJ hfield 0 N
  refine ⟨M, hM, ?_⟩
  intro n hn η hη
  have hv := hb n hn 0 ⟨le_rfl, le_rfl⟩ η hη
  rw [parameterJet_eq_iteratedDeriv hJ hfield n (hKJ hη)] at hv
  exact hv

theorem local_composition_jet_bound {S U : Set ℝ} (hS : IsOpen S) (hU : IsOpen U)
    {f g : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f S) (hg : ContDiffOn ℝ ∞ g U)
    (hmap : MapsTo f S U) {x : ℝ} (hx : x ∈ S) (n : ℕ) {B D : ℝ}
    (hB : ∀ i ≤ n, |iteratedDeriv i g (f x)| ≤ B)
    (hD : ∀ i, 1 ≤ i → i ≤ n → |iteratedDeriv i f x| ≤ D ^ i) :
    |iteratedDeriv n (g ∘ f) x| ≤ n.factorial * B * D ^ n := by
  have hC : ∀ i ≤ n, ‖iteratedFDerivWithin ℝ i g U (f x)‖ ≤ B := by
    intro i hi
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
      ((hg.contDiffAt (hU.mem_nhds (hmap hx))).of_le (nat_le_infty i)) (hmap hx),
      norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    exact hB i hi
  have hI : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDerivWithin ℝ i f S x‖ ≤ D ^ i := by
    intro i hi hin
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hS.uniqueDiffOn
      ((hf.contDiffAt (hS.mem_nhds hx)).of_le (nat_le_infty i)) hx,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    exact hD i hi hin
  have hb := norm_iteratedFDerivWithin_comp_le hg hf (nat_le_infty n) hU.uniqueDiffOn
    hS.uniqueDiffOn hmap hx hC hI
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hS.uniqueDiffOn
    (((hg.contDiffAt (hU.mem_nhds (hmap hx))).comp x (hf.contDiffAt (hS.mem_nhds hx))).of_le
      (nat_le_infty n)) hx, norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at hb
  exact hb

theorem finite_majorant (v : ℕ → ℝ) (N : ℕ) :
    ∃ B, 1 ≤ B ∧ ∀ n ≤ N, v n ≤ B := by
  induction N with
  | zero => exact ⟨max 1 (v 0), le_max_left _ _, fun n hn => by
      have he : n = 0 := Nat.eq_zero_of_le_zero hn
      simpa only [he] using le_max_right (1 : ℝ) (v 0)⟩
  | succ N ih =>
    obtain ⟨B, hB, hb⟩ := ih
    refine ⟨max B (v (N + 1)), hB.trans (le_max_left _ _), ?_⟩
    intro n hn
    rcases Nat.eq_or_lt_of_le hn with he | hn'
    · simpa only [he] using le_max_right B (v (N + 1))
    · exact (hb n (Nat.le_of_lt_succ hn')).trans (le_max_left _ _)

section UniformEndpointJets

open NaturalProfile NaturalAxisCoefficients ReferencePath

variable {h j σ Λ : ℝ} {P0 : ℝ → ℝ} (d : AnalyticInputs h j σ P0)

include d in
theorem phase_smooth : ContDiffOn ℝ ∞ (realPhase h j σ) parameterInterval := by
  intro η hη
  have hc : ContDiffAt ℂ ∞ (axisPhase h j σ) (η : ℂ) :=
    (d.phase_analytic (η : ℂ) (d.real_mem_compact ⟨hη.1.le, hη.2.le⟩)).contDiffAt
  have hr : ContDiffAt ℝ ∞ (realPhase h j σ) η := by
    simpa only [axisPhase_ofReal, Complex.ofReal_re] using hc.real_of_complex
  exact hr.contDiffWithinAt

theorem log_smooth_positive : ContDiffOn ℝ ∞ Real.log (Ioi (0 : ℝ)) :=
  contDiffOn_id.log (fun _ hx => ne_of_gt hx)

theorem exists_uniform_logPhi_jets (hσ : 0 < σ)
    (hscale : AxisReference.stabilityScale d.coefficients.epsilon (profileErrorConstant d) ≤ Λ)
    (N : ℕ) :
    ∃ B ≥ 0, ∀ C, ∀ E : NaturalEntrance.CoefficientProfile d Λ C,
      ∀ Y ∈ Icc (0 : ℝ) (41 / 10), ∀ n ≤ N, ∀ η ∈ parameterInterval,
        |iteratedDeriv n (fun ξ => Real.log (AxisEvaluation.profile window d.coefficients.epsilon
          E.coefficients.1 (Y, ξ))) η| ≤ B := by
  obtain ⟨D, hD, hd⟩ := finite_majorant (fun n => ReferenceJetBounds.jetConstant d.coefficients 0
    n) N
  obtain ⟨B, hB, hb⟩ := compact_scalar_jets isOpen_Ioi (isCompact_Icc : IsCompact (Icc (1 / 8 : ℝ)
    D))
    (by intro x hx; exact lt_of_lt_of_le (by norm_num) hx.1) log_smooth_positive N
  obtain ⟨M, hM, hm⟩ := finite_majorant (fun n => n.factorial * B * D ^ n) N
  refine ⟨M, zero_le_one.trans hM, ?_⟩
  intro C E Y hY n hn η hη
  have hY20 : Y ∈ Ioo (-20 : ℝ) 20 := by constructor <;> linarith [hY.1, hY.2]
  have hY5 : |Y| ≤ 5 := (abs_le.mpr ⟨by linarith [hY.1], by linarith [hY.2]⟩)
  let φ : ℝ → ℝ := fun ξ => AxisEvaluation.profile window d.coefficients.epsilon E.coefficients.1
    (Y, ξ)
  have hφ : ContDiffOn ℝ ∞ φ parameterInterval :=
    (AxisEvaluation.profile_smooth window d.coefficients.epsilon_pos E.coefficients.1).comp
      (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hξ => ⟨hY20, hξ⟩)
  have hφlower (ξ : ℝ) (hξ : ξ ∈ parameterInterval) : 1 / 8 < φ ξ :=
    NaturalEntrance.coefficient_phi_lower d.coefficients hσ
      (NaturalEntrance.profileErrorConstant_nonneg d) hscale E.coefficients E.norm_error
      hY.1 hY.2 hξ
  have hφjet (i : ℕ) (hi : i ≤ N) : |iteratedDeriv i φ η| ≤ D := by
    have hiφ : iteratedDeriv i φ η =
        AxisEvaluation.mixedSeries window d.coefficients.epsilon E.coefficients.1 0 i (Y, η) := by
      simpa only [AxisEvaluation.mixedSeries_zero, Nat.zero_add] using
        AxisEvaluation.iteratedDeriv_eta window d.coefficients.epsilon_pos E.coefficients.1 0 0 i
          hY20 hη
    rw [hiφ]
    exact ((ReferenceJetBounds.coefficient_jet_bound d.coefficients E.coefficients E.norm_ball
      0 i (p := (Y, η)) hY5).1).trans (hd i hi)
  have hφmem : φ η ∈ Icc (1 / 8 : ℝ) D :=
    ⟨(hφlower η hη).le, (le_abs_self _).trans (hφjet 0 (Nat.zero_le N))⟩
  have hcomp := local_composition_jet_bound parameterInterval_open isOpen_Ioi hφ log_smooth_positive
    (fun ξ hξ => lt_trans (by norm_num) (hφlower ξ hξ)) hη n
    (fun i hi => hb i (hi.trans hn) (φ η) hφmem)
    (fun i hi hin => (hφjet i (hin.trans hn)).trans (le_self_pow₀ hD (by omega)))
  exact hcomp.trans (hm n hn)

noncomputable def normalizedNaturalLog {C : ℝ} (E : NaturalEntrance.CoefficientProfile d Λ C)
    (Y : ℝ) (η : ℝ) : ℝ :=
  Λ * realPhase h j σ η +
    Real.log (AxisEvaluation.profile window d.coefficients.epsilon E.coefficients.1 (Y, η))

theorem normalizedNaturalLog_smooth (hσ : 0 < σ)
    (hscale : AxisReference.stabilityScale d.coefficients.epsilon (profileErrorConstant d) ≤ Λ)
    {C : ℝ} (E : NaturalEntrance.CoefficientProfile d Λ C) {Y : ℝ} (hY : Y ∈ Icc (0 : ℝ) (41 / 10))
      :
    ContDiffOn ℝ ∞ (normalizedNaturalLog d E Y) parameterInterval := by
  have hY20 : Y ∈ Ioo (-20 : ℝ) 20 := by constructor <;> linarith [hY.1, hY.2]
  have hφ : ContDiffOn ℝ ∞
      (fun η => AxisEvaluation.profile window d.coefficients.epsilon E.coefficients.1 (Y, η))
        parameterInterval :=
    (AxisEvaluation.profile_smooth window d.coefficients.epsilon_pos E.coefficients.1).comp
      (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hη => ⟨hY20, hη⟩)
  refine (contDiffOn_const.mul (phase_smooth d)).add (hφ.log ?_)
  intro η hη
  exact (lt_trans (by norm_num : (0 : ℝ) < 1 / 8)
    (NaturalEntrance.coefficient_phi_lower d.coefficients hσ
      (NaturalEntrance.profileErrorConstant_nonneg d) hscale E.coefficients E.norm_error hY.1 hY.2
        hη)).ne'

theorem exists_normalized_natural_jets (hΛ : 0 < Λ) (hσ : 0 < σ)
    (hscale : AxisReference.stabilityScale d.coefficients.epsilon (profileErrorConstant d) ≤ Λ)
    (N : ℕ) :
    ∃ B, 1 ≤ B ∧ ∀ C, ∀ E : NaturalEntrance.CoefficientProfile d Λ C,
      ∀ Y ∈ Icc (0 : ℝ) (41 / 10), ∀ n ≤ N, ∀ η ∈ Icc (-1 : ℝ) 1,
        |iteratedDeriv n (normalizedNaturalLog d E Y) η| ≤ B := by
  obtain ⟨A, hA, ha⟩ := compact_scalar_jets parameterInterval_open isCompact_Icc
    original_interval_interior (phase_smooth d) N
  obtain ⟨L, hL, hl⟩ := exists_uniform_logPhi_jets d hσ hscale N
  refine ⟨1 + Λ * A + L, by nlinarith [mul_nonneg hΛ.le hA], ?_⟩
  intro C E Y hY n hn η hη
  have hηJ := original_interval_interior hη
  have hphase := ((phase_smooth d).contDiffAt (parameterInterval_open.mem_nhds hηJ)).of_le
    (nat_le_infty n)
  have hY20 : Y ∈ Ioo (-20 : ℝ) 20 := by constructor <;> linarith [hY.1, hY.2]
  have hφ := ((AxisEvaluation.profile_smooth window d.coefficients.epsilon_pos
    E.coefficients.1).contDiffAt
    ((AxisEvaluation.strip_isOpen window 20).mem_nhds ⟨hY20, hηJ⟩)).comp η
      (contDiffAt_const.prodMk contDiffAt_id)
  have hφpos := NaturalEntrance.coefficient_phi_lower d.coefficients hσ
    (NaturalEntrance.profileErrorConstant_nonneg d) hscale E.coefficients E.norm_error hY.1 hY.2 hηJ
  have hlog := (hφ.log (lt_trans (by norm_num : (0 : ℝ) < 1 / 8) hφpos).ne').of_le (nat_le_infty n)
  have hlog' : ContDiffAt ℝ n
      (fun ξ => Real.log (AxisEvaluation.profile window d.coefficients.epsilon E.coefficients.1 (Y,
        ξ))) η := by
    simpa only [Function.comp_apply, id_eq] using hlog
  have hphase' : ContDiffAt ℝ n (fun ξ => Λ * realPhase h j σ ξ) η := contDiffAt_const.mul hphase
  unfold normalizedNaturalLog
  change |iteratedDeriv n ((fun ξ => Λ * realPhase h j σ ξ) +
    (fun ξ => Real.log (AxisEvaluation.profile window d.coefficients.epsilon E.coefficients.1 (Y,
      ξ)))) η| ≤ _
  rw [iteratedDeriv_add hphase' hlog', iteratedDeriv_const_mul Λ hphase]
  calc
    _ ≤ |Λ * iteratedDeriv n (realPhase h j σ) η| +
        |iteratedDeriv n (fun ξ => Real.log (AxisEvaluation.profile window d.coefficients.epsilon
          E.coefficients.1 (Y, ξ))) η| := abs_add_le _ _
    _ ≤ Λ * A + L := by
      rw [abs_mul, abs_of_pos hΛ]
      exact add_le_add (mul_le_mul_of_nonneg_left (ha n hn η hη) hΛ.le) (hl C E Y hY n hn η hηJ)
    _ ≤ _ := by linarith

theorem natural_normalization_identity {C : ℝ} (E : NaturalEntrance.CoefficientProfile d Λ C)
    (hC : 0 < C) {X η : ℝ}
    (hφ : 0 < AxisEvaluation.profile window d.coefficients.epsilon E.coefficients.1 (Λ * X, η)) :
    E.family.f (X, η) = C⁻¹ * Real.exp (normalizedNaturalLog d E (Λ * X) η) := by
  rw [E.f_eq]
  change realAmplitude h j σ Λ C η *
    AxisEvaluation.profile window d.coefficients.epsilon E.coefficients.1 (Λ * X, η) = _
  unfold normalizedNaturalLog realAmplitude
  rw [Real.exp_add, Real.exp_log hφ]
  field_simp

end UniformEndpointJets

theorem exp_jet_bound_local {J : Set ℝ} (hJ : IsOpen J) {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ ∞ g J) {η : ℝ} (hη : η ∈ J) (n : ℕ) {B : ℝ}
    (hB : 1 ≤ B) (hb : ∀ i ≤ n, |iteratedDeriv i g η| ≤ B) :
    |iteratedDeriv n (fun ξ => Real.exp (g ξ)) η| ≤ n.factorial * Real.exp B * B ^ n := by
  apply local_composition_jet_bound hJ isOpen_univ hg Real.contDiff_exp.contDiffOn
    (mapsTo_univ _ _) hη n
  · intro i hi
    have he : iteratedDeriv i Real.exp = Real.exp := by simpa using iteratedDeriv_exp_const_mul i 1
    rw [he, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self (g η)).trans (hb 0 (Nat.zero_le n)))
  · intro i hi hin
    exact (hb i hin).trans (le_self_pow₀ hB (by omega))

theorem exp_jet_bound_local_of_upper {J : Set ℝ} (hJ : IsOpen J) {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ ∞ g J) {η : ℝ} (hη : η ∈ J) (n : ℕ) {B : ℝ}
    (hB : 1 ≤ B) (hvalue : g η ≤ B)
    (hb : ∀ i, 1 ≤ i → i ≤ n → |iteratedDeriv i g η| ≤ B) :
    |iteratedDeriv n (fun ξ => Real.exp (g ξ)) η| ≤ n.factorial * Real.exp B * B ^ n := by
  apply local_composition_jet_bound hJ isOpen_univ hg Real.contDiff_exp.contDiffOn
    (mapsTo_univ _ _) hη n
  · intro i hi
    have he : iteratedDeriv i Real.exp = Real.exp := by simpa using iteratedDeriv_exp_const_mul i 1
    rw [he, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr hvalue
  · intro i hi hin
    exact (hb i hi hin).trans (le_self_pow₀ hB (by omega))

theorem jet_transfer {A B : ℝ → ℝ} {η M ε : ℝ} (n : ℕ)
    (hA : ContDiffAt ℝ ∞ A η) (hB : ContDiffAt ℝ ∞ B η)
    (he : |iteratedDeriv n (fun ξ => A ξ - B ξ) η| ≤ ε)
    (hb : |iteratedDeriv n B η| ≤ M) : |iteratedDeriv n A η| ≤ M + ε := by
  have hd : iteratedDeriv n (fun ξ => A ξ - B ξ) η = iteratedDeriv n A η - iteratedDeriv n B η :=
    iteratedDeriv_sub (hA.of_le (nat_le_infty n)) (hB.of_le (nat_le_infty n))
  rw [hd] at he
  calc
    _ = |(iteratedDeriv n A η - iteratedDeriv n B η) + iteratedDeriv n B η| := by ring_nf
    _ ≤ |iteratedDeriv n A η - iteratedDeriv n B η| + |iteratedDeriv n B η| := abs_add_le _ _
    _ ≤ _ := by linarith

namespace StockReference

variable {J : Set ℝ} (R : StockReference J)

noncomputable def normalizedInitial (C : ℝ) (η : ℝ) : ℝ := Real.log C + R.initialLog η
noncomputable def normalizedLog (T κ w₁ w₂ C y : ℝ) (η : ℝ) : ℝ :=
  Real.log C + R.logAmplitude T κ w₁ w₂ (y, η)

theorem normalizedInitial_smooth (hJ : IsOpen J) (C : ℝ) :
    ContDiffOn ℝ ∞ (R.normalizedInitial C) J := contDiffOn_const.add (R.initialLog_smooth hJ)

theorem normalizedLog_smooth (hJ : IsOpen J) (T κ w₁ w₂ C y : ℝ) :
    ContDiffOn ℝ ∞ (R.normalizedLog T κ w₁ w₂ C y) J :=
  contDiffOn_const.add ((R.logAmplitude_smooth hJ T κ w₁ w₂).comp
    (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hη => ⟨mem_univ _, hη⟩))

theorem normalizedLog_hold (hJ : IsOpen J) {T κ w₁ w₂ C a y η : ℝ}
    (hw₂ : 0 < w₂) (ha : R.bigTime + w₁ + w₂ ≤ a) (hay : a ≤ y) (hη : η ∈ J) :
    R.normalizedLog T κ w₁ w₂ C y η =
      R.normalizedLog T κ w₁ w₂ C a η - (2 / 5 : ℝ) * (y - a) := by
  have he := logField_hold (T := T) (κ := κ) hw₂ hJ R.initialLog (R.angularStock_smooth hJ) ha hay
    hη
  unfold normalizedLog logAmplitude
  rw [he]
  ring

theorem normalizedLog_hold_positive_jet (hJ : IsOpen J) {T κ w₁ w₂ C a y η : ℝ}
    (hw₂ : 0 < w₂) (ha : R.bigTime + w₁ + w₂ ≤ a) (hay : a ≤ y) (hη : η ∈ J)
    {n : ℕ} (hn : 0 < n) :
    iteratedDeriv n (R.normalizedLog T κ w₁ w₂ C y) η =
      iteratedDeriv n (R.normalizedLog T κ w₁ w₂ C a) η := by
  have he : R.normalizedLog T κ w₁ w₂ C y =ᶠ[𝓝 η]
      (fun ξ => -(2 / 5 : ℝ) * (y - a) + R.normalizedLog T κ w₁ w₂ C a ξ) := by
    filter_upwards [hJ.mem_nhds hη] with ξ hξ
    rw [R.normalizedLog_hold hJ hw₂ ha hay hξ]
    ring
  rw [he.iteratedDeriv_eq n, iteratedDeriv_const_add hn]

theorem normalizedLog_bounds_of_control (hJ : IsOpen J) {K : Set ℝ} (hKJ : K ⊆ J)
    {N : ℕ} {T κ w₁ w₂ C B : ℝ} (hb : 0 ≤ R.bigTime) (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (hc : R.SmallLogControl K N 1 T κ w₁ w₂)
    (hi : ∀ n ≤ N, ∀ η ∈ K, |iteratedDeriv n (R.normalizedInitial C) η| ≤ B) :
    ∀ y, 0 ≤ y → ∀ η ∈ K,
      R.normalizedLog T κ w₁ w₂ C y η ≤ B + 1 ∧
      ∀ n ≤ N, 0 < n → |iteratedDeriv n (R.normalizedLog T κ w₁ w₂ C y) η| ≤ B + 1 := by
  let a := R.bigTime + w₁ + w₂
  have ha0 : 0 ≤ a := by dsimp [a]; linarith
  have ha : a ≤ R.finalTime := hc.finish_before.le
  have hvalue (y : ℝ) (hy : y ∈ Icc (0 : ℝ) a) (η : ℝ) (hη : η ∈ K) :
      R.normalizedLog T κ w₁ w₂ C y η ≤ B + 1 := by
    have he := hc.log_value y hy η hη
    have hb' := (le_abs_self (R.normalizedInitial C η)).trans (hi 0 (Nat.zero_le N) η hη)
    unfold normalizedLog normalizedInitial at *
    linarith [le_abs_self (R.logAmplitude T κ w₁ w₂ (y, η) - R.initialLog η)]
  have hjet (y : ℝ) (hy : y ∈ Icc (0 : ℝ) R.finalTime) (η : ℝ) (hη : η ∈ K)
      (n : ℕ) (hn : n ≤ N) (hn0 : 0 < n) :
      |iteratedDeriv n (R.normalizedLog T κ w₁ w₂ C y) η| ≤ B + 1 := by
    apply jet_transfer n
      ((R.normalizedLog_smooth hJ T κ w₁ w₂ C y).contDiffAt (hJ.mem_nhds (hKJ hη)))
      ((R.normalizedInitial_smooth hJ C).contDiffAt (hJ.mem_nhds (hKJ hη))) _ (hi n hn η hη)
    have he : (fun ξ => R.normalizedLog T κ w₁ w₂ C y ξ - R.normalizedInitial C ξ) =
        fun ξ => R.logAmplitude T κ w₁ w₂ (y, ξ) - R.initialLog ξ := by
      funext ξ
      unfold normalizedLog normalizedInitial
      ring
    rw [he]
    exact (hc.positive_log_jets y hy η hη n hn hn0).le
  intro y hy η hη
  constructor
  · by_cases hya : y ≤ a
    · exact hvalue y ⟨hy, hya⟩ η hη
    · have hay : a ≤ y := (lt_of_not_ge hya).le
      rw [R.normalizedLog_hold hJ hw₂ (show R.bigTime + w₁ + w₂ ≤ a from le_rfl) hay (hKJ hη)]
      have hv := hvalue a ⟨ha0, le_rfl⟩ η hη
      exact (sub_le_self _ (mul_nonneg (by norm_num) (sub_nonneg.mpr hay))).trans hv
  · intro n hn hn0
    by_cases hyf : y ≤ R.finalTime
    · exact hjet y ⟨hy, hyf⟩ η hη n hn hn0
    · rw [R.normalizedLog_hold_positive_jet hJ hw₂ hc.finish_before.le
        (le_of_not_ge hyf) (hKJ hη) hn0]
      exact hjet R.finalTime ⟨ha0.trans ha, le_rfl⟩ η hη n hn hn0

theorem endpointLog_jets_of_control (hJ : IsOpen J) {K : Set ℝ} (hKJ : K ⊆ J)
    {N : ℕ} {T κ w₁ w₂ C B : ℝ} (hb : 0 ≤ R.bigTime) (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (hc : R.SmallLogControl K N 1 T κ w₁ w₂)
    (hi : ∀ n ≤ N, ∀ η ∈ K, |iteratedDeriv n (R.normalizedInitial C) η| ≤ B) :
    ∀ n ≤ N, ∀ η ∈ K, |iteratedDeriv n (R.endpointLog T κ w₁ w₂ C) η| ≤
      B + 1 + (2 / 5 : ℝ) * Real.log (11 / 10 : ℝ) + |Real.log 220 / 2| := by
  let a := R.bigTime + w₁ + w₂
  have ha0 : 0 ≤ a := by dsimp [a]; linarith
  have ha : a ≤ R.finalTime := hc.finish_before.le
  have hgap : 0 < Real.log (11 / 10 : ℝ) := Real.log_pos (by norm_num)
  have hbound := R.normalizedLog_bounds_of_control hJ hKJ hb hw₁ hw₂ hc hi
  intro n hn η hη
  by_cases hn0 : n = 0
  · subst n
    rw [iteratedDeriv_zero]
    have he := R.normalizedLog_hold (C := C) (T := T) (κ := κ) hJ hw₂
      (show R.bigTime + w₁ + w₂ ≤ a from le_rfl) ha (hKJ hη)
    have hc0 := (hc.log_value a ⟨ha0, le_rfl⟩ η hη).le
    have hi0 := hi 0 (Nat.zero_le N) η hη
    simp only [iteratedDeriv_zero] at hi0
    have htime : 0 ≤ R.finalTime - a ∧ R.finalTime - a ≤ Real.log (11 / 10 : ℝ) := by
      have hg := R.finalTime_sub_bigTime
      dsimp [a] at *
      constructor <;> linarith
    have heq : R.endpointLog T κ w₁ w₂ C η = R.normalizedInitial C η +
        (R.logAmplitude T κ w₁ w₂ (a, η) - R.initialLog η) -
        (2 / 5 : ℝ) * (R.finalTime - a) + Real.log 220 / 2 := by
      unfold endpointLog normalizedInitial
      unfold normalizedLog at he
      linarith
    rw [heq]
    have hmul : |(2 / 5 : ℝ) * (R.finalTime - a)| ≤ (2 / 5 : ℝ) * Real.log (11 / 10 : ℝ) := by
      rw [abs_mul, abs_of_nonneg htime.1, abs_of_pos (by norm_num : (0 : ℝ) < 2 / 5)]
      exact mul_le_mul_of_nonneg_left htime.2 (by norm_num)
    calc
      _ ≤ |R.normalizedInitial C η| + |R.logAmplitude T κ w₁ w₂ (a, η) - R.initialLog η| +
          |(2 / 5 : ℝ) * (R.finalTime - a)| + |Real.log 220 / 2| := by
        exact (abs_add_le _ _).trans (add_le_add_left
          ((abs_sub _ _).trans (add_le_add_left (abs_add_le _ _) _)) _)
      _ ≤ _ := by linarith
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have heq : R.endpointLog T κ w₁ w₂ C =
        fun ξ => Real.log 220 / 2 + R.normalizedLog T κ w₁ w₂ C R.finalTime ξ := by
      funext ξ
      unfold endpointLog normalizedLog
      ring
    rw [heq, iteratedDeriv_const_add hnpos]
    exact ((hbound R.finalTime (ha0.trans ha) η hη).2 n hn hnpos).trans
      (by nlinarith [abs_nonneg (Real.log 220 / 2)])

theorem SmallLogControl.mono_tolerance {K : Set ℝ} {N : ℕ} {ε ε' T κ w₁ w₂ : ℝ}
    (hc : R.SmallLogControl K N ε T κ w₁ w₂) (hε : ε ≤ ε') :
    R.SmallLogControl K N ε' T κ w₁ w₂ where
  finish_before := hc.finish_before
  axial_jets := fun y hy η hη n hn => (hc.axial_jets y hy η hη n hn).trans_le hε
  positive_log_jets := fun y hy η hη n hn hn0 => (hc.positive_log_jets y hy η hη n hn hn0).trans_le
    hε
  log_value := fun y hy η hη => (hc.log_value y hy η hη).trans_le hε

theorem axialVelocity_jets_of_control (hJ : IsOpen J) {K : Set ℝ} (hKJ : K ⊆ J)
    {N : ℕ} {T κ w₁ w₂ B : ℝ} (hb : 0 ≤ R.bigTime) (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (hc : R.SmallLogControl K N 1 T κ w₁ w₂)
    (hi : ∀ n ≤ N, ∀ η ∈ K, |iteratedDeriv n R.initialU η| ≤ B) :
    ∀ y, 0 ≤ y → ∀ η ∈ K, ∀ n ≤ N,
      |iteratedDeriv n (fun ξ => R.axialVelocity T κ w₁ (y, ξ)) η| ≤ B + 1 := by
  have hfi : 0 ≤ R.finalTime := hb.trans R.finalTime_gt_bigTime.le
  have hbound (y : ℝ) (hy : y ∈ Icc (0 : ℝ) R.finalTime) (η : ℝ) (hη : η ∈ K)
      (n : ℕ) (hn : n ≤ N) :
      |iteratedDeriv n (fun ξ => R.axialVelocity T κ w₁ (y, ξ)) η| ≤ B + 1 := by
    apply jet_transfer n
      (((R.axialVelocity_smooth hJ T κ w₁).contDiffAt
        ((logDomain J hJ).isOpen.mem_nhds (show (y, η) ∈ (logDomain J hJ).carrier from
          ⟨mem_univ _, hKJ hη⟩))).comp η (contDiffAt_const.prodMk contDiffAt_id))
      ((R.initialU_smooth hJ).contDiffAt (hJ.mem_nhds (hKJ hη)))
      (hc.axial_jets y hy η hη n hn).le (hi n hn η hη)
  intro y hy η hη n hn
  by_cases hyf : y ≤ R.finalTime
  · exact hbound y ⟨hy, hyf⟩ η hη n hn
  · have he : (fun ξ => R.axialVelocity T κ w₁ (y, ξ)) =ᶠ[𝓝 η]
        (fun ξ => R.axialVelocity T κ w₁ (R.finalTime, ξ)) := by
      filter_upwards [hJ.mem_nhds (hKJ hη)] with ξ hξ
      exact axialField_hold hw₁ hJ R.initialU (R.axialStock_smooth hJ)
        (by linarith [hc.finish_before]) (le_of_not_ge hyf) hξ
    rw [he.iteratedDeriv_eq n]
    exact hbound R.finalTime ⟨hfi, le_rfl⟩ η hη n hn

theorem physicalF_postaxis_jet_bound (hJ : IsOpen J) {K : Set ℝ} (hKJ : K ⊆ J)
    {N : ℕ} {T κ w₁ w₂ C B X η : ℝ} (hb : 0 ≤ R.bigTime) (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (hC : 0 < C) (hB : 1 ≤ B) (hX : R.radius0 < X) (hη : η ∈ K)
    (hc : R.SmallLogControl K N 1 T κ w₁ w₂)
    (hi : ∀ n ≤ N, ∀ η ∈ K, |iteratedDeriv n (R.normalizedInitial C) η| ≤ B)
    {n : ℕ} (hn : n ≤ N) :
    |iteratedDeriv n (fun ξ => R.physicalF T κ w₁ w₂ (X, ξ)) η| ≤
      (n.factorial * Real.exp (B + 1) * (B + 1) ^ n) / C := by
  let y := R.logTime X
  have hy : 0 ≤ y := Real.log_nonneg ((one_le_div R.radius0_pos).mpr hX.le)
  have hbounds := R.normalizedLog_bounds_of_control hJ hKJ hb hw₁ hw₂ hc hi y hy η hη
  have he : (fun ξ => R.physicalF T κ w₁ w₂ (X, ξ)) =
      fun ξ => C⁻¹ * Real.exp (R.normalizedLog T κ w₁ w₂ C y ξ) := by
    funext ξ
    unfold physicalF
    rw [ite_eq_right (not_le.mpr hX)]
    unfold normalizedLog
    rw [Real.exp_add, Real.exp_log hC]
    rw [← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul]
    rfl
  have hs := R.normalizedLog_smooth hJ T κ w₁ w₂ C y
  rw [he, iteratedDeriv_const_mul
    C⁻¹ ((hs.exp.contDiffAt (hJ.mem_nhds (hKJ hη))).of_le (nat_le_infty n)),
    abs_mul, abs_of_pos (inv_pos.mpr hC)]
  have hexb := exp_jet_bound_local_of_upper hJ hs (hKJ hη) n (by linarith) hbounds.1
    (fun i hi hin => hbounds.2 i (hin.trans hn) hi)
  convert! mul_le_mul_of_nonneg_left hexb (inv_nonneg.mpr hC.le) using 1
  ring

theorem physicalU_postaxis_jet_bound (hJ : IsOpen J) {K : Set ℝ} (hKJ : K ⊆ J)
    {N : ℕ} {T κ w₁ w₂ B X η : ℝ} (hb : 0 ≤ R.bigTime) (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (hX : R.radius0 < X) (hη : η ∈ K) (hc : R.SmallLogControl K N 1 T κ w₁ w₂)
    (hi : ∀ n ≤ N, ∀ η ∈ K, |iteratedDeriv n R.initialU η| ≤ B)
    {n : ℕ} (hn : n ≤ N) :
    |iteratedDeriv n (fun ξ => R.physicalU T κ w₁ (X, ξ)) η| ≤ B + 1 := by
  have hy : 0 ≤ R.logTime X := Real.log_nonneg ((one_le_div R.radius0_pos).mpr hX.le)
  have he : (fun ξ => R.physicalU T κ w₁ (X, ξ)) =
      fun ξ => R.axialVelocity T κ w₁ (R.logTime X, ξ) := by
    funext ξ
    exact ite_eq_right (not_le.mpr hX)
  rw [he]
  exact R.axialVelocity_jets_of_control hJ hKJ hb hw₁ hw₂ hc hi (R.logTime X) hy η hη n hn

end StockReference

section SeedBounds

open NaturalProfile NaturalAxisCoefficients ReferencePath

variable {h j σ Λ : ℝ} {P0 : ℝ → ℝ} (d : AnalyticInputs h j σ P0)

theorem naturalU_slice_smooth {C : ℝ} (E : NaturalEntrance.CoefficientProfile d Λ C)
    {X : ℝ} (hY : Λ * X ∈ Ioo (-20 : ℝ) 20) :
    ContDiffOn ℝ ∞ (fun η => E.family.U (X, η)) parameterInterval :=
  E.family.natural.U_smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun _ hη => ⟨hY, hη⟩)

theorem naturalU_error_jet {C : ℝ} (E : NaturalEntrance.CoefficientProfile d Λ C)
    {X η : ℝ} (hY : Λ * X ∈ Ioo (-20 : ℝ) 20) (hη : η ∈ parameterInterval) (n : ℕ) :
    iteratedDeriv n (fun ξ => E.family.U (X, ξ) - NaturalAxisData.U j ξ) η =
      (1 / Λ) * AxisEvaluation.mixedSeries window d.coefficients.epsilon E.coefficients.2 0 n (Λ *
        X, η) := by
  have he : (fun ξ => E.family.U (X, ξ) - NaturalAxisData.U j ξ) =
      fun ξ => (1 / Λ) * AxisEvaluation.profile window d.coefficients.epsilon E.coefficients.2 (Λ *
        X, ξ) := by
    funext ξ
    rw [E.U_eq]
    change NaturalAxisData.U j ξ + (1 / Λ) * AxisEvaluation.profile window d.coefficients.epsilon
      E.coefficients.2 (Λ * X, ξ) - _ = _
    ring
  have hs : ContDiffAt ℝ ∞ (fun ξ => AxisEvaluation.profile window d.coefficients.epsilon
    E.coefficients.2 (Λ * X, ξ)) η :=
    ((AxisEvaluation.profile_smooth window d.coefficients.epsilon_pos E.coefficients.2).contDiffAt
      ((AxisEvaluation.strip_isOpen window 20).mem_nhds
        (show (Λ * X, η) ∈ AxisEvaluation.strip window 20 from ⟨hY, hη⟩))).comp η
          (contDiffAt_const.prodMk contDiffAt_id)
  rw [he, iteratedDeriv_const_mul (1 / Λ) (hs.of_le (nat_le_infty n))]
  congr 1
  simpa only [AxisEvaluation.mixedSeries_zero, Nat.zero_add] using
    AxisEvaluation.iteratedDeriv_eta window d.coefficients.epsilon_pos E.coefficients.2 0 0 n hY hη

theorem exists_naturalU_jets (hΛ : 0 < Λ) (N : ℕ) :
    ∃ B, 1 ≤ B ∧ ∀ C, ∀ E : NaturalEntrance.CoefficientProfile d Λ C,
      ∀ X, Λ * X ∈ Icc (0 : ℝ) (41 / 10) → ∀ n ≤ N, ∀ η ∈ Icc (-1 : ℝ) 1,
        |iteratedDeriv n (fun ξ => E.family.U (X, ξ)) η| ≤ B := by
  obtain ⟨B0, hB0, hb0⟩ := compact_scalar_jets parameterInterval_open isCompact_Icc
    original_interval_interior (uStar_smooth j).contDiffOn N
  obtain ⟨D, hD, hd⟩ := finite_majorant (fun n => ReferenceJetBounds.jetConstant d.coefficients 0
    n) N
  refine ⟨1 + B0 + D / Λ, by have := div_nonneg (zero_le_one.trans hD) hΛ.le; linarith, ?_⟩
  intro C E X hY n hn η hη
  have hY20 : Λ * X ∈ Ioo (-20 : ℝ) 20 := by constructor <;> linarith [hY.1, hY.2]
  have hηJ := original_interval_interior hη
  have herr : |iteratedDeriv n (fun ξ => E.family.U (X, ξ) - NaturalAxisData.U j ξ) η| ≤ D / Λ := by
    rw [naturalU_error_jet d E hY20 hηJ n, abs_mul, abs_of_pos (one_div_pos.mpr hΛ)]
    have hcoef := (ReferenceJetBounds.coefficient_jet_bound d.coefficients E.coefficients
      E.norm_ball
      0 n (p := (Λ * X, η)) (by rw [abs_of_nonneg hY.1]; linarith [hY.2])).2
    have hm := mul_le_mul_of_nonneg_left (hcoef.trans (hd n hn)) (one_div_nonneg.mpr hΛ.le)
    convert! hm using 1
    ring
  have htot := jet_transfer n
    ((naturalU_slice_smooth d E hY20).contDiffAt (parameterInterval_open.mem_nhds hηJ))
    (uStar_smooth j).contDiffAt herr (hb0 n hn η hη)
  exact htot.trans (by linarith)

theorem naturalF_jet_bound (hσ : 0 < σ)
    (hscale : AxisReference.stabilityScale d.coefficients.epsilon (profileErrorConstant d) ≤ Λ)
    {C : ℝ} (E : NaturalEntrance.CoefficientProfile d Λ C) (hC : 0 < C)
    {X η B : ℝ} (hY : Λ * X ∈ Icc (0 : ℝ) (41 / 10)) (hη : η ∈ Icc (-1 : ℝ) 1)
    {N n : ℕ} (hn : n ≤ N) (hB : 1 ≤ B)
    (hb : ∀ i ≤ N, ∀ ξ ∈ Icc (-1 : ℝ) 1, |iteratedDeriv i (normalizedNaturalLog d E (Λ * X)) ξ| ≤
      B) :
    |iteratedDeriv n (fun ξ => E.family.f (X, ξ)) η| ≤
      (n.factorial * Real.exp (B + 1) * (B + 1) ^ n) / C := by
  have hηJ := original_interval_interior hη
  have hs := normalizedNaturalLog_smooth d hσ hscale E hY
  have he : (fun ξ => E.family.f (X, ξ)) =ᶠ[𝓝 η]
      (fun ξ => C⁻¹ * Real.exp (normalizedNaturalLog d E (Λ * X) ξ)) := by
    filter_upwards [parameterInterval_open.mem_nhds hηJ] with ξ hξ
    exact natural_normalization_identity d E hC (lt_trans (by norm_num : (0 : ℝ) < 1 / 8)
      (NaturalEntrance.coefficient_phi_lower d.coefficients hσ
        (NaturalEntrance.profileErrorConstant_nonneg d) hscale E.coefficients E.norm_error hY.1
          hY.2 hξ))
  rw [he.iteratedDeriv_eq n, iteratedDeriv_const_mul
    C⁻¹ ((hs.exp.contDiffAt (parameterInterval_open.mem_nhds hηJ)).of_le (nat_le_infty n)),
    abs_mul, abs_of_pos (inv_pos.mpr hC)]
  have hbexp := exp_jet_bound_local parameterInterval_open hs hηJ n (by linarith : 1 ≤ B + 1)
    (fun i hi => (hb i (hi.trans hn) η hη).trans (by linarith))
  convert! mul_le_mul_of_nonneg_left hbexp (inv_nonneg.mpr hC.le) using 1
  ring

theorem normalizedInitial_jets (hΛ : 0 < Λ) (hsmall : NaturalAxisData.SmallParameters h j)
    (hσ : 0 < σ) (hscale : AxisReference.stabilityScale d.coefficients.epsilon
      (profileErrorConstant d) ≤ Λ)
    (hP0 : ContDiff ℝ ∞ P0) {C : ℝ} (E : NaturalEntrance.CoefficientProfile d Λ C) (hC : 0 < C)
    {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit) {N : ℕ} {B : ℝ}
    (hb : ∀ n ≤ N, ∀ η ∈ Icc (-1 : ℝ) 1, |iteratedDeriv n (normalizedNaturalLog d E 4) η| ≤ B) :
    ∀ n ≤ N, ∀ η ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv n ((ofNatural E.family hΛ hsmall hδ hδT hP0).normalizedInitial C) η| ≤ B := by
  intro n hn η hη
  have he : (ofNatural E.family hΛ hsmall hδ hδT hP0).normalizedInitial C =ᶠ[𝓝 η]
      normalizedNaturalLog d E 4 := by
    filter_upwards [parameterInterval_open.mem_nhds (original_interval_interior hη)] with ξ hξ
    exact normalized_initialLog_formula hΛ hsmall hδ hδT hP0 E hC
      (lt_trans (by norm_num : (0 : ℝ) < 1 / 8)
        (NaturalEntrance.coefficient_phi_lower d.coefficients hσ
          (NaturalEntrance.profileErrorConstant_nonneg d) hscale E.coefficients E.norm_error
          (by norm_num) (by norm_num) hξ)).ne'
  rw [he.iteratedDeriv_eq n]
  exact hb n hn η hη

/-- The actual held axial endpoint remains within the coefficient error
and the chosen continuation error of the prescribed axial datum, in every
fixed parameter derivative. -/
theorem endpointU_error_jet_bound (hΛ : 0 < Λ) (hsmall : NaturalAxisData.SmallParameters h j)
    (hP0 : ContDiff ℝ ∞ P0) {C : ℝ} (E : NaturalEntrance.CoefficientProfile d Λ C)
    {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    {N : ℕ} {ε T κ w₁ w₂ : ℝ}
    (hb : 0 ≤ (ofNatural E.family hΛ hsmall hδ hδT hP0).bigTime)
    (hc : (ofNatural E.family hΛ hsmall hδ hδT hP0).SmallLogControl (Icc (-1 : ℝ) 1) N ε T κ w₁ w₂)
    {n : ℕ} (hn : n ≤ N) {η : ℝ} (hη : η ∈ Icc (-1 : ℝ) 1) :
    |iteratedDeriv n (fun ξ => (ofNatural E.family hΛ hsmall hδ hδT hP0).endpointU T κ w₁ ξ -
      NaturalAxisData.U j ξ) η| ≤ ReferenceJetBounds.jetConstant d.coefficients 0 n / Λ + ε := by
  let R := ofNatural E.family hΛ hsmall hδ hδT hP0
  have hηJ := original_interval_interior hη
  have hfi : 0 ≤ R.finalTime := hb.trans R.finalTime_gt_bigTime.le
  have he : (fun ξ => (R.endpointU T κ w₁ ξ - NaturalAxisData.U j ξ) -
      (R.initialU ξ - NaturalAxisData.U j ξ)) =
      fun ξ => R.axialVelocity T κ w₁ (R.finalTime, ξ) - R.initialU ξ := by
    funext ξ
    unfold StockReference.endpointU
    ring
  apply jet_transfer n
    (((R.endpointU_smooth parameterInterval_open T κ w₁).contDiffAt
      (parameterInterval_open.mem_nhds hηJ)).sub (uStar_smooth j).contDiffAt)
    (((R.initialU_smooth parameterInterval_open).contDiffAt
      (parameterInterval_open.mem_nhds hηJ)).sub (uStar_smooth j).contDiffAt)
  · rw [he]
    exact (hc.axial_jets R.finalTime ⟨hfi, le_rfl⟩ η hη n hn).le
  · exact initialU_error_jet_bound hΛ hsmall hδ hδT hP0 E n hηJ

theorem endpointU_four_eta_jet_bound (hΛ : 0 < Λ) (hsmall : NaturalAxisData.SmallParameters h j)
    (hP0 : ContDiff ℝ ∞ P0) {C : ℝ} (E : NaturalEntrance.CoefficientProfile d Λ C)
    {δ : ℝ} (hδ : 0 < δ) (hδT : 2 * δ < rampLimit)
    {N : ℕ} {ε T κ w₁ w₂ : ℝ}
    (hb : 0 ≤ (ofNatural E.family hΛ hsmall hδ hδT hP0).bigTime)
    (hc : (ofNatural E.family hΛ hsmall hδ hδT hP0).SmallLogControl (Icc (-1 : ℝ) 1) N ε T κ w₁ w₂)
    {n : ℕ} (hn : n ≤ N) {η : ℝ} (hη : η ∈ Icc (-1 : ℝ) 1) :
    |iteratedDeriv n (fun ξ => (ofNatural E.family hΛ hsmall hδ hδT hP0).endpointU T κ w₁ ξ - 4 *
      ξ) η| ≤
      ReferenceJetBounds.jetConstant d.coefficients 0 n / Λ + ε + |j| := by
  let R := ofNatural E.family hΛ hsmall hδ hδT hP0
  have he : (fun ξ => R.endpointU T κ w₁ ξ - 4 * ξ) =
      fun ξ => j + (R.endpointU T κ w₁ ξ - NaturalAxisData.U j ξ) := by
    funext ξ
    unfold NaturalAxisData.U
    ring
  have hbnd := endpointU_error_jet_bound d hΛ hsmall hP0 E hδ hδT hb hc hn hη
  change |iteratedDeriv n (fun ξ => R.endpointU T κ w₁ ξ - 4 * ξ) η| ≤ _
  rw [he]
  by_cases hn0 : n = 0
  · subst n
    simp only [iteratedDeriv_zero] at hbnd ⊢
    exact (abs_add_le _ _).trans (by linarith)
  · rw [iteratedDeriv_const_add (Nat.pos_of_ne_zero hn0)]
    exact hbnd.trans (le_add_of_nonneg_right (abs_nonneg j))

/-- Uniform bounds for the full, actually constructed, seed.  The constants
are chosen after the scale and before `C`; the short ramp controls are chosen
after the concrete coefficient-space solution.  The bound is valid at every
nonnegative radius, so it also covers any later finite shape interval. -/
theorem ordered_seed_bounds (hΛ : 0 < Λ) (hsmall : NaturalAxisData.SmallParameters h j)
    (hσ : 0 < σ) (hscale : AxisReference.stabilityScale d.coefficients.epsilon
      (profileErrorConstant d) ≤ Λ)
    (hP0 : ContDiff ℝ ∞ P0) (N : ℕ) :
    ∃ B, 1 ≤ B ∧ ∃ K, 1 ≤ K ∧ ∃ BJ, 1 ≤ BJ ∧
      ∀ C, 0 < C → ∀ E : NaturalEntrance.CoefficientProfile d Λ C,
      ∀ δ, ∀ hδ : 0 < δ, ∀ hδT : 2 * δ < rampLimit,
      let R := ofNatural E.family hΛ hsmall hδ hδT hP0
      ∀ T κ w₁ w₂,
      δ ≤ R.bigTime → 0 < w₁ → 0 < w₂ →
      R.SmallLogControl (Icc (-1 : ℝ) 1) N 1 T κ w₁ w₂ →
      (∀ X, 0 ≤ X → ∀ η ∈ Icc (-1 : ℝ) 1, ∀ n ≤ N,
        |iteratedDeriv n (fun ξ => R.physicalF T κ w₁ w₂ (X, ξ)) η| ≤ K / C ∧
        |iteratedDeriv n (fun ξ => R.physicalU T κ w₁ (X, ξ)) η| ≤ B) ∧
      (∀ η ∈ Icc (-1 : ℝ) 1, ∀ n ≤ N,
        |iteratedDeriv n (R.endpointLog T κ w₁ w₂ C) η| ≤ BJ ∧
        |iteratedDeriv n (R.endpointU T κ w₁) η| ≤ B) := by
  obtain ⟨L, hL, hl⟩ := exists_normalized_natural_jets d hΛ hσ hscale N
  obtain ⟨U, hU, hu⟩ := exists_naturalU_jets d hΛ N
  obtain ⟨K, hK, hk⟩ := finite_majorant (fun n => n.factorial * Real.exp (L + 1) * (L + 1) ^ n) N
  let BJ := L + 1 + (2 / 5 : ℝ) * Real.log (11 / 10 : ℝ) + |Real.log 220 / 2|
  have hBJ : 1 ≤ BJ := by
    dsimp [BJ]
    have hg : 0 < Real.log (11 / 10 : ℝ) := Real.log_pos (by norm_num)
    nlinarith [abs_nonneg (Real.log 220 / 2)]
  refine ⟨U + 1, by linarith, K, hK, BJ, hBJ, ?_⟩
  intro C hC E δ hδ hδT R T κ w₁ w₂ hb hw₁ hw₂ hc
  let A := Input.ofNatural hΛ E.family
  have hb0 : 0 ≤ R.bigTime := hδ.le.trans hb
  have hiL : ∀ n ≤ N, ∀ η ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv n (R.normalizedInitial C) η| ≤ L :=
    normalizedInitial_jets d hΛ hsmall hσ hscale hP0 E hC hδ hδT
      (hl C E 4 (by norm_num))
  have hiU : ∀ n ≤ N, ∀ η ∈ Icc (-1 : ℝ) 1, |iteratedDeriv n R.initialU η| ≤ U := by
    have he : R.initialU = fun ξ => E.family.U (A.endpoint, ξ) :=
      funext (initialU_natural E.family hΛ hsmall hδ hδT hP0)
    intro n hn η hη
    rw [he]
    apply hu C E A.endpoint _ n hn η hη
    rw [show Λ * A.endpoint = 4 from A.scale_endpoint]
    norm_num
  constructor
  · intro X hX η hη n hn
    by_cases hx : X ≤ R.radius0
    · have hY : Λ * X ∈ Icc (0 : ℝ) (41 / 10) := by
        refine ⟨mul_nonneg hΛ.le hX, ?_⟩
        have hm := mul_le_mul_of_nonneg_left hx hΛ.le
        have he : Λ * R.radius0 = 4 := A.scale_endpoint
        rw [he] at hm
        linarith
      have hf : (fun ξ => R.physicalF T κ w₁ w₂ (X, ξ)) = fun ξ => E.family.f (X, ξ) := by
        funext ξ
        exact (physical_fields_natural E.family hΛ hsmall hδ hδT hP0 T κ w₁ w₂ hx).1
      have hUe : (fun ξ => R.physicalU T κ w₁ (X, ξ)) = fun ξ => E.family.U (X, ξ) := by
        funext ξ
        exact (physical_fields_natural E.family hΛ hsmall hδ hδT hP0 T κ w₁ w₂ hx).2
      rw [hf, hUe]
      exact ⟨(naturalF_jet_bound d hσ hscale E hC hY hη hn hL (hl C E (Λ * X) hY)).trans
        (div_le_div_of_nonneg_right (hk n hn) hC.le),
        (hu C E X hY n hn η hη).trans (by linarith)⟩
    · exact ⟨(R.physicalF_postaxis_jet_bound parameterInterval_open original_interval_interior
        hb0 hw₁ hw₂ hC hL (lt_of_not_ge hx) hη hc hiL hn).trans
          (div_le_div_of_nonneg_right (hk n hn) hC.le),
        R.physicalU_postaxis_jet_bound parameterInterval_open original_interval_interior
          hb0 hw₁ hw₂ (lt_of_not_ge hx) hη hc hiU hn⟩
  · intro η hη n hn
    refine ⟨R.endpointLog_jets_of_control parameterInterval_open original_interval_interior
      hb0 hw₁ hw₂ hc hiL n hn η hη, ?_⟩
    exact R.axialVelocity_jets_of_control parameterInterval_open original_interval_interior
      hb0 hw₁ hw₂ hc hiU R.finalTime (hb0.trans R.finalTime_gt_bigTime.le) η hη n hn

end SeedBounds

end NavierStokes.TransitionRamp

end
