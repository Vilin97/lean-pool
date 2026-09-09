/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.CorrectedPulseAmplitude
public import LeanPool.NavierStokesAndEuler.NavierStokes.SchedulePressure
public import LeanPool.NavierStokesAndEuler.NavierStokes.ProfileHistories
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

/-!
# Actual histories of the corrected outgoing fields

The first coordinate is the global logarithmic radius `y`, with normalized
`X = exp y`.  In particular smoothness here is not smoothness at the radial
axis.  Every history starts with the integral of the explicit ideal past and
then integrates the same corrected angular field and the same axial field.
The axial amplitude can be any smooth function of the parameter.

`I` and `J` omit the common physical factor `sqrt 2`.  For arbitrary entrance
radius `XR`, the physical factors are `XR` for `M,S` and `XR * sqrt (2*XR)`
for `I,J`.  These factors cancel from both normalized lags.
-/

noncomputable section

open Set Filter Function MeasureTheory
open scoped Topology ContDiff
open NavierStokes.OutgoingSchedule NavierStokes.OutgoingTail
open NavierStokes.AngularMomentReset NavierStokes.UniformAngularReset
open NavierStokes.StressAlgebra

namespace NavierStokes.OutgoingHistories

abbrev Point := ℝ × ℝ
abbrev Field := Point → ℝ
noncomputable abbrev dY := ProfileHistories.radialPartial
noncomputable abbrev dEta := ProfileHistories.parameterPartial

/-- The whole log-coordinate plane; this is not a radial domain at `X=0`. -/
noncomputable def logDomain : ProfileHistories.RadialDomain where
  carrier := univ
  isOpen := isOpen_univ
  scale_mem := by intros; trivial

theorem dY_hasDerivAt {f : Field} (hf : ContDiff ℝ ∞ f) (p : Point) :
    HasDerivAt (fun y => f (y, p.2)) (dY f p) p.1 :=
  ProfileHistories.radialPartial_hasDerivAt logDomain hf.contDiffOn (mem_univ p)

theorem dEta_hasDerivAt {f : Field} (hf : ContDiff ℝ ∞ f) (p : Point) :
    HasDerivAt (fun eta => f (p.1, eta)) (dEta f p) p.2 :=
  ProfileHistories.parameterPartial_hasDerivAt logDomain hf.contDiffOn (mem_univ p)

theorem dY_eq_deriv {f : Field} (hf : ContDiff ℝ ∞ f) (p : Point) :
    dY f p = deriv (fun y => f (y, p.2)) p.1 := (dY_hasDerivAt hf p).deriv.symm

theorem dEta_eq_deriv {f : Field} (hf : ContDiff ℝ ∞ f) (p : Point) :
    dEta f p = deriv (fun eta => f (p.1, eta)) p.2 := (dEta_hasDerivAt hf p).deriv.symm

theorem dY_smooth {f : Field} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (dY f) :=
  contDiffOn_univ.mp (ProfileHistories.radialPartial_smooth logDomain hf.contDiffOn)

theorem dEta_smooth {f : Field} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (dEta f) :=
  contDiffOn_univ.mp (ProfileHistories.parameterPartial_smooth logDomain hf.contDiffOn)

/-- A fixed incoming integral plus a finite log-coordinate integral. -/
noncomputable def history (initial : ℝ → ℝ) (f : Field) (p : Point) : ℝ :=
  initial p.2 + ProfileHistories.primitive f p

theorem prefix_smooth {initial : ℝ → ℝ} {f : Field}
    (hi : ContDiff ℝ ∞ initial) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (history initial f) :=
  (hi.comp contDiff_snd).add
    (contDiffOn_univ.mp (ProfileHistories.primitive_smooth logDomain hf.contDiffOn))

theorem prefix_hasDerivAt {initial : ℝ → ℝ} {f : Field}
    (hf : ContDiff ℝ ∞ f) (p : Point) :
    HasDerivAt (fun y => history initial f (y, p.2)) (f p) p.1 := by
  unfold history
  exact
    (ProfileHistories.primitive_hasDerivAt logDomain hf.contDiffOn (mem_univ p)).const_add
      (initial p.2)

theorem dEta_prefix {initial : ℝ → ℝ} {f : Field}
    (hi : ContDiff ℝ ∞ initial) (hf : ContDiff ℝ ∞ f) (p : Point) :
    dEta (history initial f) p = deriv initial p.2 + ProfileHistories.primitive (dEta f) p := by
  have hd := ((hi.differentiable (by simp) p.2).hasDerivAt).add
    (ProfileHistories.parameterPartial_hasDerivAt logDomain
      (ProfileHistories.primitive_smooth logDomain hf.contDiffOn) (mem_univ p))
  have he := (dEta_hasDerivAt (prefix_smooth hi hf) p).unique hd
  rw [ProfileHistories.parameterPartial_primitive logDomain hf.contDiffOn (mem_univ p)] at he
  exact he

theorem dEta_prefix_hasDerivAt {initial : ℝ → ℝ} {f : Field}
    (hi : ContDiff ℝ ∞ initial) (hf : ContDiff ℝ ∞ f) (p : Point) :
    HasDerivAt (fun y => dEta (history initial f) (y, p.2)) (dEta f p) p.1 := by
  have hd := (ProfileHistories.primitive_hasDerivAt logDomain
    (dEta_smooth hf).contDiffOn (mem_univ p)).const_add (deriv initial p.2)
  convert! hd using 1
  funext y
  exact dEta_prefix hi hf (y, p.2)

theorem dEta_mul {f g : Field} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (p : Point) :
    dEta (fun q => f q * g q) p = dEta f p * g p + f p * dEta g p :=
  (dEta_hasDerivAt (hf.mul hg) p).unique ((dEta_hasDerivAt hf p).mul (dEta_hasDerivAt hg p))

noncomputable def X (p : Point) : ℝ := Real.exp p.1

theorem X_pos (p : Point) : 0 < X p := Real.exp_pos _
theorem X_smooth : ContDiff ℝ ∞ X := contDiff_fst.exp
theorem X_hasDerivAt (p : Point) : HasDerivAt (fun y => X (y, p.2)) (X p) p.1 :=
  Real.hasDerivAt_exp p.1
theorem dEta_X (p : Point) : dEta X p = 0 :=
  (dEta_hasDerivAt X_smooth p).unique (hasDerivAt_const p.2 (Real.exp p.1))

variable {d : TailData} {K : ℝ}

noncomputable def E (w : ResetWitness d K) : Field := correctedAngular d w.coefficients
noncomputable def U (d : TailData) (Amp : ℝ → ℝ) : Field := axial d.core Amp
noncomputable def H (w : ResetWitness d K) (p : Point) : ℝ := Real.exp (p.1 / 2) * E w p

noncomputable def massWeight (d : TailData) (Amp : ℝ → ℝ) (p : Point) : ℝ := X p * U d Amp p
noncomputable def angularWeight (w : ResetWitness d K) (p : Point) : ℝ := X p * H w p
noncomputable def transportWeight (w : ResetWitness d K) (Amp : ℝ → ℝ) (p : Point) : ℝ :=
  X p * (U d Amp p * H w p)
noncomputable def energyDensity (w : ResetWitness d K) (Amp : ℝ → ℝ) (p : Point) : ℝ :=
  U d Amp p ^ 2 - E w p ^ 2 / 2
noncomputable def energyWeight (w : ResetWitness d K) (Amp : ℝ → ℝ) (p : Point) : ℝ :=
  X p * energyDensity w Amp p
noncomputable def pressureWeight (w : ResetWitness d K) (p : Point) : ℝ := E w p ^ 2 / 2

noncomputable def initialM (eta : ℝ) : ℝ := 4 * eta
noncomputable def initialI (d : TailData) (eta : ℝ) : ℝ := (5 / 8) * d.core.P * shape eta
noncomputable def initialJ (d : TailData) (eta : ℝ) : ℝ := (5 / 2) * d.core.P * eta * shape eta
noncomputable def initialS (d : TailData) (eta : ℝ) : ℝ :=
  16 * eta ^ 2 - (5 / 12) * d.core.P ^ 2 * shape eta ^ 2
noncomputable def initialPi (d : TailData) (eta : ℝ) : ℝ :=
  SchedulePressure.axisPressure d eta + (5 / 2) * d.core.P ^ 2 * shape eta ^ 2

noncomputable def M (d : TailData) (Amp : ℝ → ℝ) : Field := history initialM (massWeight d Amp)
noncomputable def I (w : ResetWitness d K) : Field := history (initialI d) (angularWeight w)
noncomputable def J (w : ResetWitness d K) (Amp : ℝ → ℝ) : Field := history (initialJ d)
  (transportWeight w Amp)
noncomputable def S (w : ResetWitness d K) (Amp : ℝ → ℝ) : Field := history (initialS d)
  (energyWeight w Amp)
noncomputable def Pi (w : ResetWitness d K) : Field := history (initialPi d) (pressureWeight w)

theorem E_smooth (w : ResetWitness d K) : ContDiff ℝ ∞ (E w) :=
  correctedAngular_contDiff d w.coefficients w.smooth
theorem E_pos (w : ResetWitness d K) (p : Point) : 0 < E w p := w.positive p
theorem U_smooth (d : TailData) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) :
    ContDiff ℝ ∞ (U d Amp) := axial_contDiff d.core ha
theorem H_smooth (w : ResetWitness d K) : ContDiff ℝ ∞ (H w) :=
  (contDiff_fst.div_const 2).exp.mul (E_smooth w)
theorem H_pos (w : ResetWitness d K) (p : Point) : 0 < H w p :=
  mul_pos (Real.exp_pos _) (E_pos w p)

theorem angularWeight_eq (w : ResetWitness d K) (p : Point) :
    angularWeight w p = Real.exp (3 * p.1 / 2) * E w p := by
  simp only [angularWeight, X, H, ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem massWeight_smooth (d : TailData) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) :
    ContDiff ℝ ∞ (massWeight d Amp) := X_smooth.mul (U_smooth d ha)
theorem angularWeight_smooth (w : ResetWitness d K) : ContDiff ℝ ∞ (angularWeight w) :=
  X_smooth.mul (H_smooth w)
theorem transportWeight_smooth (w : ResetWitness d K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) : ContDiff ℝ ∞ (transportWeight w Amp) :=
  X_smooth.mul ((U_smooth d ha).mul (H_smooth w))
theorem energyDensity_smooth (w : ResetWitness d K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) : ContDiff ℝ ∞ (energyDensity w Amp) :=
  ((U_smooth d ha).pow 2).sub (((E_smooth w).pow 2).div_const 2)
theorem energyWeight_smooth (w : ResetWitness d K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) : ContDiff ℝ ∞ (energyWeight w Amp) :=
  X_smooth.mul (energyDensity_smooth w ha)
theorem pressureWeight_smooth (w : ResetWitness d K) : ContDiff ℝ ∞ (pressureWeight w) :=
  ((E_smooth w).pow 2).div_const 2

theorem initialM_smooth : ContDiff ℝ ∞ initialM := contDiff_const.mul contDiff_id
theorem initialI_smooth (d : TailData) : ContDiff ℝ ∞ (initialI d) := contDiff_const.mul
  shape_contDiff
theorem initialJ_smooth (d : TailData) : ContDiff ℝ ∞ (initialJ d) :=
  (contDiff_const.mul contDiff_id).mul shape_contDiff
theorem initialS_smooth (d : TailData) : ContDiff ℝ ∞ (initialS d) :=
  (contDiff_const.mul (contDiff_id.pow 2)).sub (contDiff_const.mul (shape_contDiff.pow 2))
theorem initialPi_smooth (d : TailData) : ContDiff ℝ ∞ (initialPi d) :=
  (SchedulePressure.axisPressure_contDiff d).add (contDiff_const.mul (shape_contDiff.pow 2))

theorem M_smooth (d : TailData) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) :
    ContDiff ℝ ∞ (M d Amp) := prefix_smooth initialM_smooth (massWeight_smooth d ha)
theorem I_smooth (w : ResetWitness d K) : ContDiff ℝ ∞ (I w) :=
  prefix_smooth (initialI_smooth d) (angularWeight_smooth w)
theorem J_smooth (w : ResetWitness d K) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) :
    ContDiff ℝ ∞ (J w Amp) := prefix_smooth (initialJ_smooth d) (transportWeight_smooth w ha)
theorem S_smooth (w : ResetWitness d K) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) :
    ContDiff ℝ ∞ (S w Amp) := prefix_smooth (initialS_smooth d) (energyWeight_smooth w ha)
theorem Pi_smooth (w : ResetWitness d K) : ContDiff ℝ ∞ (Pi w) :=
  prefix_smooth (initialPi_smooth d) (pressureWeight_smooth w)

theorem M_hasDerivAt (d : TailData) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (p : Point) :
    HasDerivAt (fun y => M d Amp (y, p.2)) (X p * U d Amp p) p.1 :=
  prefix_hasDerivAt (massWeight_smooth d ha) p
theorem I_hasDerivAt (w : ResetWitness d K) (p : Point) :
    HasDerivAt (fun y => I w (y, p.2)) (X p * H w p) p.1 :=
  prefix_hasDerivAt (angularWeight_smooth w) p
theorem J_hasDerivAt (w : ResetWitness d K) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (p : Point) :
    HasDerivAt (fun y => J w Amp (y, p.2)) (X p * (U d Amp p * H w p)) p.1 :=
  prefix_hasDerivAt (transportWeight_smooth w ha) p
theorem S_hasDerivAt (w : ResetWitness d K) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (p : Point) :
    HasDerivAt (fun y => S w Amp (y, p.2)) (X p * energyDensity w Amp p) p.1 :=
  prefix_hasDerivAt (energyWeight_smooth w ha) p
theorem Pi_hasDerivAt (w : ResetWitness d K) (p : Point) :
    HasDerivAt (fun y => Pi w (y, p.2)) (E w p ^ 2 / 2) p.1 :=
  prefix_hasDerivAt (pressureWeight_smooth w) p

theorem dEta_massWeight (d : TailData) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (p : Point) :
    dEta (massWeight d Amp) p = X p * dEta (U d Amp) p := by
  unfold massWeight
  rw [dEta_mul X_smooth (U_smooth d ha), dEta_X, zero_mul, zero_add]

theorem dEta_angularWeight (w : ResetWitness d K) (p : Point) :
    dEta (angularWeight w) p = X p * dEta (H w) p := by
  unfold angularWeight
  rw [dEta_mul X_smooth (H_smooth w), dEta_X, zero_mul, zero_add]

theorem dEta_transportWeight (w : ResetWitness d K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) (p : Point) :
    dEta (transportWeight w Amp) p =
      X p * (dEta (U d Amp) p * H w p + U d Amp p * dEta (H w) p) := by
  unfold transportWeight
  rw [dEta_mul X_smooth ((U_smooth d ha).mul (H_smooth w)),
    dEta_X, zero_mul, zero_add, dEta_mul (U_smooth d ha) (H_smooth w)]

theorem dEta_energyDensity (w : ResetWitness d K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) (p : Point) :
    dEta (energyDensity w Amp) p =
      2 * U d Amp p * dEta (U d Amp) p - E w p * dEta (E w) p := by
  have he := (dEta_hasDerivAt (energyDensity_smooth w ha) p).unique
    (((dEta_hasDerivAt (U_smooth d ha) p).pow 2).sub
      (((dEta_hasDerivAt (E_smooth w) p).pow 2).div_const 2))
  simpa only [Nat.cast_ofNat, pow_one, Nat.reduceSub] using he.trans (by ring)

theorem dEta_energyWeight (w : ResetWitness d K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) (p : Point) :
    dEta (energyWeight w Amp) p = X p *
      (2 * U d Amp p * dEta (U d Amp) p - E w p * dEta (E w) p) := by
  unfold energyWeight
  rw [dEta_mul X_smooth (energyDensity_smooth w ha),
    dEta_X, zero_mul, zero_add, dEta_energyDensity w ha]

theorem dEta_pressureWeight (w : ResetWitness d K) (p : Point) :
    dEta (pressureWeight w) p = E w p * dEta (E w) p := by
  have he := (dEta_hasDerivAt (pressureWeight_smooth w) p).unique
    (((dEta_hasDerivAt (E_smooth w) p).pow 2).div_const 2)
  simpa only [Nat.cast_ofNat, pow_one, Nat.reduceSub] using he.trans (by ring)

theorem dEta_M_hasDerivAt (d : TailData) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (p : Point) :
    HasDerivAt (fun y => dEta (M d Amp) (y, p.2)) (X p * dEta (U d Amp) p) p.1 := by
  have hd := dEta_prefix_hasDerivAt initialM_smooth (massWeight_smooth d ha) p
  simp only [dEta_massWeight d ha] at hd
  exact hd

theorem dEta_I_hasDerivAt (w : ResetWitness d K) (p : Point) :
    HasDerivAt (fun y => dEta (I w) (y, p.2)) (X p * dEta (H w) p) p.1 := by
  have hd := dEta_prefix_hasDerivAt (initialI_smooth d) (angularWeight_smooth w) p
  simp only [dEta_angularWeight w] at hd
  exact hd

theorem dEta_J_hasDerivAt (w : ResetWitness d K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) (p : Point) :
    HasDerivAt (fun y => dEta (J w Amp) (y, p.2))
      (X p * (dEta (U d Amp) p * H w p + U d Amp p * dEta (H w) p)) p.1 := by
  have hd := dEta_prefix_hasDerivAt (initialJ_smooth d) (transportWeight_smooth w ha) p
  simp only [dEta_transportWeight w ha] at hd
  exact hd

theorem dEta_S_hasDerivAt (w : ResetWitness d K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) (p : Point) :
    HasDerivAt (fun y => dEta (S w Amp) (y, p.2))
      (X p * (2 * U d Amp p * dEta (U d Amp) p - E w p * dEta (E w) p)) p.1 := by
  have hd := dEta_prefix_hasDerivAt (initialS_smooth d) (energyWeight_smooth w ha) p
  simp only [dEta_energyWeight w ha] at hd
  exact hd

theorem dEta_Pi_hasDerivAt (w : ResetWitness d K) (p : Point) :
    HasDerivAt (fun y => dEta (Pi w) (y, p.2)) (E w p * dEta (E w) p) p.1 := by
  have hd := dEta_prefix_hasDerivAt (initialPi_smooth d) (pressureWeight_smooth w) p
  simp only [dEta_pressureWeight w] at hd
  exact hd

/-! ## Transport and the two genuine lags -/

noncomputable def XW (d : TailData) (Amp : ℝ → ℝ) (p : Point) : ℝ :=
  X p - 2 * axialExponent d.h * p.2 * M d Amp p - coordinateFactor p.2 * dEta (M d Amp) p
noncomputable def W (d : TailData) (Amp : ℝ → ℝ) (p : Point) : ℝ := XW d Amp p / X p
noncomputable def Ubar (d : TailData) (Amp : ℝ → ℝ) (p : Point) : ℝ := M d Amp p / X p

noncomputable def angularSource (w : ResetWitness d K) (Amp : ℝ → ℝ) (p : Point) : ℝ :=
  -W d Amp p * dY (H w) p - d.h * (1 - 2 * p.2 * U d Amp p) * H w p -
    (axialExponent d.h * p.2 + coordinateFactor p.2 * U d Amp p) * dEta (H w) p

noncomputable def Sq (w : ResetWitness d K) (Amp : ℝ → ℝ) (p : Point) : ℝ := angularSource w Amp p
  / H w p

noncomputable def Sn (w : ResetWitness d K) (Amp : ℝ → ℝ) (p : Point) : ℝ :=
  -W d Amp p * dY (U d Amp) p - velocityExponent d.h * (1 - 2 * p.2 * U d Amp p) * U d Amp p -
    (axialExponent d.h * p.2 + coordinateFactor p.2 * U d Amp p) * dEta (U d Amp) p -
      coordinateFactor p.2 * dEta (Pi w) p + 4 * velocityExponent d.h * p.2 * Pi w p +
        2 * p.2 * dY (Pi w) p

noncomputable def angularStock (w : ResetWitness d K) (Amp : ℝ → ℝ) (p : Point) : ℝ :=
  -(XW d Amp p * H w p) + (1 - d.h) * I w p - axialExponent d.h * p.2 * dEta (I w) p -
    coordinateFactor p.2 * dEta (J w Amp) p + 2 * (d.h - axialExponent d.h) * p.2 * J w Amp p

noncomputable def axialStock (w : ResetWitness d K) (Amp : ℝ → ℝ) (p : Point) : ℝ :=
  -(XW d Amp p * U d Amp p) + axialExponent d.h * (M d Amp p - p.2 * dEta (M d Amp) p) +
    4 * d.h * p.2 * S w Amp p - coordinateFactor p.2 * dEta (S w Amp) p +
      X p * (4 * velocityExponent d.h * p.2 * Pi w p - coordinateFactor p.2 * dEta (Pi w) p)

noncomputable def Qs (w : ResetWitness d K) (Amp : ℝ → ℝ) (p : Point) : ℝ :=
  angularStock w Amp p / (X p * H w p)
noncomputable def Ns (w : ResetWitness d K) (Amp : ℝ → ℝ) (p : Point) : ℝ := axialStock w Amp p / X
  p

theorem XW_smooth (d : TailData) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) :
    ContDiff ℝ ∞ (XW d Amp) :=
  (X_smooth.sub ((contDiff_const.mul contDiff_snd).mul (M_smooth d ha))).sub
    ((contDiff_const.sub (contDiff_snd.pow 2)).mul (dEta_smooth (M_smooth d ha)))
theorem W_smooth (d : TailData) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) :
    ContDiff ℝ ∞ (W d Amp) := (XW_smooth d ha).div X_smooth (fun p => (X_pos p).ne')
theorem Ubar_smooth (d : TailData) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) :
    ContDiff ℝ ∞ (Ubar d Amp) := (M_smooth d ha).div X_smooth (fun p => (X_pos p).ne')

theorem XW_eq_mul_W (d : TailData) (Amp : ℝ → ℝ) (p : Point) :
    XW d Amp p = X p * W d Amp p := by
  unfold W
  field_simp [(X_pos p).ne']

theorem Ubar_parameter (d : TailData) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (p : Point) :
    dEta (Ubar d Amp) p = dEta (M d Amp) p / X p := by
  exact (dEta_hasDerivAt (Ubar_smooth d ha) p).unique
    ((dEta_hasDerivAt (M_smooth d ha) p).div_const (X p))

theorem W_formula (d : TailData) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (p : Point) :
    W d Amp p = 1 - 2 * axialExponent d.h * p.2 * Ubar d Amp p -
      coordinateFactor p.2 * dEta (Ubar d Amp) p := by
  rw [Ubar_parameter d ha]
  unfold W XW Ubar
  field_simp [(X_pos p).ne']

theorem XW_hasDerivAt (d : TailData) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (p : Point) :
    HasDerivAt (fun y => XW d Amp (y, p.2))
      (X p * (1 - 2 * axialExponent d.h * p.2 * U d Amp p -
        coordinateFactor p.2 * dEta (U d Amp) p)) p.1 := by
  have hd := ((X_hasDerivAt p).sub ((M_hasDerivAt d ha p).const_mul
    (2 * axialExponent d.h * p.2))).sub
      ((dEta_M_hasDerivAt d ha p).const_mul (coordinateFactor p.2))
  convert! hd using 1
  ring

theorem angularStock_smooth (w : ResetWitness d K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) : ContDiff ℝ ∞ (angularStock w Amp) :=
  (((((XW_smooth d ha).mul (H_smooth w)).neg.add
    (contDiff_const.mul (I_smooth w))).sub
      ((contDiff_const.mul contDiff_snd).mul (dEta_smooth (I_smooth w)))).sub
        ((contDiff_const.sub (contDiff_snd.pow 2)).mul (dEta_smooth (J_smooth w ha)))).add
          ((contDiff_const.mul contDiff_snd).mul (J_smooth w ha))

theorem axialStock_smooth (w : ResetWitness d K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) : ContDiff ℝ ∞ (axialStock w Amp) :=
  (((((XW_smooth d ha).mul (U_smooth d ha)).neg.add
    (contDiff_const.mul ((M_smooth d ha).sub (contDiff_snd.mul (dEta_smooth (M_smooth d ha)))))).add
      ((contDiff_const.mul contDiff_snd).mul (S_smooth w ha))).sub
        ((contDiff_const.sub (contDiff_snd.pow 2)).mul (dEta_smooth (S_smooth w ha)))).add
          (X_smooth.mul (((contDiff_const.mul contDiff_snd).mul (Pi_smooth w)).sub
            ((contDiff_const.sub (contDiff_snd.pow 2)).mul (dEta_smooth (Pi_smooth w)))))

theorem Qs_smooth (w : ResetWitness d K) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) :
    ContDiff ℝ ∞ (Qs w Amp) :=
  (angularStock_smooth w ha).div (X_smooth.mul (H_smooth w))
    (fun p => (mul_pos (X_pos p) (H_pos w p)).ne')
theorem Ns_smooth (w : ResetWitness d K) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) :
    ContDiff ℝ ∞ (Ns w Amp) :=
  (axialStock_smooth w ha).div X_smooth (fun p => (X_pos p).ne')

theorem dY_Pi (w : ResetWitness d K) (p : Point) : dY (Pi w) p = E w p ^ 2 / 2 :=
  (dY_hasDerivAt (Pi_smooth w) p).unique (Pi_hasDerivAt w p)

theorem angularStock_hasDerivAt (w : ResetWitness d K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) (p : Point) :
    HasDerivAt (fun y => angularStock w Amp (y, p.2)) (X p * angularSource w Amp p) p.1 := by
  have hd := (((((XW_hasDerivAt d ha p).mul (dY_hasDerivAt (H_smooth w) p)).neg.add
    ((I_hasDerivAt w p).const_mul (1 - d.h))).sub
      ((dEta_I_hasDerivAt w p).const_mul (axialExponent d.h * p.2))).sub
        ((dEta_J_hasDerivAt w ha p).const_mul (coordinateFactor p.2))).add
          ((J_hasDerivAt w ha p).const_mul (2 * (d.h - axialExponent d.h) * p.2))
  change HasDerivAt (fun y => angularStock w Amp (y, p.2)) _ p.1 at hd
  apply hd.congr_deriv
  rw [XW_eq_mul_W]
  unfold angularSource
  ring

theorem axialStock_hasDerivAt (w : ResetWitness d K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) (p : Point) :
    HasDerivAt (fun y => axialStock w Amp (y, p.2)) (X p * Sn w Amp p) p.1 := by
  have hd := (((((XW_hasDerivAt d ha p).fun_mul (dY_hasDerivAt (U_smooth d ha) p)).fun_neg.fun_add
    (((M_hasDerivAt d ha p).fun_sub ((dEta_M_hasDerivAt d ha p).const_mul p.2)).const_mul
      (axialExponent d.h))).fun_add ((S_hasDerivAt w ha p).const_mul (4 * d.h * p.2))).fun_sub
        ((dEta_S_hasDerivAt w ha p).const_mul (coordinateFactor p.2))).fun_add
          ((X_hasDerivAt p).fun_mul (((Pi_hasDerivAt w p).const_mul (4 * velocityExponent d.h *
            p.2)).fun_sub
            ((dEta_Pi_hasDerivAt w p).const_mul (coordinateFactor p.2))))
  change HasDerivAt (fun y => axialStock w Amp (y, p.2)) _ p.1 at hd
  apply hd.congr_deriv
  rw [XW_eq_mul_W]
  unfold Sn
  rw [dY_Pi]
  unfold energyDensity axialExponent velocityExponent
  ring

/-- Equation (9), with every moment and derivative constructed above. -/
theorem Qs_integrated (w : ResetWitness d K) (Amp : ℝ → ℝ) (p : Point) :
    Qs w Amp p = -W d Amp p +
      ((1 - d.h) * I w p - axialExponent d.h * p.2 * dEta (I w) p -
        coordinateFactor p.2 * dEta (J w Amp) p +
          2 * (d.h - axialExponent d.h) * p.2 * J w Amp p) / (X p * H w p) := by
  unfold Qs angularStock
  rw [XW_eq_mul_W]
  field_simp [(X_pos p).ne', (H_pos w p).ne'] ; ring

/-- The axial row of (9) for the same corrected fields as `Qs`. -/
theorem Ns_integrated (w : ResetWitness d K) (Amp : ℝ → ℝ) (p : Point) :
    Ns w Amp p = -W d Amp p * U d Amp p +
      axialExponent d.h * (M d Amp p - p.2 * dEta (M d Amp) p) / X p +
        (4 * d.h * p.2 * S w Amp p - coordinateFactor p.2 * dEta (S w Amp) p) / X p +
          4 * velocityExponent d.h * p.2 * Pi w p - coordinateFactor p.2 * dEta (Pi w) p := by
  unfold Ns axialStock
  rw [XW_eq_mul_W]
  field_simp [(X_pos p).ne'] ; ring

theorem Qs_hasDerivAt (w : ResetWitness d K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) (p : Point) :
    HasDerivAt (fun y => Qs w Amp (y, p.2))
      (Sq w Amp p - (1 + dY (H w) p / H w p) * Qs w Amp p) p.1 := by
  have hd := (angularStock_hasDerivAt w ha p).fun_div
    ((X_hasDerivAt p).fun_mul (dY_hasDerivAt (H_smooth w) p))
      (mul_ne_zero (X_pos p).ne' (H_pos w p).ne')
  change HasDerivAt (fun y => Qs w Amp (y, p.2)) _ p.1 at hd
  apply hd.congr_deriv
  unfold Sq Qs
  field_simp [(X_pos p).ne', (H_pos w p).ne']

theorem Ns_hasDerivAt (w : ResetWitness d K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) (p : Point) :
    HasDerivAt (fun y => Ns w Amp (y, p.2)) (Sn w Amp p - Ns w Amp p) p.1 := by
  have hd := (axialStock_hasDerivAt w ha p).div (X_hasDerivAt p) (X_pos p).ne'
  change HasDerivAt (fun y => Ns w Amp (y, p.2)) _ p.1 at hd
  apply hd.congr_deriv
  unfold Ns
  field_simp [(X_pos p).ne']

/-- The angular ODE (6), using the derivative in the true log coordinate. -/
theorem Qs_equation (w : ResetWitness d K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) (p : Point) :
    deriv (fun y => Qs w Amp (y, p.2)) p.1 +
      (1 + dY (H w) p / H w p) * Qs w Amp p = Sq w Amp p := by
  rw [(Qs_hasDerivAt w ha p).deriv]
  ring

/-- The axial ODE (6); no derivative identity is an input hypothesis. -/
theorem Ns_equation (w : ResetWitness d K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) (p : Point) :
    deriv (fun y => Ns w Amp (y, p.2)) p.1 + Ns w Amp p = Sn w Amp p := by
  rw [(Ns_hasDerivAt w ha p).deriv]
  ring

theorem dEta_H (w : ResetWitness d K) (p : Point) :
    dEta (H w) p = Real.exp (p.1 / 2) * dEta (E w) p := by
  exact (dEta_hasDerivAt (H_smooth w) p).unique
    ((dEta_hasDerivAt (E_smooth w) p).const_mul (Real.exp (p.1 / 2)))

/-- The source as printed in (6), with logarithmic derivatives written as ratios. -/
theorem Sq_formula (w : ResetWitness d K) (Amp : ℝ → ℝ) (p : Point) :
    Sq w Amp p = -W d Amp p * (dY (H w) p / H w p) - d.h * (1 - 2 * p.2 * U d Amp p) -
      (axialExponent d.h * p.2 + coordinateFactor p.2 * U d Amp p) * (dEta (E w) p / E w p) := by
  unfold Sq angularSource
  rw [dEta_H]
  unfold H
  field_simp [(Real.exp_pos (p.1 / 2)).ne', (E_pos w p).ne']

/-! ## The incoming values and the unchanged pre-pulse region -/

theorem E_before (w : ResetWitness d K) (eta : ℝ) {y : ℝ} (hy : y ≤ d.core.endpoint) :
    E w (y, eta) = angular d.core.P d.core.dropLength d.core.lam (y, eta) := by
  have hout : y ∉ Ioo (d.releaseStart - 4) d.releaseStart := by
    intro h
    linarith [last_four_after_flatten d, flattenEnd_gt_core d, h.1]
  rw [E, correctedAngular_unchanged d w.coefficients eta hout, finalAngular_before d eta hy]

theorem E_ideal (w : ResetWitness d K) (eta : ℝ) {y : ℝ} (hy : y ≤ 0) :
    E w (y, eta) = d.core.P * shape eta * Real.exp (y / 10) := by
  rw [E_before w eta (hy.trans (SchedulePressure.endpoint_pos d).le)]
  exact angular_ideal d.core.dropLength_pos.le hy

theorem U_ideal (d : TailData) (Amp : ℝ → ℝ) (eta : ℝ) {y : ℝ} (hy : y ≤ 0) :
    U d Amp (y, eta) = 4 * eta := axial_ideal d.core Amp eta hy

theorem U_before_pulse (d : TailData) (Amp : ℝ → ℝ) (eta : ℝ) {y : ℝ} (hy : y ≤ d.core.pulseStart) :
    U d Amp (y, eta) = dropCoefficient d.core.m y * eta := axial_before_pulse d.core Amp eta hy

theorem M_eq_massMoment (d : TailData) (Amp : ℝ → ℝ) (y eta : ℝ) :
    M d Amp (y, eta) = massMoment d.core Amp eta y := rfl

theorem M_div_E_before (w : ResetWitness d K) (Amp : ℝ → ℝ) (eta : ℝ)
    {y : ℝ} (hy : y ≤ d.core.endpoint) :
    M d Amp (y, eta) / (X (y, eta) * E w (y, eta)) =
      massMoment d.core Amp eta y /
        (Real.exp y * angular d.core.P d.core.dropLength d.core.lam (y, eta)) := by
  rw [M_eq_massMoment, E_before w eta hy]
  rfl

@[simp] theorem history_zero (initial : ℝ → ℝ) (f : Field) (eta : ℝ) :
    history initial f (0, eta) = initial eta := by simp [history, ProfileHistories.primitive]

theorem dEta_history_zero {initial : ℝ → ℝ} {f : Field}
    (hi : ContDiff ℝ ∞ initial) (hf : ContDiff ℝ ∞ f) (eta : ℝ) :
    dEta (history initial f) (0, eta) = deriv initial eta := by
  rw [dEta_prefix hi hf]
  simp [ProfileHistories.primitive]

@[simp] theorem M_zero (d : TailData) (Amp : ℝ → ℝ) (eta : ℝ) :
    M d Amp (0, eta) = initialM eta := history_zero _ _ _
@[simp] theorem I_zero (w : ResetWitness d K) (eta : ℝ) :
    I w (0, eta) = initialI d eta := history_zero _ _ _
@[simp] theorem J_zero (w : ResetWitness d K) (Amp : ℝ → ℝ) (eta : ℝ) :
    J w Amp (0, eta) = initialJ d eta := history_zero _ _ _
@[simp] theorem S_zero (w : ResetWitness d K) (Amp : ℝ → ℝ) (eta : ℝ) :
    S w Amp (0, eta) = initialS d eta := history_zero _ _ _
@[simp] theorem Pi_zero (w : ResetWitness d K) (eta : ℝ) :
    Pi w (0, eta) = initialPi d eta := history_zero _ _ _
@[simp] theorem X_zero (eta : ℝ) : X (0, eta) = 1 := Real.exp_zero
@[simp] theorem H_zero (w : ResetWitness d K) (eta : ℝ) : H w (0, eta) = d.core.P * shape eta := by
  simp only [H, E_ideal w eta le_rfl, zero_div, Real.exp_zero, one_mul, mul_one]

theorem dEta_M_zero (d : TailData) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (eta : ℝ) :
    dEta (M d Amp) (0, eta) = 4 := by
  rw [M, dEta_history_zero initialM_smooth (massWeight_smooth d ha)]
  unfold initialM
  simpa only [id_eq, mul_one] using ((hasDerivAt_id eta).const_mul (4 : ℝ)).deriv

theorem dEta_I_zero (w : ResetWitness d K) (eta : ℝ) :
    dEta (I w) (0, eta) = ((5 / 8) * d.core.P) *
      (shape eta * (-(2 * eta / (1 + eta ^ 2)))) := by
  rw [I, dEta_history_zero (initialI_smooth d) (angularWeight_smooth w)]
  exact ((UniformAngularReset.shape_hasDerivAt eta).const_mul ((5 / 8) * d.core.P)).deriv

theorem dEta_J_zero (w : ResetWitness d K) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (eta : ℝ) :
    dEta (J w Amp) (0, eta) = ((5 / 2) * d.core.P) * shape eta +
      ((5 / 2) * d.core.P * eta) * (shape eta * (-(2 * eta / (1 + eta ^ 2)))) := by
  rw [J, dEta_history_zero (initialJ_smooth d) (transportWeight_smooth w ha)]
  unfold initialJ
  simpa only [id_eq, mul_one] using
    (((hasDerivAt_id eta).const_mul ((5 / 2) * d.core.P)).fun_mul
      (UniformAngularReset.shape_hasDerivAt eta)).deriv

/-- The incoming angular lag is fixed by the actual ideal-past integrals. -/
theorem Qs_initial (w : ResetWitness d K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) (eta : ℝ) :
    Qs w Amp (0, eta) =
      ((3 / 5) * (4 * (1 - 2 * d.h * eta ^ 2) - 1) - d.h * (1 - 8 * eta ^ 2) +
        (axialExponent d.h + 4 * coordinateFactor eta) * eta *
          (2 * eta / (1 + eta ^ 2))) / (8 / 5) := by
  rw [Qs_integrated]
  simp only [W, XW, X_zero, M_zero, dEta_M_zero d ha eta, I_zero, dEta_I_zero w eta,
    J_zero, dEta_J_zero w ha eta, H_zero, one_mul, div_one]
  unfold initialM initialI initialJ axialExponent coordinateFactor
  have hp := d.core.P_pos.ne'
  have hs := (shape_pos eta).ne'
  have he : (1 : ℝ) + eta ^ 2 ≠ 0 := by positivity
  field_simp [hp, hs, he] ; ring

/-! ## Exact endpoint cancellation for the common fields -/

theorem U_after_endpoint (d : TailData) (Amp : ℝ → ℝ) (eta : ℝ)
    {y : ℝ} (hy : d.core.endpoint ≤ y) : U d Amp (y, eta) = 0 :=
  axial_after_pulse d.core Amp eta hy

theorem angular_product_eq (w : ResetWitness d K) (Amp : ℝ → ℝ) (y eta : ℝ) :
    E w (y, eta) * U d Amp (y, eta) =
      angular d.core.P d.core.dropLength d.core.lam (y, eta) * U d Amp (y, eta) := by
  by_cases hy : y ≤ d.core.endpoint
  · rw [E_before w eta hy]
  · rw [U_after_endpoint d Amp eta (le_of_not_ge hy)]
    simp

theorem transportWeight_eq_core (w : ResetWitness d K) (Amp : ℝ → ℝ) (y eta : ℝ) :
    transportWeight w Amp (y, eta) = Real.exp (3 * y / 2) *
      angular d.core.P d.core.dropLength d.core.lam (y, eta) * U d Amp (y, eta) := by
  calc
    _ = angularWeight w (y, eta) * U d Amp (y, eta) := by
      unfold transportWeight angularWeight
      ring
    _ = Real.exp (3 * y / 2) * (E w (y, eta) * U d Amp (y, eta)) := by
      rw [angularWeight_eq]
      ring
    _ = _ := by rw [angular_product_eq]; ring

theorem J_eq_angularMoment (w : ResetWitness d K) (Amp : ℝ → ℝ) (y eta : ℝ) :
    Real.sqrt 2 * J w Amp (y, eta) = angularMoment d.core Amp eta y := by
  unfold J history ProfileHistories.primitive angularMoment
  rw [mul_add, ← intervalIntegral.integral_const_mul]
  congr 1
  · unfold initialJ
    ring
  · apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [transportWeight_eq_core]
    unfold U
    ring

theorem M_after_endpoint (d : TailData) (Amp : ℝ → ℝ) (eta : ℝ)
    {y : ℝ} (hy : d.core.endpoint ≤ y) : M d Amp (y, eta) = 0 :=
  massMoment_after_pulse d.core Amp eta hy

theorem J_after_endpoint (w : ResetWitness d K) (Amp : ℝ → ℝ) (eta : ℝ)
    {y : ℝ} (hy : d.core.endpoint ≤ y) : J w Amp (y, eta) = 0 := by
  have he := J_eq_angularMoment w Amp y eta
  rw [angularMoment_after_pulse d.core Amp eta hy] at he
  exact (mul_eq_zero.mp he).resolve_left (Real.sqrt_pos.mpr (by norm_num)).ne'

theorem dEta_M_after_endpoint (d : TailData) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (eta : ℝ)
    {y : ℝ} (hy : d.core.endpoint ≤ y) : dEta (M d Amp) (y, eta) = 0 := by
  have he : (fun eta => M d Amp (y, eta)) = (fun _ : ℝ => 0) :=
    funext (fun eta => M_after_endpoint d Amp eta hy)
  rw [dEta_eq_deriv (M_smooth d ha), he]
  exact deriv_const _ _

theorem dEta_J_after_endpoint (w : ResetWitness d K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) (eta : ℝ) {y : ℝ} (hy : d.core.endpoint ≤ y) :
    dEta (J w Amp) (y, eta) = 0 := by
  have he : (fun eta => J w Amp (y, eta)) = (fun _ : ℝ => 0) :=
    funext (fun eta => J_after_endpoint w Amp eta hy)
  rw [dEta_eq_deriv (J_smooth w ha), he]
  exact deriv_const _ _

theorem W_after_endpoint (d : TailData) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (eta : ℝ)
    {y : ℝ} (hy : d.core.endpoint ≤ y) : W d Amp (y, eta) = 1 := by
  simp [W, XW, M_after_endpoint d Amp eta hy, dEta_M_after_endpoint d ha eta hy, (X_pos _).ne']

theorem Qs_after_endpoint (w : ResetWitness d K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) (eta : ℝ) {y : ℝ} (hy : d.core.endpoint ≤ y) :
    Qs w Amp (y, eta) = -1 +
      ((1 - d.h) * I w (y, eta) - axialExponent d.h * eta * dEta (I w) (y, eta)) /
        (Real.exp (3 * y / 2) * E w (y, eta)) := by
  rw [Qs_integrated, W_after_endpoint d ha eta hy, J_after_endpoint w Amp eta hy,
    dEta_J_after_endpoint w ha eta hy]
  have he := angularWeight_eq w (y, eta)
  change X (y, eta) * H w (y, eta) = _ at he
  rw [he]
  ring

theorem Ns_after_endpoint (w : ResetWitness d K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) (eta : ℝ) {y : ℝ} (hy : d.core.endpoint ≤ y) :
    Ns w Amp (y, eta) =
      (4 * d.h * eta * S w Amp (y, eta) - coordinateFactor eta * dEta (S w Amp) (y, eta)) /
        Real.exp y + 4 * velocityExponent d.h * eta * Pi w (y, eta) -
          coordinateFactor eta * dEta (Pi w) (y, eta) := by
  rw [Ns_integrated, U_after_endpoint d Amp eta hy, M_after_endpoint d Amp eta hy,
    dEta_M_after_endpoint d ha eta hy]
  simp only [X, mul_zero, sub_zero, zero_div, zero_add]

/-! ## Identification with actual improper past integrals -/

theorem past_integrable {f : ℝ → ℝ} (hf : Continuous f)
    (h0 : IntegrableOn f (Iic (0 : ℝ))) (y : ℝ) : IntegrableOn f (Iic y) := by
  by_cases hy : 0 ≤ y
  · rw [← Iic_union_Ioc_eq_Iic hy]
    exact h0.union hf.integrableOn_Ioc
  · exact h0.mono_set (Iic_subset_Iic.mpr (le_of_not_ge hy))

theorem past_integral {f : ℝ → ℝ} (hf : Continuous f)
    (h0 : IntegrableOn f (Iic (0 : ℝ))) (y : ℝ) :
    (∫ t in Iic y, f t) = (∫ t in Iic (0 : ℝ), f t) + ∫ t in (0 : ℝ)..y, f t := by
  have he := intervalIntegral.integral_Iic_sub_Iic h0 (past_integrable hf h0 y)
  linarith

theorem exponential_past {f : ℝ → ℝ} (a b : ℝ) (hb : 0 < b)
    (he : ∀ y ≤ 0, f y = a * Real.exp (b * y)) :
    IntegrableOn f (Iic (0 : ℝ)) ∧ (∫ t in Iic (0 : ℝ), f t) = a / b := by
  refine ⟨IntegrableOn.congr_fun ((integrableOn_exp_mul_Iic hb 0).const_mul a)
    (fun t ht => (he t ht).symm) measurableSet_Iic, ?_⟩
  calc
    _ = ∫ t in Iic (0 : ℝ), a * Real.exp (b * t) :=
      setIntegral_congr_fun measurableSet_Iic (fun t ht => he t ht)
    _ = _ := by rw [integral_const_mul, integral_exp_mul_Iic hb]; simp [div_eq_mul_inv]

theorem mass_past (d : TailData) (Amp : ℝ → ℝ) (eta : ℝ) :
    IntegrableOn (fun y => massWeight d Amp (y, eta)) (Iic (0 : ℝ)) ∧
      (∫ y in Iic (0 : ℝ), massWeight d Amp (y, eta)) = initialM eta := by
  have he := exponential_past (f := fun y => massWeight d Amp (y, eta)) (4 * eta) 1 (by norm_num) ?_
  · simpa [initialM] using he
  · intro y hy
    unfold massWeight
    rw [U_ideal d Amp eta hy]
    simp [X, mul_comm]

theorem angularWeight_ideal (w : ResetWitness d K) (eta : ℝ) {y : ℝ} (hy : y ≤ 0) :
    angularWeight w (y, eta) = (d.core.P * shape eta) * Real.exp ((8 / 5 : ℝ) * y) := by
  rw [angularWeight_eq, E_ideal w eta hy]
  calc
    _ = (d.core.P * shape eta) * (Real.exp (3 * y / 2) * Real.exp (y / 10)) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

theorem angular_past (w : ResetWitness d K) (eta : ℝ) :
    IntegrableOn (fun y => angularWeight w (y, eta)) (Iic (0 : ℝ)) ∧
      (∫ y in Iic (0 : ℝ), angularWeight w (y, eta)) = initialI d eta := by
  have he := exponential_past (f := fun y => angularWeight w (y, eta))
    (d.core.P * shape eta) (8 / 5) (by norm_num) (fun y hy => angularWeight_ideal w eta hy)
  refine ⟨he.1, he.2.trans ?_⟩
  unfold initialI
  ring

theorem transport_past (w : ResetWitness d K) (Amp : ℝ → ℝ) (eta : ℝ) :
    IntegrableOn (fun y => transportWeight w Amp (y, eta)) (Iic (0 : ℝ)) ∧
      (∫ y in Iic (0 : ℝ), transportWeight w Amp (y, eta)) = initialJ d eta := by
  have he := exponential_past (f := fun y => transportWeight w Amp (y, eta))
    (4 * eta * (d.core.P * shape eta)) (8 / 5) (by norm_num) ?_
  · refine ⟨he.1, he.2.trans ?_⟩
    unfold initialJ
    ring
  · intro y hy
    have hw : transportWeight w Amp (y, eta) = U d Amp (y, eta) * angularWeight w (y, eta) := by
      unfold transportWeight angularWeight
      ring
    rw [hw, U_ideal d Amp eta hy, angularWeight_ideal w eta hy]
    ring

theorem weighted_square_ideal (w : ResetWitness d K) (b eta : ℝ) {y : ℝ} (hy : y ≤ 0) :
    Real.exp (b * y) * E w (y, eta) ^ 2 / 2 =
      (d.core.P ^ 2 * shape eta ^ 2 / 2) * Real.exp ((b + 1 / 5) * y) := by
  rw [E_ideal w eta hy]
  simp only [mul_pow]
  rw [pow_two (Real.exp _), ← Real.exp_add]
  calc
    _ = (d.core.P ^ 2 * shape eta ^ 2 / 2) *
        (Real.exp (b * y) * Real.exp (y / 10 + y / 10)) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

theorem energy_past (w : ResetWitness d K) (Amp : ℝ → ℝ) (eta : ℝ) :
    IntegrableOn (fun y => energyWeight w Amp (y, eta)) (Iic (0 : ℝ)) ∧
      (∫ y in Iic (0 : ℝ), energyWeight w Amp (y, eta)) = initialS d eta := by
  have hu := exponential_past (f := fun y => Real.exp y * U d Amp (y, eta) ^ 2)
    (16 * eta ^ 2) 1 (by norm_num) (by
      intro y hy
      rw [U_ideal d Amp eta hy, one_mul]
      ring)
  have he := exponential_past (f := fun y => Real.exp y * E w (y, eta) ^ 2 / 2)
    (d.core.P ^ 2 * shape eta ^ 2 / 2) (6 / 5) (by norm_num) (by
      intro y hy
      simpa only [one_mul, show (1 : ℝ) + 1 / 5 = 6 / 5 by norm_num] using
        weighted_square_ideal w 1 eta hy)
  have hf : (fun y => energyWeight w Amp (y, eta)) =
      (fun y => Real.exp y * U d Amp (y, eta) ^ 2 - Real.exp y * E w (y, eta) ^ 2 / 2) := by
    funext y
    unfold energyWeight X energyDensity
    ring
  rw [hf]
  refine ⟨hu.1.sub he.1, ?_⟩
  rw [integral_sub hu.1 he.1, hu.2, he.2]
  unfold initialS
  ring

theorem pressure_past (w : ResetWitness d K) (eta : ℝ) :
    IntegrableOn (fun y => pressureWeight w (y, eta)) (Iic (0 : ℝ)) ∧
      (∫ y in Iic (0 : ℝ), pressureWeight w (y, eta)) =
        (5 / 2) * d.core.P ^ 2 * shape eta ^ 2 := by
  have he := exponential_past (f := fun y => pressureWeight w (y, eta))
    (d.core.P ^ 2 * shape eta ^ 2 / 2) (1 / 5) (by norm_num) (by
      intro y hy
      simpa [pressureWeight] using weighted_square_ideal w 0 eta hy)
  exact ⟨he.1, he.2.trans (by ring)⟩

theorem M_eq_integral (d : TailData) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (y eta : ℝ) :
    M d Amp (y, eta) = ∫ t in Iic y, Real.exp t * U d Amp (t, eta) := by
  have he := past_integral (f := fun t => massWeight d Amp (t, eta))
    ((massWeight_smooth d ha).continuous.comp (continuous_id.prodMk continuous_const))
    (mass_past d Amp eta).1 y
  rw [(mass_past d Amp eta).2] at he
  exact he.symm

theorem I_eq_integral (w : ResetWitness d K) (y eta : ℝ) :
    I w (y, eta) = ∫ t in Iic y, Real.exp (3 * t / 2) * E w (t, eta) := by
  have he : (fun t => Real.exp (3 * t / 2) * E w (t, eta)) =
      (fun t => angularWeight w (t, eta)) := funext (fun t => (angularWeight_eq w (t, eta)).symm)
  rw [he]
  have hi := past_integral (f := fun t => angularWeight w (t, eta))
    ((angularWeight_smooth w).continuous.comp (continuous_id.prodMk continuous_const))
    (angular_past w eta).1 y
  rw [(angular_past w eta).2] at hi
  exact hi.symm

theorem J_eq_integral (w : ResetWitness d K) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (y eta : ℝ) :
    J w Amp (y, eta) = ∫ t in Iic y, Real.exp (3 * t / 2) * E w (t, eta) * U d Amp (t, eta) := by
  have he : (fun t => Real.exp (3 * t / 2) * E w (t, eta) * U d Amp (t, eta)) =
      (fun t => transportWeight w Amp (t, eta)) := by
    funext t
    have hi := angularWeight_eq w (t, eta)
    dsimp only at hi
    rw [← hi]
    unfold angularWeight transportWeight
    ring
  rw [he]
  have hi := past_integral (f := fun t => transportWeight w Amp (t, eta))
    ((transportWeight_smooth w ha).continuous.comp (continuous_id.prodMk continuous_const))
    (transport_past w Amp eta).1 y
  rw [(transport_past w Amp eta).2] at hi
  exact hi.symm

theorem S_eq_integral (w : ResetWitness d K) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (y eta : ℝ) :
    S w Amp (y, eta) = ∫ t in Iic y, Real.exp t * (U d Amp (t, eta) ^ 2 - E w (t, eta) ^ 2 / 2) :=
      by
  have hi := past_integral (f := fun t => energyWeight w Amp (t, eta))
    ((energyWeight_smooth w ha).continuous.comp (continuous_id.prodMk continuous_const))
    (energy_past w Amp eta).1 y
  rw [(energy_past w Amp eta).2] at hi
  exact hi.symm

theorem Pi_eq_past_integral (w : ResetWitness d K) (y eta : ℝ) :
    Pi w (y, eta) = SchedulePressure.axisPressure d eta +
      ∫ t in Iic y, E w (t, eta) ^ 2 / 2 := by
  have hi := past_integral (f := fun t => pressureWeight w (t, eta))
    ((pressureWeight_smooth w).continuous.comp (continuous_id.prodMk continuous_const))
    (pressure_past w eta).1 y
  rw [(pressure_past w eta).2] at hi
  change Pi w (y, eta) = SchedulePressure.axisPressure d eta +
    ∫ t in Iic y, pressureWeight w (t, eta)
  rw [hi]
  unfold Pi history ProfileHistories.primitive initialPi
  ring

/-! ## The same corrected field fixes the canonical pressure -/

theorem E_square_integrable (w : ResetWitness d K) (eta : ℝ) :
    Integrable (fun y => E w (y, eta) ^ 2) := by
  let changeE : ℝ → ℝ := fun y => E w (y, eta) ^ 2 - finalAngular d (y, eta) ^ 2
  have hc : Continuous changeE :=
    (((E_smooth w).continuous.comp (continuous_id.prodMk continuous_const)).pow 2).sub
      (((finalAngular_contDiff d).continuous.comp (continuous_id.prodMk continuous_const)).pow 2)
  have hs : support changeE ⊆ Icc (d.releaseStart - 4) d.releaseStart := by
    intro y hy
    by_contra hn
    apply hy
    have hout : y ∉ Ioo (d.releaseStart - 4) d.releaseStart := fun hm => hn ⟨hm.1.le, hm.2.le⟩
    simp [changeE, E, correctedAngular_unchanged d w.coefficients eta hout]
  have hi : Integrable changeE := hc.integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hs)
  convert! hi.add (SchedulePressure.angular_square_integrable d eta) using 1
  funext y
  dsimp [changeE]
  ring

theorem E_square_integral (w : ResetWitness d K) (eta : ℝ) :
    (∫ y, E w (y, eta) ^ 2) = ∫ y, finalAngular d (y, eta) ^ 2 := by
  have he := w.pressure_neutral eta
  change (∫ y, E w (y, eta) ^ 2 - finalAngular d (y, eta) ^ 2) = 0 at he
  rw [integral_sub (E_square_integrable w eta) (SchedulePressure.angular_square_integrable d eta)]
    at he
  linarith

theorem Pi_eq_future_integral (w : ResetWitness d K) (y eta : ℝ) :
    Pi w (y, eta) = -(1 / 2 : ℝ) * ∫ t in Ioi y, E w (t, eta) ^ 2 := by
  have hi := E_square_integrable w eta
  have hs := intervalIntegral.integral_Iic_add_Ioi
    (hi.integrableOn (s := Iic y)) (hi.integrableOn (s := Ioi y))
  have he := E_square_integral w eta
  rw [Pi_eq_past_integral, integral_div]
  unfold SchedulePressure.axisPressure
  linarith

theorem energyWeight_integrable (w : ResetWitness d K) (Amp : ℝ → ℝ) (eta : ℝ) :
    Integrable (fun y => energyWeight w Amp (y, eta)) := by
  exact CorrectedPulseAmplitude.energyIntegrand_integrable d w.coefficients (Amp eta) eta

theorem total_energy_eq (w : ResetWitness d K) (Amp : ℝ → ℝ) (eta : ℝ) :
    (∫ y, energyWeight w Amp (y, eta)) =
      CorrectedPulseAmplitude.totalEnergy d w.coefficients (Amp eta) eta := by
  unfold CorrectedPulseAmplitude.totalEnergy
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => by
    unfold energyWeight energyDensity X E U CorrectedPulseAmplitude.energyIntegrand
    dsimp only
    rw [PulseAmplitude.axial_eq_of_amplitude_eq d.core Amp (fun _ => Amp eta) eta y rfl])

theorem angular_source_continuous (w : ResetWitness d K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) (eta : ℝ) :
    Continuous (fun y => X (y, eta) * angularSource w Amp (y, eta)) := by
  have hc : Continuous (deriv (fun y => angularStock w Amp (y, eta))) :=
    ((angularStock_smooth w ha).comp (contDiff_id.prodMk contDiff_const)).continuous_deriv (by simp)
  have he : deriv (fun y => angularStock w Amp (y, eta)) =
      (fun y => X (y, eta) * angularSource w Amp (y, eta)) :=
    funext (fun y => (angularStock_hasDerivAt w ha (y, eta)).deriv)
  rwa [he] at hc

theorem axial_source_continuous (w : ResetWitness d K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) (eta : ℝ) :
    Continuous (fun y => X (y, eta) * Sn w Amp (y, eta)) := by
  have hc : Continuous (deriv (fun y => axialStock w Amp (y, eta))) :=
    ((axialStock_smooth w ha).comp (contDiff_id.prodMk contDiff_const)).continuous_deriv (by simp)
  have he : deriv (fun y => axialStock w Amp (y, eta)) =
      (fun y => X (y, eta) * Sn w Amp (y, eta)) :=
    funext (fun y => (axialStock_hasDerivAt w ha (y, eta)).deriv)
  rwa [he] at hc

theorem angularStock_eq_source_primitive (w : ResetWitness d K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) (y eta : ℝ) :
    angularStock w Amp (y, eta) = angularStock w Amp (0, eta) +
      ∫ t in (0 : ℝ)..y, X (t, eta) * angularSource w Amp (t, eta) := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y => angularStock w Amp (y,
    eta))
    (fun t _ => angularStock_hasDerivAt w ha (t, eta))
    ((angular_source_continuous w ha eta).intervalIntegrable 0 y)
  linarith

theorem axialStock_eq_source_primitive (w : ResetWitness d K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) (y eta : ℝ) :
    axialStock w Amp (y, eta) = axialStock w Amp (0, eta) +
      ∫ t in (0 : ℝ)..y, X (t, eta) * Sn w Amp (t, eta) := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y => axialStock w Amp (y,
    eta))
    (fun t _ => axialStock_hasDerivAt w ha (t, eta))
    ((axial_source_continuous w ha eta).intervalIntegrable 0 y)
  linarith

theorem exponential_integral_left {f : ℝ → ℝ} (a b : ℝ) (hb : 0 < b)
    (he : ∀ t ≤ 0, f t = a * Real.exp (b * t)) {y : ℝ} (hy : y ≤ 0) :
    (∫ t in Iic y, f t) = (a / b) * Real.exp (b * y) := by
  calc
    _ = ∫ t in Iic y, a * Real.exp (b * t) :=
      setIntegral_congr_fun measurableSet_Iic (fun t ht => he t (ht.trans hy))
    _ = _ := by rw [integral_const_mul, integral_exp_mul_Iic hb]; ring

/-- A left closed interval determines the derivative even at its endpoint. -/
theorem derivative_from_left {f g : ℝ → ℝ} {v y : ℝ} (hy : y ≤ 0)
    (hf : DifferentiableAt ℝ f y) (hg : HasDerivAt g v y)
    (he : ∀ t ≤ 0, f t = g t) : HasDerivAt f v y := by
  have hd : deriv f y = v := (uniqueDiffOn_Iic 0 y hy).eq_deriv _
    hf.hasDerivAt.hasDerivWithinAt (hg.hasDerivWithinAt.congr_of_mem he hy)
  simpa only [hd] using hf.hasDerivAt

theorem M_ideal (d : TailData) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp)
    (eta : ℝ) {y : ℝ} (hy : y ≤ 0) : M d Amp (y, eta) = 4 * eta * Real.exp y := by
  rw [M_eq_integral d ha]
  have he := exponential_integral_left (f := fun t => Real.exp t * U d Amp (t, eta))
    (4 * eta) 1 (by norm_num) (by
      intro t ht
      rw [U_ideal d Amp eta ht]
      simp [mul_comm]) hy
  simpa using he

theorem dEta_M_ideal (d : TailData) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp)
    (eta : ℝ) {y : ℝ} (hy : y ≤ 0) : dEta (M d Amp) (y, eta) = 4 * Real.exp y := by
  have he : (fun eta => M d Amp (y, eta)) = (fun eta => 4 * eta * Real.exp y) :=
    funext (fun eta => M_ideal d ha eta hy)
  have hd := (((hasDerivAt_id eta).const_mul (4 : ℝ)).mul_const (Real.exp y))
  rw [dEta_eq_deriv (M_smooth d ha), he]
  simpa only [id_eq, mul_one] using hd.deriv

theorem W_ideal (d : TailData) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp)
    (eta : ℝ) {y : ℝ} (hy : y ≤ 0) : W d Amp (y, eta) = 1 - 4 * (1 - 2 * d.h * eta ^ 2) := by
  unfold W XW
  rw [M_ideal d ha eta hy, dEta_M_ideal d ha eta hy]
  unfold X axialExponent coordinateFactor
  field_simp [(Real.exp_pos y).ne'] ; ring

theorem Pi_ideal (w : ResetWitness d K) (eta : ℝ) {y : ℝ} (hy : y ≤ 0) :
    Pi w (y, eta) = SchedulePressure.axisPressure d eta +
      (5 / 2) * d.core.P ^ 2 * shape eta ^ 2 * Real.exp (y / 5) := by
  rw [Pi_eq_past_integral]
  have he := exponential_integral_left (f := fun t => E w (t, eta) ^ 2 / 2)
    (d.core.P ^ 2 * shape eta ^ 2 / 2) (1 / 5) (by norm_num) (by
      intro t ht
      simpa only [zero_mul, Real.exp_zero, one_mul, zero_add] using weighted_square_ideal w 0 eta
        ht) hy
  rw [he, show (1 / 5 : ℝ) * y = y / 5 by ring]
  ring

noncomputable def shapeRate (eta : ℝ) : ℝ := 2 * eta / (1 + eta ^ 2)

theorem dEta_E_ideal (w : ResetWitness d K) (eta : ℝ) {y : ℝ} (hy : y ≤ 0) :
    dEta (E w) (y, eta) = -(E w (y, eta) * shapeRate eta) := by
  have he : (fun eta => E w (y, eta)) =
      (fun eta => d.core.P * shape eta * Real.exp (y / 10)) := funext (fun eta => E_ideal w eta hy)
  have hd := ((UniformAngularReset.shape_hasDerivAt eta).const_mul d.core.P).mul_const (Real.exp (y
    / 10))
  rw [dEta_eq_deriv (E_smooth w), he, hd.deriv, E_ideal w eta hy]
  unfold shapeRate
  ring

theorem dY_H_ideal (w : ResetWitness d K) (eta : ℝ) {y : ℝ} (hy : y ≤ 0) :
    dY (H w) (y, eta) = (3 / 5) * H w (y, eta) := by
  have he : ∀ t ≤ 0, H w (t, eta) = (d.core.P * shape eta) * Real.exp ((3 / 5 : ℝ) * t) := by
    intro t ht
    unfold H
    rw [E_ideal w eta ht]
    calc
      _ = (d.core.P * shape eta) * (Real.exp (t / 2) * Real.exp (t / 10)) := by ring
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  have hg := (((hasDerivAt_id y).const_mul (3 / 5 : ℝ)).exp).const_mul (d.core.P * shape eta)
  have hd := derivative_from_left hy (dY_hasDerivAt (H_smooth w) (y, eta)).differentiableAt hg he
  rw [(dY_hasDerivAt (H_smooth w) (y, eta)).unique hd, he y hy]
  simp only [id_eq]
  ring

theorem dY_U_ideal (d : TailData) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp)
    (eta : ℝ) {y : ℝ} (hy : y ≤ 0) : dY (U d Amp) (y, eta) = 0 := by
  have hd := derivative_from_left hy (dY_hasDerivAt (U_smooth d ha) (y, eta)).differentiableAt
    (hasDerivAt_const y (4 * eta)) (fun t ht => U_ideal d Amp eta ht)
  exact (dY_hasDerivAt (U_smooth d ha) (y, eta)).unique hd

theorem dEta_U_ideal (d : TailData) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp)
    (eta : ℝ) {y : ℝ} (hy : y ≤ 0) : dEta (U d Amp) (y, eta) = 4 := by
  have he : (fun eta => U d Amp (y, eta)) = (fun eta => 4 * eta) := funext (fun eta => U_ideal d
    Amp eta hy)
  rw [dEta_eq_deriv (U_smooth d ha), he]
  simp

theorem dEta_Pi_ideal (w : ResetWitness d K) (eta : ℝ) {y : ℝ} (hy : y ≤ 0) :
    dEta (Pi w) (y, eta) = deriv (SchedulePressure.axisPressure d) eta -
      5 * d.core.P ^ 2 * shape eta ^ 2 * shapeRate eta * Real.exp (y / 5) := by
  have he : (fun eta => Pi w (y, eta)) = (fun eta => SchedulePressure.axisPressure d eta +
      (5 / 2) * d.core.P ^ 2 * shape eta ^ 2 * Real.exp (y / 5)) := funext (fun eta => Pi_ideal w
        eta hy)
  have hd := ((SchedulePressure.axisPressure_contDiff d).differentiable (by simp)
    eta).hasDerivAt.fun_add
    ((((UniformAngularReset.shape_hasDerivAt eta).fun_pow 2).const_mul ((5 / 2) * d.core.P ^
      2)).mul_const
      (Real.exp (y / 5)))
  rw [dEta_eq_deriv (Pi_smooth w), he, hd.deriv]
  unfold shapeRate
  simp only [Nat.cast_ofNat, pow_one, Nat.reduceSub]
  ring

/-! ## The ideal past also fixes the source primitives -/

noncomputable def incomingSq (d : TailData) (eta : ℝ) : ℝ :=
  (3 / 5) * (4 * (1 - 2 * d.h * eta ^ 2) - 1) - d.h * (1 - 8 * eta ^ 2) +
    (axialExponent d.h + 4 * coordinateFactor eta) * eta * shapeRate eta

theorem Sq_ideal (w : ResetWitness d K) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp)
    (eta : ℝ) {y : ℝ} (hy : y ≤ 0) : Sq w Amp (y, eta) = incomingSq d eta := by
  rw [Sq_formula, W_ideal d ha eta hy, U_ideal d Amp eta hy,
    dY_H_ideal w eta hy, dEta_E_ideal w eta hy]
  unfold incomingSq
  field_simp [(H_pos w (y, eta)).ne', (E_pos w (y, eta)).ne'] ; ring

theorem angularSource_weight (w : ResetWitness d K) (Amp : ℝ → ℝ) (p : Point) :
    X p * angularSource w Amp p = angularWeight w p * Sq w Amp p := by
  unfold angularWeight Sq
  field_simp [(H_pos w p).ne']

theorem angular_source_past (w : ResetWitness d K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) (eta : ℝ) :
    IntegrableOn (fun y => X (y, eta) * angularSource w Amp (y, eta)) (Iic (0 : ℝ)) ∧
      (∫ y in Iic (0 : ℝ), X (y, eta) * angularSource w Amp (y, eta)) =
        angularStock w Amp (0, eta) := by
  have hp := exponential_past (f := fun y => X (y, eta) * angularSource w Amp (y, eta))
    (d.core.P * shape eta * incomingSq d eta) (8 / 5) (by norm_num) (by
      intro y hy
      rw [angularSource_weight, angularWeight_ideal w eta hy, Sq_ideal w ha eta hy]
      ring)
  refine ⟨hp.1, hp.2.trans ?_⟩
  have hq := Qs_initial w ha eta
  change angularStock w Amp (0, eta) / (X (0, eta) * H w (0, eta)) = incomingSq d eta / (8 / 5) at
    hq
  rw [X_zero, H_zero, one_mul] at hq
  rw [(div_eq_iff (mul_pos d.core.P_pos (shape_pos eta)).ne').mp hq]
  ring

theorem angularStock_eq_source_integral (w : ResetWitness d K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) (y eta : ℝ) :
    angularStock w Amp (y, eta) =
      ∫ t in Iic y, X (t, eta) * angularSource w Amp (t, eta) := by
  have hi := past_integral (angular_source_continuous w ha eta) (angular_source_past w ha eta).1 y
  rw [(angular_source_past w ha eta).2] at hi
  exact (angularStock_eq_source_primitive w ha y eta).trans hi.symm

/-- The regular source-integral definition of `Q_s`, including its actual past. -/
theorem Qs_eq_source_integral (w : ResetWitness d K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) (y eta : ℝ) :
    Qs w Amp (y, eta) =
      (∫ t in Iic y, Real.exp (3 * t / 2) * E w (t, eta) * Sq w Amp (t, eta)) /
        (Real.exp (3 * y / 2) * E w (y, eta)) := by
  unfold Qs
  rw [angularStock_eq_source_integral w ha]
  have he := angularWeight_eq w (y, eta)
  change X (y, eta) * H w (y, eta) = _ at he
  rw [he]
  congr 1
  apply setIntegral_congr_fun measurableSet_Iic
  intro t _
  dsimp only
  rw [angularSource_weight, angularWeight_eq]

noncomputable def incomingSnConstant (d : TailData) (eta : ℝ) : ℝ :=
  -4 * velocityExponent d.h * eta * (1 - 8 * eta ^ 2) -
    4 * (axialExponent d.h + 4 * coordinateFactor eta) * eta -
      coordinateFactor eta * deriv (SchedulePressure.axisPressure d) eta +
        4 * velocityExponent d.h * eta * SchedulePressure.axisPressure d eta

noncomputable def incomingSnGrowing (d : TailData) (eta : ℝ) : ℝ :=
  d.core.P ^ 2 * shape eta ^ 2 *
    (5 * coordinateFactor eta * shapeRate eta + (10 * velocityExponent d.h + 1) * eta)

theorem Sn_ideal (w : ResetWitness d K) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp)
    (eta : ℝ) {y : ℝ} (hy : y ≤ 0) :
    Sn w Amp (y, eta) = incomingSnConstant d eta + incomingSnGrowing d eta * Real.exp (y / 5) := by
  unfold Sn
  rw [dY_U_ideal d ha eta hy, U_ideal d Amp eta hy, dEta_U_ideal d ha eta hy,
    Pi_ideal w eta hy, dEta_Pi_ideal w eta hy, dY_Pi, E_ideal w eta hy]
  have he : Real.exp (y / 10) ^ 2 = Real.exp (y / 5) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simp only [mul_pow, he]
  unfold incomingSnConstant incomingSnGrowing
  ring

theorem dEta_S_zero (w : ResetWitness d K) {Amp : ℝ → ℝ} (ha : ContDiff ℝ ∞ Amp) (eta : ℝ) :
    dEta (S w Amp) (0, eta) = 32 * eta +
      (5 / 6) * d.core.P ^ 2 * shape eta ^ 2 * shapeRate eta := by
  rw [S, dEta_history_zero (initialS_smooth d) (energyWeight_smooth w ha)]
  have hd := (((hasDerivAt_id eta).pow 2).const_mul (16 : ℝ)).sub
    (((UniformAngularReset.shape_hasDerivAt eta).pow 2).const_mul ((5 / 12) * d.core.P ^ 2))
  change HasDerivAt (initialS d) _ eta at hd
  rw [hd.deriv]
  unfold shapeRate
  simp only [Nat.cast_ofNat, pow_one, Nat.reduceSub, id_eq]
  ring

theorem axialStock_initial (w : ResetWitness d K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) (eta : ℝ) :
    axialStock w Amp (0, eta) = incomingSnConstant d eta + (5 / 6) * incomingSnGrowing d eta := by
  unfold axialStock XW
  rw [X_zero, M_zero, dEta_M_zero d ha, U_ideal d Amp eta le_rfl, S_zero,
    dEta_S_zero w ha, Pi_ideal w eta le_rfl, dEta_Pi_ideal w eta le_rfl]
  simp only [zero_div, Real.exp_zero, mul_one, one_mul]
  unfold initialM initialS incomingSnConstant incomingSnGrowing axialExponent velocityExponent
    coordinateFactor
  ring

theorem exponential_sum_past {f : ℝ → ℝ} (a b c e : ℝ) (hb : 0 < b) (he : 0 < e)
    (hf : ∀ y ≤ 0, f y = a * Real.exp (b * y) + c * Real.exp (e * y)) :
    IntegrableOn f (Iic (0 : ℝ)) ∧ (∫ y in Iic (0 : ℝ), f y) = a / b + c / e := by
  have h1 := (integrableOn_exp_mul_Iic hb 0).const_mul a
  have h2 := (integrableOn_exp_mul_Iic he 0).const_mul c
  refine ⟨IntegrableOn.congr_fun (h1.add h2) (fun y hy => (hf y hy).symm) measurableSet_Iic, ?_⟩
  calc
    _ = ∫ y in Iic (0 : ℝ), a * Real.exp (b * y) + c * Real.exp (e * y) :=
      setIntegral_congr_fun measurableSet_Iic (fun y hy => hf y hy)
    _ = _ := by
      rw [integral_add h1 h2, integral_const_mul, integral_const_mul,
        integral_exp_mul_Iic hb, integral_exp_mul_Iic he]
      simp [div_eq_mul_inv]

theorem axial_source_past (w : ResetWitness d K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) (eta : ℝ) :
    IntegrableOn (fun y => X (y, eta) * Sn w Amp (y, eta)) (Iic (0 : ℝ)) ∧
      (∫ y in Iic (0 : ℝ), X (y, eta) * Sn w Amp (y, eta)) = axialStock w Amp (0, eta) := by
  have hp := exponential_sum_past (f := fun y => X (y, eta) * Sn w Amp (y, eta))
    (incomingSnConstant d eta) 1 (incomingSnGrowing d eta) (6 / 5) (by norm_num) (by norm_num) (by
      intro y hy
      rw [Sn_ideal w ha eta hy]
      have he : Real.exp y * Real.exp (y / 5) = Real.exp ((6 / 5 : ℝ) * y) := by
        rw [← Real.exp_add]
        congr 1
        ring
      unfold X
      rw [one_mul]
      calc
        _ = incomingSnConstant d eta * Real.exp y +
            incomingSnGrowing d eta * (Real.exp y * Real.exp (y / 5)) := by ring
        _ = _ := by rw [he])
  refine ⟨hp.1, hp.2.trans ?_⟩
  rw [axialStock_initial w ha]
  ring

theorem axialStock_eq_source_integral (w : ResetWitness d K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) (y eta : ℝ) :
    axialStock w Amp (y, eta) = ∫ t in Iic y, X (t, eta) * Sn w Amp (t, eta) := by
  have hi := past_integral (axial_source_continuous w ha eta) (axial_source_past w ha eta).1 y
  rw [(axial_source_past w ha eta).2] at hi
  exact (axialStock_eq_source_primitive w ha y eta).trans hi.symm

/-- The regular source-integral definition of `N_s`, including its actual past. -/
theorem Ns_eq_source_integral (w : ResetWitness d K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) (y eta : ℝ) :
    Ns w Amp (y, eta) = (∫ t in Iic y, Real.exp t * Sn w Amp (t, eta)) / Real.exp y := by
  unfold Ns
  rw [axialStock_eq_source_integral w ha]
  rfl

/-! ## Entrance-radius factors -/

noncomputable def physicalX (XR : ℝ) (p : Point) : ℝ := XR * X p
noncomputable def physicalH (XR : ℝ) (w : ResetWitness d K) (p : Point) : ℝ := Real.sqrt (2 * XR) *
  H w p
noncomputable def physicalM (XR : ℝ) (d : TailData) (Amp : ℝ → ℝ) (p : Point) : ℝ := XR * M d Amp p
noncomputable def physicalI (XR : ℝ) (w : ResetWitness d K) (p : Point) : ℝ := XR * Real.sqrt (2 *
  XR) * I w p
noncomputable def physicalJ (XR : ℝ) (w : ResetWitness d K) (Amp : ℝ → ℝ) (p : Point) : ℝ :=
  XR * Real.sqrt (2 * XR) * J w Amp p
noncomputable def physicalS (XR : ℝ) (w : ResetWitness d K) (Amp : ℝ → ℝ) (p : Point) : ℝ := XR * S
  w Amp p

theorem physicalH_eq (XR : ℝ) (hXR : 0 < XR) (w : ResetWitness d K) (p : Point) :
    physicalH XR w p = Real.sqrt (2 * physicalX XR p) * E w p := by
  unfold physicalH physicalX X H
  rw [show 2 * (XR * Real.exp p.1) = (2 * XR) * Real.exp p.1 by ring,
    Real.sqrt_mul (by positivity : 0 ≤ 2 * XR), AngularMomentReset.sqrt_exp_half]
  ring

theorem physicalM_eq_integral (XR : ℝ) (d : TailData) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) (y eta : ℝ) :
    physicalM XR d Amp (y, eta) = ∫ t in Iic y, physicalX XR (t, eta) * U d Amp (t, eta) := by
  unfold physicalM
  rw [M_eq_integral d ha, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Iic
  intro t _
  dsimp [physicalX, X]
  ring

theorem physicalI_eq_integral (XR : ℝ) (w : ResetWitness d K) (y eta : ℝ) :
    physicalI XR w (y, eta) = ∫ t in Iic y, physicalX XR (t, eta) * physicalH XR w (t, eta) := by
  unfold physicalI
  rw [I_eq_integral, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Iic
  intro t _
  dsimp only
  have he := angularWeight_eq w (t, eta)
  change X (t, eta) * H w (t, eta) = _ at he
  rw [← he]
  unfold physicalX physicalH
  ring

theorem physicalJ_eq_integral (XR : ℝ) (w : ResetWitness d K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) (y eta : ℝ) :
    physicalJ XR w Amp (y, eta) =
      ∫ t in Iic y, physicalX XR (t, eta) * (U d Amp (t, eta) * physicalH XR w (t, eta)) := by
  unfold physicalJ
  rw [J_eq_integral w ha, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Iic
  intro t _
  dsimp only
  have he := angularWeight_eq w (t, eta)
  change X (t, eta) * H w (t, eta) = _ at he
  rw [← he]
  unfold physicalX physicalH
  ring

theorem physicalS_eq_integral (XR : ℝ) (w : ResetWitness d K) {Amp : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ Amp) (y eta : ℝ) :
    physicalS XR w Amp (y, eta) =
      ∫ t in Iic y, physicalX XR (t, eta) * (U d Amp (t, eta) ^ 2 - E w (t, eta) ^ 2 / 2) := by
  unfold physicalS
  rw [S_eq_integral w ha, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Iic
  intro t _
  dsimp [physicalX, X]
  ring

/-- The common angular scaling cancels exactly from the source-integral lag. -/
theorem Qs_dilation (XR : ℝ) (hXR : 0 < XR) (w : ResetWitness d K)
    (Amp : ℝ → ℝ) (p : Point) :
    (XR * Real.sqrt (2 * XR) * angularStock w Amp p) /
      (physicalX XR p * physicalH XR w p) = Qs w Amp p := by
  unfold physicalX physicalH Qs
  have hs : Real.sqrt (2 * XR) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  field_simp [hXR.ne', hs, (X_pos p).ne', (H_pos w p).ne']

/-- The common axial scaling cancels exactly from the source-integral lag. -/
theorem Ns_dilation (XR : ℝ) (hXR : 0 < XR) (w : ResetWitness d K)
    (Amp : ℝ → ℝ) (p : Point) :
    (XR * axialStock w Amp p) / physicalX XR p = Ns w Amp p := by
  unfold physicalX Ns
  field_simp [hXR.ne', (X_pos p).ne']

noncomputable def p1 (XR : ℝ) (w : ResetWitness d K) (Amp : ℝ → ℝ) (p : Point) : ℝ :=
  physicalX XR p * Qs w Amp p / (1 - 2 * d.h * p.2 ^ 2)
noncomputable def p2 (XR : ℝ) (w : ResetWitness d K) (Amp : ℝ → ℝ) (p : Point) : ℝ :=
  physicalX XR p * Ns w Amp p / ((1 - 2 * d.h * p.2 ^ 2) * E w p)

theorem p1_dilation (XR : ℝ) (w : ResetWitness d K) (Amp : ℝ → ℝ) (p : Point) :
    p1 XR w Amp p = XR * p1 1 w Amp p := by
  unfold p1 physicalX
  ring

theorem p2_dilation (XR : ℝ) (w : ResetWitness d K) (Amp : ℝ → ℝ) (p : Point) :
    p2 XR w Amp p = XR * p2 1 w Amp p := by
  unfold p2 physicalX
  ring

end NavierStokes.OutgoingHistories
