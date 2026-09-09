/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.MeanMomentBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.MeanIncrementBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.MeanRankUpdate
public import LeanPool.NavierStokesAndEuler.NavierStokes.CorrectionState

@[expose] public section

/-!
# Actual defect changes under the slow rank update

The pressure, angular flux, and axial flux defects are actual torus/radial
moments.  Their linear changes are precisely the last three rows of (35).
The remaining terms include the complete radial-source remainder of (32).
-/

namespace NavierStokes.DefectIncrementBounds

noncomputable section

open Set Function MeasureTheory Filter
open scoped ContDiff Topology Interval
open WeightedClasses MeanIncrementBounds

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

abbrev Point (P : Type) := PressureStream.Lift P
abbrev ScalarField (D : Type) := MeanIncrementBounds.Field D

noncomputable def positiveDomain : Set (Point P) := {x | 0 < x.1}

omit [NormedSpace ℝ P] in
theorem positiveDomain_open : IsOpen (positiveDomain (P := P)) :=
  isOpen_lt continuous_const continuous_fst

/-- Global smooth zero extension with a fixed radial support shell. -/
structure Shell (a b : ℝ) (f : ScalarField (Point P)) : Prop where
  smooth : ∀ n, ContDiff ℝ ∞ (f n)
  supported : ∀ n, RadialAlias.RadiallySupported a b (f n)

namespace Shell

variable {a b : ℝ} {f g : ScalarField (Point P)}

theorem zero_of_not_mem (hf : Shell a b f) (n : ℕ) (x : Point P)
    (hx : x.1 ∉ Icc a b) : f n x = 0 := by
  by_contra hn
  exact hx (hf.supported n hn)

theorem zero : Shell a b (0 : ScalarField (Point P)) :=
  ⟨fun _ => contDiff_const, fun _ _ hx => (hx rfl).elim⟩

theorem add (hf : Shell a b f) (hg : Shell a b g) : Shell a b (f + g) := by
  refine ⟨fun n => (hf.smooth n).add (hg.smooth n), ?_⟩
  intro n x hx
  by_contra hn
  exact hx (by simp [hf.zero_of_not_mem n x hn, hg.zero_of_not_mem n x hn])

theorem neg (hf : Shell a b f) : Shell a b (-f) := by
  refine ⟨fun n => (hf.smooth n).neg, ?_⟩
  intro n x hx
  exact hf.supported n (neg_ne_zero.mp hx)

theorem sub (hf : Shell a b f) (hg : Shell a b g) : Shell a b (f - g) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem mul (hf : Shell a b f) (hg : Shell a b g) : Shell a b (f * g) := by
  refine ⟨fun n => (hf.smooth n).mul (hg.smooth n), ?_⟩
  intro n x hx
  exact hf.supported n (left_ne_zero_of_mul hx)

theorem band_mul (hf : Shell a b f) (c : ℕ → ℝ) :
    Shell a b (fun n x => c n * f n x) := by
  refine ⟨fun n => contDiff_const.mul (hf.smooth n), ?_⟩
  intro n x hx
  exact hf.supported n (right_ne_zero_of_mul hx)

theorem smul (hf : Shell a b f) (c : ℝ) : Shell a b (c • f) :=
  hf.band_mul (fun _ => c)

theorem directional (hf : Shell a b f) (v : Point P) :
    Shell a b (fun n x => fderiv ℝ (f n) x v) :=
  ⟨fun n => ((hf.smooth n).fderiv_right (by simp)).clm_apply contDiff_const,
    fun n => RadialAlias.radialSupport_fderiv_apply (hf.supported n) v⟩

/-- Coefficients need smoothness only on the physical region `R > 0`.
Near the axis the actual product vanishes because the other factor is
supported away from it. -/
theorem coefficient_mul (hf : Shell a b f) (ha : 0 < a)
    (hg : SmoothOn (positiveDomain (P := P)) g) : Shell a b (g * f) := by
  refine ⟨?_, fun n x hx => hf.supported n (right_ne_zero_of_mul hx)⟩
  intro n
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x.1 < a
  · apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Point P => (0 : ℝ)) x).congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hx] with y hy
    have hzero := hf.zero_of_not_mem n y (fun h => (not_le_of_gt hy) h.1)
    simp only [Pi.mul_apply, hzero, mul_zero]
  · have hpos : x ∈ positiveDomain (P := P) := ha.trans_le (le_of_not_gt hx)
    exact ((hg n).contDiffAt (positiveDomain_open.mem_nhds hpos)).mul (hf.smooth n).contDiffAt

theorem mul_coefficient (hf : Shell a b f) (ha : 0 < a)
    (hg : SmoothOn (positiveDomain (P := P)) g) : Shell a b (f * g) := by
  simpa only [mul_comm] using hf.coefficient_mul ha hg

theorem smoothOn (hf : Shell a b f) (U : Set (Point P)) : SmoothOn U f :=
  fun n => (hf.smooth n).contDiffOn

end Shell

structure ShellTriple (a b : ℝ) (m : Triple (Point P)) : Prop where
  radial : Shell a b m.radial
  angular : Shell a b m.angular
  axial : Shell a b m.axial

theorem ShellTriple.updated {a b : ℝ} {m h : Triple (Point P)}
    (hm : ShellTriple a b m) (hh : ShellTriple a b h) : ShellTriple a b (updated m h) :=
  ⟨hm.radial.add hh.radial, hm.angular.add hh.angular, hm.axial.add hh.axial⟩

theorem ShellTriple.smooth {a b : ℝ} {m : Triple (Point P)}
    (hm : ShellTriple a b m) (U : Set (Point P)) : SmoothTriple U m :=
  ⟨hm.radial.smoothOn U, hm.angular.smoothOn U, hm.axial.smoothOn U⟩

/-- The radial chart has its actual radius and a coefficient smooth on the
physical positive radial region. No estimate on a residual is assumed. -/
structure PositiveOperators (o : Operators (Point P)) : Prop where
  radius_eq : o.radius = Prod.fst
  radialProfile : ContDiffOn ℝ ∞ o.radialProfile (positiveDomain (P := P))

theorem PositiveOperators.invRadius_smooth {o : Operators (Point P)}
    (ho : PositiveOperators o) : SmoothOn (positiveDomain (P := P)) o.invRadius := by
  intro n
  change ContDiffOn ℝ ∞ (fun x => (o.radius x)⁻¹) positiveDomain
  rw [ho.radius_eq]
  exact contDiffOn_fst.inv (fun x hx => (ne_of_gt hx))

namespace Shell

variable {a b : ℝ} {f : ScalarField (Point P)} {o : Operators (Point P)}

theorem dr (hf : Shell a b f) (ha : 0 < a) (ho : PositiveOperators o) :
    Shell a b (o.dr f) := by
  have hr := hf.directional o.eR
  have hv := ((hf.directional o.vR).coefficient_mul ha
    (fun _ => ho.radialProfile)).band_mul o.radialFrequency
  exact hr.add hv

theorem dz (hf : Shell a b f) (o : Operators (Point P)) : Shell a b (o.dz f) :=
  (hf.directional o.eZ).band_mul o.epsilon

theorem time (hf : Shell a b f) (o : Operators (Point P)) : Shell a b (o.time f) :=
  ((hf.directional o.eT).band_mul o.epsilon).neg.add
    ((hf.directional o.vT).band_mul o.fastCoefficient)

theorem inv_mul (hf : Shell a b f) (ha : 0 < a) (ho : PositiveOperators o) :
    Shell a b (o.invRadius * f) := hf.coefficient_mul ha ho.invRadius_smooth

theorem radialDiv (hf : Shell a b f) (ha : 0 < a) (ho : PositiveOperators o) (c : ℝ) :
    Shell a b (o.radialDiv c f) :=
  (hf.dr ha ho).add ((hf.inv_mul ha ho).smul c)

theorem viscosity (hf : Shell a b f) (ha : 0 < a) (ho : PositiveOperators o) (c : ℝ) :
    Shell a b (o.viscosity c f) := by
  exact (((((hf.dr ha ho).dr ha ho).add ((hf.dr ha ho).inv_mul ha ho)).add
    ((hf.dz o).dz o)).sub (((hf.inv_mul ha ho).inv_mul ha ho).smul c)).band_mul o.epsilon

end Shell

section FluxSupport

variable {a b : ℝ} (ha : 0 < a) {base m h : Triple (Point P)}
  (hb : SmoothTriple (positiveDomain (P := P)) base)
  (hm : ShellTriple a b m) (hh : ShellTriple a b h)

include ha hb hm in
theorem thetaAxial_shell : Shell a b (thetaAxial base m) :=
  ((hm.angular.coefficient_mul ha hb.axial).add
    (hm.axial.coefficient_mul ha hb.angular)).add (hm.axial.mul hm.angular)

include ha hb hm in
theorem axialAxial_shell : Shell a b (axialAxial base m) :=
  ((hm.axial.coefficient_mul ha hb.axial).smul 2).add (hm.axial.mul hm.axial)

include ha hb hm in
theorem axialRadial_shell : Shell a b (axialRadial base m) :=
  ((hm.axial.coefficient_mul ha hb.radial).add
    (hm.radial.mul_coefficient ha hb.axial)).add (hm.radial.mul hm.axial)

include ha hb hm in
theorem radialRadial_shell : Shell a b (radialRadial base m) :=
  ((hm.radial.coefficient_mul ha hb.radial).smul 2).add (hm.radial.mul hm.radial)

include ha hb hm in
theorem radialAngular_shell : Shell a b (radialAngular base m) :=
  ((hm.angular.coefficient_mul ha hb.angular).smul 2).add (hm.angular.mul hm.angular)

include ha hb hm in
theorem gr_shell {o : Operators (Point P)} (ho : PositiveOperators o)
    (W : Fin 3 → Fin 3 → ScalarField (Point P)) (hW : ∀ i j, Shell a b (W i j)) :
    Shell a b (gr o base m W) := by
  exact (((((hm.radial.time o).add
    (((radialRadial_shell ha hb hm).add (hW 0 0)).radialDiv ha ho 1)).add
    (((axialRadial_shell ha hb hm).add (hW 2 0)).dz o)).sub
    (((radialAngular_shell ha hb hm).add (hW 1 1)).inv_mul ha ho)).sub
    (hm.radial.viscosity ha ho 1)).neg

include ha hb hh in
theorem leadingRadial_shell {o : Operators (Point P)} (ho : PositiveOperators o) :
    Shell a b (leadingRadial o base h) :=
  (((hh.angular.coefficient_mul ha hb.angular).smul 2).inv_mul ha ho)

end FluxSupport

/-! ## The actual three moments and their linearity -/

noncomputable def barMoment (k : ℕ) (f : ScalarField (Point P)) : ScalarField P :=
  CorrectionState.radialMoment k f

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem barMoment_apply (k : ℕ) (f : ScalarField (Point P)) (n : ℕ) (p : P) :
    barMoment k f n p = ∫ r, r ^ k * PressureStream.torusAverage (f n) (r, p) :=
  MeanMomentBounds.pressureMass_radialWeighted k (f n) p

omit [NormedSpace ℝ P] in
theorem torusAverage_add {f g : Point P → ℝ} (hf : Continuous f) (hg : Continuous g)
    (p : ℝ × P) :
    PressureStream.torusAverage (fun x => f x + g x) p =
      PressureStream.torusAverage f p + PressureStream.torusAverage g p := by
  change FourierAlias.torusMean (fun Y => f (p.1, (p.2, Y)) + g (p.1, (p.2, Y))) = _
  exact FourierAlias.torusMean_add
    (hf.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id)))
    (hg.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id)))

theorem Shell.barIntegrable {a b : ℝ} {f : ScalarField (Point P)} (hf : Shell a b f)
    (k n : ℕ) (p : P) :
    Integrable (fun r => r ^ k * PressureStream.torusAverage (f n) (r, p)) :=
  IntegratedMeanBalances.weighted_integrable
    (PressureStream.torusAverage_slice_contDiff (hf.smooth n) p).continuous
    (PressureStream.torusAverage_slice_hasCompactSupport (hf.supported n) p) k

theorem barMoment_add {a b : ℝ} {f g : ScalarField (Point P)}
    (hf : Shell a b f) (hg : Shell a b g) (k : ℕ) :
    barMoment k (f + g) = barMoment k f + barMoment k g := by
  funext n p
  change barMoment k (f + g) n p = barMoment k f n p + barMoment k g n p
  have he : PressureStream.torusAverage ((f + g) n) =
      fun q => PressureStream.torusAverage (f n) q + PressureStream.torusAverage (g n) q := by
    funext q
    exact torusAverage_add (hf.smooth n).continuous (hg.smooth n).continuous q
  simp only [barMoment_apply, he, mul_add]
  exact integral_add (hf.barIntegrable k n p) (hg.barIntegrable k n p)

theorem barMoment_sub {a b : ℝ} {f g : ScalarField (Point P)}
    (hf : Shell a b f) (hg : Shell a b g) (k : ℕ) :
    barMoment k (f - g) = barMoment k f - barMoment k g := by
  funext n p
  change barMoment k (f - g) n p = barMoment k f n p - barMoment k g n p
  have he : PressureStream.torusAverage ((f - g) n) =
      fun q => PressureStream.torusAverage (f n) q - PressureStream.torusAverage (g n) q := by
    funext q
    exact PressureStream.torusAverage_sub (hf.smooth n).continuous (hg.smooth n).continuous q
  simp only [barMoment_apply, he, mul_sub]
  exact integral_sub (hf.barIntegrable k n p) (hg.barIntegrable k n p)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem barMoment_smul (c : ℝ) (f : ScalarField (Point P)) (k : ℕ) :
    barMoment k (c • f) = c • barMoment k f := by
  funext n p
  change PressureStream.pressureMass (fun x => x.1 ^ k * (c * f n x)) p =
    c * PressureStream.pressureMass (fun x => x.1 ^ k * f n x) p
  have he : (fun x : Point P => x.1 ^ k * (c * f n x)) =
      (fun x => c * (x.1 ^ k * f n x)) := by funext x; ring
  rw [he]
  simp only [PressureStream.pressureMass, PressureStream.torusAverage, PressureStream.torusInner,
    intervalIntegral.integral_const_mul, integral_const_mul]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
@[simp] theorem barMoment_zero (k : ℕ) : barMoment k (0 : ScalarField (Point P)) = 0 := by
  funext n p
  simp [barMoment, CorrectionState.radialMoment, PressureStream.pressureMass,
    PressureStream.torusAverage, PressureStream.torusInner]

theorem barMoment_mem
    {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR)
    (ε S : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1)
    (hS : ∀ n, 1 ≤ S n) {α : ℝ} {f : ScalarField (Point P)}
    (hf : Shell a b f)
    (hclass : MeanClass
      (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR ε S hε hεone hS) α f)
    (k : ℕ) :
    UnweightedClass (MeanMomentBounds.slowStripData (D := P) ε S hε hεone hS) α (barMoment k f) :=
      by
  have h := MeanMomentBounds.meanClass_radialMoment ha hab hcL hcR ε S hε hεone hS
    hf.smooth hf.supported hclass k
  have he : barMoment k f = fun n =>
      IntegratedMeanBalances.radialMoment k (PressureStream.torusAverage (f n)) := by
    funext n p
    exact barMoment_apply k f n p
  rw [he]
  exact h

/-! ## Literal changes, linear rows, and explicit nonlinear remainders -/

noncomputable def thetaLeading (base h : Triple (Point P)) : ScalarField (Point P) :=
  base.axial * h.angular + base.angular * h.axial

noncomputable def axialLeading (base h : Triple (Point P)) : ScalarField (Point P) :=
  (2 : ℝ) • (base.axial * h.axial)

noncomputable def thetaQuadratic (m h : Triple (Point P)) : ScalarField (Point P) :=
  m.axial * h.angular + h.axial * m.angular + h.axial * h.angular

noncomputable def axialQuadratic (m h : Triple (Point P)) : ScalarField (Point P) :=
  (2 : ℝ) • (m.axial * h.axial) + h.axial * h.axial

/-- This is the actual source difference minus the centrifugal linear row;
its formula and class are proved from equation (32). -/
noncomputable def actualRadialError (o : Operators (Point P)) (base m h : Triple (Point P))
    (W : Fin 3 → Fin 3 → ScalarField (Point P)) : ScalarField (Point P) :=
  gr o base (updated m h) W - gr o base m W - leadingRadial o base h

noncomputable def pressureDefect (o : Operators (Point P)) (base m : Triple (Point P))
    (W : Fin 3 → Fin 3 → ScalarField (Point P)) : ScalarField P := barMoment 0 (gr o base m W)

noncomputable def thetaDefect (base m : Triple (Point P))
    (W : Fin 3 → Fin 3 → ScalarField (Point P)) : ScalarField P :=
  barMoment 2 (thetaAxial base m + W 2 1)

noncomputable def axialDefect (o : Operators (Point P)) (base m : Triple (Point P))
    (W : Fin 3 → Fin 3 → ScalarField (Point P)) : ScalarField P :=
  barMoment 1 (axialAxial base m + W 2 2) - (1 / 2 : ℝ) • barMoment 2 (gr o base m W)

noncomputable def defects (o : Operators (Point P)) (base m : Triple (Point P))
    (W : Fin 3 → Fin 3 → ScalarField (Point P)) : ℕ → P → Fin 3 → ℝ :=
  fun n p => ![pressureDefect o base m W n p, thetaDefect base m W n p,
    axialDefect o base m W n p]

noncomputable def linearRows (o : Operators (Point P)) (base h : Triple (Point P)) :
    ℕ → P → Fin 3 → ℝ := fun n p =>
  ![barMoment 0 (leadingRadial o base h) n p,
    barMoment 2 (thetaLeading base h) n p,
    barMoment 1 (axialLeading base h) n p - (1 / 2) * barMoment 2 (leadingRadial o base h) n p]

noncomputable def remainders (o : Operators (Point P)) (base m h : Triple (Point P))
    (W : Fin 3 → Fin 3 → ScalarField (Point P)) : ℕ → P → Fin 3 → ℝ := fun n p =>
  ![barMoment 0 (actualRadialError o base m h W) n p,
    barMoment 2 (thetaQuadratic m h) n p,
    barMoment 1 (axialQuadratic m h) n p -
      (1 / 2) * barMoment 2 (actualRadialError o base m h W) n p]

theorem thetaQuadratic_shell {a b : ℝ} {m h : Triple (Point P)}
    (hm : ShellTriple a b m) (hh : ShellTriple a b h) : Shell a b (thetaQuadratic m h) :=
  ((hm.axial.mul hh.angular).add (hh.axial.mul hm.angular)).add (hh.axial.mul hh.angular)

theorem axialQuadratic_shell {a b : ℝ} {m h : Triple (Point P)}
    (hm : ShellTriple a b m) (hh : ShellTriple a b h) : Shell a b (axialQuadratic m h) :=
  ((hm.axial.mul hh.axial).smul 2).add (hh.axial.mul hh.axial)

theorem thetaLeading_shell {a b : ℝ} (ha : 0 < a) {base h : Triple (Point P)}
    (hb : SmoothTriple positiveDomain base) (hh : ShellTriple a b h) :
    Shell a b (thetaLeading base h) :=
  (hh.angular.coefficient_mul ha hb.axial).add (hh.axial.coefficient_mul ha hb.angular)

theorem axialLeading_shell {a b : ℝ} (ha : 0 < a) {base h : Triple (Point P)}
    (hb : SmoothTriple positiveDomain base) (hh : ShellTriple a b h) :
    Shell a b (axialLeading base h) := (hh.axial.coefficient_mul ha hb.axial).smul 2

theorem actualRadialError_shell {a b : ℝ} (ha : 0 < a) {o : Operators (Point P)}
    (ho : PositiveOperators o) {base m h : Triple (Point P)}
    (hb : SmoothTriple positiveDomain base) (hm : ShellTriple a b m) (hh : ShellTriple a b h)
    (W : Fin 3 → Fin 3 → ScalarField (Point P)) (hW : ∀ i j, Shell a b (W i j)) :
    Shell a b (actualRadialError o base m h W) :=
  ((gr_shell ha hb (hm.updated hh) ho W hW).sub
    (gr_shell ha hb hm ho W hW)).sub (leadingRadial_shell ha hb hh ho)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem thetaAxial_update_split (base m h : Triple (Point P))
    (W : Fin 3 → Fin 3 → ScalarField (Point P)) :
    thetaAxial base (updated m h) + W 2 1 =
      (thetaAxial base m + W 2 1) + thetaLeading base h + thetaQuadratic m h := by
  ext n x
  simp only [thetaAxial, updated, thetaLeading, thetaQuadratic, Pi.add_apply, Pi.mul_apply]
  ring

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem axialAxial_update_split (base m h : Triple (Point P))
    (W : Fin 3 → Fin 3 → ScalarField (Point P)) :
    axialAxial base (updated m h) + W 2 2 =
      (axialAxial base m + W 2 2) + axialLeading base h + axialQuadratic m h := by
  ext n x
  simp only [axialAxial, updated, axialLeading, axialQuadratic, Pi.add_apply, Pi.mul_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

theorem radial_update_split (o : Operators (Point P)) (base m h : Triple (Point P))
    (W : Fin 3 → Fin 3 → ScalarField (Point P)) :
    gr o base (updated m h) W =
      gr o base m W + leadingRadial o base h + actualRadialError o base m h W := by
  unfold actualRadialError
  abel

/-- The complete equation-(32) remainder: slow/fast time, radial transport,
axial transport, old/new angular products, and viscosity are retained. -/
theorem actualRadialError_eq_formula {U : Set (Point P)} (hU : IsOpen U)
    (o : Operators (Point P)) (ha : ContDiffOn ℝ ∞ o.radialProfile U)
    {base m h : Triple (Point P)} (hb : SmoothTriple U base)
    (hm : SmoothTriple U m) (hh : SmoothTriple U h)
    (W : Fin 3 → Fin 3 → ScalarField (Point P)) (hW : ∀ i j, SmoothOn U (W i j)) :
    Agree U (actualRadialError o base m h W) (radialRemainder o base m h) := by
  intro n x hx
  have he := gr_change hU o ha hb hm hh W hW n hx
  simp only [actualRadialError, Pi.add_apply, Pi.sub_apply] at he ⊢
  linarith

section RemainderClasses

variable {s : StripData (Point P)} {o : Operators (Point P)} {κ H : ℝ}
  {base m h : Triple (Point P)} (ho : OperatorBounds s o κ)
  (hb : BaseBounds s base) (hm : CumulativeBounds s m) (hh : IncrementBounds s H h)
  (hH : 9 / 10 ≤ H)

include ho hm hh hH in
theorem thetaQuadratic_mem : MeanClass s (H + 9 / 10 - 2 * κ) (thetaQuadratic m h) := by
  have h1 : MeanClass s (H + 9 / 10) (m.axial * h.angular) := by
    simpa only [add_comm] using Class.product hm.axial hh.angular ho.weight_le_one
  have h2 := Class.product hh.axial hm.angular ho.weight_le_one
  have h3 := (Class.product hh.axial hh.angular ho.weight_le_one).mono_exponent
    (show H + 9 / 10 ≤ H + H from by linarith)
  exact ((h1.add h2).add h3).mono_exponent (by linarith [ho.kappa_nonneg])

include ho hm hh hH in
theorem axialQuadratic_mem : MeanClass s (H + 9 / 10 - 2 * κ) (axialQuadratic m h) := by
  have h1 : MeanClass s (H + 9 / 10) ((2 : ℝ) • (m.axial * h.axial)) := by
    simpa only [add_comm] using Class.smul (Class.product hm.axial hh.axial ho.weight_le_one) 2
  have h2 := (Class.product hh.axial hh.axial ho.weight_le_one).mono_exponent
    (show H + 9 / 10 ≤ H + H from by linarith)
  exact (h1.add h2).mono_exponent (by linarith [ho.kappa_nonneg])

include ho hb hm hh hH in
theorem actualRadialError_mem
    (W : Fin 3 → Fin 3 → ScalarField (Point P)) (hW : ∀ i j, SmoothOn s.domain (W i j)) :
    MeanClass s (H + 9 / 10 - 2 * κ) (actualRadialError o base m h W) :=
  gr_change_sub_leading_mem ho hb hm hh hH W hW

end RemainderClasses

section ExactMoments

variable {a b : ℝ} (ha : 0 < a) {o : Operators (Point P)} (hop : PositiveOperators o)
  {base m h : Triple (Point P)} (hb : SmoothTriple positiveDomain base)
  (hm : ShellTriple a b m) (hh : ShellTriple a b h)
  (W : Fin 3 → Fin 3 → ScalarField (Point P)) (hW : ∀ i j, Shell a b (W i j))

include ha hop hb hm hh hW in
theorem pressureDefect_update :
    pressureDefect o base (updated m h) W = pressureDefect o base m W +
      barMoment 0 (leadingRadial o base h) + barMoment 0 (actualRadialError o base m h W) := by
  have h0 := gr_shell ha hb hm hop W hW
  have hl := leadingRadial_shell ha hb hh hop
  have hr := actualRadialError_shell ha hop hb hm hh W hW
  unfold pressureDefect
  rw [radial_update_split, barMoment_add (h0.add hl) hr, barMoment_add h0 hl]

include ha hb hm hh hW in
theorem thetaDefect_update :
    thetaDefect base (updated m h) W = thetaDefect base m W +
      barMoment 2 (thetaLeading base h) + barMoment 2 (thetaQuadratic m h) := by
  have h0 := (thetaAxial_shell ha hb hm).add (hW 2 1)
  have hl := thetaLeading_shell ha hb hh
  have hr := thetaQuadratic_shell hm hh
  unfold thetaDefect
  rw [thetaAxial_update_split, barMoment_add (h0.add hl) hr, barMoment_add h0 hl]

include ha hop hb hm hh hW in
theorem axialDefect_update :
    axialDefect o base (updated m h) W = axialDefect o base m W +
      (barMoment 1 (axialLeading base h) - (1 / 2 : ℝ) • barMoment 2 (leadingRadial o base h)) +
      (barMoment 1 (axialQuadratic m h) -
        (1 / 2 : ℝ) • barMoment 2 (actualRadialError o base m h W)) := by
  have hz0 := (axialAxial_shell ha hb hm).add (hW 2 2)
  have hzl := axialLeading_shell ha hb hh
  have hzr := axialQuadratic_shell hm hh
  have hr0 := gr_shell ha hb hm hop W hW
  have hrl := leadingRadial_shell ha hb hh hop
  have hrr := actualRadialError_shell ha hop hb hm hh W hW
  unfold axialDefect
  rw [axialAxial_update_split, radial_update_split,
    barMoment_add (hz0.add hzl) hzr, barMoment_add hz0 hzl,
    barMoment_add (hr0.add hrl) hrr, barMoment_add hr0 hrl]
  simp only [smul_add]
  abel

include ha hop hb hm hh hW in
/-- Every defect changes by the exact row (35) and its explicitly computed
remainder.  No estimate or cancellation is a premise of this identity. -/
theorem defects_update :
    defects o base (updated m h) W =
      defects o base m W + linearRows o base h + remainders o base m h W := by
  have hp := pressureDefect_update ha hop hb hm hh W hW
  have ht := thetaDefect_update ha hb hm hh W hW
  have hz := axialDefect_update ha hop hb hm hh W hW
  funext n p i
  fin_cases i <;>
    simp [defects, linearRows, remainders, hp, ht, hz, Pi.add_apply, Pi.sub_apply, smul_eq_mul]

include ha hop hb hm hh hW in
theorem defects_after_solved_rows
    (hrows : linearRows o base h = -defects o base m W) :
    defects o base (updated m h) W = remainders o base m h W := by
  rw [defects_update ha hop hb hm hh W hW, hrows]
  simp

end ExactMoments

theorem unweighted_sub {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {s : StripData D} {α : ℝ} {f g : ScalarField D}
    (hf : UnweightedClass s α f) (hg : UnweightedClass s α g) :
    UnweightedClass s α (f - g) := by
  have hn : UnweightedClass s α (-g) := by
    exact hg.map (-ContinuousLinearMap.id ℝ ℝ)
  simp only [sub_eq_add_neg]
  exact hf.add hn

theorem unweighted_smul {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {s : StripData D} {α : ℝ} {f : ScalarField D}
    (hf : UnweightedClass s α f) (c : ℝ) : UnweightedClass s α (c • f) := by
  exact hf.map (c • ContinuousLinearMap.id ℝ ℝ)

section IntegratedBounds

variable {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR)
  (ε S : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hS : ∀ n, 1 ≤ S n)
  {o : Operators (Point P)} {κ H : ℝ} {base m h : Triple (Point P)}
  (hop : PositiveOperators o) (hbs : SmoothTriple positiveDomain base)
  (hms : ShellTriple a b m) (hhs : ShellTriple a b h)
  (W : Fin 3 → Fin 3 → ScalarField (Point P)) (hW : ∀ i j, Shell a b (W i j))

variable (ho : OperatorBounds
    (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR ε S hε hεone hS) o κ)
  (hb : BaseBounds
    (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR ε S hε hεone hS) base)
  (hm : CumulativeBounds
    (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR ε S hε hεone hS) m)
  (hh : IncrementBounds
    (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR ε S hε hεone hS) H h)
  (hH : 9 / 10 ≤ H)

include ha hab hcL hcR hop hbs hms hhs hW ho hb hm hh hH in
/-- The remainder bound is derived from the primitive mean classes and the
literal equation-(32) source, then integrated by the actual moment map. -/
theorem remainders_mem (i : Fin 3) :
    UnweightedClass (MeanMomentBounds.slowStripData (D := P) ε S hε hεone hS) (H + 9 / 10 - 2 * κ)
      (fun n p => remainders o base m h W n p i) := by
  have hrc := actualRadialError_mem ho hb hm hh hH W
    (fun i j => (hW i j).smoothOn
      (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR ε S hε hεone hS).domain)
  have hrs := actualRadialError_shell ha hop hbs hms hhs W hW
  have hr0 := barMoment_mem ha hab hcL hcR ε S hε hεone hS hrs hrc 0
  have hr2 := barMoment_mem ha hab hcL hcR ε S hε hεone hS hrs hrc 2
  have ht := barMoment_mem ha hab hcL hcR ε S hε hεone hS
    (thetaQuadratic_shell hms hhs) (thetaQuadratic_mem ho hm hh hH) 2
  have hz := barMoment_mem ha hab hcL hcR ε S hε hεone hS
    (axialQuadratic_shell hms hhs) (axialQuadratic_mem ho hm hh hH) 1
  fin_cases i
  · exact hr0
  · exact ht
  · exact unweighted_sub hz (unweighted_smul hr2 (1 / 2))

include ha hab hcL hcR hop hbs hms hhs hW ho hb hm hh hH in
theorem defects_after_rank_mem
    (hrows : linearRows o base h = -defects o base m W) (i : Fin 3) :
    UnweightedClass (MeanMomentBounds.slowStripData (D := P) ε S hε hεone hS) (H + 9 / 10 - 2 * κ)
      (fun n p => defects o base (updated m h) W n p i) := by
  rw [defects_after_solved_rows ha hop hbs hms hhs W hW hrows]
  exact remainders_mem ha hab hcL hcR ε S hε hεone hS hop hbs hms hhs W hW ho hb hm hh hH i

end IntegratedBounds

/-! ## Identification with the five solved rows and both exact masses -/

noncomputable def slowSlice (f : ScalarField (Point P)) (n : ℕ) (p : P) (r : ℝ) : ℝ :=
  f n (r, (p, 0))

noncomputable def IsSlow (f : ScalarField (Point P)) : Prop :=
  ∀ n r p Y, f n (r, (p, Y)) = slowSlice f n p r

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem IsSlow.add {f g : ScalarField (Point P)} (hf : IsSlow f) (hg : IsSlow g) :
    IsSlow (f + g) := by
  intro n r p Y
  simp only [Pi.add_apply, slowSlice, hf n r p Y, hg n r p Y]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem IsSlow.mul {f g : ScalarField (Point P)} (hf : IsSlow f) (hg : IsSlow g) :
    IsSlow (f * g) := by
  intro n r p Y
  simp only [Pi.mul_apply, slowSlice, hf n r p Y, hg n r p Y]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem IsSlow.smul {f : ScalarField (Point P)} (hf : IsSlow f) (c : ℝ) : IsSlow (c • f) := by
  intro n r p Y
  simp only [Pi.smul_apply, smul_eq_mul, slowSlice, hf n r p Y]

theorem PositiveOperators.invRadius_slow {o : Operators (Point P)} (ho : PositiveOperators o) :
    IsSlow o.invRadius := by
  intro n r p Y
  simp only [Operators.invRadius, slowSlice, ho.radius_eq]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem barMoment_slow {f : ScalarField (Point P)} (hf : IsSlow f) (k n : ℕ) (p : P) :
    barMoment k f n p = ∫ r, r ^ k * slowSlice f n p r := by
  rw [barMoment_apply]
  apply integral_congr_ae
  filter_upwards [] with r
  congr 1
  simp [PressureStream.torusAverage, PressureStream.torusInner, hf n r p]

theorem Shell.sliceIntegrable {a b : ℝ} {f : ScalarField (Point P)} (hf : Shell a b f)
    (k n : ℕ) (p : P) : Integrable (fun r => r ^ k * slowSlice f n p r) :=
  IntegratedMeanBalances.weighted_integrable
    ((hf.smooth n).continuous.comp (continuous_id.prodMk continuous_const))
    (IntegratedMeanBalances.radial_slice_compact (hf.supported n) (p, 0)) k

theorem fiveRows_mass_zero {o : Operators (Point P)} {base m h : Triple (Point P)}
    {W : Fin 3 → Fin 3 → ScalarField (Point P)}
    (hv : IsSlow h.angular) (hg : IsSlow h.axial)
    (hrows : ∀ n p, FiveRowRank.FiveRows (slowSlice base.angular n p) (slowSlice base.axial n p)
      (defects o base m W n p) (slowSlice h.angular n p) (slowSlice h.axial n p)) :
    barMoment 2 h.angular = 0 ∧ barMoment 1 h.axial = 0 := by
  constructor
  · funext n p
    rw [barMoment_slow hv]
    exact (hrows n p).1
  · funext n p
    rw [barMoment_slow hg]
    simpa only [pow_one, Pi.zero_apply] using (hrows n p).2.1

theorem fiveRows_preserve_masses {a b : ℝ} {o : Operators (Point P)}
    {base m h : Triple (Point P)} {W : Fin 3 → Fin 3 → ScalarField (Point P)}
    (hm : ShellTriple a b m) (hh : ShellTriple a b h)
    (hv : IsSlow h.angular) (hg : IsSlow h.axial)
    (hrows : ∀ n p, FiveRowRank.FiveRows (slowSlice base.angular n p) (slowSlice base.axial n p)
      (defects o base m W n p) (slowSlice h.angular n p) (slowSlice h.axial n p)) :
    barMoment 2 (updated m h).angular = barMoment 2 m.angular ∧
      barMoment 1 (updated m h).axial = barMoment 1 m.axial := by
  obtain ⟨hzv, hzg⟩ := fiveRows_mass_zero hv hg hrows
  change barMoment 2 (m.angular + h.angular) = _ ∧ barMoment 1 (m.axial + h.axial) = _
  rw [barMoment_add hm.angular hh.angular, barMoment_add hm.axial hh.axial, hzv, hzg]
  simp

/-- The three moment rows are exactly those solved in (35), including the
minus sign and factor one half in the axial pressure moment. -/
theorem linearRows_eq_neg_of_fiveRows {a b : ℝ} (ha : 0 < a)
    {o : Operators (Point P)} (hop : PositiveOperators o) {base m h : Triple (Point P)}
    (hb : SmoothTriple positiveDomain base) (hh : ShellTriple a b h)
    (hV : IsSlow base.angular) (hG : IsSlow base.axial)
    (hv : IsSlow h.angular) (hg : IsSlow h.axial)
    (W : Fin 3 → Fin 3 → ScalarField (Point P))
    (hrows : ∀ n p, FiveRowRank.FiveRows (slowSlice base.angular n p) (slowSlice base.axial n p)
      (defects o base m W n p) (slowSlice h.angular n p) (slowSlice h.axial n p)) :
    linearRows o base h = -defects o base m W := by
  have hrslow : IsSlow (leadingRadial o base h) :=
    hop.invRadius_slow.mul ((hV.mul hv).smul 2)
  have htslow : IsSlow (thetaLeading base h) := (hG.mul hv).add (hV.mul hg)
  have hzslow : IsSlow (axialLeading base h) := (hG.mul hg).smul 2
  have hrs := leadingRadial_shell ha hb hh hop
  have hzs := axialLeading_shell ha hb hh
  funext n p i
  fin_cases i
  · change barMoment 0 (leadingRadial o base h) n p = -(defects o base m W n p 0)
    rw [barMoment_slow hrslow]
    calc
      _ = ∫ r, (2 * slowSlice base.angular n p r / r) * slowSlice h.angular n p r := by
        apply integral_congr_ae
        filter_upwards [] with r
        simp only [slowSlice, leadingRadial, Operators.invRadius, hop.radius_eq,
          Pi.mul_apply, Pi.smul_apply, smul_eq_mul, pow_zero, one_mul, div_eq_mul_inv]
        ring
      _ = _ := (hrows n p).2.2.1
  · change barMoment 2 (thetaLeading base h) n p = -(defects o base m W n p 1)
    rw [barMoment_slow htslow]
    exact (hrows n p).2.2.2.1
  · change barMoment 1 (axialLeading base h) n p -
      (1 / 2) * barMoment 2 (leadingRadial o base h) n p = -(defects o base m W n p 2)
    rw [barMoment_slow hzslow, barMoment_slow hrslow]
    calc
      _ = ∫ r, r ^ (1 : ℕ) * slowSlice (axialLeading base h) n p r -
          (1 / 2) * (r ^ (2 : ℕ) * slowSlice (leadingRadial o base h) n p r) := by
        rw [integral_sub (hzs.sliceIntegrable 1 n p) ((hrs.sliceIntegrable 2 n p).const_mul (1 /
          2)),
          integral_const_mul]
      _ = ∫ r, 2 * r * slowSlice base.axial n p r * slowSlice h.axial n p r -
          r * slowSlice base.angular n p r * slowSlice h.angular n p r := by
        apply integral_congr_ae
        filter_upwards [] with r
        simp only [slowSlice, axialLeading, leadingRadial, Operators.invRadius, hop.radius_eq,
          Pi.mul_apply, Pi.smul_apply, smul_eq_mul, pow_one]
        by_cases hr : r = 0
        · simp [hr]
        · field_simp
      _ = _ := (hrows n p).2.2.2.2

/-! ## The actual constructed `CorrectionState.rankStage` -/

theorem defects_eq_stateDebt (c : CorrectionState.Context (Point P))
    (u : CorrectionState.State (Point P)) :
    defects c.operators c.base u.mean u.covariance = CorrectionState.debt c u := rfl

theorem rankStage_covariance (p : CorrectionState.ReconstructionData) (r : CorrectionState.RankData
  P)
    (axial : P × PressureStream.Plane) (c : CorrectionState.Context (Point P))
    (u : CorrectionState.State (Point P)) :
    (CorrectionState.rankStage p r axial c u).covariance = u.covariance := by
  funext i j
  change CorrectionState.bilinearCovariance (u.oscillation + 0) (u.oscillation + 0) i j = _
  rw [add_zero]
  rfl

theorem rankStage_debt_eq (p : CorrectionState.ReconstructionData) (r : CorrectionState.RankData P)
    (axial : P × PressureStream.Plane) (c : CorrectionState.Context (Point P))
    (u : CorrectionState.State (Point P)) :
    CorrectionState.debt c (CorrectionState.rankStage p r axial c u) =
      defects c.operators c.base
        (updated u.mean (CorrectionState.rankIncrement p r axial c u)) u.covariance := by
  rw [← defects_eq_stateDebt, rankStage_covariance]
  rfl

/-- Geometric and primitive regularity hypotheses for the constructed rank
patch.  The conclusion is not among the fields: the inverse, actual stream,
five rows, and their cancellation are supplied by proved theorems. -/
structure RankGeometry (p : CorrectionState.ReconstructionData) (r : CorrectionState.RankData P)
    (c : CorrectionState.Context (Point P)) (u : CorrectionState.State (Point P)) : Prop where
  primitive_inner_pos : 0 < p.inner
  exponent_pos : 0 < p.exponent
  lambda_pos : 0 < r.lambda
  coefficient_ne : ∀ n x, r.coefficient n x ≠ 0
  inner_pos : 0 < r.inner
  inner_lt_outer : r.inner < r.outer
  length_pos : ∀ n x, 0 < r.length n x
  velocity_ne : ∀ n x, r.velocity n x ≠ 0
  desired_smooth : ∀ n, ContDiff ℝ ∞ (CorrectionState.rankDesiredAxial r c u n)
  desired_supported : ∀ n, RadialAlias.RadiallySupported p.inner p.outer
    (CorrectionState.rankDesiredAxial r c u n)
  angular_model : ∀ n x R, R ∈ Ioo (r.length n x * r.inner) (r.length n x * r.outer) →
    c.base.angular n (R, (x, 0)) =
      MeanRankUpdate.background r.lambda (r.coefficient n x) (r.length n x) (r.velocity n x) R
  axial_model : ∀ n x R, R ∈ Ioo (r.length n x * r.inner) (r.length n x * r.outer) →
    c.base.axial n (R, (x, 0)) = 0

theorem rankIncrement_angular_slow (p : CorrectionState.ReconstructionData)
    (r : CorrectionState.RankData P) (axial : P × PressureStream.Plane)
    (c : CorrectionState.Context (Point P)) (u : CorrectionState.State (Point P)) :
    IsSlow (CorrectionState.rankIncrement p r axial c u).angular := by
  intro n R x Y
  rfl

namespace RankGeometry

variable {p : CorrectionState.ReconstructionData} {r : CorrectionState.RankData P}
  {c : CorrectionState.Context (Point P)} {u : CorrectionState.State (Point P)}
  (hg : RankGeometry p r c u) (axial : P × PressureStream.Plane)

include hg

theorem axial_exact (n : ℕ) (x : Point P) :
    (CorrectionState.rankIncrement p r axial c u).axial n x =
      CorrectionState.rankDesiredAxial r c u n (x.1, x.2.1) :=
  CorrectionState.rank_axial_eq_desired p r axial c u hg.primitive_inner_pos hg.exponent_pos n
    hg.lambda_pos (hg.coefficient_ne n) hg.inner_pos hg.inner_lt_outer (hg.length_pos n)
    (hg.velocity_ne n) (hg.desired_smooth n) (hg.desired_supported n) x

theorem axial_slow : IsSlow (CorrectionState.rankIncrement p r axial c u).axial := by
  intro n R x Y
  change (CorrectionState.rankIncrement p r axial c u).axial n (R, (x, Y)) =
    (CorrectionState.rankIncrement p r axial c u).axial n (R, (x, 0))
  rw [hg.axial_exact, hg.axial_exact]

/-- These are the solved rows for the actual axial stream, not for an
unrealized desired increment. -/
theorem fiveRows (n : ℕ) (x : P) :
    FiveRowRank.FiveRows (slowSlice c.base.angular n x) (slowSlice c.base.axial n x)
      (defects c.operators c.base u.mean u.covariance n x)
      (slowSlice (CorrectionState.rankIncrement p r axial c u).angular n x)
      (slowSlice (CorrectionState.rankIncrement p r axial c u).axial n x) := by
  have hax : slowSlice (CorrectionState.rankIncrement p r axial c u).axial n x =
      fun R => CorrectionState.rankDesiredAxial r c u n (R, x) := by
    funext R
    exact hg.axial_exact axial n (R, (x, 0))
  rw [hax]
  exact CorrectionState.rank_rows_on_patch r c u n x 0 hg.lambda_pos (hg.coefficient_ne n x)
    hg.inner_pos hg.inner_lt_outer (hg.length_pos n x) (hg.velocity_ne n x)
    (hg.angular_model n x) (hg.axial_model n x)

theorem solved_rows {a b : ℝ} (ha : 0 < a) (hop : PositiveOperators c.operators)
    (hb : SmoothTriple positiveDomain c.base)
    (hh : ShellTriple a b (CorrectionState.rankIncrement p r axial c u))
    (hV : IsSlow c.base.angular) (hG : IsSlow c.base.axial) :
    linearRows c.operators c.base (CorrectionState.rankIncrement p r axial c u) =
      -defects c.operators c.base u.mean u.covariance :=
  linearRows_eq_neg_of_fiveRows ha hop hb hh hV hG
    (rankIncrement_angular_slow p r axial c u) (hg.axial_slow axial)
    u.covariance (hg.fiveRows axial)

theorem preserve_masses {a b : ℝ} (hm : ShellTriple a b u.mean)
    (hh : ShellTriple a b (CorrectionState.rankIncrement p r axial c u)) :
    CorrectionState.radialMoment 2 (CorrectionState.rankStage p r axial c u).mean.angular =
        CorrectionState.radialMoment 2 u.mean.angular ∧
      CorrectionState.radialMoment 1 (CorrectionState.rankStage p r axial c u).mean.axial =
        CorrectionState.radialMoment 1 u.mean.axial :=
  fiveRows_preserve_masses hm hh (rankIncrement_angular_slow p r axial c u)
    (hg.axial_slow axial) (hg.fiveRows axial)

theorem zeroMasses {a b : ℝ} (hm : ShellTriple a b u.mean)
    (hh : ShellTriple a b (CorrectionState.rankIncrement p r axial c u))
    (hzero : CorrectionState.ZeroMasses u) :
    CorrectionState.ZeroMasses (CorrectionState.rankStage p r axial c u) := by
  obtain ⟨hv, hz⟩ := hg.preserve_masses axial hm hh
  exact ⟨hv.trans hzero.1, hz.trans hzero.2⟩

theorem debt_eq_remainders {a b : ℝ} (ha : 0 < a) (hop : PositiveOperators c.operators)
    (hb : SmoothTriple positiveDomain c.base) (hm : ShellTriple a b u.mean)
    (hh : ShellTriple a b (CorrectionState.rankIncrement p r axial c u))
    (hW : ∀ i j, Shell a b (u.covariance i j))
    (hV : IsSlow c.base.angular) (hG : IsSlow c.base.axial) :
    CorrectionState.debt c (CorrectionState.rankStage p r axial c u) =
      remainders c.operators c.base u.mean (CorrectionState.rankIncrement p r axial c u)
        u.covariance := by
  rw [rankStage_debt_eq]
  exact defects_after_solved_rows ha hop hb hm hh u.covariance hW
    (hg.solved_rows axial ha hop hb hh hV hG)

end RankGeometry

section ConstructedBounds

variable {a b cL cR : ℝ} (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR)
  (ε S : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hεone : ∀ n, ε n ≤ 1) (hS : ∀ n, 1 ≤ S n)
  {p : CorrectionState.ReconstructionData} {r : CorrectionState.RankData P}
  {c : CorrectionState.Context (Point P)} {u : CorrectionState.State (Point P)}
  (axial : P × PressureStream.Plane) (hg : RankGeometry p r c u)
  (hop : PositiveOperators c.operators) (hbs : SmoothTriple positiveDomain c.base)
  (hms : ShellTriple a b u.mean)
  (hhs : ShellTriple a b (CorrectionState.rankIncrement p r axial c u))
  (hW : ∀ i j, Shell a b (u.covariance i j))
  (hV : IsSlow c.base.angular) (hG : IsSlow c.base.axial) {κ H : ℝ}
  (ho : OperatorBounds
    (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR ε S hε hεone hS) c.operators κ)
  (hb : BaseBounds
    (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR ε S hε hεone hS) c.base)
  (hm : CumulativeBounds
    (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR ε S hε hεone hS) u.mean)
  (hh : IncrementBounds
    (WeightedRadialPrimitive.logStripData a b cL cR ha hcL hcR ε S hε hεone hS) H
      (CorrectionState.rankIncrement p r axial c u))
  (hH : 9 / 10 ≤ H)

include ha hab hcL hcR axial hg hop hbs hms hhs hW hV hG ho hb hm hh hH in
/-- The constructed rank solve followed by actual pressure recomputation
has the claimed stronger defects. The inputs are primitive fields and their
classes; no solved-row, defect-remainder, or pressure-error estimate is assumed. -/
theorem rankStage_defect_class (i : Fin 3) :
    UnweightedClass (MeanMomentBounds.slowStripData (D := P) ε S hε hεone hS)
      (H + 9 / 10 - 2 * κ)
      (fun n x => CorrectionState.debt c (CorrectionState.rankStage p r axial c u) n x i) := by
  rw [rankStage_debt_eq]
  exact defects_after_rank_mem ha hab hcL hcR ε S hε hεone hS hop hbs hms hhs
    u.covariance hW ho hb hm hh hH (hg.solved_rows axial ha hop hbs hhs hV hG) i

include ha hab hcL hcR axial hg hop hbs hms hhs hW hV hG ho hb hm hh hH in
theorem rankStage_defectBounds {σ : ℝ} (hσ : 1 + σ ≤ H + 9 / 10 - 2 * κ) :
    CorrectionState.DefectBounds (MeanMomentBounds.slowStripData (D := P) ε S hε hεone hS) σ c
      (CorrectionState.rankStage p r axial c u) := by
  intro i
  exact (rankStage_defect_class ha hab hcL hcR ε S hε hεone hS axial hg hop hbs hms hhs hW
    hV hG ho hb hm hh hH i).mono_exponent hσ

end ConstructedBounds

end

end NavierStokes.DefectIncrementBounds
