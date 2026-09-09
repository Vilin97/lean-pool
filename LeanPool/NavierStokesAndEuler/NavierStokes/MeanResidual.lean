/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.CylindricalResidual
public import LeanPool.NavierStokesAndEuler.NavierStokes.TransportPrimitive

@[expose] public section

/-!
# Exact angularly averaged Navier--Stokes balances

The average is a normalized actual interval integral. All coordinate derivatives
are Fréchet derivatives on spacetime, and the Reynolds products include the
entire oscillatory velocity.
-/

namespace NavierStokes.MeanResidual

noncomputable section

open ProblemStatement Set Filter MeasureTheory
open AxisymmetricFields (projection)
open AxisymmetricResidual (pack pack_zero pack_one pack_two)
open scoped ContDiff Topology Interval

abbrev Scalar := SpaceTime → ℝ
abbrev Components := Fin 3 → Scalar

noncomputable def period : ℝ := 2 * Real.pi
noncomputable def angularVector : SpaceTime := (0, coordinateVector 1)
noncomputable def angularShift (q : SpaceTime) (a : ℝ) : SpaceTime := q + a • angularVector
noncomputable def radius (q : SpaceTime) : ℝ := q.2 0

theorem period_pos : 0 < period := mul_pos (by norm_num) Real.pi_pos
theorem period_ne_zero : period ≠ 0 := ne_of_gt period_pos

@[simp] theorem angularShift_zero (q : SpaceTime) : angularShift q 0 = q := by
  simp [angularShift]

@[simp] theorem radius_angularShift (q : SpaceTime) (a : ℝ) :
    radius (angularShift q a) = radius q := by
  simp [radius, angularShift, angularVector, coordinateVector]

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def direction (v : SpaceTime) (f : SpaceTime → E) (q : SpaceTime) : E :=
  fderiv ℝ f q v

noncomputable def dt (f : SpaceTime → E) := direction (1, 0) f
noncomputable def dr (f : SpaceTime → E) := direction (0, coordinateVector 0) f
noncomputable def dtheta (f : SpaceTime → E) := direction angularVector f
noncomputable def dz (f : SpaceTime → E) := direction (0, coordinateVector 2) f

noncomputable def average (f : SpaceTime → E) (q : SpaceTime) : E :=
  period⁻¹ • ∫ a in (0 : ℝ)..period, f (angularShift q a)

def AngularContinuous (f : SpaceTime → E) : Prop :=
  ∀ q, Continuous (fun a => f (angularShift q a))

def AngularPeriodic (f : SpaceTime → E) : Prop :=
  ∀ q, f (angularShift q period) = f q

def AngularInvariant (f : SpaceTime → E) : Prop :=
  ∀ q a, f (angularShift q a) = f q

theorem contDiff_angularShift :
    ContDiff ℝ ∞ (fun qa : SpaceTime × ℝ => angularShift qa.1 qa.2) :=
  contDiff_fst.add (contDiff_snd.smul contDiff_const)

theorem direction_smooth (v : SpaceTime) {f : SpaceTime → E} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (direction v f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

@[fun_prop] theorem direction_continuous (v : SpaceTime) {f : SpaceTime → E}
    (hf : ContDiff ℝ ∞ f) : Continuous (direction v f) := (direction_smooth v hf).continuous

@[fun_prop] theorem continuous_angularShift (q : SpaceTime) : Continuous (angularShift q) :=
  continuous_const.add (continuous_id.smul continuous_const)

omit [NormedSpace ℝ E] in
theorem angularContinuous_of_continuous {f : SpaceTime → E} (hf : Continuous f) :
    AngularContinuous f := by
  intro q
  exact hf.comp (continuous_const.add (continuous_id.smul continuous_const))

omit [NormedSpace ℝ E] in
theorem AngularContinuous.add {f g : SpaceTime → E}
    (hf : AngularContinuous f) (hg : AngularContinuous g) :
    AngularContinuous (fun q => f q + g q) := fun q => (hf q).add (hg q)

omit [NormedSpace ℝ E] in
theorem AngularContinuous.sub {f g : SpaceTime → E}
    (hf : AngularContinuous f) (hg : AngularContinuous g) :
    AngularContinuous (fun q => f q - g q) := fun q => (hf q).sub (hg q)

theorem AngularContinuous.mul {f g : Scalar}
    (hf : AngularContinuous f) (hg : AngularContinuous g) :
    AngularContinuous (fun q => f q * g q) := fun q => (hf q).mul (hg q)

theorem AngularContinuous.div_radius {f : Scalar} (hf : AngularContinuous f) (n : ℕ) :
    AngularContinuous (fun q => f q / radius q ^ n) := by
  intro q
  simpa only [radius_angularShift] using (hf q).div_const (radius q ^ n)

theorem AngularContinuous.const_mul {f : Scalar} (hf : AngularContinuous f) (c : ℝ) :
    AngularContinuous (fun q => c * f q) := fun q => continuous_const.mul (hf q)

omit [NormedSpace ℝ E] in
theorem AngularInvariant.angularContinuous {f : SpaceTime → E} (hf : AngularInvariant f) :
    AngularContinuous f := by
  intro q
  change ∀ q a, f (angularShift q a) = f q at hf
  simpa only [hf] using (continuous_const : Continuous (fun _ : ℝ => f q))

theorem average_add {f g : SpaceTime → E} (hf : AngularContinuous f)
    (hg : AngularContinuous g) (q : SpaceTime) :
    average (fun y => f y + g y) q = average f q + average g q := by
  unfold average
  rw [intervalIntegral.integral_add ((hf q).intervalIntegrable _ _)
    ((hg q).intervalIntegrable _ _), smul_add]

theorem average_sub {f g : SpaceTime → E} (hf : AngularContinuous f)
    (hg : AngularContinuous g) (q : SpaceTime) :
    average (fun y => f y - g y) q = average f q - average g q := by
  unfold average
  rw [intervalIntegral.integral_sub ((hf q).intervalIntegrable _ _)
    ((hg q).intervalIntegrable _ _), smul_sub]

theorem average_invariant [CompleteSpace E] {f : SpaceTime → E}
    (hf : AngularInvariant f) (q : SpaceTime) :
    average f q = f q := by
  change ∀ q a, f (angularShift q a) = f q at hf
  simp only [average, hf, intervalIntegral.integral_const, sub_zero, smul_smul,
    inv_mul_cancel₀ period_ne_zero, one_smul]

theorem average_const [CompleteSpace E] (c : E) (q : SpaceTime) : average (fun _ => c) q = c :=
  average_invariant (fun _ _ => rfl) q

theorem average_mul_invariant {a f : Scalar} (ha : AngularInvariant a) (q : SpaceTime) :
    average (fun y => a y * f y) q = a q * average f q := by
  change ∀ q θ, a (angularShift q θ) = a q at ha
  simp only [average, ha, intervalIntegral.integral_const_mul, smul_eq_mul]
  ring

theorem average_div_radius (f : Scalar) (q : SpaceTime) (n : ℕ) :
    average (fun y => f y / radius y ^ n) q = average f q / radius q ^ n := by
  simp only [average, radius_angularShift, intervalIntegral.integral_div, smul_eq_mul]
  ring

theorem average_div_r (f : Scalar) (q : SpaceTime) :
    average (fun y => f y / radius y) q = average f q / radius q := by
  simpa only [pow_one] using average_div_radius f q 1

theorem average_const_mul (c : ℝ) (f : Scalar) (q : SpaceTime) :
    average (fun y => c * f y) q = c * average f q :=
  average_mul_invariant (fun _ _ => rfl) q

theorem average_congr {f g : SpaceTime → E} {q : SpaceTime}
    (h : ∀ a ∈ uIcc (0 : ℝ) period, f (angularShift q a) = g (angularShift q a)) :
    average f q = average g q := by
  unfold average
  congr 1
  exact intervalIntegral.integral_congr h

theorem average_smooth [CompleteSpace E] {f : SpaceTime → E} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (average f) :=
  (TransportPrimitive.parameterIntegral_contDiff (hf.comp contDiff_angularShift)
    0 period).const_smul _

/-- Differentiation under the actual compact angular integral. -/
theorem direction_average [CompleteSpace E] {f : SpaceTime → E}
    (hf : ContDiff ℝ ∞ f) (v q : SpaceTime) :
    direction v (average f) q = average (direction v f) q := by
  let g : SpaceTime × ℝ → E := fun qa => f (angularShift qa.1 qa.2)
  have hg : ContDiff ℝ ∞ g := hf.comp contDiff_angularShift
  have hI := TransportPrimitive.parameterIntegral_hasFDerivAt hg 0 period q
  unfold direction average
  rw [(hI.fun_const_smul (period⁻¹)).fderiv]
  simp only [_root_.smul_apply]
  congr 1
  rw [ContinuousLinearMap.intervalIntegral_apply]
  · apply intervalIntegral.integral_congr
    intro a _
    have hchain : HasFDerivAt (fun x => f (angularShift x a))
        (fderiv ℝ f (angularShift q a)) q := by
      simpa only [angularShift, Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using
        ((hf.differentiable (by simp)) (angularShift q a)).hasFDerivAt.comp q
          ((hasFDerivAt_id q).add_const (a • angularVector))
    exact congrArg (fun L : SpaceTime →L[ℝ] E => L v)
      ((TransportPrimitive.parameter_hasFDerivAt hg q a).unique hchain)
  · exact ((TransportPrimitive.parameterDerivative_contDiff hg).continuous.comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable _ _

theorem AngularPeriodic.direction {f : SpaceTime → E} (hp : AngularPeriodic f)
    (v : SpaceTime) : AngularPeriodic (direction v f) := by
  intro q
  have he : (fun x => f (x + period • angularVector)) = f := funext hp
  have hd := congrArg (fun F => fderiv ℝ F q) he
  rw [fderiv_comp_add_right] at hd
  exact congrArg (fun L : SpaceTime →L[ℝ] E => L v) hd

theorem AngularInvariant.direction {f : SpaceTime → E} (hp : AngularInvariant f)
    (v : SpaceTime) : AngularInvariant (direction v f) := by
  intro q a
  have he : (fun x => f (x + a • angularVector)) = f := funext (fun x => hp x a)
  have hd := congrArg (fun F => fderiv ℝ F q) he
  rw [fderiv_comp_add_right] at hd
  exact congrArg (fun L : SpaceTime →L[ℝ] E => L v) hd

theorem AngularPeriodic.mul {f g : Scalar} (hf : AngularPeriodic f) (hg : AngularPeriodic g) :
    AngularPeriodic (fun q => f q * g q) := by
  intro q
  change f (angularShift q period) * g (angularShift q period) = f q * g q
  rw [hf q, hg q]

/-- A full angular derivative has exactly zero average, by the fundamental theorem. -/
theorem average_dtheta_zero [CompleteSpace E] {f : SpaceTime → E}
    (hf : ContDiff ℝ ∞ f) (hp : AngularPeriodic f) (q : SpaceTime) :
    average (dtheta f) q = 0 := by
  have hd : ∀ a : ℝ, HasDerivAt (fun b => f (angularShift q b))
      (dtheta f (angularShift q a)) a := by
    intro a
    have hs : HasDerivAt (fun b : ℝ => angularShift q b) angularVector a := by
      simpa [angularShift] using ((hasDerivAt_id a).smul_const angularVector).const_add q
    exact ((hf.differentiable (by simp)) (angularShift q a)).hasFDerivAt.comp_hasDerivAt a hs
  have hc : AngularContinuous (dtheta f) :=
    angularContinuous_of_continuous (direction_smooth angularVector hf).continuous
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun a _ => hd a)
    ((hc q).intervalIntegrable 0 period)
  rw [hp, angularShift_zero, sub_self] at hi
  simp only [average, hi, smul_zero]

theorem dtheta_invariant_zero [CompleteSpace E] {f : SpaceTime → E}
    (hf : ContDiff ℝ ∞ f) (hp : AngularInvariant f) (q : SpaceTime) : dtheta f q = 0 := by
  have he : average f = f := funext (average_invariant hp)
  calc
    dtheta f q = dtheta (average f) q := by rw [he]
    _ = average (dtheta f) q := direction_average hf angularVector q
    _ = 0 := average_dtheta_zero hf (fun y => hp y period) q

theorem direction_add {f g : SpaceTime → E} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (v q : SpaceTime) :
    direction v (fun y => f y + g y) q = direction v f q + direction v g q := by
  unfold direction
  rw [fderiv_fun_add (hf.differentiable (by simp) q) (hg.differentiable (by simp) q)]
  rfl

theorem direction_sub {f g : SpaceTime → E} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (v q : SpaceTime) :
    direction v (fun y => f y - g y) q = direction v f q - direction v g q := by
  unfold direction
  rw [fderiv_fun_sub (hf.differentiable (by simp) q) (hg.differentiable (by simp) q)]
  rfl

theorem direction_mul {f g : Scalar} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (v q : SpaceTime) :
    direction v (fun y => f y * g y) q = direction v f q * g q + f q * direction v g q := by
  unfold direction
  rw [fderiv_fun_mul (hf.differentiable (by simp) q) (hg.differentiable (by simp) q)]
  simp
  ring

theorem direction_map (L : E →L[ℝ] F) {f : SpaceTime → E} (hf : ContDiff ℝ ∞ f)
    (v q : SpaceTime) :
    direction v (fun y => L (f y)) q = L (direction v f q) := by
  unfold direction
  change (fderiv ℝ (L ∘ f) q) v = _
  rw [(L.hasFDerivAt.comp q (hf.differentiable (by simp) q).hasFDerivAt).fderiv]
  rfl

theorem spatial_direction {f : SpaceTime → E} (hf : ContDiff ℝ ∞ f)
    (t : ℝ) (x : Space) (i : Fin 3) :
    CylindricalResidual.dCoord i (fun y => f (t, y)) x =
      direction (0, coordinateVector i) f (t, x) := by
  have h := (hf.differentiable (by simp) (t, x)).hasFDerivAt.comp x
    ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
  change (fderiv ℝ (f ∘ fun y => (t, y)) x) _ = _
  rw [h.fderiv]
  rfl

theorem spatial_second {f : SpaceTime → E} (hf : ContDiff ℝ ∞ f)
    (t : ℝ) (x : Space) (i : Fin 3) :
    CylindricalResidual.dCoord i (CylindricalResidual.dCoord i (fun y => f (t, y))) x =
      direction (0, coordinateVector i) (direction (0, coordinateVector i) f) (t, x) := by
  rw [show CylindricalResidual.dCoord i (fun y => f (t, y)) =
      fun y => direction (0, coordinateVector i) f (t, y) from
    funext (fun y => spatial_direction hf t y i)]
  exact spatial_direction (direction_smooth _ hf) t x i

theorem temporal_direction {f : SpaceTime → E} (hf : ContDiff ℝ ∞ f)
    (t : ℝ) (x : Space) :
    fderiv ℝ (fun s => f (s, x)) t 1 = dt f (t, x) := by
  have h := (hf.differentiable (by simp) (t, x)).hasFDerivAt.comp t
    ((hasFDerivAt_id (𝕜 := ℝ) t).prodMk (hasFDerivAt_const (𝕜 := ℝ) x t))
  change (fderiv ℝ (f ∘ fun s => (id s, x)) t) 1 = _
  rw [h.fderiv]
  rfl

noncomputable def velocity (w : Components) : VelocityField :=
  fun q => pack (w 0 q) (w 1 q) (w 2 q)

@[simp] theorem velocity_apply (w : Components) (q : SpaceTime) (i : Fin 3) :
    velocity w q i = w i q := by
  fin_cases i <;> simp [velocity]

theorem velocity_smooth {w : Components} (hw : ∀ i, ContDiff ℝ ∞ (w i)) :
    ContDiff ℝ ∞ (velocity w) :=
  (((hw 0).smul contDiff_const).add ((hw 1).smul contDiff_const)).add
    ((hw 2).smul contDiff_const)

theorem direction_velocity {w : Components} (hw : ∀ i, ContDiff ℝ ∞ (w i))
    (v q : SpaceTime) : direction v (velocity w) q =
      pack (direction v (w 0) q) (direction v (w 1) q) (direction v (w 2) q) := by
  exact AxisymmetricResidual.fderiv_pack_apply
    ((hw 0).differentiable (by simp) q) ((hw 1).differentiable (by simp) q)
    ((hw 2).differentiable (by simp) q) v

theorem direction_velocity_component {w : Components} (hw : ∀ i, ContDiff ℝ ∞ (w i))
    (v q : SpaceTime) (i : Fin 3) : direction v (velocity w) q i = direction v (w i) q := by
  rw [direction_velocity hw]
  fin_cases i <;> simp

noncomputable def laplacian (f : Scalar) (q : SpaceTime) : ℝ :=
  dr (dr f) q + dr f q / radius q + dtheta (dtheta f) q / radius q ^ 2 + dz (dz f) q

noncomputable def meanLaplacian (f : Scalar) (q : SpaceTime) : ℝ :=
  dr (dr f) q + dr f q / radius q + dz (dz f) q

noncomputable def radialDivergence (c : ℝ) (f : Scalar) (q : SpaceTime) : ℝ :=
  dr f q + c / radius q * f q

noncomputable def divergence (w : Components) (q : SpaceTime) : ℝ :=
  dr (w 0) q + w 0 q / radius q + dtheta (w 1) q / radius q + dz (w 2) q

noncomputable def transport (w : Components) (f : Scalar) (q : SpaceTime) : ℝ :=
  w 0 q * dr f q + w 1 q / radius q * dtheta f q + w 2 q * dz f q

noncomputable def residualRadial (w : Components) (p : Scalar) (q : SpaceTime) : ℝ :=
  dt (w 0) q + transport w (w 0) q - (w 1 q) ^ 2 / radius q - laplacian (w 0) q +
    w 0 q / radius q ^ 2 + 2 * dtheta (w 1) q / radius q ^ 2 + dr p q

noncomputable def residualAngular (w : Components) (p : Scalar) (q : SpaceTime) : ℝ :=
  dt (w 1) q + transport w (w 1) q + w 0 q * w 1 q / radius q - laplacian (w 1) q +
    w 1 q / radius q ^ 2 - 2 * dtheta (w 0) q / radius q ^ 2 + dtheta p q / radius q

noncomputable def residualAxial (w : Components) (p : Scalar) (q : SpaceTime) : ℝ :=
  dt (w 2) q + transport w (w 2) q - laplacian (w 2) q + dz p q

theorem scalarLaplacian_eq {f : Scalar} (hf : ContDiff ℝ ∞ f) (q : SpaceTime) :
    CylindricalResidual.scalarLaplacian (fun y => f (q.1, y)) q.2 = laplacian f q := by
  simp only [CylindricalResidual.scalarLaplacian, spatial_second hf, spatial_direction hf,
    laplacian, dr, dtheta, dz, angularVector, radius, smul_eq_mul]
  ring

theorem scalarLaplacian_velocity {w : Components} (hw : ∀ i, ContDiff ℝ ∞ (w i))
    (q : SpaceTime) (i : Fin 3) :
    CylindricalResidual.scalarLaplacian (fun y => velocity w (q.1, y)) q.2 i =
      laplacian (w i) q := by
  have hv : ContDiff ℝ 2 (velocity w) := (velocity_smooth hw).of_le
    (show (2 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hs : ContDiffAt ℝ 2 (fun y => velocity w (q.1, y)) q.2 :=
    (hv.comp (contDiff_const.prodMk contDiff_id)).contDiffAt
  rw [← CylindricalResidual.scalarLaplacian_component hs i]
  simpa only [velocity_apply] using scalarLaplacian_eq (hw i) q

theorem cylindricalResidual_radial {w : Components} {p : Scalar}
    (hw : ∀ i, ContDiff ℝ ∞ (w i)) (hp : ContDiff ℝ ∞ p) (q : SpaceTime) :
    CylindricalResidual.cylindricalResidual (velocity w) p q.1 q.2 0 =
      residualRadial w p q := by
  change (temporalDerivative (velocity w) q.1 q.2) 0 +
    CylindricalResidual.vectorAdvection (fun y => velocity w (q.1, y)) q.2 0 -
    CylindricalResidual.vectorLaplacian (fun y => velocity w (q.1, y)) q.2 0 +
    CylindricalResidual.scalarGradient (fun y => p (q.1, y)) q.2 0 = _
  rw [CylindricalResidual.vectorAdvection_radial, CylindricalResidual.vectorLaplacian_radial,
    scalarLaplacian_velocity hw q 0]
  simp only [temporalDerivative, temporal_direction (velocity_smooth hw), dt,
    direction_velocity_component hw, spatial_direction (velocity_smooth hw),
    velocity_apply, CylindricalResidual.scalarGradient, pack_zero, spatial_direction hp,
    residualRadial, transport, dr, dtheta, dz, angularVector, radius]
  ring

theorem cylindricalResidual_angular {w : Components} {p : Scalar}
    (hw : ∀ i, ContDiff ℝ ∞ (w i)) (hp : ContDiff ℝ ∞ p) (q : SpaceTime) :
    CylindricalResidual.cylindricalResidual (velocity w) p q.1 q.2 1 =
      residualAngular w p q := by
  change (temporalDerivative (velocity w) q.1 q.2) 1 +
    CylindricalResidual.vectorAdvection (fun y => velocity w (q.1, y)) q.2 1 -
    CylindricalResidual.vectorLaplacian (fun y => velocity w (q.1, y)) q.2 1 +
    CylindricalResidual.scalarGradient (fun y => p (q.1, y)) q.2 1 = _
  rw [CylindricalResidual.vectorAdvection_angular, CylindricalResidual.vectorLaplacian_angular,
    scalarLaplacian_velocity hw q 1]
  simp only [temporalDerivative, temporal_direction (velocity_smooth hw), dt,
    direction_velocity_component hw, spatial_direction (velocity_smooth hw),
    velocity_apply, CylindricalResidual.scalarGradient, pack_one, spatial_direction hp,
    residualAngular, transport, dr, dtheta, dz, angularVector, radius]
  ring

theorem cylindricalResidual_axial {w : Components} {p : Scalar}
    (hw : ∀ i, ContDiff ℝ ∞ (w i)) (hp : ContDiff ℝ ∞ p) (q : SpaceTime) :
    CylindricalResidual.cylindricalResidual (velocity w) p q.1 q.2 2 =
      residualAxial w p q := by
  change (temporalDerivative (velocity w) q.1 q.2) 2 +
    CylindricalResidual.vectorAdvection (fun y => velocity w (q.1, y)) q.2 2 -
    CylindricalResidual.vectorLaplacian (fun y => velocity w (q.1, y)) q.2 2 +
    CylindricalResidual.scalarGradient (fun y => p (q.1, y)) q.2 2 = _
  rw [CylindricalResidual.vectorAdvection_axial, CylindricalResidual.vectorLaplacian_axial,
    scalarLaplacian_velocity hw q 2]
  simp only [temporalDerivative, temporal_direction (velocity_smooth hw), dt,
    direction_velocity_component hw, spatial_direction (velocity_smooth hw),
    velocity_apply, CylindricalResidual.scalarGradient, pack_two, spatial_direction hp,
    residualAxial, transport, dr, dtheta, dz, angularVector, radius]

noncomputable def conservativeRadial (w : Components) (p : Scalar) (q : SpaceTime) : ℝ :=
  dt (w 0) q + radialDivergence 1 (fun y => w 0 y * w 0 y) q +
    dtheta (fun y => w 1 y * w 0 y) q / radius q +
    dz (fun y => w 2 y * w 0 y) q - (w 1 q * w 1 q) / radius q - laplacian (w 0) q +
    w 0 q / radius q ^ 2 + 2 * dtheta (w 1) q / radius q ^ 2 + dr p q

noncomputable def conservativeAngular (w : Components) (p : Scalar) (q : SpaceTime) : ℝ :=
  dt (w 1) q + radialDivergence 2 (fun y => w 0 y * w 1 y) q +
    dtheta (fun y => w 1 y * w 1 y) q / radius q +
    dz (fun y => w 2 y * w 1 y) q - laplacian (w 1) q +
    w 1 q / radius q ^ 2 - 2 * dtheta (w 0) q / radius q ^ 2 + dtheta p q / radius q

noncomputable def conservativeAxial (w : Components) (p : Scalar) (q : SpaceTime) : ℝ :=
  dt (w 2) q + radialDivergence 1 (fun y => w 0 y * w 2 y) q +
    dtheta (fun y => w 1 y * w 2 y) q / radius q +
    dz (fun y => w 2 y * w 2 y) q - laplacian (w 2) q + dz p q

theorem conservativeRadial_eq {w : Components} (hw : ∀ i, ContDiff ℝ ∞ (w i))
    (p : Scalar) (q : SpaceTime) :
    conservativeRadial w p q = residualRadial w p q + w 0 q * divergence w q := by
  simp only [conservativeRadial, residualRadial, radialDivergence, transport, divergence,
    dr, dtheta, dz, direction_mul (hw 0) (hw 0), direction_mul (hw 1) (hw 0),
    direction_mul (hw 2) (hw 0)]
  ring

theorem conservativeAngular_eq {w : Components} (hw : ∀ i, ContDiff ℝ ∞ (w i))
    (p : Scalar) (q : SpaceTime) :
    conservativeAngular w p q = residualAngular w p q + w 1 q * divergence w q := by
  simp only [conservativeAngular, residualAngular, radialDivergence, transport, divergence,
    dr, dtheta, dz, direction_mul (hw 0) (hw 1), direction_mul (hw 1) (hw 1),
    direction_mul (hw 2) (hw 1)]
  ring

theorem conservativeAxial_eq {w : Components} (hw : ∀ i, ContDiff ℝ ∞ (w i))
    (p : Scalar) (q : SpaceTime) :
    conservativeAxial w p q = residualAxial w p q + w 2 q * divergence w q := by
  simp only [conservativeAxial, residualAxial, radialDivergence, transport, divergence,
    dr, dtheta, dz, direction_mul (hw 0) (hw 2), direction_mul (hw 1) (hw 2),
    direction_mul (hw 2) (hw 2)]
  ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem angularInvariant_radius (f : ℝ → E) : AngularInvariant (fun q => f (radius q)) := by
  intro q a
  exact congrArg f (radius_angularShift q a)

theorem average_direction [CompleteSpace E] {f : SpaceTime → E}
    (hf : ContDiff ℝ ∞ f) (v q : SpaceTime) :
    average (direction v f) q = direction v (average f) q := (direction_average hf v q).symm

theorem average_direction_twice [CompleteSpace E] {f : SpaceTime → E}
    (hf : ContDiff ℝ ∞ f) (v w q : SpaceTime) :
    average (direction v (direction w f)) q = direction v (direction w (average f)) q := by
  rw [average_direction (direction_smooth w hf)]
  rw [show average (direction w f) = direction w (average f) from
    funext (average_direction hf w)]

theorem average_dt {f : Scalar} (hf : ContDiff ℝ ∞ f) (q : SpaceTime) :
    average (dt f) q = dt (average f) q := average_direction hf _ q

theorem average_dr {f : Scalar} (hf : ContDiff ℝ ∞ f) (q : SpaceTime) :
    average (dr f) q = dr (average f) q := average_direction hf _ q

theorem average_dz {f : Scalar} (hf : ContDiff ℝ ∞ f) (q : SpaceTime) :
    average (dz f) q = dz (average f) q := average_direction hf _ q

theorem average_drdr {f : Scalar} (hf : ContDiff ℝ ∞ f) (q : SpaceTime) :
    average (dr (dr f)) q = dr (dr (average f)) q := average_direction_twice hf _ _ q

theorem average_dzdz {f : Scalar} (hf : ContDiff ℝ ∞ f) (q : SpaceTime) :
    average (dz (dz f)) q = dz (dz (average f)) q := average_direction_twice hf _ _ q

theorem angularContinuous_direction {f : Scalar} (hf : ContDiff ℝ ∞ f) (v : SpaceTime) :
    AngularContinuous (direction v f) := angularContinuous_of_continuous (direction_smooth v
      hf).continuous

theorem AngularContinuous.div_r {f : Scalar} (hf : AngularContinuous f) :
    AngularContinuous (fun q => f q / radius q) := by
  simpa only [pow_one] using hf.div_radius 1

theorem angularContinuous_radialDivergence {f : Scalar} (hf : ContDiff ℝ ∞ f) (c : ℝ) :
    AngularContinuous (radialDivergence c f) :=
  (angularContinuous_direction hf _).add
    ((angularInvariant_radius (fun r => c / r)).angularContinuous.mul
      (angularContinuous_of_continuous hf.continuous))

theorem angularContinuous_laplacian {f : Scalar} (hf : ContDiff ℝ ∞ f) :
    AngularContinuous (laplacian f) :=
  (((angularContinuous_direction (direction_smooth _ hf) _).add
    (angularContinuous_direction hf _).div_r).add
      ((angularContinuous_direction (direction_smooth _ hf) _).div_radius 2)).add
        (angularContinuous_direction (direction_smooth _ hf) _)

theorem average_radialDivergence {f : Scalar} (hf : ContDiff ℝ ∞ f)
    (c : ℝ) (q : SpaceTime) :
    average (radialDivergence c f) q = radialDivergence c (average f) q := by
  have hr : AngularContinuous (dr f) := angularContinuous_of_continuous
    (direction_smooth _ hf).continuous
  have hc : AngularInvariant (fun y => c / radius y) := angularInvariant_radius _
  have hcf := hc.angularContinuous.mul (angularContinuous_of_continuous hf.continuous)
  unfold radialDivergence
  rw [average_add hr hcf, average_mul_invariant hc, average_dr hf]

theorem average_laplacian {f : Scalar} (hf : ContDiff ℝ ∞ f) (hp : AngularPeriodic f)
    (q : SpaceTime) : average (laplacian f) q = meanLaplacian (average f) q := by
  have hrr : AngularContinuous (dr (dr f)) := angularContinuous_of_continuous
    (direction_smooth _ (direction_smooth _ hf)).continuous
  have hr : AngularContinuous (dr f) := angularContinuous_of_continuous
    (direction_smooth _ hf).continuous
  have haa : AngularContinuous (dtheta (dtheta f)) := angularContinuous_of_continuous
    (direction_smooth _ (direction_smooth _ hf)).continuous
  have hzz : AngularContinuous (dz (dz f)) := angularContinuous_of_continuous
    (direction_smooth _ (direction_smooth _ hf)).continuous
  have hrd : AngularContinuous (fun y => dr f y / radius y) := by
    simpa only [pow_one] using hr.div_radius 1
  unfold laplacian meanLaplacian
  rw [average_add ((hrr.add hrd).add (haa.div_radius 2)) hzz,
    average_add (hrr.add hrd) (haa.div_radius 2), average_add hrr hrd]
  rw [show (fun y => dr f y / radius y) = (fun y => dr f y / radius y ^ 1) by simp]
  rw [average_div_radius, average_div_radius, average_drdr hf,
    average_dr hf, average_dzdz hf,
    average_dtheta_zero (f := dtheta f) (direction_smooth _ hf) (hp.direction angularVector)]
  simp

noncomputable def reynoldsRadial (w : Components) (p : Scalar) (q : SpaceTime) : ℝ :=
  dt (average (w 0)) q + radialDivergence 1 (average (fun y => w 0 y * w 0 y)) q +
    dz (average (fun y => w 2 y * w 0 y)) q - average (fun y => w 1 y * w 1 y) q / radius q -
    meanLaplacian (average (w 0)) q + average (w 0) q / radius q ^ 2 + dr (average p) q

noncomputable def reynoldsAngular (w : Components) (q : SpaceTime) : ℝ :=
  dt (average (w 1)) q + radialDivergence 2 (average (fun y => w 0 y * w 1 y)) q +
    dz (average (fun y => w 2 y * w 1 y)) q - meanLaplacian (average (w 1)) q +
    average (w 1) q / radius q ^ 2

noncomputable def reynoldsAxial (w : Components) (p : Scalar) (q : SpaceTime) : ℝ :=
  dt (average (w 2)) q + radialDivergence 1 (average (fun y => w 0 y * w 2 y)) q +
    dz (average (fun y => w 2 y * w 2 y)) q - meanLaplacian (average (w 2)) q +
    dz (average p) q

theorem average_conservativeAngular {w : Components} {p : Scalar}
    (hw : ∀ i, ContDiff ℝ ∞ (w i)) (hp : ContDiff ℝ ∞ p)
    (hwper : ∀ i, AngularPeriodic (w i)) (hpper : AngularPeriodic p) (q : SpaceTime) :
    average (conservativeAngular w p) q = reynoldsAngular w q := by
  have h1 : AngularContinuous (dt (w 1)) := angularContinuous_direction (hw 1) _
  have h2 := angularContinuous_radialDivergence ((hw 0).mul (hw 1)) 2
  have h3 : AngularContinuous (fun y => dtheta (fun y => w 1 y * w 1 y) y / radius y) :=
    (angularContinuous_direction ((hw 1).mul (hw 1)) _).div_r
  have h4 : AngularContinuous (dz (fun y => w 2 y * w 1 y)) :=
    angularContinuous_direction ((hw 2).mul (hw 1)) _
  have h5 := angularContinuous_laplacian (hw 1)
  have h6 := (angularContinuous_of_continuous (hw 1).continuous).div_radius 2
  have h7 : AngularContinuous (fun y => 2 * dtheta (w 0) y / radius y ^ 2) :=
    ((angularContinuous_direction (hw 0) _).const_mul 2).div_radius 2
  have h8 : AngularContinuous (fun y => dtheta p y / radius y) :=
    (angularContinuous_direction hp _).div_r
  unfold conservativeAngular
  simp (disch := solve_by_elim (maxDepth := 20) [AngularContinuous.add, AngularContinuous.sub])
    only [average_add, average_sub]
  rw [average_radialDivergence ((hw 0).mul (hw 1)),
    average_laplacian (hw 1) (hwper 1)]
  rw [average_dt (hw 1), average_dz ((hw 2).mul (hw 1))]
  rw [show (fun y => dtheta (fun y => w 1 y * w 1 y) y / radius y) =
      (fun y => dtheta (fun y => w 1 y * w 1 y) y / radius y ^ 1) by simp]
  rw [show (fun y => dtheta p y / radius y) = (fun y => dtheta p y / radius y ^ 1) by simp]
  rw [average_div_radius, average_div_radius, average_div_radius, average_div_radius,
    average_const_mul, average_dtheta_zero ((hw 1).mul (hw 1)) ((hwper 1).mul (hwper 1)),
    average_dtheta_zero (hw 0) (hwper 0), average_dtheta_zero hp hpper]
  simp [reynoldsAngular, dt, dz]

theorem average_conservativeRadial {w : Components} {p : Scalar}
    (hw : ∀ i, ContDiff ℝ ∞ (w i)) (hp : ContDiff ℝ ∞ p)
    (hwper : ∀ i, AngularPeriodic (w i)) (q : SpaceTime) :
    average (conservativeRadial w p) q = reynoldsRadial w p q := by
  have h1 : AngularContinuous (dt (w 0)) := angularContinuous_direction (hw 0) _
  have h2 := angularContinuous_radialDivergence ((hw 0).mul (hw 0)) 1
  have h3 : AngularContinuous (fun y => dtheta (fun y => w 1 y * w 0 y) y / radius y) :=
    (angularContinuous_direction ((hw 1).mul (hw 0)) _).div_r
  have h4 : AngularContinuous (dz (fun y => w 2 y * w 0 y)) :=
    angularContinuous_direction ((hw 2).mul (hw 0)) _
  have h5 := (angularContinuous_of_continuous ((hw 1).mul (hw 1)).continuous).div_r
  have h6 := angularContinuous_laplacian (hw 0)
  have h7 := (angularContinuous_of_continuous (hw 0).continuous).div_radius 2
  have h8 : AngularContinuous (fun y => 2 * dtheta (w 1) y / radius y ^ 2) :=
    ((angularContinuous_direction (hw 1) _).const_mul 2).div_radius 2
  have h9 : AngularContinuous (dr p) := angularContinuous_direction hp _
  unfold conservativeRadial
  simp (disch := solve_by_elim (maxDepth := 20) [AngularContinuous.add, AngularContinuous.sub])
    only [average_add, average_sub]
  rw [average_radialDivergence ((hw 0).mul (hw 0)), average_laplacian (hw 0) (hwper 0),
    average_dt (hw 0), average_dz ((hw 2).mul (hw 0)), average_dr hp]
  simp only [average_div_r, average_div_radius, average_const_mul,
    average_dtheta_zero ((hw 1).mul (hw 0)) ((hwper 1).mul (hwper 0)),
    average_dtheta_zero (hw 1) (hwper 1), zero_div, mul_zero, add_zero]
  rfl

theorem average_conservativeAxial {w : Components} {p : Scalar}
    (hw : ∀ i, ContDiff ℝ ∞ (w i)) (hp : ContDiff ℝ ∞ p)
    (hwper : ∀ i, AngularPeriodic (w i)) (q : SpaceTime) :
    average (conservativeAxial w p) q = reynoldsAxial w p q := by
  have h1 : AngularContinuous (dt (w 2)) := angularContinuous_direction (hw 2) _
  have h2 := angularContinuous_radialDivergence ((hw 0).mul (hw 2)) 1
  have h3 : AngularContinuous (fun y => dtheta (fun y => w 1 y * w 2 y) y / radius y) :=
    (angularContinuous_direction ((hw 1).mul (hw 2)) _).div_r
  have h4 : AngularContinuous (dz (fun y => w 2 y * w 2 y)) :=
    angularContinuous_direction ((hw 2).mul (hw 2)) _
  have h5 := angularContinuous_laplacian (hw 2)
  have h6 : AngularContinuous (dz p) := angularContinuous_direction hp _
  unfold conservativeAxial
  simp (disch := solve_by_elim (maxDepth := 20) [AngularContinuous.add, AngularContinuous.sub])
    only [average_add, average_sub]
  rw [average_radialDivergence ((hw 0).mul (hw 2)), average_laplacian (hw 2) (hwper 2),
    average_dt (hw 2), average_dz ((hw 2).mul (hw 2)), average_dz hp]
  simp only [average_div_r,
    average_dtheta_zero ((hw 1).mul (hw 2)) ((hwper 1).mul (hwper 2)), zero_div, add_zero]
  rfl

theorem average_residualRadial {w : Components} {p : Scalar}
    (hw : ∀ i, ContDiff ℝ ∞ (w i)) (hp : ContDiff ℝ ∞ p)
    (hwper : ∀ i, AngularPeriodic (w i))
    (hdiv : ∀ y, 0 < radius y → divergence w y = 0)
    (q : SpaceTime) (hr : 0 < radius q) :
    average (residualRadial w p) q = reynoldsRadial w p q := by
  have he : average (residualRadial w p) q = average (conservativeRadial w p) q := by
    apply average_congr
    intro a _
    have hd := hdiv (angularShift q a) (by simpa only [radius_angularShift] using hr)
    simpa only [hd, mul_zero, add_zero] using (conservativeRadial_eq hw p (angularShift q a)).symm
  rw [he, average_conservativeRadial hw hp hwper]

theorem average_residualAngular {w : Components} {p : Scalar}
    (hw : ∀ i, ContDiff ℝ ∞ (w i)) (hp : ContDiff ℝ ∞ p)
    (hwper : ∀ i, AngularPeriodic (w i)) (hpper : AngularPeriodic p)
    (hdiv : ∀ y, 0 < radius y → divergence w y = 0)
    (q : SpaceTime) (hr : 0 < radius q) :
    average (residualAngular w p) q = reynoldsAngular w q := by
  have he : average (residualAngular w p) q = average (conservativeAngular w p) q := by
    apply average_congr
    intro a _
    have hd := hdiv (angularShift q a) (by simpa only [radius_angularShift] using hr)
    simpa only [hd, mul_zero, add_zero] using (conservativeAngular_eq hw p (angularShift q a)).symm
  rw [he, average_conservativeAngular hw hp hwper hpper]

theorem average_residualAxial {w : Components} {p : Scalar}
    (hw : ∀ i, ContDiff ℝ ∞ (w i)) (hp : ContDiff ℝ ∞ p)
    (hwper : ∀ i, AngularPeriodic (w i))
    (hdiv : ∀ y, 0 < radius y → divergence w y = 0)
    (q : SpaceTime) (hr : 0 < radius q) :
    average (residualAxial w p) q = reynoldsAxial w p q := by
  have he : average (residualAxial w p) q = average (conservativeAxial w p) q := by
    apply average_congr
    intro a _
    have hd := hdiv (angularShift q a) (by simpa only [radius_angularShift] using hr)
    simpa only [hd, mul_zero, add_zero] using (conservativeAxial_eq hw p (angularShift q a)).symm
  rw [he, average_conservativeAxial hw hp hwper]

omit [NormedSpace ℝ E] in
theorem AngularInvariant.add {f g : SpaceTime → E}
    (hf : AngularInvariant f) (hg : AngularInvariant g) :
    AngularInvariant (fun q => f q + g q) := by
  intro q a
  exact congrArg₂ (· + ·) (hf q a) (hg q a)

theorem AngularInvariant.mul {f g : Scalar}
    (hf : AngularInvariant f) (hg : AngularInvariant g) :
    AngularInvariant (fun q => f q * g q) := by
  intro q a
  exact congrArg₂ (· * ·) (hf q a) (hg q a)

omit [NormedSpace ℝ E] in
theorem AngularPeriodic.add {f g : SpaceTime → E}
    (hf : AngularPeriodic f) (hg : AngularPeriodic g) :
    AngularPeriodic (fun q => f q + g q) := by
  intro q
  exact congrArg₂ (· + ·) (hf q) (hg q)

/-- The complete velocity split, with no omission of any part of `osc`. -/
noncomputable def total (base mean osc : Components) : Components :=
  fun i q => base i q + mean i q + osc i q

/-- The exact Reynolds product of the full oscillatory fields. -/
noncomputable def covariance (osc : Components) (i j : Fin 3) : Scalar :=
  average (fun q => osc i q * osc j q)

noncomputable def fluxDifference (base mean osc : Components) (i j : Fin 3) : Scalar :=
  fun q => base i q * mean j q + mean i q * base j q +
    mean i q * mean j q + covariance osc i j q

theorem covariance_smooth {osc : Components} (ho : ∀ i, ContDiff ℝ ∞ (osc i)) (i j : Fin 3) :
    ContDiff ℝ ∞ (covariance osc i j) := average_smooth ((ho i).mul (ho j))

theorem covariance_symm (osc : Components) (i j : Fin 3) : covariance osc i j = covariance osc j i
  := by
  simp only [covariance, mul_comm]

theorem total_smooth {base mean osc : Components}
    (hb : ∀ i, ContDiff ℝ ∞ (base i)) (hm : ∀ i, ContDiff ℝ ∞ (mean i))
    (ho : ∀ i, ContDiff ℝ ∞ (osc i)) (i : Fin 3) :
    ContDiff ℝ ∞ (total base mean osc i) := ((hb i).add (hm i)).add (ho i)

theorem fluxDifference_smooth {base mean osc : Components}
    (hb : ∀ i, ContDiff ℝ ∞ (base i)) (hm : ∀ i, ContDiff ℝ ∞ (mean i))
    (ho : ∀ i, ContDiff ℝ ∞ (osc i)) (i j : Fin 3) :
    ContDiff ℝ ∞ (fluxDifference base mean osc i j) :=
  ((((hb i).mul (hm j)).add ((hm i).mul (hb j))).add ((hm i).mul (hm j))).add
    (covariance_smooth ho i j)

theorem total_periodic {base mean osc : Components}
    (hb : ∀ i, AngularInvariant (base i)) (hm : ∀ i, AngularInvariant (mean i))
    (ho : ∀ i, AngularPeriodic (osc i)) (i : Fin 3) :
    AngularPeriodic (total base mean osc i) :=
  AngularPeriodic.add (AngularPeriodic.add (fun q => hb i q period)
    (fun q => hm i q period)) (ho i)

theorem average_affine_product {a b f g : Scalar}
    (ha : AngularInvariant a) (hb : AngularInvariant b)
    (hf : AngularContinuous f) (hg : AngularContinuous g)
    (q : SpaceTime) (hf0 : average f q = 0) (hg0 : average g q = 0) :
    average (fun y => (a y + f y) * (b y + g y)) q =
      a q * b q + average (fun y => f y * g y) q := by
  have he : (fun y => (a y + f y) * (b y + g y)) =
      (fun y => a y * b y + a y * g y + b y * f y + f y * g y) := by
    funext y
    ring
  have h1 := ha.angularContinuous.mul hb.angularContinuous
  have h2 := ha.angularContinuous.mul hg
  have h3 := hb.angularContinuous.mul hf
  have h4 := hf.mul hg
  rw [he, average_add ((h1.add h2).add h3) h4, average_add (h1.add h2) h3,
    average_add h1 h2, average_invariant (ha.mul hb),
    average_mul_invariant ha, average_mul_invariant hb, hf0, hg0]
  ring

theorem average_total {base mean osc : Components}
    (hb : ∀ i, AngularInvariant (base i)) (hm : ∀ i, AngularInvariant (mean i))
    (ho : ∀ i, AngularContinuous (osc i))
    (hz : ∀ i q, average (osc i) q = 0) (i : Fin 3) :
    average (total base mean osc i) = fun q => base i q + mean i q := by
  funext q
  unfold total
  rw [average_add ((hb i).angularContinuous.add (hm i).angularContinuous) (ho i),
    average_add (hb i).angularContinuous (hm i).angularContinuous,
    average_invariant (hb i), average_invariant (hm i), hz]
  simp

theorem average_total_product {base mean osc : Components}
    (hb : ∀ i, AngularInvariant (base i)) (hm : ∀ i, AngularInvariant (mean i))
    (ho : ∀ i, AngularContinuous (osc i))
    (hz : ∀ i q, average (osc i) q = 0) (i j : Fin 3) :
    average (fun q => total base mean osc i q * total base mean osc j q) =
      fun q => base i q * base j q + fluxDifference base mean osc i j q := by
  funext q
  unfold total
  rw [average_affine_product ((hb i).add (hm i)) ((hb j).add (hm j))
    (ho i) (ho j) q (hz i q) (hz j q)]
  unfold fluxDifference covariance
  ring

theorem fluxDifference_diagonal (base mean osc : Components) (i : Fin 3) (q : SpaceTime) :
    fluxDifference base mean osc i i q =
      2 * base i q * mean i q + (mean i q) ^ 2 + covariance osc i i q := by
  unfold fluxDifference
  ring

theorem direction_twice_add {f g : SpaceTime → E} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (v w q : SpaceTime) :
    direction v (direction w (fun y => f y + g y)) q =
      direction v (direction w f) q + direction v (direction w g) q := by
  rw [show direction w (fun y => f y + g y) =
      (fun y => direction w f y + direction w g y) from funext (direction_add hf hg w)]
  exact direction_add (direction_smooth _ hf) (direction_smooth _ hg) v q

theorem meanLaplacian_add {f g : Scalar} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (q : SpaceTime) : meanLaplacian (fun y => f y + g y) q =
      meanLaplacian f q + meanLaplacian g q := by
  simp only [meanLaplacian, dr, dz, direction_twice_add hf hg, direction_add hf hg]
  ring

theorem radialDivergence_add {f g : Scalar} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (c : ℝ) (q : SpaceTime) : radialDivergence c (fun y => f y + g y) q =
      radialDivergence c f q + radialDivergence c g q := by
  simp only [radialDivergence, dr, direction_add hf hg]
  ring

noncomputable def baseRadial (b : Components) (p : Scalar) (q : SpaceTime) : ℝ :=
  dt (b 0) q + radialDivergence 1 (fun y => b 0 y * b 0 y) q +
    dz (fun y => b 2 y * b 0 y) q - b 1 q * b 1 q / radius q -
    meanLaplacian (b 0) q + b 0 q / radius q ^ 2 + dr p q

noncomputable def baseAngular (b : Components) (q : SpaceTime) : ℝ :=
  dt (b 1) q + radialDivergence 2 (fun y => b 0 y * b 1 y) q +
    dz (fun y => b 2 y * b 1 y) q - meanLaplacian (b 1) q + b 1 q / radius q ^ 2

noncomputable def baseAxial (b : Components) (p : Scalar) (q : SpaceTime) : ℝ :=
  dt (b 2) q + radialDivergence 1 (fun y => b 0 y * b 2 y) q +
    dz (fun y => b 2 y * b 2 y) q - meanLaplacian (b 2) q + dz p q

/-- Physical version of `E_theta` in (32), with viscosity one. -/
noncomputable def Etheta (b m o : Components) (Ttheta : Scalar) (q : SpaceTime) : ℝ :=
  dt (m 1) q + radialDivergence 2 (fluxDifference b m o 0 1) q +
    dz (fluxDifference b m o 2 1) q - meanLaplacian (m 1) q + m 1 q / radius q ^ 2 -
    radialDivergence 2 Ttheta q

/-- Physical version of `E_z` in (32), with viscosity one. -/
noncomputable def Ez (b m o : Components) (pm Tz : Scalar) (q : SpaceTime) : ℝ :=
  dt (m 2) q + radialDivergence 1 (fluxDifference b m o 0 2) q +
    dz (fun y => fluxDifference b m o 2 2 y + pm y) q - meanLaplacian (m 2) q -
    radialDivergence 1 Tz q

/-- Required physical radial pressure derivative in (32). -/
noncomputable def gr (b m o : Components) (q : SpaceTime) : ℝ :=
  -(dt (m 0) q + radialDivergence 1 (fluxDifference b m o 0 0) q +
    dz (fluxDifference b m o 2 0) q - fluxDifference b m o 1 1 q / radius q -
    meanLaplacian (m 0) q + m 0 q / radius q ^ 2)

theorem reynoldsAngular_total_sub {b m o : Components}
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) (hm : ∀ i, ContDiff ℝ ∞ (m i))
    (ho : ∀ i, ContDiff ℝ ∞ (o i))
    (hbi : ∀ i, AngularInvariant (b i)) (hmi : ∀ i, AngularInvariant (m i))
    (hz : ∀ i q, average (o i) q = 0) (Ttheta : Scalar) (q : SpaceTime) :
    reynoldsAngular (total b m o) q - baseAngular b q - radialDivergence 2 Ttheta q =
      Etheta b m o Ttheta q := by
  have hoc i := angularContinuous_of_continuous (ho i).continuous
  have hflux := fluxDifference_smooth hb hm ho
  unfold reynoldsAngular baseAngular Etheta
  rw [average_total hbi hmi hoc hz 1, average_total_product hbi hmi hoc hz 0 1,
    average_total_product hbi hmi hoc hz 2 1,
    radialDivergence_add ((hb 0).mul (hb 1)) (hflux 0 1), meanLaplacian_add (hb 1) (hm 1)]
  simp only [dt, dz, direction_add (hb 1) (hm 1), direction_add ((hb 2).mul (hb 1)) (hflux 2 1)]
  ring

theorem reynoldsRadial_total_sub {b m o : Components} {p pb pm : Scalar}
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) (hm : ∀ i, ContDiff ℝ ∞ (m i))
    (ho : ∀ i, ContDiff ℝ ∞ (o i)) (hpb : ContDiff ℝ ∞ pb) (hpm : ContDiff ℝ ∞ pm)
    (hbi : ∀ i, AngularInvariant (b i)) (hmi : ∀ i, AngularInvariant (m i))
    (hz : ∀ i q, average (o i) q = 0)
    (hpavg : average p = fun q => pb q + pm q) (q : SpaceTime) :
    reynoldsRadial (total b m o) p q - baseRadial b pb q = dr pm q - gr b m o q := by
  have hoc i := angularContinuous_of_continuous (ho i).continuous
  have hflux := fluxDifference_smooth hb hm ho
  unfold reynoldsRadial baseRadial gr
  rw [average_total hbi hmi hoc hz 0, average_total_product hbi hmi hoc hz 0 0,
    average_total_product hbi hmi hoc hz 2 0, average_total_product hbi hmi hoc hz 1 1,
    hpavg, radialDivergence_add ((hb 0).mul (hb 0)) (hflux 0 0),
    meanLaplacian_add (hb 0) (hm 0)]
  simp only [dt, dr, dz, direction_add (hb 0) (hm 0), direction_add ((hb 2).mul (hb 0)) (hflux 2 0),
    direction_add hpb hpm]
  ring

theorem reynoldsAxial_total_sub {b m o : Components} {p pb pm : Scalar}
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) (hm : ∀ i, ContDiff ℝ ∞ (m i))
    (ho : ∀ i, ContDiff ℝ ∞ (o i)) (hpb : ContDiff ℝ ∞ pb) (hpm : ContDiff ℝ ∞ pm)
    (hbi : ∀ i, AngularInvariant (b i)) (hmi : ∀ i, AngularInvariant (m i))
    (hz : ∀ i q, average (o i) q = 0)
    (hpavg : average p = fun q => pb q + pm q) (Tz : Scalar) (q : SpaceTime) :
    reynoldsAxial (total b m o) p q - baseAxial b pb q - radialDivergence 1 Tz q =
      Ez b m o pm Tz q := by
  have hoc i := angularContinuous_of_continuous (ho i).continuous
  have hflux := fluxDifference_smooth hb hm ho
  unfold reynoldsAxial baseAxial Ez
  rw [average_total hbi hmi hoc hz 2, average_total_product hbi hmi hoc hz 0 2,
    average_total_product hbi hmi hoc hz 2 2, hpavg,
    radialDivergence_add ((hb 0).mul (hb 2)) (hflux 0 2), meanLaplacian_add (hb 2) (hm 2)]
  simp only [dt, dz, direction_add (hb 2) (hm 2), direction_add ((hb 2).mul (hb 2)) (hflux 2 2),
    direction_add hpb hpm, direction_add (hflux 2 2) hpm]
  ring

theorem reynoldsAngular_invariant {b : Components} (hbi : ∀ i, AngularInvariant (b i))
    (q : SpaceTime) : reynoldsAngular b q = baseAngular b q := by
  have h1 i : average (b i) = b i := funext (average_invariant (hbi i))
  have h2 i j : average (fun y => b i y * b j y) = (fun y => b i y * b j y) :=
    funext (average_invariant ((hbi i).mul (hbi j)))
  simp only [reynoldsAngular, h1, h2, baseAngular]

theorem reynoldsRadial_invariant {b : Components} {p : Scalar}
    (hbi : ∀ i, AngularInvariant (b i)) (hpi : AngularInvariant p)
    (q : SpaceTime) : reynoldsRadial b p q = baseRadial b p q := by
  have h1 i : average (b i) = b i := funext (average_invariant (hbi i))
  have h2 i j : average (fun y => b i y * b j y) = (fun y => b i y * b j y) :=
    funext (average_invariant ((hbi i).mul (hbi j)))
  have h3 : average p = p := funext (average_invariant hpi)
  simp only [reynoldsRadial, h1, h2, h3, baseRadial]

theorem reynoldsAxial_invariant {b : Components} {p : Scalar}
    (hbi : ∀ i, AngularInvariant (b i)) (hpi : AngularInvariant p)
    (q : SpaceTime) : reynoldsAxial b p q = baseAxial b p q := by
  have h1 i : average (b i) = b i := funext (average_invariant (hbi i))
  have h2 i j : average (fun y => b i y * b j y) = (fun y => b i y * b j y) :=
    funext (average_invariant ((hbi i).mul (hbi j)))
  have h3 : average p = p := funext (average_invariant hpi)
  simp only [reynoldsAxial, h1, h2, h3, baseAxial]

theorem residuals_invariant {b : Components} {p : Scalar}
    (hbi : ∀ i, AngularInvariant (b i)) (hpi : AngularInvariant p) :
    AngularInvariant (residualRadial b p) ∧ AngularInvariant (residualAngular b p) ∧
      AngularInvariant (residualAxial b p) := by
  have h0 : ∀ i q a, b i (angularShift q a) = b i q := fun i => hbi i
  have h1 : ∀ i v q a, direction v (b i) (angularShift q a) = direction v (b i) q :=
    fun i v => (hbi i).direction v
  have h2 : ∀ i v w q a, direction v (direction w (b i)) (angularShift q a) =
      direction v (direction w (b i)) q := fun i v w => ((hbi i).direction w).direction v
  have h3 : ∀ v q a, direction v p (angularShift q a) = direction v p q :=
    fun v => hpi.direction v
  refine ⟨?_, ?_, ?_⟩
  all_goals
    intro q a
    simp only [residualRadial, residualAngular, residualAxial, transport, laplacian,
      dt, dr, dtheta, dz, radius_angularShift, h0, h1, h2, h3]

theorem base_residuals {b : Components} {p : Scalar}
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) (hp : ContDiff ℝ ∞ p)
    (hbi : ∀ i, AngularInvariant (b i)) (hpi : AngularInvariant p)
    (hdiv : ∀ y, 0 < radius y → divergence b y = 0)
    (q : SpaceTime) (hr : 0 < radius q) :
    residualRadial b p q = baseRadial b p q ∧
      residualAngular b p q = baseAngular b q ∧ residualAxial b p q = baseAxial b p q := by
  have hper : ∀ i, AngularPeriodic (b i) := fun i y => hbi i y period
  have hip := residuals_invariant hbi hpi
  have hR := average_residualRadial hb hp hper hdiv q hr
  have hA := average_residualAngular hb hp hper (fun y => hpi y period) hdiv q hr
  have hZ := average_residualAxial hb hp hper hdiv q hr
  rw [average_invariant hip.1, reynoldsRadial_invariant hbi hpi] at hR
  rw [average_invariant hip.2.1, reynoldsAngular_invariant hbi] at hA
  rw [average_invariant hip.2.2, reynoldsAxial_invariant hbi hpi] at hZ
  exact ⟨hR, hA, hZ⟩

/-- Exact physical mean balances (32) for the actual cylindrical residual.
The tensor entries are the prescribed physical radial flux entries; `covariance`
is the integral of the entire oscillatory field, including any curl corrections. -/
theorem exact_mean_balances {b m o : Components} {p pb pm : Scalar}
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) (hm : ∀ i, ContDiff ℝ ∞ (m i))
    (ho : ∀ i, ContDiff ℝ ∞ (o i)) (hp : ContDiff ℝ ∞ p)
    (hpb : ContDiff ℝ ∞ pb) (hpm : ContDiff ℝ ∞ pm)
    (hbi : ∀ i, AngularInvariant (b i)) (hmi : ∀ i, AngularInvariant (m i))
    (hop : ∀ i, AngularPeriodic (o i)) (hpp : AngularPeriodic p) (hpbi : AngularInvariant pb)
    (hz : ∀ i q, average (o i) q = 0) (hpavg : average p = fun q => pb q + pm q)
    (hdiv : ∀ y, 0 < radius y → divergence (total b m o) y = 0)
    (hbdiv : ∀ y, 0 < radius y → divergence b y = 0)
    (Ttheta Tz : Scalar) (q : SpaceTime) (hr : 0 < radius q) :
    (average (fun y => CylindricalResidual.cylindricalResidual
      (velocity (total b m o)) p y.1 y.2 1) q -
      CylindricalResidual.cylindricalResidual (velocity b) pb q.1 q.2 1 -
      radialDivergence 2 Ttheta q = Etheta b m o Ttheta q) ∧
    (average (fun y => CylindricalResidual.cylindricalResidual
      (velocity (total b m o)) p y.1 y.2 2) q -
      CylindricalResidual.cylindricalResidual (velocity b) pb q.1 q.2 2 -
      radialDivergence 1 Tz q = Ez b m o pm Tz q) ∧
    (average (fun y => CylindricalResidual.cylindricalResidual
      (velocity (total b m o)) p y.1 y.2 0) q -
      CylindricalResidual.cylindricalResidual (velocity b) pb q.1 q.2 0 = dr pm q - gr b m o q) :=
        by
  have ht := total_smooth hb hm ho
  have htp := total_periodic hbi hmi hop
  have hbase := base_residuals hb hpb hbi hpbi hbdiv q hr
  have heA : (fun y => CylindricalResidual.cylindricalResidual
      (velocity (total b m o)) p y.1 y.2 1) = residualAngular (total b m o) p :=
    funext (cylindricalResidual_angular ht hp)
  have heZ : (fun y => CylindricalResidual.cylindricalResidual
      (velocity (total b m o)) p y.1 y.2 2) = residualAxial (total b m o) p :=
    funext (cylindricalResidual_axial ht hp)
  have heR : (fun y => CylindricalResidual.cylindricalResidual
      (velocity (total b m o)) p y.1 y.2 0) = residualRadial (total b m o) p :=
    funext (cylindricalResidual_radial ht hp)
  rw [heA, heZ, heR, cylindricalResidual_angular hb hpb, cylindricalResidual_axial hb hpb,
    cylindricalResidual_radial hb hpb, hbase.1, hbase.2.1, hbase.2.2,
    average_residualAngular ht hp htp hpp hdiv q hr,
    average_residualAxial ht hp htp hdiv q hr, average_residualRadial ht hp htp hdiv q hr]
  exact ⟨reynoldsAngular_total_sub hb hm ho hbi hmi hz Ttheta q,
    reynoldsAxial_total_sub hb hm ho hpb hpm hbi hmi hz hpavg Tz q,
    reynoldsRadial_total_sub hb hm ho hpb hpm hbi hmi hz hpavg q⟩

theorem Etheta_expanded (b m o : Components) (T : Scalar) (q : SpaceTime) :
    Etheta b m o T q = dt (m 1) q +
      radialDivergence 2 (fun y => b 0 y * m 1 y + m 0 y * b 1 y +
        m 0 y * m 1 y + covariance o 0 1 y) q +
      dz (fun y => b 2 y * m 1 y + b 1 y * m 2 y + m 2 y * m 1 y + covariance o 2 1 y) q -
      (meanLaplacian (m 1) q - m 1 q / radius q ^ 2) - radialDivergence 2 T q := by
  have he : fluxDifference b m o 2 1 =
      (fun y => b 2 y * m 1 y + b 1 y * m 2 y + m 2 y * m 1 y + covariance o 2 1 y) := by
    funext y
    unfold fluxDifference
    ring
  have he01 : fluxDifference b m o 0 1 =
      (fun y => b 0 y * m 1 y + m 0 y * b 1 y + m 0 y * m 1 y + covariance o 0 1 y) := rfl
  unfold Etheta
  rw [he, he01]
  ring

theorem Ez_expanded (b m o : Components) (pm T : Scalar) (q : SpaceTime) :
    Ez b m o pm T q = dt (m 2) q +
      radialDivergence 1 (fun y => b 0 y * m 2 y + m 0 y * b 2 y +
        m 0 y * m 2 y + covariance o 0 2 y) q +
      dz (fun y => 2 * b 2 y * m 2 y + (m 2 y) ^ 2 + covariance o 2 2 y + pm y) q -
      meanLaplacian (m 2) q - radialDivergence 1 T q := by
  simp only [Ez, fluxDifference_diagonal]
  rfl

theorem gr_expanded (b m o : Components) (q : SpaceTime) :
    gr b m o q = -(dt (m 0) q +
      radialDivergence 1 (fun y => 2 * b 0 y * m 0 y + (m 0 y) ^ 2 + covariance o 0 0 y) q +
      dz (fun y => b 0 y * m 2 y + b 2 y * m 0 y + m 0 y * m 2 y + covariance o 2 0 y) q -
      (2 * b 1 q * m 1 q + (m 1 q) ^ 2 + covariance o 1 1 q) / radius q -
      (meanLaplacian (m 0) q - m 0 q / radius q ^ 2)) := by
  have he0 : fluxDifference b m o 0 0 =
      (fun y => 2 * b 0 y * m 0 y + (m 0 y) ^ 2 + covariance o 0 0 y) :=
    funext (fluxDifference_diagonal b m o 0)
  have he2 : fluxDifference b m o 2 0 =
      (fun y => b 0 y * m 2 y + b 2 y * m 0 y + m 0 y * m 2 y + covariance o 2 0 y) := by
    funext y
    unfold fluxDifference
    ring
  unfold gr
  rw [he0, he2, fluxDifference_diagonal]
  ring

/-- The perturbation pressure is defined from its actual angular mean. -/
noncomputable def meanPressure (p pb : Scalar) : Scalar := fun q => average p q - pb q

theorem meanPressure_smooth {p pb : Scalar} (hp : ContDiff ℝ ∞ p) (hpb : ContDiff ℝ ∞ pb) :
    ContDiff ℝ ∞ (meanPressure p pb) := (average_smooth hp).sub hpb

theorem meanPressure_reconstruction (p pb : Scalar) :
    average p = fun q => pb q + meanPressure p pb q := by
  funext q
  unfold meanPressure
  ring

theorem cylindricalDivergence_eq {w : Components} (hw : ∀ i, ContDiff ℝ ∞ (w i))
    (q : SpaceTime) :
    CylindricalResidual.vectorDivergence (fun y => velocity w (q.1, y)) q.2 = divergence w q := by
  simp only [CylindricalResidual.vectorDivergence, spatial_direction (velocity_smooth hw),
    direction_velocity_component hw, velocity_apply, divergence, dr, dtheta, dz, angularVector,
      radius]

def Represents (u : VelocityField) (w : Components) : Prop :=
  ∀ q : SpaceTime, u (q.1, CylindricalResidual.chart q.2) =
    CylindricalResidual.frame (q.2 1) (velocity w q)

theorem Represents.components {u : VelocityField} {w : Components} (h : Represents u w) :
    CylindricalResidual.velocityComponents u = velocity w := by
  funext q
  change CylindricalResidual.frame (-(q.2 1)) (u (q.1, CylindricalResidual.chart q.2)) = velocity w
    q
  rw [h q, CylindricalResidual.frame_inverse]

/-- Exact physical Cartesian residual resolved in the cylindrical frame. -/
noncomputable def cartesianResidual (u : VelocityField) (p : PressureField)
    (i : Fin 3) (q : SpaceTime) : ℝ :=
  (CylindricalResidual.frame (-(q.2 1))
    (navierStokesResidual u p q.1 (CylindricalResidual.chart q.2))) i

theorem cartesianResidual_eq {u : VelocityField} {p : PressureField}
    {w : Components} {P : Scalar} (hrep : Represents u w)
    (hpull : CylindricalResidual.pressurePullback p = P)
    (q : SpaceTime) (hr : 0 < radius q)
    (hu : ContDiffAt ℝ 2 u (q.1, CylindricalResidual.chart q.2))
    (hp : DifferentiableAt ℝ p (q.1, CylindricalResidual.chart q.2)) (i : Fin 3) :
    cartesianResidual u p i q =
      CylindricalResidual.cylindricalResidual (velocity w) P q.1 q.2 i := by
  unfold cartesianResidual
  rw [CylindricalResidual.navierStokesResidual_cylindrical hu hp hr,
    hrep.components, hpull, CylindricalResidual.frame_inverse]

theorem cartesianDivergence_eq {u : VelocityField} {w : Components}
    (hw : ∀ i, ContDiff ℝ ∞ (w i)) (hrep : Represents u w)
    (q : SpaceTime) (hr : 0 < radius q)
    (hu : ContDiffAt ℝ 2 u (q.1, CylindricalResidual.chart q.2)) :
    spatialDivergence u q.1 (CylindricalResidual.chart q.2) = divergence w q := by
  have hs : DifferentiableAt ℝ (fun x => u (q.1, x)) (CylindricalResidual.chart q.2) :=
    (hu.differentiableAt (by norm_num)).comp _
      ((differentiableAt_const _).prodMk differentiableAt_id)
  rw [CylindricalResidual.divergence_cylindrical hs hr, hrep.components, cylindricalDivergence_eq
    hw]

theorem average_cartesianResidual_eq {u : VelocityField} {p : PressureField}
    {w : Components} {P : Scalar} (hrep : Represents u w)
    (hpull : CylindricalResidual.pressurePullback p = P)
    (hu : ∀ y, 0 < radius y → ContDiffAt ℝ 2 u (y.1, CylindricalResidual.chart y.2))
    (hp : ∀ y, 0 < radius y → DifferentiableAt ℝ p (y.1, CylindricalResidual.chart y.2))
    (q : SpaceTime) (hr : 0 < radius q) (i : Fin 3) :
    average (cartesianResidual u p i) q =
      average (fun y => CylindricalResidual.cylindricalResidual (velocity w) P y.1 y.2 i) q := by
  apply average_congr
  intro a _
  have hra : 0 < radius (angularShift q a) := by simpa only [radius_angularShift] using hr
  exact cartesianResidual_eq hrep hpull _ hra (hu _ hra) (hp _ hra) i

/-- End-to-end mean balances for the actual Cartesian operators. Cartesian
regularity is required only at positive-radius chart points. -/
theorem exact_cartesian_mean_balances
    {u ub : VelocityField} {P Pb : PressureField} {b m o : Components} {p pb pm : Scalar}
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) (hm : ∀ i, ContDiff ℝ ∞ (m i))
    (ho : ∀ i, ContDiff ℝ ∞ (o i)) (hp : ContDiff ℝ ∞ p)
    (hpb : ContDiff ℝ ∞ pb) (hpm : ContDiff ℝ ∞ pm)
    (hbi : ∀ i, AngularInvariant (b i)) (hmi : ∀ i, AngularInvariant (m i))
    (hop : ∀ i, AngularPeriodic (o i)) (hpp : AngularPeriodic p) (hpbi : AngularInvariant pb)
    (hz : ∀ i q, average (o i) q = 0) (hpavg : average p = fun q => pb q + pm q)
    (hrep : Represents u (total b m o)) (hbrep : Represents ub b)
    (hpull : CylindricalResidual.pressurePullback P = p)
    (hbpull : CylindricalResidual.pressurePullback Pb = pb)
    (hu : ∀ y, 0 < radius y → ContDiffAt ℝ 2 u (y.1, CylindricalResidual.chart y.2))
    (hub : ∀ y, 0 < radius y → ContDiffAt ℝ 2 ub (y.1, CylindricalResidual.chart y.2))
    (hP : ∀ y, 0 < radius y → DifferentiableAt ℝ P (y.1, CylindricalResidual.chart y.2))
    (hPb : ∀ y, 0 < radius y → DifferentiableAt ℝ Pb (y.1, CylindricalResidual.chart y.2))
    (hdiv : ∀ y, 0 < radius y → spatialDivergence u y.1 (CylindricalResidual.chart y.2) = 0)
    (hbdiv : ∀ y, 0 < radius y → spatialDivergence ub y.1 (CylindricalResidual.chart y.2) = 0)
    (Ttheta Tz : Scalar) (q : SpaceTime) (hr : 0 < radius q) :
    (average (cartesianResidual u P 1) q - cartesianResidual ub Pb 1 q -
      radialDivergence 2 Ttheta q = Etheta b m o Ttheta q) ∧
    (average (cartesianResidual u P 2) q - cartesianResidual ub Pb 2 q -
      radialDivergence 1 Tz q = Ez b m o pm Tz q) ∧
    (average (cartesianResidual u P 0) q - cartesianResidual ub Pb 0 q = dr pm q - gr b m o q) := by
  have hdc : ∀ y, 0 < radius y → divergence (total b m o) y = 0 := by
    intro y hy
    rw [← cartesianDivergence_eq (total_smooth hb hm ho) hrep y hy (hu y hy)]
    exact hdiv y hy
  have hdbc : ∀ y, 0 < radius y → divergence b y = 0 := by
    intro y hy
    rw [← cartesianDivergence_eq hb hbrep y hy (hub y hy)]
    exact hbdiv y hy
  have h := exact_mean_balances hb hm ho hp hpb hpm hbi hmi hop hpp hpbi hz hpavg
    hdc hdbc Ttheta Tz q hr
  rw [average_cartesianResidual_eq hrep hpull hu hP q hr 1,
    average_cartesianResidual_eq hrep hpull hu hP q hr 2,
    average_cartesianResidual_eq hrep hpull hu hP q hr 0,
    cartesianResidual_eq hbrep hbpull q hr (hub q hr) (hPb q hr) 1,
    cartesianResidual_eq hbrep hbpull q hr (hub q hr) (hPb q hr) 2,
    cartesianResidual_eq hbrep hbpull q hr (hub q hr) (hPb q hr) 0]
  exact h

theorem average_invariant_of_periodic [CompleteSpace E] {f : SpaceTime → E}
    (hf : ContDiff ℝ ∞ f) (hp : AngularPeriodic f) : AngularInvariant (average f) := by
  intro q a
  have hd : ∀ b : ℝ, HasDerivAt (fun c => average f (angularShift q c)) 0 b := by
    intro b
    have hs : HasDerivAt (fun c : ℝ => angularShift q c) angularVector b := by
      simpa [angularShift] using ((hasDerivAt_id b).smul_const angularVector).const_add q
    have hder : HasDerivAt (fun c => average f (angularShift q c))
        (dtheta (average f) (angularShift q b)) b :=
      (((average_smooth hf).differentiable (by simp)) (angularShift q
        b)).hasFDerivAt.comp_hasDerivAt b hs
    have hz : dtheta (average f) (angularShift q b) = 0 := by
      rw [show dtheta (average f) (angularShift q b) = average (dtheta f) (angularShift q b) from
        direction_average hf angularVector (angularShift q b), average_dtheta_zero hf hp]
    rwa [hz] at hder
  simpa only [angularShift_zero] using
    is_const_of_deriv_eq_zero (fun b => (hd b).differentiableAt) (fun b => (hd b).deriv) a 0

theorem covariance_invariant {o : Components} (ho : ∀ i, ContDiff ℝ ∞ (o i))
    (hop : ∀ i, AngularPeriodic (o i)) (i j : Fin 3) : AngularInvariant (covariance o i j) :=
  average_invariant_of_periodic ((ho i).mul (ho j)) ((hop i).mul (hop j))

/-- Substitution of (24) retains, rather than discards, its full base error. -/
theorem retain_base_error {Rtheta Rz Rr Btheta Bz Br Ttheta Tz Etheta Ez Drp gr
    ftheta fz fr : ℝ}
    (hθ : Rtheta - Btheta - Ttheta = Etheta)
    (hz : Rz - Bz - Tz = Ez) (hr : Rr - Br = Drp - gr)
    (hbθ : Btheta = -Ttheta + ftheta) (hbz : Bz = -Tz + fz) (hbr : Br = fr) :
    Rtheta = Etheta + ftheta ∧ Rz = Ez + fz ∧ Rr = Drp - gr + fr := by
  constructor
  · linarith
  constructor <;> linarith

end

end NavierStokes.MeanResidual
