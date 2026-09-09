/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.BaseResidual
public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalHeatCoordinates
public import LeanPool.NavierStokesAndEuler.NavierStokes.TerminalPressure
public import LeanPool.NavierStokesAndEuler.NavierStokes.HeatProfileExtension
public import LeanPool.NavierStokesAndEuler.NavierStokes.AssembledSlowBase

@[expose] public section

/-!
# The actual pure-heat exterior of the summed slow base

The exterior comparison is with the physical radial heat solution and its
canonical improper-integral pressure. All stream cutoffs are retained until
their coefficients are shown to vanish in an exterior neighborhood.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators

namespace NavierStokes.BaseExterior

open SimilarityProfile ProblemStatement SlowBorelBase

private theorem nat_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n).le

section PureHeat

/-- The regular Cartesian swirl coefficient of the physical heat solution. -/
noncomputable def heatCoefficient (C h : ℝ) : PhysicalProfile :=
  TerminalStress.swirlCoefficient C h (fun _ => 1)

/-- The pressure is the literal canonical radial integral. -/
noncomputable def heatPressure (C h : ℝ) : PhysicalProfile :=
  TerminalStress.canonicalPressure (heatCoefficient C h)

noncomputable def heatVelocity (C h : ℝ) : VelocityField :=
  AxisymmetricResidual.velocity (fun _ => 0) (heatCoefficient C h) (fun _ => 0)

noncomputable def heatPressureField (C h : ℝ) : PressureField :=
  AxisymmetricResidual.pressure (heatPressure C h)

theorem heatCoefficient_eq (C h : ℝ) (p : PhysicalPoint) :
    heatCoefficient C h p = TerminalStress.physicalHeat C (1 + h) p / Real.sqrt (2 * p.2.1) := by
  simp [heatCoefficient, TerminalStress.swirlCoefficient, TerminalStress.flattening]

theorem heatCoefficient_z_invariant (C h t s z z' : ℝ) :
    heatCoefficient C h (t, (s, z)) = heatCoefficient C h (t, (s, z')) := rfl

theorem heatPressure_z_invariant (C h t s z z' : ℝ) :
    heatPressure C h (t, (s, z)) = heatPressure C h (t, (s, z')) := rfl

theorem heatCoefficient_smoothAt (C : ℝ) {h : ℝ} (hh : 0 < h)
    {p : PhysicalPoint} (ht : p.1 < 1) (hs : 0 < p.2.1) :
    ContDiffAt ℝ ∞ (heatCoefficient C h) p := by
  have he : heatCoefficient C h = fun p =>
      TerminalStress.physicalHeat C (1 + h) p / Real.sqrt (2 * p.2.1) :=
    funext (heatCoefficient_eq C h)
  rw [he]
  exact (TerminalStress.physicalHeat_contDiffAt C (by linarith) ht hs).div
    ((contDiffAt_const.mul contDiffAt_snd.fst).sqrt (by positivity))
    (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))

theorem heatPressure_smoothAt (C : ℝ) {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : PhysicalPoint} (ht : p.1 < 1) (hs : 0 < p.2.1) :
    ContDiffAt ℝ ∞ (heatPressure C h) p :=
  TerminalPressure.canonicalPressure_contDiffAt (Y := 0) C hh hh1 ht hs contDiff_const
    (fun _ => by norm_num) (fun _ _ => rfl)

theorem partialZ_of_invariant {f : PhysicalProfile} {p : PhysicalPoint}
    (hf : DifferentiableAt ℝ f p)
    (he : ∀ z : ℝ, f (p.1, (p.2.1, z)) = f p) : partialZ f p = 0 := by
  have hd := hf.hasFDerivAt.comp_hasDerivAt p.2.2
    ((hasDerivAt_const p.2.2 p.1).prodMk
      ((hasDerivAt_const p.2.2 p.2.1).prodMk (hasDerivAt_id p.2.2)))
  have hz : HasDerivAt (fun z => f (p.1, (p.2.1, z))) 0 p.2.2 := by
    simpa only [he] using hasDerivAt_const p.2.2 (f p)
  exact hd.unique hz

theorem heatCoefficient_partialZ (C : ℝ) {h : ℝ} (hh : 0 < h)
    {p : PhysicalPoint} (ht : p.1 < 1) (hs : 0 < p.2.1) :
    partialZ (heatCoefficient C h) p = 0 :=
  partialZ_of_invariant ((heatCoefficient_smoothAt C hh ht hs).differentiableAt (by simp))
    (fun z => heatCoefficient_z_invariant C h _ _ z _)

theorem heatCoefficient_partialZZ (C : ℝ) {h : ℝ} (hh : 0 < h)
    {p : PhysicalPoint} (ht : p.1 < 1) (hs : 0 < p.2.1) :
    partialZ (partialZ (heatCoefficient C h)) p = 0 := by
  have he : partialZ (heatCoefficient C h) =ᶠ[𝓝 p] (fun _ => 0) := by
    filter_upwards [continuousAt_fst.eventually (Iio_mem_nhds ht),
      continuousAt_snd.fst.eventually (Ioi_mem_nhds hs)] with y hyt hys
    exact heatCoefficient_partialZ C hh hyt hys
  simp [partialZ, he.fderiv_eq]

theorem heatPressure_partialZ (C : ℝ) {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : PhysicalPoint} (ht : p.1 < 1) (hs : 0 < p.2.1) :
    partialZ (heatPressure C h) p = 0 :=
  partialZ_of_invariant ((heatPressure_smoothAt C hh hh1 ht hs).differentiableAt (by simp))
    (fun z => heatPressure_z_invariant C h _ _ z _)

theorem heatCoefficient_sq_integrable (C : ℝ) {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {t a z : ℝ} (ht : t < 1) (ha : 0 < a) :
    IntegrableOn (fun s => heatCoefficient C h (t, (s, z)) ^ 2) (Ioi a) :=
  TerminalPressure.swirlCoefficient_sq_integrable (p := (t, (a, z))) C hh hh1 ht ha
    continuous_const (fun _ => by norm_num)

theorem heatCoefficient_sq_continuous (C : ℝ) {h : ℝ} (hh : 0 < h)
    {t a z : ℝ} (ht : t < 1) (ha : 0 < a) :
    ContinuousOn (fun s => heatCoefficient C h (t, (s, z)) ^ 2) (Ioi a) := by
  intro s hs
  exact (((heatCoefficient_smoothAt C hh (p := (t, (s, z))) ht (ha.trans hs)).comp s
    (contDiffAt_const.prodMk (contDiffAt_id.prodMk contDiffAt_const))).pow
      2).continuousAt.continuousWithinAt

theorem heatPressure_partialS (C : ℝ) {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : PhysicalPoint} (ht : p.1 < 1) (hs : 0 < p.2.1) :
    partialS (heatPressure C h) p = heatCoefficient C h p ^ 2 :=
  TerminalStress.canonicalPressure_partialS (a := p.2.1 / 2) (by linarith)
    (heatCoefficient_sq_integrable C hh hh1 ht (by positivity))
    (heatCoefficient_sq_continuous C hh ht (by positivity))
    ((heatPressure_smoothAt C hh hh1 ht hs).differentiableAt (by simp))

theorem heatCoefficient_residual_zero (C : ℝ) {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : PhysicalPoint} (ht : p.1 < 1) (hs : 0 < p.2.1) :
    TerminalStress.residualCoefficient (heatCoefficient C h) p = 0 := by
  let r := Real.sqrt (2 * p.2.1)
  have hr : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have he : TerminalStress.radiusPoint p.1 r p.2.2 = p := by
    have hr2 : r ^ 2 = 2 * p.2.1 := Real.sq_sqrt (by positivity)
    simp only [TerminalStress.radiusPoint, hr2]
    congr 1
    ext <;> simp
  have hd := TerminalStress.swirlCoefficient_leading_residual C (z := p.2.2) hh hh1 ht hr
    (f := fun _ => 1) contDiffAt_const
  rw [he] at hd
  have hzero : TerminalStress.leadingResidual C h (fun _ => 1) p.1 r p.2.2 = 0 := by
    have hc : TerminalStress.radialSlice (TerminalStress.flattening h (fun _ => 1)) p.1 p.2.2 =
        (fun _ => 1) := rfl
    simp [TerminalStress.leadingResidual, TerminalStress.viscousResidual,
      hc]
  rw [hzero] at hd
  have hmain := (mul_eq_zero.mp hd).resolve_left hr.ne'
  unfold TerminalStress.residualCoefficient
  rw [heatCoefficient_partialZZ C hh ht hs, sub_zero]
  exact hmain

/-- The physical heat exterior solves the unforced Cartesian equations
exactly. Both the heat equation and canonical pressure balance are proved. -/
theorem heat_navierStokesResidual_zero (C : ℝ) {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {t : ℝ} {x : Space} (ht : t < 1) (hs : 0 < AxisymmetricFields.radialEnergy x) :
    navierStokesResidual (heatVelocity C h) (heatPressureField C h) t x = 0 := by
  unfold heatVelocity heatPressureField
  rw [TerminalStress.pureSwirl_navierStokesResidual
    ((heatCoefficient_smoothAt C hh ht hs).of_le (nat_le_infty 2))
    ((heatPressure_smoothAt C hh hh1 ht hs).differentiableAt (by simp)),
    heatPressure_partialS C hh hh1 ht hs, heatPressure_partialZ C hh hh1 ht hs,
    heatCoefficient_residual_zero C hh hh1 ht hs]
  simp [AxisymmetricResidual.pack]

end PureHeat

section ExteriorSummation

/-- Original scalar coefficient and mass identities. These say nothing
about the summed velocity or its residual. -/
structure ExteriorCoefficients (d : Coefficients) (R : ℝ) : Prop where
  axial : ∀ n : ℕ, ∀ w : Inner, R < w.1 → w.2 ∈ Icc (-1) 1 → d.axial n w = 0
  mass : ∀ n : ℕ, ∀ w : Inner, R < w.1 → w.2 ∈ Icc (-1) 1 →
    ProfileHistories.primitive (d.axial n) w = 0
  phi : ∀ n : ℕ, 0 < n → ∀ w : Inner, R < w.1 → w.2 ∈ Icc (-1) 1 → d.phi n w = 0
  pressure : ∀ n : ℕ, 0 < n → ∀ w : Inner, R < w.1 → w.2 ∈ Icc (-1) 1 → d.pressure n w = 0

theorem ExteriorCoefficients.average {d : Coefficients} {R : ℝ}
    (hd : ExteriorCoefficients d R) (hR : 0 ≤ R) (n : ℕ) {w : Inner}
    (hw : R < w.1) (he : w.2 ∈ Icc (-1) 1) : ProfileHistories.average (d.axial n) w = 0 := by
  have hm := hd.mass n w hw he
  rw [ProfileHistories.primitive_eq_mul_average] at hm
  exact (mul_eq_zero.mp hm).resolve_left (ne_of_gt (hR.trans_lt hw))

theorem physical_eta_mem {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : PhysicalPoint} (ht : p.1 < 1) : (physicalChart h p).2.2 ∈ Icc (-1) 1 :=
  (physicalChart_inner_mem (lo := (physicalChart h p).2.1) (hi := (physicalChart h p).2.1)
    hh hh1 ht ⟨le_rfl, le_rfl⟩).2

noncomputable def exteriorDomain (h R : ℝ) : Set PhysicalPoint :=
  {p | p.1 < 1 ∧ R < (physicalChart h p).2.1}

noncomputable def cartesianExterior (h R : ℝ) : Set SpaceTime :=
  {z | z.1 < 1 ∧ R < (cartesianChart h z).2.1}

theorem exteriorDomain_isOpen {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (R : ℝ) :
    IsOpen (exteriorDomain h R) := by
  simpa [exteriorDomain, SimilarityProfile.physicalDomain] using
    SimilarityProfile.isOpen_physicalDomain hh hh1
      ((isOpen_Ioi : IsOpen (Ioi R)).prod (isOpen_univ : IsOpen (univ : Set ℝ)))

theorem cartesianExterior_isOpen {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (R : ℝ) :
    IsOpen (cartesianExterior h R) :=
  (exteriorDomain_isOpen hh hh1 R).preimage
    (AxisymmetricFields.contDiff_profilePoint (n := ∞)).continuous

theorem physicalProfile_eq_leading {a : ℕ → ℕ} {h b : ℝ} {f : ℕ → Inner → ℝ}
    {p : PhysicalPoint} (hf : ∀ n : ℕ, 0 < n → f n (physicalChart h p).2 = 0) :
    physicalProfile a h b f p = SimilarityProfile.pullback h b (f 0) p := by
  unfold physicalProfile
  rw [show slowSum a h f (physicalChart h p) = f 0 (physicalChart h p).2 from
    BaseResidual.slowSum_eq_leading_of_positive_zero a h _ hf]
  rfl

theorem exterior_stream_zero {a : ℕ → ℕ} {h C R : ℝ} {d : Coefficients}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hR : 0 ≤ R) (hd : ExteriorCoefficients d R)
    {p : PhysicalPoint} (hp : p ∈ exteriorDomain h R) : streamFactor a h C d p = 0 := by
  apply BaseResidual.physicalProfile_zero_of_all
  intro n
  exact hd.average hR n hp.2 (physical_eta_mem hh hh1 hp.1)

/-- All derivatives of the actual cut stream vanish in the exterior.
In particular this includes derivatives falling on the scale cutoffs. -/
theorem exterior_stream_germ {a : ℕ → ℕ} {h C R : ℝ} {d : Coefficients}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hR : 0 ≤ R) (hd : ExteriorCoefficients d R)
    {p : PhysicalPoint} (hp : p ∈ exteriorDomain h R) :
    streamFactor a h C d =ᶠ[𝓝 p] (fun _ => 0) := by
  filter_upwards [(exteriorDomain_isOpen hh hh1 R).mem_nhds hp] with y hy
  exact exterior_stream_zero hh hh1 hR hd hy

noncomputable def leadingAngular (h C : ℝ) (d : Coefficients) : PhysicalProfile :=
  fun p => C⁻¹ * SimilarityProfile.pullback h (-CoordinateAlgebra.A h - 1 / 2) (d.phi 0) p

noncomputable def leadingPressure (h : ℝ) (d : Coefficients) : PhysicalProfile :=
  SimilarityProfile.pullback h (-2 * CoordinateAlgebra.A h) (d.pressure 0)

theorem exterior_swirl_derivative {a : ℕ → ℕ} (ha : StrictMono a) {h C R : ℝ}
    {d : Coefficients} (hh : 0 < h) (hh1 : h < 1 / 2) (hds : SmoothCoefficients d)
    (hd : ExteriorCoefficients d R) {p : PhysicalPoint} (hp : p ∈ exteriorDomain h R) :
    AxisymmetricFields.partialS (swirlPotential a h C d) p = -leadingAngular h C d p := by
  rw [partialS_swirlPotential ha hh hh1 hds C hp.1,
    physicalProfile_eq_leading (fun n hn => hd.phi n hn _ hp.2 (physical_eta_mem hh hh1 hp.1))]
  simp only [leadingAngular]
  ring

theorem exterior_velocity_eq_leading {a : ℕ → ℕ} (ha : StrictMono a) {h C R : ℝ}
    {d : Coefficients} (hh : 0 < h) (hh1 : h < 1 / 2) (hR : 0 ≤ R)
    (hds : SmoothCoefficients d) (hd : ExteriorCoefficients d R)
    {z : SpaceTime} (hz : z ∈ cartesianExterior h R) :
    baseVelocity a h C d z =
      AxisymmetricResidual.velocity (fun _ => 0) (leadingAngular h C d) (fun _ => 0) z := by
  let p := AxisymmetricFields.profilePoint z.1 z.2
  have hp : p ∈ exteriorDomain h R := hz
  have hH : DifferentiableAt ℝ (streamFactor a h C d) p :=
    (physicalProfile_smoothAt ha hh hh1 (bundleComponent_smooth hds C 0) _ hp.1).differentiableAt
      (by simp)
  have hK : DifferentiableAt ℝ (swirlPotential a h C d) p :=
    (physicalProfile_smoothAt ha hh hh1 (bundleComponent_smooth hds C 1) _ hp.1).differentiableAt
      (by simp)
  have he := exterior_stream_germ (a := a) (C := C) hh hh1 hR hd hp
  have h0 := he.self_of_nhds
  have hS : AxisymmetricFields.partialS (streamFactor a h C d) p = 0 := by
    simp [AxisymmetricFields.partialS, he.fderiv_eq]
  have hZ : AxisymmetricFields.partialZ (streamFactor a h C d) p = 0 := by
    simp [AxisymmetricFields.partialZ, he.fderiv_eq]
  have hsw := exterior_swirl_derivative (C := C) ha hh hh1 hds hd hp
  dsimp only [p] at h0 hS hZ hsw
  ext i
  fin_cases i
  · change baseVelocity a h C d z 0 = _
    rw [show baseVelocity a h C d z 0 = _ from AxisymmetricFields.velocity_zero _ _ _ _ hH hK]
    simp [hZ, hsw, AxisymmetricResidual.velocity, AxisymmetricResidual.componentX,
      AxisymmetricResidual.componentY, AxisymmetricResidual.pack, AxisymmetricResidual.lift,
      coordinateVector]
  · change baseVelocity a h C d z 1 = _
    rw [show baseVelocity a h C d z 1 = _ from AxisymmetricFields.velocity_one _ _ _ _ hH hK]
    simp [hZ, hsw, AxisymmetricResidual.velocity, AxisymmetricResidual.componentX,
      AxisymmetricResidual.componentY, AxisymmetricResidual.pack, AxisymmetricResidual.lift,
      coordinateVector]
  · change baseVelocity a h C d z 2 = _
    rw [show baseVelocity a h C d z 2 = _ from AxisymmetricFields.velocity_two _ _ _ _ hH hK]
    simp [h0, hS, AxisymmetricResidual.velocity, AxisymmetricResidual.componentX,
      AxisymmetricResidual.componentY, AxisymmetricResidual.pack, AxisymmetricResidual.lift,
      coordinateVector, Fin.ext_iff]

theorem exterior_pressure_eq_leading {a : ℕ → ℕ} {h C R : ℝ} {d : Coefficients}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hd : ExteriorCoefficients d R)
    {z : SpaceTime} (hz : z ∈ cartesianExterior h R) :
    basePressure a h C d z = AxisymmetricResidual.pressure (leadingPressure h d) z := by
  apply physicalProfile_eq_leading
  intro n hn
  exact hd.pressure n hn _ hz.2 (physical_eta_mem hh hh1 hz.1)

/-- Exact physical leading identities suffice for the exterior comparison;
there is no hypothesis about the summed velocity or residual. -/
theorem exterior_base_eq_heat {a : ℕ → ℕ} (ha : StrictMono a) {h C R K : ℝ}
    {d : Coefficients} (hh : 0 < h) (hh1 : h < 1 / 2) (hR : 0 ≤ R)
    (hds : SmoothCoefficients d) (hd : ExteriorCoefficients d R)
    (hphi : EqOn (leadingAngular h C d) (heatCoefficient K h) (exteriorDomain h R))
    (hp : EqOn (leadingPressure h d) (heatPressure K h) (exteriorDomain h R)) :
    EqOn (baseVelocity a h C d) (heatVelocity K h) (cartesianExterior h R) ∧
      EqOn (basePressure a h C d) (heatPressureField K h) (cartesianExterior h R) := by
  constructor
  · intro z hz
    rw [exterior_velocity_eq_leading ha hh hh1 hR hds hd hz]
    unfold AxisymmetricResidual.velocity heatVelocity AxisymmetricResidual.componentX
      AxisymmetricResidual.componentY AxisymmetricResidual.lift
    rw [hphi hz]
    rfl
  · intro z hz
    rw [exterior_pressure_eq_leading hh hh1 hd hz]
    exact hp hz

theorem exterior_base_residual_zero {a : ℕ → ℕ} (ha : StrictMono a) {h C R K : ℝ}
    {d : Coefficients} (hh : 0 < h) (hh1 : h < 1 / 2) (hR : 0 ≤ R)
    (hds : SmoothCoefficients d) (hd : ExteriorCoefficients d R)
    (hphi : EqOn (leadingAngular h C d) (heatCoefficient K h) (exteriorDomain h R))
    (hp : EqOn (leadingPressure h d) (heatPressure K h) (exteriorDomain h R))
    {z : SpaceTime} (hz : z ∈ cartesianExterior h R) :
    navierStokesResidual (baseVelocity a h C d) (basePressure a h C d) z.1 z.2 = 0 := by
  have he := exterior_base_eq_heat ha hh hh1 hR hds hd hphi hp
  have heq := ResidualRegularity.residual_eqOn (cartesianExterior_isOpen hh hh1 R) he.1 he.2 hz
  change navierStokesResidual (baseVelocity a h C d) (basePressure a h C d) z.1 z.2 =
    navierStokesResidual (heatVelocity K h) (heatPressureField K h) z.1 z.2 at heq
  rw [heq]
  apply heat_navierStokesResidual_zero K hh hh1 hz.1
  have hx : 0 < (cartesianChart h z).2.1 := hR.trans_lt hz.2
  change 0 < AxisymmetricFields.radialEnergy z.2 / _ at hx
  exact (div_pos_iff.mp hx).resolve_right (fun h =>
    (not_lt_of_ge (AxisymmetricFields.radialEnergy_nonneg z.2)) h.1) |>.1

end ExteriorSummation

section PressureScaling

theorem q_radial (h t s s' z : ℝ) : q h (t, (s, z)) = q h (t, (s', z)) := rfl

theorem eta_radial (h t s s' z : ℝ) : eta h (t, (s, z)) = eta h (t, (s', z)) := rfl

theorem pullback_radial_scaled (h b : ℝ) (f : InnerProfile) {p : PhysicalPoint}
    (hq : 0 < q h p) (u : ℝ) :
    pullback h b f (p.1, (q h p * u, p.2.2)) = q h p ^ b * f (u, eta h p) := by
  change q h p ^ b * f (q h p * u / q h p, eta h p) = _
  rw [mul_div_cancel_left₀ _ hq.ne']

/-- Dilation of the actual improper pressure integral. No pressure
regularity or pressure identity is assumed. -/
theorem canonicalPressure_pullback (h b : ℝ) (f : InnerProfile) {p : PhysicalPoint}
    (hq : 0 < q h p) :
    TerminalStress.canonicalPressure (pullback h b f) p =
      q h p ^ (2 * b + 1) * (-(∫ u in Ioi (X h p), f (u, eta h p) ^ 2)) := by
  let g : ℝ → ℝ := fun s => pullback h b f (p.1, (s, p.2.2)) ^ 2
  have hscale := integral_comp_mul_left_Ioi g (X h p) hq
  have hqx : q h p * X h p = p.2.1 := by
    unfold X
    exact mul_div_cancel₀ _ hq.ne'
  rw [hqx] at hscale
  have he : (∫ s in Ioi p.2.1, g s) = q h p * (∫ u in Ioi (X h p), g (q h p * u)) := by
    rw [hscale, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul]
  have hg : (fun u => g (q h p * u)) =
      (fun u => (q h p ^ b) ^ 2 * f (u, eta h p) ^ 2) := by
    funext u
    simp only [g, pullback_radial_scaled h b f hq u, mul_pow]
  have hpow : q h p * (q h p ^ b) ^ 2 = q h p ^ (2 * b + 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le, Real.rpow_add hq, Real.rpow_one]
    norm_num only
    rw [mul_comm b 2]
    ring
  change -(∫ s in Ioi p.2.1, g s) = _
  rw [he, hg, integral_const_mul, ← mul_assoc, hpow]
  ring

theorem canonicalPressure_congr_tail {F G : PhysicalProfile} {p : PhysicalPoint}
    (he : ∀ s : ℝ, p.2.1 < s → F (p.1, (s, p.2.2)) = G (p.1, (s, p.2.2))) :
    TerminalStress.canonicalPressure F p = TerminalStress.canonicalPressure G p := by
  unfold TerminalStress.canonicalPressure
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi (fun s hs => congrArg (fun x : ℝ => x ^ 2) (he s
    hs))

theorem physical_angular_from_profile (h : ℝ) {f E : InnerProfile} {p : PhysicalPoint}
    (hq : 0 < q h p) (hs : 0 < p.2.1)
    (he : E (inner h p) = Real.sqrt (2 * X h p) * f (inner h p)) :
    pullback h (-CoordinateAlgebra.A h - 1 / 2) f p =
      q h p ^ (-CoordinateAlgebra.A h) * E (inner h p) / Real.sqrt (2 * p.2.1) := by
  have hroot : Real.sqrt (2 * p.2.1) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  rw [he]
  unfold pullback
  rw [X, show 2 * (p.2.1 / q h p) = (2 * p.2.1) / q h p by ring,
    Real.sqrt_div (by positivity : 0 ≤ 2 * p.2.1) (q h p), Real.sqrt_eq_rpow (q h p),
    Real.rpow_sub hq]
  field_simp

end PressureScaling

section ClosedTimeRegularity

noncomputable def closedHeatDomain : Set PhysicalPoint := {p | p.1 ≤ 1 ∧ 0 < p.2.1}

theorem heatCoefficient_sq_scaled (C h : ℝ) {p : PhysicalPoint} (hs : 0 < p.2.1)
    {v : ℝ} (hv : 0 < v) :
    heatCoefficient C h (p.1, (p.2.1 * v, p.2.2)) ^ 2 =
      (C ^ 2 / 2 * p.2.1 ^ (-2 * TerminalPressure.amplitudeExponent h - 1)) *
        TerminalPressure.heatDensity h ((1 - p.1) / p.2.1) v := by
  rw [heatCoefficient, TerminalPressure.swirlCoefficient_sq C h (fun _ => 1) (mul_pos hs hv),
    Real.mul_rpow hs.le hv.le]
  have he : 2 * (1 - p.1) / (p.2.1 * v) = 2 * ((1 - p.1) / p.2.1) / v := by ring
  rw [he]
  unfold TerminalPressure.heatDensity TerminalPressure.pressureWeight
  ring

/-- A formula for the canonical heat pressure valid also at zero time
remaining. Its factor is the actual convergent pressure integral. -/
theorem heatPressure_formula (C h : ℝ) {p : PhysicalPoint} (hs : 0 < p.2.1) :
    heatPressure C h p =
      -(C ^ 2 / 2) * p.2.1 ^ (-2 * TerminalPressure.amplitudeExponent h) *
        TerminalPressure.heatPressureFactor h ((1 - p.1) / p.2.1) := by
  let g : ℝ → ℝ := fun s => heatCoefficient C h (p.1, (s, p.2.2)) ^ 2
  have hscale := integral_comp_mul_left_Ioi g 1 hs
  have he : (∫ s in Ioi p.2.1, g s) = p.2.1 * (∫ v in Ioi (1 : ℝ), g (p.2.1 * v)) := by
    rw [hscale, mul_one, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
  have hd : (∫ v in Ioi (1 : ℝ), g (p.2.1 * v)) =
      (C ^ 2 / 2 * p.2.1 ^ (-2 * TerminalPressure.amplitudeExponent h - 1)) *
        TerminalPressure.heatPressureFactor h ((1 - p.1) / p.2.1) := by
    rw [TerminalPressure.heatPressureFactor, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact heatCoefficient_sq_scaled C h hs (zero_lt_one.trans hv)
  change -(∫ s in Ioi p.2.1, g s) = _
  rw [he, hd, Real.rpow_sub hs, Real.rpow_one]
  field_simp

/-- Joint one-sided smoothness at `t=1` at every positive physical radius. -/
theorem heatCoefficient_contDiffOn_closed (C : ℝ) {h : ℝ} (hh : 0 < h) :
    ContDiffOn ℝ ∞ (heatCoefficient C h) closedHeatDomain := by
  have hheat : ContDiffOn ℝ ∞ (fun p : PhysicalPoint =>
      RadialHeatProfile.spatialProfile (1 + h) (1 - p.1) p.2.1) closedHeatDomain :=
    (RadialHeatProfile.spatialProfile_joint_contDiffOn (by linarith)).comp
      (contDiffOn_snd.fst.prodMk (contDiffOn_const.sub contDiffOn_fst))
      (fun _ hp => ⟨hp.2, sub_nonneg.mpr hp.1⟩)
  have hr : ContDiffOn ℝ ∞ (fun p : PhysicalPoint => Real.sqrt (2 * p.2.1)) closedHeatDomain :=
    (contDiffOn_const.mul contDiffOn_snd.fst).sqrt (fun _ hp => by have := hp.2; positivity)
  have hdiv := ((contDiffOn_const (c := C)).mul hheat).div hr
    (fun _ hp => (Real.sqrt_pos.mpr (by have := hp.2; positivity)).ne')
  rw [show heatCoefficient C h = (fun p => TerminalStress.physicalHeat C (1 + h) p /
    Real.sqrt (2 * p.2.1)) from funext (heatCoefficient_eq C h)]
  exact hdiv

theorem heatPressure_contDiffOn_closed (C : ℝ) {h : ℝ} (hh : 0 < h) :
    ContDiffOn ℝ ∞ (heatPressure C h) closedHeatDomain := by
  have hnu : ContDiffOn ℝ ∞ (fun p : PhysicalPoint => (1 - p.1) / p.2.1) closedHeatDomain :=
    (contDiffOn_const.sub contDiffOn_fst).div contDiffOn_snd.fst (fun _ hp => hp.2.ne')
  have hfac := (TerminalPressure.heatPressureFactor_contDiffOn hh).comp hnu
    (fun _ hp => div_nonneg (sub_nonneg.mpr hp.1) hp.2.le)
  have hpow : ContDiffOn ℝ ∞ (fun p : PhysicalPoint =>
      p.2.1 ^ (-2 * TerminalPressure.amplitudeExponent h)) closedHeatDomain :=
    contDiffOn_snd.fst.rpow_const_of_ne (fun _ hp => hp.2.ne')
  apply ((contDiffOn_const.mul hpow).mul hfac).congr
  intro p hp
  exact heatPressure_formula C h hp.2

end ClosedTimeRegularity

section NominalExterior

open AssembledSlowBase

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)

noncomputable def nominalHeatSwitch : ℝ := OutgoingDilation.switchRadius F W.controls.radius

noncomputable def nominalExteriorRadius : ℝ :=
  max (nominalOuterX W) (max W.controls.radius (nominalHeatSwitch W * Real.exp 3))

noncomputable def nominalHeatNormalization : ℝ :=
  PhysicalHeatCoordinates.normalization F.data (nominalHeatSwitch W)

theorem nominalHeatSwitch_pos : 0 < nominalHeatSwitch W :=
  OutgoingDilation.switchRadius_pos F W.controls.radius W.controls.radius_pos

theorem nominalExteriorRadius_pos : 0 < nominalExteriorRadius W :=
  (nominalOuterX_pos W).trans_le (le_max_left _ _)

theorem nominalExteriorRadius_ge_outer : nominalOuterX W ≤ nominalExteriorRadius W := le_max_left _
  _

theorem nominalExteriorRadius_ge_radius : W.controls.radius ≤ nominalExteriorRadius W :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem nominalExteriorRadius_ge_late : nominalHeatSwitch W * Real.exp 3 ≤ nominalExteriorRadius W
  :=
  (le_max_right _ _).trans (le_max_right _ _)

theorem nominalExteriorRadius_gt_switch : nominalHeatSwitch W < nominalExteriorRadius W := by
  have he : (1 : ℝ) < Real.exp 3 := Real.one_lt_exp_iff.mpr (by norm_num)
  exact (lt_mul_of_one_lt_right (nominalHeatSwitch_pos W) he).trans_le
    (nominalExteriorRadius_ge_late W)

/-- All required original coefficient support and mass identities are
discharged for the actual repaired nominal sequence. -/
theorem nominal_exterior_coefficients :
    ExteriorCoefficients (nominalCoefficients W) (nominalExteriorRadius W) := by
  constructor
  · intro n w hw he
    exact nominalCoefficients_axial_zero_all W n
      ((nominalExteriorRadius_ge_outer W).trans hw.le) (abs_le.mpr he)
  · intro n w hw he
    exact nominal_axial_primitive_zero_all W n
      ((nominalExteriorRadius_ge_outer W).trans hw.le) (abs_le.mpr he)
  · intro n hn w hw _
    exact (nominalCoefficients_positive_exterior W hn
      ((nominalExteriorRadius_ge_outer W).trans hw.le)).1
  · intro n hn w hw _
    exact (nominalCoefficients_positive_exterior W hn
      ((nominalExteriorRadius_ge_outer W).trans hw.le)).2.2

theorem nominal_leadingAngular_eq_pullback {p : PhysicalPoint}
    (ht : p.1 < 1) (hX : 0 ≤ X F.data.h p) :
    leadingAngular F.data.h W.axis.normalization (nominalCoefficients W) p =
      pullback F.data.h (-CoordinateAlgebra.A F.data.h - 1 / 2) W.f p := by
  have he := physical_eta_mem F.data.h_pos F.data.h_lt_half ht
  have hc := (nominalCoefficients_zero_fields W hX (abs_le.mpr he)).1
  simp only [physicalChart_eq] at hc
  unfold leadingAngular pullback
  rw [hc]
  field_simp [W.axis.normalization_pos.ne']

theorem nominal_late_ratio {X : ℝ} (hX : nominalExteriorRadius W < X) :
    3 ≤ Real.log (X / nominalHeatSwitch W) + 1 / 5 := by
  have hx : 0 < X := (nominalExteriorRadius_pos W).trans hX
  have harg : 0 < X / nominalHeatSwitch W := div_pos hx (nominalHeatSwitch_pos W)
  have he : Real.exp (3 : ℝ) < X / nominalHeatSwitch W := by
    apply (lt_div_iff₀ (nominalHeatSwitch_pos W)).mpr
    rw [mul_comm]
    exact (nominalExteriorRadius_ge_late W).trans_lt hX
  have hl := (Real.lt_log_iff_exp_lt harg).mpr he
  linarith

theorem nominal_angular_pure_heat {p : PhysicalPoint}
    (hp : p ∈ exteriorDomain F.data.h (nominalExteriorRadius W)) :
    leadingAngular F.data.h W.axis.normalization (nominalCoefficients W) p =
      heatCoefficient (nominalHeatNormalization W) F.data.h p := by
  have hq := q_pos F.data.h_pos F.data.h_lt_half hp.1
  have hX : 0 < X F.data.h p := (nominalExteriorRadius_pos W).trans hp.2
  have hs : 0 < p.2.1 := (div_pos_iff.mp hX).resolve_right
    (fun h => (not_lt_of_ge hq.le) h.2) |>.1
  have he : eta F.data.h p ∈ HeatedOutgoing.parameterDomain :=
    physical_eta_mem F.data.h_pos F.data.h_lt_half hp.1
  have hjoin : W.controls.heatJoin < X F.data.h p :=
    (W.controls.heatJoin_lt_radius.trans_le (nominalExteriorRadius_ge_radius W)).trans hp.2
  have hswitch : nominalHeatSwitch W ≤ X F.data.h p :=
    (nominalExteriorRadius_gt_switch W).le.trans hp.2.le
  have hE : W.E (inner F.data.h p) =
      ParametricHeatTail.physicalEdit F.data (nominalHeatSwitch W) (eta F.data.h p) (X F.data.h p)
        :=
    (W.heat_agreement hjoin he).2.1.trans
      (HeatedOutgoing.E_after_switch F W.controls.radius W.heat.physical.coefficients
        (eta F.data.h p) (X F.data.h p) W.controls.radius_pos hswitch)
  rw [nominal_leadingAngular_eq_pullback W hp.1 hX.le,
    physical_angular_from_profile F.data.h hq hs (W.E_eq_sqrt_f hX), hE]
  change PhysicalHeatCoordinates.editedAngular F.data (nominalHeatSwitch W) p /
    Real.sqrt (2 * p.2.1) = _
  rw [PhysicalHeatCoordinates.editedAngular_eq_pure_heat F.data (nominalHeatSwitch_pos W)
    F.data.h_lt_half hp.1 hs (nominal_late_ratio W hp.2), heatCoefficient_eq]
  rfl

/-- The nominal pressure is the actual squared regular swirl integral. -/
theorem nominal_pressure_regular_integral {X eta : ℝ} (hX : 0 ≤ X)
    (he : eta ∈ HeatedOutgoing.parameterDomain) :
    W.Pi (X, eta) = -(∫ u in Ioi X, W.f (u, eta) ^ 2) := by
  rw [W.pressure_canonical hX he]
  have hi : (∫ u in Ioi X, W.E (u, eta) ^ 2 / u) =
      ∫ u in Ioi X, 2 * W.f (u, eta) ^ 2 := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    have hu0 := hX.trans_lt hu
    change W.E (u, eta) ^ 2 / u = 2 * W.f (u, eta) ^ 2
    rw [W.E_eq_sqrt_f (p := (u, eta)) hu0, mul_pow, Real.sq_sqrt (by positivity)]
    field_simp
  rw [hi, integral_const_mul]
  ring

theorem nominal_pressure_pullback {p : PhysicalPoint}
    (ht : p.1 < 1) (hX : 0 ≤ X F.data.h p) :
    leadingPressure F.data.h (nominalCoefficients W) p =
      TerminalStress.canonicalPressure
        (pullback F.data.h (-CoordinateAlgebra.A F.data.h - 1 / 2) W.f) p := by
  have he := physical_eta_mem F.data.h_pos F.data.h_lt_half ht
  have hc := (nominalCoefficients_zero_fields W hX (abs_le.mpr he)).2.2
  simp only [physicalChart_eq] at hc
  have hp := canonicalPressure_pullback F.data.h (-CoordinateAlgebra.A F.data.h - 1 / 2) W.f
    (q_pos F.data.h_pos F.data.h_lt_half ht)
  rw [show 2 * (-CoordinateAlgebra.A F.data.h - 1 / 2) + 1 =
    -2 * CoordinateAlgebra.A F.data.h by ring] at hp
  unfold leadingPressure pullback
  rw [hc]
  change q F.data.h p ^ (-2 * CoordinateAlgebra.A F.data.h) *
    W.Pi (X F.data.h p, eta F.data.h p) = _
  rw [nominal_pressure_regular_integral W hX (show eta F.data.h p ∈ HeatedOutgoing.parameterDomain
    from he)]
  exact hp.symm

theorem nominal_pressure_pure_heat {p : PhysicalPoint}
    (hp : p ∈ exteriorDomain F.data.h (nominalExteriorRadius W)) :
    leadingPressure F.data.h (nominalCoefficients W) p =
      heatPressure (nominalHeatNormalization W) F.data.h p := by
  have hX : 0 < X F.data.h p := (nominalExteriorRadius_pos W).trans hp.2
  rw [nominal_pressure_pullback W hp.1 hX.le]
  apply canonicalPressure_congr_tail
  intro s hs
  have hq := q_pos F.data.h_pos F.data.h_lt_half hp.1
  have hx' : nominalExteriorRadius W < X F.data.h (p.1, (s, p.2.2)) := by
    exact hp.2.trans (div_lt_div_of_pos_right hs hq)
  have hpt : (p.1, (s, p.2.2)) ∈ exteriorDomain F.data.h (nominalExteriorRadius W) :=
    ⟨hp.1, hx'⟩
  rw [← nominal_leadingAngular_eq_pullback W (p := (p.1, (s, p.2.2))) hp.1
    ((nominalExteriorRadius_pos W).trans hx').le]
  exact nominal_angular_pure_heat W hpt

/-- The actual summed nominal velocity and pressure are exactly the radial
heat field outside one common profile radius, for every cutoff schedule. -/
theorem nominal_base_eq_heat {a : ℕ → ℕ} (ha : StrictMono a) :
    EqOn (baseVelocity a F.data.h W.axis.normalization (nominalCoefficients W))
      (heatVelocity (nominalHeatNormalization W) F.data.h)
      (cartesianExterior F.data.h (nominalExteriorRadius W)) ∧
    EqOn (basePressure a F.data.h W.axis.normalization (nominalCoefficients W))
      (heatPressureField (nominalHeatNormalization W) F.data.h)
      (cartesianExterior F.data.h (nominalExteriorRadius W)) :=
  exterior_base_eq_heat ha F.data.h_pos F.data.h_lt_half (nominalExteriorRadius_pos W).le
    (nominalCoefficients_smooth W) (nominal_exterior_coefficients W)
    (fun _ hp => nominal_angular_pure_heat W hp) (fun _ hp => nominal_pressure_pure_heat W hp)

/-- Exact zero residual in the actual summed exterior. No exterior
solution property is supplied as a premise. -/
theorem nominal_base_residual_zero {a : ℕ → ℕ} (ha : StrictMono a)
    {z : SpaceTime} (hz : z ∈ cartesianExterior F.data.h (nominalExteriorRadius W)) :
    navierStokesResidual (baseVelocity a F.data.h W.axis.normalization (nominalCoefficients W))
      (basePressure a F.data.h W.axis.normalization (nominalCoefficients W)) z.1 z.2 = 0 :=
  exterior_base_residual_zero ha F.data.h_pos F.data.h_lt_half (nominalExteriorRadius_pos W).le
    (nominalCoefficients_smooth W) (nominal_exterior_coefficients W)
    (fun _ hp => nominal_angular_pure_heat W hp) (fun _ hp => nominal_pressure_pure_heat W hp) hz

theorem nominal_base_residual_germ_zero {a : ℕ → ℕ} (ha : StrictMono a)
    {z : SpaceTime} (hz : z ∈ cartesianExterior F.data.h (nominalExteriorRadius W)) :
    (fun y => navierStokesResidual
      (baseVelocity a F.data.h W.axis.normalization (nominalCoefficients W))
      (basePressure a F.data.h W.axis.normalization (nominalCoefficients W)) y.1 y.2)
        =ᶠ[𝓝 z] (fun _ => 0) := by
  filter_upwards [(cartesianExterior_isOpen F.data.h_pos F.data.h_lt_half
    (nominalExteriorRadius W)).mem_nhds hz] with y hy
  exact nominal_base_residual_zero W ha hy

/-- Every physical derivative of the actual Cartesian residual is exactly
zero on the exterior, not just asymptotically small. -/
theorem nominal_base_residual_jets_zero {a : ℕ → ℕ} (ha : StrictMono a)
    {z : SpaceTime} (hz : z ∈ cartesianExterior F.data.h (nominalExteriorRadius W)) (m : ℕ) :
    iteratedFDeriv ℝ m (fun y => navierStokesResidual
      (baseVelocity a F.data.h W.axis.normalization (nominalCoefficients W))
      (basePressure a F.data.h W.axis.normalization (nominalCoefficients W)) y.1 y.2) z = 0 := by
  rw [(SolenoidalDiagonal.iteratedFDeriv_eventuallyEq (nominal_base_residual_germ_zero W ha hz)
    m).self_of_nhds,
    iteratedFDeriv_fun_zero, Pi.zero_apply]

end NominalExterior

section TerminalExtension

noncomputable def closedCartesianHeatDomain : Set SpaceTime :=
  {z | z.1 ≤ 1 ∧ 0 < AxisymmetricFields.radialEnergy z.2}

theorem heatVelocity_eq_angularVector (C h : ℝ) (z : SpaceTime) :
    heatVelocity C h z = heatCoefficient C h (AxisymmetricFields.profilePoint z.1 z.2) •
      BaseResidual.angularVector z := by
  ext i
  fin_cases i <;>
    simp [heatVelocity, AxisymmetricResidual.velocity, AxisymmetricResidual.componentX,
      AxisymmetricResidual.componentY, AxisymmetricResidual.lift, AxisymmetricResidual.pack,
      BaseResidual.angularVector, coordinateVector, Fin.ext_iff] <;> ring

/-- The exact exterior solution is jointly smooth up to the terminal time
on every region of positive physical radius, in Cartesian coordinates. -/
theorem heatVelocity_contDiffOn_closed (C : ℝ) {h : ℝ} (hh : 0 < h) :
    ContDiffOn ℝ ∞ (heatVelocity C h) closedCartesianHeatDomain := by
  have hs := (heatCoefficient_contDiffOn_closed C hh).comp
    (AxisymmetricFields.contDiff_profilePoint (n := ∞)).contDiffOn
    (show MapsTo (fun z : SpaceTime => AxisymmetricFields.profilePoint z.1 z.2)
      closedCartesianHeatDomain closedHeatDomain from fun _ hz => hz)
  have he : heatVelocity C h = (fun z =>
      heatCoefficient C h (AxisymmetricFields.profilePoint z.1 z.2) • BaseResidual.angularVector z)
        :=
    funext (heatVelocity_eq_angularVector C h)
  rw [he]
  exact hs.smul BaseResidual.angularVector_smooth.contDiffOn

theorem heatPressureField_contDiffOn_closed (C : ℝ) {h : ℝ} (hh : 0 < h) :
    ContDiffOn ℝ ∞ (heatPressureField C h) closedCartesianHeatDomain :=
  (heatPressure_contDiffOn_closed C hh).comp
    (AxisymmetricFields.contDiff_profilePoint (n := ∞)).contDiffOn
    (show MapsTo (fun z : SpaceTime => AxisymmetricFields.profilePoint z.1 z.2)
      closedCartesianHeatDomain closedHeatDomain from fun _ hz => hz)

theorem near_one_in_exterior {h R : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) (hR : 0 ≤ R)
    {x : Space} (hx : x 2 = 0) (_hs : 0 < AxisymmetricFields.radialEnergy x)
    {t : ℝ} (ht : t ∈ Ioo (1 - AxisymmetricFields.radialEnergy x / (R + 1)) 1) :
    (t, x) ∈ cartesianExterior h R := by
  have hq : q h (AxisymmetricFields.profilePoint t x) = 1 - t := by
    change NaturalCore.physicalQ h (t, (AxisymmetricFields.radialEnergy x, x 2)) = _
    rw [hx]
    exact NaturalCore.physicalQ_at_zero_z hh hh1 ht.2 _
  refine ⟨ht.2, ?_⟩
  change R < AxisymmetricFields.radialEnergy x / q h (AxisymmetricFields.profilePoint t x)
  rw [hq]
  apply (lt_div_iff₀ (sub_pos.mpr ht.2)).mpr
  have hRp : 0 < R + 1 := by linarith
  have hsmall : 1 - t < AxisymmetricFields.radialEnergy x / (R + 1) := by linarith [ht.1]
  have hprod := (lt_div_iff₀ hRp).mp hsmall
  nlinarith [sub_pos.mpr ht.2]

open AssembledSlowBase

/-- For each fixed positive radius on the central plane, the actual base
equals the explicit heat extension on a whole terminal time interval. -/
theorem nominal_base_terminal_extension {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    {a : ℕ → ℕ} (ha : StrictMono a) {x : Space} (hx : x 2 = 0)
    (hs : 0 < AxisymmetricFields.radialEnergy x) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ t ∈ Ioo (1 - δ) 1,
        baseVelocity a F.data.h W.axis.normalization (nominalCoefficients W) (t, x) =
          heatVelocity (nominalHeatNormalization W) F.data.h (t, x) ∧
        basePressure a F.data.h W.axis.normalization (nominalCoefficients W) (t, x) =
          heatPressureField (nominalHeatNormalization W) F.data.h (t, x)) ∧
      ContDiffOn ℝ ∞ (fun t => heatVelocity (nominalHeatNormalization W) F.data.h (t, x)) (Iic 1) ∧
      ContDiffOn ℝ ∞ (fun t => heatPressureField (nominalHeatNormalization W) F.data.h (t, x)) (Iic
        1) := by
  refine ⟨AxisymmetricFields.radialEnergy x / (nominalExteriorRadius W + 1),
    div_pos hs (by linarith [nominalExteriorRadius_pos W]), ?_, ?_, ?_⟩
  · intro t ht
    have hm := near_one_in_exterior F.data.h_pos F.data.h_lt_half (nominalExteriorRadius_pos W).le
      hx hs ht
    exact ⟨(nominal_base_eq_heat W ha).1 hm, (nominal_base_eq_heat W ha).2 hm⟩
  · exact (heatVelocity_contDiffOn_closed (nominalHeatNormalization W) F.data.h_pos).comp
      (contDiffOn_id.prodMk contDiffOn_const) (fun _ ht => ⟨ht, hs⟩)
  · exact (heatPressureField_contDiffOn_closed (nominalHeatNormalization W) F.data.h_pos).comp
      (contDiffOn_id.prodMk contDiffOn_const) (fun _ ht => ⟨ht, hs⟩)

theorem nominal_base_meridional_zero {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
    {a : ℕ → ℕ} (ha : StrictMono a) {z : SpaceTime}
    (hz : z ∈ cartesianExterior F.data.h (nominalExteriorRadius W)) :
    baseVelocity a F.data.h W.axis.normalization (nominalCoefficients W) z 2 = 0 ∧
      z.2 0 * baseVelocity a F.data.h W.axis.normalization (nominalCoefficients W) z 0 +
        z.2 1 * baseVelocity a F.data.h W.axis.normalization (nominalCoefficients W) z 1 = 0 := by
  rw [(nominal_base_eq_heat W ha).1 hz, heatVelocity_eq_angularVector]
  simp [BaseResidual.angularVector, coordinateVector, Fin.ext_iff]
  ring

end TerminalExtension

end NavierStokes.BaseExterior
