/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.TerminalHistoryBridge
public import LeanPool.NavierStokesAndEuler.NavierStokes.ModulatedProfileAssembly
import LeanPool.NavierStokesAndEuler.NavierStokes.FirstOrderBaseEdge
import LeanPool.NavierStokesAndEuler.NavierStokes.NaturalCore
import LeanPool.NavierStokesAndEuler.NavierStokes.ResidualRegularity
public import LeanPool.NavierStokesAndEuler.NavierStokes.BaseResidual
public import LeanPool.NavierStokesAndEuler.NavierStokes.AssembledSlowBase

/-!
# The actual constructed slow base

The finite residual identities, regular axis descriptors, and stress support
used here are derived from the same repaired coefficient sequence.  No
residual estimate or infinite-dimensional output certificate is an input.
-/

section

/-!
# The actual pure-heat exterior of the summed slow base

The exterior comparison is with the physical radial heat solution and its
canonical improper-integral pressure. All stream cutoffs are retained until
their coefficients are shown to vanish in an exterior neighborhood.
-/

@[expose] public section

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

/-- Heat velocity, given by `AxisymmetricResidual.velocity (fun _ => 0) (heatCoefficient C h)
(fun _ => 0)`. -/
noncomputable def heatVelocity (C h : ℝ) : VelocityField :=
  AxisymmetricResidual.velocity (fun _ => 0) (heatCoefficient C h) (fun _ => 0)

/-- Heat pressure field, given by `AxisymmetricResidual.pressure (heatPressure C h)`. -/
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

/-- Exterior domain, given by `{p | p.1 < 1 ∧ R < (physicalChart h p).2.1}`. -/
noncomputable def exteriorDomain (h R : ℝ) : Set PhysicalPoint :=
  {p | p.1 < 1 ∧ R < (physicalChart h p).2.1}

/-- Cartesian exterior, given by `{z | z.1 < 1 ∧ R < (cartesianChart h z).2.1}`. -/
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

/-- Leading angular, defined pointwise by `C⁻¹ * SimilarityProfile.pullback h
(-CoordinateAlgebra.A h - 1 / 2) (d.phi 0) p`. -/
noncomputable def leadingAngular (h C : ℝ) (d : Coefficients) : PhysicalProfile :=
  fun p => C⁻¹ * SimilarityProfile.pullback h (-CoordinateAlgebra.A h - 1 / 2) (d.phi 0) p

/-- Leading pressure, given by `SimilarityProfile.pullback h (-2 * CoordinateAlgebra.A h)
(d.pressure 0)`. -/
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
        (by
        simp)
  have hK : DifferentiableAt ℝ (swirlPotential a h C d) p :=
    (physicalProfile_smoothAt ha hh hh1 (bundleComponent_smooth hds C 1) _ hp.1).differentiableAt
        (by
        simp)
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

/-- Closed heat domain, given by `{p | p.1 ≤ 1 ∧ 0 < p.2.1}`. -/
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
  · intro p hp
    exact heatPressure_formula C h hp.2

end ClosedTimeRegularity

section NominalExterior

open AssembledSlowBase

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)

/-- Nominal heat switch, given by `OutgoingDilation.switchRadius F W.controls.radius`. -/
noncomputable def nominalHeatSwitch : ℝ := OutgoingDilation.switchRadius F W.controls.radius

/-- Nominal exterior radius, given by `max (nominalOuterX W) (max W.controls.radius
(nominalHeatSwitch W * Real.exp 3))`. -/
noncomputable def nominalExteriorRadius : ℝ :=
  max (nominalOuterX W) (max W.controls.radius (nominalHeatSwitch W * Real.exp 3))

/-- Nominal heat normalization, given by `PhysicalHeatCoordinates.normalization F.data
(nominalHeatSwitch W)`. -/
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

/-- Closed cartesian heat domain, given by `{z | z.1 ≤ 1 ∧ 0 < AxisymmetricFields.radialEnergy
z.2}`. -/
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
  linarith [sub_pos.mpr ht.2]

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

end
end

end

section

/-!
# The curl of the finite slow potentials

The finite Borel prefixes use the average of the axial coefficient and the
primitive of the angular coefficient.  Their curl is identified here with
the finite slow field, using the actual radial flux formula and FTC.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.BasePrefixIdentity

open Set Filter
open scoped Topology ContDiff

open SlowBorelBase (Inner Chart Coefficients SmoothCoefficients)

/-- Differentiating the actual primitive gives the radial average identity. -/
theorem average_radial_identity {U : Inner → ℝ} (hU : ContDiff ℝ ∞ U) (w : Inner) :
    ProfileHistories.average U w + w.1 * SimilarityProfile.partialX (ProfileHistories.average U) w =
      U w := by
  have he : ProfileHistories.primitive U =
      fun y => y.1 * ProfileHistories.average U y :=
    funext (ProfileHistories.primitive_eq_mul_average U)
  have hf : HasFDerivAt (fun y : Inner => y.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) w :=
    hasFDerivAt_fst
  have hd := hf.fun_mul
    ((SlowBorelBase.average_smooth hU).differentiable (by simp)).differentiableAt.hasFDerivAt
  have hi := congrFun (SlowBorelBase.partialX_primitive hU) w
  rw [he] at hi
  unfold SimilarityProfile.partialX at hi ⊢
  rw [hd.fderiv] at hi
  simpa [add_comm] using hi

/-- The flux computed from histories is the axial derivative of the averaged
stream coefficient, with its exact exponent.  No divergence equation is assumed. -/
theorem radialFlux_eq_neg_X_Z_average {U : Inner → ℝ} (hU : ContDiff ℝ ∞ U)
    (h lam : ℝ) (w : Inner) :
    SlowDivergence.radialFlux h lam U w =
      -w.1 * SimilarityProfile.Z h (-CoordinateAlgebra.A h + lam) (ProfileHistories.average U) w :=
          by
  have hi := average_radial_identity hU w
  unfold SlowDivergence.radialFlux SimilarityProfile.Z CoordinateAlgebra.axialCoeff
  rw [← hi]
  simp only [CoordinateAlgebra.A, CoordinateAlgebra.D, div_eq_mul_inv]
  ring

/-- The direct finite profile and the finite Borel prefix have the same local
germ throughout the past-time chart. -/
theorem physicalUncutPrefix_germ {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (b : ℝ) (f : ℕ → Inner → ℝ) (J : ℕ) {p : Chart} (hp : p.1 < 1) :
    SlowBorelBase.physicalUncutPrefix h b f J =ᶠ[𝓝 p] SlowExpansionResidual.finiteProfile J h b f
        := by
  filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hp] with y hy
  exact SlowBorelBase.physicalUncutPrefix_eq_finiteProfile hh hh1 b f J hy

theorem partialS_physicalUncutPrefix {h b : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (J : ℕ) (f : ℕ → Inner → ℝ) {p : Chart} (hp : p.1 < 1)
    (hf : ∀ n ≤ J, DifferentiableAt ℝ (f n) (SimilarityProfile.inner h p)) :
    AxisymmetricFields.partialS (SlowBorelBase.physicalUncutPrefix h b f J) p =
      SlowExpansionResidual.finiteProfile J h (b - 1) (fun n => SimilarityProfile.partialX (f n)) p
          := by
  change fderiv ℝ _ p (0, (1, 0)) = _
  rw [(physicalUncutPrefix_germ hh hh1 b f J hp).fderiv_eq]
  exact SlowExpansionResidual.partialS_finiteProfile hh hh1 J f hp hf

theorem partialZ_physicalUncutPrefix {h b : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (J : ℕ) (f : ℕ → Inner → ℝ) {p : Chart} (hp : p.1 < 1)
    (hf : ∀ n ≤ J, DifferentiableAt ℝ (f n) (SimilarityProfile.inner h p)) :
    AxisymmetricFields.partialZ (SlowBorelBase.physicalUncutPrefix h b f J) p =
      SlowExpansionResidual.finiteProfile J h (b - CoordinateAlgebra.D h)
        (fun n => SimilarityProfile.Z h (b + SlowExpansionResidual.slowOrder h n) (f n)) p := by
  change fderiv ℝ _ p (0, (0, 1)) = _
  rw [(physicalUncutPrefix_germ hh hh1 b f J hp).fderiv_eq]
  exact SlowExpansionResidual.partialZ_finiteProfile hh hh1 J f hp hf

/-- The coefficient family whose flux is constructed from its axial history. -/
noncomputable def profiles (h : ℝ) (d : Coefficients) : SlowExpansionResidual.SlowProfiles where
  phi := d.phi
  axial := d.axial
  pressure := d.pressure
  flux n := SlowDivergence.radialFlux h (SlowExpansionResidual.slowOrder h n) (d.axial n)

theorem prefixStream_axial {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {d : Coefficients} (hd : SmoothCoefficients d) (J : ℕ) (C : ℝ)
    {p : Chart} (hp : p.1 < 1) :
    BaseResidual.prefixStream J h C d p + p.2.1 * AxisymmetricFields.partialS
        (BaseResidual.prefixStream J h C d) p =
      SlowExpansionResidual.slowAxial J h (profiles h d) p := by
  have hq := SimilarityProfile.q_pos hh hh1 hp
  rw [BaseResidual.prefixStream, SlowBorelBase.physicalUncutPrefix_eq_finiteProfile hh hh1 _ _ _ hp]
  rw [partialS_physicalUncutPrefix hh hh1 J _ hp
    (fun n _ => ((SlowBorelBase.bundleComponent_smooth hd C 0 n).differentiable (by
        simp)).differentiableAt)]
  simp only [SlowExpansionResidual.slowAxial, SlowExpansionResidual.axialExponent, profiles,
      SlowExpansionResidual.finiteProfile,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  change SimilarityProfile.pullback h (-CoordinateAlgebra.A h + SlowExpansionResidual.slowOrder h n)
      (ProfileHistories.average (d.axial n)) p +
      p.2.1 * SimilarityProfile.pullback h (-CoordinateAlgebra.A h - 1 +
          SlowExpansionResidual.slowOrder h n)
        (SimilarityProfile.partialX (ProfileHistories.average (d.axial n))) p =
    SimilarityProfile.pullback h (-CoordinateAlgebra.A h + SlowExpansionResidual.slowOrder h n)
        (d.axial n) p
  have hi := average_radial_identity (hd.axial n) (SimilarityProfile.inner h p)
  rw [show -CoordinateAlgebra.A h - 1 + SlowExpansionResidual.slowOrder h n =
    (-CoordinateAlgebra.A h + SlowExpansionResidual.slowOrder h n) - 1 by ring]
  simp only [SimilarityProfile.pullback, Real.rpow_sub_one hq.ne']
  rw [← hi]
  simp only [SimilarityProfile.inner, SimilarityProfile.X]
  ring

theorem prefixSwirl_radial {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {d : Coefficients} (hd : SmoothCoefficients d) (J : ℕ) (C : ℝ)
    {p : Chart} (hp : p.1 < 1) :
    -AxisymmetricFields.partialS (BaseResidual.prefixSwirl J h C d) p =
      SlowExpansionResidual.slowSwirl J h C (profiles h d) p := by
  rw [BaseResidual.prefixSwirl, partialS_physicalUncutPrefix hh hh1 J _ hp
    (fun n _ => ((SlowBorelBase.bundleComponent_smooth hd C 1 n).differentiable (by
        simp)).differentiableAt)]
  have he : (fun n => SimilarityProfile.partialX (SlowBorelBase.bundleComponent C d 1 n)) =
      fun n w => -C⁻¹ * d.phi n w := by
    funext n
    exact SlowBorelBase.partialX_swirl_primitive (hd.phi n) C
  rw [he]
  simp only [SlowExpansionResidual.slowSwirl, SlowExpansionResidual.angularExponent, profiles,
      SlowExpansionResidual.finiteProfile,
    Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [SimilarityProfile.pullback]
  rw [show 1 / 2 - CoordinateAlgebra.A h - 1 + SlowExpansionResidual.slowOrder h n =
    -CoordinateAlgebra.A h - 1 / 2 + SlowExpansionResidual.slowOrder h n by ring]
  ring

theorem prefixStream_flux {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {d : Coefficients} (hd : SmoothCoefficients d) (J : ℕ) (C : ℝ)
    {p : Chart} (hp : p.1 < 1) :
    -p.2.1 * AxisymmetricFields.partialZ (BaseResidual.prefixStream J h C d) p =
      SlowExpansionResidual.slowFlux J h (profiles h d) p := by
  have hq := SimilarityProfile.q_pos hh hh1 hp
  rw [BaseResidual.prefixStream, partialZ_physicalUncutPrefix hh hh1 J _ hp
    (fun n _ => ((SlowBorelBase.bundleComponent_smooth hd C 0 n).differentiable (by
        simp)).differentiableAt)]
  simp only [SlowExpansionResidual.slowFlux, profiles, SlowExpansionResidual.finiteProfile,
      Finset.mul_sum, zero_add]
  apply Finset.sum_congr rfl
  intro n hn
  change -p.2.1 * SimilarityProfile.pullback h
      (-CoordinateAlgebra.A h - CoordinateAlgebra.D h + SlowExpansionResidual.slowOrder h n)
      (SimilarityProfile.Z h (-CoordinateAlgebra.A h + SlowExpansionResidual.slowOrder h n)
        (ProfileHistories.average (d.axial n))) p =
    SimilarityProfile.pullback h (SlowExpansionResidual.slowOrder h n)
      (SlowDivergence.radialFlux h (SlowExpansionResidual.slowOrder h n) (d.axial n)) p
  rw [show -CoordinateAlgebra.A h - CoordinateAlgebra.D h + SlowExpansionResidual.slowOrder h n =
    SlowExpansionResidual.slowOrder h n - 1 by unfold CoordinateAlgebra.A CoordinateAlgebra.D; ring]
  simp only [SimilarityProfile.pullback, Real.rpow_sub_one hq.ne',
    radialFlux_eq_neg_X_Z_average (hd.axial n)]
  simp only [SimilarityProfile.inner, SimilarityProfile.X]
  ring

/-- The actual finite curl is the slow field with the flux constructed above. -/
theorem prefixVelocity_eq_profiles {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {d : Coefficients} (hd : SmoothCoefficients d) (J : ℕ) (C : ℝ)
    {t : ℝ} (ht : t < 1) (x : ProblemStatement.Space)
    (hs : 0 < AxisymmetricFields.radialEnergy x) :
    BaseResidual.prefixVelocity J h C d (t, x) =
      SlowExpansionResidual.slowVelocity J h C (profiles h d) (t, x) := by
  have hH := (SlowBorelBase.physicalUncutPrefix_smoothAt hh hh1
    (SlowBorelBase.bundleComponent_smooth hd C 0) (-CoordinateAlgebra.A h) J
    (p := AxisymmetricFields.profilePoint t x) ht).differentiableAt (by simp)
  have hK := (SlowBorelBase.physicalUncutPrefix_smoothAt hh hh1
    (SlowBorelBase.bundleComponent_smooth hd C 1) (1 / 2 - CoordinateAlgebra.A h) J
    (p := AxisymmetricFields.profilePoint t x) ht).differentiableAt (by simp)
  change DifferentiableAt ℝ (BaseResidual.prefixStream J h C d)
    (AxisymmetricFields.profilePoint t x) at hH
  change DifferentiableAt ℝ (BaseResidual.prefixSwirl J h C d)
    (AxisymmetricFields.profilePoint t x) at hK
  have hu := prefixStream_axial hh hh1 hd J C (p := AxisymmetricFields.profilePoint t x) ht
  have hf := prefixSwirl_radial hh hh1 hd J C (p := AxisymmetricFields.profilePoint t x) ht
  have hv := prefixStream_flux hh hh1 hd J C (p := AxisymmetricFields.profilePoint t x) ht
  change AxisymmetricFields.velocity (BaseResidual.prefixStream J h C d)
    (BaseResidual.prefixSwirl J h C d) (t, x) = _
  rw [SlowExpansionResidual.slowVelocity_components]
  ext i
  fin_cases i
  · change AxisymmetricFields.velocity (BaseResidual.prefixStream J h C d)
      (BaseResidual.prefixSwirl J h C d) (t, x) 0 = _
    rw [AxisymmetricFields.velocity_zero _ _ _ _ hH hK, ← hf, ← hv]
    norm_num [AxisymmetricResidual.pack, ProblemStatement.coordinateVector, PiLp.single_apply]
    norm_num [Fin.ext_iff]
    dsimp only [AxisymmetricFields.profilePoint]
    field_simp [hs.ne']
  · change AxisymmetricFields.velocity (BaseResidual.prefixStream J h C d)
      (BaseResidual.prefixSwirl J h C d) (t, x) 1 = _
    rw [AxisymmetricFields.velocity_one _ _ _ _ hH hK, ← hf, ← hv]
    norm_num [AxisymmetricResidual.pack, ProblemStatement.coordinateVector, PiLp.single_apply]
    norm_num [Fin.ext_iff]
    dsimp only [AxisymmetricFields.profilePoint]
    field_simp [hs.ne']; ring
  · change AxisymmetricFields.velocity (BaseResidual.prefixStream J h C d)
      (BaseResidual.prefixSwirl J h C d) (t, x) 2 = _
    rw [AxisymmetricFields.velocity_two _ _ _ _ hH hK]
    simp only [Fin.isValue, Fin.reduceFinMk, AxisymmetricResidual.pack_two] at hu ⊢
    exact hu

/-- The physical similarity coordinates range inside this open half strip. -/
noncomputable def profileWindow : Set Inner := Ioi 0 ×ˢ Ioo (-1) 1

theorem profileWindow_open : IsOpen profileWindow := isOpen_Ioi.prod isOpen_Ioo

theorem inner_mem_profileWindow {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {p : Chart} (ht : p.1 < 1) (hs : 0 < p.2.1) :
    SimilarityProfile.inner h p ∈ profileWindow := by
  refine ⟨LeadingStress.inner_X_pos hh hh1 ht hs, ?_⟩
  have he := SimilarityProfile.eta_sq_lt_one hh hh1 ht
  change -1 < SimilarityProfile.eta h p ∧ SimilarityProfile.eta h p < 1
  constructor <;> linarith [sq_nonneg (SimilarityProfile.eta h p + 1),
    sq_nonneg (SimilarityProfile.eta h p - 1)]

/-- Only scalar coefficient values and the actual flux identity are needed
to identify the reconstructed velocity. -/
structure VelocityMatches (h : ℝ) (d : Coefficients)
    (f : SlowExpansionResidual.SlowProfiles) : Prop where
  phi : ∀ n, EqOn (d.phi n) (f.phi n) profileWindow
  axial : ∀ n, EqOn (d.axial n) (f.axial n) profileWindow
  flux : ∀ n, EqOn
    (SlowDivergence.radialFlux h (SlowExpansionResidual.slowOrder h n) (d.axial n))
    (f.flux n) profileWindow

theorem finiteProfile_eq_of_values (J : ℕ) (h b : ℝ)
    {f g : ℕ → Inner → ℝ} {p : Chart}
    (he : ∀ n ≤ J, f n (SimilarityProfile.inner h p) = g n (SimilarityProfile.inner h p)) :
    SlowExpansionResidual.finiteProfile J h b f p =
      SlowExpansionResidual.finiteProfile J h b g p := by
  apply Finset.sum_congr rfl
  intro n hn
  unfold SimilarityProfile.pullback
  rw [he n (Nat.le_of_lt_succ (Finset.mem_range.mp hn))]

theorem prefixVelocity_eq_slowVelocity {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {d : Coefficients} (hd : SmoothCoefficients d) {f : SlowExpansionResidual.SlowProfiles}
    (hm : VelocityMatches h d f) (J : ℕ) (C : ℝ)
    {t : ℝ} (ht : t < 1) (x : ProblemStatement.Space)
    (hs : 0 < AxisymmetricFields.radialEnergy x) :
    BaseResidual.prefixVelocity J h C d (t, x) =
      SlowExpansionResidual.slowVelocity J h C f (t, x) := by
  rw [prefixVelocity_eq_profiles hh hh1 hd J C ht x hs]
  have hw := inner_mem_profileWindow hh hh1 (p := AxisymmetricFields.profilePoint t x) ht hs
  have hv : SlowExpansionResidual.slowFlux J h (profiles h d)
      (AxisymmetricFields.profilePoint t x) =
      SlowExpansionResidual.slowFlux J h f (AxisymmetricFields.profilePoint t x) :=
    finiteProfile_eq_of_values J h 0 (fun n _ => hm.flux n hw)
  have hu : SlowExpansionResidual.slowAxial J h (profiles h d)
      (AxisymmetricFields.profilePoint t x) =
      SlowExpansionResidual.slowAxial J h f (AxisymmetricFields.profilePoint t x) :=
    finiteProfile_eq_of_values J h _ (fun n _ => hm.axial n hw)
  have hf : SlowExpansionResidual.slowSwirl J h C (profiles h d)
      (AxisymmetricFields.profilePoint t x) =
      SlowExpansionResidual.slowSwirl J h C f (AxisymmetricFields.profilePoint t x) := by
    exact congrArg (fun r : ℝ => C⁻¹ * r)
      (finiteProfile_eq_of_values J h _ (fun n _ => hm.phi n hw))
  rw [SlowExpansionResidual.slowVelocity_components, SlowExpansionResidual.slowVelocity_components,
    hv, hu, hf]

theorem prefixVelocity_germ {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {d : Coefficients} (hd : SmoothCoefficients d) {f : SlowExpansionResidual.SlowProfiles}
    (hm : VelocityMatches h d f) (J : ℕ) (C : ℝ) {z : ProblemStatement.SpaceTime}
    (hz : z ∈ BaseResidual.annularPast) :
    BaseResidual.prefixVelocity J h C d =ᶠ[𝓝 z] SlowExpansionResidual.slowVelocity J h C f := by
  filter_upwards [BaseResidual.annularPast_isOpen.mem_nhds hz] with w hw
  exact prefixVelocity_eq_slowVelocity hh hh1 hd hm J C hw.1 w.2 hw.2

/-- In the regular radial-quotient convention, the sole radial input is the
proved identity `X * beta = radialFlux`; it determines the finite curl. -/
theorem velocityMatches_of_beta (h : ℝ) (d : Coefficients) (beta : ℕ → Inner → ℝ)
    (hb : ∀ n, ∀ w ∈ profileWindow, w.1 * beta n w =
      SlowDivergence.radialFlux h (SlowExpansionResidual.slowOrder h n) (d.axial n) w) :
    VelocityMatches h d (SlowResidualMatching.ofBeta d.phi d.axial beta d.pressure) where
  phi := fun _ _ _ => rfl
  axial := fun _ _ _ => rfl
  flux := fun n w hw => (hb n w hw).symm

/-- The remaining agreements concern scalar pressure and the actual canonical
stress primitives.  No finite-field or residual identity is an input. -/
structure CoefficientMatches (h C : ℝ) (d : Coefficients)
    (f : SlowExpansionResidual.SlowProfiles) : Prop extends VelocityMatches h d f where
  pressure : ∀ n, EqOn (d.pressure n) (f.pressure n) profileWindow
  stressTheta : ∀ n, EqOn (d.stressTheta n) (SlowResidualMatching.thetaStress h C f n) profileWindow
  stressAxial : ∀ n, EqOn (d.stressAxial n) (SlowResidualMatching.zStress h f n) profileWindow

theorem coefficient_germ {f g : Inner → ℝ} (he : EqOn f g profileWindow)
    {w : Inner} (hw : w ∈ profileWindow) : f =ᶠ[𝓝 w] g := by
  filter_upwards [profileWindow_open.mem_nhds hw] with y hy
  exact he hy

theorem prefixProfile_germ_of_coefficients {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    (J : ℕ) (b : ℝ) {f g : ℕ → Inner → ℝ}
    (he : ∀ n, EqOn (f n) (g n) profileWindow)
    {p : Chart} (ht : p.1 < 1) (hs : 0 < p.2.1) :
    SlowBorelBase.physicalUncutPrefix h b f J =ᶠ[𝓝 p]
      SlowExpansionResidual.finiteProfile J h b g := by
  filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds ht,
    (isOpen_lt continuous_const (continuous_fst.comp continuous_snd)).mem_nhds hs]
    with y hyt hys
  rw [SlowBorelBase.physicalUncutPrefix_eq_finiteProfile hh hh1 b f J hyt]
  exact finiteProfile_eq_of_values J h b (fun n _ => he n (inner_mem_profileWindow hh hh1 hyt hys))

theorem prefixPressure_germ {h C : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {d : Coefficients} {f : SlowExpansionResidual.SlowProfiles}
    (hm : CoefficientMatches h C d f) (J : ℕ) {z : ProblemStatement.SpaceTime}
    (hz : z ∈ BaseResidual.annularPast) :
    BaseResidual.prefixPressure J h C d =ᶠ[𝓝 z] SlowExpansionResidual.slowPressureField J h f := by
  have he := prefixProfile_germ_of_coefficients hh hh1 J (-2 * CoordinateAlgebra.A h)
    (f := SlowBorelBase.bundleComponent C d 2) hm.pressure
    (p := AxisymmetricFields.profilePoint z.1 z.2) hz.1 hz.2
  exact he.comp_tendsto (AxisymmetricFields.contDiff_profilePoint (n := ∞)).continuous.continuousAt

theorem radialDivergence_congr_germ (k : ℝ) {f g : Chart → ℝ} {p : Chart}
    (he : f =ᶠ[𝓝 p] g) :
    LeadingStress.radialDivergence k f p = LeadingStress.radialDivergence k g p := by
  unfold LeadingStress.radialDivergence SimilarityProfile.partialS
  rw [he.eq_of_nhds, he.fderiv_eq]

theorem prefixStressForce_eq {h C : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {d : Coefficients} {f : SlowExpansionResidual.SlowProfiles}
    (hm : CoefficientMatches h C d f) (J : ℕ) {z : ProblemStatement.SpaceTime}
    (hz : z ∈ BaseResidual.annularPast) :
    BaseResidual.prefixStressForce J h C d z =
      SlowResidualMatching.tangentialStressForce
        (SlowResidualMatching.physicalThetaStress J h C f)
        (SlowResidualMatching.physicalZStress J h f) z.1 z.2 := by
  have htheta := prefixProfile_germ_of_coefficients hh hh1 J (-CoordinateAlgebra.A h - 1 / 2)
    (f := SlowBorelBase.bundleComponent C d 3) hm.stressTheta
    (p := AxisymmetricFields.profilePoint z.1 z.2) hz.1 hz.2
  have haxial := prefixProfile_germ_of_coefficients hh hh1 J (-CoordinateAlgebra.A h - 1 / 2)
    (f := SlowBorelBase.bundleComponent C d 4) hm.stressAxial
    (p := AxisymmetricFields.profilePoint z.1 z.2) hz.1 hz.2
  change BaseResidual.prefixStressTheta J h C d =ᶠ[𝓝 (AxisymmetricFields.profilePoint z.1 z.2)]
    SlowResidualMatching.physicalThetaStress J h C f at htheta
  change BaseResidual.prefixStressAxial J h C d =ᶠ[𝓝 (AxisymmetricFields.profilePoint z.1 z.2)]
    SlowResidualMatching.physicalZStress J h f at haxial
  unfold BaseResidual.prefixStressForce BaseResidual.stressForce
    SlowResidualMatching.tangentialStressForce
  rw [radialDivergence_congr_germ 2 htheta, radialDivergence_congr_germ 1 haxial]

theorem VelocityMatches.phi_contDiffAt {h : ℝ} {d : Coefficients}
    (hd : SmoothCoefficients d) {f : SlowExpansionResidual.SlowProfiles}
    (hm : VelocityMatches h d f) (n : ℕ) {w : Inner} (hw : w ∈ profileWindow) :
    ContDiffAt ℝ ∞ (f.phi n) w :=
  (hd.phi n).contDiffAt.congr_of_eventuallyEq (coefficient_germ (hm.phi n) hw).symm

theorem VelocityMatches.axial_contDiffAt {h : ℝ} {d : Coefficients}
    (hd : SmoothCoefficients d) {f : SlowExpansionResidual.SlowProfiles}
    (hm : VelocityMatches h d f) (n : ℕ) {w : Inner} (hw : w ∈ profileWindow) :
    ContDiffAt ℝ ∞ (f.axial n) w :=
  (hd.axial n).contDiffAt.congr_of_eventuallyEq (coefficient_germ (hm.axial n) hw).symm

theorem VelocityMatches.flux_contDiffAt {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {d : Coefficients} (hd : SmoothCoefficients d) {f : SlowExpansionResidual.SlowProfiles}
    (hm : VelocityMatches h d f) (n : ℕ) {w : Inner} (hw : w ∈ profileWindow) :
    ContDiffAt ℝ ∞ (f.flux n) w := by
  have hs : w.2 ^ 2 ≤ 1 := by
    have h1 := hw.2.1
    have h2 := hw.2.2
    linarith [mul_nonneg (show 0 ≤ 1 - w.2 by linarith) (show 0 ≤ 1 + w.2 by linarith)]
  have hL := (CoordinateAlgebra.L_pos hh.le hh1 hs).ne'
  exact (SlowDivergence.radialFlux_smoothAt SlowBorelBase.globalRadialDomain
    (hd.axial n).contDiffOn h (SlowExpansionResidual.slowOrder h n) (mem_univ _)
        hL).congr_of_eventuallyEq
      (coefficient_germ (hm.flux n) hw).symm

theorem CoefficientMatches.pressure_contDiffAt {h C : ℝ} {d : Coefficients}
    (hd : SmoothCoefficients d) {f : SlowExpansionResidual.SlowProfiles}
    (hm : CoefficientMatches h C d f) (n : ℕ) {w : Inner} (hw : w ∈ profileWindow) :
    ContDiffAt ℝ ∞ (f.pressure n) w :=
  (hd.pressure n).contDiffAt.congr_of_eventuallyEq (coefficient_germ (hm.pressure n) hw).symm

/-- The finite identity required by the Borel residual estimates, now derived
from the actual finite potentials and scalar recurrence data. -/
theorem finiteIdentities_of_coefficients {h C : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {d : Coefficients} (hd : SmoothCoefficients d) {f : SlowExpansionResidual.SlowProfiles}
    (hm : CoefficientMatches h C d f)
    (hTheta : ∀ n, SlowStressSupport.Smooth (Ioo (-1) 1) (SlowResidualMatching.thetaDensity h C f
        n))
    (hZ : ∀ n, SlowStressSupport.Smooth (Ioo (-1) 1) (SlowResidualMatching.zDensity h f n))
    (hp : ∀ n, ∀ w ∈ profileWindow, SlowExpansionResidual.pressureCoefficient h C f n w = 0) :
    BaseResidual.FiniteIdentities h C d f := by
  intro J z hz
  have hw := inner_mem_profileWindow hh hh1 (p := AxisymmetricFields.profilePoint z.1 z.2) hz.1 hz.2
  rw [ResidualRegularity.residual_congr (prefixVelocity_germ hh hh1 hd hm.toVelocityMatches J C hz)
    (prefixPressure_germ hh hh1 hm J hz), prefixStressForce_eq hh hh1 hm J hz]
  exact SlowResidualMatching.navierStokesResidual_eq_stress_add_truncation isOpen_Ioo hh hh1 J C f
    (fun n _ => hTheta n) (fun n _ => hZ n) hz.1 hz.2 hw.2
    (fun n _ => (hm.toVelocityMatches.flux_contDiffAt hh hh1 hd n hw).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (fun n _ => (hm.toVelocityMatches.phi_contDiffAt hd n hw).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (fun n _ => (hm.toVelocityMatches.axial_contDiffAt hd n hw).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (fun n _ => (hm.pressure_contDiffAt hd n hw).differentiableAt (by simp))
    (fun n _ => hp n _ hw)

end NavierStokes.BasePrefixIdentity

end
end

end

@[expose] public section

noncomputable section

open Set Filter Function
open scoped ContDiff Topology BigOperators

namespace NavierStokes.ConstructedSlowBase

open GlobalSlowProfiles AssembledSlowBase SlowBorelBase

private theorem parameter_abs_le {eta : ℝ} (h : eta ∈ Ioo (-1 : ℝ) 1) :
    |eta| ≤ 1 := (abs_lt.mpr h).le

/-- Restricting the compact set preserves the very same cutoff schedule. -/
theorem admissibleScales_mono {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a : ℕ → ℕ} {h : ℝ} {f : ℕ → Inner → V} {K K' : Set Inner}
    (ha : AdmissibleScales h f K a) (hK : K' ⊆ K) : AdmissibleScales h f K' a where
  positive := ha.positive
  doubling := ha.doubling
  strictMono := ha.strictMono
  ordinary := fun j hj m hm q hq hq1 w hw => ha.ordinary j hj m hm q hq hq1 w (hK hw)
  blown := fun j hj m hm q hq hq1 w hw => ha.blown j hj m hm q hq hq1 w (hK hw)

/-- The genuine smooth vector potential of the summed base. -/
noncomputable def potential (a : ℕ → ℕ) (h C : ℝ) (d : Coefficients) :
    ProblemStatement.VelocityField :=
  AxisymmetricFields.potential (streamFactor a h C d) (swirlPotential a h C d)

theorem velocity_eq_curl_potential (a : ℕ → ℕ) (h C : ℝ) (d : Coefficients) :
    baseVelocity a h C d = SpatialCurl.spatialCurl (potential a h C d) := rfl

theorem potential_smooth {a : ℕ → ℕ} (ha : StrictMono a) {h : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) {d : Coefficients} (hd : SmoothCoefficients d) (C : ℝ) :
    ContDiffOn ℝ ∞ (potential a h C d) BaseResidual.past :=
  AxisymmetricFields.contDiffOn_potential
    (physicalProfile_smoothOn ha hh hh1 (bundleComponent_smooth hd C 0) _)
    (physicalProfile_smoothOn ha hh hh1 (bundleComponent_smooth hd C 1) _)

section RepairedFamily

variable {S : Set ℝ} {h C rho inner : ℝ} {U : Set ℂ}
  {base : Fin 5 → SimilarityProfile.InnerProfile} {s : Scheme S h C}
  {A : SlowRecursion.LocalHierarchy rho U h C base}
  (L : Localization s A inner) (B0 : BaseAgreement s A inner)
  (Z0 : ZeroOrderSolved s inner) (hI : Icc (-1 : ℝ) 1 ⊆ S)

/-- The only base flux premise is the actual mass reconstruction.  Every
positive-order flux is reconstructed by the global recursion itself. -/
theorem repaired_coefficientMatches
    (hbase : s.base.beta = betaFromU s.domain 0 s.base.axial) :
    BasePrefixIdentity.CoefficientMatches h C (coefficients L B0 Z0 hI) (asSlowProfiles s) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro n w hw
    exact (coefficients_fields_eq L B0 Z0 hI n hw.1.le (parameter_abs_le hw.2)).1
  · intro n w hw
    exact (coefficients_fields_eq L B0 Z0 hI n hw.1.le (parameter_abs_le hw.2)).2.1
  · intro n w hw
    have hb : w.1 * extendedCoefficient s hI n 2 w =
        SlowDivergence.radialFlux h (SlowExpansionResidual.slowOrder h n)
          ((coefficients L B0 Z0 hI).axial n) w := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · have he := extended_flux_zero s hI hbase hw.1.le (parameter_abs_le hw.2)
        simp only [SlowExpansionResidual.slowOrder, Nat.cast_zero, mul_zero, zero_mul] at he ⊢
        exact he
      · exact extended_flux s hI hn hw.1.le (parameter_abs_le hw.2)
    rw [← hb]
    change w.1 * extendedCoefficient s hI n 2 w = w.1 * xProfile (profiles s n).beta w
    rw [extendedCoefficient_eq s hI n 2 hw.1.le (parameter_abs_le hw.2)]
    rfl
  · intro n w hw
    exact (coefficients_fields_eq L B0 Z0 hI n hw.1.le (parameter_abs_le hw.2)).2.2
  · intro n w hw
    exact (coefficients_stress_eq L B0 Z0 hI n hw.1.le (parameter_abs_le hw.2)).1
  · intro n w hw
    exact (coefficients_stress_eq L B0 Z0 hI n hw.1.le (parameter_abs_le hw.2)).2

/-- The finite Cartesian PDE identity is derived from scalar equations and
the actual stream primitives, using the proved finite-prefix bridge. -/
theorem repaired_finiteIdentities (hh : 0 < h) (hh1 : h < 1 / 2)
    (hbase : s.base.beta = betaFromU s.domain 0 s.base.axial)
    (hp : ∀ n, ∀ w ∈ BasePrefixIdentity.profileWindow,
      SlowExpansionResidual.pressureCoefficient h C (asSlowProfiles s) n w = 0) :
    BaseResidual.FiniteIdentities h C (coefficients L B0 Z0 hI) (asSlowProfiles s) := by
  apply BasePrefixIdentity.finiteIdentities_of_coefficients hh hh1
    (coefficients_smooth L B0 Z0 hI) (repaired_coefficientMatches L B0 Z0 hI hbase)
  · intro n
    exact (thetaDensity_smooth L B0 Z0 n).mono
      (fun _ hw => ⟨hw.1, hI ⟨hw.2.1.le, hw.2.2.le⟩⟩)
  · intro n
    exact (zDensity_smooth L B0 Z0 n).mono
      (fun _ hw => ⟨hw.1, hI ⟨hw.2.1.le, hw.2.2.le⟩⟩)
  · exact hp

theorem repaired_stressZeroCore :
    BaseResidual.StressZeroCore (coefficients L B0 Z0 hI) (inner / 8) := by
  intro n X hX eta _
  exact coefficients_stress_zero_left L B0 Z0 hI n hX.2.le

/-- One open coefficient neighborhood contains the whole physical parameter
band and avoids the coordinate denominator's zeros. -/
noncomputable def regularDomain (s : Scheme S h C) (hI : Icc (-1 : ℝ) 1 ⊆ S) : Set Inner :=
  {w | |w.2| < (commonWindow s hI).inner ∧ CoordinateAlgebra.L h w.2 ≠ 0}

theorem regularDomain_open : IsOpen (regularDomain s hI) := by
  have hL : Continuous (fun w : Inner => CoordinateAlgebra.L h w.2) :=
    continuous_const.sub (continuous_const.mul (continuous_snd.pow 2))
  exact (isOpen_lt continuous_snd.abs continuous_const).inter
    (isOpen_ne_fun hL continuous_const)

theorem innerBox_subset_regularDomain (hh : 0 < h) (hh1 : h < 1 / 2) (lo hi : ℝ) :
    innerBox lo hi ⊆ regularDomain s hI := by
  intro w hw
  have he : |w.2| ≤ 1 := abs_le.mpr hw.2
  exact ⟨he.trans_lt (commonWindow s hI).one_lt_inner,
    (CoordinateAlgebra.L_pos hh.le hh1 ((sq_le_one_iff_abs_le_one w.2).mpr he)).ne'⟩

theorem regular_fields_eq (n : ℕ) {w : Inner} (hw : w ∈ regularDomain s hI) (hX : 0 ≤ w.1) :
    (asSlowProfiles s).phi n w = extendedCoefficient s hI n 0 w ∧
    (asSlowProfiles s).axial n w = extendedCoefficient s hI n 1 w ∧
    (asSlowProfiles s).flux n w = w.1 * extendedCoefficient s hI n 2 w := by
  refine ⟨?_, ?_, ?_⟩
  · exact (extendEven_eq (commonWindow s hI) (profiles s n).phi hX hw.1.le).symm
  · exact (extendEven_eq (commonWindow s hI) (profiles s n).axial hX hw.1.le).symm
  · exact congrArg (w.1 * ·)
      (extendEven_eq (commonWindow s hI) (profiles s n).beta hX hw.1.le).symm

/-- Every fixed physical derivative has every requested power of decay,
including on approaches that meet the symmetry axis. -/
theorem repaired_jetRate {l : Filter ProblemStatement.SpaceTime} {a : ℕ → ℕ} {hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (P : BaseResidual.PhysicalApproach l h 0 hi)
    (ha : AdmissibleScales h (coefficientBundle C (coefficients L B0 Z0 hI)) (innerBox 0 hi) a)
    (hf : BaseResidual.FiniteIdentities h C (coefficients L B0 Z0 hI) (asSlowProfiles s))
    (m : ℕ) (n : ℝ) (hn : 0 ≤ n) :
    DiagonalResidual.JetRate l (fun z => (cartesianChart h z).1)
      (BaseResidual.baseResidual a h C (coefficients L B0 Z0 hI)) m n := by
  exact BaseResidual.baseResidual_jetRate_axis hh hh1 P
    (div_pos L.inner_pos (by norm_num)) (coefficients_smooth L B0 Z0 hI)
    (repaired_stressZeroCore L B0 Z0 hI) ha (asSlowProfiles s) hf
    (regularDomain_open hI) (innerBox_subset_regularDomain hI hh hh1 0 hi)
    (fun j => extendedCoefficient s hI j 0) (fun j => extendedCoefficient s hI j 1)
    (fun j => extendedCoefficient s hI j 2)
    (fun j => (extendedCoefficient_contDiff s hI j 0).contDiffOn)
    (fun j => (extendedCoefficient_contDiff s hI j 1).contDiffOn)
    (fun j => (extendedCoefficient_contDiff s hI j 2).contDiffOn)
    (fun j _ hw hx => (regular_fields_eq hI j hw hx).2.2)
    (fun j _ hw hx => (regular_fields_eq hI j hw hx).2.1)
    (fun j _ hw hx => (regular_fields_eq hI j hw hx).1)
    (fun _ hw => hw.2) m n hn

theorem repaired_allJetsFlat {l : Filter ProblemStatement.SpaceTime} {a : ℕ → ℕ} {hi : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (P : BaseResidual.PhysicalApproach l h 0 hi)
    (ha : AdmissibleScales h (coefficientBundle C (coefficients L B0 Z0 hI)) (innerBox 0 hi) a)
    (hf : BaseResidual.FiniteIdentities h C (coefficients L B0 Z0 hI) (asSlowProfiles s)) :
    ResidualStability.AllJetsFlat l (fun z => (cartesianChart h z).1)
      (BaseResidual.baseResidual a h C (coefficients L B0 Z0 hI)) := by
  exact BaseResidual.baseResidual_allJetsFlat_axis hh hh1 P
    (div_pos L.inner_pos (by norm_num)) (coefficients_smooth L B0 Z0 hI)
    (repaired_stressZeroCore L B0 Z0 hI) ha (asSlowProfiles s) hf
    (regularDomain_open hI) (innerBox_subset_regularDomain hI hh hh1 0 hi)
    (fun j => extendedCoefficient s hI j 0) (fun j => extendedCoefficient s hI j 1)
    (fun j => extendedCoefficient s hI j 2)
    (fun j => (extendedCoefficient_contDiff s hI j 0).contDiffOn)
    (fun j => (extendedCoefficient_contDiff s hI j 1).contDiffOn)
    (fun j => (extendedCoefficient_contDiff s hI j 2).contDiffOn)
    (fun j _ hw hx => (regular_fields_eq hI j hw hx).2.2)
    (fun j _ hw hx => (regular_fields_eq hI j hw hx).2.1)
    (fun j _ hw hx => (regular_fields_eq hI j hw hx).1)
    (fun _ hw => hw.2)

/-- Exterior confinement is a consequence of the five repaired rows, not
an extra hypothesis on higher-order stress coefficients. -/
theorem repaired_higherInteriorSupport
    (hbase : s.base.beta = betaFromU s.domain 0 s.base.axial)
    {left right : ℝ} (hl : Real.exp left < inner / 8) (hr : s.B ^ 2 / 2 < Real.exp right) :
    BaseResidual.HigherInteriorSupport (coefficients L B0 Z0 hI) left right := by
  intro n hn
  have he := GlobalStressSupport.raw_stresses_exterior s hbase hn
  have hs := coefficients_stress_support L B0 Z0 hI n s.B_pos.le he.1 he.2
  have hz {w : Inner} (hw : w.1 ∉ Icc (inner / 8) (s.B ^ 2 / 2)) :
      ((coefficients L B0 Z0 hI).stressTheta n w,
        (coefficients L B0 Z0 hI).stressAxial n w) = 0 := by
    by_contra hh
    exact hw (hs (subset_closure hh)).1
  refine ⟨inner / 8, s.B ^ 2 / 2, fun _ hw => ⟨hl.trans_le hw.1, hw.2.trans_lt hr⟩, ?_, ?_⟩
  · intro eta _ X hX
    exact congrArg Prod.fst (hz hX)
  · intro eta _ X hX
    exact congrArg Prod.snd (hz hX)

end RepairedFamily

section Nominal

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)

include W

theorem height_pos : 0 < F.data.h := W.axis.small.h_pos

theorem height_lt_half : F.data.h < 1 / 2 := by linarith [W.axis.small.h_le]

theorem nominal_coefficientMatches :
    BasePrefixIdentity.CoefficientMatches F.data.h W.axis.normalization
      (nominalCoefficients W) (asSlowProfiles (nominalScheme W)) :=
  repaired_coefficientMatches (nominalLocalization W) (nominalBaseAgreement W)
    (nominalZeroOrder W) (nominalParameters_contains W) rfl

theorem nominal_finiteIdentities :
    BaseResidual.FiniteIdentities F.data.h W.axis.normalization
      (nominalCoefficients W) (asSlowProfiles (nominalScheme W)) := by
  apply repaired_finiteIdentities (nominalLocalization W) (nominalBaseAgreement W)
    (nominalZeroOrder W) (nominalParameters_contains W) (height_pos W) (height_lt_half W) rfl
  intro n w hw
  exact nominal_pressureCoefficient W n hw.1
    (nominalParameters_contains W ⟨hw.2.1.le, hw.2.2.le⟩)

theorem nominal_stressZeroCore :
    BaseResidual.StressZeroCore (nominalCoefficients W) (nominalInner W / 8) :=
  repaired_stressZeroCore (nominalLocalization W) (nominalBaseAgreement W)
    (nominalZeroOrder W) (nominalParameters_contains W)

theorem nominal_jetRate {l : Filter ProblemStatement.SpaceTime} {a : ℕ → ℕ} {hi : ℝ}
    (P : BaseResidual.PhysicalApproach l F.data.h 0 hi)
    (ha : AdmissibleScales F.data.h (coefficientBundle W.axis.normalization (nominalCoefficients W))
      (innerBox 0 hi) a) (m : ℕ) (n : ℝ) (hn : 0 ≤ n) :
    DiagonalResidual.JetRate l (fun z => (cartesianChart F.data.h z).1)
      (BaseResidual.baseResidual a F.data.h W.axis.normalization (nominalCoefficients W)) m n :=
  repaired_jetRate (nominalLocalization W) (nominalBaseAgreement W) (nominalZeroOrder W)
    (nominalParameters_contains W) (height_pos W) (height_lt_half W) P ha
    (nominal_finiteIdentities W) m n hn

theorem nominal_allJetsFlat {l : Filter ProblemStatement.SpaceTime} {a : ℕ → ℕ} {hi : ℝ}
    (P : BaseResidual.PhysicalApproach l F.data.h 0 hi)
    (ha : AdmissibleScales F.data.h (coefficientBundle W.axis.normalization (nominalCoefficients W))
      (innerBox 0 hi) a) :
    ResidualStability.AllJetsFlat l (fun z => (cartesianChart F.data.h z).1)
      (BaseResidual.baseResidual a F.data.h W.axis.normalization (nominalCoefficients W)) :=
  repaired_allJetsFlat (nominalLocalization W) (nominalBaseAgreement W) (nominalZeroOrder W)
    (nominalParameters_contains W) (height_pos W) (height_lt_half W) P ha
    (nominal_finiteIdentities W)

theorem nominal_higherInteriorSupport {left right : ℝ}
    (hl : Real.exp left < nominalInner W / 8) (hr : nominalOuterX W < Real.exp right) :
    BaseResidual.HigherInteriorSupport (nominalCoefficients W) left right := by
  apply repaired_higherInteriorSupport (nominalLocalization W) (nominalBaseAgreement W)
    (nominalZeroOrder W) (nominalParameters_contains W) rfl hl
  change nominalOuterRadius W ^ 2 / 2 < Real.exp right
  rwa [nominalOuterRadius_square]

/-- The leading coefficient retains the actual natural axis datum. -/
theorem nominal_leading_axis {eta : ℝ} (heta : eta ∈ Icc (-1 : ℝ) 1) :
    (nominalCoefficients W).axial 0 (0, eta) = 4 * eta + W.axis.j := by
  have h0 : (0 : ℝ) ≤ 4 / W.axis.scale := (div_pos (by norm_num) W.axis.scale_pos).le
  calc
    _ = W.U (0, eta) := (nominalCoefficients_zero_fields W (p := (0, eta)) le_rfl (abs_le.mpr
        heta)).2.1
    _ = W.controls.seedU (0, eta) :=
      (W.seed_agreement (p := (0, eta)) le_rfl NominalProfile.Xi_pos.le).2.1
    _ = W.axis.natural.profile.family.U (0, eta) := (W.controls.seed_initial h0).2
    _ = _ := W.axis.natural.profile.family.natural.U_axis eta
      (NaturalAxisCoefficients.original_interval_interior heta)

theorem nominal_leading_origin : (nominalCoefficients W).axial 0 (0, 0) = W.axis.j := by
  simpa using nominal_leading_axis W (eta := 0) (by constructor <;> norm_num)

theorem nominal_origin {a : ℕ → ℕ} (ha : StrictMono a) {t : ℝ} (ht : t < 1) :
    baseVelocity a F.data.h W.axis.normalization (nominalCoefficients W) (t, 0) =
      ((1 - t) ^ (-CoordinateAlgebra.A F.data.h) * W.axis.j) •
        ProblemStatement.coordinateVector 2 := by
  rw [BaseResidual.baseVelocity_at_origin ha (height_pos W) (height_lt_half W)
    (nominalCoefficients_smooth W) W.axis.normalization
    (fun _ hn => (nominalCoefficients_axis W hn (by norm_num : |(0 : ℝ)| ≤ 1)).2.1) ht,
    nominal_leading_origin]

theorem nominal_axis_tendsto {a : ℕ → ℕ} (ha : StrictMono a) :
    Tendsto (fun t : ℝ => ‖baseVelocity a F.data.h W.axis.normalization (nominalCoefficients W) (t,
        0)‖)
      (𝓝[<] 1) atTop := by
  apply BaseResidual.baseVelocity_axis_tendsto_atTop ha (height_pos W) (height_lt_half W)
    (nominalCoefficients_smooth W) W.axis.normalization
    (fun _ hn => (nominalCoefficients_axis W hn (by norm_num : |(0 : ℝ)| ≤ 1)).2.1)
  rw [nominal_leading_origin]
  exact W.axis.small.j_pos

theorem nominal_speedUnbounded {a : ℕ → ℕ} (ha : StrictMono a) :
    ProblemStatement.SpeedUnboundedAtOne
      (baseVelocity a F.data.h W.axis.normalization (nominalCoefficients W)) :=
  NaturalCore.speedUnbounded_of_axis_tendsto (nominal_axis_tendsto W ha)

theorem nominal_velocity_smooth {a : ℕ → ℕ} (ha : StrictMono a) :
    ContDiffOn ℝ ∞ (baseVelocity a F.data.h W.axis.normalization (nominalCoefficients W))
      BaseResidual.past :=
  baseVelocity_smooth ha (height_pos W) (height_lt_half W) (nominalCoefficients_smooth W)
    W.axis.normalization

theorem nominal_pressure_smooth {a : ℕ → ℕ} (ha : StrictMono a) :
    ContDiffOn ℝ ∞ (basePressure a F.data.h W.axis.normalization (nominalCoefficients W))
      BaseResidual.past :=
  BaseResidual.basePressure_smooth ha (height_pos W) (height_lt_half W)
    (nominalCoefficients_smooth W) W.axis.normalization

theorem nominal_stressForce_smooth {a : ℕ → ℕ} (ha : StrictMono a) :
    ContDiffOn ℝ ∞ (BaseResidual.baseStressForce a F.data.h W.axis.normalization
        (nominalCoefficients W))
      BaseResidual.past :=
  BaseResidual.baseStressForce_smooth_past ha (height_pos W) (height_lt_half W)
    (div_pos (nominalInner_pos W) (by
        norm_num)) (nominalCoefficients_smooth W) (nominal_stressZeroCore W)

theorem nominal_residual_smooth {a : ℕ → ℕ} (ha : StrictMono a) :
    ContDiffOn ℝ ∞ (BaseResidual.baseResidual a F.data.h W.axis.normalization (nominalCoefficients
        W))
      BaseResidual.past :=
  (ResidualRegularity.contDiffOn_residual BaseResidual.past_isOpen
    (nominal_velocity_smooth W ha) (nominal_pressure_smooth W ha)).sub (nominal_stressForce_smooth
        W ha)

theorem nominal_divergence_zero {a : ℕ → ℕ} (ha : StrictMono a) {t : ℝ} (ht : t < 1)
    (x : ProblemStatement.Space) :
    ProblemStatement.spatialDivergence
      (baseVelocity a F.data.h W.axis.normalization (nominalCoefficients W)) t x = 0 :=
  baseVelocity_divergence_zero ha (height_pos W) (height_lt_half W)
    (nominalCoefficients_smooth W) W.axis.normalization ht x

end Nominal

section Modified

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
  {D : ProfileHistories.RadialDomain} (Q : ProfileHistories.Profiles D)
  {S : Set ℝ} {lo hi : ℝ} (M : FiniteModification W Q S lo hi)

include M

theorem modified_coefficientMatches :
    BasePrefixIdentity.CoefficientMatches F.data.h W.axis.normalization
      (modifiedCoefficients W Q M) (asSlowProfiles (modifiedScheme W Q M)) :=
  repaired_coefficientMatches (modifiedLocalization W Q M) (modifiedBaseAgreement W Q M)
    (modifiedZeroOrder W Q M) M.contains rfl

theorem modified_finiteIdentities :
    BaseResidual.FiniteIdentities F.data.h W.axis.normalization
      (modifiedCoefficients W Q M) (asSlowProfiles (modifiedScheme W Q M)) := by
  apply repaired_finiteIdentities (modifiedLocalization W Q M) (modifiedBaseAgreement W Q M)
    (modifiedZeroOrder W Q M) M.contains (height_pos W) (height_lt_half W) rfl
  intro n w hw
  exact modified_pressureCoefficient W Q M n hw.1 (M.contains ⟨hw.2.1.le, hw.2.2.le⟩)

theorem modified_stressZeroCore :
    BaseResidual.StressZeroCore (modifiedCoefficients W Q M) (nominalInner W / 8) :=
  repaired_stressZeroCore (modifiedLocalization W Q M) (modifiedBaseAgreement W Q M)
    (modifiedZeroOrder W Q M) M.contains

theorem modified_jetRate {l : Filter ProblemStatement.SpaceTime} {a : ℕ → ℕ} {upper : ℝ}
    (P : BaseResidual.PhysicalApproach l F.data.h 0 upper)
    (ha : AdmissibleScales F.data.h
      (coefficientBundle W.axis.normalization (modifiedCoefficients W Q M)) (innerBox 0 upper) a)
    (m : ℕ) (n : ℝ) (hn : 0 ≤ n) :
    DiagonalResidual.JetRate l (fun z => (cartesianChart F.data.h z).1)
      (BaseResidual.baseResidual a F.data.h W.axis.normalization (modifiedCoefficients W Q M)) m n
          :=
  repaired_jetRate (modifiedLocalization W Q M) (modifiedBaseAgreement W Q M)
    (modifiedZeroOrder W Q M) M.contains (height_pos W) (height_lt_half W) P ha
    (modified_finiteIdentities W Q M) m n hn

theorem modified_allJetsFlat {l : Filter ProblemStatement.SpaceTime} {a : ℕ → ℕ} {upper : ℝ}
    (P : BaseResidual.PhysicalApproach l F.data.h 0 upper)
    (ha : AdmissibleScales F.data.h
      (coefficientBundle W.axis.normalization (modifiedCoefficients W Q M)) (innerBox 0 upper) a) :
    ResidualStability.AllJetsFlat l (fun z => (cartesianChart F.data.h z).1)
      (BaseResidual.baseResidual a F.data.h W.axis.normalization (modifiedCoefficients W Q M)) :=
  repaired_allJetsFlat (modifiedLocalization W Q M) (modifiedBaseAgreement W Q M)
    (modifiedZeroOrder W Q M) M.contains (height_pos W) (height_lt_half W) P ha
    (modified_finiteIdentities W Q M)

theorem modified_higherInteriorSupport {left right : ℝ}
    (hl : Real.exp left < nominalInner W / 8) (hr : nominalOuterX W < Real.exp right) :
    BaseResidual.HigherInteriorSupport (modifiedCoefficients W Q M) left right := by
  apply repaired_higherInteriorSupport (modifiedLocalization W Q M) (modifiedBaseAgreement W Q M)
    (modifiedZeroOrder W Q M) M.contains rfl hl
  change nominalOuterRadius W ^ 2 / 2 < Real.exp right
  rwa [nominalOuterRadius_square]

theorem modified_leading_axis {eta : ℝ} (heta : eta ∈ Icc (-1 : ℝ) 1) :
    (modifiedCoefficients W Q M).axial 0 (0, eta) = 4 * eta + W.axis.j := by
  calc
    _ = Q.U (0, eta) := (modifiedCoefficients_zero_fields W Q M (p := (0, eta)) le_rfl (abs_le.mpr
        heta)).2.1
    _ = W.U (0, eta) := (M.fields (0, eta) le_rfl (M.contains heta)
      (Or.inl ((nominalInner_pos W).le.trans M.inner))).2
    _ = (nominalCoefficients W).axial 0 (0, eta) :=
      (nominalCoefficients_zero_fields W (p := (0, eta)) le_rfl (abs_le.mpr heta)).2.1.symm
    _ = _ := nominal_leading_axis W heta

theorem modified_leading_origin : (modifiedCoefficients W Q M).axial 0 (0, 0) = W.axis.j := by
  simpa using modified_leading_axis W Q M (eta := 0) (by constructor <;> norm_num)

theorem modified_origin {a : ℕ → ℕ} (ha : StrictMono a) {t : ℝ} (ht : t < 1) :
    baseVelocity a F.data.h W.axis.normalization (modifiedCoefficients W Q M) (t, 0) =
      ((1 - t) ^ (-CoordinateAlgebra.A F.data.h) * W.axis.j) •
        ProblemStatement.coordinateVector 2 := by
  rw [BaseResidual.baseVelocity_at_origin ha (height_pos W) (height_lt_half W)
    (modifiedCoefficients_smooth W Q M) W.axis.normalization
    (fun _ hn => (modifiedCoefficients_axis W Q M hn (by norm_num : |(0 : ℝ)| ≤ 1)).2.1) ht,
    modified_leading_origin]

theorem modified_axis_tendsto {a : ℕ → ℕ} (ha : StrictMono a) :
    Tendsto (fun t : ℝ =>
      ‖baseVelocity a F.data.h W.axis.normalization (modifiedCoefficients W Q M) (t, 0)‖)
      (𝓝[<] 1) atTop := by
  apply BaseResidual.baseVelocity_axis_tendsto_atTop ha (height_pos W) (height_lt_half W)
    (modifiedCoefficients_smooth W Q M) W.axis.normalization
    (fun _ hn => (modifiedCoefficients_axis W Q M hn (by norm_num : |(0 : ℝ)| ≤ 1)).2.1)
  rw [modified_leading_origin]
  exact W.axis.small.j_pos

theorem modified_speedUnbounded {a : ℕ → ℕ} (ha : StrictMono a) :
    ProblemStatement.SpeedUnboundedAtOne
      (baseVelocity a F.data.h W.axis.normalization (modifiedCoefficients W Q M)) :=
  NaturalCore.speedUnbounded_of_axis_tendsto (modified_axis_tendsto W Q M ha)

end Modified

section CommonWeightedSchedule

open BaseResidual ActiveAnnulusWeight

/-- The actual two-slot, all-order weighted estimate, used only as an output
of the coefficient construction and common schedule selection. -/
def WeightedStressBound (a : ℕ → ℕ) (h : ℝ) (d : Coefficients) (c left right : ℝ) : Prop :=
  ∀ m : ℕ, ∃ D : ℝ, 0 < D ∧ ∃ N : ℕ, ∀ q : ℝ, 0 < q → q ≤ 1 →
    ∀ w ∈ activeWindow left right,
      ‖blownJet m (fun v => normalizedTensor a h d v - stressPair d 0 v.2) (q, w)‖ ≤
        D * q ^ h * activeZeta c left right w * (activeDelta left right w)⁻¹ ^ N

/-- This form uses actual derivative bounds on the closed parameter band.
It requires no ambient germ equality to an auxiliary extension at eta=±1. -/
theorem weighted_on_actual_scales {a : ℕ → ℕ} {h C : ℝ} (hh : 0 < h)
    {d : Coefficients} (hd : SmoothCoefficients d) {c left right inner cut : ℝ}
    (hc : 0 < c) (hl : Real.exp left < inner) (hi : inner ≤ cut) (hr : cut < Real.exp right)
    (hs : HigherInteriorSupport d left right)
    (hz : ∀ w : Inner, w.1 < inner → stressPair d 1 w = 0)
    (ho : PolynomialEdgeJets (outerWindow cut right) (activeZeta c left right)
      (activeDelta left right) (stressPair d 1))
    {K : Set Inner} (hK : IsCompact K) (hWK : activeWindow left right ⊆ K)
    (ha : AdmissibleScales h (weightedBundle C d (activeZeta c left right)) K a) :
    WeightedStressBound a h d c left right := by
  let O : Set Inner := Ioo (Real.exp left) (Real.exp right) ×ˢ univ
  have hO : IsOpen O := isOpen_Ioo.prod isOpen_univ
  have hWO : activeWindow left right ⊆ O := fun _ hw => ⟨hw.1, mem_univ _⟩
  exact normalizedTensor_weighted_bound hh hd hK hWK hO hWO
    (activeZeta_smooth hc left right) (fun _ hw => radialWeight_pos hw.1)
    (fun _ hw => activeDelta_bounds hw)
    (edgeJets_of_outer_collar (stressPair_smooth hd 1) hc hl hi hr hz ho)
    (activeZeta_edgeJets (Real.exp_lt_exp.mp ((hl.trans_le hi).trans hr)) hc)
    (higherStressQuotient_smooth_of_support hd hc hs) ha

/-- The terminal amplitude and the normalization of the slow swirl field
are independent constants.  This proof keeps them independent. -/
theorem firstStress_edgeJets (Cedge : ℝ) (tail : OutgoingTail.TailData) (y0 : ℝ)
    {d : Coefficients} (hd : SmoothCoefficients d)
    {c left width inner : ℝ} (hc : 0 < c) (hw : 0 < width)
    (hl : Real.exp left < inner) (hi : inner ≤ Real.exp (y0 + 3 - width))
    (hz : ∀ w : Inner, w.1 < inner → stressPair d 1 w = 0)
    (he : ∀ w ∈ outerWindow (Real.exp (y0 + 3 - width)) (y0 + 3),
      stressPair d 1 =ᶠ[𝓝 w] (fun v => (SlowFirstOrderEdge.stressX Cedge tail y0 v, 0))) :
    PolynomialEdgeJets (activeWindow left (y0 + 3))
      (activeZeta c left (y0 + 3)) (activeDelta left (y0 + 3)) (stressPair d 1) := by
  have hlog : left < y0 + 3 - width := Real.exp_lt_exp.mp (hl.trans_le hi)
  exact edgeJets_of_outer_collar (stressPair_smooth hd 1) hc hl hi
    (Real.exp_lt_exp.mpr (by linarith)) hz
    (firstOrder_pair_outer_edgeJets Cedge tail y0 hc hw hlog he)

/-- Choose one sequence for the actual seven-component stream bundle and
the higher stress quotients.  The weighted estimate is then derived. -/
theorem exists_common_scales_from_primitive {h : ℝ} (hh : 0 < h) (Cbase Cedge : ℝ)
    {d : Coefficients} (hd : SmoothCoefficients d) (tail : OutgoingTail.TailData)
    (y0 : ℝ) {c left width inner : ℝ} (hc : 0 < c) (hw : 0 < width)
    (hl : Real.exp left < inner) (hi : inner ≤ Real.exp (y0 + 3 - width))
    (hs : HigherInteriorSupport d left (y0 + 3))
    (hz : ∀ w : Inner, w.1 < inner → stressPair d 1 w = 0)
    (he : ∀ w ∈ outerWindow (Real.exp (y0 + 3 - width)) (y0 + 3),
      stressPair d 1 =ᶠ[𝓝 w] (fun v => (SlowFirstOrderEdge.stressX Cedge tail y0 v, 0)))
    {K : Set Inner} (hK : IsCompact K) (hWK : activeWindow left (y0 + 3) ⊆ K) (B : ℕ) :
    ∃ a : ℕ → ℕ, B ≤ a 0 ∧
      AdmissibleScales h (weightedBundle Cbase d (activeZeta c left (y0 + 3))) K a ∧
      AdmissibleScales h (coefficientBundle Cbase d) K a ∧
      WeightedStressBound a h d c left (y0 + 3) := by
  have hq := higherStressQuotient_smooth_of_support hd hc hs
  obtain ⟨a, ha0, ha⟩ := exists_admissibleScales (weightedBundle_smooth hd hq Cbase) hh hK B
  refine ⟨a, ha0, ha, weightedBundle_base_scales hd hq ha, ?_⟩
  have hlog : left < y0 + 3 - width := Real.exp_lt_exp.mp (hl.trans_le hi)
  let O : Set Inner := Ioo (Real.exp left) (Real.exp (y0 + 3)) ×ˢ univ
  have hO : IsOpen O := isOpen_Ioo.prod isOpen_univ
  have hWO : activeWindow left (y0 + 3) ⊆ O := fun _ hw => ⟨hw.1, mem_univ _⟩
  exact normalizedTensor_weighted_bound hh hd hK hWK hO hWO
    (activeZeta_smooth hc left (y0 + 3)) (fun _ hw => radialWeight_pos hw.1)
    (fun _ hw => activeDelta_bounds hw)
    (firstStress_edgeJets Cedge tail y0 hd hc hw hl hi hz he)
    (activeZeta_edgeJets (by linarith) hc) hq ha

end CommonWeightedSchedule

section FixedGeometry

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)

/-- Active left, given by `Real.log (nominalInner W / 16)`. -/
noncomputable def activeLeft : ℝ := Real.log (nominalInner W / 16)

/-- Terminal shift, given by `TerminalHistoryBridge.shift F W.controls.radius`. -/
noncomputable def terminalShift : ℝ := TerminalHistoryBridge.shift F W.controls.radius

/-- Active right, given by `terminalShift W + 3`. -/
noncomputable def activeRight : ℝ := terminalShift W + 3

/-- Active upper, given by `Real.exp (activeRight W)`. -/
noncomputable def activeUpper : ℝ := Real.exp (activeRight W)

/-- Scale upper, given by `max upper (activeUpper W)`. -/
noncomputable def scaleUpper (upper : ℝ) : ℝ := max upper (activeUpper W)

theorem exp_activeLeft : Real.exp (activeLeft W) = nominalInner W / 16 :=
  Real.exp_log (div_pos (nominalInner_pos W) (by norm_num))

theorem activeLeft_margin : Real.exp (activeLeft W) < nominalInner W / 8 := by
  rw [exp_activeLeft]
  linarith [nominalInner_pos W]

theorem core_before_outer : nominalInner W / 8 < nominalOuterX W := by
  have hi := (nominalInner_lt_stop W).trans (nominalStop_lt_initial W)
  have ho := (W.controls.Xi_lt_heatJoin W.separated).trans
    (W.controls.heatJoin_lt_radius.trans (nominalOuterX_gt_radius W))
  have hxi := nominalInitial_le_Xi W
  linarith [nominalInner_pos W]

theorem switch_before_collar : BaseExterior.nominalHeatSwitch W < Real.exp (terminalShift W + 2) :=
    by
  change BaseExterior.nominalHeatSwitch W <
    Real.exp (Real.log (BaseExterior.nominalHeatSwitch W) - 1 / 5 + 2)
  calc
    _ = Real.exp (Real.log (BaseExterior.nominalHeatSwitch W)) :=
      (Real.exp_log (BaseExterior.nominalHeatSwitch_pos W)).symm
    _ < _ := Real.exp_lt_exp.mpr (by linarith)

theorem outer_before_collar : nominalOuterX W < Real.exp (terminalShift W + 2) :=
  (nominalOuterX_lt_switch W).trans (switch_before_collar W)

theorem collar_before_upper : Real.exp (terminalShift W + 2) < activeUpper W :=
  Real.exp_lt_exp.mpr (by dsimp [activeUpper, activeRight]; linarith)

theorem outer_before_upper : nominalOuterX W < activeUpper W :=
  (outer_before_collar W).trans (collar_before_upper W)

theorem core_before_collar : nominalInner W / 8 ≤ Real.exp (terminalShift W + 3 - 1) := by
  have hh := (core_before_outer W).trans (outer_before_collar W)
  simpa only [show terminalShift W + 3 - 1 = terminalShift W + 2 by ring] using hh.le

theorem activeLeft_before_collar : activeLeft W < terminalShift W + 2 :=
  Real.exp_lt_exp.mp ((activeLeft_margin W).trans
    ((core_before_outer W).trans (outer_before_collar W)))

theorem activeEdges_ordered : activeLeft W < activeRight W := by
  apply Real.exp_lt_exp.mp
  exact (activeLeft_margin W).trans ((core_before_outer W).trans (outer_before_upper W))

theorem scaleUpper_pos (upper : ℝ) : 0 < scaleUpper W upper :=
  (Real.exp_pos _).trans_le (le_max_right _ _)

theorem activeWindow_subset_box (upper : ℝ) :
    BaseResidual.activeWindow (activeLeft W) (activeRight W) ⊆ innerBox 0 (scaleUpper W upper) := by
  intro w hw
  exact ⟨⟨(Real.exp_pos _).le.trans hw.1.1.le,
    hw.1.2.le.trans (le_max_right upper (activeUpper W))⟩, hw.2⟩

theorem nominal_higher_support :
    BaseResidual.HigherInteriorSupport (nominalCoefficients W) (activeLeft W) (activeRight W) :=
  nominal_higherInteriorSupport W (activeLeft_margin W) (outer_before_upper W)

theorem nominal_quotients_smooth {c : ℝ} (hc : 0 < c) (j : ℕ) :
    ContDiff ℝ ∞ (BaseResidual.higherStressQuotient (nominalCoefficients W)
      (BaseResidual.activeZeta c (activeLeft W) (activeRight W)) j) :=
  BaseResidual.higherStressQuotient_smooth_of_support (nominalCoefficients_smooth W) hc
    (nominal_higher_support W) j

theorem modified_higher_support {D : ProfileHistories.RadialDomain} (Q : ProfileHistories.Profiles
    D)
    {S : Set ℝ} {lo hi : ℝ} (M : FiniteModification W Q S lo hi) :
    BaseResidual.HigherInteriorSupport (modifiedCoefficients W Q M) (activeLeft W) (activeRight W)
        :=
  modified_higherInteriorSupport W Q M (activeLeft_margin W) (outer_before_upper W)

theorem modified_quotients_smooth {D : ProfileHistories.RadialDomain} (Q :
    ProfileHistories.Profiles D)
    {S : Set ℝ} {lo hi : ℝ} (M : FiniteModification W Q S lo hi) {c : ℝ} (hc : 0 < c) (j : ℕ) :
    ContDiff ℝ ∞ (BaseResidual.higherStressQuotient (modifiedCoefficients W Q M)
      (BaseResidual.activeZeta c (activeLeft W) (activeRight W)) j) :=
  BaseResidual.higherStressQuotient_smooth_of_support (modifiedCoefficients_smooth W Q M) hc
    (modified_higher_support W Q M) j

end FixedGeometry

section SelectedSchedules

open BaseResidual

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
  (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ)

/-- This is one actual choice for the enlarged bundle.  The ordinary base
schedule and the weighted stress estimate use this very same function. -/
noncomputable def nominalScales : ℕ → ℕ :=
  Classical.choose (exists_admissibleScales
    (weightedBundle_smooth (nominalCoefficients_smooth W) (nominal_quotients_smooth W hc)
      W.axis.normalization) (height_pos W) (innerBox_isCompact 0 (scaleUpper W upper)) B)

theorem nominalScales_spec : B ≤ nominalScales W c hc upper B 0 ∧
    AdmissibleScales F.data.h
      (weightedBundle W.axis.normalization (nominalCoefficients W)
        (activeZeta c (activeLeft W) (activeRight W)))
      (innerBox 0 (scaleUpper W upper)) (nominalScales W c hc upper B) :=
  Classical.choose_spec (exists_admissibleScales
    (weightedBundle_smooth (nominalCoefficients_smooth W) (nominal_quotients_smooth W hc)
      W.axis.normalization) (height_pos W) (innerBox_isCompact 0 (scaleUpper W upper)) B)

theorem nominalScales_admissible :
    AdmissibleScales F.data.h (coefficientBundle W.axis.normalization (nominalCoefficients W))
      (innerBox 0 (scaleUpper W upper)) (nominalScales W c hc upper B) :=
  weightedBundle_base_scales (nominalCoefficients_smooth W) (nominal_quotients_smooth W hc)
    (nominalScales_spec W c hc upper B).2

theorem nominalScales_strictMono : StrictMono (nominalScales W c hc upper B) :=
  (nominalScales_spec W c hc upper B).2.strictMono

theorem nominalScales_admissible_on {lo hi : ℝ} (hlo : 0 ≤ lo) (hhi : hi ≤ scaleUpper W upper) :
    AdmissibleScales F.data.h (coefficientBundle W.axis.normalization (nominalCoefficients W))
      (innerBox lo hi) (nominalScales W c hc upper B) :=
  admissibleScales_mono (nominalScales_admissible W c hc upper B)
    (fun _ hw => ⟨⟨hlo.trans hw.1.1, hw.1.2.trans hhi⟩, hw.2⟩)

theorem nominalScales_jetRate {l : Filter ProblemStatement.SpaceTime} {hi : ℝ}
    (P : PhysicalApproach l F.data.h 0 hi) (hhi : hi ≤ scaleUpper W upper)
    (m : ℕ) (n : ℝ) (hn : 0 ≤ n) :
    DiagonalResidual.JetRate l (fun z => (cartesianChart F.data.h z).1)
      (baseResidual (nominalScales W c hc upper B) F.data.h W.axis.normalization
        (nominalCoefficients W)) m n :=
  nominal_jetRate W P (nominalScales_admissible_on W c hc upper B le_rfl hhi) m n hn

theorem nominalScales_allJetsFlat {l : Filter ProblemStatement.SpaceTime} {hi : ℝ}
    (P : PhysicalApproach l F.data.h 0 hi) (hhi : hi ≤ scaleUpper W upper) :
    ResidualStability.AllJetsFlat l (fun z => (cartesianChart F.data.h z).1)
      (baseResidual (nominalScales W c hc upper B) F.data.h W.axis.normalization
        (nominalCoefficients W)) :=
  nominal_allJetsFlat W P (nominalScales_admissible_on W c hc upper B le_rfl hhi)

theorem nominalScales_origin {t : ℝ} (ht : t < 1) :
    baseVelocity (nominalScales W c hc upper B) F.data.h W.axis.normalization
      (nominalCoefficients W) (t, 0) =
      ((1 - t) ^ (-CoordinateAlgebra.A F.data.h) * W.axis.j) •
        ProblemStatement.coordinateVector 2 :=
  nominal_origin W (nominalScales_strictMono W c hc upper B) ht

theorem nominalScales_speedUnbounded :
    ProblemStatement.SpeedUnboundedAtOne
      (baseVelocity (nominalScales W c hc upper B) F.data.h W.axis.normalization
          (nominalCoefficients W)) :=
  nominal_speedUnbounded W (nominalScales_strictMono W c hc upper B)

theorem nominalScales_smooth_and_divergence :
    ContDiffOn ℝ ∞
      (baseVelocity (nominalScales W c hc upper B) F.data.h W.axis.normalization
          (nominalCoefficients W)) past ∧
    ContDiffOn ℝ ∞
      (basePressure (nominalScales W c hc upper B) F.data.h W.axis.normalization
          (nominalCoefficients W)) past ∧
    ∀ t < (1 : ℝ), ∀ x : ProblemStatement.Space,
      ProblemStatement.spatialDivergence
        (baseVelocity (nominalScales W c hc upper B) F.data.h W.axis.normalization
          (nominalCoefficients W)) t x = 0 :=
  ⟨nominal_velocity_smooth W (nominalScales_strictMono W c hc upper B),
    nominal_pressure_smooth W (nominalScales_strictMono W c hc upper B),
    fun _ ht x => nominal_divergence_zero W (nominalScales_strictMono W c hc upper B) ht x⟩

theorem nominalScales_potential_smooth :
    ContDiffOn ℝ ∞
      (potential (nominalScales W c hc upper B) F.data.h W.axis.normalization (nominalCoefficients
          W)) past :=
  potential_smooth (nominalScales_strictMono W c hc upper B) (height_pos W) (height_lt_half W)
    (nominalCoefficients_smooth W) W.axis.normalization

theorem nominalScales_tangential_bound {lo hi : ℝ} (hlo : 0 < lo) (hhi : hi ≤ scaleUpper W upper)
    (m : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ q : ℝ, 0 < q → q ≤ 1 → ∀ w ∈ innerBox lo hi,
      ‖blownJet m (fun y =>
        normalizedSwirl (nominalScales W c hc upper B) F.data.h W.axis.normalization
            (nominalCoefficients W) y -
          leadingSwirl W.axis.normalization (nominalCoefficients W) y.2) (q, w)‖ ≤ D * q ^ (2 *
              F.data.h) ∧
      ‖blownJet m (fun y => slowSum (nominalScales W c hc upper B) F.data.h (nominalCoefficients
          W).axial y -
        (nominalCoefficients W).axial 0 y.2) (q, w)‖ ≤ D * q ^ (2 * F.data.h) :=
  normalized_tangential_bounds (height_pos W) hlo (nominalCoefficients_smooth W)
    (nominalScales_admissible_on W c hc upper B hlo.le hhi) m

theorem nominalScales_exterior_residual_zero {z : ProblemStatement.SpaceTime}
    (hz : z ∈ BaseExterior.cartesianExterior F.data.h (BaseExterior.nominalExteriorRadius W)) :
    ProblemStatement.navierStokesResidual
      (baseVelocity (nominalScales W c hc upper B) F.data.h W.axis.normalization
          (nominalCoefficients W))
      (basePressure (nominalScales W c hc upper B) F.data.h W.axis.normalization
          (nominalCoefficients W)) z.1 z.2 = 0 :=
  BaseExterior.nominal_base_residual_zero W (nominalScales_strictMono W c hc upper B) hz

variable {D : ProfileHistories.RadialDomain} (Q : ProfileHistories.Profiles D)
  {S : Set ℝ} {lo hi : ℝ} (M : FiniteModification W Q S lo hi)

/-- The modified family gets one schedule, derived from its actual repaired
coefficients. No stress estimate enters this definition. -/
noncomputable def modifiedScales : ℕ → ℕ :=
  Classical.choose (exists_admissibleScales
    (weightedBundle_smooth (modifiedCoefficients_smooth W Q M) (modified_quotients_smooth W Q M hc)
      W.axis.normalization) (height_pos W) (innerBox_isCompact 0 (scaleUpper W upper)) B)

theorem modifiedScales_spec : B ≤ modifiedScales W c hc upper B Q M 0 ∧
    AdmissibleScales F.data.h
      (weightedBundle W.axis.normalization (modifiedCoefficients W Q M)
        (activeZeta c (activeLeft W) (activeRight W)))
      (innerBox 0 (scaleUpper W upper)) (modifiedScales W c hc upper B Q M) :=
  Classical.choose_spec (exists_admissibleScales
    (weightedBundle_smooth (modifiedCoefficients_smooth W Q M) (modified_quotients_smooth W Q M hc)
      W.axis.normalization) (height_pos W) (innerBox_isCompact 0 (scaleUpper W upper)) B)

theorem modifiedScales_admissible :
    AdmissibleScales F.data.h (coefficientBundle W.axis.normalization (modifiedCoefficients W Q M))
      (innerBox 0 (scaleUpper W upper)) (modifiedScales W c hc upper B Q M) :=
  weightedBundle_base_scales (modifiedCoefficients_smooth W Q M) (modified_quotients_smooth W Q M
      hc)
    (modifiedScales_spec W c hc upper B Q M).2

theorem modifiedScales_strictMono : StrictMono (modifiedScales W c hc upper B Q M) :=
  (modifiedScales_spec W c hc upper B Q M).2.strictMono

theorem modifiedScales_allJetsFlat {l : Filter ProblemStatement.SpaceTime} {radius : ℝ}
    (P : PhysicalApproach l F.data.h 0 radius) (hr : radius ≤ scaleUpper W upper) :
    ResidualStability.AllJetsFlat l (fun z => (cartesianChart F.data.h z).1)
      (baseResidual (modifiedScales W c hc upper B Q M) F.data.h W.axis.normalization
        (modifiedCoefficients W Q M)) :=
  modified_allJetsFlat W Q M P (admissibleScales_mono (modifiedScales_admissible W c hc upper B Q M)
    (fun _ hw => ⟨⟨hw.1.1, hw.1.2.trans hr⟩, hw.2⟩))

theorem modifiedScales_origin {t : ℝ} (ht : t < 1) :
    baseVelocity (modifiedScales W c hc upper B Q M) F.data.h W.axis.normalization
      (modifiedCoefficients W Q M) (t, 0) =
      ((1 - t) ^ (-CoordinateAlgebra.A F.data.h) * W.axis.j) •
        ProblemStatement.coordinateVector 2 :=
  modified_origin W Q M (modifiedScales_strictMono W c hc upper B Q M) ht

theorem modifiedScales_speedUnbounded :
    ProblemStatement.SpeedUnboundedAtOne
      (baseVelocity (modifiedScales W c hc upper B Q M) F.data.h W.axis.normalization
        (modifiedCoefficients W Q M)) :=
  modified_speedUnbounded W Q M (modifiedScales_strictMono W c hc upper B Q M)

theorem modifiedScales_smooth_and_divergence :
    ContDiffOn ℝ ∞
      (baseVelocity (modifiedScales W c hc upper B Q M) F.data.h W.axis.normalization
        (modifiedCoefficients W Q M)) past ∧
    ContDiffOn ℝ ∞
      (basePressure (modifiedScales W c hc upper B Q M) F.data.h W.axis.normalization
        (modifiedCoefficients W Q M)) past ∧
    ∀ t < (1 : ℝ), ∀ x : ProblemStatement.Space,
      ProblemStatement.spatialDivergence
        (baseVelocity (modifiedScales W c hc upper B Q M) F.data.h W.axis.normalization
          (modifiedCoefficients W Q M)) t x = 0 := by
  have ha := modifiedScales_strictMono W c hc upper B Q M
  exact ⟨baseVelocity_smooth ha (height_pos W) (height_lt_half W) (modifiedCoefficients_smooth W Q
      M) _,
    basePressure_smooth ha (height_pos W) (height_lt_half W) (modifiedCoefficients_smooth W Q M) _,
    fun _ ht x => baseVelocity_divergence_zero ha (height_pos W) (height_lt_half W)
      (modifiedCoefficients_smooth W Q M) _ ht x⟩

theorem modifiedScales_potential_smooth :
    ContDiffOn ℝ ∞
      (potential (modifiedScales W c hc upper B Q M) F.data.h W.axis.normalization
        (modifiedCoefficients W Q M)) past :=
  potential_smooth (modifiedScales_strictMono W c hc upper B Q M) (height_pos W) (height_lt_half W)
    (modifiedCoefficients_smooth W Q M) W.axis.normalization

end SelectedSchedules

section ActualWeightedStress

variable {F : OutgoingProfile.Profile} (W : NominalProfile.Witness F)
  (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ)

/-- The actual nominal coefficient supplies the terminal derivative bounds;
the already selected sequence gives the full weighted stress estimate. -/
theorem nominalScales_weighted_bound :
    WeightedStressBound (nominalScales W c hc upper B) F.data.h (nominalCoefficients W)
      c (activeLeft W) (activeRight W) := by
  refine weighted_on_actual_scales (height_pos W) (nominalCoefficients_smooth W) hc
    (activeLeft_margin W) (core_before_collar W) ?_ (nominal_higher_support W) ?_
    (FirstOrderBaseEdge.nominal_first_edgeJets W hc (activeLeft_before_collar W))
    (innerBox_isCompact 0 (scaleUpper W upper)) (activeWindow_subset_box W upper)
    (nominalScales_spec W c hc upper B).2
  · apply Real.exp_lt_exp.mpr
    change terminalShift W + 3 - 1 < terminalShift W + 3
    linarith
  · intro w hw
    have hz := nominalCoefficients_stress_zero W hw.le 1
    exact Prod.ext hz.1 hz.2

variable {D : ProfileHistories.RadialDomain} (Q : ProfileHistories.Profiles D)
  {S : Set ℝ} {lo hi : ℝ} (M : FiniteModification W Q S lo hi)

/-- A finite modification additionally retains its literal angular history.
This fixes the first-order integration constant; the actual modulation
witness proves this equality from its five restored rows. -/
theorem modifiedScales_weighted_bound
    (hI : ∀ eta ∈ S, Q.I (nominalOuterX W, eta) = W.profiles.I (nominalOuterX W, eta)) :
    WeightedStressBound (modifiedScales W c hc upper B Q M) F.data.h (modifiedCoefficients W Q M)
      c (activeLeft W) (activeRight W) := by
  refine weighted_on_actual_scales (height_pos W) (modifiedCoefficients_smooth W Q M) hc
    (activeLeft_margin W) (core_before_collar W) ?_ (modified_higher_support W Q M) ?_
    (FirstOrderBaseEdge.modified_first_edgeJets W Q M hI hc (activeLeft_before_collar W))
    (innerBox_isCompact 0 (scaleUpper W upper)) (activeWindow_subset_box W upper)
    (modifiedScales_spec W c hc upper B Q M).2
  · apply Real.exp_lt_exp.mpr
    change terminalShift W + 3 - 1 < terminalShift W + 3
    linarith
  · intro w hw
    have hz := coefficients_stress_zero_left (modifiedLocalization W Q M) (modifiedBaseAgreement W
        Q M)
      (modifiedZeroOrder W Q M) M.contains 1 hw.le
    exact Prod.ext hz.1 hz.2

end ActualWeightedStress

namespace Modulated

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  {ld : ModulatedProfileAssembly.LoopData W} (v : ModulatedProfileAssembly.Witness ld)

/-- The coefficients are rebuilt from this particular solved finite
modulation, using its preserved histories and its original nominal witness. -/
noncomputable def coefficients : Coefficients :=
  modifiedCoefficients W v.profiles v.finiteModification

theorem coefficients_smooth : SmoothCoefficients (coefficients v) :=
  modifiedCoefficients_smooth W v.profiles v.finiteModification

/-- Scales, given by `modifiedScales W c hc upper B v.profiles v.finiteModification`. -/
noncomputable def scales (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) : ℕ → ℕ :=
  modifiedScales W c hc upper B v.profiles v.finiteModification

theorem scales_spec (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    B ≤ scales v c hc upper B 0 ∧
    AdmissibleScales F.data.h
      (BaseResidual.weightedBundle W.axis.normalization (coefficients v)
        (BaseResidual.activeZeta c (activeLeft W) (activeRight W)))
      (innerBox 0 (scaleUpper W upper)) (scales v c hc upper B) :=
  modifiedScales_spec W c hc upper B v.profiles v.finiteModification

theorem scales_admissible (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    AdmissibleScales F.data.h (coefficientBundle W.axis.normalization (coefficients v))
      (innerBox 0 (scaleUpper W upper)) (scales v c hc upper B) :=
  modifiedScales_admissible W c hc upper B v.profiles v.finiteModification

theorem scales_strictMono (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    StrictMono (scales v c hc upper B) := (scales_spec v c hc upper B).2.strictMono

/-- Velocity, given by `baseVelocity (scales v c hc upper B) F.data.h W.axis.normalization
(coefficients v)`. -/
noncomputable def velocity (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    ProblemStatement.VelocityField :=
  baseVelocity (scales v c hc upper B) F.data.h W.axis.normalization (coefficients v)

/-- Pressure, given by `basePressure (scales v c hc upper B) F.data.h W.axis.normalization
(coefficients v)`. -/
noncomputable def pressure (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    ProblemStatement.PressureField :=
  basePressure (scales v c hc upper B) F.data.h W.axis.normalization (coefficients v)

/-- Stress force, given by `BaseResidual.baseStressForce (scales v c hc upper B) F.data.h
W.axis.normalization (coefficients v)`. -/
noncomputable def stressForce (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    ProblemStatement.SpaceTime → ProblemStatement.Space :=
  BaseResidual.baseStressForce (scales v c hc upper B) F.data.h W.axis.normalization (coefficients
      v)

/-- Error, given by `BaseResidual.baseResidual (scales v c hc upper B) F.data.h
W.axis.normalization (coefficients v)`. -/
noncomputable def error (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    ProblemStatement.SpaceTime → ProblemStatement.Space :=
  BaseResidual.baseResidual (scales v c hc upper B) F.data.h W.axis.normalization (coefficients v)

/-- Vector potential, given by `potential (scales v c hc upper B) F.data.h W.axis.normalization
(coefficients v)`. -/
noncomputable def vectorPotential (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    ProblemStatement.VelocityField :=
  potential (scales v c hc upper B) F.data.h W.axis.normalization (coefficients v)

theorem velocity_eq_curl (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    velocity v c hc upper B = SpatialCurl.spatialCurl (vectorPotential v c hc upper B) := rfl

theorem vectorPotential_smooth (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    ContDiffOn ℝ ∞ (vectorPotential v c hc upper B) BaseResidual.past :=
  modifiedScales_potential_smooth W c hc upper B v.profiles v.finiteModification

theorem smooth_and_divergence (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    ContDiffOn ℝ ∞ (velocity v c hc upper B) BaseResidual.past ∧
    ContDiffOn ℝ ∞ (pressure v c hc upper B) BaseResidual.past ∧
    ∀ t < (1 : ℝ), ∀ x : ProblemStatement.Space,
      ProblemStatement.spatialDivergence (velocity v c hc upper B) t x = 0 :=
  modifiedScales_smooth_and_divergence W c hc upper B v.profiles v.finiteModification

theorem origin (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) {t : ℝ} (ht : t < 1) :
    velocity v c hc upper B (t, 0) =
      ((1 - t) ^ (-CoordinateAlgebra.A F.data.h) * W.axis.j) • ProblemStatement.coordinateVector 2
          :=
  modifiedScales_origin W c hc upper B v.profiles v.finiteModification ht

theorem speedUnbounded (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    ProblemStatement.SpeedUnboundedAtOne (velocity v c hc upper B) :=
  modifiedScales_speedUnbounded W c hc upper B v.profiles v.finiteModification

theorem finiteIdentities :
    BaseResidual.FiniteIdentities F.data.h W.axis.normalization (coefficients v)
      (asSlowProfiles (modifiedScheme W v.profiles v.finiteModification)) :=
  modified_finiteIdentities W v.profiles v.finiteModification

theorem residual_identity (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) (z : ProblemStatement.SpaceTime)
    :
    ProblemStatement.navierStokesResidual (velocity v c hc upper B) (pressure v c hc upper B) z.1
        z.2 =
      stressForce v c hc upper B z + error v c hc upper B z :=
  BaseResidual.baseResidual_identity _ _ _ _ z

theorem error_allJetsFlat (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ)
    {l : Filter ProblemStatement.SpaceTime} {radius : ℝ}
    (P : BaseResidual.PhysicalApproach l F.data.h 0 radius) (hr : radius ≤ scaleUpper W upper) :
    ResidualStability.AllJetsFlat l (fun z => (cartesianChart F.data.h z).1) (error v c hc upper B)
        :=
  modifiedScales_allJetsFlat W c hc upper B v.profiles v.finiteModification P hr

/-- Every finite identity and support input of this weighted estimate is
proved for the same actual modulation witness. -/
theorem weighted_bound (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    WeightedStressBound (scales v c hc upper B) F.data.h (coefficients v)
      c (activeLeft W) (activeRight W) :=
  modifiedScales_weighted_bound W c hc upper B v.profiles v.finiteModification
    (fun _ heta => v.slow_outer_angular heta)

end Modulated

/-- An actual nominal profile and its solved finite modulation are chosen
by the proved finite construction.  The resulting summed base has genuine
Cartesian smoothness, incompressibility, weighted stress, exact axial growth,
and flat error.
There is no profile, PDE identity, or residual estimate among the inputs. -/
theorem exists_actual_base (c : ℝ) (hc : 0 < c) (upper : ℝ) (B : ℕ) :
    ∃ (F : OutgoingProfile.Profile) (W : NominalProfile.Witness F)
      (ld : ModulatedProfileAssembly.LoopData W) (v : ModulatedProfileAssembly.Witness ld),
      (∀ p : Inner, NominalConeAssembly.activeLeft W < p.1 →
        p.1 < NominalConeAssembly.activeRight W → p.2 ∈ Icc (-1 : ℝ) 1 →
        TrueConeLoop.InTrueCone
          (ActivationStocks.profileStockOne v.profiles F.data.h p)
          (ActivationStocks.profileStockTwo v.profiles F.data.h p)
          (ModulatedCone.angularShear v.profiles.E p)
          (ModulatedCone.signedAxialShear v.profiles.E v.profiles.U p)) ∧
      B ≤ Modulated.scales v c hc upper B 0 ∧
      AdmissibleScales F.data.h
        (BaseResidual.weightedBundle W.axis.normalization (Modulated.coefficients v)
          (BaseResidual.activeZeta c (activeLeft W) (activeRight W)))
        (innerBox 0 (scaleUpper W upper)) (Modulated.scales v c hc upper B) ∧
      WeightedStressBound (Modulated.scales v c hc upper B) F.data.h (Modulated.coefficients v)
        c (activeLeft W) (activeRight W) ∧
      ContDiffOn ℝ ∞ (Modulated.velocity v c hc upper B) BaseResidual.past ∧
      ContDiffOn ℝ ∞ (Modulated.pressure v c hc upper B) BaseResidual.past ∧
      (∀ t < (1 : ℝ), ∀ x : ProblemStatement.Space,
        ProblemStatement.spatialDivergence (Modulated.velocity v c hc upper B) t x = 0) ∧
      (∀ t < (1 : ℝ), Modulated.velocity v c hc upper B (t, 0) =
        ((1 - t) ^ (-CoordinateAlgebra.A F.data.h) * W.axis.j) • ProblemStatement.coordinateVector
            2) ∧
      ProblemStatement.SpeedUnboundedAtOne (Modulated.velocity v c hc upper B) ∧
      ∀ (l : Filter ProblemStatement.SpaceTime), BaseResidual.PhysicalApproach l F.data.h 0 upper →
        ResidualStability.AllJetsFlat l (fun z => (cartesianChart F.data.h z).1)
          (Modulated.error v c hc upper B) := by
  obtain ⟨F, W, ld, v, hcone⟩ := ModulatedProfileAssembly.exists_modulated_profile
  have hs := Modulated.smooth_and_divergence v c hc upper B
  exact ⟨F, W, ld, v, hcone, (Modulated.scales_spec v c hc upper B).1,
    (Modulated.scales_spec v c hc upper B).2, Modulated.weighted_bound v c hc upper B,
    hs.1, hs.2.1, hs.2.2,
    fun _ ht => Modulated.origin v c hc upper B ht, Modulated.speedUnbounded v c hc upper B,
    fun _ hp => Modulated.error_allJetsFlat v c hc upper B hp (le_max_left _ _)⟩

end NavierStokes.ConstructedSlowBase
