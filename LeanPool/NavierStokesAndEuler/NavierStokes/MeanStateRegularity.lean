/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.GaugeDebtIncrement

/-!
# Regularity of the actual mean equations on a moving annulus

The inputs below are the individual mean, covariance, base, and virtual
stress fields.  Smoothness, moving support, and torus periodicity of their
actual nonlinear fluxes and differential residuals are consequences.
Base coefficients need smoothness and periodicity only at positive radii.
-/

@[expose] public section


namespace NavierStokes.MeanStateRegularity

noncomputable section

open Set Function Filter
open scoped ContDiff Topology
open MeanIncrementBounds CorrectionState LocalSignedRequest

/-- Plane: an abbreviation for `PressureStream.Plane`. -/
abbrev Plane := PressureStream.Plane
/-- Point: an abbreviation for `PressureStream.Lift Plane`. -/
abbrev Point := PressureStream.Lift Plane
/-- Scalar: an abbreviation for `MeanIncrementBounds.Field Point`. -/
abbrev Scalar := MeanIncrementBounds.Field Point
/-- Tensor: an abbreviation for `Fin 3 → Fin 3 → Scalar`. -/
abbrev Tensor := Fin 3 → Fin 3 → Scalar

/-- Periodicity on the entire fast torus at each allowed slow point. -/
noncomputable def Periodic (U : Set Plane) (f : Scalar) : Prop :=
  ∀ n, PhysicalMeanDomain.PeriodicOn U (f n)

/-- A background coefficient is only used at positive physical radii. -/
noncomputable def PositivePeriodic (U : Set Plane) (f : Scalar) : Prop :=
  ∀ n R, 0 < R → ∀ s, s ∈ U →
    FourierAlias.TorusPeriodic (fun Y => f n (R, (s, Y)))

namespace Periodic

variable {U : Set Plane} {f g : Scalar}

theorem positive (hf : Periodic U f) : PositivePeriodic U f :=
  fun n R _ s hs => hf n R s hs

theorem zero : Periodic U (0 : Scalar) := fun _ _ _ _ _ _ => rfl

theorem add (hf : Periodic U f) (hg : Periodic U g) : Periodic U (f + g) :=
  fun n R s hs Y k => congrArg₂ (· + ·) (hf n R s hs Y k) (hg n R s hs Y k)

theorem neg (hf : Periodic U f) : Periodic U (-f) :=
  fun n R s hs Y k => congrArg Neg.neg (hf n R s hs Y k)

theorem sub (hf : Periodic U f) (hg : Periodic U g) : Periodic U (f - g) :=
  fun n R s hs Y k => congrArg₂ (· - ·) (hf n R s hs Y k) (hg n R s hs Y k)

theorem mul (hf : Periodic U f) (hg : Periodic U g) : Periodic U (f * g) :=
  fun n R s hs Y k => congrArg₂ (· * ·) (hf n R s hs Y k) (hg n R s hs Y k)

theorem smul (hf : Periodic U f) (c : ℝ) : Periodic U (c • f) :=
  fun n R s hs Y k => congrArg (fun t : ℝ => c * t) (hf n R s hs Y k)

theorem band_mul (hf : Periodic U f) (c : ℕ → ℝ) :
    Periodic U (fun n x => c n * f n x) :=
  fun n R s hs Y k => congrArg (fun t : ℝ => c n * t) (hf n R s hs Y k)

/-- Translation invariance of the actual Fréchet derivative is local in
the slow parameter.  No global extension of the field is required. -/
theorem directional (hf : Periodic U f) (hU : IsOpen U) (v : Point) :
    Periodic U (fun n x => fderiv ℝ (f n) x v) := by
  intro n R s hs Y k
  let a : Point := (0, (0, ((k.1 : ℝ), (k.2 : ℝ))))
  have he : (fun x : Point => f n (x + a)) =ᶠ[𝓝 (R, (s, Y))] f n := by
    filter_upwards [(PhysicalMeanDomain.slowDomain_open hU).mem_nhds hs] with x hx
    simpa only [a, Prod.add_def, add_zero] using hf n x.1 x.2.1 hx x.2.2 k
  have hd : fderiv ℝ (fun x : Point => f n (x + a)) (R, (s, Y)) =
      fderiv ℝ (f n) (R, (s, Y)) := he.fderiv_eq
  rw [fderiv_comp_add_right] at hd
  simpa only [a, Prod.add_def, add_zero] using
    congrArg (fun L : Point →L[ℝ] ℝ => L v) hd

end Periodic

/-- The native graph coefficient is smooth and periodic where it can be
multiplied by a supported mean field. -/
structure OperatorData (U : Set Plane) (o : Operators Point) : Prop where
  regular : LocalRankDefect.LocalOperators U o
  profile_periodic : PositivePeriodic U (fun _ => o.radialProfile)

namespace OperatorData

variable {U : Set Plane} {o : Operators Point}

theorem inv_periodic (ho : OperatorData U o) : PositivePeriodic U o.invRadius := by
  intro n R hR s hs Y k
  simp only [Operators.invRadius, ho.regular.radius_eq]

/-- The actual reconstruction operators meet the primitive hypotheses. -/
theorem native (U : Set Plane) (r : ReconstructionData) (ε fast : ℕ → ℝ)
    (z t v : Plane) : OperatorData U (StateMomentBalances.nativeOperators r ε fast z t v) := by
  refine ⟨⟨rfl, ?_⟩, fun _ _ _ _ _ _ _ => rfl⟩
  exact (StateMomentBalances.nativeOperators_positive r ε fast z t v).radialProfile.mono
    (fun _ hx => hx.1)

end OperatorData

namespace MovingField

variable {coord a b : ℝ} {U : SlowRegion coord} {f g : Scalar}

theorem regular (hf : GaugeMomentBalances.MovingField U a b f) :
    GaugeDebtIncrement.Regular U a b f := ⟨hf.smooth, hf.supported⟩

theorem of_regular (hf : GaugeDebtIncrement.Regular U a b f) (hp : Periodic U.carrier f) :
    GaugeMomentBalances.MovingField U a b f := ⟨hf.smooth, hf.supported, hp⟩

theorem zero : GaugeMomentBalances.MovingField U a b (0 : Scalar) :=
  of_regular GaugeDebtIncrement.Regular.zero Periodic.zero

theorem add (hf : GaugeMomentBalances.MovingField U a b f)
    (hg : GaugeMomentBalances.MovingField U a b g) :
    GaugeMomentBalances.MovingField U a b (f + g) :=
  of_regular ((regular hf).add (regular hg)) (Periodic.add hf.periodic hg.periodic)

theorem neg (hf : GaugeMomentBalances.MovingField U a b f) :
    GaugeMomentBalances.MovingField U a b (-f) :=
  of_regular (regular hf).neg (Periodic.neg hf.periodic)

theorem sub (hf : GaugeMomentBalances.MovingField U a b f)
    (hg : GaugeMomentBalances.MovingField U a b g) :
    GaugeMomentBalances.MovingField U a b (f - g) :=
  of_regular ((regular hf).sub (regular hg)) (Periodic.sub hf.periodic hg.periodic)

theorem mul (hf : GaugeMomentBalances.MovingField U a b f)
    (hg : GaugeMomentBalances.MovingField U a b g) :
    GaugeMomentBalances.MovingField U a b (f * g) :=
  of_regular ((regular hf).mul (regular hg)) (Periodic.mul hf.periodic hg.periodic)

theorem smul (hf : GaugeMomentBalances.MovingField U a b f) (c : ℝ) :
    GaugeMomentBalances.MovingField U a b (c • f) :=
  of_regular ((regular hf).smul c) (Periodic.smul hf.periodic c)

theorem band_mul (hf : GaugeMomentBalances.MovingField U a b f) (c : ℕ → ℝ) :
    GaugeMomentBalances.MovingField U a b (fun n x => c n * f n x) :=
  of_regular ((regular hf).band_mul c) (Periodic.band_mul hf.periodic c)

theorem directional (hf : GaugeMomentBalances.MovingField U a b f) (v : Point) :
    GaugeMomentBalances.MovingField U a b (fun n x => fderiv ℝ (f n) x v) :=
  of_regular ((regular hf).directional v) (Periodic.directional hf.periodic U.isOpen v)

/-- The base is not assumed smooth or periodic through the axis.  The
supported factor is identically zero there and below it. -/
theorem coefficient_mul (hf : GaugeMomentBalances.MovingField U a b f)
    (ha : 0 < a) (hab : a < b)
    (hg : SmoothOn (LocalRankDefect.positiveDomain U.carrier) g)
    (hp : PositivePeriodic U.carrier g) : GaugeMomentBalances.MovingField U a b (g * f) := by
  apply of_regular ((regular hf).coefficient_mul ha hab hg)
  intro n R s hs Y k
  by_cases hR : 0 < R
  · exact congrArg₂ (· * ·) (hp n R hR s hs Y k) (hf.periodic n R s hs Y k)
  · have hz (Y : Plane) : f n (R, (s, Y)) = 0 :=
      (regular hf).zero_of_nonpositive ha n hs (le_of_not_gt hR)
    simp only [Pi.mul_apply, hz, mul_zero]

theorem mul_coefficient (hf : GaugeMomentBalances.MovingField U a b f)
    (ha : 0 < a) (hab : a < b)
    (hg : SmoothOn (LocalRankDefect.positiveDomain U.carrier) g)
    (hp : PositivePeriodic U.carrier g) : GaugeMomentBalances.MovingField U a b (f * g) := by
  simpa only [mul_comm] using coefficient_mul hf ha hab hg hp

theorem dr (hf : GaugeMomentBalances.MovingField U a b f) (ha : 0 < a) (hab : a < b)
    {o : Operators Point} (ho : OperatorData U.carrier o) :
    GaugeMomentBalances.MovingField U a b (o.dr f) :=
  add (directional hf o.eR)
    (band_mul (coefficient_mul (directional hf o.vR) ha hab
      (fun _ => ho.regular.radialProfile) ho.profile_periodic) o.radialFrequency)

theorem dz (hf : GaugeMomentBalances.MovingField U a b f) (o : Operators Point) :
    GaugeMomentBalances.MovingField U a b (o.dz f) :=
  band_mul (directional hf o.eZ) o.epsilon

theorem time (hf : GaugeMomentBalances.MovingField U a b f) (o : Operators Point) :
    GaugeMomentBalances.MovingField U a b (o.time f) :=
  add (neg (band_mul (directional hf o.eT) o.epsilon))
    (band_mul (directional hf o.vT) o.fastCoefficient)

theorem inv_mul (hf : GaugeMomentBalances.MovingField U a b f) (ha : 0 < a) (hab : a < b)
    {o : Operators Point} (ho : OperatorData U.carrier o) :
    GaugeMomentBalances.MovingField U a b (o.invRadius * f) :=
  coefficient_mul hf ha hab ho.regular.invRadius_smooth ho.inv_periodic

theorem radialDiv (hf : GaugeMomentBalances.MovingField U a b f)
    (ha : 0 < a) (hab : a < b) {o : Operators Point} (ho : OperatorData U.carrier o) (c : ℝ) :
    GaugeMomentBalances.MovingField U a b (o.radialDiv c f) :=
  add (dr hf ha hab ho) (smul (inv_mul hf ha hab ho) c)

theorem viscosity (hf : GaugeMomentBalances.MovingField U a b f)
    (ha : 0 < a) (hab : a < b) {o : Operators Point} (ho : OperatorData U.carrier o) (c : ℝ) :
    GaugeMomentBalances.MovingField U a b (o.viscosity c f) :=
  band_mul (sub (add (add (dr (dr hf ha hab ho) ha hab ho)
    (inv_mul (dr hf ha hab ho) ha hab ho)) (dz (dz hf o) o))
    (smul (inv_mul (inv_mul hf ha hab ho) ha hab ho) c)) o.epsilon

/-- The moving physical interval is exactly the normalized support used
by the signed-stress request. -/
theorem movingSupport (hf : GaugeMomentBalances.MovingField U a b f) (n : ℕ) :
    LocalSignedRequest.MovingSupport a b coord U.carrier (f n) := by
  intro x hx hn
  have hs := hf.supported n x hx hn
  have hl := VariableGaugeMean.qLength_pos U.coord_pos U.coord_lt_one (U.time_pos _ hx)
  change x.1 / VariableGaugeMean.qLength coord x.2.1 ∈ Icc a b
  exact ⟨(le_div_iff₀ hl).mpr (by simpa only [mul_comm] using hs.1),
    (div_le_iff₀ hl).mpr (by simpa only [mul_comm] using hs.2)⟩

end MovingField

/-- Primitive base regularity on the positive-radius domain. -/
structure BaseData (U : Set Plane) (b : Triple Point) : Prop where
  smooth : SmoothTriple (LocalRankDefect.positiveDomain U) b
  radial_periodic : PositivePeriodic U b.radial
  angular_periodic : PositivePeriodic U b.angular
  axial_periodic : PositivePeriodic U b.axial

/-- Periodic triple data, collecting `radial`, `angular`, `axial`. -/
structure PeriodicTriple (U : Set Plane) (m : Triple Point) : Prop where
  radial : Periodic U m.radial
  angular : Periodic U m.angular
  axial : Periodic U m.axial

theorem BaseData.of_periodic {U : Set Plane} {b : Triple Point}
    (hb : SmoothTriple (LocalRankDefect.positiveDomain U) b) (hp : PeriodicTriple U b) :
    BaseData U b := ⟨hb, hp.radial.positive, hp.angular.positive, hp.axial.positive⟩

/-- Moving triple data, collecting `radial`, `angular`, `axial`. -/
structure MovingTriple {coord : ℝ} (U : SlowRegion coord) (a b : ℝ) (m : Triple Point) : Prop where
  radial : GaugeMomentBalances.MovingField U a b m.radial
  angular : GaugeMomentBalances.MovingField U a b m.angular
  axial : GaugeMomentBalances.MovingField U a b m.axial

namespace MovingTriple

variable {coord a b : ℝ} {U : SlowRegion coord} {m h base : Triple Point}

theorem of_regular (hm : GaugeDebtIncrement.RegularTriple U a b m)
    (hp : PeriodicTriple U.carrier m) : MovingTriple U a b m :=
  ⟨MovingField.of_regular hm.radial hp.radial,
    MovingField.of_regular hm.angular hp.angular, MovingField.of_regular hm.axial hp.axial⟩

theorem regular (hm : MovingTriple U a b m) : GaugeDebtIncrement.RegularTriple U a b m :=
  ⟨MovingField.regular hm.radial, MovingField.regular hm.angular, MovingField.regular hm.axial⟩

theorem periodic (hm : MovingTriple U a b m) : PeriodicTriple U.carrier m :=
  ⟨hm.radial.periodic, hm.angular.periodic, hm.axial.periodic⟩

theorem updated (hm : MovingTriple U a b m) (hh : MovingTriple U a b h) :
    MovingTriple U a b (MeanIncrementBounds.updated m h) :=
  ⟨MovingField.add hm.radial hh.radial, MovingField.add hm.angular hh.angular,
    MovingField.add hm.axial hh.axial⟩

theorem thetaRadial (hm : MovingTriple U a b m) (ha : 0 < a) (hab : a < b)
    (hb : BaseData U.carrier base) :
    GaugeMomentBalances.MovingField U a b (MeanIncrementBounds.thetaRadial base m) :=
  MovingField.add (MovingField.add
    (MovingField.coefficient_mul hm.angular ha hab hb.smooth.radial hb.radial_periodic)
    (MovingField.mul_coefficient hm.radial ha hab hb.smooth.angular hb.angular_periodic))
    (MovingField.mul hm.radial hm.angular)

theorem thetaAxial (hm : MovingTriple U a b m) (ha : 0 < a) (hab : a < b)
    (hb : BaseData U.carrier base) :
    GaugeMomentBalances.MovingField U a b (MeanIncrementBounds.thetaAxial base m) :=
  MovingField.add (MovingField.add
    (MovingField.coefficient_mul hm.angular ha hab hb.smooth.axial hb.axial_periodic)
    (MovingField.coefficient_mul hm.axial ha hab hb.smooth.angular hb.angular_periodic))
    (MovingField.mul hm.axial hm.angular)

theorem axialRadial (hm : MovingTriple U a b m) (ha : 0 < a) (hab : a < b)
    (hb : BaseData U.carrier base) :
    GaugeMomentBalances.MovingField U a b (MeanIncrementBounds.axialRadial base m) :=
  MovingField.add (MovingField.add
    (MovingField.coefficient_mul hm.axial ha hab hb.smooth.radial hb.radial_periodic)
    (MovingField.mul_coefficient hm.radial ha hab hb.smooth.axial hb.axial_periodic))
    (MovingField.mul hm.radial hm.axial)

theorem axialAxial (hm : MovingTriple U a b m) (ha : 0 < a) (hab : a < b)
    (hb : BaseData U.carrier base) :
    GaugeMomentBalances.MovingField U a b (MeanIncrementBounds.axialAxial base m) :=
  MovingField.add
    (MovingField.smul (MovingField.coefficient_mul hm.axial ha hab hb.smooth.axial
        hb.axial_periodic) 2)
    (MovingField.mul hm.axial hm.axial)

theorem radialRadial (hm : MovingTriple U a b m) (ha : 0 < a) (hab : a < b)
    (hb : BaseData U.carrier base) :
    GaugeMomentBalances.MovingField U a b (MeanIncrementBounds.radialRadial base m) :=
  MovingField.add
    (MovingField.smul (MovingField.coefficient_mul hm.radial ha hab hb.smooth.radial
        hb.radial_periodic) 2)
    (MovingField.mul hm.radial hm.radial)

theorem radialAngular (hm : MovingTriple U a b m) (ha : 0 < a) (hab : a < b)
    (hb : BaseData U.carrier base) :
    GaugeMomentBalances.MovingField U a b (MeanIncrementBounds.radialAngular base m) :=
  MovingField.add
    (MovingField.smul (MovingField.coefficient_mul hm.angular ha hab hb.smooth.angular
        hb.angular_periodic) 2)
    (MovingField.mul hm.angular hm.angular)

theorem thetaResidual (hm : MovingTriple U a b m) (ha : 0 < a) (hab : a < b)
    (hb : BaseData U.carrier base) {o : Operators Point} (ho : OperatorData U.carrier o)
    {W : Tensor} (hW : ∀ i j, GaugeMomentBalances.MovingField U a b (W i j))
    {T : Scalar} (hT : GaugeMomentBalances.MovingField U a b T) :
    GaugeMomentBalances.MovingField U a b (MeanIncrementBounds.thetaResidual o base m W T) := by
  have hR := MovingField.add (hm.thetaRadial ha hab hb) (hW 0 1)
  have hZ := MovingField.add (hm.thetaAxial ha hab hb) (hW 2 1)
  exact MovingField.sub (MovingField.sub
    (MovingField.add (MovingField.add (MovingField.time hm.angular o)
      (MovingField.radialDiv hR ha hab ho 2)) (MovingField.dz hZ o))
    (MovingField.viscosity hm.angular ha hab ho 1)) (MovingField.radialDiv hT ha hab ho 2)

theorem axialResidual (hm : MovingTriple U a b m) (ha : 0 < a) (hab : a < b)
    (hb : BaseData U.carrier base) {o : Operators Point} (ho : OperatorData U.carrier o)
    {W : Tensor} (hW : ∀ i j, GaugeMomentBalances.MovingField U a b (W i j))
    {p T : Scalar} (hp : GaugeMomentBalances.MovingField U a b p)
    (hT : GaugeMomentBalances.MovingField U a b T) :
    GaugeMomentBalances.MovingField U a b (MeanIncrementBounds.axialResidual o base m W p T) := by
  have hR := MovingField.add (hm.axialRadial ha hab hb) (hW 0 2)
  have hZ := MovingField.add (MovingField.add (hm.axialAxial ha hab hb) (hW 2 2)) hp
  exact MovingField.sub (MovingField.sub
    (MovingField.add (MovingField.add (MovingField.time hm.axial o)
      (MovingField.radialDiv hR ha hab ho 1)) (MovingField.dz hZ o))
    (MovingField.viscosity hm.axial ha hab ho 0)) (MovingField.radialDiv hT ha hab ho 1)

theorem gr (hm : MovingTriple U a b m) (ha : 0 < a) (hab : a < b)
    (hb : BaseData U.carrier base) {o : Operators Point} (ho : OperatorData U.carrier o)
    {W : Tensor} (hW : ∀ i j, GaugeMomentBalances.MovingField U a b (W i j)) :
    GaugeMomentBalances.MovingField U a b (MeanIncrementBounds.gr o base m W) := by
  have hR := MovingField.add (hm.radialRadial ha hab hb) (hW 0 0)
  have hZ := MovingField.add (hm.axialRadial ha hab hb) (hW 2 0)
  have hA := MovingField.add (hm.radialAngular ha hab hb) (hW 1 1)
  exact MovingField.neg (MovingField.sub (MovingField.sub
    (MovingField.add (MovingField.add (MovingField.time hm.radial o)
      (MovingField.radialDiv hR ha hab ho 1)) (MovingField.dz hZ o))
    (MovingField.inv_mul hA ha hab ho)) (MovingField.viscosity hm.radial ha hab ho 1))

end MovingTriple

/-- Only the individual incoming fields are constrained.  No residual,
flux, pressure reconstruction, or quantitative class bound is an input. -/
structure PrimitiveData {coord : ℝ} (U : SlowRegion coord) (a b : ℝ)
    (c : Context Point) (u : State Point) : Prop where
  operators : OperatorData U.carrier c.operators
  base : BaseData U.carrier c.base
  mean : MovingTriple U a b u.mean
  covariance : ∀ i j, GaugeMomentBalances.MovingField U a b (u.covariance i j)
  virtualTheta : GaugeMomentBalances.MovingField U a b c.virtualTheta
  virtualAxial : GaugeMomentBalances.MovingField U a b c.virtualAxial

namespace PrimitiveData

variable {coord a b : ℝ} {U : SlowRegion coord} {c : Context Point} {u : State Point}

theorem of_regular (ho : OperatorData U.carrier c.operators) (hb : BaseData U.carrier c.base)
    (hm : GaugeDebtIncrement.RegularTriple U a b u.mean) (hmp : PeriodicTriple U.carrier u.mean)
    (hW : ∀ i j, GaugeDebtIncrement.Regular U a b (u.covariance i j))
    (hWp : ∀ i j, Periodic U.carrier (u.covariance i j))
    (hT : GaugeMomentBalances.MovingField U a b c.virtualTheta)
    (hZ : GaugeMomentBalances.MovingField U a b c.virtualAxial) : PrimitiveData U a b c u :=
  ⟨ho, hb, MovingTriple.of_regular hm hmp,
    fun i j => MovingField.of_regular (hW i j) (hWp i j), hT, hZ⟩

theorem angular_flux (H : PrimitiveData U a b c u) (ha : 0 < a) (hab : a < b) :
    GaugeMomentBalances.MovingAngularInputs U a b c u :=
  ⟨H.mean.angular,
    MovingField.add (H.mean.thetaRadial ha hab H.base) (H.covariance 0 1),
    MovingField.add (H.mean.thetaAxial ha hab H.base) (H.covariance 2 1), H.virtualTheta⟩

theorem axial_flux (H : PrimitiveData U a b c u) (ha : 0 < a) (hab : a < b) :
    GaugeMomentBalances.MovingAxialInputs U a b c u :=
  ⟨H.mean.axial,
    MovingField.add (H.mean.axialRadial ha hab H.base) (H.covariance 0 2),
    MovingField.add (H.mean.axialAxial ha hab H.base) (H.covariance 2 2), H.virtualAxial⟩

theorem source (H : PrimitiveData U a b c u) (ha : 0 < a) (hab : a < b) :
    GaugeMomentBalances.MovingField U a b (u.gr c) :=
  H.mean.gr ha hab H.base H.operators H.covariance

theorem theta (H : PrimitiveData U a b c u) (ha : 0 < a) (hab : a < b) :
    GaugeMomentBalances.MovingField U a b (u.thetaResidual c) :=
  H.mean.thetaResidual ha hab H.base H.operators H.covariance H.virtualTheta

theorem axial (H : PrimitiveData U a b c u) (ha : 0 < a) (hab : a < b)
    (hp : GaugeMomentBalances.MovingField U a b u.pressure) :
    GaugeMomentBalances.MovingField U a b (u.axialResidual c) :=
  H.mean.axialResidual ha hab H.base H.operators H.covariance hp H.virtualAxial

/-- A reconstructed incoming state needs no separate regularity premise
on its pressure. -/
theorem pressure {g : VariableGaugeMean.GaugeData Plane}
    (H : PrimitiveData U g.radial.inner g.radial.outer c u)
    (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent)
    (hg : ∀ n, g.length n = VariableGaugeMean.qLength coord)
    (hfixed : (VariableGaugeMean.reconstructState g c u).pressure = u.pressure) :
    GaugeMomentBalances.MovingField U g.radial.inner g.radial.outer u.pressure := by
  have hp := GaugeMomentBalances.pressureRecipe_movingField U g ha hd hg c u
    (H.source ha g.radial.inner_lt_outer)
  simpa only [GaugeMomentBalances.pressureRecipe, hfixed] using hp

theorem axial_reconstructed {g : VariableGaugeMean.GaugeData Plane}
    (H : PrimitiveData U g.radial.inner g.radial.outer c u)
    (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent)
    (hg : ∀ n, g.length n = VariableGaugeMean.qLength coord)
    (hfixed : (VariableGaugeMean.reconstructState g c u).pressure = u.pressure) :
    GaugeMomentBalances.MovingField U g.radial.inner g.radial.outer (u.axialResidual c) :=
  H.axial ha g.radial.inner_lt_outer (H.pressure ha hd hg hfixed)

/-- The same primitive fields after adding the actual wave covariance
increment.  The pressure is still obtained by the genuine reconstruction. -/
theorem waveStage (H : PrimitiveData U a b c u) (g : VariableGaugeMean.GaugeData Plane)
    (w : Oscillation Point) (q : OscillatoryScalar Point) (gaussian : Oscillation Point)
    (hX : ∀ i j, GaugeMomentBalances.MovingField U a b
      (SignedMeanGain.covarianceIncrement u.oscillation w i j)) :
    PrimitiveData U a b c (SignedMeanGain.waveStage g c u w q gaussian) := by
  refine ⟨H.operators, H.base, ?_, ?_, H.virtualTheta, H.virtualAxial⟩
  · rw [SignedMeanGain.waveStage_mean]
    exact H.mean
  · intro i j
    rw [SignedMeanGain.waveStage_covariance]
    exact MovingField.add (H.covariance i j) (hX i j)

theorem waveStage_of_regular (H : PrimitiveData U a b c u) (g : VariableGaugeMean.GaugeData Plane)
    (w : Oscillation Point) (q : OscillatoryScalar Point) (gaussian : Oscillation Point)
    (hX : ∀ i j, GaugeDebtIncrement.Regular U a b
      (SignedMeanGain.covarianceIncrement u.oscillation w i j))
    (hXp : ∀ i j, Periodic U.carrier (SignedMeanGain.covarianceIncrement u.oscillation w i j)) :
    PrimitiveData U a b c (SignedMeanGain.waveStage g c u w q gaussian) :=
  H.waveStage g w q gaussian (fun i j => MovingField.of_regular (hX i j) (hXp i j))

end PrimitiveData

/-! ## Direct assembly of the signed mean-stage inputs -/

/-- All residual, flux, and source regularity fields of `LocalData` follow
from primitive data.  Reconstruction and the two mass identities are the
actual state invariants, not regularity premises. -/
theorem localData (G : SignedMeanGain.Geometry) (c : Context Point) (u : State Point)
    (w : Oscillation Point) (q : OscillatoryScalar Point) (gaussian : Oscillation Point)
    (H : PrimitiveData G.region G.patch.a G.patch.b c u)
    (ho : c.operators = G.operators)
    (hX : ∀ i j, GaugeMomentBalances.MovingField G.region G.patch.a G.patch.b
      (SignedMeanGain.covarianceIncrement u.oscillation w i j))
    (hfixed : VariableGaugeMean.reconstructState G.gauge c u = u)
    (hmθ : ∀ n s, s ∈ G.region.carrier → radialMoment 2 u.mean.angular n s = 0)
    (hmz : ∀ n s, s ∈ G.region.carrier → radialMoment 1 u.mean.axial n s = 0) :
    SignedMeanGain.LocalData G c u w q gaussian := by
  have Hg : PrimitiveData G.region G.gauge.radial.inner G.gauge.radial.outer c u := by
    simpa only [G.inner_eq, G.outer_eq] using H
  have hp : GaugeMomentBalances.MovingField G.region G.patch.a G.patch.b u.pressure := by
    simpa only [G.inner_eq, G.outer_eq] using
      Hg.pressure G.inner_pos G.exponent_pos G.length_eq
        (congrArg (fun s : State Point => s.pressure) hfixed)
  have hθ := H.theta G.patch.a_pos G.patch.a_lt_b
  have hz := H.axial G.patch.a_pos G.patch.a_lt_b hp
  exact
    { operators_eq := ho
      base := GaugeDebtIncrement.smoothTriple_mono H.base.smooth
        (fun _ hx => ⟨G.strip_radius_pos hx, G.strip_subset hx⟩)
      mean := GaugeDebtIncrement.smoothTriple_mono H.mean.regular.smooth G.strip_subset
      covariance := fun i j n => ((H.covariance i j).smooth n).mono G.strip_subset
      theta := hθ.smooth
      axial := hz.smooth
      theta_support := MovingField.movingSupport hθ
      axial_support := MovingField.movingSupport hz
      angular_flux := H.angular_flux G.patch.a_pos G.patch.a_lt_b
      axial_flux := H.axial_flux G.patch.a_pos G.patch.a_lt_b
      source := H.source G.patch.a_pos G.patch.a_lt_b
      updated_source := (H.waveStage G.gauge w q gaussian hX).source
        G.patch.a_pos G.patch.a_lt_b
      reconstructed := hfixed
      angular_mass := hmθ
      axial_mass := hmz }

/-- The regularity endpoint for the actual covariance increment, including
the one supplied by `WaveStateRegularity`, combines with primitive
periodicity and supplies the complete signed-stage input record. -/
theorem localData_of_regular (G : SignedMeanGain.Geometry) (c : Context Point) (u : State Point)
    (w : Oscillation Point) (q : OscillatoryScalar Point) (gaussian : Oscillation Point)
    (H : PrimitiveData G.region G.patch.a G.patch.b c u)
    (ho : c.operators = G.operators)
    (hX : ∀ i j, GaugeDebtIncrement.Regular G.region G.patch.a G.patch.b
      (SignedMeanGain.covarianceIncrement u.oscillation w i j))
    (hXp : ∀ i j, Periodic G.region.carrier (SignedMeanGain.covarianceIncrement u.oscillation w i
        j))
    (hfixed : VariableGaugeMean.reconstructState G.gauge c u = u)
    (hmθ : ∀ n s, s ∈ G.region.carrier → radialMoment 2 u.mean.angular n s = 0)
    (hmz : ∀ n s, s ∈ G.region.carrier → radialMoment 1 u.mean.axial n s = 0) :
    SignedMeanGain.LocalData G c u w q gaussian :=
  localData G c u w q gaussian H ho
    (fun i j => MovingField.of_regular (hX i j) (hXp i j)) hfixed hmθ hmz

end

end NavierStokes.MeanStateRegularity
