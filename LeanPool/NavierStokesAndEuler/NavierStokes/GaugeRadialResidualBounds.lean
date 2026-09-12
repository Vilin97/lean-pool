/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.MeanStateRegularity
import LeanPool.NavierStokesAndEuler.NavierStokes.RankStateBounds

/-!
# The radial residual of the actual moving pressure gauge

The current pressure alias is subtracted literally. The remaining field is
minus the normalized moving density times the measured pressure debt. Its
mean class follows on the same moving strip, retaining the vanishing edge
weight and all ordinary slow derivatives.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.GaugeRadialResidualBounds

open Set Function Filter
open scoped ContDiff Topology
open WeightedClasses CorrectionState LocalSignedRequest

/-- Plane: an abbreviation for `PressureStream.Plane`. -/
abbrev Plane := PressureStream.Plane
/-- Point: an abbreviation for `PressureStream.Lift Plane`. -/
abbrev Point := PressureStream.Lift Plane
/-- Scalar: an abbreviation for `MeanIncrementBounds.Field Point`. -/
abbrev Scalar := MeanIncrementBounds.Field Point

/-- Only the primitive coefficients of the actual radial derivative are
matched. No residual or quantitative bound is a field of this record. -/
structure RadialMatch (U : Set Plane) (g : VariableGaugeMean.GaugeData Plane)
    (o : MeanIncrementBounds.Operators Point) : Prop where
  frequency : o.radialFrequency = g.radial.frequency
  profile : ∀ x : Point, x.2.1 ∈ U →
    o.radialProfile x = RadialPullback.radialJacobian g.radial.exponent x.1
  eR : o.eR = (1, (0, 0))
  vR : o.vR = (0, (0, g.radial.radialDirection))

namespace RadialMatch

variable {U : Set Plane} {g : VariableGaugeMean.GaugeData Plane}
  {o : MeanIncrementBounds.Operators Point}

theorem graphOperators (U : Set Plane) (g : VariableGaugeMean.GaugeData Plane)
    (epsilon fast : ℕ → ℝ) (axial slowTime : Plane × Plane) (temporal : Plane) :
    RadialMatch U g (CorrectionState.graphOperators g.radial epsilon fast axial slowTime temporal)
        :=
  ⟨rfl, fun _ _ => rfl, rfl, rfl⟩

theorem nativeOperators (U : Set Plane) (g : VariableGaugeMean.GaugeData Plane)
    (epsilon fast : ℕ → ℝ) (axial slowTime temporal : Plane) :
    RadialMatch U g (StateMomentBalances.nativeOperators g.radial epsilon fast axial slowTime
        temporal) :=
  graphOperators U g epsilon fast (axial, 0) (slowTime, 0) temporal

/-- The primitive matches give the genuine derivative identity for every
field, without requiring differentiability to identify the two operators. -/
theorem dr (H : RadialMatch U g o) (f : Scalar) (n : ℕ) {x : Point} (hx : x.2.1 ∈ U) :
    o.dr f n x = PressureStream.graphDr
      (PressureStream.physicalSpeed g.radial.exponent (g.radial.frequency n))
      ((0 : Plane), g.radial.radialDirection) (f n) x := by
  calc
    o.dr f n x = (CorrectionState.graphOperators g.radial (fun _ => 1) (fun _ => 1)
        (0, 0) (0, 0) 0).dr f n x := by
      simp only [MeanIncrementBounds.Operators.dr, WeightedClasses.graphDerivative,
        H.frequency, H.profile x hx, H.eR, H.vR, CorrectionState.graphOperators]
    _ = _ := CorrectionState.graphOperators_dr g.radial (fun _ => 1) (fun _ => 1)
      (0, 0) (0, 0) 0 f n x

end RadialMatch

/-- The literal radial component after removing the current pressure alias. -/
noncomputable def radialMinusAlias (g : VariableGaugeMean.GaugeData Plane)
    (c : Context Point) (u : State Point) : Scalar := fun n x =>
  u.radialResidual c n x - VariableGaugeMean.pressureAliasState g c u n (x, 0) 0

theorem radialMinusAlias_angle (g : VariableGaugeMean.GaugeData Plane)
    (c : Context Point) (u : State Point) (n : ℕ) (x : Point) (theta : ℝ) :
    u.radialResidual c n x - VariableGaugeMean.pressureAliasState g c u n (x, theta) 0 =
      radialMinusAlias g c u n x := rfl

/-- The pressure defect is the actual zeroth radial moment of the radial
source, with the same auxiliary-torus average used by the gauge. -/
theorem pressureDefect_eq_mass (c : Context Point) (u : State Point) (n : ℕ) (s : Plane) :
    pressureDefect c u n s = PressureStream.pressureMass (u.gr c n) s := by
  simp only [pressureDefect, radialMoment, pow_zero, one_mul]

/-- Pressure reconstruction preserves every primitive input field: this
record deliberately contains no output regularity assertion for pressure. -/
theorem primitiveData_reconstructState {coord a b : ℝ} {U : SlowRegion coord}
    (g : VariableGaugeMean.GaugeData Plane) {c : Context Point} {u : State Point}
    (H : MeanStateRegularity.PrimitiveData U a b c u) :
    MeanStateRegularity.PrimitiveData U a b c (VariableGaugeMean.reconstructState g c u) :=
  ⟨H.operators, H.base, H.mean, H.covariance, H.virtualTheta, H.virtualAxial⟩

section Identity

variable {coord : ℝ} (U : SlowRegion coord) (g : VariableGaugeMean.GaugeData Plane)
  (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent)
  (hell : ∀ n, g.length n = VariableGaugeMean.qLength coord)
  (c : Context Point) (u : State Point)

include ha hd hell

/-- Primitive field regularity supplies the source regularity and support.
Only the pressure reconstruction equality is required of the incoming state. -/
theorem radialMinusAlias_identity
    (H : MeanStateRegularity.PrimitiveData U g.radial.inner g.radial.outer c u)
    (hr : RadialMatch U.carrier g c.operators)
    (hfixed : (VariableGaugeMean.reconstructState g c u).pressure = u.pressure)
    (n : ℕ) {x : Point} (hx : x.2.1 ∈ U.carrier) :
    radialMinusAlias g c u n x =
      -VariableGaugeMean.density g.radial.inner g.radial.outer g.radial.inner_lt_outer
        (g.length n) x * pressureDefect c u n x.2.1 := by
  have hs := H.source ha g.radial.inner_lt_outer
  have he := VariableGaugeMean.reconstructState_radial_identity U g ha hd hell c u n
    (hs.smooth n) (hs.supported n) hx
  rw [hfixed] at he
  simp only [radialMinusAlias, State.radialResidual, Pi.sub_apply]
  rw [hr.dr u.pressure n hx, he, pressureDefect_eq_mass]
  simp only [VariableGaugeMean.pressureAliasState, Matrix.cons_val_zero]
  ring

/-- Applying the actual constructor discharges pressure reconstruction; the
same incoming primitive data and pressure debt are used. -/
theorem reconstructed_identity
    (H : MeanStateRegularity.PrimitiveData U g.radial.inner g.radial.outer c u)
    (hr : RadialMatch U.carrier g c.operators)
    (n : ℕ) {x : Point} (hx : x.2.1 ∈ U.carrier) :
    radialMinusAlias g c (VariableGaugeMean.reconstructState g c u) n x =
      -VariableGaugeMean.density g.radial.inner g.radial.outer g.radial.inner_lt_outer
        (g.length n) x * pressureDefect c u n x.2.1 :=
  radialMinusAlias_identity U g ha hd hell c (VariableGaugeMean.reconstructState g c u)
    (primitiveData_reconstructState g H) hr rfl n hx

end Identity

section Classes

variable {coord cL cR : ℝ} (U : SlowRegion coord)
  (g : VariableGaugeMean.GaugeData Plane) (ha : 0 < g.radial.inner)
  (hd : 0 < g.radial.exponent) (hcL : 0 < cL) (hcR : 0 < cR)
  (epsilon slow : ℕ → ℝ) (hepsilon : ∀ n, 0 < epsilon n)
  (hepsilon_one : ∀ n, epsilon n ≤ 1) (hslow : ∀ n, 1 ≤ slow n)
  (hell : ∀ n, g.length n = VariableGaugeMean.qLength coord)

local notation "strip" => movingStripData U g.radial.inner g.radial.outer cL cR
  ha hcL hcR epsilon slow hepsilon hepsilon_one hslow

local notation "slowStrip" => PhysicalMeanDomain.localSlowStripData U.carrier U.isOpen
  epsilon slow hepsilon hepsilon_one hslow

include hell

/-- The measured slow debt lifts without loss and multiplies the actual
normalized moving density. The density contributes the genuine edge weight. -/
theorem density_times_debt_class {alpha : ℝ} {debt : ℕ → Plane → ℝ}
    (hdebt : UnweightedClass slowStrip alpha debt) :
    MeanClass strip alpha (fun n x =>
      -VariableGaugeMean.density g.radial.inner g.radial.outer g.radial.inner_lt_outer
        (g.length n) x * debt n x.2.1) := by
  have hsub : ∀ x ∈ (strip).domain, x.2.1 ∈ U.carrier := fun x hx =>
    ((movingStrip_domain U g.radial.inner g.radial.outer cL cR ha hcL hcR
      epsilon slow hepsilon hepsilon_one hslow x).mp hx).1
  have hlift := RankStateBounds.slowClass_lift strip U.isOpen hsub hdebt
  have hrho := VariableGaugeMean.density_meanClass_moving U ha hcL hcR
    epsilon slow hepsilon hepsilon_one hslow g.radial.inner_lt_outer
  have hm := MeanIncrementBounds.Class.neg (MeanIncrementBounds.Class.mul_coefficient hrho hlift)
  simp only [zero_add, neg_mul, hell] at hm ⊢
  exact hm

include hd in
/-- The literal radial residual minus its current pressure alias has exactly
the measured debt's order on the same moving strip. No source class is assumed. -/
theorem radialMinusAlias_class (c : Context Point) (u : State Point)
    (H : MeanStateRegularity.PrimitiveData U g.radial.inner g.radial.outer c u)
    (hr : RadialMatch U.carrier g c.operators)
    (hfixed : (VariableGaugeMean.reconstructState g c u).pressure = u.pressure)
    {alpha : ℝ} (hdebt : UnweightedClass slowStrip alpha (pressureDefect c u)) :
    MeanClass strip alpha (radialMinusAlias g c u) := by
  have hm := density_times_debt_class U g ha hcL hcR epsilon slow
    hepsilon hepsilon_one hslow hell hdebt
  apply MeanRankUpdate.meanClass_congr_on hm
  intro n x hx
  have hxu := ((movingStrip_domain U g.radial.inner g.radial.outer cL cR ha hcL hcR
    epsilon slow hepsilon hepsilon_one hslow x).mp hx).1
  exact radialMinusAlias_identity U g ha hd hell c u H hr hfixed n hxu

include hd in
/-- The actual reconstructed state's radial class is derived without an
input assertion that its pressure already equals the gauge formula. -/
theorem reconstructed_class (c : Context Point) (u : State Point)
    (H : MeanStateRegularity.PrimitiveData U g.radial.inner g.radial.outer c u)
    (hr : RadialMatch U.carrier g c.operators)
    {alpha : ℝ} (hdebt : UnweightedClass slowStrip alpha (pressureDefect c u)) :
    MeanClass strip alpha (radialMinusAlias g c (VariableGaugeMean.reconstructState g c u)) :=
  radialMinusAlias_class U g ha hd hcL hcR epsilon slow hepsilon hepsilon_one hslow hell
    c (VariableGaugeMean.reconstructState g c u) (primitiveData_reconstructState g H) hr rfl hdebt

end Classes

section Similarity

variable {h a b cL cR sigma : ℝ} (U : SlowRegion (2 * h))
  (ha : 0 < a) (hab : a < b) (hcL : 0 < cL) (hcR : 0 < cR)
  (Mbase : ℝ) (index : ℕ → ℕ)
  (epsilon slow : ℕ → ℝ) (hepsilon : ∀ n, 0 < epsilon n)
  (hepsilon_one : ∀ n, epsilon n ≤ 1) (hslow : ∀ n, 1 ≤ slow n)

local notation "gauge" => VariableGaugeMean.similarityGauge h (ChartScales.radialExponent h)
  a b Mbase hab index

local notation "strip" => movingStripData U a b cL cR ha hcL hcR
  epsilon slow hepsilon hepsilon_one hslow

local notation "slowStrip" => PhysicalMeanDomain.localSlowStripData U.carrier U.isOpen
  epsilon slow hepsilon hepsilon_one hslow

include ha in
/-- The normalized bump and sign for the actual similarity gauge. -/
theorem similarity_identity (c : Context Point) (u : State Point)
    (H : MeanStateRegularity.PrimitiveData U a b c u)
    (hr : RadialMatch U.carrier gauge c.operators)
    (hfixed : (VariableGaugeMean.reconstructState gauge c u).pressure = u.pressure)
    (n : ℕ) {x : Point} (hx : x.2.1 ∈ U.carrier) :
    u.radialResidual c n x - VariableGaugeMean.pressureAliasState gauge c u n (x, 0) 0 =
      -VariableGaugeMean.density a b hab (VariableGaugeMean.qLength (2 * h)) x *
        pressureDefect c u n x.2.1 := by
  have hh : 0 ≤ h := by linarith [U.coord_pos]
  exact radialMinusAlias_identity U gauge ha (ChartScales.radialExponent_pos h hh)
    (fun _ => rfl) c u H hr hfixed n hx

/-- The iteration's radial component: an S_(1+sigma) pressure debt gives
M_(1+sigma) for the current alias-subtracted radial residual. -/
theorem similarity_class (c : Context Point) (u : State Point)
    (H : MeanStateRegularity.PrimitiveData U a b c u)
    (hr : RadialMatch U.carrier gauge c.operators)
    (hfixed : (VariableGaugeMean.reconstructState gauge c u).pressure = u.pressure)
    (hdebt : UnweightedClass slowStrip (1 + sigma) (pressureDefect c u)) :
    MeanClass strip (1 + sigma) (fun n x =>
      u.radialResidual c n x - VariableGaugeMean.pressureAliasState gauge c u n (x, 0) 0) := by
  have hh : 0 ≤ h := by linarith [U.coord_pos]
  exact radialMinusAlias_class U gauge ha (ChartScales.radialExponent_pos h hh)
    hcL hcR epsilon slow hepsilon hepsilon_one hslow (fun _ => rfl) c u H hr hfixed hdebt

/-- With the actual native operators, every radial matching field is proved
from the constructor. The only operator premise is the literal input binding. -/
theorem similarity_native_class (c : Context Point) (u : State Point)
    (H : MeanStateRegularity.PrimitiveData U a b c u)
    (fast : ℕ → ℝ) (axial slowTime temporal : Plane)
    (ho : c.operators = StateMomentBalances.nativeOperators (gauge).radial
      epsilon fast axial slowTime temporal)
    (hfixed : (VariableGaugeMean.reconstructState gauge c u).pressure = u.pressure)
    (hdebt : UnweightedClass slowStrip (1 + sigma) (pressureDefect c u)) :
    MeanClass strip (1 + sigma) (fun n x =>
      u.radialResidual c n x - VariableGaugeMean.pressureAliasState gauge c u n (x, 0) 0) := by
  apply similarity_class U ha hab hcL hcR Mbase index epsilon slow hepsilon hepsilon_one hslow c u H
  · rw [ho]
    exact RadialMatch.nativeOperators U.carrier gauge epsilon fast axial slowTime temporal
  · exact hfixed
  · exact hdebt

end Similarity

end NavierStokes.GaugeRadialResidualBounds
