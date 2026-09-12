/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.MeanStateRegularity

/-!
# Primitive regularity under the actual mean stages

The temporal and rank increments below are the literal variable-gauge
stream constructions.  Their smoothness, moving support, and periodicity
are derived before updating the state.  No new residual regularity or
quantitative estimate is an input to preservation.
-/

@[expose] public section


namespace NavierStokes.MeanStageRegularity

noncomputable section

open Set Function Filter
open scoped ContDiff Topology
open MeanIncrementBounds CorrectionState LocalSignedRequest MeanStateRegularity

/-- Plane: an abbreviation for `PressureStream.Plane`. -/
abbrev Plane := PressureStream.Plane
/-- Point: an abbreviation for `PressureStream.Lift Plane`. -/
abbrev Point := PressureStream.Lift Plane
/-- Scalar: an abbreviation for `MeanIncrementBounds.Field Point`. -/
abbrev Scalar := MeanIncrementBounds.Field Point

namespace MovingField

variable {coord a b : ℝ} {U : SlowRegion coord} {f : Scalar}

theorem temporalAtIndex (hf : GaugeMomentBalances.MovingField U a b f)
    (h : ℝ) (index : ℕ → ℕ) :
    GaugeMomentBalances.MovingField U a b
      (fun n => MeanChartCompatibility.temporalAtIndex h n (index n) (f n)) :=
  ⟨fun n => VariableGaugeMean.temporalAtIndex_contDiffOn h n (index n) U.isOpen
    (hf.smooth n) (hf.periodic n),
    fun n => VariableGaugeMean.temporalAtIndex_supportedGauge h n (index n) (hf.supported n),
    fun n R s _ => MeanChartCompatibility.temporalAtIndex_periodic h n (index n) (f n) R s⟩

theorem streamPotential (hf : GaugeMomentBalances.MovingField U a b f)
    (ha : 0 < a) (hab : a < b) {d : ℝ} (hd : 0 < d) (M : ℕ → ℝ) (v : Plane) :
    GaugeMomentBalances.MovingField U a b
      (fun n => VariableGaugeMean.streamPotential d a b (M n)
        (VariableGaugeMean.qLength coord) v (f n)) :=
  ⟨fun n => VariableGaugeMean.streamPotential_q_contDiffOn U ha hab hd (M n) v
    (hf.smooth n) (hf.supported n),
    fun n => VariableGaugeMean.streamPotential_supportedGauge ha hab hd
      (VariableGaugeMean.qLength coord) v U.isOpen
      (fun s hs => VariableGaugeMean.qLength_pos U.coord_pos U.coord_lt_one (U.time_pos s hs))
      (hf.smooth n) (hf.supported n),
    fun n => VariableGaugeMean.streamPotential_periodicOn d a b (M n)
      (VariableGaugeMean.qLength coord) v (hf.periodic n)⟩

theorem divideRadius (hf : GaugeMomentBalances.MovingField U a b f)
    (ha : 0 < a) (hab : a < b) :
    GaugeMomentBalances.MovingField U a b (fun n => PressureStream.divideRadius (f n)) := by
  have hg : SmoothOn (LocalRankDefect.positiveDomain U.carrier)
      (fun (_ : ℕ) (x : Point) => x.1⁻¹) :=
    fun _ => contDiffOn_fst.inv (fun _ hx => hx.1.ne')
  have hp : PositivePeriodic U.carrier (fun (_ : ℕ) (x : Point) => x.1⁻¹) :=
    fun _ _ _ _ _ _ _ => rfl
  have he := MeanStateRegularity.MovingField.coefficient_mul hf ha hab hg hp
  simp only [mul_comm] at he ⊢
  exact he

theorem streamBeta (hf : GaugeMomentBalances.MovingField U a b f)
    (ε : ℕ → ℝ) (w : Plane × Plane) :
    GaugeMomentBalances.MovingField U a b (fun n => PressureStream.streamBeta (ε n • w) (f n)) := by
  have hh := MeanStateRegularity.MovingField.band_mul
    (MeanStateRegularity.MovingField.neg (MeanStateRegularity.MovingField.directional hf (0, w))) ε
  simpa only [LocalRankDefect.streamBeta_smul, PressureStream.streamBeta,
    PressureStream.graphDz, Pi.neg_apply] using hh

theorem graphDr_eq (d M : ℝ) (v : Plane) (F : Point → ℝ) (x : Point) :
    PressureStream.graphDr (PressureStream.physicalSpeed d M) ((0 : Plane), v) F x =
      fderiv ℝ F x (1, 0) + PressureStream.physicalSpeed d M x.1 *
        fderiv ℝ F x (0, (0, v)) := by
  change fderiv ℝ F x (1, _ • ((0 : Plane), v)) = _
  rw [show (((1 : ℝ), PressureStream.physicalSpeed d M x.1 • ((0 : Plane), v)) : Point) =
      (1, (0, (0 : Plane))) + PressureStream.physicalSpeed d M x.1 • (0, (0, v)) by simp]
  simp only [map_add, map_smul, smul_eq_mul]
  rfl

theorem streamGamma (hf : GaugeMomentBalances.MovingField U a b f)
    (ha : 0 < a) (hab : a < b) (d : ℝ) (M : ℕ → ℝ) (v : Plane) :
    GaugeMomentBalances.MovingField U a b
      (fun n => PressureStream.streamGamma (PressureStream.physicalSpeed d (M n))
        ((0 : Plane), v) (f n)) := by
  have hg : SmoothOn (LocalRankDefect.positiveDomain U.carrier)
      (fun n (x : Point) => PressureStream.physicalSpeed d (M n) x.1) := by
    intro n x hx
    exact ((PressureStream.physicalSpeed_smooth d (M n) hx.1.ne').comp x
      contDiffAt_fst).contDiffWithinAt
  have hp : PositivePeriodic U.carrier
      (fun n (x : Point) => PressureStream.physicalSpeed d (M n) x.1) :=
    fun _ _ _ _ _ _ _ => rfl
  have hr := MeanStateRegularity.MovingField.directional hf (1, 0)
  have ht := MeanStateRegularity.MovingField.coefficient_mul
    (MeanStateRegularity.MovingField.directional hf (0, (0, v))) ha hab hg hp
  have hd := divideRadius hf ha hab
  convert! MeanStateRegularity.MovingField.add (MeanStateRegularity.MovingField.add hr ht) hd using
      1
  funext n x
  exact congrArg (fun t => t + PressureStream.divideRadius (f n) x) (graphDr_eq d (M n) v (f n) x)

end MovingField

section Temporal

variable {coord : ℝ} {U : SlowRegion coord} {g : VariableGaugeMean.GaugeData Plane}
    {c : Context Point} {u : State Point}

/-- Actual stream-based temporal coefficients, including the radial
component and all radii. -/
theorem temporalIncrement_moving (H : PrimitiveData U g.radial.inner g.radial.outer c u)
    (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent)
    (hell : ∀ n, g.length n = VariableGaugeMean.qLength coord)
    (hfixed : (VariableGaugeMean.reconstructState g c u).pressure = u.pressure)
    (h : ℝ) (index : ℕ → ℕ) (axial : Plane × Plane) :
    MovingTriple U g.radial.inner g.radial.outer
      (VariableGaugeMean.temporalIncrementState g h index axial c u) := by
  have hθ := MovingField.temporalAtIndex (H.theta ha g.radial.inner_lt_outer) h index
  have hz := MovingField.temporalAtIndex (H.axial_reconstructed ha hd hell hfixed) h index
  have hp : GaugeMomentBalances.MovingField U g.radial.inner g.radial.outer
      (VariableGaugeMean.temporalPotential g h index c u) := by
    convert! MovingField.streamPotential hz ha g.radial.inner_lt_outer hd
      g.radial.frequency g.radial.radialDirection using 1
    funext n x
    simp only [VariableGaugeMean.temporalPotential, hell]
  exact ⟨MovingField.streamBeta hp c.operators.epsilon axial, hθ,
    MovingField.streamGamma hp ha g.radial.inner_lt_outer
      g.radial.exponent g.radial.frequency g.radial.radialDirection⟩

theorem temporalStage_primitive (H : PrimitiveData U g.radial.inner g.radial.outer c u)
    (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent)
    (hell : ∀ n, g.length n = VariableGaugeMean.qLength coord)
    (hfixed : (VariableGaugeMean.reconstructState g c u).pressure = u.pressure)
    (h : ℝ) (index : ℕ → ℕ) (axial : Plane × Plane) :
    PrimitiveData U g.radial.inner g.radial.outer c
      (VariableGaugeMean.temporalStageState g h index axial c u) := by
  have hi := temporalIncrement_moving H ha hd hell hfixed h index axial
  refine ⟨H.operators, H.base, H.mean.updated hi, ?_, H.virtualTheta, H.virtualAxial⟩
  intro i j
  rw [GaugeDebtIncrement.temporalStage_covariance]
  exact H.covariance i j

theorem temporalStage_reconstructed (g : VariableGaugeMean.GaugeData Plane)
    (c : Context Point) (u : State Point) (h : ℝ) (index : ℕ → ℕ) (axial : Plane × Plane) :
    VariableGaugeMean.reconstructState g c (VariableGaugeMean.temporalStageState g h index axial c
        u) =
      VariableGaugeMean.temporalStageState g h index axial c u := rfl

/-- The primitive invariant and actual pressure reconstruction are both
available for the next stage. -/
theorem temporalStage_preserves (H : PrimitiveData U g.radial.inner g.radial.outer c u)
    (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent)
    (hell : ∀ n, g.length n = VariableGaugeMean.qLength coord)
    (hfixed : (VariableGaugeMean.reconstructState g c u).pressure = u.pressure)
    (h : ℝ) (index : ℕ → ℕ) (axial : Plane × Plane) :
    PrimitiveData U g.radial.inner g.radial.outer c
        (VariableGaugeMean.temporalStageState g h index axial c u) ∧
      VariableGaugeMean.reconstructState g c (VariableGaugeMean.temporalStageState g h index axial
          c u) =
        VariableGaugeMean.temporalStageState g h index axial c u :=
  ⟨temporalStage_primitive H ha hd hell hfixed h index axial,
    temporalStage_reconstructed g c u h index axial⟩

end Temporal

/-! ## The measured debt remains an actual smooth input to rank repair -/

theorem debt_smooth {coord a b : ℝ} {U : SlowRegion coord} {c : Context Point} {u : State Point}
    (H : PrimitiveData U a b c u) (ha : 0 < a) (hab : a < b) (n : ℕ) :
    ContDiffOn ℝ ∞ (CorrectionState.debt c u n) U.carrier := by
  have hP := (H.source ha hab).radialMoment_smooth ha hab 0 n
  have hP₂ := (H.source ha hab).radialMoment_smooth ha hab 2 n
  have hT := (H.angular_flux ha hab).axial.radialMoment_smooth ha hab 2 n
  have hZ := (H.axial_flux ha hab).axial.radialMoment_smooth ha hab 1 n
  apply contDiffOn_pi.2
  intro i
  fin_cases i
  · simp only [CorrectionState.debt, CorrectionState.pressureDefect]
    exact hP
  · simp only [CorrectionState.debt, CorrectionState.thetaDefect]
    exact hT
  · simp only [CorrectionState.debt, CorrectionState.axialDefect, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    exact hZ.sub (contDiffOn_const.mul hP₂)

/-- The fixed rank geometry can be reused at a new state.  Its only
state-dependent analytic field, smoothness of the measured debt, is
reproved from that state's primitive invariant. -/
theorem rankGeometry_for_state {coord a b : ℝ} {U : SlowRegion coord}
    {g : VariableGaugeMean.GaugeData Plane} {r : RankData Plane}
    {c : Context Point} {u v : State Point}
    (H : PrimitiveData U a b c u) (ha : 0 < a) (hab : a < b)
    (hg : LocalRankDefect.RankGeometry g r U.carrier c v) :
    LocalRankDefect.RankGeometry g r U.carrier c u :=
  { primitive_inner_pos := hg.primitive_inner_pos
    exponent_pos := hg.exponent_pos
    lambda_pos := hg.lambda_pos
    inner_pos := hg.inner_pos
    inner_lt_outer := hg.inner_lt_outer
    coefficient_ne := hg.coefficient_ne
    length_pos := hg.length_pos
    velocity_ne := hg.velocity_ne
    coefficient_smooth := hg.coefficient_smooth
    length_smooth := hg.length_smooth
    velocity_smooth := hg.velocity_smooth
    debt_smooth := debt_smooth H ha hab
    gauge_length_pos := hg.gauge_length_pos
    gauge_left := hg.gauge_left
    gauge_right := hg.gauge_right
    angular_model := hg.angular_model
    axial_model := hg.axial_model }

section Rank

variable {coord : ℝ} {U : SlowRegion coord} {g : VariableGaugeMean.GaugeData Plane}
    {r : RankData Plane} {c : Context Point} {u : State Point}

/-- The actual desired rank source has support inside the original
moving gauge, using its proved reserved-patch support and enclosure. -/
theorem rankDesired_moving (hg : LocalRankDefect.RankGeometry g r U.carrier c u)
    (hell : ∀ n, g.length n = VariableGaugeMean.qLength coord) :
    GaugeMomentBalances.MovingField U g.radial.inner g.radial.outer
      (fun n => MeanRankUpdate.slowLift (CorrectionState.rankDesiredAxial r c u n)) := by
  refine ⟨hg.desired_lift_smooth, ?_, fun _ _ _ _ _ _ => rfl⟩
  intro n x hx hn
  have hs := hg.desired_supportedGauge n x hx hn
  have hl := hg.gauge_left n x.2.1 hx
  have hr := hg.gauge_right n x.2.1 hx
  rw [hell n] at hl hr
  exact ⟨hl.trans hs.1, hs.2.trans hr⟩

theorem rankAngular_moving (hg : LocalRankDefect.RankGeometry g r U.carrier c u)
    (hell : ∀ n, g.length n = VariableGaugeMean.qLength coord) (axial : Plane × Plane) :
    GaugeMomentBalances.MovingField U g.radial.inner g.radial.outer
      (VariableGaugeMean.rankIncrementState g r axial c u).angular := by
  refine ⟨hg.angular_lift_smooth, ?_, fun _ _ _ _ _ _ => rfl⟩
  intro n x hx hn
  have hs := hg.angular_supportedGauge axial n x hx hn
  have hl := hg.gauge_left n x.2.1 hx
  have hr := hg.gauge_right n x.2.1 hx
  rw [hell n] at hl hr
  exact ⟨hl.trans hs.1, hs.2.trans hr⟩

theorem rankIncrement_moving (hg : LocalRankDefect.RankGeometry g r U.carrier c u)
    (hell : ∀ n, g.length n = VariableGaugeMean.qLength coord) (axial : Plane × Plane) :
    MovingTriple U g.radial.inner g.radial.outer
      (VariableGaugeMean.rankIncrementState g r axial c u) := by
  have hD := rankDesired_moving hg hell
  have hp : GaugeMomentBalances.MovingField U g.radial.inner g.radial.outer
      (VariableGaugeMean.rankPotential g r c u) := by
    convert! MovingField.streamPotential hD hg.primitive_inner_pos g.radial.inner_lt_outer
      hg.exponent_pos g.radial.frequency g.radial.radialDirection using 1
    funext n x
    simp only [VariableGaugeMean.rankPotential, hell]
  exact ⟨MovingField.streamBeta hp c.operators.epsilon axial, rankAngular_moving hg hell axial,
    MovingField.streamGamma hp hg.primitive_inner_pos g.radial.inner_lt_outer
      g.radial.exponent g.radial.frequency g.radial.radialDirection⟩

theorem rankStage_primitive (H : PrimitiveData U g.radial.inner g.radial.outer c u)
    (hg : LocalRankDefect.RankGeometry g r U.carrier c u)
    (hell : ∀ n, g.length n = VariableGaugeMean.qLength coord) (axial : Plane × Plane) :
    PrimitiveData U g.radial.inner g.radial.outer c
      (VariableGaugeMean.rankStageState g r axial c u) := by
  have hi := rankIncrement_moving hg hell axial
  refine ⟨H.operators, H.base, H.mean.updated hi, ?_, H.virtualTheta, H.virtualAxial⟩
  intro i j
  rw [LocalRankDefect.rankStage_covariance]
  exact H.covariance i j

theorem rankStage_reconstructed (g : VariableGaugeMean.GaugeData Plane) (r : RankData Plane)
    (c : Context Point) (u : State Point) (axial : Plane × Plane) :
    VariableGaugeMean.reconstructState g c (VariableGaugeMean.rankStageState g r axial c u) =
      VariableGaugeMean.rankStageState g r axial c u := rfl

theorem rankStage_preserves (H : PrimitiveData U g.radial.inner g.radial.outer c u)
    (hg : LocalRankDefect.RankGeometry g r U.carrier c u)
    (hell : ∀ n, g.length n = VariableGaugeMean.qLength coord) (axial : Plane × Plane) :
    PrimitiveData U g.radial.inner g.radial.outer c
        (VariableGaugeMean.rankStageState g r axial c u) ∧
      VariableGaugeMean.reconstructState g c (VariableGaugeMean.rankStageState g r axial c u) =
        VariableGaugeMean.rankStageState g r axial c u :=
  ⟨rankStage_primitive H hg hell axial, rankStage_reconstructed g r c u axial⟩

/-- An earlier geometric certificate suffices.  The new state's debt is
computed and its smoothness is derived before performing rank repair. -/
theorem rankStage_from_geometry {v : State Point}
    (H : PrimitiveData U g.radial.inner g.radial.outer c u)
    (hg : LocalRankDefect.RankGeometry g r U.carrier c v)
    (hell : ∀ n, g.length n = VariableGaugeMean.qLength coord) (axial : Plane × Plane) :
    PrimitiveData U g.radial.inner g.radial.outer c
        (VariableGaugeMean.rankStageState g r axial c u) ∧
      VariableGaugeMean.reconstructState g c (VariableGaugeMean.rankStageState g r axial c u) =
        VariableGaugeMean.rankStageState g r axial c u :=
  rankStage_preserves H
    (rankGeometry_for_state H hg.primitive_inner_pos g.radial.inner_lt_outer hg) hell axial

end Rank

/-- The two literal mean stages preserve the same primitive invariant.
The rank geometry is refreshed from the actual temporal output before
the rank correction is formed. -/
theorem temporal_rank_preserves {coord : ℝ} {U : SlowRegion coord}
    {g : VariableGaugeMean.GaugeData Plane} {r : RankData Plane}
    {c : Context Point} {u v : State Point}
    (H : PrimitiveData U g.radial.inner g.radial.outer c u)
    (hg : LocalRankDefect.RankGeometry g r U.carrier c v)
    (hell : ∀ n, g.length n = VariableGaugeMean.qLength coord)
    (hfixed : (VariableGaugeMean.reconstructState g c u).pressure = u.pressure)
    (h : ℝ) (index : ℕ → ℕ) (axialTime axialRank : Plane × Plane) :
    let next := VariableGaugeMean.rankStageState g r axialRank c
      (VariableGaugeMean.temporalStageState g h index axialTime c u)
    PrimitiveData U g.radial.inner g.radial.outer c next ∧
      VariableGaugeMean.reconstructState g c next = next :=
  rankStage_from_geometry
    (temporalStage_primitive H hg.primitive_inner_pos hg.exponent_pos hell hfixed h index axialTime)
    hg hell axialRank

end

end NavierStokes.MeanStageRegularity
