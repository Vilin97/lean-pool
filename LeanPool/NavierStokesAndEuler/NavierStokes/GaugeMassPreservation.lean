/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.VariableGaugeMean
import LeanPool.NavierStokesAndEuler.NavierStokes.GaugeAliasDecay

/-!
# Local mass preservation for the actual moving-gauge temporal update

All conclusions are restricted to the valid open slow region. The common
torus index and the moving radial support are retained throughout.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.GaugeMassPreservation

open Set Filter Function MeasureTheory
open scoped ContDiff Topology Interval BigOperators
open VariableGaugeMean LocalSignedRequest CorrectionState

/-- Plane: an abbreviation for `PressureStream.Plane`. -/
abbrev Plane := PressureStream.Plane
/-- Point: an abbreviation for `PressureStream.Lift Plane`. -/
abbrev Point := PressureStream.Lift Plane

/-- Equality of the moving and frozen stream realizations on one complete
radial/torus fiber. Radial differentiation, including at zero, is retained. -/
theorem streamGamma_frozen_on {coord a b d M : ℝ} (U : SlowRegion coord)
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (v : Plane)
    {f : Point → ℝ} (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : SupportedGauge a b (qLength coord) U.carrier f)
    {s : Plane} (hsm : s ∈ U.carrier) (R : ℝ) (Y : Plane) :
    PressureStream.streamGamma (PressureStream.physicalSpeed d M) ((0 : Plane), v)
      (streamPotential d a b M (qLength coord) v f) (R, (s, Y)) =
    PressureStream.streamGamma (PressureStream.physicalSpeed d M) ((0 : Plane), v)
      (PressureStream.streamPotential d (qLength coord s * a) (qLength coord s * b)
        M ((0 : Plane), v) (PhysicalMeanDomain.freezeSlow s f)) (R, (s, Y)) := by
  let F := PhysicalMeanDomain.freezeSlow s f
  have hF : ContDiff ℝ ∞ F := freezeSlow_contDiff U.isOpen hsm hf
  have hFs : RadialAlias.RadiallySupported (qLength coord s * a) (qLength coord s * b) F := by
    intro z hz
    exact hs (z.1, (s, z.2.2)) hsm hz
  have hl := qLength_pos U.coord_pos U.coord_lt_one (U.time_pos s hsm)
  have hleft : DifferentiableAt ℝ (streamPotential d a b M (qLength coord) v f) (R, (s, Y)) :=
    ((streamPotential_q_contDiffOn U ha hab hd M v hf hs).contDiffAt
      ((PhysicalMeanDomain.slowDomain_open U.isOpen).mem_nhds hsm)).differentiableAt (by simp)
  have hright : DifferentiableAt ℝ
      (PressureStream.streamPotential d (qLength coord s * a) (qLength coord s * b)
        M ((0 : Plane), v) F) (R, (s, Y)) :=
    ((PressureStream.streamPotential_contDiff (mul_pos hl ha)
      (mul_lt_mul_of_pos_left hab hl) hd ((0 : Plane), v) hF hFs).differentiable (by simp)) _
  have he (r : ℝ) (Z : Plane) : streamPotential d a b M (qLength coord) v f (r, (s, Z)) =
      PressureStream.streamPotential d (qLength coord s * a) (qLength coord s * b)
        M ((0 : Plane), v) F (r, (s, Z)) := by
    exact (streamPotential_eq_fixed d a b M (qLength coord) v f (r, (s, Z))).trans
      (PhysicalMeanDomain.streamPotential_fiberLocal d (qLength coord s * a) (qLength coord s * b)
        M v f F s (fun _ _ => rfl) r Z)
  change PressureStream.graphDr _ _ _ _ + _ = PressureStream.graphDr _ _ _ _ + _
  rw [graphDr_eq_on_radialFiber hleft hright he]
  exact congrArg (fun x => PressureStream.graphDr (PressureStream.physicalSpeed d M)
    ((0 : Plane), v) (PressureStream.streamPotential d (qLength coord s * a)
      (qLength coord s * b) M ((0 : Plane), v) F) (R, (s, Y)) + x / R) (he R Y)

theorem streamGamma_slice_continuous_on {coord a b d M : ℝ} (U : SlowRegion coord)
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (v : Plane)
    {f : Point → ℝ} (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : SupportedGauge a b (qLength coord) U.carrier f)
    {s : Plane} (hsm : s ∈ U.carrier) (R : ℝ) :
    Continuous (fun Y => PressureStream.streamGamma (PressureStream.physicalSpeed d M) ((0 :
        Plane), v)
      (streamPotential d a b M (qLength coord) v f) (R, (s, Y))) := by
  let F := PhysicalMeanDomain.freezeSlow s f
  have hF : ContDiff ℝ ∞ F := freezeSlow_contDiff U.isOpen hsm hf
  have hFs : RadialAlias.RadiallySupported (qLength coord s * a) (qLength coord s * b) F := by
    intro z hz
    exact hs (z.1, (s, z.2.2)) hsm hz
  have hl := qLength_pos U.coord_pos U.coord_lt_one (U.time_pos s hsm)
  have hc : Continuous (fun Y : Plane => PressureStream.streamGamma
      (PressureStream.physicalSpeed d M) ((0 : Plane), v)
      (PressureStream.streamPotential d (qLength coord s * a) (qLength coord s * b)
        M ((0 : Plane), v) F) (R, (s, Y))) :=
    (PressureStream.streamGamma_contDiff (M := M) (mul_pos hl ha)
    (mul_lt_mul_of_pos_left hab hl) hd ((0 : Plane), v) hF hFs).continuous.comp
      (continuous_const.prodMk (continuous_const.prodMk continuous_id))
  exact hc.congr (fun Y => (streamGamma_frozen_on U ha hab hd v hf hs hsm R Y).symm)

/-- Zero weighted bar mass gives the prescribed axial bar in the moving
gauge. The conclusion covers every real radius, including zero. -/
theorem streamGamma_bar_eq_desired_on {coord a b d M : ℝ} (U : SlowRegion coord)
    (ha : 0 < a) (hab : a < b) (hd : 0 < d) (v : Plane)
    {f : Point → ℝ} (hf : ContDiffOn ℝ ∞ f (PhysicalMeanDomain.slowDomain U.carrier))
    (hs : SupportedGauge a b (qLength coord) U.carrier f)
    (hp : PhysicalMeanDomain.PeriodicOn U.carrier f)
    {s : Plane} (hsm : s ∈ U.carrier)
    (hm : (∫ r, r * PressureStream.torusAverage f (r, s)) = 0) (R : ℝ) :
    PressureStream.torusAverage (PressureStream.streamGamma (PressureStream.physicalSpeed d M)
      ((0 : Plane), v) (streamPotential d a b M (qLength coord) v f)) (R, s) =
      PressureStream.torusAverage f (R, s) := by
  let F := PhysicalMeanDomain.freezeSlow s f
  have hF : ContDiff ℝ ∞ F := freezeSlow_contDiff U.isOpen hsm hf
  have hFs : RadialAlias.RadiallySupported (qLength coord s * a) (qLength coord s * b) F := by
    intro z hz
    exact hs (z.1, (s, z.2.2)) hsm hz
  have hFp : PressureStream.TorusPeriodicLift F := fun r t Y k => hp r s hsm Y k
  have hFm (t : Plane) : (∫ r, r * PressureStream.torusAverage F (r, t)) = 0 := hm
  have hl := qLength_pos U.coord_pos U.coord_lt_one (U.time_pos s hsm)
  calc
    _ = PressureStream.torusAverage (PressureStream.streamGamma (PressureStream.physicalSpeed d M)
        ((0 : Plane), v) (PressureStream.streamPotential d (qLength coord s * a)
          (qLength coord s * b) M ((0 : Plane), v) F)) (R, s) :=
      PressureStream.torusAverage_congr_slice (R, s) (streamGamma_frozen_on U ha hab hd v hf hs hsm
          R)
    _ = PressureStream.torusAverage F (R, s) :=
      PressureStream.streamGamma_bar_eq_desired (mul_pos hl ha)
        (mul_lt_mul_of_pos_left hab hl) hd v hF hFs hFp hFm (R, s)
    _ = _ := rfl

theorem continuous_torus_slice {U : Set Plane} {f : Point → ℝ}
    (hf : ContinuousOn f (PhysicalMeanDomain.slowDomain U)) {s : Plane} (hs : s ∈ U) (R : ℝ) :
    Continuous (fun Y : Plane => f (R, (s, Y))) :=
  hf.comp_continuous (continuous_const.prodMk (continuous_const.prodMk continuous_id)) (fun _ => hs)

theorem torusAverage_add_slice (f g : Point → ℝ) (R : ℝ) (s : Plane)
    (hf : Continuous (fun Y => f (R, (s, Y)))) (hg : Continuous (fun Y => g (R, (s, Y)))) :
    PressureStream.torusAverage (fun z => f z + g z) (R, s) =
      PressureStream.torusAverage f (R, s) + PressureStream.torusAverage g (R, s) :=
  FourierAlias.torusMean_add hf hg

theorem radialMoment_congr_torusAverage (k : ℕ) (f g : ScalarField Point)
    (n : ℕ) (s : Plane)
    (he : ∀ R, PressureStream.torusAverage (f n) (R, s) =
      PressureStream.torusAverage (g n) (R, s)) :
    CorrectionState.radialMoment k f n s = CorrectionState.radialMoment k g n s := by
  rw [StateMomentBalances.state_radialMoment_eq, StateMomentBalances.state_radialMoment_eq]
  apply integral_congr_ae
  filter_upwards [] with R
  exact congrArg (fun x => R ^ k * x) (he R)

theorem radialMoment_zero_of_torusAverage (k : ℕ) (f : ScalarField Point)
    (n : ℕ) (s : Plane) (he : ∀ R, PressureStream.torusAverage (f n) (R, s) = 0) :
    CorrectionState.radialMoment k f n s = 0 := by
  rw [StateMomentBalances.state_radialMoment_eq]
  change (∫ R, R ^ k * PressureStream.torusAverage (f n) (R, s)) = 0
  simp_rw [he, mul_zero, integral_zero]

/-- The two conserved mean masses, restricted to a specified slow set. -/
noncomputable def ZeroMassesOn (U : Set Plane) (u : State Point) : Prop :=
  ∀ n s, s ∈ U → CorrectionState.radialMoment 2 u.mean.angular n s = 0 ∧
    CorrectionState.radialMoment 1 u.mean.axial n s = 0

theorem ZeroMassesOn.of_global {U : Set Plane} {u : State Point}
    (hu : CorrectionState.ZeroMasses u) : ZeroMassesOn U u := by
  intro n s _
  constructor
  · exact congrFun (congrFun hu.1 n) s
  · exact congrFun (congrFun hu.2 n) s

section Temporal

variable {coord : ℝ} (U : SlowRegion coord) (g : GaugeData Plane)
    (ha : 0 < g.radial.inner) (hd : 0 < g.radial.exponent)
    (hell : ∀ n, g.length n = qLength coord)
    (h : ℝ) (index : ℕ → ℕ) (axial : Plane × Plane)
    (c : Context Point) (u : State Point)

include ha hd hell

theorem temporalIncrement_torusMean_on
    (hθ : ∀ n, ContDiffOn ℝ ∞ (u.thetaResidual c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hz : ∀ n, ContDiffOn ℝ ∞ (u.axialResidual c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hpθ : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (u.thetaResidual c n))
    (hpz : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (u.axialResidual c n))
    (hsz : ∀ n, SupportedGauge g.radial.inner g.radial.outer (qLength coord) U.carrier
        (u.axialResidual c n))
    (n : ℕ) (R : ℝ) {s : Plane} (hs : s ∈ U.carrier) :
    PressureStream.torusAverage ((temporalIncrementState g h index axial c u).angular n) (R, s) = 0
        ∧
      PressureStream.torusAverage ((temporalIncrementState g h index axial c u).axial n) (R, s) = 0
          := by
  constructor
  · exact GaugeAliasDecay.temporalAtIndex_zeroMean_on U h n (index n) (hθ n) (hpθ n) R hs
  · change PressureStream.torusAverage (PressureStream.streamGamma
      (PressureStream.physicalSpeed g.radial.exponent (g.radial.frequency n)) ((0 : Plane),
          g.radial.radialDirection)
      (streamPotential g.radial.exponent g.radial.inner g.radial.outer (g.radial.frequency n)
        (g.length n) g.radial.radialDirection
        (MeanChartCompatibility.temporalAtIndex h n (index n) (u.axialResidual c n)))) (R, s) = 0
    rw [hell n]
    have hsm := temporalAtIndex_contDiffOn h n (index n) U.isOpen (hz n) (hpz n)
    have hsp := temporalAtIndex_supportedGauge h n (index n) (hsz n)
    have hper : PhysicalMeanDomain.PeriodicOn U.carrier
        (MeanChartCompatibility.temporalAtIndex h n (index n) (u.axialResidual c n)) :=
      fun r t _ Y k => MeanChartCompatibility.temporalAtIndex_periodic h n (index n)
          (u.axialResidual c n) r t Y k
    have hm : (∫ r, r * PressureStream.torusAverage
        (MeanChartCompatibility.temporalAtIndex h n (index n) (u.axialResidual c n)) (r, s)) = 0 :=
            by
      simp_rw [GaugeAliasDecay.temporalAtIndex_zeroMean_on U h n (index n) (hz n) (hpz n) _ hs,
        mul_zero, integral_zero]
    rw [streamGamma_bar_eq_desired_on U ha g.radial.inner_lt_outer hd g.radial.radialDirection hsm
        hsp hper hs hm R]
    exact GaugeAliasDecay.temporalAtIndex_zeroMean_on U h n (index n) (hz n) (hpz n) R hs

theorem temporalIncrement_slice_continuous_on
    (hθ : ∀ n, ContDiffOn ℝ ∞ (u.thetaResidual c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hz : ∀ n, ContDiffOn ℝ ∞ (u.axialResidual c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hpθ : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (u.thetaResidual c n))
    (hpz : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (u.axialResidual c n))
    (hsz : ∀ n, SupportedGauge g.radial.inner g.radial.outer (qLength coord) U.carrier
        (u.axialResidual c n))
    (n : ℕ) (R : ℝ) {s : Plane} (hs : s ∈ U.carrier) :
    Continuous (fun Y => (temporalIncrementState g h index axial c u).angular n (R, (s, Y))) ∧
      Continuous (fun Y => (temporalIncrementState g h index axial c u).axial n (R, (s, Y))) := by
  constructor
  · exact continuous_torus_slice
      (temporalAtIndex_contDiffOn h n (index n) U.isOpen (hθ n) (hpθ n)).continuousOn hs R
  · change Continuous (fun Y => PressureStream.streamGamma
      (PressureStream.physicalSpeed g.radial.exponent (g.radial.frequency n)) ((0 : Plane),
          g.radial.radialDirection)
      (streamPotential g.radial.exponent g.radial.inner g.radial.outer (g.radial.frequency n)
        (g.length n) g.radial.radialDirection
        (MeanChartCompatibility.temporalAtIndex h n (index n) (u.axialResidual c n))) (R, (s, Y)))
    rw [hell n]
    exact streamGamma_slice_continuous_on U ha g.radial.inner_lt_outer hd g.radial.radialDirection
      (temporalAtIndex_contDiffOn h n (index n) U.isOpen (hz n) (hpz n))
      (temporalAtIndex_supportedGauge h n (index n) (hsz n)) hs R

/-- Every radial moment of either conserved increment vanishes on the valid
slow set, since its full torus average is identically zero there. -/
theorem temporalIncrement_radialMoments_zero_on
    (hθ : ∀ n, ContDiffOn ℝ ∞ (u.thetaResidual c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hz : ∀ n, ContDiffOn ℝ ∞ (u.axialResidual c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hpθ : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (u.thetaResidual c n))
    (hpz : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (u.axialResidual c n))
    (hsz : ∀ n, SupportedGauge g.radial.inner g.radial.outer (qLength coord) U.carrier
        (u.axialResidual c n))
    (k n : ℕ) {s : Plane} (hs : s ∈ U.carrier) :
    CorrectionState.radialMoment k (temporalIncrementState g h index axial c u).angular n s = 0 ∧
      CorrectionState.radialMoment k (temporalIncrementState g h index axial c u).axial n s = 0 :=
          by
  constructor
  · exact radialMoment_zero_of_torusAverage k _ n s (fun R =>
      (temporalIncrement_torusMean_on U g ha hd hell h index axial c u hθ hz hpθ hpz hsz n R hs).1)
  · exact radialMoment_zero_of_torusAverage k _ n s (fun R =>
      (temporalIncrement_torusMean_on U g ha hd hell h index axial c u hθ hz hpθ hpz hsz n R hs).2)

/-- Pressure reconstruction and the stored temporal alias leave the actual
angular/axial torus means unchanged after the common-index increment. -/
theorem temporalStage_torusMean_on
    (hmθ : ∀ n, ContinuousOn (u.mean.angular n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hmz : ∀ n, ContinuousOn (u.mean.axial n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hθ : ∀ n, ContDiffOn ℝ ∞ (u.thetaResidual c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hz : ∀ n, ContDiffOn ℝ ∞ (u.axialResidual c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hpθ : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (u.thetaResidual c n))
    (hpz : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (u.axialResidual c n))
    (hsz : ∀ n, SupportedGauge g.radial.inner g.radial.outer (qLength coord) U.carrier
        (u.axialResidual c n))
    (n : ℕ) (R : ℝ) {s : Plane} (hs : s ∈ U.carrier) :
    PressureStream.torusAverage ((temporalStageState g h index axial c u).mean.angular n) (R, s) =
        PressureStream.torusAverage (u.mean.angular n) (R, s) ∧
      PressureStream.torusAverage ((temporalStageState g h index axial c u).mean.axial n) (R, s) =
        PressureStream.torusAverage (u.mean.axial n) (R, s) := by
  have hz0 := temporalIncrement_torusMean_on U g ha hd hell h index axial c u hθ hz hpθ hpz hsz n R
      hs
  have hcont := temporalIncrement_slice_continuous_on U g ha hd hell h index axial c u hθ hz hpθ
      hpz hsz n R hs
  constructor
  · change PressureStream.torusAverage (fun z => u.mean.angular n z +
      (temporalIncrementState g h index axial c u).angular n z) (R, s) = _
    rw [torusAverage_add_slice _ _ R s (continuous_torus_slice (hmθ n) hs R) hcont.1, hz0.1,
        add_zero]
  · change PressureStream.torusAverage (fun z => u.mean.axial n z +
      (temporalIncrementState g h index axial c u).axial n z) (R, s) = _
    rw [torusAverage_add_slice _ _ R s (continuous_torus_slice (hmz n) hs R) hcont.2, hz0.2,
        add_zero]

/-- The literal reconstructed temporal state preserves both physical mean
masses on the valid slow region. No statement is made outside that region. -/
theorem temporalStage_preserve_masses_on
    (hmθ : ∀ n, ContinuousOn (u.mean.angular n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hmz : ∀ n, ContinuousOn (u.mean.axial n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hθ : ∀ n, ContDiffOn ℝ ∞ (u.thetaResidual c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hz : ∀ n, ContDiffOn ℝ ∞ (u.axialResidual c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hpθ : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (u.thetaResidual c n))
    (hpz : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (u.axialResidual c n))
    (hsz : ∀ n, SupportedGauge g.radial.inner g.radial.outer (qLength coord) U.carrier
        (u.axialResidual c n))
    (n : ℕ) {s : Plane} (hs : s ∈ U.carrier) :
    CorrectionState.radialMoment 2 (temporalStageState g h index axial c u).mean.angular n s =
        CorrectionState.radialMoment 2 u.mean.angular n s ∧
      CorrectionState.radialMoment 1 (temporalStageState g h index axial c u).mean.axial n s =
        CorrectionState.radialMoment 1 u.mean.axial n s := by
  constructor
  · exact radialMoment_congr_torusAverage 2 _ _ n s (fun R =>
      (temporalStage_torusMean_on U g ha hd hell h index axial c u
        hmθ hmz hθ hz hpθ hpz hsz n R hs).1)
  · exact radialMoment_congr_torusAverage 1 _ _ n s (fun R =>
      (temporalStage_torusMean_on U g ha hd hell h index axial c u
        hmθ hmz hθ hz hpθ hpz hsz n R hs).2)

theorem temporalStage_zeroMassesOn
    (hmθ : ∀ n, ContinuousOn (u.mean.angular n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hmz : ∀ n, ContinuousOn (u.mean.axial n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hθ : ∀ n, ContDiffOn ℝ ∞ (u.thetaResidual c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hz : ∀ n, ContDiffOn ℝ ∞ (u.axialResidual c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hpθ : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (u.thetaResidual c n))
    (hpz : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (u.axialResidual c n))
    (hsz : ∀ n, SupportedGauge g.radial.inner g.radial.outer (qLength coord) U.carrier
        (u.axialResidual c n))
    (hu : ZeroMassesOn U.carrier u) :
    ZeroMassesOn U.carrier (temporalStageState g h index axial c u) := by
  intro n s hs
  have he := temporalStage_preserve_masses_on U g ha hd hell h index axial c u
    hmθ hmz hθ hz hpθ hpz hsz n hs
  exact ⟨he.1.trans (hu n s hs).1, he.2.trans (hu n s hs).2⟩

theorem temporalStage_zeroMassesOn_of_global
    (hmθ : ∀ n, ContinuousOn (u.mean.angular n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hmz : ∀ n, ContinuousOn (u.mean.axial n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hθ : ∀ n, ContDiffOn ℝ ∞ (u.thetaResidual c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hz : ∀ n, ContDiffOn ℝ ∞ (u.axialResidual c n) (PhysicalMeanDomain.slowDomain U.carrier))
    (hpθ : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (u.thetaResidual c n))
    (hpz : ∀ n, PhysicalMeanDomain.PeriodicOn U.carrier (u.axialResidual c n))
    (hsz : ∀ n, SupportedGauge g.radial.inner g.radial.outer (qLength coord) U.carrier
        (u.axialResidual c n))
    (hu : CorrectionState.ZeroMasses u) :
    ZeroMassesOn U.carrier (temporalStageState g h index axial c u) :=
  temporalStage_zeroMassesOn U g ha hd hell h index axial c u hmθ hmz hθ hz hpθ hpz hsz
    (ZeroMassesOn.of_global hu)

end Temporal

end NavierStokes.GaugeMassPreservation
