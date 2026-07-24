/-
Copyright (c) 2026 Wei Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Wang
-/
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.RadiusWeights
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.RadialIdentity

/-!
# Boundary and radius interfaces

This module contains the boundary identities and the abstract one-dimensional
radius/coarea interfaces used by the weak monotonicity proof.

These interfaces are internal scaffolding: they expose the intermediate
boundary and radius statements so the proof can be checked modularly, but they
are not intended as the public API of the project.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace LeanStationaryHarmonicMaps
namespace StationaryHarmonicMap

/-- The a.e. boundary identity
`rho E'(rho) - (n-2) E(rho) = 2 rho Q'(rho)`.
-/
def BoundaryIdentity {n m : ℕ} (u : Domain n → Target m) (a : Domain n) (R0 : ℝ) : Prop :=
  ∀ᵐ rho ∂(volume.restrict (Ioo (0 : ℝ) R0)),
    rho * deriv (ballEnergy u a) rho - ((n : ℝ) - 2) * ballEnergy u a rho
      =
    2 * rho * deriv (ballRadialEnergy u a) rho

/-- Weak a.e. boundary identity, stated directly in terms of the weak gradient
energy and weak radial energy. -/
def WeakBoundaryIdentity {n m : ℕ}
    (Du : Domain n → Gradient n m) (a : Domain n) (R0 : ℝ) : Prop :=
  ∀ᵐ rho ∂(volume.restrict (Ioo (0 : ℝ) R0)),
    rho * deriv (weakBallEnergy Du a) rho - ((n : ℝ) - 2) * weakBallEnergy Du a rho
      =
    2 * rho * deriv (weakBallRadialEnergy Du a) rho

/-- The weak boundary identity at one fixed radius. -/
def WeakBoundaryRadiusIdentityAt {n m : ℕ}
    (Du : Domain n → Gradient n m) (a : Domain n) (rho : ℝ) : Prop :=
  rho * deriv (weakBallEnergy Du a) rho - ((n : ℝ) - 2) * weakBallEnergy Du a rho
    =
  2 * rho * deriv (weakBallRadialEnergy Du a) rho

/-- The signed identity at one fixed radius produced by the decreasing
sharp-cutoff approximation. -/
def WeakSharpCutoffRadiusIdentityAt {n m : ℕ}
    (Du : Domain n → Gradient n m) (a : Domain n) (rho : ℝ) : Prop :=
  ((n : ℝ) - 2) * weakBallEnergy Du a rho
      - rho * deriv (weakBallEnergy Du a) rho
    =
  -(2 * rho * deriv (weakBallRadialEnergy Du a) rho)

/-- The scalar defect whose vanishing is the sharp-cutoff radius identity. -/
def weakSharpCutoffDefect {n m : ℕ}
    (Du : Domain n → Gradient n m) (a : Domain n) (rho : ℝ) : ℝ :=
  ((n : ℝ) - 2) * weakBallEnergy Du a rho
      - rho * deriv (weakBallEnergy Du a) rho
      + 2 * rho * deriv (weakBallRadialEnergy Du a) rho

/-- Vanishing of the defect is exactly the signed sharp-cutoff identity at one
radius. -/
theorem weakSharpCutoffRadiusIdentityAt_iff_defect_eq_zero {n m : ℕ}
    {Du : Domain n → Gradient n m} {a : Domain n} {rho : ℝ} :
    WeakSharpCutoffRadiusIdentityAt Du a rho ↔
      weakSharpCutoffDefect Du a rho = 0 := by
  unfold WeakSharpCutoffRadiusIdentityAt weakSharpCutoffDefect
  constructor <;> intro h <;> linarith

/-- Pointwise conversion from vanishing defect to the signed sharp-cutoff radius
identity. -/
theorem weakSharpCutoffRadiusIdentityAt_of_defect_eq_zero {n m : ℕ}
    {Du : Domain n → Gradient n m} {a : Domain n} {rho : ℝ}
    (h : weakSharpCutoffDefect Du a rho = 0) :
    WeakSharpCutoffRadiusIdentityAt Du a rho :=
  weakSharpCutoffRadiusIdentityAt_iff_defect_eq_zero.mpr h

/-- The a.e. identity obtained from the radial stationarity identity by testing
with smooth radial cutoffs approximating the sharp cutoff of `B_r(a)`.

The sign reflects the fact that the approximating cutoffs decrease from `1` to
`0`, so their derivatives converge to `-δ_r`. -/
def WeakSharpCutoffLimitIdentity {n m : ℕ}
    (Du : Domain n → Gradient n m) (a : Domain n) (R0 : ℝ) : Prop :=
  ∀ᵐ rho ∂(volume.restrict (Ioo (0 : ℝ) R0)),
    WeakSharpCutoffRadiusIdentityAt Du a rho

/-- Distributional form of the sharp-cutoff limit: the sharp-cutoff defect pairs
to zero against every compactly supported smooth test function in `(0, R0)`. -/
def WeakSharpCutoffDistributionIdentity {n m : ℕ}
    (Du : Domain n → Gradient n m) (a : Domain n) (R0 : ℝ) : Prop :=
  ∀ g : ℝ → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) g →
      HasCompactSupport g →
        tsupport g ⊆ Ioo (0 : ℝ) R0 →
          (∫ rho : ℝ, g rho • weakSharpCutoffDefect Du a rho) = 0

/-- If the sharp-cutoff defect is locally integrable and vanishes as a
distribution on `(0, R0)`, then the sharp-cutoff radius identity holds a.e. -/
theorem weakSharpCutoffLimitIdentity_of_distribution {n m : ℕ}
    {Du : Domain n → Gradient n m} {a : Domain n} {R0 : ℝ}
    (hdefect_loc :
      LocallyIntegrableOn (fun rho : ℝ => weakSharpCutoffDefect Du a rho)
        (Ioo (0 : ℝ) R0) volume)
    (hdist : WeakSharpCutoffDistributionIdentity Du a R0) :
    WeakSharpCutoffLimitIdentity Du a R0 := by
  have hzero_global :
      ∀ᵐ rho ∂(volume : Measure ℝ),
        rho ∈ Ioo (0 : ℝ) R0 →
          weakSharpCutoffDefect Du a rho = 0 := by
    exact isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (μ := volume) hdefect_loc hdist
  have hzero_restrict :
      ∀ᵐ rho ∂volume.restrict (Ioo (0 : ℝ) R0),
        weakSharpCutoffDefect Du a rho = 0 := by
    exact (ae_restrict_iff' measurableSet_Ioo).2 hzero_global
  filter_upwards [hzero_restrict] with rho hzero
  exact weakSharpCutoffRadiusIdentityAt_of_defect_eq_zero hzero

/-- Pointwise algebra from the signed sharp-cutoff identity to the boundary
identity. -/
theorem weakBoundaryRadiusIdentityAt_of_sharpCutoff {n m : ℕ}
    {Du : Domain n → Gradient n m} {a : Domain n} {rho : ℝ}
    (h : WeakSharpCutoffRadiusIdentityAt Du a rho) :
    WeakBoundaryRadiusIdentityAt Du a rho := by
  unfold WeakSharpCutoffRadiusIdentityAt WeakBoundaryRadiusIdentityAt at *
  linarith

/-- Pointwise algebra from the boundary identity back to the signed
sharp-cutoff form. -/
theorem weakSharpCutoffRadiusIdentityAt_of_boundary {n m : ℕ}
    {Du : Domain n → Gradient n m} {a : Domain n} {rho : ℝ}
    (h : WeakBoundaryRadiusIdentityAt Du a rho) :
    WeakSharpCutoffRadiusIdentityAt Du a rho := by
  unfold WeakSharpCutoffRadiusIdentityAt WeakBoundaryRadiusIdentityAt at *
  linarith

/-- The sharp-cutoff limit form is just the boundary identity with all terms
moved across the equality. -/
theorem weakBoundaryIdentity_of_sharpCutoffLimit {n m : ℕ}
    {Du : Domain n → Gradient n m} {a : Domain n} {R0 : ℝ}
    (hlimit : WeakSharpCutoffLimitIdentity Du a R0) :
    WeakBoundaryIdentity Du a R0 := by
  filter_upwards [hlimit] with rho hrho
  exact weakBoundaryRadiusIdentityAt_of_sharpCutoff hrho

/-- Conversely, the boundary identity can be written in the signed
sharp-cutoff-limit form used by the approximation argument. -/
theorem weakSharpCutoffLimit_of_boundaryIdentity {n m : ℕ}
    {Du : Domain n → Gradient n m} {a : Domain n} {R0 : ℝ}
    (hboundary : WeakBoundaryIdentity Du a R0) :
    WeakSharpCutoffLimitIdentity Du a R0 := by
  filter_upwards [hboundary] with rho hrho
  exact weakSharpCutoffRadiusIdentityAt_of_boundary hrho

/-- Algebraic equivalence between the sharp-cutoff limit identity and the weak
boundary identity. -/
theorem weakSharpCutoffLimitIdentity_iff_boundaryIdentity {n m : ℕ}
    {Du : Domain n → Gradient n m} {a : Domain n} {R0 : ℝ} :
    WeakSharpCutoffLimitIdentity Du a R0 ↔ WeakBoundaryIdentity Du a R0 :=
  ⟨weakBoundaryIdentity_of_sharpCutoffLimit,
    weakSharpCutoffLimit_of_boundaryIdentity⟩

/-- The analytic cutoff-limit step still to be supplied: approximate the sharp
radial cutoff in the weak radial stationarity identity and pass to a.e. radii. -/
def WeakRadialCutoffLimitStep {n m : ℕ}
    (Du : Domain n → Gradient n m) (R0 : ℝ) : Prop :=
  WeakRadialStationarityIdentity Du R0 →
    WeakSharpCutoffLimitIdentity Du (0 : Domain n) R0

/-- Main one-dimensional radial integrand after applying coarea. -/
def weakRadialOneDimensionalMainIntegrand {n m : ℕ}
    (Du : Domain n → Gradient n m) (phi : ℝ → ℝ) (rho : ℝ) : ℝ :=
  (((n : ℝ) - 2) * phi rho + rho * deriv phi rho) *
    deriv (weakBallEnergy Du (0 : Domain n)) rho

/-- Radial-energy one-dimensional integrand after applying coarea. -/
def weakRadialOneDimensionalRhsIntegrand {n m : ℕ}
    (Du : Domain n → Gradient n m) (phi : ℝ → ℝ) (rho : ℝ) : ℝ :=
  (rho * deriv phi rho) *
    deriv (weakBallRadialEnergy Du (0 : Domain n)) rho

/-- One-dimensional radius form of the weak radial identity.  This is the
coarea/absolute-continuity form of `WeakRadialStationarityIdentity`: the ball
integrals have been converted into derivatives of the ball energy functions. -/
def WeakRadialOneDimensionalIdentity {n m : ℕ}
    (Du : Domain n → Gradient n m) (R0 : ℝ) : Prop :=
  ∀ phi : ℝ → ℝ,
    Differentiable ℝ phi →
        ContDiff ℝ 1 phi →
        HasCompactSupport phi →
          tsupport phi ⊆ Iio R0 →
          (∫ rho in Ioo (0 : ℝ) R0,
              weakRadialOneDimensionalMainIntegrand Du phi rho)
            =
          2 * ∫ rho in Ioo (0 : ℝ) R0,
              weakRadialOneDimensionalRhsIntegrand Du phi rho

/-- Weak radial stationarity restricted to the scalar cutoff class used by the
one-dimensional sharp-cutoff argument.  This is the `W^{1,2}_{loc}`-friendly
entry point: the vector-field regularity and integrability are discharged
before this interface. -/
def WeakRadialScalarCutoffStationarityIdentity {n m : ℕ}
    (Du : Domain n → Gradient n m) (R0 : ℝ) : Prop :=
  ∀ phi : ℝ → ℝ,
    Differentiable ℝ phi →
      ContDiff ℝ 1 phi →
        HasCompactSupport phi →
          tsupport phi ⊆ Iio R0 →
          (∫ x in Metric.ball (0 : Domain n) R0,
              weakRadialMainIntegrand Du phi x)
            =
          2 * ∫ x in Metric.ball (0 : Domain n) R0,
              weakRadialRhsIntegrand Du phi x

/-- The concrete coarea/radius-derivative formula needed to turn the spatial
radial identity into its one-dimensional radius form.  This is the place where a
future polar-coordinate or coarea formalization should plug in. -/
def WeakRadialCoareaDerivativeFormula {n m : ℕ}
    (Du : Domain n → Gradient n m) (R0 : ℝ) : Prop :=
  ∀ phi : ℝ → ℝ,
            Differentiable ℝ phi →
      ContDiff ℝ 1 phi →
        HasCompactSupport phi →
          tsupport phi ⊆ Iio R0 →
            ContDiff ℝ 1 (radialVectorField (n := n) phi) ∧
              (∫ x in Metric.ball (0 : Domain n) R0,
                  weakRadialMainIntegrand Du phi x)
                =
              (∫ rho in Ioo (0 : ℝ) R0,
                  weakRadialOneDimensionalMainIntegrand Du phi rho) ∧
              (∫ x in Metric.ball (0 : Domain n) R0,
                  weakRadialRhsIntegrand Du phi x)
                =
              (∫ rho in Ioo (0 : ℝ) R0,
                  weakRadialOneDimensionalRhsIntegrand Du phi rho)

/-- Regularity of the radial vector field for the scalar cutoffs used in the
one-dimensional argument.  The support properties are automatic from
`tsupport phi ⊆ Iio R0`; this predicate only records the remaining `C¹` fact. -/
def RadialVectorFieldContDiffForCutoffs (n : ℕ) (R0 : ℝ) : Prop :=
  ∀ phi : ℝ → ℝ,
    Differentiable ℝ phi →
      ContDiff ℝ 1 phi →
        HasCompactSupport phi →
          tsupport phi ⊆ Iio R0 →
            ContDiff ℝ 1 (radialVectorField (n := n) phi)

/-- The scalar cutoffs used for the radial vector-field tests are flat at the
origin.  This is the natural condition ensuring that `phi(|x|) x` is `C¹` at
`x = 0`. -/
def ScalarCutoffsConstNearOrigin (R0 : ℝ) : Prop :=
  ∀ phi : ℝ → ℝ,
    Differentiable ℝ phi →
      ContDiff ℝ 1 phi →
        HasCompactSupport phi →
          tsupport phi ⊆ Iio R0 →
            ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε → phi t = phi 0

/-- Flatness at the origin discharges the radial vector-field `C¹` regularity
ingredient. -/
theorem radialVectorFieldContDiffForCutoffs_of_constNearOrigin {n : ℕ} {R0 : ℝ}
    (hflat : ScalarCutoffsConstNearOrigin R0) :
    RadialVectorFieldContDiffForCutoffs n R0 := by
  intro phi hphi_diff hphi_cont hphi_compact hphi_support
  exact radialVectorField_contDiff_of_contDiff_const_near_origin
    (n := n) hphi_cont
    (hflat phi hphi_diff hphi_cont hphi_compact hphi_support)

/-- Weak `W^{1,2}_{loc}` stationarity gives the scalar-cutoff radial identity
for every cutoff in the flat-at-origin class used by the sharp-cutoff
argument. -/
theorem weak_radial_scalar_cutoff_identity_from_stationarity_of_W12Loc
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hstationary : WeakStationaryIn Du (Metric.ball (0 : Domain n) R0))
    (hW : W12LocIn u Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hflat : ScalarCutoffsConstNearOrigin R0) :
    WeakRadialScalarCutoffStationarityIdentity Du R0 := by
  intro phi hphi_diff hphi_cont hphi_compact hphi_support
  rcases exists_admissibleRadialCutoff_of_contDiff_const_near_origin
      (n := n) (R0 := R0) (phi := phi)
      hR0_nonneg hphi_diff hphi_cont hphi_compact hphi_support
      (hflat phi hphi_diff hphi_cont hphi_compact hphi_support) with
    ⟨M0, M1, hcut⟩
  exact weak_radial_identity_from_stationarity_of_W12Loc_cutoff
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω)
    (R0 := R0) (M0 := M0) (M1 := M1)
    hstationary hW hclosedBall_subset hcut

/-- Weak `W^{1,2}_{loc}` stationarity gives the scalar-cutoff radial identity
once the radial vector fields for the scalar cutoffs are known to be `C¹`.
This avoids the false global assumption that every scalar cutoff is flat near
the origin. -/
theorem weak_radial_scalar_cutoff_identity_from_stationarity_of_W12Loc_vectorFieldContDiff
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hstationary : WeakStationaryIn Du (Metric.ball (0 : Domain n) R0))
    (hW : W12LocIn u Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hX : RadialVectorFieldContDiffForCutoffs n R0) :
    WeakRadialScalarCutoffStationarityIdentity Du R0 := by
  intro phi hphi_diff hphi_cont hphi_compact hphi_support
  rcases exists_admissibleRadialCutoff_of_contDiff_and_vectorFieldContDiff
      (n := n) (R0 := R0) (phi := phi)
      hR0_nonneg hphi_diff hphi_cont hphi_compact hphi_support
      (hX phi hphi_diff hphi_cont hphi_compact hphi_support) with
    ⟨M0, M1, hcut⟩
  exact weak_radial_identity_from_stationarity_of_W12Loc_cutoff
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω)
    (R0 := R0) (M0 := M0) (M1 := M1)
    hstationary hW hclosedBall_subset hcut

/-- The true coarea/radius-integral content, separated from vector-field
regularity and support bookkeeping. -/
def WeakRadialCoareaIntegralFormula {n m : ℕ}
    (Du : Domain n → Gradient n m) (R0 : ℝ) : Prop :=
  ∀ phi : ℝ → ℝ,
    Differentiable ℝ phi →
      ContDiff ℝ 1 phi →
        HasCompactSupport phi →
          tsupport phi ⊆ Iio R0 →
            (∫ x in Metric.ball (0 : Domain n) R0,
                weakRadialMainIntegrand Du phi x)
              =
            (∫ rho in Ioo (0 : ℝ) R0,
                weakRadialOneDimensionalMainIntegrand Du phi rho) ∧
            (∫ x in Metric.ball (0 : Domain n) R0,
                weakRadialRhsIntegrand Du phi x)
              =
            (∫ rho in Ioo (0 : ℝ) R0,
                weakRadialOneDimensionalRhsIntegrand Du phi rho)

theorem thetaFactor_indicator_aestronglyMeasurable {n : ℕ} {R0 s r : ℝ}
    (hs : 0 < s) :
    AEStronglyMeasurable
      ((Ioo s r).indicator (thetaFactor n)) (radiusIntervalMeasure R0) := by
  rw [aestronglyMeasurable_indicator_iff measurableSet_Ioo]
  have hcont : ContinuousOn (thetaFactor n) (Icc s r) :=
    thetaFactor_continuousOn_Icc (n := n) (s := s) (r := r) hs
  have hmeas : MeasurableSet (Ioo s r ∩ Ioo (0 : ℝ) R0) :=
    measurableSet_Ioo.inter measurableSet_Ioo
  have hsubset : Ioo s r ∩ Ioo (0 : ℝ) R0 ⊆ Icc s r := by
    intro rho hrho
    exact ⟨le_of_lt hrho.1.1, le_of_lt hrho.1.2⟩
  have htheta :
      AEStronglyMeasurable (thetaFactor n)
        (volume.restrict (Ioo s r ∩ Ioo (0 : ℝ) R0)) :=
    hcont.aestronglyMeasurable_of_subset_isCompact isCompact_Icc hmeas hsubset
  simpa [radiusIntervalMeasure, Measure.restrict_restrict measurableSet_Ioo] using htheta

theorem radiusWeightOn_indicator_thetaFactor {n : ℕ} {R0 s r : ℝ}
    (hs : 0 < s) :
    RadiusWeightOn R0 ((Ioo s r).indicator (thetaFactor n)) := by
  have hmeas :
      AEStronglyMeasurable
        ((Ioo s r).indicator (thetaFactor n)) (radiusIntervalMeasure R0) :=
    thetaFactor_indicator_aestronglyMeasurable (n := n) (R0 := R0)
      (s := s) (r := r) hs
  have hcont : ContinuousOn (thetaFactor n) (Icc s r) :=
    thetaFactor_continuousOn_Icc (n := n) (s := s) (r := r) hs
  rcases isCompact_Icc.exists_bound_of_continuousOn hcont with ⟨C, hC⟩
  refine radiusWeightOn_indicator_of_aestronglyMeasurable_bound_on_set
    (R0 := R0) (c := thetaFactor n) (s := Ioo s r)
    (C := max C 0) hmeas (le_max_right C 0) ?_
  intro rho hrho
  exact (hC rho ⟨le_of_lt hrho.1, le_of_lt hrho.2⟩).trans (le_max_left C 0)

/-- Radius-integration formula for weak energy density.  This is the exact
coarea/ball-derivative statement needed for the energy part. -/
def WeakEnergyRadiusIntegralFormula {n m : ℕ}
    (Du : Domain n → Gradient n m) (R0 : ℝ) : Prop :=
  ∀ c : ℝ → ℝ,
    (∫ x in Metric.ball (0 : Domain n) R0, c ‖x‖ * weakEnergyDensity Du x)
      =
    (∫ rho in Ioo (0 : ℝ) R0,
      c rho * deriv (weakBallEnergy Du (0 : Domain n)) rho)

/-- Radius-integration formula for weak energy density, restricted to
measurable essentially bounded radius weights. -/
def WeakEnergyRadiusIntegralFormulaForWeights {n m : ℕ}
    (Du : Domain n → Gradient n m) (R0 : ℝ) : Prop :=
  ∀ c : ℝ → ℝ,
    RadiusWeightOn R0 c →
      (∫ x in Metric.ball (0 : Domain n) R0, c ‖x‖ * weakEnergyDensity Du x)
        =
      (∫ rho in Ioo (0 : ℝ) R0,
        c rho * deriv (weakBallEnergy Du (0 : Domain n)) rho)

/-- Radius-integration formula for weak radial-energy density. -/
def WeakRadialEnergyRadiusIntegralFormula {n m : ℕ}
    (Du : Domain n → Gradient n m) (R0 : ℝ) : Prop :=
  ∀ c : ℝ → ℝ,
    (∫ x in Metric.ball (0 : Domain n) R0,
      c ‖x‖ * weakRadialEnergyDensity Du (0 : Domain n) x)
      =
    (∫ rho in Ioo (0 : ℝ) R0,
      c rho * deriv (weakBallRadialEnergy Du (0 : Domain n)) rho)

/-- Radius-integration formula for weak radial-energy density, restricted to
measurable essentially bounded radius weights. -/
def WeakRadialEnergyRadiusIntegralFormulaForWeights {n m : ℕ}
    (Du : Domain n → Gradient n m) (R0 : ℝ) : Prop :=
  ∀ c : ℝ → ℝ,
    RadiusWeightOn R0 c →
      (∫ x in Metric.ball (0 : Domain n) R0,
        c ‖x‖ * weakRadialEnergyDensity Du (0 : Domain n) x)
        =
      (∫ rho in Ioo (0 : ℝ) R0,
        c rho * deriv (weakBallRadialEnergy Du (0 : Domain n)) rho)

/-- The two radius-derivative/coarea formulas needed for the weak
monotonicity argument, bundled as a single reusable analytic input. -/
def WeakRadiusIntegralFormulas {n m : ℕ}
    (Du : Domain n → Gradient n m) (R0 : ℝ) : Prop :=
  WeakEnergyRadiusIntegralFormula Du R0 ∧
    WeakRadialEnergyRadiusIntegralFormula Du R0

/-- The restricted-weight version of the bundled radius formulas. -/
def WeakRadiusIntegralFormulasForWeights {n m : ℕ}
    (Du : Domain n → Gradient n m) (R0 : ℝ) : Prop :=
  WeakEnergyRadiusIntegralFormulaForWeights Du R0 ∧
    WeakRadialEnergyRadiusIntegralFormulaForWeights Du R0

theorem weakEnergyRadiusIntegralFormulaForWeights_of_unrestricted {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (henergy : WeakEnergyRadiusIntegralFormula Du R0) :
    WeakEnergyRadiusIntegralFormulaForWeights Du R0 := by
  intro c _hc
  exact henergy c

theorem weakRadialEnergyRadiusIntegralFormulaForWeights_of_unrestricted {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hradial : WeakRadialEnergyRadiusIntegralFormula Du R0) :
    WeakRadialEnergyRadiusIntegralFormulaForWeights Du R0 := by
  intro c _hc
  exact hradial c

theorem weakRadiusIntegralFormulasForWeights_of_unrestricted {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hradius : WeakRadiusIntegralFormulas Du R0) :
    WeakRadiusIntegralFormulasForWeights Du R0 :=
  ⟨weakEnergyRadiusIntegralFormulaForWeights_of_unrestricted
      (n := n) (m := m) (Du := Du) (R0 := R0) hradius.1,
    weakRadialEnergyRadiusIntegralFormulaForWeights_of_unrestricted
      (n := n) (m := m) (Du := Du) (R0 := R0) hradius.2⟩

/-- The two standard radius-integration formulas imply the coarea integral
formula for the radial stationarity coefficients. -/
theorem weakRadialCoareaIntegralFormula_of_radiusIntegral {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (henergy : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial : WeakRadialEnergyRadiusIntegralFormula Du R0) :
    WeakRadialCoareaIntegralFormula Du R0 := by
  intro phi _hphi_diff _hphi_cont _hphi_compact _hphi_support
  constructor
  · simpa [weakRadialMainIntegrand, weakRadialMainCoeff,
      weakRadialOneDimensionalMainIntegrand] using
      henergy (fun rho : ℝ => ((n : ℝ) - 2) * phi rho + rho * deriv phi rho)
  · simpa [weakRadialRhsIntegrand, weakRadialRhsCoeff,
      weakRadialOneDimensionalRhsIntegrand] using
      hradial (fun rho : ℝ => rho * deriv phi rho)

/-- The restricted radius-integration formulas are enough for the scalar-cutoff
coarea step, because the two cutoff coefficients are measurable essentially
bounded radius weights. -/
theorem weakRadialCoareaIntegralFormula_of_radiusIntegralForWeights {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (henergy : WeakEnergyRadiusIntegralFormulaForWeights Du R0)
    (hradial : WeakRadialEnergyRadiusIntegralFormulaForWeights Du R0) :
    WeakRadialCoareaIntegralFormula Du R0 := by
  intro phi _hphi_diff hphi_cont _hphi_compact _hphi_support
  constructor
  · simpa [weakRadialMainIntegrand, weakRadialMainCoeff,
      weakRadialOneDimensionalMainIntegrand] using
      henergy
        (fun rho : ℝ => ((n : ℝ) - 2) * phi rho + rho * deriv phi rho)
        (radiusWeightOn_radialMainCoeff_of_contDiff_one
          (n := n) (R0 := R0) hphi_cont)
  · simpa [weakRadialRhsIntegrand, weakRadialRhsCoeff,
      weakRadialOneDimensionalRhsIntegrand] using
      hradial (fun rho : ℝ => rho * deriv phi rho)
        (radiusWeightOn_rho_mul_deriv_of_contDiff_one
          (R0 := R0) hphi_cont)

/-- Bundled radius-integration formulas imply the coarea integral formula. -/
theorem weakRadialCoareaIntegralFormula_of_radiusIntegralFormulas {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hradius : WeakRadiusIntegralFormulas Du R0) :
    WeakRadialCoareaIntegralFormula Du R0 :=
  weakRadialCoareaIntegralFormula_of_radiusIntegral
    (n := n) (m := m) (Du := Du) (R0 := R0) hradius.1 hradius.2

/-- Bundled restricted radius-integration formulas imply the scalar-cutoff
coarea integral formula. -/
theorem weakRadialCoareaIntegralFormula_of_radiusIntegralFormulasForWeights
    {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hradius : WeakRadiusIntegralFormulasForWeights Du R0) :
    WeakRadialCoareaIntegralFormula Du R0 :=
  weakRadialCoareaIntegralFormula_of_radiusIntegralForWeights
    (n := n) (m := m) (Du := Du) (R0 := R0) hradius.1 hradius.2

/-- The scalar-cutoff radial stationarity identity plus the coarea/radius
integral formula gives the one-dimensional radius identity. -/
theorem weakRadialOneDimensionalIdentity_of_scalar_cutoff_and_coarea {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hrad : WeakRadialScalarCutoffStationarityIdentity Du R0)
    (hcoarea : WeakRadialCoareaIntegralFormula Du R0) :
    WeakRadialOneDimensionalIdentity Du R0 := by
  intro phi hphi_diff hphi_cont hphi_compact hphi_support
  rcases hcoarea phi hphi_diff hphi_cont hphi_compact hphi_support with
    ⟨hmain, hrhs⟩
  have hspace :
      (∫ x in Metric.ball (0 : Domain n) R0,
          weakRadialMainIntegrand Du phi x)
        =
      2 * ∫ x in Metric.ball (0 : Domain n) R0,
          weakRadialRhsIntegrand Du phi x :=
    hrad phi hphi_diff hphi_cont hphi_compact hphi_support
  rw [← hmain, hspace, hrhs]

/-- Restricted radius-integration formulas plus the scalar-cutoff radial
stationarity identity give the one-dimensional radius identity. -/
theorem weakRadialOneDimensionalIdentity_of_scalar_cutoff_and_radiusIntegralForWeights
    {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hrad : WeakRadialScalarCutoffStationarityIdentity Du R0)
    (henergy : WeakEnergyRadiusIntegralFormulaForWeights Du R0)
    (hradial : WeakRadialEnergyRadiusIntegralFormulaForWeights Du R0) :
    WeakRadialOneDimensionalIdentity Du R0 :=
  weakRadialOneDimensionalIdentity_of_scalar_cutoff_and_coarea
    (n := n) (m := m) (Du := Du) (R0 := R0) hrad
    (weakRadialCoareaIntegralFormula_of_radiusIntegralForWeights
      (n := n) (m := m) (Du := Du) (R0 := R0) henergy hradial)

/-- Vector-field regularity plus the coarea/radius-integral formula gives the
combined coarea derivative formula used by the radial-to-boundary route. -/
theorem weakRadialCoareaDerivativeFormula_of_contDiff_and_integral {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hX : RadialVectorFieldContDiffForCutoffs n R0)
    (hcoarea : WeakRadialCoareaIntegralFormula Du R0) :
    WeakRadialCoareaDerivativeFormula Du R0 := by
  intro phi hphi_diff hphi_cont hphi_compact hphi_support
  rcases hcoarea phi hphi_diff hphi_cont hphi_compact hphi_support with ⟨hmain, hrhs⟩
  exact ⟨hX phi hphi_diff hphi_cont hphi_compact hphi_support, hmain, hrhs⟩

/-- The coarea and radius-derivative step translating the spatial radial
identity into its one-dimensional radius form. -/
def WeakRadialCoareaDerivativeStep {n m : ℕ}
    (Du : Domain n → Gradient n m) (R0 : ℝ) : Prop :=
  WeakRadialStationarityIdentity Du R0 →
    WeakRadialOneDimensionalIdentity Du R0

/-- A concrete radial coarea/radius-derivative formula discharges the abstract
coarea step. -/
theorem weakRadialCoareaDerivativeStep_of_formula {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hformula : WeakRadialCoareaDerivativeFormula Du R0) :
    WeakRadialCoareaDerivativeStep Du R0 := by
  intro hrad phi hphi hphi_cont hphi_compact hphi_support
  rcases hformula phi hphi hphi_cont hphi_compact hphi_support with
    ⟨hXdiff, hmain, hrhs⟩
  have hXcompact : HasCompactSupport (radialVectorField (n := n) phi) :=
    radialVectorField_hasCompactSupport_of_scalar_tsupport_Iio
      (n := n) (phi := phi) (R0 := R0) hphi_support
  have hXsupport :
      tsupport (radialVectorField (n := n) phi) ⊆ Metric.ball (0 : Domain n) R0 :=
    radialVectorField_tsupport_subset_ball_of_scalar_tsupport_Iio
      (n := n) (phi := phi) (R0 := R0) hphi_support
  have hspace :
      (∫ x in Metric.ball (0 : Domain n) R0,
          weakRadialMainIntegrand Du phi x)
        =
      2 * ∫ x in Metric.ball (0 : Domain n) R0,
          weakRadialRhsIntegrand Du phi x :=
    hrad phi hphi hXdiff hXcompact hXsupport
  rw [← hmain, hspace, hrhs]

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps

end
