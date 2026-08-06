/-
Copyright (c) 2026 Wei Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Wang
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.PrimitiveCutoffs
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.Euclidean

/-!
# Radius absolute continuity inputs

This module contains the abstract absolute-continuity and integration-by-parts
interfaces for the radius-variable energy functions.

These radius formulas are internal scaffolding.  They remain visible so the
coarea and one-dimensional calculus steps can be audited independently, while
public users should rely on `MainTheorem.lean`.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace LeanStationaryHarmonicMaps
namespace StationaryHarmonicMap

/-- The one-dimensional integration-by-parts step to be proved from
`WeakRadialOneDimensionalIdentity`. -/
def WeakOneDimensionalIBPStep {n m : ℕ}
    (Du : Domain n → Gradient n m) (R0 : ℝ) : Prop :=
  WeakRadialOneDimensionalIdentity Du R0 →
    WeakOneDimensionalDefectDerivativeIdentity Du R0

/-- The concrete integration-by-parts identity needed to turn the
one-dimensional radial identity into a defect-derivative identity. -/
def WeakOneDimensionalIBPFormula {n m : ℕ}
    (Du : Domain n → Gradient n m) (R0 : ℝ) : Prop :=
  ∀ phi : ℝ → ℝ,
    Differentiable ℝ phi →
      ContDiff ℝ 1 phi →
        HasCompactSupport phi →
          tsupport phi ⊆ Iio R0 →
            (∫ rho in Ioo (0 : ℝ) R0,
              (-deriv phi rho) * weakSharpCutoffDefect Du (0 : Domain n) rho)
              =
            (∫ rho in Ioo (0 : ℝ) R0,
              weakRadialOneDimensionalMainIntegrand Du phi rho)
              -
            2 * ∫ rho in Ioo (0 : ℝ) R0,
              weakRadialOneDimensionalRhsIntegrand Du phi rho

/-- The genuine one-dimensional energy integration-by-parts input:
`∫ -phi' ((n-2)E) = ∫ ((n-2)phi) E'`.  This is the part that ultimately comes
from absolute continuity of the ball energy function. -/
def WeakBallEnergyIntegrationByPartsFormula {n m : ℕ}
    (Du : Domain n → Gradient n m) (R0 : ℝ) : Prop :=
  ∀ phi : ℝ → ℝ,
    Differentiable ℝ phi →
      ContDiff ℝ 1 phi →
        HasCompactSupport phi →
          tsupport phi ⊆ Iio R0 →
            (∫ rho in Ioo (0 : ℝ) R0,
              (-deriv phi rho) *
                (((n : ℝ) - 2) * weakBallEnergy Du (0 : Domain n) rho))
              =
            (∫ rho in Ioo (0 : ℝ) R0,
              (((n : ℝ) - 2) * phi rho) *
                deriv (weakBallEnergy Du (0 : Domain n)) rho)

/-- Integrability side conditions needed only to justify splitting the Bochner
integrals in the one-dimensional IBP algebra. -/
def WeakOneDimensionalIBPIntegrability {n m : ℕ}
    (Du : Domain n → Gradient n m) (R0 : ℝ) : Prop :=
  ∀ phi : ℝ → ℝ,
    Differentiable ℝ phi →
      ContDiff ℝ 1 phi →
        HasCompactSupport phi →
          tsupport phi ⊆ Iio R0 →
            IntegrableOn
              (fun rho : ℝ =>
                (-deriv phi rho) *
                  (((n : ℝ) - 2) * weakBallEnergy Du (0 : Domain n) rho))
              (Ioo (0 : ℝ) R0) volume ∧
            IntegrableOn
              (fun rho : ℝ =>
                (((n : ℝ) - 2) * phi rho) *
                  deriv (weakBallEnergy Du (0 : Domain n)) rho)
              (Ioo (0 : ℝ) R0) volume ∧
            IntegrableOn
              (fun rho : ℝ =>
                (rho * deriv phi rho) *
                  deriv (weakBallEnergy Du (0 : Domain n)) rho)
              (Ioo (0 : ℝ) R0) volume ∧
            IntegrableOn
              (fun rho : ℝ =>
                (rho * deriv phi rho) *
                  deriv (weakBallRadialEnergy Du (0 : Domain n)) rho)
              (Ioo (0 : ℝ) R0) volume

/-- The absolute-continuity target for the radius functions used in the weak
monotonicity proof.  This is the analytic statement one ultimately gets from
coarea/radius differentiation in the `W^{1,2}_{loc}` setting. -/
def WeakEnergyAbsolutelyContinuousOnRadii {n m : ℕ}
    (Du : Domain n → Gradient n m) (R0 : ℝ) : Prop :=
  (∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b ≤ R0 →
    AbsolutelyContinuousOnInterval (weakBallEnergy Du (0 : Domain n)) a b) ∧
  (∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b ≤ R0 →
    AbsolutelyContinuousOnInterval (weakBallRadialEnergy Du (0 : Domain n)) a b)

/-- Absolute continuity, in the radius variable, of the ball integral generated
by a scalar integrand.  This is the generic analytic statement supplied by the
coarea/radius theorem for `L¹` functions. -/
def BallIntegralRadiusAbsolutelyContinuous {n : ℕ}
    (f : Domain n → ℝ) (R0 : ℝ) : Prop :=
  ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b ≤ R0 →
    AbsolutelyContinuousOnInterval
      (fun r : ℝ => ∫ x in Metric.ball (0 : Domain n) r, f x) a b

/-- The reusable analytic theorem we still need from coarea/thin-annulus
estimates: in positive dimension, every `L¹` scalar integrand on `B_R0` has an
absolutely continuous ball-integral radius function on `[0, R0]`.  The positive
dimension assumption is essential: in dimension zero the open ball jumps at
radius `0`. -/
def BallIntegralRadiusACOfIntegrableOnBall (n : ℕ) : Prop :=
  [NeZero n] →
  ∀ {f : Domain n → ℝ} {R0 : ℝ},
    IntegrableOn f (Metric.ball (0 : Domain n) R0) volume →
      BallIntegralRadiusAbsolutelyContinuous f R0

/-- Absolute continuity of a scalar ball-integral radius function gives local
integrability of its a.e. derivative on the open radius interval. -/
theorem locallyIntegrableOn_deriv_ballIntegral_of_radius_ac {n : ℕ}
    {f : Domain n → ℝ} {R0 : ℝ}
    (hac : BallIntegralRadiusAbsolutelyContinuous f R0) :
    LocallyIntegrableOn
      (fun rho : ℝ => deriv (fun r : ℝ =>
        ∫ x in Metric.ball (0 : Domain n) r, f x) rho)
      (Ioo (0 : ℝ) R0) volume := by
  intro x hx
  let a : ℝ := x / 2
  let b : ℝ := (x + R0) / 2
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact div_nonneg (le_of_lt hx.1) (by norm_num)
  have hxa : a < x := by
    dsimp [a]
    nlinarith [hx.1]
  have hxb : x < b := by
    dsimp [b]
    nlinarith [hx.2]
  have hab : a ≤ b := le_of_lt (hxa.trans hxb)
  have hbR : b ≤ R0 := by
    dsimp [b]
    nlinarith [hx.2]
  have hnhds : Ioo a b ∈ 𝓝[Ioo (0 : ℝ) R0] x :=
    nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds ⟨hxa, hxb⟩)
  refine ⟨Ioo a b, hnhds, ?_⟩
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp
    ((hac ha0 hab hbR).intervalIntegrable_deriv)

/-- The reusable coarea/radius-derivative theorem still to be supplied
geometrically: every `L¹` scalar density on a ball has the radius integration
formula against arbitrary scalar radius weights.  The specialized weak energy
and radial-energy formulas below are just applications of this statement to the
two relevant densities. -/
def BallIntegralRadiusDerivativeFormula (n : ℕ) : Prop :=
  [NeZero n] →
  ∀ {f : Domain n → ℝ} {R0 : ℝ},
    IntegrableOn f (Metric.ball (0 : Domain n) R0) volume →
      ∀ c : ℝ → ℝ,
        (∫ x in Metric.ball (0 : Domain n) R0, c ‖x‖ * f x)
          =
        (∫ rho in Ioo (0 : ℝ) R0,
          c rho * deriv (fun r : ℝ =>
            ∫ x in Metric.ball (0 : Domain n) r, f x) rho)

/-- Restricted-weight version of `BallIntegralRadiusDerivativeFormula`, using
the measurable essentially bounded radius weights that occur in the weak
monotonicity proof. -/
def BallIntegralRadiusDerivativeFormulaForWeights (n : ℕ) : Prop :=
  [NeZero n] →
  ∀ {f : Domain n → ℝ} {R0 : ℝ},
    IntegrableOn f (Metric.ball (0 : Domain n) R0) volume →
      ∀ c : ℝ → ℝ,
        RadiusWeightOn R0 c →
          (∫ x in Metric.ball (0 : Domain n) R0, c ‖x‖ * f x)
            =
          (∫ rho in Ioo (0 : ℝ) R0,
            c rho * deriv (fun r : ℝ =>
              ∫ x in Metric.ball (0 : Domain n) r, f x) rho)

/-- Pure radial pushforward/coarea input: a scalar density on a Euclidean ball
has some one-dimensional radial density `D` representing all integrals against
radius weights.  No derivative of the ball integral is mentioned here. -/
def BallIntegralRadiusWeightedRepresentation (n : ℕ) : Prop :=
  [NeZero n] →
  ∀ {f : Domain n → ℝ} {R0 : ℝ},
    IntegrableOn f (Metric.ball (0 : Domain n) R0) volume →
      ∃ D : ℝ → ℝ,
        LocallyIntegrableOn D (Ioo (0 : ℝ) R0) volume ∧
        ∀ c : ℝ → ℝ,
          (∫ x in Metric.ball (0 : Domain n) R0, c ‖x‖ * f x)
            =
          (∫ rho in Ioo (0 : ℝ) R0, c rho * D rho)

/-- Restricted-weight version of the pure radial pushforward/coarea input. -/
def BallIntegralRadiusWeightedRepresentationForWeights (n : ℕ) : Prop :=
  [NeZero n] →
  ∀ {f : Domain n → ℝ} {R0 : ℝ},
    IntegrableOn f (Metric.ball (0 : Domain n) R0) volume →
      ∃ D : ℝ → ℝ,
        LocallyIntegrableOn D (Ioo (0 : ℝ) R0) volume ∧
        ∀ c : ℝ → ℝ,
          RadiusWeightOn R0 c →
            (∫ x in Metric.ball (0 : Domain n) R0, c ‖x‖ * f x)
              =
            (∫ rho in Ioo (0 : ℝ) R0, c rho * D rho)

/-- One-dimensional identification input: whenever a radial density represents
all radius-weighted integrals of `f`, it agrees a.e. with the derivative of the
ball integral radius function. -/
def BallIntegralRadiusDerivativeIdentification (n : ℕ) : Prop :=
  [NeZero n] →
  ∀ {f : Domain n → ℝ} {R0 : ℝ} {D : ℝ → ℝ},
    IntegrableOn f (Metric.ball (0 : Domain n) R0) volume →
      LocallyIntegrableOn D (Ioo (0 : ℝ) R0) volume →
      (∀ c : ℝ → ℝ,
        (∫ x in Metric.ball (0 : Domain n) R0, c ‖x‖ * f x)
          =
        (∫ rho in Ioo (0 : ℝ) R0, c rho * D rho)) →
        ∀ᵐ rho ∂volume.restrict (Ioo (0 : ℝ) R0),
          deriv (fun r : ℝ =>
            ∫ x in Metric.ball (0 : Domain n) r, f x) rho = D rho

/-- Restricted-weight version of the one-dimensional derivative identification
input.  This is the realistic version of the uniqueness step: bounded
measurable test weights determine equality a.e. on the radius interval. -/
def BallIntegralRadiusDerivativeIdentificationForWeights (n : ℕ) : Prop :=
  [NeZero n] →
  ∀ {f : Domain n → ℝ} {R0 : ℝ} {D : ℝ → ℝ},
    IntegrableOn f (Metric.ball (0 : Domain n) R0) volume →
      LocallyIntegrableOn D (Ioo (0 : ℝ) R0) volume →
      (∀ c : ℝ → ℝ,
        RadiusWeightOn R0 c →
          (∫ x in Metric.ball (0 : Domain n) R0, c ‖x‖ * f x)
            =
          (∫ rho in Ioo (0 : ℝ) R0, c rho * D rho)) →
        ∀ᵐ rho ∂radiusIntervalMeasure R0,
          deriv (fun r : ℝ =>
            ∫ x in Metric.ball (0 : Domain n) r, f x) rho = D rho

/-- A more geometric way to supply `BallIntegralRadiusDerivativeFormula`: for
each scalar density on a ball, produce a one-dimensional radial density `D`
which both represents all radius-weighted integrals and agrees a.e. with the
derivative of the ball integral radius function.  This separates the genuine
coarea/pushforward theorem from the one-dimensional derivative identification. -/
def BallIntegralRadiusDerivativeRepresentation (n : ℕ) : Prop :=
  [NeZero n] →
  ∀ {f : Domain n → ℝ} {R0 : ℝ},
    IntegrableOn f (Metric.ball (0 : Domain n) R0) volume →
      ∃ D : ℝ → ℝ,
        LocallyIntegrableOn D (Ioo (0 : ℝ) R0) volume ∧
        (∀ᵐ rho ∂volume.restrict (Ioo (0 : ℝ) R0),
          deriv (fun r : ℝ =>
            ∫ x in Metric.ball (0 : Domain n) r, f x) rho = D rho) ∧
        ∀ c : ℝ → ℝ,
          (∫ x in Metric.ball (0 : Domain n) R0, c ‖x‖ * f x)
            =
          (∫ rho in Ioo (0 : ℝ) R0, c rho * D rho)

/-- Restricted-weight version of the combined radial-density representation. -/
def BallIntegralRadiusDerivativeRepresentationForWeights (n : ℕ) : Prop :=
  [NeZero n] →
  ∀ {f : Domain n → ℝ} {R0 : ℝ},
    IntegrableOn f (Metric.ball (0 : Domain n) R0) volume →
      ∃ D : ℝ → ℝ,
        LocallyIntegrableOn D (Ioo (0 : ℝ) R0) volume ∧
        (∀ᵐ rho ∂radiusIntervalMeasure R0,
          deriv (fun r : ℝ =>
            ∫ x in Metric.ball (0 : Domain n) r, f x) rho = D rho) ∧
        ∀ c : ℝ → ℝ,
          RadiusWeightOn R0 c →
            (∫ x in Metric.ball (0 : Domain n) R0, c ‖x‖ * f x)
              =
            (∫ rho in Ioo (0 : ℝ) R0, c rho * D rho)

/-- The unrestricted generic coarea formula implies the restricted-weight
version. -/
theorem ballIntegralRadiusDerivativeFormulaForWeights_of_unrestricted {n : ℕ}
    (hcoarea : BallIntegralRadiusDerivativeFormula n) :
    BallIntegralRadiusDerivativeFormulaForWeights n := by
  intro hne f R0 hf c _hc
  exact hcoarea (f := f) (R0 := R0) hf c

/-- The unrestricted weighted representation implies its restricted-weight
version. -/
theorem ballIntegralRadiusWeightedRepresentationForWeights_of_unrestricted
    {n : ℕ}
    (hweighted : BallIntegralRadiusWeightedRepresentation n) :
    BallIntegralRadiusWeightedRepresentationForWeights n := by
  intro hne f R0 hf
  rcases hweighted (f := f) (R0 := R0) hf with ⟨D, hD_loc, hD⟩
  exact ⟨D, hD_loc, fun c _hc => hD c⟩

/-- A pure weighted radial representation plus the a.e. derivative
identification give the combined radial-density representation. -/
theorem ballIntegralRadiusDerivativeRepresentation_of_weightedRepresentation
    {n : ℕ}
    (hweighted : BallIntegralRadiusWeightedRepresentation n)
    (hidentify : BallIntegralRadiusDerivativeIdentification n) :
    BallIntegralRadiusDerivativeRepresentation n := by
  intro hne f R0 hf
  let : NeZero n := hne
  rcases hweighted (f := f) (R0 := R0) hf with ⟨D, hD_loc, hD_weighted⟩
  exact ⟨D, hD_loc,
    hidentify (f := f) (R0 := R0) (D := D) hf hD_loc hD_weighted, hD_weighted⟩

/-- Restricted weighted representation plus restricted a.e. derivative
identification give the restricted combined representation. -/
theorem ballIntegralRadiusDerivativeRepresentationForWeights_of_weightedRepresentation
    {n : ℕ}
    (hweighted : BallIntegralRadiusWeightedRepresentationForWeights n)
    (hidentify : BallIntegralRadiusDerivativeIdentificationForWeights n) :
    BallIntegralRadiusDerivativeRepresentationForWeights n := by
  intro hne f R0 hf
  let : NeZero n := hne
  rcases hweighted (f := f) (R0 := R0) hf with ⟨D, hD_loc, hD_weighted⟩
  exact ⟨D, hD_loc,
    hidentify (f := f) (R0 := R0) (D := D) hf hD_loc hD_weighted, hD_weighted⟩

/-- The radial-density representation immediately gives the older packaged
coarea/radius-derivative formula. -/
theorem ballIntegralRadiusDerivativeFormula_of_representation {n : ℕ}
    (hrep : BallIntegralRadiusDerivativeRepresentation n) :
    BallIntegralRadiusDerivativeFormula n := by
  intro hne f R0 hf c
  let : NeZero n := hne
  rcases hrep (f := f) (R0 := R0) hf with ⟨D, _hD_loc, hD_deriv, hD_weighted⟩
  rw [hD_weighted c]
  apply integral_congr_ae
  filter_upwards [hD_deriv] with rho hderiv
  rw [hderiv]

/-- The restricted radial-density representation gives the restricted packaged
coarea/radius-derivative formula. -/
theorem ballIntegralRadiusDerivativeFormulaForWeights_of_representation
    {n : ℕ}
    (hrep : BallIntegralRadiusDerivativeRepresentationForWeights n) :
    BallIntegralRadiusDerivativeFormulaForWeights n := by
  intro hne f R0 hf c hc
  let : NeZero n := hne
  rcases hrep (f := f) (R0 := R0) hf with ⟨D, _hD_loc, hD_deriv, hD_weighted⟩
  rw [hD_weighted c hc]
  apply integral_congr_ae
  filter_upwards [hD_deriv] with rho hderiv
  rw [hderiv]

/-- Restricted weighted representation and restricted derivative identification
directly give the restricted coarea/radius-derivative formula. -/
theorem ballIntegralRadiusDerivativeFormulaForWeights_of_weightedRepresentation
    {n : ℕ}
    (hweighted : BallIntegralRadiusWeightedRepresentationForWeights n)
    (hidentify : BallIntegralRadiusDerivativeIdentificationForWeights n) :
    BallIntegralRadiusDerivativeFormulaForWeights n :=
  ballIntegralRadiusDerivativeFormulaForWeights_of_representation
    (n := n)
    (ballIntegralRadiusDerivativeRepresentationForWeights_of_weightedRepresentation
      (n := n) hweighted hidentify)

/-- A one-dimensional form of the remaining Euclidean geometry needed for the
thin radial-shell estimate: the radius function `r ↦ |B_r|` is absolutely
continuous on compact nonnegative intervals.  This is discharged through the
project Euclidean interface. -/
def EuclideanBallVolumeAbsolutelyContinuous (n : ℕ) : Prop :=
  [NeZero n] →
  ∀ {a b : ℝ}, 0 ≤ a → a ≤ b →
    AbsolutelyContinuousOnInterval
      (fun r : ℝ => (volume (Metric.ball (0 : Domain n) r)).toReal) a b

/-- The radial open shell between two radii.  We use the unordered endpoints so
that the shell attached to an interval in the absolute-continuity definition is
independent of its orientation. -/
def RadialOpenShell {n : ℕ} (r s : ℝ) : Set (Domain n) :=
  {x | ‖x‖ ∈ Ioo (min r s) (max r s)}

/-- The union of the radial open shells associated to a finite interval family
from the absolute-continuity filter. -/
def RadialOpenShells {n : ℕ} (E : ℕ × (ℕ → ℝ × ℝ)) : Set (Domain n) :=
  ⋃ i ∈ Finset.range E.1, RadialOpenShell (n := n) (E.2 i).1 (E.2 i).2

/-- The geometric thin-annulus estimate needed for the `L¹` radius theorem:
finite unions of radial shells have volume tending to zero when the total
one-dimensional length of the generating intervals tends to zero. -/
def RadialOpenShellsVolumeTendstoZero (n : ℕ) : Prop :=
  [NeZero n] →
  ∀ {a b : ℝ}, 0 ≤ a → a ≤ b →
    Filter.Tendsto
      (fun E : ℕ × (ℕ → ℝ × ℝ) => volume (RadialOpenShells (n := n) E))
      (AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
        Filter.principal (AbsolutelyContinuousOnInterval.disjWithin a b))
      (𝓝 0)

/-- A radial open shell is Borel measurable. -/
theorem radialOpenShell_measurable {n : ℕ} (r s : ℝ) :
    MeasurableSet (RadialOpenShell (n := n) r s) := by
  exact (isOpen_Ioo.preimage continuous_norm).measurableSet

/-- The open shell is contained in the unordered half-open interval shell used
by the absolute-continuity filter. -/
theorem radialOpenShell_subset_uIoc {n : ℕ} (r s : ℝ) :
    RadialOpenShell (n := n) r s ⊆ {x : Domain n | ‖x‖ ∈ uIoc r s} := by
  intro x hx
  exact ⟨hx.1, hx.2.le⟩

/-- A single radial shell has volume controlled by the variation of the ball
volume radius function across its two endpoints. -/
theorem radialOpenShell_volume_le_ballVolume_dist {n : ℕ}
    (r s : ℝ) :
    volume (RadialOpenShell (n := n) r s) ≤
      ENNReal.ofReal
        (dist
          ((volume (Metric.ball (0 : Domain n) r)).toReal)
          ((volume (Metric.ball (0 : Domain n) s)).toReal)) := by
  let lo : ℝ := min r s
  let hi : ℝ := max r s
  have hsubset :
      RadialOpenShell (n := n) r s ⊆
        Metric.ball (0 : Domain n) hi \ Metric.ball (0 : Domain n) lo := by
    intro x hx
    constructor
    · simpa [Metric.mem_ball, dist_eq_norm, hi] using hx.2
    · intro hxlo
      have hlt : ‖x‖ < lo := by
        simpa [Metric.mem_ball, dist_eq_norm, lo] using hxlo
      exact (not_lt_of_ge hx.1.le) hlt
  have hle0 :
      volume (RadialOpenShell (n := n) r s) ≤
        volume (Metric.ball (0 : Domain n) hi \ Metric.ball (0 : Domain n) lo) :=
    measure_mono hsubset
  have hdiff :
      volume (Metric.ball (0 : Domain n) hi \ Metric.ball (0 : Domain n) lo) =
        volume (Metric.ball (0 : Domain n) hi) -
          volume (Metric.ball (0 : Domain n) lo) :=
    measure_sdiff (Metric.ball_subset_ball min_le_max)
      measurableSet_ball.nullMeasurableSet measure_ball_lt_top.ne
  have hle1 :
      volume (RadialOpenShell (n := n) r s) ≤
        volume (Metric.ball (0 : Domain n) hi) -
          volume (Metric.ball (0 : Domain n) lo) := by
    simpa [hdiff] using hle0
  have hvol_le :
      volume (Metric.ball (0 : Domain n) lo) ≤
        volume (Metric.ball (0 : Domain n) hi) :=
    measure_mono (Metric.ball_subset_ball min_le_max)
  have htop_hi : volume (Metric.ball (0 : Domain n) hi) ≠ ∞ :=
    measure_ball_lt_top.ne
  have htop_lo : volume (Metric.ball (0 : Domain n) lo) ≠ ∞ :=
    measure_ball_lt_top.ne
  have hsub_toReal :
      (volume (Metric.ball (0 : Domain n) hi) -
          volume (Metric.ball (0 : Domain n) lo)).toReal =
        (volume (Metric.ball (0 : Domain n) hi)).toReal -
          (volume (Metric.ball (0 : Domain n) lo)).toReal :=
    ENNReal.toReal_sub_of_le hvol_le htop_hi
  have htarget :
      volume (Metric.ball (0 : Domain n) hi) -
          volume (Metric.ball (0 : Domain n) lo) =
        ENNReal.ofReal
          ((volume (Metric.ball (0 : Domain n) hi)).toReal -
            (volume (Metric.ball (0 : Domain n) lo)).toReal) := by
    rw [← hsub_toReal]
    exact (ENNReal.ofReal_toReal (ENNReal.sub_ne_top htop_hi)).symm
  have hdist_eq :
      dist
          ((volume (Metric.ball (0 : Domain n) r)).toReal)
          ((volume (Metric.ball (0 : Domain n) s)).toReal)
        =
      (volume (Metric.ball (0 : Domain n) hi)).toReal -
        (volume (Metric.ball (0 : Domain n) lo)).toReal := by
    by_cases hrs : r ≤ s
    · have hlo : lo = r := min_eq_left hrs
      have hhi : hi = s := max_eq_right hrs
      have hle_rs :
          volume (Metric.ball (0 : Domain n) r) ≤
            volume (Metric.ball (0 : Domain n) s) :=
        measure_mono (Metric.ball_subset_ball hrs)
      have hle_real :
          (volume (Metric.ball (0 : Domain n) r)).toReal ≤
            (volume (Metric.ball (0 : Domain n) s)).toReal :=
        (ENNReal.toReal_le_toReal measure_ball_lt_top.ne
          measure_ball_lt_top.ne).2 hle_rs
      rw [Real.dist_eq, hlo, hhi, abs_sub_comm]
      exact abs_of_nonneg (sub_nonneg.mpr hle_real)
    · have hsr : s ≤ r := le_of_not_ge hrs
      have hlo : lo = s := min_eq_right hsr
      have hhi : hi = r := max_eq_left hsr
      have hle_sr :
          volume (Metric.ball (0 : Domain n) s) ≤
            volume (Metric.ball (0 : Domain n) r) :=
        measure_mono (Metric.ball_subset_ball hsr)
      have hle_real :
          (volume (Metric.ball (0 : Domain n) s)).toReal ≤
            (volume (Metric.ball (0 : Domain n) r)).toReal :=
        (ENNReal.toReal_le_toReal measure_ball_lt_top.ne
          measure_ball_lt_top.ne).2 hle_sr
      simp [Real.dist_eq, hlo, hhi, abs_of_nonneg (sub_nonneg.mpr hle_real)]
  calc
    volume (RadialOpenShell (n := n) r s)
        ≤ volume (Metric.ball (0 : Domain n) hi) -
            volume (Metric.ball (0 : Domain n) lo) := hle1
    _ =
        ENNReal.ofReal
          ((volume (Metric.ball (0 : Domain n) hi)).toReal -
            (volume (Metric.ball (0 : Domain n) lo)).toReal) := htarget
    _ =
        ENNReal.ofReal
          (dist
            ((volume (Metric.ball (0 : Domain n) r)).toReal)
            ((volume (Metric.ball (0 : Domain n) s)).toReal)) := by
      rw [hdist_eq]

/-- Finite unions of radial open shells are measurable. -/
theorem radialOpenShells_measurable {n : ℕ} (E : ℕ × (ℕ → ℝ × ℝ)) :
    MeasurableSet (RadialOpenShells (n := n) E) := by
  classical
  unfold RadialOpenShells
  exact Finset.measurableSet_biUnion (Finset.range E.1)
    (fun i _hi => radialOpenShell_measurable (n := n) (E.2 i).1 (E.2 i).2)

/-- A finite union of radial shells is controlled by the corresponding
variation sum of the ball-volume radius function. -/
theorem radialOpenShells_volume_le_ballVolume_variation {n : ℕ}
    (E : ℕ × (ℕ → ℝ × ℝ)) :
    volume (RadialOpenShells (n := n) E) ≤
      ENNReal.ofReal
        (∑ i ∈ Finset.range E.1,
          dist
            ((volume (Metric.ball (0 : Domain n) (E.2 i).1)).toReal)
            ((volume (Metric.ball (0 : Domain n) (E.2 i).2)).toReal)) := by
  classical
  calc
    volume (RadialOpenShells (n := n) E)
        =
      volume (⋃ i ∈ Finset.range E.1,
        RadialOpenShell (n := n) (E.2 i).1 (E.2 i).2) := by
        rfl
    _ ≤
      ∑ i ∈ Finset.range E.1,
        volume (RadialOpenShell (n := n) (E.2 i).1 (E.2 i).2) :=
        measure_biUnion_finset_le (Finset.range E.1)
          (fun i => RadialOpenShell (n := n) (E.2 i).1 (E.2 i).2)
    _ ≤
      ∑ i ∈ Finset.range E.1,
        ENNReal.ofReal
          (dist
            ((volume (Metric.ball (0 : Domain n) (E.2 i).1)).toReal)
            ((volume (Metric.ball (0 : Domain n) (E.2 i).2)).toReal)) := by
        exact Finset.sum_le_sum (fun i _hi =>
          radialOpenShell_volume_le_ballVolume_dist
            (n := n) (E.2 i).1 (E.2 i).2)
    _ =
      ENNReal.ofReal
        (∑ i ∈ Finset.range E.1,
          dist
            ((volume (Metric.ball (0 : Domain n) (E.2 i).1)).toReal)
            ((volume (Metric.ball (0 : Domain n) (E.2 i).2)).toReal)) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro i _hi
        positivity

/-- Absolute continuity of the Euclidean ball-volume radius function implies
the thin radial-shell volume estimate used in the weak monotonicity proof. -/
theorem radialOpenShellsVolumeTendstoZero_of_ballVolume_ac {n : ℕ}
    (hball : EuclideanBallVolumeAbsolutelyContinuous n) :
    RadialOpenShellsVolumeTendstoZero n := by
  intro _inst a b ha hab
  let V : ℝ → ℝ := fun r : ℝ =>
    (volume (Metric.ball (0 : Domain n) r)).toReal
  have hV : AbsolutelyContinuousOnInterval V a b := by
    simpa [V] using hball ha hab
  have hvar :
      Filter.Tendsto
        (fun E : ℕ × (ℕ → ℝ × ℝ) =>
          ∑ i ∈ Finset.range E.1, dist (V (E.2 i).1) (V (E.2 i).2))
        (AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
          Filter.principal (AbsolutelyContinuousOnInterval.disjWithin a b))
        (𝓝 0) := by
    simpa [AbsolutelyContinuousOnInterval] using hV
  have hvar_enn :
      Filter.Tendsto
        (fun E : ℕ × (ℕ → ℝ × ℝ) =>
          ENNReal.ofReal
            (∑ i ∈ Finset.range E.1, dist (V (E.2 i).1) (V (E.2 i).2)))
        (AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
          Filter.principal (AbsolutelyContinuousOnInterval.disjWithin a b))
        (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hvar
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hvar_enn
  · intro E
    simp
  · intro E
    simpa [V] using radialOpenShells_volume_le_ballVolume_variation (n := n) E

/-- Disjoint radius intervals give disjoint radial open shells. -/
theorem pairwiseDisjoint_radialOpenShell_of_disjWithin {n : ℕ}
    {a b : ℝ} {E : ℕ × (ℕ → ℝ × ℝ)}
    (hE : E ∈ AbsolutelyContinuousOnInterval.disjWithin a b) :
    Set.PairwiseDisjoint (Finset.range E.1)
      (fun i => RadialOpenShell (n := n) (E.2 i).1 (E.2 i).2) := by
  intro i hi j hj hij
  change Disjoint
    (RadialOpenShell (n := n) (E.2 i).1 (E.2 i).2)
    (RadialOpenShell (n := n) (E.2 j).1 (E.2 j).2)
  rw [Set.disjoint_left]
  intro x hxi hxj
  have hri :
      ‖x‖ ∈ uIoc (E.2 i).1 (E.2 i).2 :=
    radialOpenShell_subset_uIoc (n := n) (E.2 i).1 (E.2 i).2 hxi
  have hrj :
      ‖x‖ ∈ uIoc (E.2 j).1 (E.2 j).2 :=
    radialOpenShell_subset_uIoc (n := n) (E.2 j).1 (E.2 j).2 hxj
  exact (Set.disjoint_left.mp (hE.2 hi hj hij)) hri hrj

/-- The thin-annulus volume estimate remains true after restricting the ambient
measure to any fixed ball. -/
theorem radialOpenShells_restrictVolume_tendstoZero {n : ℕ} [NeZero n]
    {a b R0 : ℝ}
    (hthin : RadialOpenShellsVolumeTendstoZero n)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    Filter.Tendsto
      (fun E : ℕ × (ℕ → ℝ × ℝ) =>
        (volume.restrict (Metric.ball (0 : Domain n) R0))
          (RadialOpenShells (n := n) E))
      (AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
        Filter.principal (AbsolutelyContinuousOnInterval.disjWithin a b))
      (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (hthin ha hab)
  · intro E
    simp
  · intro E
    exact Measure.restrict_le_self (RadialOpenShells (n := n) E)

/-- Consequently, an `L¹` integrand has vanishing integral over such thin
radial shell unions. -/
theorem radialOpenShells_lintegral_enorm_tendstoZero {n : ℕ} [NeZero n]
    {f : Domain n → ℝ} {a b R0 : ℝ}
    (hthin : RadialOpenShellsVolumeTendstoZero n)
    (hf : IntegrableOn f (Metric.ball (0 : Domain n) R0) volume)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    Filter.Tendsto
      (fun E : ℕ × (ℕ → ℝ × ℝ) =>
        ∫⁻ x in RadialOpenShells (n := n) E, ‖f x‖ₑ
          ∂(volume.restrict (Metric.ball (0 : Domain n) R0)))
      (AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
        Filter.principal (AbsolutelyContinuousOnInterval.disjWithin a b))
      (𝓝 0) := by
  exact tendsto_setLIntegral_zero
    (μ := volume.restrict (Metric.ball (0 : Domain n) R0))
    (f := fun x : Domain n => ‖f x‖ₑ)
    (ne_of_lt hf.hasFiniteIntegral)
    (radialOpenShells_restrictVolume_tendstoZero
      (n := n) (a := a) (b := b) (R0 := R0) hthin ha hab)

/-- If the two scalar densities have absolutely continuous ball-integral radius
functions, then the weak energy and weak radial energy radius functions are
absolutely continuous. -/
theorem weakEnergyAbsolutelyContinuousOnRadii_of_ballIntegralRadiusAC {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (henergy_ac :
      BallIntegralRadiusAbsolutelyContinuous
        (fun x : Domain n => weakEnergyDensity Du x) R0)
    (hradial_ac :
      BallIntegralRadiusAbsolutelyContinuous
        (fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x) R0) :
    WeakEnergyAbsolutelyContinuousOnRadii Du R0 := by
  constructor
  · intro a b ha hab hb
    exact henergy_ac ha hab hb
  · intro a b ha hab hb
    exact hradial_ac ha hab hb

/-- Local `L²` control plus the generic `L¹` ball-integral AC theorem supplies
absolute continuity of the weak energy and weak radial energy radius functions. -/
theorem weakEnergyAbsolutelyContinuousOnRadii_of_locallyL2_ballIntegralAC
    {n m : ℕ} [NeZero n]
    {Du : Domain n → Gradient n m} {Ω : Set (Domain n)} {R0 : ℝ}
    (hball_ac : BallIntegralRadiusACOfIntegrableOnBall n)
    (hDu_meas : GradientAEStronglyMeasurableIn Du Ω)
    (hgrad : GradientLocallyL2In Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω) :
    WeakEnergyAbsolutelyContinuousOnRadii Du R0 := by
  have henergy :
      IntegrableOn (fun x : Domain n => weakEnergyDensity Du x)
        (Metric.ball (0 : Domain n) R0) volume :=
    gradientLocallyL2In_integrableOn_ball
      (n := n) (m := m) (Du := Du) (Ω := Ω)
      hgrad hclosedBall_subset
  have hradial_meas :
      AEStronglyMeasurable
        (fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x)
        (volume.restrict (Metric.ball (0 : Domain n) R0)) :=
    weakRadialEnergyDensity_aestronglyMeasurable_on_ball_of_gradient
      (n := n) (m := m) (Du := Du) (Ω := Ω)
      (a := 0) (r := R0) hDu_meas hclosedBall_subset
  have hradial :
      IntegrableOn (fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x)
        (Metric.ball (0 : Domain n) R0) volume :=
    weakRadialEnergyDensity_integrableOn_of_energy
      (n := n) (m := m) (Du := Du)
      (Ω := Metric.ball (0 : Domain n) R0)
      henergy hradial_meas
  exact weakEnergyAbsolutelyContinuousOnRadii_of_ballIntegralRadiusAC
    (n := n) (m := m) (Du := Du) (R0 := R0)
    (hball_ac henergy) (hball_ac hradial)

/-- The `W^{1,2}_{loc}` packaged version of radius absolute continuity, using
the generic `L¹` ball-integral AC theorem. -/
theorem weakEnergyAbsolutelyContinuousOnRadii_of_W12LocIn_ballIntegralAC
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)} {R0 : ℝ}
    (hball_ac : BallIntegralRadiusACOfIntegrableOnBall n)
    (hW : W12LocIn u Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω) :
    WeakEnergyAbsolutelyContinuousOnRadii Du R0 :=
  weakEnergyAbsolutelyContinuousOnRadii_of_locallyL2_ballIntegralAC
    (n := n) (m := m) (Du := Du) (Ω := Ω) (R0 := R0)
    hball_ac hW.gradient_aestronglyMeasurable hW.gradient_locallyL2
    hclosedBall_subset

/-- A single package for the one-dimensional radius calculus still needed after
radial stationarity has been reduced to scalar cutoffs.  The first field records
the intended absolute-continuity theorem; the last two fields are the concrete
IBP and integrability consequences consumed by the existing algebra. -/
def WeakBallEnergyOneDimensionalCalculus {n m : ℕ}
    (Du : Domain n → Gradient n m) (R0 : ℝ) : Prop :=
  WeakEnergyAbsolutelyContinuousOnRadii Du R0 ∧
  WeakBallEnergyIntegrationByPartsFormula Du R0 ∧
  WeakOneDimensionalIBPIntegrability Du R0

theorem weakEnergyAbsolutelyContinuousOnRadii_of_oneDimensionalCalculus
    {n m : ℕ} {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hcalc : WeakBallEnergyOneDimensionalCalculus Du R0) :
    WeakEnergyAbsolutelyContinuousOnRadii Du R0 :=
  hcalc.1

theorem weakBallEnergyIntegrationByPartsFormula_of_oneDimensionalCalculus
    {n m : ℕ} {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hcalc : WeakBallEnergyOneDimensionalCalculus Du R0) :
    WeakBallEnergyIntegrationByPartsFormula Du R0 :=
  hcalc.2.1

theorem weakOneDimensionalIBPIntegrability_of_oneDimensionalCalculus
    {n m : ℕ} {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hcalc : WeakBallEnergyOneDimensionalCalculus Du R0) :
    WeakOneDimensionalIBPIntegrability Du R0 :=
  hcalc.2.2

/-- Trimming an integral over `(0, R0)` by the indicator of `(a, b)` gives the
usual interval integral over `a..b`, provided `0 ≤ a ≤ b ≤ R0`. -/
theorem integral_Ioo_zero_radius_indicator_Ioo_eq_intervalIntegral
    {f : ℝ → ℝ} {a b R0 : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ R0) :
    (∫ rho in Ioo (0 : ℝ) R0,
      (Ioo a b).indicator (fun _ : ℝ => (1 : ℝ)) rho * f rho)
      =
    ∫ rho in a..b, f rho := by
  calc
    (∫ rho in Ioo (0 : ℝ) R0,
      (Ioo a b).indicator (fun _ : ℝ => (1 : ℝ)) rho * f rho)
        =
      ∫ rho in Ioo (0 : ℝ) R0, (Ioo a b).indicator f rho := by
        apply integral_congr_ae
        filter_upwards with rho
        by_cases h : rho ∈ Ioo a b <;> simp [h]
    _ =
      ∫ rho in Ioo (0 : ℝ) R0 ∩ Ioo a b, f rho := by
        rw [setIntegral_indicator measurableSet_Ioo]
    _ =
      ∫ rho in Ioo a b, f rho := by
        have hset : Ioo (0 : ℝ) R0 ∩ Ioo a b = Ioo a b := by
          ext rho
          constructor
          · intro h
            exact h.2
          · intro h
            exact ⟨⟨lt_of_le_of_lt ha h.1, lt_of_lt_of_le h.2 hb⟩, h⟩
        rw [hset]
    _ =
      ∫ rho in a..b, f rho := by
        rw [intervalIntegral.integral_of_le hab]
        rw [integral_Ioc_eq_integral_Ioo]

/-- Absolute continuity is unchanged when two functions agree on the closed
interval where it is tested. -/
theorem absolutelyContinuousOnInterval_congr_uIcc {f g : ℝ → ℝ} {a b : ℝ}
    (hfg : EqOn f g (uIcc a b))
    (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval f a b := by
  rw [absolutelyContinuousOnInterval_iff] at hg ⊢
  intro ε hε
  rcases hg ε hε with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro E hE hdist
  convert hδ E hE hdist using 1
  apply Finset.sum_congr rfl
  intro i hi
  have hi_mem :
      (E.2 i).1 ∈ uIcc a b ∧ (E.2 i).2 ∈ uIcc a b := by
    exact hE.1 i hi
  rw [hfg hi_mem.1, hfg hi_mem.2]

/-- The Euclidean ball-volume radius function is absolutely continuous on every
compact nonnegative radius interval. -/
theorem euclideanBallVolumeAbsolutelyContinuous (n : ℕ) :
    EuclideanBallVolumeAbsolutelyContinuous n := by
  intro _inst a b ha hab
  let c : ℝ :=
    √Real.pi ^ Fintype.card (Fin n) /
      Real.Gamma (((Fintype.card (Fin n) : ℝ) / 2) + 1)
  let V : ℝ → ℝ := fun r : ℝ =>
    (volume (Metric.ball (0 : Domain n) r)).toReal
  let P : ℝ → ℝ := fun r : ℝ => r ^ Fintype.card (Fin n) * c
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact div_nonneg
      (pow_nonneg (Real.sqrt_nonneg Real.pi) (Fintype.card (Fin n)))
      (le_of_lt (by positivity))
  refine absolutelyContinuousOnInterval_congr_uIcc (f := V) (g := P) ?_ ?_
  · intro r hr
    have hrange : a ≤ r ∧ r ≤ b := by
      simpa [uIcc_of_le hab] using hr
    have hr_nonneg : 0 ≤ r := ha.trans hrange.1
    have hvol := domain_volume_ball_zero n r
    calc
      V r =
          ((ENNReal.ofReal r) ^ Fintype.card (Fin n) *
            ENNReal.ofReal c).toReal := by
          simp [V, c, hvol]
      _ =
          r ^ Fintype.card (Fin n) * c := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_pow,
            ENNReal.toReal_ofReal hr_nonneg, ENNReal.toReal_ofReal hc_nonneg]
      _ = P r := by
          simp [P]
  · apply ContDiffOn.absolutelyContinuousOnInterval
    have hP : ContDiff ℝ 1 P := by
      dsimp [P, c]
      fun_prop
    exact hP.contDiffOn

/-- The thin radial-shell volume estimate in Euclidean space. -/
theorem radialOpenShellsVolumeTendstoZero_euclidean (n : ℕ) :
    RadialOpenShellsVolumeTendstoZero n :=
  radialOpenShellsVolumeTendstoZero_of_ballVolume_ac
    (n := n) (euclideanBallVolumeAbsolutelyContinuous n)

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps

end
