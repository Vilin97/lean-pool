/-
Copyright (c) 2026 Wei Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Wang
-/
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.RadialIntegrability

/-!
# Weak radial stationarity identity

This module turns weak stationarity tested against radial vector fields into
the weak radial integral identity, with integrability side conditions supplied
by `RadialIntegrability`.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace LeanStationaryHarmonicMaps
namespace StationaryHarmonicMap

/-- The radial identity obtained by testing stationarity with `X(x) = phi(|x|) x`.

This is equation `(1)` in the LaTeX proof, stated for the smooth model and center `0`.
-/
def RadialStationarityIdentity {n m : ℕ} (u : Domain n → Target m) (R0 : ℝ) : Prop :=
  ∀ phi : ℝ → ℝ,
    ContDiff ℝ 1 (radialVectorField (n := n) phi) →
      HasCompactSupport (radialVectorField (n := n) phi) →
        tsupport (radialVectorField (n := n) phi) ⊆ Metric.ball (0 : Domain n) R0 →
        (∫ x in Metric.ball (0 : Domain n) R0,
            (((n : ℝ) - 2) * phi ‖x‖ + ‖x‖ * deriv phi ‖x‖) * energyDensity u x)
          =
        2 * ∫ x in Metric.ball (0 : Domain n) R0,
            (‖x‖ * deriv phi ‖x‖) * radialEnergyDensity u 0 x

/-- Weak radial identity obtained by testing stationarity with `X(x)=phi(|x|)x`,
stated at center `0`. -/
def WeakRadialStationarityIdentity {n m : ℕ}
    (Du : Domain n → Gradient n m) (R0 : ℝ) : Prop :=
  ∀ phi : ℝ → ℝ,
    Differentiable ℝ phi →
      ContDiff ℝ 1 (radialVectorField (n := n) phi) →
        HasCompactSupport (radialVectorField (n := n) phi) →
          tsupport (radialVectorField (n := n) phi) ⊆ Metric.ball (0 : Domain n) R0 →
          (∫ x in Metric.ball (0 : Domain n) R0,
              weakRadialMainIntegrand Du phi x)
            =
          2 * ∫ x in Metric.ball (0 : Domain n) R0,
              weakRadialRhsIntegrand Du phi x

/-- The pointwise radial integrand simplification holds almost everywhere on
balls: the only excluded point is the origin. -/
theorem weakStationarityIntegrand_radialVectorField_ae {n m : ℕ} [NeZero n]
    (Du : Domain n → Gradient n m) {phi : ℝ → ℝ}
    (hphi : Differentiable ℝ phi) (R0 : ℝ) :
    (fun x : Domain n => weakStationarityIntegrand Du (radialVectorField phi) x)
      =ᵐ[volume.restrict (Metric.ball (0 : Domain n) R0)]
    (fun x : Domain n =>
      weakRadialMainIntegrand Du phi x - 2 * weakRadialRhsIntegrand Du phi x) := by
  have hne_global : ∀ᵐ x ∂(volume : Measure (Domain n)), x ≠ 0 := by
    have hzero : (volume : Measure (Domain n)) ({0} : Set (Domain n)) = 0 := by
      exact measure_singleton (0 : Domain n)
    exact compl_mem_ae_iff.mpr hzero
  have hne :
      ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) R0), x ≠ 0 :=
    ae_restrict_of_ae hne_global
  filter_upwards [hne] with x hx
  exact weakStationarityIntegrand_radialVectorField Du hphi x hx

/-- Weak stationarity plus the radial vector-field computation gives the weak
radial identity, once the two resulting radial integrands are known to be
integrable on the ball.  The integrability hypotheses will later be discharged
from `W^{1,2}_{loc}` and compact support of the cutoff. -/
theorem weak_radial_identity_from_stationarity {n m : ℕ} [NeZero n]
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hstationary : WeakStationaryIn Du (Metric.ball (0 : Domain n) R0))
    {phi : ℝ → ℝ}
    (hphi : Differentiable ℝ phi)
    (hXdiff : ContDiff ℝ 1 (radialVectorField (n := n) phi))
    (hXcompact : HasCompactSupport (radialVectorField (n := n) phi))
    (hXsupport :
      tsupport (radialVectorField (n := n) phi) ⊆ Metric.ball (0 : Domain n) R0)
    (hmain_int :
      IntegrableOn (fun x : Domain n => weakRadialMainIntegrand Du phi x)
        (Metric.ball (0 : Domain n) R0) volume)
    (hrhs_int :
      IntegrableOn (fun x : Domain n => weakRadialRhsIntegrand Du phi x)
        (Metric.ball (0 : Domain n) R0) volume) :
    (∫ x in Metric.ball (0 : Domain n) R0,
        weakRadialMainIntegrand Du phi x)
      =
    2 * ∫ x in Metric.ball (0 : Domain n) R0,
        weakRadialRhsIntegrand Du phi x := by
  let Ω : Set (Domain n) := Metric.ball (0 : Domain n) R0
  have hstat :
      (∫ x in Ω, weakStationarityIntegrand Du (radialVectorField phi) x) = 0 := by
    exact hstationary (radialVectorField phi) hXdiff hXcompact hXsupport
  have hae :
      (fun x : Domain n => weakStationarityIntegrand Du (radialVectorField phi) x)
        =ᵐ[volume.restrict Ω]
      (fun x : Domain n =>
        weakRadialMainIntegrand Du phi x - 2 * weakRadialRhsIntegrand Du phi x) := by
    simpa [Ω] using weakStationarityIntegrand_radialVectorField_ae
      (n := n) (m := m) Du hphi R0
  have hzero :
      (∫ x in Ω,
        weakRadialMainIntegrand Du phi x - 2 * weakRadialRhsIntegrand Du phi x) = 0 := by
    rw [← integral_congr_ae hae]
    exact hstat
  have hmain_integrable :
      Integrable (fun x : Domain n => weakRadialMainIntegrand Du phi x)
        (volume.restrict Ω) := by
    simpa [Ω] using hmain_int.integrable
  have hrhs_integrable :
      Integrable (fun x : Domain n => weakRadialRhsIntegrand Du phi x)
        (volume.restrict Ω) := by
    simpa [Ω] using hrhs_int.integrable
  have htworhs_integrable :
      Integrable (fun x : Domain n => 2 * weakRadialRhsIntegrand Du phi x)
        (volume.restrict Ω) :=
    hrhs_integrable.const_mul 2
  have hdiff :
      (∫ x in Ω, weakRadialMainIntegrand Du phi x)
        - 2 * ∫ x in Ω, weakRadialRhsIntegrand Du phi x = 0 := by
    rw [integral_sub hmain_integrable htworhs_integrable] at hzero
    rw [integral_const_mul] at hzero
    exact hzero
  linarith

/-- Weak stationarity gives the radial identity when the integrability side
conditions are discharged from weak-energy integrability and bounded cutoff
coefficients. -/
theorem weak_radial_identity_from_stationarity_of_energy_bound {n m : ℕ} [NeZero n]
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hstationary : WeakStationaryIn Du (Metric.ball (0 : Domain n) R0))
    {phi : ℝ → ℝ}
    (hphi : Differentiable ℝ phi)
    (hXdiff : ContDiff ℝ 1 (radialVectorField (n := n) phi))
    (hXcompact : HasCompactSupport (radialVectorField (n := n) phi))
    (hXsupport :
      tsupport (radialVectorField (n := n) phi) ⊆ Metric.ball (0 : Domain n) R0)
    {Cmain Crhs : ℝ}
    (henergy :
      IntegrableOn (fun x : Domain n => weakEnergyDensity Du x)
        (Metric.ball (0 : Domain n) R0) volume)
    (hradial_meas :
      AEStronglyMeasurable
        (fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x)
        (volume.restrict (Metric.ball (0 : Domain n) R0)))
    (hradial_bound :
      ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) R0),
        ‖weakRadialEnergyDensity Du (0 : Domain n) x‖ ≤ weakEnergyDensity Du x)
    (hmain_meas :
      AEStronglyMeasurable (fun x : Domain n => weakRadialMainCoeff n phi x)
        (volume.restrict (Metric.ball (0 : Domain n) R0)))
    (hmain_bound :
      ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) R0),
        ‖weakRadialMainCoeff n phi x‖ ≤ Cmain)
    (hrhs_meas :
      AEStronglyMeasurable (fun x : Domain n => weakRadialRhsCoeff phi x)
        (volume.restrict (Metric.ball (0 : Domain n) R0)))
    (hrhs_bound :
      ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) R0),
        ‖weakRadialRhsCoeff phi x‖ ≤ Crhs) :
    (∫ x in Metric.ball (0 : Domain n) R0,
        weakRadialMainIntegrand Du phi x)
      =
    2 * ∫ x in Metric.ball (0 : Domain n) R0,
        weakRadialRhsIntegrand Du phi x := by
  have hint :
      IntegrableOn (fun x : Domain n => weakRadialMainIntegrand Du phi x)
          (Metric.ball (0 : Domain n) R0) volume ∧
        IntegrableOn (fun x : Domain n => weakRadialRhsIntegrand Du phi x)
          (Metric.ball (0 : Domain n) R0) volume :=
    weak_radial_cutoff_integrable_of_energy_bound
      (n := n) (m := m) (Du := Du)
      (Ω := Metric.ball (0 : Domain n) R0) (phi := phi)
      henergy hradial_meas hradial_bound
      hmain_meas hmain_bound hrhs_meas hrhs_bound
  exact weak_radial_identity_from_stationarity
    (n := n) (m := m) (Du := Du) (R0 := R0)
    hstationary hphi hXdiff hXcompact hXsupport hint.1 hint.2

/-- Weak stationarity gives the radial identity from weak-energy integrability.
The radial-energy integrability is supplied by the pointwise estimate
`weakRadialEnergyDensity ≤ weakEnergyDensity`. -/
theorem weak_radial_identity_from_stationarity_of_energy {n m : ℕ} [NeZero n]
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hstationary : WeakStationaryIn Du (Metric.ball (0 : Domain n) R0))
    {phi : ℝ → ℝ}
    (hphi : Differentiable ℝ phi)
    (hXdiff : ContDiff ℝ 1 (radialVectorField (n := n) phi))
    (hXcompact : HasCompactSupport (radialVectorField (n := n) phi))
    (hXsupport :
      tsupport (radialVectorField (n := n) phi) ⊆ Metric.ball (0 : Domain n) R0)
    {Cmain Crhs : ℝ}
    (henergy :
      IntegrableOn (fun x : Domain n => weakEnergyDensity Du x)
        (Metric.ball (0 : Domain n) R0) volume)
    (hradial_meas :
      AEStronglyMeasurable
        (fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x)
        (volume.restrict (Metric.ball (0 : Domain n) R0)))
    (hmain_meas :
      AEStronglyMeasurable (fun x : Domain n => weakRadialMainCoeff n phi x)
        (volume.restrict (Metric.ball (0 : Domain n) R0)))
    (hmain_bound :
      ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) R0),
        ‖weakRadialMainCoeff n phi x‖ ≤ Cmain)
    (hrhs_meas :
      AEStronglyMeasurable (fun x : Domain n => weakRadialRhsCoeff phi x)
        (volume.restrict (Metric.ball (0 : Domain n) R0)))
    (hrhs_bound :
      ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Domain n) R0),
        ‖weakRadialRhsCoeff phi x‖ ≤ Crhs) :
    (∫ x in Metric.ball (0 : Domain n) R0,
        weakRadialMainIntegrand Du phi x)
      =
    2 * ∫ x in Metric.ball (0 : Domain n) R0,
        weakRadialRhsIntegrand Du phi x := by
  exact weak_radial_identity_from_stationarity_of_energy_bound
    (n := n) (m := m) (Du := Du) (R0 := R0)
    hstationary hphi hXdiff hXcompact hXsupport
    henergy hradial_meas
    (Filter.Eventually.of_forall fun x =>
      norm_weakRadialEnergyDensity_le_weakEnergyDensity Du (0 : Domain n) x)
    hmain_meas hmain_bound hrhs_meas hrhs_bound

/-- Weak stationarity gives the radial identity on a ball directly from
gradient measurability, `GradientLocallyL2In` on a containing set, and elementary
cutoff bounds. -/
theorem weak_radial_identity_from_stationarity_of_locallyL2 {n m : ℕ} [NeZero n]
    {Du : Domain n → Gradient n m} {Ω : Set (Domain n)} {R0 M0 M1 : ℝ}
    (hstationary : WeakStationaryIn Du (Metric.ball (0 : Domain n) R0))
    (hDu_meas : GradientAEStronglyMeasurableIn Du Ω)
    (hgrad : GradientLocallyL2In Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    {phi : ℝ → ℝ}
    (hphi : Differentiable ℝ phi)
    (hphi_c1 : ContDiff ℝ 1 phi)
    (hXdiff : ContDiff ℝ 1 (radialVectorField (n := n) phi))
    (hXcompact : HasCompactSupport (radialVectorField (n := n) phi))
    (hXsupport :
      tsupport (radialVectorField (n := n) phi) ⊆ Metric.ball (0 : Domain n) R0)
    (hphi_bound : ∀ t : ℝ, 0 ≤ t → t ≤ R0 → ‖phi t‖ ≤ M0)
    (hdphi_bound : ∀ t : ℝ, 0 ≤ t → t ≤ R0 → ‖deriv phi t‖ ≤ M1)
    (hR0_nonneg : 0 ≤ R0) :
    (∫ x in Metric.ball (0 : Domain n) R0,
        weakRadialMainIntegrand Du phi x)
      =
    2 * ∫ x in Metric.ball (0 : Domain n) R0,
        weakRadialRhsIntegrand Du phi x := by
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
  exact weak_radial_identity_from_stationarity_of_energy
    (n := n) (m := m) (Du := Du) (R0 := R0)
    hstationary hphi hXdiff hXcompact hXsupport
    (Cmain := ‖((n : ℝ) - 2)‖ * M0 + R0 * M1) (Crhs := R0 * M1)
    henergy hradial_meas
    (weakRadialMainCoeff_aestronglyMeasurable_of_contDiff
      (n := n) (Ω := Metric.ball (0 : Domain n) R0) hphi_c1)
    (weakRadialMainCoeff_ae_bound_on_ball_of_radius_bounds
      (n := n) (phi := phi) (R0 := R0) (M0 := M0) (M1 := M1)
      hphi_bound hdphi_bound hR0_nonneg)
    (weakRadialRhsCoeff_aestronglyMeasurable_of_contDiff
      (n := n) (Ω := Metric.ball (0 : Domain n) R0) hphi_c1)
    (weakRadialRhsCoeff_ae_bound_on_ball_of_radius_bound
      (n := n) (phi := phi) (R0 := R0) (M1 := M1)
      hdphi_bound hR0_nonneg)

/-- Weak radial identity on a ball from local `L²` data and the packaged cutoff
interface. -/
theorem weak_radial_identity_from_stationarity_of_locallyL2_cutoff {n m : ℕ} [NeZero n]
    {Du : Domain n → Gradient n m} {Ω : Set (Domain n)} {R0 M0 M1 : ℝ}
    (hstationary : WeakStationaryIn Du (Metric.ball (0 : Domain n) R0))
    (hDu_meas : GradientAEStronglyMeasurableIn Du Ω)
    (hgrad : GradientLocallyL2In Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    {phi : ℝ → ℝ}
    (hcut : AdmissibleRadialCutoff n R0 M0 M1 phi) :
    (∫ x in Metric.ball (0 : Domain n) R0,
        weakRadialMainIntegrand Du phi x)
      =
    2 * ∫ x in Metric.ball (0 : Domain n) R0,
        weakRadialRhsIntegrand Du phi x := by
  exact weak_radial_identity_from_stationarity_of_locallyL2
    (n := n) (m := m) (Du := Du) (Ω := Ω)
    (R0 := R0) (M0 := M0) (M1 := M1)
    hstationary hDu_meas hgrad hclosedBall_subset
    hcut.differentiable hcut.contDiff hcut.vectorField_contDiff
    hcut.vectorField_hasCompactSupport hcut.vectorField_support_subset
    hcut.phi_bound hcut.deriv_bound hcut.radius_nonneg

/-- Weak radial identity on a ball from the `W^{1,2}_{loc}` interface and the
packaged cutoff interface.  The stationarity hypothesis is still stated on the
ball; proving its restriction from a larger domain is a separate localization
step. -/
theorem weak_radial_identity_from_stationarity_of_W12Loc_cutoff {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 M0 M1 : ℝ}
    (hstationary : WeakStationaryIn Du (Metric.ball (0 : Domain n) R0))
    (hW : W12LocIn u Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    {phi : ℝ → ℝ}
    (hcut : AdmissibleRadialCutoff n R0 M0 M1 phi) :
    (∫ x in Metric.ball (0 : Domain n) R0,
        weakRadialMainIntegrand Du phi x)
      =
    2 * ∫ x in Metric.ball (0 : Domain n) R0,
        weakRadialRhsIntegrand Du phi x := by
  exact weak_radial_identity_from_stationarity_of_locallyL2_cutoff
    (n := n) (m := m) (Du := Du) (Ω := Ω)
    (R0 := R0) (M0 := M0) (M1 := M1)
    hstationary hW.gradient_aestronglyMeasurable hW.gradient_locallyL2
    hclosedBall_subset hcut

/-- Weak radial identity for a one-dimensional smooth bump cutoff.  The
derivative-bound constant required by `AdmissibleRadialCutoff` is produced from
compactness of `[0, R0]`. -/
theorem weak_radial_identity_from_stationarity_of_W12Loc_contDiffBump {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hstationary : WeakStationaryIn Du (Metric.ball (0 : Domain n) R0))
    (hW : W12LocIn u Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (f : ContDiffBump (0 : ℝ)) (hRout : f.rOut < R0) :
    (∫ x in Metric.ball (0 : Domain n) R0,
        weakRadialMainIntegrand Du (fun t : ℝ => f t) x)
      =
    2 * ∫ x in Metric.ball (0 : Domain n) R0,
        weakRadialRhsIntegrand Du (fun t : ℝ => f t) x := by
  rcases ContDiffBump.exists_admissibleRadialCutoff (n := n) f hRout with ⟨M1, hcut⟩
  exact weak_radial_identity_from_stationarity_of_W12Loc_cutoff
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω)
    (R0 := R0) (M0 := 1) (M1 := M1)
    hstationary hW hclosedBall_subset hcut

/-- Full weak radial identity from weak stationarity, packaged with the
integrability estimates needed to split the integral of `A - 2B`. -/
theorem weak_radial_identity_from_stationarity_with_integrability {n m : ℕ} [NeZero n]
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hstationary : WeakStationaryIn Du (Metric.ball (0 : Domain n) R0))
    (hintegrable :
      ∀ phi : ℝ → ℝ,
        Differentiable ℝ phi →
          ContDiff ℝ 1 (radialVectorField (n := n) phi) →
            HasCompactSupport (radialVectorField (n := n) phi) →
              tsupport (radialVectorField (n := n) phi) ⊆
                Metric.ball (0 : Domain n) R0 →
                IntegrableOn (fun x : Domain n => weakRadialMainIntegrand Du phi x)
                  (Metric.ball (0 : Domain n) R0) volume ∧
                IntegrableOn (fun x : Domain n => weakRadialRhsIntegrand Du phi x)
                  (Metric.ball (0 : Domain n) R0) volume) :
    WeakRadialStationarityIdentity Du R0 := by
  intro phi hphi hXdiff hXcompact hXsupport
  have hint := hintegrable phi hphi hXdiff hXcompact hXsupport
  exact weak_radial_identity_from_stationarity
    (n := n) (m := m) (Du := Du) (R0 := R0)
    hstationary hphi hXdiff hXcompact hXsupport hint.1 hint.2

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps

end
