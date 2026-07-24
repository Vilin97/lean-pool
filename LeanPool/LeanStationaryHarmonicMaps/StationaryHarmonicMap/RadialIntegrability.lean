/-
Copyright (c) 2026 Wei Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Wang
-/
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.EnergyQuantities
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.RadialCutoffs

/-!
# Weak radial integrability

This module contains the weak radial integrands and the integrability lemmas
that discharge the side conditions in the radial stationarity identity.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace LeanStationaryHarmonicMaps
namespace StationaryHarmonicMap

/-- The main energy integrand in the weak radial identity at center `0`. -/
def weakRadialMainIntegrand {n m : ℕ}
    (Du : Domain n → Gradient n m) (phi : ℝ → ℝ) (x : Domain n) : ℝ :=
  weakRadialMainCoeff n phi x * weakEnergyDensity Du x

/-- The radial-energy integrand in the weak radial identity at center `0`. -/
def weakRadialRhsIntegrand {n m : ℕ}
    (Du : Domain n → Gradient n m) (phi : ℝ → ℝ) (x : Domain n) : ℝ :=
  weakRadialRhsCoeff phi x * weakRadialEnergyDensity Du 0 x

/-- Multiplication by an a.e. bounded scalar coefficient preserves integrability on a set. -/
theorem integrableOn_bdd_mul_of_integrableOn {n : ℕ} {Ω : Set (Domain n)}
    {c g : Domain n → ℝ} {C : ℝ}
    (hg : IntegrableOn g Ω volume)
    (hc_meas : AEStronglyMeasurable c (volume.restrict Ω))
    (hc_bound : ∀ᵐ x ∂volume.restrict Ω, ‖c x‖ ≤ C) :
    IntegrableOn (fun x : Domain n => c x * g x) Ω volume := by
  exact hg.integrable.bdd_mul hc_meas hc_bound

/-- A function dominated in norm by an integrable scalar function is integrable on the set. -/
theorem integrableOn_of_norm_le_integrableOn {n : ℕ} {Ω : Set (Domain n)}
    {f g : Domain n → ℝ}
    (hg : IntegrableOn g Ω volume)
    (hf_meas : AEStronglyMeasurable f (volume.restrict Ω))
    (hbound : ∀ᵐ x ∂volume.restrict Ω, ‖f x‖ ≤ g x) :
    IntegrableOn f Ω volume := by
  exact hg.integrable.mono' hf_meas hbound

/-- Radial energy is integrable once it is a.e. dominated by the weak energy density. -/
theorem weakRadialEnergyDensity_integrableOn_of_energy_bound {n m : ℕ}
    {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    (henergy : IntegrableOn (fun x : Domain n => weakEnergyDensity Du x) Ω volume)
    (hradial_meas :
      AEStronglyMeasurable
        (fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x)
        (volume.restrict Ω))
    (hradial_bound :
      ∀ᵐ x ∂volume.restrict Ω,
        ‖weakRadialEnergyDensity Du (0 : Domain n) x‖ ≤ weakEnergyDensity Du x) :
    IntegrableOn (fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x)
      Ω volume := by
  exact integrableOn_of_norm_le_integrableOn
    (n := n) (Ω := Ω)
    (f := fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x)
    (g := fun x : Domain n => weakEnergyDensity Du x)
    henergy hradial_meas hradial_bound

/-- Radial energy is integrable on a set as soon as weak energy is integrable there,
provided the radial-energy density is a.e. strongly measurable. -/
theorem weakRadialEnergyDensity_integrableOn_of_energy {n m : ℕ}
    {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    (henergy : IntegrableOn (fun x : Domain n => weakEnergyDensity Du x) Ω volume)
    (hradial_meas :
      AEStronglyMeasurable
        (fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x)
        (volume.restrict Ω)) :
    IntegrableOn (fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x)
      Ω volume := by
  exact weakRadialEnergyDensity_integrableOn_of_energy_bound
    (n := n) (m := m) (Du := Du) (Ω := Ω)
    henergy hradial_meas
    (Filter.Eventually.of_forall fun x =>
      norm_weakRadialEnergyDensity_le_weakEnergyDensity Du (0 : Domain n) x)

/-- If the radial main coefficient is a.e. bounded and the weak energy is integrable,
then the main radial integrand is integrable. -/
theorem weakRadialMainIntegrand_integrableOn_of_bounded_coeff {n m : ℕ}
    {Du : Domain n → Gradient n m} {Ω : Set (Domain n)} {phi : ℝ → ℝ} {C : ℝ}
    (henergy : IntegrableOn (fun x : Domain n => weakEnergyDensity Du x) Ω volume)
    (hcoeff_meas :
      AEStronglyMeasurable (fun x : Domain n => weakRadialMainCoeff n phi x)
        (volume.restrict Ω))
    (hcoeff_bound :
      ∀ᵐ x ∂volume.restrict Ω, ‖weakRadialMainCoeff n phi x‖ ≤ C) :
    IntegrableOn (fun x : Domain n => weakRadialMainIntegrand Du phi x) Ω volume := by
  simpa [weakRadialMainIntegrand] using
    integrableOn_bdd_mul_of_integrableOn
      (n := n) (Ω := Ω)
      (c := fun x : Domain n => weakRadialMainCoeff n phi x)
      (g := fun x : Domain n => weakEnergyDensity Du x)
      henergy hcoeff_meas hcoeff_bound

/-- If the radial right-hand coefficient is a.e. bounded and the weak radial energy
is integrable, then the right-hand radial integrand is integrable. -/
theorem weakRadialRhsIntegrand_integrableOn_of_bounded_coeff {n m : ℕ}
    {Du : Domain n → Gradient n m} {Ω : Set (Domain n)} {phi : ℝ → ℝ} {C : ℝ}
    (hradial :
      IntegrableOn (fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x)
        Ω volume)
    (hcoeff_meas :
      AEStronglyMeasurable (fun x : Domain n => weakRadialRhsCoeff phi x)
        (volume.restrict Ω))
    (hcoeff_bound :
      ∀ᵐ x ∂volume.restrict Ω, ‖weakRadialRhsCoeff phi x‖ ≤ C) :
    IntegrableOn (fun x : Domain n => weakRadialRhsIntegrand Du phi x) Ω volume := by
  simpa [weakRadialRhsIntegrand] using
    integrableOn_bdd_mul_of_integrableOn
      (n := n) (Ω := Ω)
      (c := fun x : Domain n => weakRadialRhsCoeff phi x)
      (g := fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x)
      hradial hcoeff_meas hcoeff_bound

/-- A single package for the two integrability estimates needed in the weak radial identity. -/
theorem weak_radial_cutoff_integrable_of_bounded_coefficients {n m : ℕ}
    {Du : Domain n → Gradient n m} {Ω : Set (Domain n)} {phi : ℝ → ℝ}
    {Cmain Crhs : ℝ}
    (henergy : IntegrableOn (fun x : Domain n => weakEnergyDensity Du x) Ω volume)
    (hradial :
      IntegrableOn (fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x)
        Ω volume)
    (hmain_meas :
      AEStronglyMeasurable (fun x : Domain n => weakRadialMainCoeff n phi x)
        (volume.restrict Ω))
    (hmain_bound :
      ∀ᵐ x ∂volume.restrict Ω, ‖weakRadialMainCoeff n phi x‖ ≤ Cmain)
    (hrhs_meas :
      AEStronglyMeasurable (fun x : Domain n => weakRadialRhsCoeff phi x)
        (volume.restrict Ω))
    (hrhs_bound :
      ∀ᵐ x ∂volume.restrict Ω, ‖weakRadialRhsCoeff phi x‖ ≤ Crhs) :
    IntegrableOn (fun x : Domain n => weakRadialMainIntegrand Du phi x) Ω volume ∧
      IntegrableOn (fun x : Domain n => weakRadialRhsIntegrand Du phi x) Ω volume := by
  exact
    ⟨weakRadialMainIntegrand_integrableOn_of_bounded_coeff
        (n := n) (m := m) (Du := Du) (Ω := Ω) (phi := phi)
        henergy hmain_meas hmain_bound,
      weakRadialRhsIntegrand_integrableOn_of_bounded_coeff
        (n := n) (m := m) (Du := Du) (Ω := Ω) (phi := phi)
        hradial hrhs_meas hrhs_bound⟩

/-- The two radial-integrability estimates using only weak-energy integrability,
provided radial energy is a.e. dominated by weak energy. -/
theorem weak_radial_cutoff_integrable_of_energy_bound {n m : ℕ}
    {Du : Domain n → Gradient n m} {Ω : Set (Domain n)} {phi : ℝ → ℝ}
    {Cmain Crhs : ℝ}
    (henergy : IntegrableOn (fun x : Domain n => weakEnergyDensity Du x) Ω volume)
    (hradial_meas :
      AEStronglyMeasurable
        (fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x)
        (volume.restrict Ω))
    (hradial_bound :
      ∀ᵐ x ∂volume.restrict Ω,
        ‖weakRadialEnergyDensity Du (0 : Domain n) x‖ ≤ weakEnergyDensity Du x)
    (hmain_meas :
      AEStronglyMeasurable (fun x : Domain n => weakRadialMainCoeff n phi x)
        (volume.restrict Ω))
    (hmain_bound :
      ∀ᵐ x ∂volume.restrict Ω, ‖weakRadialMainCoeff n phi x‖ ≤ Cmain)
    (hrhs_meas :
      AEStronglyMeasurable (fun x : Domain n => weakRadialRhsCoeff phi x)
        (volume.restrict Ω))
    (hrhs_bound :
      ∀ᵐ x ∂volume.restrict Ω, ‖weakRadialRhsCoeff phi x‖ ≤ Crhs) :
    IntegrableOn (fun x : Domain n => weakRadialMainIntegrand Du phi x) Ω volume ∧
      IntegrableOn (fun x : Domain n => weakRadialRhsIntegrand Du phi x) Ω volume := by
  have hradial :
      IntegrableOn
        (fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x) Ω volume :=
    weakRadialEnergyDensity_integrableOn_of_energy_bound
      (n := n) (m := m) (Du := Du) (Ω := Ω)
      henergy hradial_meas hradial_bound
  exact weak_radial_cutoff_integrable_of_bounded_coefficients
    (n := n) (m := m) (Du := Du) (Ω := Ω) (phi := phi)
    henergy hradial hmain_meas hmain_bound hrhs_meas hrhs_bound

/-- The two radial-integrability estimates using weak-energy integrability and
the pointwise bound `weakRadialEnergyDensity ≤ weakEnergyDensity`. -/
theorem weak_radial_cutoff_integrable_of_energy {n m : ℕ}
    {Du : Domain n → Gradient n m} {Ω : Set (Domain n)} {phi : ℝ → ℝ}
    {Cmain Crhs : ℝ}
    (henergy : IntegrableOn (fun x : Domain n => weakEnergyDensity Du x) Ω volume)
    (hradial_meas :
      AEStronglyMeasurable
        (fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x)
        (volume.restrict Ω))
    (hmain_meas :
      AEStronglyMeasurable (fun x : Domain n => weakRadialMainCoeff n phi x)
        (volume.restrict Ω))
    (hmain_bound :
      ∀ᵐ x ∂volume.restrict Ω, ‖weakRadialMainCoeff n phi x‖ ≤ Cmain)
    (hrhs_meas :
      AEStronglyMeasurable (fun x : Domain n => weakRadialRhsCoeff phi x)
        (volume.restrict Ω))
    (hrhs_bound :
      ∀ᵐ x ∂volume.restrict Ω, ‖weakRadialRhsCoeff phi x‖ ≤ Crhs) :
    IntegrableOn (fun x : Domain n => weakRadialMainIntegrand Du phi x) Ω volume ∧
      IntegrableOn (fun x : Domain n => weakRadialRhsIntegrand Du phi x) Ω volume := by
  have hradial :
      IntegrableOn
        (fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x) Ω volume :=
    weakRadialEnergyDensity_integrableOn_of_energy
      (n := n) (m := m) (Du := Du) (Ω := Ω) henergy hradial_meas
  exact weak_radial_cutoff_integrable_of_bounded_coefficients
    (n := n) (m := m) (Du := Du) (Ω := Ω) (phi := phi)
    henergy hradial hmain_meas hmain_bound hrhs_meas hrhs_bound

/-- The two radial-integrability estimates on a ball, with weak-gradient
measurability and weak-energy integrability supplied on a containing set.

The coefficient measurability comes from `ContDiff ℝ 1 phi`, and the a.e.
bounds come from pointwise bounds for `phi` and `phi'` on `[0, R0]`. -/
theorem weak_radial_cutoff_integrable_of_locallyL2 {n m : ℕ}
    {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 M0 M1 : ℝ} {phi : ℝ → ℝ}
    (hDu_meas : GradientAEStronglyMeasurableIn Du Ω)
    (hgrad : GradientLocallyL2In Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hphi_c1 : ContDiff ℝ 1 phi)
    (hphi_bound : ∀ t : ℝ, 0 ≤ t → t ≤ R0 → ‖phi t‖ ≤ M0)
    (hdphi_bound : ∀ t : ℝ, 0 ≤ t → t ≤ R0 → ‖deriv phi t‖ ≤ M1)
    (hR0_nonneg : 0 ≤ R0) :
    IntegrableOn (fun x : Domain n => weakRadialMainIntegrand Du phi x)
        (Metric.ball (0 : Domain n) R0) volume ∧
      IntegrableOn (fun x : Domain n => weakRadialRhsIntegrand Du phi x)
        (Metric.ball (0 : Domain n) R0) volume := by
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
  exact weak_radial_cutoff_integrable_of_energy
    (n := n) (m := m) (Du := Du)
    (Ω := Metric.ball (0 : Domain n) R0) (phi := phi)
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

/-- Cutoff-integrability on a ball, using the packaged cutoff interface. -/
theorem weak_radial_cutoff_integrable_of_locallyL2_cutoff {n m : ℕ}
    {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 M0 M1 : ℝ} {phi : ℝ → ℝ}
    (hDu_meas : GradientAEStronglyMeasurableIn Du Ω)
    (hgrad : GradientLocallyL2In Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hcut : AdmissibleRadialCutoff n R0 M0 M1 phi) :
    IntegrableOn (fun x : Domain n => weakRadialMainIntegrand Du phi x)
        (Metric.ball (0 : Domain n) R0) volume ∧
      IntegrableOn (fun x : Domain n => weakRadialRhsIntegrand Du phi x)
        (Metric.ball (0 : Domain n) R0) volume := by
  exact weak_radial_cutoff_integrable_of_locallyL2
    (n := n) (m := m) (Du := Du) (Ω := Ω)
    (R0 := R0) (M0 := M0) (M1 := M1) (phi := phi)
    hDu_meas hgrad hclosedBall_subset
    hcut.contDiff hcut.phi_bound hcut.deriv_bound hcut.radius_nonneg

/-- Cutoff-integrability on a ball from the `W^{1,2}_{loc}` interface. -/
theorem weak_radial_cutoff_integrable_of_W12Loc_cutoff {n m : ℕ}
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 M0 M1 : ℝ} {phi : ℝ → ℝ}
    (hW : W12LocIn u Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hcut : AdmissibleRadialCutoff n R0 M0 M1 phi) :
    IntegrableOn (fun x : Domain n => weakRadialMainIntegrand Du phi x)
        (Metric.ball (0 : Domain n) R0) volume ∧
      IntegrableOn (fun x : Domain n => weakRadialRhsIntegrand Du phi x)
        (Metric.ball (0 : Domain n) R0) volume := by
  exact weak_radial_cutoff_integrable_of_locallyL2_cutoff
    (n := n) (m := m) (Du := Du) (Ω := Ω)
    (R0 := R0) (M0 := M0) (M1 := M1) (phi := phi)
    hW.gradient_aestronglyMeasurable hW.gradient_locallyL2
    hclosedBall_subset hcut

/-- Cutoff-integrability for a one-dimensional smooth bump cutoff. -/
theorem weak_radial_cutoff_integrable_of_W12Loc_contDiffBump {n m : ℕ}
    {u : Domain n → Target m} {Du : Domain n → Gradient n m} {Ω : Set (Domain n)}
    {R0 : ℝ}
    (hW : W12LocIn u Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (f : ContDiffBump (0 : ℝ)) (hRout : f.rOut < R0) :
    IntegrableOn (fun x : Domain n => weakRadialMainIntegrand Du (fun t : ℝ => f t) x)
        (Metric.ball (0 : Domain n) R0) volume ∧
      IntegrableOn (fun x : Domain n => weakRadialRhsIntegrand Du (fun t : ℝ => f t) x)
        (Metric.ball (0 : Domain n) R0) volume := by
  rcases ContDiffBump.exists_admissibleRadialCutoff (n := n) f hRout with ⟨M1, hcut⟩
  exact weak_radial_cutoff_integrable_of_W12Loc_cutoff
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω)
    (R0 := R0) (M0 := 1) (M1 := M1)
    hW hclosedBall_subset hcut

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps

end
