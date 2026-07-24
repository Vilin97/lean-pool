/-
Copyright (c) 2026 Wei Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Wang
-/
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.BallIntegralAC

/-!
# Weak radius formula constructors

This module constructs the weak radius integration and one-dimensional calculus
packages from local L2, coarea, and annulus inputs.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace LeanStationaryHarmonicMaps
namespace StationaryHarmonicMap

/-- Integrability of the weak energy and weak radial energy on the ambient ball
turns the open-annulus identity into the packaged annulus formula. -/
theorem weakEnergyAnnulusFormula_of_integrableOn_ball {n m : ℕ} [NeZero n]
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (henergy :
      IntegrableOn (fun x : Domain n => weakEnergyDensity Du x)
        (Metric.ball (0 : Domain n) R0) volume)
    (hradial :
      IntegrableOn (fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x)
        (Metric.ball (0 : Domain n) R0) volume) :
    WeakEnergyAnnulusFormula Du R0 := by
  constructor
  · intro a b _ha hab hb
    have henergy_b :
        IntegrableOn (fun x : Domain n => weakEnergyDensity Du x)
          (Metric.ball (0 : Domain n) b) volume :=
      henergy.mono_set (Metric.ball_subset_ball hb)
    exact
      (ball_annulus_indicator_integral_eq_energy_diff
        (n := n) (f := fun x : Domain n => weakEnergyDensity Du x)
        (a := a) (b := b) (R0 := R0) hab hb henergy_b).symm
  · intro a b _ha hab hb
    have hradial_b :
        IntegrableOn (fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x)
          (Metric.ball (0 : Domain n) b) volume :=
      hradial.mono_set (Metric.ball_subset_ball hb)
    exact
      (ball_annulus_indicator_integral_eq_energy_diff
        (n := n) (f := fun x : Domain n =>
          weakRadialEnergyDensity Du (0 : Domain n) x)
        (a := a) (b := b) (R0 := R0) hab hb hradial_b).symm

/-- Local `L²` control and a.e. measurability supply the annulus formula on a
closed ball contained in the weak map domain. -/
theorem weakEnergyAnnulusFormula_of_locallyL2 {n m : ℕ} [NeZero n]
    {Du : Domain n → Gradient n m} {Ω : Set (Domain n)} {R0 : ℝ}
    (hDu_meas : GradientAEStronglyMeasurableIn Du Ω)
    (hgrad : GradientLocallyL2In Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω) :
    WeakEnergyAnnulusFormula Du R0 := by
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
  exact weakEnergyAnnulusFormula_of_integrableOn_ball
    (n := n) (m := m) (Du := Du) (R0 := R0) henergy hradial

/-- A `W^{1,2}_{loc}` map with chosen weak gradient automatically has the
annulus formula on any closed ball contained in the domain. -/
theorem weakEnergyAnnulusFormula_of_W12LocIn {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)} {R0 : ℝ}
    (hW : W12LocIn u Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω) :
    WeakEnergyAnnulusFormula Du R0 :=
  weakEnergyAnnulusFormula_of_locallyL2
    (n := n) (m := m) (Du := Du) (Ω := Ω) (R0 := R0)
    hW.gradient_aestronglyMeasurable hW.gradient_locallyL2 hclosedBall_subset

/-- The generic ball-integral radius derivative formula specializes to the weak
energy radius formula. -/
theorem weakEnergyRadiusIntegralFormula_of_ballRadiusDerivative {n m : ℕ} [NeZero n]
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hcoarea : BallIntegralRadiusDerivativeFormula n)
    (henergy :
      IntegrableOn (fun x : Domain n => weakEnergyDensity Du x)
        (Metric.ball (0 : Domain n) R0) volume) :
    WeakEnergyRadiusIntegralFormula Du R0 := by
  intro c
  exact
    hcoarea (f := fun x : Domain n => weakEnergyDensity Du x)
      (R0 := R0) henergy c

/-- The restricted generic ball-integral radius derivative formula specializes
to the restricted weak energy radius formula. -/
theorem weakEnergyRadiusIntegralFormulaForWeights_of_ballRadiusDerivativeForWeights
    {n m : ℕ} [NeZero n]
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hcoarea : BallIntegralRadiusDerivativeFormulaForWeights n)
    (henergy :
      IntegrableOn (fun x : Domain n => weakEnergyDensity Du x)
        (Metric.ball (0 : Domain n) R0) volume) :
    WeakEnergyRadiusIntegralFormulaForWeights Du R0 := by
  intro c hc
  exact
    hcoarea (f := fun x : Domain n => weakEnergyDensity Du x)
      (R0 := R0) henergy c hc

/-- The generic ball-integral radius derivative formula specializes to the weak
radial-energy radius formula. -/
theorem weakRadialEnergyRadiusIntegralFormula_of_ballRadiusDerivative
    {n m : ℕ} [NeZero n]
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hcoarea : BallIntegralRadiusDerivativeFormula n)
    (hradial :
      IntegrableOn
        (fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x)
        (Metric.ball (0 : Domain n) R0) volume) :
    WeakRadialEnergyRadiusIntegralFormula Du R0 := by
  intro c
  exact
    hcoarea
      (f := fun x : Domain n =>
        weakRadialEnergyDensity Du (0 : Domain n) x)
      (R0 := R0) hradial c

/-- The restricted generic ball-integral radius derivative formula specializes
to the restricted weak radial-energy radius formula. -/
theorem weakRadialEnergyRadiusIntegralFormulaForWeights_of_ballRadiusDerivativeForWeights
    {n m : ℕ} [NeZero n]
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hcoarea : BallIntegralRadiusDerivativeFormulaForWeights n)
    (hradial :
      IntegrableOn
        (fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x)
        (Metric.ball (0 : Domain n) R0) volume) :
    WeakRadialEnergyRadiusIntegralFormulaForWeights Du R0 := by
  intro c hc
  exact
    hcoarea
      (f := fun x : Domain n =>
        weakRadialEnergyDensity Du (0 : Domain n) x)
      (R0 := R0) hradial c hc

/-- Local `L²` control plus the generic ball-integral radius derivative theorem
supplies both weak radius integration formulas on a contained ball. -/
theorem weakRadiusIntegralFormulas_of_locallyL2_coarea {n m : ℕ} [NeZero n]
    {Du : Domain n → Gradient n m} {Ω : Set (Domain n)} {R0 : ℝ}
    (hcoarea : BallIntegralRadiusDerivativeFormula n)
    (hDu_meas : GradientAEStronglyMeasurableIn Du Ω)
    (hgrad : GradientLocallyL2In Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω) :
    WeakRadiusIntegralFormulas Du R0 := by
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
      IntegrableOn
        (fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x)
        (Metric.ball (0 : Domain n) R0) volume :=
    weakRadialEnergyDensity_integrableOn_of_energy
      (n := n) (m := m) (Du := Du)
      (Ω := Metric.ball (0 : Domain n) R0)
      henergy hradial_meas
  exact ⟨
    weakEnergyRadiusIntegralFormula_of_ballRadiusDerivative
      (n := n) (m := m) (Du := Du) (R0 := R0) hcoarea henergy,
    weakRadialEnergyRadiusIntegralFormula_of_ballRadiusDerivative
      (n := n) (m := m) (Du := Du) (R0 := R0) hcoarea hradial⟩

/-- Local `L²` control plus the restricted generic ball-integral radius
derivative theorem supplies both restricted weak radius integration formulas on
a contained ball. -/
theorem weakRadiusIntegralFormulasForWeights_of_locallyL2_coarea
    {n m : ℕ} [NeZero n]
    {Du : Domain n → Gradient n m} {Ω : Set (Domain n)} {R0 : ℝ}
    (hcoarea : BallIntegralRadiusDerivativeFormulaForWeights n)
    (hDu_meas : GradientAEStronglyMeasurableIn Du Ω)
    (hgrad : GradientLocallyL2In Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω) :
    WeakRadiusIntegralFormulasForWeights Du R0 := by
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
      IntegrableOn
        (fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x)
        (Metric.ball (0 : Domain n) R0) volume :=
    weakRadialEnergyDensity_integrableOn_of_energy
      (n := n) (m := m) (Du := Du)
      (Ω := Metric.ball (0 : Domain n) R0)
      henergy hradial_meas
  exact ⟨
    weakEnergyRadiusIntegralFormulaForWeights_of_ballRadiusDerivativeForWeights
      (n := n) (m := m) (Du := Du) (R0 := R0) hcoarea henergy,
    weakRadialEnergyRadiusIntegralFormulaForWeights_of_ballRadiusDerivativeForWeights
      (n := n) (m := m) (Du := Du) (R0 := R0) hcoarea hradial⟩

/-- `W^{1,2}_{loc}` data plus the generic ball-integral radius derivative
theorem supplies both weak radius integration formulas. -/
theorem weakRadiusIntegralFormulas_of_W12LocIn_coarea {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)} {R0 : ℝ}
    (hcoarea : BallIntegralRadiusDerivativeFormula n)
    (hW : W12LocIn u Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω) :
    WeakRadiusIntegralFormulas Du R0 :=
  weakRadiusIntegralFormulas_of_locallyL2_coarea
    (n := n) (m := m) (Du := Du) (Ω := Ω) (R0 := R0)
    hcoarea hW.gradient_aestronglyMeasurable hW.gradient_locallyL2
    hclosedBall_subset

/-- `W^{1,2}_{loc}` data plus the restricted generic ball-integral radius
derivative theorem supplies both restricted weak radius integration formulas. -/
theorem weakRadiusIntegralFormulasForWeights_of_W12LocIn_coarea
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)} {R0 : ℝ}
    (hcoarea : BallIntegralRadiusDerivativeFormulaForWeights n)
    (hW : W12LocIn u Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω) :
    WeakRadiusIntegralFormulasForWeights Du R0 :=
  weakRadiusIntegralFormulasForWeights_of_locallyL2_coarea
    (n := n) (m := m) (Du := Du) (Ω := Ω) (R0 := R0)
    hcoarea hW.gradient_aestronglyMeasurable hW.gradient_locallyL2
    hclosedBall_subset

/-- `W^{1,2}_{loc}` data plus bounded a.e. interval-step approximation of
radius weights supplies the two restricted weak radius integration formulas.
This is the direct bridge from the finite-step cutoff/coarea core to the weak
map package. -/
theorem weakRadiusIntegralFormulasForWeights_of_W12LocIn_finiteIntervalStepApproxAE
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)} {R0 : ℝ}
    (hR0_pos : 0 < R0)
    (happrox : ∀ c : ℝ → ℝ,
      RadiusWeightOn R0 c → RadiusWeightFiniteIntervalStepApproxAE R0 c)
    (hW : W12LocIn u Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω) :
    WeakRadiusIntegralFormulasForWeights Du R0 := by
  have henergy :
      IntegrableOn (fun x : Domain n => weakEnergyDensity Du x)
        (Metric.ball (0 : Domain n) R0) volume :=
    gradientLocallyL2In_integrableOn_ball
      (n := n) (m := m) (Du := Du) (Ω := Ω)
      hW.gradient_locallyL2 hclosedBall_subset
  have henergy_ac :
      BallIntegralRadiusAbsolutelyContinuous
        (fun x : Domain n => weakEnergyDensity Du x) R0 :=
    ballIntegralRadiusAbsolutelyContinuous_of_radialOpenShellsVolumeTendstoZero
      (n := n) (f := fun x : Domain n => weakEnergyDensity Du x) (R0 := R0)
      (radialOpenShellsVolumeTendstoZero_euclidean n) henergy
  have hradial_meas :
      AEStronglyMeasurable
        (fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x)
        (volume.restrict (Metric.ball (0 : Domain n) R0)) :=
    weakRadialEnergyDensity_aestronglyMeasurable_on_ball_of_gradient
      (n := n) (m := m) (Du := Du) (Ω := Ω)
      (a := 0) (r := R0) hW.gradient_aestronglyMeasurable hclosedBall_subset
  have hradial :
      IntegrableOn
        (fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x)
        (Metric.ball (0 : Domain n) R0) volume :=
    weakRadialEnergyDensity_integrableOn_of_energy
      (n := n) (m := m) (Du := Du)
      (Ω := Metric.ball (0 : Domain n) R0)
      henergy hradial_meas
  have hradial_ac :
      BallIntegralRadiusAbsolutelyContinuous
        (fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x) R0 :=
    ballIntegralRadiusAbsolutelyContinuous_of_radialOpenShellsVolumeTendstoZero
      (n := n)
      (f := fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x)
      (R0 := R0)
      (radialOpenShellsVolumeTendstoZero_euclidean n) hradial
  refine ⟨?_, ?_⟩
  · intro c hc
    exact
      ballIntegralRadiusDerivativeFormula_of_finiteIntervalStepApproxAE
        (n := n) (f := fun x : Domain n => weakEnergyDensity Du x)
        (R0 := R0) (c := c)
        hR0_pos henergy henergy_ac (happrox c hc)
  · intro c hc
    exact
      ballIntegralRadiusDerivativeFormula_of_finiteIntervalStepApproxAE
        (n := n)
        (f := fun x : Domain n => weakRadialEnergyDensity Du (0 : Domain n) x)
        (R0 := R0) (c := c)
        hR0_pos hradial hradial_ac (happrox c hc)

/-- The radius integration formula, after localization to an annulus, gives the
increment/FTC form of the radius calculus. -/
theorem weakEnergyRadiusIncrementFormula_of_radiusIntegral_annulus
    {n m : ℕ} {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hderiv_int : WeakEnergyRadiusDerivativeIntegrability Du R0)
    (henergy_radius : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0)
    (hannulus : WeakEnergyAnnulusFormula Du R0) :
    WeakEnergyRadiusIncrementFormula Du R0 := by
  constructor
  · intro a b ha hab hb
    refine ⟨hderiv_int.1 ha hab hb, ?_⟩
    calc
      weakBallEnergy Du (0 : Domain n) b -
          weakBallEnergy Du (0 : Domain n) a
          =
        ∫ x in Metric.ball (0 : Domain n) R0,
          (Ioo a b).indicator (fun _ : ℝ => (1 : ℝ)) ‖x‖ *
            weakEnergyDensity Du x := hannulus.1 ha hab hb
      _ =
        ∫ rho in Ioo (0 : ℝ) R0,
          (Ioo a b).indicator (fun _ : ℝ => (1 : ℝ)) rho *
            deriv (weakBallEnergy Du (0 : Domain n)) rho := by
          exact henergy_radius
            (fun rho : ℝ => (Ioo a b).indicator (fun _ : ℝ => (1 : ℝ)) rho)
      _ =
        ∫ rho in a..b, deriv (weakBallEnergy Du (0 : Domain n)) rho :=
          integral_Ioo_zero_radius_indicator_Ioo_eq_intervalIntegral
            (f := deriv (weakBallEnergy Du (0 : Domain n)))
            ha hab hb
  · intro a b ha hab hb
    refine ⟨hderiv_int.2 ha hab hb, ?_⟩
    calc
      weakBallRadialEnergy Du (0 : Domain n) b -
          weakBallRadialEnergy Du (0 : Domain n) a
          =
        ∫ x in Metric.ball (0 : Domain n) R0,
          (Ioo a b).indicator (fun _ : ℝ => (1 : ℝ)) ‖x‖ *
            weakRadialEnergyDensity Du (0 : Domain n) x := hannulus.2 ha hab hb
      _ =
        ∫ rho in Ioo (0 : ℝ) R0,
          (Ioo a b).indicator (fun _ : ℝ => (1 : ℝ)) rho *
            deriv (weakBallRadialEnergy Du (0 : Domain n)) rho := by
          exact hradial_radius
            (fun rho : ℝ => (Ioo a b).indicator (fun _ : ℝ => (1 : ℝ)) rho)
      _ =
        ∫ rho in a..b, deriv (weakBallRadialEnergy Du (0 : Domain n)) rho :=
          integral_Ioo_zero_radius_indicator_Ioo_eq_intervalIntegral
            (f := deriv (weakBallRadialEnergy Du (0 : Domain n)))
            ha hab hb

/-- Restricted-weight radius integration is enough for the annulus-localized
increment/FTC form, since the localization weight is the bounded measurable
indicator of `(a, b)`. -/
theorem weakEnergyRadiusIncrementFormula_of_radiusIntegralForWeights_annulus
    {n m : ℕ} {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hderiv_int : WeakEnergyRadiusDerivativeIntegrability Du R0)
    (henergy_radius : WeakEnergyRadiusIntegralFormulaForWeights Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormulaForWeights Du R0)
    (hannulus : WeakEnergyAnnulusFormula Du R0) :
    WeakEnergyRadiusIncrementFormula Du R0 := by
  constructor
  · intro a b ha hab hb
    refine ⟨hderiv_int.1 ha hab hb, ?_⟩
    calc
      weakBallEnergy Du (0 : Domain n) b -
          weakBallEnergy Du (0 : Domain n) a
          =
        ∫ x in Metric.ball (0 : Domain n) R0,
          (Ioo a b).indicator (fun _ : ℝ => (1 : ℝ)) ‖x‖ *
            weakEnergyDensity Du x := hannulus.1 ha hab hb
      _ =
        ∫ rho in Ioo (0 : ℝ) R0,
          (Ioo a b).indicator (fun _ : ℝ => (1 : ℝ)) rho *
            deriv (weakBallEnergy Du (0 : Domain n)) rho := by
          exact henergy_radius
            (fun rho : ℝ => (Ioo a b).indicator (fun _ : ℝ => (1 : ℝ)) rho)
            (radiusWeightOn_indicator_one (R0 := R0) (a := a) (b := b))
      _ =
        ∫ rho in a..b, deriv (weakBallEnergy Du (0 : Domain n)) rho :=
          integral_Ioo_zero_radius_indicator_Ioo_eq_intervalIntegral
            (f := deriv (weakBallEnergy Du (0 : Domain n)))
            ha hab hb
  · intro a b ha hab hb
    refine ⟨hderiv_int.2 ha hab hb, ?_⟩
    calc
      weakBallRadialEnergy Du (0 : Domain n) b -
          weakBallRadialEnergy Du (0 : Domain n) a
          =
        ∫ x in Metric.ball (0 : Domain n) R0,
          (Ioo a b).indicator (fun _ : ℝ => (1 : ℝ)) ‖x‖ *
            weakRadialEnergyDensity Du (0 : Domain n) x := hannulus.2 ha hab hb
      _ =
        ∫ rho in Ioo (0 : ℝ) R0,
          (Ioo a b).indicator (fun _ : ℝ => (1 : ℝ)) rho *
            deriv (weakBallRadialEnergy Du (0 : Domain n)) rho := by
          exact hradial_radius
            (fun rho : ℝ => (Ioo a b).indicator (fun _ : ℝ => (1 : ℝ)) rho)
            (radiusWeightOn_indicator_one (R0 := R0) (a := a) (b := b))
      _ =
        ∫ rho in a..b, deriv (weakBallRadialEnergy Du (0 : Domain n)) rho :=
          integral_Ioo_zero_radius_indicator_Ioo_eq_intervalIntegral
            (f := deriv (weakBallRadialEnergy Du (0 : Domain n)))
            ha hab hb

/-- The increment/FTC form gives the primitive form by fixing the left endpoint
and applying the increment identity to each intermediate radius. -/
theorem weakEnergyRadiusPrimitiveFormula_of_increment {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hinc : WeakEnergyRadiusIncrementFormula Du R0) :
    WeakEnergyRadiusPrimitiveFormula Du R0 := by
  constructor
  · intro a b ha hab hb
    rcases hinc.1 ha hab hb with ⟨hint, _hinc_ab⟩
    refine ⟨hint, ?_⟩
    intro r hr
    have hrange : a ≤ r ∧ r ≤ b := by
      simpa [uIcc_of_le hab] using hr
    rcases hinc.1 ha hrange.1 (hrange.2.trans hb) with ⟨_hint_ar, hinc_ar⟩
    linarith
  · intro a b ha hab hb
    rcases hinc.2 ha hab hb with ⟨hint, _hinc_ab⟩
    refine ⟨hint, ?_⟩
    intro r hr
    have hrange : a ≤ r ∧ r ≤ b := by
      simpa [uIcc_of_le hab] using hr
    rcases hinc.2 ha hrange.1 (hrange.2.trans hb) with ⟨_hint_ar, hinc_ar⟩
    linarith

/-- The radius primitive formula immediately gives absolute continuity of the
ball-energy and radial-energy radius functions. -/
theorem weakEnergyAbsolutelyContinuousOnRadii_of_radiusPrimitive {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hprim : WeakEnergyRadiusPrimitiveFormula Du R0) :
    WeakEnergyAbsolutelyContinuousOnRadii Du R0 := by
  constructor
  · intro a b ha hab hb
    rcases hprim.1 ha hab hb with ⟨hint, hEq⟩
    refine absolutelyContinuousOnInterval_congr_uIcc hEq ?_
    have hconst :
        AbsolutelyContinuousOnInterval
          (fun _ : ℝ => weakBallEnergy Du (0 : Domain n) a) a b := by
      apply ContDiffOn.absolutelyContinuousOnInterval
      exact contDiffOn_const
    have hint_ac :
        AbsolutelyContinuousOnInterval
          (fun r : ℝ => ∫ rho in a..r,
            deriv (weakBallEnergy Du (0 : Domain n)) rho) a b :=
      hint.absolutelyContinuousOnInterval_intervalIntegral (by simp [hab])
    exact hconst.add hint_ac
  · intro a b ha hab hb
    rcases hprim.2 ha hab hb with ⟨hint, hEq⟩
    refine absolutelyContinuousOnInterval_congr_uIcc hEq ?_
    have hconst :
        AbsolutelyContinuousOnInterval
          (fun _ : ℝ => weakBallRadialEnergy Du (0 : Domain n) a) a b := by
      apply ContDiffOn.absolutelyContinuousOnInterval
      exact contDiffOn_const
    have hint_ac :
        AbsolutelyContinuousOnInterval
          (fun r : ℝ => ∫ rho in a..r,
            deriv (weakBallRadialEnergy Du (0 : Domain n)) rho) a b :=
      hint.absolutelyContinuousOnInterval_intervalIntegral (by simp [hab])
    exact hconst.add hint_ac

/-- The increment/FTC form gives absolute continuity of the two radius energy
functions. -/
theorem weakEnergyAbsolutelyContinuousOnRadii_of_increment {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hinc : WeakEnergyRadiusIncrementFormula Du R0) :
    WeakEnergyAbsolutelyContinuousOnRadii Du R0 :=
  weakEnergyAbsolutelyContinuousOnRadii_of_radiusPrimitive
    (n := n) (m := m) (Du := Du) (R0 := R0)
    (weakEnergyRadiusPrimitiveFormula_of_increment
      (n := n) (m := m) (Du := Du) (R0 := R0) hinc)

/-- Absolute continuity of the ball-energy radius function gives the concrete
one-dimensional energy integration-by-parts formula. -/
theorem weakBallEnergyIBPFormula_of_radius_ac {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hac : WeakEnergyAbsolutelyContinuousOnRadii Du R0) :
    WeakBallEnergyIntegrationByPartsFormula Du R0 := by
  intro phi _hphi_diff hphi_cont _hphi_compact hphi_support
  let E : ℝ → ℝ := weakBallEnergy Du (0 : Domain n)
  let c : ℝ := (n : ℝ) - 2
  let F : ℝ → ℝ := fun rho => c * phi rho
  have hEac : AbsolutelyContinuousOnInterval E 0 R0 := by
    exact hac.1 (by norm_num) hR0_nonneg le_rfl
  have hFac : AbsolutelyContinuousOnInterval F 0 R0 := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    have hphi_on : ContDiffOn ℝ 1 phi (uIcc (0 : ℝ) R0) :=
      hphi_cont.contDiffOn
    simpa [F, smul_eq_mul] using hphi_on.const_smul c
  have hphi_R0 : phi R0 = 0 := by
    have hnot : R0 ∉ tsupport phi := by
      intro hmem
      exact (lt_irrefl R0) (hphi_support hmem)
    exact image_eq_zero_of_notMem_tsupport hnot
  have hE0 : E 0 = 0 := by
    simp [E, weakBallEnergy_zero_radius]
  have hibp :=
    AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul hFac hEac
  have hright :
      (∫ rho in (0 : ℝ)..R0, F rho * deriv E rho)
        =
      - ∫ rho in (0 : ℝ)..R0, deriv F rho * E rho := by
    rw [hibp]
    simp [F, hphi_R0, hE0]
  have hleft :
      (∫ rho in (0 : ℝ)..R0, (-deriv phi rho) * (c * E rho))
        =
      - ∫ rho in (0 : ℝ)..R0, deriv F rho * E rho := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with rho _hrho
    simp [F, deriv_const_mul_field]
    ring_nf
  have hinterval :
      (∫ rho in (0 : ℝ)..R0, (-deriv phi rho) * (c * E rho))
        =
      (∫ rho in (0 : ℝ)..R0, F rho * deriv E rho) := by
    rw [hleft, hright]
  calc
    (∫ rho in Ioo (0 : ℝ) R0, (-deriv phi rho) * (c * E rho))
        =
      (∫ rho in (0 : ℝ)..R0, (-deriv phi rho) * (c * E rho)) := by
        rw [intervalIntegral.integral_of_le hR0_nonneg]
        rw [integral_Ioc_eq_integral_Ioo]
    _ =
      (∫ rho in (0 : ℝ)..R0, F rho * deriv E rho) := hinterval
    _ =
      (∫ rho in Ioo (0 : ℝ) R0, F rho * deriv E rho) := by
        rw [intervalIntegral.integral_of_le hR0_nonneg]
        rw [integral_Ioc_eq_integral_Ioo]

/-- Absolute continuity of the ball-energy and radial-energy radius functions
also gives the integrability side conditions used in the one-dimensional
algebraic splitting. -/
theorem weakOneDimensionalIBPIntegrability_of_radius_ac {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hac : WeakEnergyAbsolutelyContinuousOnRadii Du R0) :
    WeakOneDimensionalIBPIntegrability Du R0 := by
  intro phi _hphi_diff hphi_cont _hphi_compact _hphi_support
  let E : ℝ → ℝ := weakBallEnergy Du (0 : Domain n)
  let Q : ℝ → ℝ := weakBallRadialEnergy Du (0 : Domain n)
  let c : ℝ := (n : ℝ) - 2
  have hEac : AbsolutelyContinuousOnInterval E 0 R0 := by
    exact hac.1 (by norm_num) hR0_nonneg le_rfl
  have hQac : AbsolutelyContinuousOnInterval Q 0 R0 := by
    exact hac.2 (by norm_num) hR0_nonneg le_rfl
  have hEcont : ContinuousOn E (uIcc (0 : ℝ) R0) := hEac.continuousOn
  have hEderiv_int : IntervalIntegrable (deriv E) volume (0 : ℝ) R0 :=
    hEac.intervalIntegrable_deriv
  have hQderiv_int : IntervalIntegrable (deriv Q) volume (0 : ℝ) R0 :=
    hQac.intervalIntegrable_deriv
  have hphi_continuous : Continuous phi := hphi_cont.continuous
  have hderiv_continuous : Continuous (deriv phi) :=
    hphi_cont.continuous_deriv_one
  have hD_cont :
      ContinuousOn (fun rho : ℝ => (-deriv phi rho) * (c * E rho))
        (uIcc (0 : ℝ) R0) := by
    fun_prop
  have hA_coeff_cont :
      ContinuousOn (fun rho : ℝ => c * phi rho) (uIcc (0 : ℝ) R0) := by
    fun_prop
  have hB_coeff_cont :
      ContinuousOn (fun rho : ℝ => rho * deriv phi rho)
        (uIcc (0 : ℝ) R0) := by
    fun_prop
  have hD_intvl :
      IntervalIntegrable (fun rho : ℝ => (-deriv phi rho) * (c * E rho))
        volume (0 : ℝ) R0 :=
    hD_cont.intervalIntegrable
  have hA_intvl :
      IntervalIntegrable (fun rho : ℝ => (c * phi rho) * deriv E rho)
        volume (0 : ℝ) R0 :=
    hEderiv_int.continuousOn_mul hA_coeff_cont
  have hB_intvl :
      IntervalIntegrable (fun rho : ℝ => (rho * deriv phi rho) * deriv E rho)
        volume (0 : ℝ) R0 :=
    hEderiv_int.continuousOn_mul hB_coeff_cont
  have hC_intvl :
      IntervalIntegrable (fun rho : ℝ => (rho * deriv phi rho) * deriv Q rho)
        volume (0 : ℝ) R0 :=
    hQderiv_int.continuousOn_mul hB_coeff_cont
  exact ⟨
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hR0_nonneg).mp hD_intvl,
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hR0_nonneg).mp hA_intvl,
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hR0_nonneg).mp hB_intvl,
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hR0_nonneg).mp hC_intvl⟩

/-- Constructor for the packaged one-dimensional calculus: on a nonnegative
radius interval, absolute continuity of `E(r)` and `Q(r)` supplies both the
energy IBP formula and the integrability side conditions. -/
theorem weakBallEnergyOneDimensionalCalculus_of_radius_ac {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hac : WeakEnergyAbsolutelyContinuousOnRadii Du R0) :
    WeakBallEnergyOneDimensionalCalculus Du R0 :=
  ⟨hac,
    weakBallEnergyIBPFormula_of_radius_ac
      (n := n) (m := m) (Du := Du) (R0 := R0) hR0_nonneg hac,
    weakOneDimensionalIBPIntegrability_of_radius_ac
      (n := n) (m := m) (Du := Du) (R0 := R0) hR0_nonneg hac⟩

/-- Constructor for the packaged one-dimensional calculus from the
increment/FTC form of the radius energy identities. -/
theorem weakBallEnergyOneDimensionalCalculus_of_increment {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hinc : WeakEnergyRadiusIncrementFormula Du R0) :
    WeakBallEnergyOneDimensionalCalculus Du R0 :=
  weakBallEnergyOneDimensionalCalculus_of_radius_ac
    (n := n) (m := m) (Du := Du) (R0 := R0)
    hR0_nonneg
    (weakEnergyAbsolutelyContinuousOnRadii_of_increment
      (n := n) (m := m) (Du := Du) (R0 := R0) hinc)

/-- Constructor for the packaged one-dimensional calculus from radius
integration localized to annuli. -/
theorem weakBallEnergyOneDimensionalCalculus_of_radiusIntegral_annulus {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hderiv_int : WeakEnergyRadiusDerivativeIntegrability Du R0)
    (henergy_radius : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0)
    (hannulus : WeakEnergyAnnulusFormula Du R0) :
    WeakBallEnergyOneDimensionalCalculus Du R0 :=
  weakBallEnergyOneDimensionalCalculus_of_increment
    (n := n) (m := m) (Du := Du) (R0 := R0) hR0_nonneg
    (weakEnergyRadiusIncrementFormula_of_radiusIntegral_annulus
      (n := n) (m := m) (Du := Du) (R0 := R0)
      hderiv_int henergy_radius hradial_radius hannulus)

/-- Restricted-weight radius integration over annuli gives the packaged
one-dimensional calculus. -/
theorem weakBallEnergyOneDimensionalCalculus_of_radiusIntegralForWeights_annulus
    {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hderiv_int : WeakEnergyRadiusDerivativeIntegrability Du R0)
    (henergy_radius : WeakEnergyRadiusIntegralFormulaForWeights Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormulaForWeights Du R0)
    (hannulus : WeakEnergyAnnulusFormula Du R0) :
    WeakBallEnergyOneDimensionalCalculus Du R0 :=
  weakBallEnergyOneDimensionalCalculus_of_increment
    (n := n) (m := m) (Du := Du) (R0 := R0) hR0_nonneg
    (weakEnergyRadiusIncrementFormula_of_radiusIntegralForWeights_annulus
      (n := n) (m := m) (Du := Du) (R0 := R0)
      hderiv_int henergy_radius hradial_radius hannulus)

/-- Radius integration over annuli plus radius absolute continuity gives the
one-dimensional calculus package; the derivative integrability is extracted
automatically from the absolute-continuity input. -/
theorem weakBallEnergyOneDimensionalCalculus_of_radiusIntegral_annulus_radius_ac
    {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hac : WeakEnergyAbsolutelyContinuousOnRadii Du R0)
    (henergy_radius : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0)
    (hannulus : WeakEnergyAnnulusFormula Du R0) :
    WeakBallEnergyOneDimensionalCalculus Du R0 :=
  weakBallEnergyOneDimensionalCalculus_of_radiusIntegral_annulus
    (n := n) (m := m) (Du := Du) (R0 := R0)
    hR0_nonneg
    (weakEnergyRadiusDerivativeIntegrability_of_radius_ac
      (n := n) (m := m) (Du := Du) (R0 := R0) hac)
    henergy_radius hradial_radius hannulus

/-- Restricted-weight radius integration over annuli plus radius absolute
continuity gives the one-dimensional calculus package. -/
theorem weakBallEnergyOneDimensionalCalculus_of_radiusIntegralForWeights_annulus_radius_ac
    {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hac : WeakEnergyAbsolutelyContinuousOnRadii Du R0)
    (henergy_radius : WeakEnergyRadiusIntegralFormulaForWeights Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormulaForWeights Du R0)
    (hannulus : WeakEnergyAnnulusFormula Du R0) :
    WeakBallEnergyOneDimensionalCalculus Du R0 :=
  weakBallEnergyOneDimensionalCalculus_of_radiusIntegralForWeights_annulus
    (n := n) (m := m) (Du := Du) (R0 := R0)
    hR0_nonneg
    (weakEnergyRadiusDerivativeIntegrability_of_radius_ac
      (n := n) (m := m) (Du := Du) (R0 := R0) hac)
    henergy_radius hradial_radius hannulus

/-- Local `L²` control supplies the annulus formula needed by the radius
integration route to the one-dimensional calculus package. -/
theorem weakBallEnergyOneDimensionalCalculus_of_radiusIntegral_locallyL2
    {n m : ℕ} [NeZero n]
    {Du : Domain n → Gradient n m} {Ω : Set (Domain n)} {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hDu_meas : GradientAEStronglyMeasurableIn Du Ω)
    (hgrad : GradientLocallyL2In Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hderiv_int : WeakEnergyRadiusDerivativeIntegrability Du R0)
    (henergy_radius : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0) :
    WeakBallEnergyOneDimensionalCalculus Du R0 :=
  weakBallEnergyOneDimensionalCalculus_of_radiusIntegral_annulus
    (n := n) (m := m) (Du := Du) (R0 := R0)
    hR0_nonneg hderiv_int henergy_radius hradial_radius
    (weakEnergyAnnulusFormula_of_locallyL2
      (n := n) (m := m) (Du := Du) (Ω := Ω) (R0 := R0)
      hDu_meas hgrad hclosedBall_subset)

/-- Local `L²` control supplies the annulus formula needed by the
restricted-weight radius integration route to the one-dimensional calculus
package. -/
theorem weakBallEnergyOneDimensionalCalculus_of_radiusIntegralForWeights_locallyL2
    {n m : ℕ} [NeZero n]
    {Du : Domain n → Gradient n m} {Ω : Set (Domain n)} {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hDu_meas : GradientAEStronglyMeasurableIn Du Ω)
    (hgrad : GradientLocallyL2In Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hderiv_int : WeakEnergyRadiusDerivativeIntegrability Du R0)
    (henergy_radius : WeakEnergyRadiusIntegralFormulaForWeights Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormulaForWeights Du R0) :
    WeakBallEnergyOneDimensionalCalculus Du R0 :=
  weakBallEnergyOneDimensionalCalculus_of_radiusIntegralForWeights_annulus
    (n := n) (m := m) (Du := Du) (R0 := R0)
    hR0_nonneg hderiv_int henergy_radius hradial_radius
    (weakEnergyAnnulusFormula_of_locallyL2
      (n := n) (m := m) (Du := Du) (Ω := Ω) (R0 := R0)
      hDu_meas hgrad hclosedBall_subset)

/-- `W^{1,2}_{loc}` supplies the annulus formula needed by the radius
integration route to the one-dimensional calculus package. -/
theorem weakBallEnergyOneDimensionalCalculus_of_radiusIntegral_W12LocIn
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)} {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hW : W12LocIn u Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hderiv_int : WeakEnergyRadiusDerivativeIntegrability Du R0)
    (henergy_radius : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0) :
    WeakBallEnergyOneDimensionalCalculus Du R0 :=
  weakBallEnergyOneDimensionalCalculus_of_radiusIntegral_locallyL2
    (n := n) (m := m) (Du := Du) (Ω := Ω) (R0 := R0)
    hR0_nonneg hW.gradient_aestronglyMeasurable hW.gradient_locallyL2
    hclosedBall_subset hderiv_int henergy_radius hradial_radius

/-- `W^{1,2}_{loc}` supplies the annulus formula needed by the
restricted-weight radius integration route to the one-dimensional calculus
package. -/
theorem weakBallEnergyOneDimensionalCalculus_of_radiusIntegralForWeights_W12LocIn
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)} {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hW : W12LocIn u Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hderiv_int : WeakEnergyRadiusDerivativeIntegrability Du R0)
    (henergy_radius : WeakEnergyRadiusIntegralFormulaForWeights Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormulaForWeights Du R0) :
    WeakBallEnergyOneDimensionalCalculus Du R0 :=
  weakBallEnergyOneDimensionalCalculus_of_radiusIntegralForWeights_locallyL2
    (n := n) (m := m) (Du := Du) (Ω := Ω) (R0 := R0)
    hR0_nonneg hW.gradient_aestronglyMeasurable hW.gradient_locallyL2
    hclosedBall_subset hderiv_int henergy_radius hradial_radius

/-- Local `L²` supplies the annulus formula, while radius absolute continuity
supplies derivative integrability; this is the annulus route without a separate
`WeakEnergyRadiusDerivativeIntegrability` assumption. -/
theorem weakBallEnergyOneDimensionalCalculus_of_radiusIntegral_locallyL2_radius_ac
    {n m : ℕ} [NeZero n]
    {Du : Domain n → Gradient n m} {Ω : Set (Domain n)} {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hDu_meas : GradientAEStronglyMeasurableIn Du Ω)
    (hgrad : GradientLocallyL2In Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hac : WeakEnergyAbsolutelyContinuousOnRadii Du R0)
    (henergy_radius : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0) :
    WeakBallEnergyOneDimensionalCalculus Du R0 :=
  weakBallEnergyOneDimensionalCalculus_of_radiusIntegral_annulus_radius_ac
    (n := n) (m := m) (Du := Du) (R0 := R0)
    hR0_nonneg hac henergy_radius hradial_radius
    (weakEnergyAnnulusFormula_of_locallyL2
      (n := n) (m := m) (Du := Du) (Ω := Ω) (R0 := R0)
      hDu_meas hgrad hclosedBall_subset)

/-- Local `L²` supplies the annulus formula, while radius absolute continuity
supplies derivative integrability; this is the restricted-weight annulus route
without a separate derivative-integrability hypothesis. -/
theorem weakBallEnergyOneDimensionalCalculus_of_radiusIntegralForWeights_locallyL2_radius_ac
    {n m : ℕ} [NeZero n]
    {Du : Domain n → Gradient n m} {Ω : Set (Domain n)} {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hDu_meas : GradientAEStronglyMeasurableIn Du Ω)
    (hgrad : GradientLocallyL2In Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hac : WeakEnergyAbsolutelyContinuousOnRadii Du R0)
    (henergy_radius : WeakEnergyRadiusIntegralFormulaForWeights Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormulaForWeights Du R0) :
    WeakBallEnergyOneDimensionalCalculus Du R0 :=
  weakBallEnergyOneDimensionalCalculus_of_radiusIntegralForWeights_annulus_radius_ac
    (n := n) (m := m) (Du := Du) (R0 := R0)
    hR0_nonneg hac henergy_radius hradial_radius
    (weakEnergyAnnulusFormula_of_locallyL2
      (n := n) (m := m) (Du := Du) (Ω := Ω) (R0 := R0)
      hDu_meas hgrad hclosedBall_subset)

/-- `W^{1,2}_{loc}` supplies the annulus formula, while radius absolute
continuity supplies derivative integrability; this is the `W^{1,2}` packaged
version with no separate derivative-integrability hypothesis. -/
theorem weakBallEnergyOneDimensionalCalculus_of_radiusIntegral_W12LocIn_radius_ac
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)} {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hW : W12LocIn u Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hac : WeakEnergyAbsolutelyContinuousOnRadii Du R0)
    (henergy_radius : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0) :
    WeakBallEnergyOneDimensionalCalculus Du R0 :=
  weakBallEnergyOneDimensionalCalculus_of_radiusIntegral_locallyL2_radius_ac
    (n := n) (m := m) (Du := Du) (Ω := Ω) (R0 := R0)
    hR0_nonneg hW.gradient_aestronglyMeasurable hW.gradient_locallyL2
    hclosedBall_subset hac henergy_radius hradial_radius

/-- `W^{1,2}_{loc}` supplies the annulus formula, while radius absolute
continuity supplies derivative integrability; this is the restricted-weight
packaged version with no separate derivative-integrability hypothesis. -/
theorem weakBallEnergyOneDimensionalCalculus_of_radiusIntegralForWeights_W12LocIn_radius_ac
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)} {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hW : W12LocIn u Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (hac : WeakEnergyAbsolutelyContinuousOnRadii Du R0)
    (henergy_radius : WeakEnergyRadiusIntegralFormulaForWeights Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormulaForWeights Du R0) :
    WeakBallEnergyOneDimensionalCalculus Du R0 :=
  weakBallEnergyOneDimensionalCalculus_of_radiusIntegralForWeights_locallyL2_radius_ac
    (n := n) (m := m) (Du := Du) (Ω := Ω) (R0 := R0)
    hR0_nonneg hW.gradient_aestronglyMeasurable hW.gradient_locallyL2
    hclosedBall_subset hac henergy_radius hradial_radius

/-- The radius-integration route with the generic `L¹` ball-integral AC theorem
supplying the radius absolute-continuity input from `W^{1,2}_{loc}`. -/
theorem weakBallEnergyOneDimensionalCalculus_of_radiusIntegral_W12LocIn_ballIntegralAC
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)} {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hball_ac : BallIntegralRadiusACOfIntegrableOnBall n)
    (hW : W12LocIn u Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (henergy_radius : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0) :
    WeakBallEnergyOneDimensionalCalculus Du R0 :=
  weakBallEnergyOneDimensionalCalculus_of_radiusIntegral_W12LocIn_radius_ac
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
    hR0_nonneg hW hclosedBall_subset
    (weakEnergyAbsolutelyContinuousOnRadii_of_W12LocIn_ballIntegralAC
      (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
      hball_ac hW hclosedBall_subset)
    henergy_radius hradial_radius

/-- The restricted-weight radius-integration route with the generic `L¹`
ball-integral AC theorem supplying the radius absolute-continuity input from
`W^{1,2}_{loc}`. -/
theorem weakBallEnergyOneDimensionalCalculus_of_radiusIntegralForWeights_W12LocIn_ballIntegralAC
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)} {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hball_ac : BallIntegralRadiusACOfIntegrableOnBall n)
    (hW : W12LocIn u Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (henergy_radius : WeakEnergyRadiusIntegralFormulaForWeights Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormulaForWeights Du R0) :
    WeakBallEnergyOneDimensionalCalculus Du R0 :=
  weakBallEnergyOneDimensionalCalculus_of_radiusIntegralForWeights_W12LocIn_radius_ac
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
    hR0_nonneg hW hclosedBall_subset
    (weakEnergyAbsolutelyContinuousOnRadii_of_W12LocIn_ballIntegralAC
      (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
      hball_ac hW hclosedBall_subset)
    henergy_radius hradial_radius

/-- The radius-integration route with thin radial-shell volume control supplying
the radius absolute-continuity input from `W^{1,2}_{loc}`. -/
theorem weakBallEnergyOneDimensionalCalculus_of_radiusIntegral_W12LocIn_radialShellsVolume
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)} {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hthin : RadialOpenShellsVolumeTendstoZero n)
    (hW : W12LocIn u Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (henergy_radius : WeakEnergyRadiusIntegralFormula Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormula Du R0) :
    WeakBallEnergyOneDimensionalCalculus Du R0 :=
  weakBallEnergyOneDimensionalCalculus_of_radiusIntegral_W12LocIn_radius_ac
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
    hR0_nonneg hW hclosedBall_subset
    (weakEnergyAbsolutelyContinuousOnRadii_of_W12LocIn_radialShellsVolume
      (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
      hthin hW hclosedBall_subset)
    henergy_radius hradial_radius

/-- The restricted-weight radius-integration route with thin radial-shell
volume control supplying the radius absolute-continuity input from
`W^{1,2}_{loc}`. -/
theorem weakBallEnergyOneDimensionalCalculus_of_radiusIntegralForWeights_W12LocIn_radialShellsVolume
    {n m : ℕ} [NeZero n]
    {u : Domain n → Target m} {Du : Domain n → Gradient n m}
    {Ω : Set (Domain n)} {R0 : ℝ}
    (hR0_nonneg : 0 ≤ R0)
    (hthin : RadialOpenShellsVolumeTendstoZero n)
    (hW : W12LocIn u Du Ω)
    (hclosedBall_subset : Metric.closedBall (0 : Domain n) R0 ⊆ Ω)
    (henergy_radius : WeakEnergyRadiusIntegralFormulaForWeights Du R0)
    (hradial_radius : WeakRadialEnergyRadiusIntegralFormulaForWeights Du R0) :
    WeakBallEnergyOneDimensionalCalculus Du R0 :=
  weakBallEnergyOneDimensionalCalculus_of_radiusIntegralForWeights_W12LocIn_radius_ac
    (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
    hR0_nonneg hW hclosedBall_subset
    (weakEnergyAbsolutelyContinuousOnRadii_of_W12LocIn_radialShellsVolume
      (n := n) (m := m) (u := u) (Du := Du) (Ω := Ω) (R0 := R0)
      hthin hW hclosedBall_subset)
    henergy_radius hradial_radius

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps

end
