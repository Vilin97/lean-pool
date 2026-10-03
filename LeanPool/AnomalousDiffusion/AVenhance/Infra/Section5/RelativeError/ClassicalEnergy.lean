/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.TimeEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.PeriodicCalculus
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.ClassicalRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.BreakUp.Slicing
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SmoothField

/-!# RelativeError: classical periodic energy and mean identities

These are the energy and mean bridges for the smooth torus solution used in
the RelativeError trace estimate.  The spatial transport and Laplacian integrations by
parts reuse the established periodic calculus.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set intervalIntegral
open Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance
open AVenhance.Infra.Classical
open AVenhance.Infra.Section5.LeftToShow
open AVenhance.Infra.Torus

/-- The spatial Dirichlet energy of a classical solution at a fixed time,
computed on the half-open torus cell. -/
def classicalCellGradientEnergy (u : ℝ → Vec 2 → ℝ) (t : ℝ) : ℝ :=
  ∫ x in unitCell 2, vecNormSq (spaceGrad (u t) x)

theorem classical_slice_laplacian_continuous
    {u : ℝ → Vec 2 → ℝ} {t : ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) (u t)) :
    Continuous (spaceLap (u t)) := by
  have hgrad (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => spaceGrad (u t) x i) := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun x => fderiv ℝ (u t) x (basisVec i))
    exact (hu.fderiv_right (by simp)).clm_apply contDiff_const
  have hterm (i : Fin 2) : Continuous
      (fun x => spaceGrad (fun y => spaceGrad (u t) y i) x i) := by
    change Continuous (fun x =>
      fderiv ℝ (fun y => spaceGrad (u t) y i) x (basisVec i))
    exact (hgrad i).continuous_fderiv (by simp) |>.clm_apply continuous_const
  change Continuous (fun x => ∑ i : Fin 2,
    spaceGrad (fun y => spaceGrad (u t) y i) x i)
  exact continuous_finsetSum Finset.univ (fun i hi => hterm i)

/-- The classical PDE gives the periodic energy derivative at every positive
time. -/
theorem classical_solution_energy_derivative
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {g : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ}
    (hb : Infra.Flow.SmoothPeriodicField b)
    (hdiv : ∀ t x, vecDiv (b t) x = 0)
    (hsol : IsClassicalSol b κ (fun _ _ => 0) g u)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x in unitCell 2, (u s x) ^ 2)
      (-2 * κ * classicalCellGradientEnergy u t) t := by
  have hslice : ContDiff ℝ (⊤ : ℕ∞) (u t) :=
    classicalSmooth_slice_nonneg hsol.1 (le_of_lt ht)
  have hper : IsZ2Periodic (u t) := hsol.2.1 t (le_of_lt ht)
  have hpartial := unitCell_energy_hasDerivAt hsol.1 ht
  have huOpen : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u)
      classicalPositiveTimeDomain := hsol.1.mono (by
        intro p hp
        simp only [classicalPositiveTimeDomain, Set.mem_prod, Set.mem_Ioi,
          Set.mem_univ] at hp
        exact ⟨le_of_lt hp.1, trivial⟩)
  have hpartialTime := classicalTimePartial_eq_deriv huOpen ht
  have hpde0 := hsol.2.2.2 t ht
  have hpde : ∀ x, classicalTimePartial u (t, x) =
      κ * spaceLap (u t) x - vecDot (b t x) (spaceGrad (u t) x) := by
    intro x
    have heq := hpde0 x
    change deriv (fun s => u s x) t - κ * spaceLap (u t) x +
      vecDot (b t x) (spaceGrad (u t) x) = 0 at heq
    rw [← hpartialTime x] at heq
    dsimp [classicalTimePartial] at heq ⊢
    linarith
  have hbSlice : ContDiff ℝ (⊤ : ℕ∞) (b t) := by
    have hembed : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)) := by fun_prop
    exact hb.smooth.comp hembed
  have hbper (i : Fin 2) : IsZ2Periodic (fun x => b t x i) := by
    intro k x
    have h := hb.periodic 0 k t x
    simpa using congrArg (fun z : Vec 2 => z i) h
  have hpartialCont : Continuous (fun x => classicalTimePartial u (t, x)) :=
    classicalTimePartial_continuous_slice huOpen ht
  have hgradCont : Continuous (spaceGrad (u t)) :=
    (classicalSol_spaceGrad_contDiff_of_nonneg hsol (le_of_lt ht)).continuous
  have hlapCont : Continuous (spaceLap (u t)) :=
    classical_slice_laplacian_continuous hslice
  have htermsInt : IntegrableOn
      (fun x => 2 * u t x * classicalTimePartial u (t, x)) (unitCell 2) :=
    continuous_integrableOn_unitCell ((continuous_const.mul hslice.continuous).mul hpartialCont)
  have hlapInt : IntegrableOn
      (fun x => u t x * spaceLap (u t) x) (unitCell 2) :=
    continuous_integrableOn_unitCell (hslice.continuous.mul hlapCont)
  have htransportInt : IntegrableOn
      (fun x => vecDot (b t x) (spaceGrad (u t) x) * u t x) (unitCell 2) := by
    apply continuous_integrableOn_unitCell
    change Continuous (fun x =>
      (∑ i : Fin 2, b t x i * spaceGrad (u t) x i) * u t x)
    have hgradComp : ∀ i : Fin 2, Continuous (fun x => spaceGrad (u t) x i) := by
      intro i
      exact (continuous_apply i).comp hgradCont
    exact (continuous_finsetSum Finset.univ (fun i hi =>
      ((contDiff_pi.1 hbSlice) i).continuous.mul (hgradComp i))).mul hslice.continuous
  have hpoint (x : Vec 2) :
      2 * u t x * classicalTimePartial u (t, x) =
        2 * κ * (u t x * spaceLap (u t) x) -
          2 * (vecDot (b t x) (spaceGrad (u t) x) * u t x) := by
    rw [hpde x]
    ring
  have hintegral :
      (∫ x in unitCell 2, 2 * u t x * classicalTimePartial u (t, x)) =
        2 * κ * (∫ x in unitCell 2, u t x * spaceLap (u t) x) -
          2 * (∫ x in unitCell 2,
            vecDot (b t x) (spaceGrad (u t) x) * u t x) := by
    calc
      _ = ∫ x in unitCell 2,
          (2 * κ * (u t x * spaceLap (u t) x) -
            2 * (vecDot (b t x) (spaceGrad (u t) x) * u t x)) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          exact hpoint x
      _ = _ := by
          rw [MeasureTheory.integral_sub (hlapInt.const_mul (2 * κ))
            (htransportInt.const_mul 2), MeasureTheory.integral_const_mul,
            MeasureTheory.integral_const_mul]
  have hlap := integral_unitCell_lap_energy hslice hper
  have htransport := integral_unitCell_transport_energy_zero (b t)
    (hbSlice.of_le (by norm_num)) hbper
    (hdiv t) (u t) (hslice.of_le (by norm_num)) hper
  have hgradReplace :
      (∫ x in unitCell 2,
        vecDot (spaceGrad (u t) x) (spaceGrad (u t) x)) =
      classicalCellGradientEnergy u t := by
    rfl
  have hformula :
      (∫ x in unitCell 2, 2 * u t x * classicalTimePartial u (t, x)) =
        -2 * κ * classicalCellGradientEnergy u t := by
    rw [hintegral, htransport, hlap, hgradReplace]
    ring
  convert hpartial using 1
  exact hformula.symm

/-- Integrating the classical energy derivative from the initial trace gives
the exact periodic energy identity. -/
theorem classical_solution_energy_identity
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {g : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ}
    (hb : Infra.Flow.SmoothPeriodicField b)
    (hdiv : ∀ t x, vecDiv (b t) x = 0)
    (hsol : IsClassicalSol b κ (fun _ _ => 0) g u)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (∫ x in unitCell 2, (u t x) ^ 2) +
      2 * κ * (∫ s in (0 : ℝ)..t, classicalCellGradientEnergy u s) =
        ∫ x in unitCell 2, g x ^ 2 := by
  have hgradJoint := LeftToShow.spaceGrad_continuousOn hsol.1
  have hgradEnergyJoint :
      ContinuousOn (fun p : ℝ × Vec 2 => vecNormSq (spaceGrad (u p.1) p.2))
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
    apply LeftToShow.continuous_vecNormSq_two.comp_continuousOn
    exact hgradJoint.mono (by
      rintro ⟨s, x⟩ ⟨hs, hx⟩
      exact ⟨hs.1, trivial⟩)
  have hgradEnergyCube :
      ContinuousOn (fun s => ∫ x in unitCube, vecNormSq (spaceGrad (u s) x))
        (Set.Icc (0 : ℝ) 1) :=
    LeftToShow.continuousOn_integral_unitCube hgradEnergyJoint
  have hcellCube : (fun s => classicalCellGradientEnergy u s) =
      (fun s => ∫ x in unitCube, vecNormSq (spaceGrad (u s) x)) := by
    funext s
    exact Infra.Torus.integral_unitCell_eq_unitCube _
  have hgradEnergyContinuous :
      ContinuousOn (classicalCellGradientEnergy u) (Set.Icc (0 : ℝ) t) := by
    change ContinuousOn (fun s => classicalCellGradientEnergy u s) (Set.Icc (0 : ℝ) t)
    rw [hcellCube]
    exact hgradEnergyCube.mono (by
      intro s hs
      exact ⟨hs.1, le_trans hs.2 ht1⟩)
  have hderivInt : IntervalIntegrable
      (fun s => -2 * κ * classicalCellGradientEnergy u s) volume 0 t := by
    have hcontU : ContinuousOn (classicalCellGradientEnergy u)
        (Set.uIcc (0 : ℝ) t) := by
      rw [Set.uIcc_of_le (le_of_lt ht)]
      exact hgradEnergyContinuous
    have hcont := hcontU.const_mul (-2 * κ)
    simpa [mul_assoc] using hcont.intervalIntegrable
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (le_of_lt ht) (unitCell_energy_continuousOn hsol.1 (le_of_lt ht))
    (fun s hs => classical_solution_energy_derivative hb hdiv hsol hs.1)
    hderivInt
  have hFTC' :
      (-2 * κ) * (∫ s in (0 : ℝ)..t, classicalCellGradientEnergy u s) =
        (∫ x in unitCell 2, (u t x) ^ 2) -
          (∫ x in unitCell 2, (u 0 x) ^ 2) := by
    simpa only [intervalIntegral.integral_const_mul] using hFTC
  have hinitial : (∫ x in unitCell 2, (u 0 x) ^ 2) =
      ∫ x in unitCell 2, g x ^ 2 := by
    apply setIntegral_congr_fun (Infra.Torus.measurableSet_unitCell 2)
    intro x hx
    change (u 0 x) ^ 2 = (g x) ^ 2
    rw [hsol.2.2.1 x]
  linarith

end AVenhance.Infra.Section5.RelativeError

end
