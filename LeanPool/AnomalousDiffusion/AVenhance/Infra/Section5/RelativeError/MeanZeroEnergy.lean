/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ClassicalEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.TimeIBP.Cube

/-!# RelativeError: mean preservation and mean-zero energy control

The mean is conserved by the classical periodic equation.  This supplies the
mean-zero hypothesis for the Fourier Poincare inequality at each time slice.
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

theorem MeanZeroEnergy.classical_solution_time_partial_eq_pde
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {g : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ}
    (hsol : IsClassicalSol b κ (fun _ _ => 0) g u)
    {t : ℝ} (ht : 0 < t) (x : Vec 2) :
    classicalTimePartial u (t, x) =
      κ * spaceLap (u t) x - vecDot (b t x) (spaceGrad (u t) x) := by
  have huOpen : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u)
      classicalPositiveTimeDomain := hsol.1.mono (by
        intro p hp
        simp only [classicalPositiveTimeDomain, Set.mem_prod, Set.mem_Ioi,
          Set.mem_univ] at hp
        exact ⟨le_of_lt hp.1, trivial⟩)
  have htime := classicalTimePartial_eq_deriv huOpen ht x
  have hpde := hsol.2.2.2 t ht x
  change deriv (fun s => u s x) t - κ * spaceLap (u t) x +
    vecDot (b t x) (spaceGrad (u t) x) = 0 at hpde
  rw [← htime] at hpde
  dsimp [classicalTimePartial] at hpde ⊢
  linarith

theorem MeanZeroEnergy.integral_unitCell_laplacian_zero
    {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hper : IsZ2Periodic f) :
    ∫ x in unitCell 2, spaceLap f x = 0 := by
  have hOnePer : IsZ2Periodic (fun _ : Vec 2 => (1 : ℝ)) := by
    intro k x
    rfl
  have hparts := Infra.Classical.integral_unitCell_lap_mul
    (f := fun _ : Vec 2 => (1 : ℝ)) (g := f) contDiff_const hf hOnePer hper
  have hgradOne : spaceGrad (fun _ : Vec 2 => (1 : ℝ)) = 0 := by
    funext x
    funext i
    simp [spaceGrad]
  simpa [hgradOne, vecDot] using hparts

theorem MeanZeroEnergy.integral_unitCell_transport_mean_zero
    {b : Vec 2 → Vec 2} {f : Vec 2 → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbp : ∀ i : Fin 2, IsZ2Periodic (fun x => b x i))
    (hdiv : ∀ x, vecDiv b x = 0)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfp : IsZ2Periodic f) :
    ∫ x in unitCell 2, vecDot (b x) (spaceGrad f x) = 0 := by
  let fPlus : Vec 2 → ℝ := fun x => f x + 1
  have hfPlus : ContDiff ℝ (⊤ : ℕ∞) fPlus := hf.add contDiff_const
  have hfpPlus : IsZ2Periodic fPlus := by
    intro k x
    simp [fPlus, hfp k x]
  have hgradPlus : spaceGrad fPlus = spaceGrad f := by
    funext x
    funext i
    change fderiv ℝ fPlus x (basisVec i) = fderiv ℝ f x (basisVec i)
    change fderiv ℝ (fun y => f y + 1) x (basisVec i) = _
    rw [fderiv_add_const 1]
  have hb1 : ContDiff ℝ 1 b := hb.of_le (by norm_num)
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hfPlus1 : ContDiff ℝ 1 fPlus := hfPlus.of_le (by norm_num)
  have hTPlus := Infra.Classical.integral_unitCell_transport_energy_zero
    b hb1 hbp hdiv fPlus hfPlus1 hfpPlus
  have hT := Infra.Classical.integral_unitCell_transport_energy_zero
    b hb1 hbp hdiv f hf1 hfp
  have hPlusInt : IntegrableOn
      (fun x => vecDot (b x) (spaceGrad fPlus x) * fPlus x) (unitCell 2) := by
    apply Infra.Classical.continuous_integrableOn_unitCell
    change Continuous (fun x =>
      (∑ i : Fin 2, b x i * spaceGrad fPlus x i) * fPlus x)
    have hbComp i : Continuous (fun x => b x i) := (contDiff_pi.1 hb) i |>.continuous
    have hfGradComp i : Continuous (fun x => spaceGrad fPlus x i) := by
      change Continuous (fun x => fderiv ℝ fPlus x (basisVec i))
      exact (hfPlus.continuous_fderiv (by simp)).clm_apply continuous_const
    exact (continuous_finsetSum Finset.univ (fun i hi =>
      (hbComp i).mul (hfGradComp i))).mul hfPlus.continuous
  have hInt : IntegrableOn
      (fun x => vecDot (b x) (spaceGrad f x) * f x) (unitCell 2) := by
    apply Infra.Classical.continuous_integrableOn_unitCell
    change Continuous (fun x =>
      (∑ i : Fin 2, b x i * spaceGrad f x i) * f x)
    have hbComp i : Continuous (fun x => b x i) := (contDiff_pi.1 hb) i |>.continuous
    have hfGradComp i : Continuous (fun x => spaceGrad f x i) := by
      change Continuous (fun x => fderiv ℝ f x (basisVec i))
      exact (hf.continuous_fderiv (by simp)).clm_apply continuous_const
    exact (continuous_finsetSum Finset.univ (fun i hi =>
      (hbComp i).mul (hfGradComp i))).mul hf.continuous
  have hMassInt : IntegrableOn
      (fun x => vecDot (b x) (spaceGrad f x)) (unitCell 2) := by
    apply Infra.Classical.continuous_integrableOn_unitCell
    change Continuous (fun x => ∑ i : Fin 2, b x i * spaceGrad f x i)
    have hbComp i : Continuous (fun x => b x i) := (contDiff_pi.1 hb) i |>.continuous
    have hfGradComp i : Continuous (fun x => spaceGrad f x i) := by
      change Continuous (fun x => fderiv ℝ f x (basisVec i))
      exact (hf.continuous_fderiv (by simp)).clm_apply continuous_const
    exact continuous_finsetSum Finset.univ (fun i hi =>
      (hbComp i).mul (hfGradComp i))
  have hpoint (x : Vec 2) :
      vecDot (b x) (spaceGrad fPlus x) * fPlus x -
        vecDot (b x) (spaceGrad f x) * f x = vecDot (b x) (spaceGrad f x) := by
    rw [hgradPlus]
    simp [fPlus]
    ring
  have hIntEq :
      (∫ x in unitCell 2, vecDot (b x) (spaceGrad fPlus x) * fPlus x) -
        (∫ x in unitCell 2, vecDot (b x) (spaceGrad f x) * f x) =
          ∫ x in unitCell 2, vecDot (b x) (spaceGrad f x) := by
    calc
      _ = ∫ x in unitCell 2,
          (vecDot (b x) (spaceGrad fPlus x) * fPlus x -
            vecDot (b x) (spaceGrad f x) * f x) := by
          rw [MeasureTheory.integral_sub hPlusInt hInt]
      _ = _ := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          exact hpoint x
  calc
    (∫ x in unitCell 2, vecDot (b x) (spaceGrad f x)) =
        (∫ x in unitCell 2,
          vecDot (b x) (spaceGrad fPlus x) * fPlus x) -
        (∫ x in unitCell 2, vecDot (b x) (spaceGrad f x) * f x) := hIntEq.symm
    _ = 0 := by rw [hTPlus, hT]; ring

theorem MeanZeroEnergy.classical_time_partial_continuousOn
    {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u)
      classicalPositiveTimeDomain) :
    ContinuousOn (classicalTimePartial u) classicalPositiveTimeDomain := by
  have hf := hu.continuousOn_fderiv_of_isOpen
    (isOpen_Ioi.prod isOpen_univ) (by simp)
  change ContinuousOn
    (fun p : ℝ × Vec 2 => (fderiv ℝ (Function.uncurry u) p) (1, 0))
    classicalPositiveTimeDomain
  exact hf.clm_apply continuousOn_const

/-- The spatial integral of the time derivative vanishes at every positive
time for a smooth periodic classical solution. -/
theorem classical_solution_mean_derivative_zero
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {g : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ}
    (hb : Infra.Flow.SmoothPeriodicField b)
    (hdiv : ∀ t x, vecDiv (b t) x = 0)
    (hsol : IsClassicalSol b κ (fun _ _ => 0) g u)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x in unitCell 2, u s x) 0 t := by
    have huOpen : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u)
        classicalPositiveTimeDomain := hsol.1.mono (by
          intro p hp
          simp only [classicalPositiveTimeDomain, Set.mem_prod, Set.mem_Ioi,
            Set.mem_univ] at hp
          exact ⟨le_of_lt hp.1, trivial⟩)
    have hbSlice : ContDiff ℝ (⊤ : ℕ∞) (b t) := by
      have hembed : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)) := by fun_prop
      exact hb.smooth.comp hembed
    have hbper (i : Fin 2) : IsZ2Periodic (fun x => b t x i) := by
      intro k x
      simpa using congrArg (fun z : Vec 2 => z i) (hb.periodic 0 k t x)
    have huSlice := classicalSmooth_slice_nonneg hsol.1 (le_of_lt ht)
    have hper := hsol.2.1 t (le_of_lt ht)
    have hpartialPDE := MeanZeroEnergy.classical_solution_time_partial_eq_pde hsol ht
    have hlapZero := MeanZeroEnergy.integral_unitCell_laplacian_zero huSlice hper
    have htransportZero := MeanZeroEnergy.integral_unitCell_transport_mean_zero hbSlice hbper
      (hdiv t) huSlice hper
    have hpartialCont := classicalTimePartial_continuous_slice huOpen ht
    have hlapCont := classical_slice_laplacian_continuous huSlice
    have hgradCont :=
      (classicalSol_spaceGrad_contDiff_of_nonneg hsol (le_of_lt ht)).continuous
    have hpartialInt : IntegrableOn
        (fun x => classicalTimePartial u (t, x)) (unitCell 2) :=
      Infra.Classical.continuous_integrableOn_unitCell hpartialCont
    have hlapInt : IntegrableOn (spaceLap (u t)) (unitCell 2) :=
      Infra.Classical.continuous_integrableOn_unitCell hlapCont
    have htransportInt : IntegrableOn
        (fun x => vecDot (b t x) (spaceGrad (u t) x)) (unitCell 2) := by
      apply Infra.Classical.continuous_integrableOn_unitCell
      change Continuous (fun x => ∑ i : Fin 2, b t x i * spaceGrad (u t) x i)
      have hbComp i : Continuous (fun x => b t x i) :=
        (contDiff_pi.1 hbSlice) i |>.continuous
      have hgradComp i : Continuous (fun x => spaceGrad (u t) x i) :=
        (continuous_apply i).comp hgradCont
      exact continuous_finsetSum Finset.univ (fun i hi =>
        (hbComp i).mul (hgradComp i))
    have hpartialIntZero :
        (∫ x in unitCell 2, classicalTimePartial u (t, x)) = 0 := by
      have hpdeInt :
          (∫ x in unitCell 2, classicalTimePartial u (t, x)) =
            κ * (∫ x in unitCell 2, spaceLap (u t) x) -
              (∫ x in unitCell 2, vecDot (b t x) (spaceGrad (u t) x)) := by
        calc
          _ = ∫ x in unitCell 2,
              (κ * spaceLap (u t) x - vecDot (b t x) (spaceGrad (u t) x)) := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with x
              exact hpartialPDE x
          _ = _ := by
              rw [MeasureTheory.integral_sub (hlapInt.const_mul κ) htransportInt,
                MeasureTheory.integral_const_mul]
      rw [hpdeInt, hlapZero, htransportZero]
      ring
    have hmeanDerivativeCube := LeftToShow.hasDerivAt_integral_unitCube
      huOpen.continuousOn
      (fun s hs x => classicalTimeSection_hasDerivAt huOpen hs x)
      (MeanZeroEnergy.classical_time_partial_continuousOn huOpen) ht
    have hmeanEq : (fun s => ∫ x in unitCell 2, u s x) =
        (fun s => ∫ x in unitCube, u s x) := by
      funext s
      exact Infra.Torus.integral_unitCell_eq_unitCube _
    have hmeanDerivativeCell :
        HasDerivAt (fun s => ∫ x in unitCell 2, u s x)
          (∫ x in unitCell 2, classicalTimePartial u (t, x)) t := by
      rw [hmeanEq]
      convert hmeanDerivativeCube using 1
      exact Infra.Torus.integral_unitCell_eq_unitCube _
    exact hmeanDerivativeCell.congr_deriv hpartialIntZero

/-- The mean of a smooth periodic classical solution is conserved on the
unit time interval. -/
theorem classical_solution_mean_preserved
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {g : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ}
    (hb : Infra.Flow.SmoothPeriodicField b)
    (hdiv : ∀ t x, vecDiv (b t) x = 0)
    (hsol : IsClassicalSol b κ (fun _ _ => 0) g u)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (∫ x in unitCell 2, u t x) = ∫ x in unitCell 2, g x := by
  have hmeanEq : (fun s => ∫ x in unitCell 2, u s x) =
      (fun s => ∫ x in unitCube, u s x) := by
    funext s
    exact Infra.Torus.integral_unitCell_eq_unitCube _
  have huContinuous :
      ContinuousOn (fun p : ℝ × Vec 2 => u p.1 p.2)
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) :=
    hsol.1.continuousOn.mono (by
      rintro ⟨s, x⟩ ⟨hs, hx⟩
      exact ⟨hs.1, trivial⟩)
  have hmeanContinuousCube :
      ContinuousOn (fun s => ∫ x in unitCube, u s x) (Set.Icc (0 : ℝ) 1) :=
    LeftToShow.continuousOn_integral_unitCube huContinuous
  have hmeanContinuous :
      ContinuousOn (fun s => ∫ x in unitCell 2, u s x) (Set.Icc (0 : ℝ) 1) := by
    rw [hmeanEq]
    exact hmeanContinuousCube
  by_cases hzero : t = 0
  · subst t
    apply setIntegral_congr_fun (Infra.Torus.measurableSet_unitCell 2)
    intro x hx
    rw [hsol.2.2.1 x]
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm hzero)
    have hcontT : ContinuousOn (fun s => ∫ x in unitCell 2, u s x)
        (Set.Icc (0 : ℝ) t) := hmeanContinuous.mono (by
      intro s hs
      exact ⟨hs.1, le_trans hs.2 ht.2⟩)
    have hderiv : ∀ s ∈ Set.Ioo (0 : ℝ) t,
        HasDerivAt (fun r => ∫ x in unitCell 2, u r x) 0 s := by
      intro s hs
      exact classical_solution_mean_derivative_zero hb hdiv hsol hs.1
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      htpos.le hcontT hderiv intervalIntegrable_const
    have hmean0 : (∫ x in unitCell 2, u 0 x) = ∫ x in unitCell 2, g x := by
      apply setIntegral_congr_fun (Infra.Torus.measurableSet_unitCell 2)
      intro x hx
      rw [hsol.2.2.1 x]
    have hmeanDiff :
        (∫ x in unitCell 2, u t x) - (∫ x in unitCell 2, u 0 x) = 0 := by
      simpa using hFTC.symm
    linarith

end AVenhance.Infra.Section5.RelativeError

end
