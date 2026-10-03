/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.ClassicalEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftToShow.TimeIBP.Cube

/-! # RelativeError: pairing a classical solution with a transported test

The scalar test is supplied with smoothness, periodicity, and its transport
equation. This file proves the parabolic/transport pairing identity; the flow
construction of the specific Piola test remains a separate bridge.
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

/-- Smooth periodic solutions of the homogeneous scalar transport equation. -/
structure IsClassicalTransportTest
    (b : ℝ → Vec 2 → Vec 2) (h : ℝ → Vec 2 → ℝ) : Prop where
  smooth : ContDiff ℝ 2 (Function.uncurry h)
  periodic : ∀ t : ℝ, 0 ≤ t → IsZ2Periodic (h t)
  equation : ∀ t : ℝ, 0 < t → ∀ x : Vec 2,
    classicalTimePartial h (t, x) +
      vecDot (b t x) (spaceGrad (h t) x) = 0

theorem TransportPairing.classicalTimePartial_continuousOn_of_smooth
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

theorem TransportPairing.classicalTimePartial_continuousOn_of_C2
    {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ 2 (Function.uncurry u)
      classicalPositiveTimeDomain) :
    ContinuousOn (classicalTimePartial u) classicalPositiveTimeDomain := by
  have hu1 := hu.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)
  have hf := hu1.continuousOn_fderiv_of_isOpen
    (isOpen_Ioi.prod isOpen_univ) (by simp)
  change ContinuousOn
    (fun p : ℝ × Vec 2 => (fderiv ℝ (Function.uncurry u) p) (1, 0))
    classicalPositiveTimeDomain
  exact hf.clm_apply continuousOn_const

theorem classicalTimeSection_hasDerivAt_of_C2
    {u : ℝ → Vec 2 → ℝ}
    (hu : ContDiffOn ℝ 2 (Function.uncurry u)
      classicalPositiveTimeDomain)
    {t : ℝ} (ht : 0 < t) (x : Vec 2) :
    HasDerivAt (fun s => u s x) (classicalTimePartial u (t, x)) t := by
  have hp : (t, x) ∈ classicalPositiveTimeDomain := by
    simp [classicalPositiveTimeDomain, ht]
  have hAt := hu.contDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds hp)
  have hF : HasFDerivAt (Function.uncurry u)
      (fderiv ℝ (Function.uncurry u) (t, x)) (t, x) :=
    (hAt.differentiableAt (by norm_num)).hasFDerivAt
  have hline : HasDerivAt (fun s : ℝ => (s, x)) (1, 0) t := by
    convert (hasDerivAt_id t).prodMk (hasDerivAt_const t x) using 1
    simp
  have hcomp := hF.comp_hasDerivAt t hline
  change HasDerivAt (fun s => u s x)
    ((fderiv ℝ (Function.uncurry u) (t, x)) (1, 0)) t
  exact hcomp

theorem TransportPairing.classical_solution_time_partial_eq_pde
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
  dsimp [classicalTimePartial] at htime hpde ⊢
  linarith

/-- Divergence-free transport has zero mean on every smooth periodic scalar. -/
theorem TransportPairing.integral_unitCell_transport_linear_zero
    {b : Vec 2 → Vec 2} {f : Vec 2 → ℝ}
    (hb : ContDiff ℝ 1 b)
    (hbp : ∀ i : Fin 2, IsZ2Periodic (fun x => b x i))
    (hdiv : ∀ x, vecDiv b x = 0)
    (hf : ContDiff ℝ 1 f) (hfp : IsZ2Periodic f) :
    (∫ x in unitCell 2, vecDot (b x) (spaceGrad f x)) = 0 := by
  have hparts (i : Fin 2) :
      (∫ x in unitCell 2, b x i * spaceGrad f x i) =
        -∫ x in unitCell 2, spaceGrad (fun y => b y i) x i * f x := by
    exact integral_unitCell_coord_ibp_real i
      ((contDiff_pi.1 hb) i) hf (hbp i) hfp
  have hbComp (i : Fin 2) : Continuous (fun x => b x i) :=
    ((contDiff_pi.1 hb) i).continuous
  have hgradBCont (i : Fin 2) : Continuous
      (fun x => spaceGrad (fun y => b y i) x i) := by
    change Continuous (fun x =>
      fderiv ℝ (fun y => b y i) x (basisVec i))
    exact (contDiff_pi.1 hb i).continuous_fderiv
      (by simp) |>.clm_apply continuous_const
  have htermInt (i : Fin 2) :
      IntegrableOn (fun x => b x i * spaceGrad f x i) (unitCell 2) := by
    have hgradF : Continuous (fun x => spaceGrad f x i) := by
      change Continuous (fun x => fderiv ℝ f x (basisVec i))
      exact hf.continuous_fderiv (by simp) |>.clm_apply continuous_const
    exact continuous_integrableOn_unitCell ((hbComp i).mul hgradF)
  have hdivTermInt (i : Fin 2) : IntegrableOn
      (fun x => spaceGrad (fun y => b y i) x i * f x) (unitCell 2) := by
    exact continuous_integrableOn_unitCell ((hgradBCont i).mul hf.continuous)
  have hsum :
      (∫ x in unitCell 2, vecDot (b x) (spaceGrad f x)) =
        ∑ i : Fin 2, ∫ x in unitCell 2, b x i * spaceGrad f x i := by
    unfold vecDot
    rw [MeasureTheory.integral_finsetSum]
    intro i hi
    exact htermInt i
  rw [hsum]
  calc
    (∑ i : Fin 2, ∫ x in unitCell 2, b x i * spaceGrad f x i) =
        -∑ i : Fin 2, ∫ x in unitCell 2,
          spaceGrad (fun y => b y i) x i * f x := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            exact hparts i
    _ = -∫ x in unitCell 2, vecDiv b x * f x := by
      rw [← MeasureTheory.integral_finsetSum (Finset.univ)
        (μ := (volume : Measure (Vec 2)).restrict (unitCell 2))
        (f := fun i x => spaceGrad (fun y => b y i) x i * f x)
        (by intro i hi; exact hdivTermInt i)]
      congr 1
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      simp only [vecDiv]
      rw [← Finset.sum_mul]
    _ = 0 := by
      simp [hdiv]

theorem TransportPairing.integral_unitCell_lap_mul_C2 {f g : Vec 2 → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 2 g)
    (hpf : IsZ2Periodic f) (hpg : IsZ2Periodic g) :
    (∫ x in unitCell 2, f x * spaceLap g x) =
      -∫ x in unitCell 2, vecDot (spaceGrad f x) (spaceGrad g x) := by
  have hgrad (i : Fin 2) : ContDiff ℝ 1
      (fun x => spaceGrad g x i) := by
    change ContDiff ℝ 1 (fun x => fderiv ℝ g x (basisVec i))
    have hderiv : ContDiff ℝ 1 (fun x => fderiv ℝ g x) :=
      hg.fderiv_right (by norm_num)
    exact hderiv.clm_apply contDiff_const
  have hgradPer (i : Fin 2) :
      IsZ2Periodic (fun x => spaceGrad g x i) :=
    Infra.Classical.periodic_spaceGrad_component hpg i
  have htermInt (i : Fin 2) : IntegrableOn
      (fun x => f x * spaceGrad
        (fun y => spaceGrad g y i) x i) (unitCell 2) := by
    have hsecond : Continuous
        (fun x => spaceGrad (fun y => spaceGrad g y i) x i) := by
      change Continuous (fun x => fderiv ℝ
        (fun y => spaceGrad g y i) x (basisVec i))
      exact (hgrad i).continuous_fderiv (by simp) |>.clm_apply continuous_const
    exact continuous_integrableOn_unitCell (hf.continuous.mul hsecond)
  have hparts (i : Fin 2) :
      (∫ x in unitCell 2, f x * spaceGrad
        (fun y => spaceGrad g y i) x i) =
      -∫ x in unitCell 2, spaceGrad f x i * spaceGrad g x i :=
    integral_unitCell_coord_ibp_real i hf (hgrad i) hpf (hgradPer i)
  have hgradProductInt (i : Fin 2) : IntegrableOn
      (fun x => spaceGrad f x i * spaceGrad g x i) (unitCell 2) := by
    have hDf : Continuous (fun x => spaceGrad f x i) := by
      change Continuous (fun x => fderiv ℝ f x (basisVec i))
      exact hf.continuous_fderiv (by simp) |>.clm_apply continuous_const
    exact continuous_integrableOn_unitCell (hDf.mul (hgrad i).continuous)
  have hsumLap :
      (∫ x in unitCell 2, f x * spaceLap g x) =
        ∑ i : Fin 2, ∫ x in unitCell 2, f x * spaceGrad
          (fun y => spaceGrad g y i) x i := by
    calc
      _ = ∫ x in unitCell 2, ∑ i : Fin 2, f x * spaceGrad
          (fun y => spaceGrad g y i) x i := by
        apply setIntegral_congr_fun (Infra.Torus.measurableSet_unitCell 2)
        intro x hx
        simp [spaceLap, Fin.sum_univ_two]
        ring
      _ = _ := MeasureTheory.integral_finsetSum Finset.univ
        (μ := (volume : Measure (Vec 2)).restrict (unitCell 2))
        (f := fun i x => f x * spaceGrad
          (fun y => spaceGrad g y i) x i)
        (by intro i hi; exact htermInt i)
  have hsumGrad :
      (∫ x in unitCell 2, vecDot (spaceGrad f x) (spaceGrad g x)) =
        ∑ i : Fin 2, ∫ x in unitCell 2,
          spaceGrad f x i * spaceGrad g x i := by
    unfold vecDot
    exact MeasureTheory.integral_finsetSum Finset.univ
      (μ := (volume : Measure (Vec 2)).restrict (unitCell 2))
      (f := fun i x => spaceGrad f x i * spaceGrad g x i)
      (by intro i hi; exact hgradProductInt i)
  calc
    (∫ x in unitCell 2, f x * spaceLap g x) =
        -∑ i : Fin 2, ∫ x in unitCell 2,
          spaceGrad f x i * spaceGrad g x i := by
      rw [hsumLap]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      exact hparts i
    _ = -∫ x in unitCell 2,
        vecDot (spaceGrad f x) (spaceGrad g x) := by rw [hsumGrad]

/-- A classical parabolic solution paired with any smooth inverse-transport
test has derivative equal to minus the diffusivity times the gradient
pairing. -/
theorem classical_solution_transportPairing_derivative
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {g : Vec 2 → ℝ}
    {u h : ℝ → Vec 2 → ℝ}
    (hb : Infra.Flow.SmoothPeriodicField b)
    (hdiv : ∀ t x, vecDiv (b t) x = 0)
    (hsol : IsClassicalSol b κ (fun _ _ => 0) g u)
    (htest : IsClassicalTransportTest b h)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun s => ∫ x in unitCell 2, u s x * h s x)
      (-κ * (∫ x in unitCell 2,
        vecDot (spaceGrad (u t) x) (spaceGrad (h t) x))) t := by
  have huOpen : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry u)
      classicalPositiveTimeDomain := hsol.1.mono (by
        intro p hp
        simp only [classicalPositiveTimeDomain, Set.mem_prod, Set.mem_Ioi,
          Set.mem_univ] at hp
        exact ⟨le_of_lt hp.1, trivial⟩)
  have hhOpen : ContDiffOn ℝ 2 (Function.uncurry h)
      classicalPositiveTimeDomain :=
    htest.smooth.contDiffOn.mono (Set.subset_univ _)
  let p : ℝ → Vec 2 → ℝ := fun s x => u s x * h s x
  let p' : ℝ → Vec 2 → ℝ := fun s x =>
    classicalTimePartial u (s, x) * h s x +
      u s x * classicalTimePartial h (s, x)
  have hpCont : ContinuousOn (Function.uncurry p) classicalPositiveTimeDomain := by
    change ContinuousOn
      (fun q : ℝ × Vec 2 => u q.1 q.2 * h q.1 q.2)
      classicalPositiveTimeDomain
    exact huOpen.continuousOn.mul hhOpen.continuousOn
  have huTimeCont := TransportPairing.classicalTimePartial_continuousOn_of_smooth huOpen
  have hhTimeCont := TransportPairing.classicalTimePartial_continuousOn_of_C2 hhOpen
  have hp'Cont : ContinuousOn (Function.uncurry p') classicalPositiveTimeDomain := by
    change ContinuousOn
      (fun q : ℝ × Vec 2 =>
        classicalTimePartial u q * h q.1 q.2 +
          u q.1 q.2 * classicalTimePartial h q)
      classicalPositiveTimeDomain
    exact (huTimeCont.mul hhOpen.continuousOn).add
      (huOpen.continuousOn.mul hhTimeCont)
  have hpDeriv (s : ℝ) (hs : 0 < s) (x : Vec 2) :
      HasDerivAt (fun r => p r x) (p' s x) s := by
    have huD := classicalTimeSection_hasDerivAt huOpen hs x
    have hhD := classicalTimeSection_hasDerivAt_of_C2 hhOpen hs x
    change HasDerivAt
      ((fun r => u r x) * (fun r => h r x)) (p' s x) s
    simpa [p'] using huD.mul hhD
  have hderivCube := LeftToShow.hasDerivAt_integral_unitCube
    hpCont (fun s hs x => hpDeriv s hs x) hp'Cont ht
  have hcellCube : (fun s => ∫ x in unitCell 2, p s x) =
      fun s => ∫ x in unitCube, p s x := by
    funext s
    exact Torus.integral_unitCell_eq_unitCube _
  have hpairDeriv : HasDerivAt
      (fun s => ∫ x in unitCell 2, p s x)
      (∫ x in unitCell 2, p' t x) t := by
    rw [hcellCube]
    convert hderivCube using 1
    exact Torus.integral_unitCell_eq_unitCube _
  have huSlice : ContDiff ℝ (⊤ : ℕ∞) (u t) :=
    classicalSmooth_slice_nonneg hsol.1 (le_of_lt ht)
  have hhSlice : ContDiff ℝ 2 (h t) := by
    have hembed : ContDiff ℝ 2 (fun x : Vec 2 => (t, x)) := by fun_prop
    change ContDiff ℝ 2 (Function.uncurry h ∘ fun x : Vec 2 => (t, x))
    exact htest.smooth.comp hembed
  have huPer := hsol.2.1 t (le_of_lt ht)
  have hhPer := htest.periodic t (le_of_lt ht)
  have hprodSmooth : ContDiff ℝ 2 (fun x => u t x * h t x) :=
    (huSlice.of_le (by simp)).mul hhSlice
  have hprodPer : IsZ2Periodic (fun x => u t x * h t x) := by
    intro k x
    simp [huPer k x, hhPer k x]
  have hbSlice : ContDiff ℝ (⊤ : ℕ∞) (b t) := by
    have hembed : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)) := by fun_prop
    exact hb.smooth.comp hembed
  have hbPer (i : Fin 2) : IsZ2Periodic (fun x => b t x i) := by
    intro k x
    simpa using congrArg (fun z : Vec 2 => z i) (hb.periodic 0 k t x)
  have hdivt : ∀ x, vecDiv (b t) x = 0 := hdiv t
  have hpde := TransportPairing.classical_solution_time_partial_eq_pde hsol ht
  have hhPde (x : Vec 2) :
      classicalTimePartial h (t, x) =
        -vecDot (b t x) (spaceGrad (h t) x) := by
    linarith [htest.equation t ht x]
  have hprodGrad (x : Vec 2) (i : Fin 2) :
      spaceGrad (fun y => u t y * h t y) x i =
        spaceGrad (u t) x i * h t x + u t x * spaceGrad (h t) x i := by
    change fderiv ℝ (fun y => u t y * h t y) x (basisVec i) = _
    rw [fderiv_fun_mul
      ((huSlice.contDiffAt).differentiableAt (by simp))
      ((hhSlice.contDiffAt).differentiableAt (by simp))]
    simp only [add_apply, smul_apply, smul_eq_mul, spaceGrad]
    ring
  have hprodGradCont : Continuous
      (spaceGrad (fun y => u t y * h t y)) := by
    exact continuous_pi (fun i => by
      change Continuous (fun x => fderiv ℝ
        (fun y => u t y * h t y) x (basisVec i))
      exact (hprodSmooth.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  have htransportCont : Continuous
      (fun x => vecDot (b t x)
        (spaceGrad (fun y => u t y * h t y) x)) := by
    change Continuous (fun x => ∑ i : Fin 2,
      b t x i * spaceGrad (fun y => u t y * h t y) x i)
    exact continuous_finsetSum Finset.univ (fun i hi =>
      ((contDiff_pi.1 hbSlice) i).continuous.mul
        ((continuous_apply i).comp hprodGradCont))
  have htransportInt : IntegrableOn
      (fun x => vecDot (b t x)
        (spaceGrad (fun y => u t y * h t y) x)) (unitCell 2) :=
    continuous_integrableOn_unitCell htransportCont
  have hlapCont := classical_slice_laplacian_continuous huSlice
  have hlapProductInt : IntegrableOn
      (fun x => h t x * spaceLap (u t) x) (unitCell 2) :=
    continuous_integrableOn_unitCell (hhSlice.continuous.mul hlapCont)
  have hp'Slice : Continuous (fun x => p' t x) := by
    have hline : Continuous fun x : Vec 2 => (t, x) :=
      continuous_const.prodMk continuous_id
    exact hp'Cont.comp_continuous hline (fun x => ⟨ht, trivial⟩)
  have hp'Int : IntegrableOn (fun x => p' t x) (unitCell 2) :=
    continuous_integrableOn_unitCell hp'Slice
  have htransportZero := TransportPairing.integral_unitCell_transport_linear_zero
    (hbSlice.of_le (by norm_num)) hbPer hdivt
    (hprodSmooth.of_le (by norm_num)) hprodPer
  have hlapPair := TransportPairing.integral_unitCell_lap_mul_C2
    (f := h t) (g := u t) (hhSlice.of_le (by norm_num))
    (huSlice.of_le (by norm_num)) hhPer huPer
  have hlapPair' :
      (∫ x in unitCell 2, h t x * spaceLap (u t) x) =
        -∫ x in unitCell 2,
          vecDot (spaceGrad (u t) x) (spaceGrad (h t) x) := by
    calc
      _ = -∫ x in unitCell 2,
          vecDot (spaceGrad (h t) x) (spaceGrad (u t) x) := hlapPair
      _ = _ := by
        congr 1
        apply setIntegral_congr_fun (Infra.Torus.measurableSet_unitCell 2)
        intro x hx
        simp [Homogenization.vecDot, mul_comm]
  have htransportPoint (x : Vec 2) :
      vecDot (b t x) (spaceGrad (fun y => u t y * h t y) x) =
        vecDot (b t x) (spaceGrad (u t) x) * h t x +
          u t x * vecDot (b t x) (spaceGrad (h t) x) := by
    simp [Homogenization.vecDot, hprodGrad, Fin.sum_univ_two]
    ring
  have hpoint (x : Vec 2) :
      p' t x = κ * (h t x * spaceLap (u t) x) -
        vecDot (b t x) (spaceGrad (fun y => u t y * h t y) x) := by
    change classicalTimePartial u (t, x) * h t x +
      u t x * classicalTimePartial h (t, x) = _
    rw [TransportPairing.classical_solution_time_partial_eq_pde hsol ht x, hhPde x]
    rw [htransportPoint x]
    ring
  have hintegral :
      (∫ x in unitCell 2, p' t x) =
        κ * (∫ x in unitCell 2, h t x * spaceLap (u t) x) -
          ∫ x in unitCell 2,
            vecDot (b t x) (spaceGrad (fun y => u t y * h t y) x) := by
    calc
      _ = ∫ x in unitCell 2,
          (κ * (h t x * spaceLap (u t) x) -
          vecDot (b t x) (spaceGrad (fun y => u t y * h t y) x)) := by
          apply setIntegral_congr_fun (Infra.Torus.measurableSet_unitCell 2)
          intro x hx
          exact hpoint x
      _ = _ := by
        rw [MeasureTheory.integral_sub (hlapProductInt.const_mul κ) htransportInt,
          MeasureTheory.integral_const_mul]
  have hformula :
      (∫ x in unitCell 2, p' t x) =
        -κ * (∫ x in unitCell 2,
          vecDot (spaceGrad (u t) x) (spaceGrad (h t) x)) := by
    rw [hintegral, htransportZero, hlapPair']
    ring
  convert hpairDeriv using 1
  exact hformula.symm

end AVenhance.Infra.Section5.RelativeError

end
