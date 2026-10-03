/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaTimeEnergy
public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.MeasureTheory.Measure.OpenPos

/-! L² energy uniqueness for smooth periodic advection-diffusion solutions. -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open Homogenization
open AVenhance.Infra.Torus
open scoped Topology

namespace AVenhance.Infra.Section4

theorem ThetaClassicalUniqueness.continuous_spaceGrad_component {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 2) :
    Continuous (fun x => AVenhance.spaceGrad f x i) := by
  change Continuous (fun x => fderiv ℝ f x (Homogenization.basisVec i))
  exact (hf.continuous_fderiv (by simp)).clm_apply continuous_const

theorem ThetaClassicalUniqueness.continuous_spaceLap {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Continuous (AVenhance.spaceLap f) := by
  unfold AVenhance.spaceLap
  apply continuous_finsetSum
  intro i hi
  have hgrad : ContDiff ℝ (⊤ : ℕ∞) (fun x => AVenhance.spaceGrad f x i) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ f x (Homogenization.basisVec i))
    exact (hf.fderiv_right (by simp)).clm_apply contDiff_const
  exact ThetaClassicalUniqueness.continuous_spaceGrad_component hgrad i

theorem ThetaClassicalUniqueness.continuous_vecDot {f g : Vec 2 → Vec 2}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => Homogenization.vecDot (f x) (g x)) := by
  change Continuous (fun x => ∑ i : Fin 2, f x i * g x i)
  apply continuous_finsetSum
  intro i hi
  exact ((continuous_apply i).comp hf).mul ((continuous_apply i).comp hg)

theorem ThetaClassicalUniqueness.theta_smooth_spaceGrad_sub {f g : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    AVenhance.spaceGrad (fun x => f x - g x) =
      fun x => AVenhance.spaceGrad f x - AVenhance.spaceGrad g x := by
  funext x i
  change fderiv ℝ (fun y => f y - g y) x (Homogenization.basisVec i) = _
  rw [fderiv_fun_sub (hf.differentiable (by simp) x)
    (hg.differentiable (by simp) x)]
  simp [AVenhance.spaceGrad]

theorem ThetaClassicalUniqueness.thetaSpaceGrad_contDiff {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (AVenhance.spaceGrad f) := by
  apply contDiff_pi.2
  intro i
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x => fderiv ℝ f x (Homogenization.basisVec i))
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem ThetaClassicalUniqueness.theta_smooth_spaceLap_sub {f g : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    AVenhance.spaceLap (fun x => f x - g x) =
      fun x => AVenhance.spaceLap f x - AVenhance.spaceLap g x := by
  funext x
  simp only [AVenhance.spaceLap]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hfi : ContDiff ℝ (⊤ : ℕ∞) (fun y => AVenhance.spaceGrad f y i) := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun y => fderiv ℝ f y (Homogenization.basisVec i))
    exact (hf.fderiv_right (by simp)).clm_apply contDiff_const
  have hgi : ContDiff ℝ (⊤ : ℕ∞) (fun y => AVenhance.spaceGrad g y i) := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun y => fderiv ℝ g y (Homogenization.basisVec i))
    exact (hg.fderiv_right (by simp)).clm_apply contDiff_const
  have hinner : (fun y => AVenhance.spaceGrad (fun z => f z - g z) y i) =
      (fun y => AVenhance.spaceGrad f y i - AVenhance.spaceGrad g y i) := by
    funext y
    exact congrFun (congrFun (ThetaClassicalUniqueness.theta_smooth_spaceGrad_sub hf hg) y) i
  rw [hinner]
  change fderiv ℝ
      (fun y => AVenhance.spaceGrad f y i - AVenhance.spaceGrad g y i)
      x (Homogenization.basisVec i) = _
  rw [fderiv_fun_sub (hfi.differentiable (by simp) x)
    (hgi.differentiable (by simp) x)]
  simp [AVenhance.spaceGrad]

theorem ThetaClassicalUniqueness.thetaTime_continuous_integrableOn_unitCellAt
    {f : Vec 2 → ℝ} (a : Vec 2) (hf : Continuous f) :
    IntegrableOn f (AVenhance.Infra.Torus.unitCellAt 2 a) := by
  let closedCell : Set (Vec 2) := Set.pi Set.univ
    (fun i => Set.Icc (a i) (a i + 1))
  have hclosed : IsCompact closedCell := by
    simpa [closedCell] using isCompact_univ_pi
      (fun i : Fin 2 => isCompact_Icc)
  have hsub : AVenhance.Infra.Torus.unitCellAt 2 a ⊆ closedCell := by
    intro x hx
    simp only [AVenhance.Infra.Torus.unitCellAt, Set.mem_ofPred_eq] at hx
    simp only [closedCell, Set.mem_pi, Set.mem_univ, forall_true_left]
    intro i
    exact ⟨le_of_lt (hx i).1, hx i |>.2⟩
  exact (hf.continuousOn.integrableOn_compact hclosed).mono_set hsub

private theorem streamVel_classical_unique_energyRate1 :
  ∀ (φ : ℝ → Vec (2 : ℕ) → ℝ), IsAdmissibleStream φ → ∀ (κ : ℝ) (F : ℝ → Vec (2 : ℕ) → ℝ) (θ₀ :
    Vec (2 : ℕ) → ℝ) {θ ψ : ℝ → Vec (2 : ℕ) → ℝ}, IsClassicalSol (streamVel φ) κ F θ₀ θ →
    IsClassicalSol (streamVel φ) κ F θ₀ ψ →
  let w : ℝ → Vec (2 : ℕ) → ℝ := fun (t : ℝ) (x : Vec (2 : ℕ)) => ψ t x - θ t x;
  ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry w) (Ici (0 : ℝ) ×ˢ univ) → ContDiffOn
    ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry w) classicalPositiveTimeDomain → (∀ (t : ℝ), (0
    : ℝ) ≤ t → IsZ2Periodic (w t)) → (∀ (t : ℝ), (0 : ℝ) < t → ∀ (x : Vec (2 : ℕ)),
    classicalTimePartial w (t, x) - κ * spaceLap (w t) x + vecDot (streamVel φ t x) (spaceGrad
    (w t) x) = (0 : ℝ)) → ∀ (t : ℝ), (0 : ℝ) < t → deriv (fun (s : ℝ) => ∫ (x : Vec (2 : ℕ)) in
    unitCube, w s x ^ (2 : ℕ)) t = -((2 : ℝ) * κ) * ∫ (x : Vec (2 : ℕ)) in unitCube, vecDot
    (spaceGrad (w t) x) (spaceGrad (w t) x)
    := by
  intro φ hφ κ F θ₀ θ ψ hθ hψ w hw hwOpen hwper hPDE t ht
  let dt : Vec 2 → ℝ := fun x => classicalTimePartial w (t, x)
  let lap : Vec 2 → ℝ := fun x => AVenhance.spaceLap (w t) x
  let drift : Vec 2 → ℝ := fun x =>
    Homogenization.vecDot (AVenhance.streamVel φ t x) (AVenhance.spaceGrad (w t) x)
  let a : Vec 2 → ℝ := fun x => 2 * w t x * dt x
  let l : Vec 2 → ℝ := fun x => w t x * lap x
  let q : Vec 2 → ℝ := fun x => drift x * w t x
  have hwSlice := classicalSmooth_slice_nonneg hθ.1 (le_of_lt ht)
  have hψSlice := classicalSmooth_slice_nonneg hψ.1 (le_of_lt ht)
  have hwDiffSlice : ContDiff ℝ (⊤ : ℕ∞) (w t) := by
    simpa [w] using hψSlice.sub hwSlice
  have hwC : Continuous (w t) := hwDiffSlice.continuous
  have hdtC := classicalTimePartial_continuous_slice hwOpen ht
  have hdtCont : Continuous dt := by simpa [dt] using hdtC
  have hlapCont : Continuous lap := by
    simpa [lap] using ThetaClassicalUniqueness.continuous_spaceLap hwDiffSlice
  have hφSliceForVel : ContDiff ℝ (⊤ : ℕ∞) (φ t) := by
    have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)) := by
      fun_prop
    have hcomp := hφ.1.comp hmap
    simpa [Function.uncurry, Function.comp_def] using hcomp
  have hbForm : AVenhance.streamVel φ t = fun x =>
      ![-AVenhance.spaceGrad (φ t) x 1,
        AVenhance.spaceGrad (φ t) x 0] := by
    funext x i
    fin_cases i <;> simp [AVenhance.streamVel, AVenhance.sigmaMat,
      Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two]
  have hbSliceTop : ContDiff ℝ (⊤ : ℕ∞) (AVenhance.streamVel φ t) := by
    rw [hbForm]
    apply contDiff_pi.2
    intro i
    fin_cases i
    · exact (contDiff_pi.mp
        (ThetaClassicalUniqueness.thetaSpaceGrad_contDiff hφSliceForVel) 1).neg
    · exact contDiff_pi.mp (ThetaClassicalUniqueness.thetaSpaceGrad_contDiff hφSliceForVel) 0
  have hbSlice : ContDiff ℝ 1 (AVenhance.streamVel φ t) :=
    hbSliceTop.of_le (by simp)
  have hbC : Continuous (AVenhance.streamVel φ t) := hbSlice.continuous
  have hgradC : Continuous (AVenhance.spaceGrad (w t)) := by
    apply continuous_pi
    intro i
    exact ThetaClassicalUniqueness.continuous_spaceGrad_component hwDiffSlice i
  have hdriftC : Continuous drift := by
    simpa [drift] using ThetaClassicalUniqueness.continuous_vecDot hbC hgradC
  have haInt : IntegrableOn a (AVenhance.unitCube) := by
    apply thetaTime_integrableOn_unitCube
    change Continuous (fun x => 2 * w t x * classicalTimePartial w (t, x))
    exact (continuous_const.mul hwC).mul hdtCont
  have hlInt : IntegrableOn l (AVenhance.unitCube) := by
    apply thetaTime_integrableOn_unitCube
    change Continuous (fun x => w t x * AVenhance.spaceLap (w t) x)
    exact hwC.mul hlapCont
  have hqInt : IntegrableOn q (AVenhance.unitCube) := by
    apply thetaTime_integrableOn_unitCube
    change Continuous (fun x =>
      Homogenization.vecDot (AVenhance.streamVel φ t x)
        (AVenhance.spaceGrad (w t) x) * w t x)
    exact hdriftC.mul hwC
  have hpoint (x : Vec 2) : a x - (2 * κ) * l x + 2 * q x = 0 := by
    have hp := hPDE t ht x
    dsimp [a, l, q, dt, lap, drift]
    calc
      2 * w t x * classicalTimePartial w (t, x) -
          (2 * κ) * (w t x * AVenhance.spaceLap (w t) x) +
          2 * (Homogenization.vecDot (AVenhance.streamVel φ t x)
            (AVenhance.spaceGrad (w t) x) * w t x) =
          2 * w t x * (classicalTimePartial w (t, x) -
            κ * AVenhance.spaceLap (w t) x +
            Homogenization.vecDot (AVenhance.streamVel φ t x)
              (AVenhance.spaceGrad (w t) x)) := by ring
      _ = 0 := by rw [hp]; ring
  have hsumInt : IntegrableOn (fun x => a x - (2 * κ) * l x + 2 * q x)
      (AVenhance.unitCube) := (haInt.sub (hlInt.const_mul (2 * κ))).add (hqInt.const_mul 2)
  have hsumZero : ∫ x in AVenhance.unitCube, (a x - (2 * κ) * l x + 2 * q x) = 0 := by
    calc
      ∫ x in AVenhance.unitCube, (a x - (2 * κ) * l x + 2 * q x) = ∫ _ : Vec 2 in
          AVenhance.unitCube, (0 : ℝ) := by
        apply integral_congr_ae
        filter_upwards with x
        exact hpoint x
      _ = 0 := by simp
  have hsumZero' :
      (∫ x in AVenhance.unitCube, a x) - (2 * κ) * (∫ x in AVenhance.unitCube, l x) +
        2 * (∫ x in AVenhance.unitCube, q x) = 0 := by
    have hsplit :
        (∫ x in AVenhance.unitCube, (a x - (2 * κ) * l x + 2 * q x)) =
          (∫ x in AVenhance.unitCube, a x) - (2 * κ) * (∫ x in AVenhance.unitCube, l x) +
            2 * (∫ x in AVenhance.unitCube, q x) := by
      calc
        _ = ∫ x in AVenhance.unitCube,
            ((fun y => a y - (2 * κ) * l y) x + (fun y => 2 * q y) x) := rfl
        _ = (∫ x in AVenhance.unitCube, (fun y => a y - (2 * κ) * l y) x) +
              ∫ x in AVenhance.unitCube, (fun y => 2 * q y) x :=
          integral_add (haInt.sub (hlInt.const_mul (2 * κ))) (hqInt.const_mul 2)
        _ = _ := by
          rw [integral_sub haInt (hlInt.const_mul (2 * κ))]
          rw [integral_const_mul, integral_const_mul]
    rw [← hsplit]
    exact hsumZero
  have hwDiffSlice1 : ContDiff ℝ 1 (w t) := hwDiffSlice.of_le (by norm_num)
  have hφper : AVenhance.IsZ2Periodic (φ t) := by
    intro k x
    simpa using hφ.2 0 k t x
  have htransport := theta_stream_drift_pairing_zero hφSliceForVel hφper
    hwDiffSlice (hwper t (le_of_lt ht))
  have htransport' : ∫ x in AVenhance.unitCube,
      Homogenization.vecDot (AVenhance.streamVel φ t x)
        (AVenhance.spaceGrad (w t) x) * w t x = 0 := by
    calc
      _ = ∫ x in AVenhance.unitCube,
          w t x * Homogenization.vecDot (AVenhance.streamVel φ t x)
            (AVenhance.spaceGrad (w t) x) := by
        apply integral_congr_ae
        filter_upwards with x
        ring
      _ = 0 := by simpa [AVenhance.streamVel] using htransport
  have hlapEnergy := theta_laplacian_pairing hwDiffSlice
    (hwper t (le_of_lt ht))
  have henergyDeriv := theta_energy_hasDerivAt hw ht
  have hderiv := henergyDeriv.deriv
  rw [htransport', hlapEnergy] at hsumZero'
  have hrate :
      deriv (fun s => ∫ x in AVenhance.unitCube, (w s x) ^ 2) t =
        ∫ x in AVenhance.unitCube, 2 * w t x * classicalTimePartial w (t, x) := by
    simpa [dt] using hderiv
  rw [hrate]
  have hnorm : (fun x => Homogenization.vecNormSq
      (AVenhance.spaceGrad (w t) x)) =
      fun x => Homogenization.vecDot (AVenhance.spaceGrad (w t) x)
        (AVenhance.spaceGrad (w t) x) := by
    funext x
    simp [Homogenization.vecNormSq]
  rw [hnorm] at hsumZero'
  dsimp [a, dt] at hsumZero'
  linarith

theorem streamVel_classical_unique
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ) (θ₀ : Vec 2 → ℝ)
    {θ ψ : ℝ → Vec 2 → ℝ}
    (hθ : AVenhance.IsClassicalSol (AVenhance.streamVel φ) κ F θ₀ θ)
    (hψ : AVenhance.IsClassicalSol (AVenhance.streamVel φ) κ F θ₀ ψ) :
    ∀ t : ℝ, 0 ≤ t → ∀ x : Vec 2, ψ t x = θ t x := by
  let w : ℝ → Vec 2 → ℝ := fun t x => ψ t x - θ t x
  have hw : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry w)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    have hsub := hψ.1.sub hθ.1
    change ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry w)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) at hsub
    exact hsub
  have hwOpen : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry w)
      classicalPositiveTimeDomain := by
    apply hw.mono
    intro p hp
    simp only [classicalPositiveTimeDomain, Set.mem_prod, Set.mem_Ioi, Set.mem_univ] at hp
    exact ⟨le_of_lt hp.1, trivial⟩
  have hwper : ∀ t : ℝ, 0 ≤ t → AVenhance.IsZ2Periodic (w t) := by
    intro t ht k x
    simp [w, hψ.2.1 t ht k x, hθ.2.1 t ht k x]
  have hwzero : ∀ x : Vec 2, w 0 x = 0 := by
    intro x
    simp [w, hψ.2.2.1 x, hθ.2.2.1 x]
  have hPDE (t : ℝ) (ht : 0 < t) (x : Vec 2) :
      classicalTimePartial w (t, x) - κ * AVenhance.spaceLap (w t) x +
        Homogenization.vecDot (AVenhance.streamVel φ t x) (AVenhance.spaceGrad (w t) x) = 0 := by
    have hθsmoothOn : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry θ)
        (Set.Ici (0 : ℝ) ×ˢ Set.univ) := hθ.1
    have hψsmoothOn : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry ψ)
        (Set.Ici (0 : ℝ) ×ˢ Set.univ) := hψ.1
    have hθsmoothOpen : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry θ)
        classicalPositiveTimeDomain := hθsmoothOn.mono (by
      intro p hp
      simp only [classicalPositiveTimeDomain, Set.mem_prod, Set.mem_Ioi, Set.mem_univ] at hp
      exact ⟨le_of_lt hp.1, trivial⟩)
    have hψsmoothOpen : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry ψ)
        classicalPositiveTimeDomain := hψsmoothOn.mono (by
      intro p hp
      simp only [classicalPositiveTimeDomain, Set.mem_prod, Set.mem_Ioi, Set.mem_univ] at hp
      exact ⟨le_of_lt hp.1, trivial⟩)
    have hθtime := classicalTimeSection_hasDerivAt hθsmoothOpen ht x
    have hψtime := classicalTimeSection_hasDerivAt hψsmoothOpen ht x
    have hderiv : deriv (fun s => ψ s x) t - deriv (fun s => θ s x) t =
        classicalTimePartial w (t, x) := by
      have hsub := (hψtime.sub hθtime).deriv
      rw [← hψtime.deriv, ← hθtime.deriv] at hsub
      have hfun : (fun s => w s x) = (fun s => ψ s x) - (fun s => θ s x) := by
        funext s
        rfl
      calc
        deriv (fun s => ψ s x) t - deriv (fun s => θ s x) t =
            deriv (fun s => w s x) t := by
          calc
            _ = deriv ((fun s => ψ s x) - (fun s => θ s x)) t := hsub.symm
            _ = deriv (fun s => w s x) t := by rw [← hfun]
        _ = classicalTimePartial w (t, x) :=
          (classicalTimePartial_eq_deriv hwOpen ht x).symm
    have hθsmooth := classicalSmooth_slice_nonneg hθ.1 (le_of_lt ht)
    have hψsmooth := classicalSmooth_slice_nonneg hψ.1 (le_of_lt ht)
    have hgrad := congrFun (ThetaClassicalUniqueness.theta_smooth_spaceGrad_sub hψsmooth hθsmooth) x
    have hlap := congrFun (ThetaClassicalUniqueness.theta_smooth_spaceLap_sub hψsmooth hθsmooth) x
    have hdot :
        Homogenization.vecDot (AVenhance.streamVel φ t x) (AVenhance.spaceGrad (w t) x) =
          Homogenization.vecDot (AVenhance.streamVel φ t x) (AVenhance.spaceGrad (ψ t) x) -
            Homogenization.vecDot (AVenhance.streamVel φ t x) (AVenhance.spaceGrad (θ t) x) := by
      simp only [Homogenization.vecDot]
      rw [hgrad]
      simp only [Pi.sub_apply, mul_sub]
      rw [Finset.sum_sub_distrib]
    have hψeq := hψ.2.2.2 t ht x
    have hθeq := hθ.2.2.2 t ht x
    have hoper :
        AVenhance.advDiffOp (AVenhance.streamVel φ) κ ψ t x -
          AVenhance.advDiffOp (AVenhance.streamVel φ) κ θ t x = 0 := by
      rw [hψeq, hθeq]
      ring
    calc
      classicalTimePartial w (t, x) - κ * AVenhance.spaceLap (w t) x +
          Homogenization.vecDot (AVenhance.streamVel φ t x) (AVenhance.spaceGrad (w t) x) =
          (deriv (fun s => ψ s x) t - deriv (fun s => θ s x) t) -
            κ * (AVenhance.spaceLap (ψ t) x - AVenhance.spaceLap (θ t) x) +
            (Homogenization.vecDot (AVenhance.streamVel φ t x) (AVenhance.spaceGrad (ψ t) x) -
              Homogenization.vecDot (AVenhance.streamVel φ t x) (AVenhance.spaceGrad (θ t) x)) := by
        rw [← hderiv, hlap, hdot]
      _ = AVenhance.advDiffOp (AVenhance.streamVel φ) κ ψ t x -
            AVenhance.advDiffOp (AVenhance.streamVel φ) κ θ t x := by
        simp only [AVenhance.advDiffOp]
        ring_nf
      _ = 0 := hoper
  have henergyRate (t : ℝ) (ht : 0 < t) :
      deriv (fun s => ∫ x in AVenhance.unitCube, (w s x) ^ 2) t =
        -(2 * κ) * ∫ x in AVenhance.unitCube,
          Homogenization.vecDot (AVenhance.spaceGrad (w t) x)
            (AVenhance.spaceGrad (w t) x) := by
    exact @streamVel_classical_unique_energyRate1 φ hφ κ F θ₀ θ ψ hθ hψ hw hwOpen hwper hPDE t ht
  intro t ht x
  by_cases hzeroTime : t = 0
  · subst t
    simp [hψ.2.2.1 x, hθ.2.2.1 x]
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm hzeroTime)
    let E : ℝ → ℝ := fun s => ∫ y in AVenhance.unitCube, (w s y) ^ 2
    have hEcont := theta_energy_continuousOn hw htpos.le
    have hEderiv (s : ℝ) (hs : 0 < s) : HasDerivAt E
        (∫ y in AVenhance.unitCube, 2 * w s y * classicalTimePartial w (s, y)) s := by
      simpa [E] using theta_energy_hasDerivAt hw hs
    have hgradNonneg (s : ℝ) (hs : 0 < s) :
        0 ≤ ∫ y in AVenhance.unitCube,
          Homogenization.vecDot (AVenhance.spaceGrad (w s) y)
            (AVenhance.spaceGrad (w s) y) := by
      apply integral_nonneg
      intro y
      simp only [Homogenization.vecDot]
      apply Finset.sum_nonneg
      intro i hi
      nlinarith [sq_nonneg (AVenhance.spaceGrad (w s) y i)]
    have hdiff (s : ℝ) (hs : s ∈ interior (Set.Icc (0 : ℝ) t)) : DifferentiableAt ℝ E s := by
      have hs' : s ∈ Set.Ioo (0 : ℝ) t := by simpa [interior_Icc, htpos.ne'] using hs
      exact (hEderiv s hs'.1).differentiableAt
    have hderivNonpos (s : ℝ) (hs : s ∈ interior (Set.Icc (0 : ℝ) t)) : deriv E s ≤ 0 := by
      have hs' : s ∈ Set.Ioo (0 : ℝ) t := by simpa [interior_Icc, htpos.ne'] using hs
      rw [henergyRate s hs'.1]
      exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith [hκ]) (hgradNonneg s hs'.1)
    have hanti : AntitoneOn E (Set.Icc (0 : ℝ) t) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) t) ?_ ?_ hderivNonpos
      · simpa [E] using hEcont
      · exact fun s hs => (hdiff s hs).differentiableWithinAt
    have hEzero : E t = 0 := by
      have hle : E t ≤ E 0 := hanti ⟨le_rfl, htpos.le⟩ ⟨htpos.le, le_rfl⟩ htpos.le
      have hE0 : E 0 = 0 := by
        dsimp [E]
        apply integral_eq_zero_of_ae
        filter_upwards with y
        rw [hwzero y]
        simp
      have hge : 0 ≤ E t := by
        dsimp [E]
        apply integral_nonneg
        intro y
        exact sq_nonneg _
      linarith
    let f : Vec 2 → ℝ := fun y => (w t y) ^ 2
    have hfFrozen : AVenhance.IsZ2Periodic f := by
      intro k y
      change (w t (y + AVenhance.latticeShift k)) ^ 2 = (w t y) ^ 2
      rw [hwper t ht k y]
    have hfper : AVenhance.Infra.Torus.IsZdPeriodic f :=
      (AVenhance.Infra.Torus.isZdPeriodic_iff_frozen f).2 hfFrozen
    let a : Vec 2 := fun i => x i - (1 / 2 : ℝ)
    let U : Set (Vec 2) := Set.pi Set.univ (fun i => Set.Ioo (a i) (a i + 1))
    have hUopen : IsOpen U := by
      dsimp [U]
      exact isOpen_set_pi Set.finite_univ (fun i hi => isOpen_Ioo)
    have hxU : x ∈ U := by
      intro i hi
      have hi' : x i ∈ Set.Ioo (a i) (a i + 1) := by
        dsimp [a]
        constructor <;> linarith
      exact hi'
    have hUsub : U ⊆ AVenhance.Infra.Torus.unitCellAt 2 a := by
      intro y hy i
      have hi := hy i (mem_univ i)
      exact ⟨hi.1, le_of_lt hi.2⟩
    have hfInt : IntegrableOn f (AVenhance.Infra.Torus.unitCellAt 2 a) := by
      apply ThetaClassicalUniqueness.thetaTime_continuous_integrableOn_unitCellAt a
      have hwSlice := classicalSmooth_slice_nonneg hw ht
      change Continuous (fun y => (w t y) ^ 2)
      exact hwSlice.continuous.pow 2
    have hcellIntegral : ∫ y in AVenhance.Infra.Torus.unitCellAt 2 a, f y = 0 := by
      calc
        ∫ y in AVenhance.Infra.Torus.unitCellAt 2 a, f y =
            ∫ y in AVenhance.Infra.Torus.unitCell 2, f y :=
          AVenhance.Infra.Torus.integral_periodic_unitCellAt_eq hfper a
        _ = ∫ y in AVenhance.unitCube, f y :=
          AVenhance.Infra.Torus.integral_unitCell_eq_unitCube f
        _ = E t := rfl
        _ = 0 := hEzero
    have hnonneg : ∀ y, 0 ≤ f y := fun y => sq_nonneg _
    have haeSq : f =ᵐ[volume.restrict (AVenhance.Infra.Torus.unitCellAt 2 a)] 0 :=
      (integral_eq_zero_iff_of_nonneg hnonneg hfInt).mp hcellIntegral
    have hae : w t =ᵐ[volume.restrict (AVenhance.Infra.Torus.unitCellAt 2 a)] 0 := by
      filter_upwards [haeSq] with y hy
      exact (sq_eq_zero_iff.mp hy)
    have haeU : w t =ᵐ[volume.restrict U] 0 :=
      ae_restrict_of_ae_restrict_of_subset hUsub hae
    have hwCont : Continuous (w t) := by
      exact (classicalSmooth_slice_nonneg hw ht).continuous
    have heqOn := MeasureTheory.Measure.eqOn_open_of_ae_eq haeU hUopen
      hwCont.continuousOn continuousOn_const
    have hwx : w t x = 0 := heqOn hxU
    exact sub_eq_zero.mp (by simpa [w] using hwx)

/-- A continuous periodic datum whose torus L² norm vanishes is pointwise
zero.  The shifted open cell lets periodicity move the integral away from
cell-boundary representatives. -/
theorem theta_continuous_periodic_eq_zero_of_l2NormSq_eq_zero
    {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hper : AVenhance.IsZ2Periodic f)
    (hzero : AVenhance.l2NormSq f = 0) : f = 0 := by
  funext x
  let a : Vec 2 := fun i => x i - (1 / 2 : ℝ)
  let U : Set (Vec 2) := Set.pi Set.univ (fun i => Set.Ioo (a i) (a i + 1))
  have hUopen : IsOpen U := by
    dsimp [U]
    exact isOpen_set_pi Set.finite_univ (fun i hi => isOpen_Ioo)
  have hxU : x ∈ U := by
    intro i hi
    dsimp [a]
    constructor <;> linarith
  have hUsub : U ⊆ AVenhance.Infra.Torus.unitCellAt 2 a := by
    intro y hy i
    have hi := hy i (mem_univ i)
    exact ⟨hi.1, le_of_lt hi.2⟩
  let sqf : Vec 2 → ℝ := fun y => f y ^ 2
  have hsqper : AVenhance.IsZ2Periodic sqf := by
    intro k y
    simp [sqf, hper k y]
  have hsqper' : AVenhance.Infra.Torus.IsZdPeriodic sqf :=
    (AVenhance.Infra.Torus.isZdPeriodic_iff_frozen sqf).2 hsqper
  have hsqInt : IntegrableOn sqf (AVenhance.Infra.Torus.unitCellAt 2 a) := by
    apply ThetaClassicalUniqueness.thetaTime_continuous_integrableOn_unitCellAt a
    exact hf.continuous.pow 2
  have hcell :
      (∫ y in AVenhance.Infra.Torus.unitCellAt 2 a, sqf y) = 0 := by
    calc
      _ = ∫ y in AVenhance.Infra.Torus.unitCell 2, sqf y :=
        AVenhance.Infra.Torus.integral_periodic_unitCellAt_eq hsqper' a
      _ = ∫ y in AVenhance.unitCube, sqf y :=
        AVenhance.Infra.Torus.integral_unitCell_eq_unitCube sqf
      _ = AVenhance.l2NormSq f := rfl
      _ = 0 := hzero
  have hnonneg : ∀ y, 0 ≤ sqf y := fun y => sq_nonneg _
  have haeSq : sqf =ᵐ[volume.restrict
      (AVenhance.Infra.Torus.unitCellAt 2 a)] 0 :=
    (integral_eq_zero_iff_of_nonneg hnonneg hsqInt).mp hcell
  have hae : f =ᵐ[volume.restrict
      (AVenhance.Infra.Torus.unitCellAt 2 a)] 0 := by
    filter_upwards [haeSq] with y hy
    exact (sq_eq_zero_iff.mp (by simpa [sqf] using hy))
  have haeU : f =ᵐ[volume.restrict U] 0 :=
    ae_restrict_of_ae_restrict_of_subset hUsub hae
  have heqOn := MeasureTheory.Measure.eqOn_open_of_ae_eq haeU hUopen
    hf.continuous.continuousOn continuousOn_const
  exact heqOn hxU

end AVenhance.Infra.Section4

end
