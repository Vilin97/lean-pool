/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.TransportPiolaCellBound
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.TransportTraceGradient
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.TraceEuclideanFlowBound

/-! # RelativeError: Euclidean transport bounds without coordinate losses -/

@[expose] public section

noncomputable section

open Homogenization
open MeasureTheory
open scoped ContDiff

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance
open AVenhance.Infra.Classical
open AVenhance.Infra.Torus

theorem TraceEuclideanTransport.shortFlow_exp_bound {B T t : ℝ} (hB : 0 ≤ B)
    (hBT : B * T ≤ 1) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Real.exp (2 * B * (t - 0)) ≤ (Real.exp 1) ^ 2 := by
  have hBt : B * t ≤ 1 := by
    calc
      B * t ≤ B * T := mul_le_mul_of_nonneg_left ht.2 hB
      _ ≤ 1 := hBT
  have harg : 2 * B * (t - 0) ≤ 2 := by nlinarith [hBt]
  calc
    Real.exp (2 * B * (t - 0)) ≤ Real.exp 2 := Real.exp_le_exp.mpr harg
    _ = (Real.exp 1) ^ 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      ring

theorem TraceEuclideanTransport.inverseFlow_derivative_short_euclidean_bound
    {b : ℝ → Vec 2 → Vec 2} (hb : Infra.Flow.SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlow b X)
    (hdiv : ∀ t x, vecDiv (b t) x = 0)
    {B T : ℝ} (hB : 0 ≤ B) (hBT : B * T ≤ 1)
    (hDb : ∀ r y, ‖Infra.Flow.jointSpatialFDeriv b r y‖ ≤ B)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (x z : Vec 2) :
    vecNormSq (fderiv ℝ (fun y => X 0 y t) x z) ≤
      (Real.exp 1) ^ 2 * vecNormSq z := by
  have hraw := inverseFlow_derivative_vecNormSq_le hb hX hdiv hDb
    (s := t) (t := 0) (by exact ht.1) x z
  have hexp := TraceEuclideanTransport.shortFlow_exp_bound hB hBT ht
  calc
    vecNormSq (fderiv ℝ (fun y => X 0 y t) x z) ≤
        vecNormSq z * Real.exp (2 * B * (t - 0)) := hraw
    _ ≤ vecNormSq z * (Real.exp 1) ^ 2 :=
      mul_le_mul_of_nonneg_left hexp (vecNormSq_nonneg z)
    _ = _ := by ring

theorem TraceEuclideanTransport.forwardFlow_derivative_short_euclidean_bound
    {b : ℝ → Vec 2 → Vec 2} (hb : Infra.Flow.SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlow b X)
    (hdiv : ∀ t x, vecDiv (b t) x = 0)
    {B T : ℝ} (hB : 0 ≤ B) (hBT : B * T ≤ 1)
    (hDb : ∀ r y, ‖Infra.Flow.jointSpatialFDeriv b r y‖ ≤ B)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (x z : Vec 2) :
    vecNormSq (fderiv ℝ (fun y => X t y 0) x z) ≤
      (Real.exp 1) ^ 2 * vecNormSq z := by
  have hraw := forwardFlow_derivative_vecNormSq_le hb hX hdiv hDb
    (s := 0) (t := t) (by exact ht.1) x z
  have hexp := TraceEuclideanTransport.shortFlow_exp_bound hB hBT ht
  calc
    vecNormSq (fderiv ℝ (fun y => X t y 0) x z) ≤
        vecNormSq z * Real.exp (2 * B * (t - 0)) := hraw
    _ ≤ vecNormSq z * (Real.exp 1) ^ 2 :=
      mul_le_mul_of_nonneg_left hexp (vecNormSq_nonneg z)
    _ = _ := by ring

/-- The gradient of the inverse-flow transported test has its exact
Euclidean operator bound, with no coordinatewise matrix estimate. -/
theorem inverseFlow_transportedGradient_euclidean_pointwise_le
    {b : ℝ → Vec 2 → Vec 2} (hb : Infra.Flow.SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlow b X)
    (hdiv : ∀ t x, vecDiv (b t) x = 0)
    {B T : ℝ} (hB : 0 ≤ B) (hBT : B * T ≤ 1)
    (hDb : ∀ r y, ‖Infra.Flow.jointSpatialFDeriv b r y‖ ≤ B)
    {h₀ : Vec 2 → ℝ} (hh₀ : ContDiff ℝ (⊤ : ℕ∞) h₀)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (x : Vec 2) :
    vecNormSq (spaceGrad (inverseFlowTransportTest (h₀ := h₀) X t) x) ≤
      (Real.exp 1) ^ 2 * vecNormSq (spaceGrad h₀ (X 0 x t)) := by
  let Y : Vec 2 → Vec 2 := fun z => X 0 z t
  let L : Vec 2 →L[ℝ] Vec 2 := fderiv ℝ Y x
  have hY : ContDiff ℝ (⊤ : ℕ∞) Y := by
    have hInv := Infra.Flow.flow_inverse_joint_contDiff_infty hb hX
    have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec 2 => (t, z, (0 : ℝ))) := by
      fun_prop
    change ContDiff ℝ (⊤ : ℕ∞)
      ((fun p : ℝ × Vec 2 × ℝ => X p.2.2 p.2.1 p.1) ∘
        fun z : Vec 2 => (t, z, (0 : ℝ)))
    exact hInv.comp hmap
  have hYdiff : DifferentiableAt ℝ Y x := hY.differentiable (by simp) x
  have hhDiff : DifferentiableAt ℝ h₀ (Y x) :=
    hh₀.differentiable (by simp) (Y x)
  have hL : ∀ z, vecNormSq (L z) ≤ (Real.exp 1) ^ 2 * vecNormSq z := by
    intro z
    exact TraceEuclideanTransport.inverseFlow_derivative_short_euclidean_bound hb hX hdiv hB hBT
      hDb ht x z
  have hchain (i : Fin 2) :
      spaceGrad (fun z => h₀ (Y z)) x i =
        ∑ j : Fin 2, gradMatrix Y x i j * spaceGrad h₀ (Y x) j :=
    AVenhance.Infra.Section5.spaceGrad_comp_eq_gradMatrix_mul
      hhDiff.hasFDerivAt hYdiff.hasFDerivAt i
  have hcompose : spaceGrad (fun z => h₀ (Y z)) x =
      euclideanTransposeApply L (spaceGrad h₀ (Y x)) := by
    ext i
    rw [hchain i]
    simp only [euclideanTransposeApply]
    apply Finset.sum_congr rfl
    intro j hj
    rw [gradMatrix_entry_eq_fderiv hYdiff i j]
  have htranspose := euclideanTranspose_vecNormSq_le L (C := Real.exp 1)
    (fun z => hL z) (spaceGrad h₀ (Y x))
  change vecNormSq (spaceGrad (fun z => h₀ (Y z)) x) ≤ _
  rw [hcompose]
  simpa [L] using htranspose

/-- Cell L² version of the Euclidean transported-gradient estimate. -/
theorem inverseFlow_transportedGradient_euclidean_cellL2_bound
    {b : ℝ → Vec 2 → Vec 2} (hb : Infra.Flow.SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlow b X)
    (hdiv : ∀ t x, vecDiv (b t) x = 0)
    {B T : ℝ} (hB : 0 ≤ B) (hBT : B * T ≤ 1)
    (hDb : ∀ r y, ‖Infra.Flow.jointSpatialFDeriv b r y‖ ≤ B)
    {h₀ : Vec 2 → ℝ} (hh₀ : ContDiff ℝ (⊤ : ℕ∞) h₀)
    (hper : IsZ2Periodic h₀) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∫ x in unitCell 2,
      vecNormSq (spaceGrad (inverseFlowTransportTest (h₀ := h₀) X t) x) ≤
      (Real.exp 1) ^ 2 * (∫ x in unitCell 2, vecNormSq (spaceGrad h₀ x)) := by
  let H : ℝ → Vec 2 → ℝ := inverseFlowTransportTest (h₀ := h₀) X
  have hHsmooth : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry H) :=
    inverseFlowTransportTest_contDiff_infty hb hX hh₀
  have hHper : IsZ2Periodic (H t) :=
    (inverseFlowTransportTest_isClassicalTransportTest hb hX hh₀ hper).periodic t ht.1
  have hHslice (s : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (H s) := by
    have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (s, x)) := by fun_prop
    exact hHsmooth.comp hmap
  have henergyPer : IsZ2Periodic
      (fun x => vecNormSq (spaceGrad h₀ x)) := by
    intro k x
    have hp0 := Infra.Classical.periodic_spaceGrad_component hper 0 k x
    have hp1 := Infra.Classical.periodic_spaceGrad_component hper 1 k x
    simp [vecNormSq, vecDot, hp0, hp1]
  have hleftCont : Continuous
      (fun x => vecNormSq (spaceGrad (H t) x)) := by
    have hgrad : Continuous (spaceGrad (H t)) := by
      apply continuous_pi
      intro i
      change Continuous (fun x => fderiv ℝ (H t) x (basisVec i))
      exact ((hHslice t).continuous_fderiv (by norm_num)).clm_apply continuous_const
    exact AVenhance.Infra.Section5.LeftToShow.continuous_vecNormSq_two.comp hgrad
  have hrightCont : Continuous
      (fun x => vecNormSq (spaceGrad h₀ (X 0 x t))) := by
    have hgrad : Continuous (spaceGrad h₀) := by
      apply continuous_pi
      intro i
      change Continuous (fun x => fderiv ℝ h₀ x (basisVec i))
      exact (hh₀.continuous_fderiv (by simp)).clm_apply continuous_const
    have hY : Continuous (fun x : Vec 2 => X 0 x t) := by
      have hInv := Infra.Flow.flow_inverse_joint_contDiff_infty hb hX
      have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x, (0 : ℝ))) := by
        fun_prop
      have hYdiff : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => X 0 x t) := by
        change ContDiff ℝ (⊤ : ℕ∞)
          ((fun p : ℝ × Vec 2 × ℝ => X p.2.2 p.2.1 p.1) ∘
            fun x : Vec 2 => (t, x, (0 : ℝ)))
        exact hInv.comp hmap
      exact hYdiff.continuous
    exact AVenhance.Infra.Section5.LeftToShow.continuous_vecNormSq_two.comp
      (hgrad.comp hY)
  have hpoint (x : Vec 2) :=
    inverseFlow_transportedGradient_euclidean_pointwise_le
      hb hX hdiv hB hBT hDb hh₀ ht x
  have hmono := setIntegral_mono_on
    (Infra.Classical.continuous_integrableOn_unitCell hleftCont)
    ((Infra.Classical.continuous_integrableOn_unitCell hrightCont).const_mul
      ((Real.exp 1) ^ 2))
    (Infra.Torus.measurableSet_unitCell 2) (by
      intro x hx
      exact hpoint x)
  calc
    ∫ x in unitCell 2, vecNormSq (spaceGrad (H t) x) ≤
        ∫ x in unitCell 2,
          (Real.exp 1) ^ 2 * vecNormSq (spaceGrad h₀ (X 0 x t)) := hmono
    _ = (Real.exp 1) ^ 2 *
        (∫ x in unitCell 2, vecNormSq (spaceGrad h₀ (X 0 x t))) := by
          rw [integral_const_mul]
    _ = (Real.exp 1) ^ 2 *
        (∫ x in unitCell 2, vecNormSq (spaceGrad h₀ x)) := by
          rw [integral_unitCell_comp_inverseFlow hb hX hdiv henergyPer t]

/-- The Piola vector has the same exact Euclidean cell-energy bound. Its
cofactor representation equals the forward flow derivative applied to the
initial gradient, and Liouville unfolds the cell integral. -/
theorem inverseFlow_piolaVector_euclideanCellEnergy_sharp_bound
    {b : ℝ → Vec 2 → Vec 2} (hb : Infra.Flow.SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlow b X)
    (hdiv : ∀ t x, vecDiv (b t) x = 0)
    {B T : ℝ} (hB : 0 ≤ B) (hBT : B * T ≤ 1)
    (hDb : ∀ r y, ‖Infra.Flow.jointSpatialFDeriv b r y‖ ≤ B)
    {f : Vec 2 → ℝ} (hf : ContDiff ℝ 3 f)
    (hper : IsZ2Periodic f) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∫ x in unitCell 2, vecNormSq
      (Matrix.mulVec
        (FaaDiBruno.flowMatrixCofactorTranspose
          (FaaDiBruno.spatialGradientMatrix (fun y => X 0 y t) x))
        (spaceGrad f (X 0 x t))) ≤
      (Real.exp 1) ^ 2 * (∫ x in unitCell 2, vecNormSq (spaceGrad f x)) := by
  let Y : Vec 2 → Vec 2 := fun x => X 0 x t
  let W : Vec 2 → Vec 2 := fun x => Matrix.mulVec
    (FaaDiBruno.flowMatrixCofactorTranspose
      (FaaDiBruno.spatialGradientMatrix Y x)) (spaceGrad f (Y x))
  have hY : ContDiff ℝ ∞ Y := by
    have hInv := Infra.Flow.flow_inverse_joint_contDiff_infty hb hX
    have hmap : ContDiff ℝ ∞ (fun x : Vec 2 => (t, x, (0 : ℝ))) := by fun_prop
    change ContDiff ℝ ∞
      ((fun p : ℝ × Vec 2 × ℝ => X p.2.2 p.2.1 p.1) ∘
        fun x : Vec 2 => (t, x, (0 : ℝ)))
    exact hInv.comp hmap
  have hF : ContDiff ℝ ∞ (fun x => X t x 0) := by
    have hforward := Infra.Flow.flow_joint_contDiff_infty hb hX
    have hmap : ContDiff ℝ ∞ (fun x : Vec 2 => (t, x, (0 : ℝ))) := by fun_prop
    change ContDiff ℝ ∞
      ((fun p : ℝ × Vec 2 × ℝ => X p.1 p.2.1 p.2.2) ∘
        fun x : Vec 2 => (t, x, (0 : ℝ)))
    exact hforward.comp hmap
  have hWcont : Continuous W := inverseFlow_piolaVector_continuous hb hX hf t
  have henergyPer : IsZ2Periodic (fun x => vecNormSq (spaceGrad f x)) := by
    intro k x
    have hper0 := Infra.Classical.periodic_spaceGrad_component hper 0 k x
    have hper1 := Infra.Classical.periodic_spaceGrad_component hper 1 k x
    simp [vecNormSq, vecDot, hper0, hper1]
  have hpoint (x : Vec 2) :
      vecNormSq (W x) ≤ (Real.exp 1) ^ 2 * vecNormSq (spaceGrad f (Y x)) := by
    have hcof := inverseFlow_forwardJacobian_eq_cofactor hb hX hdiv t x
    have heq : W x = fderiv ℝ (fun z => X t z 0) (Y x) (spaceGrad f (Y x)) := by
      dsimp [W, Y]
      calc
        Matrix.mulVec
            (FaaDiBruno.flowMatrixCofactorTranspose
              (FaaDiBruno.spatialGradientMatrix (fun z => X 0 z t) x))
            (spaceGrad f (X 0 x t)) =
          Matrix.mulVec
            (FaaDiBruno.spatialGradientMatrix (fun z => X t z 0) (X 0 x t))
            (spaceGrad f (X 0 x t)) := by rw [← hcof]
        _ = fderiv ℝ (fun z => X t z 0) (X 0 x t)
            (spaceGrad f (X 0 x t)) := spatialGradientMatrix_mulVec_eq_fderiv _ _
    rw [heq]
    exact TraceEuclideanTransport.forwardFlow_derivative_short_euclidean_bound hb hX hdiv hB hBT
      hDb ht (Y x) (spaceGrad f (Y x))
  have hleftCont : Continuous (fun x => vecNormSq (W x)) :=
    AVenhance.Infra.Section5.LeftToShow.continuous_vecNormSq_two.comp hWcont
  have hrightCont : Continuous
      (fun x => (Real.exp 1) ^ 2 * vecNormSq (spaceGrad f (Y x))) := by
    have hgrad : Continuous (spaceGrad f) := by
      apply continuous_pi
      intro i
      change Continuous (fun x => fderiv ℝ f x (basisVec i))
      exact (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
    exact continuous_const.mul
      (AVenhance.Infra.Section5.LeftToShow.continuous_vecNormSq_two.comp
        (hgrad.comp hY.continuous))
  have hmono := setIntegral_mono_on
    (Infra.Classical.continuous_integrableOn_unitCell hleftCont)
    (Infra.Classical.continuous_integrableOn_unitCell hrightCont)
    (Infra.Torus.measurableSet_unitCell 2) (by
      intro x hx
      exact hpoint x)
  calc
    ∫ x in unitCell 2, vecNormSq (W x) ≤
        ∫ x in unitCell 2,
          (Real.exp 1) ^ 2 * vecNormSq (spaceGrad f (Y x)) := hmono
    _ = (Real.exp 1) ^ 2 *
        (∫ x in unitCell 2, vecNormSq (spaceGrad f (Y x))) := by
          rw [integral_const_mul]
    _ = (Real.exp 1) ^ 2 *
        (∫ x in unitCell 2, vecNormSq (spaceGrad f x)) := by
          rw [integral_unitCell_comp_inverseFlow hb hX hdiv henergyPer t]

/-- Pairing `u` with the transported `-Δf` costs exactly `e` in Euclidean
gradient energy. -/
theorem inverseFlow_laplacian_pairing_abs_le_euclidean
    {b : ℝ → Vec 2 → Vec 2} (hb : Infra.Flow.SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlow b X)
    (hdiv : ∀ t x, vecDiv (b t) x = 0)
    {B T : ℝ} (hB : 0 ≤ B) (hBT : B * T ≤ 1)
    (hDb : ∀ r y, ‖Infra.Flow.jointSpatialFDeriv b r y‖ ≤ B)
    {f u₀ : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfper : IsZ2Periodic f) (hu : ContDiff ℝ 1 u₀)
    (huper : IsZ2Periodic u₀) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    |∫ x in unitCell 2,
      u₀ x * inverseFlowTransportTest
        (h₀ := fun y => -spaceLap f y) X t x| ≤
      Real.sqrt (∫ x in unitCell 2, vecNormSq (spaceGrad u₀ x)) *
        (Real.exp 1 * Real.sqrt
          (∫ x in unitCell 2, vecNormSq (spaceGrad f x))) := by
  rw [inverseFlow_laplacian_pairing_eq_piola hb hX hdiv hu huper hf hfper t]
  let W : Vec 2 → Vec 2 := fun x => Matrix.mulVec
    (FaaDiBruno.flowMatrixCofactorTranspose
      (FaaDiBruno.spatialGradientMatrix (fun y => X 0 y t) x))
    (spaceGrad f (X 0 x t))
  have hgradU : Continuous (spaceGrad u₀) := by
    apply continuous_pi
    intro i
    change Continuous (fun x => fderiv ℝ u₀ x (basisVec i))
    exact (hu.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hWcont : Continuous W := inverseFlow_piolaVector_continuous hb hX
    (hf.of_le (by norm_num)) t
  have hCS := integral_unitCell_vecDot_abs_le hgradU hWcont
  have hWenergy := inverseFlow_piolaVector_euclideanCellEnergy_sharp_bound
    hb hX hdiv hB hBT hDb (hf.of_le (by norm_num)) hfper ht
  have hWnonneg : 0 ≤ ∫ x in unitCell 2, vecNormSq (W x) :=
    integral_nonneg (fun x => vecNormSq_nonneg _)
  have hgradFnonneg : 0 ≤ ∫ x in unitCell 2,
      vecNormSq (spaceGrad f x) :=
    integral_nonneg (fun x => vecNormSq_nonneg _)
  have hWroot :
      Real.sqrt (∫ x in unitCell 2, vecNormSq (W x)) ≤
        Real.exp 1 * Real.sqrt
          (∫ x in unitCell 2, vecNormSq (spaceGrad f x)) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).1
    rw [Real.sq_sqrt hWnonneg, mul_pow, Real.sq_sqrt hgradFnonneg]
    nlinarith [hWenergy]
  calc
    |∫ x in unitCell 2, vecDot (spaceGrad u₀ x) (W x)| ≤
        Real.sqrt (∫ x in unitCell 2, vecNormSq (spaceGrad u₀ x)) *
          Real.sqrt (∫ x in unitCell 2, vecNormSq (W x)) := by
            simpa [W] using hCS
    _ ≤ Real.sqrt (∫ x in unitCell 2, vecNormSq (spaceGrad u₀ x)) *
          (Real.exp 1 * Real.sqrt
            (∫ x in unitCell 2, vecNormSq (spaceGrad f x))) :=
        mul_le_mul_of_nonneg_left hWroot (Real.sqrt_nonneg _)

end AVenhance.Infra.Section5.RelativeError

end
