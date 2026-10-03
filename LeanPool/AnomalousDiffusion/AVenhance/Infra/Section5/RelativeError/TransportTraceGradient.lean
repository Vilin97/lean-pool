/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.TransportTracePairing
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.TransportFlowCellIntegral
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.GradientChain
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.PulledGradientTransport
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.PeriodicCalculus

/-! # RelativeError: control the gradient of the transported test -/

@[expose] public section

noncomputable section

open Homogenization
open MeasureTheory
open scoped ContDiff

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance
open AVenhance.Infra.Torus

theorem TransportTraceGradient.inverseFlow_transportedGradient_pointwise_le
    {b : ℝ → Vec 2 → Vec 2} (hb : Infra.Flow.SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlow b X)
    {B T : ℝ} (hB : 0 ≤ B) (hBT : B * T ≤ 1)
    (hDb : ∀ r y, ‖Infra.Flow.jointSpatialFDeriv b r y‖ ≤ B)
    {h₀ : Vec 2 → ℝ} (hh₀ : ContDiff ℝ (⊤ : ℕ∞) h₀)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (x : Vec 2) :
    vecNormSq
      (spaceGrad (inverseFlowTransportTest (h₀ := h₀) X t) x) ≤
      4 * (Real.exp 1) ^ 2 *
        vecNormSq (spaceGrad h₀ (X 0 x t)) := by
  let Y : Vec 2 → Vec 2 := fun z => X 0 z t
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
  have hJ := (flow_transport_derivatives_le_exp_one hb hX hB hBT hDb ht x).2
  have hEntry (i j : Fin 2) : |gradMatrix Y x i j| ≤ Real.exp 1 := by
    rw [gradMatrix_entry_eq_fderiv hYdiff i j]
    have hcolumn :
        ‖fderiv ℝ Y x (basisVec i)‖ ≤ Real.exp 1 := by
      calc
        ‖fderiv ℝ Y x (basisVec i)‖ ≤
            ‖fderiv ℝ Y x‖ * ‖basisVec i‖ :=
              (fderiv ℝ Y x).le_opNorm (basisVec i)
        _ = ‖fderiv ℝ Y x‖ := by simp [basisVec, Pi.norm_single]
        _ ≤ Real.exp 1 := hJ
    have hcomponent :
        ‖fderiv ℝ Y x (basisVec i) j‖ ≤
          ‖fderiv ℝ Y x (basisVec i)‖ :=
      (pi_norm_le_iff_of_nonneg
        (norm_nonneg (fderiv ℝ Y x (basisVec i)))).1 le_rfl j
    simpa [Real.norm_eq_abs] using hcomponent.trans hcolumn
  have hchain (i : Fin 2) :
      spaceGrad (fun z => h₀ (Y z)) x i =
        ∑ j : Fin 2, gradMatrix Y x i j * spaceGrad h₀ (Y x) j :=
    AVenhance.Infra.Section5.spaceGrad_comp_eq_gradMatrix_mul
      hhDiff.hasFDerivAt hYdiff.hasFDerivAt i
  have hcomponentBound (i : Fin 2) :
      |spaceGrad (fun z => h₀ (Y z)) x i| ≤
        Real.exp 1 * (|spaceGrad h₀ (Y x) 0| +
          |spaceGrad h₀ (Y x) 1|) := by
    rw [hchain i, Fin.sum_univ_two]
    have h0 := hEntry i 0
    have h1 := hEntry i 1
    calc
        |gradMatrix Y x i 0 * spaceGrad h₀ (Y x) 0 +
          gradMatrix Y x i 1 * spaceGrad h₀ (Y x) 1| ≤
        |gradMatrix Y x i 0 * spaceGrad h₀ (Y x) 0| +
          |gradMatrix Y x i 1 * spaceGrad h₀ (Y x) 1| := abs_add_le _ _
      _ = |gradMatrix Y x i 0| * |spaceGrad h₀ (Y x) 0| +
          |gradMatrix Y x i 1| * |spaceGrad h₀ (Y x) 1| := by rw [abs_mul, abs_mul]
      _ ≤ Real.exp 1 * |spaceGrad h₀ (Y x) 0| +
          Real.exp 1 * |spaceGrad h₀ (Y x) 1| := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right h0 (abs_nonneg _))
          (mul_le_mul_of_nonneg_right h1 (abs_nonneg _))
      _ = _ := by ring
  let a : ℝ := |spaceGrad h₀ (Y x) 0| + |spaceGrad h₀ (Y x) 1|
  have hA : a ^ 2 ≤ 2 * vecNormSq (spaceGrad h₀ (Y x)) := by
    dsimp [a]
    simp only [vecNormSq, vecDot, Fin.sum_univ_two]
    nlinarith [sq_abs (spaceGrad h₀ (Y x) 0),
      sq_abs (spaceGrad h₀ (Y x) 1),
      sq_nonneg
        (|spaceGrad h₀ (Y x) 0| - |spaceGrad h₀ (Y x) 1|)]
  have h0sq :
      (spaceGrad (fun z => h₀ (Y z)) x 0) ^ 2 ≤ (Real.exp 1 * a) ^ 2 := by
    have hh := (sq_le_sq₀
      (abs_nonneg (spaceGrad (fun z => h₀ (Y z)) x 0)) (by positivity)).2
        (hcomponentBound 0)
    simpa [sq_abs, a] using hh
  have h1sq :
      (spaceGrad (fun z => h₀ (Y z)) x 1) ^ 2 ≤ (Real.exp 1 * a) ^ 2 := by
    have hh := (sq_le_sq₀
      (abs_nonneg (spaceGrad (fun z => h₀ (Y z)) x 1)) (by positivity)).2
        (hcomponentBound 1)
    simpa [sq_abs, a] using hh
  have henergy :
      vecNormSq (spaceGrad (fun z => h₀ (Y z)) x) ≤
        4 * (Real.exp 1) ^ 2 * vecNormSq (spaceGrad h₀ (Y x)) := by
    simp only [vecNormSq, vecDot, Fin.sum_univ_two]
    calc
      (spaceGrad (fun z => h₀ (Y z)) x 0) *
          (spaceGrad (fun z => h₀ (Y z)) x 0) +
        (spaceGrad (fun z => h₀ (Y z)) x 1) *
          (spaceGrad (fun z => h₀ (Y z)) x 1) ≤
        2 * (Real.exp 1 * a) ^ 2 := by nlinarith [h0sq, h1sq]
      _ = 2 * (Real.exp 1) ^ 2 * a ^ 2 := by ring
      _ ≤ 4 * (Real.exp 1) ^ 2 * vecNormSq (spaceGrad h₀ (Y x)) := by
        have hA' := hA
        simp only [vecNormSq, vecDot, Fin.sum_univ_two] at hA'
        nlinarith [hA', sq_nonneg (Real.exp 1)]
      _ = 4 * (Real.exp 1) ^ 2 *
          (spaceGrad h₀ (Y x) 0 * spaceGrad h₀ (Y x) 0 +
            spaceGrad h₀ (Y x) 1 * spaceGrad h₀ (Y x) 1) := by
        simp [vecNormSq, vecDot, Fin.sum_univ_two]
  change vecNormSq (spaceGrad (fun z => h₀ (Y z)) x) ≤
    4 * (Real.exp 1) ^ 2 * vecNormSq (spaceGrad h₀ (Y x))
  exact henergy

end AVenhance.Infra.Section5.RelativeError

end
