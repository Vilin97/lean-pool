/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.Convolution
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.Smooth
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.SpaceSecondDeriv

/-!
# The Gaussian subordination identity for the Newtonian kernel

The time integral of the three-dimensional heat kernel is the Newtonian
kernel away from its singularity.  This identity is the scalar analytic
input for the heat-kernel route to the pressure decomposition.
-/

public section

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set


noncomputable section

namespace CKN.Foundation.Heat

open CKN.Foundation.Parabolic

lemma shift_fderiv_apply_basisVec {u : Vec3 → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (x y : Vec3) (i : Fin 3) :
    (fderiv ℝ (fun z : Vec3 => u (x - z)) y) (CKN.basisVec i) =
      -CKN.spatialDeriv u i (x - y) := by
  have houter : HasFDerivAt u (fderiv ℝ u (x - y)) (x - y) :=
    ((hu.differentiable (by simp)) (x - y)).hasFDerivAt
  have hinner : HasFDerivAt (fun z : Vec3 => x - z)
      (-ContinuousLinearMap.id ℝ Vec3) y := by
    convert (hasFDerivAt_const x y).sub (hasFDerivAt_id y) using 1
    · funext z
      rfl
    · ext z
      simp
  have hcomp := HasFDerivAt.comp y houter hinner
  have hval := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (CKN.basisVec i)) hcomp.fderiv
  dsimp at hval
  simpa [Function.comp_def, CKN.spatialDeriv] using hval

private lemma heatKernel_laplacian_integral_eq_smooth_hi_1 :
    ∀ {u : Vec3 → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) u →
        ∀ {t : ℝ},
          (0 : ℝ) < t →
            ∀ (x : Vec3),
              (Continuous (Y := ℝ) fun (y : Vec3) => heatKernel y t) →
                (∀ (i : Fin (3 : ℕ)),
                    Continuous (Y := ℝ) fun (y : Vec3) => heatKernelSpaceDerivative y t i) →
                  (∀ (i : Fin (3 : ℕ)),
                      Continuous (Y := ℝ) fun (y : Vec3) => heatKernelSpaceSecondDerivative y t i) →
                    let h0 : Vec3 → ℝ := fun (y : Vec3) => u (x - y);
                    Continuous h0 →
                      HasCompactSupport h0 →
                        (∀ (i : Fin (3 : ℕ)), ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv u i)) →
                          (∀ (i : Fin (3 : ℕ)),
                              Continuous (Y := ℝ) fun (y : Vec3) => spatialDeriv u i (x - y)) →
                            (∀ (i : Fin (3 : ℕ)),
                                HasCompactSupport (β := ℝ) fun (y : Vec3) =>
                                  spatialDeriv u i (x - y)) →
                              (∀ (i : Fin (3 : ℕ)),
                                  Continuous (Y := ℝ) fun (y : Vec3) =>
                                    spatialDeriv (spatialDeriv u i) i (x - y)) →
                                (∀ (i : Fin (3 : ℕ)),
                                    HasCompactSupport (β := ℝ) fun (y : Vec3) =>
                                      spatialDeriv (spatialDeriv u i) i (x - y)) →
                                  (∀ (y : Vec3),
                                      DifferentiableAt ℝ (F := ℝ) (fun (z : Vec3) => heatKernel z t)
                                        y) →
                                    (∀ (i : Fin (3 : ℕ)) (y : Vec3),
                                        DifferentiableAt ℝ (F := ℝ)
                                          (fun (z : Vec3) => heatKernelSpaceDerivative z t i) y) →
                                      (∀ (v : Vec3 → ℝ),
                                          ContDiff ℝ (⊤ : ℕ∞) v →
                                            ∀ (y : Vec3),
                                              DifferentiableAt ℝ (F := ℝ)
                                                (fun (z : Vec3) => v (x - z)) y) →
                                        (∀ (f g : Vec3 → ℝ),
                                            Continuous f →
                                              Continuous g →
                                                HasCompactSupport g →
                                                  @Integrable ℝ _ _ _ MeasureSpace.toMeasurableSpace
                                                    (fun (y : Vec3) => f y * g y) volume) →
                                          ∀ (i : Fin (3 : ℕ)),
                                            Eq (α := ℝ)
                                              (@integral _ _ _ _ MeasureSpace.toMeasurableSpace
                                                volume fun (y : Vec3) =>
                                                heatKernelSpaceSecondDerivative y t i * h0 y)
                                              (@integral _ _ _ _ MeasureSpace.toMeasurableSpace
                                                volume fun (y : Vec3) =>
                                                heatKernel y t *
                                                  spatialDeriv (spatialDeriv u i) i (x - y))
    := by
  intro u hu t ht x hk hk1 hk2 h0 h0c h0s hu1 h1c h1s h2c h2s hkernel_diff hkernel1_diff
    hshift_diff hcompact_integrable i
  let f : Vec3 → ℝ := fun y => heatKernel y t
  let f1 : Vec3 → ℝ := fun y => heatKernelSpaceDerivative y t i
  let g : Vec3 → ℝ := h0
  have hdf : Continuous (fun y => (fderiv ℝ f y) (CKN.basisVec i)) := by
    rw [show (fun y => (fderiv ℝ f y) (CKN.basisVec i)) =
        fun y => heatKernelSpaceDerivative y t i by
      funext y
      dsimp [f]
      exact heatKernel_fderiv_apply_basisVec ht i]
    exact hk1 i
  have hdf1 : Continuous (fun y => (fderiv ℝ f1 y) (CKN.basisVec i)) := by
    rw [show (fun y => (fderiv ℝ f1 y) (CKN.basisVec i)) =
        fun y => heatKernelSpaceSecondDerivative y t i by
      funext y
      dsimp [f1]
      exact heatKernelSpaceDerivative_fderiv_apply_basisVec ht i]
    exact hk2 i
  have hdg : Continuous (fun y => (fderiv ℝ g y) (CKN.basisVec i)) := by
    rw [show (fun y => (fderiv ℝ g y) (CKN.basisVec i)) =
        fun y => -CKN.spatialDeriv u i (x - y) by
      funext y
      dsimp [g, h0]
      exact shift_fderiv_apply_basisVec hu x y i]
    exact (h1c i).neg
  have hdgs : HasCompactSupport
      (fun y => (fderiv ℝ g y) (CKN.basisVec i)) := by
    rw [show (fun y => (fderiv ℝ g y) (CKN.basisVec i)) =
        fun y => -CKN.spatialDeriv u i (x - y) by
      funext y
      dsimp [g, h0]
      exact shift_fderiv_apply_basisVec hu x y i]
    exact (h1s i).neg
  have hIBP2 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := f1) (g := g) (v := CKN.basisVec i)
    (hcompact_integrable (fun y => (fderiv ℝ f1 y) (CKN.basisVec i)) g
      hdf1 h0c h0s)
    (hcompact_integrable f1 (fun y => (fderiv ℝ g y) (CKN.basisVec i))
      (hk1 i) hdg hdgs)
    (hcompact_integrable f1 g (hk1 i) h0c h0s)
    (fun z _ => by simpa [f1] using hkernel1_diff i z)
    (fun z _ => hshift_diff u hu z)
  have hIBP3 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := f) (g := fun y : Vec3 => CKN.spatialDeriv u i (x - y))
    (v := CKN.basisVec i)
    (hcompact_integrable (fun y => (fderiv ℝ f y) (CKN.basisVec i))
      (fun y : Vec3 => CKN.spatialDeriv u i (x - y)) hdf (h1c i) (h1s i))
    (hcompact_integrable f
      (fun y => (fderiv ℝ (fun z : Vec3 => CKN.spatialDeriv u i (x - z)) y)
        (CKN.basisVec i)) hk
      (by
        exact (by
          rw [show (fun y : Vec3 =>
              (fderiv ℝ (fun z : Vec3 => CKN.spatialDeriv u i (x - z)) y)
                (CKN.basisVec i)) =
              fun y => -CKN.spatialDeriv (CKN.spatialDeriv u i) i (x - y) by
            funext y
            exact shift_fderiv_apply_basisVec (hu1 i) x y i]
          exact (h2c i).neg))
      (by
        rw [show (fun y : Vec3 =>
            (fderiv ℝ (fun z : Vec3 => CKN.spatialDeriv u i (x - z)) y)
              (CKN.basisVec i)) =
            fun y => -CKN.spatialDeriv (CKN.spatialDeriv u i) i (x - y) by
          funext y
          exact shift_fderiv_apply_basisVec (hu1 i) x y i]
        exact (h2s i).neg))
    (hcompact_integrable f (fun y : Vec3 => CKN.spatialDeriv u i (x - y))
      hk (h1c i) (h1s i))
    (fun z _ => by simpa [f] using hkernel_diff z)
    (fun z _ => hshift_diff (CKN.spatialDeriv u i) (hu1 i) z)
  have hsecond : ∫ y : Vec3, (fderiv ℝ f1 y) (CKN.basisVec i) * g y =
      ∫ y : Vec3, f1 y * CKN.spatialDeriv u i (x - y) := by
    have h := hIBP2
    have hderivg : (fun y : Vec3 => (fderiv ℝ g y) (CKN.basisVec i)) =
        fun y => -CKN.spatialDeriv u i (x - y) := by
      funext y
      dsimp [g, h0]
      exact shift_fderiv_apply_basisVec hu x y i
    have hrewrite :
        (∫ y : Vec3, f1 y * (fderiv ℝ g y) (CKN.basisVec i)) =
          -∫ y : Vec3, f1 y * CKN.spatialDeriv u i (x - y) := by
      calc
        ∫ y : Vec3, f1 y * (fderiv ℝ g y) (CKN.basisVec i) =
            ∫ y : Vec3, f1 y * (-CKN.spatialDeriv u i (x - y)) := by
              apply integral_congr_ae
              filter_upwards [] with y
              rw [congrFun hderivg y]
        _ = -∫ y : Vec3, f1 y * CKN.spatialDeriv u i (x - y) := by
          simp only [mul_neg, integral_neg]
    linarith only [h, hrewrite]
  have hthird : ∫ y : Vec3, (fderiv ℝ f y) (CKN.basisVec i) *
      CKN.spatialDeriv u i (x - y) =
      ∫ y : Vec3, f y * CKN.spatialDeriv (CKN.spatialDeriv u i) i (x - y) := by
    have h := hIBP3
    have hderivh :
        (fun y : Vec3 => (fderiv ℝ (fun z : Vec3 =>
          CKN.spatialDeriv u i (x - z)) y) (CKN.basisVec i)) =
        fun y => -CKN.spatialDeriv (CKN.spatialDeriv u i) i (x - y) := by
      funext y
      exact shift_fderiv_apply_basisVec (hu1 i) x y i
    have hrewrite :
        (∫ y : Vec3, f y *
          (fderiv ℝ (fun z : Vec3 => CKN.spatialDeriv u i (x - z)) y)
            (CKN.basisVec i)) =
          -∫ y : Vec3, f y *
            CKN.spatialDeriv (CKN.spatialDeriv u i) i (x - y) := by
      calc
        ∫ y : Vec3, f y *
            (fderiv ℝ (fun z : Vec3 => CKN.spatialDeriv u i (x - z)) y)
              (CKN.basisVec i) =
            ∫ y : Vec3, f y *
              (-CKN.spatialDeriv (CKN.spatialDeriv u i) i (x - y)) := by
                apply integral_congr_ae
                filter_upwards [] with y
                rw [congrFun hderivh y]
        _ = -∫ y : Vec3, f y *
            CKN.spatialDeriv (CKN.spatialDeriv u i) i (x - y) := by
          simp only [mul_neg, integral_neg]
    linarith only [h, hrewrite]
  dsimp [f, f1, g, h0] at hsecond hthird ⊢
  calc
    ∫ y : Vec3, heatKernelSpaceSecondDerivative y t i * h0 y =
        ∫ y : Vec3, (fderiv ℝ f1 y) (CKN.basisVec i) * g y := by
          apply integral_congr_ae
          filter_upwards [] with y
          rw [heatKernelSpaceDerivative_fderiv_apply_basisVec ht i]
    _ = ∫ y : Vec3, f1 y * CKN.spatialDeriv u i (x - y) := hsecond
    _ = ∫ y : Vec3, (fderiv ℝ f y) (CKN.basisVec i) *
        CKN.spatialDeriv u i (x - y) := by
          apply integral_congr_ae
          filter_upwards [] with y
          rw [heatKernel_fderiv_apply_basisVec ht i]
    _ = ∫ y : Vec3, f y * CKN.spatialDeriv (CKN.spatialDeriv u i) i (x - y) := hthird
    _ = ∫ y : Vec3, heatKernel y t *
        CKN.spatialDeriv (CKN.spatialDeriv u i) i (x - y) := rfl

/-- Integration by parts moves the heat-kernel Laplacian onto a compactly supported function. -/
theorem heatKernel_laplacian_integral_eq_smooth {u : Vec3 → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huSupport : HasCompactSupport u)
    {t : ℝ} (ht : 0 < t) (x : Vec3) :
    (∫ y : Vec3, heatKernelLaplacian y t * u (x - y)) =
      heatConv t (CKN.spatialLaplacian u) x := by
  have hk : Continuous (fun y : Vec3 => heatKernel y t) := by
    rw [show (fun y : Vec3 => heatKernel y t) = fun y : Vec3 =>
        (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
          Real.exp (-(∑ j, y j ^ 2) / (4 * t)) by
      funext y
      exact heatKernel_eq_formula_sum ht]
    fun_prop (disch := positivity)
  have hk1 (i : Fin 3) : Continuous
      (fun y : Vec3 => heatKernelSpaceDerivative y t i) := by
    rw [show (fun y : Vec3 => heatKernelSpaceDerivative y t i) = fun y : Vec3 =>
        -(y i) / (2 * t) *
          ((4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
            Real.exp (-(∑ j, y j ^ 2) / (4 * t))) by
      funext y
      rw [heatKernelSpaceDerivative, ite_eq_left ht,
        heatKernel_eq_formula_sum ht]]
    fun_prop (disch := positivity)
  have hk2 (i : Fin 3) : Continuous
      (fun y : Vec3 => heatKernelSpaceSecondDerivative y t i) := by
    rw [show (fun y : Vec3 => heatKernelSpaceSecondDerivative y t i) = fun y : Vec3 =>
        ((y i) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) *
          ((4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
            Real.exp (-(∑ j, y j ^ 2) / (4 * t))) by
      funext y
      rw [heatKernelSpaceSecondDerivative, ite_eq_left ht,
        heatKernel_eq_formula_sum ht]]
    fun_prop (disch := positivity)
  let h0 : Vec3 → ℝ := fun y => u (x - y)
  have h0c : Continuous h0 := by
    dsimp [h0]
    fun_prop
  have h0s : HasCompactSupport h0 := by
    dsimp [h0]
    exact huSupport.comp_homeomorph (Homeomorph.subLeft x)
  have hu1 (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (CKN.spatialDeriv u i) := by
    have h := hu.contDiff_fderiv_apply (m := (⊤ : ℕ∞))
      (n := (⊤ : ℕ∞)) (by simp)
    have hc : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Vec3 => (x, CKN.basisVec i)) := by
      fun_prop
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec3 => (fderiv ℝ u x) (CKN.basisVec i))
    simpa only [CKN.spatialDeriv, Function.comp_def] using h.comp hc
  have hu2 (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (CKN.spatialDeriv (CKN.spatialDeriv u i) i) := by
    have h := (hu1 i).contDiff_fderiv_apply (m := (⊤ : ℕ∞))
      (n := (⊤ : ℕ∞)) (by simp)
    have hc : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Vec3 => (x, CKN.basisVec i)) := by
      fun_prop
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec3 => (fderiv ℝ (CKN.spatialDeriv u i) x) (CKN.basisVec i))
    simpa only [CKN.spatialDeriv, Function.comp_def] using h.comp hc
  have h1c (i : Fin 3) : Continuous
      (fun y : Vec3 => CKN.spatialDeriv u i (x - y)) := by
    exact (hu1 i).continuous.comp (by fun_prop)
  have h1s (i : Fin 3) : HasCompactSupport
      (fun y : Vec3 => CKN.spatialDeriv u i (x - y)) := by
    exact (huSupport.fderiv_apply (𝕜 := ℝ) (CKN.basisVec i)).comp_homeomorph
      (Homeomorph.subLeft x)
  have h2c (i : Fin 3) : Continuous
      (fun y : Vec3 => CKN.spatialDeriv (CKN.spatialDeriv u i) i (x - y)) := by
    exact (hu2 i).continuous.comp (by fun_prop)
  have h2s (i : Fin 3) : HasCompactSupport
      (fun y : Vec3 => CKN.spatialDeriv (CKN.spatialDeriv u i) i (x - y)) := by
    exact ((huSupport.fderiv_apply (𝕜 := ℝ) (CKN.basisVec i)).fderiv_apply
      (𝕜 := ℝ) (CKN.basisVec i)).comp_homeomorph (Homeomorph.subLeft x)
  have hkernel_diff (y : Vec3) : DifferentiableAt ℝ
      (fun z : Vec3 => heatKernel z t) y := by
    rw [show (fun z : Vec3 => heatKernel z t) = fun z : Vec3 =>
        (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
          Real.exp (-(∑ j, z j ^ 2) / (4 * t)) by
      funext z
      exact heatKernel_eq_formula_sum ht]
    fun_prop (disch := positivity)
  have hkernel1_diff (i : Fin 3) (y : Vec3) : DifferentiableAt ℝ
      (fun z : Vec3 => heatKernelSpaceDerivative z t i) y := by
    rw [show (fun z : Vec3 => heatKernelSpaceDerivative z t i) = fun z : Vec3 =>
        -(z i) / (2 * t) *
          ((4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
            Real.exp (-(∑ j, z j ^ 2) / (4 * t))) by
      funext z
      rw [heatKernelSpaceDerivative, ite_eq_left ht,
        heatKernel_eq_formula_sum ht]]
    fun_prop (disch := positivity)
  have hshift_diff (v : Vec3 → ℝ) (hv : ContDiff ℝ (⊤ : ℕ∞) v) (y : Vec3) :
      DifferentiableAt ℝ (fun z : Vec3 => v (x - z)) y := by
    have hvd : Differentiable ℝ v := hv.differentiable (by simp)
    have houter : HasFDerivAt v (fderiv ℝ v (x - y)) (x - y) :=
      (hvd (x - y)).hasFDerivAt
    have hinner : HasFDerivAt (fun z : Vec3 => x - z)
        (-ContinuousLinearMap.id ℝ Vec3) y := by
      convert (hasFDerivAt_const x y).sub (hasFDerivAt_id y) using 1
      · funext z
        rfl
      · ext z
        simp
    exact (HasFDerivAt.comp y houter hinner).differentiableAt
  have hcompact_integrable (f g : Vec3 → ℝ) (hf : Continuous f)
      (hg : Continuous g) (hgs : HasCompactSupport g) :
      Integrable (fun y : Vec3 => f y * g y) volume := by
    exact hf.mul hg |>.integrable_of_hasCompactSupport hgs.mul_left
  have hi (i : Fin 3) := @heatKernel_laplacian_integral_eq_smooth_hi_1 u hu t ht x hk hk1 hk2 h0c
    h0s hu1 h1c h1s h2c h2s hkernel_diff hkernel1_diff hshift_diff hcompact_integrable i
  have hInt : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      Integrable (fun y : Vec3 => heatKernelSpaceSecondDerivative y t i * h0 y) volume := by
    intro i hi
    exact (hk2 i).mul h0c |>.integrable_of_hasCompactSupport h0s.mul_left
  have hInt' : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      Integrable (fun y : Vec3 => heatKernel y t *
        CKN.spatialDeriv (CKN.spatialDeriv u i) i (x - y)) volume := by
    intro i hi
    exact hk.mul (h2c i) |>.integrable_of_hasCompactSupport (h2s i).mul_left
  simp only [heatKernelLaplacian]
  rw [show (fun y : Vec3 => (∑ i, heatKernelSpaceSecondDerivative y t i) *
      u (x - y)) = fun y => ∑ i, heatKernelSpaceSecondDerivative y t i * u (x - y) by
    funext y
    rw [Finset.sum_mul]]
  change (∫ y : Vec3, ∑ i, heatKernelSpaceSecondDerivative y t i * h0 y) = _
  rw [MeasureTheory.integral_finsetSum (s := Finset.univ) hInt]
  calc
    ∑ i : Fin 3, ∫ y : Vec3,
        heatKernelSpaceSecondDerivative y t i * h0 y =
        ∑ i : Fin 3, ∫ y : Vec3, heatKernel y t *
          CKN.spatialDeriv (CKN.spatialDeriv u i) i (x - y) := by
      apply Finset.sum_congr rfl
      intro i hmem
      exact hi i
    _ = ∫ y : Vec3, ∑ i : Fin 3, heatKernel y t *
        CKN.spatialDeriv (CKN.spatialDeriv u i) i (x - y) := by
      rw [MeasureTheory.integral_finsetSum (s := Finset.univ) hInt']
    _ = heatConv t (CKN.spatialLaplacian u) x := by
      rw [heatConv_eq_integral]
      apply integral_congr_ae
      filter_upwards [] with y
      rw [CKN.spatialLaplacian]
      rw [Finset.mul_sum]


lemma heatKernel_integral_Ioi {x : Vec3} (hx : x ≠ 0) :
    ∫ t : ℝ in Ioi 0, heatKernel x t =
      1 / (4 * Real.pi * vec3EuclideanNorm x) := by
  have hr : 0 < vec3EuclideanNorm x := by
    rw [vec3EuclideanNorm_eq_l2]
    apply norm_pos_iff.mpr
    intro hzero
    apply hx
    exact (WithLp.toLp_injective 2) hzero
  let b : ℝ := (vec3EuclideanNorm x) ^ 2 / 4
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hheat : (fun t : ℝ => heatKernel x t) =ᵐ[volume.restrict (Ioi 0)]
      (fun t => (4 * Real.pi) ^ (-(3 : ℝ) / 2) *
        (t ^ (-(3 : ℝ) / 2) * Real.exp (-b * t⁻¹))) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have htpos : 0 < t := ht
    rw [heatKernel_eq_formula htpos]
    dsimp [b]
    rw [show 4 * Real.pi * t = (4 * Real.pi) * t by ring_nf,
      Real.mul_rpow (by positivity) htpos.le]
    have hexp : -vec3EuclideanNorm x ^ 2 / (4 * t) =
        -(vec3EuclideanNorm x) ^ 2 / 4 * t⁻¹ := by
      field_simp
    rw [hexp]
    ring_nf
  rw [integral_congr_ae hheat, integral_const_mul]
  have hsub := integral_comp_rpow_Ioi
    (fun y : ℝ => y ^ (-(1 : ℝ) / 2) * Real.exp (-b * y))
    (p := -(1 : ℝ)) (by norm_num)
  have hsub' :
      (∫ t : ℝ in Ioi 0, t ^ (-(3 : ℝ) / 2) * Real.exp (-b * t⁻¹)) =
        ∫ y : ℝ in Ioi 0, y ^ (-(1 : ℝ) / 2) * Real.exp (-b * y) := by
    rw [← hsub]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have htpos : 0 < t := ht
    rw [smul_eq_mul]
    simp only [abs_neg, abs_one, one_mul]
    rw [← Real.rpow_mul htpos.le]
    have hpow : t ^ (-(1 : ℝ) - 1) * t ^ (-(1 : ℝ) * (-(1 : ℝ) / 2)) =
        t ^ (-(3 : ℝ) / 2) := by
      calc
        t ^ (-(1 : ℝ) - 1) * t ^ (-(1 : ℝ) * (-(1 : ℝ) / 2)) =
            t ^ ((-(1 : ℝ) - 1) + (-(1 : ℝ) * (-(1 : ℝ) / 2))) :=
          (Real.rpow_add htpos _ _).symm
        _ = t ^ (-(3 : ℝ) / 2) := by
          congr 1
          ring_nf
    calc
      t ^ (-(3 : ℝ) / 2) * Real.exp (-b * t⁻¹) =
          (t ^ (-(1 : ℝ) - 1) * t ^ (-(1 : ℝ) * (-(1 : ℝ) / 2))) *
            Real.exp (-b * t⁻¹) := by rw [hpow]
      _ = t ^ (-(1 : ℝ) - 1) *
          (t ^ (-(1 : ℝ) * (-(1 : ℝ) / 2)) * Real.exp (-b * t⁻¹)) := by
        ring_nf
      _ = t ^ (-(1 : ℝ) - 1) *
          (t ^ (-(1 : ℝ) * (-(1 : ℝ) / 2)) * Real.exp (-b * t ^ (-(1 : ℝ)))) := by
        rw [Real.rpow_neg htpos.le, Real.rpow_one]
  rw [hsub']
  have hgamma := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := -(1 : ℝ) / 2)
    (b := b) (by norm_num) (by norm_num) hb
  have hgamma' :
      (∫ y : ℝ in Ioi 0, y ^ (-(1 : ℝ) / 2) * Real.exp (-b * y)) =
        b ^ (-( -(1 : ℝ) / 2 + 1) / 1) * (1 / 1) * Real.Gamma
          ((-(1 : ℝ) / 2 + 1) / 1) := by
    simpa only [Real.rpow_one] using hgamma
  rw [hgamma']
  norm_num only [one_div, div_one, neg_div, neg_neg]
  rw [Real.Gamma_one_half_eq]
  dsimp [b]
  have hrpow : (vec3EuclideanNorm x ^ 2 / 4) ^ (-(1 : ℝ) / 2) =
      2 / vec3EuclideanNorm x := by
    rw [Real.div_rpow (sq_nonneg _) (by norm_num)]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    have hexp : (↑(2 : ℕ) : ℝ) * (-(1 : ℝ) / 2) = -1 := by norm_num
    rw [hexp, Real.rpow_neg hr.le, Real.rpow_one]
    rw [show (-(1 : ℝ) / 2) = -(1 / 2 : ℝ) by ring_nf,
      Real.rpow_neg (by norm_num : 0 ≤ (4 : ℝ)), ← Real.sqrt_eq_rpow]
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (by norm_num)]
    field_simp
  have hrpow' : (vec3EuclideanNorm x ^ 2 / 4) ^ (-(1 / 2 : ℝ)) =
      2 / vec3EuclideanNorm x := by
    convert hrpow using 1
    ring_nf
  rw [hrpow']
  have hbase : (4 * Real.pi) ^ (-(3 / 2 : ℝ)) =
      (8 * Real.pi * Real.sqrt Real.pi)⁻¹ := by
    rw [show -(3 / 2 : ℝ) = -((3 : ℝ) / 2) by ring_nf,
      Real.rpow_neg (by positivity)]
    have hpow : (4 * Real.pi) ^ ((3 : ℝ) / 2) =
        8 * Real.pi * Real.sqrt Real.pi := by
      rw [show (3 : ℝ) / 2 = 1 + (1 / 2 : ℝ) by ring_nf,
        Real.rpow_add (by positivity), Real.rpow_one, Real.sqrt_eq_rpow,
        Real.mul_rpow (by norm_num) (by positivity)]
      have hfour : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
        rw [← Real.sqrt_eq_rpow]
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.sqrt_sq_eq_abs,
          abs_of_nonneg (by norm_num)]
      rw [hfour]
      ring_nf
    rw [hpow]
  rw [hbase]
  field_simp
  ring_nf

end CKN.Foundation.Heat
