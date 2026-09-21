/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.LimitHessian
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.SummationByParts

/-! # Limit Pairing -/

namespace Homogenization

open scoped Manifold

noncomputable section

namespace WeakPoissonEquationOn

variable {d : ℕ} {V : Set (Vec d)}

private theorem support_h1WeakTest_deriv_subset
    {U : Set (Vec d)} (φ : H1WeakTestFunction U) (j : Fin d) :
    Function.support (fun x => φ.deriv j x) ⊆ U := by
  intro x hx
  exact φ.support_subset <|
    (support_fderiv_subset (𝕜 := ℝ) (f := (φ : Vec d → ℝ))) <| by
      change fderiv ℝ (φ : Vec d → ℝ) x ≠ 0
      intro hzero
      apply hx
      simp [H1WeakTestFunction.deriv, hzero]

private theorem continuous_h1WeakTest_deriv
    {U : Set (Vec d)} (φ : H1WeakTestFunction U) (j : Fin d) :
    Continuous (fun x => φ.deriv j x) := by
  simpa [H1WeakTestFunction.deriv] using
    (φ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const

private theorem hasCompactSupport_h1WeakTest_deriv
    {U : Set (Vec d)} (φ : H1WeakTestFunction U) (j : Fin d) :
    HasCompactSupport (fun x => φ.deriv j x) := by
  simpa [H1WeakTestFunction.deriv] using
    φ.compactSupport.fderiv_apply (𝕜 := ℝ) (basisVec j)

private theorem contDiff_h1WeakTest_deriv
    {U : Set (Vec d)} (φ : H1WeakTestFunction U) (j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => φ.deriv j x) := by
  simpa [H1WeakTestFunction.deriv, euclideanCoordDeriv] using!
    contDiff_euclideanCoordDeriv φ.smooth j

private theorem tsupport_h1WeakTest_deriv_subset
    {U : Set (Vec d)} (φ : H1WeakTestFunction U) (j : Fin d) :
    tsupport (fun x => φ.deriv j x) ⊆ U := by
  have hsub :
      tsupport (euclideanCoordDeriv j (φ : Vec d → ℝ)) ⊆
        tsupport (φ : Vec d → ℝ) :=
    tsupport_euclideanCoordDeriv_subset_tsupport j (φ : Vec d → ℝ)
  simpa [H1WeakTestFunction.deriv, euclideanCoordDeriv] using!
    hsub.trans φ.support_subset

private theorem support_fderiv_h1WeakTest_deriv_apply_subset
    {U : Set (Vec d)} (φ : H1WeakTestFunction U) (i j : Fin d) :
    Function.support
        (fun x => (fderiv ℝ (fun y => φ.deriv j y) x) (basisVec i)) ⊆ U := by
  intro x hx
  exact tsupport_h1WeakTest_deriv_subset φ j <|
    (support_fderiv_subset (𝕜 := ℝ) (f := fun y => φ.deriv j y)) <| by
      change fderiv ℝ (fun y => φ.deriv j y) x ≠ 0
      intro hzero
      apply hx
      simp [hzero]

private theorem memScalarL2_h1WeakTest_deriv_of_subset
    {S U : Set (Vec d)} (hS_meas : MeasurableSet S)
    (φ : H1WeakTestFunction S) (j : Fin d) :
    MemScalarL2 U (fun x => φ.deriv j x) := by
  have hderiv_memS : MemScalarL2 S (fun x => φ.deriv j x) := by
    simpa [MemScalarL2, volumeMeasureOn] using
      ((continuous_h1WeakTest_deriv φ j).memLp_of_hasCompactSupport
        (hasCompactSupport_h1WeakTest_deriv φ j)).restrict S
  exact
    memLp_restrict_of_support_subset_of_memLp
      (U := U) (V := S) hS_meas
      (support_h1WeakTest_deriv_subset φ j) hderiv_memS

private theorem integrable_mul_h1Function_h1WeakTest_deriv_of_subset
    {S U : Set (Vec d)} (hS_meas : MeasurableSet S)
    (u : H1Function U) (φ : H1WeakTestFunction S) (j : Fin d)
    (hSU : S ⊆ U) :
    MeasureTheory.Integrable (fun x => u.toFun x * φ.deriv j x)
      MeasureTheory.volume := by
  have hderiv_memU :
      MemScalarL2 U (fun x => φ.deriv j x) :=
    memScalarL2_h1WeakTest_deriv_of_subset hS_meas φ j
  have hprodU :
      MeasureTheory.IntegrableOn (fun x => u.toFun x * φ.deriv j x) U
        MeasureTheory.volume := by
    simpa [MeasureTheory.IntegrableOn, MemL2On, MemScalarL2, volumeMeasureOn]
      using! u.memL2.integrable_mul hderiv_memU
  have hprod_support :
      Function.support (fun x => u.toFun x * φ.deriv j x) ⊆ U :=
    (Function.support_mul_subset_right u.toFun (fun x => φ.deriv j x)).trans
      ((support_h1WeakTest_deriv_subset φ j).trans hSU)
  exact
    (MeasureTheory.integrableOn_iff_integrable_of_support_subset hprod_support).mp
      hprodU

private theorem integrable_shifted_h1Function_mul_h1WeakTest_deriv
    {S U : Set (Vec d)} (hS_meas : MeasurableSet S)
    (u : H1Function U) (φ : H1WeakTestFunction S) {step : ℝ} (i j : Fin d)
    (hSshift : ∀ x ∈ S, euclideanCoordShift step i x ∈ U) :
    MeasureTheory.Integrable
      (fun x => u.toFun (euclideanCoordShift step i x) * φ.deriv j x)
      MeasureTheory.volume := by
  let z : Vec d := (-step) • basisVec i
  have hS_translate : S ⊆ translateSet z U := by
    intro x hx
    rw [mem_translateSet_iff_sub_mem]
    simpa [z, euclideanCoordShift, sub_eq_add_neg, neg_smul] using hSshift x hx
  have hshift_memS :
      MemScalarL2 S (fun x => u.toFun (euclideanCoordShift step i x)) := by
    have hmono :
        MeasureTheory.MemLp (fun x => (u.translate z).toFun x) 2
          (MeasureTheory.volume.restrict S) :=
      (u.translate z).memL2.mono_measure
        (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hS_translate)
    simpa [MemScalarL2, MemL2On, volumeMeasureOn, z, euclideanCoordShift,
      sub_eq_add_neg, neg_smul] using hmono
  have hderiv_memS : MemScalarL2 S (fun x => φ.deriv j x) :=
    memScalarL2_h1WeakTest_deriv_of_subset hS_meas φ j
  have hprodS :
      MeasureTheory.IntegrableOn
        (fun x => u.toFun (euclideanCoordShift step i x) * φ.deriv j x) S
        MeasureTheory.volume := by
    simpa [MeasureTheory.IntegrableOn, MemScalarL2, volumeMeasureOn]
      using! hshift_memS.integrable_mul hderiv_memS
  have hprod_support :
      Function.support
        (fun x => u.toFun (euclideanCoordShift step i x) * φ.deriv j x) ⊆ S :=
    (Function.support_mul_subset_right
      (fun x => u.toFun (euclideanCoordShift step i x))
      (fun x => φ.deriv j x)).trans
      (support_h1WeakTest_deriv_subset φ j)
  exact
    (MeasureTheory.integrableOn_iff_integrable_of_support_subset hprod_support).mp
      hprodS

private theorem support_forwardDifferenceQuotient_mul_h1WeakTest_deriv_subset
    {U : Set (Vec d)} {u : Vec d → ℝ} (step : ℝ) (i j : Fin d)
    (φ : H1WeakTestFunction U) :
    Function.support
        (fun x => euclideanForwardDifferenceQuotient step i u x * φ.deriv j x)
        ⊆ U := by
  intro x hx
  have hderiv_ne : φ.deriv j x ≠ 0 := by
    intro hzero
    apply hx
    simp [hzero]
  exact support_h1WeakTest_deriv_subset φ j hderiv_ne

private theorem support_h1WeakTest_deriv_comp_coordShift_neg_subset
    {S U V : Set (Vec d)} {step : ℝ} (i j : Fin d)
    (φ : H1WeakTestFunction S) (hSV : S ⊆ V)
    (hVshift : ∀ x ∈ V, euclideanCoordShift step i x ∈ U) :
    Function.support
        (fun x => φ.deriv j (euclideanCoordShift (-step) i x)) ⊆ U := by
  intro x hx
  have hpreS :
      euclideanCoordShift (-step) i x ∈ S :=
    support_h1WeakTest_deriv_subset φ j hx
  have hxU :
      euclideanCoordShift step i (euclideanCoordShift (-step) i x) ∈ U :=
    hVshift (euclideanCoordShift (-step) i x) (hSV hpreS)
  simpa using hxU

private theorem integrable_mul_h1Function_h1WeakTest_deriv_comp_coordShift_neg
    {S U V : Set (Vec d)} {step : ℝ}
    (u : H1Function U) (φ : H1WeakTestFunction S) (i j : Fin d)
    (hSV : S ⊆ V)
    (hVshift : ∀ x ∈ V, euclideanCoordShift step i x ∈ U) :
    MeasureTheory.Integrable
      (fun x => u.toFun x * φ.deriv j (euclideanCoordShift (-step) i x))
      MeasureTheory.volume := by
  have hderiv_shift_cont :
      Continuous (fun x => φ.deriv j (euclideanCoordShift (-step) i x)) :=
    (continuous_h1WeakTest_deriv φ j).comp
      (continuous_id.add continuous_const)
  have hderiv_shift_compact :
      HasCompactSupport (fun x => φ.deriv j (euclideanCoordShift (-step) i x)) :=
    hasCompactSupport_comp_euclideanCoordShift
      (hasCompactSupport_h1WeakTest_deriv φ j) (-step) i
  have hderiv_shift_memU :
      MemScalarL2 U
        (fun x => φ.deriv j (euclideanCoordShift (-step) i x)) := by
    simpa [MemScalarL2, volumeMeasureOn] using
      (hderiv_shift_cont.memLp_of_hasCompactSupport hderiv_shift_compact).restrict U
  have hprodU :
      MeasureTheory.IntegrableOn
        (fun x => u.toFun x * φ.deriv j (euclideanCoordShift (-step) i x)) U
        MeasureTheory.volume := by
    simpa [MeasureTheory.IntegrableOn, MemL2On, MemScalarL2, volumeMeasureOn]
      using! u.memL2.integrable_mul hderiv_shift_memU
  have hprod_support :
      Function.support
        (fun x => u.toFun x * φ.deriv j (euclideanCoordShift (-step) i x))
        ⊆ U :=
    (Function.support_mul_subset_right u.toFun
      (fun x => φ.deriv j (euclideanCoordShift (-step) i x))).trans
      (support_h1WeakTest_deriv_comp_coordShift_neg_subset i j φ hSV hVshift)
  exact
    (MeasureTheory.integrableOn_iff_integrable_of_support_subset hprod_support).mp
      hprodU

/-- Fixed-step open-inner Hessian pairings can be moved from the forward
quotient on the rough potential to the backward quotient on the smooth test
derivative.

This is the concrete bridge from the quotient estimate to the limiting weak
second derivative: the nonsmooth `H¹` representative appears only as an
`L¹`-paired factor. -/
theorem openCubeInnerOpenCubeQuotientHessianPairing_eq_integral_mul_backwardDifferenceQuotient_deriv
    {Q : TriadicCube d} (uQ : H1Function (openCubeSet Q))
    {step : ℝ} (i j : Fin d) {ρ₁ : ℝ}
    (φ : H1WeakTestFunction (scaledOpenCubeSet Q ρ₁))
    (hSV : scaledOpenCubeSet Q ρ₁ ⊆ V)
    (hshiftInt :
      MeasureTheory.Integrable
        (fun x : Vec d =>
          uQ.toFun (euclideanCoordShift step i x) * φ.deriv j x)
        MeasureTheory.volume)
    (huvInt :
      MeasureTheory.Integrable
        (fun x : Vec d => uQ.toFun x * φ.deriv j x)
        MeasureTheory.volume)
    (hbackShiftInt :
      MeasureTheory.Integrable
        (fun x : Vec d =>
          uQ.toFun x * φ.deriv j (euclideanCoordShift (-step) i x))
        MeasureTheory.volume) :
    openCubeInnerOpenCubeQuotientHessianPairing uQ V step i j φ =
      ∫ x,
        uQ.toFun x *
          euclideanBackwardDifferenceQuotient step i (fun y => φ.deriv j y) x
        ∂MeasureTheory.volume := by
  have hleft_support :
      Function.support
          (fun x =>
            euclideanForwardDifferenceQuotient step i uQ.toFun x * φ.deriv j x)
          ⊆ V :=
    (support_forwardDifferenceQuotient_mul_h1WeakTest_deriv_subset
      (U := scaledOpenCubeSet Q ρ₁) step i j φ).trans hSV
  have hV_eq_univ :
      ∫ x in V,
          euclideanForwardDifferenceQuotient step i uQ.toFun x * φ.deriv j x
          ∂MeasureTheory.volume =
        ∫ x,
          euclideanForwardDifferenceQuotient step i uQ.toFun x * φ.deriv j x
          ∂MeasureTheory.volume := by
    have hsubset :=
      integral_subset_of_support_subset
        (U := (Set.univ : Set (Vec d))) (V := V)
        (Set.subset_univ V) hleft_support
    simpa using hsubset.symm
  have hsbp :
      ∫ x,
          euclideanForwardDifferenceQuotient step i uQ.toFun x * φ.deriv j x
          ∂MeasureTheory.volume =
        -∫ x,
          uQ.toFun x *
            euclideanBackwardDifferenceQuotient step i (fun y => φ.deriv j y) x
          ∂MeasureTheory.volume :=
    integral_euclideanForwardDifferenceQuotient_mul_eq_neg_integral_mul_euclideanBackwardDifferenceQuotient_of_integrable
      (u := uQ.toFun) (v := fun y => φ.deriv j y) step i
      (by simpa using hshiftInt)
      (by simpa using huvInt)
      (by simpa using hbackShiftInt)
  calc
    openCubeInnerOpenCubeQuotientHessianPairing uQ V step i j φ =
        -∫ x in V,
          euclideanForwardDifferenceQuotient step i uQ.toFun x * φ.deriv j x
          ∂MeasureTheory.volume := by
          rfl
    _ = -∫ x,
          euclideanForwardDifferenceQuotient step i uQ.toFun x * φ.deriv j x
          ∂MeasureTheory.volume := by
          rw [hV_eq_univ]
    _ = -(-∫ x,
          uQ.toFun x *
            euclideanBackwardDifferenceQuotient step i (fun y => φ.deriv j y) x
          ∂MeasureTheory.volume) := by
          rw [hsbp]
    _ = ∫ x,
          uQ.toFun x *
            euclideanBackwardDifferenceQuotient step i (fun y => φ.deriv j y) x
          ∂MeasureTheory.volume := by
          ring

/-- Fixed-step pairing rewrite with the L1 hypotheses discharged from the
interior support and one-step cube-margin conditions. -/
theorem openCubeInnerOpenCubeQuotientHessianPairing_eq_integral_mul_backwardDifferenceQuotient_deriv_of_subset_of_shift
    {Q : TriadicCube d} (uQ : H1Function (openCubeSet Q))
    {step : ℝ} (i j : Fin d) {ρ₁ : ℝ}
    (φ : H1WeakTestFunction (scaledOpenCubeSet Q ρ₁))
    (hSV : scaledOpenCubeSet Q ρ₁ ⊆ V)
    (hVU : V ⊆ openCubeSet Q)
    (hVshift : ∀ x ∈ V, euclideanCoordShift step i x ∈ openCubeSet Q) :
    openCubeInnerOpenCubeQuotientHessianPairing uQ V step i j φ =
      ∫ x,
        uQ.toFun x *
          euclideanBackwardDifferenceQuotient step i (fun y => φ.deriv j y) x
        ∂MeasureTheory.volume := by
  have hS_meas : MeasurableSet (scaledOpenCubeSet Q ρ₁) :=
    (isOpen_scaledOpenCubeSet Q ρ₁).measurableSet
  refine
    openCubeInnerOpenCubeQuotientHessianPairing_eq_integral_mul_backwardDifferenceQuotient_deriv
      uQ i j φ hSV ?_ ?_ ?_
  · exact
      integrable_shifted_h1Function_mul_h1WeakTest_deriv
        hS_meas uQ φ i j (fun x hx => hVshift x (hSV hx))
  · exact
      integrable_mul_h1Function_h1WeakTest_deriv_of_subset
        hS_meas uQ φ j (hSV.trans hVU)
  · exact
      integrable_mul_h1Function_h1WeakTest_deriv_comp_coordShift_neg
        uQ φ i j hSV hVshift

/-- The classical limit of the smooth-test summation-by-parts expression is
the desired limiting Hessian pairing. -/
theorem integral_mul_fderiv_h1WeakTest_deriv_eq_openCubeInnerOpenCubeLimitHessianPairing
    {Q : TriadicCube d} (uQ : H1Function (openCubeSet Q))
    (i j : Fin d) {ρ₁ : ℝ}
    (φ : H1WeakTestFunction (scaledOpenCubeSet Q ρ₁))
    (hSV : scaledOpenCubeSet Q ρ₁ ⊆ V)
    (hVU : V ⊆ openCubeSet Q) :
    ∫ x,
        uQ.toFun x *
          (fderiv ℝ (fun y => φ.deriv j y) x) (basisVec i)
        ∂MeasureTheory.volume =
      openCubeInnerOpenCubeLimitHessianPairing uQ V i j φ := by
  let U : Set (Vec d) := openCubeSet Q
  let S : Set (Vec d) := scaledOpenCubeSet Q ρ₁
  let g : Vec d → ℝ := fun y => φ.deriv j y
  have hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g := by
    simpa [g] using contDiff_h1WeakTest_deriv φ j
  have hg_compact : HasCompactSupport g := by
    simpa [g] using hasCompactSupport_h1WeakTest_deriv φ j
  have hg_subU : tsupport g ⊆ U := by
    simpa [g, U, S] using
      (tsupport_h1WeakTest_deriv_subset φ j).trans (hSV.trans hVU)
  have hleft_support :
      Function.support
          (fun x =>
            uQ.toFun x *
              (fderiv ℝ (fun y => φ.deriv j y) x) (basisVec i))
          ⊆ U := by
    refine (Function.support_mul_subset_right uQ.toFun
      (fun x => (fderiv ℝ (fun y => φ.deriv j y) x) (basisVec i))).trans ?_
    simpa [g, U] using
      (support_fderiv_h1WeakTest_deriv_apply_subset φ i j).trans (hSV.trans hVU)
  have hleft_univ_eq_U :
      ∫ x,
          uQ.toFun x *
            (fderiv ℝ (fun y => φ.deriv j y) x) (basisVec i)
          ∂MeasureTheory.volume =
        ∫ x in U,
          uQ.toFun x *
            (fderiv ℝ (fun y => φ.deriv j y) x) (basisVec i)
          ∂MeasureTheory.volume := by
    have hsubset :=
      integral_subset_of_support_subset
        (U := (Set.univ : Set (Vec d))) (V := U)
        (Set.subset_univ U) hleft_support
    simpa [U] using hsubset
  have hweak :
      ∫ x in U,
          uQ.toFun x * (fderiv ℝ g x) (basisVec i)
          ∂MeasureTheory.volume =
        -∫ x in U, uQ.grad x i * g x ∂MeasureTheory.volume := by
    simpa [U] using uQ.hasWeakGradient i g hg_smooth hg_compact hg_subU
  have hright_support :
      Function.support (fun x => uQ.grad x i * φ.deriv j x) ⊆ V :=
    (Function.support_mul_subset_right (fun x => uQ.grad x i)
      (fun x => φ.deriv j x)).trans
      ((support_h1WeakTest_deriv_subset φ j).trans hSV)
  have hright_U_eq_V :
      ∫ x in U, uQ.grad x i * φ.deriv j x ∂MeasureTheory.volume =
        ∫ x in V, uQ.grad x i * φ.deriv j x ∂MeasureTheory.volume := by
    exact integral_subset_of_support_subset
      (U := U) (V := V) (by simpa [U] using hVU) hright_support
  calc
    ∫ x,
        uQ.toFun x *
          (fderiv ℝ (fun y => φ.deriv j y) x) (basisVec i)
        ∂MeasureTheory.volume =
        ∫ x in U,
          uQ.toFun x *
            (fderiv ℝ (fun y => φ.deriv j y) x) (basisVec i)
          ∂MeasureTheory.volume := hleft_univ_eq_U
    _ = ∫ x in U,
          uQ.toFun x * (fderiv ℝ g x) (basisVec i)
          ∂MeasureTheory.volume := by rfl
    _ = -∫ x in U, uQ.grad x i * g x ∂MeasureTheory.volume := hweak
    _ = -∫ x in V, uQ.grad x i * φ.deriv j x ∂MeasureTheory.volume := by
          rw [hright_U_eq_V]
    _ = openCubeInnerOpenCubeLimitHessianPairing uQ V i j φ := by
          rfl

/-- The remaining smooth-test convergence statement implies the
`OpenCubeInnerHessianPairingTendsto` interface consumed by the limiting Riesz
construction. -/
theorem openCubeInnerHessianPairingTendsto_of_integral_backwardDifferenceQuotient_deriv_tendsto
    {Q : TriadicCube d} (uQ : H1Function (openCubeSet Q))
    (stepSeq : ℕ → ℝ) (i j : Fin d) {ρ₁ : ℝ}
    (hSV : scaledOpenCubeSet Q ρ₁ ⊆ V)
    (hVU : V ⊆ openCubeSet Q)
    (hVshift : ∀ n, ∀ x ∈ V,
      euclideanCoordShift (stepSeq n) i x ∈ openCubeSet Q)
    (hback_lim :
      ∀ φ : H1WeakTestFunction (scaledOpenCubeSet Q ρ₁),
        Filter.Tendsto
          (fun n : ℕ =>
            ∫ x,
              uQ.toFun x *
                euclideanBackwardDifferenceQuotient (stepSeq n) i
                  (fun y => φ.deriv j y) x
              ∂MeasureTheory.volume)
          Filter.atTop
          (nhds
            (∫ x,
              uQ.toFun x *
                (fderiv ℝ (fun y => φ.deriv j y) x) (basisVec i)
              ∂MeasureTheory.volume))) :
    OpenCubeInnerHessianPairingTendsto (ρ₁ := ρ₁) uQ V stepSeq i j := by
  intro φ
  have hseq :
      (fun n : ℕ =>
          openCubeInnerOpenCubeQuotientHessianPairing uQ V (stepSeq n) i j φ) =
        fun n : ℕ =>
          ∫ x,
            uQ.toFun x *
              euclideanBackwardDifferenceQuotient (stepSeq n) i
                (fun y => φ.deriv j y) x
            ∂MeasureTheory.volume := by
    funext n
    exact
      openCubeInnerOpenCubeQuotientHessianPairing_eq_integral_mul_backwardDifferenceQuotient_deriv_of_subset_of_shift
        uQ i j φ hSV hVU (hVshift n)
  have htarget :
      ∫ x,
          uQ.toFun x *
            (fderiv ℝ (fun y => φ.deriv j y) x) (basisVec i)
          ∂MeasureTheory.volume =
        openCubeInnerOpenCubeLimitHessianPairing uQ V i j φ :=
    integral_mul_fderiv_h1WeakTest_deriv_eq_openCubeInnerOpenCubeLimitHessianPairing
      uQ i j φ hSV hVU
  simpa [hseq, htarget] using hback_lim φ

end WeakPoissonEquationOn

end

end Homogenization
