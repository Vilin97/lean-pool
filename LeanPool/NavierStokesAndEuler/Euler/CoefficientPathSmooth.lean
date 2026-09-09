/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CoefficientPathOrbit
public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderRectangular
public import LeanPool.NavierStokesAndEuler.Euler.AllOrderCorrectionData

@[expose] public section

/-! Genuine bounded smooth cylinder coefficients and all their derivative
jets are constructed from the actual coefficient translation orbit. -/

noncomputable section

namespace EulerCoefficientPath

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerMeanCoefficients EulerMetricTransport EulerTransportDerivatives
  EulerSpatialSobolevInverse EulerCylinderSobolev EulerLpCylinderRectangular
open scoped ContDiff BoundedContinuousFunction

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

section General

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

private local instance : NormedAddCommGroup (Space →ᵇ V) := inferInstance
private local instance : NormedSpace ℝ (Space →ᵇ V) := inferInstance

theorem cylinder_norm_iteratedFDeriv_le (P : ℝ) (A : C(K, Space →ᵇ V))
    (hA : ContDiff ℝ ∞ (translateCoefficientPath A))
    (n : ℕ) (t : K) (x : LiftDomain P) (y : LiftTangent) :
    ‖iteratedFDeriv ℝ n (localFieldLift P (fun z : LiftDomain P => A t z.1) x) y‖ ≤
      ‖iteratedFDeriv ℝ n (translateCoefficientPath A) 0‖ := by
  let f : Space → V := fun z => A t (x.1+z)
  have hf : ContDiff ℝ ∞ f :=
    (coefficientOrbit_smooth A hA t).comp (contDiff_const.add contDiff_id)
  have he : localFieldLift P (fun z : LiftDomain P => A t z.1) x =
      f ∘ (ContinuousLinearMap.fst ℝ Space ℝ) := rfl
  rw [he,(ContinuousLinearMap.fst ℝ Space ℝ).iteratedFDeriv_comp_right hf y (by simp)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  calc
    _ ≤ ‖iteratedFDeriv ℝ n f y.1‖ * ∏ _i : Fin n, (1 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        (fun _ _ => ContinuousLinearMap.norm_fst_le ℝ Space ℝ)
    _ = ‖iteratedFDeriv ℝ n f y.1‖ := by simp only [Finset.prod_const_one,mul_one]
    _ = ‖iteratedFDeriv ℝ n (A t : Space → V) (x.1+y.1)‖ := by
      dsimp only [f]
      rw [iteratedFDeriv_comp_add_left]
    _ ≤ _ := coefficientOrbit_norm_iteratedFDeriv_le A hA n t (x.1+y.1)

theorem cylinder_fieldDerivative (P : ℝ) (A : C(K, Space →ᵇ V))
    (hA : ContDiff ℝ ∞ (translateCoefficientPath A))
    (t : K) (v : LiftTangent) (x : LiftDomain P) :
    fieldDerivative P v (fun z : LiftDomain P => A t z.1) x =
      orbitDerivativePath A v.1 t x.1 := by
  rw [orbitDerivativePath_apply A hA]
  have hi : HasFDerivAt (fun h : LiftTangent => x.1+h.1)
      (ContinuousLinearMap.fst ℝ Space ℝ) 0 :=
    (hasFDerivAt_fst : HasFDerivAt (Prod.fst : LiftTangent → Space)
      (ContinuousLinearMap.fst ℝ Space ℝ) 0).const_add x.1
  have hd := ((coefficientOrbit_smooth A hA t).differentiable (by simp)
    (x.1+(0 : LiftTangent).1)).hasFDerivAt.comp (0 : LiftTangent) hi
  have he := congrArg (fun L : LiftTangent →L[ℝ] V => L v) hd.fderiv
  change (fderiv ℝ (fun h : LiftTangent => A t (x.1+h.1)) 0) v = _
  simpa only [Function.comp_def,Prod.fst_zero,add_zero,comp_apply,
    ContinuousLinearMap.coe_fst'] using he

end General

private local instance : NormedAddCommGroup (Space →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (Space →L[ℝ] Space) := inferInstance
private local instance : NormedAddCommGroup (Space →ᵇ Space →L[ℝ] Space) := inferInstance
private local instance : NormedSpace ℝ (Space →ᵇ Space →L[ℝ] Space) := inferInstance

section Basic

variable (P : ℝ) [Fact (0 < P)]
  (A : C(K, Space →ᵇ Space →L[ℝ] Space))
  (hA : ContDiff ℝ ∞ (translateCoefficientPath A))

def smoothCoefficient (t : K) : SmoothCoefficient P where
  coefficient x := A t x.1
  smooth x := (coefficientOrbit_smooth A hA t).comp (contDiff_const.add contDiff_fst)
  bound := ‖A t‖₊
  norm_bound x := (A t).norm_coe_le_norm x.1
  firstBound := ‖iteratedFDeriv ℝ 1 (translateCoefficientPath A) 0‖₊
  norm_first x := by
    rw [← norm_iteratedFDeriv_one]
    exact cylinder_norm_iteratedFDeriv_le P A hA 1 t x 0
  secondBound := ‖iteratedFDeriv ℝ 2 (translateCoefficientPath A) 0‖₊
  norm_second x y := by
    rw [← norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv]
    exact cylinder_norm_iteratedFDeriv_le P A hA 2 t x y

omit [Fact (0 < P)] in
@[simp] theorem smoothCoefficient_apply (t : K) (x : LiftDomain P) :
    (smoothCoefficient P A hA t).coefficient x = A t x.1 := rfl

end Basic

def coefficientJet (P : ℝ) [Fact (0 < P)]
    (A : C(K, Space →ᵇ Space →L[ℝ] Space))
    (hA : ContDiff ℝ ∞ (translateCoefficientPath A)) (q : ℕ) (t : K) :
    CoefficientJet P standardDirection q (smoothCoefficient P A hA t) :=
  match q with
  | 0 => .zero _
  | n+1 => .succ
      (fun i => smoothCoefficient P (orbitDerivativePath A (standardDirection i).1)
        (orbitDerivativePath_orbit A hA (standardDirection i).1) t)
      (fun i => coefficientJet P (orbitDerivativePath A (standardDirection i).1)
        (orbitDerivativePath_orbit A hA (standardDirection i).1) n t)
      (fun i x => (cylinder_fieldDerivative P A hA t (standardDirection i) x).symm)

variable (P : ℝ) [Fact (0 < P)]
  (A : C(K, Space →ᵇ Space →L[ℝ] Space))
  (hA : ContDiff ℝ ∞ (translateCoefficientPath A))

theorem smoothCoefficient_operator (t : K) :
    (smoothCoefficient P A hA t).operator = fullOperatorMap P (A t) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [(smoothCoefficient P A hA t).operator_ae f,
    EulerLpOperatorField.full_ae (liftMeasure P) (EulerLpCylinderTranslation.fieldLift P (A t)) f]
    with x h₁ h₂
  exact h₁.trans h₂.symm

theorem smoothCoefficient_operator_continuous :
    Continuous (fun t => (smoothCoefficient P A hA t).operator) := by
  simp_rw [smoothCoefficient_operator]
  exact (fullOperatorMap P).continuous.comp A.continuous

end EulerCoefficientPath
