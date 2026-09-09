/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryFieldAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryWordBounds
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryH3Norms

@[expose] public section

/-! Literal scalar multiplication of smooth ordinary L² fields and all
of their genuine spatial derivatives. -/

noncomputable section

namespace EulerOrdinarySobolev

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field Finset
open scoped ContDiff

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def scaleField (c : ℝ) (A : SmoothL2Field V) : SmoothL2Field V :=
  mapField (c • ContinuousLinearMap.id ℝ V) A

@[simp] theorem scaleField_field (c : ℝ) (A : SmoothL2Field V) (x : Space) :
    (scaleField c A).field x=c • A.field x := rfl

theorem scaleField_toLp (c : ℝ) (A : SmoothL2Field V) :
    (scaleField c A).toLp=c • A.toLp := by
  apply Lp.ext
  filter_upwards [(scaleField c A).toLp_ae,A.toLp_ae,Lp.coeFn_smul c A.toLp] with x hs ha hc
  rw [hs,scaleField_field,hc,Pi.smul_apply,ha]

theorem scaleField_jetLp (c : ℝ) (A : SmoothL2Field V) (n : ℕ) :
    (scaleField c A).jetLp n=c • A.jetLp n := by
  apply Lp.ext
  filter_upwards [(scaleField c A).jetLp_ae n,A.jetLp_ae n,Lp.coeFn_smul c (A.jetLp n)]
    with x hs ha hc
  rw [hs,hc,Pi.smul_apply,ha]
  change iteratedFDeriv ℝ n (fun x => c • A.field x) x=c • iteratedFDeriv ℝ n A.field x
  exact iteratedFDeriv_const_smul_apply (A.smooth.contDiffAt.of_le (by simp))

theorem scaleField_fderiv (c : ℝ) (A : SmoothL2Field V) (x : Space) :
    fderiv ℝ (scaleField c A).field x=c • fderiv ℝ A.field x :=
  ((A.smooth.differentiable (by simp) x).hasFDerivAt.const_smul c).fderiv

theorem scaleField_one (A : SmoothL2Field V) : scaleField 1 A=A := by
  apply field_ext
  exact funext (fun x => by simp only [scaleField_field,one_smul])

theorem scaleField_continuous {K : Type*} [TopologicalSpace K]
    (c : ℝ) (A : K → SmoothL2Field V)
    (hA : ∀ n, Continuous (fun t => (A t).jetLp n)) (n : ℕ) :
    Continuous (fun t => (scaleField c (A t)).jetLp n) :=
  continuous_jetLp_mapField _ A hA n

theorem tensorNorm_scaleField (c : ℝ) (A : SmoothL2Field Space) (q : ℕ) :
    tensorNorm q (scaleField c A)=|c| * tensorNorm q A := by
  simp only [tensorNorm,scaleField_jetLp,norm_smul,Real.norm_eq_abs,Finset.mul_sum]

theorem tensorNorm_scaleField_le (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (A : SmoothL2Field Space) (q : ℕ) : tensorNorm q (scaleField c A) ≤ tensorNorm q A := by
  rw [tensorNorm_scaleField,abs_of_nonneg hc]
  exact mul_le_of_le_one_left (tensorNorm_nonneg q A) hc1

end EulerOrdinarySobolev
