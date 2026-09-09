/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinarySmoothWords
public import LeanPool.NavierStokesAndEuler.Euler.SmoothL2CoefficientPath
public import LeanPool.NavierStokesAndEuler.Euler.LpSmoothCoefficientProduct

@[expose] public section

/-! Genuine smooth L² sums, scalar products, and ordinary advection. -/

noncomputable section

namespace EulerOrdinarySobolev

open MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerParameterWordGevrey EulerMeanCoefficients
  EulerMeanSobolevBoundedField EulerLpSmoothCoefficientProduct Finset Filter
open scoped ContDiff

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def sumField {ι : Type*} (I : Finset ι) (A : ι → SmoothL2Field V) : SmoothL2Field V where
  field x := ∑ i ∈ I, (A i).field x
  smooth := ContDiff.sum (fun i _ => (A i).smooth)
  integrable n := by
    have hm : MemLp (fun x => ∑ i ∈ I, iteratedFDeriv ℝ n (A i).field x) 2 volume :=
      memLp_finsetSum I (fun i _ => (A i).integrable n)
    exact hm.ae_eq (Eventually.of_forall (fun x =>
      (iteratedFDeriv_fun_sum_apply (fun i _ => (A i).smooth.contDiffAt.of_le (by simp))).symm))

@[simp] theorem sumField_field {ι : Type*} (I : Finset ι) (A : ι → SmoothL2Field V) (x : Space) :
    (sumField I A).field x = ∑ i ∈ I, (A i).field x := rfl

theorem toLp_sumField {ι : Type*} (I : Finset ι) (A : ι → SmoothL2Field V) :
    (sumField I A).toLp = ∑ i ∈ I, (A i).toLp := by
  apply Lp.ext
  have hr : (∑ i ∈ I, (A i).toLp : Space → V) =ᵐ[volume]
      ∑ i ∈ I, (A i).field := eventuallyEq_sum (s := I) (fun i _ => (A i).toLp_ae)
  filter_upwards [(sumField I A).toLp_ae,Lp.coeFn_finsetSum I (fun i => (A i).toLp),hr]
    with x ha hb hc
  rw [ha,hb]
  simpa only [sumField_field,Finset.sum_apply] using hc.symm

theorem wordField_sum {ι : Type*} (I : Finset ι) (A : ι → SmoothL2Field V)
    {n : ℕ} (w : Fin n → Fin 3) :
    wordField (sumField I A) w = sumField I (fun i => wordField (A i) w) := by
  apply field_ext
  funext x
  rw [wordField_field,sumField_field]
  simp only [wordField_field,wordDerivative]
  change (iteratedFDeriv ℝ n (fun x => ∑ i ∈ I, (A i).field x) x) _ = _
  rw [iteratedFDeriv_fun_sum_apply (fun i _ => (A i).smooth.contDiffAt.of_le (by simp))]
  simp only [_root_.sum_apply]

def fieldNeg (A : SmoothL2Field V) : SmoothL2Field V := mapField (-(ContinuousLinearMap.id ℝ V)) A

@[simp] theorem fieldNeg_field (A : SmoothL2Field V) (x : Space) :
    (fieldNeg A).field x = -A.field x := rfl

def fieldSub (A B : SmoothL2Field V) : SmoothL2Field V := addField A (fieldNeg B)

@[simp] theorem fieldSub_field (A B : SmoothL2Field V) (x : Space) :
    (fieldSub A B).field x = A.field x-B.field x := by
  simp only [fieldSub,addField_field,fieldNeg_field,sub_eq_add_neg]

theorem toLp_fieldNeg (A : SmoothL2Field V) : (fieldNeg A).toLp = -A.toLp := by
  apply Lp.ext
  filter_upwards [(fieldNeg A).toLp_ae,A.toLp_ae,Lp.coeFn_neg A.toLp] with x hn ha hb
  rw [hn,fieldNeg_field,hb,Pi.neg_apply,ha]

theorem toLp_fieldSub (A B : SmoothL2Field V) : (fieldSub A B).toLp = A.toLp-B.toLp := by
  rw [fieldSub,toLp_addField,toLp_fieldNeg,sub_eq_add_neg]

def scalarProduct (A : SmoothL2Field ℝ) (B : SmoothL2Field V) : SmoothL2Field V :=
  product (SmoothCoefficientPath.map (lsmul ℝ ℝ : ℝ →L[ℝ] V →L[ℝ] V)
    (coefficientPath (fun _ : Unit => A) (fun _ => continuous_const))) () B

@[simp] theorem scalarProduct_field (A : SmoothL2Field ℝ) (B : SmoothL2Field V) (x : Space) :
    (scalarProduct A B).field x = A.field x • B.field x := by
  rw [scalarProduct,product_field,SmoothCoefficientPath.map_apply,coefficientPath_apply,lsmul_apply]

theorem scalarProduct_directional (A : SmoothL2Field ℝ) (B : SmoothL2Field V) (v : Space) :
    (scalarProduct A B).directionalField v =
      addField (scalarProduct (A.directionalField v) B) (scalarProduct A (B.directionalField v)) :=
        by
  apply field_ext
  funext x
  rw [directionalField_field]
  have he : (scalarProduct A B).field=fun x => A.field x • B.field x := funext (scalarProduct_field
    A B)
  rw [he,addField_field,scalarProduct_field,scalarProduct_field,directionalField_field,directionalField_field]
  have hd := (A.smooth.differentiable (by simp) x).hasFDerivAt.smul
    (B.smooth.differentiable (by simp) x).hasFDerivAt
  have hv := congrArg (fun L : Space →L[ℝ] V => L v) hd.fderiv
  change (fderiv ℝ (fun x => A.field x • B.field x) x) v =
    A.field x • (fderiv ℝ B.field x) v+(fderiv ℝ A.field x) v • B.field x at hv
  exact hv.trans (add_comm _ _)

theorem scalarProduct_norm_left (A : SmoothL2Field ℝ) (B : SmoothL2Field V)
    (M : ℝ) (hM : ∀ x, ‖A.field x‖ ≤ M) :
    ‖(scalarProduct A B).toLp‖ ≤ M*‖B.toLp‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(scalarProduct A B).toLp_ae,B.toLp_ae] with x hp hb
  rw [hp,scalarProduct_field,hb,norm_smul]
  exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)

theorem scalarProduct_norm_right (A : SmoothL2Field ℝ) (B : SmoothL2Field V)
    (M : ℝ) (hM : ∀ x, ‖B.field x‖ ≤ M) :
    ‖(scalarProduct A B).toLp‖ ≤ M*‖A.toLp‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(scalarProduct A B).toLp_ae,A.toLp_ae] with x hp ha
  rw [hp,scalarProduct_field,ha,norm_smul,mul_comm]
  exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)

def coordinateProduct (i : Fin 3) (A : SmoothL2Field Space) (B : SmoothL2Field V) : SmoothL2Field V
  :=
  scalarProduct (mapField (EuclideanSpace.proj i) A) B

@[simp] theorem coordinateProduct_field (i : Fin 3) (A : SmoothL2Field Space)
    (B : SmoothL2Field V) (x : Space) :
    (coordinateProduct i A B).field x = A.field x i • B.field x := by
  rw [coordinateProduct,scalarProduct_field,mapField_field]
  rfl

def advectionField (A : SmoothL2Field Space) (B : SmoothL2Field V) : SmoothL2Field V :=
  sumField univ (fun i : Fin 3 => coordinateProduct i A (B.directionalField (axis i)))

@[simp] theorem advectionField_field (A : SmoothL2Field Space) (B : SmoothL2Field V) (x : Space) :
    (advectionField A B).field x = fderiv ℝ B.field x (A.field x) := by
  rw [advectionField,sumField_field]
  simp only [coordinateProduct_field,directionalField_field]
  have ha : (∑ i : Fin 3, A.field x i • axis i)=A.field x := by
    ext j
    simp [axis,Pi.single_apply,mul_ite]
  simpa only [map_sum,map_smul] using congrArg (fderiv ℝ B.field x) ha

end EulerOrdinarySobolev
