/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPiolaAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.PacketPotentialMultiplier
public import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus

@[expose] public section

/-! A determinant-one three-dimensional matrix has a quadratic inverse.
This realizes the cofactor as an actual bounded bilinear map; its estimates
therefore require no derivatives or norm bounds for a separately given inverse. -/

noncomputable section

namespace EulerPacketCofactor

open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerPacketPiola
  EulerPacketCrossProduct EulerOperatorGevreyCalculus EulerGevrey
open scoped ContDiff

abbrev EndSpace := Space →L[ℝ] Space

private local instance : NormedAddCommGroup EndSpace := inferInstance
private local instance : NormedSpace ℝ EndSpace := inferInstance
private local instance : NormedAddCommGroup (EndSpace →L[ℝ] EndSpace) := inferInstance
private local instance : NormedSpace ℝ (EndSpace →L[ℝ] EndSpace) := inferInstance
private local instance : NormedAddCommGroup (EndSpace →L[ℝ] EndSpace →L[ℝ] EndSpace) :=
  inferInstance
private local instance : NormedSpace ℝ (EndSpace →L[ℝ] EndSpace →L[ℝ] EndSpace) := inferInstance

def basis (i : Fin 3) : Space := EuclideanSpace.single i 1

@[simp] theorem basis_norm (i : Fin 3) : ‖basis i‖ = 1 := by
  simp [basis]

def rowLinear (i : Fin 3) : Space →ₗ[ℝ] EndSpace where
  toFun a := (innerSL ℝ a).smulRight (basis i)
  map_add' a b := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      inner_add_left, add_apply, add_smul]
  map_smul' c a := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      real_inner_smul_left, RingHom.id_apply, smul_apply, smul_smul]

theorem rowLinear_norm (i : Fin 3) (a : Space) : ‖rowLinear i a‖ ≤ ‖a‖ := by
  apply opNorm_le_bound _ (norm_nonneg a)
  intro v
  change ‖(inner ℝ a v) • basis i‖ ≤ ‖a‖*‖v‖
  rw [norm_smul,basis_norm,mul_one,Real.norm_eq_abs]
  exact abs_real_inner_le_norm a v

def rowOperator (i : Fin 3) : Space →L[ℝ] EndSpace :=
  (rowLinear i).mkContinuous 1 (fun a => by simpa only [one_mul] using rowLinear_norm i a)

@[simp] theorem rowOperator_apply (i : Fin 3) (a v : Space) :
    rowOperator i a v = (inner ℝ a v) • basis i := rfl

theorem rowOperator_norm (i : Fin 3) (a : Space) : ‖rowOperator i a‖ ≤ ‖a‖ :=
  rowLinear_norm i a

def cofactorValue (A B : EndSpace) : EndSpace :=
  rowOperator 0 (crossOperator (A (basis 1)) (B (basis 2)))+
  rowOperator 1 (crossOperator (A (basis 2)) (B (basis 0)))+
  rowOperator 2 (crossOperator (A (basis 0)) (B (basis 1)))

def cofactorLinear : EndSpace →ₗ[ℝ] EndSpace →ₗ[ℝ] EndSpace where
  toFun A :=
    { toFun := cofactorValue A
      map_add' B C := by
        simp only [cofactorValue,add_apply,map_add]
        abel
      map_smul' c B := by
        simp only [cofactorValue,smul_apply,map_smul,smul_add,RingHom.id_apply] }
  map_add' A B := by
    apply LinearMap.ext
    intro C
    change cofactorValue (A+B) C = cofactorValue A C+cofactorValue B C
    simp only [cofactorValue,add_apply,map_add]
    abel
  map_smul' c A := by
    apply LinearMap.ext
    intro B
    change cofactorValue (c • A) B = c • cofactorValue A B
    simp only [cofactorValue,smul_apply,map_smul,smul_add]

theorem cofactorValue_norm (A B : EndSpace) : ‖cofactorValue A B‖ ≤ 3*‖A‖*‖B‖ := by
  have h (i j k : Fin 3) :
      ‖rowOperator i (crossOperator (A (basis j)) (B (basis k)))‖ ≤ ‖A‖*‖B‖ := by
    apply (rowOperator_norm i _).trans
    change ‖cross (A (basis j)) (B (basis k))‖ ≤ ‖A‖*‖B‖
    exact (cross_norm_le _ _).trans (mul_le_mul
      (by simpa only [basis_norm,mul_one] using A.le_opNorm (basis j))
      (by simpa only [basis_norm,mul_one] using B.le_opNorm (basis k))
      (norm_nonneg _) (norm_nonneg A))
  calc
    ‖cofactorValue A B‖ ≤
        ‖rowOperator 0 (crossOperator (A (basis 1)) (B (basis 2)))‖+
        ‖rowOperator 1 (crossOperator (A (basis 2)) (B (basis 0)))‖+
        ‖rowOperator 2 (crossOperator (A (basis 0)) (B (basis 1)))‖ := norm_add₃_le
    _ ≤ 3*‖A‖*‖B‖ := by nlinarith [h 0 1 2,h 1 2 0,h 2 0 1]

def cofactorBilinear : EndSpace →L[ℝ] EndSpace →L[ℝ] EndSpace :=
  cofactorLinear.mkContinuous₂ 3 cofactorValue_norm

@[simp] theorem cofactorBilinear_apply (A B : EndSpace) : cofactorBilinear A B = cofactorValue A B
  := rfl

theorem cofactorBilinear_norm : ‖cofactorBilinear‖ ≤ 3 :=
  cofactorLinear.mkContinuous₂_norm_le (by norm_num) cofactorValue_norm

def adjugate (A : EndSpace) : EndSpace := cofactorBilinear A A

theorem adjugate_norm (A : EndSpace) : ‖adjugate A‖ ≤ 3*‖A‖^2 := by
  change ‖cofactorValue A A‖ ≤ 3*‖A‖^2
  simpa only [pow_two,mul_assoc] using cofactorValue_norm A A

theorem operatorMatrix_adjugate (A : EndSpace) :
    operatorMatrix (adjugate A) = (operatorMatrix A).adjugate := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [operatorMatrix,adjugate,cofactorValue,rowOperator_apply,
      crossLeft_apply,cross,basis,EuclideanSpace.inner_single_right,
      cross_apply,Matrix.adjugate_fin_three,Matrix.cons_val_two] <;> ring

theorem operatorMatrix_injective : Function.Injective operatorMatrix := by
  intro A B h
  apply ContinuousLinearMap.ext
  intro v
  ext i
  rw [operatorMatrix_apply,operatorMatrix_apply,h]

theorem adjugate_comp (A : EndSpace) (hdet : (operatorMatrix A).det = 1) :
    (adjugate A).comp A = ContinuousLinearMap.id ℝ Space := by
  apply operatorMatrix_injective
  rw [operatorMatrix_comp,operatorMatrix_adjugate,Matrix.adjugate_mul,hdet,
    one_smul,operatorMatrix_id]

theorem comp_adjugate (A : EndSpace) (hdet : (operatorMatrix A).det = 1) :
    A.comp (adjugate A) = ContinuousLinearMap.id ℝ Space := by
  apply operatorMatrix_injective
  rw [operatorMatrix_comp,operatorMatrix_adjugate,Matrix.mul_adjugate,hdet,
    one_smul,operatorMatrix_id]

theorem inverse_eq_adjugate (A I : EndSpace) (hdet : (operatorMatrix A).det = 1)
    (hI : ∀ v, I (A v) = v) : I = adjugate A := by
  apply ContinuousLinearMap.ext
  intro v
  have hAv : A (adjugate A v) = v := congrArg (fun L : EndSpace => L v) (comp_adjugate A hdet)
  calc
    I v = I (A (adjugate A v)) := by rw [hAv]
    _ = adjugate A v := hI _

end EulerPacketCofactor
