/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryFieldAlgebra
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryL2Integration
import Mathlib.Algebra.Order.Star.Real

/-! The sharp middle-derivative interpolation needed by H³ Euler
energy.  Everything is an actual smooth L² field.  Cubic testing and
noncompact integration by parts prove the L⁴ inequality without a
support or interpolation hypothesis. -/

@[expose] public section


noncomputable section

namespace EulerOrdinarySobolev

open MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerLpTranslation EulerLpTranslation.SmoothL2Field

theorem scalarProduct_norm_square (A B : SmoothL2Field ℝ) :
    ‖(scalarProduct A B).toLp‖^2 =
      ⟪(scalarProduct A A).toLp,(scalarProduct B B).toLp⟫_ℝ := by
  rw [← real_inner_self_eq_norm_sq,field_inner,field_inner]
  apply integral_congr_ae
  filter_upwards with x
  simp only [scalarProduct_field,RCLike.inner_apply,conj_trivial,smul_eq_mul]
  ring

theorem directional_square_identity (A : SmoothL2Field ℝ) (v : Space) :
    ‖(scalarProduct (A.directionalField v) (A.directionalField v)).toLp‖^2 =
      -3*⟪(scalarProduct A
        (scalarProduct (A.directionalField v) (A.directionalField v))).toLp,
        ((A.directionalField v).directionalField v).toLp⟫_ℝ := by
  let B := A.directionalField v
  let S := scalarProduct B B
  let C := scalarProduct B S
  have hs : ⟪B.toLp,C.toLp⟫_ℝ = ‖S.toLp‖^2 := by
    rw [← real_inner_self_eq_norm_sq,field_inner,field_inner]
    apply integral_congr_ae
    filter_upwards with x
    simp only [C,S,scalarProduct_field,RCLike.inner_apply,conj_trivial,smul_eq_mul]
    ring
  have hd : ⟪A.toLp,(C.directionalField v).toLp⟫_ℝ =
      3*⟪(scalarProduct A S).toLp,(B.directionalField v).toLp⟫_ℝ := by
    rw [field_inner,field_inner,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    simp only [C,S,scalarProduct_directional,addField_field,scalarProduct_field,
      RCLike.inner_apply,conj_trivial,smul_eq_mul]
    ring
  have hi := field_directional_inner A C v
  change ⟪B.toLp,C.toLp⟫_ℝ = -⟪A.toLp,(C.directionalField v).toLp⟫_ℝ at hi
  rw [hs,hd] at hi
  change ‖S.toLp‖^2 = -3*⟪(scalarProduct A S).toLp,(B.directionalField v).toLp⟫_ℝ
  linarith

theorem directional_square_norm (A : SmoothL2Field ℝ) (v : Space)
    (K : ℝ) (hK : ∀ x, ‖A.field x‖ ≤ K) :
    ‖(scalarProduct (A.directionalField v) (A.directionalField v)).toLp‖ ≤
      3*K*‖((A.directionalField v).directionalField v).toLp‖ := by
  let S := scalarProduct (A.directionalField v) (A.directionalField v)
  let Z := (A.directionalField v).directionalField v
  have hK0 : 0 ≤ K := (norm_nonneg (A.field 0)).trans (hK 0)
  have hb := scalarProduct_norm_left A S K hK
  have hi := directional_square_identity A v
  change ‖S.toLp‖^2 = -3*⟪(scalarProduct A S).toLp,Z.toLp⟫_ℝ at hi
  have hs : ‖S.toLp‖^2 ≤ (3*K*‖Z.toLp‖)*‖S.toLp‖ := by
    calc
      _ ≤ 3*|⟪(scalarProduct A S).toLp,Z.toLp⟫_ℝ| := by
        rw [hi]
        have h := neg_le_abs ⟪(scalarProduct A S).toLp,Z.toLp⟫_ℝ
        linarith
      _ ≤ 3*(‖(scalarProduct A S).toLp‖*‖Z.toLp‖) :=
        mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by norm_num)
      _ ≤ 3*((K*‖S.toLp‖)*‖Z.toLp‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hb (norm_nonneg _)) (by norm_num)
      _ = _ := by ring
  change ‖S.toLp‖ ≤ 3*K*‖Z.toLp‖
  have hc : 0 ≤ 3*K*‖Z.toLp‖ := by positivity
  nlinarith [norm_nonneg S.toLp]

theorem scalarProduct_norm_of_square_bounds (A B : SmoothL2Field ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hA : ‖(scalarProduct A A).toLp‖ ≤ C)
    (hB : ‖(scalarProduct B B).toLp‖ ≤ C) :
    ‖(scalarProduct A B).toLp‖ ≤ C := by
  have hs : ‖(scalarProduct A B).toLp‖^2 ≤ C^2 := by
    rw [scalarProduct_norm_square]
    exact (real_inner_le_norm _ _).trans
      ((mul_le_mul hA hB (norm_nonneg _) hC).trans_eq (by ring))
  nlinarith [norm_nonneg (scalarProduct A B).toLp]

end EulerOrdinarySobolev
