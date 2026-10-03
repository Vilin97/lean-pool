/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FlowPiola

/-! The two-dimensional cofactor-divergence identity for smooth maps. -/

@[expose] public section

open Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5

open AVenhance

theorem FlowPiolaDivergence.rowCofactor_00 (A : Matrix (Fin 2) (Fin 2) ℝ) :
    rowCofactor A 0 0 = A 1 1 := by
  simp [rowCofactor, Matrix.adjugate_apply, Matrix.det_fin_two]

theorem FlowPiolaDivergence.rowCofactor_01 (A : Matrix (Fin 2) (Fin 2) ℝ) :
    rowCofactor A 0 1 = -A 1 0 := by
  simp [rowCofactor, Matrix.adjugate_apply, Matrix.det_fin_two]

theorem FlowPiolaDivergence.rowCofactor_10 (A : Matrix (Fin 2) (Fin 2) ℝ) :
    rowCofactor A 1 0 = -A 0 1 := by
  simp [rowCofactor, Matrix.adjugate_apply, Matrix.det_fin_two]

theorem FlowPiolaDivergence.rowCofactor_11 (A : Matrix (Fin 2) (Fin 2) ℝ) :
    rowCofactor A 1 1 = A 0 0 := by
  simp [rowCofactor, Matrix.adjugate_apply, Matrix.det_fin_two]

theorem FlowPiolaDivergence.gradMatrix_entry_hasFDerivAt_of_contDiff
    {M : Vec 2 → Vec 2} {x : Vec 2} (hM : ContDiff ℝ 2 M)
    (i j : Fin 2) :
    HasFDerivAt (fun y => gradMatrix M y i j)
      ((ContinuousLinearMap.proj j).comp
        ((fderiv ℝ (fderiv ℝ M) x).flip (basisVec i))) x := by
  let D2 : Vec 2 →L[ℝ] (Vec 2 →L[ℝ] Vec 2) :=
    fderiv ℝ (fderiv ℝ M) x
  have hDfCont : ContDiffAt ℝ 1 (fderiv ℝ M) x :=
    hM.contDiffAt.fderiv_right (m := 1) (by norm_num)
  have hDf : HasFDerivAt (fderiv ℝ M) D2 x :=
    (hDfCont.differentiableAt (by norm_num)).hasFDerivAt
  have hclm : HasFDerivAt
      (fun y => fderiv ℝ M y (basisVec i)) (D2.flip (basisVec i)) x := by
    simpa [D2, ContinuousLinearMap.comp_zero] using
      hDf.clm_apply (hasFDerivAt_const (basisVec i) x)
  have hcoord := (ContinuousLinearMap.proj j).hasFDerivAt.comp x hclm
  have hentry (y : Vec 2) :
      gradMatrix M y i j = fderiv ℝ M y (basisVec i) j := by
    exact gradMatrix_entry_eq_fderiv
      (hM.differentiable (by norm_num) y) i j
  have hfun : (fun y => gradMatrix M y i j) =
      fun y => fderiv ℝ M y (basisVec i) j := by
    funext y
    exact hentry y
  rw [hfun]
  simpa [D2, Function.comp_def, ContinuousLinearMap.proj_apply] using hcoord

/-- The cofactor of the row-Jacobian of a C² map has zero column divergence.
This is the coordinate Piola identity; no volume-preservation hypothesis is
needed. -/
theorem rowCofactor_gradMatrix_piolaInputs
    {M : Vec 2 → Vec 2} (hM : ContDiff ℝ 2 M) (x : Vec 2) :
    (∀ i j : Fin 2,
      HasFDerivAt
        (fun y => rowCofactor (gradMatrix M y) i j)
        (fderiv ℝ (fun y => rowCofactor (gradMatrix M y) i j) x) x) ∧
    (∀ j : Fin 2,
      ∑ i : Fin 2,
        (fderiv ℝ (fun y => rowCofactor (gradMatrix M y) i j) x)
          (basisVec i) = 0) := by
  let Lg (i j : Fin 2) : Vec 2 →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj j).comp
      ((fderiv ℝ (fderiv ℝ M) x).flip (basisVec i))
  have hgrad (i j : Fin 2) : HasFDerivAt
      (fun y => gradMatrix M y i j) (Lg i j) x := by
    simpa [Lg] using FlowPiolaDivergence.gradMatrix_entry_hasFDerivAt_of_contDiff hM i j
  have hq00fun : (fun y => rowCofactor (gradMatrix M y) 0 0) =
      fun y => gradMatrix M y 1 1 := by
    funext y
    exact FlowPiolaDivergence.rowCofactor_00 (gradMatrix M y)
  have hq01fun : (fun y => rowCofactor (gradMatrix M y) 0 1) =
      fun y => -gradMatrix M y 1 0 := by
    funext y
    exact FlowPiolaDivergence.rowCofactor_01 (gradMatrix M y)
  have hq10fun : (fun y => rowCofactor (gradMatrix M y) 1 0) =
      fun y => -gradMatrix M y 0 1 := by
    funext y
    exact FlowPiolaDivergence.rowCofactor_10 (gradMatrix M y)
  have hq11fun : (fun y => rowCofactor (gradMatrix M y) 1 1) =
      fun y => gradMatrix M y 0 0 := by
    funext y
    exact FlowPiolaDivergence.rowCofactor_11 (gradMatrix M y)
  have hq00 : fderiv ℝ (fun y => rowCofactor (gradMatrix M y) 0 0) x =
      Lg 1 1 := by rw [hq00fun]; exact (hgrad 1 1).fderiv
  have hq01 : fderiv ℝ (fun y => rowCofactor (gradMatrix M y) 0 1) x =
      -Lg 1 0 := by rw [hq01fun]; exact (hgrad 1 0).neg.fderiv
  have hq10 : fderiv ℝ (fun y => rowCofactor (gradMatrix M y) 1 0) x =
      -Lg 0 1 := by rw [hq10fun]; exact (hgrad 0 1).neg.fderiv
  have hq11 : fderiv ℝ (fun y => rowCofactor (gradMatrix M y) 1 1) x =
      Lg 0 0 := by rw [hq11fun]; exact (hgrad 0 0).fderiv
  have hQ00 : HasFDerivAt
      (fun y => rowCofactor (gradMatrix M y) 0 0)
      (fderiv ℝ (fun y => rowCofactor (gradMatrix M y) 0 0) x) x := by
    rw [hq00]
    rw [hq00fun]
    exact hgrad 1 1
  have hQ01 : HasFDerivAt
      (fun y => rowCofactor (gradMatrix M y) 0 1)
      (fderiv ℝ (fun y => rowCofactor (gradMatrix M y) 0 1) x) x := by
    rw [hq01]
    rw [hq01fun]
    exact (hgrad 1 0).neg
  have hQ10 : HasFDerivAt
      (fun y => rowCofactor (gradMatrix M y) 1 0)
      (fderiv ℝ (fun y => rowCofactor (gradMatrix M y) 1 0) x) x := by
    rw [hq10]
    rw [hq10fun]
    exact (hgrad 0 1).neg
  have hQ11 : HasFDerivAt
      (fun y => rowCofactor (gradMatrix M y) 1 1)
      (fderiv ℝ (fun y => rowCofactor (gradMatrix M y) 1 1) x) x := by
    rw [hq11]
    rw [hq11fun]
    exact hgrad 0 0
  have hQ : ∀ i j : Fin 2,
      HasFDerivAt (fun y => rowCofactor (gradMatrix M y) i j)
        (fderiv ℝ (fun y => rowCofactor (gradMatrix M y) i j) x) x := by
    intro i j
    fin_cases i <;> fin_cases j
    · simpa using hQ00
    · simpa using hQ01
    · simpa using hQ10
    · simpa using hQ11
  have hsymm := (hM.contDiffAt (x := x)).isSymmSndFDerivAt (by norm_num)
  have hsecond := hsymm (basisVec (0 : Fin 2)) (basisVec 1)
  have hdiv0 :
      (fderiv ℝ (fun y => rowCofactor (gradMatrix M y) 0 0) x)
          (basisVec 0) +
        (fderiv ℝ (fun y => rowCofactor (gradMatrix M y) 1 0) x)
          (basisVec 1) = 0 := by
    rw [hq00, hq10]
    simp [Lg, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, ContinuousLinearMap.flip_apply]
    have hcomponent := congrArg (fun v : Vec 2 => v 1) hsecond
    linarith
  have hdiv1 :
      (fderiv ℝ (fun y => rowCofactor (gradMatrix M y) 0 1) x)
          (basisVec 0) +
        (fderiv ℝ (fun y => rowCofactor (gradMatrix M y) 1 1) x)
          (basisVec 1) = 0 := by
    rw [hq01, hq11]
    simp [Lg, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply, ContinuousLinearMap.flip_apply]
    have hcomponent := congrArg (fun v : Vec 2 => v 0) hsecond
    linarith
  constructor
  · exact hQ
  · intro j
    fin_cases j
    · rw [Fin.sum_univ_two]
      exact hdiv0
    · rw [Fin.sum_univ_two]
      exact hdiv1

/-- The inverse-flow cofactor has differentiable entries and zero column
divergence. The C² inverse-flow slice is supplied by the flow
regularity bridge. -/
theorem xFlowInv_cofactor_piolaInputs
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) (x : Vec 2) :
    (∀ i j : Fin 2,
      HasFDerivAt
        (fun y => rowCofactor
          (gradMatrix (I.xFlowInv hΦ m l t) y) i j)
        (fderiv ℝ (fun y => rowCofactor
          (gradMatrix (I.xFlowInv hΦ m l t) y) i j) x) x) ∧
    (∀ j : Fin 2,
      ∑ i : Fin 2,
        (fderiv ℝ (fun y => rowCofactor
          (gradMatrix (I.xFlowInv hΦ m l t) y) i j) x)
          (basisVec i) = 0) := by
  exact rowCofactor_gradMatrix_piolaInputs
    (xFlowInv_spatial_contDiff_two I hΦ m l t) x

end AVenhance.Infra.Section5
