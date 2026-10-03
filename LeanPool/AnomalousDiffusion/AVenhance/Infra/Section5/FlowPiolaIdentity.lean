/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FlowPiola
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FlowGradientRegularity

/-! Identify the inverse-flow cofactor with the forward flow matrix in the
row-Jacobian convention. -/

@[expose] public section

open Homogenization

namespace AVenhance.Infra.Section5

open AVenhance

theorem gradMatrix_comp
    {F G : Vec 2 → Vec 2} {x : Vec 2}
    (hF : DifferentiableAt ℝ F (G x)) (hG : DifferentiableAt ℝ G x) :
    gradMatrix (fun y => F (G y)) x =
      gradMatrix G x * gradMatrix F (G x) := by
  ext i j
  have hcomp := hF.hasFDerivAt.comp x hG.hasFDerivAt
  have hcomp' : HasFDerivAt (fun y => F (G y))
      (fderiv ℝ F (G x) ∘L fderiv ℝ G x) x := by
    simpa [Function.comp_def] using hcomp
  change fderiv ℝ (fun y => F (G y) j) x (basisVec i) = _
  have hcoord : fderiv ℝ (fun y => F (G y) j) x (basisVec i) =
      (fderiv ℝ F (G x) (fderiv ℝ G x (basisVec i))) j := by
    rw [fderiv_apply hcomp'.differentiableAt j, hcomp'.fderiv]
    rfl
  have hGbasis : fderiv ℝ G x (basisVec i) =
      ∑ l : Fin 2, (fderiv ℝ G x (basisVec i) l) • basisVec l := by
    funext q
    fin_cases q <;> simp [basisVec, Fin.sum_univ_two]
  rw [hcoord, hGbasis, map_sum, Matrix.mul_apply]
  simp only [map_smul]
  change ∑ c : Fin 2,
      (fderiv ℝ G x (basisVec i) c) *
        (fderiv ℝ F (G x) (basisVec c) j) =
    ∑ l : Fin 2,
      fderiv ℝ (fun y => G y l) x (basisVec i) *
        fderiv ℝ (fun y => F y j) (G x) (basisVec l)
  apply Finset.sum_congr rfl
  intro l hl
  rw [fderiv_apply hG l, fderiv_apply hF j]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]

theorem FlowPiolaIdentity.gradMatrix_id (x : Vec 2) :
    gradMatrix (fun y : Vec 2 => y) x = 1 := by
  ext i j
  change fderiv ℝ (fun y : Vec 2 => y j) x (basisVec i) = _
  rw [fderiv_apply differentiableAt_id j]
  change ((ContinuousLinearMap.proj j).comp (fderiv ℝ id x)) (basisVec i) = _
  rw [fderiv_id]
  by_cases hij : i = j
  · subst j
    simp [basisVec]
  · have hji : j ≠ i := fun h => hij h.symm
    simp [basisVec, hij, hji]

theorem FlowPiolaIdentity.adjugate_eq_rightInverse_of_mul_eq_one
    (A B : Matrix (Fin 2) (Fin 2) ℝ) (hAB : A * B = 1) (hdet : A.det = 1) :
    Matrix.adjugate A = B := by
  calc
    Matrix.adjugate A = Matrix.adjugate A * (A * B) := by rw [hAB]; simp
    _ = (Matrix.adjugate A * A) * B := by rw [Matrix.mul_assoc]
    _ = B := by rw [Matrix.adjugate_mul, hdet]; simp

/-- For an inverse flow, the row cofactor is the transpose of the forward
row-Jacobian evaluated at the inverse image. This is the source Piola
coefficient after correcting its row/column convention. -/
theorem xFlowInv_rowCofactor_eq_flowGrad_transpose
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) (x : Vec 2)
    (hdiv : ∀ r y,
      Infra.Flow.spatialDivergence (streamVel (Φ (m - 1))) r y = 0) :
    rowCofactor (gradMatrix (I.xFlowInv hΦ m l t) x) =
      (I.flowGrad hΦ m l t x).transpose := by
  let M := I.xFlowInv hΦ m l t
  let X := I.xFlow hΦ m l t
  have hM : DifferentiableAt ℝ M x :=
    (xFlowInv_spatial_contDiff_two I hΦ m l t).differentiable
      (by norm_num) x
  have hX : DifferentiableAt ℝ X (M x) :=
    (xFlow_spatial_contDiff_two I hΦ m l t).differentiable
      (by norm_num) (M x)
  have hinv (y : Vec 2) : X (M y) = y := by
    let b := streamVel (Φ (m - 1))
    let F := flow b (hΦ.adm_pred m).vel_continuous
      (hΦ.adm_pred m).vel_lipschitz
    have hF : IsFlow b F := flow_isFlow b
      (hΦ.adm_pred m).vel_continuous (hΦ.adm_pred m).vel_lipschitz
    let s := (l : ℝ) * tauPP β I.Λ m
    change F t (F s y t) s = y
    calc
      F t (F s y t) s = F t y t :=
        Infra.Flow.flow_group_law b (hΦ.adm_pred m).vel_lipschitz hF y t s t
      _ = y := hF.1 y t
  have hcomp := gradMatrix_comp hX hM
  have hcompId : gradMatrix (fun y => X (M y)) x = 1 := by
    rw [show (fun y => X (M y)) = fun y => y from funext hinv]
    exact FlowPiolaIdentity.gradMatrix_id x
  have hmat : gradMatrix M x * gradMatrix X (M x) = 1 := by
    calc
      gradMatrix M x * gradMatrix X (M x) =
          gradMatrix (fun y => X (M y)) x := hcomp.symm
      _ = 1 := hcompId
  have hdet := xFlowInv_gradMatrix_det_eq_one I hΦ m l t x hdiv
  have hadj := FlowPiolaIdentity.adjugate_eq_rightInverse_of_mul_eq_one
    (gradMatrix M x) (gradMatrix X (M x)) hmat hdet
  have hcof : rowCofactor (gradMatrix M x) =
      (gradMatrix X (M x)).transpose := by
    unfold rowCofactor
    calc
      Matrix.adjugate (Matrix.transpose (gradMatrix M x)) =
          (Matrix.adjugate (gradMatrix M x)).transpose := by
            rw [← Matrix.adjugate_transpose]
      _ = (gradMatrix X (M x)).transpose := congrArg Matrix.transpose hadj
  simpa [M, X, Ingredients.flowGrad] using hcof

end AVenhance.Infra.Section5
