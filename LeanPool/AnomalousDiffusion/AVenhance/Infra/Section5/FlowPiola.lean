/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.PiolaFormula
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FrozenFlowRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.PulledGradientTransport
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.Liouville

/-! Piola push-forward for the row-Jacobian convention used by `gradMatrix`.

The cofactor-divergence identity is kept as an explicit hypothesis until the
spatial Piola calculation for the inverse flow is supplied. The
determinant-one input is separate and follows from Liouville once the stream
velocity's classical divergence-free identity is available. -/

@[expose] public section

open Homogenization

namespace AVenhance.Infra.Section5

open AVenhance

/-- Cofactor matrix for a row-Jacobian: `adjugate(Gᵀ)`. -/
def rowCofactor (G : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.adjugate (Matrix.transpose G)

/-- The cofactor Piola formula in the repository's row-Jacobian convention.
The derivative of the cofactor columns vanishes by the Piola identity; the
chain contraction is reduced to the Jacobian determinant algebraically. -/
theorem vecDiv_rowCofactorPiola
    {M g : Vec 2 → Vec 2} {x : Vec 2}
    {LM : Vec 2 →L[ℝ] Vec 2} {Lg : Vec 2 →L[ℝ] Vec 2}
    {LQ : Fin 2 → Fin 2 → Vec 2 →L[ℝ] ℝ}
    (hM : HasFDerivAt M LM x)
    (hg : HasFDerivAt g Lg (M x))
    (hQ : ∀ i j, HasFDerivAt
      (fun y => rowCofactor (gradMatrix M y) i j) (LQ i j) x)
    (hPiolaDiv : ∀ j : Fin 2,
      ∑ i : Fin 2, (LQ i j) (basisVec i) = 0)
    (hdet : (gradMatrix M x).det = 1) :
    vecDiv (fun y => (rowCofactor (gradMatrix M y)).mulVec (g (M y))) x =
      vecDiv g (M x) := by
  have hPiolaChain (j k : Fin 2) :
      ∑ i : Fin 2, rowCofactor (gradMatrix M x) i j *
        (LM (basisVec i)) k = if j = k then 1 else 0 := by
    let G := gradMatrix M x
    let Q := rowCofactor G
    have hG (i k : Fin 2) : G i k = (LM (basisVec i)) k := by
      change gradMatrix M x i k = _
      rw [gradMatrix_entry_eq_fderiv hM.differentiableAt i k]
      rw [hM.fderiv]
    calc
      (∑ i : Fin 2, Q i j * (LM (basisVec i)) k) =
          ∑ i : Fin 2, Q i j * G i k := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hG]
      _ = (Matrix.transpose Q * G) j k := by
            simp [Matrix.mul_apply, Matrix.transpose_apply]
      _ = (Matrix.adjugate G * G) j k := by
            have hQtranspose : Matrix.transpose Q = Matrix.adjugate G := by
              simp [Q, rowCofactor, Matrix.adjugate_transpose,
                Matrix.transpose_transpose]
            rw [hQtranspose]
      _ = (G.det • (1 : Matrix (Fin 2) (Fin 2) ℝ)) j k := by
            rw [Matrix.adjugate_mul]
      _ = if j = k then 1 else 0 := by
            simp [G, hdet, Matrix.one_apply]
  exact vecDiv_correctedPiola hQ hM hg hPiolaDiv hPiolaChain

/-- The Liouville determinant-one bridge for a inverse-flow slice.
Only classical divergence-freeness of the preceding stream velocity is
explicit; smoothness and the flow characterization come from `IsStreamSeq`. -/
theorem xFlowInv_gradMatrix_det_eq_one
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) (x : Vec 2)
    (hdiv : ∀ r y,
      Infra.Flow.spatialDivergence (streamVel (Φ (m - 1))) r y = 0) :
    (gradMatrix (I.xFlowInv hΦ m l t) x).det = 1 := by
  let b := streamVel (Φ (m - 1))
  let X := flow b (hΦ.adm_pred m).vel_continuous
    (hΦ.adm_pred m).vel_lipschitz
  have hb : Infra.Flow.SmoothPeriodicField b :=
    Infra.Construction.smoothPeriodic_streamVel (hΦ.adm_pred m)
  have hX : IsFlow b X := flow_isFlow b
    (hΦ.adm_pred m).vel_continuous (hΦ.adm_pred m).vel_lipschitz
  let s := (l : ℝ) * tauPP β I.Λ m
  have hdet := Infra.Flow.flow_spatial_jacobian_det_eq_one_of_divergence_free
    hb hX (by simpa [b] using hdiv) x t s
  have hslice : (fun y => I.xFlowInv hΦ m l t y) = fun y => X s y t := by
    funext y
    simp [Ingredients.xFlowInv, AVenhance.flowInv, X, b, s]
  have hdiff := (Infra.Flow.flow_spatial_contDiff_one hb hX t s).differentiable
    (by norm_num) x
  have hgradDet :
      (gradMatrix (fun y => X s y t) x).det =
        (fderiv ℝ (fun y => X s y t) x).det := by
    let D := fderiv ℝ (fun y => X s y t) x
    have hmatrix : gradMatrix (fun y => X s y t) x =
        Matrix.transpose (LinearMap.toMatrix' D.toLinearMap) := by
      ext i j
      rw [gradMatrix_entry_eq_fderiv hdiff i j]
      simp [D, LinearMap.toMatrix'_apply, basisVec]
    change (gradMatrix (fun y => X s y t) x).det = LinearMap.det D.toLinearMap
    rw [hmatrix, Matrix.det_transpose, ← LinearMap.det_toMatrix' D.toLinearMap]
  have hgradSlice : gradMatrix (I.xFlowInv hΦ m l t) x =
      gradMatrix (fun y => X s y t) x :=
    congrArg (fun f : Vec 2 → Vec 2 => gradMatrix f x) hslice
  rw [hgradSlice]
  calc
    (gradMatrix (fun y => X s y t) x).det =
        (fderiv ℝ (fun y => X s y t) x).det := hgradDet
    _ = 1 := hdet

/-- inverse-flow version of the cofactor push-forward. The cofactor
divergence identity is an explicit premise (a Piola lemma); the unit
determinant is supplied by the Liouville bridge above. -/
theorem xFlowInv_cofactorPiola
    {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ) (t : ℝ) (x : Vec 2)
    {g : Vec 2 → Vec 2} {LM : Vec 2 →L[ℝ] Vec 2} {Lg : Vec 2 →L[ℝ] Vec 2}
    {LQ : Fin 2 → Fin 2 → Vec 2 →L[ℝ] ℝ}
    (hM : HasFDerivAt (I.xFlowInv hΦ m l t) LM x)
    (hg : HasFDerivAt g Lg (I.xFlowInv hΦ m l t x))
    (hQ : ∀ i j, HasFDerivAt
      (fun y => rowCofactor (gradMatrix (I.xFlowInv hΦ m l t) y) i j)
      (LQ i j) x)
    (hPiolaDiv : ∀ j : Fin 2,
      ∑ i : Fin 2, (LQ i j) (basisVec i) = 0)
    (hdiv : ∀ r y,
      Infra.Flow.spatialDivergence (streamVel (Φ (m - 1))) r y = 0) :
    vecDiv (fun y => (rowCofactor
        (gradMatrix (I.xFlowInv hΦ m l t) y)).mulVec
          (g (I.xFlowInv hΦ m l t y))) x =
      vecDiv g (I.xFlowInv hΦ m l t x) := by
  exact vecDiv_rowCofactorPiola hM hg hQ hPiolaDiv
    (xFlowInv_gradMatrix_det_eq_one I hΦ m l t x hdiv)

end AVenhance.Infra.Section5
