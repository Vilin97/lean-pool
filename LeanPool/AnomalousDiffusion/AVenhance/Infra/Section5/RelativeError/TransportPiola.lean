/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.TransportODEApplications
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.SpaceGrad

/-! # RelativeError: the two-dimensional cofactor Piola identity -/

@[expose] public section

noncomputable section

open Homogenization
open AVenhance
open scoped ContDiff

namespace AVenhance.Infra.Section5.RelativeError

theorem TransportPiola.mixed_spaceGrad_commute {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ 2 f) (x : Vec 2) :
    spaceGrad (fun y => spaceGrad f y 0) x 1 =
      spaceGrad (fun y => spaceGrad f y 1) x 0 := by
  have hAt := hf.contDiffAt (x := x)
  have hC2 : ContDiffAt ℝ 2 f x := hAt
  have hsymm := hC2.isSymmSndFDerivAt (by simp)
  have hc : DifferentiableAt ℝ (fderiv ℝ f) x := by
    have hCderiv : ContDiffAt ℝ 1 (fderiv ℝ f) x :=
      hAt.fderiv_right (m := 1) (by norm_num)
    exact hCderiv.differentiableAt (by norm_num)
  have hu0 : DifferentiableAt ℝ (fun _ : Vec 2 => basisVec (0 : Fin 2)) x :=
    differentiableAt_const (basisVec 0)
  have hu1 : DifferentiableAt ℝ (fun _ : Vec 2 => basisVec (1 : Fin 2)) x :=
    differentiableAt_const (basisVec 1)
  have hderiv0 : fderiv ℝ (fun y => fderiv ℝ f y (basisVec (0 : Fin 2))) x =
      (fderiv ℝ (fderiv ℝ f) x).flip (basisVec (0 : Fin 2)) := by
    simpa using fderiv_clm_apply hc hu0
  have hderiv1 : fderiv ℝ (fun y => fderiv ℝ f y (basisVec (1 : Fin 2))) x =
      (fderiv ℝ (fderiv ℝ f) x).flip (basisVec (1 : Fin 2)) := by
    simpa using fderiv_clm_apply hc hu1
  have hleft : spaceGrad (fun y => spaceGrad f y 0) x 1 =
      fderiv ℝ (fderiv ℝ f) x (basisVec 1) (basisVec 0) := by
    change fderiv ℝ (fun y => fderiv ℝ f y (basisVec 0)) x (basisVec 1) = _
    rw [hderiv0]
    rfl
  have hright : spaceGrad (fun y => spaceGrad f y 1) x 0 =
      fderiv ℝ (fderiv ℝ f) x (basisVec 0) (basisVec 1) := by
    change fderiv ℝ (fun y => fderiv ℝ f y (basisVec 1)) x (basisVec 0) = _
    rw [hderiv1]
    rfl
  rw [hleft, hright]
  exact hsymm (basisVec 1) (basisVec 0)

theorem TransportPiola.spatialGradientMatrix_entry_eq_spaceGrad
    {Y : Vec 2 → Vec 2} (hY : ContDiff ℝ 1 Y)
    (x : Vec 2) (i j : Fin 2) :
    AVenhance.FaaDiBruno.spatialGradientMatrix Y x i j =
      spaceGrad (fun y => Y y i) x j := by
  have hd := hY.differentiable (by norm_num) x
  have h := fderiv_apply hd i
  have h' := congrArg (fun L : Vec 2 →L[ℝ] ℝ =>
    L (AVenhance.FaaDiBruno.coordinateVector 2 j)) h
  simpa [AVenhance.FaaDiBruno.spatialGradientMatrix,
    AVenhance.FaaDiBruno.coordinateVector, basisVec, spaceGrad] using h'.symm

/-- The columns of the transposed cofactor of a two-dimensional gradient
are divergence-free. This is the classical Piola identity, proved by equality
of mixed second derivatives. -/
theorem cofactorTranspose_gradient_columns_divergence_free
    {Y : Vec 2 → Vec 2} (hY : ContDiff ℝ 2 Y)
    (x : Vec 2) (j : Fin 2) :
    ∑ i : Fin 2,
      (fderiv ℝ
        (fun z => AVenhance.FaaDiBruno.flowMatrixCofactorTranspose
          (AVenhance.FaaDiBruno.spatialGradientMatrix Y z) i j) x)
        (basisVec i) = 0 := by
  have hY0 : ContDiff ℝ 2 (fun y => Y y 0) := (contDiff_apply ℝ ℝ 0).comp hY
  have hY1 : ContDiff ℝ 2 (fun y => Y y 1) := (contDiff_apply ℝ ℝ 1).comp hY
  have hq00 (z : Vec 2) :
      AVenhance.FaaDiBruno.flowMatrixCofactorTranspose
        (AVenhance.FaaDiBruno.spatialGradientMatrix Y z) 0 0 =
        spaceGrad (fun y => Y y 1) z 1 := by
    simp only [AVenhance.FaaDiBruno.flowMatrixCofactorTranspose]
    exact TransportPiola.spatialGradientMatrix_entry_eq_spaceGrad
      (hY.of_le (by norm_num)) z 1 1
  have hq10 (z : Vec 2) :
      AVenhance.FaaDiBruno.flowMatrixCofactorTranspose
        (AVenhance.FaaDiBruno.spatialGradientMatrix Y z) 1 0 =
        -spaceGrad (fun y => Y y 1) z 0 := by
    change -AVenhance.FaaDiBruno.spatialGradientMatrix Y z 1 0 = _
    rw [TransportPiola.spatialGradientMatrix_entry_eq_spaceGrad
      (hY.of_le (by norm_num)) z 1 0]
  have hq01 (z : Vec 2) :
      AVenhance.FaaDiBruno.flowMatrixCofactorTranspose
        (AVenhance.FaaDiBruno.spatialGradientMatrix Y z) 0 1 =
        -spaceGrad (fun y => Y y 0) z 1 := by
    change -AVenhance.FaaDiBruno.spatialGradientMatrix Y z 0 1 = _
    rw [TransportPiola.spatialGradientMatrix_entry_eq_spaceGrad
      (hY.of_le (by norm_num)) z 0 1]
  have hq11 (z : Vec 2) :
      AVenhance.FaaDiBruno.flowMatrixCofactorTranspose
        (AVenhance.FaaDiBruno.spatialGradientMatrix Y z) 1 1 =
        spaceGrad (fun y => Y y 0) z 0 := by
    norm_num [AVenhance.FaaDiBruno.flowMatrixCofactorTranspose]
    exact TransportPiola.spatialGradientMatrix_entry_eq_spaceGrad
      (hY.of_le (by norm_num)) z 0 0
  have h00 :
      (fderiv ℝ
        (fun z => AVenhance.FaaDiBruno.flowMatrixCofactorTranspose
          (AVenhance.FaaDiBruno.spatialGradientMatrix Y z) 0 0) x)
        (basisVec 0) = spaceGrad (fun z => spaceGrad (fun y => Y y 1) z 1) x 0 := by
    have hfun : (fun z => AVenhance.FaaDiBruno.flowMatrixCofactorTranspose
        (AVenhance.FaaDiBruno.spatialGradientMatrix Y z) 0 0) =
        (fun z => spaceGrad (fun y => Y y 1) z 1) := funext hq00
    rw [hfun]
    rfl
  have h10 :
      (fderiv ℝ
        (fun z => AVenhance.FaaDiBruno.flowMatrixCofactorTranspose
          (AVenhance.FaaDiBruno.spatialGradientMatrix Y z) 1 0) x)
        (basisVec 1) = -spaceGrad (fun z => spaceGrad (fun y => Y y 1) z 0) x 1 := by
    have hfun : (fun z => AVenhance.FaaDiBruno.flowMatrixCofactorTranspose
        (AVenhance.FaaDiBruno.spatialGradientMatrix Y z) 1 0) =
        (fun z => -spaceGrad (fun y => Y y 1) z 0) := funext hq10
    rw [hfun]
    simp [spaceGrad]
  have h01 :
      (fderiv ℝ
        (fun z => AVenhance.FaaDiBruno.flowMatrixCofactorTranspose
          (AVenhance.FaaDiBruno.spatialGradientMatrix Y z) 0 1) x)
        (basisVec 0) = -spaceGrad (fun z => spaceGrad (fun y => Y y 0) z 1) x 0 := by
    have hfun : (fun z => AVenhance.FaaDiBruno.flowMatrixCofactorTranspose
        (AVenhance.FaaDiBruno.spatialGradientMatrix Y z) 0 1) =
        (fun z => -spaceGrad (fun y => Y y 0) z 1) := funext hq01
    rw [hfun]
    simp [spaceGrad]
  have h11 :
      (fderiv ℝ
        (fun z => AVenhance.FaaDiBruno.flowMatrixCofactorTranspose
          (AVenhance.FaaDiBruno.spatialGradientMatrix Y z) 1 1) x)
        (basisVec 1) = spaceGrad (fun z => spaceGrad (fun y => Y y 0) z 0) x 1 := by
    have hfun : (fun z => AVenhance.FaaDiBruno.flowMatrixCofactorTranspose
        (AVenhance.FaaDiBruno.spatialGradientMatrix Y z) 1 1) =
        (fun z => spaceGrad (fun y => Y y 0) z 0) := funext hq11
    rw [hfun]
    rfl
  fin_cases j
  · simp only [Fin.sum_univ_two]
    change
      (fderiv ℝ
        (fun z => AVenhance.FaaDiBruno.flowMatrixCofactorTranspose
          (AVenhance.FaaDiBruno.spatialGradientMatrix Y z) 0 0) x)
        (basisVec 0) +
      (fderiv ℝ
        (fun z => AVenhance.FaaDiBruno.flowMatrixCofactorTranspose
          (AVenhance.FaaDiBruno.spatialGradientMatrix Y z) 1 0) x)
        (basisVec 1) = 0
    have h00' := h00
    have h10' := h10
    rw [h00', h10']
    rw [TransportPiola.mixed_spaceGrad_commute hY1 x]
    ring
  · simp only [Fin.sum_univ_two]
    change
      (fderiv ℝ
        (fun z => AVenhance.FaaDiBruno.flowMatrixCofactorTranspose
          (AVenhance.FaaDiBruno.spatialGradientMatrix Y z) 0 1) x)
        (basisVec 0) +
      (fderiv ℝ
        (fun z => AVenhance.FaaDiBruno.flowMatrixCofactorTranspose
          (AVenhance.FaaDiBruno.spatialGradientMatrix Y z) 1 1) x)
        (basisVec 1) = 0
    rw [h01, h11]
    rw [TransportPiola.mixed_spaceGrad_commute hY0 x]
    ring

theorem TransportPiola.continuousLinearMap_det_formula
    (L : Vec 2 →L[ℝ] Vec 2) :
    L.det = L (basisVec 0) 0 * L (basisVec 1) 1 -
      L (basisVec 1) 0 * L (basisVec 0) 1 := by
  change LinearMap.det L.toLinearMap = _
  rw [← LinearMap.det_toMatrix' L.toLinearMap, Matrix.det_fin_two]
  simp [LinearMap.toMatrix'_apply, basisVec]

/-- A determinant-one inverse Jacobian obeys the cofactor chain identity
used to transform divergence under a volume-preserving flow. -/
theorem cofactorTranspose_gradient_chain
    {Y : Vec 2 → Vec 2} (x : Vec 2)
    (hdet : (fderiv ℝ Y x).det = 1) :
    ∀ j k : Fin 2, ∑ i : Fin 2,
      AVenhance.FaaDiBruno.flowMatrixCofactorTranspose
        (AVenhance.FaaDiBruno.spatialGradientMatrix Y x) i j *
        (fderiv ℝ Y x (basisVec i)) k = if j = k then 1 else 0 := by
  let A : AVenhance.FaaDiBruno.FlowMatrix :=
    AVenhance.FaaDiBruno.spatialGradientMatrix Y x
  have hdetA : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    have hdet' : A 0 0 * A 1 1 - A 0 1 * A 1 0 =
        (fderiv ℝ Y x).det := by
      simpa [A, AVenhance.FaaDiBruno.spatialGradientMatrix,
        AVenhance.FaaDiBruno.coordinateVector, basisVec] using
        (TransportPiola.continuousLinearMap_det_formula (fderiv ℝ Y x)).symm
    exact hdet'.trans hdet
  have hentry (i k : Fin 2) :
      (fderiv ℝ Y x (basisVec i)) k = A k i := by
    simp [A, AVenhance.FaaDiBruno.spatialGradientMatrix,
      AVenhance.FaaDiBruno.coordinateVector, basisVec]
  intro j k
  fin_cases j <;> fin_cases k
  · simp only [Fin.sum_univ_two]
    change A 1 1 * (fderiv ℝ Y x (basisVec 0)) 0 +
      (-A 1 0) * (fderiv ℝ Y x (basisVec 1)) 0 = 1
    rw [hentry 0 0, hentry 1 0]
    calc
      A 1 1 * A 0 0 + -A 1 0 * A 0 1 =
          A 0 0 * A 1 1 - A 0 1 * A 1 0 := by ring
      _ = 1 := hdetA
  · simp only [Fin.sum_univ_two]
    change A 1 1 * (fderiv ℝ Y x (basisVec 0)) 1 +
      (-A 1 0) * (fderiv ℝ Y x (basisVec 1)) 1 = 0
    rw [hentry 0 1, hentry 1 1]
    ring
  · simp only [Fin.sum_univ_two]
    change (-A 0 1) * (fderiv ℝ Y x (basisVec 0)) 0 +
      A 0 0 * (fderiv ℝ Y x (basisVec 1)) 0 = 0
    rw [hentry 0 0, hentry 1 0]
    ring
  · simp only [Fin.sum_univ_two]
    change (-A 0 1) * (fderiv ℝ Y x (basisVec 0)) 1 +
      A 0 0 * (fderiv ℝ Y x (basisVec 1)) 1 = 1
    rw [hentry 0 1, hentry 1 1]
    calc
      -A 0 1 * A 1 0 + A 0 0 * A 1 1 =
          A 0 0 * A 1 1 - A 0 1 * A 1 0 := by ring
      _ = 1 := hdetA

end AVenhance.Infra.Section5.RelativeError

end
