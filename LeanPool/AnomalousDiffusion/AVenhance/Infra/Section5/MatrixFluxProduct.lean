/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FluxDivergence
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.TransportIdentities

/-! Matrix-vector divergence with column divergence and row Jacobians. -/

@[expose] public section

namespace AVenhance.Infra.Section5

open AVenhance Homogenization

/-- The divergence product rule in the matrix convention used by the
corrector flux: column divergence pairs with the vector, while the remaining
contribution is the Frobenius contraction with its row-Jacobian. -/
theorem vecDiv_matrixMulVec_frob
    {A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {V : Vec 2 → Vec 2}
    {x : Vec 2} {LA : Fin 2 → Fin 2 → Vec 2 →L[ℝ] ℝ}
    {LV : Vec 2 →L[ℝ] Vec 2}
    (hA : ∀ i j, HasFDerivAt (fun y => A y i j) (LA i j) x)
    (hV : HasFDerivAt V LV x) :
    vecDiv (fun y => (A y).mulVec (V y)) x =
      vecDot (matDiv A x) (V x) + frob (A x) (gradMatrix V x) := by
  have hmat (j : Fin 2) : matDiv A x j =
      ∑ i : Fin 2, (LA i j) (basisVec i) := by
    unfold matDiv
    apply Finset.sum_congr rfl
    intro i hi
    rw [spaceGrad, (hA i j).fderiv]
  have hgrad (i j : Fin 2) : gradMatrix V x i j =
      (LV (basisVec i)) j := by
    change spaceGrad (fun y => V y j) x i = _
    have hcomp : HasFDerivAt (fun y => V y j)
        ((ContinuousLinearMap.proj j).comp LV) x := by
      exact (ContinuousLinearMap.proj j).hasFDerivAt.comp x hV
    rw [spaceGrad, hcomp.fderiv]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  rw [vecDiv_matrixMulVec hA hV]
  simp only [vecDot, frob, Fin.sum_univ_two]
  simp only [hmat, hgrad, Fin.sum_univ_two]
  ring

end AVenhance.Infra.Section5
