/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.TransportFlowBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.TransportPiolaFlow
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.SpaceGrad

/-! # RelativeError: pointwise size of the Piola vector -/

@[expose] public section

noncomputable section

open Homogenization
open AVenhance
open scoped ContDiff

namespace AVenhance.Infra.Section5.RelativeError

/-- The gradient matrix acts on a vector as the Fréchet derivative does. -/
theorem spatialGradientMatrix_mulVec_eq_fderiv
    {F : Vec 2 → Vec 2} (x : Vec 2) (v : Vec 2) :
    Matrix.mulVec (FaaDiBruno.spatialGradientMatrix F x) v =
      fderiv ℝ F x v := by
  have hv : v = v 0 • basisVec 0 + v 1 • basisVec 1 := by
    ext i
    fin_cases i <;> simp [basisVec]
  rw [hv, map_add, map_smul, map_smul]
  ext i
  simp [Matrix.mulVec, dotProduct, FaaDiBruno.spatialGradientMatrix,
    FaaDiBruno.coordinateVector, basisVec, Fin.sum_univ_two]
  ring

end AVenhance.Infra.Section5.RelativeError

end
