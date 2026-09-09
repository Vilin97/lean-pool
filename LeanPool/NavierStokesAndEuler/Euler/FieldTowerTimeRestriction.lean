/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.AllOrderCorrectionData
import LeanPool.NavierStokesAndEuler.Euler.FieldTowerRepresentative

/-! A genuine derivative at one Sobolev order gives the same derivative at
all lower orders of the coherent towers. -/

@[expose] public section


noncomputable section

namespace EulerAllOrderCorrectionData.FieldTower

open Set EulerCylinderSobolevSpace EulerVolterraConvolution

variable {P T : ℝ} [Fact (0 < P)]
  (A B : EulerAllOrderCorrectionData.FieldTower P T)

/-- Cache the standard `NormedAddCommGroup (SobolevSpace P q)` instance to shorten typeclass
synthesis. -/
local instance restrictionGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace P q) := inferInstance
/-- Cache the standard `NormedSpace ℝ (SobolevSpace P q)` instance to shorten typeclass
synthesis. -/
local instance restrictionSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace P q) := inferInstance
/-- Cache the standard `TopologicalSpace (SobolevSpace P q)` instance to shorten typeclass
synthesis. -/
local instance restrictionTopology (q : ℕ) : TopologicalSpace (SobolevSpace P q) :=
  (inferInstance : PseudoMetricSpace (SobolevSpace P q)).toUniformSpace.toTopologicalSpace

theorem realization_hasDerivWithinAt_of_le {p q : ℕ} (h : q ≤ p)
    (hT : 0 ≤ T) (t : Icc (0 : ℝ) T)
    (hd : HasDerivWithinAt (extendPath T hT (A.realization p))
      (B.realization p t) (Icc (0 : ℝ) T) t) :
    HasDerivWithinAt (extendPath T hT (A.realization q))
      (B.realization q t) (Icc (0 : ℝ) T) t := by
  have hder : HasDerivWithinAt
      (fun r => restrictOperator P h (extendPath T hT (A.realization p) r))
      (restrictOperator P h (B.realization p t)) (Icc (0 : ℝ) T) t :=
    (restrictOperator P h).hasFDerivAt.comp_hasDerivWithinAt (t : ℝ) hd
  have he : (fun r => restrictOperator P h (extendPath T hT (A.realization p) r)) =
      extendPath T hT (A.realization q) :=
    funext (fun r => A.restrict_realization h (projIcc 0 T hT r))
  rw [he,B.restrict_realization h t] at hder
  exact hder

theorem realization_hasDerivAt_of_le {p q : ℕ} (h : q ≤ p)
    (hT : 0 ≤ T) (t : Icc (0 : ℝ) T)
    (hd : HasDerivAt (extendPath T hT (A.realization p))
      (B.realization p t) t) :
    HasDerivAt (extendPath T hT (A.realization q)) (B.realization q t) t := by
  have hder : HasDerivAt
      (fun r => restrictOperator P h (extendPath T hT (A.realization p) r))
      (restrictOperator P h (B.realization p t)) t :=
    (restrictOperator P h).hasFDerivAt.comp_hasDerivAt (t : ℝ) hd
  have he : (fun r => restrictOperator P h (extendPath T hT (A.realization p) r)) =
      extendPath T hT (A.realization q) :=
    funext (fun r => A.restrict_realization h (projIcc 0 T hT r))
  rw [he,B.restrict_realization h t] at hder
  exact hder

end EulerAllOrderCorrectionData.FieldTower
