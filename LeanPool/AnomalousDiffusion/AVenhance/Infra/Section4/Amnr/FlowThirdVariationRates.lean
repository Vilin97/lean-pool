/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.VelocityHigherRates

/-! Quantitative actual third spatial flow operators. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open AVenhance.Infra.Flow

instance FlowThirdVariationRates.amnrBilinearNorm :
    NormedAddCommGroup (Vec 2 →L[ℝ] Vec 2 →L[ℝ] Vec 2) := inferInstance
instance FlowThirdVariationRates.amnrBilinearSpace :
    NormedSpace ℝ (Vec 2 →L[ℝ] Vec 2 →L[ℝ] Vec 2) := inferInstance

end AVenhance.Infra.Section4
