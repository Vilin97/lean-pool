/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinExistence
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.CutoffNesting

/-! Nested-cutoff coefficient maps for the classical Galerkin sequence. -/

@[expose] public section

noncomputable section

open MeasureTheory
open AVenhance.Infra.Parabolic.FourierGalerkin

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance classicalConvergenceMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance classicalConvergenceMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance classicalConvergenceProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Classical

/-- Restrict a coefficient vector from a larger symmetric Fourier box to a smaller one. -/
def classicalGalerkinCoefficientsRestrict {M N : ℕ} (hMN : M ≤ N)
    (c : Coefficients (RealFourierDimension N)) :
    Coefficients (RealFourierDimension M) :=
  WithLp.toLp 2 (fun i => c (realFourierIndexLiftFin hMN i))

@[simp]
theorem classicalGalerkinCoefficientsRestrict_apply {M N : ℕ} (hMN : M ≤ N)
    (c : Coefficients (RealFourierDimension N))
    (i : Fin (RealFourierDimension M)) :
    classicalGalerkinCoefficientsRestrict hMN c i =
      c (realFourierIndexLiftFin hMN i) := rfl

end AVenhance.Infra.Classical

end
