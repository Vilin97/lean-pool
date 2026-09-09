/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketIntervalForcing

/-!
The joined inverse uses coercivity only on the actual history interval.
Its source Hessian need not satisfy a smallness condition on the full
history-plus-forward time interval.
-/

@[expose] public section


noncomputable section

namespace EulerTransversePacketJoin

open Set EulerSmoothLimit EulerLpCylinderTranslation EulerTransversePacketProvider
  EulerPacketProfileRecursion

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le)) {raw : VectorField} (G : Forcing P D raw)

/-- The terminal coordinate of the actual local history, used as forward data. -/
def forwardInitial : InitialData P (D.tail τ hτ.le hτT) where
  value := (B.terminalInitial (G.initial τ hτ hτT.le)).value
  orbit := (B.terminalInitial (G.initial τ hτ hτT.le)).orbit
  mean_zero := (B.terminalInitial (G.initial τ hτ hτT.le)).mean_zero

theorem forwardInitial_eq :
    ((forwardInitial τ hτ hτT B G).value : CylinderL2 P U) =
      B.coordinatePath (G.initial τ hτ hτT.le) ⟨τ,hτ.le,le_rfl⟩ := rfl

end EulerTransversePacketJoin
