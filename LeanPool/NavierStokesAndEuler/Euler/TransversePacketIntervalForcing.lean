/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketIntervalData
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketHistory
public import LeanPool.NavierStokesAndEuler.Euler.CylinderTimePrecomposition

@[expose] public section

/-! Actual admissible forcing restriction and the history trace used as forward initial data. -/

noncomputable section

namespace EulerTransversePacketProvider

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerTimeIntervalRestriction
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths EulerCylinderSmoothOrbit
  EulerPacketProfileRecursion EulerCylinderAngleAverage
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {raw : VectorField}

def shiftedRaw (τ : ℝ) (raw : VectorField) : VectorField := fun z => raw (τ+z.1,z.2)

namespace Forcing

variable (G : Forcing P D raw)

/-- Restriction keeps the literal original forcing on the history interval. -/
def initial (τ : ℝ) (hτ : 0 < τ) (hτT : τ ≤ D.T) : Forcing P (D.initial τ hτ hτT) raw where
  path := G.path.comp (initialInclusion D.T τ hτT)
  path_orbit := timeComp_orbit_contDiff P
    (includePath P D.support D.support_measurable G.path) G.path_orbit (initialInclusion D.T τ hτT)
  raw_eq t x θ := by
    have h := G.raw_eq (initialInclusion D.T τ hτT t) x θ
    have he := congrFun (pointField_timeComp P
      (includePath P D.support D.support_measurable G.path) G.path_orbit
      (initialInclusion D.T τ hτT) t) (x,(θ : AddCircle P))
    exact h.trans he.symm
  mean_zero t := G.mean_zero (initialInclusion D.T τ hτT t)

/-- The forward forcing uses elapsed time s and the literal source time τ+s. -/
def tail (τ : ℝ) (hτ : 0 ≤ τ) (hτT : τ < D.T) :
    Forcing P (D.tail τ hτ hτT) (shiftedRaw τ raw) where
  path := G.path.comp (tailInclusion D.T τ hτ)
  path_orbit := timeComp_orbit_contDiff P
    (includePath P D.support D.support_measurable G.path) G.path_orbit (tailInclusion D.T τ hτ)
  raw_eq t x θ := by
    have h := G.raw_eq (tailInclusion D.T τ hτ t) x θ
    have he := congrFun (pointField_timeComp P
      (includePath P D.support D.support_measurable G.path) G.path_orbit
      (tailInclusion D.T τ hτ) t) (x,(θ : AddCircle P))
    exact h.trans he.symm
  mean_zero t := G.mean_zero (tailInclusion D.T τ hτ t)

end Forcing

namespace HistoryData

variable (B : HistoryData D) (G : Forcing P D raw)

/-- The genuine terminal coordinate velocity of the history problem,
with its actual support, mixed smoothness, and zero angular mean. -/
def terminalInitial : InitialData P D where
  value := ⟨B.coordinatePath G ⟨D.T,D.T_pos.le,le_rfl⟩,
    B.coordinatePath_supported G ⟨D.T,D.T_pos.le,le_rfl⟩⟩
  orbit := (ContinuousMap.evalCLM ℝ ⟨D.T,D.T_pos.le,le_rfl⟩ :
    C(Icc (0 : ℝ) D.T,CylinderL2 P U) →L[ℝ] CylinderL2 P U).contDiff.comp (B.coordinatePath_orbit G)
  mean_zero := B.coordinatePath_mean_zero G ⟨D.T,D.T_pos.le,le_rfl⟩

/-- The history trace in the same fixed reference-plane coordinates is the
actual initial datum passed to the forward interval. -/
def forwardInitial (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T) :
    InitialData P (D.tail τ hτ.le hτT) where
  value := ((B.initial τ hτ hτT.le).terminalInitial (G.initial τ hτ hτT.le)).value
  orbit := ((B.initial τ hτ hτT.le).terminalInitial (G.initial τ hτ hτT.le)).orbit
  mean_zero := ((B.initial τ hτ hτT.le).terminalInitial (G.initial τ hτ hτT.le)).mean_zero

theorem forwardInitial_eq (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T) :
    ((B.forwardInitial G τ hτ hτT).value : CylinderL2 P U) =
      (B.initial τ hτ hτT.le).coordinatePath (G.initial τ hτ hτT.le) ⟨τ,hτ.le,le_rfl⟩ := rfl

end HistoryData
end EulerTransversePacketProvider
