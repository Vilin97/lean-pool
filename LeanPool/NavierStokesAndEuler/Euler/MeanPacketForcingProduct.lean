/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketForcingAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketProvider
public import LeanPool.NavierStokesAndEuler.Euler.LpSmoothCoefficientProduct
import LeanPool.NavierStokesAndEuler.Euler.LpSmoothCoefficientContinuity

/-! Actual multiplication closure for admissible mean forcing. -/

@[expose] public section


noncomputable section

namespace EulerMeanPacketProvider.Forcing

open Set EulerSmoothLimit EulerMeanCoefficients EulerPacketProfileRecursion
  EulerLpSmoothCoefficientProduct

variable {D : Data} {raw : VectorField}

/-- Multiplying the raw field by a genuinely bounded smooth coefficient path
preserves all actual L² spatial jets and their time continuity. -/
def multiply (G : Forcing D raw) (A : SmoothCoefficientPath (Icc (0 : ℝ) D.T) (Space →L[ℝ] Space)) :
    Forcing D (fun z => A.field (D.clamp z.1) z.2.1 (raw z)) :=
  ofSlices (fun r => product A (D.clamp r) (G.slices r))
    (fun n => by
      simpa only [Data.clamp_coe] using continuous_product_jet A
        (fun t : Icc (0 : ℝ) D.T => G.slices t) G.jets_continuous n)
    (fun t x θ => by rw [G.raw_eq t x θ]; rfl)

end EulerMeanPacketProvider.Forcing
