/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketForcingProduct
public import LeanPool.NavierStokesAndEuler.Euler.SmoothL2CoefficientPath

/-!
# Nonlinear closure of actual admissible mean forcing

Sobolev evaluation supplies bounded coefficients from one actual smooth L²
factor. Consequently finite-dimensional bilinear products preserve the
literal spatial L² jets and their time continuity without an extra product
regularity assumption.
-/

@[expose] public section


noncomputable section

namespace EulerMeanPacketProvider

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerMeanSobolevBoundedField EulerPacketPointJets EulerPacketProfileRecursion

namespace Forcing

variable {D : Data} {raw raw' : VectorField}

/-- Admissibility depends only on the raw field on the actual time interval. -/
def congr (G : Forcing D raw)
    (heq : ∀ (t : Icc (0 : ℝ) D.T) x θ, raw' (t, (x, θ)) = raw (t, (x, θ))) : Forcing D raw' where
  slices := G.slices
  jets_continuous := G.jets_continuous
  path := G.path
  path_eq := G.path_eq
  raw_eq t x θ := (heq t x θ).trans (G.raw_eq t x θ)

/-- A literal bilinear product of two admissible fields is admissible. -/
def bilinear (G : Forcing D raw) (H : Forcing D raw')
    (B : Space →L[ℝ] Space →L[ℝ] Space) : Forcing D (fun z => B (raw z) (raw' z)) := by
  let A := SmoothCoefficientPath.map B
    (coefficientPath (fun t : Icc (0 : ℝ) D.T => G.slices t) G.jets_continuous)
  apply (H.multiply A).congr
  intro t x θ
  simp only [A, Data.clamp_coe, SmoothCoefficientPath.map_apply, coefficientPath_apply,
    G.raw_eq t x θ]

end Forcing

theorem admissible_bilinear (D : Data) (raw raw' : VectorField)
    (h : Nonempty (Forcing D raw)) (h' : Nonempty (Forcing D raw'))
    (B : Space →L[ℝ] Space →L[ℝ] Space) :
    Nonempty (Forcing D (fun z => B (raw z) (raw' z))) :=
  ⟨(Classical.choice h).bilinear (Classical.choice h') B⟩

end EulerMeanPacketProvider
