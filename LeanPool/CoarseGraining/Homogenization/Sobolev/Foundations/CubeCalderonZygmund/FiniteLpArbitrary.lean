/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.FiniteLpW10pLimit
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.FiniteLpLimitEquation
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.FiniteLpLimitBound

/-!
# Arbitrary-data finite-`L^p` cube Calderón--Zygmund theorem

This file closes the finite-exponent cube estimate for arbitrary `L^p` vector
data by packaging the canonical zero-trace solution limit.  The constant and
normalized estimate are inherited unchanged from the canonical gradient
limit.
-/

@[expose] public section

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

/-- For every finite exponent and arbitrary `L^p` cube datum, there is a
zero-trace `W^{1,p}` solution satisfying the scale-uniform normalized
Calderón--Zygmund estimate. -/
theorem exists_centeredCubeW10pScalarDivergenceSolution_cz
    (d : ℕ) [NeZero d] (q : FiniteLpExponent) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (m : ℤ) (sigma0 : ℝ)
        (h : CubeEuclideanLpField (originCube d m) q),
        0 < sigma0 →
          ∃ w : W10pFunction (openCubeSet (originCube d m)) q.exponent,
            IsCenteredCubeW10pScalarDivergenceSolution m sigma0 w h ∧
              (centeredCubeDomain d m).normalizedEuclideanLpENorm
                  q.exponent w.grad ≤
                C * (ENNReal.ofReal sigma0)⁻¹ *
                  (centeredCubeDomain d m).normalizedEuclideanLpENorm
                    q.exponent h.toField := by
  obtain ⟨C, hCtop, hC⟩ := INTERNAL.finiteLpGradientLimit_cz d q
  refine ⟨C, hCtop, ?_⟩
  intro m sigma0 h hsigma0
  let w : W10pFunction (openCubeSet (originCube d m)) q.exponent :=
    INTERNAL.finiteLpW10pSolutionLimit q m hsigma0 h
  refine ⟨w, ?_, ?_⟩
  · intro phi
    simpa only [w, INTERNAL.finiteLpW10pSolutionLimit_grad] using
      INTERNAL.finiteLpGradientLimit_normalized_weak d q m hsigma0 h phi
  · simpa only [w, INTERNAL.finiteLpW10pSolutionLimit_grad] using
      hC m sigma0 h hsigma0

end CubeCalderonZygmund

end

end Homogenization
