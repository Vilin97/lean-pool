/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.LimitHessianPointwise

/-! # Neumann Interior -/

@[expose] public section

namespace Homogenization

open scoped ENNReal Manifold Topology

noncomputable section

namespace MeanZeroNeumannPoissonSolution

variable {d : ℕ} {V : Set (Vec d)} {Q : TriadicCube d} {F : Vec d → ℝ}

/-- Local strict-inner weak Hessian estimate for a cube Neumann solution.

This is the direct Neumann-solution consumer of the hlim-free interior
difference-quotient theorem. It is still an interior estimate: boundary
crossing is reserved for the reflected-block enlargement step. -/
theorem exists_hasWeakHessianOn_restrict_hessianCoordL2NormSum_le_of_strict_inner_margin
    (W : MeanZeroNeumannPoissonSolution Q F)
    (hmean : cubeAverage Q F = 0)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hV : IsOpenBoundedConvexDomain V)
    {ρ₁ ρ₂ σ₁ σ₂ ν : ℝ}
    (η : QuantitativeCubeCutoff Q ρ₁ ρ₂)
    (hη_sub : tsupport (η : Vec d → ℝ) ⊆ V)
    (hinnerV : scaledClosedCubeSet Q ρ₁ ⊆ V)
    (θ : QuantitativeCubeCutoff Q σ₁ σ₂)
    (hVν : V ⊆ scaledClosedCubeSet Q ν)
    (hν_nonneg : 0 ≤ ν)
    (hνσ : ν < σ₁)
    (hσ₁_lt_one : σ₁ < 1)
    (hσ₂_nonneg : 0 ≤ σ₂)
    (hσ₂_lt_one : σ₂ < 1)
    (hρ₁_nonneg : 0 ≤ ρ₁) :
    ∃ uS : H1Function (scaledOpenCubeSet Q ρ₁),
      uS.toFun = W.w.toH1Function.toFun ∧
        uS.grad = W.w.toH1Function.grad ∧
          ∃ H : HasWeakHessianOn (scaledOpenCubeSet Q ρ₁) uS,
            H.hessianCoordL2NormSum ≤
              ∑ i : Fin d, ∑ _j : Fin d,
                @WeakPoissonEquationOn.openCubeInnerQuotientHessianSmoothTestBound
                  d Q W.w.toH1Function F i ρ₁ ρ₂ σ₁ σ₂ θ := by
  have hweak : WeakPoissonEquationOn (openCubeSet Q) W.w.toH1Function F :=
    W.weakPoissonEquationOnCube hmean hF
  have hFopen : MemScalarL2 (openCubeSet Q) F := by
    simpa [MemScalarL2, volumeMeasureOn] using
      memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hF
  exact
    hweak.exists_hasWeakHessianOn_restrict_hessianCoordL2NormSum_le_of_strict_inner_margin
      hFopen hV η hη_sub hinnerV θ hVν hν_nonneg hνσ hσ₁_lt_one
      hσ₂_nonneg hσ₂_lt_one hρ₁_nonneg

end MeanZeroNeumannPoissonSolution

end

end Homogenization
