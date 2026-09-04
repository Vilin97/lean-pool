/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Foundations.CanonicalProduct
import all LeanPool.HopfProblem.Foundations.CanonicalProduct

/-!
# Hopf problem: main theorem · core 1

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

public
theorem complexManifold_isRealManifold {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] (M : Type*) [TopologicalSpace M] [ChartedSpace E M]
    (n : ℕ∞ω) [IsManifold 𝓘(ℂ, E) n M] : IsManifold 𝓘(ℝ, E) n M := by
  apply isManifold_of_contDiffOn 𝓘(ℝ, E) n M
  intro e e' he he'
  have h := (contDiffGroupoid n 𝓘(ℂ, E)).compatible he he'
  have hc : ContDiffOn ℂ n (e.symm ≫ₕ e') (e.symm ≫ₕ e').source := by
    simpa only [contDiffPregroupoid, mfld_simps] using h.1
  simpa only [mfld_simps] using hc.restrict_scalars ℝ

end Mathoverflow1973

end
