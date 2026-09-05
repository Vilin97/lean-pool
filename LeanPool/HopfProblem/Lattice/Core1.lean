/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Foundations.LineBundleTransport
import all LeanPool.HopfProblem.Foundations.Core1
import all LeanPool.HopfProblem.Foundations.LineBundleTransport

/-!
# Hopf problem: lattice · core 1

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

/-- The rank-four integer lattice in coordinate form. -/
public
abbrev Lattice :=
  Fin 4 → ℤ

private def T₁ : LatticeMatrix :=
  !![1, 0, -6, 2; 0, -1, 1, 1; 0, -1, 0, 1; 0, 0, 0, 1]

private def T₂ : LatticeMatrix :=
  !![1, 6, 0, -3; 0, 0, -1, 1; 0, 1, 0, 0; 0, 0, 0, 1]

private def T₀ : LatticeMatrix :=
  !![1, 0, 0, 1; 0, 1, -1, 0; 0, 0, 1, 0; 0, 0, 0, 1]

private def A₁ : LatticeMatrix :=
  !![1, 0, 0, 0; 6, 0, 1, 0; -6, -1, -1, 0; -2, 1, 0, 1]

private def A₂ : LatticeMatrix :=
  !![1, 0, 0, 0; 0, 0, -1, 0; -6, 1, 0, 0; 3, 0, 1, 1]

private def M₀ : LatticeMatrix :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 1, 1, 0; -1, 0, 0, 1]

private def B₀ : Matrix (Fin 2) (Fin 2) ℤ :=
  !![0, 1; -1, 0]

private theorem T₁_cube : T₁ ^ 3 = 1 := by decide

private theorem T₂_fourth : T₂ ^ 4 = 1 := by decide

private theorem A₁_eq_transpose_sq : A₁ = (T₁ ^ 2).transpose := by decide

private theorem A₂_eq_transpose_cube : A₂ = (T₂ ^ 3).transpose := by decide

end Mathoverflow1973

end
