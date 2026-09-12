/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.HomologyTheory.FirstHurewicz3
import all LeanPool.HopfProblem.Foundations.Core1
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.HomologyTheory.FirstHurewicz3

/-!
# Hopf problem: lattice · core 2

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

private theorem A₁_fixes_ε : A₁ *ᵥ ε = ε := by decide

private theorem A₂_fixes_ε' : A₂ *ᵥ ε' = ε' := by decide

private theorem M₀_sub_one_mulVec (v : Lattice) : (M₀ - 1) *ᵥ v = ![0, 0, v 1, -v 0] := by
  ext i
  fin_cases i <;> simp [M₀, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.one_apply]

private theorem M₀_sub_one_kernel (v : Lattice) : (M₀ - 1) *ᵥ v = 0 ↔ v 0 = 0 ∧ v 1 = 0 := by
  rw [M₀_sub_one_mulVec]
  constructor
  · intro h
    have h₂ := congrFun h 2
    have h₃ := congrFun h 3
    change v 1 = 0 at h₂
    change -v 0 = 0 at h₃
    exact ⟨neg_eq_zero.mp h₃, h₂⟩
  · rintro ⟨h₀, h₁⟩
    simp [h₀, h₁]

private theorem
    M₀_sub_one_range (v : Lattice) : (∃ w : Lattice, (M₀ - 1) *ᵥ w = v) ↔ v 0 = 0 ∧ v 1 = 0 :=
  by
  constructor
  · rintro ⟨w, rfl⟩
    simp [M₀_sub_one_mulVec]
  · rintro ⟨h₀, h₁⟩
    refine ⟨![-v 3, v 2, 0, 0], ?_⟩
    rw [M₀_sub_one_mulVec]
    ext i
    fin_cases i <;> simp [h₀, h₁]

private theorem A₁_fixed_iff (v : Lattice) : A₁ *ᵥ v = v ↔ v 1 = 2 * v 0 ∧ v 2 = -4 * v 0 := by
  constructor
  · intro h
    have h₁ := congrFun h 1
    have h₂ := congrFun h 2
    have h₃ := congrFun h 3
    simp [A₁, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h₁ h₂ h₃
    omega
  · rintro ⟨h₁, h₂⟩
    ext i
    fin_cases i <;> simp [A₁, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, h₁, h₂] <;> ring

private theorem A₂_fixed_iff (v : Lattice) : A₂ *ᵥ v = v ↔ v 1 = 3 * v 0 ∧ v 2 = -3 * v 0 := by
  constructor
  · intro h
    have h₁ := congrFun h 1
    have h₂ := congrFun h 2
    have h₃ := congrFun h 3
    simp [A₂, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h₁ h₂ h₃
    omega
  · rintro ⟨h₁, h₂⟩
    ext i
    fin_cases i <;> simp [A₂, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, h₁, h₂]
    ring

/-- An integer coordinate vector of length `n`. -/
public
abbrev LocalSystemMatrices.Vec (n : ℕ) :=
  Fin n → ℤ

/-- The linear functional selecting the last coordinate of a rank-four vector. -/
public
def LocalSystemMatrices.lastCoordinate : Vec 4 →ₗ[ℤ] ℤ :=
  LinearMap.proj 3

/-- The two coordinate indices represented by an exterior-square basis element. -/
public
def LocalSystemMatrices.pairIndices : Fin 6 → Fin 2 → Fin 4 :=
  ![![0, 1], ![0, 2], ![0, 3], ![1, 2], ![1, 3], ![2, 3] ]

private def LocalSystemMatrices.exteriorSquare (T : LatticeMatrix) : Matrix (Fin 6) (Fin 6) ℤ :=
  fun i j => (T.submatrix (pairIndices i) (pairIndices j)).det

private def LocalSystemMatrices.tripleIndices : Fin 4 → Fin 3 → Fin 4 :=
  ![![0, 1, 2], ![0, 1, 3], ![0, 2, 3], ![1, 2, 3] ]

private def LocalSystemMatrices.exteriorCube (T : LatticeMatrix) : LatticeMatrix := fun i j =>
  (T.submatrix (tripleIndices i) (tripleIndices j)).det

end Mathoverflow1973

end
