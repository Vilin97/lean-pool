/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/


import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Push
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.ApplyFun
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Common
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Choose
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.SuppressCompilation
import Mathlib.Tactic.Use
import Mathlib.Tactic.Set
import Mathlib.Tactic.Polyrith
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Generalize
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Group.Support
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.InnerProductSpace.PiL2

import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Topology.MetricSpace.Isometry

import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Density

import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real

--import Mathlib.LinearAlgebra.TensorAlgebra.Basic

import LeanPool.OSforGFF.Spacetime.Basic
import LeanPool.OSforGFF.Spacetime.Euclidean

/-!
# Time Reflection Θ and Discrete Symmetries

Time reflection Θ: (t, xbar) ↦ (−t, xbar) as an orthogonal involution on ℝ⁴.
Properties: self-inverse (Θ² = id), measure-preserving, isometric.

Induced actions on test functions: (Θf)(x) = f(Θx) = f(−t, xbar).
Foundation for the OS3 reflection positivity axiom.
-/

open MeasureTheory

namespace QFT

/-- The `timeReflection` declaration. -/
abbrev timeReflection (x : SpaceTime) : SpaceTime :=
  (WithLp.equiv 2 _).symm (Function.update x.ofLp 0 (-x.ofLp 0))

/-- The `timeReflectionMatrix` declaration. -/
def timeReflectionMatrix : Matrix (Fin STDimension) (Fin STDimension) ℝ :=
  Matrix.diagonal (fun i => if i = 0 then -1 else 1)

lemma timeReflectionMatrix_is_orthogonal :
   timeReflectionMatrix ∈ Matrix.orthogonalGroup (Fin STDimension) ℝ := by
      rw [Matrix.mem_orthogonalGroup_iff]
      ext i j
      simp only [timeReflectionMatrix, Matrix.diagonal_transpose,
        Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply, Matrix.one_apply]
      split_ifs <;> norm_num

/-- The `timeReflectionIsometry` declaration. -/
def timeReflectionIsometry : Matrix.orthogonalGroup (Fin STDimension) ℝ :=
  ⟨timeReflectionMatrix, timeReflectionMatrix_is_orthogonal⟩

/-- The `timeReflectionLinear` declaration. -/
def timeReflectionLinear : SpaceTime →ₗ[ℝ] SpaceTime :=
{ toFun := timeReflection
  map_add' x y := by
    refine PiLp.ext fun i => ?_
    simp only [timeReflection, WithLp.equiv_symm_apply]
    rcases eq_or_ne i 0 with h | h
    · subst h; simp [Function.update_self]; ring
    · simp [Function.update_of_ne h]
  map_smul' c x := by
    refine PiLp.ext fun i => ?_
    simp only [timeReflection, RingHom.id_apply, WithLp.equiv_symm_apply]
    rcases eq_or_ne i 0 with h | h
    · subst h; simp [Function.update_self]
    · simp [Function.update_of_ne h] }

/-- The `timeReflectionCLM` declaration. -/
noncomputable def timeReflectionCLM : SpaceTime →L[ℝ] SpaceTime :=
timeReflectionLinear.toContinuousLinearMap (E := SpaceTime) (F' := SpaceTime)

open InnerProductSpace

/-- Time reflection preserves inner products -/
lemma timeReflection_inner_map (x y : SpaceTime) :
    ⟪timeReflection x, timeReflection y⟫_ℝ = ⟪x, y⟫_ℝ := by
  -- Direct proof using fintype inner product
  simp only [inner]
  congr 1
  ext i
  simp only [timeReflection]
  rcases eq_or_ne i 0 with h | h <;> simp [h]

/-- Time reflection as a linear isometry equivalence -/
@[simp] lemma timeReflection_involutive (x : SpaceTime) :
    timeReflection (timeReflection x) = x := by
  refine PiLp.ext fun i => ?_
  simp only [timeReflection, WithLp.equiv_symm_apply]
  rcases eq_or_ne i 0 with h | h
  · subst h; simp [Function.update_self]
  · simp [Function.update_of_ne h]

/-- The `timeReflectionLE` declaration. -/
def timeReflectionLE : SpaceTime ≃ₗᵢ[ℝ] SpaceTime :=
{ toFun := timeReflection
  invFun := timeReflection  -- Time reflection is self-inverse
  left_inv := timeReflection_involutive
  right_inv := timeReflection_involutive
  map_add' := timeReflectionLinear.map_add'
  map_smul' := timeReflectionLinear.map_smul'
  norm_map' := by
    intro x
    change ‖timeReflection x‖ = ‖x‖
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq, timeReflection_inner_map x x] }

/-- Time reflection preserves Lebesgue measure. -/
lemma timeReflection_measurePreserving :
    MeasurePreserving timeReflection volume volume := by
  -- Any linear isometry equivalence preserves the volume measure.
  simpa [timeReflection, timeReflectionLE] using (timeReflectionLE).measurePreserving

example (x : SpaceTime) :
    timeReflectionCLM x =
      Function.update x (0 : Fin STDimension) (-x 0) := rfl

/-- Composition with time reflection as a continuous linear map on **complex-valued**
    test functions. This maps a test function `f` to the function `x ↦ f(timeReflection(x))`,
    where `timeReflection` negates the time coordinate (0th component) while
    preserving spatial coordinates. This version acts on complex test functions and
    is used to formulate the Osterwalder-Schrader star operation.
-/
private lemma timeReflection_hg_upper :
    ∃ (k : ℕ) (C : ℝ), ∀ (x : SpaceTime), ‖x‖ ≤ C * (1 + ‖timeReflectionCLM x‖) ^ k := by
  refine ⟨1, 1, fun x => ?_⟩
  have h_iso : ‖timeReflectionCLM x‖ = ‖x‖ := by
    rw [← LinearIsometryEquiv.norm_map timeReflectionLE x]; rfl
  rw [h_iso]
  simp only [pow_one, one_mul]
  linarith [norm_nonneg x]

/-- The `compTimeReflection` declaration. -/
noncomputable def compTimeReflection : TestFunctionℂ →L[ℝ] TestFunctionℂ :=
  SchwartzMap.compCLM (𝕜 := ℝ)
    (hg := timeReflectionCLM.hasTemperateGrowth)
    (hg_upper := timeReflection_hg_upper)

/-- Composition with time reflection as a continuous linear map on **real-valued**
    test functions. This version will be used when working with positive-time
    subspaces defined over ℝ, so that reflection positivity can be formulated
    without passing through complex scalars.
-/
noncomputable def compTimeReflectionReal : TestFunction →L[ℝ] TestFunction :=
  SchwartzMap.compCLM (𝕜 := ℝ)
    (hg := timeReflectionCLM.hasTemperateGrowth)
    (hg_upper := timeReflection_hg_upper)

/-- Time reflection is linear on real test functions. -/
lemma compTimeReflectionReal_linear_combination {n : ℕ} (f : Fin n → TestFunction) (c : Fin n → ℝ) :
    compTimeReflectionReal (∑ i, c i • f i) = ∑ i, c i • compTimeReflectionReal (f i) := by
  -- This follows directly from the linearity of the continuous linear map compTimeReflectionReal
  simp only [map_sum, map_smul]

end QFT
