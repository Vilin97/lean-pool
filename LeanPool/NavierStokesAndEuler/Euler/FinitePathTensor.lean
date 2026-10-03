/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.ContinuousMap.Compact
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
public import LeanPool.NavierStokesAndEuler.ForMathlib.ElaborationShortcuts

/-! A continuous multilinear map with continuous-path values gives a
genuine continuous path of tensors. Finite spatial coordinates establish
continuity; the actual operator norm is preserved without a coordinate
count in the bound. -/

@[expose] public section


noncomputable section


open scoped ContDiff

namespace EulerFinitePathTensor

variable {K E V : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Coordinates, given by `ContinuousLinearMap.pi (fun w => (ContinuousLinearMap.id ℝ (E
[×n]→L[ℝ] V)).flipMultilinear (fun i => Module.finBasis ℝ E (w i)))`. -/
def coordinates (n : ℕ) :
    (E [×n]→L[ℝ] V) →L[ℝ] ((Fin n → Fin (Module.finrank ℝ E)) → V) :=
  ContinuousLinearMap.pi (fun w =>
    (ContinuousLinearMap.id ℝ (E [×n]→L[ℝ] V)).flipMultilinear
      (fun i => Module.finBasis ℝ E (w i)))

omit [FiniteDimensional ℝ V] in
private theorem coordinates_injective (n : ℕ) :
    Function.Injective (coordinates (E := E) (V := V) n) := by
  intro A B h
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ : Fin n => Module.finBasis ℝ E)
  intro w
  exact congrFun h w

/-- Reassembly, given by `((coordinates (E := E) (V := V)
n).toLinearMap.leftInverse).toContinuousLinearMap`. -/
def reassembly (n : ℕ) :
    ((Fin n → Fin (Module.finrank ℝ E)) → V) →L[ℝ] (E [×n]→L[ℝ] V) :=
  ((coordinates (E := E) (V := V) n).toLinearMap.leftInverse).toContinuousLinearMap

private theorem reassembly_coordinates (n : ℕ) (A : E [×n]→L[ℝ] V) :
    reassembly (E := E) (V := V) n (coordinates (E := E) (V := V) n A) = A :=
  LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr (coordinates_injective (E := E) (V := V) n)) A

/-- Tensor path, bundling `toFun`, `continuous_toFun`. -/
def tensorPath (n : ℕ) (A : E [×n]→L[ℝ] C(K, V)) : C(K, E [×n]→L[ℝ] V) where
  toFun t := reassembly (E := E) (V := V) n (fun w => A (fun i => Module.finBasis ℝ E (w i)) t)
  continuous_toFun := (reassembly (E := E) (V := V) n).continuous.comp
    (continuous_pi (fun w => (A (fun i => Module.finBasis ℝ E (w i))).continuous))

omit [CompactSpace K] in
theorem tensorPath_eq (n : ℕ) (A : E [×n]→L[ℝ] C(K, V)) (t : K) :
    tensorPath n A t = (ContinuousMap.evalCLM ℝ t).compContinuousMultilinearMap A := by
  change reassembly (E := E) (V := V) n (coordinates (E := E) (V := V) n
    ((ContinuousMap.evalCLM ℝ t).compContinuousMultilinearMap A)) = _
  exact reassembly_coordinates n _

omit [CompactSpace K] in
@[simp] theorem tensorPath_apply (n : ℕ) (A : E [×n]→L[ℝ] C(K, V))
    (t : K) (v : Fin n → E) : tensorPath n A t v = A v t := by
  rw [tensorPath_eq]
  rfl

theorem tensorPath_norm_le (n : ℕ) (A : E [×n]→L[ℝ] C(K, V)) :
    ‖tensorPath n A‖ ≤ ‖A‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg A)).2
  intro t
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg A)
  intro v
  rw [tensorPath_apply]
  exact ((A v).norm_coe_le_norm t).trans (A.le_opNorm v)

/-- Tensor path linear, bundling `toFun`, `map_add`, `map_smul`. -/
def tensorPathLinear (n : ℕ) :
    (E [×n]→L[ℝ] C(K,V)) →ₗ[ℝ] C(K, E [×n]→L[ℝ] V) where
  toFun := tensorPath n
  map_add' A B := by
    apply ContinuousMap.ext
    intro t
    apply ContinuousMultilinearMap.ext
    intro v
    simp only [tensorPath_apply, add_apply, ContinuousMap.add_apply]
  map_smul' c A := by
    apply ContinuousMap.ext
    intro t
    apply ContinuousMultilinearMap.ext
    intro v
    exact (tensorPath_apply n _ t v).trans (congrArg (c • ·) (tensorPath_apply n A t v)).symm

/-- Tensor path map, bundling `toLinearMap`, `cont`, `1`. -/
def tensorPathMap (n : ℕ) :
    (E [×n]→L[ℝ] C(K,V)) →L[ℝ] C(K, E [×n]→L[ℝ] V) where
  toLinearMap := tensorPathLinear n
  cont := AddMonoidHomClass.continuous_of_bound (tensorPathLinear (K := K) (E := E) (V := V) n)
    1 (fun A => by exact (tensorPath_norm_le n A).trans_eq (one_mul _).symm)

@[simp] theorem tensorPathMap_apply (n : ℕ) (A : E [×n]→L[ℝ] C(K, V))
    (t : K) (v : Fin n → E) : tensorPathMap (K := K) (E := E) (V := V) n A t v = A v t :=
  tensorPath_apply n A t v

theorem tensorPath_iteratedFDeriv (f : E → C(K, V)) (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (x : E) (t : K) :
    tensorPathMap (K := K) (E := E) (V := V) n (iteratedFDeriv ℝ n f x) t =
      iteratedFDeriv ℝ n (fun y => f y t) x := by
  change tensorPath n (iteratedFDeriv ℝ n f x) t = _
  rw [tensorPath_eq]
  exact ((ContinuousMap.evalCLM (M := V) ℝ t).iteratedFDeriv_comp_left hf.contDiffAt
    (show (n : ℕ∞) ≤ ∞ by simp)).symm

end EulerFinitePathTensor
