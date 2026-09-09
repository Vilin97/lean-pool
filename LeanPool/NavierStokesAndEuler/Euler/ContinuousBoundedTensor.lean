/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.FinitePathTensor
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

@[expose] public section

/-! Transposing a tensor with continuous bounded path values gives an
actual continuous path of bounded tensor fields. Finite coordinates prove
continuity; the norm estimate uses the original multilinear map directly
and therefore has constant one. -/

noncomputable section


open scoped ContDiff BoundedContinuousFunction

namespace EulerContinuousBoundedTensor

variable {K X E V : Type*} [TopologicalSpace K] [CompactSpace K]
  [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

private local instance (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] V) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] V) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (X →ᵇ (E [×n]→L[ℝ] V)) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (X →ᵇ (E [×n]→L[ℝ] V)) := inferInstance

private def coordinates (n : ℕ) :
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

private def reassembly (n : ℕ) :
    ((Fin n → Fin (Module.finrank ℝ E)) → V) →L[ℝ] (E [×n]→L[ℝ] V) :=
  ((coordinates (E := E) (V := V) n).toLinearMap.leftInverse).toContinuousLinearMap

private theorem reassembly_coordinates (n : ℕ) (A : E [×n]→L[ℝ] V) :
    reassembly n (coordinates n A) = A :=
  LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr (coordinates_injective n)) A

private def tupleBounded {ι : Type*} [Fintype ι] :
    (ι → (X →ᵇ V)) →L[ℝ] (X →ᵇ (ι → V)) := by
  classical
  exact ∑ i : ι,
    ((ContinuousLinearMap.single ℝ (fun _ : ι => V) i).compLeftContinuousBounded X).comp
      (ContinuousLinearMap.proj i)

omit [FiniteDimensional ℝ V] in
private theorem tupleBounded_apply {ι : Type*} [Fintype ι]
    (u : ι → (X →ᵇ V)) (x : X) (i : ι) :
    tupleBounded u x i = u i x := by
  classical
  simp [tupleBounded]

def tensorPath (n : ℕ) (A : E [×n]→L[ℝ] C(K, X →ᵇ V)) :
    C(K, X →ᵇ (E [×n]→L[ℝ] V)) where
  toFun t := (reassembly (E := E) (V := V) n).compLeftContinuousBounded X
    (tupleBounded (fun w => A (fun i => Module.finBasis ℝ E (w i)) t))
  continuous_toFun :=
    ((reassembly (E := E) (V := V) n).compLeftContinuousBounded X).continuous.comp
      ((tupleBounded (X := X) (V := V)).continuous.comp
        (continuous_pi (fun w => (A (fun i => Module.finBasis ℝ E (w i))).continuous)))

omit [CompactSpace K] in
theorem tensorPath_eq (n : ℕ) (A : E [×n]→L[ℝ] C(K, X →ᵇ V)) (t : K) (x : X) :
    tensorPath n A t x = (BoundedContinuousFunction.evalCLM ℝ x).compContinuousMultilinearMap
      ((ContinuousMap.evalCLM ℝ t).compContinuousMultilinearMap A) := by
  change reassembly n (tupleBounded _ x) = _
  have he : tupleBounded (fun w => A (fun i => Module.finBasis ℝ E (w i)) t) x =
      coordinates n ((BoundedContinuousFunction.evalCLM ℝ x).compContinuousMultilinearMap
        ((ContinuousMap.evalCLM ℝ t).compContinuousMultilinearMap A)) := by
    funext w
    rw [tupleBounded_apply]
    rfl
  rw [he, reassembly_coordinates]

omit [CompactSpace K] in
@[simp] theorem tensorPath_apply (n : ℕ) (A : E [×n]→L[ℝ] C(K, X →ᵇ V))
    (t : K) (x : X) (v : Fin n → E) : tensorPath n A t x v = A v t x := by
  rw [tensorPath_eq]
  rfl

private local instance (n : ℕ) : NormedAddCommGroup (C(K, X →ᵇ (E [×n]→L[ℝ] V))) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (C(K, X →ᵇ (E [×n]→L[ℝ] V))) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] C(K, X →ᵇ V)) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] C(K, X →ᵇ V)) := inferInstance

theorem tensorPath_norm_le (n : ℕ) (A : E [×n]→L[ℝ] C(K, X →ᵇ V)) :
    ‖tensorPath n A‖ ≤ ‖A‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg A)).2
  intro t
  apply (BoundedContinuousFunction.norm_le (norm_nonneg A)).2
  intro x
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg A)
  intro v
  rw [tensorPath_apply]
  exact (((A v t).norm_coe_le_norm x).trans ((A v).norm_coe_le_norm t)).trans (A.le_opNorm v)

def tensorPathLinear (n : ℕ) :
    (E [×n]→L[ℝ] C(K, X →ᵇ V)) →ₗ[ℝ] C(K, X →ᵇ (E [×n]→L[ℝ] V)) where
  toFun := tensorPath n
  map_add' A B := by
    apply ContinuousMap.ext
    intro t
    apply BoundedContinuousFunction.ext
    intro x
    apply ContinuousMultilinearMap.ext
    intro v
    simp only [tensorPath_apply, add_apply, ContinuousMap.add_apply,
      BoundedContinuousFunction.add_apply]
  map_smul' c A := by
    apply ContinuousMap.ext
    intro t
    apply BoundedContinuousFunction.ext
    intro x
    apply ContinuousMultilinearMap.ext
    intro v
    simp only [tensorPath_apply, smul_apply, ContinuousMap.smul_apply,
      BoundedContinuousFunction.smul_apply, RingHom.id_apply]

def tensorPathMap (n : ℕ) :
    (E [×n]→L[ℝ] C(K, X →ᵇ V)) →L[ℝ] C(K, X →ᵇ (E [×n]→L[ℝ] V)) where
  toLinearMap := tensorPathLinear n
  cont := AddMonoidHomClass.continuous_of_bound
    (tensorPathLinear (K := K) (X := X) (E := E) (V := V) n) 1
    (fun A => by
      change ‖tensorPath n A‖ ≤ 1 * ‖A‖
      simpa only [one_mul] using tensorPath_norm_le n A)

@[simp] theorem tensorPathMap_apply (n : ℕ) (A : E [×n]→L[ℝ] C(K, X →ᵇ V))
    (t : K) (x : X) (v : Fin n → E) : tensorPathMap n A t x v = A v t x :=
  tensorPath_apply n A t x v

theorem tensorPathMap_norm_le (n : ℕ) :
    ‖tensorPathMap (K := K) (X := X) (E := E) (V := V) n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro A
  change ‖tensorPath n A‖ ≤ 1 * ‖A‖
  simpa only [one_mul] using tensorPath_norm_le n A

theorem tensorPath_iteratedFDeriv (f : E → C(K, X →ᵇ V)) (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (a : E) (t : K) (x : X) :
    tensorPathMap n (iteratedFDeriv ℝ n f a) t x =
      iteratedFDeriv ℝ n (fun b => f b t x) a := by
  change tensorPath n (iteratedFDeriv ℝ n f a) t x = _
  rw [tensorPath_eq]
  have ht := (ContinuousMap.evalCLM ℝ t).iteratedFDeriv_comp_left (x := a) hf.contDiffAt
    (show (n : ℕ∞) ≤ ∞ by simp)
  rw [← ht]
  exact ((BoundedContinuousFunction.evalCLM ℝ x).iteratedFDeriv_comp_left
    ((ContinuousMap.evalCLM ℝ t).contDiff.comp hf).contDiffAt
    (show (n : ℕ∞) ≤ ∞ by simp)).symm

end EulerContinuousBoundedTensor
