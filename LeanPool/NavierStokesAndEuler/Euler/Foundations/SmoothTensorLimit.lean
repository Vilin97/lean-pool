/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.CylinderSobolev
import LeanPool.NavierStokesAndEuler.Euler.Foundations.MollifierTensors
import LeanPool.NavierStokesAndEuler.Euler.Foundations.SmoothUniformLimit

/-! Smoothness of uniform limits of complete Fréchet derivative towers. -/

@[expose] public section

noncomputable section

namespace EulerSmoothTensorLimit

open Filter
open scoped ContDiff Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A uniformly Cauchy sequence at every actual Fréchet derivative order has a genuine smooth limit.
-/
theorem exists_smooth_limit (f : ℕ → E → F) (hf : ∀ k, ContDiff ℝ ∞ (f k))
    (hC : ∀ m, UniformCauchySeqOn (fun k => iteratedFDeriv ℝ m (f k)) atTop Set.univ) :
    ∃ g : E → F, TendstoUniformly f g atTop ∧ ContDiff ℝ ∞ g := by
  let L (m : ℕ) : (E [×(m+1)]→L[ℝ] F) →L[ℝ] (E →L[ℝ] (E [×m]→L[ℝ] F)) :=
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m+1) => E)
        F).toContinuousLinearEquiv.toContinuousLinearMap
  have hD (m k : ℕ) (x : E) : HasFDerivAt (iteratedFDeriv ℝ m (f k))
      (L m (iteratedFDeriv ℝ (m+1) (f k) x)) x := by
    have hd := (hf k).differentiable_iteratedFDeriv
      (show (m : ℕ∞ω) < (∞ : ℕ∞ω) by exact_mod_cast ENat.natCast_lt_top m) x
    exact hd.hasFDerivAt
  obtain ⟨J, hJ, hJs⟩ := EulerSmoothUniformLimit.exists_smooth_limit_of_uniform_cauchy_tower
    (fun m k => iteratedFDeriv ℝ m (f k)) L hD hC
  let A := (continuousMultilinearCurryFin0 ℝ E F).toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨fun x => A (J 0 x), ?_, A.contDiff.comp (hJs 0)⟩
  have h := A.uniformContinuous.comp_tendstoUniformly (hJ 0)
  simpa only [A, Function.comp_def, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    continuousMultilinearCurryFin0_apply, iteratedFDeriv_zero_apply] using h

section Cylinder

open EulerSobolev EulerCylinderCoordinates EulerCylinderSobolev EulerLiftedGradientSpace
open EulerMetricTransport EulerMollifierTensors

/-- A pointwise cylinder limit is C∞ when every coordinate derivative word is uniformly Cauchy. -/
theorem cylinder_smooth_of_uniformCauchy_words (period : ℝ)
    (f : ℕ → LiftDomain period → Vector3)
    (hf : ∀ k x, ContDiff ℝ ∞ (localFieldLift period (f k) x))
    (hC : ∀ m (w : Fin m → Fin 4),
      UniformCauchySeqOn (fun k => iteratedFieldDerivative period w (f k)) atTop Set.univ)
    (g : LiftDomain period → Vector3)
    (hpoint : ∀ y, Tendsto (fun k => f k y) atTop (𝓝 (g y))) :
    ∀ x, ContDiff ℝ ∞ (localFieldLift period g x) := by
  intro x
  obtain ⟨G, hG, hGs⟩ := exists_smooth_limit
    (fun k => euclideanLift period (f k) x)
    (fun k => euclideanLift_smooth period (f k) (hf k) x)
    (fun m => tensor_uniformCauchy_of_words period m f hf (hC m) x)
  have he : euclideanLift period g x = G := by
    funext z
    have hp : Tendsto (fun k => euclideanLift period (f k) x z) atTop
        (𝓝 (euclideanLift period g x z)) := by
      simpa only [euclideanLift_eq_translated_cover, translated] using
        hpoint (euclideanCover period z + x)
    exact tendsto_nhds_unique hp (hG.tendsto_at z)
  have hlocal : localFieldLift period g x = G ∘ coordinateEquiv.symm := by
    rw [← he]
    funext v
    simp only [euclideanLift, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [hlocal]
  exact hGs.comp coordinateEquiv.symm.contDiff

end Cylinder

end EulerSmoothTensorLimit
