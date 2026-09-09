/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientPathJets

@[expose] public section

/-! A genuinely smooth bounded-coefficient translation orbit supplies
actual bounded spatial derivatives, continuously over the time parameter. -/

noncomputable section

namespace EulerMeanCoefficients

open EulerSmoothLimit ContinuousLinearMap
open scoped ContDiff BoundedContinuousFunction

variable {K V : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

private local instance : NormedAddCommGroup (Space →ᵇ V) := inferInstance
private local instance : NormedSpace ℝ (Space →ᵇ V) := inferInstance
private local instance : NormedAddCommGroup C(K, Space →ᵇ V) := inferInstance
private local instance : NormedSpace ℝ C(K, Space →ᵇ V) := inferInstance

theorem coefficientOrbit_smooth (A : C(K, Space →ᵇ V))
    (hA : ContDiff ℝ ∞ (translateCoefficientPath A)) (t : K) :
    ContDiff ℝ ∞ (A t : Space → V) := by
  let ev : C(K, Space →ᵇ V) →L[ℝ] V :=
    (BoundedContinuousFunction.evalCLM ℝ (0 : Space)).comp (ContinuousMap.evalCLM ℝ t)
  have h := (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (E := C(K, Space →ᵇ V)) (F := V) ev).comp hA
  change ContDiff ℝ ∞ (fun a : Space => A t (0+a)) at h
  simpa only [zero_add] using h

theorem coefficientOrbit_iteratedFDeriv_apply (A : C(K, Space →ᵇ V))
    (hA : ContDiff ℝ ∞ (translateCoefficientPath A))
    (n : ℕ) (a : Space) (t : K) (x : Space) (v : Fin n → Space) :
    (iteratedFDeriv ℝ n (translateCoefficientPath A) a v) t x =
      iteratedFDeriv ℝ n (A t : Space → V) (x+a) v := by
  let ev : C(K, Space →ᵇ V) →L[ℝ] V :=
    (BoundedContinuousFunction.evalCLM ℝ x).comp (ContinuousMap.evalCLM ℝ t)
  have he := ContinuousLinearMap.iteratedFDeriv_comp_left (𝕜 := ℝ)
    (E := Space) (F := C(K, Space →ᵇ V)) (G := V) ev
    (hA.contDiffAt (x := a)) (i := n) (by simp)
  have hv := congrArg (fun L : Space [×n]→L[ℝ] V => L v) he
  change iteratedFDeriv ℝ n (fun b => A t (x+b)) a v =
    (iteratedFDeriv ℝ n (translateCoefficientPath A) a v) t x at hv
  rw [iteratedFDeriv_comp_add_left] at hv
  exact hv.symm

theorem coefficientOrbit_fderiv_apply (A : C(K, Space →ᵇ V))
    (hA : ContDiff ℝ ∞ (translateCoefficientPath A))
    (a v : Space) (t : K) (x : Space) :
    (fderiv ℝ (translateCoefficientPath A) a v) t x =
      fderiv ℝ (A t : Space → V) (x+a) v := by
  simpa only [iteratedFDeriv_one_apply] using
    coefficientOrbit_iteratedFDeriv_apply A hA 1 a t x (fun _ => v)

/-- The derivative is itself an actual continuous path of bounded fields. -/
def orbitDerivativePath (A : C(K, Space →ᵇ V)) (v : Space) : C(K, Space →ᵇ V) :=
  fderiv ℝ (translateCoefficientPath A) 0 v

theorem orbitDerivativePath_apply (A : C(K, Space →ᵇ V))
    (hA : ContDiff ℝ ∞ (translateCoefficientPath A)) (v : Space) (t : K) (x : Space) :
    orbitDerivativePath A v t x = fderiv ℝ (A t : Space → V) x v := by
  unfold orbitDerivativePath
  simpa only [add_zero] using coefficientOrbit_fderiv_apply A hA 0 v t x

theorem orbitDerivativePath_translation (A : C(K, Space →ᵇ V))
    (hA : ContDiff ℝ ∞ (translateCoefficientPath A)) (v a : Space) :
    translateCoefficientPath (orbitDerivativePath A v) a =
      fderiv ℝ (translateCoefficientPath A) a v := by
  apply ContinuousMap.ext
  intro t
  apply BoundedContinuousFunction.ext
  intro x
  change orbitDerivativePath A v t (x+a) = _
  rw [orbitDerivativePath_apply A hA,coefficientOrbit_fderiv_apply A hA]

theorem orbitDerivativePath_orbit (A : C(K, Space →ᵇ V))
    (hA : ContDiff ℝ ∞ (translateCoefficientPath A)) (v : Space) :
    ContDiff ℝ ∞ (translateCoefficientPath (orbitDerivativePath A v)) := by
  have he : translateCoefficientPath (orbitDerivativePath A v) =
      fun a => fderiv ℝ (translateCoefficientPath A) a v :=
    funext (orbitDerivativePath_translation A hA v)
  rw [he]
  exact (hA.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- A single genuine Banach-space derivative at zero controls the spatial
derivative uniformly at every time and spatial point. -/
theorem coefficientOrbit_norm_iteratedFDeriv_le (A : C(K, Space →ᵇ V))
    (hA : ContDiff ℝ ∞ (translateCoefficientPath A)) (n : ℕ) (t : K) (x : Space) :
    ‖iteratedFDeriv ℝ n (A t : Space → V) x‖ ≤
      ‖iteratedFDeriv ℝ n (translateCoefficientPath A) 0‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro v
  have he := coefficientOrbit_iteratedFDeriv_apply A hA n 0 t x v
  simp only [add_zero] at he
  rw [← he]
  exact (((iteratedFDeriv ℝ n (translateCoefficientPath A) 0 v t).norm_coe_le_norm x).trans
    ((iteratedFDeriv ℝ n (translateCoefficientPath A) 0 v).norm_coe_le_norm t)).trans
      ((iteratedFDeriv ℝ n (translateCoefficientPath A) 0).le_opNorm v)

end EulerMeanCoefficients
