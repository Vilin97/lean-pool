/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderGraphRealization
import LeanPool.NavierStokesAndEuler.Euler.Foundations.MollifierUniform
import Mathlib.Algebra.Order.Star.Real

/-! Restriction to a fixed continuous phase graph preserves time continuity
in actual spatial L². The proof uses the uniform trace estimate for differences. -/

@[expose] public section


noncomputable section

namespace EulerCylinderGraphTrace

open Set MeasureTheory Filter EulerLiftedGradientSpace EulerMetricTransport
  EulerTransportDerivatives
open scoped ContDiff Topology

variable (P : ℝ) [Fact (0 < P)]
  {K : Type*} [TopologicalSpace K]
  (u v : C(K, LiftL2 P)) (f : K → LiftDomain P → Vector3)
  (hf : ∀ t x, ContDiff ℝ ∞ (localFieldLift P (f t) x))
  (hu : ∀ t, (u t : LiftDomain P → Vector3) =ᵐ[liftMeasure P] f t)
  (hv : ∀ t, (v t : LiftDomain P → Vector3) =ᵐ[liftMeasure P]
    fieldDerivative P (0, 1) (f t))
  (θ : Vector3 → AddCircle P) (hθ : Continuous θ)

/-- Graph path value, given by `graphRealization P (f t) (hf t) (u t) (v t) (hu t) (hv t) θ hθ`. -/
def graphPathValue (t : K) : Lp Vector3 2 (volume : Measure Vector3) :=
  graphRealization P (f t) (hf t) (u t) (v t) (hu t) (hv t) θ hθ

theorem graphPathValue_ae (t : K) :
    (graphPathValue P u v f hf hu hv θ hθ t : Vector3 → Vector3) =ᵐ[volume]
      fun x => f t (x,θ x) :=
  graphRealization_ae P (f t) (hf t) (u t) (v t) (hu t) (hv t) θ hθ

theorem graphPathValue_sub_norm_sq_le (t s : K) :
    ‖graphPathValue P u v f hf hu hv θ hθ t -
      graphPathValue P u v f hf hu hv θ hθ s‖^2 ≤
      (2/P)*‖u t-u s‖^2+(2*P)*‖v t-v s‖^2 := by
  refine graph_norm_sq_le P (fun x => f t x-f s x)
    (fun x => (hf t x).sub (hf s x)) (u t-u s) (v t-v s) ?_ ?_ θ hθ _ ?_
  · filter_upwards [Lp.coeFn_sub (u t) (u s),hu t,hu s] with x hs ht hu
    exact hs.trans (congrArg₂ (·-·) ht hu)
  · filter_upwards [Lp.coeFn_sub (v t) (v s),hv t,hv s] with x hs ht hu
    exact hs.trans ((congrArg₂ (·-·) ht hu).trans
      (EulerMollifierUniform.fieldDerivative_sub P (0,1) (f t) (f s) (hf t) (hf s) x).symm)
  · filter_upwards [Lp.coeFn_sub
      (graphPathValue P u v f hf hu hv θ hθ t)
      (graphPathValue P u v f hf hu hv θ hθ s),
      graphPathValue_ae P u v f hf hu hv θ hθ t,
      graphPathValue_ae P u v f hf hu hv θ hθ s] with x hs ht hu
    exact hs.trans (congrArg₂ (·-·) ht hu)

theorem graphPathValue_continuous :
    Continuous (graphPathValue P u v f hf hu hv θ hθ) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  rw [ContinuousAt,tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun s => (2/P)*‖u s-u t‖^2+(2*P)*‖v s-v t‖^2)
      (𝓝 t) (𝓝 (0 : ℝ)) := by
    simpa only [sub_self,norm_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      mul_zero,add_zero] using
      ((((u.continuous.tendsto t).sub_const (u t)).norm.pow 2).const_mul (2/P)).add
        ((((v.continuous.tendsto t).sub_const (v t)).norm.pow 2).const_mul (2*P))
  have hsq := squeeze_zero
    (fun s => sq_nonneg ‖graphPathValue P u v f hf hu hv θ hθ s -
      graphPathValue P u v f hf hu hv θ hθ t‖)
    (fun s => graphPathValue_sub_norm_sq_le P u v f hf hu hv θ hθ s t) hlim
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hr

/-- The continuous spatial L² path is constructed from the actual cylinder
path and its actual angular derivative. -/
def graphPath : C(K,Lp Vector3 2 (volume : Measure Vector3)) :=
  ⟨graphPathValue P u v f hf hu hv θ hθ,
    graphPathValue_continuous P u v f hf hu hv θ hθ⟩

end EulerCylinderGraphTrace
