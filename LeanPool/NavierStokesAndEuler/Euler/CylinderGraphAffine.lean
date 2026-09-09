/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderGraphRealization

@[expose] public section

/-! The graph trace estimate applies to the actual affine remainder in a
derivative quotient, with the same constants for all phase frequencies. -/

noncomputable section

namespace EulerCylinderGraphTrace

open Set MeasureTheory EulerLiftedGradientSpace EulerMetricTransport
  EulerTransportDerivatives
open scoped ContDiff

theorem affine_representative_ae {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (u : Fin 3 → Lp Vector3 2 μ) (f : Fin 3 → X → Vector3)
    (hu : ∀ i, (u i : X → Vector3) =ᵐ[μ] f i) (a : ℝ) :
    ((a • (u 1-u 0)-u 2 : Lp Vector3 2 μ) : X → Vector3) =ᵐ[μ]
      fun x => a • (f 1 x-f 0 x)-f 2 x := by
  filter_upwards [Lp.coeFn_sub (a • (u 1-u 0)) (u 2),
    Lp.coeFn_smul a (u 1-u 0),Lp.coeFn_sub (u 1) (u 0),hu 0,hu 1,hu 2]
    with x h2 hs h1 h0 h1' h2'
  simp only [Pi.sub_apply,Pi.smul_apply,h2,hs,h1,h0,h1',h2']

variable (P : ℝ) [Fact (0 < P)]

omit [Fact (0 < P)] in
theorem affine_fieldDerivative (f : Fin 3 → LiftDomain P → Vector3)
    (hf : ∀ i x, ContDiff ℝ ∞ (localFieldLift P (f i) x))
    (a : ℝ) (z : LiftDomain P) :
    fieldDerivative P (0,1) (fun x => a • (f 1 x-f 0 x)-f 2 x) z =
      a • (fieldDerivative P (0,1) (f 1) z-fieldDerivative P (0,1) (f 0) z)-
        fieldDerivative P (0,1) (f 2) z := by
  have h := (((((hf 1 z).differentiable (by simp)) 0).hasFDerivAt.sub
    ((((hf 0 z).differentiable (by simp)) 0).hasFDerivAt)).const_smul a).sub
    ((((hf 2 z).differentiable (by simp)) 0).hasFDerivAt)
  exact congrArg (fun L : LiftTangent →L[ℝ] Vector3 => L (0,1)) h.fderiv

theorem graph_affine_norm_sq_le
    (f : Fin 3 → LiftDomain P → Vector3)
    (hf : ∀ i x, ContDiff ℝ ∞ (localFieldLift P (f i) x))
    (u v : Fin 3 → LiftL2 P)
    (hu : ∀ i, (u i : LiftDomain P → Vector3) =ᵐ[liftMeasure P] f i)
    (hv : ∀ i, (v i : LiftDomain P → Vector3) =ᵐ[liftMeasure P]
      fieldDerivative P (0,1) (f i))
    (θ : Vector3 → AddCircle P) (hθ : Continuous θ)
    (w : Fin 3 → Lp Vector3 2 (volume : Measure Vector3))
    (hw : ∀ i, (w i : Vector3 → Vector3) =ᵐ[volume] fun x => f i (x,θ x))
    (a : ℝ) :
    ‖a • (w 1-w 0)-w 2‖^2 ≤
      (2/P)*‖a • (u 1-u 0)-u 2‖^2+(2*P)*‖a • (v 1-v 0)-v 2‖^2 := by
  refine graph_norm_sq_le P (fun x => a • (f 1 x-f 0 x)-f 2 x)
    (fun x => (((hf 1 x).sub (hf 0 x)).const_smul a).sub (hf 2 x))
    (a • (u 1-u 0)-u 2) (a • (v 1-v 0)-v 2)
    (affine_representative_ae (liftMeasure P) u f hu a) ?_ θ hθ _
    (affine_representative_ae volume w (fun i x => f i (x,θ x)) hw a)
  filter_upwards [affine_representative_ae (liftMeasure P) v
    (fun i => fieldDerivative P (0,1) (f i)) hv a] with x hx
  exact hx.trans (affine_fieldDerivative P f hf a x).symm

end EulerCylinderGraphTrace
