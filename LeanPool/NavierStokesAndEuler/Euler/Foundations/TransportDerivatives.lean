/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.MetricTransport
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
Actual directional differentiation of transport and coefficient multiplication.
The commutator is derived by the chain rule and symmetry of second derivatives,
rather than postulated as a recurrence on a norm sequence.
-/

@[expose] public section

noncomputable section

namespace EulerTransportDerivatives

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerMetricTransport
open scoped ContDiff ENNReal NNReal Topology

section Euclidean

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The actual Fréchet directional derivative along a constant vector. -/
def directionalDerivative (a : V) (f : V → W) (x : V) : W := fderiv ℝ f x a

/-- Differentiation of a field in the direction of a variable transport field. -/
def transport (b : V → V) (f : V → W) (x : V) : W := fderiv ℝ f x (b x)

theorem directionalDerivative_smooth (a : V) (f : V → W) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (directionalDerivative a f) := by
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem transport_smooth (b : V → V) (f : V → W)
    (hb : ContDiff ℝ ∞ b) (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (transport b f) := by
  exact (hf.fderiv_right (by simp)).clm_apply hb

theorem directional_transport_commutator (a : V) (b : V → V) (f : V → W)
    (hb : ContDiff ℝ ∞ b) (hf : ContDiff ℝ ∞ f) (x : V) :
    directionalDerivative a (transport b f) x =
      transport b (directionalDerivative a f) x +
        fderiv ℝ f x (directionalDerivative a b x) := by
  have hdf := (((hf.fderiv_right (m := ∞) (by simp)).differentiable
    (by simp)) x).hasFDerivAt
  have hdb := (hb.differentiable (by simp)).differentiableAt.hasFDerivAt (x := x)
  have hdT := congrArg (fun L : V →L[ℝ] W => L a) (hdf.clm_apply hdb).fderiv
  have hdA := congrArg (fun L : V →L[ℝ] W => L (b x))
    (hdf.clm_apply (hasFDerivAt_const a x)).fderiv
  have hs := (hf.contDiffAt (x := x)).isSymmSndFDerivAt
    (by
        rw [minSmoothness_of_isRCLikeNormedField]; exact ENat.natCast_le_of_coe_top_le_withTop
            le_rfl 2) a (b x)
  change fderiv ℝ (transport b f) x a = _ at hdT
  change fderiv ℝ (directionalDerivative a f) x (b x) = _ at hdA
  change fderiv ℝ (transport b f) x a =
    fderiv ℝ (directionalDerivative a f) x (b x) + fderiv ℝ f x (fderiv ℝ b x a)
  rw [hdT, hdA]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    zero_apply, map_zero, zero_add]
  rw [hs]
  exact add_comm _ _

theorem directional_transport_commutator_norm (a : V) (b : V → V) (f : V → W)
    (hb : ContDiff ℝ ∞ b) (hf : ContDiff ℝ ∞ f) (x : V) :
    ‖directionalDerivative a (transport b f) x -
      transport b (directionalDerivative a f) x‖ ≤
        ‖fderiv ℝ f x‖ * ‖directionalDerivative a b x‖ := by
  rw [directional_transport_commutator a b f hb hf x, add_sub_cancel_left]
  exact (fderiv ℝ f x).le_opNorm _

end Euclidean

variable (period : ℝ)

section Fields

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Directional differentiation in the cylinder covering coordinates. -/
def fieldDerivative (a : LiftTangent) (f : LiftDomain period → W)
    (x : LiftDomain period) : W := fderiv ℝ (localFieldLift period f x) 0 a

/-- The actual directional transport operator on a cylinder field. -/
def fieldTransport (b : LiftDomain period → LiftTangent)
    (f : LiftDomain period → W) (x : LiftDomain period) : W :=
  fderiv ℝ (localFieldLift period f x) 0 (b x)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
theorem localFieldLift_shift (f : LiftDomain period → W) (x : LiftDomain period)
    (h : LiftTangent) :
    localFieldLift period f (x.1 + h.1, x.2 + (h.2 : AddCircle period)) =
      fun u => localFieldLift period f x (h + u) := by
  funext u
  simp [localFieldLift, add_assoc]

theorem fderiv_localFieldLift_shift (f : LiftDomain period → W) (x : LiftDomain period)
    (h : LiftTangent) :
    fderiv ℝ (localFieldLift period f
      (x.1 + h.1, x.2 + (h.2 : AddCircle period))) 0 =
      fderiv ℝ (localFieldLift period f x) h := by
  rw [localFieldLift_shift, fderiv_comp_add_left, add_zero]

theorem localFieldLift_fieldDerivative (a : LiftTangent)
    (f : LiftDomain period → W) (x : LiftDomain period) :
    localFieldLift period (fieldDerivative period a f) x =
      directionalDerivative a (localFieldLift period f x) := by
  funext h
  exact congrArg (fun L : LiftTangent →L[ℝ] W => L a)
    (fderiv_localFieldLift_shift period f x h)

theorem localFieldLift_fieldTransport (b : LiftDomain period → LiftTangent)
    (f : LiftDomain period → W) (x : LiftDomain period) :
    localFieldLift period (fieldTransport period b f) x =
      transport (localFieldLift period b x) (localFieldLift period f x) := by
  funext h
  exact congrArg (fun L : LiftTangent →L[ℝ] W => L (localFieldLift period b x h))
    (fderiv_localFieldLift_shift period f x h)

theorem fieldDerivative_smooth (a : LiftTangent) (f : LiftDomain period → W)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) :
    ContDiff ℝ ∞ (localFieldLift period (fieldDerivative period a f) x) := by
  rw [localFieldLift_fieldDerivative]
  exact directionalDerivative_smooth a _ (hf x)

theorem fieldTransport_smooth (b : LiftDomain period → LiftTangent)
    (f : LiftDomain period → W)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) :
    ContDiff ℝ ∞ (localFieldLift period (fieldTransport period b f) x) := by
  rw [localFieldLift_fieldTransport]
  exact transport_smooth _ _ (hb x) (hf x)

theorem field_transport_commutator (a : LiftTangent)
    (b : LiftDomain period → LiftTangent) (f : LiftDomain period → W)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) :
    fieldDerivative period a (fieldTransport period b f) x =
      fieldTransport period b (fieldDerivative period a f) x +
        fderiv ℝ (localFieldLift period f x) 0 (fieldDerivative period a b x) := by
  have hc := directional_transport_commutator a (localFieldLift period b x)
    (localFieldLift period f x) (hb x) (hf x) 0
  simpa only [fieldDerivative, fieldTransport, localFieldLift_fieldTransport,
    localFieldLift_fieldDerivative, directionalDerivative, transport, localFieldLift,
    Prod.fst_zero, Prod.snd_zero, AddCircle.coe_zero, add_zero] using hc

theorem field_transport_commutator_norm (a : LiftTangent)
    (b : LiftDomain period → LiftTangent) (f : LiftDomain period → W)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : LiftDomain period) :
    ‖fieldDerivative period a (fieldTransport period b f) x -
      fieldTransport period b (fieldDerivative period a f) x‖ ≤
        ‖fderiv ℝ (localFieldLift period f x) 0‖ *
          ‖fieldDerivative period a b x‖ := by
  rw [field_transport_commutator period a b f hb hf x, add_sub_cancel_left]
  exact (fderiv ℝ (localFieldLift period f x) 0).le_opNorm _

end Fields

end EulerTransportDerivatives
