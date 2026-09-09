/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseCoordinateRegularity
public import LeanPool.NavierStokesAndEuler.Euler.TransverseStrongAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.TimeH1FieldProduct

@[expose] public section

/-!
# Strong transverse evolution from the actual variational solve

The weak momentum identity supplies an actual absolutely continuous momentum.
The constructed Gram inverse then upgrades the coordinate derivative to H¹.
Differentiating the momentum identity and using `Q_tt = -H Q` gives the literal
projected equation (10), with no assumed acceleration or differential inverse.
-/

noncomputable section

namespace EulerTransverseStrongEquation

open MeasureTheory Set InnerProductSpace ContinuousLinearMap
  EulerTimeLp EulerTerminalTimePrimitive EulerVolterraConvolution
  EulerTimeH1OperatorProduct EulerTimeH1FieldProduct EulerTimeWeakDerivative
  EulerTransverseVariationalInverse EulerTransverseGramInverse EulerTransverseGramPath
  EulerTransverseCoordinateRegularity EulerTransverseMomentumRegularity
  EulerTransverseStrongAlgebra

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ Q₂ : C(Icc (0 : ℝ) T, U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c)
  (hQ : ∀ t x, c * ‖x‖ ^ 2 ≤ ‖Q t x‖ ^ 2)

/-- The actual candidate second derivative, constructed from L² fields and
bounded coefficient multipliers. Its derivative property is proved below. -/
def coordinateSecondDerivative (H : C(Icc (0 : ℝ) T, E →L[ℝ] E))
    (u f : TimeLp T E) : TimeLp T U :=
  let v := coordinateDerivative T hT Q Q₁ c hc hQ u
  let ξ := primitiveTimeLp T hT v
  fieldProductDerivative T hT (gramInversePath T Q c hc hQ)
    (gramInverseDerivativePath T Q Q₁ c hc hQ)
    (momentum T hT Q u - timeMultiplier T hT (mixedPath T Q Q₁) ξ)
    (momentumForcing T hT Q Q₁ H u f -
      fieldProductDerivative T hT (mixedPath T Q Q₁) (mixedDerivativePath T Q Q₁ Q₂) ξ v)

/-- The coordinate velocity recovered from an actual momentum representative. -/
def velocityRepresentative (u : TimeLp T E) (p : ℝ → U) : ℝ → U :=
  fun t => extendPath T hT (gramInversePath T Q c hc hQ) t
    (p t - extendPath T hT (mixedPath T Q Q₁) t
      (coordinatePrimitive T hT Q c hc hQ u t))

variable (hd : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)
  (hd₁ : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (extendPath T hT Q₁) (Q₂ t) (Icc (0 : ℝ) T) t)

include hd in
/-- The inverse momentum formula recovers the existing coordinate derivative
as an equality of genuine Bochner fields. -/
theorem coordinateDerivative_eq_inverse_momentum (u : TimeLp T E)
    (huRange : ∀ t : Icc (0 : ℝ) T, ∃ x : U, Q t x = realPrimitive T u t) :
    coordinateDerivative T hT Q Q₁ c hc hQ u =
      timeMultiplier T hT (gramInversePath T Q c hc hQ)
        (momentum T hT Q u - timeMultiplier T hT (mixedPath T Q Q₁)
          (primitiveTimeLp T hT (coordinateDerivative T hT Q Q₁ c hc hQ u))) := by
  let v := coordinateDerivative T hT Q Q₁ c hc hQ u
  let ξ := primitiveTimeLp T hT v
  let r := momentum T hT Q u - timeMultiplier T hT (mixedPath T Q Q₁) ξ
  apply Lp.ext
  filter_upwards [timeMultiplier_ae T hT (gramInversePath T Q c hc hQ) r,
    Lp.coeFn_sub (momentum T hT Q u) (timeMultiplier T hT (mixedPath T Q Q₁) ξ),
    momentum_ae T hT Q u,
    timeMultiplier_ae T hT (mixedPath T Q Q₁) ξ,
    coordinatePrimitive_ae T hT Q Q₁ c hc hQ hd u,
    coordinateDerivative_reconstruct_ae_of_range T hT Q Q₁ c hc hQ hd u huRange]
    with t hB hr hp hC hξ hu
  change v t = (timeMultiplier T hT (gramInversePath T Q c hc hQ) r) t
  change r t = (momentum T hT Q u) t - (timeMultiplier T hT (mixedPath T Q Q₁) ξ) t at hr
  change ξ t = coordinatePrimitive T hT Q c hc hQ u t at hξ
  rw [hB, hr, hp, hC, hξ]
  exact (inverse_momentum_identity (Q (projIcc 0 T hT t)) (Q₁ (projIcc 0 T hT t))
    c hc (hQ (projIcc 0 T hT t)) (coordinatePrimitive T hT Q c hc hQ u t) (v t) (u t) hu).symm

/-- The momentum reconstruction is a pointwise identity at every real time;
clamping preserves the actual Gram inverse identities. -/
theorem velocityRepresentative_momentum (u : TimeLp T E) (p : ℝ → U) (t : ℝ) :
    extendPath T hT (gramPath T Q) t (velocityRepresentative T hT Q Q₁ c hc hQ u p t) +
      extendPath T hT (mixedPath T Q Q₁) t (coordinatePrimitive T hT Q c hc hQ u t) = p t := by
  change gram (Q (projIcc 0 T hT t))
    (gramInverse (Q (projIcc 0 T hT t)) c hc (hQ (projIcc 0 T hT t))
      (p t - extendPath T hT (mixedPath T Q Q₁) t
        (coordinatePrimitive T hT Q c hc hQ u t))) + _ = _
  rw [gram_inverse_apply, sub_add_cancel]

include hd hd₁ in
/-- Actual H¹ regularity of the coordinate velocity follows from actual H¹
momentum and the coefficient bounds. -/
theorem velocityRepresentative_h1
    (H : C(Icc (0 : ℝ) T, E →L[ℝ] E)) (u f : TimeLp T E)
    (huRange : ∀ t : Icc (0 : ℝ) T, ∃ x : U, Q t x = realPrimitive T u t)
    (p : ℝ → U) (hpAC : AbsolutelyContinuousOnInterval p 0 T)
    (hp : (momentum T hT Q u : ℝ → U) =ᵐ[timeMeasure T] p)
    (hpder : ∀ᵐ t ∂timeMeasure T, HasDerivAt p (momentumForcing T hT Q Q₁ H u f t) t) :
    AbsolutelyContinuousOnInterval (velocityRepresentative T hT Q Q₁ c hc hQ u p) 0 T ∧
      (coordinateDerivative T hT Q Q₁ c hc hQ u : ℝ → U) =ᵐ[timeMeasure T]
        velocityRepresentative T hT Q Q₁ c hc hQ u p ∧
      ∀ᵐ t ∂timeMeasure T,
        HasDerivAt (velocityRepresentative T hT Q Q₁ c hc hQ u p)
          (coordinateSecondDerivative T hT Q Q₁ Q₂ c hc hQ H u f t) t := by
  let v := coordinateDerivative T hT Q Q₁ c hc hQ u
  let ξ := primitiveTimeLp T hT v
  let C := mixedPath T Q Q₁
  let C₁ := mixedDerivativePath T Q Q₁ Q₂
  let B := gramInversePath T Q c hc hQ
  let B₁ := gramInverseDerivativePath T Q Q₁ c hc hQ
  have hC := fieldProduct_h1 T hT C C₁
    (mixedPath_hasDerivWithinAt T Q Q₁ Q₂ hT hd hd₁) ξ v
    (coordinatePrimitive T hT Q c hc hQ u)
    (coordinatePrimitive_absolutelyContinuous T hT Q Q₁ c hc hQ hd u)
    (coordinatePrimitive_ae T hT Q Q₁ c hc hQ hd u)
    (coordinatePrimitive_hasDerivAt_ae T hT Q Q₁ c hc hQ hd u)
  let r := momentum T hT Q u - timeMultiplier T hT C ξ
  let r₁ := momentumForcing T hT Q Q₁ H u f - fieldProductDerivative T hT C C₁ ξ v
  let rPath := fun t => p t - extendPath T hT C t (coordinatePrimitive T hT Q c hc hQ u t)
  have hr : (r : ℝ → U) =ᵐ[timeMeasure T] rPath := by
    filter_upwards [Lp.coeFn_sub (momentum T hT Q u) (timeMultiplier T hT C ξ), hp, hC.2.1]
      with t hsub hpt hCt
    exact hsub.trans (congrArg₂ (fun a b : U => a - b) hpt hCt)
  have hrder : ∀ᵐ t ∂timeMeasure T, HasDerivAt rPath (r₁ t) t := by
    filter_upwards [hpder, hC.2.2,
      Lp.coeFn_sub (momentumForcing T hT Q Q₁ H u f) (fieldProductDerivative T hT C C₁ ξ v)]
      with t hpt hCt hsub
    rw [hsub]
    exact hpt.sub hCt
  have hB := fieldProduct_h1 T hT B B₁
    (gramInversePath_hasDerivWithinAt T Q Q₁ c hc hQ hT hd) r r₁ rPath
    (hpAC.sub hC.1) hr hrder
  refine ⟨hB.1, ?_, hB.2.2⟩
  have heq := coordinateDerivative_eq_inverse_momentum T hT Q Q₁ c hc hQ hd u huRange
  rw [heq]
  exact hB.2.1

include hd hd₁ in
/-- Differentiating the actual momentum identity gives exactly the projected
strong equation; the sole potential cancellation is the prescribed frame ODE. -/
theorem velocityRepresentative_projected_equation
    (H : C(Icc (0 : ℝ) T, E →L[ℝ] E)) (u f : TimeLp T E)
    (huRange : ∀ t : Icc (0 : ℝ) T, ∃ x : U, Q t x = realPrimitive T u t)
    (hframe : ∀ t, Q₂ t = -((H t).comp (Q t)))
    (p : ℝ → U) (hpAC : AbsolutelyContinuousOnInterval p 0 T)
    (hp : (momentum T hT Q u : ℝ → U) =ᵐ[timeMeasure T] p)
    (hpder : ∀ᵐ t ∂timeMeasure T, HasDerivAt p (momentumForcing T hT Q Q₁ H u f t) t) :
    ∀ᵐ t ∂timeMeasure T,
      gram (extendPath T hT Q t) (coordinateSecondDerivative T hT Q Q₁ Q₂ c hc hQ H u f t) =
        (extendPath T hT Q t).adjoint
          (f t - (2 : ℝ) • extendPath T hT Q₁ t
            (coordinateDerivative T hT Q Q₁ c hc hQ u t)) := by
  have hV := velocityRepresentative_h1 T hT Q Q₁ Q₂ c hc hQ hd hd₁ H u f huRange p hpAC hp hpder
  have hmem : ∀ᵐ t ∂timeMeasure T, t ∈ Icc (0 : ℝ) T :=
    ae_restrict_mem measurableSet_Icc
  have hG := operatorPath_hasDerivAt_ae T hT (gramPath T Q) (gramDerivativePath T Q Q₁)
    (gramPath_hasDerivWithinAt T Q Q₁ hT hd)
  have hC := operatorPath_hasDerivAt_ae T hT (mixedPath T Q Q₁) (mixedDerivativePath T Q Q₁ Q₂)
    (mixedPath_hasDerivWithinAt T Q Q₁ Q₂ hT hd hd₁)
  filter_upwards [hmem, hG, hC, hV.2.1, hV.2.2,
    coordinatePrimitive_hasDerivAt_ae T hT Q Q₁ c hc hQ hd u,
    hpder, momentumForcing_ae T hT Q Q₁ H u f,
    coordinateDerivative_reconstruct_ae_of_range T hT Q Q₁ c hc hQ hd u huRange]
    with t ht hGt hCt hvt hvdt hξt hpt hft hut
  have hbalanceDer := (hGt.clm_apply hvdt).add (hCt.clm_apply hξt)
  have hbalance := hpt.unique (hbalanceDer.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s =>
      (velocityRepresentative_momentum T hT Q Q₁ c hc hQ u p s).symm))
  rw [hft, ← hvt] at hbalance
  have hη := coordinatePrimitive_reconstruct_of_range T hT Q c hc hQ u huRange ⟨t, ht⟩
  rw [← hη] at hbalance
  simp only [extendPath, projIcc_of_mem hT ht] at hbalance hut ⊢
  exact projected_equation_of_momentum_balance (Q ⟨t, ht⟩) (Q₁ ⟨t, ht⟩) (Q₂ ⟨t, ht⟩)
    (H ⟨t, ht⟩) (coordinatePrimitive T hT Q c hc hQ u t)
    (coordinateDerivative T hT Q Q₁ c hc hQ u t)
    (coordinateSecondDerivative T hT Q Q₁ Q₂ c hc hQ H u f t) (u t) (f t)
    hut (hframe ⟨t, ht⟩) (by
      change _ =
        ((Q₁ ⟨t, ht⟩).adjoint.comp (Q ⟨t, ht⟩) +
          (Q ⟨t, ht⟩).adjoint.comp (Q₁ ⟨t, ht⟩))
          (coordinateDerivative T hT Q Q₁ c hc hQ u t) +
        gram (Q ⟨t, ht⟩) (coordinateSecondDerivative T hT Q Q₁ Q₂ c hc hQ H u f t) +
        (((Q₁ ⟨t, ht⟩).adjoint.comp (Q₁ ⟨t, ht⟩) +
          (Q ⟨t, ht⟩).adjoint.comp (Q₂ ⟨t, ht⟩))
          (coordinatePrimitive T hT Q c hc hQ u t) +
        (Q ⟨t, ht⟩).adjoint ((Q₁ ⟨t, ht⟩)
          (coordinateDerivative T hT Q Q₁ c hc hQ u t))) at hbalance
      simpa only [add_assoc] using hbalance)

include hd hd₁ in
/-- A general moving-frame weak solution has genuine H² coordinates and the
literal strong projected evolution. The hypotheses concern only the original
weak equation and the prescribed coefficient frame. -/
theorem exists_strong_of_weak_momentum (hTpos : 0 < T)
    (H : C(Icc (0 : ℝ) T, E →L[ℝ] E)) (u f : TimeLp T E)
    (huRange : ∀ t : Icc (0 : ℝ) T, ∃ x : U, Q t x = realPrimitive T u t)
    (hframe : ∀ t, Q₂ t = -((H t).comp (Q t)))
    (hweak : ∀ v : TimeLp T U, initialTrace T hT v = 0 →
      ⟪momentum T hT Q u, v⟫_ℝ =
        -⟪momentumForcing T hT Q Q₁ H u f, primitiveTimeLp T hT v⟫_ℝ) :
    ∃ v : ℝ → U,
      AbsolutelyContinuousOnInterval (coordinatePrimitive T hT Q c hc hQ u) 0 T ∧
      AbsolutelyContinuousOnInterval v 0 T ∧
      (coordinateDerivative T hT Q Q₁ c hc hQ u : ℝ → U) =ᵐ[timeMeasure T] v ∧
      (∀ᵐ t ∂timeMeasure T, HasDerivAt (coordinatePrimitive T hT Q c hc hQ u) (v t) t) ∧
      (∀ᵐ t ∂timeMeasure T,
        HasDerivAt v (coordinateSecondDerivative T hT Q Q₁ Q₂ c hc hQ H u f t) t) ∧
      ∀ᵐ t ∂timeMeasure T,
        gram (extendPath T hT Q t) (coordinateSecondDerivative T hT Q Q₁ Q₂ c hc hQ H u f t) =
          (extendPath T hT Q t).adjoint (f t - (2 : ℝ) • extendPath T hT Q₁ t (v t)) := by
  obtain ⟨p, hpAC, hp, hpder⟩ := exists_ac_representative_of_weak T hTpos
    (momentum T hT Q u) (momentumForcing T hT Q Q₁ H u f) hweak
  have hV := velocityRepresentative_h1 T hT Q Q₁ Q₂ c hc hQ hd hd₁ H u f huRange p hpAC hp hpder
  refine ⟨velocityRepresentative T hT Q Q₁ c hc hQ u p,
    coordinatePrimitive_absolutelyContinuous T hT Q Q₁ c hc hQ hd u,
    hV.1, hV.2.1, ?_, hV.2.2, ?_⟩
  · filter_upwards [coordinatePrimitive_hasDerivAt_ae T hT Q Q₁ c hc hQ hd u,
      hV.2.1] with t hdt hvt
    rw [← hvt]
    exact hdt
  · filter_upwards [velocityRepresentative_projected_equation T hT Q Q₁ Q₂ c hc hQ hd hd₁
      H u f huRange hframe p hpAC hp hpder, hV.2.1] with t he ht
    rw [← ht]
    exact he

include hd hd₁ in
/-- The actual coercively constructed transverse solver satisfies the strong
projected equation (10), with genuine first and second time derivatives. -/
theorem transverseSolver_strong (hTpos : 0 < T)
    (m : Icc (0 : ℝ) T → E)
    (hm : ∀ t x, ⟪m t, Q t x⟫_ℝ = 0)
    (hRange : ∀ t η, ⟪m t, η⟫_ℝ = 0 → ∃ x : U, Q t x = η)
    (H : C(Icc (0 : ℝ) T, E →L[ℝ] E)) (K : ℝ) (hK : 0 ≤ K)
    (hH : ∀ t x, ⟪H t x, x⟫_ℝ ≤ K * ‖x‖ ^ 2)
    (hsmall : K * (T ^ 2 / 2) ≤ 1 / 2)
    (hframe : ∀ t, Q₂ t = -((H t).comp (Q t))) (f : TimeLp T E) :
    let u : TimeLp T E := transverseSolver T hT m H K hK hH hsmall f
    ∃ v : ℝ → U,
      AbsolutelyContinuousOnInterval (coordinatePrimitive T hT Q c hc hQ u) 0 T ∧
      AbsolutelyContinuousOnInterval v 0 T ∧
      (coordinateDerivative T hT Q Q₁ c hc hQ u : ℝ → U) =ᵐ[timeMeasure T] v ∧
      (∀ᵐ t ∂timeMeasure T, HasDerivAt (coordinatePrimitive T hT Q c hc hQ u) (v t) t) ∧
      (∀ᵐ t ∂timeMeasure T,
        HasDerivAt v (coordinateSecondDerivative T hT Q Q₁ Q₂ c hc hQ H u f t) t) ∧
      ∀ᵐ t ∂timeMeasure T,
        gram (extendPath T hT Q t) (coordinateSecondDerivative T hT Q Q₁ Q₂ c hc hQ H u f t) =
          (extendPath T hT Q t).adjoint (f t - (2 : ℝ) • extendPath T hT Q₁ t (v t)) := by
  apply exists_strong_of_weak_momentum T hT Q Q₁ Q₂ c hc hQ hd hd₁ hTpos H
  · exact transverse_range T hT Q m hRange (transverseSolver T hT m H K hK hH hsmall f)
  · exact hframe
  · intro v hv
    exact momentum_weak T hT Q Q₁ hd m hm H (transverseSolver T hT m H K hK hH hsmall f) f
      (transverseSolver_weak T hT m H K hK hH hsmall f) v hv

end EulerTransverseStrongEquation
