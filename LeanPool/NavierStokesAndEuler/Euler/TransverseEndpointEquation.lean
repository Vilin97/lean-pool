/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseEndpointDifferentiation
public import LeanPool.NavierStokesAndEuler.Euler.TransverseEndpointUniqueness
public import LeanPool.NavierStokesAndEuler.Euler.TransverseForwardInverse

@[expose] public section

/-!
The actual nonzero-terminal stationary displacement satisfies source (10).
Its coordinate velocity solves the very same homogeneous first-order
generator used by the packet's forward inverse.  The identity is proved by
differentiating the constructed momentum, including the endpoint derivatives.
-/

noncomputable section


namespace EulerTransverseEndpointEquation

open MeasureTheory Set InnerProductSpace ContinuousLinearMap
  EulerTimeLp EulerTerminalTimePrimitive EulerInitialTimePrimitive
  EulerVolterraConvolution EulerTransverseGramInverse EulerTransverseGramPath
  EulerTransverseInitialCoordinates EulerTransverseStrongAlgebra
  EulerTransverseMomentumRegularity EulerTransverseEndpointMomentum
  EulerTransverseEndpointVelocity EulerTransverseEndpointDifferentiation
  EulerTransverseEndpointEnergy EulerTransverseForwardInverse EulerLinearDuhamel

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ Q₂ : C(Icc (0 : ℝ) T, U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x, c * ‖x‖ ^ 2 ≤ ‖Q t x‖ ^ 2)
  (H : C(Icc (0 : ℝ) T, E →L[ℝ] E))

theorem rawCoordinateAcceleration_projected (hTpos : 0 < T)
    (hd : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)
    (hd₁ : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT Q₁) (Q₂ t) (Icc (0 : ℝ) T) t)
    (hframe : ∀ t, Q₂ t = -((H t).comp (Q t)))
    (u : TimeLp T E)
    (hweak : ∀ v : TimeLp T U, initialTrace T hT v = 0 →
      ⟪momentum T hT Q u, v⟫_ℝ =
        -⟪initialMomentumForcing T hT Q Q₁ H u, primitiveTimeLp T hT v⟫_ℝ)
    (huRange : ∀ t : Icc (0 : ℝ) T, ∃ x : U, Q t x = initialRealPrimitive T u t)
    (t : Icc (0 : ℝ) T) :
    gram (Q t) (rawCoordinateAcceleration T hT Q Q₁ Q₂ c hc hQ H u t) =
      (Q t).adjoint (0 - (2 : ℝ) • Q₁ t (coordinateVelocityPath T hT Q Q₁ c hc hQ H u t)) := by
  have hp := momentumPath_hasDerivWithinAt T hT Q Q₁ c hc hQ H hTpos hd u hweak huRange t
  have hξ := initialCoordinates_hasDerivWithinAt T hT Q Q₁ c hc hQ H hTpos hd u hweak huRange t
  have hv := coordinateVelocityPath_hasDerivWithinAt_raw T hT Q Q₁ Q₂ c hc hQ H
    hTpos hd hd₁ u hweak huRange t
  have hG := gramPath_hasDerivWithinAt T Q Q₁ hT hd t
  have hC := mixedPath_hasDerivWithinAt T Q Q₁ Q₂ hT hd hd₁ t
  have hb := (hG.clm_apply hv).add (hC.clm_apply hξ)
  change HasDerivWithinAt
    (fun s => extendPath T hT (gramPath T Q) s (coordinateVelocityPath T hT Q Q₁ c hc hQ H u s) +
      extendPath T hT (mixedPath T Q Q₁) s (initialCoordinates T hT Q c hc hQ u s)) _ _ _ at hb
  have he : (fun s => extendPath T hT (gramPath T Q) s
        (coordinateVelocityPath T hT Q Q₁ c hc hQ H u s) +
      extendPath T hT (mixedPath T Q Q₁) s (initialCoordinates T hT Q c hc hQ u s)) =
        momentumPath T hT Q Q₁ H u :=
    funext (coordinateMomentum_identity T hT Q Q₁ c hc hQ H u)
  rw [he] at hb
  have hbal := (hp.derivWithin ((uniqueDiffOn_Icc hTpos) t t.property)).symm.trans
    (hb.derivWithin ((uniqueDiffOn_Icc hTpos) t t.property))
  have hη := initialCoordinates_reconstruct T hT Q c hc hQ u huRange t
  simp only [momentumDerivativePath, extendPath, projIcc_of_mem hT t.property] at hbal
  rw [← hη] at hbal
  apply projected_equation_of_momentum_balance (Q t) (Q₁ t) (Q₂ t) (H t)
    (initialCoordinates T hT Q c hc hQ u t) (coordinateVelocityPath T hT Q Q₁ c hc hQ H u t)
    (rawCoordinateAcceleration T hT Q Q₁ Q₂ c hc hQ H u t)
    (physicalVelocityPath T hT Q Q₁ c hc hQ H u t) 0
  · simp only [physicalVelocityPath, extendPath, projIcc_of_mem hT t.property]
  · exact hframe t
  · change _ =
      ((Q₁ t).adjoint.comp (Q t) + (Q t).adjoint.comp (Q₁ t))
        (coordinateVelocityPath T hT Q Q₁ c hc hQ H u t) +
      gram (Q t) (rawCoordinateAcceleration T hT Q Q₁ Q₂ c hc hQ H u t) +
      (((Q₁ t).adjoint.comp (Q₁ t) + (Q t).adjoint.comp (Q₂ t))
        (initialCoordinates T hT Q c hc hQ u t) +
        (Q t).adjoint (Q₁ t (coordinateVelocityPath T hT Q Q₁ c hc hQ H u t))) at hbal
    simpa only [map_zero, add_zero, add_assoc] using hbal

theorem rawCoordinateAcceleration_eq_generator (hTpos : 0 < T)
    (hd : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)
    (hd₁ : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT Q₁) (Q₂ t) (Icc (0 : ℝ) T) t)
    (hframe : ∀ t, Q₂ t = -((H t).comp (Q t)))
    (u : TimeLp T E)
    (hweak : ∀ v : TimeLp T U, initialTrace T hT v = 0 →
      ⟪momentum T hT Q u, v⟫_ℝ =
        -⟪initialMomentumForcing T hT Q Q₁ H u, primitiveTimeLp T hT v⟫_ℝ)
    (huRange : ∀ t : Icc (0 : ℝ) T, ∃ x : U, Q t x = initialRealPrimitive T u t)
    (t : Icc (0 : ℝ) T) :
    rawCoordinateAcceleration T hT Q Q₁ Q₂ c hc hQ H u t =
      generator T Q Q₁ c hc hQ t (coordinateVelocityPath T hT Q Q₁ c hc hQ H u t) := by
  have he := congrArg (gramInverse (Q t) c hc (hQ t))
    (rawCoordinateAcceleration_projected T hT Q Q₁ Q₂ c hc hQ H
      hTpos hd hd₁ hframe u hweak huRange t)
  rw [inverse_gram_apply] at he
  change _ = (-2 : ℝ) • gramInverse (Q t) c hc (hQ t)
    ((Q t).adjoint (Q₁ t (coordinateVelocityPath T hT Q Q₁ c hc hQ H u t)))
  simpa only [map_sub, map_zero, map_smul, zero_sub, neg_smul, map_neg] using he

/-- Equation (10) for the actual coordinate displacement, written as the
first-order equation for its genuine derivative. -/
theorem coordinateVelocityPath_hasDerivWithinAt_generator (hTpos : 0 < T)
    (hd : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)
    (hd₁ : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT Q₁) (Q₂ t) (Icc (0 : ℝ) T) t)
    (hframe : ∀ t, Q₂ t = -((H t).comp (Q t)))
    (u : TimeLp T E)
    (hweak : ∀ v : TimeLp T U, initialTrace T hT v = 0 →
      ⟪momentum T hT Q u, v⟫_ℝ =
        -⟪initialMomentumForcing T hT Q Q₁ H u, primitiveTimeLp T hT v⟫_ℝ)
    (huRange : ∀ t : Icc (0 : ℝ) T, ∃ x : U, Q t x = initialRealPrimitive T u t)
    (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (coordinateVelocityPath T hT Q Q₁ c hc hQ H u)
      (generator T Q Q₁ c hc hQ t (coordinateVelocityPath T hT Q Q₁ c hc hQ H u t))
      (Icc (0 : ℝ) T) t := by
  have hdv := coordinateVelocityPath_hasDerivWithinAt_raw T hT Q Q₁ Q₂ c hc hQ H
    hTpos hd hd₁ u hweak huRange t
  rwa [rawCoordinateAcceleration_eq_generator T hT Q Q₁ Q₂ c hc hQ H
    hTpos hd hd₁ hframe u hweak huRange t] at hdv

/-- The stationary history velocity is the same actual solution as the packet's
homogeneous forward inverse, whenever both are placed on this time interval. -/
theorem coordinateVelocity_eq_forward (hTpos : 0 < T)
    (hd : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)
    (hd₁ : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT Q₁) (Q₂ t) (Icc (0 : ℝ) T) t)
    (hframe : ∀ t, Q₂ t = -((H t).comp (Q t)))
    (u : TimeLp T E)
    (hweak : ∀ v : TimeLp T U, initialTrace T hT v = 0 →
      ⟪momentum T hT Q u, v⟫_ℝ =
        -⟪initialMomentumForcing T hT Q Q₁ H u, primitiveTimeLp T hT v⟫_ℝ)
    (huRange : ∀ t : Icc (0 : ℝ) T, ∃ x : U, Q t x = initialRealPrimitive T u t)
    (evolution : Evolution T hT (generator T Q Q₁ c hc hQ)) (t : Icc (0 : ℝ) T) :
    coordinateVelocityPath T hT Q Q₁ c hc hQ H u t =
      coordinates T hT Q Q₁ c hc hQ evolution 0
        (coordinateVelocityPath T hT Q Q₁ c hc hQ H u 0) t := by
  change _ = evolution.solution (forcingOperator T Q c hc hQ 0)
    (coordinateVelocityPath T hT Q Q₁ c hc hQ H u 0) t
  rw [map_zero]
  apply evolution.solution_unique 0 _ (coordinateVelocityPath T hT Q Q₁ c hc hQ H u) _ rfl t
  intro s
  simpa only [ContinuousMap.zero_apply, add_zero] using
    coordinateVelocityPath_hasDerivWithinAt_generator T hT Q Q₁ Q₂ c hc hQ H
      hTpos hd hd₁ hframe u hweak huRange s

/-- The nonzero-terminal inverse used in activation has genuine first and
second coordinate derivatives satisfying the source's homogeneous equation. -/
theorem endpoint_coordinate_equation (hTpos : 0 < T)
    (hd : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)
    (hd₁ : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT Q₁) (Q₂ t) (Icc (0 : ℝ) T) t)
    (hframe : ∀ t, Q₂ t = -((H t).comp (Q t)))
    (m : Icc (0 : ℝ) T → E) (hm : ∀ t x, ⟪m t, Q t x⟫_ℝ = 0)
    (hRange : ∀ t η, ⟪m t, η⟫_ℝ = 0 → ∃ x : U, Q t x = η)
    (K : ℝ) (hK : 0 ≤ K) (hH : ∀ t x, ⟪H t x, x⟫_ℝ ≤ K * ‖x‖ ^ 2)
    (hsmall : K * (T ^ 2 / 2) ≤ 1 / 2)
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (L : V →L[ℝ] TimeLp T E)
    (hL : ∀ Y t, ⟪m t, initialPrimitive T hT (L Y) t⟫_ℝ = 0)
    (Y : V) (t : Icc (0 : ℝ) T) :
    let u := endpointDerivative T hT m H K hK hH hsmall L Y
    HasDerivWithinAt (initialCoordinates T hT Q c hc hQ u)
        (coordinateVelocityPath T hT Q Q₁ c hc hQ H u t) (Icc (0 : ℝ) T) t ∧
      HasDerivWithinAt (coordinateVelocityPath T hT Q Q₁ c hc hQ H u)
        (generator T Q Q₁ c hc hQ t (coordinateVelocityPath T hT Q Q₁ c hc hQ H u t))
        (Icc (0 : ℝ) T) t := by
  let u := endpointDerivative T hT m H K hK hH hsmall L Y
  have huRange : ∀ s : Icc (0 : ℝ) T, ∃ x : U, Q s x = initialRealPrimitive T u s := by
    intro s
    exact hRange s _ (endpointDisplacement_tangent T hT m H K hK hH hsmall L hL Y s)
  have hw := initialMomentum_weak T hT Q Q₁ H hd m hm u
    (endpointDerivative_weak T hT m H K hK hH hsmall L Y)
  exact ⟨initialCoordinates_hasDerivWithinAt T hT Q Q₁ c hc hQ H hTpos hd u hw huRange t,
    coordinateVelocityPath_hasDerivWithinAt_generator T hT Q Q₁ Q₂ c hc hQ H
      hTpos hd hd₁ hframe u hw huRange t⟩

end EulerTransverseEndpointEquation
