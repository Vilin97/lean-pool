/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseEndpointVelocity

/-!
Classical differentiation of the nonzero-terminal stationary coordinates.
The continuous physical velocity upgrades the weak momentum derivative to
an every-time derivative; the actual Gram inverse then differentiates the
coordinate velocity.  These are properties of the constructed weak solution.
-/

@[expose] public section


noncomputable section


namespace EulerTransverseEndpointDifferentiation

open MeasureTheory Set InnerProductSpace ContinuousLinearMap
  EulerTimeLp EulerTerminalTimePrimitive EulerInitialTimePrimitive
  EulerVolterraConvolution EulerTransverseGramInverse EulerTransverseGramPath
  EulerTransverseInitialCoordinates EulerTransverseStrongAlgebra
  EulerTransverseMomentumRegularity EulerTransverseEndpointMomentum
  EulerTransverseEndpointVelocity

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ Q₂ : C(Icc (0 : ℝ) T, U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x, c * ‖x‖ ^ 2 ≤ ‖Q t x‖ ^ 2)
  (H : C(Icc (0 : ℝ) T, E →L[ℝ] E))

/-- Momentum derivative path as an element of `U`. -/
def momentumDerivativePath (u : TimeLp T E) (t : ℝ) : U :=
  (extendPath T hT Q₁ t).adjoint (physicalVelocityPath T hT Q Q₁ c hc hQ H u t) -
    (extendPath T hT Q t).adjoint (extendPath T hT H t (initialRealPrimitive T u t))

theorem momentumDerivativePath_continuous (u : TimeLp T E) :
    Continuous (momentumDerivativePath T hT Q Q₁ c hc hQ H u) :=
  (((realAdjoint (U := U) (E := E)).continuous.comp (extendPath_continuous T hT Q₁)).clm_apply
    (physicalVelocityPath_continuous T hT Q Q₁ c hc hQ H u)).sub
    (((realAdjoint (U := U) (E := E)).continuous.comp (extendPath_continuous T hT Q)).clm_apply
      ((extendPath_continuous T hT H).clm_apply (initialRealPrimitive_continuous T u)))

theorem initialCoordinates_eq_initialPrimitive
    (hd : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)
    (u : TimeLp T E) (t : Icc (0 : ℝ) T) :
    initialCoordinates T hT Q c hc hQ u t =
      initialRealPrimitive T (initialCoordinateDerivative T hT Q Q₁ c hc hQ u) t := by
  have hx := initialCoordinates_h1 T hT Q Q₁ c hc hQ hd u
  let ξ := initialCoordinates T hT Q c hc hQ u
  let v := initialCoordinateDerivative T hT Q Q₁ c hc hQ u
  have hder : ∀ᵐ s ∂timeMeasure T, HasDerivAt (fun r => ξ r - ξ T) (v s) s := by
    filter_upwards [hx.2.2] with s hs
    exact hs.sub_const _
  have he := eq_realPrimitive_of_ac_hasDerivAt_ae T hT v (fun r => ξ r - ξ T)
    (hx.1.sub ((LipschitzWith.const (ξ T)).lipschitzOnWith.absolutelyContinuousOnInterval))
    hder (sub_self _)
  have h₀ := he 0 ⟨le_rfl, hT⟩
  have ht := he t t.property
  have hξ₀ : ξ 0 = 0 := initialCoordinates_initial T hT Q c hc hQ u
  change ξ t = realPrimitive T v t - realPrimitive T v 0
  rw [← ht, ← h₀, hξ₀]
  abel

theorem momentumDerivativePath_ae (hTpos : 0 < T)
    (hd : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)
    (u : TimeLp T E)
    (hweak : ∀ v : TimeLp T U, initialTrace T hT v = 0 →
      ⟪momentum T hT Q u, v⟫_ℝ =
        -⟪initialMomentumForcing T hT Q Q₁ H u, primitiveTimeLp T hT v⟫_ℝ)
    (huRange : ∀ t : Icc (0 : ℝ) T, ∃ x : U, Q t x = initialRealPrimitive T u t) :
    (initialMomentumForcing T hT Q Q₁ H u : ℝ → U) =ᵐ[timeMeasure T]
      momentumDerivativePath T hT Q Q₁ c hc hQ H u := by
  filter_upwards [initialMomentumForcing_ae T hT Q Q₁ H u,
    physicalVelocityPath_ae T hT Q Q₁ c hc hQ H hd hTpos u hweak huRange] with t hp hu
  rw [hp, hu]
  rfl

theorem momentumPath_hasDerivWithinAt (hTpos : 0 < T)
    (hd : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)
    (u : TimeLp T E)
    (hweak : ∀ v : TimeLp T U, initialTrace T hT v = 0 →
      ⟪momentum T hT Q u, v⟫_ℝ =
        -⟪initialMomentumForcing T hT Q Q₁ H u, primitiveTimeLp T hT v⟫_ℝ)
    (huRange : ∀ t : Icc (0 : ℝ) T, ∃ x : U, Q t x = initialRealPrimitive T u t)
    (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (momentumPath T hT Q Q₁ H u)
      (momentumDerivativePath T hT Q Q₁ c hc hQ H u t) (Icc (0 : ℝ) T) t := by
  let f := initialMomentumForcing T hT Q Q₁ H u
  have hd' := initialPrimitive_hasDerivWithinAt_of_continuous T f _
    (momentumDerivativePath_continuous T hT Q Q₁ c hc hQ H u)
    (momentumDerivativePath_ae T hT Q Q₁ c hc hQ H hTpos hd u hweak huRange) t
  have he : momentumPath T hT Q Q₁ H u =
      fun s => initialRealPrimitive T f s +
        (realPrimitive T f 0 + terminalMomentum T hT Q Q₁ H u) := by
    funext s
    simp only [momentumPath, initialRealPrimitive, f]
    abel
  rw [he]
  exact hd'.add_const _

theorem initialCoordinates_hasDerivWithinAt (hTpos : 0 < T)
    (hd : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)
    (u : TimeLp T E)
    (hweak : ∀ v : TimeLp T U, initialTrace T hT v = 0 →
      ⟪momentum T hT Q u, v⟫_ℝ =
        -⟪initialMomentumForcing T hT Q Q₁ H u, primitiveTimeLp T hT v⟫_ℝ)
    (huRange : ∀ t : Icc (0 : ℝ) T, ∃ x : U, Q t x = initialRealPrimitive T u t)
    (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (initialCoordinates T hT Q c hc hQ u)
      (coordinateVelocityPath T hT Q Q₁ c hc hQ H u t) (Icc (0 : ℝ) T) t := by
  have hd' := initialPrimitive_hasDerivWithinAt_of_continuous T
    (initialCoordinateDerivative T hT Q Q₁ c hc hQ u) _
    (coordinateVelocityPath_continuous T hT Q Q₁ c hc hQ H u)
    (coordinateVelocityPath_ae T hT Q Q₁ c hc hQ H hd hTpos u hweak huRange) t
  apply hd'.congr_of_mem _ t.property
  intro s hs
  exact initialCoordinates_eq_initialPrimitive T hT Q Q₁ c hc hQ hd u ⟨s, hs⟩

/-- Raw coordinate acceleration, constructed using `extendPath`. -/
def rawCoordinateAcceleration (u : TimeLp T E) (t : ℝ) : U :=
  extendPath T hT (gramInverseDerivativePath T Q Q₁ c hc hQ) t
      (momentumPath T hT Q Q₁ H u t -
        extendPath T hT (mixedPath T Q Q₁) t (initialCoordinates T hT Q c hc hQ u t)) +
    extendPath T hT (gramInversePath T Q c hc hQ) t
      (momentumDerivativePath T hT Q Q₁ c hc hQ H u t -
        (extendPath T hT (mixedDerivativePath T Q Q₁ Q₂) t (initialCoordinates T hT Q c hc hQ u t) +
          extendPath T hT (mixedPath T Q Q₁) t (coordinateVelocityPath T hT Q Q₁ c hc hQ H u t)))

theorem coordinateVelocityPath_hasDerivWithinAt_raw (hTpos : 0 < T)
    (hd : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)
    (hd₁ : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT Q₁) (Q₂ t) (Icc (0 : ℝ) T) t)
    (u : TimeLp T E)
    (hweak : ∀ v : TimeLp T U, initialTrace T hT v = 0 →
      ⟪momentum T hT Q u, v⟫_ℝ =
        -⟪initialMomentumForcing T hT Q Q₁ H u, primitiveTimeLp T hT v⟫_ℝ)
    (huRange : ∀ t : Icc (0 : ℝ) T, ∃ x : U, Q t x = initialRealPrimitive T u t)
    (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (coordinateVelocityPath T hT Q Q₁ c hc hQ H u)
      (rawCoordinateAcceleration T hT Q Q₁ Q₂ c hc hQ H u t) (Icc (0 : ℝ) T) t := by
  have hB := gramInversePath_hasDerivWithinAt T Q Q₁ c hc hQ hT hd t
  have hC := mixedPath_hasDerivWithinAt T Q Q₁ Q₂ hT hd hd₁ t
  have hp := momentumPath_hasDerivWithinAt T hT Q Q₁ c hc hQ H hTpos hd u hweak huRange t
  have hξ := initialCoordinates_hasDerivWithinAt T hT Q Q₁ c hc hQ H hTpos hd u hweak huRange t
  convert hB.clm_apply (hp.sub (hC.clm_apply hξ)) using 1
  · rfl
  · simp only [rawCoordinateAcceleration, Pi.sub_apply, extendPath, projIcc_of_mem hT t.property]

/-- The defining inverse-Gram relation is an actual pointwise momentum identity. -/
theorem coordinateMomentum_identity (u : TimeLp T E) (t : ℝ) :
    extendPath T hT (gramPath T Q) t (coordinateVelocityPath T hT Q Q₁ c hc hQ H u t) +
      extendPath T hT (mixedPath T Q Q₁) t (initialCoordinates T hT Q c hc hQ u t) =
        momentumPath T hT Q Q₁ H u t := by
  change gram (Q (projIcc 0 T hT t))
    (gramInverse (Q (projIcc 0 T hT t)) c hc (hQ (projIcc 0 T hT t))
      (momentumPath T hT Q Q₁ H u t -
        extendPath T hT (mixedPath T Q Q₁) t (initialCoordinates T hT Q c hc hQ u t))) + _ = _
  rw [gram_inverse_apply, sub_add_cancel]

end EulerTransverseEndpointDifferentiation
