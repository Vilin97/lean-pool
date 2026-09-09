/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseEndpointGreen
public import LeanPool.NavierStokesAndEuler.Euler.TransverseStrongAlgebra

@[expose] public section

/-!
Classical first-time regularity of the actual endpoint solution.  The genuine
momentum and Gram inverse construct a continuous physical velocity, which is
proved to represent the variational derivative and to be the displacement's
within-interval derivative at every time.  The endpoint energy operator is
therefore the actual projected terminal derivative.
-/

noncomputable section


namespace EulerTransverseEndpointVelocity

open MeasureTheory Set InnerProductSpace ContinuousLinearMap
  EulerTimeLp EulerTerminalTimePrimitive EulerInitialTimePrimitive
  EulerVolterraConvolution EulerTransverseGramInverse EulerTransverseGramPath
  EulerTransverseInitialCoordinates EulerTransverseStrongAlgebra
  EulerTransverseMomentumRegularity EulerTransverseEndpointMomentum
  EulerTransverseEndpointGreen EulerTransverseEndpointEnergy EulerTransverseVariationalInverse

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x, c * ‖x‖ ^ 2 ≤ ‖Q t x‖ ^ 2)
  (H : C(Icc (0 : ℝ) T, E →L[ℝ] E))

theorem initialCoordinates_continuous (u : TimeLp T E) :
    Continuous (initialCoordinates T hT Q c hc hQ u) :=
  (extendPath_continuous T hT (frameLeftInversePath T Q c hc hQ)).clm_apply
    (initialRealPrimitive_continuous T u)

def coordinateVelocityPath (u : TimeLp T E) (t : ℝ) : U :=
  extendPath T hT (gramInversePath T Q c hc hQ) t
    (momentumPath T hT Q Q₁ H u t -
      extendPath T hT (mixedPath T Q Q₁) t (initialCoordinates T hT Q c hc hQ u t))

def physicalVelocityPath (u : TimeLp T E) (t : ℝ) : E :=
  extendPath T hT Q₁ t (initialCoordinates T hT Q c hc hQ u t) +
    extendPath T hT Q t (coordinateVelocityPath T hT Q Q₁ c hc hQ H u t)

theorem coordinateVelocityPath_continuous (u : TimeLp T E) :
    Continuous (coordinateVelocityPath T hT Q Q₁ c hc hQ H u) :=
  (extendPath_continuous T hT (gramInversePath T Q c hc hQ)).clm_apply
    ((momentumPath_continuous T hT Q Q₁ H u).sub
      ((extendPath_continuous T hT (mixedPath T Q Q₁)).clm_apply
        (initialCoordinates_continuous T hT Q c hc hQ u)))

theorem physicalVelocityPath_continuous (u : TimeLp T E) :
    Continuous (physicalVelocityPath T hT Q Q₁ c hc hQ H u) :=
  ((extendPath_continuous T hT Q₁).clm_apply
    (initialCoordinates_continuous T hT Q c hc hQ u)).add
      ((extendPath_continuous T hT Q).clm_apply
        (coordinateVelocityPath_continuous T hT Q Q₁ c hc hQ H u))

/-- The continuous velocity has the exact prescribed momentum at every time. -/
theorem physicalVelocityPath_momentum (u : TimeLp T E) (t : ℝ) :
    (extendPath T hT Q t).adjoint (physicalVelocityPath T hT Q Q₁ c hc hQ H u t) =
      momentumPath T hT Q Q₁ H u t := by
  change (Q (projIcc 0 T hT t)).adjoint
    (Q₁ (projIcc 0 T hT t) (initialCoordinates T hT Q c hc hQ u t) +
      Q (projIcc 0 T hT t)
        (gramInverse (Q (projIcc 0 T hT t)) c hc (hQ (projIcc 0 T hT t))
          (momentumPath T hT Q Q₁ H u t -
            (Q (projIcc 0 T hT t)).adjoint
              (Q₁ (projIcc 0 T hT t) (initialCoordinates T hT Q c hc hQ u t))))) = _
  rw [map_add]
  change _ + gram (Q (projIcc 0 T hT t))
    (gramInverse (Q (projIcc 0 T hT t)) c hc (hQ (projIcc 0 T hT t)) _) = _
  rw [gram_inverse_apply, add_sub_cancel]

variable (hd : ∀ t : Icc (0 : ℝ) T,
  HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)

include hd in
theorem coordinateVelocityPath_ae (hTpos : 0 < T) (u : TimeLp T E)
    (hweak : ∀ v : TimeLp T U, initialTrace T hT v = 0 →
      ⟪momentum T hT Q u, v⟫_ℝ =
        -⟪initialMomentumForcing T hT Q Q₁ H u, primitiveTimeLp T hT v⟫_ℝ)
    (huRange : ∀ t : Icc (0 : ℝ) T, ∃ x : U, Q t x = initialRealPrimitive T u t) :
    (initialCoordinateDerivative T hT Q Q₁ c hc hQ u : ℝ → U) =ᵐ[timeMeasure T]
      coordinateVelocityPath T hT Q Q₁ c hc hQ H u := by
  filter_upwards [momentumPath_ae_of_weak T hT Q Q₁ H hTpos u hweak,
    momentum_ae T hT Q u,
    initialCoordinateDerivative_reconstruct_ae T hT Q Q₁ c hc hQ hd u huRange]
    with t hp hpm hu
  have hp' : momentumPath T hT Q Q₁ H u t = (extendPath T hT Q t).adjoint (u t) :=
    hp.symm.trans hpm
  unfold coordinateVelocityPath
  rw [hp']
  exact (inverse_momentum_identity (Q (projIcc 0 T hT t)) (Q₁ (projIcc 0 T hT t))
    c hc (hQ (projIcc 0 T hT t)) (initialCoordinates T hT Q c hc hQ u t)
    (initialCoordinateDerivative T hT Q Q₁ c hc hQ u t) (u t) hu).symm

include hd in
/-- The continuous physical velocity represents the original variational derivative. -/
theorem physicalVelocityPath_ae (hTpos : 0 < T) (u : TimeLp T E)
    (hweak : ∀ v : TimeLp T U, initialTrace T hT v = 0 →
      ⟪momentum T hT Q u, v⟫_ℝ =
        -⟪initialMomentumForcing T hT Q Q₁ H u, primitiveTimeLp T hT v⟫_ℝ)
    (huRange : ∀ t : Icc (0 : ℝ) T, ∃ x : U, Q t x = initialRealPrimitive T u t) :
    (u : ℝ → E) =ᵐ[timeMeasure T] physicalVelocityPath T hT Q Q₁ c hc hQ H u := by
  filter_upwards [initialCoordinateDerivative_reconstruct_ae T hT Q Q₁ c hc hQ hd u huRange,
    coordinateVelocityPath_ae T hT Q Q₁ c hc hQ H hd hTpos u hweak huRange] with t hu hv
  rw [hu, hv]
  rfl

/-- A continuous representative of a genuine L² derivative differentiates its
initial primitive at every time, including the one-sided endpoint derivative. -/
theorem initialPrimitive_hasDerivWithinAt_of_continuous (u : TimeLp T E)
    (f : ℝ → E) (hf : Continuous f) (hu : (u : ℝ → E) =ᵐ[timeMeasure T] f)
    (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (initialRealPrimitive T u) (f t) (Icc (0 : ℝ) T) t := by
  have he : ∀ s ∈ Icc (0 : ℝ) T,
      initialRealPrimitive T u s = ∫ r in (0 : ℝ)..s, f r := by
    intro s hs
    rw [initialRealPrimitive_eq_integral]
    apply intervalIntegral.integral_congr_ae
    have hau : ∀ᵐ r, r ∈ Icc (0 : ℝ) T → zeroExtension T u r = f r :=
      (ae_restrict_iff' measurableSet_Icc).mp ((zeroExtension_ae T u).trans hu)
    filter_upwards [hau] with r hr
    intro hrs
    rw [uIoc_of_le hs.1] at hrs
    exact hr ⟨hrs.1.le, hrs.2.trans hs.2⟩
  have hd' : HasDerivAt (fun s => ∫ r in (0 : ℝ)..s, f r) (f t) t :=
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 t)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  exact hd'.hasDerivWithinAt.congr_of_mem he t.property

include hd in
theorem stationary_displacement_hasDerivWithinAt (hTpos : 0 < T) (u : TimeLp T E)
    (hweak : ∀ v : TimeLp T U, initialTrace T hT v = 0 →
      ⟪momentum T hT Q u, v⟫_ℝ =
        -⟪initialMomentumForcing T hT Q Q₁ H u, primitiveTimeLp T hT v⟫_ℝ)
    (huRange : ∀ t : Icc (0 : ℝ) T, ∃ x : U, Q t x = initialRealPrimitive T u t)
    (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (initialRealPrimitive T u)
      (physicalVelocityPath T hT Q Q₁ c hc hQ H u t) (Icc (0 : ℝ) T) t :=
  initialPrimitive_hasDerivWithinAt_of_continuous T u _
    (physicalVelocityPath_continuous T hT Q Q₁ c hc hQ H u)
    (physicalVelocityPath_ae T hT Q Q₁ c hc hQ H hd hTpos u hweak huRange) t

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

include hd in
/-- The actual endpoint energy operator is the physical terminal derivative
paired with the prescribed physical terminal trace map. -/
theorem dirichletToNeumann_eq_terminal_velocity (hTpos : 0 < T)
    (m : Icc (0 : ℝ) T → E) (hm : ∀ t x, ⟪m t, Q t x⟫_ℝ = 0)
    (hRange : ∀ t η, ⟪m t, η⟫_ℝ = 0 → ∃ x : U, Q t x = η)
    (K : ℝ) (hK : 0 ≤ K) (hH : ∀ t x, ⟪H t x, x⟫_ℝ ≤ K * ‖x‖ ^ 2)
    (hsmall : K * (T ^ 2 / 2) ≤ 1 / 2)
    (L : V →L[ℝ] TimeLp T E) (R : V →L[ℝ] E)
    (hL : ∀ Y t, ⟪m t, initialPrimitive T hT (L Y) t⟫_ℝ = 0)
    (hLT : ∀ Y, initialPrimitive T hT (L Y) ⟨T, hT, le_rfl⟩ = R Y) (Y : V) :
    dirichletToNeumann T hT m H K hK hH hsmall L Y =
      R.adjoint (physicalVelocityPath T hT Q Q₁ c hc hQ H
        (endpointDerivative T hT m H K hK hH hsmall L Y) T) := by
  rw [dirichletToNeumann_eq_terminalMomentum T hT Q Q₁ c hc hQ H hTpos hd
    m hm hRange K hK hH hsmall L R hL hLT]
  apply ext_inner_right ℝ
  intro Z
  have hR : ⟪m ⟨T, hT, le_rfl⟩, R Z⟫_ℝ = 0 := by
    rw [← hLT Z]
    exact hL Z ⟨T, hT, le_rfl⟩
  obtain ⟨z, hz⟩ := hRange ⟨T, hT, le_rfl⟩ (R Z) hR
  have hrec : Q ⟨T, hT, le_rfl⟩ (terminalCoordinates T hT Q c hc hQ R Z) = R Z := by
    change Q ⟨T, hT, le_rfl⟩
      (frameLeftInverse (Q ⟨T, hT, le_rfl⟩) c hc (hQ ⟨T, hT, le_rfl⟩) (R Z)) = R Z
    rw [← hz, frameLeftInverse_apply]
  rw [adjoint_inner_left, adjoint_inner_left, ← momentumPath_terminal T hT Q Q₁ H,
    ← physicalVelocityPath_momentum T hT Q Q₁ c hc hQ H, adjoint_inner_left]
  congr 1
  simpa only [extendPath, projIcc_of_mem hT (show T ∈ Icc (0 : ℝ) T from ⟨hT, le_rfl⟩)] using hrec

include hd in
omit [CompleteSpace V] in
/-- The derivative used in the endpoint formula is the actual one at every time. -/
theorem endpointDisplacement_hasDerivWithinAt (hTpos : 0 < T)
    (m : Icc (0 : ℝ) T → E) (hm : ∀ t x, ⟪m t, Q t x⟫_ℝ = 0)
    (hRange : ∀ t η, ⟪m t, η⟫_ℝ = 0 → ∃ x : U, Q t x = η)
    (K : ℝ) (hK : 0 ≤ K) (hH : ∀ t x, ⟪H t x, x⟫_ℝ ≤ K * ‖x‖ ^ 2)
    (hsmall : K * (T ^ 2 / 2) ≤ 1 / 2) (L : V →L[ℝ] TimeLp T E)
    (hL : ∀ Y t, ⟪m t, initialPrimitive T hT (L Y) t⟫_ℝ = 0)
    (Y : V) (t : Icc (0 : ℝ) T) :
    let u := endpointDerivative T hT m H K hK hH hsmall L Y
    HasDerivWithinAt (initialRealPrimitive T u)
      (physicalVelocityPath T hT Q Q₁ c hc hQ H u t) (Icc (0 : ℝ) T) t := by
  apply stationary_displacement_hasDerivWithinAt T hT Q Q₁ c hc hQ H hd hTpos
  · exact initialMomentum_weak T hT Q Q₁ H hd m hm _
      (endpointDerivative_weak T hT m H K hK hH hsmall L Y)
  · intro s
    exact hRange s _ (endpointDisplacement_tangent T hT m H K hK hH hsmall L hL Y s)

end EulerTransverseEndpointVelocity
