/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseInitialCoordinates
public import LeanPool.NavierStokesAndEuler.Euler.TransverseEndpointMomentum

@[expose] public section

/-!
The actual Green identity for the constructed stationary transverse path.
Its endpoint energy is the terminal momentum paired with terminal coordinates.
All time boundary terms are obtained from absolute continuity and the genuine
H¹ coordinate reconstruction.
-/

noncomputable section


namespace EulerTransverseEndpointGreen

open MeasureTheory Set InnerProductSpace ContinuousLinearMap
  EulerTimeLp EulerTerminalTimePrimitive EulerInitialTimePrimitive
  EulerVolterraConvolution EulerTimeWeakDerivative EulerTransverseGramInverse
  EulerTransverseGramPath EulerTransverseInitialCoordinates
  EulerTransverseMomentumRegularity EulerTransverseEndpointMomentum
  EulerTransverseEndpointEnergy EulerTransverseVariationalInverse

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t x, c * ‖x‖ ^ 2 ≤ ‖Q t x‖ ^ 2)
  (H : C(Icc (0 : ℝ) T, E →L[ℝ] E))

/-- The exact boundary identity for any genuine tangent initial-zero test path. -/
theorem initial_coordinate_green (hTpos : 0 < T)
    (hd : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)
    (u v : TimeLp T E)
    (hweak : ∀ w : TimeLp T U, initialTrace T hT w = 0 →
      ⟪momentum T hT Q u, w⟫_ℝ =
        -⟪initialMomentumForcing T hT Q Q₁ H u, primitiveTimeLp T hT w⟫_ℝ)
    (hvRange : ∀ t : Icc (0 : ℝ) T, ∃ x : U, Q t x = initialRealPrimitive T v t) :
    ⟪energyOperator T hT H u, v⟫_ℝ =
      ⟪terminalMomentum T hT Q Q₁ H u, initialCoordinates T hT Q c hc hQ v T⟫_ℝ := by
  let φ : ℝ → ℝ := fun t =>
    ⟪momentumPath T hT Q Q₁ H u t, initialCoordinates T hT Q c hc hQ v t⟫_ℝ
  have hξ := initialCoordinates_h1 T hT Q Q₁ c hc hQ hd v
  have hφ : AbsolutelyContinuousOnInterval φ 0 T :=
    absolutelyContinuous_inner (momentumPath_absolutelyContinuous T hT Q Q₁ H u) hξ.1
  have hftc : (∫ t, deriv φ t ∂timeMeasure T) = φ T - φ 0 := by
    change (∫ t in Icc (0 : ℝ) T, deriv φ t) = _
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT]
    exact hφ.integral_deriv_eq_sub
  have hder : ∀ᵐ t ∂timeMeasure T,
      ⟪u t, v t⟫_ℝ -
        ⟪timeMultiplier T hT H (initialPrimitiveTimeLp T hT u) t,
          initialPrimitiveTimeLp T hT v t⟫_ℝ = deriv φ t := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      momentumPath_ae_of_weak T hT Q Q₁ H hTpos u hweak,
      momentum_ae T hT Q u,
      momentumPath_hasDerivAt_ae T hT Q Q₁ H u, hξ.2.2,
      initialCoordinateDerivative_reconstruct_ae T hT Q Q₁ c hc hQ hd v hvRange,
      initialMomentumForcing_ae T hT Q Q₁ H u,
      initialPrimitiveTimeLp_ae T hT u, initialPrimitiveTimeLp_ae T hT v,
      timeMultiplier_ae T hT H (initialPrimitiveTimeLp T hT u)]
      with t ht hp hpu hpd hξd hv hf hηu hηv hHu
    have hp' : momentumPath T hT Q Q₁ H u t = (extendPath T hT Q t).adjoint (u t) :=
      hp.symm.trans hpu
    have hη : extendPath T hT Q t (initialCoordinates T hT Q c hc hQ v t) =
        initialRealPrimitive T v t := by
      simpa only [extendPath, projIcc_of_mem hT ht] using
        initialCoordinates_reconstruct T hT Q c hc hQ v hvRange ⟨t, ht⟩
    have hφd : deriv φ t =
        ⟪initialMomentumForcing T hT Q Q₁ H u t, initialCoordinates T hT Q c hc hQ v t⟫_ℝ +
        ⟪momentumPath T hT Q Q₁ H u t,
          initialCoordinateDerivative T hT Q Q₁ c hc hQ v t⟫_ℝ :=
      by simpa only [φ, add_comm] using (hpd.inner ℝ hξd).deriv
    rw [hφd, hf, hp', hHu, hηu, hηv, hv, ← hη]
    simp only [inner_add_right, inner_sub_left, adjoint_inner_left]
    ring
  calc
    ⟪energyOperator T hT H u, v⟫_ℝ =
        ∫ t, ⟪u t, v t⟫_ℝ -
          ⟪timeMultiplier T hT H (initialPrimitiveTimeLp T hT u) t,
            initialPrimitiveTimeLp T hT v t⟫_ℝ ∂timeMeasure T := by
      rw [energyOperator_inner, L2.inner_def, L2.inner_def]
      exact (integral_sub (L2.integrable_inner u v)
        (L2.integrable_inner (timeMultiplier T hT H (initialPrimitiveTimeLp T hT u))
          (initialPrimitiveTimeLp T hT v))).symm
    _ = ∫ t, deriv φ t ∂timeMeasure T := integral_congr_ae hder
    _ = φ T - φ 0 := hftc
    _ = _ := by
      simp only [φ, momentumPath_terminal, initialCoordinates_initial, inner_zero_right, sub_zero]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- The true terminal coordinate map associated with a physical terminal trace. -/
def terminalCoordinates (R : V →L[ℝ] E) : V →L[ℝ] U :=
  (frameLeftInversePath T Q c hc hQ ⟨T, hT, le_rfl⟩).comp R

/-- The constructed endpoint energy operator is exactly the pulled-back terminal momentum. -/
theorem dirichletToNeumann_eq_terminalMomentum (hTpos : 0 < T)
    (hd : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)
    (m : Icc (0 : ℝ) T → E) (hm : ∀ t x, ⟪m t, Q t x⟫_ℝ = 0)
    (hRange : ∀ t η, ⟪m t, η⟫_ℝ = 0 → ∃ x : U, Q t x = η)
    (K : ℝ) (hK : 0 ≤ K) (hH : ∀ t x, ⟪H t x, x⟫_ℝ ≤ K * ‖x‖ ^ 2)
    (hsmall : K * (T ^ 2 / 2) ≤ 1 / 2)
    (L : V →L[ℝ] TimeLp T E) (R : V →L[ℝ] E)
    (hL : ∀ Y t, ⟪m t, initialPrimitive T hT (L Y) t⟫_ℝ = 0)
    (hLT : ∀ Y, initialPrimitive T hT (L Y) ⟨T, hT, le_rfl⟩ = R Y) (Y : V) :
    dirichletToNeumann T hT m H K hK hH hsmall L Y =
      (terminalCoordinates T hT Q c hc hQ R).adjoint
        (terminalMomentum T hT Q Q₁ H (endpointDerivative T hT m H K hK hH hsmall L Y)) := by
  apply ext_inner_right ℝ
  intro Z
  let u := endpointDerivative T hT m H K hK hH hsmall L Y
  let v := endpointDerivative T hT m H K hK hH hsmall L Z
  have hvRange : ∀ t : Icc (0 : ℝ) T, ∃ x : U, Q t x = initialRealPrimitive T v t := by
    intro t
    exact hRange t _ (endpointDisplacement_tangent T hT m H K hK hH hsmall L hL Z t)
  have hw := initialMomentum_weak T hT Q Q₁ H hd m hm u
    (endpointDerivative_weak T hT m H K hK hH hsmall L Y)
  have hg := initial_coordinate_green T hT Q Q₁ c hc hQ H hTpos hd u v hw hvRange
  have hterm : initialRealPrimitive T v T = R Z :=
    (endpointDisplacement_terminal T hT m H K hK hH hsmall L Z).trans (hLT Z)
  have hcoords : initialCoordinates T hT Q c hc hQ v T =
      terminalCoordinates T hT Q c hc hQ R Z := by
    simp only [initialCoordinates, extendPath, projIcc_of_mem hT (show T ∈ Icc (0 : ℝ) T from
      ⟨hT, le_rfl⟩), hterm, terminalCoordinates, comp_apply]
  rw [energyOperator_inner, hcoords] at hg
  rw [dirichletToNeumann_inner, adjoint_inner_left]
  exact hg

end EulerTransverseEndpointGreen
