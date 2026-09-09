/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseEndpointEnergy
public import LeanPool.NavierStokesAndEuler.Euler.TransverseMomentumRegularity

@[expose] public section

/-!
The actual transverse momentum for an initial-zero stationary path whose
terminal displacement may be nonzero.  A canonical bounded terminal momentum
map is obtained from the weak equation and the true time primitive.  Its
continuous representative and derivative are conclusions, not extra data.
-/

noncomputable section


namespace EulerTransverseEndpointMomentum

open MeasureTheory Set InnerProductSpace ContinuousLinearMap
  EulerTimeLp EulerTerminalTimePrimitive EulerInitialTimePrimitive
  EulerVolterraConvolution EulerTimeH1OperatorProduct EulerTimeWeakDerivative
  EulerTransverseVariationalInverse EulerTransverseMomentumRegularity
  EulerTransverseEndpointEnergy

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E))
  (H : C(Icc (0 : ℝ) T, E →L[ℝ] E))

/-- The literal derivative of Q*η_t for the homogeneous stationary equation. -/
def initialMomentumForcing : TimeLp T E →L[ℝ] TimeLp T U :=
  (timeMultiplier T hT Q₁).adjoint -
    (timeMultiplier T hT Q).adjoint.comp
      ((timeMultiplier T hT H).comp (initialPrimitiveTimeLp T hT))

theorem initialMomentumForcing_ae (u : TimeLp T E) :
    (initialMomentumForcing T hT Q Q₁ H u : ℝ → U) =ᵐ[timeMeasure T]
      fun t => (extendPath T hT Q₁ t).adjoint (u t) -
        (extendPath T hT Q t).adjoint (extendPath T hT H t (initialRealPrimitive T u t)) := by
  change (momentum T hT Q₁ u -
    momentum T hT Q (timeMultiplier T hT H (initialPrimitiveTimeLp T hT u)) : TimeLp T U)
      =ᵐ[timeMeasure T] _
  filter_upwards [Lp.coeFn_sub (momentum T hT Q₁ u)
      (momentum T hT Q (timeMultiplier T hT H (initialPrimitiveTimeLp T hT u))),
    momentum_ae T hT Q₁ u,
    momentum_ae T hT Q (timeMultiplier T hT H (initialPrimitiveTimeLp T hT u)),
    timeMultiplier_ae T hT H (initialPrimitiveTimeLp T hT u),
    initialPrimitiveTimeLp_ae T hT u] with t hs hq₁ hq hH hη
  simp only [Pi.sub_apply] at hs
  rw [hs, hq₁, hq, hH, hη]

/-- The weak derivative identity is extracted from genuine transverse product tests. -/
theorem initialMomentum_weak
    (hd : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)
    (m : Icc (0 : ℝ) T → E) (hm : ∀ t x, ⟪m t, Q t x⟫_ℝ = 0)
    (u : TimeLp T E)
    (hu : ∀ v : transverseDerivatives T hT m,
      ⟪u, (v : TimeLp T E)⟫_ℝ -
        ⟪timeMultiplier T hT H (initialPrimitiveTimeLp T hT u),
          transversePrimitive T hT m v⟫_ℝ = 0)
    (v : TimeLp T U) (hv : initialTrace T hT v = 0) :
    ⟪momentum T hT Q u, v⟫_ℝ =
      -⟪initialMomentumForcing T hT Q Q₁ H u, primitiveTimeLp T hT v⟫_ℝ := by
  have ht := hu ⟨productDerivative T hT Q Q₁ v,
    productDerivative_mem_transverse T hT Q Q₁ hd m hm v hv⟩
  change ⟪u, productDerivative T hT Q Q₁ v⟫_ℝ -
    ⟪timeMultiplier T hT H (initialPrimitiveTimeLp T hT u),
      primitiveTimeLp T hT (productDerivative T hT Q Q₁ v)⟫_ℝ = 0 at ht
  rw [primitiveTimeLp_productDerivative T hT Q Q₁ hd] at ht
  simp only [productDerivative, add_apply, comp_apply, inner_add_right] at ht
  simp only [momentum, initialMomentumForcing, sub_apply, comp_apply,
    inner_sub_left, adjoint_inner_left]
  linarith only [ht]

/-- A bounded linear map giving the terminal value of the actual momentum. -/
def terminalMomentum : TimeLp T E →L[ℝ] U :=
  (-T)⁻¹ • (initialTrace T hT).comp
    ((timeMultiplier T hT Q).adjoint -
      (primitiveTimeLp T hT).comp (initialMomentumForcing T hT Q Q₁ H))

/-- The canonical momentum representative, including both time endpoints. -/
def momentumPath (u : TimeLp T E) (t : ℝ) : U :=
  realPrimitive T (initialMomentumForcing T hT Q Q₁ H u) t +
    terminalMomentum T hT Q Q₁ H u

theorem momentumPath_continuous (u : TimeLp T E) :
    Continuous (momentumPath T hT Q Q₁ H u) :=
  (realPrimitive_continuous T _).add continuous_const

theorem momentumPath_absolutelyContinuous (u : TimeLp T E) :
    AbsolutelyContinuousOnInterval (momentumPath T hT Q Q₁ H u) 0 T :=
  (realPrimitive_absolutelyContinuous T _).add
    ((LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval)

theorem momentumPath_terminal (u : TimeLp T E) :
    momentumPath T hT Q Q₁ H u T = terminalMomentum T hT Q Q₁ H u := by
  simp only [momentumPath, realPrimitive_terminal, zero_add]

theorem momentumPath_hasDerivAt_ae (u : TimeLp T E) :
    ∀ᵐ t ∂timeMeasure T, HasDerivAt (momentumPath T hT Q Q₁ H u)
      (initialMomentumForcing T hT Q Q₁ H u t) t := by
  filter_upwards [realPrimitive_hasDerivAt_ae T (initialMomentumForcing T hT Q Q₁ H u)]
    with t ht
  exact ht.add_const _

theorem momentum_eq_primitive_add_terminal (hTpos : 0 < T) (u : TimeLp T E)
    (hweak : ∀ v : TimeLp T U, initialTrace T hT v = 0 →
      ⟪momentum T hT Q u, v⟫_ℝ =
        -⟪initialMomentumForcing T hT Q Q₁ H u, primitiveTimeLp T hT v⟫_ℝ) :
    momentum T hT Q u = primitiveTimeLp T hT (initialMomentumForcing T hT Q Q₁ H u) +
      constantField T hT (terminalMomentum T hT Q Q₁ H u) := by
  obtain ⟨v, hv⟩ := weak_derivative_eq_primitive_add_constant T hTpos
    (momentum T hT Q u) (initialMomentumForcing T hT Q Q₁ H u) hweak
  have hr : momentum T hT Q u -
      primitiveTimeLp T hT (initialMomentumForcing T hT Q Q₁ H u) =
      constantField T hT v := by
    rw [hv]
    abel
  have hc : terminalMomentum T hT Q Q₁ H u = v := by
    change (-T)⁻¹ • initialTrace T hT (momentum T hT Q u -
      primitiveTimeLp T hT (initialMomentumForcing T hT Q Q₁ H u)) = v
    rw [hr, initialTrace_constantField, smul_smul,
      inv_mul_cancel₀ (neg_ne_zero.mpr hTpos.ne'), one_smul]
  rw [hc]
  exact hv

theorem momentumPath_ae_of_weak (hTpos : 0 < T) (u : TimeLp T E)
    (hweak : ∀ v : TimeLp T U, initialTrace T hT v = 0 →
      ⟪momentum T hT Q u, v⟫_ℝ =
        -⟪initialMomentumForcing T hT Q Q₁ H u, primitiveTimeLp T hT v⟫_ℝ) :
    (momentum T hT Q u : ℝ → U) =ᵐ[timeMeasure T] momentumPath T hT Q Q₁ H u := by
  rw [momentum_eq_primitive_add_terminal T hT Q Q₁ H hTpos u hweak]
  filter_upwards [Lp.coeFn_add
      (primitiveTimeLp T hT (initialMomentumForcing T hT Q Q₁ H u))
      (constantField T hT (terminalMomentum T hT Q Q₁ H u)),
    primitiveTimeLp_ae T hT (initialMomentumForcing T hT Q Q₁ H u),
    constantField_ae T hT (terminalMomentum T hT Q Q₁ H u)] with t ha hp hc
  simpa only [Pi.add_apply, hp, hc, momentumPath] using ha

/-- The momentum of the constructed endpoint solution has this actual continuous representative. -/
theorem endpointDerivative_momentumPath_ae (hTpos : 0 < T)
    (hd : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)
    (m : Icc (0 : ℝ) T → E) (hm : ∀ t x, ⟪m t, Q t x⟫_ℝ = 0)
    (K : ℝ) (hK : 0 ≤ K) (hH : ∀ t x, ⟪H t x, x⟫_ℝ ≤ K * ‖x‖ ^ 2)
    (hsmall : K * (T ^ 2 / 2) ≤ 1 / 2)
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (L : V →L[ℝ] TimeLp T E) (Y : V) :
    let u := endpointDerivative T hT m H K hK hH hsmall L Y
    (momentum T hT Q u : ℝ → U) =ᵐ[timeMeasure T] momentumPath T hT Q Q₁ H u := by
  apply momentumPath_ae_of_weak T hT Q Q₁ H hTpos
  exact initialMomentum_weak T hT Q Q₁ H hd m hm _
    (endpointDerivative_weak T hT m H K hK hH hsmall L Y)

end EulerTransverseEndpointMomentum
