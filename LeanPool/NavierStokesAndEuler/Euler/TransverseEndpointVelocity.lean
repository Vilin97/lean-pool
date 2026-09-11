/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseStrongAlgebra
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import LeanPool.NavierStokesAndEuler.Euler.TransverseInitialCoordinates
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import LeanPool.NavierStokesAndEuler.Euler.TransverseEndpointEnergy
public import LeanPool.NavierStokesAndEuler.Euler.TransverseMomentumRegularity
public import LeanPool.NavierStokesAndEuler.Euler.TimeWeakDerivative

/-!
Classical first-time regularity of the actual endpoint solution.  The genuine
momentum and Gram inverse construct a continuous physical velocity, which is
proved to represent the variational derivative and to be the displacement's
within-interval derivative at every time.  The endpoint energy operator is
therefore the actual projected terminal derivative.
-/

section

/-!
The actual transverse momentum for an initial-zero stationary path whose
terminal displacement may be nonzero.  A canonical bounded terminal momentum
map is obtained from the weak equation and the true time primitive.  Its
continuous representative and derivative are conclusions, not extra data.
-/

@[expose] public section

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

end
end

end

section

/-!
The actual Green identity for the constructed stationary transverse path.
Its endpoint energy is the terminal momentum paired with terminal coordinates.
All time boundary terms are obtained from absolute continuity and the genuine
H¹ coordinate reconstruction.
-/

@[expose] public section

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

end
end

end

@[expose] public section

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

/-- Coordinate velocity path, constructed using `extendPath`. -/
def coordinateVelocityPath (u : TimeLp T E) (t : ℝ) : U :=
  extendPath T hT (gramInversePath T Q c hc hQ) t
    (momentumPath T hT Q Q₁ H u t -
      extendPath T hT (mixedPath T Q Q₁) t (initialCoordinates T hT Q c hc hQ u t))

/-- Physical velocity path, constructed using `extendPath`. -/
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
