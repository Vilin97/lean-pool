/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseEndpointEnergy

/-!
Uniqueness and trial independence for the actual nonzero-terminal transverse
inverse.  Equal terminal traces and actual tangency place differences in the
existing zero-endpoint Hilbert space; the proved energy coercivity then
identifies all constructions of the same weak solution.
-/

@[expose] public section


noncomputable section


namespace EulerTransverseEndpointUniqueness

open MeasureTheory Set InnerProductSpace ContinuousLinearMap
  EulerTimeLp EulerTerminalTimePrimitive EulerInitialTimePrimitive
  EulerVolterraConvolution EulerTransverseVariationalInverse
  EulerTransverseEndpointEnergy EulerDirichletEndpointReduction

variable {E V : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

variable (T : ℝ) (hT : 0 ≤ T) (m : Icc (0 : ℝ) T → E)

/-- This is membership in the actual zero-endpoint space, obtained from paths
and traces rather than supplied as a compatibility assumption. -/
theorem sub_mem_transverse_of_terminal (u v : TimeLp T E)
    (hu : ∀ t : Icc (0 : ℝ) T, ⟪m t, initialRealPrimitive T u t⟫_ℝ = 0)
    (hv : ∀ t : Icc (0 : ℝ) T, ⟪m t, initialRealPrimitive T v t⟫_ℝ = 0)
    (hterminal : initialRealPrimitive T u T = initialRealPrimitive T v T) :
    u - v ∈ transverseDerivatives T hT m := by
  apply derivative_mem_of_ac T hT m (u - v)
    (fun t => initialRealPrimitive T u t - initialRealPrimitive T v t)
    ((initialRealPrimitive_absolutelyContinuous T u).sub
      (initialRealPrimitive_absolutelyContinuous T v))
  · filter_upwards [initialRealPrimitive_hasDerivAt_ae T u,
      initialRealPrimitive_hasDerivAt_ae T v, Lp.coeFn_sub u v] with t hud hvd hsub
    rw [hsub]
    exact hud.sub hvd
  · simp only [initialRealPrimitive_initial, sub_self]
  · exact sub_eq_zero.mpr hterminal
  · intro t
    rw [inner_sub_right, hu t, hv t, sub_zero]

variable (H : C(Icc (0 : ℝ) T, E →L[ℝ] E))
  (K : ℝ) (hK : 0 ≤ K)
  (hH : ∀ t x, ⟪H t x, x⟫_ℝ ≤ K * ‖x‖ ^ 2)
  (hsmall : K * (T ^ 2 / 2) ≤ 1 / 2)

/-- Any actual weak endpoint solution equals the constructed inverse output. -/
theorem endpointDerivative_unique (L : V →L[ℝ] TimeLp T E) (Y : V)
    (hL : ∀ t : Icc (0 : ℝ) T, ⟪m t, initialRealPrimitive T (L Y) t⟫_ℝ = 0)
    (u : TimeLp T E)
    (hu : ∀ t : Icc (0 : ℝ) T, ⟪m t, initialRealPrimitive T u t⟫_ℝ = 0)
    (hterminal : initialRealPrimitive T u T = initialRealPrimitive T (L Y) T)
    (hweak : ∀ v : transverseDerivatives T hT m,
      ⟪u, (v : TimeLp T E)⟫_ℝ -
        ⟪timeMultiplier T hT H (initialPrimitiveTimeLp T hT u),
          transversePrimitive T hT m v⟫_ℝ = 0) :
    u = endpointDerivative T hT m H K hK hH hsmall L Y := by
  let w := endpointDerivative T hT m H K hK hH hsmall L Y
  have huw : u - w ∈ transverseDerivatives T hT m := by
    have h₁ := sub_mem_transverse_of_terminal T hT m u (L Y) hu hL hterminal
    have h₂ := endpointDerivative_sub_mem T hT m H K hK hH hsmall L Y
    have hh := (transverseDerivatives T hT m).sub_mem h₁ h₂
    have he : (u - L Y) - (w - L Y) = u - w := by abel
    exact he ▸ hh
  let d : transverseDerivatives T hT m := ⟨u - w, huw⟩
  have hdu : ⟪energyOperator T hT H u, (d : TimeLp T E)⟫_ℝ = 0 := by
    rw [energyOperator_inner, initialPrimitiveTimeLp_transverse T hT m d]
    exact hweak d
  have hdw : ⟪energyOperator T hT H w, (d : TimeLp T E)⟫_ℝ = 0 := by
    rw [energyOperator_inner, initialPrimitiveTimeLp_transverse T hT m d]
    exact endpointDerivative_weak T hT m H K hK hH hsmall L Y d
  have hz : ⟪energyOperator T hT H (u - w), u - w⟫_ℝ = 0 := by
    change ⟪energyOperator T hT H (u - w), (d : TimeLp T E)⟫_ℝ = 0
    rw [map_sub, inner_sub_left, hdu, hdw, sub_zero]
  have hc := energyOperator_coercive T hT H K hK hH hsmall (u - w)
  rw [hz] at hc
  have hn : ‖u - w‖ = 0 := by nlinarith only [hc, norm_nonneg (u - w)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- The stationary output depends only on the terminal trace, not on the trial lift. -/
theorem endpointDerivative_eq_of_trial_terminal
    (L₁ L₂ : V →L[ℝ] TimeLp T E)
    (hL₁ : ∀ Y t, ⟪m t, initialRealPrimitive T (L₁ Y) t⟫_ℝ = 0)
    (hL₂ : ∀ Y t, ⟪m t, initialRealPrimitive T (L₂ Y) t⟫_ℝ = 0)
    (hterminal : ∀ Y, initialRealPrimitive T (L₁ Y) T = initialRealPrimitive T (L₂ Y) T) :
    endpointDerivative T hT m H K hK hH hsmall L₁ =
      endpointDerivative T hT m H K hK hH hsmall L₂ := by
  apply ContinuousLinearMap.ext
  intro Y
  exact stationaryPart_eq_of_sub_mem (transverseDerivatives T hT m) (energyOperator T hT H)
    (1 / 2) (by norm_num) (energyOperator_coercive T hT H K hK hH hsmall) (L₁ Y) (L₂ Y)
    (sub_mem_transverse_of_terminal T hT m (L₁ Y) (L₂ Y) (hL₁ Y) (hL₂ Y) (hterminal Y))

variable [CompleteSpace V]

theorem dirichletToNeumann_eq_of_trial_terminal
    (L₁ L₂ : V →L[ℝ] TimeLp T E)
    (hL₁ : ∀ Y t, ⟪m t, initialRealPrimitive T (L₁ Y) t⟫_ℝ = 0)
    (hL₂ : ∀ Y t, ⟪m t, initialRealPrimitive T (L₂ Y) t⟫_ℝ = 0)
    (hterminal : ∀ Y, initialRealPrimitive T (L₁ Y) T = initialRealPrimitive T (L₂ Y) T) :
    dirichletToNeumann T hT m H K hK hH hsmall L₁ =
      dirichletToNeumann T hT m H K hK hH hsmall L₂ := by
  have he := endpointDerivative_eq_of_trial_terminal T hT m H K hK hH hsmall
    L₁ L₂ hL₁ hL₂ hterminal
  apply ContinuousLinearMap.ext
  intro Y
  apply ext_inner_right ℝ
  intro Z
  rw [dirichletToNeumann_inner, dirichletToNeumann_inner, he]

end EulerTransverseEndpointUniqueness
