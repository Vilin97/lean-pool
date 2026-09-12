/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.PacketActivationRay
public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryUncut
public import LeanPool.NavierStokesAndEuler.Euler.PacketScaledVelocity
public import LeanPool.NavierStokesAndEuler.Euler.TransverseActivationSelection
import LeanPool.NavierStokesAndEuler.Euler.PacketInitialGeometry
public import LeanPool.NavierStokesAndEuler.Euler.CylinderEndpointLabels
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketHistoryData
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketHistory
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketTimeData
public import LeanPool.NavierStokesAndEuler.Euler.TransverseEndpointEnergy

/-! Actual center initial data for the geometric propagation theorem.
The selected terminal coordinate drives the same stationary history and
homogeneous continuation used in the constructed packet. -/

section

/-! Actual activation data for the packet's own stationary history.  The
terminal coordinate and its signed velocity components are constructed
from the source Dirichlet-to-Neumann argument. -/

section

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

end
end

end

section

/-! The stationary path selected by the actual activation argument is the
same history used by the packet, after matching its physical terminal trace. -/

@[expose] public section

noncomputable section

namespace EulerPacketActivationHistory

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerTransversePacketProvider EulerTimeLp EulerInitialTimePrimitive
  EulerVolterraConvolution EulerTransverseEndpointEnergy EulerTransverseEndpointVelocity
  EulerTransverseEndpointUniqueness EulerTransverseEndpointParameter
      EulerTransverseEndpointCoordinates
  EulerTransverseInitialCoordinates EulerTransverseFrameCoordinates
      EulerTransverseSourceCoefficientPath

variable {U V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {D : Data U} (B : HistoryData D) (x : Space)

/-- Stationary derivative, constructed using `endpointDerivative`. -/
def stationaryDerivative (L : V →L[ℝ] TimeLp D.T Space) : V →L[ℝ] TimeLp D.T Space :=
  endpointDerivative D.T D.T_pos.le (fun t => D.normal.field t x)
    (B.coefficients.labelHessian x) B.potential B.potential_nonneg
    (B.coefficients.labelHessian_upper x) B.small L

/-- Stationary corrected velocity, constructed using `physicalVelocityPath`. -/
def stationaryCorrectedVelocity (L : V →L[ℝ] TimeLp D.T Space) (Y : V)
    (t : Icc (0 : ℝ) D.T) : Space :=
  physicalVelocityPath D.T D.T_pos.le (B.coefficients.labelFrame x)
    (B.coefficients.labelFrameDerivative x) B.coefficients.lower B.coefficients.lower_pos
    (B.coefficients.labelFrame_lower x) (B.coefficients.labelHessian x)
    (stationaryDerivative B x L Y) t -
      D.M.field t x (initialRealPrimitive D.T (stationaryDerivative B x L Y) t)

theorem history_eq_stationary_of_terminal (L : V →L[ℝ] TimeLp D.T Space)
    (hL : ∀ Y t, ⟪D.normal.field t x, initialPrimitive D.T D.T_pos.le (L Y) t⟫_ℝ = 0)
    (Y : V) (ξ : U)
    (hterminal : initialRealPrimitive D.T (L Y) D.T =
      D.frame.field ⟨D.T, D.T_pos.le, le_rfl⟩ x ξ)
    (t : Icc (0 : ℝ) D.T) :
    B.coefficients.labelVelocity x ξ t = stationaryCorrectedVelocity B x L Y t := by
  let C := B.coefficients
  let m : Icc (0 : ℝ) D.T → Space := fun s => D.normal.field s x
  let A := affineTrial D.T D.T_pos.le (C.labelFrame x) (C.labelFrameDerivative x)
  let u := stationaryDerivative B x L Y
  have hm : ∀ s η, ⟪m s,C.labelFrame x s η⟫_ℝ=0 := fun s η => D.frame_tangent s x η
  have hRange : ∀ s η, ⟪m s,η⟫_ℝ=0 → ∃ z : U, C.labelFrame x s z=η :=
    fun s η h => D.frame_range s x η h
  have hA : ∀ Z s, ⟪m s,initialPrimitive D.T D.T_pos.le (A Z) s⟫_ℝ=0 :=
    affineTrial_tangent D.T D.T_pos.le (C.labelFrame x) (C.labelFrameDerivative x)
      (C.labelFrame_derivative x) m hm
  have hu : u=endpointDerivative D.T D.T_pos.le m (C.labelHessian x)
      B.potential B.potential_nonneg (C.labelHessian_upper x) B.small A ξ := by
    apply endpointDerivative_unique D.T D.T_pos.le m (C.labelHessian x)
      B.potential B.potential_nonneg (C.labelHessian_upper x) B.small A ξ (hA ξ) u
    · exact endpointDisplacement_tangent D.T D.T_pos.le m (C.labelHessian x)
        B.potential B.potential_nonneg (C.labelHessian_upper x) B.small L hL Y
    · calc
        _ = initialRealPrimitive D.T (L Y) D.T :=
          endpointDisplacement_terminal D.T D.T_pos.le m (C.labelHessian x)
            B.potential B.potential_nonneg (C.labelHessian_upper x) B.small L Y
        _ = D.frame.field ⟨D.T,D.T_pos.le,le_rfl⟩ x ξ := hterminal
        _ = _ := (affineTrial_terminal D.T D.T_pos.le (C.labelFrame x)
          (C.labelFrameDerivative x) D.T_pos (C.labelFrame_derivative x) ξ).symm
    · exact endpointDerivative_weak D.T D.T_pos.le m (C.labelHessian x)
        B.potential B.potential_nonneg (C.labelHessian_upper x) B.small L Y
  have hhistory := historyVelocity_eq D.T D.T_pos.le (C.labelFrame x)
    (C.labelFrameDerivative x) (C.labelHessian x) C.lower C.lower_pos
    (C.labelFrame_lower x) (C.labelFrame_derivative x) C.potential C.potential_nonneg
    (C.labelHessian_upper x) C.small m hm hRange (C.labelFrameSecond x) D.T_pos
    (C.labelFrame_second_derivative x) (C.labelFrame_equation x) ξ t
  change C.labelVelocity x ξ t = C.labelFrame x t
    (coordinateVelocityPath D.T D.T_pos.le (C.labelFrame x) (C.labelFrameDerivative x)
      C.lower C.lower_pos (C.labelFrame_lower x) (C.labelHessian x)
      (endpointDerivative D.T D.T_pos.le m (C.labelHessian x) B.potential B.potential_nonneg
        (C.labelHessian_upper x) B.small A ξ) t) at hhistory
  rw [← hu] at hhistory
  have hurange : ∀ s : Icc (0 : ℝ) D.T, ∃ z : U,
      C.labelFrame x s z=initialRealPrimitive D.T u s := by
    intro s
    exact hRange s _ (endpointDisplacement_tangent D.T D.T_pos.le m (C.labelHessian x)
      B.potential B.potential_nonneg (C.labelHessian_upper x) B.small L hL Y s)
  have hrec := initialCoordinates_reconstruct D.T D.T_pos.le (C.labelFrame x)
    C.lower C.lower_pos (C.labelFrame_lower x) u hurange t
  change D.frame.field t x
    (initialCoordinates D.T D.T_pos.le (C.labelFrame x) C.lower C.lower_pos
      (C.labelFrame_lower x) u t) = initialRealPrimitive D.T u t at hrec
  change C.labelVelocity x ξ t = physicalVelocityPath D.T D.T_pos.le (C.labelFrame x)
    (C.labelFrameDerivative x) C.lower C.lower_pos (C.labelFrame_lower x) (C.labelHessian x) u t -
      D.M.field t x (initialRealPrimitive D.T u t)
  rw [hhistory]
  simp only [physicalVelocityPath,extendPath,projIcc_of_mem D.T_pos.le t.property]
  change D.frame.field t x _ = D.frameDerivative.field t x _+D.frame.field t x _-D.M.field t x _
  rw [D.frame_strain,comp_apply,hrec]
  abel

end EulerPacketActivationHistory

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketActivationHistory

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerTransversePacketProvider EulerTimeLp EulerInitialTimePrimitive
  EulerVolterraConvolution EulerTransverseEndpointEnergy EulerTransverseEndpointVelocity
   EulerTransverseEndpointParameter
      EulerTransverseEndpointCoordinates
  EulerTransverseInitialCoordinates EulerTransverseFrameCoordinates
      EulerTransverseSourceCoefficientPath
  EulerTransverseActivationSelection EulerTransverseActivationTrial

variable {U V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {D : Data U} (B : HistoryData D)

theorem select_history_coordinate
    (R : V →ₗᵢ[ℝ] Space)
    (hR : ∀ Y, ⟪D.normal.field ⟨D.T, D.T_pos.le, le_rfl⟩ 0, R Y⟫_ℝ = 0)
    (hHs : ∀ t, (B.H.field t 0).IsSymmetric)
    (h CM CH ε : ℝ) (hh : 0 < h) (hLayer : 1 ≤ h * D.T)
    (hCM : 0 ≤ CM) (hCH : 0 ≤ CH) (hε : 0 ≤ ε)
    (hM : ∀ t, ‖D.M.field t 0‖ ≤ CM * h)
    (hHnorm : ‖B.coefficients.labelHessian 0‖ ≤ CH * h ^ 2)
    (p q : V) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : ⟪p, q⟫_ℝ = 0)
    (hεsmall : 16 * (activationConstant CM CH + 1) * ε ≤ 1)
    (hB : ‖terminalPerturbation D.T D.T_pos.le R (pathEvaluation 0 D.M.field) p q h‖ ≤ ε * h)
    (hBpp : ⟪terminalPerturbation D.T D.T_pos.le R (pathEvaluation 0 D.M.field) p q h p, p⟫_ℝ < 0) :
    ∃ ξ : U, ξ ≠ 0 ∧
      ⟪B.coefficients.labelVelocity 0 ξ ⟨D.T,D.T_pos.le,le_rfl⟩,R q⟫_ℝ=1 ∧
      -8*(activationConstant CM CH+1) ≤
        ⟪B.coefficients.labelVelocity 0 ξ ⟨D.T,D.T_pos.le,le_rfl⟩,R p⟫_ℝ ∧
      ⟪B.coefficients.labelVelocity 0 ξ ⟨D.T,D.T_pos.le,le_rfl⟩,R p⟫_ℝ ≤ 0 ∧
      ‖ξ‖ ≤ (8*(activationConstant CM CH+1)*D.inverseBound)/h := by
  let C := B.coefficients
  let m : C(Icc (0 : ℝ) D.T,Space) := pathEvaluation 0 D.normal.field
  let m₁ : C(Icc (0 : ℝ) D.T,Space) := pathEvaluation 0 D.normalDerivative
  let M : C(Icc (0 : ℝ) D.T,Space →L[ℝ] Space) := pathEvaluation 0 D.M.field
  have hne : ∀ t, m t ≠ 0 := fun t => HistoryData.normal_ne_zero t 0
  have hdm : ∀ t : Icc (0 : ℝ) D.T,
      HasDerivWithinAt (extendPath D.T D.T_pos.le m) (m₁ t) (Icc (0 : ℝ) D.T) t := by
    intro t
    have hd := D.normal_hasDerivWithinAt t t.property 0
    convert! hd using 1
    simp only [extendPath,projIcc_of_mem D.T_pos.le t.property]
    rfl
  have hRay : ∀ t, m₁ t = -(M t).adjoint (m t) := fun t => D.normalDerivative_apply t 0
  have hm : ∀ t v, ⟪m t,C.labelFrame 0 t v⟫_ℝ=0 := fun t v => D.frame_tangent t 0 v
  have hRange : ∀ t η, ⟪m t,η⟫_ℝ=0 → ∃ v : U, C.labelFrame 0 t v=η :=
    fun t η ht => D.frame_range t 0 η ht
  obtain ⟨Y,hY⟩ := select_actual_activation D.T D.T_pos (C.labelFrame 0) (C.labelFrameDerivative 0)
    C.lower C.lower_pos (C.labelFrame_lower 0) (C.labelFrame_derivative 0)
    m m₁ hne hdm hm hRange R hR (C.labelHessian 0) hHs
    B.potential B.potential_nonneg (C.labelHessian_upper 0) B.small M hRay
    h CM CH ε hh hLayer hCM hCH hε hM hHnorm p q hp hq hpq hεsmall hB hBpp
  let L := activationTrial D.T D.T_pos.le m m₁ hne R.toContinuousLinearMap h
  have hL : ∀ Z t, ⟪D.normal.field t 0,initialPrimitive D.T D.T_pos.le (L Z) t⟫_ℝ=0 :=
    activationTrial_tangent D.T D.T_pos.le m m₁ hne R.toContinuousLinearMap hdm h
  have hLT : ∀ Z, initialPrimitive D.T D.T_pos.le (L Z) ⟨D.T,D.T_pos.le,le_rfl⟩=R Z :=
    activationTrial_terminal D.T D.T_pos.le m m₁ hne R.toContinuousLinearMap hdm h hLayer hR
  obtain ⟨ξ,hξ⟩ := D.frame_range ⟨D.T,D.T_pos.le,le_rfl⟩ 0 (R Y) (hR Y)
  have ht : initialRealPrimitive D.T (L Y) D.T =
      D.frame.field ⟨D.T,D.T_pos.le,le_rfl⟩ 0 ξ := (hLT Y).trans hξ.symm
  have hw := history_eq_stationary_of_terminal B 0 L hL Y ξ ht ⟨D.T,D.T_pos.le,le_rfl⟩
  rcases hY with ⟨_,_,_,_,_,hwq,hwpl,hwpu,hsize⟩
  have hqv : ⟪B.coefficients.labelVelocity 0 ξ ⟨D.T,D.T_pos.le,le_rfl⟩,R q⟫_ℝ=1 := by
    rw [hw]
    convert! hwq using 1
    simp only [stationaryCorrectedVelocity,stationaryDerivative,L,C,m,M,
      extendPath,projIcc_of_mem D.T_pos.le (show D.T ∈ Icc (0 : ℝ) D.T from ⟨D.T_pos.le,le_rfl⟩)]
    rfl
  have hpl : -8*(activationConstant CM CH+1) ≤
      ⟪B.coefficients.labelVelocity 0 ξ ⟨D.T,D.T_pos.le,le_rfl⟩,R p⟫_ℝ := by
    rw [hw]
    convert! hwpl using 1
    simp only [stationaryCorrectedVelocity,stationaryDerivative,L,C,m,M,
      extendPath,projIcc_of_mem D.T_pos.le (show D.T ∈ Icc (0 : ℝ) D.T from ⟨D.T_pos.le,le_rfl⟩)]
    rfl
  have hpu : ⟪B.coefficients.labelVelocity 0 ξ ⟨D.T,D.T_pos.le,le_rfl⟩,R p⟫_ℝ ≤ 0 := by
    rw [hw]
    convert! hwpu using 1
    simp only [stationaryCorrectedVelocity,stationaryDerivative,L,C,m,M,
      extendPath,projIcc_of_mem D.T_pos.le (show D.T ∈ Icc (0 : ℝ) D.T from ⟨D.T_pos.le,le_rfl⟩)]
    rfl
  have hnonzero : ξ ≠ 0 := by
    intro hz
    rw [hz,map_zero,ContinuousMap.zero_apply,inner_zero_left] at hqv
    norm_num at hqv
  have hleft : (D.R ξ : Space) = D.FInv.field ⟨D.T,D.T_pos.le,le_rfl⟩ 0 (R Y) := by
    have hv := congrArg (D.FInv.field ⟨D.T,D.T_pos.le,le_rfl⟩ 0) hξ
    change D.FInv.field ⟨D.T,D.T_pos.le,le_rfl⟩ 0
      (D.F.field ⟨D.T,D.T_pos.le,le_rfl⟩ 0 (D.R ξ : Space)) = _ at hv
    rwa [D.inverse_left] at hv
  have hnorm : ‖ξ‖ ≤ D.inverseBound*‖Y‖ := by
    calc
      _ = ‖(D.R ξ : Space)‖ := (D.R.norm_map ξ).symm
      _ = ‖D.FInv.field ⟨D.T,D.T_pos.le,le_rfl⟩ 0 (R Y)‖ := congrArg norm hleft
      _ ≤ ‖D.FInv.field ⟨D.T,D.T_pos.le,le_rfl⟩ 0‖*‖R Y‖ := le_opNorm _ _
      _ ≤ D.inverseBound*‖R Y‖ := mul_le_mul_of_nonneg_right (D.inverse_norm _ _) (norm_nonneg _)
      _ = D.inverseBound*‖Y‖ := by rw [R.norm_map]
  refine ⟨ξ,hnonzero,hqv,hpl,hpu,hnorm.trans ?_⟩
  exact (mul_le_mul_of_nonneg_left hsize D.inverseBound_pos.le).trans_eq (by ring)

end EulerPacketActivationHistory

end
end

end

section

/-! Source activation in the actual physical tangent plane.  Ambient
strain error and compression bounds imply the compressed terminal-matrix
hypotheses, so no abstract endpoint matrix or plane isometry is supplied. -/

@[expose] public section

noncomputable section

namespace EulerPacketActivationHistory

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerTransversePacketProvider EulerTransverseFrameCoordinates EulerTransverseSourceCoefficientPath
  EulerTransverseActivationSelection

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem terminalPerturbation_compression (T : ℝ) (hT : 0 ≤ T)
    (R : V →ₗᵢ[ℝ] Space) (M : C(Icc (0 : ℝ) T, Space →L[ℝ] Space)) (p q : V) (h : ℝ) :
    terminalPerturbation T hT R M p q h =
      R.toContinuousLinearMap.adjoint.comp
        ((M ⟨T,hT,le_rfl⟩-h • rankOne ℝ (R q) (R p)).comp R.toContinuousLinearMap) := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_right ℝ
  intro w
  simp only [terminalPerturbation,sub_apply,comp_apply,smul_apply,rankOne_apply,
    inner_sub_left,real_inner_smul_left,adjoint_inner_left,
    LinearIsometry.coe_toContinuousLinearMap,R.inner_map_map]

theorem terminalPerturbation_norm_le (T : ℝ) (hT : 0 ≤ T)
    (R : V →ₗᵢ[ℝ] Space) (M : C(Icc (0 : ℝ) T, Space →L[ℝ] Space)) (p q : V) (h : ℝ) :
    ‖terminalPerturbation T hT R M p q h‖ ≤ ‖M ⟨T,hT,le_rfl⟩-h • rankOne ℝ (R q) (R p)‖ := by
  rw [terminalPerturbation_compression]
  have hR := R.norm_toContinuousLinearMap_le
  have hRa : ‖R.toContinuousLinearMap.adjoint‖ ≤ 1 := by rwa [LinearIsometryEquiv.norm_map]
  refine (opNorm_comp_le _ _).trans ?_
  calc
    _ ≤ 1*‖(M ⟨T,hT,le_rfl⟩-h • rankOne ℝ (R q) (R p)).comp R.toContinuousLinearMap‖ :=
      mul_le_mul_of_nonneg_right hRa (norm_nonneg _)
    _ = _ := one_mul _
    _ ≤ ‖M ⟨T,hT,le_rfl⟩-h • rankOne ℝ (R q) (R p)‖*‖R.toContinuousLinearMap‖ := opNorm_comp_le _ _
    _ ≤ ‖M ⟨T,hT,le_rfl⟩-h • rankOne ℝ (R q) (R p)‖*1 :=
      mul_le_mul_of_nonneg_left hR (norm_nonneg _)
    _ = _ := mul_one _

theorem terminalPerturbation_diagonal (T : ℝ) (hT : 0 ≤ T)
    (R : V →ₗᵢ[ℝ] Space) (M : C(Icc (0 : ℝ) T, Space →L[ℝ] Space)) (p q : V) (h : ℝ)
    (hpq : ⟪p, q⟫_ℝ = 0) :
    ⟪terminalPerturbation T hT R M p q h p,p⟫_ℝ = ⟪M ⟨T,hT,le_rfl⟩ (R p),R p⟫_ℝ := by
  have hqp : ⟪q,p⟫_ℝ=0 := by rwa [real_inner_comm]
  simp only [terminalPerturbation,sub_apply,comp_apply,smul_apply,rankOne_apply,
    inner_sub_left,real_inner_smul_left,adjoint_inner_left,hqp,mul_zero,sub_zero,
    LinearIsometry.coe_toContinuousLinearMap]

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (B : HistoryData D)

theorem select_physical_history_coordinate
    (hHs : ∀ t, (B.H.field t 0).IsSymmetric)
    (h CM CH ε : ℝ) (hh : 0 < h) (hLayer : 1 ≤ h * D.T)
    (hCM : 0 ≤ CM) (hCH : 0 ≤ CH) (hε : 0 ≤ ε)
    (hM : ∀ t, ‖D.M.field t 0‖ ≤ CM * h)
    (hHnorm : ‖B.coefficients.labelHessian 0‖ ≤ CH * h ^ 2)
    (p q : Space) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : ⟪p, q⟫_ℝ = 0)
    (hpm : ⟪D.normal.field ⟨D.T, D.T_pos.le, le_rfl⟩ 0, p⟫_ℝ = 0)
    (hqm : ⟪D.normal.field ⟨D.T, D.T_pos.le, le_rfl⟩ 0, q⟫_ℝ = 0)
    (hεsmall : 16 * (activationConstant CM CH + 1) * ε ≤ 1)
    (hB : ‖D.M.field ⟨D.T, D.T_pos.le, le_rfl⟩ 0 - h • rankOne ℝ q p‖ ≤ ε * h)
    (hBpp : ⟪D.M.field ⟨D.T, D.T_pos.le, le_rfl⟩ 0 p, p⟫_ℝ < 0) :
    ∃ ξ : U, ξ ≠ 0 ∧
      ⟪B.coefficients.labelVelocity 0 ξ ⟨D.T,D.T_pos.le,le_rfl⟩,q⟫_ℝ=1 ∧
      -8*(activationConstant CM CH+1) ≤
        ⟪B.coefficients.labelVelocity 0 ξ ⟨D.T,D.T_pos.le,le_rfl⟩,p⟫_ℝ ∧
      ⟪B.coefficients.labelVelocity 0 ξ ⟨D.T,D.T_pos.le,le_rfl⟩,p⟫_ℝ ≤ 0 ∧
      ‖ξ‖ ≤ (8*(activationConstant CM CH+1)*D.inverseBound)/h := by
  let P := referencePlane (D.normal.field ⟨D.T,D.T_pos.le,le_rfl⟩ 0)
  let R : P →ₗᵢ[ℝ] Space := P.subtypeₗᵢ
  let p' : P := ⟨p,Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hpm⟩
  let q' : P := ⟨q,Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hqm⟩
  have hR : ∀ Y : P, ⟪D.normal.field ⟨D.T,D.T_pos.le,le_rfl⟩ 0,R Y⟫_ℝ=0 :=
    fun Y => Submodule.mem_orthogonal_singleton_iff_inner_right.mp Y.property
  have he : ‖terminalPerturbation D.T D.T_pos.le R (pathEvaluation 0 D.M.field) p' q' h‖ ≤ ε*h :=
    (terminalPerturbation_norm_le D.T D.T_pos.le R (pathEvaluation 0 D.M.field) p' q' h).trans hB
  have hc : ⟪terminalPerturbation D.T D.T_pos.le R (pathEvaluation 0 D.M.field) p' q' h p',p'⟫_ℝ <
      0 := by
    rw [terminalPerturbation_diagonal D.T D.T_pos.le R (pathEvaluation 0 D.M.field) p' q' h hpq]
    exact hBpp
  exact select_history_coordinate B R hR hHs h CM CH ε hh hLayer hCM hCH hε hM hHnorm
    p' q' hp hq hpq hεsmall he hc

end EulerPacketActivationHistory

end
end

end

@[expose] public section

noncomputable section

namespace EulerPacketActivationHistory

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerTransversePacketProvider EulerTransverseActivationSelection
  EulerPacketMovingFrame EulerPacketNormalizedPrimary EulerPacketCrossProduct
  EulerPacketPrimaryFactorization

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))

theorem exists_activated_primary
    (m v : ℝ → Space) (hm : m τ ≠ 0) (hv : v τ ≠ 0) (hmv : ⟪m τ, v τ⟫_ℝ = 0)
    (hchoice : D.m₀ = activationDirection (D.deformationEquiv ⟨τ, hτ.le, hτT.le⟩ 0)
      (cross (unit (m τ)) (unit (v τ))))
    (hHs : ∀ t, (B.H.field t 0).IsSymmetric)
    (h CM CH ζ a ε : ℝ) (hh : 0 < h) (hLayer : 1 ≤ h * τ)
    (hCM : 0 ≤ CM) (hCH : 0 ≤ CH) (hζ : 0 ≤ ζ) (hε : 0 < ε)
    (hM : ∀ t : Icc (0 : ℝ) τ, ‖(D.initial τ hτ hτT.le).M.field t 0‖ ≤ CM*h)
    (hHnorm : ‖B.coefficients.labelHessian 0‖ ≤ CH*h^2)
    (hζsmall : 16*(activationConstant CM CH+1)*ζ ≤ 1)
    (hB : ‖D.M.field ⟨τ,hτ.le,hτT.le⟩ 0 -
      h • rankOne ℝ (unit (v τ)) (unit (m τ))‖ ≤ ζ*h)
    (hBpp : ⟪D.M.field ⟨τ,hτ.le,hτT.le⟩ 0 (unit (m τ)),unit (m τ)⟫_ℝ < 0) :
    let s₀ := activationRayScale (D.deformationEquiv ⟨τ,hτ.le,hτT.le⟩ 0)
      (cross (unit (m τ)) (unit (v τ)))
    0 < s₀ ∧
      scaledRay m v (fun s => D.normal.field (D.clamp s) 0) s₀ τ a ε 0 = ![0,0,1] ∧
      ∃ ξ : U, ∃ lam : ℝ, ξ ≠ 0 ∧ 0 ≤ lam ∧
        lam ≤ 8*(activationConstant CM CH+1)/ε ∧
        ‖ξ‖ ≤ (8*(activationConstant CM CH+1)*D.inverseBound)/h ∧
        scaledVelocity m v (fun s => uncutVelocity τ hτ hτT B ξ s 0) τ a ε 0 0 = -lam ∧
        scaledVelocity m v (fun s => uncutVelocity τ hτ hτT B ξ s 0) τ a ε 0 1 = 1 := by
  dsimp only
  have hnormal := actual_normal_of_activation_choice D ⟨τ,hτ.le,hτT.le⟩ 0 _ hchoice
  have hp : ⟪(D.initial τ hτ hτT.le).normal.field ⟨τ,hτ.le,le_rfl⟩ 0,unit (m τ)⟫_ℝ=0 := by
    change ⟪D.normal.field ⟨τ,hτ.le,hτT.le⟩ 0,unit (m τ)⟫_ℝ=0
    rw [hnormal,real_inner_smul_left,real_inner_comm,inner_cross_first,mul_zero]
  have hq : ⟪(D.initial τ hτ hτT.le).normal.field ⟨τ,hτ.le,le_rfl⟩ 0,unit (v τ)⟫_ℝ=0 := by
    change ⟪D.normal.field ⟨τ,hτ.le,hτT.le⟩ 0,unit (v τ)⟫_ℝ=0
    rw [hnormal,real_inner_smul_left,real_inner_comm,inner_cross_second,mul_zero]
  obtain ⟨ξ,hξ,hqξ,hplo,hphi,hξnorm⟩ := select_physical_history_coordinate B hHs
    h CM CH ζ hh hLayer hCM hCH hζ hM hHnorm
    (unit (m τ)) (unit (v τ)) (unit_norm hm) (unit_norm hv) (unit_inner_zero hmv)
    hp hq hζsmall hB hBpp
  have hs := actual_activation_scaled_ray D m v ⟨τ,hτ.le,hτT.le⟩ a ε hm hv hmv hchoice
  refine ⟨hs.1,hs.2,ξ,-⟪B.coefficients.labelVelocity 0 ξ ⟨τ,hτ.le,le_rfl⟩,unit (m τ)⟫_ℝ/ε,
    hξ,?_⟩
  have hw : uncutVelocity τ hτ hτT B ξ τ 0 = B.coefficients.labelVelocity 0 ξ ⟨τ,hτ.le,le_rfl⟩ :=
    uncutVelocity_history τ hτ hτT B ξ ⟨τ,hτ.le,le_rfl⟩ 0
  have hpw : ⟪unit (m τ),uncutVelocity τ hτ hτT B ξ τ 0⟫_ℝ =
      ⟪B.coefficients.labelVelocity 0 ξ ⟨τ,hτ.le,le_rfl⟩,unit (m τ)⟫_ℝ := by
    rw [hw,real_inner_comm]
  have hqw : ⟪unit (v τ),uncutVelocity τ hτ hτT B ξ τ 0⟫_ℝ=1 := by
    rw [hw,real_inner_comm]
    exact hqξ
  have hplo' : -(8*(activationConstant CM CH+1)) ≤
      ⟪B.coefficients.labelVelocity 0 ξ ⟨τ,hτ.le,le_rfl⟩,unit (m τ)⟫_ℝ := by
    convert! hplo using 1
    ring
  have hvinit := activation_scaled_velocity (a := a) hε hplo' hphi hpw hqw
  refine ⟨hvinit.1,hvinit.2.1,?_,hvinit.2.2.1,hvinit.2.2.2⟩
  apply hξnorm.trans
  apply div_le_div_of_nonneg_right _ hh.le
  exact mul_le_mul_of_nonneg_left (D.initial_inverseBound_le τ hτ hτT.le) (by
    unfold activationConstant
    positivity)

end EulerPacketActivationHistory
