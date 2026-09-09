/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TimeContinuousPrimitive
public import LeanPool.NavierStokesAndEuler.Euler.TimeH1WeakPairing
public import LeanPool.NavierStokesAndEuler.Euler.TransverseEndpointEnergy

@[expose] public section

/-!
Uniqueness for an actual twice differentiable zero-endpoint path follows
from the source short-time energy coercivity. The differential residual
need only be orthogonal to the displacement, as for a constrained frame
equation. No inverse or uniqueness assertion is assumed.
-/

noncomputable section

namespace EulerTimeEndpointEnergyUniqueness

open Set MeasureTheory InnerProductSpace EulerTimeLp EulerVolterraConvolution
  EulerInitialTimePrimitive EulerTerminalTimePrimitive EulerTimeContinuousPrimitive
  EulerTimeH1WeakPairing EulerTransverseEndpointEnergy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem zero_of_energy_equation (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (H : C(Icc (0 : ℝ) T,E →L[ℝ] E)) (K : ℝ) (hK : 0 ≤ K)
    (hH : ∀ t x, ⟪H t x,x⟫_ℝ ≤ K*‖x‖^2)
    (hsmall : K*(T^2/2) ≤ 1/2)
    (p u q : C(Icc (0 : ℝ) T,E))
    (hp : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT p) (u t) (Icc (0 : ℝ) T) t)
    (hu : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT u) (q t) (Icc (0 : ℝ) T) t)
    (hzero : p ⟨0,le_rfl,hT⟩ = 0) (hterminal : p ⟨T,hT,le_rfl⟩ = 0)
    (heq : ∀ t, ⟪q t+H t (p t),p t⟫_ℝ = 0) : p = 0 ∧ u = 0 := by
  let pu := pathLp T hT u
  let pp := pathLp T hT p
  let pq := pathLp T hT q
  have htrace : initialTrace T hT pu = 0 :=
    initialTrace_eq_zero T hT p u hp hzero hterminal
  have hprimitive : primitiveTimeLp T hT pu = pp :=
    primitiveTimeLp_eq_pathLp T hT p u hp hzero hterminal
  have hinitial : initialPrimitiveTimeLp T hT pu = pp := by
    change pathLp T hT (initialPrimitive T hT pu) = pp
    rw [primitive_eq_path T hT p u hp hzero]
  have hparts : ⟪pu,pu⟫_ℝ = -⟪pq,pp⟫_ℝ := by
    have hh := pathLp_inner_zero_trace T hT u q hu pu htrace
    rw [hprimitive] at hh
    exact hh
  have horth : ⟪pq+timeMultiplier T hT H pp,pp⟫_ℝ = 0 := by
    rw [L2.inner_def]
    apply integral_eq_zero_of_ae
    filter_upwards [Lp.coeFn_add pq (timeMultiplier T hT H pp),
      pathLp_ae T hT p,pathLp_ae T hT q,timeMultiplier_ae T hT H pp]
      with t hadd hpt hqt hHt
    change ⟪(pq+timeMultiplier T hT H pp) t,pp t⟫_ℝ = 0
    rw [hadd,Pi.add_apply,hHt]
    change ⟪pathLp T hT q t+extendPath T hT H t (pathLp T hT p t),
      pathLp T hT p t⟫_ℝ = 0
    rw [hpt,hqt]
    exact heq (projIcc 0 T hT t)
  have henergy : ⟪energyOperator T hT H pu,pu⟫_ℝ = 0 := by
    rw [energyOperator_inner,hinitial,hparts]
    rw [inner_add_left] at horth
    linarith only [horth]
  have hnorm := energyOperator_coercive T hT H K hK hH hsmall pu
  rw [henergy] at hnorm
  have hpu : pu = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg pu]
  have hpzero : p = 0 := by
    rw [← primitive_eq_path T hT p u hp hzero]
    change initialPrimitive T hT pu = 0
    rw [hpu,map_zero]
  refine ⟨hpzero,?_⟩
  apply pathLp_injective T hT hTpos
  change pu = pathLp T hT 0
  rw [hpu]
  exact ((pathLpOperator T hT).map_zero).symm

end EulerTimeEndpointEnergyUniqueness
