/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseEndpointCoordinates
import LeanPool.NavierStokesAndEuler.Euler.FixedEndpointStrong
import LeanPool.NavierStokesAndEuler.Euler.TimeH1ContinuousDerivative
public import LeanPool.NavierStokesAndEuler.Euler.TransverseGramInverse
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
public import LeanPool.NavierStokesAndEuler.Euler.VolterraConvolution
public import Mathlib.Analysis.Calculus.Deriv.Basic
import LeanPool.NavierStokesAndEuler.Euler.TimeH1WeakPairing
import LeanPool.NavierStokesAndEuler.Euler.TransverseEndpointEnergy
public import LeanPool.NavierStokesAndEuler.Euler.ContinuousTimeIntegral
public import LeanPool.NavierStokesAndEuler.Euler.InitialTimePrimitive

/-!
The constructed affine-terminal inverse as a classical coordinate path,
and its uniqueness among actual twice differentiable coordinate paths.
-/

section

/-! The actual continuous-time integral agrees with both Bochner primitive constructions. -/

@[expose] public section

noncomputable section

namespace EulerTimeContinuousPrimitive

open Set MeasureTheory ContinuousLinearMap EulerTimeLp EulerInitialTimePrimitive
  EulerTerminalTimePrimitive EulerVolterraConvolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (T : ℝ) (hT : 0 ≤ T)

theorem initialPrimitive_pathLp (f : C(Icc (0 : ℝ) T, E)) :
    initialPrimitive T hT (pathLp T hT f) = EulerContinuousTimeIntegral.integral T hT f := by
  apply ContinuousMap.ext
  intro t
  rw [initialPrimitive_apply,initialRealPrimitive_eq_integral]
  change (∫ s in (0 : ℝ)..(t : ℝ), zeroExtension T (pathLp T hT f) s) =
    ∫ s in (0 : ℝ)..(t : ℝ), extendPath T hT f s
  rw [intervalIntegral.integral_of_le t.property.1,intervalIntegral.integral_of_le t.property.1]
  apply integral_congr_ae
  have he := (zeroExtension_ae T (pathLp T hT f)).trans (pathLp_ae T hT f)
  exact ae_restrict_of_ae_restrict_of_subset
    (show Ioc (0 : ℝ) (t : ℝ) ⊆ Icc (0 : ℝ) T from
      fun s hs => ⟨hs.1.le,hs.2.trans t.property.2⟩) he

theorem initialTrace_pathLp (f : C(Icc (0 : ℝ) T, E)) :
    initialTrace T hT (pathLp T hT f) =
      -EulerContinuousTimeIntegral.integral T hT f ⟨T,hT,le_rfl⟩ := by
  have he := initialPrimitive_eq_terminal_sub T hT (pathLp T hT f) ⟨T,hT,le_rfl⟩
  rw [initialPrimitive_pathLp,terminalPrimitive_terminal,zero_sub] at he
  simpa only [neg_neg] using congrArg Neg.neg he.symm

theorem primitive_eq_path (p q : C(Icc (0 : ℝ) T, E))
    (hd : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT p) (q t) (Icc (0 : ℝ) T) t)
    (hzero : p ⟨0,le_rfl,hT⟩ = 0) :
    initialPrimitive T hT (pathLp T hT q) = p := by
  rw [initialPrimitive_pathLp]
  apply ContinuousMap.ext
  intro t
  have he := EulerContinuousTimeIntegral.eq_initial_add_integral T hT q (extendPath T hT p) hd t
  simpa only [extendPath,projIcc_of_mem hT t.property,
    projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩),hzero,zero_add] using he.symm

theorem initialTrace_eq_zero (p q : C(Icc (0 : ℝ) T, E))
    (hd : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT p) (q t) (Icc (0 : ℝ) T) t)
    (hzero : p ⟨0,le_rfl,hT⟩ = 0) (hterminal : p ⟨T,hT,le_rfl⟩ = 0) :
    initialTrace T hT (pathLp T hT q) = 0 := by
  have he := initialPrimitive_eq_terminal_sub T hT (pathLp T hT q) ⟨T,hT,le_rfl⟩
  rw [primitive_eq_path T hT p q hd hzero,hterminal,terminalPrimitive_terminal,zero_sub] at he
  exact neg_eq_zero.mp he.symm

theorem primitiveTimeLp_eq_pathLp (p q : C(Icc (0 : ℝ) T, E))
    (hd : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT p) (q t) (Icc (0 : ℝ) T) t)
    (hzero : p ⟨0,le_rfl,hT⟩ = 0) (hterminal : p ⟨T,hT,le_rfl⟩ = 0) :
    primitiveTimeLp T hT (pathLp T hT q) = pathLp T hT p := by
  have hc : terminalPrimitive T hT (pathLp T hT q) = p := by
    apply ContinuousMap.ext
    intro t
    have he := initialPrimitive_eq_terminal_sub T hT (pathLp T hT q) t
    rw [primitive_eq_path T hT p q hd hzero,initialTrace_eq_zero T hT p q hd hzero hterminal,
      sub_zero] at he
    exact he.symm
  change pathLp T hT (terminalPrimitive T hT (pathLp T hT q)) = pathLp T hT p
  rw [hc]

omit [CompleteSpace E] [NormedSpace ℝ E] in
theorem pathLp_injective (hTpos : 0 < T) :
    Function.Injective (pathLp (E := E) T hT) := by
  intro p q he
  have hae : extendPath T hT p =ᵐ[timeMeasure T] extendPath T hT q :=
    (pathLp_ae T hT p).symm.trans (he ▸ pathLp_ae T hT q)
  have hfun := Measure.eqOn_Icc_of_ae_eq volume hTpos.ne hae
    (extendPath_continuous T hT p).continuousOn (extendPath_continuous T hT q).continuousOn
  apply ContinuousMap.ext
  intro t
  simpa only [extendPath,projIcc_of_mem hT t.property] using hfun t.property

end EulerTimeContinuousPrimitive

end
end

end

section

/-!
Boundary uniqueness for the literal moving-frame coordinate equation.
The proof passes through the physical displacement and the already proved
short-time energy coercivity, including the source identity Q'' = -H Q.
-/

section

/-!
Uniqueness for an actual twice differentiable zero-endpoint path follows
from the source short-time energy coercivity. The differential residual
need only be orthogonal to the displacement, as for a constrained frame
equation. No inverse or uniqueness assertion is assumed.
-/

@[expose] public section

noncomputable section

namespace EulerTimeEndpointEnergyUniqueness

open Set MeasureTheory InnerProductSpace EulerTimeLp EulerVolterraConvolution
  EulerInitialTimePrimitive EulerTerminalTimePrimitive EulerTimeContinuousPrimitive
  EulerTimeH1WeakPairing EulerTransverseEndpointEnergy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem zero_of_energy_equation (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (H : C(Icc (0 : ℝ) T, E →L[ℝ] E)) (K : ℝ) (hK : 0 ≤ K)
    (hH : ∀ t x, ⟪H t x, x⟫_ℝ ≤ K * ‖x‖ ^ 2)
    (hsmall : K * (T ^ 2 / 2) ≤ 1 / 2)
    (p u q : C(Icc (0 : ℝ) T, E))
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

end
end

end

@[expose] public section

noncomputable section

namespace EulerFrameEndpointUniqueness

open Set MeasureTheory InnerProductSpace ContinuousLinearMap EulerTimeLp
  EulerVolterraConvolution EulerTransverseGramInverse EulerTimeEndpointEnergyUniqueness

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Apply path, given by `⟨fun t => Q t (z t),Q.continuous.clm_apply z.continuous⟩`. -/
def applyPath {T : ℝ} (Q : C(Icc (0 : ℝ) T, U →L[ℝ] E))
    (z : C(Icc (0 : ℝ) T, U)) : C(Icc (0 : ℝ) T,E) :=
  ⟨fun t => Q t (z t),Q.continuous.clm_apply z.continuous⟩

omit [CompleteSpace U] [CompleteSpace E] in
theorem applyPath_hasDerivWithinAt (T : ℝ) (hT : 0 ≤ T)
    (Q Q₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E))
    (z v : C(Icc (0 : ℝ) T, U))
    (hd : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)
    (hz : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT z) (v t) (Icc (0 : ℝ) T) t)
    (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (applyPath Q z))
      ((applyPath Q₁ z+applyPath Q v) t) (Icc (0 : ℝ) T) t := by
  change HasDerivWithinAt (fun s => extendPath T hT Q s (extendPath T hT z s))
    (Q₁ t (z t)+Q t (v t)) (Icc (0 : ℝ) T) t
  simpa only [extendPath,projIcc_of_mem hT t.property] using (hd t).clm_apply (hz t)

theorem zero_of_projected_equation (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (Q Q₁ Q₂ : C(Icc (0 : ℝ) T, U →L[ℝ] E))
    (H : C(Icc (0 : ℝ) T, E →L[ℝ] E))
    (c : ℝ) (hc : 0 < c) (hQ : ∀ t v, c * ‖v‖ ^ 2 ≤ ‖Q t v‖ ^ 2)
    (hd : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)
    (hd₁ : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT Q₁) (Q₂ t) (Icc (0 : ℝ) T) t)
    (hframe : ∀ t, Q₂ t = -((H t).comp (Q t)))
    (K : ℝ) (hK : 0 ≤ K) (hH : ∀ t x, ⟪H t x,x⟫_ℝ ≤ K*‖x‖^2)
    (hsmall : K*(T^2/2) ≤ 1/2)
    (z v a : C(Icc (0 : ℝ) T,U))
    (hz : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT z) (v t) (Icc (0 : ℝ) T) t)
    (hv : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT v) (a t) (Icc (0 : ℝ) T) t)
    (hzero : z ⟨0,le_rfl,hT⟩ = 0) (hterminal : z ⟨T,hT,le_rfl⟩ = 0)
    (heq : ∀ t, gram (Q t) (a t) = (Q t).adjoint ((-2 : ℝ) • Q₁ t (v t))) :
    z = 0 ∧ v = 0 := by
  let p := applyPath Q z
  let u := applyPath Q₁ z+applyPath Q v
  let q := (applyPath Q₂ z+applyPath Q₁ v)+(applyPath Q₁ v+applyPath Q a)
  have hp (t : Icc (0 : ℝ) T) :
      HasDerivWithinAt (extendPath T hT p) (u t) (Icc (0 : ℝ) T) t :=
    applyPath_hasDerivWithinAt T hT Q Q₁ z v hd hz t
  have hu (t : Icc (0 : ℝ) T) :
      HasDerivWithinAt (extendPath T hT u) (q t) (Icc (0 : ℝ) T) t :=
    (applyPath_hasDerivWithinAt T hT Q₁ Q₂ z v hd₁ hz t).add
      (applyPath_hasDerivWithinAt T hT Q Q₁ v a hd hv t)
  have horth (t : Icc (0 : ℝ) T) : ⟪q t+H t (p t),p t⟫_ℝ = 0 := by
    have hcancel : q t+H t (p t) = (2 : ℝ) • Q₁ t (v t)+Q t (a t) := by
      change (Q₂ t (z t)+Q₁ t (v t))+(Q₁ t (v t)+Q t (a t))+H t (Q t (z t)) = _
      rw [hframe]
      simp only [neg_apply,comp_apply,two_smul]
      abel
    rw [hcancel]
    change ⟪(2 : ℝ) • Q₁ t (v t)+Q t (a t),Q t (z t)⟫_ℝ = 0
    rw [← adjoint_inner_left]
    have ha : (Q t).adjoint (Q t (a t)) =
        (Q t).adjoint ((-2 : ℝ) • Q₁ t (v t)) := heq t
    rw [map_add,map_smul,ha,map_smul]
    simp only [← add_smul]
    norm_num
  have hphysical := zero_of_energy_equation T hT hTpos H K hK hH hsmall p u q hp hu
    (by change Q _ (z _) = 0; rw [hzero,map_zero])
    (by change Q _ (z _) = 0; rw [hterminal,map_zero]) horth
  have hz0 : z = 0 := by
    apply ContinuousMap.ext
    intro t
    have hp0 := congrArg (fun w : C(Icc (0 : ℝ) T,E) => w t) hphysical.1
    change Q t (z t) = 0 at hp0
    rw [← frameLeftInverse_apply (Q t) c hc (hQ t) (z t),hp0,map_zero,ContinuousMap.zero_apply]
  refine ⟨hz0,?_⟩
  apply ContinuousMap.ext
  intro t
  have hu0 := congrArg (fun w : C(Icc (0 : ℝ) T,E) => w t) hphysical.2
  change Q₁ t (z t)+Q t (v t) = 0 at hu0
  rw [hz0,ContinuousMap.zero_apply,map_zero,zero_add] at hu0
  rw [← frameLeftInverse_apply (Q t) c hc (hQ t) (v t),hu0,map_zero,ContinuousMap.zero_apply]

theorem unique_of_projected_equation (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (Q Q₁ Q₂ : C(Icc (0 : ℝ) T, U →L[ℝ] E))
    (H : C(Icc (0 : ℝ) T, E →L[ℝ] E))
    (c : ℝ) (hc : 0 < c) (hQ : ∀ t v, c * ‖v‖ ^ 2 ≤ ‖Q t v‖ ^ 2)
    (hd : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)
    (hd₁ : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT Q₁) (Q₂ t) (Icc (0 : ℝ) T) t)
    (hframe : ∀ t, Q₂ t = -((H t).comp (Q t)))
    (K : ℝ) (hK : 0 ≤ K) (hH : ∀ t x, ⟪H t x,x⟫_ℝ ≤ K*‖x‖^2)
    (hsmall : K*(T^2/2) ≤ 1/2)
    (z v a w r b : C(Icc (0 : ℝ) T,U))
    (hz : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT z) (v t) (Icc (0 : ℝ) T) t)
    (hv : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT v) (a t) (Icc (0 : ℝ) T) t)
    (hw : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT w) (r t) (Icc (0 : ℝ) T) t)
    (hr : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT r) (b t) (Icc (0 : ℝ) T) t)
    (hzero : z ⟨0,le_rfl,hT⟩ = w ⟨0,le_rfl,hT⟩)
    (hterminal : z ⟨T,hT,le_rfl⟩ = w ⟨T,hT,le_rfl⟩)
    (heq : ∀ t, gram (Q t) (a t) = (Q t).adjoint ((-2 : ℝ) • Q₁ t (v t)))
    (heq' : ∀ t, gram (Q t) (b t) = (Q t).adjoint ((-2 : ℝ) • Q₁ t (r t))) :
    z = w ∧ v = r := by
  have h := zero_of_projected_equation T hT hTpos Q Q₁ Q₂ H c hc hQ hd hd₁ hframe
    K hK hH hsmall (z-w) (v-r) (a-b) (fun t => (hz t).sub (hw t))
    (fun t => (hv t).sub (hr t))
    (by simp only [ContinuousMap.sub_apply,hzero,sub_self])
    (by simp only [ContinuousMap.sub_apply,hterminal,sub_self])
    (by
      intro t
      simp only [ContinuousMap.sub_apply,map_sub,smul_sub,heq,heq'])
  exact ⟨sub_eq_zero.mp h.1,sub_eq_zero.mp h.2⟩

end EulerFrameEndpointUniqueness

end
end

end

@[expose] public section

noncomputable section

namespace EulerFixedEndpointClassical

open Set MeasureTheory ContinuousLinearMap InnerProductSpace
  EulerTimeLp EulerTerminalTimePrimitive EulerInitialTimePrimitive
  EulerVolterraConvolution EulerTransverseEndpointCoordinates
  EulerTransverseEndpointParameter EulerTransverseFixedEndpoint
  EulerTransverseForwardInverse EulerTransverseGramInverse
  EulerTransverseEndpointVelocity EulerTimeH1FrameTransport

variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (T : ℝ) (hT : 0 ≤ T)
  (Q Q₁ : C(Icc (0 : ℝ) T, U →L[ℝ] E))
  (H : C(Icc (0 : ℝ) T, E →L[ℝ] E))
  (c : ℝ) (hc : 0 < c) (hQ : ∀ t v, c * ‖v‖ ^ 2 ≤ ‖Q t v‖ ^ 2)
  (hd : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (extendPath T hT Q) (Q₁ t) (Icc (0 : ℝ) T) t)
  (K : ℝ) (hK : 0 ≤ K) (hH : ∀ t v, ⟪H t v, v⟫_ℝ ≤ K * ‖v‖ ^ 2)
  (hsmall : K * (T ^ 2 / 2) ≤ 1 / 2)

/-- Displacement, given by `(initialPrimitive T hT).comp (coordinateSlope T hT Q Q₁ H c hc hQ hd
K hK hH hsmall)`. -/
def displacement : U →L[ℝ] C(Icc (0 : ℝ) T,U) :=
  (initialPrimitive T hT).comp (coordinateSlope T hT Q Q₁ H c hc hQ hd K hK hH hsmall)

/-- Acceleration as an element of `U →L[ℝ] C(Icc (0 : ℝ) T,U)`. -/
def acceleration : U →L[ℝ] C(Icc (0 : ℝ) T,U) :=
  (EulerContinuousTimeIntegral.multiplier (generator T Q Q₁ c hc hQ)).comp
    (continuousCoordinateVelocity T hT Q Q₁ H c hc hQ hd K hK hH hsmall)

theorem displacement_initial (Y : U) :
    displacement T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y ⟨0,le_rfl,hT⟩ = 0 :=
  initialPrimitive_initial T hT _

theorem displacement_terminal (hTpos : 0 < T) (Y : U) :
    displacement T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y ⟨T,hT,le_rfl⟩ = Y := by
  let r := fixedEndpointCorrection T hT Q Q₁ H c hc hQ hd K hK hH hsmall
    (affineTrial T hT Q Q₁) Y
  have hr : initialTrace T hT (r : TimeLp T U) = 0 := r.property
  change initialPrimitive T hT (constantFieldOperator T hT (T⁻¹ • Y)-(r : TimeLp T U)) _ = Y
  rw [map_sub,ContinuousMap.sub_apply,initialPrimitive_constantFieldOperator,
    initialPrimitive_eq_terminal_sub,terminalPrimitive_terminal]
  change T • (T⁻¹ • Y)-(0-initialTrace T hT (r : TimeLp T U)) = Y
  rw [hr,sub_self,sub_zero,smul_smul,mul_inv_cancel₀ hTpos.ne',one_smul]

variable (Q₂ : C(Icc (0 : ℝ) T, U →L[ℝ] E)) (hTpos : 0 < T)
  (hd₁ : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (extendPath T hT Q₁) (Q₂ t) (Icc (0 : ℝ) T) t)
  (hframe : ∀ t, Q₂ t = -((H t).comp (Q t)))

include Q₂ hTpos hd₁ hframe in
theorem velocity_ae (Y : U) :
    (coordinateSlope T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y : ℝ → U) =ᵐ[timeMeasure T]
      extendPath T hT (continuousCoordinateVelocity T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y) := by
  have ha := EulerFixedEndpointStrong.coordinateSlope_ae T hT Q Q₁ H c hc hQ hd K hK hH hsmall
      hTpos Y
  filter_upwards [ha,ae_restrict_mem measurableSet_Icc] with t ht hm
  rw [ht]
  change _ = continuousCoordinateVelocity T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y (projIcc 0 T hT t)
  rw [projIcc_of_mem hT hm]
  exact (EulerFixedEndpointStrong.continuousCoordinateVelocity_eq T hT Q Q₁ H c hc hQ hd K hK hH
    hsmall Q₂ hTpos hd₁ hframe Y ⟨t,hm⟩).symm

include Q₂ hTpos hd₁ hframe in
theorem displacement_hasDerivWithinAt (Y : U) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (displacement T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y))
      (continuousCoordinateVelocity T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y t)
      (Icc (0 : ℝ) T) t := by
  have hh := EulerTimeH1ContinuousDerivative.hasDerivWithinAt_of_continuous_representative
    T hT (coordinateSlope T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y)
    (continuousCoordinateVelocity T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y)
    (velocity_ae T hT Q Q₁ H c hc hQ hd K hK hH hsmall Q₂ hTpos hd₁ hframe Y)
    (initialRealPrimitive T (coordinateSlope T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y))
    (initialRealPrimitive_absolutelyContinuous T _) (initialRealPrimitive_hasDerivAt_ae T _) t
  apply hh.congr_of_mem _ t.property
  intro s hs
  change initialRealPrimitive T _ (projIcc 0 T hT s) = initialRealPrimitive T _ s
  rw [projIcc_of_mem hT hs]
  rfl

include Q₂ hTpos hd₁ hframe in
theorem velocity_hasDerivWithinAt (Y : U) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt
      (extendPath T hT (continuousCoordinateVelocity T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y))
      (acceleration T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y t) (Icc (0 : ℝ) T) t :=
  EulerFixedEndpointStrong.continuousCoordinateVelocity_hasDerivWithinAt_generator
    T hT Q Q₁ H c hc hQ hd K hK hH hsmall Q₂ hTpos hd₁ hframe Y t

theorem projected_equation (Y : U) (t : Icc (0 : ℝ) T) :
    gram (Q t) (acceleration T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y t) =
      (Q t).adjoint ((-2 : ℝ) • Q₁ t
        (continuousCoordinateVelocity T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y t)) := by
  change gram (Q t) ((-2 : ℝ) • gramInverse (Q t) c hc (hQ t) ((Q t).adjoint
    (Q₁ t (continuousCoordinateVelocity T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y t)))) = _
  rw [map_smul,gram_inverse_apply,map_smul]

include Q₂ hTpos hd₁ hframe in
theorem unique (Y : U) (z v a : C(Icc (0 : ℝ) T, U))
    (hz : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT z) (v t) (Icc (0 : ℝ) T) t)
    (hv : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT v) (a t) (Icc (0 : ℝ) T) t)
    (hz0 : z ⟨0,le_rfl,hT⟩ = 0) (hzT : z ⟨T,hT,le_rfl⟩ = Y)
    (heq : ∀ t, gram (Q t) (a t) = (Q t).adjoint ((-2 : ℝ) • Q₁ t (v t))) :
    z = displacement T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y ∧
    v = continuousCoordinateVelocity T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y := by
  apply EulerFrameEndpointUniqueness.unique_of_projected_equation T hT hTpos
    Q Q₁ Q₂ H c hc hQ hd hd₁ hframe K hK hH hsmall z v a
    (displacement T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y)
    (continuousCoordinateVelocity T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y)
    (acceleration T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y) hz hv
    (displacement_hasDerivWithinAt T hT Q Q₁ H c hc hQ hd K hK hH hsmall Q₂ hTpos hd₁ hframe Y)
    (velocity_hasDerivWithinAt T hT Q Q₁ H c hc hQ hd K hK hH hsmall Q₂ hTpos hd₁ hframe Y)
    (hz0.trans (displacement_initial T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y).symm)
    (hzT.trans (displacement_terminal T hT Q Q₁ H c hc hQ hd K hK hH hsmall hTpos Y).symm)
    heq (projected_equation T hT Q Q₁ H c hc hQ hd K hK hH hsmall Y)

end EulerFixedEndpointClassical
