/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransverseGramInverse
import LeanPool.NavierStokesAndEuler.Euler.TimeEndpointEnergyUniqueness
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
Boundary uniqueness for the literal moving-frame coordinate equation.
The proof passes through the physical displacement and the already proved
short-time energy coercivity, including the source identity Q'' = -H Q.
-/

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
