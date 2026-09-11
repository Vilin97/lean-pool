/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LinearDuhamel
public import LeanPool.NavierStokesAndEuler.Euler.ContinuousTimeIntegral

/-!
# The actual bounded solution and Volterra inverse

The Duhamel integral is a bounded linear map in the forcing and initial data.
It gives a two-sided inverse for the continuous-path Volterra operator. This
unweighted inverse is used only for qualitative parameter regularity; source
quantitative estimates use the original relative propagator bound directly.
-/

@[expose] public section


noncomputable section


namespace EulerLinearDuhamel

open Set ContinuousLinearMap EulerVolterraConvolution EulerContinuousTimeIntegral
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {T : ℝ} {hT : 0 ≤ T} {B : C(Icc (0 : ℝ) T, E →L[ℝ] E)}

namespace Evolution

variable (U : Evolution T hT B)

/-- The actual zero-initial-data forcing operator. -/
def forcingOperator : C(Icc (0 : ℝ) T,E) →L[ℝ] C(Icc (0 : ℝ) T,E) :=
  (multiplier U.forward).comp ((integral T hT).comp (multiplier U.backward))

/-- The actual homogeneous initial-data operator. -/
def initialOperator : E →L[ℝ] C(Icc (0 : ℝ) T,E) :=
  (multiplier U.forward).comp ((ContinuousLinearMap.const ℝ (Icc (0 : ℝ) T)).comp
    (U.backward ⟨0,le_rfl,hT⟩))

/-- The bounded forcing operator is exactly the Duhamel construction. -/
theorem forcingOperator_eq (f : C(Icc (0 : ℝ) T, E)) :
    U.forcingOperator f = U.solution f 0 := by
  ext t
  simp only [forcingOperator, comp_apply, multiplier_apply,
      EulerContinuousTimeIntegral.integral_apply, realIntegral,
    solution, ContinuousMap.coe_mk, solutionReal, transformedForcing, extendPath, map_zero,
    zero_add, projIcc_of_mem hT t.property]

/-- Splitting the actual forced solution into its two bounded data maps. -/
theorem solution_eq_operators (f : C(Icc (0 : ℝ) T, E)) (a₀ : E) :
    U.solution f a₀ = U.initialOperator a₀ + U.forcingOperator f := by
  ext t
  change extendPath T hT U.forward t
    (U.backward ⟨0,le_rfl,hT⟩ a₀ + ∫ s in (0 : ℝ)..(t : ℝ), U.transformedForcing f s) = _
  rw [show extendPath T hT U.forward t = U.forward t by
    simp only [extendPath, projIcc_of_mem hT t.property], map_add]
  rfl

/-- The original relative propagator bound controls the actual forcing map. -/
theorem forcingOperator_profile_bound (f : C(Icc (0 : ℝ) T, E))
    (g : Icc (0 : ℝ) T → ℝ) (hg : ∀ t, 0 < g t)
    (hg₀ : g ⟨0, le_rfl, hT⟩ = 1) (C D : ℝ) (hC : 0 ≤ C)
    (hU : ∀ t s : Icc (0 : ℝ) T, s ≤ t → ‖U.propagator t s‖ ≤ C*g t/g s)
    (hf : ∀ s, ‖f s‖ ≤ D*g s) (t : Icc (0 : ℝ) T) :
    ‖U.forcingOperator f t‖ ≤ C*g t*(t : ℝ)*D := by
  rw [U.forcingOperator_eq]
  simpa only [norm_zero, zero_add, mul_assoc] using
    U.solution_profile_bound f 0 g hg hg₀ C D hC hU hf t

omit [CompleteSpace E] in
/-- The homogeneous initial-data map has the same profile and propagator constant. -/
theorem initialOperator_profile_bound (a₀ : E)
    (g : Icc (0 : ℝ) T → ℝ) (hg₀ : g ⟨0, le_rfl, hT⟩ = 1) (C : ℝ)
    (hU : ∀ t s : Icc (0 : ℝ) T, s ≤ t → ‖U.propagator t s‖ ≤ C*g t/g s)
    (t : Icc (0 : ℝ) T) : ‖U.initialOperator a₀ t‖ ≤ C*g t*‖a₀‖ := by
  change ‖U.propagator t ⟨0,le_rfl,hT⟩ a₀‖ ≤ _
  exact (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
    (by simpa only [hg₀, div_one] using hU t ⟨0,le_rfl,hT⟩ t.property.1) (norm_nonneg a₀))

/-- The forced path satisfies the actual integral equation. -/
theorem solution_integral (f : C(Icc (0 : ℝ) T, E)) (a₀ : E) :
    U.solution f a₀ = (ContinuousLinearMap.const ℝ (Icc (0 : ℝ) T)) a₀ +
      integral T hT (multiplier B (U.solution f a₀) + f) := by
  ext t
  have hd : ∀ s : Icc (0 : ℝ) T,
      HasDerivWithinAt (U.solutionReal f a₀)
        ((multiplier B (U.solution f a₀) + f) s) (Icc (0 : ℝ) T) s :=
    U.solution_derivative f a₀
  have he := eq_initial_add_integral T hT (multiplier B (U.solution f a₀) + f)
    (U.solutionReal f a₀) hd t
  have h₀ : U.solutionReal f a₀ 0 = a₀ := U.solution_initial f a₀
  change U.solutionReal f a₀ t = a₀ + integral T hT (multiplier B (U.solution f a₀) + f) t
  simpa only [h₀] using he

end Evolution

/-- The ordinary continuous-path Volterra operator. -/
def volterraOperator (T : ℝ) (hT : 0 ≤ T) (B : C(Icc (0 : ℝ) T, E →L[ℝ] E)) :
    C(Icc (0 : ℝ) T,E) →L[ℝ] C(Icc (0 : ℝ) T,E) :=
  ContinuousLinearMap.id ℝ _ - (integral T hT).comp (multiplier B)

namespace Evolution

variable (U : Evolution T hT B)

/-- Duhamel's formula gives an actual inverse on every continuous input. -/
def volterraInverse : C(Icc (0 : ℝ) T,E) →L[ℝ] C(Icc (0 : ℝ) T,E) :=
  ContinuousLinearMap.id ℝ _ + U.forcingOperator.comp (multiplier B)

/-- The Volterra operator followed by the constructed inverse is the identity. -/
theorem volterra_operator_inverse (h : C(Icc (0 : ℝ) T, E)) :
    volterraOperator T hT B (U.volterraInverse h) = h := by
  let w := U.solution (multiplier B h) 0
  have hw : w = integral T hT (multiplier B w + multiplier B h) := by
    simpa only [map_zero, zero_add] using U.solution_integral (multiplier B h) 0
  change h + U.forcingOperator (multiplier B h) -
    integral T hT (multiplier B (h + U.forcingOperator (multiplier B h))) = h
  rw [U.forcingOperator_eq]
  change h + w - integral T hT (multiplier B (h+w)) = h
  rw [map_add, add_comm (multiplier B h), ← hw]
  exact add_sub_cancel_right h w

include U in
/-- The homogeneous Volterra equation has only its zero solution. -/
theorem volterraOperator_injective : Function.Injective (volterraOperator T hT B) := by
  have hker : ∀ h, volterraOperator T hT B h = 0 → h = 0 := by
    intro h hh
    have he : h = integral T hT (multiplier B h) := sub_eq_zero.mp hh
    have hd : ∀ t : Icc (0 : ℝ) T,
        HasDerivWithinAt (extendPath T hT h)
          (B t (extendPath T hT h t) + (0 : C(Icc (0 : ℝ) T,E)) t) (Icc (0 : ℝ) T) t := by
      intro t
      have hp := integral_hasDerivWithinAt T hT (multiplier B h) t
      rw [← he] at hp
      simpa only [extendPath, projIcc_of_mem hT t.property, ContinuousMap.zero_apply,
        add_zero, multiplier_apply] using hp
    have h₀ : extendPath T hT h 0 = 0 := by
      rw [he]
      simpa only [extendPath, projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩)] using
        integral_initial T hT (multiplier B h)
    have hz : U.solution (0 : C(Icc (0 : ℝ) T,E)) 0 = 0 := by
      rw [← U.forcingOperator_eq, map_zero]
    ext t
    have hu := U.solution_unique 0 0 (extendPath T hT h) hd h₀ t
    simpa only [extendPath, projIcc_of_mem hT t.property, hz, ContinuousMap.zero_apply] using hu
  intro u v huv
  have hz : volterraOperator T hT B (u-v) = 0 := by rw [map_sub, huv, sub_self]
  exact sub_eq_zero.mp (hker (u-v) hz)

/-- The constructed inverse is also a left inverse. -/
theorem volterra_inverse_operator (h : C(Icc (0 : ℝ) T, E)) :
    U.volterraInverse (volterraOperator T hT B h) = h := by
  apply U.volterraOperator_injective
  exact U.volterra_operator_inverse _

/-- The actual two-sided Volterra equivalence. -/
def volterraEquiv : C(Icc (0 : ℝ) T,E) ≃L[ℝ] C(Icc (0 : ℝ) T,E) :=
  ContinuousLinearEquiv.equivOfInverse (volterraOperator T hT B) U.volterraInverse
    U.volterra_inverse_operator U.volterra_operator_inverse

end Evolution

end EulerLinearDuhamel
