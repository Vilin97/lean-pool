/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TimeH1OperatorProduct
public import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section

/-!
# The forced initial value problem from a homogeneous evolution

The source assumes a bound for the homogeneous tangent propagator. Here a
homogeneous fundamental evolution is the input; the forced path is an actual
Bochner integral. Its differential equation, initial trace, uniqueness, and
weighted bounds are proved, rather than included in the evolution data.
-/

noncomputable section


namespace EulerLinearDuhamel

open Set MeasureTheory ContinuousLinearMap EulerVolterraConvolution
open scoped Topology Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

variable (T : ℝ) (hT : 0 ≤ T) (B : C(Icc (0 : ℝ) T,E →L[ℝ] E))

/-- A homogeneous fundamental evolution, with its actual inverse. This data
contains no forced solution or estimate for one. -/
structure Evolution where
  forward : C(Icc (0 : ℝ) T,E →L[ℝ] E)
  backward : C(Icc (0 : ℝ) T,E →L[ℝ] E)
  forward_backward : ∀ t, (forward t).comp (backward t) = ContinuousLinearMap.id ℝ E
  backward_forward : ∀ t, (backward t).comp (forward t) = ContinuousLinearMap.id ℝ E
  derivative : ∀ t : Icc (0 : ℝ) T,
    HasDerivWithinAt (extendPath T hT forward) ((B t).comp (forward t)) (Icc (0 : ℝ) T) t

namespace Evolution

variable {T hT B} (U : Evolution T hT B)

/-- The algebraic unit represented by the homogeneous fundamental map. -/
def unit (t : Icc (0 : ℝ) T) : (E →L[ℝ] E)ˣ where
  val := U.forward t
  inv := U.backward t
  val_inv := U.forward_backward t
  inv_val := U.backward_forward t

omit [CompleteSpace E] in
/-- The supplied inverse is the genuine ring inverse. -/
theorem backward_eq_inverse (t : Icc (0 : ℝ) T) :
    U.backward t = Ring.inverse (U.forward t) :=
  (Ring.inverse_unit (U.unit t)).symm

/-- The inverse fundamental map's derivative follows from the inverse theorem. -/
theorem backward_derivative (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT U.backward)
      (-((U.backward t).comp (B t))) (Icc (0 : ℝ) T) t := by
  have hi := hasFDerivAt_ringInverse (𝕜 := ℝ) (U.unit t)
  change HasFDerivAt Ring.inverse
    (-ContinuousLinearMap.mulLeftRight ℝ (E →L[ℝ] E) (U.backward t) (U.backward t)) (U.forward t)
      at hi
  have hf := U.derivative t
  have hv : extendPath T hT U.forward t = U.forward t := by
    simp only [extendPath, projIcc_of_mem hT t.property]
  rw [← hv] at hi
  have hc := hi.comp_hasDerivWithinAt (t : ℝ) hf
  have hc' : HasDerivWithinAt (fun s => Ring.inverse (extendPath T hT U.forward s))
      (-((U.backward t).comp (B t))) (Icc (0 : ℝ) T) t := by
    convert hc using 1 <;> try rfl
    simp only [neg_apply, mulLeftRight_apply, mul_def, comp_assoc,
      U.forward_backward t, comp_id]
  apply hc'.congr_of_mem _ t.property
  intro s hs
  simp only [extendPath, projIcc_of_mem hT hs]
  exact U.backward_eq_inverse ⟨s,hs⟩

/-- The two-time homogeneous propagator. -/
def propagator (t s : Icc (0 : ℝ) T) : E →L[ℝ] E :=
  (U.forward t).comp (U.backward s)

omit [CompleteSpace E] in
/-- A propagator starts at the identity. -/
@[simp] theorem propagator_self (t : Icc (0 : ℝ) T) : U.propagator t t = ContinuousLinearMap.id ℝ E
  :=
  U.forward_backward t

/-- The forcing pulled back by the inverse homogeneous evolution. -/
def transformedForcing (f : C(Icc (0 : ℝ) T,E)) : ℝ → E :=
  fun s => extendPath T hT U.backward s (extendPath T hT f s)

omit [CompleteSpace E] in
/-- The pulled-back forcing is genuinely continuous. -/
theorem transformedForcing_continuous (f : C(Icc (0 : ℝ) T,E)) :
    Continuous (U.transformedForcing f) :=
  (extendPath_continuous T hT U.backward).clm_apply (extendPath_continuous T hT f)

/-- Duhamel's formula, as an actual interval integral. -/
def solutionReal (f : C(Icc (0 : ℝ) T,E)) (a₀ : E) : ℝ → E :=
  fun t => extendPath T hT U.forward t
    (U.backward ⟨0,le_rfl,hT⟩ a₀ + ∫ s in (0 : ℝ)..t, U.transformedForcing f s)

/-- The constructed forced path is continuous. -/
theorem solutionReal_continuous (f : C(Icc (0 : ℝ) T,E)) (a₀ : E) :
    Continuous (U.solutionReal f a₀) := by
  exact (extendPath_continuous T hT U.forward).clm_apply
    (continuous_const.add (intervalIntegral.differentiable_integral_of_continuous
      (U.transformedForcing_continuous f)).continuous)

/-- The actual continuous forced solution on the time interval. -/
def solution (f : C(Icc (0 : ℝ) T,E)) (a₀ : E) : C(Icc (0 : ℝ) T,E) :=
  ⟨fun t => U.solutionReal f a₀ t, (U.solutionReal_continuous f a₀).comp continuous_subtype_val⟩

/-- Duhamel's formula attains the prescribed initial data. -/
@[simp] theorem solution_initial (f : C(Icc (0 : ℝ) T,E)) (a₀ : E) :
    U.solution f a₀ ⟨0,le_rfl,hT⟩ = a₀ := by
  change extendPath T hT U.forward 0
    (U.backward ⟨0,le_rfl,hT⟩ a₀ + ∫ s in (0 : ℝ)..0, U.transformedForcing f s) = a₀
  simp only [intervalIntegral.integral_same, add_zero, extendPath,
    projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩)]
  exact congrArg (fun A : E →L[ℝ] E => A a₀) (U.forward_backward ⟨0,le_rfl,hT⟩)

/-- The actual constructed path solves the inhomogeneous differential equation. -/
theorem solution_derivative (f : C(Icc (0 : ℝ) T,E)) (a₀ : E) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (U.solutionReal f a₀)
      (B t (U.solution f a₀ t) + f t) (Icc (0 : ℝ) T) t := by
  have hcont := U.transformedForcing_continuous f
  have hi := intervalIntegral.integral_hasDerivAt_right (a := (0 : ℝ))
    (hcont.intervalIntegrable (0 : ℝ) (t : ℝ))
    hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt
  have hv := hi.const_add (U.backward ⟨0,le_rfl,hT⟩ a₀)
  have hd := (U.derivative t).clm_apply hv.hasDerivWithinAt
  convert hd using 1
  · rfl
  change B t (U.solution f a₀ t) + f t =
    B t (U.forward t (U.backward ⟨0,le_rfl,hT⟩ a₀ +
      ∫ s in (0 : ℝ)..(t : ℝ), U.transformedForcing f s)) +
    extendPath T hT U.forward t (U.transformedForcing f t)
  simp only [solution, ContinuousMap.coe_mk, solutionReal, transformedForcing, extendPath,
    projIcc_of_mem hT t.property]
  exact congrArg (fun z => B t (U.forward t (U.backward ⟨0,le_rfl,hT⟩ a₀ +
      ∫ s in (0 : ℝ)..(t : ℝ), extendPath T hT U.backward s (extendPath T hT f s))) + z)
    (congrArg (fun A : E →L[ℝ] E => A (f t)) (U.forward_backward t)).symm

/-- The same solution has the literal two-time Duhamel formula. -/
theorem solution_duhamel (f : C(Icc (0 : ℝ) T,E)) (a₀ : E) (t : Icc (0 : ℝ) T) :
    U.solution f a₀ t = U.propagator t ⟨0,le_rfl,hT⟩ a₀ +
      ∫ s in (0 : ℝ)..(t : ℝ), U.forward t (U.transformedForcing f s) := by
  change extendPath T hT U.forward t
    (U.backward ⟨0,le_rfl,hT⟩ a₀ + ∫ s in (0 : ℝ)..(t : ℝ), U.transformedForcing f s) = _
  rw [show extendPath T hT U.forward t = U.forward t by
    simp only [extendPath, projIcc_of_mem hT t.property], map_add]
  rw [(U.forward t).intervalIntegral_comp_comm
    ((U.transformedForcing_continuous f).intervalIntegrable 0 t)]
  rfl

/-- Any differentiable path with the same forcing and initial data equals the
actual integral construction. No uniqueness assertion is assumed of the data. -/
theorem solution_unique (f : C(Icc (0 : ℝ) T,E)) (a₀ : E) (a : ℝ → E)
    (ha : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt a (B t (a t) + f t) (Icc (0 : ℝ) T) t)
    (h₀ : a 0 = a₀) (t : Icc (0 : ℝ) T) : a t = U.solution f a₀ t := by
  let w : ℝ → E := fun s => a s - U.solutionReal f a₀ s
  let q : ℝ → E := fun s => extendPath T hT U.backward s (w s)
  have hq : ∀ s ∈ Icc (0 : ℝ) T, HasDerivWithinAt q 0 (Icc (0 : ℝ) T) s := by
    intro s hs
    have hd := (U.backward_derivative ⟨s,hs⟩).clm_apply
      ((ha ⟨s,hs⟩).sub (U.solution_derivative f a₀ ⟨s,hs⟩))
    convert hd using 1
    · rfl
    · simp only [neg_apply, comp_apply, extendPath, projIcc_of_mem hT hs,
        Pi.sub_apply, map_sub, map_add, solution, ContinuousMap.coe_mk]
      abel
  have hconst : q t = q 0 := by
    have hbound := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (C := 0) hq
      (fun s hs => by simp) (convex_Icc (0 : ℝ) T)
      (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩) t.property
    simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using hbound
  have hq₀ : q 0 = 0 := by
    change extendPath T hT U.backward 0 (a 0 - U.solution f a₀ ⟨0,le_rfl,hT⟩) = 0
    rw [h₀, U.solution_initial, sub_self, map_zero]
  have hqt : U.backward t (a t - U.solution f a₀ t) = 0 := by
    simpa only [q, w, extendPath, projIcc_of_mem hT t.property, solution, ContinuousMap.coe_mk]
      using hconst.trans hq₀
  have hr := congrArg (U.forward t) hqt
  change ((U.forward t).comp (U.backward t)) (a t - U.solution f a₀ t) = U.forward t 0 at hr
  rw [U.forward_backward, id_apply, map_zero, sub_eq_zero] at hr
  exact hr

/-- A relative homogeneous propagator bound yields the forced bound with the
same profile. No exponential in the coefficient norm is introduced. -/
theorem solution_profile_bound (f : C(Icc (0 : ℝ) T,E)) (a₀ : E)
    (g : Icc (0 : ℝ) T → ℝ) (hg : ∀ t, 0 < g t)
    (hg₀ : g ⟨0,le_rfl,hT⟩ = 1) (C D : ℝ) (hC : 0 ≤ C)
    (hU : ∀ t s : Icc (0 : ℝ) T, s ≤ t → ‖U.propagator t s‖ ≤ C*g t/g s)
    (hf : ∀ s, ‖f s‖ ≤ D*g s) (t : Icc (0 : ℝ) T) :
    ‖U.solution f a₀ t‖ ≤ C*g t*(‖a₀‖ + (t : ℝ)*D) := by
  have hinit : ‖U.propagator t ⟨0,le_rfl,hT⟩ a₀‖ ≤ C*g t*‖a₀‖ := by
    exact (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
      (by simpa only [hg₀, div_one] using hU t ⟨0,le_rfl,hT⟩ t.property.1) (norm_nonneg a₀))
  have hint : ‖∫ s in (0 : ℝ)..(t : ℝ), U.forward t (U.transformedForcing f s)‖ ≤
      C*g t*D*(t : ℝ) := by
    have hpoint : ∀ s ∈ Ι (0 : ℝ) (t : ℝ),
        ‖U.forward t (U.transformedForcing f s)‖ ≤ C*g t*D := by
      intro s hs
      rw [uIoc_of_le t.property.1] at hs
      have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le,hs.2.trans t.property.2⟩
      simp only [transformedForcing, extendPath, projIcc_of_mem hT hsT]
      change ‖U.propagator t ⟨s,hsT⟩ (f ⟨s,hsT⟩)‖ ≤ _
      calc
        _ ≤ ‖U.propagator t ⟨s,hsT⟩‖ * ‖f ⟨s,hsT⟩‖ := le_opNorm _ _
        _ ≤ (C*g t/g ⟨s,hsT⟩)*(D*g ⟨s,hsT⟩) :=
          mul_le_mul (hU t ⟨s,hsT⟩ hs.2) (hf ⟨s,hsT⟩) (norm_nonneg _)
            (div_nonneg (mul_nonneg hC (hg t).le) (hg ⟨s,hsT⟩).le)
        _ = C*g t*D := by field_simp [(hg ⟨s,hsT⟩).ne']
    simpa only [sub_zero, abs_of_nonneg t.property.1] using
      intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  rw [U.solution_duhamel]
  exact (norm_add_le _ _).trans ((add_le_add hinit hint).trans_eq (by ring))

end Evolution

end EulerLinearDuhamel
