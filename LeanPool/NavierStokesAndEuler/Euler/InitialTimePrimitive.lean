/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TerminalTimePrimitive

@[expose] public section

/-!
The initial-zero primitive of an actual Bochner L² time field.  In contrast to
the terminal-zero primitive, this applies to the nonzero-terminal paths used
in the activation argument.  The factor `T²/2` is proved from integration.
-/

noncomputable section

namespace EulerInitialTimePrimitive

open MeasureTheory Set EulerTimeLp EulerTerminalTimePrimitive

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual real-time primitive, normalized at the initial endpoint. -/
def initialRealPrimitive (T : ℝ) (u : TimeLp T E) (t : ℝ) : E :=
  realPrimitive T u t - realPrimitive T u 0

theorem initialRealPrimitive_eq_integral (T : ℝ) (u : TimeLp T E) (t : ℝ) :
    initialRealPrimitive T u t = ∫ s in 0..t, zeroExtension T u s :=
  realPrimitive_increment T u 0 t

@[simp] theorem initialRealPrimitive_initial (T : ℝ) (u : TimeLp T E) :
    initialRealPrimitive T u 0 = 0 := sub_self _

theorem initialRealPrimitive_continuous (T : ℝ) (u : TimeLp T E) :
    Continuous (initialRealPrimitive T u) :=
  (realPrimitive_continuous T u).sub continuous_const

theorem initialRealPrimitive_absolutelyContinuous (T : ℝ) (u : TimeLp T E) :
    AbsolutelyContinuousOnInterval (initialRealPrimitive T u) 0 T :=
  (realPrimitive_absolutelyContinuous T u).sub
    ((LipschitzWith.const (realPrimitive T u 0)).lipschitzOnWith.absolutelyContinuousOnInterval)

theorem initialRealPrimitive_hasDerivAt_ae [CompleteSpace E] (T : ℝ)
    (u : TimeLp T E) :
    ∀ᵐ t ∂timeMeasure T, HasDerivAt (initialRealPrimitive T u) (u t) t := by
  filter_upwards [realPrimitive_hasDerivAt_ae T u] with t ht
  exact ht.sub_const _

/-- The sharp pointwise initial trace estimate. -/
theorem initialRealPrimitive_norm_sq_le (T : ℝ) (u : TimeLp T E) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) T) :
    ‖initialRealPrimitive T u t‖ ^ 2 ≤ t * ‖u‖ ^ 2 := by
  have hlocal := norm_integral_sq_le_length_mul (zeroExtension T u) ht.1
    (zeroExtension_integrable T u).intervalIntegrable
    (zeroExtension_norm_sq_integrable T u).intervalIntegrable
  have hmono : (∫ s in 0..t, ‖zeroExtension T u s‖ ^ 2) ≤ ‖u‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le ht.1]
    exact (setIntegral_le_integral (zeroExtension_norm_sq_integrable T u)
      (Filter.Eventually.of_forall (fun s => sq_nonneg ‖zeroExtension T u s‖))).trans_eq
      (zeroExtension_norm_sq_integral T u)
  rw [initialRealPrimitive_eq_integral]
  simpa only [sub_zero] using hlocal.trans
    (mul_le_mul_of_nonneg_left hmono (by simpa only [sub_zero] using ht.1))

theorem initialRealPrimitive_norm_le (T : ℝ) (u : TimeLp T E) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) T) :
    ‖initialRealPrimitive T u t‖ ≤ Real.sqrt t * ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).1
  rw [mul_pow, Real.sq_sqrt ht.1]
  exact initialRealPrimitive_norm_sq_le T u t ht

def initialPath (T : ℝ) (u : TimeLp T E) : C(Icc (0 : ℝ) T, E) :=
  ⟨fun t => initialRealPrimitive T u t,
    (initialRealPrimitive_continuous T u).comp continuous_subtype_val⟩

theorem initialPath_add (T : ℝ) (hT : 0 ≤ T) (u v : TimeLp T E) :
    initialPath T (u + v) = initialPath T u + initialPath T v := by
  ext t
  change primitivePath T (u + v) t - primitivePath T (u + v) ⟨0, le_rfl, hT⟩ =
    (primitivePath T u t - primitivePath T u ⟨0, le_rfl, hT⟩) +
      (primitivePath T v t - primitivePath T v ⟨0, le_rfl, hT⟩)
  rw [primitivePath_add]
  simp only [ContinuousMap.add_apply]
  abel

theorem initialPath_smul (T : ℝ) (hT : 0 ≤ T) (a : ℝ) (u : TimeLp T E) :
    initialPath T (a • u) = a • initialPath T u := by
  ext t
  change primitivePath T (a • u) t - primitivePath T (a • u) ⟨0, le_rfl, hT⟩ =
    a • (primitivePath T u t - primitivePath T u ⟨0, le_rfl, hT⟩)
  rw [primitivePath_smul]
  simp only [ContinuousMap.smul_apply, smul_sub]

theorem initialPath_norm_le (T : ℝ) (_hT : 0 ≤ T) (u : TimeLp T E) :
    ‖initialPath T u‖ ≤ Real.sqrt T * ‖u‖ := by
  apply (ContinuousMap.norm_le _
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).2
  intro t
  exact (initialRealPrimitive_norm_le T u t t.property).trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt t.property.2) (norm_nonneg _))

/-- Bounded initial integration of genuine L² data. -/
def initialPrimitive (T : ℝ) (hT : 0 ≤ T) :
    TimeLp T E →L[ℝ] C(Icc (0 : ℝ) T, E) :=
  ({ toFun := initialPath T
     map_add' := initialPath_add T hT
     map_smul' := fun a u => by
       simpa only [RingHom.id_apply] using initialPath_smul T hT a u } :
      TimeLp T E →ₗ[ℝ] C(Icc (0 : ℝ) T, E)).mkContinuous
    (Real.sqrt T) (initialPath_norm_le T hT)

@[simp] theorem initialPrimitive_apply (T : ℝ) (hT : 0 ≤ T) (u : TimeLp T E)
    (t : Icc (0 : ℝ) T) :
    initialPrimitive T hT u t = initialRealPrimitive T u t := rfl

@[simp] theorem initialPrimitive_initial (T : ℝ) (hT : 0 ≤ T) (u : TimeLp T E) :
    initialPrimitive T hT u ⟨0, le_rfl, hT⟩ = 0 :=
  initialRealPrimitive_initial T u

theorem initialPrimitive_eq_terminal_sub (T : ℝ) (hT : 0 ≤ T) (u : TimeLp T E)
    (t : Icc (0 : ℝ) T) :
    initialPrimitive T hT u t = terminalPrimitive T hT u t - initialTrace T hT u := rfl

def initialPrimitiveTimeLp (T : ℝ) (hT : 0 ≤ T) : TimeLp T E →L[ℝ] TimeLp T E :=
  (pathLpOperator T hT).comp (initialPrimitive T hT)

theorem initialPrimitiveTimeLp_ae (T : ℝ) (hT : 0 ≤ T) (u : TimeLp T E) :
    (initialPrimitiveTimeLp T hT u : ℝ → E) =ᵐ[timeMeasure T]
      initialRealPrimitive T u := by
  change (pathLp T hT (initialPrimitive T hT u) : ℝ → E) =ᵐ[timeMeasure T] _
  filter_upwards [pathLp_ae T hT (initialPrimitive T hT u),
    ae_restrict_mem measurableSet_Icc] with t ht hmem
  rw [ht]
  change initialRealPrimitive T u (projIcc 0 T hT t) = initialRealPrimitive T u t
  rw [projIcc_of_mem hT hmem]

/-- The sharp initial-zero Poincaré estimate is independent of the terminal value. -/
theorem initialPrimitive_poincare (T : ℝ) (hT : 0 ≤ T) (u : TimeLp T E) :
    (∫ t in 0..T, ‖initialRealPrimitive T u t‖ ^ 2) ≤ T ^ 2 / 2 * ‖u‖ ^ 2 := by
  have hi := intervalIntegral.integral_mono_on (μ := volume) hT
    (((initialRealPrimitive_continuous T u).norm.pow 2).intervalIntegrable 0 T)
    ((continuous_id.mul continuous_const).intervalIntegrable (a := 0) (b := T))
    (fun t ht => initialRealPrimitive_norm_sq_le T u t ht)
  have he : (∫ t in 0..T, t * ‖u‖ ^ 2) = T ^ 2 / 2 * ‖u‖ ^ 2 := by
    rw [intervalIntegral.integral_mul_const, integral_id]
    norm_num
  exact hi.trans_eq he

theorem initialPrimitiveTimeLp_norm_sq_le (T : ℝ) (hT : 0 ≤ T) (u : TimeLp T E) :
    ‖initialPrimitiveTimeLp T hT u‖ ^ 2 ≤ T ^ 2 / 2 * ‖u‖ ^ 2 := by
  rw [norm_sq_eq_integral]
  have he : (∫ t, ‖(initialPrimitiveTimeLp T hT u : ℝ → E) t‖ ^ 2 ∂timeMeasure T) =
      ∫ t in 0..T, ‖initialRealPrimitive T u t‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc]
    exact integral_congr_ae ((initialPrimitiveTimeLp_ae T hT u).mono
      (fun _ h => congrArg (fun v : E => ‖v‖ ^ 2) h))
  rw [he]
  exact initialPrimitive_poincare T hT u

end EulerInitialTimePrimitive
