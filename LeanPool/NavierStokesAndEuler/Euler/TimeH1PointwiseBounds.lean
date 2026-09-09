/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TerminalTimePrimitive

@[expose] public section

/-!
# Quantitative pointwise bounds for genuine time-H¹ representatives

Absolute continuity and the actual Bochner L² derivative give exact integral
increments, square-root continuity, and initial/terminal trace bounds.
-/

noncomputable section

namespace EulerTimeH1PointwiseBounds

open MeasureTheory Set EulerTimeLp EulerTerminalTimePrimitive

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

variable (T : ℝ) (hT : 0 ≤ T) (g : TimeLp T E) (η : ℝ → E)
  (hη : AbsolutelyContinuousOnInterval η 0 T)
  (hder : ∀ᵐ t ∂timeMeasure T, HasDerivAt η (g t) t)

include hT hη hder in
/-- The terminal primitive plus the actual terminal value reconstructs any H¹ representative. -/
theorem eq_primitive_add_terminal (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    η t = realPrimitive T g t + η T := by
  have hsub : AbsolutelyContinuousOnInterval (fun r => η r-η T) 0 T :=
    hη.sub ((LipschitzWith.const (η T)).lipschitzOnWith.absolutelyContinuousOnInterval)
  have hdsub : ∀ᵐ r ∂timeMeasure T, HasDerivAt (fun s => η s-η T) (g r) r := by
    filter_upwards [hder] with r hr
    exact hr.sub_const (η T)
  have h := eq_realPrimitive_of_ac_hasDerivAt_ae T hT g (fun r => η r-η T)
    hsub hdsub (sub_self _) t ht
  exact sub_eq_iff_eq_add.mp h

include hT hη hder in
/-- The increment is the actual integral of the L² derivative's zero extension. -/
theorem increment_eq_integral (s t : ℝ) (hs : s ∈ Icc (0 : ℝ) T) (ht : t ∈ Icc (0 : ℝ) T) :
    η t-η s = ∫ r in s..t, zeroExtension T g r := by
  calc
    η t-η s = (realPrimitive T g t+η T)-(realPrimitive T g s+η T) :=
      congrArg₂ (fun x y : E => x-y)
        (eq_primitive_add_terminal T hT g η hη hder t ht)
        (eq_primitive_add_terminal T hT g η hη hder s hs)
    _ = realPrimitive T g t-realPrimitive T g s := by abel
    _ = ∫ r in s..t, zeroExtension T g r := realPrimitive_increment T g s t

include hT hη hder in
/-- The exact square-root modulus follows from Bochner Cauchy--Schwarz. -/
theorem increment_norm_sq_le (s t : ℝ) (hs : s ∈ Icc (0 : ℝ) T)
    (ht : t ∈ Icc (0 : ℝ) T) (hst : s ≤ t) :
    ‖η t-η s‖^2 ≤ (t-s)*‖g‖^2 := by
  have hlocal := norm_integral_sq_le_length_mul (zeroExtension T g) hst
    (zeroExtension_integrable T g).intervalIntegrable
    (zeroExtension_norm_sq_integrable T g).intervalIntegrable
  have hmono : (∫ r in s..t, ‖zeroExtension T g r‖^2) ≤ ‖g‖^2 := by
    rw [intervalIntegral.integral_of_le hst]
    exact (setIntegral_le_integral (zeroExtension_norm_sq_integrable T g)
      (Filter.Eventually.of_forall (fun r => sq_nonneg ‖zeroExtension T g r‖))).trans_eq
      (zeroExtension_norm_sq_integral T g)
  calc
    ‖η t-η s‖^2 = ‖∫ r in s..t, zeroExtension T g r‖^2 :=
      congrArg (fun x : E => ‖x‖^2) (increment_eq_integral T hT g η hη hder s t hs ht)
    _ ≤ (t-s)*(∫ r in s..t, ‖zeroExtension T g r‖^2) := hlocal
    _ ≤ (t-s)*‖g‖^2 := mul_le_mul_of_nonneg_left hmono (sub_nonneg.mpr hst)

include hT hη hder in
/-- A genuine H¹ path has the quantitative square-root continuity bound. -/
theorem increment_norm_le (s t : ℝ) (hs : s ∈ Icc (0 : ℝ) T)
    (ht : t ∈ Icc (0 : ℝ) T) (hst : s ≤ t) :
    ‖η t-η s‖ ≤ Real.sqrt (t-s)*‖g‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).1
  rw [mul_pow, Real.sq_sqrt (sub_nonneg.mpr hst)]
  exact increment_norm_sq_le T hT g η hη hder s t hs ht hst

include hT hη hder in
/-- The actual initial trace and L² derivative control the whole time path. -/
theorem norm_le_initial_add (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    ‖η t‖ ≤ ‖η 0‖+Real.sqrt t*‖g‖ := by
  have hi := increment_norm_le T hT g η hη hder 0 t ⟨le_rfl, hT⟩ ht ht.1
  simp only [sub_zero] at hi
  calc
    ‖η t‖ = ‖(η t-η 0)+η 0‖ := congrArg norm (sub_add_cancel (η t) (η 0)).symm
    _ ≤ ‖η t-η 0‖+‖η 0‖ := norm_add_le _ _
    _ ≤ Real.sqrt t*‖g‖+‖η 0‖ := add_le_add hi le_rfl
    _ = ‖η 0‖+Real.sqrt t*‖g‖ := add_comm _ _

include hT hη hder in
/-- The uniform-in-time version needed by fixed-index inverse estimates. -/
theorem norm_le_initial_add_uniform (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    ‖η t‖ ≤ ‖η 0‖+Real.sqrt T*‖g‖ :=
  (norm_le_initial_add T hT g η hη hder t ht).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ht.2) (norm_nonneg g)))

include hT hη hder in
/-- The actual terminal trace has the corresponding backward-in-time bound. -/
theorem norm_le_terminal_add (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    ‖η t‖ ≤ ‖η T‖+Real.sqrt (T-t)*‖g‖ := by
  have he := eq_primitive_add_terminal T hT g η hη hder t ht
  calc
    ‖η t‖ = ‖realPrimitive T g t+η T‖ := congrArg norm he
    _ ≤ ‖realPrimitive T g t‖+‖η T‖ := norm_add_le _ _
    _ ≤ Real.sqrt (T-t)*‖g‖+‖η T‖ := add_le_add (realPrimitive_norm_le T g t ht) le_rfl
    _ = ‖η T‖+Real.sqrt (T-t)*‖g‖ := add_comm _ _

end EulerTimeH1PointwiseBounds
