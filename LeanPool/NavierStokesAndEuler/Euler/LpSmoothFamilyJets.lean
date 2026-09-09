/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpSmoothFamily
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Tactic.NormNum.GCD

/-! All-order L² parameter regularity with the original square-integrable derivative bounds. -/

@[expose] public section


noncomputable section


namespace EulerLpSmoothFamily.SmoothFamily

open MeasureTheory Filter EulerLpDerivative
open scoped ContDiff Topology

universe u w

variable {X : Type u} [MeasurableSpace X] {μ : Measure X} {P : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P] {V : Type w}
  [NormedAddCommGroup V] [NormedSpace ℝ V]

private theorem contDiff_value_nat_aux (n : ℕ) :
    ∀ (V : Type w) [NormedAddCommGroup V] [NormedSpace ℝ V] (A : SmoothFamily μ P V),
      ContDiff ℝ n A.value := by
  induction n with
  | zero =>
    intro V _ _ A
    exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr
      (fun a => (A.hasFDerivAt_value a).continuousAt))
  | succ n ih =>
    intro V _ _ A
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv]
    refine ⟨fun a => (A.hasFDerivAt_value a).differentiableAt, by simp, ?_⟩
    rw [A.fderiv_value]
    exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := (n : WithTop ℕ∞))
      (E := Lp (P →L[ℝ] V) 2 μ) (F := P →L[ℝ] Lp V 2 μ)
      (derivativeBundling μ)).comp (ih (P →L[ℝ] V) A.derivative)

/-- Genuine smoothness in the full L² norm, not merely pointwise in the measured variable. -/
theorem contDiff_value (A : SmoothFamily μ P V) : ContDiff ℝ ∞ A.value :=
  contDiff_infty.mpr (fun n => contDiff_value_nat_aux n V A)

theorem norm_value_le (A : SmoothFamily μ P V) (a : P) : ‖A.value a‖ ≤ ‖A.bound 0‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [A.value_ae a, A.bounded 0] with x hx hb
  rw [hx]
  have hh : ‖A.field a x‖ ≤ A.bound 0 x := by simpa only [norm_iteratedFDeriv_zero] using hb a
  exact hh.trans (le_abs_self (A.bound 0 x))

private theorem norm_iteratedFDeriv_value_aux (n : ℕ) :
    ∀ (V : Type w) [NormedAddCommGroup V] [NormedSpace ℝ V] (A : SmoothFamily μ P V) (a : P),
      ‖iteratedFDeriv ℝ n A.value a‖ ≤ ‖A.bound n‖ := by
  induction n with
  | zero =>
    intro V _ _ A a
    rw [norm_iteratedFDeriv_zero]
    exact A.norm_value_le a
  | succ n ih =>
    intro V _ _ A a
    rw [← norm_iteratedFDeriv_fderiv, A.fderiv_value]
    have h := ContinuousLinearMap.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (E := P)
      (F := Lp (P →L[ℝ] V) 2 μ) (G := P →L[ℝ] Lp V 2 μ)
      (derivativeBundling μ) (A.derivative.contDiff_value.contDiffAt (x := a)) (n := n) (by simp)
    have hi := ih (P →L[ℝ] V) A.derivative a
    rw [show A.derivative.bound n = A.bound (n+1) from rfl] at hi
    exact h.trans ((mul_le_mul_of_nonneg_right
      (derivativeBundling_norm_le_one (P := P) (V := V) μ) (norm_nonneg _)).trans
      (by simpa only [one_mul] using hi))

/-- Each true L² derivative inherits its original fiberwise L² majorant with constant one. -/
theorem norm_iteratedFDeriv_value_le (A : SmoothFamily μ P V) (n : ℕ) (a : P) :
    ‖iteratedFDeriv ℝ n A.value a‖ ≤ ‖A.bound n‖ := norm_iteratedFDeriv_value_aux n V A a

end EulerLpSmoothFamily.SmoothFamily
