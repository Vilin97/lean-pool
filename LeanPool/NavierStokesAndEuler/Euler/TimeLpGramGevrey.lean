/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TimeLpGramInverse
import LeanPool.NavierStokesAndEuler.Euler.HilbertCoerciveGevrey
import LeanPool.NavierStokesAndEuler.Euler.HilbertCoerciveParameter
import Mathlib.Algebra.Order.Star.Real

/-!
# Uniform factorial estimates for the actual time Gram inverse

The lower frame bound and actual coefficient derivatives give the estimates
for the inverse appearing in the strong acceleration equation. No derivative
bounds on a pre-existing inverse are assumed.
-/

@[expose] public section


noncomputable section

open scoped ContDiff

namespace EulerTimeLpGramGevrey

open Set InnerProductSpace ContinuousLinearMap EulerTimeLp EulerVolterraConvolution
  EulerTimeLpGramInverse EulerHilbertCoerciveGevrey EulerHilbertCoerciveParameter
  EulerTransverseGramPath EulerGevrey

/-- A polynomial top constant for coefficient amplitude `3 C²` and forcing amplitude `D`. -/
def gramCost (c C D : ℝ) : ℝ := 1 + c⁻¹ * (3*C^2+D+1)

variable {P U E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The Gram solve is the actual smoothly parameterized coercive solution. -/
theorem gramSolution_contDiff (T : ℝ) (hT : 0 ≤ T)
    (Q : P → C(Icc (0 : ℝ) T, U →L[ℝ] E))
    (c : ℝ) (hc : 0 < c) (hLower : ∀ x t v, c * ‖v‖ ^ 2 ≤ ‖Q x t v‖ ^ 2)
    (f : P → TimeLp T U) {n : ℕ∞ω} (hQ : ContDiff ℝ n Q) (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun x => gramSolver T hT (Q x) c hc (hLower x) (f x)) :=
  contDiff_coerciveSolution_variable (fun x => gramOperator T hT (Q x)) (fun _ => c)
    (fun _ => hc) (fun x => gramOperator_coercive T hT (Q x) c (hLower x)) f
    (gramOperator_contDiff T hT Q hQ) hf

/-- One factorial shift for the genuine Gram inverse, with an explicit polynomial radius condition.
-/
theorem gramSolution_gevrey (T : ℝ) (hT : 0 ≤ T)
    (Q : P → C(Icc (0 : ℝ) T, U →L[ℝ] E))
    (c : ℝ) (hc : 0 < c) (hLower : ∀ x t v, c * ‖v‖ ^ 2 ≤ ‖Q x t v‖ ^ 2)
    (hQ : ContDiff ℝ ∞ Q)
    (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C)
    (hbQ : ∀ n x, ‖iteratedFDeriv ℝ n Q x‖ ≤ C * majorant Rc 0 n)
    (f : P → TimeLp T U) (hf : ContDiff ℝ ∞ f)
    (D R : ℝ) (hD : 0 ≤ D) (hR : 2 * gramCost c C D * (Rc + 1) ≤ R)
    (d : ℕ) (hbf : ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ D * majorant R d n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (fun y => gramSolver T hT (Q y) c hc (hLower y) (f y)) x‖ ≤
      majorant R (d+1) n := by
  have hci : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  have hM : 1 ≤ gramCost c C D := by
    unfold gramCost
    have : 0 ≤ c⁻¹*(3*C^2+D+1) := by positivity
    linarith
  have hMC : c⁻¹*(3*C^2) ≤ gramCost c C D := by
    unfold gramCost
    nlinarith
  have hMD : c⁻¹*D ≤ gramCost c C D := by
    unfold gramCost
    nlinarith [sq_nonneg C]
  have hb (j : ℕ) (y : P) :
      ‖iteratedFDeriv ℝ (j+1) (fun z => gramOperator T hT (Q z)) y‖ ≤
        (3*C^2)*(Rc^(j+1)*((j+1).factorial : ℝ)^2) := by
    simpa only [majorant, Nat.add_zero] using gramOperator_bound T hT Q hQ Rc C hRc hC hbQ (j+1) y
  exact coerciveSolution_gevrey_amplitudes (fun y => gramOperator T hT (Q y)) (fun _ => c)
    (fun _ => hc) (fun y => gramOperator_coercive T hT (Q y) c (hLower y)) f
    (gramOperator_contDiff T hT Q hQ) hf c⁻¹ (3*C^2) D (gramCost c C D) Rc R
    (by positivity) hD hM hMC hMD hRc hR (fun _ => le_rfl) hb d hbf n x

/-- The same estimate applies to the explicit inverse-Gram multiplier in the strong equation. -/
theorem inverseGramMultiplier_gevrey (T : ℝ) (hT : 0 ≤ T)
    (Q : P → C(Icc (0 : ℝ) T, U →L[ℝ] E))
    (c : ℝ) (hc : 0 < c) (hLower : ∀ x t v, c * ‖v‖ ^ 2 ≤ ‖Q x t v‖ ^ 2)
    (hQ : ContDiff ℝ ∞ Q)
    (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C)
    (hbQ : ∀ n x, ‖iteratedFDeriv ℝ n Q x‖ ≤ C * majorant Rc 0 n)
    (f : P → TimeLp T U) (hf : ContDiff ℝ ∞ f)
    (D R : ℝ) (hD : 0 ≤ D) (hR : 2 * gramCost c C D * (Rc + 1) ≤ R)
    (d : ℕ) (hbf : ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ D * majorant R d n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n
      (fun y => timeMultiplier T hT (gramInversePath T (Q y) c hc (hLower y)) (f y)) x‖ ≤
      majorant R (d+1) n := by
  have heq : (fun y => timeMultiplier T hT (gramInversePath T (Q y) c hc (hLower y)) (f y)) =
      fun y => gramSolver T hT (Q y) c hc (hLower y) (f y) := by
    funext y
    rw [gramSolver_eq_multiplier]
  rw [heq]
  exact gramSolution_gevrey T hT Q c hc hLower hQ Rc C hRc hC hbQ f hf D R hD hR d hbf n x

end EulerTimeLpGramGevrey
