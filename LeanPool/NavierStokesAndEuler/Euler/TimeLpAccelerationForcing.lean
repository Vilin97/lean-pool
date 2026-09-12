/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.Gevrey
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpMultiplier
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.L2Space
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
import LeanPool.NavierStokesAndEuler.Euler.TimeLpCoefficientGevrey
import LeanPool.NavierStokesAndEuler.Euler.TransverseGramInverse
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The actual forcing in the projected acceleration equation

Both the mean and transverse strong equations use `Q* (f - 2 Q₁ v)`.
This module gives its genuine parameter regularity and factorial estimate,
with the explicit amplitude needed by the actual Gram inverse.
-/

@[expose] public section


noncomputable section

open scoped ContDiff

namespace EulerTimeLpAccelerationForcing

open Set ContinuousLinearMap EulerTimeLp EulerVolterraConvolution
  EulerTransverseGramInverse EulerTimeLpCoefficientMap EulerTimeLpCoefficientGevrey
  EulerOperatorGevreyCalculus EulerGevrey

variable {P U E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The literal right side of the projected strong acceleration equation. -/
def forcing (T : ℝ) (hT : 0 ≤ T)
    (Q Q₁ : P → C(Icc (0 : ℝ) T, U →L[ℝ] E))
    (f : P → TimeLp T E) (v : P → TimeLp T U) (x : P) : TimeLp T U :=
  (timeMultiplier T hT (Q x)).adjoint
    (f x - (2 : ℝ) • timeMultiplier T hT (Q₁ x) (v x))

/-- The actual strong forcing is smoothly parameterized whenever its inputs are. -/
theorem forcing_contDiff (T : ℝ) (hT : 0 ≤ T)
    (Q Q₁ : P → C(Icc (0 : ℝ) T, U →L[ℝ] E))
    (f : P → TimeLp T E) (v : P → TimeLp T U) {n : ℕ∞ω}
    (hQ : ContDiff ℝ n Q) (hQ₁ : ContDiff ℝ n Q₁)
    (hf : ContDiff ℝ n f) (hv : ContDiff ℝ n v) :
    ContDiff ℝ n (forcing T hT Q Q₁ f v) :=
  ((realAdjoint (U := TimeLp T U) (E := TimeLp T E)).contDiff.comp
    (contDiff_timeMultiplier T hT Q hQ)).clm_apply
    (hf.sub (((contDiff_timeMultiplier T hT Q₁ hQ₁).clm_apply hv).const_smul (2 : ℝ)))

/-- One fixed polynomial amplitude controls all genuine forcing derivatives. -/
theorem forcing_bound (T : ℝ) (hT : 0 ≤ T)
    (Q Q₁ : P → C(Icc (0 : ℝ) T, U →L[ℝ] E))
    (f : P → TimeLp T E) (v : P → TimeLp T U)
    (hQ : ContDiff ℝ ∞ Q) (hQ₁ : ContDiff ℝ ∞ Q₁)
    (hf : ContDiff ℝ ∞ f) (hv : ContDiff ℝ ∞ v)
    (R C₀ C₁ F V : ℝ) (hR : 0 ≤ R) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hF : 0 ≤ F) (hV : 0 ≤ V) (d : ℕ)
    (hbQ : ∀ n x, ‖iteratedFDeriv ℝ n Q x‖ ≤ C₀ * majorant R 0 n)
    (hbQ₁ : ∀ n x, ‖iteratedFDeriv ℝ n Q₁ x‖ ≤ C₁ * majorant R 0 n)
    (hbf : ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ F * majorant R d n)
    (hbv : ∀ n x, ‖iteratedFDeriv ℝ n v x‖ ≤ V * majorant R d n)
    (n : ℕ) (x : P) :
    ‖iteratedFDeriv ℝ n (forcing T hT Q Q₁ f v) x‖ ≤
      (3*C₀*(F+6*C₁*V))*majorant R d n := by
  let w := fun y => timeMultiplier T hT (Q₁ y) (v y)
  have hw : ContDiff ℝ ∞ w := (contDiff_timeMultiplier T hT Q₁ hQ₁).clm_apply hv
  have hbw (j : ℕ) (y : P) : ‖iteratedFDeriv ℝ j w y‖ ≤ (3*C₁*V)*majorant R d j := by
    simpa only [Nat.zero_add] using clm_apply_bound
      (fun z => timeMultiplier T hT (Q₁ z)) v (contDiff_timeMultiplier T hT Q₁ hQ₁) hv
      R C₁ V hR hC₁ hV 0 d (timeMultiplier_bound T hT Q₁ hQ₁ R C₁ hR hC₁ 0 hbQ₁) hbv j y
  have hb2w (j : ℕ) (y : P) :
      ‖iteratedFDeriv ℝ j (fun z => (2 : ℝ) • w z) y‖ ≤ (6*C₁*V)*majorant R d j := by
    rw [iteratedFDeriv_const_smul_apply' (hw.contDiffAt.of_le (by simp)), norm_smul]
    norm_num only [Real.norm_ofNat]
    nlinarith [hbw j y]
  let r := fun y => f y - (2 : ℝ) • w y
  have hr : ContDiff ℝ ∞ r := hf.sub (hw.const_smul (2 : ℝ))
  have hbr := sub_bound f (fun y => (2 : ℝ) • w y) hf (hw.const_smul (2 : ℝ))
    R F (6*C₁*V) d hbf hb2w
  have hAdj : ContDiff ℝ ∞ (fun y => (timeMultiplier T hT (Q y)).adjoint) :=
    (realAdjoint (U := TimeLp T U) (E := TimeLp T E)).contDiff.comp (contDiff_timeMultiplier T hT Q
        hQ)
  have h := clm_apply_bound
    (fun y => (timeMultiplier T hT (Q y)).adjoint) r hAdj hr R C₀ (F+6*C₁*V)
    hR hC₀ (by positivity) 0 d
    (adjoint_bound (fun y => timeMultiplier T hT (Q y)) (contDiff_timeMultiplier T hT Q hQ)
      R C₀ hR hC₀ 0 (timeMultiplier_bound T hT Q hQ R C₀ hR hC₀ 0 hbQ)) hbr n x
  simp only [Nat.zero_add] at h
  convert h using 1
  rfl

end EulerTimeLpAccelerationForcing
