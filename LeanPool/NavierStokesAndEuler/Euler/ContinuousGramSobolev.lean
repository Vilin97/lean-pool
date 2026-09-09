/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ContinuousGramGevrey
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpGramSobolev

@[expose] public section

/-! The actual uniform-time Gram inverse in fixed Sobolev word blocks. -/

noncomputable section

namespace EulerContinuousGramSobolev

open Set ContinuousLinearMap EulerContinuousTimeIntegral EulerContinuousPathCalculus
  EulerContinuousPathComposition EulerTransverseGramPath EulerContinuousGramPath
    EulerTimeLpGramSobolev
  EulerParameterWordGevrey EulerGevrey
open scoped ContDiff

variable {P U E ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Fintype ι]

/-- The continuous Gram solve is bounded in the same fixed Sobolev order and
external radius as its input, with one factorial shift and a fixed cost. -/
theorem solution_block_gevrey (directions : ι → P)
    (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ) (T : ℝ)
    (Q : P → C(Icc (0 : ℝ) T,U →L[ℝ] E))
    (c : ℝ) (hc : 0 < c) (hLower : ∀ x t v, c*‖v‖^2 ≤ ‖Q x t v‖^2)
    (hQ : ContDiff ℝ ∞ Q)
    (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C)
    (hbQ : ∀ n x, ‖iteratedFDeriv ℝ n Q x‖ ≤ C*majorant Rc 0 n)
    (f : P → C(Icc (0 : ℝ) T,U)) (hf : ContDiff ℝ ∞ f)
    (D R : ℝ) (hD : 0 ≤ D)
    (hR : 2*gramBlockCost ι q c Rc C D*(sobolevCoefficientRadius ι Rc+1) ≤ R)
    (d : ℕ) (hbf : ∀ n x, block directions q f n x ≤ D*majorant R d n)
    (n : ℕ) (x : P) :
    block directions q (fun y => solve T (Q y) c hc (hLower y) (f y)) n x ≤
      majorant R (d+1) n := by
  let A := fun y => multiplier (gramPath T (Q y))
  let V := fun y => solve T (Q y) c hc (hLower y) (f y)
  let I := fun y => solve T (Q y) c hc (hLower y)
  have hB := gramPath_contDiff T Q hQ
  have hA : ContDiff ℝ ∞ A := contDiff_multiplier (fun y => gramPath T (Q y)) hB
  have hV : ContDiff ℝ ∞ V := solve_contDiff T c hc Q hLower f hQ hf
  have hAall := multiplier_bound (fun y => gramPath T (Q y)) hB Rc (3*C^2) hRc
    (by positivity) 0 (gramPath_bound T Q hQ Rc C hRc hC hbQ)
  exact inverse_block_gevrey_of_tensor directions hd q A V f hA hV hf
    (fun y => solve_equation T (Q y) c hc (hLower y) (f y)) I
    (fun y => solve_left_inverse T (Q y) c hc (hLower y))
    c⁻¹ Rc (3*C^2) D R hRc (by positivity) hD
    (fun y => solve_norm T (Q y) c hc (hLower y)) hAall hR d hbf n x

end EulerContinuousGramSobolev
