/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TimeLpGramGevrey
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevTensorInverse

@[expose] public section

/-!
# The genuine Bochner Gram inverse in fixed Sobolev word blocks

The coefficient family alone pays a fixed Sobolev cost. The actual right
side and solution are measured in the identical ordered-word blocks.
-/

noncomputable section

namespace EulerTimeLpGramSobolev

open Set InnerProductSpace ContinuousLinearMap EulerTimeLp EulerCoerciveProjection
  EulerTimeLpGramInverse EulerTimeLpGramGevrey EulerParameterWordGevrey EulerGevrey
open scoped ContDiff

/-- Polynomial cost of the actual Gram inverse at one fixed Sobolev order. -/
def gramBlockCost (ι : Type*) [Fintype ι] (q : ℕ) (c Rc C D : ℝ) : ℝ :=
  inverseBlockCost ι q c⁻¹ Rc (3*C^2) D

variable {P U E ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Fintype ι]

/-- One actual fixed-Hq inverse application spends one shift at the original
radius, uniformly in the input grade and external derivative order. -/
theorem gramSolution_block_gevrey (directions : ι → P)
    (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (Q : P → C(Icc (0 : ℝ) T, U →L[ℝ] E))
    (c : ℝ) (hc : 0 < c) (hLower : ∀ x t v, c*‖v‖^2 ≤ ‖Q x t v‖^2)
    (hQ : ContDiff ℝ ∞ Q)
    (Rc C : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C)
    (hbQ : ∀ n x, ‖iteratedFDeriv ℝ n Q x‖ ≤ C*majorant Rc 0 n)
    (f : P → TimeLp T U) (hf : ContDiff ℝ ∞ f)
    (D R : ℝ) (hD : 0 ≤ D)
    (hR : 2*gramBlockCost ι q c Rc C D*(sobolevCoefficientRadius ι Rc+1) ≤ R)
    (d : ℕ) (hbf : ∀ n x, block directions q f n x ≤ D*majorant R d n)
    (n : ℕ) (x : P) :
    block directions q (fun y => gramSolver T hT (Q y) c hc (hLower y) (f y)) n x ≤
      majorant R (d+1) n :=
  inverse_block_gevrey_of_tensor directions hd q (fun y => gramOperator T hT (Q y))
    (fun y => gramSolver T hT (Q y) c hc (hLower y) (f y)) f
    (gramOperator_contDiff T hT Q hQ)
    (gramSolution_contDiff T hT Q c hc hLower f hQ hf) hf
    (fun y => operator_inverse_apply _ c hc (gramOperator_coercive T hT (Q y) c (hLower y)) (f y))
    (fun y => gramSolver T hT (Q y) c hc (hLower y))
    (fun y v => inverse_operator_apply _ c hc (gramOperator_coercive T hT (Q y) c (hLower y)) v)
    c⁻¹ Rc (3*C^2) D R hRc (by positivity) hD
    (fun y => gramSolver_norm T hT (Q y) c hc (hLower y))
    (gramOperator_bound T hT Q hQ Rc C hRc hC hbQ) hR d hbf n x

end EulerTimeLpGramSobolev
