/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TimeLpAccelerationForcing
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpGramSobolev
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevAcceleration
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
import LeanPool.NavierStokesAndEuler.Euler.TimeLpCoefficientGevrey
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! Actual projected acceleration in the same fixed Sobolev word blocks. -/

@[expose] public section


noncomputable section

namespace EulerTimeLpAccelerationSobolev

open Set ContinuousLinearMap EulerTimeLp EulerTimeLpAccelerationForcing
  EulerTimeLpGramInverse EulerTimeLpGramSobolev EulerVolterraConvolution
  EulerTransverseGramInverse EulerTimeLpCoefficientMap EulerTimeLpCoefficientGevrey
  EulerOperatorGevreyCalculus EulerParameterWordGevrey EulerGevrey
open scoped ContDiff

variable {P U E ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Fintype ι]

/-- The actual acceleration forcing retains the forcing/velocity grade and radius. -/
theorem forcing_block_bound (directions : ι → P) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
    (T : ℝ) (hT : 0 ≤ T) (Q Q₁ : P → C(Icc (0 : ℝ) T, U →L[ℝ] E))
    (f : P → TimeLp T E) (v : P → TimeLp T U)
    (hQ : ContDiff ℝ ∞ Q) (hQ₁ : ContDiff ℝ ∞ Q₁)
    (hf : ContDiff ℝ ∞ f) (hv : ContDiff ℝ ∞ v)
    (Rc R C₀ C₁ Cf Cv : ℝ) (hRc : 0 ≤ Rc) (hRcR : sobolevCoefficientRadius ι Rc ≤ R)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hCf : 0 ≤ Cf) (hCv : 0 ≤ Cv)
    (hbQ : ∀ n x, ‖iteratedFDeriv ℝ n Q x‖ ≤ C₀ * majorant Rc 0 n)
    (hbQ₁ : ∀ n x, ‖iteratedFDeriv ℝ n Q₁ x‖ ≤ C₁ * majorant Rc 0 n)
    (d : ℕ)
    (hbf : ∀ n x, block directions q f n x ≤ Cf * majorant R d n)
    (hbv : ∀ n x, block directions q v n x ≤ Cv * majorant R d n)
    (n : ℕ) (x : P) :
    block directions q (forcing T hT Q Q₁ f v) n x ≤
      accelerationBlockAmplitude ι q Rc C₀ C₁ Cf Cv*majorant R d n :=
  block_acceleration_forcing_of_tensor directions hd q
    (fun y => (timeMultiplier T hT (Q y)).adjoint)
    (fun y => timeMultiplier T hT (Q₁ y)) f v
    ((realAdjoint (U := TimeLp T U) (E := TimeLp T E)).contDiff.comp
      (contDiff_timeMultiplier T hT Q hQ))
    (contDiff_timeMultiplier T hT Q₁ hQ₁) hf hv Rc R C₀ C₁ Cf Cv hRc hRcR hC₀ hC₁ hCf hCv
    (adjoint_bound (fun y => timeMultiplier T hT (Q y)) (contDiff_timeMultiplier T hT Q hQ)
      Rc C₀ hRc hC₀ 0 (timeMultiplier_bound T hT Q hQ Rc C₀ hRc hC₀ 0 hbQ))
    (timeMultiplier_bound T hT Q₁ hQ₁ Rc C₁ hRc hC₁ 0 hbQ₁) d hbf hbv n x

/-- The genuine Gram solution adds one shift, with no change of radius or
fixed Sobolev order and no assumption about solution derivatives. -/
theorem solution_block_bound (directions : ι → P) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
    (T : ℝ) (hT : 0 ≤ T) (Q Q₁ : P → C(Icc (0 : ℝ) T, U →L[ℝ] E))
    (c : ℝ) (hc : 0 < c) (hLower : ∀ x t w, c * ‖w‖ ^ 2 ≤ ‖Q x t w‖ ^ 2)
    (f : P → TimeLp T E) (v : P → TimeLp T U)
    (hQ : ContDiff ℝ ∞ Q) (hQ₁ : ContDiff ℝ ∞ Q₁)
    (hf : ContDiff ℝ ∞ f) (hv : ContDiff ℝ ∞ v)
    (Rc R C₀ C₁ Cf Cv : ℝ) (hRc : 0 ≤ Rc) (hRcR : sobolevCoefficientRadius ι Rc ≤ R)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hCf : 0 ≤ Cf) (hCv : 0 ≤ Cv)
    (hR : 2 * gramBlockCost ι q c Rc C₀ (accelerationBlockAmplitude ι q Rc C₀ C₁ Cf Cv) *
      (sobolevCoefficientRadius ι Rc + 1) ≤ R)
    (hbQ : ∀ n x, ‖iteratedFDeriv ℝ n Q x‖ ≤ C₀ * majorant Rc 0 n)
    (hbQ₁ : ∀ n x, ‖iteratedFDeriv ℝ n Q₁ x‖ ≤ C₁ * majorant Rc 0 n)
    (d : ℕ)
    (hbf : ∀ n x, block directions q f n x ≤ Cf * majorant R d n)
    (hbv : ∀ n x, block directions q v n x ≤ Cv * majorant R d n)
    (n : ℕ) (x : P) :
    block directions q (fun y => gramSolver T hT (Q y) c hc (hLower y)
      (forcing T hT Q Q₁ f v y)) n x ≤ majorant R (d+1) n :=
  gramSolution_block_gevrey directions hd q T hT Q c hc hLower hQ Rc C₀ hRc hC₀ hbQ
    (forcing T hT Q Q₁ f v) (forcing_contDiff T hT Q Q₁ f v hQ hQ₁ hf hv)
    (accelerationBlockAmplitude ι q Rc C₀ C₁ Cf Cv) R
    (accelerationBlockAmplitude_nonneg q Rc C₀ C₁ Cf Cv hRc hC₀ hC₁ hCf hCv) hR d
    (forcing_block_bound directions hd q T hT Q Q₁ f v hQ hQ₁ hf hv Rc R C₀ C₁ Cf Cv
      hRc hRcR hC₀ hC₁ hCf hCv hbQ hbQ₁ d hbf hbv) n x

end EulerTimeLpAccelerationSobolev
