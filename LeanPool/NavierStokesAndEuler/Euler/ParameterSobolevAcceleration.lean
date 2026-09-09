/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevCoefficient
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevOperations

/-! Coefficient-only Sobolev costs for the actual acceleration right side. -/

@[expose] public section


noncomputable section

namespace EulerParameterWordGevrey

open EulerGevrey
open scoped ContDiff

/-- Acceleration block amplitude, given by `3*sobolevCoefficientAmplitude ι q Rc CA *
(Cf+6*sobolevCoefficientAmplitude ι q Rc CB*Cv)`. -/
def accelerationBlockAmplitude (ι : Type*) [Fintype ι] (q : ℕ)
    (Rc CA CB Cf Cv : ℝ) : ℝ :=
  3*sobolevCoefficientAmplitude ι q Rc CA *
    (Cf+6*sobolevCoefficientAmplitude ι q Rc CB*Cv)

theorem accelerationBlockAmplitude_nonneg {ι : Type*} [Fintype ι] (q : ℕ)
    (Rc CA CB Cf Cv : ℝ) (hRc : 0 ≤ Rc) (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hCf : 0 ≤ Cf) (hCv : 0 ≤ Cv) :
    0 ≤ accelerationBlockAmplitude ι q Rc CA CB Cf Cv := by
  have ha := sobolevCoefficientAmplitude_nonneg (ι := ι) q Rc CA hRc hCA
  have hb := sobolevCoefficientAmplitude_nonneg (ι := ι) q Rc CB hRc hCB
  unfold accelerationBlockAmplitude
  positivity

variable {P E F G ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [Fintype ι]

/-- Only coefficient tensors are converted to fixed Sobolev blocks. Neither
the forcing nor velocity radius changes. -/
theorem block_acceleration_forcing_of_tensor (directions : ι → P)
    (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
    (A : P → E →L[ℝ] F) (B : P → G →L[ℝ] E) (f : P → E) (v : P → G)
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B)
    (hf : ContDiff ℝ ∞ f) (hv : ContDiff ℝ ∞ v)
    (Rc R CA CB Cf Cv : ℝ) (hRc : 0 ≤ Rc) (hRcR : sobolevCoefficientRadius ι Rc ≤ R)
    (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) (hCf : 0 ≤ Cf) (hCv : 0 ≤ Cv)
    (hbA : ∀ n x, ‖iteratedFDeriv ℝ n A x‖ ≤ CA * majorant Rc 0 n)
    (hbB : ∀ n x, ‖iteratedFDeriv ℝ n B x‖ ≤ CB * majorant Rc 0 n)
    (d : ℕ)
    (hbf : ∀ n x, block directions q f n x ≤ Cf * majorant R d n)
    (hbv : ∀ n x, block directions q v n x ≤ Cv * majorant R d n)
    (n : ℕ) (x : P) :
    block directions q (fun y => A y (f y-(2 : ℝ) • B y (v y))) n x ≤
      accelerationBlockAmplitude ι q Rc CA CB Cf Cv*majorant R d n :=
  block_acceleration_forcing_gevrey directions q A B f v hA hB hf hv
    (sobolevCoefficientRadius ι Rc) R
    (sobolevCoefficientAmplitude ι q Rc CA) (sobolevCoefficientAmplitude ι q Rc CB)
    Cf Cv (sobolevCoefficientRadius_nonneg Rc hRc) hRcR
    (sobolevCoefficientAmplitude_nonneg q Rc CA hRc hCA)
    (sobolevCoefficientAmplitude_nonneg q Rc CB hRc hCB) hCf hCv
    (coefficientBlock_of_tensor_bound directions hd q A hA Rc CA hRc hCA hbA)
    (coefficientBlock_of_tensor_bound directions hd q B hB Rc CB hRc hCB hbB)
    d hbf hbv n x

end EulerParameterWordGevrey
