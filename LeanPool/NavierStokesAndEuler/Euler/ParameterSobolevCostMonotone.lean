/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevTensorInverse
import Mathlib.Algebra.Order.Star.Real

/-! Monotonicity of the explicit finite-order inverse polynomials. These
lemmas replace actual operator constants by source-scale upper bounds. -/

@[expose] public section


noncomputable section

namespace EulerParameterWordGevrey

theorem sobolevInverseCost_mono {I J B C : ℝ}
    (hI : 0 ≤ I) (hB : 0 ≤ B) (hIJ : I ≤ J) (hBC : B ≤ C) (q : ℕ) :
    sobolevInverseCost I B q ≤ sobolevInverseCost J C q := by
  induction q with
  | zero => exact hIJ
  | succ q ih =>
    have hq := sobolevInverseCost_nonneg I B hI hB q
    have hC := hB.trans hBC
    simp only [sobolevInverseCost]
    gcongr

theorem sobolevCoefficientAmplitude_mono {ι : Type*} [Fintype ι]
    (q : ℕ) {R C D : ℝ} (hR : 0 ≤ R) (hCD : C ≤ D) :
    sobolevCoefficientAmplitude ι q R C ≤ sobolevCoefficientAmplitude ι q R D := by
  have hr := sobolevCoefficientRadius_nonneg (ι := ι) R hR
  unfold sobolevCoefficientAmplitude
  apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCD (by positivity))
  exact Finset.sum_nonneg (fun k _ => mul_nonneg (pow_nonneg hr k) (sq_nonneg _))

theorem inverseBlockCost_mono {ι : Type*} [Fintype ι]
    (q : ℕ) {I J R C C' D D' : ℝ}
    (hI : 0 ≤ I) (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hIJ : I ≤ J) (hCC : C ≤ C') (hDD : D ≤ D') :
    inverseBlockCost ι q I R C D ≤ inverseBlockCost ι q J R C' D' := by
  have hB := sobolevCoefficientAmplitude_nonneg (ι := ι) q R C hR hC
  have hBC := sobolevCoefficientAmplitude_mono (ι := ι) q hR hCC
  have hs := sobolevInverseCost_mono hI hB hIJ hBC q
  have hq := sobolevInverseCost_nonneg J (sobolevCoefficientAmplitude ι q R C')
    (hI.trans hIJ) (hB.trans hBC) q
  exact add_le_add le_rfl (mul_le_mul hs (add_le_add hBC hDD) (add_nonneg hB hD) hq)

end EulerParameterWordGevrey
