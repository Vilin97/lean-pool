/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.SampCert.Samplers.LaplaceGen.Code
import LeanPool.HopfieldNet.SampCert.Samplers.Laplace.Basic
import LeanPool.HopfieldNet.SampCert.Util.Shift

noncomputable section

open Classical PMF Nat Real

namespace SLang

@[simp]
theorem DiscreteLaplaceGenSample_apply (num : PNat) (den : PNat) (μ x : ℤ) :
  (DiscreteLaplaceGenSample num den μ) x =
  ENNReal.ofReal (((exp (1/((num : NNReal) / (den : NNReal))) - 1) / (exp (1/((num : NNReal) / (den : NNReal))) + 1)) * (exp (- (abs (x - μ) / ((num : NNReal) / (den : NNReal)))))) := by
  simp [DiscreteLaplaceGenSample]
  rw [tsum_eq_single (x - μ) (by aesop)]
  simp

theorem DiscreteLaplaceGenSample_periodic (num : PNat) (den : PNat) (μ x : ℤ) :
  (DiscreteLaplaceGenSample num den μ) x =
    (DiscreteLaplaceSample num den) (x - μ) := by
  simp [DiscreteLaplaceGenSample]
  rw [tsum_eq_single (x - μ) (by aesop)]
  simp


/--
Discrete Laplace has sum 1
-/
theorem DiscreteLaplaceGenSample_sum (num : PNat) (den : PNat) (μ : ℤ) : HasSum (DiscreteLaplaceGenSample num den μ) 1 := by
  rw [Summable.hasSum_iff ENNReal.summable]
  conv =>
    enter [1, 1, b]
    rw [DiscreteLaplaceGenSample_periodic]
  rw [<- DiscreteLaplaceSample_normalizes num den]
  apply tsum_eq_tsum_of_ne_zero_bij ?Bij
  case Bij => exact (fun w => w + μ)
  · intro _ _ H
    simp at H
    exact SetCoe.ext H
  · simp
    intro z HZ
    exists (z - μ)
    simp
    apply HZ
  · simp

/--
Discrete Laplace as a PMF
-/
def DiscreteLaplaceGenSamplePMF (num : PNat) (den : PNat) (μ : ℤ) : PMF ℤ :=
  ⟨ DiscreteLaplaceGenSample num den μ , DiscreteLaplaceGenSample_sum num den μ ⟩

end SLang
