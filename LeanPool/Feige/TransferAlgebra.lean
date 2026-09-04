/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Algebraic part of the exponential transfer identity

This file isolates the purely algebraic end of the local exponential
transfer step used in the proof of Theorem 2.1.  All probability quantities
are represented by real numbers.  The two Stein identities, together with

* `wε = uε + vε`,
* `Bε = Aε + wε`,
* `Fε = Bε - vε`, and
* `θε = uε / wε`,

imply the final factorized transfer identity.  No order or probabilistic
hypotheses are needed for these implications; only the denominators have to
be nonzero.
-/

namespace Feige

section ExponentialTransferAlgebra

variable {a b c d : ℝ}
variable {uPlus uMinus vPlus vMinus wPlus wMinus : ℝ}
variable {APlus AMinus BPlus BMinus FPlus FMinus : ℝ}
variable {thetaPlus thetaMinus : ℝ}

/-- An intermediate identity obtained from the Stein relations after
substituting `Bε = Aε + wε` and `wε = uε + vε`. -/
theorem exponentialTransfer_eq24
    (hwPlus : wPlus = uPlus + vPlus)
    (hwMinus : wMinus = uMinus + vMinus)
    (hBPlus : BPlus = APlus + wPlus)
    (hBMinus : BMinus = AMinus + wMinus)
    (hA : d * (APlus - AMinus) = a * uPlus + b * uMinus)
    (hB : c * (BPlus - BMinus) = a * vPlus + b * vMinus) :
    (c + d) * (APlus - AMinus) =
      (a - c) * wPlus + (b + c) * wMinus := by
  rw [hwPlus, hwMinus]
  rw [hBPlus, hBMinus] at hB
  rw [hwPlus, hwMinus] at hB
  linear_combination hA + hB

/-- A second intermediate identity obtained after substituting
`Fε = Bε - vε`. -/
theorem exponentialTransfer_eq25
    (hFPlus : FPlus = BPlus - vPlus)
    (hFMinus : FMinus = BMinus - vMinus)
    (hB : c * (BPlus - BMinus) = a * vPlus + b * vMinus) :
    c * (FPlus - FMinus) =
      (a - c) * vPlus + (b + c) * vMinus := by
  rw [hFPlus, hFMinus]
  linear_combination hB

/-- The definition `θ = u / w`, rewritten without division. -/
theorem one_sub_theta_mul_w
    (hw : wPlus = uPlus + vPlus)
    (hw0 : wPlus ≠ 0)
    (htheta : thetaPlus = uPlus / wPlus) :
    (1 - thetaPlus) * wPlus = vPlus := by
  rw [htheta]
  field_simp [hw0]
  linear_combination hw

/-- The purely algebraic derivation of the factorized transfer identity.

The assumptions spell out every definitional relation among the abstract
probability quantities.  Positivity from the probabilistic statement is
stronger than the nonvanishing assumptions used here.
-/
theorem exponentialTransfer_identity
    (hwPlus : wPlus = uPlus + vPlus)
    (hwMinus : wMinus = uMinus + vMinus)
    (hwPlus0 : wPlus ≠ 0)
    (hwMinus0 : wMinus ≠ 0)
    (hBPlus : BPlus = APlus + wPlus)
    (hBMinus : BMinus = AMinus + wMinus)
    (hFPlus : FPlus = BPlus - vPlus)
    (hFMinus : FMinus = BMinus - vMinus)
    (hthetaPlus : thetaPlus = uPlus / wPlus)
    (hthetaMinus : thetaMinus = uMinus / wMinus)
    (hA : d * (APlus - AMinus) = a * uPlus + b * uMinus)
    (hB : c * (BPlus - BMinus) = a * vPlus + b * vMinus)
    (hcd0 : c + d ≠ 0) :
    (1 - thetaMinus) * (APlus - AMinus) -
        (c / (c + d)) * (FPlus - FMinus) =
      ((a - c) / (c + d)) * wPlus * (thetaPlus - thetaMinus) := by
  have h24 := exponentialTransfer_eq24 hwPlus hwMinus hBPlus hBMinus hA hB
  have h25 := exponentialTransfer_eq25 hFPlus hFMinus hB
  have hvPlus :
      vPlus = (1 - thetaPlus) * wPlus :=
    (one_sub_theta_mul_w hwPlus hwPlus0 hthetaPlus).symm
  have hvMinus :
      vMinus = (1 - thetaMinus) * wMinus :=
    (one_sub_theta_mul_w hwMinus hwMinus0 hthetaMinus).symm
  field_simp [hcd0]
  rw [hvPlus, hvMinus] at h25
  linear_combination (1 - thetaMinus) * h24 - h25

end ExponentialTransferAlgebra

end Feige
