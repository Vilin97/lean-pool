/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Numerical optimization in Corvaja--Zannier Theorem 2

The last step in the proof of Corvaja--Zannier's Theorem 2 optimizes the
parameterized estimate of their Theorem 4.  The split printed in the paper is
not compatible with the strict hypothesis of Theorem 4: if

`Q = p^3 * chi / (degreeU * degreeV)^2`,

then the fixed choice `t = 4^(1/3)` requires `Q >= 32`, not `Q >= 4`.
For `Q < 32`, the valid choice is `t = Q^(1/3) / 2`.  These two choices give
exactly the maximum displayed in Theorem 2.

This file isolates that corrected real-arithmetic argument.  Its theorem takes
the parameterized Theorem-4 estimate as an ordinary hypothesis, so it can be
applied directly once the curve-theoretic part of Theorem 4 is formalized.
-/

namespace BGS.CorvajaZannier

noncomputable section

/-- The dimensionless ratio used in the final optimization of
Corvaja--Zannier Theorem 2. -/
def optimizationRatio
    (p degreeProduct eulerCharacteristic : ℝ) : ℝ :=
  p ^ 3 * eulerCharacteristic / degreeProduct ^ 2

private theorem rpow_one_third_cube {x : ℝ} (hx : 0 ≤ x) :
    (x ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = x := by
  rw [← Real.rpow_mul_natCast hx]
  norm_num

private theorem fixed_parameter_coefficient_identity :
    let t : ℝ := (4 : ℝ) ^ ((1 : ℝ) / 3)
    4 / t + t ^ 2 / 2 = 3 * (2 : ℝ) ^ ((1 : ℝ) / 3) := by
  dsimp only
  let t : ℝ := (4 : ℝ) ^ ((1 : ℝ) / 3)
  let twoRoot : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 3)
  have htPos : 0 < t := by
    dsimp [t]
    positivity
  have htCube : t ^ 3 = 4 := by
    simpa [t] using rpow_one_third_cube (show (0 : ℝ) ≤ 4 by norm_num)
  have htwoRootNonneg : 0 ≤ twoRoot := by
    dsimp [twoRoot]
    positivity
  have htwoRootCube : twoRoot ^ 3 = 2 := by
    simpa [twoRoot] using rpow_one_third_cube (show (0 : ℝ) ≤ 2 by norm_num)
  have hscaledCube : (t ^ 2 / 2) ^ 3 = 2 := by
    calc
      (t ^ 2 / 2) ^ 3 = (t ^ 3) ^ 2 / 8 := by ring
      _ = 2 := by rw [htCube]; norm_num
  have hscaled : t ^ 2 / 2 = twoRoot := by
    apply (pow_left_inj₀ (by positivity) htwoRootNonneg (by norm_num : (3 : ℕ) ≠ 0)).mp
    exact hscaledCube.trans htwoRootCube.symm
  have hfourDiv : 4 / t = t ^ 2 := by
    apply (div_eq_iff htPos.ne').2
    nlinarith [htCube]
  change 4 / t + t ^ 2 / 2 = 3 * twoRoot
  rw [hfourDiv, ← hscaled]
  ring

/-- The corrected numerical deduction of Corvaja--Zannier Theorem 2 from the
parameterized estimate in Theorem 4.

The hypothesis `hTheoremFour` is precisely the real-valued part of Theorem 4:
for every positive parameter satisfying its strict size condition, it supplies
the parameterized gcd bound.  The proof uses the valid split `Q ≥ 32` and
`Q < 32`; it does not use the erroneous `Q = 4` split printed in the final
paragraph of the paper. -/
theorem theoremTwo_bound_of_theoremFour_bound
    (p degreeU degreeV eulerCharacteristic gcdValue : ℝ)
    (hp : 0 < p) (hdegreeU : 0 < degreeU) (hdegreeV : 0 < degreeV)
    (hEuler : 0 < eulerCharacteristic)
    (hTheoremFour : ∀ t : ℝ, 0 < t →
      8 * t ^ 3 * (degreeU * degreeV) ^ 2 <
        (p + degreeU + degreeV) ^ 3 * eulerCharacteristic →
      gcdValue ≤
        (4 / t + t ^ 2 / 2) *
          (degreeU * degreeV * eulerCharacteristic) ^ ((1 : ℝ) / 3)) :
    gcdValue ≤ max
      (3 * (2 * (degreeU * degreeV * eulerCharacteristic)) ^ ((1 : ℝ) / 3))
      (12 * (degreeU * degreeV) / p) := by
  let degreeProduct : ℝ := degreeU * degreeV
  let base : ℝ := degreeProduct * eulerCharacteristic
  let Q : ℝ := optimizationRatio p degreeProduct eulerCharacteristic
  have hdegreeProduct : 0 < degreeProduct := by
    dsimp [degreeProduct]
    positivity
  have hbase : 0 < base := by
    dsimp [base]
    positivity
  have hQ : 0 < Q := by
    dsimp [Q, optimizationRatio]
    positivity
  have hQProduct : Q * degreeProduct ^ 2 = p ^ 3 * eulerCharacteristic := by
    dsimp [Q, optimizationRatio]
    field_simp [hdegreeProduct.ne']
  have hpSum : p < p + degreeU + degreeV := by linarith
  have hpCube : p ^ 3 < (p + degreeU + degreeV) ^ 3 :=
    pow_lt_pow_left₀ hpSum hp.le (by norm_num)
  have hpEuler :
      p ^ 3 * eulerCharacteristic <
        (p + degreeU + degreeV) ^ 3 * eulerCharacteristic :=
    mul_lt_mul_of_pos_right hpCube hEuler
  by_cases hlarge : (32 : ℝ) ≤ Q
  · let t : ℝ := (4 : ℝ) ^ ((1 : ℝ) / 3)
    have htPos : 0 < t := by
      dsimp [t]
      positivity
    have htCube : t ^ 3 = 4 := by
      simpa [t] using rpow_one_third_cube (show (0 : ℝ) ≤ 4 by norm_num)
    have hthreshold :
        32 * degreeProduct ^ 2 ≤ p ^ 3 * eulerCharacteristic := by
      calc
        32 * degreeProduct ^ 2 ≤ Q * degreeProduct ^ 2 := by
          exact mul_le_mul_of_nonneg_right hlarge (sq_nonneg degreeProduct)
        _ = p ^ 3 * eulerCharacteristic := hQProduct
    have htAdmissible :
        8 * t ^ 3 * (degreeU * degreeV) ^ 2 <
          (p + degreeU + degreeV) ^ 3 * eulerCharacteristic := by
      calc
        8 * t ^ 3 * (degreeU * degreeV) ^ 2 =
            32 * degreeProduct ^ 2 := by
          rw [htCube]
          simp only [degreeProduct]
          ring
        _ ≤ p ^ 3 * eulerCharacteristic := hthreshold
        _ < (p + degreeU + degreeV) ^ 3 * eulerCharacteristic := hpEuler
    have hBound := hTheoremFour t htPos htAdmissible
    have hfixed :
        (4 / t + t ^ 2 / 2) * base ^ ((1 : ℝ) / 3) =
          3 * (2 * base) ^ ((1 : ℝ) / 3) := by
      rw [show 4 / t + t ^ 2 / 2 =
          3 * (2 : ℝ) ^ ((1 : ℝ) / 3) by
        simpa [t] using fixed_parameter_coefficient_identity]
      rw [Real.mul_rpow (show (0 : ℝ) ≤ 2 by norm_num) hbase.le]
      ring
    apply hBound.trans
    rw [show degreeU * degreeV * eulerCharacteristic = base by
      simp [base, degreeProduct]]
    rw [hfixed]
    exact le_max_left _ _
  · have hsmall : Q < 32 := lt_of_not_ge hlarge
    let qRoot : ℝ := Q ^ ((1 : ℝ) / 3)
    let t : ℝ := qRoot / 2
    let baseRoot : ℝ := base ^ ((1 : ℝ) / 3)
    have hqRootPos : 0 < qRoot := by
      dsimp [qRoot]
      positivity
    have hqRootCube : qRoot ^ 3 = Q := by
      simpa [qRoot] using rpow_one_third_cube hQ.le
    have htPos : 0 < t := by
      dsimp [t]
      positivity
    have htCube : 8 * t ^ 3 = Q := by
      dsimp [t]
      nlinarith [hqRootCube]
    have htAdmissible :
        8 * t ^ 3 * (degreeU * degreeV) ^ 2 <
          (p + degreeU + degreeV) ^ 3 * eulerCharacteristic := by
      change 8 * t ^ 3 * degreeProduct ^ 2 <
        (p + degreeU + degreeV) ^ 3 * eulerCharacteristic
      rw [htCube, hQProduct]
      exact hpEuler
    have hBound := hTheoremFour t htPos htAdmissible
    have hcoefficient : 4 / t + t ^ 2 / 2 ≤ 12 / qRoot := by
      dsimp [t]
      apply (le_div_iff₀ hqRootPos).2
      field_simp [hqRootPos.ne']
      nlinarith [hqRootCube]
    have hbaseRootNonneg : 0 ≤ baseRoot := by
      dsimp [baseRoot]
      positivity
    have hbaseRootCube : baseRoot ^ 3 = base := by
      simpa [baseRoot] using rpow_one_third_cube hbase.le
    have hrootRatio : baseRoot / qRoot = degreeProduct / p := by
      apply (pow_left_inj₀ (by positivity) (by positivity)
        (by norm_num : (3 : ℕ) ≠ 0)).mp
      rw [div_pow, div_pow, hbaseRootCube, hqRootCube]
      dsimp [base, Q, optimizationRatio]
      field_simp [hp.ne', hdegreeProduct.ne', hEuler.ne']
    have hsecond :
        (12 / qRoot) * baseRoot = 12 * degreeProduct / p := by
      calc
        (12 / qRoot) * baseRoot = 12 * (baseRoot / qRoot) := by ring
        _ = 12 * (degreeProduct / p) := by rw [hrootRatio]
        _ = 12 * degreeProduct / p := by ring
    apply hBound.trans
    rw [show degreeU * degreeV * eulerCharacteristic = base by
      simp [base, degreeProduct]]
    change (4 / t + t ^ 2 / 2) * baseRoot ≤ _
    calc
      (4 / t + t ^ 2 / 2) * baseRoot ≤
          (12 / qRoot) * baseRoot :=
        mul_le_mul_of_nonneg_right hcoefficient hbaseRootNonneg
      _ = 12 * degreeProduct / p := hsecond
      _ ≤ max
          (3 * (2 * (degreeU * degreeV * eulerCharacteristic)) ^ ((1 : ℝ) / 3))
          (12 * (degreeU * degreeV) / p) := by
        simp [degreeProduct]

end

end BGS.CorvajaZannier
