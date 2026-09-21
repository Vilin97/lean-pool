/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage3BelowTwoS3F.Contract

/-!
The below-two trial's query count is bounded by its accuracy-dependent horizon.
-/

namespace V7.Stage3BelowTwoS3F

variable {d : ℕ} {eps : ℝ} {oracle : PairOracle d}
  {report : TrialReport d} {cached : CachedPair d}

theorem calls_first_bound (hp : 1 < p) (heps : 0 < eps)
    (hM : 0 < M) (hD : 0 < D)
    (hshape : FullShape p eps M D x0 oracle report m₁ m₂) :
    (report.calls : ℝ) ≤
      4 * Real.sqrt (M * D / ((p - 1) * eps)) + 2 := by
  have hcallsNat := fullShape_calls_le hshape
  have hcallsReal : (report.calls : ℝ) ≤
      (2 * horizon p eps M D : ℕ) := by exact_mod_cast hcallsNat
  have hratio : 0 ≤ M * D / ((p - 1) * eps) := by positivity
  have hnlt := Nat.ceil_lt_add_one
    (show 0 ≤ 2 * Real.sqrt (M * D / ((p - 1) * eps)) by positivity)
  change (horizon p eps M D : ℝ) <
    2 * Real.sqrt (M * D / ((p - 1) * eps)) + 1 at hnlt
  push_cast at hcallsReal
  linarith

theorem first_to_second_bound (hp : 1 < p) (heps : 0 < eps)
    (hM : 0 < M) (hD : 0 < D)
    (hkappa : 1 ≤ M * D / eps) :
    4 * Real.sqrt (M * D / ((p - 1) * eps)) + 2 ≤
      (4 / Real.sqrt (p - 1) + 2) * Real.sqrt (M * D / eps) := by
  have hsigma : 0 < p - 1 := sub_pos.mpr hp
  have hkappa0 : 0 ≤ M * D / eps := by positivity
  have hsqrtK : 1 ≤ Real.sqrt (M * D / eps) := by
    rw [Real.le_sqrt (by norm_num) hkappa0]
    simpa using hkappa
  have hratio : M * D / ((p - 1) * eps) =
      (M * D / eps) / (p - 1) := by
    field_simp [hsigma.ne', heps.ne']
  rw [hratio, Real.sqrt_div hkappa0]
  have hsqrtSigma : 0 < Real.sqrt (p - 1) := Real.sqrt_pos.2 hsigma
  calc
    4 * (Real.sqrt (M * D / eps) / Real.sqrt (p - 1)) + 2 ≤
        4 * (Real.sqrt (M * D / eps) / Real.sqrt (p - 1)) +
          2 * Real.sqrt (M * D / eps) := by linarith
    _ = (4 / Real.sqrt (p - 1) + 2) * Real.sqrt (M * D / eps) := by ring

end V7.Stage3BelowTwoS3F
