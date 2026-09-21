/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage4AboveTwoFinalTrial.Certificate

namespace V7.Stage4AboveTwoFinalTrial

variable {d : ℕ} {eps : ℝ} {oracle : PairOracle d}
  {report : TrialReport d} {cached : CachedPair d}

noncomputable def trialConstant (p : ℝ) : ℝ :=
  aboveHp p ^ (p / (p + 2)) + aboveJp p ^ (p / (p + 2)) + 2

theorem trialConstant_pos (p : ℝ) (hp : 2 < p) : 0 < trialConstant p := by
  unfold trialConstant
  have hH : 0 ≤ aboveHp p ^ (p / (p + 2)) :=
    Real.rpow_nonneg (Stage4AboveTwo.hpConstant_pos hp).le _
  have hJ : 0 ≤ aboveJp p ^ (p / (p + 2)) :=
    Real.rpow_nonneg (Stage4AboveTwo.jpConstant_pos hp).le _
  linarith

theorem calls_current_bound (hp : 2 < p) (heps : 0 < eps)
    (hM : 0 < M) (hD : 0 < D)
    (hkappa : 1 ≤ M * D / eps)
    (hshape : FullShape p eps M D x0 oracle report m₁ m₂) :
    (report.calls : ℝ) ≤
      trialConstant p * (M * D / eps) ^ (p / (p + 2)) := by
  let beta := p / (p + 2)
  let kappa := M * D / eps
  have hbeta : 0 < beta := by dsimp [beta]; positivity
  have hkappa0 : 0 ≤ kappa := le_trans (by norm_num) hkappa
  have hkappapow : 1 ≤ kappa ^ beta := by
    simpa [Real.one_rpow] using
      Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hkappa hbeta.le
  have hH : 0 < aboveHp p := Stage4AboveTwo.hpConstant_pos hp
  have hJ : 0 < aboveJp p := Stage4AboveTwo.jpConstant_pos hp
  have hdelta : 0 < delta eps M D := delta_pos heps hM hD
  have hdeltaEq : delta eps M D = 1 / kappa := by
    dsimp [delta, kappa]
    field_simp [heps.ne', hM.ne', hD.ne']
  have hHbase : aboveHp p / delta eps M D = aboveHp p * kappa := by
    rw [hdeltaEq]
    field_simp [show kappa ≠ 0 by positivity]
  have hJbase : aboveJp p / delta eps M D = aboveJp p * kappa := by
    rw [hdeltaEq]
    field_simp [show kappa ≠ 0 by positivity]
  have hnf := Nat.ceil_lt_add_one
    (Real.rpow_nonneg (div_nonneg hH.le hdelta.le) beta)
  have hnd := Nat.ceil_lt_add_one
    (Real.rpow_nonneg (div_nonneg hJ.le hdelta.le) beta)
  change (nF p eps M D : ℝ) <
    (aboveHp p / delta eps M D) ^ beta + 1 at hnf
  change (nD p eps M D : ℝ) <
    (aboveJp p / delta eps M D) ^ beta + 1 at hnd
  rw [hHbase, Real.mul_rpow hH.le hkappa0] at hnf
  rw [hJbase, Real.mul_rpow hJ.le hkappa0] at hnd
  have hcallsNat := fullShape_calls_le hshape
  have hcallsReal : (report.calls : ℝ) ≤
      (nF p eps M D : ℝ) + (nD p eps M D : ℝ) := by
    exact_mod_cast hcallsNat
  have hsum : (report.calls : ℝ) ≤
      (aboveHp p ^ beta + aboveJp p ^ beta + 2) * kappa ^ beta := by
    have hrough : (report.calls : ℝ) ≤
        (aboveHp p ^ beta + aboveJp p ^ beta) * kappa ^ beta + 2 := by
      linarith
    have hcoeff : 0 ≤ aboveHp p ^ beta + aboveJp p ^ beta := by positivity
    calc
      (report.calls : ℝ) ≤
          (aboveHp p ^ beta + aboveJp p ^ beta) * kappa ^ beta + 2 := hrough
      _ ≤ (aboveHp p ^ beta + aboveJp p ^ beta) * kappa ^ beta +
          2 * kappa ^ beta := by linarith
      _ = _ := by ring
  simpa [trialConstant, beta, kappa] using hsum

end V7.Stage4AboveTwoFinalTrial
