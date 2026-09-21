/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5F.LocalTrialAdapter
import LeanPool.ParameterFreeGradient.V7.Proofs.Stage3BelowTwoS3F.AnalyticBridge
import LeanPool.ParameterFreeGradient.V7.Proofs.Stage1E03.Semantics

namespace V7.Stage5AboveTwoLowerS5F

theorem minimizer_gradient_zero (inst : PositiveInstance p d x0)
    {xstar : Point d} (hxstar : xstar ∈ MinimizerSet inst.oracle) :
    inst.oracle.gradient xstar = 0 := by
  have hlocal : IsLocalMin inst.oracle.value xstar :=
    Filter.Eventually.of_forall hxstar
  have hfd := hlocal.fderiv_eq_zero
  have hp := (inst.coordinateGradient xstar).2 (inst.oracle.gradient xstar)
  rw [hfd] at hp
  simp only [zero_apply] at hp
  have hpair : pairing (inst.oracle.gradient xstar)
      (inst.oracle.gradient xstar) = 0 := hp.symm
  have hsq : (lpNorm 2 (inst.oracle.gradient xstar)) ^ (2 : ℕ) = 0 := by
    rw [← O3.pairing_self_eq_lpNorm_two_sq]
    exact hpair
  have hn := O3.lpNorm_nonneg 2 (inst.oracle.gradient xstar)
  have hnorm : lpNorm 2 (inst.oracle.gradient xstar) = 0 := by nlinarith
  exact (O3.lpNorm_eq_zero_iff (by norm_num)).mp hnorm

theorem initial_gradient_le_LR (inst : PositiveInstance p d x0)
    (hp : 2 < p) {L R : ℝ} (hL : 0 < L)
    (hinstL : inst.L = L) (hinstR : inst.R ≤ R) :
    lpNorm (conjugateExponent p) (inst.oracle.gradient x0) ≤ L * R := by
  obtain ⟨xstar, hxstar, hradius⟩ :=
    Stage3BelowTwoS3F.exists_minimizer_at_radius inst (by linarith : 1 < p)
  have hgstar := minimizer_gradient_zero inst hxstar
  have hsmooth := inst.smooth x0 xstar
  rw [hgstar, sub_zero, hinstL] at hsmooth
  have hdist : O3.lpNorm p (x0 - xstar) = inst.R := by
    rw [show x0 - xstar = -(xstar - x0) by module, O3.lpNorm_neg]
    exact hradius
  rw [hdist] at hsmooth
  calc
    lpNorm (conjugateExponent p) (inst.oracle.gradient x0) ≤ L * inst.R := hsmooth
    _ ≤ L * R := mul_le_mul_of_nonneg_left hinstR hL.le

end V7.Stage5AboveTwoLowerS5F
