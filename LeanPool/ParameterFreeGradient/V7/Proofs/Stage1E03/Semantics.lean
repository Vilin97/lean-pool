/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage1E03.Correctness

/-!
Compatibility of source Euclidean states and recorded checks with the original analytic
execution.
-/

namespace V7
namespace Stage1E03

/-- Classical proposition decisions used locally in the source semantics proof. -/
noncomputable local instance semanticsPropDecidable (q : Prop) : Decidable q :=
  Classical.propDecidable q

theorem minimizer_gradient_zero (inst : PositiveInstance 2 d x0)
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

/-- The current positive instance expressed in the original admissible-instance interface. -/
noncomputable def legacyInstance (inst : PositiveInstance 2 d x0)
    (eps : ℝ) (heps : 0 < eps)
    (hG : eps < lpNorm 2 (inst.oracle.gradient x0)) :
    O3.AdmissibleInstance d 2 := by
  classical
  choose xstar hxstar using inst.minimizerNonempty
  have hgstar := minimizer_gradient_zero inst hxstar
  have hg0 : inst.oracle.gradient x0 ≠ 0 := by
    intro hz
    rw [hz] at hG
    simp at hG
    linarith
  have hgrad : inst.oracle.gradient xstar ≠ inst.oracle.gradient x0 := by
    rw [hgstar]
    exact Ne.symm hg0
  have hpoint : xstar ≠ x0 := by
    intro h
    exact hgrad (congrArg inst.oracle.gradient h)
  let M0 := O3.secantScale 2 2 inst.oracle.gradient x0 xstar
  exact
    { f := inst.oracle.value
      grad := inst.oracle.gradient
      L := inst.L
      eps := eps
      x0 := x0
      z0 := xstar
      M0 := M0
      p_gt_one := by norm_num
      L_pos := inst.L_pos
      eps_pos := heps
      gradient_spec := inst.coordinateGradient
      convex := inst.convex
      minimizer_nonempty := inst.minimizerNonempty
      smooth := by
        simpa [IsLpSmooth, conjugateExponent, O3.conjugateExponent] using
          inst.smooth
      secant := ⟨hpoint, hgrad, by
        norm_num [M0, O3.secantScale, O3.conjugateExponent,
          Real.conjExponent], O3.secantScale_pos hpoint hgrad⟩ }

@[simp] theorem legacyInstance_oracle (inst : PositiveInstance 2 d x0)
    (eps : ℝ) (heps : 0 < eps)
    (hG : eps < lpNorm 2 (inst.oracle.gradient x0)) :
    (legacyInstance inst eps heps hG).oracle = inst.oracle := rfl

@[simp] theorem legacyInstance_L (inst : PositiveInstance 2 d x0)
    (eps : ℝ) (heps : 0 < eps)
    (hG : eps < lpNorm 2 (inst.oracle.gradient x0)) :
    (legacyInstance inst eps heps hG).L = inst.L := rfl

@[simp] theorem legacyInstance_f (inst : PositiveInstance 2 d x0)
    (eps : ℝ) (heps : 0 < eps)
    (hG : eps < lpNorm 2 (inst.oracle.gradient x0)) :
    (legacyInstance inst eps heps hG).f = inst.oracle.value := rfl

@[simp] theorem legacyInstance_grad (inst : PositiveInstance 2 d x0)
    (eps : ℝ) (heps : 0 < eps)
    (hG : eps < lpNorm 2 (inst.oracle.gradient x0)) :
    (legacyInstance inst eps heps hG).grad = inst.oracle.gradient := rfl

@[simp] theorem legacyInstance_eps (inst : PositiveInstance 2 d x0)
    (eps : ℝ) (heps : 0 < eps)
    (hG : eps < lpNorm 2 (inst.oracle.gradient x0)) :
    (legacyInstance inst eps heps hG).eps = eps := rfl

@[simp] theorem legacyInstance_x0 (inst : PositiveInstance 2 d x0)
    (eps : ℝ) (heps : 0 < eps)
    (hG : eps < lpNorm 2 (inst.oracle.gradient x0)) :
    (legacyInstance inst eps heps hG).x0 = x0 := rfl

@[simp] theorem legacyInstance_radius (inst : PositiveInstance 2 d x0)
    (eps : ℝ) (heps : 0 < eps)
    (hG : eps < lpNorm 2 (inst.oracle.gradient x0)) :
    (legacyInstance inst eps heps hG).radius = inst.R := rfl

theorem sourceEstimateState_eq_legacy
    (inst : PositiveInstance 2 d x0) (eps M : ℝ) (heps : 0 < eps)
    (hG : eps < lpNorm 2 (inst.oracle.gradient x0)) (k : ℕ) :
    sourceEstimateState inst.oracle M x0 k =
      O3.euclideanEstimateState (legacyInstance inst eps heps hG) M k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [sourceEstimateState, O3.euclideanEstimateState,
        nextEstimateState, estimateQuery, ih]
      rfl

theorem sourceU_eq_legacy (inst : PositiveInstance 2 d x0)
    (eps M : ℝ) (heps : 0 < eps)
    (hG : eps < lpNorm 2 (inst.oracle.gradient x0)) (n : ℕ) :
    sourceU inst M n =
      (O3.euclideanEstimateState (legacyInstance inst eps heps hG) M n).accelerated := by
  unfold sourceU
  rw [sourceEstimateState_eq_legacy]

theorem check_eq_exact_of_observations (oracle : PairOracle d)
    (check : ObservableGuardCheck d)
    (hx : check.xPair = oracle.observe check.xPair.point)
    (hy : check.yPair = oracle.observe check.yPair.point) :
    check = exactGuardCheck check.kind oracle check.xPair.point check.yPair.point := by
  cases check with
  | mk kind xPair yPair =>
      change (⟨kind, xPair, yPair⟩ : ObservableGuardCheck d) =
        ⟨kind, oracle.observe xPair.point, oracle.observe yPair.point⟩
      congr

theorem not_guardFails_of_checkHolds (p M : ℝ) (oracle : PairOracle d)
    (check : ObservableGuardCheck d)
    (hx : check.xPair = oracle.observe check.xPair.point)
    (hy : check.yPair = oracle.observe check.yPair.point)
    (hcheck : CheckHolds p M check) :
    ¬ GuardFails p M oracle check.failure := by
  have heq := check_eq_exact_of_observations oracle check hx hy
  rw [heq] at hcheck ⊢
  exact (checkHolds_exact_iff p M oracle _ _ _).mp hcheck

theorem guardFails_of_not_checkHolds (p M : ℝ) (oracle : PairOracle d)
    (check : ObservableGuardCheck d)
    (hx : check.xPair = oracle.observe check.xPair.point)
    (hy : check.yPair = oracle.observe check.yPair.point)
    (hcheck : ¬ CheckHolds p M check) :
    GuardFails p M oracle check.failure := by
  have heq := check_eq_exact_of_observations oracle check hx hy
  rw [heq] at hcheck ⊢
  by_contra hnot
  exact hcheck ((checkHolds_exact_iff p M oracle _ _ _).mpr hnot)

end Stage1E03
end V7
