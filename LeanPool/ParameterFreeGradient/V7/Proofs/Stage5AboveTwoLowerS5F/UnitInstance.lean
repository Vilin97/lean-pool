/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5F.PhysicalAnalytic

namespace V7.Stage5AboveTwoLowerS5F

open Stage5AboveTwoLower
open Stage5AboveTwoLower.S5ARepair
open Stage5AboveTwoLowerS5A2Envelope

theorem unitCompleted_smooth {p : ℝ} {d T : ℕ}
    (algorithm : DeterministicExactPairAlgorithm d)
    (hp : 2 < p) (hd : 2 ≤ d) (hT : 1 ≤ T) (hTd : T ≤ d) :
    IsLpSmooth p 1
      (unitObjectiveData p d T algorithm hT hTd).completedOracle := by
  let P := unitParameters p d T algorithm hT hTd
  let data := unitObjectiveData p d T algorithm hT hTd
  have hassum := unitObjectiveData_assumptions algorithm hp hd hT hTd
  rcases hassum.1 with ⟨-, -, -, -, -, -, -, -, -, -, -, hsteps,
    hcompletedValue, hcompletedGradient⟩
  let t0 := T - 1
  have ht0 : t0 < T := by dsimp [t0]; omega
  have hbasic : ∀ s < T, (data.xi s = 1 ∨ data.xi s = -1) ∧
      ResistingMaximumAt data.toLowerCompletionData s := by
    intro s hs
    rcases hsteps s hs with ⟨-, -, -, hxi, -, hresist, -⟩
    exact ⟨hxi, hresist⟩
  have hH : ∀ x, data.partialH t0 x =
      max (data.partialG t0 x / 2) (lpNorm p x - 3 / 2) := by
    rcases hsteps t0 ht0 with ⟨-, -, -, -, -, -, hH, -⟩
    exact hH
  have hHcert := partialH_convex_oneLipschitz data.toLowerCompletionData
    (by linarith : 1 ≤ p) ht0 hbasic hH
  have hchi : 0 < P.chi := unitChi_pos hT
  have hbase := repairSelectedOracle_smooth hp hd hchi
    (data.partialH t0) hHcert.1 hHcert.2
  have hbeta : 0 < P.beta := unitBeta_pos hp hd hT
  have hq := O3.one_lt_conjugateExponent (by linarith : 1 < p)
  intro x y
  have hb := hbase x y
  have hgradEq : ∀ z, data.completedOracle.gradient z =
      P.beta • (repairSelectedOracle p d P.chi (data.partialH t0)).gradient z := by
    intro z
    rw [hcompletedGradient]
    rfl
  rw [hgradEq, hgradEq, ← smul_sub]
  change O3.lpNorm (conjugateExponent p)
      (P.beta • ((repairSelectedOracle p d P.chi (data.partialH t0)).gradient x -
        (repairSelectedOracle p d P.chi (data.partialH t0)).gradient y)) ≤
      1 * O3.lpNorm p (x - y)
  rw [O3.Stage2RouteC.lpNorm_smul hq.le, abs_of_pos hbeta, one_mul]
  calc
    P.beta * lpNorm (conjugateExponent p)
        ((repairSelectedOracle p d P.chi (data.partialH t0)).gradient x -
          (repairSelectedOracle p d P.chi (data.partialH t0)).gradient y) ≤
      P.beta * ((repairMpd p d / P.chi) * lpNorm p (x - y)) :=
        mul_le_mul_of_nonneg_left hb hbeta.le
    _ = lpNorm p (x - y) := by
      dsimp [P, unitParameters]
      field_simp [ne_of_gt (unitChi_pos hT), ne_of_gt (repairMpd_pos hp hd)]

noncomputable def unitPositiveInstance {p : ℝ} {d T : ℕ}
    (algorithm : DeterministicExactPairAlgorithm d)
    (hp : 2 < p) (hd : 2 ≤ d) (hT : 1 ≤ T) (hTd : T ≤ d) :
    PositiveInstance p d (0 : Point d) := by
  let data := unitObjectiveData p d T algorithm hT hTd
  have hassum := unitObjectiveData_assumptions algorithm hp hd hT hTd
  have hgap := V7.aboveLowerQueryGap p hp d T data hassum
  refine
    { oracle := data.completedOracle
      L := 1
      L_pos := by norm_num
      coordinateGradient := hassum.2.2
      convex := hassum.2.1
      minimizerNonempty := ?_
      smooth := unitCompleted_smooth algorithm hp hd hT hTd }
  rcases hgap.2 with ⟨xstar, hmin, -⟩
  exact ⟨xstar, hmin⟩

end V7.Stage5AboveTwoLowerS5F
