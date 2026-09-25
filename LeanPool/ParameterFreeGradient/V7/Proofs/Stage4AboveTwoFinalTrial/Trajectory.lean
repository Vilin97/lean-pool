/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage4AboveTwoFinalTrial.TrajectoryDefinitions

/-!
The above-two dual trajectory satisfies its dynamics and exact observation requirements.
-/

@[expose] public section

namespace V7.Stage4AboveTwoFinalTrial

@[simp] theorem dualQ_zero (p eta : ℝ) (n : ℕ) (oracle : PairOracle d) :
    dualQ p eta n oracle 0 = 0 := by rw [dualQ]

@[simp] theorem dualR_zero (p eta : ℝ) (n : ℕ) (oracle : PairOracle d) :
    dualR p eta n oracle 0 = -(coeffB p eta n n n) • oracle.gradient 0 := by rw [dualR]

theorem dualQ_succ (p eta : ℝ) (n k : ℕ) (oracle : PairOracle d) :
    dualQ p eta n oracle (k + 1) = dualQ p eta n oracle k -
      increment p eta n (n - 1 - k) • aboveMirrorMap p (dualR p eta n oracle k) := by
  rw [dualQ]

theorem dualR_succ (p eta : ℝ) (n k : ℕ) (oracle : PairOracle d) :
    dualR p eta n oracle (k + 1) = dualR p eta n oracle k -
      weightedSum (k + 2) (fun i => coeffB p eta n (n - i) (n - 1 - k))
        (fun i => oracle.gradient (dualQ p eta n oracle i)) := by
  rw [dualR]
  congr 1
  ext j
  simp only [weightedSum]
  apply Finset.sum_congr rfl
  intro i hi
  have hilt : i < k + 2 := Finset.mem_range.mp hi
  by_cases hlt : i < k + 1
  · rw [ite_eq_left hlt]
  · have hieq : i = k + 1 := by omega
    subst i
    rw [ite_eq_right (by omega), ite_eq_left rfl, dualQ_succ]

theorem antiDiagonal_alpha (p eta : ℝ) (n k : ℕ) (hk : k < n)
    (Z : VectorSeq d) :
    weightedSum (k + 1) (fun i => alpha p eta n (n - i) (n - 1 - k)) Z =
      increment p eta n (n - 1 - k) • Z k := by
  ext j
  simp only [weightedSum, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single k]
  · have hrowpos : 0 < n - k := by omega
    have hrowle : n - k ≤ n := Nat.sub_le n k
    have hidx : n - k - 1 = n - 1 - k := by omega
    simp [alpha, hrowpos, hrowle, hidx]
  · intro i hi hne
    have hilt : i < k + 1 := Finset.mem_range.mp hi
    have hrowpos : 0 < n - i := by omega
    have hrowle : n - i ≤ n := Nat.sub_le n i
    have hneq : n - 1 - k ≠ n - i - 1 := by omega
    simp [alpha, hrowpos, hrowle, hneq]
  · simp

/-- The exact observations at the dual queries through the horizon. -/
noncomputable def dualTrace (p eta : ℝ) (n : ℕ) (oracle : PairOracle d) :
    List (Observation d) :=
  (List.range (n + 1)).map fun k => oracle.observe (dualQ p eta n oracle k)

/-- The concrete dual trajectories and coefficients packaged as above-two phase data. -/
noncomputable def dualData (p eta : ℝ) (n : ℕ) (oracle : PairOracle d) :
    AboveDualPhaseData p d n where
  oracle := oracle
  u := weight p eta n
  dw := increment p eta n
  alpha := alpha p eta n
  c := coeffC p eta n
  b := coeffB p eta n
  G := fun k => oracle.gradient (dualQ p eta n oracle k)
  r := dualR p eta n oracle
  q := dualQ p eta n oracle
  trace := dualTrace p eta n oracle

theorem dual_dynamics (p eta : ℝ) (n : ℕ) (hp : 2 < p)
    (heta : 0 < eta) (hn : 1 ≤ n) (oracle : PairOracle d) :
    AboveDualPhaseDynamics (dualData p eta n oracle) := by
  refine ⟨hn, coefficient_assumptions p eta n hp heta hn, ?_, ?_⟩
  · change dualR p eta n oracle 0 =
      -(coeffB p eta n n n) • oracle.gradient (dualQ p eta n oracle 0)
    rw [dualR_zero, dualQ_zero]
  · intro k hk
    constructor
    · change dualQ p eta n oracle (k + 1) = dualQ p eta n oracle k -
        weightedSum (k + 1)
          (fun i => alpha p eta n (n - i) (n - 1 - k))
          (fun i => aboveMirrorMap p (dualR p eta n oracle i))
      rw [dualQ_succ, antiDiagonal_alpha p eta n k hk]
    · exact dualR_succ p eta n k oracle

theorem dual_trace_exact (p eta : ℝ) (n : ℕ) (oracle : PairOracle d) :
    TraceExact oracle (dualTrace p eta n oracle) := by
  intro obs hobs
  simp only [dualTrace, List.mem_map] at hobs
  rcases hobs with ⟨k, hk, rfl⟩
  rfl

theorem dual_trace_length (p eta : ℝ) (n : ℕ) (oracle : PairOracle d) :
    (dualTrace p eta n oracle).length = n + 1 := by simp [dualTrace]

theorem dual_queried_at (p eta : ℝ) (n : ℕ) (oracle : PairOracle d)
    (k : ℕ) (hk : k ≤ n) :
    QueriedAt (dualTrace p eta n oracle) k (dualQ p eta n oracle k) := by
  refine ⟨oracle.observe (dualQ p eta n oracle k), ?_, rfl⟩
  simp [dualTrace, hk]

end V7.Stage4AboveTwoFinalTrial
