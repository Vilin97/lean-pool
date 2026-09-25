/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage3BelowTwoS3F.DualRecursion

/-!
The below-two dual trajectory has the required dynamics and exact chronological observations.
-/

@[expose] public section

namespace V7.Stage3BelowTwoS3F

@[simp] theorem dualQ_zero (p : ℝ) (n : ℕ) (oracle : PairOracle d) :
    dualQ p n oracle 0 = 0 := by rw [dualQ]

@[simp] theorem dualR_zero (p : ℝ) (n : ℕ) (oracle : PairOracle d) :
    dualR p n oracle 0 = -(coeffB n n n) • oracle.gradient 0 := by rw [dualR]

theorem dualQ_succ (p : ℝ) (n k : ℕ) (oracle : PairOracle d) :
    dualQ p n oracle (k + 1) =
      dualQ p n oracle k -
        increment n (n - 1 - k) • belowMirrorMap p (dualR p n oracle k) := by
  rw [dualQ]

theorem dualR_succ (p : ℝ) (n k : ℕ) (oracle : PairOracle d) :
    dualR p n oracle (k + 1) =
      dualR p n oracle k -
        weightedSum (k + 2) (fun i => coeffB n (n - i) (n - 1 - k))
          (fun i => oracle.gradient (dualQ p n oracle i)) := by
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

theorem antiDiagonal_alpha (n k : ℕ) (hk : k < n) (Z : VectorSeq d) :
    weightedSum (k + 1) (fun i => alpha n (n - i) (n - 1 - k)) Z =
      increment n (n - 1 - k) • Z k := by
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

/-- The exact observations at all normalized dual queries through the horizon. -/
noncomputable def dualTrace (p : ℝ) (n : ℕ) (oracle : PairOracle d) :
    List (Observation d) :=
  (List.range (n + 1)).map fun k => oracle.observe (dualQ p n oracle k)

/-- The concrete dual trajectories and coefficients packaged as below-two phase data. -/
noncomputable def dualData (p : ℝ) (n : ℕ) (oracle : PairOracle d) :
    BelowDualData p d n where
  oracle := oracle
  u := weight n
  dw := increment n
  alpha := alpha n
  c := coeffC n
  b := coeffB n
  G := fun k => oracle.gradient (dualQ p n oracle k)
  q := dualQ p n oracle
  r := dualR p n oracle
  trace := dualTrace p n oracle

theorem dual_dynamics (p : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (oracle : PairOracle d) : BelowDualDynamics (dualData p n oracle) := by
  refine ⟨hn, coefficient_assumptions n hn, ?_, ?_⟩
  · change dualR p n oracle 0 =
      -(coeffB n n n) • oracle.gradient (dualQ p n oracle 0)
    rw [dualR_zero, dualQ_zero]
  · intro k hk
    constructor
    · change dualQ p n oracle (k + 1) = dualQ p n oracle k -
        weightedSum (k + 1) (fun i => alpha n (n - i) (n - 1 - k))
          (fun i => belowMirrorMap p (dualR p n oracle i))
      rw [dualQ_succ, antiDiagonal_alpha n k hk]
    · exact dualR_succ p n k oracle

theorem dual_trace_exact (p : ℝ) (n : ℕ) (oracle : PairOracle d) :
    TraceExact oracle (dualTrace p n oracle) := by
  intro obs hobs
  simp only [dualTrace, List.mem_map] at hobs
  rcases hobs with ⟨k, hk, rfl⟩
  rfl

theorem dual_trace_length (p : ℝ) (n : ℕ) (oracle : PairOracle d) :
    (dualTrace p n oracle).length = n + 1 := by
  simp [dualTrace]

theorem dual_queried_at (p : ℝ) (n : ℕ) (oracle : PairOracle d)
    (k : ℕ) (hk : k ≤ n) :
    QueriedAt (dualTrace p n oracle) k (dualQ p n oracle k) := by
  refine ⟨oracle.observe (dualQ p n oracle k), ?_, rfl⟩
  simp [dualTrace, hk]

end V7.Stage3BelowTwoS3F
