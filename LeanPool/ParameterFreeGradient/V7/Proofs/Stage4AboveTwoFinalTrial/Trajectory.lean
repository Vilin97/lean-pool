/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage4AboveTwoFinalTrial.Coefficients

namespace V7.Stage4AboveTwoFinalTrial

noncomputable def delta (eps M D : ℝ) : ℝ := eps / (M * D)
noncomputable def etaF (p : ℝ) : ℝ := 1 / p
noncomputable def etaD (p eps M D : ℝ) : ℝ :=
  delta eps M D ^ conjugateExponent p / conjugateExponent p
noncomputable def nF (p eps M D : ℝ) : ℕ :=
  Nat.ceil ((aboveHp p / delta eps M D) ^ (p / (p + 2)))
noncomputable def nD (p eps M D : ℝ) : ℕ :=
  Nat.ceil ((aboveJp p / delta eps M D) ^ (p / (p + 2)))

theorem delta_pos {eps M D : ℝ} (heps : 0 < eps) (hM : 0 < M)
    (hD : 0 < D) : 0 < delta eps M D := by
  exact div_pos heps (mul_pos hM hD)

theorem etaF_pos {p : ℝ} (hp : 2 < p) : 0 < etaF p := by
  exact one_div_pos.mpr (by linarith)

theorem etaD_pos {p eps M D : ℝ} (hp : 2 < p) (heps : 0 < eps)
    (hM : 0 < M) (hD : 0 < D) : 0 < etaD p eps M D := by
  exact div_pos (Real.rpow_pos_of_pos (delta_pos heps hM hD) _)
    (Stage4AboveTwo.conjugate_pos hp)

theorem one_le_nF {p eps M D : ℝ} (hp : 2 < p) (heps : 0 < eps)
    (hM : 0 < M) (hD : 0 < D) : 1 ≤ nF p eps M D := by
  apply Nat.ceil_pos.mpr
  exact Real.rpow_pos_of_pos
    (div_pos (Stage4AboveTwo.hpConstant_pos hp) (delta_pos heps hM hD)) _

theorem one_le_nD {p eps M D : ℝ} (hp : 2 < p) (heps : 0 < eps)
    (hM : 0 < M) (hD : 0 < D) : 1 ≤ nD p eps M D := by
  apply Nat.ceil_pos.mpr
  exact Real.rpow_pos_of_pos
    (div_pos (Stage4AboveTwo.jpConstant_pos hp) (delta_pos heps hM hD)) _

structure PrimalState (d : ℕ) where
  s : Point d
  v : Point d
  x : Point d

noncomputable def primalState (p eta : ℝ) (n : ℕ) (oracle : PairOracle d) :
    ℕ → PrimalState d
  | 0 => ⟨0, 0, 0⟩
  | k + 1 =>
      let old := primalState p eta n oracle k
      let sNext := old.s - increment p eta n k • oracle.gradient old.x
      let vNext := aboveMirrorMap p sNext
      let xNext :=
        (weight p eta n k / weight p eta n (k + 1)) • old.x +
        (increment p eta n (k + 1) / weight p eta n (k + 1)) • vNext +
        (increment p eta n k / weight p eta n (k + 1)) • (vNext - old.v)
      ⟨sNext, vNext, xNext⟩

@[simp] theorem primalState_zero (p eta : ℝ) (n : ℕ)
    (oracle : PairOracle d) : primalState p eta n oracle 0 = ⟨0, 0, 0⟩ := rfl

theorem primalState_succ (p eta : ℝ) (n k : ℕ) (oracle : PairOracle d) :
    primalState p eta n oracle (k + 1) =
      let old := primalState p eta n oracle k
      let sNext := old.s - increment p eta n k • oracle.gradient old.x
      let vNext := aboveMirrorMap p sNext
      let xNext :=
        (weight p eta n k / weight p eta n (k + 1)) • old.x +
        (increment p eta n (k + 1) / weight p eta n (k + 1)) • vNext +
        (increment p eta n k / weight p eta n (k + 1)) • (vNext - old.v)
      ⟨sNext, vNext, xNext⟩ := rfl

noncomputable def primalTrace (p eta : ℝ) (n : ℕ) (oracle : PairOracle d) :
    List (Observation d) :=
  (List.range (n + 1)).map fun k => oracle.observe (primalState p eta n oracle k).x

noncomputable def primalData (p eta : ℝ) (n : ℕ) (oracle : PairOracle d)
    (fstar : ℝ) : AbovePrimalPhaseData p d n where
  oracle := oracle
  fstar := fstar
  u := weight p eta n
  dw := increment p eta n
  alpha := alpha p eta n
  c := coeffC p eta n
  b := coeffB p eta n
  s := fun k => (primalState p eta n oracle k).s
  v := fun k => (primalState p eta n oracle k).v
  x := fun k => (primalState p eta n oracle k).x
  trace := primalTrace p eta n oracle

theorem primal_dynamics (p eta : ℝ) (n : ℕ) (hp : 2 < p)
    (heta : 0 < eta) (hn : 1 ≤ n) (oracle : PairOracle d) (fstar : ℝ) :
    AbovePrimalPhaseDynamics (primalData p eta n oracle fstar) := by
  refine ⟨hn, coefficient_assumptions p eta n hp heta hn, rfl, rfl, rfl, ?_⟩
  intro k hk
  change
    (primalState p eta n oracle (k + 1)).s =
        (primalState p eta n oracle k).s -
          increment p eta n k • oracle.gradient (primalState p eta n oracle k).x ∧
    (primalState p eta n oracle (k + 1)).v =
        aboveMirrorMap p (primalState p eta n oracle (k + 1)).s ∧
    (primalState p eta n oracle (k + 1)).x =
        (weight p eta n k / weight p eta n (k + 1)) •
            (primalState p eta n oracle k).x +
        (increment p eta n (k + 1) / weight p eta n (k + 1)) •
            (primalState p eta n oracle (k + 1)).v +
        (increment p eta n k / weight p eta n (k + 1)) •
          ((primalState p eta n oracle (k + 1)).v -
            (primalState p eta n oracle k).v)
  rw [primalState_succ]
  exact ⟨rfl, rfl, rfl⟩

theorem primal_trace_exact (p eta : ℝ) (n : ℕ) (oracle : PairOracle d) :
    TraceExact oracle (primalTrace p eta n oracle) := by
  intro obs hobs
  simp only [primalTrace, List.mem_map] at hobs
  rcases hobs with ⟨k, hk, rfl⟩
  rfl

theorem primal_trace_length (p eta : ℝ) (n : ℕ) (oracle : PairOracle d) :
    (primalTrace p eta n oracle).length = n + 1 := by simp [primalTrace]

theorem primal_queried_at (p eta : ℝ) (n : ℕ) (oracle : PairOracle d)
    (k : ℕ) (hk : k ≤ n) :
    QueriedAt (primalTrace p eta n oracle) k (primalState p eta n oracle k).x := by
  refine ⟨oracle.observe (primalState p eta n oracle k).x, ?_, rfl⟩
  simp [primalTrace, hk]

mutual
  noncomputable def dualQ (p eta : ℝ) (n : ℕ) (oracle : PairOracle d) :
      ℕ → Point d
    | 0 => 0
    | k + 1 => dualQ p eta n oracle k -
        increment p eta n (n - 1 - k) • aboveMirrorMap p (dualR p eta n oracle k)
    termination_by k => k

  noncomputable def dualR (p eta : ℝ) (n : ℕ) (oracle : PairOracle d) :
      ℕ → Point d
    | 0 => -(coeffB p eta n n n) • oracle.gradient 0
    | k + 1 =>
        let qNext := dualQ p eta n oracle k -
          increment p eta n (n - 1 - k) • aboveMirrorMap p (dualR p eta n oracle k)
        let G : VectorSeq d := fun i =>
          if hi : i < k + 1 then oracle.gradient (dualQ p eta n oracle i)
          else if i = k + 1 then oracle.gradient qNext else 0
        dualR p eta n oracle k - weightedSum (k + 2)
          (fun i => coeffB p eta n (n - i) (n - 1 - k)) G
    termination_by k => k
end

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
  · rw [dif_pos hlt]
  · have hieq : i = k + 1 := by omega
    subst i
    rw [dif_neg (by omega), if_pos rfl, dualQ_succ]

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

noncomputable def dualTrace (p eta : ℝ) (n : ℕ) (oracle : PairOracle d) :
    List (Observation d) :=
  (List.range (n + 1)).map fun k => oracle.observe (dualQ p eta n oracle k)

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
