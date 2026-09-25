/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage4AboveTwoFinalTrial.Coefficients

/-!
The above-two trial parameters, explicit primal trajectory, and mutually recursive dual
trajectory.
-/

@[expose] public section

namespace V7.Stage4AboveTwoFinalTrial

/-- The accuracy normalized by the trial's smoothness and distance estimates. -/
noncomputable def delta (eps M D : ℝ) : ℝ := eps / (M * D)
/-- The primal phase error budget `1 / p`. -/
noncomputable def etaF (p : ℝ) : ℝ := 1 / p
/-- The dual phase error budget determined by the normalized accuracy. -/
noncomputable def etaD (p eps M D : ℝ) : ℝ :=
  delta eps M D ^ conjugateExponent p / conjugateExponent p
/-- The ceiling of the primal horizon required by the above-two gap bound. -/
noncomputable def nF (p eps M D : ℝ) : ℕ :=
  Nat.ceil ((aboveHp p / delta eps M D) ^ (p / (p + 2)))
/-- The ceiling of the dual horizon required by the above-two gradient bound. -/
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

/-- The dual accumulator, mirror point, and query point of an above-two primal iteration. -/
structure PrimalState (d : ℕ) where
  /-- The accumulated dual vector. -/
  s : Point d
  /-- The power mirror-map image of the accumulated dual vector. -/
  v : Point d
  /-- The current primal query point. -/
  x : Point d

/-- The literal above-two primal trajectory starting at the zero normalized state. -/
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

/-- The exact observations at the primal queries through the horizon. -/
noncomputable def primalTrace (p eta : ℝ) (n : ℕ) (oracle : PairOracle d) :
    List (Observation d) :=
  (List.range (n + 1)).map fun k => oracle.observe (primalState p eta n oracle k).x

/-- The concrete above-two primal trajectory packaged with its minimum objective value. -/
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
  /-- The recursively generated normalized query points of the above-two dual phase. -/
  noncomputable def dualQ (p eta : ℝ) (n : ℕ) (oracle : PairOracle d) :
      ℕ → Point d
    | 0 => 0
    | k + 1 => dualQ p eta n oracle k -
        increment p eta n (n - 1 - k) • aboveMirrorMap p (dualR p eta n oracle k)
    termination_by k => k

  /-- The recursively accumulated vectors of the above-two dual phase. -/
  noncomputable def dualR (p eta : ℝ) (n : ℕ) (oracle : PairOracle d) :
      ℕ → Point d
    | 0 => -(coeffB p eta n n n) • oracle.gradient 0
    | k + 1 =>
        let qNext := dualQ p eta n oracle k -
          increment p eta n (n - 1 - k) • aboveMirrorMap p (dualR p eta n oracle k)
        let G : VectorSeq d := fun i =>
          if i < k + 1 then oracle.gradient (dualQ p eta n oracle i)
          else if i = k + 1 then oracle.gradient qNext else 0
        dualR p eta n oracle k - weightedSum (k + 2)
          (fun i => coeffB p eta n (n - i) (n - 1 - k)) G
    termination_by k => k
end

end V7.Stage4AboveTwoFinalTrial
