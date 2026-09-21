/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage3BelowTwoS3F.Coefficients

namespace V7.Stage3BelowTwoS3F

structure PrimalState (d : ℕ) where
  s : Point d
  v : Point d
  x : Point d

noncomputable def primalState (p : ℝ) (n : ℕ) (oracle : PairOracle d) :
    ℕ → PrimalState d
  | 0 => ⟨0, 0, 0⟩
  | k + 1 =>
      let old := primalState p n oracle k
      let sNext := old.s - increment n k • oracle.gradient old.x
      let vNext := belowMirrorMap p sNext
      let xNext :=
        (weight n k / weight n (k + 1)) • old.x +
        (increment n (k + 1) / weight n (k + 1)) • vNext +
        (increment n k / weight n (k + 1)) • (vNext - old.v)
      ⟨sNext, vNext, xNext⟩

@[simp] theorem primalState_zero (p : ℝ) (n : ℕ) (oracle : PairOracle d) :
    primalState p n oracle 0 = ⟨0, 0, 0⟩ := rfl

theorem primalState_succ (p : ℝ) (n k : ℕ) (oracle : PairOracle d) :
    primalState p n oracle (k + 1) =
      let old := primalState p n oracle k
      let sNext := old.s - increment n k • oracle.gradient old.x
      let vNext := belowMirrorMap p sNext
      let xNext :=
        (weight n k / weight n (k + 1)) • old.x +
        (increment n (k + 1) / weight n (k + 1)) • vNext +
        (increment n k / weight n (k + 1)) • (vNext - old.v)
      ⟨sNext, vNext, xNext⟩ := rfl

noncomputable def primalTrace (p : ℝ) (n : ℕ) (oracle : PairOracle d) :
    List (Observation d) :=
  (List.range (n + 1)).map fun k => oracle.observe (primalState p n oracle k).x

noncomputable def primalData (p : ℝ) (n : ℕ) (oracle : PairOracle d)
    (z : Point d) (fstar : ℝ) : BelowPrimalData p d n where
  oracle := oracle
  z := z
  fstar := fstar
  u := weight n
  dw := increment n
  s := fun k => (primalState p n oracle k).s
  v := fun k => (primalState p n oracle k).v
  x := fun k => (primalState p n oracle k).x
  trace := primalTrace p n oracle

theorem primal_dynamics (p : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (oracle : PairOracle d) (z : Point d) (fstar : ℝ) :
    BelowPrimalDynamics (primalData p n oracle z fstar) := by
  refine ⟨hn, ?_, ?_, increment_at, ?_, rfl, rfl, rfl, ?_⟩
  · change weight n 0 = 1 / 4
    rw [weight_of_lt hn]
    norm_num
  · change weight n n = weight n (n - 1)
    rw [weight_at, weight_of_lt (show n - 1 < n by omega)]
    have hcast : (((n - 1 : ℕ) : ℝ) + 1) = (n : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
      push_cast
      ring
    rw [hcast]
  · intro k hk
    exact ⟨weight_of_lt hk, increment_of_lt hk,
      increment_formula hk, weight_sub_increment_sq hk⟩
  · intro k hk
    change
      (primalState p n oracle (k + 1)).s =
          (primalState p n oracle k).s -
            increment n k • oracle.gradient (primalState p n oracle k).x ∧
      (primalState p n oracle (k + 1)).v =
          belowMirrorMap p (primalState p n oracle (k + 1)).s ∧
      (primalState p n oracle (k + 1)).x =
          (weight n k / weight n (k + 1)) • (primalState p n oracle k).x +
          (increment n (k + 1) / weight n (k + 1)) •
            (primalState p n oracle (k + 1)).v +
          (increment n k / weight n (k + 1)) •
            ((primalState p n oracle (k + 1)).v -
              (primalState p n oracle k).v)
    rw [primalState_succ]
    exact ⟨rfl, rfl, rfl⟩

theorem primal_trace_exact (p : ℝ) (n : ℕ) (oracle : PairOracle d) :
    TraceExact oracle (primalTrace p n oracle) := by
  intro obs hobs
  simp only [primalTrace, List.mem_map] at hobs
  rcases hobs with ⟨k, hk, rfl⟩
  rfl

theorem primal_trace_length (p : ℝ) (n : ℕ) (oracle : PairOracle d) :
    (primalTrace p n oracle).length = n + 1 := by
  simp [primalTrace]

theorem primal_queried_at (p : ℝ) (n : ℕ) (oracle : PairOracle d)
    (k : ℕ) (hk : k ≤ n) :
    QueriedAt (primalTrace p n oracle) k (primalState p n oracle k).x := by
  refine ⟨oracle.observe (primalState p n oracle k).x, ?_, rfl⟩
  simp [primalTrace, hk]

end V7.Stage3BelowTwoS3F
