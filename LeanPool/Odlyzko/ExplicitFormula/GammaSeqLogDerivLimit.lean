/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.GammaSeqLogDeriv
public import Mathlib.Analysis.Normed.Field.Lemmas

/-!
# Gamma Seq Log Deriv Limit

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex Filter Real
open scoped Topology

namespace NumberField.Odlyzko

private theorem sum_range_natCast_inv_eq_harmonic (n : ℕ) :
    (∑ k ∈ Finset.range n, (((k + 1 : ℕ) : ℂ)⁻¹)) =
      (harmonic n : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, harmonic_succ]
      simp

theorem logDeriv_GammaSeq_succ_eq
    {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    logDeriv (fun z : ℂ ↦ Complex.GammaSeq z (n + 1)) s =
      gaussDigammaPartialSum s (n + 1) -
        (Real.eulerMascheroniSeq' (n + 1) : ℂ) -
          (s + (n + 1 : ℕ))⁻¹ := by
  have hnonzero :
      ∀ j ∈ Finset.range ((n + 1) + 1), s + j ≠ 0 := by
    intro j hj h
    have hre := congrArg Complex.re h
    simp only [add_re, natCast_re, zero_re] at hre
    grind
  rw [logDeriv_GammaSeq (Nat.succ_ne_zero n) hnonzero]
  rw [Finset.sum_range_succ]
  unfold gaussDigammaPartialSum
  have hharm :
      (∑ k ∈ Finset.range (n + 1),
          (((k + 1 : ℕ) : ℂ)⁻¹)) =
        (harmonic (n + 1) : ℂ) :=
    sum_range_natCast_inv_eq_harmonic (n + 1)
  rw [Real.eulerMascheroniSeq', if_neg (Nat.succ_ne_zero n)]
  rw [Finset.sum_sub_distrib, hharm]
  push_cast
  have hlog :
      Complex.log ((n : ℂ) + 1) =
        (Real.log ((n : ℝ) + 1) : ℂ) := by
    simpa using
      (Complex.ofReal_log
        (show 0 ≤ (n : ℝ) + 1 by positivity)).symm
  grind

end NumberField.Odlyzko
