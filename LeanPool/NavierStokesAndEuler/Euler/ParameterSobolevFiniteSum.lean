/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevBlocks
import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevScaling
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Finite sums preserve genuine fixed-Sobolev external-word estimates. -/

@[expose] public section


noncomputable section

namespace EulerParameterWordGevrey

open ContinuousLinearMap Finset
open scoped ContDiff

variable {P E ι κ : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

theorem block_finset_sum_le (directions : ι → P) (q : ℕ) (s : Finset κ) (f : κ → P → E)
    (hf : ∀ k ∈ s, ContDiff ℝ ∞ (f k)) (n : ℕ) (x : P) :
    block directions q (∑ k ∈ s, f k) n x ≤ ∑ k ∈ s, block directions q (f k) n x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_empty]
    change block directions q (fun _ : P => (0 : E)) n x ≤ 0
    rw [block_zero_function]
  | @insert k s hks ih =>
    rw [sum_insert hks, sum_insert hks]
    have hs : ContDiff ℝ ∞ (∑ j ∈ s, f j) := by
      have he : (∑ j ∈ s, f j) = fun y => ∑ j ∈ s, f j y := by
        funext y
        exact Finset.sum_apply y s f
      rw [he]
      exact ContDiff.sum (fun j hj => hf j (mem_insert_of_mem hj))
    exact (block_add_le directions q (f k) (∑ j ∈ s, f j)
      (hf k (mem_insert_self k s)) hs n x).trans
      (add_le_add (le_refl _) (ih (fun j hj => hf j (mem_insert_of_mem hj))))

end EulerParameterWordGevrey
