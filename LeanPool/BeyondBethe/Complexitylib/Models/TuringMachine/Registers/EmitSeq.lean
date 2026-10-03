/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Registers.RegisterOps

/-!
# Sequencing emitter stages

`bigSeqTM` folds a list of machines with `seqTM`, and `bigSeqTM_hoareTime`
chains their `EmitPred` specs: stage `k` carries the ghost state `(W k, Y k)`
to `(W (k+1), Y (k+1))`. All the finite-tuple folds of the reduction emitter
(literal chains, clause chains, the per-state/symbol/choice unrollings of the
transition family) are instances of this single rule.
-/


@[expose] public section

namespace Complexity

namespace TM

variable {n : ℕ}

/-- Sequence a list of machines (right fold, `skipTM` base). -/
def bigSeqTM : List (TM n) → TM n
  | [] => skipTM
  | m :: ms => seqTM m (bigSeqTM ms)

/-- **Indexed chain rule.** Machine `ms[k]` carries the `EmitPred` state from
    stage `k` to stage `k + 1`; the fold carries stage `0` to stage
    `ms.length`, in `|ms| · (b + 1) + 1` steps. -/
theorem bigSeqTM_hoareTime (ms : List (TM n)) (inp₀ : Tape)
    (W : ℕ → Fin n → Tape) (Y : ℕ → List Bool) (b : ℕ)
    (hinp₀ : Parked inp₀)
    (hWP : ∀ k j, Parked (W k j))
    (hms : ∀ k, (hk : k < ms.length) → ms[k].HoareTime
        (EmitPred inp₀ (W k) (Y k)) (EmitPred inp₀ (W (k + 1)) (Y (k + 1))) b) :
    (bigSeqTM ms).HoareTime
      (EmitPred inp₀ (W 0) (Y 0))
      (EmitPred inp₀ (W ms.length) (Y ms.length))
      (ms.length * (b + 1) + 1) := by
  induction ms generalizing W Y with
  | nil =>
    exact (skipTM_hoareTime inp₀ (W 0) (Y 0) hinp₀ (hWP 0)).mono_bound (by omega)
  | cons m ms ih =>
    have hhead := hms 0 (by simp)
    have hrest := ih (fun k => W (k + 1)) (fun k => Y (k + 1))
      (fun k j => hWP (k + 1) j)
      (fun k hk => by
        have h := hms (k + 1) (by simpa using Nat.succ_lt_succ hk)
        simpa using h)
    have hseq := seqTM_hoareTime m (bigSeqTM ms) hhead
      (emitPred_transition hinp₀ (hWP 1) (Y 1)) hrest
    refine hseq.consequence (fun _ _ _ h => h) (fun _ _ _ h => ?_) ?_
    · show EmitPred inp₀ (W (m :: ms).length) (Y (m :: ms).length) _ _ _
      rw [List.length_cons]
      exact h
    · rw [List.length_cons]
      have hmul : (ms.length + 1) * (b + 1) = ms.length * (b + 1) + (b + 1) :=
        Nat.succ_mul ..
      omega

end TM

end Complexity
