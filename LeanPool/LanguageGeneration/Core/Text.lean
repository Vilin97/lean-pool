/-
Copyright (c) 2026 Shuangping Li, Peng Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuangping Li, Peng Zhang
-/
module

public import LeanPool.LanguageGeneration.Core.Basic

/-!
# Ordered finite prefixes of information streams

This file supplies the paper-independent ordered-history interface used by
Gold identification.  KM and DenseGeneration usually consume `sample`, which
forgets order and repetitions; `textPrefix` retains both.  The bridge theorem
`textPrefix_toFinset` shows that the two views contain the same observed
values.
-/

@[expose] public section

namespace GenLimit

/-- The ordered observations strictly before time `t`. -/
def textPrefix {α : Type*} (stream : ℕ → α) (t : ℕ) : List α :=
  (List.range t).map stream

@[simp] theorem textPrefix_length {α : Type*} (stream : ℕ → α) (t : ℕ) :
    (textPrefix stream t).length = t := by
  simp [textPrefix]

@[simp] theorem textPrefix_zero {α : Type*} (stream : ℕ → α) :
    textPrefix stream 0 = [] := by
  simp [textPrefix]

theorem textPrefix_succ {α : Type*} (stream : ℕ → α) (t : ℕ) :
    textPrefix stream (t + 1) = textPrefix stream t ++ [stream t] := by
  simp [textPrefix, List.range_succ, List.map_append]

/-- Earlier ordered histories are list prefixes of later histories. -/
theorem textPrefix_prefix {α : Type*} (stream : ℕ → α)
    {s t : ℕ} (hst : s ≤ t) :
    textPrefix stream s <+: textPrefix stream t := by
  induction t, hst using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ t _ ih =>
      exact ih.trans (by
        rw [textPrefix_succ]
        exact List.prefix_append _ _)

/-- The list prefix is the list representation of the corresponding finite
tuple. -/
theorem textPrefix_eq_ofFn {α : Type*} (stream : ℕ → α) (t : ℕ) :
    textPrefix stream t = List.ofFn (fun i : Fin t => stream i) := by
  apply List.ext_get
  · simp [textPrefix]
  · intro i h₁ h₂
    simp [textPrefix]

theorem mem_textPrefix_iff {α : Type*} {stream : ℕ → α} {t : ℕ} {x : α} :
    x ∈ textPrefix stream t ↔ ∃ s < t, stream s = x := by
  simp [textPrefix]

/-- Forgetting order and repetitions from an ordered prefix gives the finite
sample used by the KM and DenseGeneration developments. -/
theorem textPrefix_toFinset (stream : ℕ → ℕ) (t : ℕ) :
    (textPrefix stream t).toFinset = sample stream t := by
  ext x
  simp [mem_textPrefix_iff, mem_sample_iff]

end GenLimit
