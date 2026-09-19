/-
Copyright (c) 2026 Arthur Champernowne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Champernowne
-/
module

public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.List.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Champernowne sequence: core definitions

The digits of each positive integer are written in big-endian order in base `b`.
`champBlocks b N` concatenates the first `N` blocks, and `champDigit b` is the
resulting infinite digit stream. `countOccurrences` counts overlapping finite
words, and `IsNormalSequence` states their limiting frequencies.

Definitions allow every base; hypotheses `1 < b` appear on the results that
need them. The prefix-coherence API is in `LeanPool.Champernowne.Prefix`.
-/

@[expose] public section

namespace Champernowne

/-- Big-endian digits of `n` in base `b`. -/
def bigDigits (b n : ℕ) : List ℕ := (Nat.digits b n).reverse

/-- First `N` blocks of the base-`b` Champernowne sequence: digits of 1..N. -/
def champBlocks (b N : ℕ) : List ℕ :=
  ((List.range N).map fun n => bigDigits b (n + 1)).flatten

theorem champBlocks_succ (b N : ℕ) :
    champBlocks b (N + 1) = champBlocks b N ++ bigDigits b (N + 1) := by
  simp [champBlocks, List.range_succ]

theorem le_length_champBlocks (b N : ℕ) : N ≤ (champBlocks b N).length := by
  induction N with
  | zero => simp [champBlocks]
  | succ n ih =>
    rw [champBlocks_succ, List.length_append]
    have hpos : 0 < (bigDigits b (n + 1)).length := by
      rw [bigDigits, List.length_reverse]
      exact List.length_pos_of_ne_nil
        (Nat.digits_ne_nil_iff_ne_zero.mpr (Nat.succ_ne_zero n))
    omega

/-- The `i`-th digit (0-indexed) of the base-`b` Champernowne sequence. -/
def champDigit (b i : ℕ) : ℕ :=
  (champBlocks b (i + 1))[i]'(lt_of_lt_of_le (Nat.lt_succ_self i)
    (le_length_champBlocks b (i + 1)))

/-- Number of (overlapping) occurrences of `w` as a contiguous block of `l`.

Window convention: `l.tails` yields the suffixes starting at positions
`0, 1, …, l.length` (the last being `[]`). A tail shorter than `w` can never
satisfy `w.isPrefixOf`, so the windows that can count are exactly the start
positions `0 … l.length - w.length`; there are no partial windows at the end
of the list. In particular `countOccurrences w l = 0` whenever
`w.length > l.length`, and `countOccurrences [] l = l.length + 1`
(the empty word is a prefix of every tail) — callers always pass `w ≠ []`. -/
def countOccurrences (w l : List ℕ) : ℕ :=
  l.tails.countP (w.isPrefixOf ·)

/-- Normality of a digit sequence in base `b`: every block of length `k`
(entries `< b`, leading zeros allowed) has asymptotic frequency `b⁻ᵏ`. -/
def IsNormalSequence (b : ℕ) (s : ℕ → ℕ) : Prop :=
  ∀ w : List ℕ, w ≠ [] → (∀ d ∈ w, d < b) →
    Filter.Tendsto
      (fun n => (countOccurrences w ((List.range n).map s) : ℝ) / n)
      Filter.atTop (nhds ((b : ℝ) ^ w.length)⁻¹)

end Champernowne
