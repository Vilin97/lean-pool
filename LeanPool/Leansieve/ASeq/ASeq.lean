/-
Copyright (c) 2026 tangentstorm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tangentstorm
-/
-- ASeq: Arithmetic Sequences
import Mathlib.Tactic.Linarith
import Batteries.Data.List.Lemmas

/-!
# Arithmetic sequences (`ASeq`)

An `ASeq` is a single arithmetic sequence `k + d * n` of natural numbers. This
module defines arithmetic sequences, their evaluation, composition, partition
into residue classes, and the `gte` truncation that keeps only the terms at or
above a given bound. These are the atoms out of which a `Rake` is built.
-/

namespace Leansieve

/-- An arithmetic sequence `k + d * n` of natural numbers. -/
structure ASeq where
  /-- The constant term. -/
  k : Nat
  /-- The common difference (step size). -/
  d : Nat

/-- Lexicographic order on arithmetic sequences (by delta, then constant). -/
def ASeq.le (a b : ASeq) := if a.d = b.d then a.k ≤ b.k else a.d < b.d
instance : LE ASeq where le := ASeq.le
instance : Std.Total (α := ASeq) (· ≤ ·) where
  total a b := by
    change (if a.d = b.d then a.k ≤ b.k else a.d < b.d) ∨
      (if b.d = a.d then b.k ≤ a.k else b.d < a.d)
    by_cases h : a.d = b.d
    · rw [if_pos h, if_pos h.symm]
      exact Nat.le_total a.k b.k
    · have h' : b.d ≠ a.d := by
        intro hba
        exact h hba.symm
      rw [if_neg h, if_neg h']
      exact lt_or_gt_of_ne h

instance : Inhabited ASeq where
  default := .mk 0 1

instance : Ord ASeq where
  compare s1 s2 :=
    match compare s1.k s2.k with
    | .eq => compare s1.d s2.d
    | ord => ord

/-- Build the arithmetic sequence `k + d * n`. -/
@[simp] def aseq (k : Nat) (d : Nat) := ASeq.mk k d

namespace ASeq

/-- The sequence of all naturals (`0 + 1 * n`). -/
def nats := aseq 0 1
/-- The sequence of even naturals (`0 + 2 * n`). -/
def evens := aseq 0 2
/-- The sequence of odd naturals (`1 + 2 * n`). -/
def odds := aseq 1 2

/-- The `n`-th term of the sequence, `s.k + s.d * n`. -/
@[simp] def term (s : ASeq) (n : Nat) : Nat := s.k + s.d * n

-- you can coerce an ASeq a function
instance : CoeFun ASeq fun _ => Nat → Nat := ⟨term⟩

/-- The first `n` terms of a sequence. -/
def terms (s : ASeq) (n : Nat) : List Nat := List.range n |>.map fun i => term s i

/-- Compose two sequences: `(s.compose t) n = s (t n)`. -/
def compose (s t : ASeq) : ASeq := aseq (s.k + s.d * t.k) (s.d * t.d)

theorem compose_def (s t : ASeq) {n : Nat} : (s.compose t) n = s (t n) :=
  let y := (s.compose t) n
  calc
    y = s.k + (s.d * t.k) + (s.d * t.d * n) := by rfl
    _ = s.k + s.d * (t.k + t.d * n) := by linarith
    _ = s (t.k + t.d * n) := by rfl
    _ = s (t n) := by rfl

/-- Partition a sequence into `n` sub-sequences by residue class of the input. -/
def partition (s : ASeq) (n : Nat) : List ASeq :=
  List.range n |>.map fun i => compose s <| .mk i n

theorem length_partition {s : ASeq} {n : Nat}
  : (s.partition n).length = n := by
    simp [partition]

instance : ToString ASeq where
  toString s :=
    if s.k == 0 then
      if s.d == 1 then "n"
      else s!"{s.d}n"
    else if s.d == 0 then s!"{s.k}"
    else if s.d == 1 then s!"{s.k} + n"
    else s!"{s.k} + {s.d}n"

/-- Truncate the sequence to keep only terms `≥ n`. -/
def gte (s : ASeq) (n : Nat) : ASeq :=
  if n ≤ s.k then s
  else if n ≤ s.d then .mk (s.k + s.d) s.d
  else
    let t := n / s.d
    ASeq.mk (s.k + s.d * (t + 1)) s.d

protected lemma self_lt_mul_div_add (n d : Nat) (hd : d > 0) : n ≤ d * (n/d + 1) := by
  set r := n % d with hr
  set q := n / d with hq
  simp only [ge_iff_le]
  have : d * (n/d) + (n % d) = n := Nat.div_add_mod n d
  have : r + d * q = n := by rw[←hq, ←hr] at this; linarith
  have : r < d := Nat.mod_lt n hd
  linarith

theorem gte_term (s : ASeq) (n : Nat) : s.d > 0 → n ≤ term (s.gte n) 0 := by
  intro hdz
  simp only [term, gte, mul_zero, add_zero]
  if hsk : n ≤ s.k then simp [hsk]
  else if hsd : n ≤ s.d then simp [hsd, hsk]; linarith
  else
    simp only [hsk, ↓reduceIte, hsd]
    have hle : n ≤ s.d * (n/s.d + 1) := ASeq.self_lt_mul_div_add n s.d hdz
    linarith

theorem gte_same_delta (s : ASeq) (n : Nat) : (s.gte n).d = s.d := by
  simp only [gte]
  if hsk : n ≤ s.k then simp [hsk]
  else if hsd : n ≤ s.d then simp [hsd, hsk]
  else simp[hsk,hsd]

end ASeq

end Leansieve
