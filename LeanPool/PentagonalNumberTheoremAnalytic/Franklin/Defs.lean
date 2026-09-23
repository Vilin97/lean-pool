/-
Copyright (c) 2026 Jonathan Conrad, Paula Muermann, Maryna Viazovska. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Conrad, Paula Muermann, Maryna Viazovska
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.Enumerative.Partition.GenFun
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

/-!
# Pentagonal Number Theorem — Definitions

Core definitions for the formalization of the Euler Pentagonal Number Theorem
via Franklin's involution.

## Main definitions

* `consecutiveTopRun`: length of the maximal consecutive run ending at `m` in `S`
* `distinctPartitions`: partitions of `n` into distinct positive parts
* `distinctPartitionsEven`, `distinctPartitionsOdd`: partitions with an even (resp. odd)
  number of parts
* `pe`, `po`: cardinalities of `distinctPartitionsEven n`, `distinctPartitionsOdd n`
* `partBase`, `partMax`, `partSlope`, `partSlopeSet`: structural invariants of a partition
* `distinctPartitionsAlpha`, `distinctPartitionsBeta`, `distinctPartitionsSpecial`:
  three-way decomposition of `distinctPartitions n` by Franklin's involution
* `smkSet`, `spkSet`: the special pentagonal partitions `S_{−k}` and `S_k`
* `alphaOp`, `betaOp`: Franklin's involution maps on `distinctPartitionsAlpha` and
  `distinctPartitionsBeta`
-/
@[expose] public section

open Finset

namespace PentagonalNumberTheorem.Franklin

/-- The length of the maximal consecutive run of elements of `S` ending at `m`, counted downward. -/
def consecutiveTopRun (S : Finset ℕ) : ℕ → ℕ
  | 0 => if (0 : ℕ) ∈ S then 1 else 0
  | m + 1 => if m + 1 ∈ S then 1 + consecutiveTopRun S m else 0

/-- The set of subsets `S ⊆ {1, …, n}` with `∑_{s ∈ S} s = n`, i.e., partitions of `n` into
distinct positive parts. -/
def distinctPartitions (n : ℕ) : Finset (Finset ℕ) :=
  (Icc 1 n).powerset.filter (fun S ↦ S.sum id = n)

/-- Partitions of `n` into distinct positive parts with an even number of parts. -/
def distinctPartitionsEven (n : ℕ) : Finset (Finset ℕ) :=
  (distinctPartitions n).filter (fun S ↦ S.card % 2 = 0)

/-- Partitions of `n` into distinct positive parts with an odd number of parts. -/
def distinctPartitionsOdd (n : ℕ) : Finset (Finset ℕ) :=
  (distinctPartitions n).filter (fun S ↦ S.card % 2 = 1)

/-- Number of partitions of `n` into an even number of distinct positive parts. -/
def pe (n : ℕ) : ℕ := (distinctPartitionsEven n).card

/-- Number of partitions of `n` into an odd number of distinct positive parts. -/
def po (n : ℕ) : ℕ := (distinctPartitionsOdd n).card

/-- The smallest element of a partition, returning 0 for the empty set. -/
def partBase (S : Finset ℕ) : ℕ :=
  if h : S.Nonempty then S.min' h else 0

/-- The largest element of a partition, returning 0 for the empty set. -/
def partMax (S : Finset ℕ) : ℕ :=
  if h : S.Nonempty then S.max' h else 0

/-- The length of the maximal consecutive run from `max(S)` downward in `S`. -/
def partSlope (S : Finset ℕ) : ℕ := consecutiveTopRun S (partMax S)

/-- The interval `{max(S) − slope(S) + 1, …, max(S)}` (the "slope set" of `S`). -/
def partSlopeSet (S : Finset ℕ) : Finset ℕ :=
  Icc (partMax S - partSlope S + 1) (partMax S)

/-- Partitions `S ∈ distinctPartitions n` that are nonempty and satisfy
`(b ≤ s ∧ b ∉ D) ∨ b + 1 ≤ s`, with `b = partBase S`, `s = partSlope S`. -/
def distinctPartitionsAlpha (n : ℕ) : Finset (Finset ℕ) :=
  (distinctPartitions n).filter (fun S ↦
    0 < S.card ∧
    ((partBase S ≤ partSlope S ∧ ¬(partMax S - partSlope S + 1 ≤ partBase S)) ∨
     partBase S + 1 ≤ partSlope S))

/-- Partitions `S ∈ distinctPartitions n` that are nonempty and satisfy
`(s < b ∧ b ∉ D) ∨ s + 2 ≤ b`, with `b = partBase S`, `s = partSlope S`. -/
def distinctPartitionsBeta (n : ℕ) : Finset (Finset ℕ) :=
  (distinctPartitions n).filter (fun S ↦
    0 < S.card ∧
    ((partSlope S < partBase S ∧ ¬(partMax S - partSlope S + 1 ≤ partBase S)) ∨
     partSlope S + 2 ≤ partBase S))

/-- Partitions of `n` into distinct parts that are either empty or satisfy
`base(S) ∈ slopeSet(S)` with `base(S) = slope(S)` or `base(S) = slope(S) + 1`. -/
def distinctPartitionsSpecial (n : ℕ) : Finset (Finset ℕ) :=
  (distinctPartitions n).filter (fun S ↦
    S.card = 0 ∨
    (0 < S.card ∧
     partMax S - partSlope S + 1 ≤ partBase S ∧
     (partBase S = partSlope S ∨ partBase S = partSlope S + 1)))

/-- The pentagonal partition `S_{−k} = {k, k+1, …, 2k−1}` of `(3k²−k)/2`. -/
def smkSet (k : ℕ) : Finset ℕ := Icc k (2 * k - 1)

/-- The pentagonal partition `S_k = {k+1, k+2, …, 2k}` of `(3k²+k)/2`. -/
def spkSet (k : ℕ) : Finset ℕ := Icc (k + 1) (2 * k)

/-- For `S ∈ 𝒫_α(n)` with base `b` and max `m`, `α(S) = (S \ {b, m−b+1}) ∪ {m+1}`. -/
def alphaOp (S : Finset ℕ) : Finset ℕ :=
  let b := partBase S
  let m := partMax S
  insert (m + 1) ((S.erase b).erase (m - b + 1))

/-- For `S ∈ 𝒫_β(n)` with slope `s` and max `m`, `β(S) = (S ∪ {s, m−s}) \ {m}`. -/
def betaOp (S : Finset ℕ) : Finset ℕ :=
  let s := partSlope S
  let m := partMax S
  (insert s (insert (m - s) S)).erase m

end PentagonalNumberTheorem.Franklin
