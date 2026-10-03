/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import LeanPool.Sendov.FiniteRange.Degree5
public import LeanPool.Sendov.FiniteRange.Degree7
public import LeanPool.Sendov.FiniteRange.Degree6To6
public import LeanPool.Sendov.FiniteRange.Degree8To9
public import LeanPool.Sendov.FiniteRange.Degree10To11
public import LeanPool.Sendov.FiniteRange.Degree12To13
public import LeanPool.Sendov.FiniteRange.Degree14To15
public import LeanPool.Sendov.FiniteRange.Degree16To18
public import LeanPool.Sendov.FiniteRange.Degree18To20
public import LeanPool.Sendov.FiniteRange.Degree20To22
public import LeanPool.Sendov.FiniteRange.Degree22To24
public import LeanPool.Sendov.FiniteRange.Degree24To26
public import LeanPool.Sendov.FiniteRange.Degree26To27
public import LeanPool.Sendov.FiniteRange.Degree28To29
public import LeanPool.Sendov.FiniteRange.Degree30To31
public import LeanPool.Sendov.FiniteRange.Degree32To33
public import LeanPool.Sendov.FiniteRange.Degree34To35
public import LeanPool.Sendov.FiniteRange.Degree36To37
public import LeanPool.Sendov.FiniteRange.Degree38To39
public import LeanPool.Sendov.FiniteRange.Degree40To41
public import LeanPool.Sendov.FiniteRange.Degree42To43
public import LeanPool.Sendov.FiniteRange.Degree44To45
public import LeanPool.Sendov.FiniteRange.Degree46To47
public import LeanPool.Sendov.FiniteRange.Degree48To49
public import LeanPool.Sendov.FiniteRange.Degree50To51
public import LeanPool.Sendov.FiniteRange.Degree52To53
public import LeanPool.Sendov.FiniteRange.Degree54To55
public import LeanPool.Sendov.FiniteRange.Degree56To58
public import LeanPool.Sendov.FiniteRange.Degree58To60
public import LeanPool.Sendov.FiniteRange.Degree60To63
public import LeanPool.Sendov.FiniteRange.Degree64To69
public import LeanPool.Sendov.FiniteRange.Degree70To79
public import LeanPool.Sendov.FiniteRange.Degree80To100

/-!
# The finite range `5 ≤ n ≤ 100`

This file does nothing but assemble the individual degree files and the degree *batches* into
a single statement.  Its only content is the case split, so it is also where the claim "every
degree in the range is covered" gets checked: the branches below are generated from the batch
plan, and the file would not compile if a degree were skipped.

Degrees `5` and `7` are handled one at a time (`Sendov.finite_range_five`,
`Sendov.finite_range_seven`); every other degree is covered by a batch `B n₀ n₁`, whose proof
is a single Bernstein certificate valid simultaneously for all `n₀ ≤ n ≤ n₁`.
-/

public section

namespace Sendov

variable {α : ℝ}

/-- **The finite range.**  Every degree from `5` to `100` inclusive. -/
theorem finite_range_le_100 {n : ℕ} (h0 : 5 ≤ n) (h1 : n ≤ 100)
    (hα : 0 ≤ α) (hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by
  -- degrees 5..5
  rcases Nat.lt_or_ge n 6 with h | h
  · obtain rfl : n = 5 := by omega
    exact finite_range_five hα hfeas
  -- degrees 6..6
  rcases Nat.lt_or_ge n 7 with h | h
  · exact Batch6To6.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 7..7
  rcases Nat.lt_or_ge n 8 with h | h
  · obtain rfl : n = 7 := by omega
    exact finite_range_seven hα hfeas
  -- degrees 8..9
  rcases Nat.lt_or_ge n 10 with h | h
  · exact Batch8To9.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 10..11
  rcases Nat.lt_or_ge n 12 with h | h
  · exact Batch10To11.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 12..13
  rcases Nat.lt_or_ge n 14 with h | h
  · exact Batch12To13.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 14..15
  rcases Nat.lt_or_ge n 16 with h | h
  · exact Batch14To15.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 16..18
  rcases Nat.lt_or_ge n 19 with h | h
  · exact Batch16To18.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 19..20
  rcases Nat.lt_or_ge n 21 with h | h
  · exact Batch18To20.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 21..22
  rcases Nat.lt_or_ge n 23 with h | h
  · exact Batch20To22.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 23..24
  rcases Nat.lt_or_ge n 25 with h | h
  · exact Batch22To24.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 25..26
  rcases Nat.lt_or_ge n 27 with h | h
  · exact Batch24To26.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 27..27
  rcases Nat.lt_or_ge n 28 with h | h
  · exact Batch26To27.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 28..29
  rcases Nat.lt_or_ge n 30 with h | h
  · exact Batch28To29.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 30..31
  rcases Nat.lt_or_ge n 32 with h | h
  · exact Batch30To31.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 32..33
  rcases Nat.lt_or_ge n 34 with h | h
  · exact Batch32To33.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 34..35
  rcases Nat.lt_or_ge n 36 with h | h
  · exact Batch34To35.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 36..37
  rcases Nat.lt_or_ge n 38 with h | h
  · exact Batch36To37.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 38..39
  rcases Nat.lt_or_ge n 40 with h | h
  · exact Batch38To39.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 40..41
  rcases Nat.lt_or_ge n 42 with h | h
  · exact Batch40To41.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 42..43
  rcases Nat.lt_or_ge n 44 with h | h
  · exact Batch42To43.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 44..45
  rcases Nat.lt_or_ge n 46 with h | h
  · exact Batch44To45.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 46..47
  rcases Nat.lt_or_ge n 48 with h | h
  · exact Batch46To47.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 48..49
  rcases Nat.lt_or_ge n 50 with h | h
  · exact Batch48To49.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 50..51
  rcases Nat.lt_or_ge n 52 with h | h
  · exact Batch50To51.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 52..53
  rcases Nat.lt_or_ge n 54 with h | h
  · exact Batch52To53.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 54..55
  rcases Nat.lt_or_ge n 56 with h | h
  · exact Batch54To55.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 56..58
  rcases Nat.lt_or_ge n 59 with h | h
  · exact Batch56To58.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 59..60
  rcases Nat.lt_or_ge n 61 with h | h
  · exact Batch58To60.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 61..63
  rcases Nat.lt_or_ge n 64 with h | h
  · exact Batch60To63.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 64..69
  rcases Nat.lt_or_ge n 70 with h | h
  · exact Batch64To69.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 70..79
  rcases Nat.lt_or_ge n 80 with h | h
  · exact Batch70To79.finite_range (by omega) (by omega) hα hα' hfeas
  -- degrees 80..100
  exact Batch80To100.finite_range (by omega) (by omega) hα hα' hfeas

/-- **The finite-range claim.**  The right-hand side of equation `stat` of the blog post is
strictly less than `1` on the range of degrees and of `α` left open there, that is, on
`5 ≤ n ≤ 97`, `0 ≤ α ≤ 17`, subject to the feasibility constraint `c ^ 2 ≤ A`.

This is the original challenge statement.  It is a special case of `finite_range_le_100`,
which covers three more degrees: the finite certification was pushed from `97` to `100` so
that it meets the large-degree argument of `Sendov.LargeDegree` with room to spare. -/
theorem finite_range (n : ℕ) (α : ℝ) (hn : 5 ≤ n) (hn' : n ≤ 97)
    (hα : 0 ≤ α) (hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) :
    R n α < 1 :=
  finite_range_le_100 hn (by omega) hα hα' hfeas

/-- Equation `stat` of the blog post is infeasible on the range
`5 ≤ n ≤ 97`, `0 ≤ α ≤ 17`, `c ^ 2 ≤ A`.  This is the form in which the claim is used. -/
theorem finite_range_contradiction (n : ℕ) (α : ℝ) (hn : 5 ≤ n) (hn' : n ≤ 97)
    (hα : 0 ≤ α) (hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) (hstat : 1 ≤ R n α) :
    False :=
  absurd hstat (not_le.2 (finite_range n α hn hn' hα hα' hfeas))

end Sendov
