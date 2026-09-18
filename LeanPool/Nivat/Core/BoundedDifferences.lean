/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

import LeanPool.Nivat.Core.Basic
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-
Upstream: https://github.com/boonsuan/nivat
Commit: 84fe839635bdebb7d5e80c209b4f578a0c767fcf
Originally released under MIT; the upstream copyright and permission notice follow.

MIT License

Copyright (c) 2026 Boon Suan Ho

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/-!
# Bounded configurations with vanishing higher differences

This module proves Lemma 3.4 (`lem:repeated`) of `paper/nivat.tex` and the
parallel case of Theorem 5.1. Boundedness rules out a nonzero affine slope along
a lattice orbit; boundedness of differences then reduces every positive order
to the first difference.

The main results are `difference_eq_zero_of_iterate_of_bounded`, its finite-range
specialization `difference_eq_zero_of_iterate`, and
`periodic_of_parallel_mixed_difference`. Finite-range closure lemmas also support
the orbit-closure difference in Corollary 3.6 (`cor:periodic-difference`).
-/

namespace Nivat

/-- Pointwise subtraction preserves finite range, as needed for the orbit-closure difference in
Corollary 3.6 (`cor:periodic-difference`). -/
theorem FiniteRange.sub {A : Type*} [Sub A] {c d : Configuration A}
    (hc : FiniteRange c) (hd : FiniteRange d) : FiniteRange (c - d) := by
  apply ((hc.prod hd).image (fun p : A × A => p.1 - p.2)).subset
  rintro y ⟨z, rfl⟩
  exact ⟨(c z, d z), ⟨⟨z, rfl⟩, ⟨z, rfl⟩⟩, rfl⟩

/-- A directional difference preserves finite range, as used when applying Lemma 3.4
(`lem:repeated`). -/
theorem FiniteRange.difference {A : Type*} [AddCommGroup A]
    {c : Configuration A} (hc : FiniteRange c) (h : Lattice) :
    FiniteRange (difference h c) := (hc.shift h).sub hc

/-- A bounded rational configuration with zero second difference has zero first difference: a
nonzero affine slope would contradict its uniform absolute bound. This is the affine-sequence
step in Lemma 3.4 (`lem:repeated`). -/
theorem difference_eq_zero_of_second_of_bounded (c : Configuration ℚ) (B : ℚ)
    (hc : ∀ z, |c z| ≤ B)
    (h : Lattice) (h2 : difference h (difference h c) = 0) : difference h c = 0 := by
  have hp : IsPeriod (difference h c) h := (difference_eq_zero_iff h _).mp h2
  funext z
  change difference h c z = 0
  have hseq (n : ℕ) : c (z + n • h) = c z + (n : ℚ) * difference h c z := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hd := hp.nsmul n z
      rw [difference_apply] at hd
      simp only [succ_nsmul, Nat.cast_add, Nat.cast_one]
      rw [← add_assoc]
      linarith
  by_contra hd
  obtain ⟨n, hn⟩ := exists_nat_gt ((B + |c z|) / |difference h c z|)
  have hgrow : B + |c z| < (n : ℚ) * |difference h c z| :=
    (div_lt_iff₀ (abs_pos.mpr hd)).mp hn
  have hbound : (n : ℚ) * |difference h c z| ≤ B + |c z| := by
    calc
      (n : ℚ) * |difference h c z| = |(n : ℚ) * difference h c z| := by
        rw [abs_mul, abs_of_nonneg (show 0 ≤ (n : ℚ) from Nat.cast_nonneg n)]
      _ = |c (z + n • h) - c z| := by rw [hseq n, add_sub_cancel_left]
      _ ≤ |c (z + n • h)| + |c z| := abs_sub _ _
      _ ≤ B + |c z| := add_le_add (hc (z + n • h)) le_rfl
  exact (not_lt_of_ge hbound) hgrow

/-- A finite rational range has a uniform absolute bound, as needed to apply Lemma 3.4
(`lem:repeated`) to finite-range configurations. -/
theorem FiniteRange.exists_abs_le {c : Configuration ℚ} (hc : FiniteRange c) :
    ∃ B : ℚ, ∀ z, |c z| ≤ B := by
  obtain ⟨B, hB⟩ := (hc.image abs).bddAbove
  exact ⟨B, fun z => hB ⟨c z, ⟨z, rfl⟩, rfl⟩⟩

/-- A finite-range rational configuration with zero second difference has zero first difference.
This is the affine-sequence case of Lemma 3.4 (`lem:repeated`). -/
theorem difference_eq_zero_of_second (c : Configuration ℚ) (hc : FiniteRange c)
    (h : Lattice) (h2 : difference h (difference h c) = 0) : difference h c = 0 := by
  obtain ⟨B, hB⟩ := hc.exists_abs_le
  exact difference_eq_zero_of_second_of_bounded c B hB h h2

/-- A uniform absolute bound on a rational configuration bounds each first difference by twice
that bound. This preserves boundedness during the reduction of difference order in Lemma 3.4
(`lem:repeated`). -/
theorem abs_difference_le (c : Configuration ℚ) (B : ℚ) (hc : ∀ z, |c z| ≤ B)
    (h z : Lattice) : |difference h c z| ≤ 2 * B := by
  rw [difference_apply]
  exact (abs_sub _ _).trans (by linarith [hc (z + h), hc z])

/-- Lemma 3.4 (`lem:repeated`): a bounded rational configuration annihilated by a positive iterate
of a difference is annihilated by the first difference. The direction may also be zero, when
the conclusion is immediate. -/
theorem difference_eq_zero_of_iterate_of_bounded (c : Configuration ℚ) (B : ℚ)
    (hc : ∀ z, |c z| ≤ B) (h : Lattice) (s : ℕ) (hs : 0 < s)
    (hpow : (difference h)^[s] c = 0) : difference h c = 0 := by
  induction s generalizing c B with
  | zero => omega
  | succ s ih =>
    by_cases hs0 : s = 0
    · subst s
      simpa using hpow
    · have h2 : difference h (difference h c) = 0 := by
        apply ih (difference h c) (2 * B) (abs_difference_le c B hc h) (by omega)
        simpa only [Function.iterate_succ_apply] using hpow
      exact difference_eq_zero_of_second_of_bounded c B hc h h2

/-- A finite-range rational configuration annihilated by a positive iterate of a directional
difference is annihilated by its first difference. This is the finite-range specialization of
Lemma 3.4 (`lem:repeated`). -/
theorem difference_eq_zero_of_iterate (c : Configuration ℚ) (hc : FiniteRange c)
    (h : Lattice) (s : ℕ) (hs : 0 < s) (hpow : (difference h)^[s] c = 0) :
    difference h c = 0 := by
  obtain ⟨B, hB⟩ := hc.exists_abs_le
  exact difference_eq_zero_of_iterate_of_bounded c B hB h s hs hpow

/-- A common integer multiple of two mixed-difference directions is a period of a finite-range
rational configuration. This is the repeated-difference argument in the parallel case of
Theorem 5.1; the integer coefficients may have either sign. -/
theorem difference_eq_zero_of_mixed_common_multiple (c : Configuration ℚ)
    (hc : FiniteRange c) (h t : Lattice)
    (hmix : difference h (difference t c) = 0) (a b : ℤ)
    (hab : a • h = b • t) : difference (a • h) c = 0 := by
  have hp1 : IsPeriod (difference t c) h := (difference_eq_zero_iff h _).mp hmix
  have hm1 : difference (a • h) (difference t c) = 0 :=
    (difference_eq_zero_iff (a • h) _).mpr (hp1.zsmul a)
  have hp2 : IsPeriod (difference (a • h) c) t := by
    apply (difference_eq_zero_iff t _).mp
    rw [← difference_comm (a • h) t c]
    exact hm1
  have hp3 : IsPeriod (difference (a • h) c) (a • h) := by
    simpa only [← hab] using hp2.zsmul b
  exact difference_eq_zero_of_second c hc (a • h)
    ((difference_eq_zero_iff (a • h) _).mpr hp3)

/-- The parallel case of Theorem 5.1: two nonzero parallel directions with vanishing mixed
difference force periodicity of a finite-range rational configuration. This case needs no
complexity hypothesis. -/
theorem periodic_of_parallel_mixed_difference (c : Configuration ℚ)
    (hc : FiniteRange c) (h t : Lattice) (hh : h ≠ 0) (ht : t ≠ 0)
    (hparallel : h.1 * t.2 = h.2 * t.1)
    (hmix : difference h (difference t c) = 0) : Periodic c := by
  by_cases hh1 : h.1 = 0
  · have hh2 : h.2 ≠ 0 := by
      intro h2
      exact hh (Prod.ext hh1 h2)
    have ht1 : t.1 = 0 := by
      have heq : h.2 * t.1 = 0 := by simpa [hh1] using hparallel.symm
      exact (mul_eq_zero.mp heq).resolve_left hh2
    have ht2 : t.2 ≠ 0 := by
      intro h2
      exact ht (Prod.ext ht1 h2)
    have hmul : t.2 • h = h.2 • t := by
      apply Prod.ext
      · change t.2 * h.1 = h.2 * t.1
        simp [hh1, ht1]
      · change t.2 * h.2 = h.2 * t.2
        exact mul_comm _ _
    refine ⟨t.2 • h, smul_ne_zero ht2 hh, ?_⟩
    apply (difference_eq_zero_iff (t.2 • h) c).mp
    exact difference_eq_zero_of_mixed_common_multiple c hc h t hmix t.2 h.2 hmul
  · have ht1 : t.1 ≠ 0 := by
      intro ht1
      apply ht
      apply Prod.ext ht1
      have heq : h.1 * t.2 = 0 := by simpa [ht1] using hparallel
      exact (mul_eq_zero.mp heq).resolve_left hh1
    have hmul : t.1 • h = h.1 • t := by
      apply Prod.ext
      · change t.1 * h.1 = h.1 * t.1
        exact mul_comm _ _
      · change t.1 * h.2 = h.1 * t.2
        exact (mul_comm t.1 h.2).trans hparallel.symm
    refine ⟨t.1 • h, smul_ne_zero ht1 hh, ?_⟩
    apply (difference_eq_zero_iff (t.1 • h) c).mp
    exact difference_eq_zero_of_mixed_common_multiple c hc h t hmix t.1 h.1 hmul

end Nivat
