/-
Copyright (c) 2026 jayyswan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: jayyswan
-/
module

public import LeanPool.HasseMinkowski.HilbertSymbol.Defs
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Tactic

/-!
# The Hilbert symbol and norms from `k(√b)`

For a field `k`, nonzero `a b : k` with `b` not a square, the Hilbert symbol `(a,b)_k` equals
`1` exactly when `a` is the norm of an element of the quadratic algebra `k(√b)`, realised here
as `QuadraticAlgebra k b 0` (the algebra with `ω² = b`).  Its norm form is
`norm ⟨X, Y⟩ = X² - b Y²`, so this says precisely that the ternary form
`z² - a x² - b y²` has a nontrivial zero.

The key point is the elementary equivalence between a nontrivial zero of `z² - a x² - b y²`
and `a` being a norm: if `x ≠ 0` we divide the equation by `x²`; if `x = 0` then the equation
reads `z² = b y²`, which forces `b` to be a square unless `y = z = 0`, contradicting
nontriviality.
-/

public section

namespace HasseMinkowski

attribute [local instance] Classical.propDecidable

-- Theorem: for nonzero `a`, `b`, the Hilbert symbol `(a,b)` equals `1` exactly when the
-- quadratic form `z² - a x² - b y²` has a nontrivial zero.
theorem hilbertSym_eq_one_iff_sol {k : Type*} [Field k] {a b : k}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    hilbertSym a b = 1 ↔
      ∃ z x y : k, (z, x, y) ≠ (0, 0, 0) ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0 := by
  constructor
  · intro h
    by_contra hcon
    unfold hilbertSym at h
    rw [ite_eq_right (by rw [not_or]; exact ⟨ha, hb⟩), ite_eq_right hcon] at h
    norm_num at h
  · rintro ⟨z, x, y, hne, hz⟩
    unfold hilbertSym
    rw [ite_eq_right (by rw [not_or]; exact ⟨ha, hb⟩), ite_eq_left ⟨z, x, y, hne, hz⟩]

-- Theorem: (norm characterization) over a field of characteristic `≠ 2`, for nonzero `a` and
-- nonsquare nonzero `b`, the Hilbert symbol `(a,b)` equals `1` exactly when `a` is the norm
-- of an element of `QuadraticAlgebra k b 0`, viewed as the quadratic algebra `k(√b)`.
theorem hilbertSym_eq_one_iff_isNorm {k : Type*} [Field k]
    {a b : k} (ha : a ≠ 0) (hb : b ≠ 0) (hbsq : ¬ IsSquare b) :
    hilbertSym a b = 1 ↔ ∃ t : QuadraticAlgebra k b 0, a = QuadraticAlgebra.norm t := by
  rw [hilbertSym_eq_one_iff_sol ha hb]
  constructor
  · rintro ⟨z, x, y, hne, hz⟩
    by_cases hx : x = 0
    · exfalso
      have hz' : z ^ 2 = b * y ^ 2 := by
        rw [hx] at hz
        linear_combination hz
      by_cases hy : y = 0
      · have hz0 : z = 0 := by
          have h : z ^ 2 = 0 := by simpa [hy] using hz'
          exact sq_eq_zero_iff.mp h
        exact hne (by simp [hx, hz0, hy])
      · apply hbsq
        refine ⟨z / y, ?_⟩
        field_simp
        exact hz'.symm
    · refine ⟨⟨z / x, y / x⟩, ?_⟩
      rw [QuadraticAlgebra.norm_def]
      field_simp
      linear_combination -hz
  · rintro ⟨t, ht⟩
    refine ⟨t.re, 1, t.im, by simp, ?_⟩
    rw [QuadraticAlgebra.norm_def] at ht
    rw [ht]
    ring

end HasseMinkowski
