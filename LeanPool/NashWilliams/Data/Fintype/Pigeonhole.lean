/-
Copyright (c) 2026 Yann Pequignot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Pequignot
-/
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Infinite pigeonhole on `ℕ`

`Set`-valued restatement of `Finite.exists_infinite_fiber` for sequences indexed by `ℕ`. Both the
direct proof of the infinite Ramsey theorem and the Nash-Williams development iterate this, so it
is kept here rather than in either of them.

## Main results

* `exists_infinite_fiber_nat`: a finitely-valued sequence `f : ℕ → κ` is constant on an infinite
  set.

Upstream target: `Mathlib/Data/Fintype/Pigeonhole.lean`.
-/

/-- **Infinite pigeonhole.** A sequence `f : ℕ → κ` with `κ` finite takes some value `k` on an
infinite set of indices. -/
theorem exists_infinite_fiber_nat {κ : Type*} [Finite κ] (f : ℕ → κ) :
    ∃ k : κ, {n : ℕ | f n = k}.Infinite := by
  obtain ⟨k, hk⟩ := Finite.exists_infinite_fiber f
  exact ⟨k, Set.infinite_coe_iff.mp hk⟩
