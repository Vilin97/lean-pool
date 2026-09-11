/-
Copyright (c) 2026 Yann Pequignot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Pequignot
-/
import Mathlib.Order.WellQuasiOrder
import LeanPool.NashWilliams.Combinatorics.Ramsey.Infinite

/-!
# Perfect/bad dichotomy and monotone subsequences in a well-quasi-order

The infinite Ramsey theorem for pairs gives a clean "perfect or bad" dichotomy for sequences in
any relation, from which the *monotone subsequence* property of a well-quasi-order follows
**without any transitivity assumption**.

## Main results

* `Sequences.perfect_or_bad`: every sequence has a subsequence that is either *perfect* (all
  earlier terms `r`-below all later ones) or *bad* (no earlier term `r`-below a later one). Pure
  consequence of `infinite_ramsey_pairs`; needs no order axioms.
* `WellQuasiOrdered.exists_monotone_subseq_lt`: in a WQO, every sequence has a strictly increasing
  reindexing along which `r` holds for all pairs `m < n`. No typeclass assumptions.

The second result answers a question of Leo Shine on the Mathlib Zulip: the monotone-subsequence
property of a WQO does not need the preorder (in particular transitivity) hypothesis carried by
the current Mathlib `WellQuasiOrdered.exists_monotone_subseq`.
-/

open Set

noncomputable section

namespace Sequences

variable {α : Type*}

/-- A sequence is *bad* for `r` if no earlier term is `r`-below a later one. -/
def IsBad (r : α → α → Prop) (f : ℕ → α) : Prop :=
  ∀ m n : ℕ, m < n → ¬ r (f m) (f n)

/-- A sequence is *perfect* for `r` if every earlier term is `r`-below every later one. -/
def IsPerfect (r : α → α → Prop) (f : ℕ → α) : Prop :=
  ∀ m n : ℕ, m < n → r (f m) (f n)

/-- **Perfect/bad dichotomy.** Every sequence `f : ℕ → α` has a strictly increasing reindexing
`f ∘ e` that is either perfect or bad for `r`. Immediate from the infinite Ramsey theorem for
pairs applied to the `2`-colouring `(m, n) ↦ ¬ r (f m) (f n)`; no order axioms are used. -/
theorem perfect_or_bad (r : α → α → Prop) (f : ℕ → α) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ (IsPerfect r (f ∘ e) ∨ IsBad r (f ∘ e)) := by
  classical
  obtain ⟨e, he, k, hk⟩ := @infinite_ramsey_pairs Bool inferInstance
    (fun m n (_ : m < n) => decide (¬ r (f m) (f n)))
  refine ⟨e, he, ?_⟩
  rcases Bool.eq_false_or_eq_true k with hktrue | hkfalse
  · -- colour `true`: `¬ r` on every pair — bad.
    right
    intro m n hmn
    have hc : ¬ r (f (e m)) (f (e n)) := of_decide_eq_true (hktrue ▸ hk m n hmn)
    simpa [Function.comp] using hc
  · -- colour `false`: `¬ ¬ r`, i.e. `r` holds on every pair — perfect.
    left
    intro m n hmn
    have hc : ¬ ¬ r (f (e m)) (f (e n)) := of_decide_eq_false (hkfalse ▸ hk m n hmn)
    simpa [Function.comp] using not_not.mp hc

end Sequences

open Sequences

variable {α : Type*} {r : α → α → Prop}

/-- **Monotone subsequences from a WQO, without transitivity.** In a well-quasi-order, every
sequence has a strictly increasing reindexing `e` along which `r (f (e m)) (f (e n))` holds for
all `m < n`. Follows directly from the perfect/bad dichotomy: a bad subsequence would contradict
the WQO. No typeclass assumptions on `r`. -/
theorem WellQuasiOrdered.exists_monotone_subseq_lt (h : WellQuasiOrdered r) (f : ℕ → α) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∀ m n : ℕ, m < n → r (f (e m)) (f (e n)) := by
  obtain ⟨e, he, hperf | hbad⟩ := perfect_or_bad r f
  · exact ⟨e, he, fun m n hmn => hperf m n hmn⟩
  · obtain ⟨m, n, hmn, hr⟩ := h (f ∘ e)
    exact absurd hr (hbad m n hmn)

end
