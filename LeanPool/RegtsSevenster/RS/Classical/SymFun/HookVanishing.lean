/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Common.YoungDiagrams
public import LeanPool.RegtsSevenster.RS.Classical.SymFun.RecurrenceFromVanishing
public import LeanPool.RegtsSevenster.RS.Classical.SymFun.RationalityFromRecurrence

/-!
# Super power sums from hook vanishing

The full symmetric-function lemma (Lemma A.9 of the accompanying
paper): a sequence whose determinant Schur specialization vanishes
on every Young diagram outside the `(a, b)` hook is a
difference of power sums of two disjoint multisets of nonzero
complex numbers, of sizes at most `a` and `b`.

This is the composition of `exists_recurrence_of_schurDet_vanishing`
(`RecurrenceFromVanishing.lean`) with `superPowerSums_of_recurrence`
(`RationalityFromRecurrence.lean`), through the list↔diagram bridge
of `Common/YoungDiagrams.lean`.
-/

@[expose] public section

namespace RS

/-- **Lemma A.9**: if the Schur specialization of `t` vanishes on
every diagram outside the `(a, b)` hook, then `t` is a super power
sum: a difference of power sums of disjoint multisets of nonzero
complex numbers of sizes at most `a` and `b`. -/
theorem superPowerSums_of_hook_vanishing {t : ℕ → ℂ} {a b : ℕ}
    (hvan : ∀ μ : YoungDiagram, ¬ IsInHook a b μ → diagramSchur μ t = 0) :
    ∃ α β : Multiset ℂ,
      α.card ≤ a ∧ β.card ≤ b ∧
      (∀ x ∈ α, x ≠ 0) ∧ (∀ x ∈ β, x ≠ 0) ∧ (∀ x ∈ α, x ∉ β) ∧
      ∀ m : ℕ, 1 ≤ m →
        t m = (α.map (· ^ m)).sum - (β.map (· ^ m)).sum := by
  have hlist : ∀ w : List ℕ, w.SortedGE → (∀ x ∈ w, 0 < x) →
      w.length = a + 1 → b + 1 ≤ w.getD a 0 → schurDet t w = 0 := by
    intro w hw hpos hlen hlast
    set μ := YoungDiagram.ofRowLens w hw with hμ_def
    have hrows : μ.rowLens = w :=
      YoungDiagram.rowLens_ofRowLens_eq_self hpos
    have hout : ¬ IsInHook a b μ := by
      rw [not_isInHook_iff, hμ_def, rowLen_ofRowLens_getD]
      omega
    have := hvan μ hout
    rwa [diagramSchur, hrows] at this
  obtain ⟨c, hc, hrec⟩ := exists_recurrence_of_schurDet_vanishing hlist
  exact superPowerSums_of_recurrence c hc hrec

/-- The nilpotent-trace engine: a sequence whose Schur
specialization vanishes outside a hook and which is eventually zero
vanishes identically from degree `1` onward.  (Lemmas A.9 and A.10
composed; the categorical nilpotent-trace theorem instantiates
`t m` with the traces of the powers of a nilpotent endomorphism.) -/
theorem powerSums_zero_of_hook_and_eventually_zero {t : ℕ → ℂ}
    {a b : ℕ}
    (hvan : ∀ μ : YoungDiagram, ¬ IsInHook a b μ → diagramSchur μ t = 0)
    (hev : ∃ N₀ : ℕ, ∀ m, N₀ ≤ m → t m = 0) :
    ∀ m, 1 ≤ m → t m = 0 := by
  obtain ⟨α, β, _, _, hα, hβ, hdisj, hps⟩ :=
    superPowerSums_of_hook_vanishing hvan
  exact powerSums_zero_of_eventually_zero hα hβ hdisj hps hev

end RS
