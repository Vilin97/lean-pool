/-
Copyright (c) 2026 tangentstorm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tangentstorm
-/
import LeanPool.Leansieve.Rake.Rake

/--
A RakeMap provides a 1-to-1 mapping between its rake
and a set of numbers with some property. -/
structure RakeMap (pred: Nat → Prop) where
  rake : Rake
  hbij : ∀ n, pred n ↔ ∃ m, rake.term m = n
  hord : rake.sorted := by rfl

namespace RakeMap

open Rake

def pred {p:Nat → Prop} (_:RakeMap p) : Nat → Prop := p
@[simp] def term (rm: RakeMap p) (n:Nat) := rm.rake.term n

theorem min_term_zero (rm:RakeMap p)  : ∀ n, (rm.term 0 ≤ rm.term n) :=
  @Rake.sorted_min_term_zero rm.rake rm.hord

/-- proof that rm_nat.term provides a bijection from Nat → Nat
 (it happens to be an identity map, but this is not necessary for proofs) -/
def rm_nat : RakeMap (λ _ => True) := {
  rake := nat
  hbij := by intro n; simp[Rake.term, nat, aseq, ASeq.term]}

def rm_ge2 : RakeMap (λn => 2≤n) := {
  rake := ge2
  hbij := by
    intro n; simp[Rake.term, ge2, aseq, ASeq.term]; apply Iff.intro
    · show 2 ≤ n → ∃ m, 2 + m = n
      intro n2; use n-2; simp_all
    · show (∃ m, 2 + m = n) → 2 ≤ n
      intro hm; obtain ⟨m,hm⟩ := hm; rw[←hm]; simp }

-- operations on RakeMap -------------------------------------------------------

/-
This removes all multiples of a number from the rake.
- `hx: 0 < x` is necessary because we multiply the delta
  by x in the partition step, and delta=0 gives you a cyclic rake.
- `hnmr` is a proof that the rake contains at least one non-multiple of j.
  This is a number that won't be removed. If all numbers were
  removed, `term` would become meaningless.

In the future, it may make sense to also provide a version of
`rem` that requires no such proof but returns `Option Rake`. -/
def rem (rm : RakeMap prop) (j: Nat) (hj: 0<j) (hnmr: ∃n m, ¬j∣n ∧ rm.term m = n)
  : RakeMap (λ n => prop n ∧ ¬j∣n) :=
  let r₀ := rm.rake
  let r₁ := r₀.rem hj;
  have hbij₀ := rm.hbij
  have hbij₁ : ∀n, prop n ∧ ¬j∣n ↔ ∃ m, r₁.term m = n := by
    intro n
    have hnm: r₀.HasNonMultiple j := by
      obtain ⟨n, m, hjn, ht⟩ := hnmr
      dsimp[HasNonMultiple, r₀]
      use n; aesop
    have hd := r₀.rem_drop hj
    have hk := r₀.rem_keep hj
    have hs := r₀.rem_same hj
    repeat aesop
  let r₂ := r₁.sort
  let hbij₂ : ∀ n, prop n ∧ ¬j∣n ↔ ∃ m, r₂.val.term m = n := by
    intro n
    have hs := r₁.sort_term_iff_term n
    apply Iff.intro; all_goals aesop
  { rake := r₂, hbij := hbij₂, hord := by simp[r₂.prop] }
