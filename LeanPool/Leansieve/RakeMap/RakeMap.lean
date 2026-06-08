/-
Copyright (c) 2026 tangentstorm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tangentstorm
-/
import LeanPool.Leansieve.Rake.Rake

/-!
# Rake maps (`RakeMap`)

A `RakeMap` bundles a `Rake` together with a proof that its terms biject with the
set of naturals satisfying a given predicate. This module provides the base maps
`rmNat` and `rmGe2` and the `rem` operation that removes all multiples of `j`,
refining the predicate accordingly.
-/

namespace Leansieve

/--
A RakeMap provides a 1-to-1 mapping between its rake
and a set of numbers with some property. -/
structure RakeMap (pred : Nat → Prop) where
  /-- The underlying rake. -/
  rake : Rake
  /-- The rake's terms biject with the naturals satisfying `pred`. -/
  hbij : ∀ n, pred n ↔ ∃ m, rake.term m = n
  /-- The rake is sorted. -/
  hord : rake.sorted := by rfl

namespace RakeMap

open Rake

/-- The predicate that the rake map enumerates. -/
def pred {p : Nat → Prop} (rm : RakeMap p) : Nat → Prop := match rm with | _ => p

/-- The `n`-th term of the rake map. -/
@[simp] def term (rm : RakeMap p) (n : Nat) := rm.rake.term n

theorem min_term_zero (rm : RakeMap p) : ∀ n, (rm.term 0 ≤ rm.term n) :=
  @Rake.sorted_min_term_zero rm.rake rm.hord

/-- The rake map over all naturals (`rmNat.term` is a bijection `Nat → Nat`;
it happens to be the identity map, though that is not needed for the proofs). -/
def rmNat : RakeMap (fun _ => True) := {
  rake := nat
  hbij := by intro n; simp[Rake.term, nat, aseq, ASeq.term]}

/-- The rake map over the naturals `≥ 2`. -/
def rmGe2 : RakeMap (fun n => 2 ≤ n) := {
  rake := ge2
  hbij := by
    intro n
    simp only [Rake.term, ASeq.term, aseq, ge2, List.length_cons, List.length_nil, zero_add,
      List.getElem_singleton, Nat.div_one, one_mul]
    apply Iff.intro
    · show 2 ≤ n → ∃ m, 2 + m = n
      intro n2; use n-2; simp_all
    · show (∃ m, 2 + m = n) → 2 ≤ n
      intro hm; obtain ⟨m, hm⟩ := hm; rw[←hm]; simp }

-- operations on RakeMap -------------------------------------------------------

/--
This removes all multiples of a number from the rake.
- `hj : 0 < j` is necessary because we multiply the delta
  by j in the partition step, and delta=0 gives you a cyclic rake.
- `hnmr` is a proof that the rake contains at least one non-multiple of j.
  This is a number that won't be removed. If all numbers were
  removed, `term` would become meaningless.

In the future, it may make sense to also provide a version of
`rem` that requires no such proof but returns `Option Rake`. -/
def rem {prop : Nat → Prop} (rm : RakeMap prop) (j : Nat) (hj : 0 < j)
    (hnmr : ∃ n m, ¬j ∣ n ∧ rm.term m = n)
  : RakeMap (fun n => prop n ∧ ¬j ∣ n) :=
  let r₀ := rm.rake
  let r₁ := r₀.rem hj
  have hbij₀ := rm.hbij
  have hbij₁ : ∀ n, prop n ∧ ¬j ∣ n ↔ ∃ m, r₁.term m = n := by
    intro n
    have hnm : r₀.HasNonMultiple j := by
      obtain ⟨n, m, hjn, ht⟩ := hnmr
      dsimp[HasNonMultiple, r₀]
      use n; aesop
    have hd := r₀.rem_drop hj
    have hk := r₀.rem_keep hj
    have hs := r₀.rem_same hj
    repeat aesop
  let r₂ := r₁.sort
  let hbij₂ : ∀ n, prop n ∧ ¬j ∣ n ↔ ∃ m, r₂.val.term m = n := by
    intro n
    have hs := r₁.sort_term_iff_term n
    apply Iff.intro; all_goals aesop
  { rake := r₂, hbij := hbij₂, hord := by simp[r₂.prop] }

end RakeMap

end Leansieve
