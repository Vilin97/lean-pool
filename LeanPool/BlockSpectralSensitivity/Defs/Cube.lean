/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mathlib.InformationTheory.Hamming

/-!
# The Boolean cube

An *input* on a finite coordinate set `V` is a map `V → Bool`.  For `A : Finset V`
we write `flipSet x A` for the input `x^A` of Section 1 of `bs_lambda.txt`, obtained by
flipping every coordinate of `A`.

Hamming distance is taken from Mathlib (`hammingDist`).

Adapted for Lean Pool from `Timeroot/BS_Lam` at commit
`7bd39a8d41ee7910d3296d0477ad18f8fff9d870`; ported to Lean Pool with proof and dependency cleanup.
-/

@[expose] public section

/-- The symmetric difference of two distinct singletons is the corresponding pair.  This is a
general `Finset` fact, stated here because Mathlib does not have it. -/
theorem Finset.symmDiff_singleton_singleton {α : Type*} [DecidableEq α] {p q : α} (hpq : p ≠ q) :
    symmDiff ({p} : Finset α) {q} = {p, q} := by
  ext v
  by_cases h1 : v = p <;> by_cases h2 : v = q <;> simp_all [Finset.mem_symmDiff]

namespace BSLambda

/-- An input to a Boolean function on the coordinate set `V`. -/
abbrev Input (V : Type*) : Type _ := V → Bool

/-- The all-zero input, written `0^V` in `bs_lambda.txt`. -/
def zeroInput (V : Type*) : Input V := fun _ ↦ false

@[simp] lemma zeroInput_apply {V : Type*} (v : V) : zeroInput V v = false := rfl

variable {V : Type*}

section DecEq
variable [DecidableEq V]

/-- `flipSet x A` is the input written `x^A` in the source document: it flips every
coordinate lying in `A` and leaves all other coordinates unchanged. -/
def flipSet (x : Input V) (A : Finset V) : Input V := fun v ↦ if v ∈ A then !x v else x v

@[simp] lemma flipSet_apply_of_mem {x : Input V} {A : Finset V} {v : V} (hv : v ∈ A) :
    flipSet x A v = !x v := by simp [flipSet, hv]

@[simp] lemma flipSet_apply_of_notMem {x : Input V} {A : Finset V} {v : V} (hv : v ∉ A) :
    flipSet x A v = x v := by simp [flipSet, hv]

/-- A coordinate survives `flipSet` exactly when it lies outside the flipped set. -/
@[simp] lemma flipSet_apply_eq_self_iff {x : Input V} {A : Finset V} {v : V} :
    flipSet x A v = x v ↔ v ∉ A := by
  by_cases hv : v ∈ A <;> simp [flipSet, hv]

/-- A coordinate is changed by `flipSet` exactly when it lies in the flipped set. -/
lemma flipSet_apply_ne_self_iff {x : Input V} {A : Finset V} {v : V} :
    flipSet x A v ≠ x v ↔ v ∈ A := by
  simp

/-- An input differs from its flip at every flipped coordinate. -/
lemma ne_flipSet_apply {x : Input V} {A : Finset V} {v : V} (hv : v ∈ A) :
    x v ≠ flipSet x A v := (flipSet_apply_ne_self_iff.2 hv).symm

@[simp] lemma flipSet_empty (x : Input V) : flipSet x ∅ = x := by
  funext v
  simp [flipSet]

/-- Flipping `A` and then `B` flips exactly the coordinates of the symmetric difference. -/
lemma flipSet_flipSet_symmDiff (x : Input V) (A B : Finset V) :
    flipSet (flipSet x A) B = flipSet x (symmDiff A B) := by
  funext v
  by_cases hA : v ∈ A <;> by_cases hB : v ∈ B <;> simp [flipSet, hA, hB, Finset.mem_symmDiff]

@[simp] lemma flipSet_flipSet (x : Input V) (A : Finset V) : flipSet (flipSet x A) A = x := by
  rw [flipSet_flipSet_symmDiff, symmDiff_self, Finset.bot_eq_empty, flipSet_empty]

/-- Flipping two distinct coordinates one after the other is the same as flipping the pair
at once. -/
lemma flipSet_singleton_flipSet_singleton (x : Input V) {p q : V} (hpq : p ≠ q) :
    flipSet (flipSet x {p}) {q} = flipSet x {p, q} := by
  rw [flipSet_flipSet_symmDiff, Finset.symmDiff_singleton_singleton hpq]

/-- Undoing one half of a pair flip leaves the single flip at the other coordinate: this is
the "other midpoint" identity behind every two-midpoint argument. -/
lemma flipSet_pair_flipSet_singleton (x : Input V) {p q : V} (hpq : p ≠ q) :
    flipSet (flipSet x {p, q}) {q} = flipSet x {p} := by
  rw [← flipSet_singleton_flipSet_singleton x hpq, flipSet_flipSet]

/-- Flipping a fixed set of coordinates is injective in the input. -/
lemma flipSet_left_injective (A : Finset V) : Function.Injective (flipSet · A) := by
  intro x y h
  simpa using congrArg (flipSet · A) h

@[simp] lemma flipSet_left_inj {x y : Input V} {A : Finset V} :
    flipSet x A = flipSet y A ↔ x = y :=
  (flipSet_left_injective A).eq_iff

/-- Distinct coordinates give distinct single-coordinate flips of a fixed input. -/
lemma flipSet_singleton_injective (x : Input V) :
    Function.Injective fun v : V ↦ flipSet x {v} := fun v w h ↦ by
  by_contra hvw
  simpa [hvw] using congrFun h v

/-- The flipped coordinate of a single-coordinate flip. -/
lemma flipSet_singleton_self (x : Input V) (v : V) : flipSet x {v} v = !x v := by
  simp

/-- Flipping a set of coordinates of the all-zero input yields its indicator function. -/
@[simp] lemma flipSet_zeroInput_apply (A : Finset V) (v : V) :
    flipSet (zeroInput V) A v = decide (v ∈ A) := by
  simp [flipSet]

end DecEq

section Fintype
variable [Fintype V] [DecidableEq V]

/-- The Hamming distance from `x` to `x^A` is exactly `A.card`. -/
@[simp] lemma hammingDist_flipSet (x : Input V) (A : Finset V) :
    hammingDist x (flipSet x A) = A.card := by
  simp only [hammingDist, ne_comm (a := x _), flipSet_apply_ne_self_iff,
    Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- Two flips of the same input differ exactly on the symmetric difference of the flipped
sets. -/
lemma hammingDist_flipSet_flipSet (x : Input V) (A B : Finset V) :
    hammingDist (flipSet x A) (flipSet x B) = (symmDiff A B).card := by
  have h : flipSet x B = flipSet (flipSet x A) (symmDiff A B) := by
    rw [flipSet_flipSet_symmDiff, symmDiff_symmDiff_cancel_left]
  rw [h, hammingDist_flipSet]

/-- Every input is a flip of every other, at the set of coordinates where they differ. -/
lemma flipSet_filter_ne (x y : Input V) :
    flipSet x (Finset.univ.filter fun v ↦ x v ≠ y v) = y := by
  funext v
  by_cases h : x v = y v <;> simp [flipSet, h, Bool.eq_not_iff]

/-- Two inputs at Hamming distance `1` differ in exactly one coordinate. -/
lemma exists_eq_flipSet_singleton_of_hammingDist_eq_one {x y : Input V}
    (h : hammingDist x y = 1) : ∃ v, y = flipSet x {v} := by
  obtain ⟨v, hv⟩ := Finset.card_eq_one.1 h
  exact ⟨v, (hv ▸ flipSet_filter_ne x y).symm⟩

lemma hammingDist_flipSet_singleton (x : Input V) (v : V) : hammingDist x (flipSet x {v}) = 1 := by
  simp

end Fintype

end BSLambda
