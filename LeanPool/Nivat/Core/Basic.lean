/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

module

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Tactic.Abel

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
# Configurations and translation operators

The configuration, period and operator notation of Section 1.1 of
`paper/nivat.tex`. All configurations have the full integer lattice as their domain.

`IsPeriod c h` permits the zero vector; `Periodic c` requires one nonzero period.
The forward-shift convention is shared by the Laurent action and pattern pairing.
-/

public section

namespace Nivat

/-- The integer lattice `ℤ²` on which configurations are defined (Section 1). -/
abbrev Lattice := ℤ × ℤ

/-- A configuration with alphabet `A`, as in Section 1. -/
abbrev Configuration (A : Type*) := Lattice → A

/-- The forward translation `Tʰc`, with `(Tʰc)(z) = c(z + h)` (Section 1.1). -/
@[expose] def shift {A : Type*} (h : Lattice) (c : Configuration A) : Configuration A :=
  fun z => c (z + h)

/-- A configuration takes values in a finite set (Section 1.1). -/
@[expose] def FiniteRange {A : Type*} (c : Configuration A) : Prop := (Set.range c).Finite

/-- A vector fixes the configuration at every lattice site (Section 1).
This predicate allows zero; `Periodic` requires a nonzero witness. -/
@[expose] def IsPeriod {A : Type*} (c : Configuration A) (h : Lattice) : Prop :=
  ∀ z, c (z + h) = c z

/-- Existence of one nonzero global period, the conclusion of Theorem 1.1 (`thm:main`). -/
@[expose] def Periodic {A : Type*} (c : Configuration A) : Prop :=
  ∃ h : Lattice, h ≠ 0 ∧ IsPeriod c h

/-- The difference operator `Δₕ = Tʰ - I` from Section 1.1. -/
@[expose] def difference {A : Type*} [AddCommGroup A] (h : Lattice)
    (c : Configuration A) : Configuration A := shift h c - c

/-- Evaluation of the forward shift from Section 1.1. -/
@[simp] theorem shift_apply {A : Type*} (h : Lattice) (c : Configuration A) (z) :
    shift h c z = c (z + h) := rfl

/-- The zero translation acts as the identity (Section 1.1). -/
@[simp] theorem shift_zero {A : Type*} (c : Configuration A) : shift 0 c = c := by
  funext z
  simp [shift]

/-- Composition of the shift operators from Section 1.1. -/
theorem shift_add {A : Type*} (h t : Lattice) (c : Configuration A) :
    shift (h + t) c = shift h (shift t c) := by
  funext z
  simp [shift, add_assoc]

/-- Shift operators commute, as used throughout Section 1.1. -/
theorem shift_comm {A : Type*} (h t : Lattice) (c : Configuration A) :
    shift h (shift t c) = shift t (shift h c) := by
  rw [← shift_add, ← shift_add, add_comm h t]

/-- The pointwise period condition is equivalent to `Tʰc = c` (Section 1.1). -/
theorem isPeriod_iff_shift_eq {A : Type*} (c : Configuration A) (h : Lattice) :
    IsPeriod c h ↔ shift h c = c := by
  exact ⟨fun hc => funext hc, fun hc => congrFun hc⟩

/-- The zero vector fixes every configuration (Section 1.1). -/
theorem IsPeriod.zero {A : Type*} (c : Configuration A) : IsPeriod c 0 := by
  intro z
  simp

/-- The sum of two periods is a period (Section 1.1). -/
theorem IsPeriod.add {A : Type*} {c : Configuration A} {h t : Lattice}
    (hh : IsPeriod c h) (ht : IsPeriod c t) : IsPeriod c (h + t) := by
  intro z
  rw [← add_assoc, ht, hh]

/-- Reversing a period preserves periodicity (Section 1.1). -/
theorem IsPeriod.neg {A : Type*} {c : Configuration A} {h : Lattice}
    (hh : IsPeriod c h) : IsPeriod c (-h) := by
  intro z
  simpa using (hh (z + -h)).symm

/-- Every natural multiple of a period is a period (Section 1.1). -/
theorem IsPeriod.nsmul {A : Type*} {c : Configuration A} {h : Lattice}
    (hh : IsPeriod c h) (n : ℕ) : IsPeriod c (n • h) := by
  induction n with
  | zero => simpa using IsPeriod.zero c
  | succ n ih =>
    rw [add_nsmul, one_nsmul]
    exact ih.add hh

/-- Every integer multiple of a period is a period (Section 1.1). -/
theorem IsPeriod.zsmul {A : Type*} {c : Configuration A} {h : Lattice}
    (hh : IsPeriod c h) (n : ℤ) : IsPeriod c (n • h) := by
  cases n with
  | ofNat n =>
    change IsPeriod c ((n : ℤ) • h)
    rw [natCast_zsmul]
    exact hh.nsmul n
  | negSucc n =>
    change IsPeriod c (-((n + 1 : ℕ) : ℤ) • h)
    rw [neg_zsmul, natCast_zsmul]
    exact (hh.nsmul (n + 1)).neg

/-- A configuration and any translate have the same periods (Section 1.1). -/
theorem isPeriod_shift_iff {A : Type*} (c : Configuration A) (h t : Lattice) :
    IsPeriod (shift t c) h ↔ IsPeriod c h := by
  constructor
  · intro hp z
    simpa [shift, add_assoc, add_left_comm, add_comm] using hp (z - t)
  · intro hp z
    simpa [shift, add_assoc, add_left_comm, add_comm] using hp (z + t)

/-- Periodicity is invariant under translation (Section 1.1). -/
theorem periodic_shift_iff {A : Type*} (c : Configuration A) (t : Lattice) :
    Periodic (shift t c) ↔ Periodic c := by
  simp only [Periodic, isPeriod_shift_iff]

/-- Applying a function to a finite alphabet preserves finite range (Section 1.1). -/
theorem FiniteRange.map {A B : Type*} {c : Configuration A}
    (hc : FiniteRange c) (f : A → B) : FiniteRange (f ∘ c) := by
  simpa only [FiniteRange, Set.range_comp] using hc.image f

/-- Translations preserve finite range (Section 1.1). -/
theorem FiniteRange.shift {A : Type*} {c : Configuration A}
    (hc : FiniteRange c) (h : Lattice) : FiniteRange (shift h c) := by
  apply hc.subset
  rintro _ ⟨z, rfl⟩
  exact ⟨z + h, rfl⟩

/-- A configuration over a finite alphabet has finite range (Section 1.1). -/
theorem finiteRange_of_finite {A : Type*} [Finite A] (c : Configuration A) :
    FiniteRange c := Set.toFinite _

/-- Injective alphabet labels preserve each period vector (Section 1.1). -/
theorem isPeriod_map_iff {A B : Type*} (c : Configuration A) {f : A → B}
    (hf : Function.Injective f) (h : Lattice) :
    IsPeriod (f ∘ c) h ↔ IsPeriod c h := by
  simp only [IsPeriod, Function.comp_apply, hf.eq_iff]

/-- Injective alphabet labels preserve periodicity (Section 1.1). -/
theorem periodic_map_iff {A B : Type*} (c : Configuration A) {f : A → B}
    (hf : Function.Injective f) : Periodic (f ∘ c) ↔ Periodic c := by
  simp only [Periodic, isPeriod_map_iff c hf]

/-- The pointwise formula for `Δₕc` in Section 1.1. -/
@[simp] theorem difference_apply {A : Type*} [AddCommGroup A]
    (h : Lattice) (c : Configuration A) (z) :
    difference h c z = c (z + h) - c z := rfl

/-- Vanishing of `Δₕc` is exactly the period condition (Section 1.1). -/
theorem difference_eq_zero_iff {A : Type*} [AddCommGroup A]
    (h : Lattice) (c : Configuration A) : difference h c = 0 ↔ IsPeriod c h := by
  simp only [funext_iff, difference_apply, Pi.zero_apply, sub_eq_zero, IsPeriod]

/-- Difference operators commute (Section 1.1). -/
theorem difference_comm {A : Type*} [AddCommGroup A]
    (h t : Lattice) (c : Configuration A) :
    difference h (difference t c) = difference t (difference h c) := by
  funext z
  simp only [difference_apply]
  rw [show z + h + t = z + t + h by abel]
  abel

end Nivat
