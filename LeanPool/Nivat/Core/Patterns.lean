/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

import LeanPool.Nivat.Core.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval

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
# Finite patterns and rectangle complexity

Section 1 and the notation in Section 1.1 of `paper/nivat.tex`.

`patterns` is the range of the restriction map over every integer translation.
The basic API proves finiteness, restriction surjectivity, monotonicity and
invariance under translations and injective relabeling. Unique extension is
the counting step used in Lemma 5.5 (`lem:boundary-window`).
-/

namespace Nivat

/-- The window `Rₘ,ₙ = {0, …, m-1} × {0, …, n-1}` from Section 1. -/
def rectangle (m n : ℕ) : Finset Lattice :=
  (Finset.Ico (0 : ℤ) (m : ℤ)).product (Finset.Ico (0 : ℤ) (n : ℤ))

/-- Coordinate inequalities describing the rectangle of Section 1. -/
@[simp] theorem mem_rectangle (z : Lattice) (m n : ℕ) :
    z ∈ rectangle m n ↔ 0 ≤ z.1 ∧ z.1 < m ∧ 0 ≤ z.2 ∧ z.2 < n := by
  simp [rectangle, and_assoc]

/-- The rectangle `Rₘ,ₙ` has `m * n` sites (Section 1). -/
@[simp] theorem card_rectangle (m n : ℕ) : (rectangle m n).card = m * n := by
  simp [rectangle, Int.card_Ico]

/-- The restriction of `Tᵘc` to `D`, indexed by the sites of `D` (Section 1). -/
def patternAt {A : Type*} (c : Configuration A) (D : Finset Lattice) (u : Lattice) :
    D → A := fun z => c (z.1 + u)

/-- The set `Pat_c(D)` of distinct restrictions over all lattice translations (Section 1). -/
def patterns {A : Type*} (c : Configuration A) (D : Finset Lattice) : Set (D → A) :=
  Set.range (patternAt c D)

/-- The pattern count `P_c(D)` from Section 1.
For finite-range configurations, `patterns_finite` ensures that natural set cardinality
counts this finite set; repeated occurrences contribute only one pattern. -/
noncomputable def complexity {A : Type*} (c : Configuration A) (D : Finset Lattice) : ℕ :=
  (patterns c D).ncard

/-- The signed discrepancy `δ_c(D) = P_c(D) - |D|` from Section 1.1. -/
noncomputable def discrepancy {A : Type*} (c : Configuration A) (D : Finset Lattice) : ℤ :=
  (complexity c D : ℤ) - (D.card : ℤ)

/-- The origin supplies an occurring pattern on every window (Section 1.1). -/
theorem patterns_nonempty {A : Type*} (c : Configuration A) (D : Finset Lattice) :
    (patterns c D).Nonempty := ⟨patternAt c D 0, 0, rfl⟩

/-- A finite alphabet gives finitely many patterns on a finite window (Section 1.1). -/
theorem patterns_finite {A : Type*} {c : Configuration A} (hc : FiniteRange c)
    (D : Finset Lattice) : (patterns c D).Finite := by
  apply (Set.Finite.pi' (fun _ : D => hc)).subset
  rintro _ ⟨u, rfl⟩ z
  exact ⟨z.1 + u, rfl⟩

/-- Every finite window has at least one occurring pattern (Section 1.1). -/
theorem complexity_pos {A : Type*} {c : Configuration A} (hc : FiniteRange c)
    (D : Finset Lattice) : 0 < complexity c D :=
  (Set.ncard_pos (patterns_finite hc D)).2 (patterns_nonempty c D)

/-- The empty window has exactly one pattern (Section 1.1). -/
@[simp] theorem complexity_empty {A : Type*} (c : Configuration A) :
    complexity c ∅ = 1 := by
  apply Set.ncard_eq_one.mpr
  refine ⟨patternAt c ∅ 0, ?_⟩
  ext p
  constructor
  · intro _
    exact Set.mem_singleton_iff.mpr (Subsingleton.elim _ _)
  · rintro rfl
    exact ⟨0, rfl⟩

/-- Translations of the configuration preserve its pattern sets (Section 1.1). -/
theorem patterns_shift {A : Type*} (c : Configuration A) (D : Finset Lattice)
    (h : Lattice) : patterns (shift h c) D = patterns c D := by
  ext p
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u + h, by ext z; simp [patternAt, shift, add_assoc]⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u - h, by ext z; simp [patternAt, shift, sub_eq_add_neg, add_assoc]⟩

/-- Translations of the configuration preserve complexity (Section 1.1). -/
@[simp] theorem complexity_shift {A : Type*} (c : Configuration A) (D : Finset Lattice)
    (h : Lattice) : complexity (shift h c) D = complexity c D := by
  simp only [complexity, patterns_shift]

/-- Restriction of a pattern to a smaller window (Section 1.1). -/
def restrictPattern {A : Type*} {C D : Finset Lattice} (hCD : C ⊆ D)
    (p : D → A) : C → A := fun z => p ⟨z.1, hCD z.2⟩

/-- Restriction maps onto all occurring patterns on the smaller window (Section 1.1). -/
theorem restrict_patterns {A : Type*} (c : Configuration A) {C D : Finset Lattice}
    (hCD : C ⊆ D) : restrictPattern hCD '' patterns c D = patterns c C := by
  ext p
  constructor
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨patternAt c D u, ⟨u, rfl⟩, rfl⟩

/-- Pattern complexity is monotone under inclusion of windows (Section 1.1). -/
theorem complexity_mono {A : Type*} {c : Configuration A} (hc : FiniteRange c)
    {C D : Finset Lattice} (hCD : C ⊆ D) : complexity c C ≤ complexity c D := by
  unfold complexity
  rw [← restrict_patterns c hCD]
  exact Set.ncard_image_le (patterns_finite hc D)

/-- The effect of relabeling symbols on the occurring patterns (Section 1.1). -/
theorem patterns_map {A B : Type*} (c : Configuration A) (f : A → B)
    (D : Finset Lattice) : patterns (f ∘ c) D = (fun p => f ∘ p) '' patterns c D := by
  ext p
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨patternAt c D u, ⟨u, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, rfl⟩

/-- Injective alphabet labeling preserves every finite-window complexity (Section 1.1). -/
theorem complexity_map {A B : Type*} (c : Configuration A) {f : A → B}
    (hf : Function.Injective f) (D : Finset Lattice) :
    complexity (f ∘ c) D = complexity c D := by
  unfold complexity
  rw [patterns_map]
  apply Set.ncard_image_of_injective
  intro p q hpq
  funext z
  exact hf (congrFun hpq z)

/-- Equal pattern counts imply unique extension between the two windows.
This is the restriction-bijection step in Lemma 5.5 (`lem:boundary-window`). -/
theorem equal_complexity_unique_extension {A : Type*} {c : Configuration A}
    (hc : FiniteRange c) {C D : Finset Lattice} (hCD : C ⊆ D)
    (hcard : complexity c C = complexity c D) {u v : Lattice}
    (huv : patternAt c C u = patternAt c C v) : patternAt c D u = patternAt c D v := by
  have hi : Set.InjOn (restrictPattern hCD) (patterns c D) := by
    apply Set.injOn_of_ncard_image_eq _ (patterns_finite hc D)
    rw [restrict_patterns]
    exact hcard
  exact hi ⟨u, rfl⟩ ⟨v, rfl⟩ huv

/-- Occurrence of every finite origin pattern implies occurrence at every translate.
This implements the finite-pattern inheritance used in Theorem 2.2 (`thm:descent`). -/
theorem patternAt_mem_of_language {A : Type*} {x c : Configuration A}
    (hx : ∀ D : Finset Lattice, patternAt x D 0 ∈ patterns c D)
    (D : Finset Lattice) (u : Lattice) : patternAt x D u ∈ patterns c D := by
  classical
  let E := D.image (fun z => z + u)
  obtain ⟨v, hv⟩ := hx E
  refine ⟨u + v, ?_⟩
  funext z
  have hz : z.1 + u ∈ E := Finset.mem_image.mpr ⟨z.1, z.2, rfl⟩
  have h := congrFun hv ⟨z.1 + u, hz⟩
  simpa only [patternAt, add_zero, add_assoc] using h

/-- Translating the window preserves its complexity (Section 1.1). -/
theorem complexity_translate_window {A : Type*} (c : Configuration A)
    (D : Finset Lattice) (u : Lattice) :
    complexity c (D.image (fun z => z + u)) = complexity c D := by
  classical
  apply Set.ncard_congr
    (fun p _ => fun z : D => p ⟨z.1 + u, Finset.mem_image.mpr ⟨z.1, z.2, rfl⟩⟩)
  · rintro p ⟨v, rfl⟩
    exact ⟨u + v, by funext z; simp only [patternAt, add_assoc]⟩
  · intro p q _ _ hpq
    funext z
    obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp z.2
    have h := congrFun hpq ⟨w, hw⟩
    convert h using 1 <;> congr 1 <;> exact Subtype.ext heq.symm
  · rintro p ⟨v, rfl⟩
    refine ⟨patternAt c (D.image (fun z => z + u)) (v - u), ⟨v - u, rfl⟩, ?_⟩
    funext z
    simp [patternAt, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

end Nivat
