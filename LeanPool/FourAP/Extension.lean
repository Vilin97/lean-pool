/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/
module

public import LeanPool.FourAP.Glue

/-!
# Lemma 2: the executable extension of a safe word

This file formalizes the Extension Lemma in the paper
“A 4AP-free permutation of the positive integers”. The recursive function
`extendAlgorithm` follows the choices in the paper's proof: extend the even
part first, then extend the odd part to cover the required initial interval,
and append the odd suffix before the even suffix. In the base case, list the
union of the old word and the target set in reverse binary order.

The recursion terminates because each parity projection has a strictly smaller
largest entry. `extendAlgorithm_spec` proves its safety, prefix preservation,
and target coverage in one induction. The paper's existential Lemma 2 is the
immediate corollary `safe_extend`.
-/

public section

namespace FourAP

/-- The normalized parity-`p` elements of the target set in Lemma 2.
For `p = 0` this divides the even targets by two; for `p = 1` it sends an
odd target `t` to `(t-1)/2`, equivalently `t/2` in natural-number division. -/
def parityTarget (p : ℕ) (T : Finset ℕ) : Finset ℕ :=
  (T.filter (fun t => t % 2 = p)).image (fun t => t / 2)

/-- Every target of the selected parity contributes its normalized value,
as required by the recursive calls in Lemma 2. -/
theorem div_mem_parityTarget {p t : ℕ} {T : Finset ℕ}
    (ht : t ∈ T) (hp : t % 2 = p) : t / 2 ∈ parityTarget p T :=
  Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨ht, hp⟩, rfl⟩

/-- The induction measure in Lemma 2 decreases after either parity
projection, provided the old word has a positive largest entry. -/
theorem parityWord_max_lt {P : List ℕ} {p : ℕ} (hp : p < 2)
    (hm : 0 < P.toFinset.sup id) :
    (parityWord p P).toFinset.sup id < P.toFinset.sup id := by
  apply (Finset.sup_lt_iff hm).mpr
  intro x hx
  have hxP : 2 * x + p ∈ P :=
    (mem_parityWord_iff hp P).mp (by simpa using hx)
  have hle : 2 * x + p ≤ P.toFinset.sup id :=
    Finset.le_sup (f := id) (by simpa using hxP)
  dsimp
  omega

/-- An insertion-sort implementation of the reverse listing in Lemma 1.
It is extensionally identical to `reverseWord`; using structural insertion
sort also allows the displayed numerical example to reduce in Lean's kernel. -/
@[expose] def reverseWordExecutable (T : Finset ℕ) : List ℕ :=
  Quot.liftOn T.val (List.insertionSort reverseBitsLE) fun l₁ l₂ h =>
    ((List.perm_insertionSort reverseBitsLE l₁).trans
      (h.trans (List.perm_insertionSort reverseBitsLE l₂).symm)).eq_of_pairwise'
        (List.pairwise_insertionSort reverseBitsLE l₁)
        (List.pairwise_insertionSort reverseBitsLE l₂)

/-- The executable reverse listing is the same canonical word as in Lemma 1;
the choice of sorting algorithm does not change the paper's construction. -/
@[simp] theorem reverseWordExecutable_eq (T : Finset ℕ) :
    reverseWordExecutable T = reverseWord T := by
  rcases T with ⟨s, hs⟩
  induction s using Quot.inductionOn with
  | h l => exact (List.mergeSort_eq_insertionSort reverseBitsLE l).symm

/-- An executable form of **Lemma 2 (Extension)**, using exactly the choices
in its proof. `E` and `O` are normalized suffixes, so the final maps restore
their original parity. In the base case the union of prefix and target is
listed without repetition in reverse `◁` order, as in Lemma 1. -/
def extendAlgorithm (P : List ℕ) (T : Finset ℕ) : List ℕ :=
  if _hm : P.toFinset.sup id = 0 then reverseWordExecutable (P.toFinset ∪ T)
  else
    let P₀ := parityWord 0 P
    let P₁ := parityWord 1 P
    let Q₀ := extendAlgorithm P₀ (parityTarget 0 T)
    let E := Q₀.drop P₀.length
    let h := (E.map (fun x => 2 * x + 0)).toFinset.sup id
    let Q₁ := extendAlgorithm P₁ (parityTarget 1 T ∪ Finset.range h)
    let O := Q₁.drop P₁.length
    P ++ O.map (fun x => 2 * x + 1) ++ E.map (fun x => 2 * x + 0)
termination_by P.toFinset.sup id
decreasing_by
  · exact parityWord_max_lt (by decide) (by omega)
  · exact parityWord_max_lt (by decide) (by omega)

/-- The specification asserted in Lemma 2: a safe extension, preserving the
old prefix and containing every prescribed target. This predicate packages
the three conclusions without hiding the actual output word. -/
@[expose] def ExtensionResult (P : List ℕ) (T : Finset ℕ) (Q : List ℕ) : Prop :=
  Safe bits Q ∧ P.IsPrefix Q ∧ ∀ t ∈ T, t ∈ Q

/-- Splitting off the newly appended suffix recovers the entire extension.
This is the list identity used when the paper introduces `E` and `O`. -/
theorem prefix_append_drop {P Q : List ℕ} (h : P.IsPrefix Q) :
    P ++ Q.drop P.length = Q := by
  rw [List.prefix_iff_eq_take.mp h]
  simpa only [List.length_take, min_eq_left h.length_le] using
    List.take_append_drop P.length Q

/-- Correctness of the executable Extension Lemma. This follows the paper's
induction literally; `safe_splice` contains its odd-before-even argument. -/
theorem extendAlgorithm_spec (P : List ℕ) (T : Finset ℕ) (hP : Safe bits P) :
    ExtensionResult P T (extendAlgorithm P T) := by
  rw [extendAlgorithm]
  split_ifs with hm
  · rw [reverseWordExecutable_eq]
    refine ⟨safe_reverseWord _, reverseWord_union_prefix hP.1 ?_ T, ?_⟩
    · intro x hx
      have hxle : x ≤ P.toFinset.sup id :=
        Finset.le_sup (f := id) (by simpa using hx)
      omega
    · intro t ht
      exact mem_reverseWord.mpr (Finset.mem_union_right _ ht)
  · let P₀ := parityWord 0 P
    let P₁ := parityWord 1 P
    let Q₀ := extendAlgorithm P₀ (parityTarget 0 T)
    let E := Q₀.drop P₀.length
    let h := (E.map (fun x => 2 * x + 0)).toFinset.sup id
    let Q₁ := extendAlgorithm P₁ (parityTarget 1 T ∪ Finset.range h)
    let O := Q₁.drop P₁.length
    have h₀ := extendAlgorithm_spec P₀ (parityTarget 0 T) (safe_parity (by decide) hP)
    have h₁ := extendAlgorithm_spec P₁ (parityTarget 1 T ∪ Finset.range h)
      (safe_parity (by decide) hP)
    change ExtensionResult P₀ (parityTarget 0 T) Q₀ at h₀
    change ExtensionResult P₁ (parityTarget 1 T ∪ Finset.range h) Q₁ at h₁
    have heq₀ : P₀ ++ E = Q₀ := prefix_append_drop h₀.2.1
    have heq₁ : P₁ ++ O = Q₁ := prefix_append_drop h₁.2.1
    change ExtensionResult P T
      (P ++ O.map (fun x => 2 * x + 1) ++ E.map (fun x => 2 * x + 0))
    refine ⟨?_, ?_, ?_⟩
    · apply safe_splice (h := h) hP
      · change Safe bits (P₀ ++ E)
        rw [heq₀]
        exact h₀.1
      · change Safe bits (P₁ ++ O)
        rw [heq₁]
        exact h₁.1
      · intro e he
        have he' : 2 * e + 0 ∈ E.map (fun x => 2 * x + 0) := List.mem_map.mpr ⟨e, he, rfl⟩
        exact Finset.le_sup (f := id) (by simpa using he')
      · intro k hk
        rw [heq₁]
        exact h₁.2.2 k (Finset.mem_union_right _ (Finset.mem_range.mpr hk))
    · exact ⟨O.map (fun x => 2 * x + 1) ++ E.map (fun x => 2 * x + 0),
        (List.append_assoc ..).symm⟩
    · intro t ht
      have hp : t % 2 = 0 ∨ t % 2 = 1 := by omega
      rcases hp with hp | hp
      · have ht₀ := h₀.2.2 (t / 2) (div_mem_parityTarget ht hp)
        rw [← heq₀] at ht₀
        rcases List.mem_append.mp ht₀ with htP | htE
        · have hmem := (mem_parityWord_iff (by decide : 0 < 2) P).mp htP
          have heq : 2 * (t / 2) + 0 = t := by omega
          exact List.mem_append_left _ (List.mem_append_left _ (heq ▸ hmem))
        · apply List.mem_append_right
          exact List.mem_map.mpr ⟨t / 2, htE, by omega⟩
      · have ht₁ := h₁.2.2 (t / 2)
          (Finset.mem_union_left _ (div_mem_parityTarget ht hp))
        rw [← heq₁] at ht₁
        rcases List.mem_append.mp ht₁ with htP | htO
        · have hmem := (mem_parityWord_iff (by decide : 1 < 2) P).mp htP
          have heq : 2 * (t / 2) + 1 = t := by omega
          exact List.mem_append_left _ (List.mem_append_left _ (heq ▸ hmem))
        · apply List.mem_append_left
          apply List.mem_append_right
          exact List.mem_map.mpr ⟨t / 2, htO, by omega⟩
termination_by P.toFinset.sup id
decreasing_by
  · exact parityWord_max_lt (by decide) (by omega)
  · exact parityWord_max_lt (by decide) (by omega)

/-- **Lemma 2 (Extension) of the paper.** Every safe finite word is an initial
segment of a safe finite word containing any prescribed finite target set.
The witness is the executable word constructed and verified above. -/
theorem safe_extend (P : List ℕ) (hP : Safe bits P) (T : Finset ℕ) :
    ∃ Q, Safe bits Q ∧ P.IsPrefix Q ∧ ∀ t ∈ T, t ∈ Q :=
  ⟨extendAlgorithm P T, extendAlgorithm_spec P T hP⟩

end FourAP
