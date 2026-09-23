/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/
module

public import LeanPool.FourAP.Words
public import LeanPool.FourAP.Splice

/-!
# Joining the odd and even extensions

This file formalizes the middle part of the proof of Lemma 2 in the paper
“A 4AP-free permutation of the positive integers”: after extending the two
parity words, put the new odd entries before the new even entries.

The suffixes `O` and `E` in the statements below are normalized: their entries
are rescaled by `x ↦ 2x+1` and `x ↦ 2x` when appended to the old word `P`.
The guard on the odd target set is exactly the paper's requirement that all
normalized odd entries below `h` have been included.
-/

@[expose] public section

namespace FourAP

/-- Putting further entries after a finite word preserves the fact that each
entry of that word precedes each entry outside it.  This is the comparison
between the new odd block and the new even block in Lemma 2. -/
theorem completion_append_before {R : ℕ → ℕ → Prop} {A B : List ℕ}
    {y x : ℕ} (hy : y ∈ A) (hx : x ∉ A) : Completion R (A ++ B) y x := by
  apply Or.inl
  rw [List.idxOf_append, List.idxOf_append, ite_eq_left hy, ite_eq_right hx]
  have := List.idxOf_lt_length_of_mem hy
  omega

/-- **Lemma 2, construction of `Q = P O E` and its safety.**

The two recursive calls have already provided safe extensions of `P₀` and
`P₁`.  The even bound `h` determines how many odd entries must be included.
First we identify the parity restrictions of the new completion, then prove
the odd-before-even comparison displayed as equation (2) in the paper.
The final arithmetic-progression contradiction is `safe_of_parity_and_guard`.
-/
theorem safe_splice {P E O : List ℕ}
    (hP : Safe bits P)
    (hE : Safe bits (parityWord 0 P ++ E))
    (hO : Safe bits (parityWord 1 P ++ O))
    (h : ℕ) (hbound : ∀ e ∈ E, 2 * e ≤ h)
    (hcover : ∀ k < h, k ∈ parityWord 1 P ++ O) :
    Safe bits (P ++ O.map (fun x => 2 * x + 1) ++ E.map (fun x => 2 * x + 0)) := by
  let Q := P ++ O.map (fun x => 2 * x + 1) ++ E.map (fun x => 2 * x + 0)
  have h0 : parityWord 0 Q = parityWord 0 P ++ E := by
    simp only [Q, parityWord_append,
      parityWord_map_other (by decide : 1 < 2) (by decide : 0 ≠ 1),
      parityWord_map_same (by decide : 0 < 2), List.append_nil]
  have h1 : parityWord 1 Q = parityWord 1 P ++ O := by
    simp only [Q, parityWord_append,
      parityWord_map_same (by decide : 1 < 2),
      parityWord_map_other (by decide : 0 < 2) (by decide : 1 ≠ 0),
      List.append_nil]
  have hsafe (p : ℕ) (hp : p < 2) : Safe bits (parityWord p Q) := by
    have : p = 0 ∨ p = 1 := by omega
    rcases this with rfl | rfl
    · rwa [h0]
    · rwa [h1]
  apply safe_of_parity_and_guard hP
  · exact ⟨O.map (fun x => 2 * x + 1) ++ E.map (fun x => 2 * x + 0),
      (List.append_assoc ..).symm⟩
  · exact nodup_of_parityWord (hsafe 0 (by decide)).1 (hsafe 1 (by decide)).1
  · -- An even common difference keeps all four terms in one parity.
    intro a b c d hap hp hab hbc hcd
    let p := a % 2
    have hp2 : p < 2 := Nat.mod_lt _ (by decide)
    have ha : a = 2 * (a / 2) + p := by omega
    have hb : b = 2 * (b / 2) + p := by omega
    have hc : c = 2 * (c / 2) + p := by
      have := hap.2.1
      omega
    have hd : d = 2 * (d / 2) + p := by
      have := hap.2.2
      omega
    have hap' : IsAP4 (a / 2) (b / 2) (c / 2) (d / 2) := by
      rcases hap with ⟨hne, h₁, h₂⟩
      exact ⟨by omega, by omega, by omega⟩
    apply (hsafe p hp2).2 hap'
    · apply (completion_parity hp2 Q (a / 2) (b / 2)).mp
      simpa only [← ha, ← hb] using hab
    · apply (completion_parity hp2 Q (b / 2) (c / 2)).mp
      simpa only [← hb, ← hc] using hbc
    · apply (completion_parity hp2 Q (c / 2) (d / 2)).mp
      simpa only [← hc, ← hd] using hcd
  · -- Equation (2): an unplaced odd `y ≤ 2x` must precede an unplaced even `x`.
    intro x y hxP hyP hxEven hyOdd hyx
    have hxO : x ∉ O.map (fun z => 2 * z + 1) := by
      rintro hx
      obtain ⟨z, _, hz⟩ := List.mem_map.mp hx
      omega
    by_cases hxQ : x ∈ Q
    · -- If `x` is a new even entry, the odd target has already captured `y`.
      have hxE : x ∈ E.map (fun z => 2 * z + 0) := by
        simpa only [Q, List.mem_append, hxP, hxO, false_or] using hxQ
      obtain ⟨e, he, hex⟩ := List.mem_map.mp hxE
      have hxh : x ≤ h := by have := hbound e he; omega
      have hyrepr : 2 * (y / 2) + 1 = y := by omega
      have hymem := hcover (y / 2) (by omega)
      have hyO : y / 2 ∈ O := by
        rcases List.mem_append.mp hymem with hyold | hynew
        · have hyold' := (mem_parityWord_iff (by decide : 1 < 2) P).mp hyold
          exact (hyP (hyrepr ▸ hyold')).elim
        · exact hynew
      have hyMapped : y ∈ O.map (fun z => 2 * z + 1) :=
        List.mem_map.mpr ⟨y / 2, hyO, hyrepr⟩
      exact completion_append_before
        (List.mem_append_right P hyMapped)
        (by simpa only [List.mem_append, not_or] using And.intro hxP hxO)
    · -- An unused even entry follows all odd entries, both placed and unused.
      by_cases hyQ : y ∈ Q
      · exact completion_mem_notMem hyQ hxQ
      · apply (completion_of_notMem hyQ hxQ).mpr
        rw [bits_iff_of_diff_parity (by omega : y % 2 ≠ x % 2)]
        omega

end FourAP
