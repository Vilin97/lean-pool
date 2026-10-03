/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/
module

public import LeanPool.FourAP.Binary
public import LeanPool.FourAP.Completion
public import Mathlib.Data.Finset.Sort
public import Mathlib.Tactic.SplitIfs

/-!
# Finite safe words

This file formalizes the parity restrictions of `𝒞(P)` used in the Extension
Lemma, and Lemma 1 (reverse binary order is safe).
The two arithmetic-progression equations used below include both increasing
and decreasing progressions.
-/

public section

namespace FourAP

/-- The words `P₀` and `P₁` in the Extension Lemma: retain one parity and
rescale it by `2x+p ↦ x`. -/
def parityWord (p : ℕ) (P : List ℕ) : List ℕ :=
  P.filterMap (fun n => if n % 2 = p then some (n / 2) else none)

/-- Parity restriction respects the order of concatenated words, as used
when the proof forms the extension `Q = P O E`. -/
@[simp] theorem parityWord_append (p : ℕ) (P Q : List ℕ) :
    parityWord p (P ++ Q) = parityWord p P ++ parityWord p Q := by
  simp [parityWord]

/-- The recursive description of the parity-restricted word in Lemma 2. -/
@[simp] theorem parityWord_cons (p n : ℕ) (P : List ℕ) :
    parityWord p (n :: P) =
      if n % 2 = p then n / 2 :: parityWord p P else parityWord p P := by
  by_cases h : n % 2 = p <;> simp [parityWord, h]

/-- A number occurs in `Pₚ` exactly when its original, unscaled value occurs
in `P`. This is the membership assertion implicit in the parity split. -/
theorem mem_parityWord_iff {p x : ℕ} (hp : p < 2) (P : List ℕ) :
    x ∈ parityWord p P ↔ 2 * x + p ∈ P := by
  induction P with
  | nil => simp [parityWord]
  | cons n P ih =>
    rw [parityWord_cons]
    by_cases hn : n % 2 = p
    · simp only [hn, ↓reduceIte, List.mem_cons, ih]
      have hx : x = n / 2 ↔ 2 * x + p = n := by omega
      exact or_congr hx Iff.rfl
    · have hne : 2 * x + p ≠ n := by omega
      simp [hn, ih, hne]

/-- Rescaling one parity preserves distinctness; hence the parity words
appearing in the Extension Lemma are again words without repetitions. -/
theorem nodup_parityWord {p : ℕ} (hp : p < 2) {P : List ℕ}
    (hP : P.Nodup) : (parityWord p P).Nodup := by
  induction P with
  | nil => simp [parityWord]
  | cons n P ih =>
    obtain ⟨hn, hP⟩ := List.nodup_cons.mp hP
    rw [parityWord_cons]
    split_ifs with hnp
    · apply List.nodup_cons.mpr
      refine ⟨?_, ih hP⟩
      intro h
      have hh := (mem_parityWord_iff hp P).mp h
      have heq : 2 * (n / 2) + p = n := by omega
      exact hn (heq ▸ hh)
    · exact ih hP

/-- If both parity words have distinct entries, the original word does too.
This is the distinctness argument for the new word `Q = P O E` in Lemma 2. -/
theorem nodup_of_parityWord {Q : List ℕ}
    (h0 : (parityWord 0 Q).Nodup) (h1 : (parityWord 1 Q).Nodup) : Q.Nodup := by
  induction Q with
  | nil => simp
  | cons n Q ih =>
    by_cases hn : n % 2 = 0
    · have hn1 : n % 2 ≠ 1 := by omega
      rw [parityWord_cons, ite_eq_left hn] at h0
      rw [parityWord_cons, ite_eq_right hn1] at h1
      obtain ⟨hn0, h0⟩ := List.nodup_cons.mp h0
      apply List.nodup_cons.mpr
      refine ⟨?_, ih h0 h1⟩
      intro hmem
      apply hn0
      apply (mem_parityWord_iff (by omega : 0 < 2) Q).mpr
      have heq : 2 * (n / 2) + 0 = n := by omega
      rwa [heq]
    · have hn1 : n % 2 = 1 := by omega
      rw [parityWord_cons, ite_eq_right hn] at h0
      rw [parityWord_cons, ite_eq_left hn1] at h1
      obtain ⟨hn1', h1⟩ := List.nodup_cons.mp h1
      apply List.nodup_cons.mpr
      refine ⟨?_, ih h0 h1⟩
      intro hmem
      apply hn1'
      apply (mem_parityWord_iff (by omega : 1 < 2) Q).mpr
      have heq : 2 * (n / 2) + 1 = n := by omega
      rwa [heq]

/-- Restricting `𝒞(P)` to parity `p` and rescaling gives exactly `𝒞(Pₚ)`.
This formalizes the self-similarity argument in the first inductive paragraph
of the Extension Lemma. -/
theorem completion_parity {p : ℕ} (hp : p < 2) (P : List ℕ) (a b : ℕ) :
    Completion bits P (2 * a + p) (2 * b + p) ↔
      Completion bits (parityWord p P) a b := by
  induction P with
  | nil => simp [Completion, parityWord, bits_parity a b p hp]
  | cons n P ih =>
    rw [parityWord_cons]
    by_cases hn : n % 2 = p
    · rw [ite_eq_left hn, completion_cons, completion_cons]
      have ha : 2 * a + p = n ↔ a = n / 2 := by omega
      have hb : 2 * b + p = n ↔ b = n / 2 := by omega
      simp only [Ne, ha, hb, ih]
    · have ha : 2 * a + p ≠ n := by omega
      have hb : 2 * b + p ≠ n := by omega
      simp [hn, completion_cons, ha, hb, ih]

/-- The parity words of a safe word are safe (Extension Lemma, paragraph
beginning “Both `P₀` and `P₁` are safe”). -/
theorem safe_parity {p : ℕ} (hp : p < 2) {P : List ℕ}
    (hP : Safe bits P) : Safe bits (parityWord p P) := by
  refine ⟨nodup_parityWord hp hP.1, ?_⟩
  intro a b c d hap hab hbc hcd
  apply (hP.2 : APFree (Completion bits P)) (a := 2 * a + p) (b := 2 * b + p)
    (c := 2 * c + p) (d := 2 * d + p)
  · rcases hap with ⟨hne, h₁, h₂⟩
    exact ⟨by omega, by omega, by omega⟩
  · exact (completion_parity hp P a b).mpr hab
  · exact (completion_parity hp P b c).mpr hbc
  · exact (completion_parity hp P c d).mpr hcd

/-- Normalizing a word already rescaled into parity `p` recovers the original
word, as in the construction of the suffixes `E` and `O`. -/
@[simp] theorem parityWord_map_same {p : ℕ} (hp : p < 2) (P : List ℕ) :
    parityWord p (P.map (fun x => 2 * x + p)) = P := by
  induction P with
  | nil => simp [parityWord]
  | cons x P ih =>
    simp only [List.map_cons, parityWord_cons]
    have hmod : (2 * x + p) % 2 = p := by omega
    have hdiv : (2 * x + p) / 2 = x := by omega
    simp [hmod, hdiv, ih]

/-- Projecting a word of the other parity yields the empty word. This
justifies separating the new odd and even suffixes of `Q = P O E`. -/
@[simp] theorem parityWord_map_other {p q : ℕ} (hq : q < 2)
    (hpq : p ≠ q) (P : List ℕ) :
    parityWord p (P.map (fun x => 2 * x + q)) = [] := by
  induction P with
  | nil => simp [parityWord]
  | cons x P ih =>
    simp only [List.map_cons, parityWord_cons]
    have hmod : (2 * x + q) % 2 ≠ p := by omega
    rw [ite_eq_right hmod]
    exact ih

/-- Inside a word listed in reverse `◁` order, an earlier entry is later in
`◁`. This is the first comparison used in the two-prefix-term case of Lemma 1. -/
theorem reverse_bits_of_completion {P : List ℕ}
    (hs : P.Pairwise (fun a b => bits b a)) {a b : ℕ}
    (hab : Completion bits P a b) (hb : b ∈ P) : bits b a := by
  have hij : P.idxOf a < P.idxOf b := by
    rcases hab with h | ⟨_, hn, _⟩
    · exact h
    · exact (hn hb).elim
  have hj := List.idxOf_lt_length_of_mem hb
  have hi := hij.trans hj
  have h := (List.pairwise_iff_getElem.mp hs) (P.idxOf a) (P.idxOf b) hi hj hij
  simpa only [List.getElem_idxOf] using h

/-- **Lemma 1 of the paper.** Every finite word of distinct integers listed in
reverse `◁` order is safe. The proof separates the cases of at least three,
exactly two, and at most one progression term in the finite prefix. -/
theorem safe_of_reverse_pairwise {P : List ℕ} (hn : P.Nodup)
    (hs : P.Pairwise (fun a b => bits b a)) : Safe bits P := by
  refine ⟨hn, ?_⟩
  intro a b c d hap hab hbc hcd
  by_cases hc : c ∈ P
  · -- At least three terms lie in the reverse-ordered prefix.
    have hb := completion_mem_left hbc hc
    exact bits_dual_no_three hap.2.1
      ⟨reverse_bits_of_completion hs hab hb, reverse_bits_of_completion hs hbc hc⟩
  · have hd : d ∉ P := fun hd => hc (completion_mem_left hcd hd)
    have hcd' := (completion_of_notMem hc hd).mp hcd
    by_cases hb : b ∈ P
    · -- Exactly two terms lie in the prefix: equation (1) gives a contradiction.
      have hba := reverse_bits_of_completion hs hab hb
      exact bits_asymm hba ((bits_pairs hap).mpr hcd')
    · -- At most one term lies in the prefix, leaving a forbidden 3AP in the tail.
      have hbc' := (completion_of_notMem hb hc).mp hbc
      exact bits_no_three_of_eq hap.2.2 ⟨hbc', hcd'⟩

/-- The non-strict reverse of `◁`, used solely for sorting the finite set in
Lemma 1 and in the base case of the Extension Lemma. -/
@[expose] def reverseBitsLE (a b : ℕ) : Prop := a = b ∨ bits b a

/-- The finite sorting relation in Lemma 1 has a computable comparison. -/
instance reverseBitsLEDecidable : DecidableRel reverseBitsLE :=
  fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Transitivity permits sorting in the reverse order used in Lemma 1. -/
instance reverseBitsLETrans : IsTrans ℕ reverseBitsLE where
  trans a b c hab hbc := by
    rcases hab with rfl | hab
    · exact hbc
    rcases hbc with rfl | hbc
    · exact Or.inr hab
    · exact Or.inr (bits_trans hbc hab)

/-- Antisymmetry makes the reverse listing of a finite set unique. -/
instance reverseBitsLEAntisymm : Std.Antisymm reverseBitsLE where
  antisymm a b hab hba := by
    rcases hab with h | hab
    · exact h
    rcases hba with h | hba
    · exact h.symm
    · exact (bits_asymm hab hba).elim

/-- Any two integers can be compared when forming the reverse listing. -/
instance reverseBitsLETotal : Std.Total reverseBitsLE where
  total a b := by
    by_cases h : a = b
    · exact Or.inl (Or.inl h)
    · rcases bits_total h with h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inl (Or.inr h)

/-- List a finite set in reverse `◁` order, exactly as prescribed in Lemma 1.
This definition is computable, using mathlib's finite-set merge sort. -/
@[expose] def reverseWord (T : Finset ℕ) : List ℕ := T.sort reverseBitsLE

/-- The reverse listing contains each and only each prescribed entry. -/
@[simp] theorem mem_reverseWord {T : Finset ℕ} {x : ℕ} :
    x ∈ reverseWord T ↔ x ∈ T := Finset.mem_sort reverseBitsLE

/-- The reverse listing contains no repeated entry, as required of a word. -/
theorem reverseWord_nodup (T : Finset ℕ) : (reverseWord T).Nodup :=
  Finset.sort_nodup T reverseBitsLE

/-- The reverse listing has the strict reverse order required in Lemma 1. -/
theorem reverseWord_pairwise (T : Finset ℕ) :
    (reverseWord T).Pairwise (fun a b => bits b a) := by
  apply List.Pairwise.imp₂ (R := reverseBitsLE) (S := (· ≠ ·))
    (fun _ _ h hne => h.resolve_left hne)
  · exact Finset.pairwise_sort T reverseBitsLE
  · exact reverseWord_nodup T

/-- Lemma 1 specialized to the canonical reverse listing of a finite set. -/
theorem safe_reverseWord (T : Finset ℕ) : Safe bits (reverseWord T) :=
  safe_of_reverse_pairwise (reverseWord_nodup T) (reverseWord_pairwise T)

/-- If zero belongs to a finite set, its reverse binary listing begins with
zero. This is the sorting observation in the base case of Lemma 2. -/
theorem reverseWord_zero_first {T : Finset ℕ} (h0 : 0 ∈ T) :
    reverseWord T = 0 :: reverseWord (T.erase 0) := by
  have hsort := Finset.sort_insert (s := T.erase 0) reverseBitsLE
    (a := 0) (fun b hb => Or.inr (bits_zero (Finset.mem_erase.mp hb).1))
    (by simp : 0 ∉ T.erase 0)
  simpa only [Finset.insert_erase h0, reverseWord] using hsort

/-- Canonical form of the base-case extension in Lemma 2. Sorting `P ∪ T`
in reverse binary order preserves the old prefix whenever all its entries
are zero. This also connects the executable construction to the proof. -/
theorem reverseWord_union_prefix {P : List ℕ} (hP : P.Nodup)
    (hzero : ∀ x ∈ P, x = 0) (T : Finset ℕ) :
    P.IsPrefix (reverseWord (P.toFinset ∪ T)) := by
  cases P with
  | nil => exact List.nil_prefix
  | cons x P =>
    have hx : x = 0 := hzero x (by simp)
    subst x
    have hnil : P = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro x hx
      have hx0 : x = 0 := hzero x (by simp [hx])
      subst x
      exact (List.nodup_cons.mp hP).1 hx
    subst P
    rw [reverseWord_zero_first (by simp : 0 ∈ ([0] : List ℕ).toFinset ∪ T)]
    exact ⟨reverseWord ((([0] : List ℕ).toFinset ∪ T).erase 0), rfl⟩


end FourAP
