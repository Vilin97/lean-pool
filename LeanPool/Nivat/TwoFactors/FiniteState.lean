/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Convert

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
# Finite states, word complexity, and periodic forcing

Section 5.1 of `paper/nivat.tex`: Lemma 5.2 (`lem:finite-states`),
Corollary 5.3 (`cor:morse`), and Lemma 5.4 (`lem:forcing`). Bilaterality
makes the deterministic successor map on occurring states a permutation.
A complexity plateau supplies a finite-state presentation of a word; a periodic
parameter is handled by recording its phase together with the finite memory.
-/

public section

namespace Nivat.TwoFactors

/-- A finite-range bilateral sequence with a uniquely determined successor has a positive period
bounded by its number of occurring states. Bilaterality makes the successor map surjective
on those states. Lemma 5.2 (`lem:finite-states`). -/
theorem periodic_of_deterministic_successor_bounded {A : Type*} (s : ℤ → A)
    (hs : (Set.range s).Finite)
    (hdet : ∀ i j : ℤ, s i = s j → s (i + 1) = s (j + 1)) :
    ∃ p : ℕ, 0 < p ∧ p ≤ (Set.range s).ncard ∧ Function.Periodic s (p : ℤ) := by
  classical
  let : Fintype (Set.range s) := hs.fintype
  let t : ℤ → Set.range s := fun i => ⟨s i, i, rfl⟩
  let next : Set.range s → Set.range s := fun a => t (a.property.choose + 1)
  have hnext (i : ℤ) : next (t i) = t (i + 1) := by
    apply Subtype.ext
    exact hdet _ _ (t i).property.choose_spec
  have hsurj : Function.Surjective next := by
    rintro ⟨a, i, rfl⟩
    refine ⟨t (i - 1), ?_⟩
    simpa only [sub_add_cancel] using hnext (i - 1)
  have hinj : Function.Injective next := Finite.injective_iff_surjective.mpr hsurj
  have hprev (i j : ℤ) (h : t i = t j) : t (i - 1) = t (j - 1) := by
    apply hinj
    simpa only [hnext, sub_add_cancel] using h
  have hiter (n : ℕ) (i : ℤ) : next^[n] (t i) = t (i + (n : ℤ)) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, hnext]
      congr 1
      push_cast
      ring
  let p := Function.minimalPeriod next (t 0)
  have hp : 0 < p :=
    Function.minimalPeriod_pos_of_mem_periodicPts (hinj.mem_periodicPts (t 0))
  have hzero : t (p : ℤ) = t 0 := by
    simpa only [hiter, zero_add] using
      (Function.isPeriodicPt_minimalPeriod next (t 0)).eq
  have hperiod (i : ℤ) : t (i + (p : ℤ)) = t i := by
    induction i using Int.induction_on with
    | zero => simpa using hzero
    | succ i hi =>
      simpa only [hnext, add_right_comm _ (1 : ℤ)] using congrArg next hi
    | pred i hi =>
      simpa only [sub_eq_add_neg, add_right_comm _ (-(1 : ℤ))] using hprev _ _ hi
  refine ⟨p, hp, ?_, fun i => congrArg Subtype.val (hperiod i)⟩
  simpa only [Set.ncard_eq_toFinset_card', Set.toFinset_card] using
    (Function.minimalPeriod_le_card (f := next) (x := t 0))

/-- A finite-range bilateral sequence whose next state is determined by its current state has a
positive period. Lemma 5.2 (`lem:finite-states`). -/
theorem periodic_of_deterministic_successor {A : Type*} (s : ℤ → A)
    (hs : (Set.range s).Finite)
    (hdet : ∀ i j : ℤ, s i = s j → s (i + 1) = s (j + 1)) :
    ∃ p : ℕ, 0 < p ∧ Function.Periodic s (p : ℤ) := by
  obtain ⟨p, hp, _, hper⟩ := periodic_of_deterministic_successor_bounded s hs hdet
  exact ⟨p, hp, hper⟩

/-- A uniquely determined predecessor gives a positive period bounded by the number of occurring
states, by reversing the integer index. Lemma 5.2 (`lem:finite-states`). -/
theorem periodic_of_deterministic_predecessor_bounded {A : Type*} (s : ℤ → A)
    (hs : (Set.range s).Finite)
    (hdet : ∀ i j : ℤ, s i = s j → s (i - 1) = s (j - 1)) :
    ∃ p : ℕ, 0 < p ∧ p ≤ (Set.range s).ncard ∧ Function.Periodic s (p : ℤ) := by
  have hrange : Set.range (fun i : ℤ => s (-i)) = Set.range s := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨-i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨-i, by simp⟩
  have hrev : ∀ i j : ℤ, s (-i) = s (-j) → s (-(i + 1)) = s (-(j + 1)) := by
    intro i j h
    simpa only [neg_add, sub_eq_add_neg] using hdet (-i) (-j) h
  obtain ⟨p, hp, hb, hper⟩ := periodic_of_deterministic_successor_bounded
    (fun i : ℤ => s (-i)) (hrange ▸ hs) hrev
  refine ⟨p, hp, hrange ▸ hb, ?_⟩
  intro i
  convert (hper (-i - (p : ℤ))).symm using 1 <;> congr 1 <;> ring

/-- A finite-range bilateral sequence with a uniquely determined predecessor is periodic; this
is the form applied to strip states. Lemma 5.2 (`lem:finite-states`). -/
theorem periodic_of_deterministic_predecessor {A : Type*} (s : ℤ → A)
    (hs : (Set.range s).Finite)
    (hdet : ∀ i j : ℤ, s i = s j → s (i - 1) = s (j - 1)) :
    ∃ p : ℕ, 0 < p ∧ Function.Periodic s (p : ℤ) := by
  obtain ⟨p, hp, _, hper⟩ := periodic_of_deterministic_predecessor_bounded s hs hdet
  exact ⟨p, hp, hper⟩

/-- Equal residues modulo a period give equal parameter values, so the residue class records all
the forcing information needed in a finite state. Lemma 5.4 (`lem:forcing`). -/
theorem periodic_eq_of_emod_eq {F : Type*} (f : ℤ → F) (p : ℤ)
    (hf : Function.Periodic f p) {i j : ℤ} (h : i % p = j % p) : f i = f j := by
  have hrem (z : ℤ) : f (z % p) = f z := by
    calc
      f (z % p) = f (z % p + z / p * p) := (hf.int_mul (z / p) (z % p)).symm
      _ = f z := congrArg f (Int.emod_add_ediv_mul z p)
  exact (hrem i).symm.trans ((congrArg f h).trans (hrem j))

/-- A finite-range word with a periodic parameter and a uniquely determined next letter from its
occurring memory data has a positive period. The state contains the phase and `k + 1`
letters, including when `k = 0`. Lemma 5.4 (`lem:forcing`). -/
theorem periodic_of_periodic_forcing {A F : Type*} (a : ℤ → A) (f : ℤ → F)
    (ha : (Set.range a).Finite) (p k : ℕ) (hp : 0 < p)
    (hf : Function.Periodic f (p : ℤ))
    (hrule : ∀ i j : ℤ, f i = f j →
      (∀ r : Fin k, a (i + (r : ℕ)) = a (j + (r : ℕ))) →
      a (i + k) = a (j + k)) :
    ∃ q : ℕ, 0 < q ∧ Function.Periodic a (q : ℤ) := by
  classical
  let : Fintype (Set.range a) := ha.fintype
  let : Fintype (Set.Ico (0 : ℤ) (p : ℤ)) := (Set.finite_Ico _ _).fintype
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  let phase : ℤ → Set.Ico (0 : ℤ) (p : ℤ) := fun i =>
    ⟨i % (p : ℤ), Int.emod_nonneg i (by omega), Int.emod_lt_of_pos i hpz⟩
  let state : ℤ → (Set.Ico (0 : ℤ) (p : ℤ)) × (Fin (k + 1) → Set.range a) :=
    fun i => (phase i, fun r => ⟨a (i + (r : ℕ)), i + (r : ℕ), rfl⟩)
  have hdet : ∀ i j : ℤ, state i = state j → state (i + 1) = state (j + 1) := by
    intro i j hij
    have hmod : i % (p : ℤ) = j % (p : ℤ) :=
      congrArg (fun s => s.1.val) hij
    have hnextmod : (i + 1) % (p : ℤ) = (j + 1) % (p : ℤ) := by
      rw [Int.add_emod i 1, Int.add_emod j 1, hmod]
    have hletters (r : Fin (k + 1)) : a (i + (r : ℕ)) = a (j + (r : ℕ)) :=
      congrArg (fun s => (s.2 r).val) hij
    have hnextletters (r : Fin k) : a (i + 1 + (r : ℕ)) = a (j + 1 + (r : ℕ)) := by
      convert hletters ⟨(r : ℕ) + 1, by omega⟩ using 1 <;> push_cast <;> congr 1 <;> ring
    apply Prod.ext
    · exact Subtype.ext hnextmod
    · funext r
      apply Subtype.ext
      change a (i + 1 + (r : ℕ)) = a (j + 1 + (r : ℕ))
      by_cases hr : (r : ℕ) < k
      · exact hnextletters ⟨r, hr⟩
      · have heq : (r : ℕ) = k := by omega
        simpa only [heq] using hrule (i + 1) (j + 1)
          (periodic_eq_of_emod_eq f (p : ℤ) hf hnextmod) hnextletters
  obtain ⟨q, hq, hper⟩ :=
    periodic_of_deterministic_successor state (Set.toFinite (Set.range state)) hdet
  refine ⟨q, hq, fun i => ?_⟩
  have h := congrArg (fun s => (s.2 (0 : Fin (k + 1))).val) (hper i)
  simpa only [state, Fin.val_zero, Nat.cast_zero, add_zero] using h

/-- The length-`k` word beginning at an arbitrary integer index of a bilateral sequence.
Corollary 5.3 (`cor:morse`). -/
@[expose] def word {A : Type*} (a : ℤ → A) (k : ℕ) (i : ℤ) : Fin k → A :=
  fun r => a (i + (r : ℕ))

/-- The number of distinct length-`k` words over all integer starting indices; finite range
ensures that the counted set is finite. Corollary 5.3 (`cor:morse`). -/
@[expose] noncomputable def wordComplexity {A : Type*} (a : ℤ → A) (k : ℕ) : ℕ :=
  (Set.range (word a k)).ncard

/-- A finite alphabet gives only finitely many occurring words of any fixed finite length.
Corollary 5.3 (`cor:morse`). -/
theorem finite_word_range {A : Type*} (a : ℤ → A) (ha : (Set.range a).Finite) (k : ℕ) :
    (Set.range (word a k)).Finite := by
  refine (Set.Finite.pi' (fun _ : Fin k => ha)).subset ?_
  rintro _ ⟨i, rfl⟩ r
  exact ⟨i + (r : ℕ), rfl⟩

/-- There is exactly one empty word, providing the initial value `p(0) = 1` in the plateau
argument. Corollary 5.3 (`cor:morse`). -/
@[simp] theorem wordComplexity_zero {A : Type*} (a : ℤ → A) : wordComplexity a 0 = 1 := by
  have hrange : Set.range (word a 0) = {word a 0 0} := by
    ext b
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      exact Subsingleton.elim _ _
    · rintro rfl
      exact ⟨0, rfl⟩
  simp only [wordComplexity, hrange, Set.ncard_singleton]

/-- Taking the initial subword maps the occurring longer words onto all occurring shorter words.
Corollary 5.3 (`cor:morse`). -/
theorem word_restriction_image {A : Type*} (a : ℤ → A) {m n : ℕ} (hmn : m ≤ n) :
    (fun b : Fin n → A => fun r : Fin m => b ⟨r, lt_of_lt_of_le r.isLt hmn⟩) ''
      Set.range (word a n) = Set.range (word a m) := by
  ext b
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨word a n i, ⟨i, rfl⟩, rfl⟩

/-- Word complexity is nondecreasing with word length because initial restriction is surjective.
Corollary 5.3 (`cor:morse`). -/
theorem wordComplexity_mono {A : Type*} (a : ℤ → A) (ha : (Set.range a).Finite) :
    Monotone (wordComplexity a) := by
  intro m n hmn
  unfold wordComplexity
  rw [← word_restriction_image a hmn]
  exact Set.ncard_image_le (finite_word_range a ha n)

/-- If length-`k` complexity is at most `k`, one of the first `k` increases is zero, since
empty-word complexity is one. Corollary 5.3 (`cor:morse`). -/
theorem exists_wordComplexity_plateau {A : Type*} (a : ℤ → A)
    (ha : (Set.range a).Finite) (k : ℕ) (_hk : 0 < k) (hbound : wordComplexity a k ≤ k) :
    ∃ j < k, wordComplexity a (j + 1) = wordComplexity a j := by
  by_contra! hnone
  have hstrict (j : ℕ) (hj : j < k) : wordComplexity a j < wordComplexity a (j + 1) := by
    exact lt_of_le_of_ne (wordComplexity_mono a ha (by omega)) (Ne.symm (hnone j hj))
  have hlower : ∀ j ≤ k, j + 1 ≤ wordComplexity a j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro hj
      have hprev := ih (by omega)
      have hnext := hstrict j (by omega)
      omega
  have := hlower k le_rfl
  omega

/-- At a complexity plateau, initial restriction is bijective on occurring words, so a word
determines its following letter. Corollary 5.3 (`cor:morse`). -/
theorem word_extension_unique_of_complexity_eq {A : Type*} (a : ℤ → A)
    (ha : (Set.range a).Finite) (k : ℕ)
    (heq : wordComplexity a (k + 1) = wordComplexity a k) :
    ∀ i j : ℤ, word a k i = word a k j → word a (k + 1) i = word a (k + 1) j := by
  let restrict : (Fin (k + 1) → A) → (Fin k → A) :=
    fun b r => b ⟨r, by omega⟩
  have himage : restrict '' Set.range (word a (k + 1)) = Set.range (word a k) :=
    word_restriction_image a (by omega)
  have hinj : Set.InjOn restrict (Set.range (word a (k + 1))) :=
    Set.injOn_of_ncard_image_eq (by rw [himage]; exact heq.symm)
      (finite_word_range a ha (k + 1))
  intro i j hij
  exact hinj ⟨i, rfl⟩ ⟨j, rfl⟩ hij

/-- A bilateral finite-range word with at most `k` length-`k` words has a positive period at
most `k`. The states at a plateau use one extra letter so projection to the original word
also covers a plateau at zero. Corollary 5.3 (`cor:morse`). -/
theorem morse_hedlund {A : Type*} (a : ℤ → A) (ha : (Set.range a).Finite)
    (k : ℕ) (hk : 0 < k) (hbound : wordComplexity a k ≤ k) :
    ∃ p : ℕ, 0 < p ∧ p ≤ k ∧ Function.Periodic a (p : ℤ) := by
  obtain ⟨j, hj, heq⟩ := exists_wordComplexity_plateau a ha k hk hbound
  have hdet : ∀ i l : ℤ, word a (j + 1) i = word a (j + 1) l →
      word a (j + 1) (i + 1) = word a (j + 1) (l + 1) := by
    intro i l hil
    apply word_extension_unique_of_complexity_eq a ha j heq
    funext r
    have h := congrFun hil (⟨(r : ℕ) + 1, by omega⟩ : Fin (j + 1))
    change a (i + 1 + (r : ℕ)) = a (l + 1 + (r : ℕ))
    dsimp only [word] at h
    convert h using 1 <;> push_cast <;> congr 1 <;> ring
  obtain ⟨p, hp, hb, hper⟩ := periodic_of_deterministic_successor_bounded
    (word a (j + 1)) (finite_word_range a ha (j + 1)) hdet
  refine ⟨p, hp, hb.trans ((wordComplexity_mono a ha (by omega)).trans hbound), ?_⟩
  intro i
  have h := congrFun (hper i) (0 : Fin (j + 1))
  simpa only [word, Fin.val_zero, Nat.cast_zero, add_zero] using h

end Nivat.TwoFactors
