/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.Permanent
import Mathlib.Data.List.FinRange
import Mathlib.Tactic

/-! # Kuhn Matching -/

namespace BeyondBethe

/-!
# Executable augmenting-path matching

This file implements the polynomial augmenting-path algorithm for the
positive support of a square rational matrix.  A state maps each column to
its currently matched row.  Failed recursive searches return the enlarged
set of visited columns, so a single root search examines each column at most
once; this detail is essential for the polynomial bound.
-/

abbrev ColumnMate (n : ℕ) := Fin n → Option (Fin n)

def emptyColumnMate (n : ℕ) : ColumnMate n := fun _ ↦ none

/-- A column-to-row table represents a partial matching in the positive
support of `A`. -/
structure IsSupportColumnMate {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (mate : ColumnMate n) : Prop where
  support : ∀ {col row}, mate col = some row → A row col ≠ 0
  injective : ∀ {col col' row},
    mate col = some row → mate col' = some row → col = col'

def RowUnmatched {n : ℕ} (mate : ColumnMate n) (row : Fin n) : Prop :=
  ∀ col, mate col ≠ some row

def MatchesRow {n : ℕ} (mate : ColumnMate n) (row : Fin n) : Prop :=
  ∃ col, mate col = some row

theorem rowUnmatched_iff_not_matchesRow {n : ℕ}
    (mate : ColumnMate n) (row : Fin n) :
    RowUnmatched mate row ↔ ¬MatchesRow mate row := by
  simp [RowUnmatched, MatchesRow]

theorem emptyColumnMate_support (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℚ) :
    IsSupportColumnMate A (emptyColumnMate n) := by
  constructor <;> simp [emptyColumnMate]

theorem rowUnmatched_emptyColumnMate (n : ℕ) (row : Fin n) :
    RowUnmatched (emptyColumnMate n) row := by
  simp [RowUnmatched, emptyColumnMate]

theorem IsSupportColumnMate.update_none {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℚ} {mate : ColumnMate n}
    (h : IsSupportColumnMate A mate) (col : Fin n) :
    IsSupportColumnMate A (Function.update mate col none) := by
  constructor
  · intro j row hj
    by_cases hcol : j = col
    · subst j
      simp at hj
    · simp [Function.update, hcol] at hj
      exact h.support hj
  · intro j j' row hj hj'
    by_cases hjc : j = col
    · subst j
      simp at hj
    · simp [Function.update, hjc] at hj
      by_cases hjc' : j' = col
      · subst j'
        simp at hj'
      · simp [Function.update, hjc'] at hj'
        exact h.injective hj hj'

theorem IsSupportColumnMate.update_some {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℚ} {mate : ColumnMate n}
    (h : IsSupportColumnMate A mate) {col row : Fin n}
    (hrow : RowUnmatched mate row) (hedge : A row col ≠ 0) :
    IsSupportColumnMate A (Function.update mate col (some row)) := by
  constructor
  · intro j r hj
    by_cases hcol : j = col
    · subst j
      simp at hj
      subst r
      exact hedge
    · simp [Function.update, hcol] at hj
      exact h.support hj
  · intro j j' r hj hj'
    by_cases hjc : j = col
    · subst j
      simp at hj
      subst r
      by_cases hjc' : j' = col
      · exact hjc'.symm
      · simp [Function.update, hjc'] at hj'
        exact (hrow j' hj').elim
    · simp [Function.update, hjc] at hj
      by_cases hjc' : j' = col
      · subst j'
        simp at hj'
        subst r
        exact (hrow j hj).elim
      · simp [Function.update, hjc'] at hj'
        exact h.injective hj hj'

theorem matchesRow_update_none_iff {n : ℕ}
    {mate : ColumnMate n} {col oldRow row : Fin n}
    (hinj : ∀ {j j' r},
      mate j = some r → mate j' = some r → j = j')
    (hmate : mate col = some oldRow) :
    MatchesRow (Function.update mate col none) row ↔
      MatchesRow mate row ∧ row ≠ oldRow := by
  constructor
  · rintro ⟨j, hj⟩
    have hjne : j ≠ col := by
      intro h
      subst j
      simp at hj
    have hjold : mate j = some row := by
      simpa [Function.update, hjne] using hj
    refine ⟨⟨j, hjold⟩, ?_⟩
    intro hrow
    subst row
    exact hjne (hinj hjold hmate)
  · rintro ⟨⟨j, hj⟩, hrow⟩
    refine ⟨j, ?_⟩
    have hjne : j ≠ col := by
      intro h
      subst j
      rw [hmate] at hj
      exact hrow (Option.some.inj hj).symm
    simpa [Function.update, hjne] using hj

theorem rowUnmatched_update_none_of_mate {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℚ} {mate : ColumnMate n}
    (h : IsSupportColumnMate A mate) {col oldRow : Fin n}
    (hmate : mate col = some oldRow) :
    RowUnmatched (Function.update mate col none) oldRow := by
  rw [rowUnmatched_iff_not_matchesRow, matchesRow_update_none_iff h.injective hmate]
  simp

theorem matchesRow_update_some_iff {n : ℕ}
    {mate : ColumnMate n} {col newRow row : Fin n}
    (hcol : mate col = none) :
    MatchesRow (Function.update mate col (some newRow)) row ↔
      MatchesRow mate row ∨ row = newRow := by
  constructor
  · rintro ⟨j, hj⟩
    by_cases h : j = col
    · subst j
      simp at hj
      exact Or.inr hj.symm
    · left
      exact ⟨j, by simpa [Function.update, h] using hj⟩
  · rintro (⟨j, hj⟩ | rfl)
    · have h : j ≠ col := by
        intro heq
        subst j
        rw [hcol] at hj
        contradiction
      exact ⟨j, by simpa [Function.update, h] using hj⟩
    · exact ⟨col, by simp⟩

/-- Result of one augmenting-path search.  `mate? = some m` records success;
either way, `seen` contains every column examined by the search. -/
structure KuhnSearchResult (n : ℕ) where
  mate? : Option (ColumnMate n)
  seen : Finset (Fin n)

/-- Depth-first augmenting-path search with a shared visited-column set.
The first natural-number argument bounds alternating-path depth; the column
list is the part of the current row that remains to be scanned.  A failed
recursive call threads its enlarged visited set into the rest of the scan.
The lexicographic recursion makes both sources of progress explicit. -/
def kuhnSearch {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    (fuel : ℕ) → List (Fin n) → Fin n → Finset (Fin n) →
      ColumnMate n → KuhnSearchResult n
  | 0, _remaining, _row, seen, _mate => ⟨none, seen⟩
  | _fuel + 1, [], _row, seen, _mate => ⟨none, seen⟩
  | fuel + 1, col :: remaining, row, seen, mate =>
      if hskip : col ∈ seen ∨ A row col = 0 then
        kuhnSearch A (fuel + 1) remaining row seen mate
      else
        let seen' := insert col seen
        match hmate : mate col with
        | none => ⟨some (Function.update mate col (some row)), seen'⟩
        | some oldRow =>
            let mateWithoutOld := Function.update mate col none
            let recursive :=
              kuhnSearch A fuel (List.finRange n) oldRow seen' mateWithoutOld
            match recursive.mate? with
            | some mate' =>
                ⟨some (Function.update mate' col (some row)), recursive.seen⟩
            | none =>
                kuhnSearch A (fuel + 1) remaining row recursive.seen mate
termination_by fuel remaining _row _seen _mate => (fuel, remaining.length)

/-- Number of column inspections made by `kuhnSearch`.  Recursive work is
charged only on the branch actually taken by the executable search. -/
def kuhnSearchWork {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    (fuel : ℕ) → List (Fin n) → Fin n → Finset (Fin n) → ColumnMate n → ℕ
  | 0, _remaining, _row, _seen, _mate => 0
  | _fuel + 1, [], _row, _seen, _mate => 0
  | fuel + 1, col :: remaining, row, seen, mate =>
      if col ∈ seen ∨ A row col = 0 then
        1 + kuhnSearchWork A (fuel + 1) remaining row seen mate
      else
        let seen' := insert col seen
        match mate col with
        | none => 1
        | some oldRow =>
            let mateWithoutOld := Function.update mate col none
            let recursive :=
              kuhnSearch A fuel (List.finRange n) oldRow seen' mateWithoutOld
            let recursiveWork :=
              kuhnSearchWork A fuel (List.finRange n) oldRow seen' mateWithoutOld
            match recursive.mate? with
            | some _ => 1 + recursiveWork
            | none => 1 + recursiveWork +
                kuhnSearchWork A (fuel + 1) remaining row recursive.seen mate
termination_by fuel remaining _row _seen _mate => (fuel, remaining.length)

/-- Search all columns from scratch for an augmenting path rooted at `row`. -/
def kuhnAugment {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (fuel : ℕ) (row : Fin n) (seen : Finset (Fin n))
    (mate : ColumnMate n) : KuhnSearchResult n :=
  kuhnSearch A fuel (List.finRange n) row seen mate

theorem kuhnSearch_seen_mono {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (fuel : ℕ)
    (remaining : List (Fin n)) (row : Fin n)
    (seen : Finset (Fin n)) (mate : ColumnMate n) :
    seen ⊆ (kuhnSearch A fuel remaining row seen mate).seen := by
  fun_induction kuhnSearch <;> simp_all [Finset.subset_iff] <;> aesop

/-- Amortized work bound.  Scanning the current suffix is charged directly;
each newly visited column pays for at most one fresh full row scan. -/
theorem kuhnSearchWork_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (fuel : ℕ)
    (remaining : List (Fin n)) (row : Fin n)
    (seen : Finset (Fin n)) (mate : ColumnMate n) :
    kuhnSearchWork A fuel remaining row seen mate ≤
      remaining.length + (n + 1) *
        ((kuhnSearch A fuel remaining row seen mate).seen.card - seen.card) := by
  fun_induction kuhnSearchWork with
  | case1 =>
      rw [kuhnSearch.eq_def]
      simp
  | case2 =>
      rw [kuhnSearch.eq_def]
      simp
  | case3 fuel col remaining row seen mate hskip ih =>
      rw [kuhnSearch.eq_def]
      dsimp only
      rw [dif_pos hskip]
      simp only [List.length_cons]
      omega
  | case4 fuel col remaining row seen mate hskip hmate =>
      rw [kuhnSearch.eq_def]
      dsimp only
      rw [dite_eq_right hskip, hmate]
      simp only [List.length_cons]
      have hnot : col ∉ seen := by aesop
      rw [Finset.card_insert_of_notMem hnot]
      omega
  | case5 fuel col remaining row seen mate hskip seen' oldRow hmate
      mateWithoutOld recursive recursiveWork mateRec hrec ih =>
      rw [kuhnSearch.eq_def]
      dsimp only
      rw [dite_eq_right hskip, hmate]
      simp
      rw [show (kuhnSearch A fuel (List.finRange n) oldRow
        (insert col seen) (Function.update mate col none)).mate? = some mateRec by
          simpa [recursive] using hrec]
      change 1 + recursiveWork ≤ remaining.length + 1 +
        (n + 1) * (recursive.seen.card - seen.card)
      have hnot : col ∉ seen := by aesop
      have hcardInsert : seen'.card = seen.card + 1 := by
        simpa [seen'] using Finset.card_insert_of_notMem hnot
      have hsubset : seen' ⊆ recursive.seen := by
        simpa [recursive] using kuhnSearch_seen_mono A fuel
          (List.finRange n) oldRow seen' mateWithoutOld
      have hcard : seen'.card ≤ recursive.seen.card :=
        Finset.card_le_card hsubset
      have hih : recursiveWork ≤
          n + (n + 1) * (recursive.seen.card - seen'.card) := by
        simpa [recursiveWork, recursive] using ih
      have hsubEq : recursive.seen.card - seen.card =
          (recursive.seen.card - seen'.card) + 1 := by
        omega
      rw [hsubEq, Nat.mul_add]
      omega
  | case6 fuel col remaining row seen mate hskip seen' oldRow hmate
      mateWithoutOld recursive recursiveWork hrec ihRec ihContinue =>
      rw [kuhnSearch.eq_def]
      dsimp only
      rw [dite_eq_right hskip, hmate]
      simp
      rw [show (kuhnSearch A fuel (List.finRange n) oldRow
        (insert col seen) (Function.update mate col none)).mate? = none by
          simpa [recursive] using hrec]
      change 1 + recursiveWork +
          kuhnSearchWork A (fuel + 1) remaining row recursive.seen mate ≤
        remaining.length + 1 + (n + 1) *
          ((kuhnSearch A (fuel + 1) remaining row recursive.seen mate).seen.card -
            seen.card)
      have hnot : col ∉ seen := by aesop
      have hcardInsert : seen'.card = seen.card + 1 := by
        simpa [seen'] using Finset.card_insert_of_notMem hnot
      have hsubsetRec : seen' ⊆ recursive.seen := by
        simpa [recursive] using kuhnSearch_seen_mono A fuel
          (List.finRange n) oldRow seen' mateWithoutOld
      have hcardRec : seen'.card ≤ recursive.seen.card :=
        Finset.card_le_card hsubsetRec
      have hsubsetFinal : recursive.seen ⊆
          (kuhnSearch A (fuel + 1) remaining row recursive.seen mate).seen :=
        kuhnSearch_seen_mono A (fuel + 1) remaining row recursive.seen mate
      have hcardFinal : recursive.seen.card ≤
          (kuhnSearch A (fuel + 1) remaining row recursive.seen mate).seen.card :=
        Finset.card_le_card hsubsetFinal
      have hihRec : recursiveWork ≤
          n + (n + 1) * (recursive.seen.card - seen'.card) := by
        simpa [recursiveWork, recursive] using ihRec
      let finalCard :=
        (kuhnSearch A (fuel + 1) remaining row recursive.seen mate).seen.card
      have hihContinue :
          kuhnSearchWork A (fuel + 1) remaining row recursive.seen mate ≤
            remaining.length + (n + 1) *
              (finalCard - recursive.seen.card) := by
        simpa [finalCard] using ihContinue
      clear ihContinue
      have hsplitOne : recursive.seen.card - seen.card =
          (recursive.seen.card - seen'.card) + 1 := by
        omega
      have hsplitAll : finalCard - seen.card =
          (finalCard - recursive.seen.card) +
            (recursive.seen.card - seen.card) := by
        dsimp only [finalCard]
        omega
      change 1 + recursiveWork +
          kuhnSearchWork A (fuel + 1) remaining row recursive.seen mate ≤
        remaining.length + 1 + (n + 1) * (finalCard - seen.card)
      rw [hsplitAll, hsplitOne, Nat.mul_add, Nat.mul_add]
      omega

def kuhnAugmentWork {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (fuel : ℕ) (row : Fin n) (seen : Finset (Fin n))
    (mate : ColumnMate n) : ℕ :=
  kuhnSearchWork A fuel (List.finRange n) row seen mate

/-- One augmentation makes at most `n + (n+1)n` column inspections. -/
theorem kuhnAugmentWork_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (fuel : ℕ)
    (row : Fin n) (mate : ColumnMate n) :
    kuhnAugmentWork A fuel row ∅ mate ≤ n + (n + 1) * n := by
  have hwork := kuhnSearchWork_le A fuel (List.finRange n) row ∅ mate
  have hcard := Finset.card_le_univ
    (kuhnSearch A fuel (List.finRange n) row ∅ mate).seen
  simp only [Fintype.card_fin] at hcard
  simp only [List.length_finRange, Finset.card_empty, Nat.sub_zero] at hwork
  exact hwork.trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left (n + 1) hcard) n)

/-- A search never changes a column that was already marked as visited when
the search began. -/
theorem kuhnSearch_preserves_seen {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (fuel : ℕ)
    (remaining : List (Fin n)) (row c : Fin n)
    (seen : Finset (Fin n)) (mate mate' : ColumnMate n)
    (hc : c ∈ seen)
    (hresult : (kuhnSearch A fuel remaining row seen mate).mate? = some mate') :
    mate' c = mate c := by
  fun_induction kuhnSearch generalizing c mate' with
  | case1 => simp_all
  | case2 => simp_all
  | case3 => simp_all
  | case4 fuel col remaining row seen mate hskip seen' hmate =>
      have hnot : col ∉ seen := by
        intro hmem
        exact hskip (Or.inl hmem)
      have hcne : c ≠ col := by
        intro heq
        subst c
        exact hnot hc
      change some (Function.update mate col (some row)) = some mate' at hresult
      injection hresult with heq
      subst mate'
      simp [Function.update, hcne]
  | case5 fuel col remaining row seen mate hskip seen' oldRow hmate
      mateWithoutOld recursive mateRec hrec ih =>
      have hnot : col ∉ seen := by
        intro hmem
        exact hskip (Or.inl hmem)
      have hcne : c ≠ col := by
        intro heq
        subst c
        exact hnot hc
      change some (Function.update mateRec col (some row)) = some mate' at hresult
      injection hresult with heq
      subst mate'
      calc
        Function.update mateRec col (some row) c = mateRec c := by
          simp [Function.update, hcne]
        _ = Function.update mate col none c :=
          ih c mateRec (by simp [seen', hc]) hrec
        _ = mate c := by simp [Function.update, hcne]
  | case6 fuel col remaining row seen mate hskip seen' oldRow hmate
      mateWithoutOld recursive hrec ihRec ihRec' ihContinue =>
      apply ihContinue c mate' ?_ hresult
      apply kuhnSearch_seen_mono A fuel (List.finRange n) oldRow seen'
        mateWithoutOld
      simp [seen', hc]

/-- On success, augmenting adds exactly the root row to the set of matched
rows, and it preserves the support and injectivity invariants. -/
theorem kuhnSearch_success {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (fuel : ℕ)
    (remaining : List (Fin n)) (row : Fin n)
    (seen : Finset (Fin n)) (mate mate' : ColumnMate n)
    (hsupport : IsSupportColumnMate A mate)
    (hunmatched : RowUnmatched mate row)
    (hresult : (kuhnSearch A fuel remaining row seen mate).mate? = some mate') :
    IsSupportColumnMate A mate' ∧
      ∀ r, MatchesRow mate' r ↔ MatchesRow mate r ∨ r = row := by
  fun_induction kuhnSearch generalizing mate' with
  | case1 => simp_all
  | case2 => simp_all
  | case3 fuel col remaining row seen mate hskip ih =>
      exact ih mate' hsupport hunmatched hresult
  | case4 fuel col remaining row seen mate hskip seen' hmate =>
      change some (Function.update mate col (some row)) = some mate' at hresult
      injection hresult with heq
      subst mate'
      have hedge : A row col ≠ 0 := by aesop
      exact ⟨hsupport.update_some hunmatched hedge,
        fun r ↦ matchesRow_update_some_iff hmate⟩
  | case5 fuel col remaining row seen mate hskip seen' oldRow hmate
      mateWithoutOld recursive mateRec hrec ih =>
      have hcleared : IsSupportColumnMate A mateWithoutOld := by
        simpa [mateWithoutOld] using hsupport.update_none col
      have holdUnmatched : RowUnmatched mateWithoutOld oldRow := by
        simpa [mateWithoutOld] using
          rowUnmatched_update_none_of_mate hsupport hmate
      have hrecResult :
          (kuhnSearch A fuel (List.finRange n) oldRow seen' mateWithoutOld).mate? =
            some mateRec := by
        simpa [recursive] using hrec
      obtain ⟨hrecSupport, hrecRows⟩ :=
        ih mateRec hcleared holdUnmatched hrecResult
      have hcolSeen : col ∈ seen' := by simp [seen']
      have hrecCol : mateRec col = none := by
        calc
          mateRec col = mateWithoutOld col :=
            kuhnSearch_preserves_seen A fuel (List.finRange n) oldRow col seen'
              mateWithoutOld mateRec hcolSeen hrecResult
          _ = none := by simp [mateWithoutOld]
      have hrowNe : row ≠ oldRow := by
        intro heq
        subst oldRow
        exact hunmatched col hmate
      have hrootUnmatched : RowUnmatched mateRec row := by
        rw [rowUnmatched_iff_not_matchesRow]
        intro hroot
        rw [hrecRows row] at hroot
        rcases hroot with hroot | hroot
        · rw [matchesRow_update_none_iff hsupport.injective hmate] at hroot
          exact (rowUnmatched_iff_not_matchesRow mate row).mp hunmatched hroot.1
        · exact hrowNe hroot
      have hedge : A row col ≠ 0 := by aesop
      change some (Function.update mateRec col (some row)) = some mate' at hresult
      injection hresult with heq
      subst mate'
      constructor
      · exact hrecSupport.update_some hrootUnmatched hedge
      · intro r
        rw [matchesRow_update_some_iff hrecCol, hrecRows,
          matchesRow_update_none_iff hsupport.injective hmate]
        constructor
        · rintro ((⟨hr, hrne⟩ | rfl) | rfl)
          · exact Or.inl hr
          · exact Or.inl ⟨col, hmate⟩
          · exact Or.inr rfl
        · rintro (hr | rfl)
          · by_cases hrold : r = oldRow
            · exact Or.inl (Or.inr hrold)
            · exact Or.inl (Or.inl ⟨hr, hrold⟩)
          · exact Or.inr rfl
  | case6 fuel col remaining row seen mate hskip seen' oldRow hmate
      mateWithoutOld recursive hrec ihRec ihRec' ihContinue =>
      exact ihContinue mate' hsupport hunmatched hresult

def AllSupportNeighborsIn {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (row : Fin n)
    (cols : Finset (Fin n)) : Prop :=
  ∀ col, A row col ≠ 0 → col ∈ cols

/-- A failed search has explored every remaining support edge of its root.
Every newly explored column was occupied, and the old row at that column has
all of its support neighbors in the final explored set. -/
structure KuhnFailureCertificate {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (mate : ColumnMate n)
    (row : Fin n) (initialSeen finalSeen : Finset (Fin n))
    (remaining : List (Fin n)) : Prop where
  seen_subset : initialSeen ⊆ finalSeen
  scanned : ∀ col, col ∈ remaining → A row col ≠ 0 → col ∈ finalSeen
  occupied_closed : ∀ col, col ∈ finalSeen → col ∉ initialSeen →
    ∃ oldRow, mate col = some oldRow ∧ AllSupportNeighborsIn A oldRow finalSeen

/-- The precise failure certificate returned by the executable search.  The
strict fuel-plus-visited inequality is preserved by every recursive descent;
at zero fuel it contradicts the fact that there are only `n` columns. -/
theorem kuhnSearch_failure_certificate {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (fuel : ℕ)
    (remaining : List (Fin n)) (row : Fin n)
    (seen : Finset (Fin n)) (mate : ColumnMate n)
    (hroom : n < fuel + seen.card)
    (hresult : (kuhnSearch A fuel remaining row seen mate).mate? = none) :
    KuhnFailureCertificate A mate row seen
      (kuhnSearch A fuel remaining row seen mate).seen remaining := by
  fun_induction kuhnSearch with
  | case1 remaining row seen mate =>
      have hcard := Finset.card_le_univ seen
      simp [Fintype.card_fin] at hcard
      omega
  | case2 =>
      constructor
      · exact fun _ h ↦ h
      · simp
      · intro col hmem hnot
        exact (hnot hmem).elim
  | case3 fuel col remaining row seen mate hskip ih =>
      have cert := ih hroom hresult
      refine ⟨cert.seen_subset, ?_, cert.occupied_closed⟩
      intro c hc hedge
      rcases (List.mem_cons.mp hc) with rfl | hc
      · rcases hskip with hseen | hzero
        · exact cert.seen_subset hseen
        · exact (hedge hzero).elim
      · exact cert.scanned c hc hedge
  | case4 => simp_all
  | case5 => simp_all
  | case6 fuel col remaining row seen mate hskip seen' oldRow hmate
      mateWithoutOld recursive hrec ihRec ihRec' ihContinue =>
      have hnotSeen : col ∉ seen := by aesop
      have hseenCard : seen'.card = seen.card + 1 := by
        simpa [seen'] using Finset.card_insert_of_notMem hnotSeen
      have hroomRec : n < fuel + seen'.card := by omega
      have certRec := ihRec' hroomRec hrec
      have hcardMono : seen'.card ≤ recursive.seen.card := by
        apply Finset.card_le_card
        simpa [recursive] using certRec.seen_subset
      have hroomContinue : n < (fuel + 1) + recursive.seen.card := by
        omega
      have certContinue := ihContinue hroomContinue hresult
      have hrecSubset : recursive.seen ⊆
          (kuhnSearch A (fuel + 1) remaining row recursive.seen mate).seen :=
        certContinue.seen_subset
      refine ⟨?_, ?_, ?_⟩
      · intro c hc
        apply hrecSubset
        apply certRec.seen_subset
        simp [hc]
      · intro c hc hedge
        rcases (List.mem_cons.mp hc) with rfl | hc
        · apply hrecSubset
          exact certRec.seen_subset (by simp)
        · exact certContinue.scanned c hc hedge
      · intro c hcout hcnot
        by_cases hcinRec : c ∈ recursive.seen
        · by_cases hccol : c = col
          · subst c
            refine ⟨oldRow, hmate, ?_⟩
            intro d hd
            apply hrecSubset
            exact certRec.scanned d (List.mem_finRange d) hd
          · have hcnotSeen' : c ∉ seen' := by
              simp only [seen', Finset.mem_insert, not_or]
              exact ⟨hccol, hcnot⟩
            obtain ⟨r, hrmate, hrclosed⟩ :=
              certRec.occupied_closed c hcinRec hcnotSeen'
            refine ⟨r, ?_, ?_⟩
            · simpa [mateWithoutOld, Function.update, hccol] using hrmate
            · intro d hd
              exact hrecSubset (hrclosed d hd)
        · exact certContinue.occupied_closed c hcout hcinRec

/-- If a full search from an unmatched row fails, its alternating-closure
certificate contradicts any perfect matching.  The contradiction is a finite
pigeonhole argument: the root together with the old rows at the explored
columns would inject into the explored columns. -/
theorem noPerfectMatching_of_kuhnAugment_failure {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (row : Fin n)
    (mate : ColumnMate n)
    (hsupport : IsSupportColumnMate A mate)
    (hunmatched : RowUnmatched mate row)
    (hfail : (kuhnAugment A (n + 1) row ∅ mate).mate? = none) :
    ¬Matrix.HasPerfectMatching A := by
  classical
  intro hperfect
  obtain ⟨σ, hσ⟩ := hperfect
  have hroom : n < (n + 1) + (∅ : Finset (Fin n)).card := by simp
  have cert := kuhnSearch_failure_certificate A (n + 1)
    (List.finRange n) row ∅ mate hroom (by simpa [kuhnAugment] using hfail)
  let finalSeen : Finset (Fin n) :=
    (kuhnSearch A (n + 1) (List.finRange n) row ∅ mate).seen
  let SeenColumn := {c : Fin n // c ∈ finalSeen}
  have occupied (c : SeenColumn) :
      ∃ oldRow, mate c.1 = some oldRow ∧
        AllSupportNeighborsIn A oldRow finalSeen := by
    apply cert.occupied_closed c.1
    · exact c.2
    · simp
  let oldRow : SeenColumn → Fin n := fun c ↦ Classical.choose (occupied c)
  have oldRow_mate (c : SeenColumn) : mate c.1 = some (oldRow c) := by
    exact (Classical.choose_spec (occupied c)).1
  have oldRow_closed (c : SeenColumn) :
      AllSupportNeighborsIn A (oldRow c) finalSeen := by
    exact (Classical.choose_spec (occupied c)).2
  let sourceRow : Option SeenColumn → Fin n
    | none => row
    | some c => oldRow c
  have sourceRow_injective : Function.Injective sourceRow := by
    intro x y hxy
    cases x with
    | none =>
        cases y with
        | none => rfl
        | some c =>
            exfalso
            have hr : row = oldRow c := by simpa [sourceRow] using hxy
            apply hunmatched c.1
            simpa [hr] using oldRow_mate c
    | some c =>
        cases y with
        | none =>
            exfalso
            have hr : oldRow c = row := by simpa [sourceRow] using hxy
            apply hunmatched c.1
            simpa [← hr] using oldRow_mate c
        | some d =>
            apply congrArg some
            apply Subtype.ext
            apply hsupport.injective (oldRow_mate c)
            have hr : oldRow c = oldRow d := by simpa [sourceRow] using hxy
            simpa [← hr] using oldRow_mate d
  have target_mem (x : Option SeenColumn) :
      σ.symm (sourceRow x) ∈ finalSeen := by
    cases x with
    | none =>
        apply cert.scanned (σ.symm row) (List.mem_finRange _)
        simpa [sourceRow] using hσ (σ.symm row)
    | some c =>
        apply oldRow_closed c (σ.symm (oldRow c))
        simpa using hσ (σ.symm (oldRow c))
  let targetColumn : Option SeenColumn → SeenColumn := fun x ↦
    ⟨σ.symm (sourceRow x), target_mem x⟩
  have targetColumn_injective : Function.Injective targetColumn := by
    intro x y hxy
    apply sourceRow_injective
    apply σ.symm.injective
    exact congrArg Subtype.val hxy
  have hcard := Fintype.card_le_of_injective targetColumn targetColumn_injective
  simp only [Fintype.card_option] at hcard
  omega

theorem kuhnAugment_succeeds_of_hasPerfectMatching {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (row : Fin n)
    (mate : ColumnMate n)
    (hsupport : IsSupportColumnMate A mate)
    (hunmatched : RowUnmatched mate row)
    (hperfect : Matrix.HasPerfectMatching A) :
    ∃ mate', (kuhnAugment A (n + 1) row ∅ mate).mate? = some mate' := by
  cases hresult : (kuhnAugment A (n + 1) row ∅ mate).mate? with
  | none =>
      exact (noPerfectMatching_of_kuhnAugment_failure A row mate hsupport
        hunmatched hresult hperfect).elim
  | some mate' => exact ⟨mate', rfl⟩

theorem kuhnAugment_success {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (row : Fin n)
    (mate mate' : ColumnMate n)
    (hsupport : IsSupportColumnMate A mate)
    (hunmatched : RowUnmatched mate row)
    (hresult : (kuhnAugment A (n + 1) row ∅ mate).mate? = some mate') :
    IsSupportColumnMate A mate' ∧
      ∀ r, MatchesRow mate' r ↔ MatchesRow mate r ∨ r = row := by
  exact kuhnSearch_success A (n + 1) (List.finRange n) row ∅ mate mate'
    hsupport hunmatched (by simpa [kuhnAugment] using hresult)

/-- Insert the listed rows one at a time, augmenting whenever possible. -/
def kuhnBuild {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    List (Fin n) → ColumnMate n → ColumnMate n
  | [], mate => mate
  | row :: rows, mate =>
      let result := kuhnAugment A (n + 1) row ∅ mate
      kuhnBuild A rows (result.mate?.getD mate)

def kuhnBuildWork {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    List (Fin n) → ColumnMate n → ℕ
  | [], _mate => 0
  | row :: rows, mate =>
      let result := kuhnAugment A (n + 1) row ∅ mate
      kuhnAugmentWork A (n + 1) row ∅ mate +
        kuhnBuildWork A rows (result.mate?.getD mate)

/-- The row-building phase has a cubic coordinate-inspection bound. -/
theorem kuhnBuildWork_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (rows : List (Fin n))
    (mate : ColumnMate n) :
    kuhnBuildWork A rows mate ≤ rows.length * (n + (n + 1) * n) := by
  induction rows generalizing mate with
  | nil => simp [kuhnBuildWork]
  | cons row rows ih =>
      rw [kuhnBuildWork]
      calc
        kuhnAugmentWork A (n + 1) row ∅ mate +
            kuhnBuildWork A rows
              ((kuhnAugment A (n + 1) row ∅ mate).mate?.getD mate) ≤
          (n + (n + 1) * n) + rows.length * (n + (n + 1) * n) :=
            Nat.add_le_add (kuhnAugmentWork_le A (n + 1) row mate) (ih _)
        _ = (row :: rows).length * (n + (n + 1) * n) := by
          simp [Nat.add_mul, Nat.add_comm]

/-- If a perfect matching exists, inserting a duplicate-free list of
initially unmatched rows succeeds at every step and adds exactly those rows. -/
theorem kuhnBuild_of_hasPerfectMatching {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (rows : List (Fin n))
    (mate : ColumnMate n)
    (hperfect : Matrix.HasPerfectMatching A)
    (hnodup : rows.Nodup)
    (hsupport : IsSupportColumnMate A mate)
    (hunmatched : ∀ r, r ∈ rows → RowUnmatched mate r) :
    IsSupportColumnMate A (kuhnBuild A rows mate) ∧
      ∀ r, MatchesRow (kuhnBuild A rows mate) r ↔
        MatchesRow mate r ∨ r ∈ rows := by
  induction rows generalizing mate with
  | nil =>
      simp [kuhnBuild, hsupport]
  | cons row rows ih =>
      have hrowUnmatched : RowUnmatched mate row :=
        hunmatched row (by simp)
      obtain ⟨mateOne, haugment⟩ :=
        kuhnAugment_succeeds_of_hasPerfectMatching A row mate hsupport
          hrowUnmatched hperfect
      obtain ⟨hsupportOne, hrowsOne⟩ :=
        kuhnAugment_success A row mate mateOne hsupport hrowUnmatched haugment
      have htailNodup : rows.Nodup := hnodup.tail
      have hheadNotMem : row ∉ rows := (List.nodup_cons.mp hnodup).1
      have htailUnmatched : ∀ r, r ∈ rows → RowUnmatched mateOne r := by
        intro r hr
        rw [rowUnmatched_iff_not_matchesRow]
        intro hmatched
        rw [hrowsOne r] at hmatched
        rcases hmatched with hmatched | heq
        · exact (rowUnmatched_iff_not_matchesRow mate r).mp
            (hunmatched r (by simp [hr])) hmatched
        · subst r
          exact hheadNotMem hr
      obtain ⟨hfinalSupport, hfinalRows⟩ :=
        ih mateOne htailNodup hsupportOne htailUnmatched
      have hget :
          ((kuhnAugment A (n + 1) row ∅ mate).mate?.getD mate) = mateOne := by
        rw [haugment]
        rfl
      have hbuild : kuhnBuild A (row :: rows) mate =
          kuhnBuild A rows mateOne := by
        simp only [kuhnBuild]
        rw [hget]
      rw [hbuild]
      refine ⟨hfinalSupport, ?_⟩
      intro r
      rw [hfinalRows r, hrowsOne r]
      simp only [List.mem_cons]
      tauto

/-- Support and injectivity are preserved even when some augmenting searches
fail. -/
theorem kuhnBuild_support {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (rows : List (Fin n))
    (mate : ColumnMate n)
    (hnodup : rows.Nodup)
    (hsupport : IsSupportColumnMate A mate)
    (hunmatched : ∀ r, r ∈ rows → RowUnmatched mate r) :
    IsSupportColumnMate A (kuhnBuild A rows mate) := by
  induction rows generalizing mate with
  | nil => simpa [kuhnBuild] using hsupport
  | cons row rows ih =>
      have hrowUnmatched : RowUnmatched mate row :=
        hunmatched row (by simp)
      cases hresult : (kuhnAugment A (n + 1) row ∅ mate).mate? with
      | none =>
          have htailUnmatched : ∀ r, r ∈ rows → RowUnmatched mate r := by
            intro r hr
            exact hunmatched r (by simp [hr])
          simpa [kuhnBuild, hresult] using
            ih mate hnodup.tail hsupport htailUnmatched
      | some mateOne =>
          obtain ⟨hsupportOne, hrowsOne⟩ :=
            kuhnAugment_success A row mate mateOne hsupport hrowUnmatched hresult
          have hheadNotMem : row ∉ rows := (List.nodup_cons.mp hnodup).1
          have htailUnmatched : ∀ r, r ∈ rows → RowUnmatched mateOne r := by
            intro r hr
            rw [rowUnmatched_iff_not_matchesRow]
            intro hmatched
            rw [hrowsOne r] at hmatched
            rcases hmatched with hmatched | heq
            · exact (rowUnmatched_iff_not_matchesRow mate r).mp
                (hunmatched r (by simp [hr])) hmatched
            · subst r
              exact hheadNotMem hr
          simpa [kuhnBuild, hresult] using
            ih mateOne hnodup.tail hsupportOne htailUnmatched

def kuhnColumnMate {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) : ColumnMate n :=
  kuhnBuild A (List.finRange n) (emptyColumnMate n)

def matchedRowDecision {n : ℕ} (mate : ColumnMate n) (row : Fin n) : Bool :=
  (List.finRange n).any fun col ↦ mate col == some row

theorem matchedRowDecision_eq_true_iff {n : ℕ}
    (mate : ColumnMate n) (row : Fin n) :
    matchedRowDecision mate row = true ↔ MatchesRow mate row := by
  simp [matchedRowDecision, MatchesRow]

/-- The executable support-perfect-matching decision. -/
def kuhnSupportMatchingDecision {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) : Bool :=
  (List.finRange n).all fun row ↦ matchedRowDecision (kuhnColumnMate A) row

/-- Coordinate inspections in matching construction plus the final `n` by
`n` row-coverage check. -/
def kuhnSupportMatchingWork {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) : ℕ :=
  kuhnBuildWork A (List.finRange n) (emptyColumnMate n) + n * n

theorem kuhnSupportMatchingWork_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    kuhnSupportMatchingWork A ≤
      n * (n + (n + 1) * n) + n * n := by
  exact Nat.add_le_add_right
    (by simpa using kuhnBuildWork_le A (List.finRange n) (emptyColumnMate n)) _

theorem kuhnColumnMate_support {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    IsSupportColumnMate A (kuhnColumnMate A) := by
  apply kuhnBuild_support A (List.finRange n) (emptyColumnMate n)
  · exact List.nodup_finRange n
  · exact emptyColumnMate_support n A
  · intro row _
    exact rowUnmatched_emptyColumnMate n row

theorem hasPerfectMatching_of_all_rows_matched {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (mate : ColumnMate n)
    (hsupport : IsSupportColumnMate A mate)
    (hallRows : ∀ row, MatchesRow mate row) :
    Matrix.HasPerfectMatching A := by
  classical
  let colOfRow : Fin n → Fin n := fun row ↦ Classical.choose (hallRows row)
  have colOfRow_spec (row : Fin n) : mate (colOfRow row) = some row :=
    Classical.choose_spec (hallRows row)
  have colOfRow_injective : Function.Injective colOfRow := by
    intro r s hrs
    have hr := colOfRow_spec r
    have hs := colOfRow_spec s
    rw [hrs] at hr
    rw [hr] at hs
    exact Option.some.inj hs
  have colOfRow_bijective : Function.Bijective colOfRow :=
    (Fintype.bijective_iff_injective_and_card colOfRow).2
      ⟨colOfRow_injective, rfl⟩
  let e : Fin n ≃ Fin n := Equiv.ofBijective colOfRow colOfRow_bijective
  refine ⟨e.symm, ?_⟩
  intro col
  have heq : colOfRow (e.symm col) = col := e.apply_symm_apply col
  apply hsupport.support
  calc
    mate col = mate (colOfRow (e.symm col)) := congrArg mate heq.symm
    _ = some (e.symm col) := colOfRow_spec (e.symm col)

theorem kuhnColumnMate_all_rows_of_hasPerfectMatching {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ)
    (hperfect : Matrix.HasPerfectMatching A) :
    ∀ row, MatchesRow (kuhnColumnMate A) row := by
  obtain ⟨_, hrows⟩ := kuhnBuild_of_hasPerfectMatching A
    (List.finRange n) (emptyColumnMate n) hperfect
    (List.nodup_finRange n) (emptyColumnMate_support n A)
    (fun row _ ↦ rowUnmatched_emptyColumnMate n row)
  intro row
  simpa [kuhnColumnMate] using
    (hrows row).2 (Or.inr (List.mem_finRange row))

theorem kuhnSupportMatchingDecision_eq_true_iff {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    kuhnSupportMatchingDecision A = true ↔ Matrix.HasPerfectMatching A := by
  constructor
  · intro hdecision
    apply hasPerfectMatching_of_all_rows_matched A (kuhnColumnMate A)
      (kuhnColumnMate_support A)
    intro row
    have hrow := (List.all_eq_true.mp hdecision) row (List.mem_finRange row)
    exact (matchedRowDecision_eq_true_iff _ _).mp hrow
  · intro hperfect
    apply List.all_eq_true.mpr
    intro row _
    exact (matchedRowDecision_eq_true_iff _ _).mpr
      (kuhnColumnMate_all_rows_of_hasPerfectMatching A hperfect row)

theorem kuhnSupportMatchingDecision_eq_false_iff {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    kuhnSupportMatchingDecision A = false ↔ ¬Matrix.HasPerfectMatching A := by
  rw [← kuhnSupportMatchingDecision_eq_true_iff]
  exact Bool.eq_false_iff

theorem emptyColumnMate_apply (n : ℕ) (j : Fin n) :
    emptyColumnMate n j = none := rfl

theorem kuhnAugment_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) (row : Fin n)
    (seen : Finset (Fin n)) (mate : ColumnMate n) :
    kuhnAugment A 0 row seen mate = ⟨none, seen⟩ := by
  simp [kuhnAugment, kuhnSearch]

end BeyondBethe
