/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.GKPCarry.BadCarryCounting
import LeanPool.GKPCarry.PowerResidues

/-!
# Counting deficient-carry ternary units

Powers of two modulo a power of three range over unit residues, whose least
significant ternary digit is nonzero. This file refines the full-word automaton
count to that unit slice. Among unit words of length `n + 3`, exactly
`(n + 9) * 2 ^ n` create fewer than two doubling carries.
-/

namespace GKPCarry

/-- Natural value of a fixed-length ternary word. -/
def ternaryWordValue {length : ℕ}
    (word : List.Vector (Fin 3) length) : ℕ :=
  Nat.ofDigits 3 (ternaryWordDigits word)

lemma ternaryWordValue_lt {length : ℕ}
    (word : List.Vector (Fin 3) length) :
    ternaryWordValue word < 3 ^ length := by
  simpa [ternaryWordValue, ternaryWordDigits] using
    (Nat.ofDigits_lt_base_pow_length (b := 3) (by decide)
      (by simp [ternaryWordDigits] :
        ∀ digit ∈ ternaryWordDigits word, digit < 3))

/-- The value of a ternary word, packaged in its complete residue block. -/
def ternaryWordValueFin {length : ℕ}
    (word : List.Vector (Fin 3) length) : Fin (3 ^ length) :=
  ⟨ternaryWordValue word, ternaryWordValue_lt word⟩

lemma ternaryWordValueFin_injective (length : ℕ) :
    Function.Injective
      (ternaryWordValueFin :
        List.Vector (Fin 3) length → Fin (3 ^ length)) := by
  intro word₁ word₂ hvalue
  apply List.Vector.toList_injective
  apply (List.map_injective_iff.mpr Fin.val_injective)
  apply Nat.ofDigits_inj_of_len_eq (b := 3) (by decide)
  · simp
  · simp
  · simp
  · exact congrArg Fin.val hvalue

/-- Fixed-length ternary words with a nonzero least significant digit. The
parameter is the tail length, so the full word has length `length + 1`. -/
abbrev TernaryUnitWords (length : ℕ) :=
  {word : List.Vector (Fin 3) (length + 1) // word.head.val ≠ 0}

lemma ternaryWordValue_mod_three {length : ℕ}
    (word : List.Vector (Fin 3) (length + 1)) :
    ternaryWordValue word % 3 = word.head.val := by
  rw [ternaryWordValue, ternaryWordDigits_succ, Nat.ofDigits_cons]
  have hlt := word.head.isLt
  omega

lemma ternaryWordValue_coprime_three_pow_iff {length : ℕ}
    (word : List.Vector (Fin 3) (length + 1)) :
    Nat.Coprime (ternaryWordValue word) (3 ^ (length + 1)) ↔
      word.head.val ≠ 0 := by
  rw [Nat.coprime_pow_right_iff (by omega), Nat.coprime_comm,
    Nat.prime_three.coprime_iff_not_dvd, Nat.dvd_iff_mod_eq_zero,
    ternaryWordValue_mod_three]

/-- Split a unit word into its nonzero head digit and its remaining digits. -/
def ternaryUnitWordsHeadTailEquiv (length : ℕ) :
    TernaryUnitWords length ≃
      {digit : Fin 3 // digit.val ≠ 0} × List.Vector (Fin 3) length where
  toFun word := (⟨word.val.head, word.property⟩, word.val.tail)
  invFun pair :=
    ⟨List.Vector.cons pair.1.val pair.2, by simpa using pair.1.property⟩
  left_inv word := by
    apply Subtype.ext
    exact List.Vector.cons_head_tail word.val
  right_inv pair := by
    rcases pair with ⟨⟨digit, hdigit⟩, tail⟩
    simp

/-- There are `2 * 3 ^ length` unit words with `length + 1` ternary digits. -/
theorem card_ternaryUnitWords (length : ℕ) :
    Fintype.card (TernaryUnitWords length) = 2 * 3 ^ length := by
  rw [Fintype.card_congr (ternaryUnitWordsHeadTailEquiv length),
    Fintype.card_prod]
  have hhead : Fintype.card {digit : Fin 3 // digit.val ≠ 0} = 2 := by
    decide
  rw [hhead]
  simp

/-- Convert a ternary unit word to the corresponding unit modulo a power of
three. -/
def ternaryUnitWordToUnit (length : ℕ) :
    TernaryUnitWords length → (ZMod (3 ^ (length + 1)))ˣ :=
  fun word => ZMod.unitOfCoprime (ternaryWordValue word.val)
    ((ternaryWordValue_coprime_three_pow_iff word.val).mpr word.property)

lemma ternaryUnitWordToUnit_injective (length : ℕ) :
    Function.Injective (ternaryUnitWordToUnit length) := by
  intro word₁ word₂ hequal
  apply Subtype.ext
  apply ternaryWordValueFin_injective (length + 1)
  apply Fin.ext
  have hcoe := congrArg
    (fun unit : (ZMod (3 ^ (length + 1)))ˣ =>
      (unit : ZMod (3 ^ (length + 1)))) hequal
  change
    (ternaryWordValue word₁.val : ZMod (3 ^ (length + 1))) =
      (ternaryWordValue word₂.val : ZMod (3 ^ (length + 1))) at hcoe
  have hmod := (ZMod.natCast_eq_natCast_iff'
    (ternaryWordValue word₁.val) (ternaryWordValue word₂.val)
    (3 ^ (length + 1))).mp hcoe
  rw [Nat.mod_eq_of_lt (ternaryWordValue_lt word₁.val),
    Nat.mod_eq_of_lt (ternaryWordValue_lt word₂.val)] at hmod
  exact hmod

/-- Unit words are equivalent to the full unit group modulo the corresponding
power of three. -/
noncomputable def ternaryUnitWordEquiv (length : ℕ) :
    TernaryUnitWords length ≃ (ZMod (3 ^ (length + 1)))ˣ :=
  Equiv.ofBijective (ternaryUnitWordToUnit length) <|
    (Fintype.bijective_iff_injective_and_card _).2
      ⟨ternaryUnitWordToUnit_injective length, by
        rw [card_ternaryUnitWords, card_units_three_pow_succ]⟩

@[simp]
theorem ternaryUnitWordEquiv_apply (length : ℕ)
    (word : TernaryUnitWords length) :
    ternaryUnitWordEquiv length word = ternaryUnitWordToUnit length word :=
  rfl

theorem val_ternaryUnitWordEquiv_apply (length : ℕ)
    (word : TernaryUnitWords length) :
    ((ternaryUnitWordEquiv length word :
        (ZMod (3 ^ (length + 1)))ˣ) : ZMod (3 ^ (length + 1))).val =
      ternaryWordValue word.val := by
  change
    (ternaryWordValue word.val : ZMod (3 ^ (length + 1))).val =
      ternaryWordValue word.val
  rw [ZMod.val_natCast,
    Nat.mod_eq_of_lt (ternaryWordValue_lt word.val)]

lemma ternaryDoubleCarryCountAux_replicate_zero
    (count carry : ℕ) (hcarry : carry ≤ 1) :
    ternaryDoubleCarryCountAux (List.replicate count 0) carry = 0 := by
  induction count generalizing carry with
  | zero => simp [ternaryDoubleCarryCountAux]
  | succ count ih =>
      have hstep : ternaryDoubleCarryStep carry 0 = 0 := by
        simp [ternaryDoubleCarryStep]
        omega
      simp [List.replicate_succ, ternaryDoubleCarryCountAux,
        hstep, ih 0 (by omega)]

lemma ternaryDoubleCarryCountAux_append_replicate_zero
    (digits : List ℕ) (count carry : ℕ) (hcarry : carry ≤ 1) :
    ternaryDoubleCarryCountAux (digits ++ List.replicate count 0) carry =
      ternaryDoubleCarryCountAux digits carry := by
  induction digits generalizing carry with
  | nil =>
      simpa [ternaryDoubleCarryCountAux] using
        ternaryDoubleCarryCountAux_replicate_zero count carry hcarry
  | cons digit digits ih =>
      simp only [List.cons_append, ternaryDoubleCarryCountAux]
      rw [ih (ternaryDoubleCarryStep carry digit)
        (ternaryDoubleCarryStep_le_one carry digit)]

lemma ternaryDoubleCarryCount_append_replicate_zero
    (digits : List ℕ) (count : ℕ) :
    ternaryDoubleCarryCount (digits ++ List.replicate count 0) =
      ternaryDoubleCarryCount digits := by
  exact ternaryDoubleCarryCountAux_append_replicate_zero
    digits count 0 (by omega)

/-- Fixed-length leading zeroes do not change the carry count, so a word and
the canonical ternary expansion of its value have the same count. -/
theorem ternaryDoubleCarryCount_word_eq_value {length : ℕ}
    (word : List.Vector (Fin 3) length) :
    ternaryDoubleCarryCount (ternaryWordDigits word) =
      ternaryDoubleCarryCount (Nat.digits 3 (ternaryWordValue word)) := by
  have hword :
      ternaryWordDigits word ∈
        {digits : List ℕ |
          digits.length = length ∧ ∀ digit ∈ digits, digit < 3} := by
    simp [ternaryWordDigits]
  have hinverse :
      Nat.digitsAppend 3 length (ternaryWordValue word) =
        ternaryWordDigits word := by
    simpa [ternaryWordValue] using
      (Nat.setInvOn_digitsAppend_ofDigits (b := 3) (by decide) length).1 hword
  rw [← hinverse, Nat.digitsAppend,
    ternaryDoubleCarryCount_append_replicate_zero]

/-! ## Deficient-carry unit words -/

/-- Unit words whose doubling produces fewer than two carries. -/
abbrev UnitBadCarryWords (length : ℕ) :=
  {word : TernaryUnitWords length //
    badCarryStateAux (ternaryWordDigits word.val) .zeroCarry ≠ .good}

/-- Remove the nonzero leading digit and record the automaton state it enters. -/
def unitBadCarryWordsToSum (length : ℕ) :
    UnitBadCarryWords length →
      BadCarryWordsFrom .zeroCarry length ⊕
        BadCarryWordsFrom .oneCarryOut length := fun word => by
  by_cases hone : word.val.val.head.val = 1
  · apply Sum.inl
    refine ⟨word.val.val.tail, ?_⟩
    have hbad := word.property
    rw [ternaryWordDigits_succ] at hbad
    simpa [badCarryStateAux, badCarryStateStep, hone] using hbad
  · apply Sum.inr
    refine ⟨word.val.val.tail, ?_⟩
    have htwo : word.val.val.head.val = 2 := by
      have hlt := word.val.val.head.isLt
      have hne := word.val.property
      omega
    have hbad := word.property
    rw [ternaryWordDigits_succ] at hbad
    simpa [badCarryStateAux, badCarryStateStep, htwo] using hbad

/-- Peeling the nonzero least significant digit splits deficient unit words
into the states reached by digit `1` and digit `2`. -/
def unitBadCarryWordsEquiv (length : ℕ) :
    UnitBadCarryWords length ≃
      BadCarryWordsFrom .zeroCarry length ⊕
        BadCarryWordsFrom .oneCarryOut length where
  toFun := unitBadCarryWordsToSum length
  invFun result := by
    rcases result with tail | tail
    · exact
        ⟨⟨List.Vector.cons ⟨1, by omega⟩ tail.val, by simp⟩,
          by simpa [ternaryWordDigits, badCarryStateAux,
            badCarryStateStep] using tail.property⟩
    · exact
        ⟨⟨List.Vector.cons ⟨2, by omega⟩ tail.val, by simp⟩,
          by simpa [ternaryWordDigits, badCarryStateAux,
            badCarryStateStep] using tail.property⟩
  left_inv word := by
    apply Subtype.ext
    apply Subtype.ext
    by_cases hone : word.val.val.head.val = 1
    · simp only [unitBadCarryWordsToSum, hone, dif_pos]
      have hhead : (1 : Fin 3) = word.val.val.head := by
        apply Fin.ext
        exact hone.symm
      exact (congrArg
        (fun digit : Fin 3 => List.Vector.cons digit word.val.val.tail)
        hhead).trans (List.Vector.cons_head_tail word.val.val)
    · have htwo : word.val.val.head.val = 2 := by
        have hlt := word.val.val.head.isLt
        have hne := word.val.property
        omega
      simp only [unitBadCarryWordsToSum, hone]
      have hhead : (2 : Fin 3) = word.val.val.head := by
        apply Fin.ext
        exact htwo.symm
      exact (congrArg
        (fun digit : Fin 3 => List.Vector.cons digit word.val.val.tail)
        hhead).trans (List.Vector.cons_head_tail word.val.val)
  right_inv result := by
    rcases result with tail | tail
    · simp [unitBadCarryWordsToSum]
    · simp [unitBadCarryWordsToSum]

/-- Exact deficient-carry count on ternary unit words of length `n + 3`. -/
theorem card_unitBadCarryWords (n : ℕ) :
    Fintype.card (UnitBadCarryWords (n + 2)) =
      (n + 9) * 2 ^ n := by
  rw [Fintype.card_congr (unitBadCarryWordsEquiv (n + 2)),
    Fintype.card_sum]
  change
    Fintype.card (BadCarryWords (n + 2)) +
        Fintype.card (BadCarryWordsFrom .oneCarryOut (n + 2)) =
      (n + 9) * 2 ^ n
  rw [card_badCarryWords n, card_badCarryWordsFrom_eq_count]
  rw [show n + 2 = (n + 1) + 1 by omega,
    badCarryWordCountFrom_oneCarryOut_succ, pow_succ]
  ring

end GKPCarry
