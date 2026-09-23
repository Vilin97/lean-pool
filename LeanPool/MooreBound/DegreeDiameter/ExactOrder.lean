/-
Copyright (c) 2026 Wouter Cames van Batenburg, Samuel Korsky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Cames van Batenburg, Samuel Korsky
-/

module

public import LeanPool.MooreBound.DegreeDiameter.CompletionCount
public import LeanPool.MooreBound.DegreeDiameter.FlagSpace
public import LeanPool.MooreBound.DegreeDiameter.FlagEnumeration

/-!
# Exact order of the halved flag graph

This file carries out the double count in Proposition 3.1.  A complete flag
is the same thing as an even partial flag together with a compatible odd
partial flag.  The equivalence is explicit, and the fibre over every even
partial flag has the exact cardinality `(q + 1)^k` proved in
`CompletionCount`.  Combining that equality with the exact q-factorial
enumeration of complete flags gives both the multiplication form and the
division form of the paper's vertex-count formula.

Lean Pool port of wewantmoore commit d59bd80ea93fabb9faf769e790ab47692645e022.
The port adds a namespace and adapts proofs to the current Mathlib APIs and repository style.
-/

@[expose] public section

namespace MooreBound

open Module

namespace DegreeDiameter

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [Finite V] [FiniteDimensional K V]

/-- The dependent type of compatible even/odd partial-flag pairs. -/
abbrev CompatiblePartialFlagPair (k : ℕ) :=
  Σ P : EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1),
    {Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1) // Compatible P Q}

/-- Splitting a complete flag into its parity parts is an equivalence onto
the type of compatible pairs.  This is the precise bijection used in the
double count. -/
noncomputable def completeFlagEquivCompatiblePartialFlagPair (k : ℕ) :
    CompleteFlag K V (2 * k + 1) ≃ CompatiblePartialFlagPair (K := K) (V := V) k where
  toFun F :=
    ⟨PartialFlag.ofComplete 0 F,
      ⟨PartialFlag.ofComplete 1 F, compatible_parts F⟩⟩
  invFun x := Classical.choose x.2.property
  left_inv F := by
    apply compatible_unique
      (P := PartialFlag.ofComplete 0 F)
      (Q := PartialFlag.ofComplete 1 F)
    · exact (Classical.choose_spec
        (show Compatible (PartialFlag.ofComplete 0 F)
          (PartialFlag.ofComplete 1 F) from compatible_parts F)).1
    · exact (Classical.choose_spec
        (show Compatible (PartialFlag.ofComplete 0 F)
          (PartialFlag.ofComplete 1 F) from compatible_parts F)).2
    · rfl
    · rfl
  right_inv x := by
    obtain ⟨P, Q, hPQ⟩ := x
    have hchosen := Classical.choose_spec hPQ
    change
      (⟨PartialFlag.ofComplete 0 (Classical.choose hPQ),
        ⟨PartialFlag.ofComplete 1 (Classical.choose hPQ),
          compatible_parts (Classical.choose hPQ)⟩⟩ :
        CompatiblePartialFlagPair (K := K) (V := V) k) =
      ⟨P, ⟨Q, hPQ⟩⟩
    have hpred : ∀ R : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1),
        Compatible (PartialFlag.ofComplete 0 (Classical.choose hPQ)) R ↔
          Compatible P R := by
      intro R
      rw [hchosen.1]
    apply Sigma.ext hchosen.1
    apply (Subtype.heq_iff_coe_eq hpred).2
    exact hchosen.2

/-- Exact double-counting identity before inserting the q-factorial formula:
the number of complete flags is the number of even partial flags times the
constant compatible-completion multiplicity. -/
theorem natCard_completeFlag_eq_evenPartialFlag_mul_completion (k : ℕ) :
    Nat.card (CompleteFlag K V (2 * k + 1)) =
      Nat.card (EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) *
        (Nat.card K + 1) ^ k := by
  classical
  let X := EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)
  let : Fintype X := Fintype.ofFinite X
  calc
    Nat.card (CompleteFlag K V (2 * k + 1)) =
        Nat.card (CompatiblePartialFlagPair (K := K) (V := V) k) :=
      Nat.card_congr (completeFlagEquivCompatiblePartialFlagPair
        (K := K) (V := V) k)
    _ = ∑ P : X,
          Nat.card {Q : OddPartialFlag (K := K) (V := V) (n := 2 * k + 1) //
            Compatible P Q} := Nat.card_sigma
    _ = ∑ _P : X, (Nat.card K + 1) ^ k := by
      apply Finset.sum_congr rfl
      intro P _hP
      exact natCard_odd_compatible_eq k P
    _ = Nat.card X * (Nat.card K + 1) ^ k := by
      simp [Nat.card_eq_fintype_card]

/-- Equation (6) of the write-up in multiplication form.  This form records
the exact double count without relying on truncated natural-number division. -/
theorem natCard_evenPartialFlag_mul_completion_eq_qFactorial (k : ℕ)
    (hV : finrank K V = 2 * k + 1) :
    Nat.card (EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) *
        (Nat.card K + 1) ^ k =
      qFactorial (Nat.card K) (2 * k + 1) := by
  rw [← natCard_completeFlag_eq_evenPartialFlag_mul_completion (K := K) (V := V) k]
  exact natCard_completeFlag_of_finrank hV

/-- Equation (6) of the write-up in its displayed division form. -/
theorem natCard_evenPartialFlag_eq_qFactorial_div (k : ℕ)
    (hV : finrank K V = 2 * k + 1) :
    Nat.card (EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) =
      qFactorial (Nat.card K) (2 * k + 1) / (Nat.card K + 1) ^ k := by
  have hmul := natCard_evenPartialFlag_mul_completion_eq_qFactorial
    (K := K) (V := V) k hV
  have hcompletion : 0 < (Nat.card K + 1) ^ k :=
    pow_pos (Nat.succ_pos (Nat.card K)) k
  calc
    Nat.card (EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) =
        (Nat.card (EvenPartialFlag (K := K) (V := V) (n := 2 * k + 1)) *
          (Nat.card K + 1) ^ k) / (Nat.card K + 1) ^ k := by
      rw [Nat.mul_div_left _ hcompletion]
    _ = qFactorial (Nat.card K) (2 * k + 1) / (Nat.card K + 1) ^ k := by
      rw [hmul]

/-- The same exact formula for the recursively split coordinate model used
by the big-cell construction. -/
theorem natCard_flagSpaceEvenPartialFlag_eq_qFactorial_div (k : ℕ) :
    Nat.card (EvenPartialFlag
      (K := K) (V := FlagSpace K k) (n := 2 * k + 1)) =
      qFactorial (Nat.card K) (2 * k + 1) / (Nat.card K + 1) ^ k := by
  apply natCard_evenPartialFlag_eq_qFactorial_div
  simpa [flagDim_eq] using finrank_flagSpace (K := K) k

end DegreeDiameter

end MooreBound
