/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Gluing.TwoPoleProfile

/-!
# Rank-one and doubled-point tests through two-pole responses

`TwoPoleProfile.lean` gives an exact scalar criterion for winnability of one
factor sum.  This file lifts that criterion to the two tests used by the
genus-five programmes:

* rank at least one, equivalently a response match after subtracting every
  possible single vertex;
* winnability after subtracting a prescribed doubled vertex.

The statements are equivalences.  They isolate the real work after restoring
the second cross-edge without replacing it by a stronger sufficient
condition.  They also apply to every seam phase and to arbitrary factor
divisors, not only canonical divisors or genus-two graphs.
-/

@[expose] public section

namespace Utilities
namespace TwoPole

universe u v
/-- Subtracting a pile at a left vertex stays entirely in the left factor. -/
theorem sumDivisor_sub_zsmul_one_chip_inl
    (A : CFGraph.{u}) (B : CFGraph.{v}) (p : TwoPole A) (q : TwoPole B)
    (D : CFDiv A) (E : CFDiv B) (a : A.V) (n : ℤ) :
    sumDivisor A B p q D E -
        n • oneChip (Sum.inl a : (join A B p q).V) =
      sumDivisor A B p q (D - n • oneChip a) E := by
  funext z
  cases z with
  | inl c =>
      by_cases hc : c = a
      · subst c
        simp [oneChip]
      · have hSum :
            (Sum.inl c : (join A B p q).V) ≠ Sum.inl a :=
          fun h => hc (Sum.inl.inj h)
        simp [oneChip, hc, hSum]
  | inr b => simp [oneChip]
/-- Subtracting a pile at a right vertex stays entirely in the right factor. -/
theorem sumDivisor_sub_zsmul_one_chip_inr
    (A : CFGraph.{u}) (B : CFGraph.{v}) (p : TwoPole A) (q : TwoPole B)
    (D : CFDiv A) (E : CFDiv B) (b : B.V) (n : ℤ) :
    sumDivisor A B p q D E -
        n • oneChip (Sum.inr b : (join A B p q).V) =
      sumDivisor A B p q D (E - n • oneChip b) := by
  funext z
  cases z with
  | inl a => simp [oneChip]
  | inr c =>
      by_cases hc : c = b
      · subst c
        simp [oneChip]
      · have hSum :
            (Sum.inr c : (join A B p q).V) ≠ Sum.inr b :=
          fun h => hc (Sum.inr.inj h)
        simp [oneChip, hc, hSum]

theorem sumDivisor_sub_one_chip_inl
    (A : CFGraph.{u}) (B : CFGraph.{v}) (p : TwoPole A) (q : TwoPole B)
    (D : CFDiv A) (E : CFDiv B) (a : A.V) :
    sumDivisor A B p q D E - oneChip (Sum.inl a) =
      sumDivisor A B p q (D - oneChip a) E := by
  simpa using sumDivisor_sub_zsmul_one_chip_inl A B p q D E a 1

theorem sumDivisor_sub_one_chip_inr
    (A : CFGraph.{u}) (B : CFGraph.{v}) (p : TwoPole A) (q : TwoPole B)
    (D : CFDiv A) (E : CFDiv B) (b : B.V) :
    sumDivisor A B p q D E - oneChip (Sum.inr b) =
      sumDivisor A B p q D (E - oneChip b) := by
  simpa using sumDivisor_sub_zsmul_one_chip_inr A B p q D E b 1

/-- The exact factor-response data for rank one of a factor sum.  The first
component handles targets in the left factor and the second handles targets
in the right factor. -/
def HasRankOneResponseCover
    {A : CFGraph.{u}} {B : CFGraph.{v}}
    (p : TwoPole A) (q : TwoPole B) (D : CFDiv A) (E : CFDiv B) : Prop :=
  (∀ a : A.V, ∃ c₁ c₂ s t : ℤ,
      IsDebitResponse p (D - oneChip a) c₁ c₂ s ∧
      IsCreditResponse q E c₁ c₂ t ∧
      s - t = c₁ - c₂) ∧
  (∀ b : B.V, ∃ c₁ c₂ s t : ℤ,
      IsDebitResponse p D c₁ c₂ s ∧
      IsCreditResponse q (E - oneChip b) c₁ c₂ t ∧
      s - t = c₁ - c₂)

/-- **Exact rank-one response criterion.** -/
theorem rank_sumDivisor_ge_one_iff_responseCover
    (A : CFGraph.{u}) (B : CFGraph.{v}) (p : TwoPole A) (q : TwoPole B)
    (D : CFDiv A) (E : CFDiv B) :
    rank (join A B p q) (sumDivisor A B p q D E) ≥ 1 ↔
      HasRankOneResponseCover p q D E := by
  rw [rank_ge_one_iff_winnable_sub_one_chip]
  constructor
  · intro hRank
    constructor
    · intro a
      have hWin := hRank (Sum.inl a)
      rw [sumDivisor_sub_one_chip_inl] at hWin
      exact (winnable_sumDivisor_iff_exists_responses
        A B p q (D - oneChip a) E).mp hWin
    · intro b
      have hWin := hRank (Sum.inr b)
      rw [sumDivisor_sub_one_chip_inr] at hWin
      exact (winnable_sumDivisor_iff_exists_responses
        A B p q D (E - oneChip b)).mp hWin
  · rintro ⟨hLeft, hRight⟩ z
    cases z with
    | inl a =>
        rw [sumDivisor_sub_one_chip_inl]
        exact (winnable_sumDivisor_iff_exists_responses
          A B p q (D - oneChip a) E).mpr (hLeft a)
    | inr b =>
        rw [sumDivisor_sub_one_chip_inr]
        exact (winnable_sumDivisor_iff_exists_responses
          A B p q D (E - oneChip b)).mpr (hRight b)

/-- The same exact rank-one criterion at an arbitrary seam phase. -/
theorem rank_phase_sumDivisor_ge_one_iff_responseCover
    (A : CFGraph.{u}) (B : CFGraph.{v}) (p : TwoPole A) (q : TwoPole B)
    (D : CFDiv A) (E : CFDiv B) (n : ℤ) :
    rank (join A B p q) (phase A B p q (sumDivisor A B p q D E) n) ≥ 1 ↔
      HasRankOneResponseCover p q
        (D + n • oneChip p.second) (E - n • oneChip q.second) := by
  rw [phase_sumDivisor]
  exact rank_sumDivisor_ge_one_iff_responseCover A B p q _ _

/-- A doubled left target is winnable exactly when its two factor residuals
have a compatible response. -/
theorem winnable_sumDivisor_sub_two_inl_iff_responses
    (A : CFGraph.{u}) (B : CFGraph.{v}) (p : TwoPole A) (q : TwoPole B)
    (D : CFDiv A) (E : CFDiv B) (a : A.V) :
    winnable (join A B p q)
        (sumDivisor A B p q D E - (2 : ℤ) • oneChip (Sum.inl a)) ↔
      ∃ c₁ c₂ s t : ℤ,
        IsDebitResponse p (D - (2 : ℤ) • oneChip a) c₁ c₂ s ∧
        IsCreditResponse q E c₁ c₂ t ∧
        s - t = c₁ - c₂ := by
  rw [sumDivisor_sub_zsmul_one_chip_inl]
  exact winnable_sumDivisor_iff_exists_responses
    A B p q (D - (2 : ℤ) • oneChip a) E

/-- A doubled right target is winnable exactly when its two factor residuals
have a compatible response. -/
theorem winnable_sumDivisor_sub_two_inr_iff_responses
    (A : CFGraph.{u}) (B : CFGraph.{v}) (p : TwoPole A) (q : TwoPole B)
    (D : CFDiv A) (E : CFDiv B) (b : B.V) :
    winnable (join A B p q)
        (sumDivisor A B p q D E - (2 : ℤ) • oneChip (Sum.inr b)) ↔
      ∃ c₁ c₂ s t : ℤ,
        IsDebitResponse p D c₁ c₂ s ∧
        IsCreditResponse q (E - (2 : ℤ) • oneChip b) c₁ c₂ t ∧
        s - t = c₁ - c₂ := by
  rw [sumDivisor_sub_zsmul_one_chip_inr]
  exact winnable_sumDivisor_iff_exists_responses
    A B p q D (E - (2 : ℤ) • oneChip b)

/-- The doubled-left test at an arbitrary seam phase. -/
theorem winnable_phase_sumDivisor_sub_two_inl_iff_responses
    (A : CFGraph.{u}) (B : CFGraph.{v}) (p : TwoPole A) (q : TwoPole B)
    (D : CFDiv A) (E : CFDiv B) (n : ℤ) (a : A.V) :
    winnable (join A B p q)
        (phase A B p q (sumDivisor A B p q D E) n -
          (2 : ℤ) • oneChip (Sum.inl a)) ↔
      ∃ c₁ c₂ s t : ℤ,
        IsDebitResponse p
            (D + n • oneChip p.second - (2 : ℤ) • oneChip a)
            c₁ c₂ s ∧
        IsCreditResponse q (E - n • oneChip q.second) c₁ c₂ t ∧
        s - t = c₁ - c₂ := by
  rw [phase_sumDivisor, winnable_sumDivisor_sub_two_inl_iff_responses]

/-- The doubled-right test at an arbitrary seam phase. -/
theorem winnable_phase_sumDivisor_sub_two_inr_iff_responses
    (A : CFGraph.{u}) (B : CFGraph.{v}) (p : TwoPole A) (q : TwoPole B)
    (D : CFDiv A) (E : CFDiv B) (n : ℤ) (b : B.V) :
    winnable (join A B p q)
        (phase A B p q (sumDivisor A B p q D E) n -
          (2 : ℤ) • oneChip (Sum.inr b)) ↔
      ∃ c₁ c₂ s t : ℤ,
        IsDebitResponse p (D + n • oneChip p.second) c₁ c₂ s ∧
        IsCreditResponse q
            (E - n • oneChip q.second - (2 : ℤ) • oneChip b)
            c₁ c₂ t ∧
        s - t = c₁ - c₂ := by
  rw [phase_sumDivisor, winnable_sumDivisor_sub_two_inr_iff_responses]

/-- The two-edge `K_A + K_B` statement is exactly a canonical response cover.
This theorem is useful both as a proof interface and as an honest record of
the phase obligation that the one-pole Riemann--Roch argument does not see. -/
theorem rank_canonicalSum_ge_one_iff_responseCover
    (A : CFGraph.{u}) (B : CFGraph.{v}) (p : TwoPole A) (q : TwoPole B) :
    rank (join A B p q) (canonicalSum A B p q) ≥ 1 ↔
      HasRankOneResponseCover p q (canonicalDivisor A) (canonicalDivisor B) := by
  exact rank_sumDivisor_ge_one_iff_responseCover
    A B p q (canonicalDivisor A) (canonicalDivisor B)

end TwoPole
end Utilities
