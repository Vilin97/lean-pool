/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.NegativeMonomialIdeal
public import Mathlib.RingTheory.Ideal.Prime

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Statements.ProductValue

/-!
# Multiplicativity of the support supremum

LM24, Proposition 3.5.1(2) states that support supremum is multiplicative on nonpositive real
Hahn series. The paragraph preceding the proposition cites Berarducci, Corollary 9.8: the ideal
`negativeMonomialIdeal K` is prime. This module first proves the proposition from that exact
prerequisite, with zero factors handled explicitly, and then discharges the prerequisite using
the formalized Berarducci theorem.

For nonzero `b` and `c`, normalize both supports to have supremum zero. Primality prevents the
normalized product from having strictly negative supremum. Translating the product back then
adds the original real suprema. The resulting theorem is valid for all inputs because `⊥` is
absorbing under addition.

The converse is also proved: full support-supremum multiplicativity implies that the
negative-monomial ideal is prime. Thus
`negativeMonomialIdeal_isPrime_iff_supportSup_mul` records the equivalence.

The optional normal-form proof printed after LM24, Proposition 3.5.1 assumes strict inequalities
between consecutive normal-form exponents, although the source definition permits equality. The
prime-ideal argument above does not require that extra assumption.
-/

universe v

public noncomputable section

namespace HahnSeries.Nonpositive

variable {K : Type v} [Field K]

/-- If the negative-monomial ideal is prime, the product of two series with support supremum zero
again has support supremum zero. -/
theorem supportSup_mul_eq_zero_of_negativeMonomialIdeal_isPrime
    (hJ : (negativeMonomialIdeal K).IsPrime)
    {b c : Nonpositive ℝ K}
    (hb : supportSup b = 0) (hc : supportSup c = 0) :
    supportSup (b * c) = 0 := by
  apply le_antisymm (supportSup_le_zero (b * c))
  apply le_of_not_gt
  intro hproduct
  have hmem : b * c ∈ negativeMonomialIdeal K :=
    mem_negativeMonomialIdeal_iff_supportSup_lt_zero.mpr hproduct
  rcases hJ.mem_or_mem hmem with hbmem | hcmem
  · rw [mem_negativeMonomialIdeal_iff_supportSup_lt_zero, hb] at hbmem
    exact (lt_irrefl (0 : WithBot ℝ)) hbmem
  · rw [mem_negativeMonomialIdeal_iff_supportSup_lt_zero, hc] at hcmem
    exact (lt_irrefl (0 : WithBot ℝ)) hcmem

/-- LM24, Proposition 3.5.1(2), reduced to its cited Berarducci prerequisite that the
negative-monomial ideal is prime. The equality includes zero factors via the absorbing bottom
convention. -/
theorem supportSup_mul_of_negativeMonomialIdeal_isPrime
    (hJ : (negativeMonomialIdeal K).IsPrime)
    (b c : Nonpositive ℝ K) :
    supportSup (b * c) = supportSup b + supportSup c := by
  by_cases hb : b = 0
  · subst b
    simp
  by_cases hc : c = 0
  · subst c
    simp
  have hbc : b * c ≠ 0 := mul_ne_zero hb hc
  have hnormalizedProduct :
      supportSup (normalize b * normalize c) = 0 :=
    supportSup_mul_eq_zero_of_negativeMonomialIdeal_isPrime hJ
      (supportSup_normalize hb) (supportSup_normalize hc)
  have hnormalizedProductNe : normalize b * normalize c ≠ 0 :=
    mul_ne_zero (normalize_ne_zero hb) (normalize_ne_zero hc)
  have hnormalizedProductNe' :
      (((normalize b * normalize c : Nonpositive ℝ K) : K⟦ℝ⟧)) ≠ 0 := by
    intro hzero
    exact hnormalizedProductNe (Subtype.ext hzero)
  have hnormalizedProductSup :
      sSup (((normalize b * normalize c : Nonpositive ℝ K) : K⟦ℝ⟧).support) = 0 := by
    rw [supportSup_of_ne hnormalizedProductNe] at hnormalizedProduct
    exact WithBot.coe_eq_coe.mp hnormalizedProduct
  have hproduct :
      (((b * c : Nonpositive ℝ K) : K⟦ℝ⟧)) =
        translate
          (sSup (b : K⟦ℝ⟧).support + sSup (c : K⟦ℝ⟧).support)
          ((normalize b * normalize c : Nonpositive ℝ K) : K⟦ℝ⟧) := by
    calc
      (((b * c : Nonpositive ℝ K) : K⟦ℝ⟧)) =
          (b : K⟦ℝ⟧) * (c : K⟦ℝ⟧) := rfl
      _ = translate (sSup (b : K⟦ℝ⟧).support) (normalize b : K⟦ℝ⟧) *
          translate (sSup (c : K⟦ℝ⟧).support) (normalize c : K⟦ℝ⟧) := by
        rw [translate_csSup_normalize, translate_csSup_normalize]
      _ = _ := translate_mul_translate _ _ _ _
  rw [supportSup_of_ne hbc, supportSup_of_ne hb, supportSup_of_ne hc]
  norm_cast
  calc
    sSup ((((b * c : Nonpositive ℝ K) : K⟦ℝ⟧)).support) =
        sSup
          (translate
            (sSup (b : K⟦ℝ⟧).support + sSup (c : K⟦ℝ⟧).support)
            ((normalize b * normalize c : Nonpositive ℝ K) : K⟦ℝ⟧)).support :=
      congrArg (fun z : K⟦ℝ⟧ ↦ sSup z.support) hproduct
    _ = (sSup (b : K⟦ℝ⟧).support + sSup (c : K⟦ℝ⟧).support) +
        sSup (((normalize b * normalize c : Nonpositive ℝ K) : K⟦ℝ⟧).support) :=
      csSup_support_translate
        (x := ((normalize b * normalize c : Nonpositive ℝ K) : K⟦ℝ⟧))
        hnormalizedProductNe' (bddAbove_support (normalize b * normalize c)) _
    _ = sSup (b : K⟦ℝ⟧).support + sSup (c : K⟦ℝ⟧).support := by
      rw [hnormalizedProductSup, add_zero]

/-- LM24, Proposition 3.5.1(2): support supremum is multiplicative on nonpositive real Hahn
series. The equality includes zero factors via the absorbing bottom convention. -/
theorem supportSup_mul [CharZero K] (b c : Nonpositive ℝ K) :
    supportSup (b * c) = supportSup b + supportSup c :=
  supportSup_mul_of_negativeMonomialIdeal_isPrime
    Berarducci.negativeMonomialIdeal_isPrime b c

/-- Primality of the negative-monomial ideal is equivalent to multiplicativity of support
supremum on all nonpositive real Hahn series. -/
theorem negativeMonomialIdeal_isPrime_iff_supportSup_mul :
    (negativeMonomialIdeal K).IsPrime ↔
      ∀ b c : Nonpositive ℝ K,
        supportSup (b * c) = supportSup b + supportSup c := by
  constructor
  · exact fun hJ b c =>
      supportSup_mul_of_negativeMonomialIdeal_isPrime hJ b c
  · intro hmul
    rw [Ideal.isPrime_iff]
    refine ⟨negativeMonomialIdeal_ne_top, ?_⟩
    intro b c hbc
    rw [mem_negativeMonomialIdeal_iff_supportSup_lt_zero] at hbc
    rw [hmul] at hbc
    by_cases hb : b = 0
    · left
      rw [hb]
      exact (negativeMonomialIdeal K).zero_mem
    by_cases hc : c = 0
    · right
      rw [hc]
      exact (negativeMonomialIdeal K).zero_mem
    have hbSup : sSup (b : K⟦ℝ⟧).support ≤ 0 :=
      csSup_le
        (support_nonempty_iff.mpr (by simpa using hb))
        (support_subset b)
    rw [supportSup_of_ne hb, supportSup_of_ne hc] at hbc
    have hbc' :
        sSup (b : K⟦ℝ⟧).support + sSup (c : K⟦ℝ⟧).support < 0 := by
      exact_mod_cast hbc
    rcases lt_or_eq_of_le hbSup with hbNeg | hbZero
    · left
      rw [mem_negativeMonomialIdeal_iff_supportSup_lt_zero,
        supportSup_of_ne hb]
      exact WithBot.coe_lt_coe.mpr hbNeg
    · right
      rw [hbZero, zero_add] at hbc'
      rw [mem_negativeMonomialIdeal_iff_supportSup_lt_zero,
        supportSup_of_ne hc]
      exact WithBot.coe_lt_coe.mpr hbc'

end HahnSeries.Nonpositive
