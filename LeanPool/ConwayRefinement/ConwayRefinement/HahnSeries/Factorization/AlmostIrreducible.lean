/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Monomial
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.RealSupportSupremum
public import Mathlib.Algebra.Group.Irreducible.Defs
public import Mathlib.GroupTheory.Divisible

import Mathlib.Algebra.GroupWithZero.Divisibility

/-!
# Almost-irreducible Hahn series

LM24, Section 6.5 weakens irreducibility for a divisible additive subgroup `H ⊆ ℝ`. A
series is almost irreducible when, in every factorisation, a nonmonomial factor forces the other
factor to be a monomial.

The three consequences surrounding LM24, Remark 6.5.1 are formalized explicitly. Irreducibility
implies almost irreducibility, and a strictly negative real support supremum prevents
irreducibility. The printed converse at support supremum zero omits the condition that the series
is not a unit: `1` is almost irreducible and has support supremum zero, but is not irreducible.
The corrected theorem below adds exactly that missing condition. The definition itself is not
changed, because monomials are intended to remain almost irreducible later in LM24.
-/

open scoped HahnSeries

universe v

public noncomputable section

namespace HahnSeries.Nonpositive

variable {H : AddSubgroup ℝ} {K : Type v} [Field K]

/-- Every factorisation with a nonmonomial left factor has a monomial right factor. This is
LM24's notion of an almost-irreducible series from Section 6.5. -/
def IsAlmostIrreducible (b : Nonpositive H K) : Prop :=
  ∀ c d : Nonpositive H K, b = c * d → ¬IsMonomial c → IsMonomial d

/-- Characterization of almost irreducibility by factorisations. -/
theorem isAlmostIrreducible_iff {b : Nonpositive H K} :
    IsAlmostIrreducible b ↔
      ∀ c d : Nonpositive H K, b = c * d → ¬IsMonomial c → IsMonomial d :=
  Iff.rfl

/-- An almost-irreducible series is nonzero. -/
theorem IsAlmostIrreducible.ne_zero {b : Nonpositive H K}
    (hb : IsAlmostIrreducible b) : b ≠ 0 := by
  intro hzero
  subst b
  have hzeroNotMonomial : ¬IsMonomial (0 : Nonpositive H K) :=
    fun h ↦ h.ne_zero rfl
  exact (hb 0 0 (by simp) hzeroNotMonomial).ne_zero rfl

/-- An irreducible nonpositive Hahn series is almost irreducible. This is the first assertion of
LM24, Remark 6.5.1. -/
theorem Irreducible.isAlmostIrreducible {b : Nonpositive H K}
    (hb : Irreducible b) : IsAlmostIrreducible b := by
  intro c d hfactor hc
  rcases hb.isUnit_or_isUnit hfactor with hcUnit | hdUnit
  · exact (hc (isMonomial_of_isUnit hcUnit)).elim
  · exact isMonomial_of_isUnit hdUnit

/-- The multiplicative identity is almost irreducible. This is the counterexample showing that
the printed support-supremum-zero implication in LM24, Remark 6.5.1 needs a nonunit hypothesis.
-/
theorem one_isAlmostIrreducible :
    IsAlmostIrreducible (1 : Nonpositive H K) := by
  intro c d hfactor _
  exact isMonomial_of_isUnit (IsUnit.of_mul_eq_one_right c hfactor.symm)

/-- A monomial divisor of a series with real support supremum zero is a unit. -/
theorem IsMonomial.isUnit_of_dvd_of_realSupportSup_eq_zero
    {b c : Nonpositive H K} (hc : IsMonomial c) (hcb : c ∣ b)
    (hbSup : realSupportSup H b = 0) : IsUnit c := by
  obtain ⟨d, hfactor⟩ := hcb
  obtain ⟨g, k, hg, hk, rfl⟩ := isMonomial_iff.mp hc
  rcases lt_or_eq_of_le hg with hgNeg | rfl
  · have hlub := (Iff.mp (realSupportSup_eq_coe_iff H) hbSup).2
    have hgUpper : (g : ℝ) ∈ upperBounds
        ((fun h : H ↦ (h : ℝ)) '' (b : K⟦H⟧).support) := by
      rintro _ ⟨z, hz, rfl⟩
      rw [hfactor] at hz
      obtain ⟨x, hx, y, hy, rfl⟩ := HahnSeries.support_mul_subset hz
      have hxg : x = g := by
        have hx' : x ∈ (HahnSeries.single g k : K⟦H⟧).support := by
          simpa only [coe_single] using hx
        simpa [HahnSeries.support_single_of_ne hk] using hx'
      subst x
      have hyNonpos := support_subset d hy
      exact_mod_cast (add_le_of_nonpos_right hyNonpos)
    have hzeroLe : (0 : ℝ) ≤ g := hlub.2 hgUpper
    exfalso
    exact (not_le_of_gt (show (g : ℝ) < 0 by exact_mod_cast hgNeg)) hzeroLe
  · have hconstant : single (0 : H) k le_rfl = (C : K →+* Nonpositive H K) k := by
      apply Subtype.ext
      rw [coe_single, coe_C]
      rfl
    rw [hconstant]
    exact (isUnit_iff_ne_zero.mpr hk).map C

/-- Corrected support-supremum-zero implication from LM24, Remark 6.5.1. An
almost-irreducible nonunit with real support supremum zero is irreducible. -/
theorem IsAlmostIrreducible.irreducible_of_not_isUnit_of_realSupportSup_eq_zero
    {b : Nonpositive H K} (hb : IsAlmostIrreducible b) (hbNotUnit : ¬IsUnit b)
    (hbSup : realSupportSup H b = 0) : Irreducible b := by
  rw [irreducible_iff]
  refine ⟨hbNotUnit, ?_⟩
  intro c d hfactor
  by_cases hc : IsMonomial c
  · exact Or.inl (hc.isUnit_of_dvd_of_realSupportSup_eq_zero
      ⟨d, hfactor⟩ hbSup)
  · have hd := hb c d hfactor hc
    exact Or.inr (hd.isUnit_of_dvd_of_realSupportSup_eq_zero
      ⟨c, by simpa [mul_comm] using hfactor⟩ hbSup)

/-- A series with strictly negative real support supremum is not irreducible. This is the final
assertion of LM24, Remark 6.5.1. -/
theorem not_irreducible_of_realSupportSup_lt_zero [DivisibleBy H ℤ]
    {b : Nonpositive H K} (hbSup : realSupportSup H b < 0) : ¬Irreducible b := by
  letI : DivisibleBy H ℕ := AddGroup.divisibleByNatOfDivisibleByInt H
  intro hbIrreducible
  have hbNe : b ≠ 0 := hbIrreducible.ne_zero
  have hbSupNeBot : realSupportSup H b ≠ ⊥ := by
    intro hbot
    exact hbNe (Iff.mp (realSupportSup_eq_bot H) hbot)
  obtain ⟨s, hsSup⟩ := WithBot.ne_bot_iff_exists.mp hbSupNeBot
  have hsSup' : realSupportSup H b = (s : WithBot ℝ) := hsSup.symm
  have hsNeg : s < 0 := by
    rw [hsSup'] at hbSup
    exact_mod_cast hbSup
  have hlub := (Iff.mp (realSupportSup_eq_coe_iff H) hsSup').2
  have htwoSNotUpper : (2 * s : ℝ) ∉ upperBounds
      ((fun h : H ↦ (h : ℝ)) '' (b : K⟦H⟧).support) := by
    intro htwoSUpper
    have hsLeTwoS := hlub.2 htwoSUpper
    linarith
  rw [mem_upperBounds] at htwoSNotUpper
  push Not at htwoSNotUpper
  obtain ⟨_, ⟨y, hySupport, rfl⟩, hyLower⟩ := htwoSNotUpper
  have hyUpper : (y : ℝ) ≤ s := hlub.1 ⟨y, hySupport, rfl⟩
  have hyNeg : (y : ℝ) < 0 := hyUpper.trans_lt hsNeg
  let x : H := DivisibleBy.div y (2 : ℕ)
  have htwoX : 2 • x = y := DivisibleBy.div_cancel y (by norm_num)
  have htwoXReal : (x : ℝ) + x = y := by
    exact_mod_cast (by simpa [two_nsmul] using htwoX)
  have hsLtX : s < (x : ℝ) := by linarith
  have hxNeg : (x : ℝ) < 0 := by linarith
  have hxNonpos : x ≤ 0 := by exact_mod_cast hxNeg.le
  let dFull : K⟦H⟧ := HahnSeries.single (-x) 1 * (b : K⟦H⟧)
  have hdSupportStrict : ∀ z ∈ dFull.support, z < 0 := by
    intro z hz
    obtain ⟨u, hu, v, hv, rfl⟩ := HahnSeries.support_mul_subset hz
    have huEq : u = -x := by
      simpa [HahnSeries.support_single_of_ne one_ne_zero] using hu
    subst u
    have hvLe : (v : ℝ) ≤ s := hlub.1 ⟨v, hv, rfl⟩
    exact_mod_cast (show (-(x : ℝ) + v) < 0 by linarith)
  let d : Nonpositive H K :=
    ⟨dFull, by
      rw [HahnSeries.mem_nonpositiveSubring]
      exact fun z hz ↦ (hdSupportStrict z hz).le⟩
  have hfactor : b = single x 1 hxNonpos * d := by
    apply Subtype.ext
    rw [Subring.coe_mul, coe_single]
    change (b : K⟦H⟧) = HahnSeries.single x 1 * dFull
    simp [dFull, ← mul_assoc]
  have hxNonzero : x ≠ 0 := by
    intro hxZero
    exact (ne_of_lt hxNeg) (congrArg Subtype.val hxZero)
  have hxNotUnit : ¬IsUnit (single x (1 : K) hxNonpos) := by
    rw [isUnit_single_iff (G := H) (K := K) one_ne_zero hxNonpos]
    exact hxNonzero
  have hdNotUnit : ¬IsUnit d := by
    intro hdUnit
    have hsupport := support_eq_singleton_zero_of_isUnit hdUnit
    have hzeroMem : (0 : H) ∈ (d : K⟦H⟧).support := by simp [hsupport]
    exact (lt_irrefl (0 : H)) (hdSupportStrict 0 hzeroMem)
  exact hxNotUnit
    (hbIrreducible.isUnit_or_isUnit hfactor |>.resolve_right hdNotUnit)

end HahnSeries.Nonpositive
