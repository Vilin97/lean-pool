/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Nonpositive
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Translation
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Supremum of the support of a nonpositive real Hahn series

For a Hahn series supported in `ℝ⁽≤0⁾`, `HahnSeries.Nonpositive.supportSup` is the
supremum from LM24, Definition 3.1.3. Its codomain is `WithBot ℝ`: the zero series has value
`⊥`, while a nonzero series has the ordinary real supremum of its nonempty, bounded support.
The least-upper-bound characterization certifies this semantic identification directly.

The addition and multiplication inequalities are LM24, Proposition 3.1.4. Normalization translates
a series by the negative of its real support supremum. A nonzero normalized series is again
nonpositive and has support supremum zero; this is the normalization used in the proof of LM24,
Proposition 3.3.7.

This operation is deliberately not extended to arbitrary real Hahn series. An unbounded support
has no value in `WithBot ℝ`, and LM24, Remark 3.3.9 uses precisely this obstruction to show that
arbitrary real Hahn series need not have normal forms.

The construction uses conditional completeness of the reals. Its public characterization and
monomial formula avoid exposing the underlying supremum calculation.
-/

universe v

public noncomputable section

namespace HahnSeries.Nonpositive

variable {R : Type v} [Ring R]

/-- The supremum of a nonpositive real Hahn-series support, with value `⊥` at zero. -/
def supportSup (x : Nonpositive ℝ R) : WithBot ℝ :=
  sSup ((fun a : ℝ ↦ (a : WithBot ℝ)) '' (x : R⟦ℝ⟧).support)

/-- Negation preserves the support supremum. -/
@[simp]
theorem supportSup_neg (x : Nonpositive ℝ R) : supportSup (-x) = supportSup x := by
  simp only [supportSup, Subring.coe_neg, HahnSeries.support_neg]

/-- A nonpositive real Hahn-series support is bounded above by zero. -/
theorem bddAbove_support (x : Nonpositive ℝ R) :
    BddAbove (x : R⟦ℝ⟧).support :=
  ⟨0, support_subset x⟩

@[simp]
theorem supportSup_zero : supportSup (0 : Nonpositive ℝ R) = ⊥ := by
  rw [supportSup]
  simp

/-- On a nonzero series, `supportSup` is the ordinary real supremum of the support. -/
theorem supportSup_of_ne {x : Nonpositive ℝ R} (hx : x ≠ 0) :
    supportSup x = (sSup (x : R⟦ℝ⟧).support : ℝ) := by
  rw [supportSup]
  have hx' : (x : R⟦ℝ⟧) ≠ 0 := by simpa using hx
  exact (WithBot.coe_sSup' (support_nonempty_iff.mpr hx') (bddAbove_support x)).symm

/-- The support supremum is `⊥` exactly at the zero series. -/
@[simp]
theorem supportSup_eq_bot {x : Nonpositive ℝ R} : supportSup x = ⊥ ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    rw [supportSup_of_ne hx] at h
    exact WithBot.coe_ne_bot h
  · rintro rfl
    exact supportSup_zero

/-- Characterization of a finite support-supremum value by the least-upper-bound property. -/
theorem supportSup_eq_coe_iff {x : Nonpositive ℝ R} {a : ℝ} :
    supportSup x = (a : WithBot ℝ) ↔
      x ≠ 0 ∧ IsLUB (x : R⟦ℝ⟧).support a := by
  constructor
  · intro h
    have hx : x ≠ 0 := by
      intro hzero
      subst x
      simp at h
    have hx' : (x : R⟦ℝ⟧) ≠ 0 := by simpa using hx
    rw [supportSup_of_ne hx, WithBot.coe_eq_coe] at h
    exact ⟨hx, h ▸ isLUB_csSup (support_nonempty_iff.mpr hx') (bddAbove_support x)⟩
  · rintro ⟨hx, ha⟩
    have hx' : (x : R⟦ℝ⟧) ≠ 0 := by simpa using hx
    rw [supportSup_of_ne hx, WithBot.coe_eq_coe]
    exact ha.csSup_eq (support_nonempty_iff.mpr hx')

/-- The support supremum of a nonpositive series is at most zero. -/
theorem supportSup_le_zero (x : Nonpositive ℝ R) : supportSup x ≤ 0 := by
  by_cases hx : x = 0
  · subst x
    simp
  · rw [supportSup_of_ne hx]
    norm_cast
    have hx' : (x : R⟦ℝ⟧) ≠ 0 := by simpa using hx
    exact csSup_le (support_nonempty_iff.mpr hx') (support_subset x)

/-- The support supremum of a nonzero monomial is its exponent. -/
theorem supportSup_single {x : ℝ} {r : R} (hr : r ≠ 0) (hx : x ≤ 0) :
    supportSup (single x r hx) = x := by
  have hne : single x r hx ≠ 0 := by
    intro h
    have h' : HahnSeries.single x r = (0 : R⟦ℝ⟧) := by
      simpa only [coe_single, Subring.coe_zero] using congrArg Subtype.val h
    exact HahnSeries.single_ne_zero hr h'
  rw [supportSup_of_ne hne]
  norm_cast
  rw [coe_single, HahnSeries.support_single_of_ne hr, csSup_singleton]

/-- Support supremum satisfies the ultrametric addition inequality. This is LM24, Proposition
3.1.4(1). -/
theorem supportSup_add_le (x y : Nonpositive ℝ R) :
    supportSup (x + y) ≤ max (supportSup x) (supportSup y) := by
  by_cases hsum : x + y = 0
  · rw [hsum, supportSup_zero]
    exact bot_le
  by_cases hx : x = 0
  · subst x
    simp
  by_cases hy : y = 0
  · subst y
    simp
  rw [supportSup_of_ne hsum, supportSup_of_ne hx, supportSup_of_ne hy]
  norm_cast
  have hsum' : ((x + y : Nonpositive ℝ R) : R⟦ℝ⟧) ≠ 0 :=
    fun h ↦ hsum (Subtype.ext h)
  apply csSup_le (support_nonempty_iff.mpr hsum')
  intro g hg
  rcases support_add_subset (x : R⟦ℝ⟧) y hg with hg | hg
  · exact (le_csSup (bddAbove_support x) hg).trans (le_max_left _ _)
  · exact (le_csSup (bddAbove_support y) hg).trans (le_max_right _ _)

/-- Support supremum is submultiplicative. This is LM24, Proposition 3.1.4(2). -/
theorem supportSup_mul_le (x y : Nonpositive ℝ R) :
    supportSup (x * y) ≤ supportSup x + supportSup y := by
  by_cases hxy : x * y = 0
  · rw [hxy, supportSup_zero]
    exact bot_le
  have hx : x ≠ 0 := fun h ↦ hxy (h ▸ zero_mul y)
  have hy : y ≠ 0 := fun h ↦ hxy (h ▸ mul_zero x)
  rw [supportSup_of_ne hxy, supportSup_of_ne hx, supportSup_of_ne hy]
  norm_cast
  have hxy' : ((x * y : Nonpositive ℝ R) : R⟦ℝ⟧) ≠ 0 :=
    fun h ↦ hxy (Subtype.ext h)
  apply csSup_le (support_nonempty_iff.mpr hxy')
  intro g hg
  obtain ⟨i, hi, j, hj, rfl⟩ := support_mul_subset hg
  exact add_le_add (le_csSup (bddAbove_support x) hi)
    (le_csSup (bddAbove_support y) hj)

end HahnSeries.Nonpositive

namespace HahnSeries

variable {R : Type v} [Ring R]

/-- Translating a nonzero bounded real Hahn-series support translates its real supremum. -/
theorem csSup_support_translate {x : R⟦ℝ⟧} (hx : x ≠ 0)
    (hbounded : BddAbove x.support) (a : ℝ) :
    sSup (translate a x).support = a + sSup x.support := by
  rw [support_translate]
  exact ((OrderIso.addLeft a).map_csSup' (support_nonempty_iff.mpr hx) hbounded).symm

namespace Nonpositive

/-- Translate a nonpositive series by the negative of the real supremum of its support. For a
nonzero series, the result has support supremum zero. -/
def normalize (x : Nonpositive ℝ R) : Nonpositive ℝ R :=
  ⟨translate (-sSup (x : R⟦ℝ⟧).support) x, by
    rw [mem_nonpositiveSubring, support_translate]
    rintro _ ⟨g, hg, rfl⟩
    have hgSup : g ≤ sSup (x : R⟦ℝ⟧).support :=
      le_csSup (bddAbove_support x) hg
    simpa [sub_eq_add_neg, add_comm] using sub_nonpos.mpr hgSup⟩

@[simp]
theorem coe_normalize (x : Nonpositive ℝ R) :
    (normalize x : R⟦ℝ⟧) = translate (-sSup (x : R⟦ℝ⟧).support) x :=
  (rfl)

@[simp]
theorem normalize_zero : normalize (0 : Nonpositive ℝ R) = 0 := by
  apply Subtype.ext
  simp

/-- Normalization preserves nonzeroness. -/
theorem normalize_ne_zero {x : Nonpositive ℝ R} (hx : x ≠ 0) : normalize x ≠ 0 := by
  intro hzero
  have hval := congrArg Subtype.val hzero
  change translate (-sSup (x : R⟦ℝ⟧).support) (x : R⟦ℝ⟧) = (0 : R⟦ℝ⟧) at hval
  have hxval : (x : R⟦ℝ⟧) = 0 :=
    (translate _).injective (hval.trans (map_zero _).symm)
  exact hx (Subtype.ext hxval)

/-- Translating a normalized series back by its original support supremum recovers the series. -/
theorem translate_csSup_normalize (x : Nonpositive ℝ R) :
    translate (sSup (x : R⟦ℝ⟧).support) (normalize x : R⟦ℝ⟧) = x := by
  rw [coe_normalize, translate_add_apply]
  simp

/-- Normalization preserves ordinary support order type. -/
theorem supportOrderType_normalize (x : Nonpositive ℝ R) :
    (normalize x : R⟦ℝ⟧).supportOrderType = (x : R⟦ℝ⟧).supportOrderType := by
  rw [coe_normalize, supportOrderType_translate]

/-- A nonzero normalized series has support supremum zero. -/
theorem supportSup_normalize {x : Nonpositive ℝ R} (hx : x ≠ 0) :
    supportSup (normalize x) = 0 := by
  rw [supportSup_of_ne (normalize_ne_zero hx)]
  norm_cast
  rw [coe_normalize, csSup_support_translate]
  · simp
  · simpa using hx
  · exact bddAbove_support x

end Nonpositive

end HahnSeries
