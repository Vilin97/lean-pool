/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Nonpositive

import Mathlib.Algebra.GroupWithZero.Divisibility

/-!
# Monomials in a nonpositive Hahn-series ring

A monomial is a nonzero scalar multiple of a single group monomial. This is the notion used
throughout LM24 and, in particular, in Section 6.5. The support-singleton characterization is
intrinsic and avoids exposing the proof that the exponent is nonpositive.

The unit lemmas record a boundary specific to the nonpositive ring: every unit has support
exactly `{0}`, and hence a nonzero monomial is a unit precisely when its exponent is zero.
-/

open scoped HahnSeries

universe u v

public noncomputable section

namespace HahnSeries.Nonpositive

variable {G : Type u} {K : Type v}
  [LinearOrder G] [AddCommGroup G] [IsOrderedAddMonoid G]
  [Field K]

/-- A nonzero scalar multiple of one group monomial. -/
def IsMonomial (b : Nonpositive G K) : Prop :=
  ∃ (g : G) (k : K) (hg : g ≤ 0), k ≠ 0 ∧ b = single g k hg

/-- Characterization of a monomial by an exponent, a nonzero coefficient, and a single Hahn
monomial. -/
theorem isMonomial_iff {b : Nonpositive G K} :
    IsMonomial b ↔
      ∃ (g : G) (k : K) (hg : g ≤ 0), k ≠ 0 ∧ b = single g k hg :=
  Iff.rfl

/-- A nonpositive Hahn series is a monomial exactly when its support is a singleton. -/
theorem isMonomial_iff_support_eq_singleton {b : Nonpositive G K} :
    IsMonomial b ↔ ∃ g : G, (b : K⟦G⟧).support = {g} := by
  constructor
  · rintro ⟨g, k, hg, hk, rfl⟩
    exact ⟨g, by simp [coe_single, hk]⟩
  · rintro ⟨g, hsupport⟩
    have hgmem : g ∈ (b : K⟦G⟧).support := by simp [hsupport]
    have hg : g ≤ 0 := support_subset b hgmem
    have hk : (b : K⟦G⟧).coeff g ≠ 0 := by
      rwa [HahnSeries.mem_support] at hgmem
    refine ⟨g, (b : K⟦G⟧).coeff g, hg, hk, ?_⟩
    apply Subtype.ext
    ext h
    by_cases hh : h = g
    · subst h
      simp [coe_single]
    · have hhmem : h ∉ (b : K⟦G⟧).support := by simp [hsupport, hh]
      rw [HahnSeries.mem_support, not_ne_iff] at hhmem
      simp [coe_single, hh, hhmem]

/-- A monomial is nonzero. -/
theorem IsMonomial.ne_zero {b : Nonpositive G K} (hb : IsMonomial b) : b ≠ 0 := by
  rw [isMonomial_iff_support_eq_singleton] at hb
  obtain ⟨g, hg⟩ := hb
  intro hzero
  subst b
  simp at hg

/-- A monomial has finite support. -/
theorem IsMonomial.support_finite {b : Nonpositive G K} (hb : IsMonomial b) :
    (b : K⟦G⟧).support.Finite := by
  obtain ⟨g, hg⟩ := isMonomial_iff_support_eq_singleton.mp hb
  rw [hg]
  exact Set.finite_singleton g

/-- Every unit of the nonpositive Hahn-series ring has support exactly `{0}`. -/
theorem support_eq_singleton_zero_of_isUnit {b : Nonpositive G K} (hb : IsUnit b) :
    (b : K⟦G⟧).support = {0} := by
  obtain ⟨u, rfl⟩ := hb
  let c : Nonpositive G K := ↑u⁻¹
  have hbNe : (↑u : Nonpositive G K) ≠ 0 := IsUnit.ne_zero u.isUnit
  have hcNe : c ≠ 0 := IsUnit.ne_zero (u⁻¹).isUnit
  have hbNe' : ((↑u : Nonpositive G K) : K⟦G⟧) ≠ 0 :=
    fun h ↦ hbNe (Subtype.ext h)
  have hcNe' : (c : K⟦G⟧) ≠ 0 := fun h ↦ hcNe (Subtype.ext h)
  have hproduct : (↑u : Nonpositive G K) * c = 1 := by
    simp [c]
  have horder := congrArg HahnSeries.order (congrArg Subtype.val hproduct)
  have horder' : (↑u : K⟦G⟧).order + (c : K⟦G⟧).order = 0 := by
    simpa [HahnSeries.order_mul hbNe' hcNe'] using horder
  have hbOrderMem : (↑u : K⟦G⟧).order ∈ (↑u : K⟦G⟧).support := by
    rw [HahnSeries.mem_support]
    exact HahnSeries.coeff_order_eq_zero.not.mpr hbNe'
  have hcOrderMem : (c : K⟦G⟧).order ∈ (c : K⟦G⟧).support := by
    rw [HahnSeries.mem_support]
    exact HahnSeries.coeff_order_eq_zero.not.mpr hcNe'
  have hbOrderNonpos := support_subset (↑u : Nonpositive G K) hbOrderMem
  have hcOrderNonpos := support_subset c hcOrderMem
  have hbOrderZero : (↑u : K⟦G⟧).order = 0 :=
    eq_zero_of_add_nonneg_left hbOrderNonpos hcOrderNonpos horder'.ge
  apply Set.Subset.antisymm
  · intro g hg
    rw [Set.mem_singleton_iff]
    apply le_antisymm (support_subset (↑u : Nonpositive G K) hg)
    rw [← hbOrderZero]
    rw [HahnSeries.mem_support] at hg
    exact HahnSeries.order_le_of_coeff_ne_zero hg
  · intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst g
    simpa [hbOrderZero] using hbOrderMem

/-- Every unit is the constant series determined by its coefficient at zero. -/
theorem eq_C_constantCoeff_of_isUnit {b : Nonpositive G K} (hb : IsUnit b) :
    b = C (constantCoeff b) := by
  have hsupport := support_eq_singleton_zero_of_isUnit hb
  apply Subtype.ext
  apply HahnSeries.coeff_injective
  funext g
  by_cases hg : g = 0
  · subst g
    simp [constantCoeff_apply]
  · have hgNotMem : g ∉ (b : K⟦G⟧).support := by
      rw [hsupport]
      simpa using hg
    rw [HahnSeries.mem_support, not_ne_iff] at hgNotMem
    simp [hg, hgNotMem]

/-- Every unit of the nonpositive Hahn-series ring is a monomial. -/
theorem isMonomial_of_isUnit {b : Nonpositive G K} (hb : IsUnit b) :
    IsMonomial b :=
  isMonomial_iff_support_eq_singleton.mpr
    ⟨0, support_eq_singleton_zero_of_isUnit hb⟩

/-- A unit with constant coefficient one is the multiplicative identity. -/
theorem eq_one_of_isUnit_of_constantCoeff_eq_one {b : Nonpositive G K}
    (hbUnit : IsUnit b) (hbConstant : constantCoeff b = 1) : b = 1 := by
  have hsupport := support_eq_singleton_zero_of_isUnit hbUnit
  apply Subtype.ext
  apply HahnSeries.coeff_injective
  funext g
  by_cases hg : g = 0
  · subst g
    simpa [constantCoeff_apply] using hbConstant
  · have hgNotMem : g ∉ (b : K⟦G⟧).support := by
      rw [hsupport]
      simpa using hg
    rw [HahnSeries.mem_support, not_ne_iff] at hgNotMem
    simp [hg, hgNotMem]

/-- A nonzero monomial in the nonpositive ring is a unit exactly at exponent zero. -/
theorem isUnit_single_iff {g : G} {k : K} (hk : k ≠ 0) (hg : g ≤ 0) :
    IsUnit (single g k hg) ↔ g = 0 := by
  constructor
  · intro hunit
    have hsupport := support_eq_singleton_zero_of_isUnit hunit
    rw [coe_single, HahnSeries.support_single_of_ne hk] at hsupport
    exact Set.singleton_injective hsupport
  · rintro rfl
    have hconstant : single (0 : G) k le_rfl = (C : K →+* Nonpositive G K) k := by
      apply Subtype.ext
      rw [coe_single, coe_C]
      rfl
    rw [hconstant]
    exact (isUnit_iff_ne_zero.mpr hk).map C

end HahnSeries.Nonpositive
