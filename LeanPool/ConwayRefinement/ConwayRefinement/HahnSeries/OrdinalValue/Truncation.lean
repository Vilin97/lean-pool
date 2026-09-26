/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Germ
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

import Mathlib.Tactic.Linarith

/-!
# Berarducci germs at a real exponent

For a real Hahn series `b` and an exponent `γ`, `Berarducci.translatedTruncation b γ` restricts
`b` to exponents at most `γ` and translates `γ` to zero. Its image in
`Berarducci.Germ K` is `Berarducci.germAt b γ`.

Two series have the same germ at `γ` exactly when their coefficients agree on an interval
`(η, γ]`. The right endpoint is essential: after translation, a discrepancy at `γ` is a
nonzero constant and therefore does not belong to Berarducci's ideal `J`.

Berarducci, Remark 6.3: the translated truncation `b^{|γ}` lies in `J` unless `γ` belongs to the
closure of the support of `b`.

-/

universe v

public noncomputable section

namespace Berarducci

open HahnSeries

variable {K : Type v} [Field K]

/-- Restrict a real Hahn series at `γ` and translate `γ` to zero, obtaining a nonpositive
series. -/
def translatedTruncation (b : K⟦ℝ⟧) (γ : ℝ) : Series K :=
  ⟨HahnSeries.translate (-γ) (HahnSeries.truncLE γ b), by
    rw [HahnSeries.mem_nonpositiveSubring]
    rw [HahnSeries.support_translate]
    rintro δ ⟨x, hx, rfl⟩
    rw [HahnSeries.support_truncLE] at hx
    change -γ + x ≤ 0
    linarith [hx.2]⟩

/-- The underlying Hahn series of the translated closed truncation. -/
theorem coe_translatedTruncation (b : K⟦ℝ⟧) (γ : ℝ) :
    ((translatedTruncation b γ : Series K) : K⟦ℝ⟧) =
      HahnSeries.translate (-γ) (HahnSeries.truncLE γ b) :=
  (rfl)

/-- The support of the translated truncation is the translated closed lower support. -/
theorem support_translatedTruncation (b : K⟦ℝ⟧) (γ : ℝ) :
    ((translatedTruncation b γ : Series K) : K⟦ℝ⟧).support =
      (-γ + ·) '' {x ∈ b.support | x ≤ γ} := by
  simp only [translatedTruncation, HahnSeries.support_translate, HahnSeries.support_truncLE]

/-- The coefficient at `δ ≤ 0` is the original coefficient at `γ + δ`; all positive
coefficients vanish. -/
@[simp]
theorem coeff_translatedTruncation (b : K⟦ℝ⟧) (γ δ : ℝ) :
    ((translatedTruncation b γ : Series K) : K⟦ℝ⟧).coeff δ =
      if δ ≤ 0 then b.coeff (γ + δ) else 0 := by
  simp only [translatedTruncation, HahnSeries.coeff_translate, HahnSeries.coeff_truncLE]
  have hindex : δ - -γ = γ + δ := by
    simp [add_comm]
  rw [hindex]
  by_cases hδ : δ ≤ 0
  · have hle : γ + δ ≤ γ := by linarith
    simp [hδ, hle]
  · have hnot : ¬γ + δ ≤ γ := by linarith
    simp [hδ, hnot]

/-- Translated closed truncation preserves addition. -/
theorem translatedTruncation_add (b c : K⟦ℝ⟧) (γ : ℝ) :
    translatedTruncation (b + c) γ = translatedTruncation b γ + translatedTruncation c γ := by
  apply Subtype.ext
  ext δ
  change
    ((translatedTruncation (b + c) γ : Series K) : K⟦ℝ⟧).coeff δ =
      ((translatedTruncation b γ : Series K) : K⟦ℝ⟧).coeff δ +
        ((translatedTruncation c γ : Series K) : K⟦ℝ⟧).coeff δ
  rw [coeff_translatedTruncation, coeff_translatedTruncation, coeff_translatedTruncation]
  by_cases hδ : δ ≤ 0 <;> simp [hδ]

/-- Translated closed truncation commutes with multiplication by a constant Hahn series. -/
theorem translatedTruncation_C_mul (k : K) (b : K⟦ℝ⟧) (γ : ℝ) :
    translatedTruncation (HahnSeries.C k * b) γ =
      (HahnSeries.Nonpositive.C : K →+* Series K) k * translatedTruncation b γ := by
  apply Subtype.ext
  ext δ
  rw [coeff_translatedTruncation, Subring.coe_mul, HahnSeries.Nonpositive.coe_C]
  simp only [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul,
    coeff_translatedTruncation]
  by_cases hδ : δ ≤ 0 <;> simp [hδ]

/-- Translated closed truncation sends the zero series to zero. -/
@[simp]
theorem translatedTruncation_zero_input (γ : ℝ) :
    translatedTruncation (0 : K⟦ℝ⟧) γ = 0 := by
  apply Subtype.ext
  ext δ
  rw [coeff_translatedTruncation]
  simp

/-- Translated closed truncation at a fixed exponent as an additive homomorphism. -/
def translatedTruncationAddMonoidHom (γ : ℝ) : K⟦ℝ⟧ →+ Series K where
  toFun b := translatedTruncation b γ
  map_zero' := translatedTruncation_zero_input γ
  map_add' b c := translatedTruncation_add b c γ

/-- Evaluation of the additive translated-truncation map. -/
@[simp]
theorem translatedTruncationAddMonoidHom_apply (γ : ℝ) (b : K⟦ℝ⟧) :
    translatedTruncationAddMonoidHom γ b = translatedTruncation b γ :=
  by
    rw [translatedTruncationAddMonoidHom]
    rfl

/-- Truncation and translation at zero leave a nonpositive series unchanged. -/
@[simp]
theorem translatedTruncation_zero (b : Series K) :
    translatedTruncation (b : K⟦ℝ⟧) 0 = b := by
  apply Subtype.ext
  ext δ
  rw [coeff_translatedTruncation]
  by_cases hδ : δ ≤ 0
  · simp [hδ]
  · rw [ite_eq_right hδ]
    apply Eq.symm
    apply not_ne_iff.mp
    rw [← HahnSeries.mem_support]
    exact fun hmem ↦ hδ (HahnSeries.Nonpositive.support_subset b hmem)

/-- The germ at `γ` of the monomial supported at `γ` is represented by its coefficient as a
constant series. -/
theorem translatedTruncation_single_cut (k : K) (γ : ℝ) :
    translatedTruncation (HahnSeries.single γ k) γ = HahnSeries.Nonpositive.C k := by
  apply Subtype.ext
  ext δ
  rw [coeff_translatedTruncation]
  by_cases hδ : δ = 0
  · subst δ
    simp
  · by_cases hδ0 : δ ≤ 0
    · have hsum : γ + δ ≠ γ := by
        intro h
        apply hδ
        exact add_left_cancel (a := γ) (by simpa using h)
      simp [hδ0, hsum, hδ]
    · simp [hδ0, hδ]

/-- A translated truncation of a translated truncation is the translated truncation at the sum
of the exponents, when the second exponent is nonpositive: `(b^{|γ})^{|γ'} = b^{|γ + γ'}`. -/
theorem translatedTruncation_translatedTruncation (b : K⟦ℝ⟧) (γ : ℝ) {γ' : ℝ} (hγ' : γ' ≤ 0) :
    translatedTruncation ((translatedTruncation b γ : Series K) : K⟦ℝ⟧) γ' =
      translatedTruncation b (γ + γ') := by
  apply Subtype.ext
  ext δ
  simp only [coeff_translatedTruncation]
  by_cases hδ : δ ≤ 0
  · simp [hδ, add_nonpos hγ' hδ, add_assoc]
  · simp [hδ]

/-- The Berarducci germ at the real exponent `γ`. -/
def germAt (b : K⟦ℝ⟧) (γ : ℝ) : Germ K :=
  toGerm (translatedTruncation b γ)

/-- Evaluation of the germ at `γ` through the quotient map. -/
@[simp]
theorem germAt_apply (b : K⟦ℝ⟧) (γ : ℝ) :
    germAt b γ = toGerm (translatedTruncation b γ) :=
  (rfl)

/-- Two real Hahn series have the same germ at `γ` exactly when their coefficients agree on
some interval `(η, γ]`. -/
theorem germAt_eq_germAt_iff_exists_coeff_eq {b c : K⟦ℝ⟧} {γ : ℝ} :
    germAt b γ = germAt c γ ↔
      ∃ η < γ, ∀ δ : ℝ, η < δ → δ ≤ γ → b.coeff δ = c.coeff δ := by
  rw [germAt_apply, germAt_apply, toGerm_eq_toGerm_iff_exists_coeff_eq]
  constructor
  · rintro ⟨ε, hε, heq⟩
    refine ⟨γ + ε, by linarith, fun δ hεδ hδγ ↦ ?_⟩
    have hshiftLower : ε < δ - γ := by linarith
    have hshiftUpper : δ - γ ≤ 0 := by linarith
    have h := heq (δ - γ) hshiftLower hshiftUpper
    rw [coeff_translatedTruncation, coeff_translatedTruncation, ite_eq_left hshiftUpper,
      ite_eq_left hshiftUpper] at h
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
  · rintro ⟨η, hη, heq⟩
    refine ⟨η - γ, by linarith, fun δ hεδ hδ0 ↦ ?_⟩
    have hLower : η < γ + δ := by linarith
    have hUpper : γ + δ ≤ γ := by linarith
    rw [coeff_translatedTruncation, coeff_translatedTruncation, ite_eq_left hδ0, ite_eq_left hδ0]
    exact heq (γ + δ) hLower hUpper

/-- A germ taken at a point outside the closure of the support vanishes. -/
theorem germAt_eq_zero_of_not_mem_closure_support {b : K⟦ℝ⟧} {γ : ℝ}
    (h : γ ∉ closure b.support) : germAt b γ = 0 := by
  rw [Metric.mem_closure_iff] at h
  push Not at h
  obtain ⟨ε, hε, hall⟩ := h
  have hzero : (0 : Germ K) = toGerm 0 := by simp
  rw [germAt_apply, hzero, toGerm_eq_toGerm_iff_exists_coeff_eq]
  refine ⟨-ε, by linarith, fun δ hδlow hδ0 ↦ ?_⟩
  rw [coeff_translatedTruncation, ite_eq_left hδ0]
  simp only [Subring.coe_zero, HahnSeries.coeff_zero]
  by_contra hcoeff
  have hmem : γ + δ ∈ b.support := (HahnSeries.mem_support _ _).mpr hcoeff
  have hdist := hall (γ + δ) hmem
  rw [Real.dist_eq] at hdist
  have habs : |γ - (γ + δ)| = -δ := by
    rw [show γ - (γ + δ) = -δ by ring, abs_of_nonneg (by linarith)]
  rw [habs] at hdist
  linarith

/-- A translated truncation taken at a point outside the closure of the support lies in `J`. -/
theorem translatedTruncation_mem_negativeMonomialIdeal_of_not_mem_closure_support
    {b : K⟦ℝ⟧} {γ : ℝ} (h : γ ∉ closure b.support) :
    translatedTruncation b γ ∈ HahnSeries.Nonpositive.negativeMonomialIdeal K := by
  have hzero := germAt_eq_zero_of_not_mem_closure_support h
  rwa [germAt_apply, toGerm_apply, Ideal.Quotient.eq_zero_iff_mem] at hzero

end Berarducci
