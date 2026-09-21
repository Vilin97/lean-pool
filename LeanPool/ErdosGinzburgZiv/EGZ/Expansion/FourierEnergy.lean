/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Expansion.SetGrowth
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-!
# Fourier energy of translation boundaries

The character basis diagonalizes translation.  This file develops the
finite sum identities used in the spectral growth estimate directly,
without introducing a weighted graph or its eigenvalues.
-/

open scoped BigOperators ComplexConjugate
open RCLike

namespace EGZ.Expansion

theorem re_sum {ι : Type*} (I : Finset ι) (f : ι → ℂ) :
    (∑ i ∈ I, f i).re = ∑ i ∈ I, (f i).re :=
  map_sum Complex.reAddGroupHom f I

section InnerSums

variable {G ι : Type*} [Fintype G]

theorem wInner_sum_left (I : Finset ι) (w : G → ℝ) (f : ι → G → ℂ) (g : G → ℂ) :
    ⟪∑ i ∈ I, f i, g⟫_[ℂ, w] = ∑ i ∈ I, ⟪f i, g⟫_[ℂ, w] := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih => simp only [Finset.sum_insert hi, RCLike.wInner_add_left, ih]

theorem wInner_sum_right (I : Finset ι) (w : G → ℝ) (f : G → ℂ) (g : ι → G → ℂ) :
    ⟪f, ∑ i ∈ I, g i⟫_[ℂ, w] = ∑ i ∈ I, ⟪f, g i⟫_[ℂ, w] := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih => simp only [Finset.sum_insert hi, RCLike.wInner_add_right, ih]

end InnerSums

section Fourier

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Coordinates in the normalized orthonormal character basis. -/
noncomputable def fourierCoeff (f : G → ℂ) (χ : AddChar G ℂ) : ℂ :=
  (AddChar.complexBasis G).repr f χ

theorem fourier_expansion (f : G → ℂ) :
    (∑ χ : AddChar G ℂ, fourierCoeff f χ • (χ : G → ℂ)) = f := by
  simpa only [fourierCoeff, AddChar.complexBasis_apply] using
    (AddChar.complexBasis G).sum_repr f

theorem inner_character_sums (c d : AddChar G ℂ → ℂ) :
    ⟪∑ χ, c χ • (χ : G → ℂ), ∑ χ, d χ • (χ : G → ℂ)⟫ₙ_[ℂ] =
      ∑ χ, conj (c χ) * d χ := by
  classical
  rw [wInner_sum_left]
  simp_rw [RCLike.wInner_smul_left, wInner_sum_right, RCLike.wInner_smul_right,
    AddChar.wInner_cWeight_eq_boole, smul_eq_mul]
  simp

/-- Finite Parseval identity in normalized character coordinates. -/
theorem fourier_inner (f g : G → ℂ) :
    ⟪f, g⟫ₙ_[ℂ] = ∑ χ, conj (fourierCoeff f χ) * fourierCoeff g χ := by
  rw [← inner_character_sums, fourier_expansion, fourier_expansion]

theorem fourierCoeff_eq_inner (f : G → ℂ) (χ : AddChar G ℂ) :
    fourierCoeff f χ = ⟪(χ : G → ℂ), f⟫ₙ_[ℂ] := by
  classical
  conv_rhs => rw [← fourier_expansion f]
  rw [wInner_sum_right]
  simp_rw [RCLike.wInner_smul_right, AddChar.wInner_cWeight_eq_boole, smul_eq_mul]
  simp

theorem fourier_translation_inner (f : G → ℂ) (a : G) :
    ⟪f, (fun x ↦ f (x + a))⟫ₙ_[ℂ] =
      ∑ χ, (conj (fourierCoeff f χ) * fourierCoeff f χ) * χ a := by
  have htrans : (fun x ↦ f (x + a)) =
      ∑ χ : AddChar G ℂ, (fourierCoeff f χ * χ a) • (χ : G → ℂ) := by
    funext x
    have hh := congrFun (fourier_expansion f) (x + a)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, AddChar.map_add_eq_mul] at hh ⊢
    rw [← hh]
    apply Finset.sum_congr rfl
    intro χ _
    ring
  rw [htrans]
  conv_lhs => arg 2; rw [← fourier_expansion f]
  rw [inner_character_sums]
  apply Finset.sum_congr rfl
  intro χ _
  ring

end Fourier

section Indicator

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The complex-valued indicator of a finite subset of the group. -/
noncomputable def setIndicator (Y : Finset G) (x : G) : ℂ := if x ∈ Y then 1 else 0

/-- The proportion of group elements belonging to the finite subset. -/
noncomputable def density (Y : Finset G) : ℝ := Y.card / Fintype.card G

omit [AddCommGroup G] in
theorem sum_setIndicator (Y : Finset G) : (∑ x, setIndicator Y x) = (Y.card : ℂ) := by
  simp [setIndicator]

omit [AddCommGroup G] in
theorem inner_setIndicator_self (Y : Finset G) :
    ⟪setIndicator Y, setIndicator Y⟫ₙ_[ℂ] = (density Y : ℂ) := by
  rw [RCLike.wInner_cWeight_eq_expect, Fintype.expect_eq_sum_div_card]
  have heq (x : G) : inner ℂ (setIndicator Y x) (setIndicator Y x) = setIndicator Y x := by
    by_cases hx : x ∈ Y <;> simp [setIndicator, hx]
  simp_rw [heq]
  rw [sum_setIndicator]
  simp [density]

theorem fourierCoeff_setIndicator_zero (Y : Finset G) :
    fourierCoeff (setIndicator Y) 0 = (density Y : ℂ) := by
  rw [fourierCoeff_eq_inner, RCLike.wInner_cWeight_eq_expect,
    Fintype.expect_eq_sum_div_card]
  simp only [AddChar.zero_apply, RCLike.inner_apply, map_one, mul_one]
  rw [sum_setIndicator]
  simp [density]

theorem sum_fourierCoeff_normSq (Y : Finset G) :
    (∑ χ : AddChar G ℂ, Complex.normSq (fourierCoeff (setIndicator Y) χ)) = density Y := by
  have h := congrArg Complex.re (fourier_inner (setIndicator Y) (setIndicator Y))
  rw [inner_setIndicator_self] at h
  simpa only [Complex.ofReal_re, re_sum, ← Complex.normSq_eq_conj_mul_self] using h.symm

theorem inner_setIndicator_translation (Y : Finset G) (a : G) :
    ⟪setIndicator Y, (fun x ↦ setIndicator Y (x - a))⟫ₙ_[ℂ] =
      ((translate Y a ∩ Y).card : ℂ) / Fintype.card G := by
  rw [RCLike.wInner_cWeight_eq_expect, Fintype.expect_eq_sum_div_card]
  congr 1
  have heq (x : G) : inner ℂ (setIndicator Y x) (setIndicator Y (x - a)) =
      if x ∈ translate Y a ∩ Y then (1 : ℂ) else 0 := by
    by_cases hx : x ∈ Y <;> by_cases hxa : x - a ∈ Y <;>
      simp [setIndicator, hx, hxa]
  simp_rw [heq]
  simpa only [setIndicator] using sum_setIndicator (translate Y a ∩ Y)

/-- The energy of one translation, expressed in character coordinates. -/
theorem boundary_fourier (Y : Finset G) (a : G) :
    (boundary Y a : ℝ) / Fintype.card G = density Y -
      ∑ χ : AddChar G ℂ, Complex.normSq (fourierCoeff (setIndicator Y) χ) *
        (χ (-a)).re := by
  have h := congrArg Complex.re (fourier_translation_inner (setIndicator Y) (-a))
  simp only [← sub_eq_add_neg] at h
  rw [inner_setIndicator_translation] at h
  have hreal : ((translate Y a ∩ Y).card : ℝ) / Fintype.card G =
      ∑ χ : AddChar G ℂ, Complex.normSq (fourierCoeff (setIndicator Y) χ) * (χ (-a)).re := by
    have hc : ((((translate Y a ∩ Y).card : ℝ) / Fintype.card G : ℝ) : ℂ) =
        ((translate Y a ∩ Y).card : ℂ) / Fintype.card G := by simp
    rw [← hc, Complex.ofReal_re, re_sum] at h
    simpa only [← Complex.normSq_eq_conj_mul_self, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using h
  rw [← hreal, density, ← sub_div]
  congr 1
  have hh := boundary_add_overlap Y a
  have hr : (boundary Y a : ℝ) + (translate Y a ∩ Y).card = Y.card := by exact_mod_cast hh
  linarith

end Indicator

section SpectralGrowth

variable {G ι : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] [Fintype ι]

/-- Fourier identity for an arbitrary finite real-weighted family of
translations, allowing repeated translation vectors. -/
theorem translation_energy (Y : Finset G) (w : ι → ℝ) (a : ι → G) :
    (∑ i, w i * (boundary Y (a i) : ℝ)) / Fintype.card G =
      (∑ i, w i) * density Y -
        ∑ χ : AddChar G ℂ, Complex.normSq (fourierCoeff (setIndicator Y) χ) *
          (∑ i, w i * (χ (-a i)).re) := by
  calc
    _ = ∑ i, w i * ((boundary Y (a i) : ℝ) / Fintype.card G) := by
      rw [Finset.sum_div]
      simp only [mul_div_assoc]
    _ = ∑ i, w i * (density Y -
        ∑ χ : AddChar G ℂ, Complex.normSq (fourierCoeff (setIndicator Y) χ) *
          (χ (-a i)).re) := by simp only [boundary_fourier]
    _ = _ := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro χ _
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- A gap in every nontrivial character implies average boundary growth.
This is the finite Cayley-graph spectral estimate in multiplicity form. -/
theorem spectral_boundary_average (Y : Finset G) (w : ι → ℝ) (a : ι → G)
    (hw : ∀ i, 0 ≤ w i) {η : ℝ} (hη : 0 ≤ η)
    (hhalf : 2 * Y.card ≤ Fintype.card G)
    (hgap : ∀ χ : AddChar G ℂ, χ ≠ 0 →
      (∑ i, w i * (χ (-a i)).re) ≤ (1 - η) * ∑ i, w i) :
    η * (∑ i, w i) * Y.card ≤ 2 * ∑ i, w i * (boundary Y (a i) : ℝ) := by
  classical
  let s := density Y
  let W := ∑ i, w i
  let D := ∑ i, w i * (boundary Y (a i) : ℝ)
  let n : AddChar G ℂ → ℝ := fun χ ↦ Complex.normSq (fourierCoeff (setIndicator Y) χ)
  let eig : AddChar G ℂ → ℝ := fun χ ↦ ∑ i, w i * (χ (-a i)).re
  have hn (χ : AddChar G ℂ) : 0 ≤ n χ := Complex.normSq_nonneg _
  have hW : 0 ≤ W := Finset.sum_nonneg (fun i _ ↦ hw i)
  have hN : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hs : 0 ≤ s := div_nonneg (Nat.cast_nonneg _) hN.le
  have hsN : s * Fintype.card G = (Y.card : ℝ) := div_mul_cancel₀ _ hN.ne'
  have hs2 : 2 * s ≤ 1 := by
    have hh : (2 : ℝ) * Y.card ≤ Fintype.card G := by exact_mod_cast hhalf
    nlinarith
  have hns : (∑ χ, n χ) = s := sum_fourierCoeff_normSq Y
  have hnzero : n 0 = s ^ 2 := by simp [n, fourierCoeff_setIndicator_zero, s, pow_two]
  have heigzero : eig 0 = W := by simp [eig, W]
  have heigbound : (∑ χ, n χ * eig χ) ≤ (1 - η) * W * s + η * W * s ^ 2 := by
    calc
      (∑ χ, n χ * eig χ) ≤
          ∑ χ, ((1 - η) * W * n χ + if χ = 0 then η * W * n χ else 0) := by
        apply Finset.sum_le_sum
        intro χ _
        by_cases hχ : χ = 0
        · rw [hχ, heigzero, ite_eq_left rfl]
          ring_nf
          exact le_rfl
        · rw [ite_eq_right hχ, add_zero]
          have hh := mul_le_mul_of_nonneg_left (hgap χ hχ) (hn χ)
          convert hh using 1
          ring
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hns]
        simp only [Fintype.sum_ite_eq', hnzero]
  have henergy : D / Fintype.card G = W * s - ∑ χ, n χ * eig χ :=
    translation_energy Y w a
  have hpos : 0 ≤ η * W * (s * (1 - 2 * s)) :=
    mul_nonneg (mul_nonneg hη hW) (mul_nonneg hs (by linarith))
  have havg : η * W * s ≤ 2 * (D / Fintype.card G) := by nlinarith
  calc
    η * W * Y.card = (η * W * s) * Fintype.card G := by rw [← hsN]; ring
    _ ≤ (2 * (D / Fintype.card G)) * Fintype.card G :=
      mul_le_mul_of_nonneg_right havg hN.le
    _ = 2 * D := by rw [mul_assoc, div_mul_cancel₀ _ hN.ne']

/-- Some positive-weight translation achieves the spectral average bound. -/
theorem exists_boundary_of_spectral_gap (Y : Finset G) (w : ι → ℝ) (a : ι → G)
    (hw : ∀ i, 0 ≤ w i) (hW : 0 < ∑ i, w i) {η : ℝ} (hη : 0 ≤ η)
    (hhalf : 2 * Y.card ≤ Fintype.card G)
    (hgap : ∀ χ : AddChar G ℂ, χ ≠ 0 →
      (∑ i, w i * (χ (-a i)).re) ≤ (1 - η) * ∑ i, w i) :
    ∃ i, 0 < w i ∧ η * Y.card ≤ 2 * (boundary Y (a i) : ℝ) := by
  classical
  have havg := spectral_boundary_average Y w a hw hη hhalf hgap
  by_contra! h
  have hex : ∃ i, 0 < w i := by
    by_contra! hn
    have hh := Finset.sum_nonpos (s := Finset.univ) (fun i _ ↦ hn i)
    linarith
  obtain ⟨i, hi⟩ := hex
  have hle (j : ι) : 2 * (w j * (boundary Y (a j) : ℝ)) ≤ w j * (η * Y.card) := by
    by_cases hj : 0 < w j
    · have hh := mul_le_mul_of_nonneg_left (h j hj).le (hw j)
      nlinarith
    · have hj0 : w j = 0 := le_antisymm (le_of_not_gt hj) (hw j)
      simp [hj0]
  have hlt : (∑ j, 2 * (w j * (boundary Y (a j) : ℝ))) < ∑ j, w j * (η * Y.card) := by
    apply Finset.sum_lt_sum (fun j _ ↦ hle j)
    refine ⟨i, Finset.mem_univ _, ?_⟩
    have hh := mul_lt_mul_of_pos_left (h i hi) hi
    nlinarith
  rw [← Finset.mul_sum, ← Finset.sum_mul] at hlt
  nlinarith

end SpectralGrowth

end EGZ.Expansion
