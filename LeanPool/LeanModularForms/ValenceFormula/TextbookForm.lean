/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.ValenceFormula.CoreIdentity
import LeanPool.LeanModularForms.ValenceFormula.TextbookExistence
import Mathlib.Algebra.BigOperators.Finprod

/-!
# Textbook Orbit-Finsum Form of the Valence Formula

This file proves the valence formula in literal orbit-sum form using `∑ᶠ` over
non-elliptic orbits of `SL₂(ℤ)` acting on `ℍ`.

## Main Results

* `valence_formula_textbook_orbit_finsum` — the valence formula with `∑ᶠ`
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular MatrixGroups

attribute [local instance] Classical.propDecidable

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)

/-- The order of vanishing on non-elliptic orbits, cast to `ℂ`. -/
def ordOrbitQ (q : NonEllOrbit) : ℂ := (ordOrbit f q.val : ℂ)

private lemma repCanon_ne_elliptic (p : ℍ) (hp : p ∈ repCanon f hf) :
    p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧
    p ≠ ellipticPointRhoPlusOne' := by
  simp only [repCanon, Finset.mem_union] at hp
  rcases hp with (h | h) | h
  · have h2 := (Finset.mem_filter.mp h).2; exact ⟨h2.1, h2.2.1, h2.2.2.1⟩
  · have h2 := (Finset.mem_filter.mp h).2; refine ⟨?_, ?_, ?_⟩
    · intro heq; rw [heq] at h2
      have : (ellipticPointI' : ℂ).re = 0 := Complex.I_re; linarith [h2.1]
    · intro heq; rw [heq] at h2; linarith [h2.2, ellipticPointRho_norm]
    · intro heq; rw [heq] at h2
      have : (ellipticPointRhoPlusOne' : ℂ).re = 1/2 := by
        change (1/2 + (Real.sqrt 3 / 2) * I : ℂ).re = 1/2; simp [add_re, mul_re, I_re, I_im]
      linarith [h2.1]
  · have h2 := (Finset.mem_filter.mp h).2; refine ⟨?_, h2.1, ?_⟩
    · intro heq; rw [heq] at h2
      have : (ellipticPointI' : ℂ).re = 0 := Complex.I_re; linarith [h2.2.2]
    · intro heq; rw [heq] at h2
      have : (ellipticPointRhoPlusOne' : ℂ).re = 1/2 := by
        change (1/2 + (Real.sqrt 3 / 2) * I : ℂ).re = 1/2; simp [add_re, mul_re, I_re, I_im]
      linarith [h2.2.2]

private lemma denom_at_I (g : SL(2, ℤ)) :
    UpperHalfPlane.denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) g)) (Complex.I) =
    ↑((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) * Complex.I +
    ↑((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) := by
  simp [UpperHalfPlane.denom, Matrix.SpecialLinearGroup.toGL, Matrix.SpecialLinearGroup.map]

private lemma normSq_denom_at_I (g : SL(2, ℤ)) :
    Complex.normSq (UpperHalfPlane.denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) g)) (Complex.I)) =
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) ^ 2 +
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) ^ 2 := by
  rw [denom_at_I, Complex.normSq_apply]
  simp [add_re, mul_re, add_im, mul_im, Complex.I_re, Complex.I_im]; ring

private lemma sl2_det (g : SL(2, ℤ)) :
    (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
    (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 *
      (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by have h := g.prop; rwa [Matrix.det_fin_two] at h

private lemma ellipticPointI'_coe : (ellipticPointI' : ℂ) = Complex.I := rfl
private lemma ellipticPointI'_im : (ellipticPointI' : ℍ).im = 1 := Complex.I_im

private lemma normSq_denom_eq_one_of_smul_i_in_fd (g : SL(2, ℤ))
    (h_fd : g • ellipticPointI' ∈ 𝒟) :
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) ^ 2 +
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) ^ 2 = 1 := by
  let c := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  let d := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  have h_im := ModularGroup.im_smul_eq_div_normSq g ellipticPointI'
  rw [ellipticPointI'_im, show (ellipticPointI' : ℂ) = I from rfl, normSq_denom_at_I] at h_im
  have h_gt : (1 : ℝ)/2 < 1 / ((c : ℝ) ^ 2 + (d : ℝ) ^ 2) := by
    rw [← h_im]; exact fd_im_gt_half _ h_fd
  have h_ge : c ^ 2 + d ^ 2 ≥ 1 := by
    by_contra h; push Not at h
    have hc0 : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := by nlinarith [sq_nonneg c]
    have hd0 : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 0 := by nlinarith [sq_nonneg d]
    have := sl2_det g; rw [hc0, hd0] at this; norm_num at this
  have h_pos : (c : ℝ) ^ 2 + (d : ℝ) ^ 2 > 0 :=
    by exact_mod_cast show (0 : ℤ) < c ^ 2 + d ^ 2 by omega
  have h_lt2 : (c : ℝ) ^ 2 + (d : ℝ) ^ 2 < 2 := by
    nlinarith [mul_lt_mul_of_pos_right h_gt h_pos, div_mul_cancel₀ (1 : ℝ) (ne_of_gt h_pos)]
  have : c ^ 2 + d ^ 2 < 2 := by exact_mod_cast h_lt2
  exact_mod_cast show c ^ 2 + d ^ 2 = 1 by omega

private lemma re_smul_ellipticPointI (g : SL(2, ℤ)) :
    (g • ellipticPointI').re =
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 +
     (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) /
    (((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) ^ 2 +
     ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) ^ 2) := by
  change (↑(g • ellipticPointI') : ℂ).re = _
  rw [UpperHalfPlane.coe_specialLinearGroup_apply, ellipticPointI'_coe]
  simp only [algebraMap_int_eq, Int.coe_castRingHom]
  rw [Complex.div_re, Complex.normSq_apply]
  simp only [add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im,
    I_im, mul_one, sub_zero, add_im, mul_im, add_zero]
  ring

private theorem fd'_orbit_i_eq_i (p : ℍ) (hp : p ∈ 𝒟) (horb : orb p = oi) :
    p = ellipticPointI' := by
  obtain ⟨g, hg⟩ := (Quotient.exact' horb : ∃ g : SL(2, ℤ), g • ellipticPointI' = p)
  subst hg
  set c := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 with hc_def
  set d := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 with hd_def
  set a := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 with ha_def
  set b := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 with hb_def
  have h_cd1 := normSq_denom_eq_one_of_smul_i_in_fd g hp
  have h_im := ModularGroup.im_smul_eq_div_normSq g ellipticPointI'
  rw [ellipticPointI'_im, show (ellipticPointI' : ℂ) = I from rfl,
      normSq_denom_at_I, h_cd1, div_one] at h_im
  have h_re := re_smul_ellipticPointI g
  rw [h_cd1, div_one] at h_re
  obtain ⟨n, hn⟩ : ∃ n : ℤ, (g • ellipticPointI').re = (n : ℝ) :=
    ⟨a * c + b * d, by rw [h_re]; push_cast; ring⟩
  have h_n_zero : n = 0 := by
    by_contra h_ne
    have h2 := hp.2; rw [hn] at h2
    linarith [show (1 : ℝ) ≤ |(n : ℝ)| from by exact_mod_cast Int.one_le_abs h_ne]
  exact UpperHalfPlane.ext_re_im
    (by rw [hn, h_n_zero, Int.cast_zero]
        exact (Complex.I_re : (I : ℂ).re = 0).symm)
    (by linarith [h_im, ellipticPointI'_im])

private lemma ellipticPointRho'_re : (ellipticPointRho' : ℍ).re = -1/2 := by
  change (-1/2 + (Real.sqrt 3 / 2) * I : ℂ).re = -1/2; simp [add_re, mul_re, I_re, I_im]

private lemma ellipticPointRho'_im :
    (ellipticPointRho' : ℍ).im = Real.sqrt 3 / 2 := by
  change (-1/2 + (Real.sqrt 3 / 2) * I : ℂ).im = Real.sqrt 3 / 2; simp [add_im, mul_im, I_re, I_im]

private lemma ellipticPointRhoPlusOne'_re :
    (ellipticPointRhoPlusOne' : ℍ).re = 1/2 := by
  change (1/2 + (Real.sqrt 3 / 2) * I : ℂ).re = 1/2; simp [add_re, mul_re, I_re, I_im]

private lemma ellipticPointRhoPlusOne'_im :
    (ellipticPointRhoPlusOne' : ℍ).im = Real.sqrt 3 / 2 := by
  change (1/2 + (Real.sqrt 3 / 2) * I : ℂ).im = Real.sqrt 3 / 2; simp [add_im, mul_im, I_re, I_im]

private lemma denom_at_rho (g : SL(2, ℤ)) :
    UpperHalfPlane.denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) g)) (ellipticPointRho' : ℍ) =
    ↑((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) *
      (-1/2 + (Real.sqrt 3 / 2) * I) +
    ↑((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) := by
  simp [UpperHalfPlane.denom, Matrix.SpecialLinearGroup.toGL,
    Matrix.SpecialLinearGroup.map, ellipticPointRho']

private lemma normSq_denom_at_rho (g : SL(2, ℤ)) :
    Complex.normSq (UpperHalfPlane.denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) g)) (ellipticPointRho' : ℍ)) =
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) ^ 2 -
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) * ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) +
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) ^ 2 := by
  rw [denom_at_rho, Complex.normSq_apply]
  simp only [add_re, mul_re, neg_re, one_re, div_ofNat_re, ofReal_re, mul_zero, I_re, I_im,
    sub_zero, mul_one, add_im, neg_im, one_im, div_ofNat_im, ofReal_im, zero_div, mul_im,
    zero_mul, add_zero, Complex.intCast_re, Complex.intCast_im]
  ring_nf; nlinarith [Real.mul_self_sqrt (show (3 : ℝ) ≥ 0 by norm_num)]

private lemma normSq_denom_eq_one_of_smul_rho_in_fd (g : SL(2, ℤ))
    (h_fd : g • ellipticPointRho' ∈ 𝒟) :
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) ^ 2 -
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) * ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) +
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) ^ 2 = 1 := by
  let c := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  let d := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  have h_im := ModularGroup.im_smul_eq_div_normSq g ellipticPointRho'
  rw [ellipticPointRho'_im, normSq_denom_at_rho] at h_im
  have h_gt : (1 : ℝ)/2 < (g • ellipticPointRho').im := fd_im_gt_half _ h_fd
  rw [h_im] at h_gt
  have h_pos : (c : ℝ) ^ 2 - (c : ℝ) * (d : ℝ) + (d : ℝ) ^ 2 > 0 := by
    by_contra h; push Not at h
    have : Real.sqrt 3 / 2 / ((c : ℝ) ^ 2 - (c : ℝ) * (d : ℝ) + (d : ℝ) ^ 2) ≤ 0 :=
      div_nonpos_iff.mpr (Or.inl ⟨by positivity, h⟩)
    linarith
  have h_lt2 : (c : ℝ) ^ 2 - (c : ℝ) * (d : ℝ) + (d : ℝ) ^ 2 < 2 := by
    nlinarith [Real.mul_self_sqrt (show (3 : ℝ) ≥ 0 by norm_num),
      mul_lt_mul_of_pos_right h_gt h_pos,
      div_mul_cancel₀ ((Real.sqrt 3 / 2 : ℝ)) (ne_of_gt h_pos),
      sq_nonneg (Real.sqrt 3 - 2)]
  have : (0 : ℤ) < c ^ 2 - c * d + d ^ 2 := by exact_mod_cast h_pos
  have : c ^ 2 - c * d + d ^ 2 < (2 : ℤ) := by exact_mod_cast h_lt2
  exact_mod_cast show c ^ 2 - c * d + d ^ 2 = 1 by omega

private lemma abs_re_eq_half_of_smul_rho_in_fd (g : SL(2, ℤ))
    (h_fd : g • ellipticPointRho' ∈ 𝒟)
    (h_cd1 : ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) ^ 2 -
      ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) *
        ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) +
      ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) ^ 2 = 1) :
    |(g • ellipticPointRho').re| = 1/2 := by
  have h_im_eq : (g • ellipticPointRho').im = Real.sqrt 3 / 2 := by
    have h_im := ModularGroup.im_smul_eq_div_normSq g ellipticPointRho'
    rw [ellipticPointRho'_im, normSq_denom_at_rho, h_cd1, div_one] at h_im; exact h_im
  have h_im_sq : (g • ellipticPointRho').im ^ 2 = 3/4 := by
    rw [h_im_eq]; nlinarith [Real.mul_self_sqrt (show (3 : ℝ) ≥ 0 by norm_num)]
  have h_nsq : (g • ellipticPointRho').re ^ 2 +
      (g • ellipticPointRho').im ^ 2 ≥ 1 := by
    have h_apply := Complex.normSq_apply (↑(g • ellipticPointRho') : ℂ)
    rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at h_apply
    nlinarith [h_fd.1, h_apply]
  exact le_antisymm h_fd.2 (by
    by_contra h_lt; push Not at h_lt; nlinarith [sq_abs (g • ellipticPointRho').re,
      abs_nonneg (g • ellipticPointRho').re, h_im_sq, h_nsq])

private theorem fd'_orbit_rho_eq (p : ℍ) (hp : p ∈ 𝒟) (horb : orb p = orho) :
    p = ellipticPointRho' ∨ p = ellipticPointRhoPlusOne' := by
  obtain ⟨g, hg⟩ := (Quotient.exact' horb : ∃ g : SL(2, ℤ), g • ellipticPointRho' = p)
  rw [← hg] at hp ⊢
  set c := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 with hc_def
  set d := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 with hd_def
  set a := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 with ha_def
  set b := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 with hb_def
  have h_cd1 := normSq_denom_eq_one_of_smul_rho_in_fd g hp
  have h_im : (g • ellipticPointRho').im = Real.sqrt 3 / 2 := by
    have := ModularGroup.im_smul_eq_div_normSq g ellipticPointRho'
    rw [ellipticPointRho'_im, normSq_denom_at_rho, h_cd1, div_one] at this; exact this
  have h_re_eq : (g • ellipticPointRho').re = -1/2 ∨ (g • ellipticPointRho').re = 1/2 := by
    have h_re_abs := abs_re_eq_half_of_smul_rho_in_fd g hp h_cd1
    rcases le_or_gt (g • ellipticPointRho').re 0 with h_neg | h_pos
    · left; linarith [abs_of_nonpos h_neg]
    · right; linarith [abs_of_pos h_pos]
  rcases h_re_eq with h_re_left | h_re_right
  · left
    exact UpperHalfPlane.ext_re_im (by linarith [h_re_left, ellipticPointRho'_re])
      (by linarith [h_im, ellipticPointRho'_im])
  · right
    exact UpperHalfPlane.ext_re_im (by linarith [h_re_right, ellipticPointRhoPlusOne'_re])
      (by linarith [h_im, ellipticPointRhoPlusOne'_im])

private theorem orb_repCanon_nonEll (p : ℍ) (hp : p ∈ repCanon f hf) :
    orb p ≠ oi ∧ orb p ≠ orho := by
  have ⟨hne_i, hne_rho, hne_rho1⟩ := repCanon_ne_elliptic f hf p hp
  have hp_fd := repCanon_mem_fd f hf hp
  exact ⟨fun h => hne_i (fd'_orbit_i_eq_i p hp_fd h),
    fun h => (fd'_orbit_rho_eq p hp_fd h).elim hne_rho hne_rho1⟩

private lemma denom_formula_general (h : SL(2, ℤ)) (p : ℍ) :
    UpperHalfPlane.denom h p = ((h : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * ↑p +
      ((h : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ) := by
  simp only [UpperHalfPlane.denom, Matrix.SpecialLinearGroup.toGL,
    Matrix.SpecialLinearGroup.map, RingHom.mapMatrix_apply]; rfl

private lemma normSq_denom_expand_general (h : SL(2, ℤ)) (p : ℍ) :
    Complex.normSq (UpperHalfPlane.denom h p) =
    ((h : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) ^ 2 * Complex.normSq (↑p) +
    2 * ((h : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) *
      ((h : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) * (↑p : ℂ).re +
    ((h : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) ^ 2 := by
  rw [denom_formula_general, Complex.normSq_apply]
  simp only [add_re, mul_re, add_im, mul_im,
    Complex.intCast_re, Complex.intCast_im, Complex.normSq_apply]
  ring

private lemma abs_int_cast_eq_one_of_sq_one {c : ℤ}
    (h : (c : ℝ) ^ 2 = 1) : |(c : ℝ)| = 1 := by
  nlinarith [sq_abs (c : ℝ), abs_nonneg (c : ℝ), sq_nonneg (|(c : ℝ)| - 1)]

private lemma d_mul_linear_nonneg {c d : ℤ} {z : ℍ}
    (hz : z ∈ 𝒟) (h_c_abs : |(c : ℝ)| = 1) :
    (d : ℝ) * (2 * (c : ℝ) * (z : ℂ).re + (d : ℝ)) ≥ 0 := by
  have h_bound : |2 * (c : ℝ) * (z : ℂ).re| ≤ 1 := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (2 : ℝ) > 0), h_c_abs, mul_one]
    have h_re : |(z : ℂ).re| ≤ 1/2 := hz.2; linarith
  rcases le_or_gt (d : ℤ) 0 with hd | hd
  · rcases eq_or_lt_of_le hd with hd0 | hd_neg
    · simp [show (d : ℝ) = 0 from by exact_mod_cast hd0]
    · have hd_le : (d : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hd_neg
      exact mul_nonneg_iff.mpr (Or.inr ⟨by linarith, by linarith [abs_le.mp h_bound]⟩)
  · have hd_ge : (d : ℝ) ≥ 1 := by exact_mod_cast hd
    exact mul_nonneg (by linarith) (by linarith [abs_le.mp h_bound])

private lemma normSq_denom_ge_one (h : SL(2, ℤ)) (z : ℍ) (hz : z ∈ 𝒟)
    (h_csq : ((h : Matrix (Fin 2) (Fin 2) ℤ) 1 0) ^ 2 = 1) :
    Complex.normSq (UpperHalfPlane.denom h z) ≥ 1 := by
  have h_csq_real : ((h : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) ^ 2 = 1 := by exact_mod_cast h_csq
  rw [normSq_denom_expand_general, h_csq_real, one_mul]
  nlinarith [hz.1, d_mul_linear_nonneg (c := (h : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
    (d := (h : Matrix (Fin 2) (Fin 2) ℤ) 1 1) hz (abs_int_cast_eq_one_of_sq_one h_csq_real)]

private lemma inv_c_sq_eq (g : SL(2, ℤ)) :
    ((g⁻¹ : SL(2, ℤ)).1 1 0) ^ 2 = ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0) ^ 2 := by
  have : (g⁻¹ : SL(2, ℤ)).1 1 0 = -((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0) := by
    rw [Matrix.SpecialLinearGroup.coe_inv g, Matrix.adjugate_fin_two]
    simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
               Matrix.cons_val_fin_one, Matrix.cons_val_one]
  rw [this]; ring

private lemma repCanon_norm_one_re_neg (p : ℍ) (hp : p ∈ repCanon f hf)
    (h_norm : ‖(p : ℂ)‖ = 1) : (p : ℂ).re < 0 := by
  simp only [repCanon, Finset.mem_union] at hp
  rcases hp with (h | h) | h
  · exfalso; exact absurd h_norm (ne_of_gt (Finset.mem_filter.mp h).2.2.2.2.1)
  · exfalso
    simp only [repLeftVert, sLeftVert, Finset.mem_filter] at h
    linarith [h.2.2]
  · exact (Finset.mem_filter.mp h).2.2.2

private lemma normSq_eq_one_of_denom_one (h : SL(2, ℤ)) (z : ℍ) (hz : z ∈ 𝒟)
    (h_csq : ((h : Matrix (Fin 2) (Fin 2) ℤ) 1 0) ^ 2 = 1)
    (h_denom : Complex.normSq (UpperHalfPlane.denom h z) = 1) :
    Complex.normSq (z : ℂ) = 1 := by
  have h_csq_real : ((h : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) ^ 2 = 1 := by exact_mod_cast h_csq
  have h_expand := normSq_denom_expand_general h z
  rw [h_denom, h_csq_real, one_mul] at h_expand
  nlinarith [hz.1, d_mul_linear_nonneg (c := (h : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
    (d := (h : Matrix (Fin 2) (Fin 2) ℤ) 1 1) hz (abs_int_cast_eq_one_of_sq_one h_csq_real)]

private lemma c_abs_le_one_of_smul_fd (g : SL(2, ℤ)) (p₁ p₂ : ℍ)
    (hg : g • p₂ = p₁) (hp₁ : p₁ ∈ 𝒟) (hp₂ : p₂ ∈ 𝒟) :
    |(g : Matrix (Fin 2) (Fin 2) ℤ) 1 0| ≤ 1 := by
  set c := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  have h_p1_im_eq : p₁.im = p₂.im / Complex.normSq (UpperHalfPlane.denom g p₂) := by
    have := ModularGroup.im_smul_eq_div_normSq g p₂; rw [hg] at this; exact this
  have h_nsq_eq : Complex.normSq (UpperHalfPlane.denom g p₂) = p₂.im / p₁.im := by
    rw [h_p1_im_eq]; field_simp
  by_contra h_gt; push Not at h_gt
  have h_c2 : c ^ 2 ≥ 4 := by nlinarith [sq_abs c]
  have h1 : (↑c : ℝ) ^ 2 * p₂.im ^ 2 ≤ p₂.im / p₁.im := by
    rw [← h_nsq_eq]; convert p₂.c_mul_im_sq_le_normSq_denom g using 1; simp [c]; ring
  have h2 : (↑c : ℝ) ^ 2 * p₂.im ^ 2 * p₁.im ≤ p₂.im := by
    have := mul_le_mul_of_nonneg_right h1 p₁.im_pos.le
    rwa [div_mul_cancel₀ _ (ne_of_gt p₁.im_pos)] at this
  have h3 : (↑c : ℝ) ^ 2 * p₂.im * p₁.im ≤ 1 := by
    have h_eq : (↑c : ℝ) ^ 2 * p₂.im * p₁.im =
        (↑c : ℝ) ^ 2 * p₂.im ^ 2 * p₁.im / p₂.im := by field_simp
    rw [h_eq]; exact (div_le_one p₂.im_pos).mpr h2
  have h_prod : 4 * (p₂.im * p₁.im) ≤ 1 := by
    have h_c2_real : (↑c : ℝ) ^ 2 ≥ 4 := by exact_mod_cast h_c2
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (↑c : ℝ) ^ 2 - 4 from by linarith)
      (mul_nonneg p₂.im_pos.le p₁.im_pos.le)]
  have hp1_im : (1 : ℝ) / 2 < p₁.im := by rw [← UpperHalfPlane.coe_im]; exact fd_im_gt_half _ hp₁
  have hp2_im : (1 : ℝ) / 2 < p₂.im := by rw [← UpperHalfPlane.coe_im]; exact fd_im_gt_half _ hp₂
  nlinarith [mul_pos (by linarith : (0 : ℝ) < p₁.im - 1/2)
    (by linarith : (0 : ℝ) < p₂.im - 1/2)]

private lemma repCanon_re_lt_half (p : ℍ) (hp : p ∈ repCanon f hf) : p.re < 1/2 := by
  simp only [repCanon, Finset.mem_union] at hp; rcases hp with (h | h) | h
  · exact lt_of_abs_lt (Finset.mem_filter.mp h).2.2.2.2.2
  · simp only [repLeftVert, sLeftVert, Finset.mem_filter] at h
    have : p.re = (↑p : ℂ).re := rfl; linarith [h.2.1]
  · have := (Finset.mem_filter.mp h).2.2.2; have : p.re = (↑p : ℂ).re := rfl; linarith

private lemma injOn_c_eq_zero (g : SL(2, ℤ)) (p₁ p₂ : ℍ)
    (hg : g • p₂ = p₁) (hp₁ : p₁ ∈ repCanon f hf) (hp₂ : p₂ ∈ repCanon f hf)
    (hp₁_fd : p₁ ∈ 𝒟) (hp₂_fd : p₂ ∈ 𝒟)
    (hc : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0) :
    p₁ = p₂ := by
  obtain ⟨n, hn⟩ := ModularGroup.exists_eq_T_zpow_of_c_eq_zero hc
  have hTn : p₁ = ModularGroup.T ^ n • p₂ := by rw [hn] at hg; exact hg.symm
  have h_re_shift : p₁.re = p₂.re + (n : ℝ) := by rw [hTn]; exact ModularGroup.re_T_zpow_smul p₂ n
  have h_n_zero : n = 0 := by
    have h1 := repCanon_re_lt_half f hf p₁ hp₁
    have h3 := repCanon_re_lt_half f hf p₂ hp₂
    have h4 : -(1 / 2) ≤ p₂.re := by
      have := hp₂_fd.2; rw [← UpperHalfPlane.coe_re] at this; exact (abs_le.mp this).1
    have h5 : -(1 / 2) ≤ p₁.re := by
      have := hp₁_fd.2; rw [← UpperHalfPlane.coe_re] at this; exact (abs_le.mp this).1
    have h_n_lt : (↑n : ℝ) < 1 := by linarith
    have h_n_gt : (-1 : ℝ) < (↑n : ℝ) := by linarith
    have : n < 1 := by exact_mod_cast h_n_lt
    have : -1 < n := by exact_mod_cast h_n_gt
    omega
  rw [hTn, h_n_zero, zpow_zero, one_smul]

private lemma normSq_denom_one_of_im_eq (g : SL(2, ℤ))
    (p₁ p₂ : ℍ) (h_smul : g • p₁ = p₂)
    (h_im : p₁.im = p₂.im) :
    Complex.normSq (UpperHalfPlane.denom g p₁) = 1 := by
  have h := ModularGroup.im_smul_eq_div_normSq g p₁
  rw [h_smul, h_im] at h
  have hne : Complex.normSq (UpperHalfPlane.denom g p₁) ≠ 0 := by
    intro h0; simp [h0] at h; linarith [p₂.im_pos]
  rw [eq_div_iff hne] at h
  nlinarith [p₂.im_pos]

private lemma injOn_c_ne_zero (g : SL(2, ℤ)) (p₁ p₂ : ℍ)
    (hg : g • p₂ = p₁) (hp₁ : p₁ ∈ repCanon f hf) (hp₂ : p₂ ∈ repCanon f hf)
    (hp₁_fd : p₁ ∈ 𝒟) (hp₂_fd : p₂ ∈ 𝒟)
    (h_c_ne : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 ≠ 0)
    (h_abs_c : |(g : Matrix (Fin 2) (Fin 2) ℤ) 1 0| ≤ 1) :
    p₁ = p₂ := by
  have h_csq : ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0) ^ 2 = 1 := by
    nlinarith [sq_abs ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0), Int.one_le_abs h_c_ne]
  have h_nsq_eq : Complex.normSq (UpperHalfPlane.denom g p₂) = p₂.im / p₁.im := by
    have h := ModularGroup.im_smul_eq_div_normSq g p₂; rw [hg] at h; rw [h]; field_simp
  have h_im_eq : p₁.im = p₂.im := le_antisymm
    (by have h := normSq_denom_ge_one g p₂ hp₂_fd h_csq
        rw [h_nsq_eq] at h; rwa [ge_iff_le, le_div_iff₀ p₁.im_pos, one_mul] at h)
    (by have h := ModularGroup.im_smul_eq_div_normSq g⁻¹ p₁
        rw [inv_smul_eq_iff.mpr hg.symm] at h; rw [h]
        exact div_le_self p₁.im_pos.le
          (normSq_denom_ge_one g⁻¹ p₁ hp₁_fd ((inv_c_sq_eq g).trans h_csq)))
  have h_p2_nsq := normSq_eq_one_of_denom_one g p₂ hp₂_fd h_csq
    (by rw [h_nsq_eq, h_im_eq, div_self (ne_of_gt p₂.im_pos)])
  have h_p1_nsq := normSq_eq_one_of_denom_one g⁻¹ p₁ hp₁_fd
    ((inv_c_sq_eq g).trans h_csq)
    (normSq_denom_one_of_im_eq g⁻¹ p₁ p₂ (inv_smul_eq_iff.mpr hg.symm) h_im_eq)
  have h_p1_norm : ‖(p₁ : ℂ)‖ = 1 := by
    nlinarith [Complex.normSq_eq_norm_sq (p₁ : ℂ), norm_nonneg (p₁ : ℂ),
      sq_nonneg (‖(p₁ : ℂ)‖ - 1)]
  have h_p2_norm : ‖(p₂ : ℂ)‖ = 1 := by
    nlinarith [Complex.normSq_eq_norm_sq (p₂ : ℂ), norm_nonneg (p₂ : ℂ),
      sq_nonneg (‖(p₂ : ℂ)‖ - 1)]
  have h_re_eq : (p₁ : ℂ).re = (p₂ : ℂ).re := by
    rw [Complex.normSq_apply] at h_p1_nsq h_p2_nsq
    rw [show (↑p₁ : ℂ).im = (↑p₂ : ℂ).im from h_im_eq] at h_p1_nsq
    nlinarith [sq_nonneg ((p₁ : ℂ).re - (p₂ : ℂ).re),
      sq_nonneg ((p₁ : ℂ).re + (p₂ : ℂ).re),
      repCanon_norm_one_re_neg f hf p₁ hp₁ h_p1_norm,
      repCanon_norm_one_re_neg f hf p₂ hp₂ h_p2_norm]
  exact UpperHalfPlane.ext_re_im h_re_eq h_im_eq

private theorem orb_injOn_repCanon :
    Set.InjOn orb ↑(repCanon f hf) := by
  intro p₁ hp₁ p₂ hp₂ h_eq
  simp only [orb] at h_eq
  obtain ⟨g, hg⟩ := Quotient.exact' h_eq
  have hp₁_fd := repCanon_mem_fd f hf hp₁
  have hp₂_fd := repCanon_mem_fd f hf hp₂
  rcases eq_or_ne ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0) 0 with hc | hc
  · exact injOn_c_eq_zero f hf g p₁ p₂ hg hp₁ hp₂ hp₁_fd hp₂_fd hc
  · exact injOn_c_ne_zero f hf g p₁ p₂ hg hp₁ hp₂ hp₁_fd hp₂_fd hc
      (c_abs_le_one_of_smul_fd g p₁ p₂ hg hp₁_fd hp₂_fd)

/-- The finsum over non-elliptic orbits equals the repCanon sum. -/
theorem finsum_nonell_eq_repCanon_sum :
    ∑ᶠ (q : NonEllOrbit), ordOrbitQ f q =
    ∑ s ∈ repCanon f hf, (orderOfVanishingAt' (⇑f) s : ℂ) := by
  set S := (finite_support_ordOrbit_nonEll f hf).toFinset with hS_def
  rw [finsum_eq_sum_of_support_subset _ (fun q hq => by
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    exact Int.cast_ne_zero.mp (Function.mem_support.mp hq))]
  set R := repCanon f hf
  set φ : (p : ℍ) → p ∈ R → NonEllOrbit :=
    fun p hp => ⟨orb p, orb_repCanon_nonEll f hf p hp⟩ with hφ_def
  have h_im : ∀ p (hp : p ∈ R), φ p hp ∈ S := fun p hp => by
    rw [Set.Finite.mem_toFinset]; change ordOrbit f (orb p) ≠ 0; rw [ordOrbit_mk]
    have hp_s₀ := repCanon_mem_s₀ f hf hp
    rw [s₀, Set.Finite.mem_toFinset] at hp_s₀; exact hp_s₀.2
  have h_surj : ∀ q ∈ S, ∃ p, ∃ hp : p ∈ R, φ p hp = q := fun q hq => by
    obtain ⟨p, hp_mem, hp_orb⟩ := exists_repCanon_of_nonEllOrbit f hf q
      ((Set.Finite.mem_toFinset _).mp hq)
    exact ⟨p, hp_mem, Subtype.ext hp_orb⟩
  exact (Finset.sum_bij φ h_im
    (fun _ h₁ _ h₂ heq => orb_injOn_repCanon f hf h₁ h₂ (congr_arg Subtype.val heq))
    h_surj (fun p hp => by
      simp only [ordOrbitQ, hφ_def]; exact_mod_cast (ordOrbit_mk f p).symm)).symm

private lemma disjoint_repStrict_repLeftVert :
    Disjoint (repStrict f hf) (repLeftVert f hf) := by
  apply Finset.disjoint_left.mpr; intro p hp_s hp_lv
  have h1 : |(p : ℂ).re| < 1/2 := (Finset.mem_filter.mp hp_s).2.2.2.2.2
  rw [(Finset.mem_filter.mp hp_lv).2.1] at h1; norm_num at h1

private lemma disjoint_union_repLeftArc :
    Disjoint (repStrict f hf ∪ repLeftVert f hf) (repLeftArc f hf) := by
  apply Finset.disjoint_left.mpr; intro p hp_u hp_a
  have h_norm_eq : ‖(p : ℂ)‖ = 1 := (Finset.mem_filter.mp hp_a).2.2.1
  rcases Finset.mem_union.mp hp_u with hp_s | hp_lv
  · exact absurd h_norm_eq (ne_of_gt (Finset.mem_filter.mp hp_s).2.2.2.2.1)
  · exact absurd h_norm_eq (ne_of_gt (Finset.mem_filter.mp hp_lv).2.2)

private lemma repCanon_sum_split :
    ∑ s ∈ repCanon f hf, (orderOfVanishingAt' (⇑f) s : ℂ) =
    ∑ s ∈ repStrict f hf, (orderOfVanishingAt' (⇑f) s : ℂ) +
    ∑ s ∈ repLeftVert f hf, (orderOfVanishingAt' (⇑f) s : ℂ) +
    ∑ s ∈ repLeftArc f hf, (orderOfVanishingAt' (⇑f) s : ℂ) := by
  simp only [repCanon]; rw [Finset.sum_union (disjoint_union_repLeftArc f hf),
    Finset.sum_union (disjoint_repStrict_repLeftVert f hf)]

include hf in
/-- The valence formula as an orbit-sum with `∑ᶠ` over non-elliptic orbits. -/
theorem valence_formula_textbook_orbit_finsum :
    (orderAtCusp' f : ℂ) +
    (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointI') +
    (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') +
    ∑ᶠ (q : NonEllOrbit), ordOrbitQ f q =
    (k : ℂ) / 12 := by
  rw [finsum_nonell_eq_repCanon_sum f hf, repCanon_sum_split f hf]
  unfold repStrict repLeftVert repLeftArc
  linear_combination
    valence_formula_orbit_sum f hf (s₀ f hf) (s₀_mem_fd f hf) (s₀_complete f hf)


end
