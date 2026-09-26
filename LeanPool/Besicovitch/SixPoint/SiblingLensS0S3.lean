/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.SixPoint.RationalChord
public import LeanPool.Besicovitch.SixPoint.SiblingIncidenceLedger

/-!
# The `S0/S3` sibling incidence

This file closes the balanced/balanced orbit `S0/S3`. A common quadratic tangent controls the
three positive cross distances. Two secants of the square root retain enough of the two larger
radial penalties, and three exact rational Gram factorizations cover the resulting radial ranges.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace LeanPool.Besicovitch

private theorem s0s3_scalarGram_low_low (e p₁ p₂ w₁ w₂ : ℝ) :
    18 / 5 * ((e - p₁ - w₁) ^ 2 + (e - p₂ - w₁) ^ 2 +
        (e - p₂ - w₂) ^ 2) - 11930 / 543 * (p₁ ^ 2 + w₂ ^ 2) -
        1930 / 693 * (p₂ ^ 2 + w₁ ^ 2) ≤
      1157 / 50 * e ^ 2 + 1263 / 50 * (p₂ ^ 2 + w₁ ^ 2) -
        871 / 100 * ((p₁ - p₂) ^ 2 + (w₁ - w₂) ^ 2) := by
  apply sub_nonneg.mp
  rw [show
    1157 / 50 * e ^ 2 + 1263 / 50 * (p₂ ^ 2 + w₁ ^ 2) -
        871 / 100 * ((p₁ - p₂) ^ 2 + (w₁ - w₂) ^ 2) -
        (18 / 5 * ((e - p₁ - w₁) ^ 2 + (e - p₂ - w₁) ^ 2 +
          (e - p₂ - w₂) ^ 2) - 11930 / 543 * (p₁ ^ 2 + w₂ ^ 2) -
          1930 / 693 * (p₂ ^ 2 + w₁ ^ 2)) =
      (3511 / 1000 * e + 41 / 40 * p₁ + 41 / 20 * p₂ + 41 / 20 * w₁ +
          41 / 40 * w₂) ^ 2 +
        (733 / 250 * p₁ + 2253 / 1000 * p₂ - 243 / 125 * w₁ -
          179 / 500 * w₂) ^ 2 +
        (843 / 500 * p₂ - 203 / 100 * w₁ - 2903 / 1000 * w₂) ^ 2 +
        (69 / 500 * w₁ + 67 / 500 * w₂) ^ 2 + (41 / 250 * w₂) ^ 2 +
        49 / 40000 * (e + p₁) ^ 2 + 49 / 20000 * (e + p₂) ^ 2 +
        49 / 20000 * (e + w₁) ^ 2 + 49 / 40000 * (e + w₂) ^ 2 +
        1477 / 500000 * (p₁ + p₂) ^ 2 + 721 / 500000 * (p₁ - w₁) ^ 2 +
        969 / 1000000 * (p₁ - w₂) ^ 2 + 11 / 125000 * (p₂ - w₁) ^ 2 +
        109 / 500000 * (p₂ - w₂) ^ 2 + 19 / 15625 * (w₁ + w₂) ^ 2 +
        5529 / 1000000 * e ^ 2 + 3635423 / 543000000 * p₁ ^ 2 +
        1133441 / 138600000 * p₂ ^ 2 + 711779 / 86625000 * w₁ ^ 2 +
        1589923 / 271500000 * w₂ ^ 2 by ring]
  positivity

private theorem s0s3_scalarGram_low_high (e p₁ p₂ w₁ w₂ : ℝ) :
    18 / 5 * ((e - p₁ - w₁) ^ 2 + (e - p₂ - w₁) ^ 2 +
        (e - p₂ - w₂) ^ 2) - 11930 / 543 * p₁ ^ 2 - 1193 / 85 * w₂ ^ 2 -
        1930 / 693 * (p₂ ^ 2 + w₁ ^ 2) ≤
      621 / 25 * e ^ 2 + 2701 / 100 * p₂ ^ 2 + 1863 / 100 * w₁ ^ 2 -
        849 / 100 * (p₁ - p₂) ^ 2 - 131 / 25 * (w₁ - w₂) ^ 2 := by
  apply sub_nonneg.mp
  rw [show
    621 / 25 * e ^ 2 + 2701 / 100 * p₂ ^ 2 + 1863 / 100 * w₁ ^ 2 -
        849 / 100 * (p₁ - p₂) ^ 2 - 131 / 25 * (w₁ - w₂) ^ 2 -
        (18 / 5 * ((e - p₁ - w₁) ^ 2 + (e - p₂ - w₁) ^ 2 +
          (e - p₂ - w₂) ^ 2) - 11930 / 543 * p₁ ^ 2 -
          1193 / 85 * w₂ ^ 2 - 1930 / 693 * (p₂ ^ 2 + w₁ ^ 2)) =
      (1873 / 500 * e + 961 / 1000 * p₁ + 961 / 500 * p₂ + 961 / 500 * w₁ +
          961 / 1000 * w₂) ^ 2 +
        (2991 / 1000 * p₁ + 2221 / 1000 * p₂ - 1821 / 1000 * w₁ -
          309 / 1000 * w₂) ^ 2 +
        (1169 / 500 * p₂ - 139 / 100 * w₁ - 509 / 250 * w₂) ^ 2 +
        (29 / 200 * w₁ - 1 / 500 * w₂) ^ 2 + (141 / 1000 * w₂) ^ 2 +
        47 / 500000 * (e + p₁) ^ 2 + 47 / 250000 * (e + p₂) ^ 2 +
        47 / 250000 * (e + w₁) ^ 2 + 47 / 500000 * (e + w₂) ^ 2 +
        53 / 1000000 * (p₁ - p₂) ^ 2 + 431 / 1000000 * (p₁ - w₁) ^ 2 +
        349 / 500000 * (p₁ + w₂) ^ 2 + 177 / 1000000 * (p₂ + w₁) ^ 2 +
        117 / 200000 * (p₂ - w₂) ^ 2 + 519 / 1000000 * (w₁ + w₂) ^ 2 +
        173 / 25000 * e ^ 2 + 2621623 / 271500000 * p₁ ^ 2 +
        1874701 / 173250000 * p₂ ^ 2 + 1445291 / 138600000 * w₁ ^ 2 +
        156657 / 17000000 * w₂ ^ 2 by ring]
  positivity

private theorem s0s3_scalarGram_high_high (e p₁ p₂ w₁ w₂ : ℝ) :
    18 / 5 * ((e - p₁ - w₁) ^ 2 + (e - p₂ - w₁) ^ 2 +
        (e - p₂ - w₂) ^ 2) - 1193 / 85 * (p₁ ^ 2 + w₂ ^ 2) -
        1930 / 693 * (p₂ ^ 2 + w₁ ^ 2) ≤
      2641 / 100 * e ^ 2 + 2071 / 100 * (p₂ ^ 2 + w₁ ^ 2) -
        517 / 100 * ((p₁ - p₂) ^ 2 + (w₁ - w₂) ^ 2) := by
  apply sub_nonneg.mp
  rw [show
    2641 / 100 * e ^ 2 + 2071 / 100 * (p₂ ^ 2 + w₁ ^ 2) -
        517 / 100 * ((p₁ - p₂) ^ 2 + (w₁ - w₂) ^ 2) -
        (18 / 5 * ((e - p₁ - w₁) ^ 2 + (e - p₂ - w₁) ^ 2 +
          (e - p₂ - w₂) ^ 2) - 1193 / 85 * (p₁ ^ 2 + w₂ ^ 2) -
          1930 / 693 * (p₂ ^ 2 + w₁ ^ 2)) =
      (79 / 20 * e + 911 / 1000 * p₁ + 1823 / 1000 * p₂ + 1823 / 1000 * w₁ +
          911 / 1000 * w₂) ^ 2 +
        (2103 / 1000 * p₁ + 417 / 250 * p₂ - 2501 / 1000 * w₁ -
          79 / 200 * w₂) ^ 2 +
        (1119 / 500 * p₂ - 1229 / 1000 * w₁ - 257 / 125 * w₂) ^ 2 +
        (157 / 1000 * w₁ - 11 / 250 * w₂) ^ 2 + (39 / 200 * w₂) ^ 2 +
        31 / 20000 * (e + p₁) ^ 2 + 17 / 20000 * (e - p₂) ^ 2 +
        17 / 20000 * (e - w₁) ^ 2 + 31 / 20000 * (e + w₂) ^ 2 +
        1443 / 1000000 * (p₁ + p₂) ^ 2 + 23 / 20000 * (p₁ - w₁) ^ 2 +
        191 / 250000 * (p₁ + w₂) ^ 2 + 1159 / 1000000 * (p₂ - w₁) ^ 2 +
        113 / 200000 * (p₂ - w₂) ^ 2 + 359 / 250000 * (w₁ + w₂) ^ 2 +
        27 / 10000 * e ^ 2 + 133571 / 17000000 * p₁ ^ 2 +
        2348849 / 346500000 * p₂ ^ 2 + 967121 / 138600000 * w₁ ^ 2 +
        67457 / 8500000 * w₂ ^ 2 by ring]
  positivity

private theorem s0s3_gram_low_low (e p₁ p₂ w₁ w₂ : (EuclideanSpace ℝ (Fin 2))) :
    18 / 5 * (‖e - p₁ - w₁‖ ^ 2 + ‖e - p₂ - w₁‖ ^ 2 +
        ‖e - p₂ - w₂‖ ^ 2) - 11930 / 543 * (‖p₁‖ ^ 2 + ‖w₂‖ ^ 2) -
        1930 / 693 * (‖p₂‖ ^ 2 + ‖w₁‖ ^ 2) ≤
      1157 / 50 * ‖e‖ ^ 2 + 1263 / 50 * (‖p₂‖ ^ 2 + ‖w₁‖ ^ 2) -
        871 / 100 * (‖p₁ - p₂‖ ^ 2 + ‖w₁ - w₂‖ ^ 2) := by
  have h₀ := s0s3_scalarGram_low_low (e 0) (p₁ 0) (p₂ 0) (w₁ 0) (w₂ 0)
  have h₁ := s0s3_scalarGram_low_low (e 1) (p₁ 1) (p₂ 1) (w₁ 1) (w₂ 1)
  have h := add_le_add h₀ h₁
  simp only [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two, PiLp.sub_apply, Real.norm_eq_abs,
    sq_abs] at ⊢
  ring_nf at h ⊢
  exact h

private theorem s0s3_gram_low_high (e p₁ p₂ w₁ w₂ : (EuclideanSpace ℝ (Fin 2))) :
    18 / 5 * (‖e - p₁ - w₁‖ ^ 2 + ‖e - p₂ - w₁‖ ^ 2 +
        ‖e - p₂ - w₂‖ ^ 2) - 11930 / 543 * ‖p₁‖ ^ 2 -
        1193 / 85 * ‖w₂‖ ^ 2 - 1930 / 693 * (‖p₂‖ ^ 2 + ‖w₁‖ ^ 2) ≤
      621 / 25 * ‖e‖ ^ 2 + 2701 / 100 * ‖p₂‖ ^ 2 + 1863 / 100 * ‖w₁‖ ^ 2 -
        849 / 100 * ‖p₁ - p₂‖ ^ 2 - 131 / 25 * ‖w₁ - w₂‖ ^ 2 := by
  have h₀ := s0s3_scalarGram_low_high (e 0) (p₁ 0) (p₂ 0) (w₁ 0) (w₂ 0)
  have h₁ := s0s3_scalarGram_low_high (e 1) (p₁ 1) (p₂ 1) (w₁ 1) (w₂ 1)
  have h := add_le_add h₀ h₁
  simp only [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two, PiLp.sub_apply, Real.norm_eq_abs,
    sq_abs] at ⊢
  ring_nf at h ⊢
  exact h

private theorem s0s3_gram_high_high (e p₁ p₂ w₁ w₂ : (EuclideanSpace ℝ (Fin 2))) :
    18 / 5 * (‖e - p₁ - w₁‖ ^ 2 + ‖e - p₂ - w₁‖ ^ 2 +
        ‖e - p₂ - w₂‖ ^ 2) - 1193 / 85 * (‖p₁‖ ^ 2 + ‖w₂‖ ^ 2) -
        1930 / 693 * (‖p₂‖ ^ 2 + ‖w₁‖ ^ 2) ≤
      2641 / 100 * ‖e‖ ^ 2 + 2071 / 100 * (‖p₂‖ ^ 2 + ‖w₁‖ ^ 2) -
        517 / 100 * (‖p₁ - p₂‖ ^ 2 + ‖w₁ - w₂‖ ^ 2) := by
  have h₀ := s0s3_scalarGram_high_high (e 0) (p₁ 0) (p₂ 0) (w₁ 0) (w₂ 0)
  have h₁ := s0s3_scalarGram_high_high (e 1) (p₁ 1) (p₂ 1) (w₁ 1) (w₂ 1)
  have h := add_le_add h₀ h₁
  simp only [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two, PiLp.sub_apply, Real.norm_eq_abs,
    sq_abs] at ⊢
  ring_nf at h ⊢
  exact h

private theorem s0s3_scalarGram_high_low (e p₁ p₂ w₁ w₂ : ℝ) :
    18 / 5 * ((e - p₁ - w₁) ^ 2 + (e - p₂ - w₁) ^ 2 +
        (e - p₂ - w₂) ^ 2) - 1193 / 85 * p₁ ^ 2 - 11930 / 543 * w₂ ^ 2 -
        1930 / 693 * (p₂ ^ 2 + w₁ ^ 2) ≤
      621 / 25 * e ^ 2 + 1863 / 100 * p₂ ^ 2 + 2701 / 100 * w₁ ^ 2 -
        131 / 25 * (p₁ - p₂) ^ 2 - 849 / 100 * (w₁ - w₂) ^ 2 := by
  have h := s0s3_scalarGram_low_high e w₂ w₁ p₂ p₁
  ring_nf at h ⊢
  exact h

private theorem s0s3_gram_high_low (e p₁ p₂ w₁ w₂ : (EuclideanSpace ℝ (Fin 2))) :
    18 / 5 * (‖e - p₁ - w₁‖ ^ 2 + ‖e - p₂ - w₁‖ ^ 2 +
        ‖e - p₂ - w₂‖ ^ 2) - 1193 / 85 * ‖p₁‖ ^ 2 -
        11930 / 543 * ‖w₂‖ ^ 2 - 1930 / 693 * (‖p₂‖ ^ 2 + ‖w₁‖ ^ 2) ≤
      621 / 25 * ‖e‖ ^ 2 + 1863 / 100 * ‖p₂‖ ^ 2 + 2701 / 100 * ‖w₁‖ ^ 2 -
        131 / 25 * ‖p₁ - p₂‖ ^ 2 - 849 / 100 * ‖w₁ - w₂‖ ^ 2 := by
  have h₀ := s0s3_scalarGram_high_low (e 0) (p₁ 0) (p₂ 0) (w₁ 0) (w₂ 0)
  have h₁ := s0s3_scalarGram_high_low (e 1) (p₁ 1) (p₂ 1) (w₁ 1) (w₂ 1)
  have h := add_le_add h₀ h₁
  simp only [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two, PiLp.sub_apply, Real.norm_eq_abs,
    sq_abs] at ⊢
  ring_nf at h ⊢
  exact h

private theorem s0s3_positive_distances_le (e p₁ p₂ w₁ w₂ : (EuclideanSpace ℝ (Fin 2))) :
    17 * ‖e - p₁ - w₁‖ + 20 * ‖e - p₂ - w₁‖ +
        17 * ‖e - p₂ - w₂‖ ≤
      815 / 12 + 18 / 5 * (‖e - p₁ - w₁‖ ^ 2 +
        ‖e - p₂ - w₁‖ ^ 2 + ‖e - p₂ - w₂‖ ^ 2) := by
  have h₁₁ := weightedNorm_le_quadratic (e - p₁ - w₁) 17 (18 / 5) (by norm_num)
  have h₂₁ := weightedNorm_le_quadratic (e - p₂ - w₁) 20 (18 / 5) (by norm_num)
  have h₂₂ := weightedNorm_le_quadratic (e - p₂ - w₂) 17 (18 / 5) (by norm_num)
  norm_num at h₁₁ h₂₁ h₂₂ ⊢
  linarith

private theorem secant_le (x lower upper : ℝ) (hlower : lower ≤ x) (hupper : x ≤ upper)
    (hsum : 0 < lower + upper) :
    (x ^ 2 + lower * upper) / (lower + upper) ≤ x := by
  rw [div_le_iff₀ hsum]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hlower)
    (sub_nonpos.mpr hupper)]

private theorem s0s3_radius_floor {E : Type*} [NormedAddCommGroup E] (x y : E)
    (hy : ‖y‖ ≤ 1) (hseparation : barC ≤ ‖x - y‖) :
    193 / 500 ≤ ‖x‖ := by
  have htriangle := norm_sub_le x y
  have hc := barC_mem_isolation_box.1
  norm_num at hc ⊢
  linarith

private theorem s0s3_low_radial_secant (x : ℝ) (hlower : 193 / 500 ≤ x)
    (hupper : x ≤ 1) :
    1930 / 693 * x ^ 2 + 37249 / 34650 ≤ 193 / 50 * x := by
  have h := secant_le x (193 / 500) 1 hlower hupper (by norm_num)
  norm_num at h ⊢
  linarith

private theorem s0s3_high_radial_low_secant (x : ℝ) (hlower : 193 / 500 ≤ x)
    (hupper : x ≤ 7 / 10) :
    11930 / 543 * x ^ 2 + 1611743 / 271500 ≤ 1193 / 50 * x := by
  have h := secant_le x (193 / 500) (7 / 10) hlower hupper (by norm_num)
  norm_num at h ⊢
  linarith

private theorem s0s3_high_radial_high_secant (x : ℝ) (hlower : 7 / 10 ≤ x)
    (hupper : x ≤ 1) :
    1193 / 85 * x ^ 2 + 8351 / 850 ≤ 1193 / 50 * x := by
  have h := secant_le x (7 / 10) 1 hlower hupper (by norm_num)
  norm_num at h ⊢
  linarith

private theorem s0s3_high_coefficient_le : 1193 / 50 ≤ 10 * (barC + 1) := by
  have hc := barC_mem_isolation_box.1
  norm_num at hc ⊢
  linarith

private theorem s0s3_low_coefficient_le : 193 / 50 ≤ 10 * (barC - 1) := by
  have hc := barC_mem_isolation_box.1
  norm_num at hc ⊢
  linarith

private theorem s0s3_low_low_constant_neg :
    815 / 12 + 1157 / 50 + 2 * (1263 / 50) - 2 * (871 / 100) * barC ^ 2 -
      2 * (37249 / 34650) - 2 * (1611743 / 271500) +
      54 * barC - 88 * barC ^ 2 < 0 := by
  have hc := barC_mem_isolation_box.1
  norm_num at hc ⊢
  nlinarith [sq_nonneg (barC - 1)]

private theorem s0s3_low_high_constant_neg :
    815 / 12 + 621 / 25 + 2701 / 100 + 1863 / 100 -
      (849 / 100 + 131 / 25) * barC ^ 2 - 2 * (37249 / 34650) -
      1611743 / 271500 - 8351 / 850 + 54 * barC - 88 * barC ^ 2 < 0 := by
  have hc := barC_mem_isolation_box.1
  norm_num at hc ⊢
  nlinarith [sq_nonneg (barC - 1)]

private theorem s0s3_high_high_constant_neg :
    815 / 12 + 2641 / 100 + 2 * (2071 / 100) - 2 * (517 / 100) * barC ^ 2 -
      2 * (37249 / 34650) - 2 * (8351 / 850) +
      54 * barC - 88 * barC ^ 2 < 0 := by
  have hc := barC_mem_isolation_box.1
  norm_num at hc ⊢
  nlinarith [sq_nonneg (barC - 1)]

private theorem s0s3_gramBound_low_low
    (e p₁ p₂ w₁ w₂ : (EuclideanSpace ℝ (Fin 2))) (he : ‖e‖ = 1)
    (hp₂ : ‖p₂‖ ≤ 1) (hw₁ : ‖w₁‖ ≤ 1) (hpsep : barC ≤ ‖p₁ - p₂‖)
    (hwsep : barC ≤ ‖w₁ - w₂‖) :
    18 / 5 * (‖e - p₁ - w₁‖ ^ 2 + ‖e - p₂ - w₁‖ ^ 2 +
        ‖e - p₂ - w₂‖ ^ 2) - 11930 / 543 * (‖p₁‖ ^ 2 + ‖w₂‖ ^ 2) -
        1930 / 693 * (‖p₂‖ ^ 2 + ‖w₁‖ ^ 2) ≤
      1157 / 50 + 2 * (1263 / 50) - 2 * (871 / 100) * barC ^ 2 := by
  have hp₂Sq : ‖p₂‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg p₂]
  have hw₁Sq : ‖w₁‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg w₁]
  have hpsepSq : barC ^ 2 ≤ ‖p₁ - p₂‖ ^ 2 := by
    nlinarith [barC_pos, norm_nonneg (p₁ - p₂)]
  have hwsepSq : barC ^ 2 ≤ ‖w₁ - w₂‖ ^ 2 := by
    nlinarith [barC_pos, norm_nonneg (w₁ - w₂)]
  have hgram := s0s3_gram_low_low e p₁ p₂ w₁ w₂
  rw [he, one_pow] at hgram
  nlinarith only [hgram, hp₂Sq, hw₁Sq, hpsepSq, hwsepSq]

private theorem s0s3_gramBound_low_high
    (e p₁ p₂ w₁ w₂ : (EuclideanSpace ℝ (Fin 2))) (he : ‖e‖ = 1)
    (hp₂ : ‖p₂‖ ≤ 1) (hw₁ : ‖w₁‖ ≤ 1) (hpsep : barC ≤ ‖p₁ - p₂‖)
    (hwsep : barC ≤ ‖w₁ - w₂‖) :
    18 / 5 * (‖e - p₁ - w₁‖ ^ 2 + ‖e - p₂ - w₁‖ ^ 2 +
        ‖e - p₂ - w₂‖ ^ 2) - 11930 / 543 * ‖p₁‖ ^ 2 -
        1193 / 85 * ‖w₂‖ ^ 2 - 1930 / 693 * (‖p₂‖ ^ 2 + ‖w₁‖ ^ 2) ≤
      621 / 25 + 2701 / 100 + 1863 / 100 -
        (849 / 100 + 131 / 25) * barC ^ 2 := by
  have hp₂Sq : ‖p₂‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg p₂]
  have hw₁Sq : ‖w₁‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg w₁]
  have hpsepSq : barC ^ 2 ≤ ‖p₁ - p₂‖ ^ 2 := by
    nlinarith [barC_pos, norm_nonneg (p₁ - p₂)]
  have hwsepSq : barC ^ 2 ≤ ‖w₁ - w₂‖ ^ 2 := by
    nlinarith [barC_pos, norm_nonneg (w₁ - w₂)]
  have hgram := s0s3_gram_low_high e p₁ p₂ w₁ w₂
  rw [he, one_pow] at hgram
  nlinarith only [hgram, hp₂Sq, hw₁Sq, hpsepSq, hwsepSq]

private theorem s0s3_gramBound_high_low
    (e p₁ p₂ w₁ w₂ : (EuclideanSpace ℝ (Fin 2))) (he : ‖e‖ = 1)
    (hp₂ : ‖p₂‖ ≤ 1) (hw₁ : ‖w₁‖ ≤ 1) (hpsep : barC ≤ ‖p₁ - p₂‖)
    (hwsep : barC ≤ ‖w₁ - w₂‖) :
    18 / 5 * (‖e - p₁ - w₁‖ ^ 2 + ‖e - p₂ - w₁‖ ^ 2 +
        ‖e - p₂ - w₂‖ ^ 2) - 1193 / 85 * ‖p₁‖ ^ 2 -
        11930 / 543 * ‖w₂‖ ^ 2 - 1930 / 693 * (‖p₂‖ ^ 2 + ‖w₁‖ ^ 2) ≤
      621 / 25 + 2701 / 100 + 1863 / 100 -
        (849 / 100 + 131 / 25) * barC ^ 2 := by
  have hp₂Sq : ‖p₂‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg p₂]
  have hw₁Sq : ‖w₁‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg w₁]
  have hpsepSq : barC ^ 2 ≤ ‖p₁ - p₂‖ ^ 2 := by
    nlinarith [barC_pos, norm_nonneg (p₁ - p₂)]
  have hwsepSq : barC ^ 2 ≤ ‖w₁ - w₂‖ ^ 2 := by
    nlinarith [barC_pos, norm_nonneg (w₁ - w₂)]
  have hgram := s0s3_gram_high_low e p₁ p₂ w₁ w₂
  rw [he, one_pow] at hgram
  nlinarith only [hgram, hp₂Sq, hw₁Sq, hpsepSq, hwsepSq]

private theorem s0s3_gramBound_high_high
    (e p₁ p₂ w₁ w₂ : (EuclideanSpace ℝ (Fin 2))) (he : ‖e‖ = 1)
    (hp₂ : ‖p₂‖ ≤ 1) (hw₁ : ‖w₁‖ ≤ 1) (hpsep : barC ≤ ‖p₁ - p₂‖)
    (hwsep : barC ≤ ‖w₁ - w₂‖) :
    18 / 5 * (‖e - p₁ - w₁‖ ^ 2 + ‖e - p₂ - w₁‖ ^ 2 +
        ‖e - p₂ - w₂‖ ^ 2) - 1193 / 85 * (‖p₁‖ ^ 2 + ‖w₂‖ ^ 2) -
        1930 / 693 * (‖p₂‖ ^ 2 + ‖w₁‖ ^ 2) ≤
      2641 / 100 + 2 * (2071 / 100) - 2 * (517 / 100) * barC ^ 2 := by
  have hp₂Sq : ‖p₂‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg p₂]
  have hw₁Sq : ‖w₁‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg w₁]
  have hpsepSq : barC ^ 2 ≤ ‖p₁ - p₂‖ ^ 2 := by
    nlinarith [barC_pos, norm_nonneg (p₁ - p₂)]
  have hwsepSq : barC ^ 2 ≤ ‖w₁ - w₂‖ ^ 2 := by
    nlinarith [barC_pos, norm_nonneg (w₁ - w₂)]
  have hgram := s0s3_gram_high_high e p₁ p₂ w₁ w₂
  rw [he, one_pow] at hgram
  nlinarith only [hgram, hp₂Sq, hw₁Sq, hpsepSq, hwsepSq]

private theorem s0s3_radialBound_of_secants (p₁ p₂ w₁ w₂ : (EuclideanSpace ℝ (Fin 2)))
    (pSlope pConstant wSlope wConstant : ℝ)
    (hp₁ : pSlope * ‖p₁‖ ^ 2 + pConstant ≤ 1193 / 50 * ‖p₁‖)
    (hp₂ : 1930 / 693 * ‖p₂‖ ^ 2 + 37249 / 34650 ≤ 193 / 50 * ‖p₂‖)
    (hw₁ : 1930 / 693 * ‖w₁‖ ^ 2 + 37249 / 34650 ≤ 193 / 50 * ‖w₁‖)
    (hw₂ : wSlope * ‖w₂‖ ^ 2 + wConstant ≤ 1193 / 50 * ‖w₂‖) :
    pSlope * ‖p₁‖ ^ 2 + wSlope * ‖w₂‖ ^ 2 +
        1930 / 693 * (‖p₂‖ ^ 2 + ‖w₁‖ ^ 2) +
        pConstant + wConstant + 2 * (37249 / 34650) ≤
      10 * (barC + 1) * (‖p₁‖ + ‖w₂‖) +
        10 * (barC - 1) * (‖p₂‖ + ‖w₁‖) := by
  have hhigh := mul_le_mul_of_nonneg_right s0s3_high_coefficient_le
    (add_nonneg (norm_nonneg p₁) (norm_nonneg w₂))
  have hlow := mul_le_mul_of_nonneg_right s0s3_low_coefficient_le
    (add_nonneg (norm_nonneg p₂) (norm_nonneg w₁))
  calc
    _ ≤ 1193 / 50 * (‖p₁‖ + ‖w₂‖) +
        193 / 50 * (‖p₂‖ + ‖w₁‖) := by linarith
    _ ≤ _ := add_le_add hhigh hlow

/-- A two-secant rational Gram separator for the `S0/S3` incidence representative. -/
theorem gramCertificate_s0s3 (e p₁ p₂ w₁ w₂ : (EuclideanSpace ℝ (Fin 2)))
    (he : ‖e‖ = 1)
    (hp₁ : ‖p₁‖ ≤ 1) (hp₂ : ‖p₂‖ ≤ 1) (hw₁ : ‖w₁‖ ≤ 1)
    (hw₂ : ‖w₂‖ ≤ 1) (hpsep : barC ≤ ‖p₁ - p₂‖)
    (hwsep : barC ≤ ‖w₁ - w₂‖) :
    17 * ‖e - p₁ - w₁‖ + 20 * ‖e - p₂ - w₁‖ +
        17 * ‖e - p₂ - w₂‖ -
        10 * (barC + 1) * (‖p₁‖ + ‖w₂‖) -
        10 * (barC - 1) * (‖p₂‖ + ‖w₁‖) +
        54 * barC - 88 * barC ^ 2 < 0 := by
  have hp₁Lower := s0s3_radius_floor p₁ p₂ hp₂ hpsep
  have hp₂Lower := s0s3_radius_floor p₂ p₁ hp₁ (by simpa [norm_sub_rev] using hpsep)
  have hw₁Lower := s0s3_radius_floor w₁ w₂ hw₂ hwsep
  have hw₂Lower := s0s3_radius_floor w₂ w₁ hw₁ (by simpa [norm_sub_rev] using hwsep)
  have htangent := s0s3_positive_distances_le e p₁ p₂ w₁ w₂
  have hp₂Radial := s0s3_low_radial_secant ‖p₂‖ hp₂Lower hp₂
  have hw₁Radial := s0s3_low_radial_secant ‖w₁‖ hw₁Lower hw₁
  by_cases hp₁Low : ‖p₁‖ ≤ 7 / 10
  · have hp₁Radial := s0s3_high_radial_low_secant ‖p₁‖ hp₁Lower hp₁Low
    by_cases hw₂Low : ‖w₂‖ ≤ 7 / 10
    · have hw₂Radial := s0s3_high_radial_low_secant ‖w₂‖ hw₂Lower hw₂Low
      have hgram :=
        s0s3_gramBound_low_low e p₁ p₂ w₁ w₂ he hp₂ hw₁ hpsep hwsep
      have hradial := s0s3_radialBound_of_secants p₁ p₂ w₁ w₂
        (11930 / 543) (1611743 / 271500) (11930 / 543) (1611743 / 271500)
        hp₁Radial hp₂Radial hw₁Radial hw₂Radial
      nlinarith only [htangent, hgram, hradial, s0s3_low_low_constant_neg]
    · have hw₂Radial := s0s3_high_radial_high_secant ‖w₂‖
        (le_of_not_ge hw₂Low) hw₂
      have hgram :=
        s0s3_gramBound_low_high e p₁ p₂ w₁ w₂ he hp₂ hw₁ hpsep hwsep
      have hradial := s0s3_radialBound_of_secants p₁ p₂ w₁ w₂
        (11930 / 543) (1611743 / 271500) (1193 / 85) (8351 / 850)
        hp₁Radial hp₂Radial hw₁Radial hw₂Radial
      nlinarith only [htangent, hgram, hradial, s0s3_low_high_constant_neg]
  · have hp₁Radial := s0s3_high_radial_high_secant ‖p₁‖
      (le_of_not_ge hp₁Low) hp₁
    by_cases hw₂Low : ‖w₂‖ ≤ 7 / 10
    · have hw₂Radial := s0s3_high_radial_low_secant ‖w₂‖ hw₂Lower hw₂Low
      have hgram :=
        s0s3_gramBound_high_low e p₁ p₂ w₁ w₂ he hp₂ hw₁ hpsep hwsep
      have hradial := s0s3_radialBound_of_secants p₁ p₂ w₁ w₂
        (1193 / 85) (8351 / 850) (11930 / 543) (1611743 / 271500)
        hp₁Radial hp₂Radial hw₁Radial hw₂Radial
      nlinarith only [htangent, hgram, hradial, s0s3_low_high_constant_neg]
    · have hw₂Radial := s0s3_high_radial_high_secant ‖w₂‖
        (le_of_not_ge hw₂Low) hw₂
      have hgram :=
        s0s3_gramBound_high_high e p₁ p₂ w₁ w₂ he hp₂ hw₁ hpsep hwsep
      have hradial := s0s3_radialBound_of_secants p₁ p₂ w₁ w₂
        (1193 / 85) (8351 / 850) (1193 / 85) (8351 / 850)
        hp₁Radial hp₂Radial hw₁Radial hw₂Radial
      nlinarith only [htangent, hgram, hradial, s0s3_high_high_constant_neg]

/-- The `S0/S3` separator is strictly negative for every admissible configuration. -/
theorem balancedBalancedS0S3GramBound_of_admissible
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS) :
    7 * diagonalMatchingReducedSlack configuration +
        20 * redBalancedReducedSlack configuration 0 +
        20 * blueBalancedReducedSlack configuration 3 < 0 := by
  let e := configuration.rootDisplacement
  let p₁ := configuration.redDisplacement .left
  let p₂ := configuration.redDisplacement .right
  let w₁ := configuration.bluePullback .left
  let w₂ := configuration.bluePullback .right
  have hpsep : barC ≤ ‖p₁ - p₂‖ := by
    have hred := configuration.two_mul_le_dist_redDisplacement h
    rw [barS, show 2 * (barC / 2) = barC by ring, dist_eq_norm] at hred
    exact hred
  have hwsep : barC ≤ ‖w₁ - w₂‖ := by
    have hblue := configuration.two_mul_le_dist_bluePullback h
    rw [barS, show 2 * (barC / 2) = barC by ring, dist_eq_norm] at hblue
    exact hblue
  have hcertificate := gramCertificate_s0s3 e p₁ p₂ w₁ w₂
    (configuration.norm_rootDisplacement h)
    (configuration.norm_redDisplacement_le_one h (by simp))
    (configuration.norm_redDisplacement_le_one h (by simp))
    (configuration.norm_bluePullback_le_one h (by simp))
    (configuration.norm_bluePullback_le_one h (by simp)) hpsep hwsep
  simp only [diagonalMatchingReducedSlack, redBalancedReducedSlack,
    blueBalancedReducedSlack, balancedIncidencePenalty, incidenceCrossDistance_eq_norm,
    incidenceChildRadius_red_eq_norm, incidenceChildRadius_blue_eq_norm]
  norm_num [incidenceFirst, incidenceSecond, incidenceChild, otherChild]
  dsimp only [e, p₁, p₂, w₁, w₂] at hcertificate
  nlinarith

/-- The `S0/S3` balanced/balanced representative is impossible. -/
theorem not_redBalanced_zero_and_blueBalanced_three
    {configuration : SixPointConfiguration} (h : configuration.IsAdmissibleAt barS)
    (hmatching : SelectedDiagonalMatchingFails configuration) :
    ¬ (redSiblingTriangleFailure configuration (.balanced 0) ∧
      blueSiblingTriangleFailure configuration (.balanced 3)) := by
  rintro ⟨hred, hblue⟩
  have hmatchingSlack := diagonalMatchingReducedSlack_nonneg h hmatching
  have hredSlack := redBalancedReducedSlack_pos h 0 hred
  have hblueSlack := blueBalancedReducedSlack_pos h 3 hblue
  have hbound := balancedBalancedS0S3GramBound_of_admissible h
  nlinarith

end LeanPool.Besicovitch
