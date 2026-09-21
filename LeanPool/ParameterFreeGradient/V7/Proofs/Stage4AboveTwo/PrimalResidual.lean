/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage4AboveTwo.Identity

/-!
Lower bounds for the mixed gradient and mirror residual in above-two geometry.
-/

namespace V7.Stage4AboveTwo

private noncomputable def scalarYoungConstant (p : ℝ) : ℝ :=
  (p - 2) / p * (2 / (p * aboveUniformConstant p)) ^ (2 / (p - 2))

private theorem scalarYoung_holderConjugate {p : ℝ} (hp : 2 < p) :
    (p / 2).HolderConjugate (p / (p - 2)) := by
  apply Real.holderConjugate_iff.mpr
  constructor
  · linarith
  · field_simp
    ring

private theorem scalarYoung_pointwise
    {p c xi gamma : ℝ} (hp : 2 < p)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hxi : 0 ≤ xi) (hgamma : 0 < gamma) :
    c * xi ^ (2 : ℕ) - aboveUniformConstant p * gamma * xi ^ p ≤
      scalarYoungConstant p * gamma ^ (-2 / (p - 2)) := by
  have hap : 0 < aboveUniformConstant p := uniformConstant_pos hp
  let K : ℝ := p * aboveUniformConstant p * gamma / 2
  have hK : 0 < K := by
    dsimp [K]
    positivity
  let a : ℝ := K ^ (2 / p) * xi ^ (2 : ℕ)
  let b : ℝ := c * K ^ (-2 / p)
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hb : 0 ≤ b := by
    dsimp [b]
    positivity
  have hy := Real.young_inequality_of_nonneg ha hb (scalarYoung_holderConjugate hp)
  have ha_pow : a ^ (p / 2) / (p / 2) =
      aboveUniformConstant p * gamma * xi ^ p := by
    dsimp [a, K]
    rw [Real.mul_rpow (Real.rpow_nonneg (by positivity) _) (sq_nonneg xi)]
    rw [← Real.rpow_mul (le_of_lt hK)]
    rw [← Real.rpow_natCast xi 2]
    rw [← Real.rpow_mul hxi]
    have hp0 : p ≠ 0 := by linarith
    have htwo : (2 : ℝ) ≠ 0 := by norm_num
    rw [show (2 / p) * (p / 2) = 1 by field_simp]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℝ) * (p / 2) = p by ring]
    rw [Real.rpow_one]
    field_simp [hp0, htwo]
    ring
  have hab : a * b = c * xi ^ (2 : ℕ) := by
    dsimp [a, b]
    have hcancel : K ^ (2 / p) * K ^ (-2 / p) = 1 := by
      rw [← Real.rpow_add hK]
      rw [show 2 / p + -2 / p = 0 by ring]
      simp
    calc
      K ^ (2 / p) * xi ^ (2 : ℕ) * (c * K ^ (-2 / p)) =
          c * xi ^ (2 : ℕ) * (K ^ (2 / p) * K ^ (-2 / p)) := by ring
      _ = c * xi ^ (2 : ℕ) := by rw [hcancel, mul_one]
  have hc_pow : c ^ (p / (p - 2)) ≤ 1 := by
    have hexp : 0 ≤ p / (p - 2) := (div_pos (by linarith) (by linarith)).le
    simpa using Real.rpow_le_rpow hc0 hc1 hexp
  have hb_pow : b ^ (p / (p - 2)) / (p / (p - 2)) ≤
      (p - 2) / p * K ^ (-2 / (p - 2)) := by
    dsimp [b]
    rw [Real.mul_rpow hc0 (Real.rpow_nonneg (by positivity) _)]
    rw [← Real.rpow_mul (le_of_lt hK)]
    have hp0 : p ≠ 0 := by linarith
    have hp2ne : p - 2 ≠ 0 := by linarith
    rw [show (-2 / p) * (p / (p - 2)) = -2 / (p - 2) by field_simp]
    rw [div_eq_mul_inv]
    rw [show (p / (p - 2))⁻¹ = (p - 2) / p by field_simp]
    nlinarith [mul_le_mul_of_nonneg_right hc_pow
      (show 0 ≤ (p - 2) / p * K ^ (-2 / (p - 2)) by positivity)]
  have hK_split : (p - 2) / p * K ^ (-2 / (p - 2)) =
      scalarYoungConstant p * gamma ^ (-2 / (p - 2)) := by
    dsimp [K, scalarYoungConstant]
    have hpa : 0 < p * aboveUniformConstant p := mul_pos (by linarith) hap
    rw [show p * aboveUniformConstant p * gamma / 2 =
        (p * aboveUniformConstant p / 2) * gamma by ring]
    rw [Real.mul_rpow (div_nonneg hpa.le (by norm_num)) hgamma.le]
    have hexp : -2 / (p - 2) = -(2 / (p - 2)) := by ring
    rw [hexp, Real.rpow_neg_eq_inv_rpow]
    rw [show 2 / (p * aboveUniformConstant p) =
        (p * aboveUniformConstant p / 2)⁻¹ by field_simp [hpa.ne']]
    ring
  rw [hab, ha_pow] at hy
  calc
    c * xi ^ (2 : ℕ) - aboveUniformConstant p * gamma * xi ^ p ≤
        b ^ (p / (p - 2)) / (p / (p - 2)) := by linarith
    _ ≤ (p - 2) / p * K ^ (-2 / (p - 2)) := hb_pow
    _ = scalarYoungConstant p * gamma ^ (-2 / (p - 2)) := hK_split

theorem scalar_power_deficit_le {p t y : ℝ} (hp : 2 < p)
    (ht : 0 ≤ t) (hy : 0 ≤ y) :
    t / 2 * y ^ (2 : ℕ) - aboveUniformConstant p * y ^ p ≤
      aboveErrorConstant p * t ^ (aboveErrorPower p) := by
  by_cases ht0 : t = 0
  · subst t
    rw [Real.zero_rpow (by
      have := errorPower_gt_one hp
      linarith : aboveErrorPower p ≠ 0)]
    simp only [zero_div, zero_mul]
    rw [mul_zero]
    simpa only [zero_sub] using neg_nonpos.mpr
      (mul_nonneg (uniformConstant_pos hp).le (Real.rpow_nonneg hy p))
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    have hyoung := scalarYoung_pointwise (p := p) (c := 1) (xi := y)
      (gamma := 2 / t) hp (by norm_num) (by norm_num) hy (div_pos (by norm_num) htpos)
    have hscaled := mul_le_mul_of_nonneg_left hyoung
      (show 0 ≤ t / 2 from div_nonneg ht (by norm_num))
    have hleft : t / 2 *
        (1 * y ^ (2 : ℕ) - aboveUniformConstant p * (2 / t) * y ^ p) =
        t / 2 * y ^ (2 : ℕ) - aboveUniformConstant p * y ^ p := by
      field_simp [ht0]
    rw [hleft] at hscaled
    calc
      t / 2 * y ^ (2 : ℕ) - aboveUniformConstant p * y ^ p ≤
          t / 2 * scalarYoungConstant p *
            (2 / t) ^ (-2 / (p - 2)) := by
              simpa [mul_assoc] using hscaled
      _ = aboveErrorConstant p * t ^ (aboveErrorPower p) := by
        unfold scalarYoungConstant aboveErrorConstant aboveErrorPower
        have hap : 0 < aboveUniformConstant p := uniformConstant_pos hp
        have hpa : 0 < p * aboveUniformConstant p := mul_pos (by linarith) hap
        rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 2) ht]
        rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 2) hpa.le]
        have htwo : 0 < (2 : ℝ) := by norm_num
        have htpow : 0 < t ^ (2 / (p - 2)) := Real.rpow_pos_of_pos htpos _
        have htwopow : 0 < (2 : ℝ) ^ (2 / (p - 2)) :=
          Real.rpow_pos_of_pos htwo _
        have hpapow : 0 < (p * aboveUniformConstant p) ^ (2 / (p - 2)) :=
          Real.rpow_pos_of_pos hpa _
        rw [show -2 / (p - 2) = -(2 / (p - 2)) by ring]
        rw [Real.rpow_neg htwo.le, Real.rpow_neg hpa.le]
        rw [Real.rpow_neg ht]
        have hexp : 1 + 2 / (p - 2) = p / (p - 2) := by
          field_simp [show p - 2 ≠ 0 by linarith]
          ring
        have htpower : t * t ^ (2 / (p - 2)) = t ^ (p / (p - 2)) := by
          calc
            t * t ^ (2 / (p - 2)) = t ^ (1 : ℝ) * t ^ (2 / (p - 2)) := by
              rw [Real.rpow_one]
            _ = t ^ (1 + 2 / (p - 2)) := (Real.rpow_add htpos _ _).symm
            _ = t ^ (p / (p - 2)) := by rw [hexp]
        field_simp [ht0, htpow.ne', htwopow.ne', hpapow.ne', hpa.ne']
        calc
          t * (p - 2) * t ^ (2 / (p - 2)) =
              (p - 2) * (t * t ^ (2 / (p - 2))) := by ring
          _ = (p - 2) * t ^ (p / (p - 2)) := by rw [htpower]

theorem mixedResidual_lower {p u d x y : ℝ} (hp : 2 < p)
    (hu : 0 < u) (hy : 0 ≤ y) :
    u / 2 * x ^ (2 : ℕ) + aboveUniformConstant p * y ^ p - d * x * y ≥
      -(aboveErrorConstant p * (d ^ (2 : ℕ) / u) ^ (aboveErrorPower p)) := by
  let t := d ^ (2 : ℕ) / u
  have ht : 0 ≤ t := div_nonneg (sq_nonneg d) hu.le
  have hsquare : 0 ≤ (u * x - d * y) ^ (2 : ℕ) := sq_nonneg _
  have hquad : u / 2 * x ^ (2 : ℕ) - d * x * y ≥
      -(t / 2 * y ^ (2 : ℕ)) := by
    dsimp [t]
    field_simp [hu.ne']
    nlinarith
  have hscalar := scalar_power_deficit_le hp ht hy
  dsimp [t] at hscalar ⊢
  linarith

theorem mixedVectorResidual_lower {p u d : ℝ} (hp : 2 < p)
    (hu : 0 < u) (hd : 0 ≤ d) (a b : Point m) :
    u / 2 * (lpNorm (conjugateExponent p) a) ^ (2 : ℕ) +
        aboveUniformConstant p * (lpNorm p b) ^ p + d * pairing a b ≥
      -(aboveErrorConstant p * (d ^ (2 : ℕ) / u) ^ (aboveErrorPower p)) := by
  have hq := O3.holderConjugate_conjugateExponent (by linarith : 1 < p)
  have habs := O3.abs_pairing_le_lpNorm_mul hq.symm a b
  have hpair : -(lpNorm (conjugateExponent p) a * lpNorm p b) ≤ pairing a b := by
    linarith [neg_le_of_abs_le habs]
  have hdPair := mul_le_mul_of_nonneg_left hpair hd
  have hmix := mixedResidual_lower (p := p) (u := u) (d := d)
    (x := lpNorm (conjugateExponent p) a) (y := lpNorm p b)
    hp hu (O3.lpNorm_nonneg _ _)
  linarith

/-- The sum of quadratic gradient, power mirror, and mixed-pairing residual terms. -/
noncomputable def aboveMixedResidual (p : ℝ) (n : ℕ)
    (u dw : ScalarSeq) (A B : VectorSeq d) : ℝ :=
  ∑ k ∈ Finset.range n,
    ((u k / 2) * (lpNorm (conjugateExponent p) (A k - A (k + 1))) ^ (2 : ℕ) +
      aboveUniformConstant p * (lpNorm p (B k - B (k + 1))) ^ p +
      dw k * pairing (A k - A (k + 1)) (B k - B (k + 1)))

theorem aboveMixedResidual_lower (p : ℝ) (hp : 2 < p) (n : ℕ)
    (u dw : ScalarSeq) (A B : VectorSeq d)
    (hu : ∀ k < n, 0 < u k) (hdw : ∀ k < n, 0 ≤ dw k) :
    aboveMixedResidual p n u dw A B ≥ -aboveErrorSum p n u dw := by
  unfold aboveMixedResidual aboveErrorSum
  have hsum :
      (∑ k ∈ Finset.range n,
          (-(aboveErrorConstant p *
            ((dw k) ^ (2 : ℕ) / u k) ^ (aboveErrorPower p)))) ≤
        (∑ k ∈ Finset.range n,
          ((u k / 2) *
              (lpNorm (conjugateExponent p) (A k - A (k + 1))) ^ (2 : ℕ) +
            aboveUniformConstant p *
              (lpNorm p (B k - B (k + 1))) ^ p +
            dw k * pairing (A k - A (k + 1)) (B k - B (k + 1)))) := by
    apply Finset.sum_le_sum
    intro k hk
    exact mixedVectorResidual_lower hp (hu k (Finset.mem_range.mp hk))
      (hdw k (Finset.mem_range.mp hk))
      (A k - A (k + 1)) (B k - B (k + 1))
  rw [Finset.mul_sum]
  rw [← Finset.sum_neg_distrib]
  exact hsum

end V7.Stage4AboveTwo
