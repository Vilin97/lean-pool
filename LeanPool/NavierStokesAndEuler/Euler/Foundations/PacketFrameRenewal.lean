/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketFrameStability
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Positivity.Finset

/-!
# Packet Frame Renewal
-/

@[expose] public section

noncomputable section

open Set

namespace EulerPacketFrameRenewal

open Real EulerPacketGrowth EulerPacketRay EulerPacketFrameStability

/-- Square-root normalization preserves an error from the unit value. -/
theorem sqrt_unit_error
    {E d : ℝ} (hE : 1 ≤ E) (herror : E - 1 ≤ d) (hd : d ≤ 1) :
    1 ≤ sqrt E ∧ sqrt E ≤ 2 ∧ |sqrt E - 1| ≤ d := by
  have hs : 1 ≤ sqrt E := Real.one_le_sqrt.mpr hE
  have hself : sqrt E ≤ E := Real.sqrt_le_self_iff.mpr (Or.inr hE)
  refine ⟨hs, by linarith, ?_⟩
  rw [abs_of_nonneg (by linarith : 0 ≤ sqrt E - 1)]
  linarith

/-- The ray square root is uniformly stable away from zero. -/
theorem sqrt_ray_error
    {D D₀ d : ℝ} (hD : 1 / 4 ≤ D) (hD₀ : 1 ≤ D₀) (herror : |D - D₀| ≤ d) :
    1 / 2 ≤ sqrt D ∧ |sqrt D - sqrt D₀| ≤ d := by
  have hD0 : 0 ≤ D := by linarith
  have hD₀0 : 0 ≤ D₀ := by linarith
  have hsq := sq_sqrt hD0
  have hsq₀ := sq_sqrt hD₀0
  have hs0 := sqrt_nonneg D
  have hs₀ : 1 ≤ sqrt D₀ := Real.one_le_sqrt.mpr hD₀
  have hsum : 1 ≤ sqrt D + sqrt D₀ := by linarith
  have hid : (sqrt D - sqrt D₀) * (sqrt D + sqrt D₀) = D - D₀ := by nlinarith only [hsq, hsq₀]
  have hh : |sqrt D - sqrt D₀| * (sqrt D + sqrt D₀) ≤ d := by
    rw [← abs_of_nonneg (by linarith : 0 ≤ sqrt D + sqrt D₀), ← abs_mul, hid]
    exact herror
  have hm := mul_le_mul_of_nonneg_left hsum (abs_nonneg (sqrt D - sqrt D₀))
  constructor <;> nlinarith only [hD, hsq, hs0, hh, hm]

/-- Stability of the next-frame expansion coefficient under perturbation
of the pressure numerator and both normalization factors. -/
theorem expansion_quotient_error
    {D D₀ E J J₀ dD dE dJ M aerr : ℝ}
    (hD : 1 / 4 ≤ D) (hD₀ : 1 ≤ D₀) (hE : 1 ≤ E)
    (hDE : |D - D₀| ≤ dD) (hEE : E - 1 ≤ dE) (hdE : dE ≤ 1)
    (hJE : |J - J₀| ≤ dJ) (hJ₀ : |J₀| ≤ M) (hroot : sqrt D₀ ≤ M)
    (hideal : |J₀ / sqrt D₀ - 1| ≤ aerr) :
    |J / (sqrt D * sqrt E) - 1| ≤
      aerr + 4 * dJ + 4 * M * (2 * dD + M * dE) := by
  obtain ⟨hrootD, hrootDiff⟩ := sqrt_ray_error hD hD₀ hDE
  obtain ⟨hrootE, hrootE2, hrootEE⟩ := sqrt_unit_error hE hEE hdE
  have hrootD₀ : 1 ≤ sqrt D₀ := Real.one_le_sqrt.mpr hD₀
  have hM : 0 ≤ M := (abs_nonneg _).trans hJ₀
  have hden : 1 / 4 ≤ sqrt D * sqrt E := by
    have hh := mul_le_mul hrootD hrootE (by norm_num : (0 : ℝ) ≤ 1) (sqrt_nonneg D)
    nlinarith only [hh]
  have hdenDiff : |sqrt D * sqrt E - sqrt D₀| ≤ 2 * dD + M * dE := by
    have hh := abs_product_difference hrootDiff hrootEE
      (show |sqrt D₀| ≤ M by rw [abs_of_nonneg (sqrt_nonneg D₀)]; exact hroot)
      (show |sqrt E| ≤ 2 by rw [abs_of_nonneg (sqrt_nonneg E)]; exact hrootE2)
    simpa only [mul_one, mul_comm dD 2] using hh
  have hdiff := quotient_difference_bound hden hrootD₀ hJE hJ₀ hdenDiff
  have ht := abs_add_le (J / (sqrt D * sqrt E) - J₀ / sqrt D₀) (J₀ / sqrt D₀ - 1)
  have hid : J / (sqrt D * sqrt E) - J₀ / sqrt D₀ + (J₀ / sqrt D₀ - 1) =
      J / (sqrt D * sqrt E) - 1 := by ring
  rw [hid] at ht
  nlinarith only [ht, hdiff, hideal]

/-- Quotient stability when the reference denominator is at least one half. -/
theorem quotient_error_half_denominator
    {a a₀ b b₀ da db M : ℝ}
    (hb : 1 / 4 ≤ b) (hb₀ : 1 / 2 ≤ b₀)
    (ha : |a - a₀| ≤ da) (ha₀ : |a₀| ≤ M) (hbb : |b - b₀| ≤ db) :
    |a / b - a₀ / b₀| ≤ 8 * da + 16 * M * db := by
  have ha2 : |2 * a - 2 * a₀| ≤ 2 * da := by
    have hid : 2 * a - 2 * a₀ = 2 * (a - a₀) := by ring
    rw [hid, abs_mul]
    norm_num
    linarith only [ha]
  have ha₀2 : |2 * a₀| ≤ 2 * M := by rw [abs_mul]; norm_num; linarith only [ha₀]
  have hb2 : |2 * b - 2 * b₀| ≤ 2 * db := by
    have hid : 2 * b - 2 * b₀ = 2 * (b - b₀) := by ring
    rw [hid, abs_mul]
    norm_num
    linarith only [hbb]
  have hh := quotient_difference_bound (show (1 : ℝ) / 4 ≤ 2 * b by linarith)
    (show (1 : ℝ) ≤ 2 * b₀ by linarith) ha2 ha₀2 hb2
  have hbe : b ≠ 0 := by linarith
  have hb₀e : b₀ ≠ 0 := by linarith
  have h₁ : 2 * a / (2 * b) = a / b := by field_simp
  have h₂ : 2 * a₀ / (2 * b₀) = a₀ / b₀ := by field_simp
  rw [h₁, h₂] at hh
  nlinarith only [hh]

/-- Stability of the next coupling multiplied by the target scale squared. -/
theorem coupling_quotient_error
    {P₀ E J J₀ S S₀ dE dJ dS berr : ℝ}
    (hP₀ : 0 < P₀) (hE : 1 ≤ E) (hEE : E - 1 ≤ dE) (hdE : dE ≤ 1)
    (hJE : |J - J₀| ≤ dJ) (hJEsmall : dJ ≤ P₀ / 4)
    (hJ₀ : 1 / 2 ≤ J₀ / P₀) (hJ₀upper : J₀ / P₀ ≤ 2)
    (hSE : |S - S₀| ≤ dS) (hS₀ : |S₀| ≤ 20)
    (hideal : |S₀ / (J₀ / P₀) - 1| ≤ berr) :
    |P₀ * S / (J * sqrt E) - 1| ≤ berr + 8 * dS + 640 * (dJ / P₀) + 640 * dE := by
  have hP₀ne : P₀ ≠ 0 := ne_of_gt hP₀
  obtain ⟨hrootE, hrootE2, hrootEE⟩ := sqrt_unit_error hE hEE hdE
  have hJscaled : |J / P₀ - J₀ / P₀| ≤ dJ / P₀ := by
    rw [← sub_div, abs_div, abs_of_pos hP₀]
    exact div_le_div_of_nonneg_right hJE hP₀.le
  have hJsmall : dJ / P₀ ≤ 1 / 4 := (div_le_iff₀ hP₀).mpr (by nlinarith only [hJEsmall])
  have hJlower : 1 / 4 ≤ J / P₀ := by
    have hh := (abs_le.mp hJscaled).1
    nlinarith only [hh, hJ₀, hJsmall]
  have hden : 1 / 4 ≤ (J / P₀) * sqrt E := by
    have hh := mul_le_mul hJlower hrootE (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith : 0 ≤ J / P₀)
    nlinarith only [hh]
  have hJ₀abs : |J₀ / P₀| ≤ 2 := by rw [abs_of_nonneg (by linarith : 0 ≤ J₀ / P₀)]; exact hJ₀upper
  have hdenDiff : |(J / P₀) * sqrt E - J₀ / P₀| ≤ 2 * (dJ / P₀) + 2 * dE := by
    have hh := abs_product_difference hJscaled hrootEE hJ₀abs
      (show |sqrt E| ≤ 2 by rw [abs_of_nonneg (sqrt_nonneg E)]; exact hrootE2)
    simpa only [mul_one, mul_comm (dJ / P₀) 2] using hh
  have hdiff := quotient_error_half_denominator hden hJ₀ hSE hS₀ hdenDiff
  have hJpos : 0 < J := by
    have hh : 0 < J / P₀ := by linarith only [hJlower]
    exact (div_pos_iff_of_pos_right hP₀).mp hh
  have hid : P₀ * S / (J * sqrt E) = S / ((J / P₀) * sqrt E) := by field_simp
  rw [hid]
  have ht := abs_add_le (S / ((J / P₀) * sqrt E) - S₀ / (J₀ / P₀)) (S₀ / (J₀ / P₀) - 1)
  have hsum : S / ((J / P₀) * sqrt E) - S₀ / (J₀ / P₀) + (S₀ / (J₀ / P₀) - 1) =
      S / ((J / P₀) * sqrt E) - 1 := by ring
  rw [hsum] at ht
  nlinarith only [ht, hdiff, hideal]

/-- Absolute bounds for the ideal inversion-coordinate frame quantities. -/
theorem ideal_frame_absolute_bounds
    {ε y z : ℝ} (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 4)
    (hy : 0 ≤ y) (hysmall : y ≤ 1 / 2) (hz : 0 ≤ z) (hzupper : z ≤ 4) :
    idealFrameDenominator ε y z ≤ 2 ∧ |idealFrameNumerator ε y z| ≤ 20 := by
  have hy2 : y ^ 2 ≤ 1 / 4 := by nlinarith only [hy, hysmall]
  have hy3 : y ^ 3 ≤ 1 / 8 := by
    have hh := pow_le_pow_left₀ hy hysmall 3
    norm_num at hh
    exact hh
  have hy4 : y ^ 4 ≤ 1 / 16 := by
    have hh := pow_le_pow_left₀ hy hysmall 4
    norm_num at hh
    exact hh
  have hz2 : z ^ 2 ≤ 16 := by nlinarith only [hz, hzupper]
  have hε2 : ε ^ 2 ≤ 1 / 16 := by nlinarith only [hε, hεsmall]
  have hT : ε ^ 2 * y ^ 2 ≤ 1 / 64 := by
    have hh := mul_le_mul hε2 hy2 (sq_nonneg y) (by norm_num : (0 : ℝ) ≤ 1 / 16)
    nlinarith only [hh]
  have hZ : (1 + y ^ 4) * z ^ 2 ≤ 17 := by
    have hh := mul_le_mul (show 1 + y ^ 4 ≤ 17 / 16 by linarith only [hy4]) hz2
      (sq_nonneg z) (by norm_num : (0 : ℝ) ≤ 17 / 16)
    nlinarith only [hh]
  have hεz : ε * z ≤ 1 := by
    have hh := mul_le_mul hεsmall hzupper hz (by norm_num : (0 : ℝ) ≤ 1 / 4)
    nlinarith only [hh]
  have hU : 2 * ε * z * y ^ 3 ≤ 1 / 4 := by
    have hh := mul_le_mul hεz hy3 (pow_nonneg hy 3) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith only [hh]
  have hT0 : 0 ≤ ε ^ 2 * y ^ 2 := mul_nonneg (sq_nonneg ε) (sq_nonneg y)
  have hZ0 : 0 ≤ (1 + y ^ 4) * z ^ 2 := by positivity
  have hU0 : 0 ≤ 2 * ε * z * y ^ 3 := by positivity
  constructor
  · unfold idealFrameDenominator
    nlinarith only [hT0, hU]
  · unfold idealFrameNumerator
    apply abs_le.mpr
    constructor <;> nlinarith only [hT0, hZ0, hU0, hT, hZ, hU]

theorem target_sqrt_identity {y : ℝ} (hy : y ≠ 0) :
    sqrt (1 + (y⁻¹) ^ 4) = sqrt (1 + y ^ 4) / y ^ 2 := by
  have hid : 1 + (y⁻¹) ^ 4 = (1 + y ^ 4) / (y ^ 2) ^ 2 := by field_simp; ring
  rw [hid, Real.sqrt_div (by positivity : 0 ≤ 1 + y ^ 4), sqrt_sq (sq_nonneg y)]

/-- Ideal frame renewal expressed directly in the original scalar
solution and the target time, rather than in auxiliary Riccati variables. -/
theorem equation30_target_ideal_quantities
    {ε y : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hy : 0 < y) (hysmall : y ≤ 1 / 2)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0) :
    let t := y⁻¹ / ε
    let P₀ := ε ^ 2 * t ^ 2
    let Q₀ := -2 * ε ^ 2 * t
    let r₀ := -V₁ t / V t
    let J₀ := P₀ + ε ^ 2 + Q₀ * r₀
    let S₀ := idealCrossNumerator (ε ^ 2) P₀ Q₀ r₀
    1 ≤ P₀ ∧ 1 / 2 ≤ J₀ / P₀ ∧ J₀ / P₀ ≤ 2 ∧ |S₀| ≤ 20 ∧
      |J₀ / sqrt (1 + P₀ ^ 2) - 1| ≤ y ^ 4 + ε ^ 2 * y ^ 2 + 8 * ε * y ^ 3 ∧
      |S₀ / (J₀ / P₀) - 1| ≤ 1500 * ε := by
  let t := y⁻¹ / ε
  let P₀ := ε ^ 2 * t ^ 2
  let Q₀ := -2 * ε ^ 2 * t
  let r₀ := -V₁ t / V t
  let J₀ := P₀ + ε ^ 2 + Q₀ * r₀
  let S₀ := idealCrossNumerator (ε ^ 2) P₀ Q₀ r₀
  let z := -ε * invertedScalarDeriv ε V V₁ y / invertedScalar ε V y
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hyne : y ≠ 0 := ne_of_gt hy
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have hVp := equation30_global_positive hε hεsmall hV hflux hV0 hV₁0 t ht0
  have hPr : P₀ = (y⁻¹) ^ 2 := by dsimp [P₀, t]; field_simp
  have hQr : Q₀ = -2 * ε * y⁻¹ := by dsimp [Q₀, t]; field_simp
  have hr : r₀ = ε * y - z * y ^ 2 := by
    have hh := inverted_logarithmic_identity (V₁ := V₁) hεne hyne (ne_of_gt hVp)
    dsimp [r₀, t, z]
    rw [neg_div]
    nlinarith only [hh]
  have hJr : J₀ = idealFrameDenominator ε y z / y ^ 2 := by
    dsimp [J₀]
    rw [hPr, hQr, hr]
    exact (ideal_frame_identities hyne).1
  have hSr : S₀ = idealFrameNumerator ε y z := by
    dsimp [S₀, idealCrossNumerator]
    rw [hPr, hQr, hr]
    convert! (ideal_frame_identities (ε := ε) (z := z) hyne).2 using 1
    ring
  have hR := equation30_inverted_riccati_range hε hεsmall hV hflux hV0 hV₁0 y hy (by linarith)
  have hB := equation30_ideal_frame_bounds hε hεsmall hV hflux hV0 hV₁0 y hy hysmall
  have hA := ideal_frame_absolute_bounds hε.le hεsmall hy.le hysmall hR.1 hR.2
  have hJP : J₀ / P₀ = idealFrameDenominator ε y z := by rw [hJr, hPr]; field_simp
  have hJroot : J₀ / sqrt (1 + P₀ ^ 2) = idealFrameDenominator ε y z / sqrt (1 + y ^ 4) := by
    rw [hJr, hPr]
    have hid : ((y⁻¹) ^ 2) ^ 2 = (y⁻¹) ^ 4 := by ring
    rw [hid, target_sqrt_identity hyne]
    field_simp
  have hyinv : 1 ≤ y⁻¹ := by
    rw [← one_div]
    exact (le_div_iff₀ hy).mpr (by linarith)
  change 1 ≤ P₀ ∧ 1 / 2 ≤ J₀ / P₀ ∧ J₀ / P₀ ≤ 2 ∧ |S₀| ≤ 20 ∧
    |J₀ / sqrt (1 + P₀ ^ 2) - 1| ≤ _ ∧ |S₀ / (J₀ / P₀) - 1| ≤ _
  rw [hJP, hSr, hJroot]
  refine ⟨?_, hB.1, hA.1, hA.2, hB.2.2.1, hB.2.2.2⟩
  rw [hPr]
  nlinarith only [hyinv]

/-- The perturbed target ray keeps the shear compression strictly negative
with the reciprocal target-time magnitude used in equation (35). -/
theorem perturbed_target_compression
    {β t ε H P Q N ρ : ℝ}
    (hβ : 0 < β) (ht : 0 < t) (hε : 0 ≤ ε) (hH : 0 ≤ H)
    (hscale : 1 ≤ β * t ^ 2) (_hρ : 0 ≤ ρ) (hρsmall : ρ ≤ 1 / 2) (hρQ : ρ ≤ β * t)
    (hP : |P - β * t ^ 2| ≤ ρ) (hQ : |Q + 2 * β * t| ≤ ρ) (hN : |N - 1| ≤ ρ)
    (hεQ : |ε * Q| ≤ 1 / 2) :
    H * ε * Q * P / rayDenominator ε P Q N ≤ -(H * ε) / (10 * t) := by
  have hPb := abs_le.mp hP
  have hQb := abs_le.mp hQ
  have hNb := abs_le.mp hN
  have hPlower : β * t ^ 2 / 2 ≤ P := by nlinarith only [hPb, hρsmall, hscale]
  have hPupper : P ≤ 3 / 2 * (β * t ^ 2) := by nlinarith only [hPb, hρsmall, hscale]
  have hPpos : 0 < P := by nlinarith only [hPlower, hscale]
  have hQupper : Q ≤ -β * t := by nlinarith only [hQb, hρQ]
  have hNabs : |N| ≤ 3 / 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith only [hNb, hρsmall]
  have hPabs : |P| ≤ 3 / 2 * (β * t ^ 2) := by rwa [abs_of_pos hPpos]
  have hPsq : P ^ 2 ≤ 9 / 4 * (β * t ^ 2) ^ 2 := by
    have hh := (sq_le_sq₀ (abs_nonneg P) (by positivity : 0 ≤ 3 / 2 * (β * t ^ 2))).mpr hPabs
    rw [sq_abs] at hh
    nlinarith only [hh]
  have hNsq : N ^ 2 ≤ 9 / 4 := by
    have hh := (sq_le_sq₀ (abs_nonneg N) (by norm_num : (0 : ℝ) ≤ 3 / 2)).mpr hNabs
    rw [sq_abs] at hh
    nlinarith only [hh]
  have hεQsq : ε ^ 2 * Q ^ 2 ≤ 1 / 4 := by
    have hh := (sq_le_sq₀ (abs_nonneg (ε * Q)) (by norm_num : (0 : ℝ) ≤ 1 / 2)).mpr hεQ
    rw [sq_abs] at hh
    nlinarith only [hh]
  have hscale2 : 1 ≤ (β * t ^ 2) ^ 2 := by nlinarith only [hscale]
  have hDupper : rayDenominator ε P Q N ≤ 5 * β ^ 2 * t ^ 4 := by
    unfold rayDenominator
    nlinarith only [hPsq, hNsq, hεQsq, hscale2]
  have hDpos : 0 < rayDenominator ε P Q N := by
    unfold rayDenominator
    have hh : 0 < P ^ 2 := sq_pos_of_pos hPpos
    positivity
  have hQP : Q * P ≤ -(β ^ 2 * t ^ 3) / 2 := by
    have h₁ := mul_le_mul_of_nonneg_right hQupper hPpos.le
    have h₂ := mul_le_mul_of_nonneg_left hPlower (mul_nonneg hβ.le ht.le)
    nlinarith only [h₁, h₂]
  have hHε : 0 ≤ H * ε := mul_nonneg hH hε
  have hnum := mul_le_mul_of_nonneg_left hQP hHε
  have hnumtime := mul_le_mul_of_nonneg_right hnum (by positivity : 0 ≤ 10 * t)
  have hden := mul_le_mul_of_nonneg_left hDupper hHε
  apply (div_le_div_iff₀ hDpos (by positivity : 0 < 10 * t)).mpr
  nlinarith only [hnumtime, hden]

/-- The coordinate quadratic form of a real three-by-three matrix. -/
def quadraticForm3 (B : Fin 3 → Fin 3 → ℝ) (p q n : ℝ) : ℝ :=
  p * (B 0 0 * p + B 0 1 * q + B 0 2 * n) +
  q * (B 1 0 * p + B 1 1 * q + B 1 2 * n) +
  n * (B 2 0 * p + B 2 1 * q + B 2 2 * n)

theorem quadratic_form_bound
    {B : Fin 3 → Fin 3 → ℝ} {G p q n : ℝ}
    (hB : ∀ i j, |B i j| ≤ G) :
    |quadraticForm3 B p q n| ≤ 3 * G * (p ^ 2 + q ^ 2 + n ^ 2) := by
  have hG : 0 ≤ G := (abs_nonneg _).trans (hB 0 0)
  have hrow0 := three_term_bound (p := p) (q := q) (n := n) (hB 0 0) (hB 0 1) (hB 0 2)
  have hrow1 := three_term_bound (p := p) (q := q) (n := n) (hB 1 0) (hB 1 1) (hB 1 2)
  have hrow2 := three_term_bound (p := p) (q := q) (n := n) (hB 2 0) (hB 2 1) (hB 2 2)
  have h₀ := mul_le_mul_of_nonneg_left hrow0 (abs_nonneg p)
  have h₁ := mul_le_mul_of_nonneg_left hrow1 (abs_nonneg q)
  have h₂ := mul_le_mul_of_nonneg_left hrow2 (abs_nonneg n)
  have ht0 := abs_add_le (p * (B 0 0 * p + B 0 1 * q + B 0 2 * n))
    (q * (B 1 0 * p + B 1 1 * q + B 1 2 * n))
  have ht1 := abs_add_le
    (p * (B 0 0 * p + B 0 1 * q + B 0 2 * n) + q * (B 1 0 * p + B 1 1 * q + B 1 2 * n))
    (n * (B 2 0 * p + B 2 1 * q + B 2 2 * n))
  simp only [abs_mul] at ht0 ht1
  have hnorm : norm3 p q n ^ 2 ≤ 3 * (p ^ 2 + q ^ 2 + n ^ 2) := by
    have h₁ := sq_nonneg (|p| - |q|)
    have h₂ := sq_nonneg (|p| - |n|)
    have h₃ := sq_nonneg (|q| - |n|)
    have hp := sq_abs p
    have hq := sq_abs q
    have hn := sq_abs n
    unfold norm3
    nlinarith only [h₁, h₂, h₃, hp, hq, hn]
  have hm := mul_le_mul_of_nonneg_left hnorm hG
  unfold quadraticForm3 norm3 at *
  nlinarith only [h₀, h₁, h₂, ht0, ht1, hm]

/-- The full normalized compression is the negative shear term plus a
controlled contribution from the older gradient and the packet error. -/
theorem parent_ray_compression
    {B E : Fin 3 → Fin 3 → ℝ} {H ε P Q N G : ℝ}
    (hD : 0 < rayDenominator ε P Q N)
    (hB : ∀ i j, |B i j + E i j| ≤ G) :
    quadraticForm3 (parentEntry B E H) P (ε * Q) N / rayDenominator ε P Q N ≤
      H * ε * Q * P / rayDenominator ε P Q N + 3 * G := by
  have hid : quadraticForm3 (parentEntry B E H) P (ε * Q) N =
      H * ε * Q * P + quadraticForm3 (fun i j => B i j + E i j) P (ε * Q) N := by
    norm_num [quadraticForm3, parentEntry, Fin.ext_iff]
    ring
  have hb := quadratic_form_bound (p := P) (q := ε * Q) (n := N) hB
  have hquad : quadraticForm3 (fun i j => B i j + E i j) P (ε * Q) N ≤
      3 * G * rayDenominator ε P Q N := by
    have hh := le_abs_self (quadraticForm3 (fun i j => B i j + E i j) P (ε * Q) N)
    unfold rayDenominator
    nlinarith only [hh, hb]
  rw [hid, add_div]
  gcongr
  exact (div_le_iff₀ hD).mpr hquad

/-- The ideal pressure-to-velocity ratio at the inverse target scale. -/
noncomputable def idealTargetPressure (ε y : ℝ) (V V₁ : ℝ → ℝ) : ℝ :=
  let t := y⁻¹ / ε
  ε ^ 2 * t ^ 2 + ε ^ 2 + (-2 * ε ^ 2 * t) * (-V₁ t / V t)

/-- The ideal cross numerator at the inverse target scale. -/
noncomputable def idealTargetCross (ε y : ℝ) (V V₁ : ℝ → ℝ) : ℝ :=
  let t := y⁻¹ / ε
  idealCrossNumerator (ε ^ 2) (ε ^ 2 * t ^ 2) (-2 * ε ^ 2 * t) (-V₁ t / V t)

/-- Actual target-frame renewal, with all ideal quantities obtained from
the scalar equation and all perturbation losses displayed explicitly. -/
theorem equation30_target_frame_renewal
    {ε y D E J S dD dE dJ dS : ℝ} {V V₁ : ℝ → ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hy : 0 < y) (hysmall : y ≤ 1 / 2)
    (hV : ∀ t, 0 ≤ t → HasDerivAt V (V₁ t) t)
    (hflux : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (ε ^ 2 * s ^ 2) ^ 2) * V₁ s)
        (2 * (1 - ε ^ 2 * (ε ^ 2 * t ^ 2)) * V t) t)
    (hV0 : V 0 = 1) (hV₁0 : 0 ≤ V₁ 0)
    (hD : 1 / 4 ≤ D) (hE : 1 ≤ E)
    (hDE : |D - (1 + (y⁻¹) ^ 4)| ≤ dD) (hEE : E - 1 ≤ dE) (hdE : dE ≤ 1)
    (hJE : |J - idealTargetPressure ε y V V₁| ≤ dJ) (hJEsmall : dJ ≤ (y⁻¹) ^ 2 / 4)
    (hSE : |S - idealTargetCross ε y V V₁| ≤ dS) :
    |J / (sqrt D * sqrt E) - 1| ≤
      y ^ 4 + ε ^ 2 * y ^ 2 + 8 * ε * y ^ 3 + 4 * dJ +
        16 * (y⁻¹) ^ 2 * dD + 16 * (y⁻¹) ^ 4 * dE ∧
    |(y⁻¹) ^ 2 * S / (J * sqrt E) - 1| ≤
      1500 * ε + 8 * dS + 640 * (dJ / (y⁻¹) ^ 2) + 640 * dE := by
  let t := y⁻¹ / ε
  let P₀ := (y⁻¹) ^ 2
  let J₀ := idealTargetPressure ε y V V₁
  let S₀ := idealTargetCross ε y V V₁
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hPeq : ε ^ 2 * t ^ 2 = P₀ := by dsimp [t, P₀]; field_simp
  have hI := equation30_target_ideal_quantities hε hεsmall hy hysmall hV hflux hV0 hV₁0
  change 1 ≤ ε ^ 2 * t ^ 2 ∧ 1 / 2 ≤ J₀ / (ε ^ 2 * t ^ 2) ∧
    J₀ / (ε ^ 2 * t ^ 2) ≤ 2 ∧ |S₀| ≤ 20 ∧
    |J₀ / sqrt (1 + (ε ^ 2 * t ^ 2) ^ 2) - 1| ≤ _ ∧
    |S₀ / (J₀ / (ε ^ 2 * t ^ 2)) - 1| ≤ _ at hI
  rw [hPeq] at hI
  obtain ⟨hP₀, hJ₀lower, hJ₀upper, hS₀, hAideal, hBideal⟩ := hI
  have hP₀pos : 0 < P₀ := by linarith
  have hJ₀pos : 0 < J₀ := by
    have hh := (le_div_iff₀ hP₀pos).mp hJ₀lower
    nlinarith only [hh, hP₀pos]
  have hJ₀abs : |J₀| ≤ 2 * P₀ := by
    rw [abs_of_pos hJ₀pos]
    exact (div_le_iff₀ hP₀pos).mp hJ₀upper
  have hD₀ : 1 ≤ 1 + P₀ ^ 2 := by nlinarith [sq_nonneg P₀]
  have hroot : sqrt (1 + P₀ ^ 2) ≤ 2 * P₀ := by
    have hh := sq_sqrt (by positivity : 0 ≤ 1 + P₀ ^ 2)
    have hn := sqrt_nonneg (1 + P₀ ^ 2)
    nlinarith only [hh, hn, hP₀]
  have hD₀eq : 1 + P₀ ^ 2 = 1 + (y⁻¹) ^ 4 := by dsimp [P₀]; ring
  have hDE' : |D - (1 + P₀ ^ 2)| ≤ dD := by rwa [hD₀eq]
  have ha := expansion_quotient_error hD hD₀ hE hDE' hEE hdE hJE hJ₀abs hroot hAideal
  have hb := coupling_quotient_error hP₀pos hE hEE hdE hJE hJEsmall hJ₀lower hJ₀upper hSE hS₀
      hBideal
  constructor
  · dsimp [P₀] at ha
    nlinarith only [ha]
  · exact hb

end EulerPacketFrameRenewal
