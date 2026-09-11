/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketFrameStability
import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketFrameRenewal
import Mathlib.Algebra.Order.Star.Real

/-!
# Packet Frame Quantitative
-/

@[expose] public section

noncomputable section

open Set

namespace EulerPacketFrameQuantitative

open Real EulerPacketGrowth EulerPacketRay EulerPacketFrameStability
    EulerPacketFrameRenewal

/-- Comparison of the polynomial losses on a common time scale. -/
theorem scaled_power_le
    {Θ K e : ℝ} {n m : ℕ} (hΘ : 1 ≤ Θ) (hK : 1 ≤ K) (he : 0 ≤ e) (hnm : n ≤ m) :
    e * Θ ^ n ≤ K * e * Θ ^ m := by
  have hpow := pow_le_pow_right₀ hΘ hnm
  have hm := mul_le_mul_of_nonneg_left hpow he
  have hKmul := mul_le_mul_of_nonneg_right hK (by positivity : 0 ≤ e * Θ ^ m)
  linarith only [hm, hKmul]

/-- Explicit polynomial control of all target-frame perturbation losses. -/
theorem frame_error_polynomial_bounds
    {Θ K e ε P₀ : ℝ}
    (hΘ : 1 ≤ Θ) (hK : 1 ≤ K) (he : 0 ≤ e) (hε : 0 ≤ ε) (hεe : ε ≤ e)
    (hsmall : 1000000 * K * e * Θ ^ 40 ≤ 1)
    (hP₀ : 1 ≤ P₀) (hP₀upper : P₀ ≤ Θ ^ 2) :
    let ρ := 800 * e * Θ ^ 5
    let η := K * e * Θ ^ 29
    let dD := 6 * ρ * Θ ^ 2 + 9 * ε ^ 2 * Θ ^ 4
    let dE := 3681 * ε ^ 2 * Θ ^ 4
    let dJ := 1470 * e * Θ ^ 4 + 20 * ρ + 20 * Θ ^ 2 * η
    let dS := (1100 * ρ + 400 * η + 2520 * e * Θ ^ 2 + 500 * ε ^ 2) * Θ ^ 4
    ρ ≤ 1 / 2 ∧ η ≤ 1 / 2 ∧ 210 * e * Θ ^ 2 ≤ 1 ∧ dE ≤ 1 ∧ dJ ≤ P₀ / 4 ∧
      4 * dJ + 16 * P₀ * dD + 16 * P₀ ^ 2 * dE ≤ 30000000 * K * e * Θ ^ 40 ∧
      8 * dS + 640 * (dJ / P₀) + 640 * dE ≤ 30000000 * K * e * Θ ^ 40 := by
  let ρ := 800 * e * Θ ^ 5
  let η := K * e * Θ ^ 29
  let dD := 6 * ρ * Θ ^ 2 + 9 * ε ^ 2 * Θ ^ 4
  let dE := 3681 * ε ^ 2 * Θ ^ 4
  let dJ := 1470 * e * Θ ^ 4 + 20 * ρ + 20 * Θ ^ 2 * η
  let dS := (1100 * ρ + 400 * η + 2520 * e * Θ ^ 2 + 500 * ε ^ 2) * Θ ^ 4
  let M := K * e * Θ ^ 40
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hMb : 1000000 * M ≤ 1 := by dsimp [M]; linarith only [hsmall]
  have hp (n : ℕ) (hn : n ≤ 40) : e * Θ ^ n ≤ M := scaled_power_le hΘ hK he hn
  have hKp (n : ℕ) (hn : n ≤ 40) : K * e * Θ ^ n ≤ M := by
    have hh := pow_le_pow_right₀ hΘ hn
    have hm := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ K * e)
    exact hm
  have he1 : e ≤ 1 := by
    have hh := hp 0 (by decide)
    norm_num at hh
    linarith only [hh, hMb]
  have hε1 : ε ≤ 1 := hεe.trans he1
  have hε2 : ε ^ 2 ≤ e := by nlinarith only [hε, hε1, hεe]
  have hεp (n : ℕ) (hn : n ≤ 40) : ε ^ 2 * Θ ^ n ≤ M := by
    have hh := mul_le_mul_of_nonneg_right hε2 (by positivity : 0 ≤ Θ ^ n)
    exact hh.trans (hp n hn)
  have hρb : ρ ≤ 1 / 2 := by have hh := hp 5 (by decide); dsimp [ρ]; linarith only [hh, hMb]
  have hηb : η ≤ 1 / 2 := by have hh := hKp 29 (by decide); dsimp [η]; linarith only [hh, hMb]
  have hAb : 210 * e * Θ ^ 2 ≤ 1 := by have hh := hp 2 (by decide); linarith only [hh, hMb]
  have hEb : dE ≤ 1 := by have hh := hεp 4 (by decide); dsimp [dE]; linarith only [hh, hMb]
  have hJbound : dJ ≤ 17490 * M := by
    have h4 := hp 4 (by decide)
    have h5 := hp 5 (by decide)
    have h31 := hKp 31 (by decide)
    dsimp [dJ, ρ, η]
    linarith only [h4, h5, h31]
  have hJb : dJ ≤ P₀ / 4 := by linarith only [hJbound, hMb, hP₀]
  have hD0 : 0 ≤ dD := by dsimp [dD, ρ]; positivity
  have hE0 : 0 ≤ dE := by dsimp [dE]; positivity
  have hJ0 : 0 ≤ dJ := by dsimp [dJ, ρ, η]; positivity
  have hP₀0 : 0 ≤ P₀ := by linarith
  have hP₀sq : P₀ ^ 2 ≤ Θ ^ 4 := by
    have hh := (sq_le_sq₀ hP₀0 (sq_nonneg Θ)).mpr hP₀upper
    linarith only [hh]
  have hPD : P₀ * dD ≤ 4809 * M := by
    have hm := mul_le_mul_of_nonneg_right hP₀upper hD0
    have h9 := hp 9 (by decide)
    have h6 := hεp 6 (by decide)
    dsimp [dD, ρ] at hm ⊢
    linarith only [hm, h9, h6]
  have hPE : P₀ ^ 2 * dE ≤ 3681 * M := by
    have hm := mul_le_mul_of_nonneg_right hP₀sq hE0
    have h8 := hεp 8 (by decide)
    dsimp [dE] at hm ⊢
    linarith only [hm, h8]
  have hSbound : dS ≤ 883420 * M := by
    have h9 := hp 9 (by decide)
    have h33 := hKp 33 (by decide)
    have h6 := hp 6 (by decide)
    have h4 := hεp 4 (by decide)
    dsimp [dS, ρ, η]
    linarith only [h9, h33, h6, h4]
  have hEbound : dE ≤ 3681 * M := by
    have hh := hεp 4 (by decide)
    dsimp [dE]
    linarith only [hh]
  have hJdiv : dJ / P₀ ≤ dJ := by
    apply (div_le_iff₀ (by linarith : 0 < P₀)).mpr
    linarith only [mul_nonneg hJ0 (sub_nonneg.mpr hP₀)]
  change ρ ≤ 1 / 2 ∧ η ≤ 1 / 2 ∧ 210 * e * Θ ^ 2 ≤ 1 ∧ dE ≤ 1 ∧ dJ ≤ P₀ / 4 ∧
    4 * dJ + 16 * P₀ * dD + 16 * P₀ ^ 2 * dE ≤ 30000000 * K * e * Θ ^ 40 ∧
    8 * dS + 640 * (dJ / P₀) + 640 * dE ≤ 30000000 * K * e * Θ ^ 40
  dsimp [M] at hJbound hPD hPE hSbound hEbound hM
  refine ⟨hρb, hηb, hAb, hEb, hJb, ?_, ?_⟩
  · linarith only [hJbound, hPD, hPE, hM]
  · linarith only [hSbound, hJbound, hJdiv, hEbound, hM]

/-- The source's `Θ^40` frame-renewal estimate, derived from coefficient,
ray, and relative state errors and the actual scalar initial value problem. -/
theorem frame_renewal_order40
    {σ y Θ K e ε P Q N r : ℝ} {A : Fin 3 → Fin 3 → ℝ} {Z Z₁ : ℝ → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1 / 4) (hy : 0 < y) (hysmall : y ≤ 1 / 2)
    (hΘ : 1 ≤ Θ) (hK : 1 ≤ K) (he : 0 ≤ e) (hε : 0 ≤ ε) (hεe : ε ≤ e)
    (htΘ : y⁻¹ / σ ≤ Θ) (hsmall : 1000000 * K * e * Θ ^ 40 ≤ 1)
    (hZ : ∀ t, 0 ≤ t → HasDerivAt Z (Z₁ t) t)
    (hfluxZ : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => (1 + (σ ^ 2 * s ^ 2) ^ 2) * Z₁ s)
        (2 * (1 - σ ^ 2 * (σ ^ 2 * t ^ 2)) * Z t) t)
    (hZ0 : Z 0 = 1) (hZ₁0 : 0 ≤ Z₁ 0)
    (hP : |P - (y⁻¹) ^ 2| ≤ 800 * e * Θ ^ 5)
    (hQ : |Q + 2 * σ * y⁻¹| ≤ 800 * e * Θ ^ 5)
    (hN : |N - 1| ≤ 800 * e * Θ ^ 5)
    (hr : |r + Z₁ (y⁻¹ / σ) / Z (y⁻¹ / σ)| ≤ 10 * (K * e * Θ ^ 29))
    (hA : ∀ i j, |A i j - idealVelocityEntry (σ ^ 2) i j| ≤ 3 * e) :
    let w := velocityThird P Q N r 1
    let D := rayDenominator ε P Q N
    let E := velocityDirectionNormSq ε r w
    let J := velocityNumerator A P Q N r 1 w
    let S := frameCrossNumerator ε P Q N r w (rowAction A 0 r w) (rowAction A 1 r w) (rowAction A 2
        r w)
    |J / (sqrt D * sqrt E) - 1| ≤
      y ^ 4 + σ ^ 2 * y ^ 2 + 8 * σ * y ^ 3 + 30000000 * K * e * Θ ^ 40 ∧
    |(y⁻¹) ^ 2 * S / (J * sqrt E) - 1| ≤ 1500 * σ + 30000000 * K * e * Θ ^ 40 := by
  let t := y⁻¹ / σ
  let P₀ := (y⁻¹) ^ 2
  let Q₀ := -2 * σ * y⁻¹
  let r₀ := -Z₁ t / Z t
  let ρ := 800 * e * Θ ^ 5
  let η := K * e * Θ ^ 29
  let dD := 6 * ρ * Θ ^ 2 + 9 * ε ^ 2 * Θ ^ 4
  let dE := 3681 * ε ^ 2 * Θ ^ 4
  let dJ := 1470 * e * Θ ^ 4 + 20 * ρ + 20 * Θ ^ 2 * η
  let dS := (1100 * ρ + 400 * η + 2520 * e * Θ ^ 2 + 500 * ε ^ 2) * Θ ^ 4
  let w := velocityThird P Q N r 1
  let D := rayDenominator ε P Q N
  let E := velocityDirectionNormSq ε r w
  let J := velocityNumerator A P Q N r 1 w
  let S := frameCrossNumerator ε P Q N r w (rowAction A 0 r w) (rowAction A 1 r w) (rowAction A 2 r
      w)
  have hΘ0 : 0 ≤ Θ := by linarith
  have hσne : σ ≠ 0 := ne_of_gt hσ
  have hyinv0 : 0 ≤ y⁻¹ := inv_nonneg.mpr hy.le
  have hyinv : 1 ≤ y⁻¹ := by
    rw [← one_div]
    exact (le_div_iff₀ hy).mpr (by linarith)
  have hyinvΘ : y⁻¹ ≤ Θ := by
    have hh := (div_le_iff₀ hσ).mp htΘ
    have hm := mul_le_mul_of_nonneg_left (show σ ≤ 1 by linarith) hΘ0
    linarith only [hh, hm]
  have ht : 1 ≤ t := by
    dsimp [t]
    apply (le_div_iff₀ hσ).mpr
    linarith only [hyinv, hσsmall]
  have hP₀ : 1 ≤ P₀ := by dsimp [P₀]; nlinarith only [hyinv]
  have hP₀upper : P₀ ≤ Θ ^ 2 := (sq_le_sq₀ hyinv0 hΘ0).mpr hyinvΘ
  have hP₀abs : |P₀| ≤ Θ ^ 2 := by rw [abs_of_nonneg (by dsimp [P₀]; positivity)]; exact hP₀upper
  have hQ₀abs : |Q₀| ≤ 2 * Θ ^ 2 := by
    dsimp [Q₀]
    rw [abs_mul, abs_mul, abs_of_pos hσ, abs_of_nonneg hyinv0]
    norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hm := mul_le_mul_of_nonneg_right (show σ ≤ 1 by linarith) hyinv0
    have hΘ2 : Θ ≤ Θ ^ 2 := by nlinarith only [hΘ]
    linarith only [hm, hyinvΘ, hΘ2]
  have hσabs : |σ ^ 2| ≤ 1 := by rw [abs_of_nonneg (sq_nonneg σ)]; nlinarith only [hσ, hσsmall]
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hpoly := frame_error_polynomial_bounds hΘ hK he hε hεe hsmall hP₀ hP₀upper
  change ρ ≤ 1 / 2 ∧ η ≤ 1 / 2 ∧ 210 * e * Θ ^ 2 ≤ 1 ∧ dE ≤ 1 ∧ dJ ≤ P₀ / 4 ∧
    4 * dJ + 16 * P₀ * dD + 16 * P₀ ^ 2 * dE ≤ 30000000 * K * e * Θ ^ 40 ∧
    8 * dS + 640 * (dJ / P₀) + 640 * dE ≤ 30000000 * K * e * Θ ^ 40 at hpoly
  obtain ⟨hρsmall, hηsmall, hAsmall, hEsmall, hJsmall, hAbound, hBbound⟩ := hpoly
  have hQ' : |Q - Q₀| ≤ ρ := by
    have hid : Q - Q₀ = Q + 2 * σ * y⁻¹ := by dsimp [Q₀]; ring
    rwa [hid]
  have hr₀ : |r₀| ≤ 4 := by
    have hh := equation30_primary_logderivative_bound hσ hσsmall hZ hfluxZ hZ0 hZ₁0 t ht
    simpa only [r₀, neg_div, abs_neg] using hh
  have hr' : |r - r₀| ≤ 10 * η := by
    simpa only [r₀, t, neg_div, sub_neg_eq_add] using hr
  obtain ⟨hrabs, _, hwabs, _⟩ := third_ratio_error hΘ hρ hρsmall hη hηsmall hP₀abs hQ₀abs hP hQ' hN
      hr₀ hr'
  obtain ⟨_, hp, hq, hn, hw, hDlower, hDerror⟩ :=
    ray_geometric_bounds (ε := ε) (U := r) (V := 1) hΘ hρ hρsmall hP₀abs hQ₀abs hP hQ' hN
  have hDE : |D - (1 + (y⁻¹) ^ 4)| ≤ dD := by
    have hid : 1 + P₀ ^ 2 = 1 + (y⁻¹) ^ 4 := by dsimp [P₀]; ring
    rw [hid] at hDerror
    exact hDerror
  have hEnorm := velocity_direction_norm_bound (ε := ε) hΘ hrabs hwabs
  have hEE : E - 1 ≤ dE := hEnorm.2
  have hE : 1 ≤ E := hEnorm.1
  have hcross := frame_cross_error_from_matrix (ε := ε) hΘ hρ hρsmall hη hηsmall
    (by positivity : 0 ≤ 3 * e) (by linarith only [hAsmall] : 70 * (3 * e) * Θ ^ 2 ≤ 1)
    hσabs hP₀abs hQ₀abs hP hQ' hN hr₀ hr' hA
  have hSE' : |S - idealCrossNumerator (σ ^ 2) P₀ Q₀ r₀| ≤ dS := by
    dsimp only at hcross
    dsimp [S, dS]
    linarith only [hcross]
  let j := 147 * e * Θ ^ 4 + 2 * ρ
  have hj : 0 ≤ j := by dsimp [j]; positivity
  have hJraw : |J - ((P₀ + σ ^ 2) * 1 + Q₀ * r)| ≤ j * (|r| + |(1 : ℝ)|) := by
    have hh := velocity_numerator_error hΘ hρ (by
        positivity : 0 ≤ 3 * e) hσabs hA hp hq hn hP hQ' hN hw
    dsimp [J, j, w, P₀]
    linarith only [hh]
  have hpressure := pressure_ratio_error hΘ hη hηsmall hj (by norm_num : (0 : ℝ) < 1)
    hQ₀abs hr₀ (by simpa only [div_one] using hr') hJraw
  have hJE' : |J - (P₀ + σ ^ 2 + Q₀ * r₀)| ≤ dJ := by
    simp only [div_one] at hpressure
    dsimp [j, dJ] at *
    linarith only [hpressure]
  have hPeq : σ ^ 2 * t ^ 2 = P₀ := by dsimp [t, P₀]; field_simp
  have hQeq : -2 * σ ^ 2 * t = Q₀ := by dsimp [t, Q₀]; field_simp
  have hJideal : idealTargetPressure σ y Z Z₁ = P₀ + σ ^ 2 + Q₀ * r₀ := by
    change σ ^ 2 * t ^ 2 + σ ^ 2 + (-2 * σ ^ 2 * t) * r₀ = _
    rw [hPeq, hQeq]
  have hSideal : idealTargetCross σ y Z Z₁ = idealCrossNumerator (σ ^ 2) P₀ Q₀ r₀ := by
    change idealCrossNumerator (σ ^ 2) (σ ^ 2 * t ^ 2) (-2 * σ ^ 2 * t) r₀ = _
    rw [hPeq, hQeq]
  have hJE : |J - idealTargetPressure σ y Z Z₁| ≤ dJ := by rwa [hJideal]
  have hSE : |S - idealTargetCross σ y Z Z₁| ≤ dS := by rwa [hSideal]
  have hrenew := equation30_target_frame_renewal hσ hσsmall hy hysmall hZ hfluxZ hZ0 hZ₁0
    hDlower hE hDE hEE hEsmall hJE hJsmall hSE
  change |J / (sqrt D * sqrt E) - 1| ≤ _ ∧ |(y⁻¹) ^ 2 * S / (J * sqrt E) - 1| ≤ _
  constructor
  · have hh := hrenew.1
    dsimp [P₀] at hAbound
    linarith only [hh, hAbound]
  · have hh := hrenew.2
    exact hh.trans (by dsimp [P₀] at hBbound; linarith only [hBbound])

end EulerPacketFrameQuantitative
