/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Cutoff.TimeScaleFacts

/-! Algebraic scale conversion for the corrected `4δ` exponent in the diffusivity-recursion
    estimate. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section3

open AVenhance

/-- The exponent identity in the source proof is `8δ`. -/
theorem exprat_source_exponent_eq_eight_delta {β : ℝ} (hβ : 1 < β) :
    (2 - β) * (q β - 1) - q β * gamma β = 8 * delta β := by
  unfold gamma delta
  have hqpos : 0 < q β := by
    rw [Infra.Cutoff.q_eq_beta_div_four_sub_one hβ]
    positivity
  have hqp : q β + 1 ≠ 0 := by linarith
  field_simp [hqp]
  ring

/-- The corrected scale exponent after using
`τ_m ≍ ε_{m-1}^{2-β+4δ}`. -/
theorem exprat_normalized_exponent_eq_four_delta {β : ℝ} (hβ : 1 < β) :
    q β * (2 - β - gamma β) - (2 - β + 4 * delta β) =
      4 * delta β := by
  have h := exprat_source_exponent_eq_eight_delta hβ
  have halg :
      q β * (2 - β - gamma β) - (2 - β + 4 * delta β) =
        ((2 - β) * (q β - 1) - q β * gamma β) - 4 * delta β := by ring
  rw [halg, h]
  ring

/-- Factor the quotient so that the `4δ` contribution from the time scale
and the normalized diffusivity contribution can be bounded independently. -/
theorem exprat_factorization {β : ℝ} {e τ κm : ℝ}
    (he : 0 < e) (hτ : 0 < τ) (hκm : 0 < κm) :
    e ^ 2 / (κm * τ) =
      (e ^ (2 - β - gamma β) / τ) *
        (e ^ (β + gamma β) / κm) := by
  have hnat : e ^ (2 : ℕ) = e ^ (2 : ℝ) := (Real.rpow_natCast e 2).symm
  rw [hnat, show (2 : ℝ) = (2 - β - gamma β) + (β + gamma β) by ring,
    Real.rpow_add he]
  field_simp [ne_of_gt hτ, ne_of_gt hκm]
  ring_nf

theorem ExpratScaling.rpow_scale_ratio_bounds {x y A B τ lo hi p q r : ℝ}
    (hy : 0 < y) (hA : 0 < A) (hB : 0 < B) (hp : 0 ≤ p)
    (hτ : 0 < τ) (hlo : 0 < lo) (hhi : 0 < hi)
    (hscaleLo : A * y ^ q ≤ x) (hscaleHi : x ≤ B * y ^ q)
    (hτLo : lo * y ^ r ≤ τ) (hτHi : τ ≤ hi * y ^ r) :
    (A ^ p / hi) * y ^ (q * p - r) ≤ x ^ p / τ ∧
      x ^ p / τ ≤ (B ^ p / lo) * y ^ (q * p - r) := by
  have hxp : 0 < x := by
    have hyq : 0 < y ^ q := Real.rpow_pos_of_pos hy q
    exact lt_of_lt_of_le (mul_pos hA hyq) hscaleLo
  have hnumLo : A ^ p * y ^ (q * p) ≤ x ^ p := by
    calc
      A ^ p * y ^ (q * p) = (A * y ^ q) ^ p := by
        rw [Real.mul_rpow hA.le (Real.rpow_nonneg hy.le q), Real.rpow_mul hy.le]
      _ ≤ x ^ p := Real.rpow_le_rpow (mul_pos hA (Real.rpow_pos_of_pos hy q)).le
        hscaleLo hp
  have hnumHi : x ^ p ≤ B ^ p * y ^ (q * p) := by
    calc
      x ^ p ≤ (B * y ^ q) ^ p := Real.rpow_le_rpow hxp.le hscaleHi hp
      _ = B ^ p * y ^ (q * p) := by
        rw [Real.mul_rpow hB.le (Real.rpow_nonneg hy.le q), Real.rpow_mul hy.le]
  have hnumLoNonneg : 0 ≤ A ^ p * y ^ (q * p) := by positivity
  have hnumHiNonneg : 0 ≤ B ^ p * y ^ (q * p) := by positivity
  have hdenLo : 0 < lo * y ^ r := mul_pos hlo (Real.rpow_pos_of_pos hy r)
  have hdenHi : 0 < hi * y ^ r := mul_pos hhi (Real.rpow_pos_of_pos hy r)
  have hratioLo :
      (A ^ p * y ^ (q * p)) / (hi * y ^ r) ≤ x ^ p / τ := by
    calc
      (A ^ p * y ^ (q * p)) / (hi * y ^ r) ≤
          (A ^ p * y ^ (q * p)) / τ :=
        div_le_div_of_nonneg_left hnumLoNonneg hτ hτHi
      _ ≤ x ^ p / τ := div_le_div_of_nonneg_right hnumLo hτ.le
  have hratioHi :
      x ^ p / τ ≤ (B ^ p * y ^ (q * p)) / (lo * y ^ r) := by
    calc
      x ^ p / τ ≤ (B ^ p * y ^ (q * p)) / τ :=
        div_le_div_of_nonneg_right hnumHi hτ.le
      _ ≤ (B ^ p * y ^ (q * p)) / (lo * y ^ r) :=
        div_le_div_of_nonneg_left hnumHiNonneg hdenLo hτLo
  constructor
  · have hform : (A ^ p / hi) * y ^ (q * p - r) =
    (A ^ p * y ^ (q * p)) / (hi * y ^ r) := by
      rw [Real.rpow_sub hy]
      field_simp [ne_of_gt hhi, ne_of_gt (Real.rpow_pos_of_pos hy r)]
    rw [hform]
    exact hratioLo
  · have hform : (B ^ p * y ^ (q * p)) / (lo * y ^ r) =
    (B ^ p / lo) * y ^ (q * p - r) := by
      rw [Real.rpow_sub hy]
      field_simp [ne_of_gt hlo, ne_of_gt (Real.rpow_pos_of_pos hy r)]
    rw [← hform]
    exact hratioHi

/-- The normalized `κ_m` estimate and the corrected time-scale exponent imply
the two-sided `e.exprat.bound` with exponent `4δ`. The scale-ratio and
time-scale hypotheses are stated explicitly so this lemma does not conceal the
separate proof of the `κ_m` recurrence estimate. -/
theorem exprat_bounds_of_normalized_kappa {β : ℝ} {e eprev τ κm : ℝ}
    {aLo aHi tauLo tauHi kappaLo kappaHi : ℝ}
    (hβ : 1 < β)
    (he : 0 < e) (heprev : 0 < eprev) (hτ : 0 < τ) (hκm : 0 < κm)
    (haLo : 0 < aLo) (haHi : 0 < aHi)
    (htauLo : 0 < tauLo) (htauHi : 0 < tauHi)
    (hkappaLo : 0 < kappaLo) (hkappaHi : 0 < kappaHi)
    (hp : 0 ≤ 2 - β - gamma β)
    (hscaleLo : aLo * eprev ^ (q β) ≤ e)
    (hscaleHi : e ≤ aHi * eprev ^ (q β))
    (htimeLo : tauLo * eprev ^ (2 - β + 4 * delta β) ≤ τ)
    (htimeHi : τ ≤ tauHi * eprev ^ (2 - β + 4 * delta β))
    (hkappaLoBound : kappaLo * e ^ (β + gamma β) ≤ κm)
    (hkappaHiBound : κm ≤ kappaHi * e ^ (β + gamma β)) :
    (aLo ^ (2 - β - gamma β) / (kappaHi * tauHi)) *
        eprev ^ (4 * delta β) ≤ e ^ 2 / (κm * τ) ∧
      e ^ 2 / (κm * τ) ≤
        (aHi ^ (2 - β - gamma β) / (kappaLo * tauLo)) *
          eprev ^ (4 * delta β) := by
  have hpow := ExpratScaling.rpow_scale_ratio_bounds heprev haLo haHi hp hτ htauLo htauHi
    hscaleLo hscaleHi htimeLo htimeHi
  · have hfactor := exprat_factorization (β := β) he hτ hκm
    rw [hfactor]
    have hEs : 0 < e ^ (β + gamma β) := Real.rpow_pos_of_pos he _
    have hsecondLo : 1 / kappaHi ≤ e ^ (β + gamma β) / κm := by
      have hInv := (one_div_le_one_div
        (mul_pos hkappaHi hEs) hκm).2 hkappaHiBound
      calc
        1 / kappaHi = e ^ (β + gamma β) * (1 / (kappaHi * e ^ (β + gamma β))) := by
          field_simp [ne_of_gt hkappaHi, ne_of_gt hEs]
        _ ≤ e ^ (β + gamma β) * (1 / κm) :=
          mul_le_mul_of_nonneg_left hInv hEs.le
        _ = e ^ (β + gamma β) / κm := by ring
    have hsecondHi : e ^ (β + gamma β) / κm ≤ 1 / kappaLo := by
      have hInv := one_div_le_one_div_of_le (mul_pos hkappaLo hEs)
        hkappaLoBound
      calc
        e ^ (β + gamma β) / κm = e ^ (β + gamma β) * (1 / κm) := by ring
        _ ≤ e ^ (β + gamma β) * (1 / (kappaLo * e ^ (β + gamma β))) :=
          mul_le_mul_of_nonneg_left hInv hEs.le
        _ = 1 / kappaLo := by
          field_simp [ne_of_gt hkappaLo, ne_of_gt hEs]
    have hExp := exprat_normalized_exponent_eq_four_delta hβ
    have hfirstLo := hpow.1
    have hfirstHi := hpow.2
    rw [hExp] at hfirstLo hfirstHi
    constructor
    · calc
        (aLo ^ (2 - β - gamma β) / (kappaHi * tauHi)) *
            eprev ^ (4 * delta β) =
          ((aLo ^ (2 - β - gamma β) / tauHi) *
            eprev ^ (4 * delta β)) * (1 / kappaHi) := by ring
        _ ≤ (e ^ (2 - β - gamma β) / τ) *
            (e ^ (β + gamma β) / κm) := by
          exact mul_le_mul hfirstLo hsecondLo (by positivity) (by positivity)
    · calc
        (e ^ (2 - β - gamma β) / τ) *
            (e ^ (β + gamma β) / κm) ≤
          ((aHi ^ (2 - β - gamma β) / tauLo) *
            eprev ^ (4 * delta β)) * (1 / kappaLo) := by
                exact mul_le_mul hfirstHi hsecondHi (by positivity) (by positivity)
        _ = (aHi ^ (2 - β - gamma β) / (kappaLo * tauLo)) *
            eprev ^ (4 * delta β) := by ring
end AVenhance.Infra.Section3

end
