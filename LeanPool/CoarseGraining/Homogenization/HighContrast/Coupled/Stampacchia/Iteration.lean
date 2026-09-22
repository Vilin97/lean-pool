/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.HighContrast.Coupled.IterationLemma
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Generic De Giorgi iteration (level-volume decay)

This file isolates the purely analytic heart of the coupled Stampacchia estimate:
starting from the geometric *level-recursion* inequality on the combined upper
level volumes

`(l − k)² · (a l)^{(d−2)/d} ≤ Crec · a k`   (for `0 ≤ k < l`),

the combined level volume `a` tends to `0` along the truncation levels
`k_n := K (1 − 2^{-n})` as soon as the threshold `K` is chosen large enough.

The statement is fully abstract in the nonnegative "level-volume" function
`a : ℝ → ℝ`; the geometric bookkeeping (`α = d/(d−2)`, `B = 4^α`,
`Y_n = L^{-d} a(k_n)`) reduces the recursion to the toolbox lemma
`iteration_geometric_decay_tendsto_zero`.
-/

namespace Homogenization

open Filter Topology

/-- The truncation levels `k_n = K (1 − 2^{-n})` used by the De Giorgi iteration. -/
noncomputable def deGiorgiLevel (K : ℝ) (n : ℕ) : ℝ := K * (1 - (2 : ℝ) ^ (-(n : ℝ)))

@[simp] theorem deGiorgiLevel_zero (K : ℝ) : deGiorgiLevel K 0 = 0 := by
  simp [deGiorgiLevel]

theorem deGiorgiLevel_nonneg {K : ℝ} (hK : 0 ≤ K) (n : ℕ) : 0 ≤ deGiorgiLevel K n := by
  have h2n : (0 : ℝ) < (2 : ℝ) ^ (-(n : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have h2n1 : (2 : ℝ) ^ (-(n : ℝ)) ≤ 1 := by
    rw [Real.rpow_neg (by norm_num), inv_le_one_iff₀]
    right
    exact Real.one_le_rpow (by norm_num) (by positivity)
  have : 0 ≤ 1 - (2 : ℝ) ^ (-(n : ℝ)) := by linarith
  exact mul_nonneg hK this

theorem deGiorgiLevel_lt {K : ℝ} (hK : 0 < K) (n : ℕ) : deGiorgiLevel K n < K := by
  have h2n : (0 : ℝ) < (2 : ℝ) ^ (-(n : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have : deGiorgiLevel K n = K - K * (2 : ℝ) ^ (-(n : ℝ)) := by
    simp only [deGiorgiLevel]; ring
  rw [this]
  have : 0 < K * (2 : ℝ) ^ (-(n : ℝ)) := by positivity
  linarith

theorem deGiorgiLevel_strictMono {K : ℝ} (hK : 0 < K) : StrictMono (deGiorgiLevel K) := by
  intro n m hnm
  simp only [deGiorgiLevel]
  have hbase : (0 : ℝ) < 2 := by norm_num
  have hmono : (2 : ℝ) ^ (-(m : ℝ)) < (2 : ℝ) ^ (-(n : ℝ)) := by
    apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
    have : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
    linarith
  have h2m : (0 : ℝ) < (2 : ℝ) ^ (-(m : ℝ)) := Real.rpow_pos_of_pos hbase _
  nlinarith [hmono, hK]

/-- The successive gap between De Giorgi levels: `k_{n+1} − k_n = K·2^{-(n+1)}`. -/
theorem deGiorgiLevel_succ_sub {K : ℝ} (n : ℕ) :
    deGiorgiLevel K (n + 1) - deGiorgiLevel K n = K * (2 : ℝ) ^ (-((n : ℝ) + 1)) := by
  simp only [deGiorgiLevel]
  have h : (2 : ℝ) ^ (-((n : ℝ) + 1)) = (2 : ℝ) ^ (-(n : ℝ)) / 2 := by
    rw [show (-((n : ℝ) + 1)) = (-(n : ℝ)) + (-1) by ring, Real.rpow_add (by norm_num)]
    rw [Real.rpow_neg_one]
    ring
  push_cast
  rw [h]
  ring

/-- Auxiliary: `(4 : ℝ) ^ y = 2 ^ (2 * y)` for real exponents. -/
theorem four_rpow_eq (y : ℝ) : (4 : ℝ) ^ y = (2 : ℝ) ^ (2 * y) := by
  have h4 : (2 : ℝ) ^ (2 : ℝ) = 4 := by
    have e : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
    rw [e, Real.rpow_natCast]; norm_num
  rw [← h4, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]

/-- The squared gap between successive De Giorgi levels, in `4`-power form. -/
theorem deGiorgiLevel_succ_sub_sq {K : ℝ} (n : ℕ) :
    (deGiorgiLevel K (n + 1) - deGiorgiLevel K n) ^ 2
      = K ^ 2 * (4 : ℝ) ^ (-((n : ℝ) + 1)) := by
  rw [deGiorgiLevel_succ_sub]
  rw [mul_pow]
  congr 1
  rw [← Real.rpow_natCast ((2 : ℝ) ^ (-((n : ℝ) + 1))) 2, ← Real.rpow_mul (by norm_num),
    four_rpow_eq]
  congr 1
  push_cast
  ring

/-- **Generic De Giorgi iteration.**  If the combined upper-level volume `a`
obeys the geometric level recursion and the threshold `K` is chosen so the
leading iteration constant is admissible, then `a` tends to `0` along the
truncation levels `k_n = K(1 − 2^{-n})`.

Here `γ = (d−2)/d` is the recursion exponent, `α = d/(d−2) = 1/γ`, `β = α − 1`,
and `B = 4^α`. -/
theorem deGiorgi_levelVolume_tendsto_zero
    {a : ℝ → ℝ} {Ld Crec K α β γ B : ℝ}
    (hnn : ∀ k, 0 ≤ a k)
    (hLd : 0 < Ld)
    (hCrec : 0 ≤ Crec)
    (hK : 0 < K)
    (hα1 : 1 < α)
    (hβ : β = α - 1)
    (hγα : γ * α = 1)
    (hB : B = (4 : ℝ) ^ α)
    (ha0 : a (deGiorgiLevel K 0) ≤ Ld)
    (hrec : ∀ k l : ℝ, 0 ≤ k → k < l →
      (l - k) ^ 2 * (a l) ^ γ ≤ Crec * a k)
    (hKcond : (Crec / K ^ 2) ^ α * B * Ld ^ β ≤ B ^ (-(1 / β))) :
    Tendsto (fun n => a (deGiorgiLevel K n)) atTop (𝓝 0) := by
  have hαpos : 0 < α := lt_trans one_pos hα1
  have hβpos : 0 < β := by rw [hβ]; linarith
  have hBpos : 0 < B := by rw [hB]; exact Real.rpow_pos_of_pos (by norm_num) _
  -- normalized sequence
  set Y : ℕ → ℝ := fun n => a (deGiorgiLevel K n) / Ld with hY_def
  -- leading iteration constant
  set A : ℝ := (Crec / K ^ 2) ^ α * B * Ld ^ β with hA_def
  have hYnn : ∀ n, 0 ≤ Y n := fun n => div_nonneg (hnn _) hLd.le
  have hY0 : Y 0 ≤ 1 := by
    rw [hY_def]
    rw [div_le_one hLd]
    exact ha0
  have hA0 : 0 ≤ A := by
    rw [hA_def]
    have h1 : 0 ≤ (Crec / K ^ 2) ^ α := Real.rpow_nonneg (by positivity) _
    have h2 : 0 ≤ Ld ^ β := Real.rpow_nonneg hLd.le _
    positivity
  -- the Y-recursion
  have hrecY : ∀ n, Y (n + 1) ≤ A * B ^ (n : ℝ) * Y n ^ (1 + β) := by
    intro n
    have hkn0 : 0 ≤ deGiorgiLevel K n := deGiorgiLevel_nonneg hK.le n
    have hknlt : deGiorgiLevel K n < deGiorgiLevel K (n + 1) :=
      deGiorgiLevel_strictMono hK (Nat.lt_succ_self n)
    have H1 := hrec (deGiorgiLevel K n) (deGiorgiLevel K (n + 1)) hkn0 hknlt
    -- abbreviations for the two consecutive level volumes
    set aN : ℝ := a (deGiorgiLevel K n) with haN
    set aN1 : ℝ := a (deGiorgiLevel K (n + 1)) with haN1
    have haNnn : 0 ≤ aN := hnn _
    have haN1nn : 0 ≤ aN1 := hnn _
    -- rewrite the gap square
    rw [deGiorgiLevel_succ_sub_sq] at H1
    -- (a_{n+1})^γ ≤ Crec * a_n / (K^2 * 4^{-(n+1)})
    have hgap_pos : 0 < K ^ 2 * (4 : ℝ) ^ (-((n : ℝ) + 1)) := by
      have : 0 < (4 : ℝ) ^ (-((n : ℝ) + 1)) := Real.rpow_pos_of_pos (by norm_num) _
      positivity
    have hpow_le : aN1 ^ γ ≤ Crec * aN / (K ^ 2 * (4 : ℝ) ^ (-((n : ℝ) + 1))) := by
      rw [le_div_iff₀ hgap_pos]
      calc aN1 ^ γ * (K ^ 2 * (4 : ℝ) ^ (-((n : ℝ) + 1)))
          = K ^ 2 * (4 : ℝ) ^ (-((n : ℝ) + 1)) * aN1 ^ γ := by ring
        _ ≤ Crec * aN := H1
    -- raise to power α
    have hRHSnn : 0 ≤ Crec * aN / (K ^ 2 * (4 : ℝ) ^ (-((n : ℝ) + 1))) :=
      div_nonneg (mul_nonneg hCrec haNnn) hgap_pos.le
    have hpowα : aN1 ≤ (Crec * aN / (K ^ 2 * (4 : ℝ) ^ (-((n : ℝ) + 1)))) ^ α := by
      have hmono := Real.rpow_le_rpow (Real.rpow_nonneg haN1nn γ) hpow_le hαpos.le
      rwa [← Real.rpow_mul haN1nn, hγα, Real.rpow_one] at hmono
    -- rewrite `Crec*aN/(K²·4^{-(n+1)}) = (Crec/K²)·aN·4^{n+1}`
    have hrw : Crec * aN / (K ^ 2 * (4 : ℝ) ^ (-((n : ℝ) + 1)))
        = (Crec / K ^ 2) * aN * (4 : ℝ) ^ ((n : ℝ) + 1) := by
      rw [Real.rpow_neg (by norm_num)]
      have h4pos : (0 : ℝ) < (4 : ℝ) ^ ((n : ℝ) + 1) := Real.rpow_pos_of_pos (by norm_num) _
      field_simp
    -- `4^{n+1}` raised to `α` equals `B · Bⁿ`
    have hpow4 : ((4 : ℝ) ^ ((n : ℝ) + 1)) ^ α = B * B ^ (n : ℝ) := by
      rw [hB, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 4)]
      congr 1
      ring
    -- assemble `key : aN1 ≤ (Crec/K²)^α · (B·Bⁿ) · aN^α`
    have key : aN1 ≤ (Crec / K ^ 2) ^ α * (B * B ^ (n : ℝ)) * aN ^ α := by
      refine le_trans hpowα ?_
      rw [hrw, Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by positivity) haNnn, hpow4]
      apply le_of_eq; ring
    -- convert `key` into the `Y`-recursion
    show aN1 / Ld ≤ A * B ^ (n : ℝ) * (aN / Ld) ^ (1 + β)
    have h1β : (1 : ℝ) + β = α := by rw [hβ]; ring
    rw [h1β, hA_def, Real.div_rpow haNnn hLd.le]
    have hLdα : Ld ^ α = Ld ^ β * Ld := by
      rw [hβ, Real.rpow_sub hLd, Real.rpow_one]
      field_simp
    have hLdβpos : (0 : ℝ) < Ld ^ β := Real.rpow_pos_of_pos hLd _
    have hRHSeq :
        (Crec / K ^ 2) ^ α * B * Ld ^ β * B ^ (n : ℝ) * (aN ^ α / Ld ^ α)
          = ((Crec / K ^ 2) ^ α * (B * B ^ (n : ℝ)) * aN ^ α) / Ld := by
      rw [hLdα]
      field_simp
    rw [hRHSeq]
    have := mul_le_mul_of_nonneg_right key (le_of_lt (by positivity : (0 : ℝ) < Ld⁻¹))
    simpa [div_eq_mul_inv] using this
  -- apply the geometric-decay corollary
  have hBB : 1 < B := by
    rw [hB]
    exact (Real.one_lt_rpow_iff_of_pos (by norm_num)).mpr (Or.inl ⟨by norm_num, hαpos⟩)
  have hdecay := iteration_geometric_decay_tendsto_zero hY0 hYnn hβpos hBB hA0
    (by rw [hA_def]; exact hKcond) hrecY
  -- transfer back to `a`
  have : (fun n => a (deGiorgiLevel K n)) = fun n => Ld * Y n := by
    funext n; rw [hY_def]; field_simp
  rw [this]
  have := hdecay.const_mul Ld
  simpa using this

open MeasureTheory in
/-- A finite-measure set whose real mass is dominated by a null-tending sequence
is null.  Used to convert the level-volume decay into `|{w > m + K}| = 0`. -/
theorem measure_eq_zero_of_toReal_tendsto {α : Type*} {m0 : MeasurableSpace α}
    {μ : Measure α} {T : Set α} (hT : μ T ≠ ⊤) {b : ℕ → ℝ}
    (hle : ∀ n, (μ T).toReal ≤ b n) (hb : Tendsto b atTop (𝓝 0)) : μ T = 0 := by
  have hc : (μ T).toReal ≤ 0 := ge_of_tendsto hb (Filter.Eventually.of_forall hle)
  have hnn : 0 ≤ (μ T).toReal := ENNReal.toReal_nonneg
  have hzero : (μ T).toReal = 0 := le_antisymm hc hnn
  exact (ENNReal.toReal_eq_zero_iff _).mp hzero |>.resolve_right hT

end Homogenization
