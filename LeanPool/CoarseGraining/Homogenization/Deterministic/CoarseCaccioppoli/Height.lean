/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.Basic

/-! # Height -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped BigOperators

theorem coarseCaccioppoli_sigma_pos {s t : ℝ}
    (hst : s + t < 1) :
    0 < coarseCaccioppoliSigma s t := by
  unfold coarseCaccioppoliSigma
  linarith

theorem coarseCaccioppoli_beta_nonneg {s t : ℝ}
    (hs : 0 < s) (hst : s + t < 1) :
    0 ≤ coarseCaccioppoliBeta s t := by
  have hσ : 0 < coarseCaccioppoliSigma s t :=
    coarseCaccioppoli_sigma_pos hst
  have hnum : 0 ≤ 2 * (1 - t) := by
    have ht1 : t < 1 := by linarith
    exact mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) (sub_nonneg.mpr ht1.le)
  unfold coarseCaccioppoliBeta
  exact div_nonneg hnum hσ.le

theorem coarseCaccioppoli_power_nonneg {s t : ℝ}
    (hs : 0 < s) (hst : s + t < 1) :
    0 ≤ coarseCaccioppoliPower s t := by
  have hσ : 0 < coarseCaccioppoliSigma s t :=
    coarseCaccioppoli_sigma_pos hst
  unfold coarseCaccioppoliPower
  exact div_nonneg (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) hs.le) hσ.le

theorem coarseCaccioppoli_sigma_le_one_sub_s {s t : ℝ} (ht : 0 < t) :
    coarseCaccioppoliSigma s t ≤ 1 - s := by
  unfold coarseCaccioppoliSigma
  linarith

theorem coarseCaccioppoli_sigma_div_one_sub_s_le_one {s t : ℝ}
    (ht : 0 < t) (hst : s + t < 1) :
    coarseCaccioppoliSigma s t / (1 - s) ≤ 1 := by
  have hs1_pos : 0 < 1 - s := by linarith
  rw [div_le_iff₀ hs1_pos]
  simpa using coarseCaccioppoli_sigma_le_one_sub_s (s := s) (t := t) ht

theorem coarseCaccioppoli_sigma_mul_beta {s t : ℝ}
    (hst : s + t < 1) :
    coarseCaccioppoliSigma s t * coarseCaccioppoliBeta s t =
      2 * (1 - t) := by
  have hσ : coarseCaccioppoliSigma s t ≠ 0 :=
    (coarseCaccioppoli_sigma_pos hst).ne'
  unfold coarseCaccioppoliBeta
  field_simp [hσ]

theorem coarseCaccioppoli_sigma_mul_power {s t : ℝ}
    (hst : s + t < 1) :
    coarseCaccioppoliSigma s t * coarseCaccioppoliPower s t = 2 * s := by
  have hσ : coarseCaccioppoliSigma s t ≠ 0 :=
    (coarseCaccioppoli_sigma_pos hst).ne'
  unfold coarseCaccioppoliPower
  field_simp [hσ]

theorem coarseCaccioppoli_sigma_mul_beta_le_two {s t : ℝ}
    (ht : 0 < t) (hst : s + t < 1) :
    coarseCaccioppoliSigma s t * coarseCaccioppoliBeta s t ≤ 2 := by
  rw [coarseCaccioppoli_sigma_mul_beta hst]
  calc
    2 * (1 - t) ≤ 2 * 1 :=
      mul_le_mul_of_nonneg_left (sub_le_self (1 : ℝ) ht.le) (by norm_num)
    _ = 2 := by ring

theorem coarseCaccioppoli_sigma_mul_power_le_two {s t : ℝ}
    (_hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    coarseCaccioppoliSigma s t * coarseCaccioppoliPower s t ≤ 2 := by
  rw [coarseCaccioppoli_sigma_mul_power hst]
  have hs_le_one : s ≤ 1 := by linarith
  calc
    2 * s ≤ 2 * 1 :=
      mul_le_mul_of_nonneg_left hs_le_one (by norm_num : 0 ≤ (2 : ℝ))
    _ = 2 := by ring

theorem coarseCaccioppoli_beta_eq_two_add_power {s t : ℝ}
    (hst : s + t < 1) :
    coarseCaccioppoliBeta s t = 2 + coarseCaccioppoliPower s t := by
  have hσ_pos : 0 < coarseCaccioppoliSigma s t :=
    coarseCaccioppoli_sigma_pos hst
  have hσ_ne : coarseCaccioppoliSigma s t ≠ 0 := hσ_pos.ne'
  have hsplit : 1 - t = coarseCaccioppoliSigma s t + s := by
    unfold coarseCaccioppoliSigma
    ring
  calc
    coarseCaccioppoliBeta s t
        = (2 * (coarseCaccioppoliSigma s t + s)) / coarseCaccioppoliSigma s t := by
            unfold coarseCaccioppoliBeta
            rw [hsplit]
    _ = 2 * ((coarseCaccioppoliSigma s t + s) / coarseCaccioppoliSigma s t) := by
          field_simp [hσ_ne]
    _ = 2 * (1 + s / coarseCaccioppoliSigma s t) := by
          field_simp [hσ_ne]
    _ = 2 + 2 * s / coarseCaccioppoliSigma s t := by
          ring
    _ = 2 + coarseCaccioppoliPower s t := by
          unfold coarseCaccioppoliPower
          rfl

theorem coarseCaccioppoli_beta_ge_two {s t : ℝ}
    (hs : 0 < s) (hst : s + t < 1) :
    2 ≤ coarseCaccioppoliBeta s t := by
  rw [coarseCaccioppoli_beta_eq_two_add_power hst]
  linarith [coarseCaccioppoli_power_nonneg hs hst]

theorem coarseCaccioppoli_natCeil_beta_le_two_mul_beta {s t : ℝ}
    (hs : 0 < s) (hst : s + t < 1) :
    (Nat.ceil (coarseCaccioppoliBeta s t) : ℝ) ≤
      2 * coarseCaccioppoliBeta s t := by
  have hβ_nonneg : 0 ≤ coarseCaccioppoliBeta s t := by
    linarith [coarseCaccioppoli_beta_ge_two hs hst]
  have hceil_lt :
      (Nat.ceil (coarseCaccioppoliBeta s t) : ℝ) <
        coarseCaccioppoliBeta s t + 1 :=
    Nat.ceil_lt_add_one hβ_nonneg
  linarith [coarseCaccioppoli_beta_ge_two hs hst]

theorem coarseCaccioppoli_sigma_mul_natCeil_beta_le_four {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    coarseCaccioppoliSigma s t *
        (Nat.ceil (coarseCaccioppoliBeta s t) : ℝ) ≤ 4 := by
  have hσ_pos : 0 < coarseCaccioppoliSigma s t :=
    coarseCaccioppoli_sigma_pos hst
  calc
    coarseCaccioppoliSigma s t *
        (Nat.ceil (coarseCaccioppoliBeta s t) : ℝ)
        ≤ coarseCaccioppoliSigma s t *
            (2 * coarseCaccioppoliBeta s t) := by
          exact mul_le_mul_of_nonneg_left
            (coarseCaccioppoli_natCeil_beta_le_two_mul_beta hs hst)
            hσ_pos.le
    _ = 2 * (coarseCaccioppoliSigma s t *
            coarseCaccioppoliBeta s t) := by ring
    _ ≤ 4 := by
          nlinarith [coarseCaccioppoli_sigma_mul_beta_le_two ht hst]

theorem coarseCaccioppoli_power_ge_two_mul_s {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    2 * s ≤ coarseCaccioppoliPower s t := by
  have hσ_pos : 0 < coarseCaccioppoliSigma s t :=
    coarseCaccioppoli_sigma_pos hst
  have hσ_le_one : coarseCaccioppoliSigma s t ≤ 1 := by
    unfold coarseCaccioppoliSigma
    linarith
  unfold coarseCaccioppoliPower
  have hmul : 2 * s * coarseCaccioppoliSigma s t ≤ 2 * s := by
    nlinarith
  exact (le_div_iff₀ hσ_pos).2 hmul

theorem coarseCaccioppoli_beta_ge_two_add_two_mul_s {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    2 + 2 * s ≤ coarseCaccioppoliBeta s t := by
  rw [coarseCaccioppoli_beta_eq_two_add_power hst]
  linarith [coarseCaccioppoli_power_ge_two_mul_s hs ht hst]

theorem coarseCaccioppoli_noteExponent_eq_two_mul_beta_sub_two {s t : ℝ}
    (hst : s + t < 1) :
    2 + 4 * s / coarseCaccioppoliSigma s t =
      2 * coarseCaccioppoliBeta s t - 2 := by
  rw [coarseCaccioppoli_beta_eq_two_add_power hst]
  unfold coarseCaccioppoliPower
  ring

theorem coarseCaccioppoli_noteExponent_pos {s t : ℝ}
    (hs : 0 < s) (hst : s + t < 1) :
    0 < 2 + 4 * s / coarseCaccioppoliSigma s t := by
  have hσ_pos : 0 < coarseCaccioppoliSigma s t :=
    coarseCaccioppoli_sigma_pos hst
  have hdiv_nonneg : 0 ≤ 4 * s / coarseCaccioppoliSigma s t := by
    positivity
  linarith

theorem coarseCaccioppoli_noteExponent_ge_one {s t : ℝ}
    (hs : 0 < s) (hst : s + t < 1) :
    1 ≤ 2 + 4 * s / coarseCaccioppoliSigma s t := by
  have hσ_pos : 0 < coarseCaccioppoliSigma s t :=
    coarseCaccioppoli_sigma_pos hst
  have hdiv_nonneg : 0 ≤ 4 * s / coarseCaccioppoliSigma s t := by
    positivity
  linarith

theorem coarseCaccioppoli_beta_le_noteExponent {s t : ℝ}
    (hs : 0 < s) (hst : s + t < 1) :
    coarseCaccioppoliBeta s t ≤
      2 + 4 * s / coarseCaccioppoliSigma s t := by
  rw [coarseCaccioppoli_noteExponent_eq_two_mul_beta_sub_two hst]
  linarith [coarseCaccioppoli_beta_ge_two hs hst]

theorem coarseCaccioppoli_power_le_noteExponent {s t : ℝ}
    (hs : 0 < s) (hst : s + t < 1) :
    coarseCaccioppoliPower s t ≤
      2 + 4 * s / coarseCaccioppoliSigma s t := by
  have hq_nonneg := coarseCaccioppoli_power_nonneg hs hst
  have hp_eq :
      2 + 4 * s / coarseCaccioppoliSigma s t =
        2 + 2 * coarseCaccioppoliPower s t := by
    unfold coarseCaccioppoliPower
    ring
  rw [hp_eq]
  linarith

theorem coarseCaccioppoli_power_div_noteExponent_le_one {s t : ℝ}
    (hs : 0 < s) (hst : s + t < 1) :
    coarseCaccioppoliPower s t /
        (2 + 4 * s / coarseCaccioppoliSigma s t) ≤ 1 := by
  have hp_pos := coarseCaccioppoli_noteExponent_pos hs hst
  rw [div_le_iff₀ hp_pos]
  simpa using coarseCaccioppoli_power_le_noteExponent hs hst

/-- The note exponent dominates the integerized radius exponent, up to the
fixed four-unit loss from taking a ceiling. -/
theorem coarseCaccioppoli_two_natCeil_beta_sub_four_le_noteExponent {s t : ℝ}
    (hs : 0 < s) (hst : s + t < 1) :
    2 * (Nat.ceil (coarseCaccioppoliBeta s t) : ℝ) - 4 ≤
      2 + 4 * s / coarseCaccioppoliSigma s t := by
  have hβ_nonneg : 0 ≤ coarseCaccioppoliBeta s t := by
    linarith [coarseCaccioppoli_beta_ge_two hs hst]
  have hceil_lt :
      (Nat.ceil (coarseCaccioppoliBeta s t) : ℝ) <
        coarseCaccioppoliBeta s t + 1 :=
    Nat.ceil_lt_add_one hβ_nonneg
  rw [coarseCaccioppoli_noteExponent_eq_two_mul_beta_sub_two hst]
  linarith

theorem coarseCaccioppoli_natCeil_beta_le_noteExponent_of_four_le {s t : ℝ}
    (hs : 0 < s) (hst : s + t < 1)
    (hk : 4 ≤ Nat.ceil (coarseCaccioppoliBeta s t)) :
    (Nat.ceil (coarseCaccioppoliBeta s t) : ℝ) ≤
      2 + 4 * s / coarseCaccioppoliSigma s t := by
  have hk_real :
      (Nat.ceil (coarseCaccioppoliBeta s t) : ℝ) ≤
        2 * (Nat.ceil (coarseCaccioppoliBeta s t) : ℝ) - 4 := by
    have hk_real4 :
        (4 : ℝ) ≤ (Nat.ceil (coarseCaccioppoliBeta s t) : ℝ) := by
      exact_mod_cast hk
    linarith
  exact hk_real.trans
    (coarseCaccioppoli_two_natCeil_beta_sub_four_le_noteExponent hs hst)

theorem coarseCaccioppoli_sigma_mul_noteExponent_le_four {s t : ℝ}
    (_hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    coarseCaccioppoliSigma s t *
        (2 + 4 * s / coarseCaccioppoliSigma s t) ≤ 4 := by
  have hσ_pos : 0 < coarseCaccioppoliSigma s t :=
    coarseCaccioppoli_sigma_pos hst
  rw [coarseCaccioppoli_noteExponent_eq_two_mul_beta_sub_two hst]
  calc
    coarseCaccioppoliSigma s t *
        (2 * coarseCaccioppoliBeta s t - 2)
        = 2 * (coarseCaccioppoliSigma s t *
            coarseCaccioppoliBeta s t) -
          2 * coarseCaccioppoliSigma s t := by ring
    _ ≤ 2 * (coarseCaccioppoliSigma s t *
            coarseCaccioppoliBeta s t) := by
          exact sub_le_self _
            (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) hσ_pos.le)
    _ ≤ 4 := by
          calc
            2 * (coarseCaccioppoliSigma s t * coarseCaccioppoliBeta s t) ≤
                2 * 2 :=
              mul_le_mul_of_nonneg_left
                (coarseCaccioppoli_sigma_mul_beta_le_two ht hst)
                (by norm_num : 0 ≤ (2 : ℝ))
            _ = 4 := by ring

/-- Entropy-type scalar bound used in the Caccioppoli constant extraction.
For `0 < r ≤ 1`, the factor `r^{-r}` is uniformly bounded by `exp 1`.  This is the
one-variable cancellation behind the small-`s` branch of the note constant. -/
theorem rpow_neg_self_le_exp_one {r : ℝ} (hr : 0 < r) (_hr_le : r ≤ 1) :
    Real.rpow r (-r) ≤ Real.exp 1 := by
  have hinv_pos : 0 < r⁻¹ := inv_pos.mpr hr
  have hlog_inv_le : Real.log r⁻¹ ≤ r⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos hinv_pos
  have hlog_inv_eq : Real.log r⁻¹ = -Real.log r := Real.log_inv r
  have hmul :
      r * Real.log r⁻¹ ≤ r * (r⁻¹ - 1) :=
    mul_le_mul_of_nonneg_left hlog_inv_le hr.le
  have hentropy : -r * Real.log r ≤ 1 := by
    calc
      -r * Real.log r = r * Real.log r⁻¹ := by
        rw [hlog_inv_eq]
        ring
      _ ≤ r * (r⁻¹ - 1) := hmul
      _ = 1 - r := by
        field_simp [hr.ne']
      _ ≤ 1 := by linarith
  have hrpow_eq : Real.rpow r (-r) = Real.exp (-r * Real.log r) := by
    calc
      Real.rpow r (-r) = Real.exp (Real.log r * (-r)) :=
        Real.rpow_def_of_pos hr (-r)
      _ = Real.exp (-r * Real.log r) := by ring_nf
  calc
    Real.rpow r (-r) = Real.exp (-r * Real.log r) := hrpow_eq
    _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hentropy

/-- A two-fold version of `rpow_neg_self_le_exp_one`. -/
theorem rpow_neg_two_mul_self_le_exp_two {r : ℝ} (hr : 0 < r) (_hr_le : r ≤ 1) :
    Real.rpow r (-(2 * r)) ≤ Real.exp 2 := by
  have hinv_pos : 0 < r⁻¹ := inv_pos.mpr hr
  have hlog_inv_le : Real.log r⁻¹ ≤ r⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos hinv_pos
  have hlog_inv_eq : Real.log r⁻¹ = -Real.log r := Real.log_inv r
  have hmul :
      r * Real.log r⁻¹ ≤ r * (r⁻¹ - 1) :=
    mul_le_mul_of_nonneg_left hlog_inv_le hr.le
  have hentropy : -r * Real.log r ≤ 1 := by
    calc
      -r * Real.log r = r * Real.log r⁻¹ := by
        rw [hlog_inv_eq]
        ring
      _ ≤ r * (r⁻¹ - 1) := hmul
      _ = 1 - r := by
        field_simp [hr.ne']
      _ ≤ 1 := by linarith
  have htwo_entropy : -(2 * r) * Real.log r ≤ 2 := by
    have hscale : (2 : ℝ) * (-r * Real.log r) ≤ 2 * 1 :=
      mul_le_mul_of_nonneg_left hentropy (by norm_num)
    linarith
  have hrpow_eq : Real.rpow r (-(2 * r)) =
      Real.exp (-(2 * r) * Real.log r) := by
    calc
      Real.rpow r (-(2 * r)) = Real.exp (Real.log r * (-(2 * r))) :=
        Real.rpow_def_of_pos hr (-(2 * r))
      _ = Real.exp (-(2 * r) * Real.log r) := by ring_nf
  calc
    Real.rpow r (-(2 * r)) = Real.exp (-(2 * r) * Real.log r) := hrpow_eq
    _ ≤ Real.exp 2 := Real.exp_le_exp.mpr htwo_entropy

/-- The singular scalar factors left after taking the note-exponent root are
uniformly bounded.  This is the explicit `s,t` cancellation in the Caccioppoli
constant extraction. -/
theorem coarseCaccioppoli_sigma_mul_singularRoot_le_exp_two {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    let σ : ℝ := coarseCaccioppoliSigma s t
    let q : ℝ := coarseCaccioppoliPower s t
    let p : ℝ := 2 + 4 * s / σ
    σ * Real.rpow s (-(q / p)) * Real.rpow (1 - s) (-(q / p)) ≤
      Real.exp 2 := by
  let σ : ℝ := coarseCaccioppoliSigma s t
  let q : ℝ := coarseCaccioppoliPower s t
  let p : ℝ := 2 + 4 * s / σ
  let e : ℝ := q / p
  have hσ_pos : 0 < σ := by
    dsimp [σ]
    exact coarseCaccioppoli_sigma_pos hst
  have hs1_pos : 0 < 1 - s := by linarith
  have hσ_le_one_sub_s : σ ≤ 1 - s := by
    dsimp [σ]
    unfold coarseCaccioppoliSigma
    linarith
  have hσ_le_one : σ ≤ 1 := by
    dsimp [σ]
    unfold coarseCaccioppoliSigma
    linarith
  have hp_pos : 0 < p := by
    dsimp [p]
    exact coarseCaccioppoli_noteExponent_pos hs hst
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact coarseCaccioppoli_power_nonneg hs hst
  have he_nonneg : 0 ≤ e := by
    dsimp [e]
    exact div_nonneg hq_nonneg hp_pos.le
  have hp_eq : p = 2 + 2 * q := by
    dsimp [p, q, coarseCaccioppoliPower]
    ring
  have he_le_half : e ≤ (1 / 2 : ℝ) := by
    dsimp [e]
    rw [div_le_iff₀ hp_pos]
    rw [hp_eq]
    ring_nf
    linarith
  have hone_sub_two_e_nonneg : 0 ≤ 1 - 2 * e := by
    linarith
  have hF_pos :
      0 <
        σ * Real.rpow s (-e) * Real.rpow (1 - s) (-e) := by
    exact mul_pos (mul_pos hσ_pos (Real.rpow_pos_of_pos hs (-e)))
      (Real.rpow_pos_of_pos hs1_pos (-e))
  have hlogF :
      Real.log (σ * Real.rpow s (-e) * Real.rpow (1 - s) (-e)) =
        Real.log σ - e * Real.log s - e * Real.log (1 - s) := by
    have hs_rpow_pos : 0 < Real.rpow s (-e) := Real.rpow_pos_of_pos hs (-e)
    have hs1_rpow_pos :
        0 < Real.rpow (1 - s) (-e) := Real.rpow_pos_of_pos hs1_pos (-e)
    calc
      Real.log (σ * Real.rpow s (-e) * Real.rpow (1 - s) (-e))
          = Real.log (σ * Real.rpow s (-e)) +
              Real.log (Real.rpow (1 - s) (-e)) := by
            rw [Real.log_mul (mul_ne_zero hσ_pos.ne' hs_rpow_pos.ne')
              hs1_rpow_pos.ne']
      _ = (Real.log σ + Real.log (Real.rpow s (-e))) +
              Real.log (Real.rpow (1 - s) (-e)) := by
            rw [Real.log_mul hσ_pos.ne' hs_rpow_pos.ne']
      _ = (Real.log σ + (-e) * Real.log s) +
              (-e) * Real.log (1 - s) := by
            rw [show Real.log (Real.rpow s (-e)) = (-e) * Real.log s by
                simpa using Real.log_rpow hs (-e),
              show Real.log (Real.rpow (1 - s) (-e)) =
                  (-e) * Real.log (1 - s) by
                simpa using Real.log_rpow hs1_pos (-e)]
      _ = Real.log σ - e * Real.log s - e * Real.log (1 - s) := by ring
  have hlog_le_two :
      Real.log (σ * Real.rpow s (-e) * Real.rpow (1 - s) (-e)) ≤ 2 := by
    by_cases hσ_le_s : σ ≤ s
    · have hlog_s_ge : Real.log σ ≤ Real.log s :=
        Real.log_le_log hσ_pos hσ_le_s
      have hlog_one_sub_ge : Real.log σ ≤ Real.log (1 - s) :=
        Real.log_le_log hσ_pos hσ_le_one_sub_s
      have hneg_s :
          -e * Real.log s ≤ -e * Real.log σ := by
        exact mul_le_mul_of_nonpos_left hlog_s_ge (by linarith)
      have hneg_one_sub :
          -e * Real.log (1 - s) ≤ -e * Real.log σ := by
        exact mul_le_mul_of_nonpos_left hlog_one_sub_ge (by linarith)
      have hσ_log_nonpos : Real.log σ ≤ 0 :=
        Real.log_nonpos hσ_pos.le hσ_le_one
      have hmain :
          Real.log σ - e * Real.log s - e * Real.log (1 - s) ≤
            (1 - 2 * e) * Real.log σ := by
        linarith
      have hright_nonpos : (1 - 2 * e) * Real.log σ ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hone_sub_two_e_nonneg hσ_log_nonpos
      rw [hlogF]
      linarith
    · have hs_le_σ : s ≤ σ := le_of_not_ge hσ_le_s
      have hs_le_one_sub : s ≤ 1 - s := hs_le_σ.trans hσ_le_one_sub_s
      let r : ℝ := s / σ
      have hr_pos : 0 < r := by
        dsimp [r]
        positivity
      have hr_le_one : r ≤ 1 := by
        dsimp [r]
        exact (div_le_one hσ_pos).2 hs_le_σ
      have he_le_r : e ≤ r := by
        have hq_eq : q = 2 * r := by
          dsimp [q, r, coarseCaccioppoliPower]
          ring
        have hp_ge_two : (2 : ℝ) ≤ p := by
          rw [hp_eq]
          exact le_add_of_nonneg_right
            (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) hq_nonneg)
        dsimp [e]
        calc
          q / p ≤ q / 2 :=
            div_le_div_of_nonneg_left hq_nonneg (by norm_num : 0 < (2 : ℝ))
              hp_ge_two
          _ = r := by
            rw [hq_eq]
            ring
      have hlog_s_le : Real.log s ≤ Real.log (1 - s) :=
        Real.log_le_log hs hs_le_one_sub
      have hneg_one_sub :
          -e * Real.log (1 - s) ≤ -e * Real.log s := by
        exact mul_le_mul_of_nonpos_left hlog_s_le (by linarith)
      have hlog_r : Real.log r = Real.log s - Real.log σ := by
        dsimp [r]
        rw [Real.log_div hs.ne' hσ_pos.ne']
      have hσ_log_nonpos : Real.log σ ≤ 0 :=
        Real.log_nonpos hσ_pos.le hσ_le_one
      have hfirst :
          Real.log σ - e * Real.log s - e * Real.log (1 - s) ≤
            Real.log σ - 2 * e * Real.log s := by
        linarith
      have hsplit :
          Real.log σ - 2 * e * Real.log s =
            (1 - 2 * e) * Real.log σ - 2 * e * Real.log r := by
        rw [hlog_r]
        ring
      have hdrop :
          (1 - 2 * e) * Real.log σ - 2 * e * Real.log r ≤
            -2 * e * Real.log r := by
        have hterm_nonpos : (1 - 2 * e) * Real.log σ ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hone_sub_two_e_nonneg hσ_log_nonpos
        linarith
      have hlog_r_nonpos : Real.log r ≤ 0 :=
        Real.log_nonpos hr_pos.le hr_le_one
      have hentropy :
          -2 * e * Real.log r ≤ -2 * r * Real.log r := by
        have hmul : e * Real.log r ≥ r * Real.log r := by
          exact mul_le_mul_of_nonpos_right he_le_r hlog_r_nonpos
        linarith
      have hrpow_bound :
          -2 * r * Real.log r ≤ 2 := by
        have h := rpow_neg_two_mul_self_le_exp_two hr_pos hr_le_one
        have hlog_bound :
            Real.log (Real.rpow r (-(2 * r))) ≤ 2 :=
          (Real.log_le_iff_le_exp (Real.rpow_pos_of_pos hr_pos (-(2 * r)))).2 h
        have hlog_rpow :
            Real.log (Real.rpow r (-(2 * r))) =
              -(2 * r) * Real.log r := by
          simpa using Real.log_rpow hr_pos (-(2 * r))
        calc
          -2 * r * Real.log r = -(2 * r) * Real.log r := by ring
          _ = Real.log (Real.rpow r (-(2 * r))) := hlog_rpow.symm
          _ ≤ 2 := hlog_bound
      rw [hlogF]
      calc
        Real.log σ - e * Real.log s - e * Real.log (1 - s) ≤
            Real.log σ - 2 * e * Real.log s := hfirst
        _ = (1 - 2 * e) * Real.log σ - 2 * e * Real.log r := hsplit
        _ ≤ -2 * e * Real.log r := hdrop
        _ ≤ -2 * r * Real.log r := hentropy
        _ ≤ 2 := hrpow_bound
  exact (Real.log_le_iff_le_exp hF_pos).1 hlog_le_two

theorem coarseCaccioppoliBoundaryExplicitHeightAtScale_ge_k_add_four
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C : ℝ) (k : ℕ) :
    (k : ℝ) + 4 ≤ coarseCaccioppoliBoundaryExplicitHeightAtScale Q a s t C k := by
  unfold coarseCaccioppoliBoundaryExplicitHeightAtScale
  exact le_max_left _ _

theorem coarseCaccioppoliBoundaryExplicitHeightAtScale_le_localizedExplicitHeightAtScale
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C : ℝ) (k : ℕ) :
    coarseCaccioppoliBoundaryExplicitHeightAtScale Q a s t C k ≤
      coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale Q a s t C k := by
  unfold coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale
  exact le_max_left _ _

theorem coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale_ge_k_add_four
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C : ℝ) (k : ℕ) :
    (k : ℝ) + 4 ≤
      coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale Q a s t C k := by
  exact le_trans
    (coarseCaccioppoliBoundaryExplicitHeightAtScale_ge_k_add_four Q a s t C k)
    (coarseCaccioppoliBoundaryExplicitHeightAtScale_le_localizedExplicitHeightAtScale
      Q a s t C k)

theorem coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale_ge_four_div_s
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C : ℝ) (k : ℕ) :
    (4 : ℝ) / s ≤
      coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale Q a s t C k := by
  unfold coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale
  exact le_max_right _ _

theorem coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale_ge_four_div_s_add_t
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) {s t C : ℝ} (k : ℕ)
    (hs : 0 < s) (ht : 0 < t) :
    (4 : ℝ) / (s + t) ≤
      coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale Q a s t C k := by
  have hst : s < s + t := by linarith
  have hpos : 0 < s + t := by linarith
  have hdiv : (4 : ℝ) / (s + t) ≤ 4 / s := by
    exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (4 : ℝ)) hs hst.le
  exact le_trans hdiv
    (coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale_ge_four_div_s Q a s t C k)

/-- Natural depth obtained by integerizing the localized explicit height.  This
is the depth used by the small-cube Caccioppoli route. -/
noncomputable def coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthAtScale {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C : ℝ) (k : ℕ) : ℕ :=
  Nat.ceil (coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale Q a s t C k)

/-- Radius-indexed integerized localized height depth. -/
noncomputable def coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthOfScaleChoice {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s t C : ℝ)
    (k : ℝ → ℝ → ℕ) : ℝ → ℝ → ℕ :=
  fun ρ₁ ρ₂ =>
    coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthAtScale Q a s t C (k ρ₁ ρ₂)

/-- Real-valued height associated to the integerized localized depth. -/
noncomputable def coarseCaccioppoliBoundaryIntegerizedLocalizedExplicitHeightOfScaleChoice
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C : ℝ)
    (k : ℝ → ℝ → ℕ) : ℝ → ℝ → ℝ :=
  fun ρ₁ ρ₂ =>
    (coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthOfScaleChoice Q a s t C k
      ρ₁ ρ₂ : ℝ)

/-- The integerized localized depth dominates the localized real height. -/
theorem coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale_le_depth
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C : ℝ) (k : ℕ) :
    coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale Q a s t C k ≤
      (coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthAtScale Q a s t C k : ℝ) := by
  exact Nat.le_ceil _

/-- The integerized localized height keeps the `k + 4` lower bound. -/
theorem coarseCaccioppoliBoundaryIntegerizedLocalizedExplicitHeightAtScale_ge_k_add_four
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C : ℝ) (k : ℕ) :
    (k : ℝ) + 4 ≤
      (coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthAtScale Q a s t C k : ℝ) := by
  exact le_trans
    (coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale_ge_k_add_four Q a s t C k)
    (coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale_le_depth Q a s t C k)

/-- The integerized localized depth is at least the triadic gap scale. -/
theorem coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthAtScale_ge_scale
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C : ℝ) (k : ℕ) :
    k ≤ coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthAtScale Q a s t C k := by
  have hreal :
      (k : ℝ) ≤
        (coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthAtScale Q a s t C k : ℝ) := by
    have hfour :=
      coarseCaccioppoliBoundaryIntegerizedLocalizedExplicitHeightAtScale_ge_k_add_four
        Q a s t C k
    nlinarith
  exact_mod_cast hreal

/-- Radius-indexed version of
`coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthAtScale_ge_scale`. -/
theorem coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthOfScaleChoice_ge_scaleChoice
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C : ℝ)
    (k : ℝ → ℝ → ℕ) (ρ₁ ρ₂ : ℝ) :
    k ρ₁ ρ₂ ≤
      coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthOfScaleChoice Q a s t C k
        ρ₁ ρ₂ := by
  simpa [coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthOfScaleChoice] using
    coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthAtScale_ge_scale
      Q a s t C (k ρ₁ ρ₂)

/-- The integerized localized height keeps the `4 / s` lower bound. -/
theorem coarseCaccioppoliBoundaryIntegerizedLocalizedExplicitHeightAtScale_ge_four_div_s
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C : ℝ) (k : ℕ) :
    (4 : ℝ) / s ≤
      (coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthAtScale Q a s t C k : ℝ) := by
  exact le_trans
    (coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale_ge_four_div_s Q a s t C k)
    (coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale_le_depth Q a s t C k)

/-- The integerized localized height keeps the `4 / (s + t)` lower bound. -/
theorem coarseCaccioppoliBoundaryIntegerizedLocalizedExplicitHeightAtScale_ge_four_div_s_add_t
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) {s t C : ℝ} (k : ℕ)
    (hs : 0 < s) (ht : 0 < t) :
    (4 : ℝ) / (s + t) ≤
      (coarseCaccioppoliBoundaryLocalizedExplicitHeightDepthAtScale Q a s t C k : ℝ) := by
  exact le_trans
    (coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale_ge_four_div_s_add_t
      Q a k hs ht)
    (coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale_le_depth Q a s t C k)

theorem coarseCaccioppoliBoundaryExplicitHeightAtScale_logBound
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C : ℝ) (k : ℕ)
    (hst : s + t < 1) :
    Real.log (coarseCaccioppoliBoundaryHeightLogArg Q a s t C k) ≤
      coarseCaccioppoliSigma s t *
        coarseCaccioppoliBoundaryExplicitHeightAtScale Q a s t C k *
        Real.log (3 : ℝ) := by
  have hσ_pos : 0 < coarseCaccioppoliSigma s t := coarseCaccioppoli_sigma_pos hst
  have hlog3_pos : 0 < Real.log (3 : ℝ) := by
    exact Real.log_pos (by norm_num)
  have hden_pos : 0 < coarseCaccioppoliSigma s t * Real.log (3 : ℝ) :=
    mul_pos hσ_pos hlog3_pos
  have hceil_le :
      Real.log (coarseCaccioppoliBoundaryHeightLogArg Q a s t C k) /
          (coarseCaccioppoliSigma s t * Real.log (3 : ℝ)) ≤
        coarseCaccioppoliBoundaryExplicitHeightAtScale Q a s t C k := by
    calc
      Real.log (coarseCaccioppoliBoundaryHeightLogArg Q a s t C k) /
          (coarseCaccioppoliSigma s t * Real.log (3 : ℝ))
          ≤
            ((Nat.ceil
              (Real.log (coarseCaccioppoliBoundaryHeightLogArg Q a s t C k) /
                (coarseCaccioppoliSigma s t * Real.log (3 : ℝ))) : ℕ) : ℝ) := by
              exact Nat.le_ceil _
      _ ≤ coarseCaccioppoliBoundaryExplicitHeightAtScale Q a s t C k := by
            unfold coarseCaccioppoliBoundaryExplicitHeightAtScale
            exact le_max_right _ _
  have hscaled :=
    mul_le_mul_of_nonneg_right hceil_le hden_pos.le
  have hden_ne : coarseCaccioppoliSigma s t * Real.log (3 : ℝ) ≠ 0 := hden_pos.ne'
  calc
    Real.log (coarseCaccioppoliBoundaryHeightLogArg Q a s t C k)
        = (Real.log (coarseCaccioppoliBoundaryHeightLogArg Q a s t C k) /
            (coarseCaccioppoliSigma s t * Real.log (3 : ℝ))) *
            (coarseCaccioppoliSigma s t * Real.log (3 : ℝ)) := by
              field_simp [hden_ne]
    _ ≤ coarseCaccioppoliBoundaryExplicitHeightAtScale Q a s t C k *
          (coarseCaccioppoliSigma s t * Real.log (3 : ℝ)) := hscaled
    _ = coarseCaccioppoliSigma s t *
          coarseCaccioppoliBoundaryExplicitHeightAtScale Q a s t C k *
          Real.log (3 : ℝ) := by ring

private theorem coarseCaccioppoli_le_rpow_three_of_logBound {A h σ : ℝ}
    (hA_nonneg : 0 ≤ A)
    (hlog : Real.log A ≤ σ * h * Real.log (3 : ℝ)) :
    A ≤ Real.rpow (3 : ℝ) (σ * h) := by
  by_cases hA_zero : A = 0
  · simpa [hA_zero] using
      (Real.rpow_nonneg (show 0 ≤ (3 : ℝ) by norm_num) (σ * h))
  · have hA_pos : 0 < A := lt_of_le_of_ne hA_nonneg (by simpa [eq_comm] using hA_zero)
    have hexp : Real.exp (Real.log A) ≤ Real.exp (σ * h * Real.log (3 : ℝ)) :=
      (Real.exp_le_exp).2 hlog
    rw [Real.exp_log hA_pos] at hexp
    calc
      A ≤ Real.exp (σ * h * Real.log (3 : ℝ)) := hexp
      _ = Real.rpow (3 : ℝ) (σ * h) := by
            rw [show σ * h * Real.log (3 : ℝ) = Real.log (3 : ℝ) * (σ * h) by ring]
            rw [Real.exp_mul, Real.exp_log (by norm_num : 0 < (3 : ℝ))]
            rw [Real.rpow_eq_pow]

theorem coarseCaccioppoliBoundaryExplicitHeightAtScale_absorption
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C : ℝ) (k : ℕ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    C / (s * (1 - s)) * (3 : ℝ) ^ k *
        Real.rpow (3 : ℝ)
          (-coarseCaccioppoliSigma s t *
            coarseCaccioppoliBoundaryExplicitHeightAtScale Q a s t C k) *
        Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ) ≤ (1 / 4 : ℝ) := by
  let h0 : ℝ := coarseCaccioppoliBoundaryExplicitHeightAtScale Q a s t C k
  let M : ℝ :=
    C / (s * (1 - s)) * (3 : ℝ) ^ k *
      Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ)
  let A : ℝ := coarseCaccioppoliBoundaryHeightLogArg Q a s t C k
  have hs1 : s < 1 := by
    linarith
  have hden_nonneg : 0 ≤ s * (1 - s) := mul_one_sub_nonneg hs.le hs1.le
  have htheta_nonneg : 0 ≤ ThetaRatio Q s t a :=
    thetaRatio_nonneg Q s t a hs.le ht.le
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    refine mul_nonneg ?_ (Real.rpow_nonneg htheta_nonneg _)
    refine mul_nonneg ?_ (pow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
    exact div_nonneg hC hden_nonneg
  have hA_eq : A = 4 * M := by
    rfl
  have hA_nonneg : 0 ≤ A := by
    rw [hA_eq]
    nlinarith
  have hA_le :
      A ≤ Real.rpow (3 : ℝ) (coarseCaccioppoliSigma s t * h0) := by
    apply coarseCaccioppoli_le_rpow_three_of_logBound
    · exact hA_nonneg
    · simpa [A, h0] using
        coarseCaccioppoliBoundaryExplicitHeightAtScale_logBound Q a s t C k hst
  have hM_eq : M = (1 / 4 : ℝ) * A := by
    rw [hA_eq]
    ring
  have hM_le :
      M ≤ (1 / 4 : ℝ) * Real.rpow (3 : ℝ) (coarseCaccioppoliSigma s t * h0) := by
    rw [hM_eq]
    exact mul_le_mul_of_nonneg_left hA_le (by norm_num : 0 ≤ (1 / 4 : ℝ))
  have hpow_nonneg :
      0 ≤ Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * h0) := by
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hcancel :
      Real.rpow (3 : ℝ) (coarseCaccioppoliSigma s t * h0) *
          Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * h0) = 1 := by
    calc
      Real.rpow (3 : ℝ) (coarseCaccioppoliSigma s t * h0) *
          Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * h0) =
          Real.rpow (3 : ℝ)
            (coarseCaccioppoliSigma s t * h0 + -coarseCaccioppoliSigma s t * h0) := by
              symm
              exact Real.rpow_add (by norm_num : 0 < (3 : ℝ)) _ _
      _ = Real.rpow (3 : ℝ) 0 := by
            congr 1
            ring
      _ = 1 := by simp
  calc
    C / (s * (1 - s)) * (3 : ℝ) ^ k *
        Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * h0) *
        Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ)
        = M * Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * h0) := by
            dsimp [M]
            ring
    _ ≤
        ((1 / 4 : ℝ) * Real.rpow (3 : ℝ) (coarseCaccioppoliSigma s t * h0)) *
          Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * h0) := by
            exact mul_le_mul_of_nonneg_right hM_le hpow_nonneg
    _ = (1 / 4 : ℝ) *
        (Real.rpow (3 : ℝ) (coarseCaccioppoliSigma s t * h0) *
          Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * h0)) := by
            ring
    _ = (1 / 4 : ℝ) := by rw [hcancel]; ring

theorem coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale_absorption
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C : ℝ) (k : ℕ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    C / (s * (1 - s)) * (3 : ℝ) ^ k *
        Real.rpow (3 : ℝ)
          (-coarseCaccioppoliSigma s t *
            coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale Q a s t C k) *
        Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ) ≤ (1 / 4 : ℝ) := by
  let hOld : ℝ := coarseCaccioppoliBoundaryExplicitHeightAtScale Q a s t C k
  let hNew : ℝ := coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale Q a s t C k
  let M : ℝ :=
    C / (s * (1 - s)) * (3 : ℝ) ^ k *
      Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ)
  have hs1 : s < 1 := by
    linarith
  have hσ_pos : 0 < coarseCaccioppoliSigma s t :=
    coarseCaccioppoli_sigma_pos hst
  have hOld_le_new : hOld ≤ hNew := by
    dsimp [hOld, hNew]
    exact coarseCaccioppoliBoundaryExplicitHeightAtScale_le_localizedExplicitHeightAtScale
      Q a s t C k
  have hpow_exp :
      -coarseCaccioppoliSigma s t * hNew ≤
        -coarseCaccioppoliSigma s t * hOld := by
    exact mul_le_mul_of_nonpos_left hOld_le_new (neg_nonpos.mpr hσ_pos.le)
  have hpow_le :
      Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * hNew) ≤
        Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * hOld) := by
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (3 : ℝ)) hpow_exp
  have hden_nonneg : 0 ≤ s * (1 - s) := mul_one_sub_nonneg hs.le (by linarith)
  have htheta_nonneg : 0 ≤ ThetaRatio Q s t a :=
    thetaRatio_nonneg Q s t a hs.le ht.le
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg
      (mul_nonneg (div_nonneg hC hden_nonneg) (pow_nonneg (by norm_num) k))
      (Real.rpow_nonneg htheta_nonneg _)
  calc
    C / (s * (1 - s)) * (3 : ℝ) ^ k *
        Real.rpow (3 : ℝ)
          (-coarseCaccioppoliSigma s t *
            coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale Q a s t C k) *
        Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ)
        = M * Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * hNew) := by
            dsimp [M, hNew]
            ring
    _ ≤ M * Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * hOld) := by
          exact mul_le_mul_of_nonneg_left hpow_le hM_nonneg
    _ =
        C / (s * (1 - s)) * (3 : ℝ) ^ k *
          Real.rpow (3 : ℝ) (-coarseCaccioppoliSigma s t * hOld) *
          Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ) := by
            dsimp [M]
            ring
    _ ≤ (1 / 4 : ℝ) := by
          simpa [hOld] using
            coarseCaccioppoliBoundaryExplicitHeightAtScale_absorption
              Q a s t C k hC hs ht hst

theorem coarseCaccioppoli_boundary_heightChoice_of_explicitHeightOfScaleChoice
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C : ℝ)
    (k : ℝ → ℝ → ℕ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂) :
    CoarseCaccioppoliBoundaryHeightChoice Q a s t C
      (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k) := by
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  refine ⟨k ρ₁ ρ₂, hscale hρ₁ hlt hρ₂, ?_, ?_⟩
  · simpa [coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice] using
      coarseCaccioppoliBoundaryExplicitHeightAtScale_ge_k_add_four
        Q a s t C (k ρ₁ ρ₂)
  · simpa [coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice] using
      coarseCaccioppoliBoundaryExplicitHeightAtScale_absorption
        Q a s t C (k ρ₁ ρ₂) hC hs ht hst

theorem coarseCaccioppoli_interior_heightChoice_of_explicitHeightOfScaleChoice
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C : ℝ)
    (k : ℝ → ℝ → ℕ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂) :
    CoarseCaccioppoliInteriorHeightChoice Q a s t C
      (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k) := by
  exact coarseCaccioppoli_boundary_heightChoice_of_explicitHeightOfScaleChoice
    Q a s t C k hC hs ht hst hscale

theorem coarseCaccioppoli_boundary_heightChoice_of_localizedExplicitHeightOfScaleChoice
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C : ℝ)
    (k : ℝ → ℝ → ℕ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂) :
    CoarseCaccioppoliBoundaryHeightChoice Q a s t C
      (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k) := by
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  refine ⟨k ρ₁ ρ₂, hscale hρ₁ hlt hρ₂, ?_, ?_⟩
  · simpa [coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice] using
      coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale_ge_k_add_four
        Q a s t C (k ρ₁ ρ₂)
  · simpa [coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice] using
      coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale_absorption
        Q a s t C (k ρ₁ ρ₂) hC hs ht hst

theorem coarseCaccioppoli_interior_heightChoice_of_localizedExplicitHeightOfScaleChoice
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C : ℝ)
    (k : ℝ → ℝ → ℕ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂) :
    CoarseCaccioppoliInteriorHeightChoice Q a s t C
      (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k) := by
  exact coarseCaccioppoli_boundary_heightChoice_of_localizedExplicitHeightOfScaleChoice
    Q a s t C k hC hs ht hst hscale

@[simp] theorem coarseCaccioppoliRadiusSequence_zero :
    coarseCaccioppoliRadiusSequence 0 = (1 / 3 : ℝ) := by
  unfold coarseCaccioppoliRadiusSequence
  norm_num


end

end Homogenization
