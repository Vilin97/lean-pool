/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Definitions
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal.Endpoints

/-! # Coarse Caccioppoli Standard Scalar -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Standard scalar bound for coarse Caccioppoli

This file contains the scalar algebra for the standard beta-dependent split
note constant.  The scale-zero envelope module imports this theorem and adds
the dimension-only budget bookkeeping.
-/

noncomputable section

open scoped ENNReal

/-- Explicit scalar majorant for the split deterministic note constant when the
standard beta-dependent radius iteration is used. -/
noncomputable def caccioppoliStandardExplicitNoteBoundSplit
    (s t Calpha Ccross : ℝ) : ℝ :=
  let σ : ℝ := coarseCaccioppoliSigma s t
  let p : ℝ := 2 + 4 * s / σ
  let q : ℝ := coarseCaccioppoliPower s t
  let R : ℝ := coarseCaccioppoliStandardRadiusIterationConst (coarseCaccioppoliBeta s t)
  let B₁ : ℝ := (6561 : ℝ) * 6561 * Ccross ^ (2 : ℕ)
  let B₂ : ℝ :=
    ((9 : ℝ) * Real.rpow (4 : ℝ) q * Real.rpow (81 : ℝ) q) *
      Ccross * Ccross * Real.rpow Calpha q * Real.rpow (1 - s) (-q)
  let B : ℝ := R * (B₁ + B₂)
  σ * Real.rpow (B + 1) p⁻¹

theorem caccioppoliStandardExplicitNoteBoundSplit_mono
    {s t Calpha₁ Calpha₂ Ccross₁ Ccross₂ : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hCalpha₁ : 0 ≤ Calpha₁) (hCalpha₁₂ : Calpha₁ ≤ Calpha₂)
    (hCcross₁ : 0 ≤ Ccross₁) (hCcross₁₂ : Ccross₁ ≤ Ccross₂) :
    caccioppoliStandardExplicitNoteBoundSplit s t Calpha₁ Ccross₁ ≤
      caccioppoliStandardExplicitNoteBoundSplit s t Calpha₂ Ccross₂ := by
  let σ : ℝ := coarseCaccioppoliSigma s t
  let p : ℝ := 2 + 4 * s / σ
  let q : ℝ := coarseCaccioppoliPower s t
  let R : ℝ := coarseCaccioppoliStandardRadiusIterationConst (coarseCaccioppoliBeta s t)
  have hσ_nonneg : 0 ≤ σ := by
    dsimp [σ]
    exact (coarseCaccioppoli_sigma_pos hst).le
  have hp_inv_nonneg : 0 ≤ p⁻¹ := by
    exact inv_nonneg.mpr (coarseCaccioppoli_noteExponent_pos hs hst).le
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact coarseCaccioppoli_power_nonneg hs hst
  have hCalpha₂ : 0 ≤ Calpha₂ := hCalpha₁.trans hCalpha₁₂
  have hCcross₂ : 0 ≤ Ccross₂ := hCcross₁.trans hCcross₁₂
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    exact
      coarseCaccioppoliStandardRadiusIterationConst_nonneg
        (coarseCaccioppoli_beta_nonneg hs hst)
  have hs1_pos : 0 < 1 - s := by linarith
  unfold caccioppoliStandardExplicitNoteBoundSplit
  dsimp [σ, p, q, R]
  gcongr

private theorem caccioppoli_sigma_u_root_singular_le_exp_one
    {σ s u e : ℝ}
    (hσ : 0 < σ) (hs : 0 < s) (hu_eq : u = σ + s)
    (hu_le_one : u ≤ 1) (hσ_le_one_sub_s : σ ≤ 1 - s)
    (heq : e = s / (σ + 2 * s)) :
    σ * Real.rpow (u / σ) (1 - e) * Real.rpow s (-e) *
        Real.rpow (1 - s) (-e) ≤ Real.exp 1 := by
  have hu_pos : 0 < u := by
    rw [hu_eq]
    nlinarith
  have hs_le_u : s ≤ u := by
    rw [hu_eq]
    linarith
  have hs1_pos : 0 < 1 - s := lt_of_lt_of_le hσ hσ_le_one_sub_s
  have hden_pos : 0 < σ + 2 * s := by nlinarith
  have he_nonneg : 0 ≤ e := by
    rw [heq]
    positivity
  have he_le_half : e ≤ (1 / 2 : ℝ) := by
    rw [heq]
    rw [div_le_iff₀ hden_pos]
    nlinarith
  have he_le_one_sub_e : e ≤ 1 - e := by linarith
  let r : ℝ := s / u
  have hr_pos : 0 < r := by
    dsimp [r]
    positivity
  have hr_le_one : r ≤ 1 := by
    dsimp [r]
    rw [div_le_one₀ hu_pos]
    exact hs_le_u
  have he_le_r : e ≤ r := by
    rw [heq]
    dsimp [r]
    rw [div_le_div_iff₀ hden_pos hu_pos]
    nlinarith [hs_le_u]
  have hneg_r_le_neg_e : -r ≤ -e := by linarith
  have hcore_eq :
      σ * Real.rpow (u / σ) (1 - e) * Real.rpow s (-e) *
          Real.rpow (1 - s) (-e) =
        Real.rpow u (1 - e) * Real.rpow s (-e) *
          Real.rpow (σ / (1 - s)) e := by
    have hσe_pos : 0 < Real.rpow σ e := Real.rpow_pos_of_pos hσ e
    have hs1e_pos : 0 < Real.rpow (1 - s) e :=
      Real.rpow_pos_of_pos hs1_pos e
    have hσ_sub :
        Real.rpow σ (1 - e) = σ / Real.rpow σ e := by
      simpa using Real.rpow_sub hσ (1 : ℝ) e
    have hdiv_uσ :
        Real.rpow (u / σ) (1 - e) =
          Real.rpow u (1 - e) / Real.rpow σ (1 - e) := by
      simpa using Real.div_rpow hu_pos.le hσ.le (1 - e)
    have hdiv_σs :
        Real.rpow (σ / (1 - s)) e =
          Real.rpow σ e / Real.rpow (1 - s) e := by
      simpa using Real.div_rpow hσ.le hs1_pos.le e
    have hs1_neg :
        Real.rpow (1 - s) (-e) = (Real.rpow (1 - s) e)⁻¹ := by
      simpa using Real.rpow_neg hs1_pos.le e
    rw [hdiv_uσ, hdiv_σs, hσ_sub, hs1_neg]
    field_simp [hσ.ne', hσe_pos.ne', hs1e_pos.ne']
  have hratio_nonneg : 0 ≤ σ / (1 - s) := div_nonneg hσ.le hs1_pos.le
  have hratio_le_one : σ / (1 - s) ≤ 1 := by
    rw [div_le_one₀ hs1_pos]
    exact hσ_le_one_sub_s
  have hratio_pow_le_one : Real.rpow (σ / (1 - s)) e ≤ 1 := by
    calc
      Real.rpow (σ / (1 - s)) e ≤ Real.rpow (1 : ℝ) e :=
        Real.rpow_le_rpow hratio_nonneg hratio_le_one he_nonneg
      _ = 1 := by simp
  have hu_pow_mono :
      Real.rpow u (1 - e) ≤ Real.rpow u e := by
    exact
      Real.rpow_le_rpow_of_exponent_ge hu_pos hu_le_one he_le_one_sub_e
  have hfirst_nonneg : 0 ≤ Real.rpow u (1 - e) * Real.rpow s (-e) := by
    exact mul_nonneg (Real.rpow_nonneg hu_pos.le (1 - e))
      (Real.rpow_nonneg hs.le (-e))
  have hstep :
      Real.rpow u (1 - e) * Real.rpow s (-e) *
          Real.rpow (σ / (1 - s)) e ≤
        Real.rpow u e * Real.rpow s (-e) := by
    calc
      Real.rpow u (1 - e) * Real.rpow s (-e) *
          Real.rpow (σ / (1 - s)) e ≤
        Real.rpow u (1 - e) * Real.rpow s (-e) * 1 := by
          exact mul_le_mul_of_nonneg_left hratio_pow_le_one hfirst_nonneg
      _ = Real.rpow u (1 - e) * Real.rpow s (-e) := by ring
      _ ≤ Real.rpow u e * Real.rpow s (-e) := by
          exact mul_le_mul_of_nonneg_right hu_pow_mono
            (Real.rpow_nonneg hs.le (-e))
  have hratio_eq :
      Real.rpow u e * Real.rpow s (-e) = Real.rpow r (-e) := by
    have hue_pos : 0 < Real.rpow u e := Real.rpow_pos_of_pos hu_pos e
    have hse_pos : 0 < Real.rpow s e := Real.rpow_pos_of_pos hs e
    have hdiv_rs :
        Real.rpow (s / u) (-e) =
          Real.rpow s (-e) / Real.rpow u (-e) := by
      simpa using Real.div_rpow hs.le hu_pos.le (-e)
    have hs_neg :
        Real.rpow s (-e) = (Real.rpow s e)⁻¹ := by
      simpa using Real.rpow_neg hs.le e
    have hu_neg :
        Real.rpow u (-e) = (Real.rpow u e)⁻¹ := by
      simpa using Real.rpow_neg hu_pos.le e
    dsimp [r]
    change Real.rpow u e * Real.rpow s (-e) = Real.rpow (s / u) (-e)
    rw [hdiv_rs, hs_neg, hu_neg]
    field_simp [hue_pos.ne', hse_pos.ne']
  have hrpow_le_self :
      Real.rpow r (-e) ≤ Real.rpow r (-r) := by
    exact Real.rpow_le_rpow_of_exponent_ge hr_pos hr_le_one hneg_r_le_neg_e
  calc
    σ * Real.rpow (u / σ) (1 - e) * Real.rpow s (-e) *
        Real.rpow (1 - s) (-e)
        = Real.rpow u (1 - e) * Real.rpow s (-e) *
          Real.rpow (σ / (1 - s)) e := hcore_eq
    _ ≤ Real.rpow u e * Real.rpow s (-e) := hstep
    _ = Real.rpow r (-e) := hratio_eq
    _ ≤ Real.rpow r (-r) := hrpow_le_self
    _ ≤ Real.exp 1 := rpow_neg_self_le_exp_one hr_pos hr_le_one

private theorem caccioppoli_standardRadiusRoot_singular_le
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    let σ : ℝ := coarseCaccioppoliSigma s t
    let q : ℝ := coarseCaccioppoliPower s t
    let p : ℝ := 2 + 4 * s / σ
    let R : ℝ :=
      coarseCaccioppoliStandardRadiusIterationConst (coarseCaccioppoliBeta s t)
    σ * Real.rpow R p⁻¹ * Real.rpow s (-(q / p)) *
        Real.rpow (1 - s) (-(q / p)) ≤ 36 * Real.exp 1 := by
  let σ : ℝ := coarseCaccioppoliSigma s t
  let q : ℝ := coarseCaccioppoliPower s t
  let β : ℝ := coarseCaccioppoliBeta s t
  let p : ℝ := 2 + 4 * s / σ
  let R : ℝ := coarseCaccioppoliStandardRadiusIterationConst β
  let e : ℝ := q / p
  let u : ℝ := 1 - t
  have hσ_pos : 0 < σ := by
    dsimp [σ]
    exact coarseCaccioppoli_sigma_pos hst
  have hp_pos : 0 < p := by
    dsimp [p, σ]
    exact coarseCaccioppoli_noteExponent_pos hs hst
  have hp_ge_one : 1 ≤ p := by
    dsimp [p, σ]
    exact coarseCaccioppoli_noteExponent_ge_one hs hst
  have hp_inv_nonneg : 0 ≤ p⁻¹ := inv_nonneg.mpr hp_pos.le
  have hp_inv_le_one : p⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp_ge_one
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact coarseCaccioppoli_power_nonneg hs hst
  have he_nonneg : 0 ≤ e := by
    dsimp [e]
    positivity
  have he_le_one : e ≤ 1 := by
    dsimp [e, q, p, σ]
    exact coarseCaccioppoli_power_div_noteExponent_le_one hs hst
  have hone_sub_e_nonneg : 0 ≤ 1 - e := by linarith
  have hone_sub_e_le_one : 1 - e ≤ 1 := by linarith
  have hβ_ge_two : 2 ≤ β := by
    dsimp [β]
    exact coarseCaccioppoli_beta_ge_two hs hst
  have hβ_nonneg : 0 ≤ β := by linarith
  have hβ_pos : 0 < β := by linarith
  have hbase_pos : 0 < 6 * β := by positivity
  have hbase_nonneg : 0 ≤ 6 * β := hbase_pos.le
  have hβp_eq :
      β * p⁻¹ = 1 - e := by
    have hp_ne : p ≠ 0 := hp_pos.ne'
    have hβ_add_q : β + q = p := by
      have hβ_eq_two_add_q : β = 2 + q := by
        dsimp [β, q]
        exact coarseCaccioppoli_beta_eq_two_add_power hst
      have hp_eq_q : p = 2 + 2 * q := by
        dsimp [p, q, σ, coarseCaccioppoliPower]
        ring
      rw [hβ_eq_two_add_q, hp_eq_q]
      ring
    dsimp [e]
    field_simp [hp_ne]
    linarith
  have hβ_eq : β = 2 * u / σ := by
    dsimp [β, u, σ, coarseCaccioppoliBeta, coarseCaccioppoliSigma]
  have hstandard_root :
      Real.rpow R p⁻¹ ≤
        3 * Real.rpow (12 * (u / σ)) (1 - e) := by
    have hmax : max 1 β = β := max_eq_right (by linarith)
    have hthree_root_le : Real.rpow (3 : ℝ) p⁻¹ ≤ 3 := by
      calc
        Real.rpow (3 : ℝ) p⁻¹ ≤ Real.rpow (3 : ℝ) (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le
            (by norm_num : (1 : ℝ) ≤ 3) hp_inv_le_one
        _ = 3 := by simp
    unfold R
    rw [coarseCaccioppoliStandardRadiusIterationConst_eq_growth, hmax]
    have hsplit :
        Real.rpow (3 * Real.rpow (6 * β) β) p⁻¹ =
          Real.rpow (3 : ℝ) p⁻¹ *
            Real.rpow (Real.rpow (6 * β) β) p⁻¹ := by
      exact Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3)
        (Real.rpow_nonneg hbase_nonneg β)
    rw [hsplit]
    have hbase_mul :
        Real.rpow (Real.rpow (6 * β) β) p⁻¹ =
          Real.rpow (6 * β) (β * p⁻¹) := by
      exact (Real.rpow_mul hbase_nonneg β p⁻¹).symm
    rw [hbase_mul, hβp_eq]
    have hbase_eq : 6 * β = 12 * (u / σ) := by
      rw [hβ_eq]
      ring
    rw [hbase_eq]
    have htarget_nonneg : 0 ≤ 12 * (u / σ) := by
      rw [← hbase_eq]
      exact hbase_nonneg
    exact mul_le_mul_of_nonneg_right hthree_root_le
      (Real.rpow_nonneg htarget_nonneg (1 - e))
  have hu_eq : u = σ + s := by
    dsimp [u, σ, coarseCaccioppoliSigma]
    ring
  have hu_le_one : u ≤ 1 := by
    dsimp [u]
    linarith
  have hσ_le_one_sub_s : σ ≤ 1 - s := by
    dsimp [σ, coarseCaccioppoliSigma]
    linarith
  have heq : e = s / (σ + 2 * s) := by
    have hp_ne : p ≠ 0 := hp_pos.ne'
    have hσ_ne : σ ≠ 0 := hσ_pos.ne'
    have hden_ne : σ + 2 * s ≠ 0 := by nlinarith
    have hp_eq_frac : p = (2 * (σ + 2 * s)) / σ := by
      dsimp [p]
      field_simp [hσ_ne]
      ring
    calc
      e = q / p := rfl
      _ = (2 * s / σ) / ((2 * (σ + 2 * s)) / σ) := by
        rw [hp_eq_frac]
        rfl
      _ = s / (σ + 2 * s) := by
        field_simp [hσ_ne, hden_ne]
  have htwelfth_split :
      Real.rpow (12 * (u / σ)) (1 - e) ≤
        12 * Real.rpow (u / σ) (1 - e) := by
    have hu_pos : 0 < u := by
      rw [hu_eq]
      nlinarith
    have hratio_nonneg : 0 ≤ u / σ := div_nonneg hu_pos.le hσ_pos.le
    have htwelfth_root : Real.rpow (12 : ℝ) (1 - e) ≤ 12 := by
      calc
        Real.rpow (12 : ℝ) (1 - e) ≤ Real.rpow (12 : ℝ) (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le
            (by norm_num : (1 : ℝ) ≤ 12) hone_sub_e_le_one
        _ = 12 := by simp
    rw [show (12 : ℝ) * (u / σ) = 12 * (u / σ) by rfl]
    have hmul :
        Real.rpow ((12 : ℝ) * (u / σ)) (1 - e) =
          Real.rpow (12 : ℝ) (1 - e) *
            Real.rpow (u / σ) (1 - e) := by
      exact Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 12)
        hratio_nonneg
    rw [hmul]
    exact mul_le_mul_of_nonneg_right htwelfth_root
      (Real.rpow_nonneg hratio_nonneg (1 - e))
  have hsingular :
      σ * Real.rpow (u / σ) (1 - e) * Real.rpow s (-e) *
          Real.rpow (1 - s) (-e) ≤ Real.exp 1 :=
    caccioppoli_sigma_u_root_singular_le_exp_one
      hσ_pos hs hu_eq hu_le_one hσ_le_one_sub_s heq
  have hs1_pos : 0 < 1 - s := lt_of_lt_of_le hσ_pos hσ_le_one_sub_s
  have hsingularFactor_nonneg :
      0 ≤ Real.rpow s (-e) * Real.rpow (1 - s) (-e) :=
    mul_nonneg (Real.rpow_nonneg hs.le (-e))
      (Real.rpow_nonneg hs1_pos.le (-e))
  calc
    σ * Real.rpow R p⁻¹ * Real.rpow s (-(q / p)) *
        Real.rpow (1 - s) (-(q / p))
        = σ * Real.rpow R p⁻¹ * Real.rpow s (-e) *
          Real.rpow (1 - s) (-e) := by
            dsimp [e]
    _ ≤ σ * (3 * Real.rpow (12 * (u / σ)) (1 - e)) *
          Real.rpow s (-e) * Real.rpow (1 - s) (-e) := by
            calc
              σ * Real.rpow R p⁻¹ * Real.rpow s (-e) *
                  Real.rpow (1 - s) (-e) =
                (σ * Real.rpow R p⁻¹) *
                  (Real.rpow s (-e) * Real.rpow (1 - s) (-e)) := by ring
              _ ≤
                (σ * (3 * Real.rpow (12 * (u / σ)) (1 - e))) *
                  (Real.rpow s (-e) * Real.rpow (1 - s) (-e)) := by
                    exact mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_left hstandard_root hσ_pos.le)
                      hsingularFactor_nonneg
              _ = σ * (3 * Real.rpow (12 * (u / σ)) (1 - e)) *
                  Real.rpow s (-e) * Real.rpow (1 - s) (-e) := by ring
    _ ≤ σ * (3 * (12 * Real.rpow (u / σ) (1 - e))) *
          Real.rpow s (-e) * Real.rpow (1 - s) (-e) := by
            calc
              σ * (3 * Real.rpow (12 * (u / σ)) (1 - e)) *
                  Real.rpow s (-e) * Real.rpow (1 - s) (-e) =
                (σ * (3 * Real.rpow (12 * (u / σ)) (1 - e))) *
                  (Real.rpow s (-e) * Real.rpow (1 - s) (-e)) := by ring
              _ ≤
                (σ * (3 * (12 * Real.rpow (u / σ) (1 - e)))) *
                  (Real.rpow s (-e) * Real.rpow (1 - s) (-e)) := by
                    have hleft :
                        σ * (3 * Real.rpow (12 * (u / σ)) (1 - e)) ≤
                          σ * (3 * (12 * Real.rpow (u / σ) (1 - e))) := by
                      exact mul_le_mul_of_nonneg_left
                        (mul_le_mul_of_nonneg_left htwelfth_split (by norm_num))
                        hσ_pos.le
                    exact mul_le_mul_of_nonneg_right hleft hsingularFactor_nonneg
              _ = σ * (3 * (12 * Real.rpow (u / σ) (1 - e))) *
                  Real.rpow s (-e) * Real.rpow (1 - s) (-e) := by ring
    _ = 36 *
          (σ * Real.rpow (u / σ) (1 - e) * Real.rpow s (-e) *
            Real.rpow (1 - s) (-e)) := by ring
    _ ≤ 36 * Real.exp 1 := by
          exact mul_le_mul_of_nonneg_left hsingular (by norm_num)

private theorem rpow_add_three_le_sum_rpow
    {a b c α : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1) :
    Real.rpow (a + b + c) α ≤
      Real.rpow a α + Real.rpow b α + Real.rpow c α := by
  have hab_nonneg : 0 ≤ a + b := add_nonneg ha hb
  have habc_nonneg : 0 ≤ a + b + c := add_nonneg hab_nonneg hc
  calc
    Real.rpow (a + b + c) α ≤ Real.rpow (a + b) α + Real.rpow c α :=
      Real.rpow_add_le_add_rpow hab_nonneg hc hα_nonneg hα_le_one
    _ ≤ (Real.rpow a α + Real.rpow b α) + Real.rpow c α := by
      have h := Real.rpow_add_le_add_rpow ha hb hα_nonneg hα_le_one
      exact add_le_add h (le_refl (Real.rpow c α))
    _ = Real.rpow a α + Real.rpow b α + Real.rpow c α := by ring

private theorem rpow_mul_seven
    {a b c d e f g α : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (he : 0 ≤ e) (hf : 0 ≤ f) (hg : 0 ≤ g) :
    Real.rpow ((((((a * b) * c) * d) * e) * f) * g) α =
      ((((((Real.rpow a α * Real.rpow b α) * Real.rpow c α) *
          Real.rpow d α) * Real.rpow e α) * Real.rpow f α) *
        Real.rpow g α) := by
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have habc : 0 ≤ (a * b) * c := mul_nonneg hab hc
  have habcd : 0 ≤ ((a * b) * c) * d := mul_nonneg habc hd
  have habcde : 0 ≤ (((a * b) * c) * d) * e := mul_nonneg habcd he
  have habcdef : 0 ≤ ((((a * b) * c) * d) * e) * f := mul_nonneg habcde hf
  have h₁ :
      Real.rpow ((((((a * b) * c) * d) * e) * f) * g) α =
        Real.rpow (((((a * b) * c) * d) * e) * f) α *
          Real.rpow g α :=
    Real.mul_rpow habcdef hg
  have h₂ :
      Real.rpow (((((a * b) * c) * d) * e) * f) α =
        Real.rpow ((((a * b) * c) * d) * e) α * Real.rpow f α :=
    Real.mul_rpow habcde hf
  have h₃ :
      Real.rpow ((((a * b) * c) * d) * e) α =
        Real.rpow (((a * b) * c) * d) α * Real.rpow e α :=
    Real.mul_rpow habcd he
  have h₄ :
      Real.rpow (((a * b) * c) * d) α =
        Real.rpow ((a * b) * c) α * Real.rpow d α :=
    Real.mul_rpow habc hd
  have h₅ :
      Real.rpow ((a * b) * c) α =
        Real.rpow (a * b) α * Real.rpow c α :=
    Real.mul_rpow hab hc
  have h₆ :
      Real.rpow (a * b) α = Real.rpow a α * Real.rpow b α :=
    Real.mul_rpow ha hb
  rw [h₁, h₂, h₃, h₄, h₅, h₆]

private theorem rpow_le_self_of_one_le_of_exponent_le_one
    {x α : ℝ} (hx : 1 ≤ x) (_hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1) :
    Real.rpow x α ≤ x := by
  calc
    Real.rpow x α ≤ Real.rpow x (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx hα_le_one
    _ = x := by simp

private theorem rpow_le_bound_of_nonneg_le_of_one_le
    {x X α : ℝ} (hx : 0 ≤ x) (hxX : x ≤ X) (hX : 1 ≤ X)
    (hα_nonneg : 0 ≤ α) (hα_le_one : α ≤ 1) :
    Real.rpow x α ≤ X := by
  by_cases hx_le_one : x ≤ 1
  · exact (Real.rpow_le_one hx hx_le_one hα_nonneg).trans hX
  · have hx_ge_one : 1 ≤ x := le_of_lt (lt_of_not_ge hx_le_one)
    exact
      (rpow_le_self_of_one_le_of_exponent_le_one hx_ge_one
        hα_nonneg hα_le_one).trans hxX

private theorem rpow_alphaBudget_le_envelope_mul_singular
    {s Calpha A e : ℝ}
    (hs : 0 < s) (_hs1 : s < 1)
    (hCalpha_nonneg : 0 ≤ Calpha) (hCalpha_le : Calpha ≤ A * s⁻¹)
    (hA_ge_one : 1 ≤ A) (he_nonneg : 0 ≤ e) (he_le_one : e ≤ 1) :
    Real.rpow Calpha e ≤ A * Real.rpow s (-e) := by
  have hA_nonneg : 0 ≤ A := zero_le_one.trans hA_ge_one
  have hsinv_nonneg : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
  have htarget_nonneg : 0 ≤ A * s⁻¹ := mul_nonneg hA_nonneg hsinv_nonneg
  have hA_root_le : Real.rpow A e ≤ A :=
    rpow_le_self_of_one_le_of_exponent_le_one hA_ge_one he_nonneg he_le_one
  have hsplit :
      Real.rpow (A * s⁻¹) e = Real.rpow A e * Real.rpow s (-e) := by
    have hinv :
        Real.rpow s⁻¹ e = Real.rpow s (-e) := by
      have h₁ : Real.rpow s⁻¹ e = (Real.rpow s e)⁻¹ := by
        exact Real.inv_rpow hs.le e
      have h₂ : Real.rpow s (-e) = (Real.rpow s e)⁻¹ := by
        exact Real.rpow_neg hs.le e
      rw [h₁, h₂]
    have hmul :
        Real.rpow (A * s⁻¹) e = Real.rpow A e * Real.rpow s⁻¹ e :=
      Real.mul_rpow hA_nonneg hsinv_nonneg
    rw [hmul, hinv]
  calc
    Real.rpow Calpha e ≤ Real.rpow (A * s⁻¹) e :=
      Real.rpow_le_rpow hCalpha_nonneg hCalpha_le he_nonneg
    _ = Real.rpow A e * Real.rpow s (-e) := hsplit
    _ ≤ A * Real.rpow s (-e) := by
      exact mul_le_mul_of_nonneg_right hA_root_le (Real.rpow_nonneg hs.le (-e))

private theorem caccioppoli_localQuadraticRoot_le_envelope
    {p Ccross X : ℝ}
    (hp_pos : 0 < p) (hp_ge_one : 1 ≤ p)
    (hCcross_nonneg : 0 ≤ Ccross) (hCcross_le : Ccross ≤ X)
    (hX_ge_one : 1 ≤ X) :
    Real.rpow ((6561 : ℝ) * 6561 * Ccross ^ (2 : ℕ)) p⁻¹ ≤
      (6561 : ℝ) * 6561 * X ^ (2 : ℕ) := by
  let M : ℝ := (6561 : ℝ) * 6561 * X ^ (2 : ℕ)
  have hX_nonneg : 0 ≤ X := zero_le_one.trans hX_ge_one
  have hp_inv_nonneg : 0 ≤ p⁻¹ := inv_nonneg.mpr hp_pos.le
  have hp_inv_le_one : p⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp_ge_one
  have hC_sq_le : Ccross ^ (2 : ℕ) ≤ X ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (X - Ccross)]
  have hbase_le :
      (6561 : ℝ) * 6561 * Ccross ^ (2 : ℕ) ≤ M := by
    dsimp [M]
    exact mul_le_mul_of_nonneg_left hC_sq_le (by norm_num)
  have hbase_nonneg :
      0 ≤ (6561 : ℝ) * 6561 * Ccross ^ (2 : ℕ) := by positivity
  have hM_ge_one : 1 ≤ M := by
    dsimp [M]
    nlinarith [sq_nonneg X, hX_ge_one]
  calc
    Real.rpow ((6561 : ℝ) * 6561 * Ccross ^ (2 : ℕ)) p⁻¹ ≤
        Real.rpow M p⁻¹ :=
      Real.rpow_le_rpow hbase_nonneg hbase_le hp_inv_nonneg
    _ ≤ M :=
      rpow_le_self_of_one_le_of_exponent_le_one hM_ge_one
        hp_inv_nonneg hp_inv_le_one
    _ = (6561 : ℝ) * 6561 * X ^ (2 : ℕ) := rfl

private theorem caccioppoli_frontBranchRoot_le_envelope
    {s t Calpha Ccross A X : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hCalpha_nonneg : 0 ≤ Calpha) (hCalpha_le : Calpha ≤ A * s⁻¹)
    (hCcross_nonneg : 0 ≤ Ccross) (hCcross_le : Ccross ≤ X)
    (hA_ge_one : 1 ≤ A) (hX_ge_one : 1 ≤ X) :
    let σ : ℝ := coarseCaccioppoliSigma s t
    let q : ℝ := coarseCaccioppoliPower s t
    let p : ℝ := 2 + 4 * s / σ
    let e : ℝ := q / p
    let B₂ : ℝ :=
      ((9 : ℝ) * Real.rpow (4 : ℝ) q * Real.rpow (81 : ℝ) q) *
        Ccross * Ccross * Real.rpow Calpha q * Real.rpow (1 - s) (-q)
    Real.rpow B₂ p⁻¹ ≤
      (9 : ℝ) * 4 * 81 * X * X * A *
        Real.rpow s (-e) * Real.rpow (1 - s) (-e) := by
  let σ : ℝ := coarseCaccioppoliSigma s t
  let q : ℝ := coarseCaccioppoliPower s t
  let p : ℝ := 2 + 4 * s / σ
  let e : ℝ := q / p
  let B₂ : ℝ :=
    ((9 : ℝ) * Real.rpow (4 : ℝ) q * Real.rpow (81 : ℝ) q) *
      Ccross * Ccross * Real.rpow Calpha q * Real.rpow (1 - s) (-q)
  have hs1 : s < 1 := by linarith
  have hs1_pos : 0 < 1 - s := by linarith
  have hp_pos : 0 < p := by
    dsimp [p, σ]
    exact coarseCaccioppoli_noteExponent_pos hs hst
  have hp_ge_one : 1 ≤ p := by
    dsimp [p, σ]
    exact coarseCaccioppoli_noteExponent_ge_one hs hst
  have hp_inv_nonneg : 0 ≤ p⁻¹ := inv_nonneg.mpr hp_pos.le
  have hp_inv_le_one : p⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp_ge_one
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact coarseCaccioppoli_power_nonneg hs hst
  have he_nonneg : 0 ≤ e := by
    dsimp [e]
    exact div_nonneg hq_nonneg hp_pos.le
  have he_le_one : e ≤ 1 := by
    dsimp [e, q, p, σ]
    exact coarseCaccioppoli_power_div_noteExponent_le_one hs hst
  have hq_mul_inv : q * p⁻¹ = e := by
    dsimp [e]
    rw [div_eq_mul_inv]
  have h4_nonneg : 0 ≤ Real.rpow (4 : ℝ) q :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (4 : ℝ)) q
  have h81_nonneg : 0 ≤ Real.rpow (81 : ℝ) q :=
    Real.rpow_nonneg (by norm_num : 0 ≤ (81 : ℝ)) q
  have hCalpha_q_nonneg : 0 ≤ Real.rpow Calpha q :=
    Real.rpow_nonneg hCalpha_nonneg q
  have hs1_q_nonneg : 0 ≤ Real.rpow (1 - s) (-q) :=
    Real.rpow_nonneg hs1_pos.le (-q)
  have hsplit :
      Real.rpow B₂ p⁻¹ =
        ((((((Real.rpow (9 : ℝ) p⁻¹ *
          Real.rpow (Real.rpow (4 : ℝ) q) p⁻¹) *
          Real.rpow (Real.rpow (81 : ℝ) q) p⁻¹) *
          Real.rpow Ccross p⁻¹) * Real.rpow Ccross p⁻¹) *
          Real.rpow (Real.rpow Calpha q) p⁻¹) *
          Real.rpow (Real.rpow (1 - s) (-q)) p⁻¹) := by
    dsimp [B₂]
    simpa [mul_assoc] using
      rpow_mul_seven
        (a := (9 : ℝ)) (b := Real.rpow (4 : ℝ) q)
        (c := Real.rpow (81 : ℝ) q) (d := Ccross) (e := Ccross)
        (f := Real.rpow Calpha q) (g := Real.rpow (1 - s) (-q))
        (α := p⁻¹)
        (by norm_num : 0 ≤ (9 : ℝ)) h4_nonneg h81_nonneg
        hCcross_nonneg hCcross_nonneg hCalpha_q_nonneg hs1_q_nonneg
  have h9_root : Real.rpow (9 : ℝ) p⁻¹ ≤ 9 :=
    rpow_le_self_of_one_le_of_exponent_le_one
      (by norm_num : (1 : ℝ) ≤ 9) hp_inv_nonneg hp_inv_le_one
  have h4_root : Real.rpow (Real.rpow (4 : ℝ) q) p⁻¹ ≤ 4 := by
    have hmul :
        Real.rpow (Real.rpow (4 : ℝ) q) p⁻¹ =
          Real.rpow (4 : ℝ) (q * p⁻¹) :=
      (Real.rpow_mul (by norm_num : 0 ≤ (4 : ℝ)) q p⁻¹).symm
    rw [hmul, hq_mul_inv]
    exact rpow_le_self_of_one_le_of_exponent_le_one
      (by norm_num : (1 : ℝ) ≤ 4) he_nonneg he_le_one
  have h81_root : Real.rpow (Real.rpow (81 : ℝ) q) p⁻¹ ≤ 81 := by
    have hmul :
        Real.rpow (Real.rpow (81 : ℝ) q) p⁻¹ =
          Real.rpow (81 : ℝ) (q * p⁻¹) :=
      (Real.rpow_mul (by norm_num : 0 ≤ (81 : ℝ)) q p⁻¹).symm
    rw [hmul, hq_mul_inv]
    exact rpow_le_self_of_one_le_of_exponent_le_one
      (by norm_num : (1 : ℝ) ≤ 81) he_nonneg he_le_one
  have hCcross_root : Real.rpow Ccross p⁻¹ ≤ X :=
    rpow_le_bound_of_nonneg_le_of_one_le hCcross_nonneg hCcross_le hX_ge_one
      hp_inv_nonneg hp_inv_le_one
  have hCalpha_root :
      Real.rpow (Real.rpow Calpha q) p⁻¹ ≤ A * Real.rpow s (-e) := by
    have hmul :
        Real.rpow (Real.rpow Calpha q) p⁻¹ =
          Real.rpow Calpha (q * p⁻¹) :=
      (Real.rpow_mul hCalpha_nonneg q p⁻¹).symm
    rw [hmul, hq_mul_inv]
    exact
      rpow_alphaBudget_le_envelope_mul_singular hs hs1 hCalpha_nonneg
        hCalpha_le hA_ge_one he_nonneg he_le_one
  have hs1_root :
      Real.rpow (Real.rpow (1 - s) (-q)) p⁻¹ =
        Real.rpow (1 - s) (-e) := by
    have hmul :
        Real.rpow (Real.rpow (1 - s) (-q)) p⁻¹ =
          Real.rpow (1 - s) ((-q) * p⁻¹) :=
      (Real.rpow_mul hs1_pos.le (-q) p⁻¹).symm
    have hexp : (-q) * p⁻¹ = -e := by
      rw [← hq_mul_inv]
      ring
    rw [hmul, hexp]
  change Real.rpow B₂ p⁻¹ ≤
      (9 : ℝ) * 4 * 81 * X * X * A *
        Real.rpow s (-e) * Real.rpow (1 - s) (-e)
  rw [hsplit, hs1_root]
  calc
    ((((((Real.rpow (9 : ℝ) p⁻¹ *
          Real.rpow (Real.rpow (4 : ℝ) q) p⁻¹) *
          Real.rpow (Real.rpow (81 : ℝ) q) p⁻¹) *
          Real.rpow Ccross p⁻¹) * Real.rpow Ccross p⁻¹) *
          Real.rpow (Real.rpow Calpha q) p⁻¹) *
          Real.rpow (1 - s) (-e))
        ≤ ((((((9 : ℝ) * 4) * 81) * X) * X) *
          (A * Real.rpow s (-e))) * Real.rpow (1 - s) (-e) := by
          gcongr <;>
            first
            | exact Real.rpow_nonneg hs1_pos.le (-e)
            | exact Real.rpow_nonneg hCalpha_q_nonneg p⁻¹
            | exact Real.rpow_nonneg hCcross_nonneg p⁻¹
            | exact Real.rpow_nonneg h81_nonneg p⁻¹
            | exact Real.rpow_nonneg h4_nonneg p⁻¹
    _ = (9 : ℝ) * 4 * 81 * X * X * A *
        Real.rpow s (-e) * Real.rpow (1 - s) (-e) := by ring

theorem caccioppoliStandardExplicitNoteBoundSplit_le_envelope
    {s t Calpha Ccross A X : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hCalpha_nonneg : 0 ≤ Calpha) (hCalpha_le : Calpha ≤ A * s⁻¹)
    (hCcross_nonneg : 0 ≤ Ccross) (hCcross_le : Ccross ≤ X)
    (hA_ge_one : 1 ≤ A) (hX_ge_one : 1 ≤ X) :
    caccioppoliStandardExplicitNoteBoundSplit s t Calpha Ccross ≤
      36 * ((6561 : ℝ) * 6561 * X ^ (2 : ℕ)) +
        36 * Real.exp 1 * ((9 : ℝ) * 4 * 81 * X * X * A) + 1 := by
  let σ : ℝ := coarseCaccioppoliSigma s t
  let q : ℝ := coarseCaccioppoliPower s t
  let p : ℝ := 2 + 4 * s / σ
  let R : ℝ := coarseCaccioppoliStandardRadiusIterationConst (coarseCaccioppoliBeta s t)
  let e : ℝ := q / p
  let B₁ : ℝ := (6561 : ℝ) * 6561 * Ccross ^ (2 : ℕ)
  let B₂ : ℝ :=
    ((9 : ℝ) * Real.rpow (4 : ℝ) q * Real.rpow (81 : ℝ) q) *
      Ccross * Ccross * Real.rpow Calpha q * Real.rpow (1 - s) (-q)
  let M₁ : ℝ := (6561 : ℝ) * 6561 * X ^ (2 : ℕ)
  let K₂ : ℝ := (9 : ℝ) * 4 * 81 * X * X * A
  have hσ_pos : 0 < σ := by
    dsimp [σ]
    exact coarseCaccioppoli_sigma_pos hst
  have hσ_nonneg : 0 ≤ σ := hσ_pos.le
  have hσ_le_one : σ ≤ 1 := by
    dsimp [σ, coarseCaccioppoliSigma]
    linarith
  have hp_pos : 0 < p := by
    dsimp [p, σ]
    exact coarseCaccioppoli_noteExponent_pos hs hst
  have hp_ge_one : 1 ≤ p := by
    dsimp [p, σ]
    exact coarseCaccioppoli_noteExponent_ge_one hs hst
  have hp_inv_nonneg : 0 ≤ p⁻¹ := inv_nonneg.mpr hp_pos.le
  have hp_inv_le_one : p⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp_ge_one
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact coarseCaccioppoli_power_nonneg hs hst
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    exact
      coarseCaccioppoliStandardRadiusIterationConst_nonneg
        (coarseCaccioppoli_beta_nonneg hs hst)
  have hB₁_nonneg : 0 ≤ B₁ := by
    dsimp [B₁]
    positivity
  have hs1_pos : 0 < 1 - s := by linarith
  have hB₂_nonneg : 0 ≤ B₂ := by
    dsimp [B₂]
    positivity
  have hRB₁_nonneg : 0 ≤ R * B₁ := mul_nonneg hR_nonneg hB₁_nonneg
  have hRB₂_nonneg : 0 ≤ R * B₂ := mul_nonneg hR_nonneg hB₂_nonneg
  have hsum_nonneg : 0 ≤ R * B₁ + R * B₂ := add_nonneg hRB₁_nonneg hRB₂_nonneg
  have hmain_root :
      Real.rpow (R * (B₁ + B₂) + 1) p⁻¹ ≤
        Real.rpow (R * B₁) p⁻¹ + Real.rpow (R * B₂) p⁻¹ +
          Real.rpow (1 : ℝ) p⁻¹ := by
    have hrewrite : R * (B₁ + B₂) + 1 = R * B₁ + R * B₂ + 1 := by ring
    rw [hrewrite]
    exact
      rpow_add_three_le_sum_rpow hRB₁_nonneg hRB₂_nonneg
        (by norm_num : 0 ≤ (1 : ℝ)) hp_inv_nonneg hp_inv_le_one
  have hRroot_nonneg : 0 ≤ Real.rpow R p⁻¹ := Real.rpow_nonneg hR_nonneg p⁻¹
  have hB₁root_nonneg : 0 ≤ Real.rpow B₁ p⁻¹ := Real.rpow_nonneg hB₁_nonneg p⁻¹
  have hσRroot_nonneg : 0 ≤ σ * Real.rpow R p⁻¹ :=
    mul_nonneg hσ_nonneg hRroot_nonneg
  have hσRroot_le :
      σ * Real.rpow R p⁻¹ ≤ 36 := by
    dsimp [σ, p, R]
    simpa using
      coarseCaccioppoli_sigma_mul_standardRadiusIterationConst_root_le
        hs ht hst
  have hB₁root_le : Real.rpow B₁ p⁻¹ ≤ M₁ := by
    dsimp [B₁, M₁]
    exact
      caccioppoli_localQuadraticRoot_le_envelope
        hp_pos hp_ge_one hCcross_nonneg hCcross_le hX_ge_one
  have hterm₁ :
      σ * Real.rpow (R * B₁) p⁻¹ ≤ 36 * M₁ := by
    have hsplit :
        Real.rpow (R * B₁) p⁻¹ =
          Real.rpow R p⁻¹ * Real.rpow B₁ p⁻¹ :=
      Real.mul_rpow hR_nonneg hB₁_nonneg
    calc
      σ * Real.rpow (R * B₁) p⁻¹ =
          (σ * Real.rpow R p⁻¹) * Real.rpow B₁ p⁻¹ := by
            rw [hsplit]
            ring
      _ ≤ 36 * M₁ :=
          mul_le_mul hσRroot_le hB₁root_le hB₁root_nonneg
            (by positivity : 0 ≤ (36 : ℝ))
  have hB₂root_le :
      Real.rpow B₂ p⁻¹ ≤
        K₂ * Real.rpow s (-e) * Real.rpow (1 - s) (-e) := by
    dsimp [B₂, K₂, e, q, p, σ]
    simpa [mul_assoc] using
      caccioppoli_frontBranchRoot_le_envelope
        (s := s) (t := t) (Calpha := Calpha) (Ccross := Ccross)
        (A := A) (X := X)
        hs ht hst hCalpha_nonneg hCalpha_le hCcross_nonneg hCcross_le
        hA_ge_one hX_ge_one
  have hK₂_nonneg : 0 ≤ K₂ := by
    dsimp [K₂]
    positivity
  have hsingular :
      σ * Real.rpow R p⁻¹ * Real.rpow s (-e) *
          Real.rpow (1 - s) (-e) ≤ 36 * Real.exp 1 := by
    dsimp [σ, q, p, R, e]
    simpa using caccioppoli_standardRadiusRoot_singular_le hs ht hst
  have hterm₂ :
      σ * Real.rpow (R * B₂) p⁻¹ ≤ 36 * Real.exp 1 * K₂ := by
    have hsplit :
        Real.rpow (R * B₂) p⁻¹ =
          Real.rpow R p⁻¹ * Real.rpow B₂ p⁻¹ :=
      Real.mul_rpow hR_nonneg hB₂_nonneg
    calc
      σ * Real.rpow (R * B₂) p⁻¹ =
          (σ * Real.rpow R p⁻¹) * Real.rpow B₂ p⁻¹ := by
            rw [hsplit]
            ring
      _ ≤ (σ * Real.rpow R p⁻¹) *
          (K₂ * Real.rpow s (-e) * Real.rpow (1 - s) (-e)) := by
            exact mul_le_mul_of_nonneg_left hB₂root_le hσRroot_nonneg
      _ = K₂ * (σ * Real.rpow R p⁻¹ * Real.rpow s (-e) *
          Real.rpow (1 - s) (-e)) := by ring
      _ ≤ K₂ * (36 * Real.exp 1) :=
          mul_le_mul_of_nonneg_left hsingular hK₂_nonneg
      _ = 36 * Real.exp 1 * K₂ := by ring
  have hterm₃ : σ * Real.rpow (1 : ℝ) p⁻¹ ≤ 1 := by
    simpa using hσ_le_one
  unfold caccioppoliStandardExplicitNoteBoundSplit
  dsimp [σ, p, q, R, B₁, B₂]
  calc
    σ * Real.rpow (R * (B₁ + B₂) + 1) p⁻¹ ≤
        σ * (Real.rpow (R * B₁) p⁻¹ + Real.rpow (R * B₂) p⁻¹ +
          Real.rpow (1 : ℝ) p⁻¹) :=
          mul_le_mul_of_nonneg_left hmain_root hσ_nonneg
    _ =
        σ * Real.rpow (R * B₁) p⁻¹ +
          σ * Real.rpow (R * B₂) p⁻¹ +
          σ * Real.rpow (1 : ℝ) p⁻¹ := by ring
    _ ≤ 36 * M₁ + 36 * Real.exp 1 * K₂ + 1 := by
          linarith
    _ =
      36 * ((6561 : ℝ) * 6561 * X ^ (2 : ℕ)) +
        36 * Real.exp 1 * ((9 : ℝ) * 4 * 81 * X * X * A) + 1 := by
          rfl



end

end Ch03
end Book
end Homogenization
