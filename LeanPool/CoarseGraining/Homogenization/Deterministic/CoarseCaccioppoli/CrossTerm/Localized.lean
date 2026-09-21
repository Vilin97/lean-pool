/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.CrossTerm.ExplicitHeight

/-! # Localized -/

namespace Homogenization

/-!
# Coarse Caccioppoli cross term: localized explicit height
-/

noncomputable section

open scoped BigOperators

theorem coarseCaccioppoli_boundary_noteCrossTermBound_of_localizedExplicitHeightOfScaleChoice
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (k : ℝ → ℝ → ℕ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂) :
    ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
      (coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s C uL2Sq
          (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
          ρ₁ ρ₂) ^ (2 : ℕ) ≤
        coarseCaccioppoliBoundaryExplicitHeightRecursionRhs Q a s t C uL2Sq *
          Real.rpow (ρ₂ - ρ₁) (-coarseCaccioppoliBeta s t) := by
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  let hOld : ℝ := coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k ρ₁ ρ₂
  let hNew : ℝ :=
    coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k ρ₁ ρ₂
  by_cases hbranch : (4 : ℝ) / s ≤ hOld
  · have hNew_eq : hNew = hOld := by
      have hbranch' :
          (4 : ℝ) / s ≤
            coarseCaccioppoliBoundaryExplicitHeightAtScale Q a s t C (k ρ₁ ρ₂) := by
        simpa [hOld, coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice] using hbranch
      dsimp [hNew, hOld, coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice,
        coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale,
        coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice]
      rw [max_eq_left hbranch']
    have hheight_eval :
        coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k ρ₁ ρ₂ =
          coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k ρ₁ ρ₂ := by
      simpa [hNew, hOld] using hNew_eq
    simpa [coarseCaccioppoliBoundaryCrossCoeffOfHeight, hheight_eval] using
      (coarseCaccioppoli_boundary_noteCrossTermBound_of_explicitHeightOfScaleChoice
        Q a s t C uL2Sq k hC hs ht hst hu hscale hρ₁ hlt hρ₂)
  · have hOld_lt : hOld < (4 : ℝ) / s := lt_of_not_ge hbranch
    have hNew_eq : hNew = (4 : ℝ) / s := by
      have hOld_lt' :
          coarseCaccioppoliBoundaryExplicitHeightAtScale Q a s t C (k ρ₁ ρ₂) <
            (4 : ℝ) / s := by
        simpa [hOld, coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice] using hOld_lt
      dsimp [hNew, hOld, coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice,
        coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale,
        coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice]
      rw [max_eq_right hOld_lt'.le]
    let p : ℝ := coarseCaccioppoliPower s t
    let M : ℝ := C / (s * (1 - s)) * Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ)
    have hLambda_nonneg : 0 ≤ LambdaSq Q s (.finite 1) a :=
      multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs.le
    have hgap_pos : 0 < coarseCaccioppoliGapInv ρ₁ ρ₂ := by
      rw [coarseCaccioppoliGapInv_eq_inv]
      exact inv_pos.mpr (sub_pos.mpr hlt)
    have hgap_ge_one : 1 ≤ coarseCaccioppoliGapInv ρ₁ ρ₂ := by
      have hthree_halves : (3 / 2 : ℝ) ≤ coarseCaccioppoliGapInv ρ₁ ρ₂ :=
        coarseCaccioppoliGapInv_ge_three_halves hρ₁ hlt hρ₂
      linarith
    have h2s_nonneg : 0 ≤ 2 * s := by positivity
    have hgap_pow_ge_one :
        1 ≤ Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (2 * s) := by
      simpa using
        Real.rpow_le_rpow (by norm_num : 0 ≤ (1 : ℝ)) hgap_ge_one h2s_nonneg
    have hgap_sq :
        (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) =
          Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (2 : ℝ) := by
      symm
      exact Real.rpow_natCast _ 2
    have hgap_exp :
        Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (2 : ℝ) *
            Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (2 * s) =
          Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (2 + 2 * s) := by
      simpa using
        (Real.rpow_add hgap_pos (2 : ℝ) (2 * s)).symm
    have hgap_beta :
        Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (2 + 2 * s) ≤
          Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (coarseCaccioppoliBeta s t) := by
      exact Real.rpow_le_rpow_of_exponent_le hgap_ge_one
        (coarseCaccioppoli_beta_ge_two_add_two_mul_s hs ht hst)
    have hprefix_nonneg :
        0 ≤ C * (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) *
          LambdaSq Q s (.finite 1) a * uL2Sq := by
      refine mul_nonneg (mul_nonneg ?_ hLambda_nonneg) hu
      exact mul_nonneg hC (sq_nonneg _)
    have hp_nonneg : 0 ≤ p := coarseCaccioppoli_power_nonneg hs hst
    have htheta_nonneg : 0 ≤ ThetaRatio Q s t a :=
      thetaRatio_nonneg Q s t a hs.le ht.le
    have hden_nonneg : 0 ≤ s * (1 - s) :=
      mul_one_sub_nonneg hs.le (by linarith)
    have hM_nonneg : 0 ≤ M := by
      dsimp [M]
      exact mul_nonneg
        (div_nonneg hC hden_nonneg)
        (Real.rpow_nonneg htheta_nonneg _)
    have hrec_nonneg :
        0 ≤ coarseCaccioppoliBoundaryRecursionRhs Q a s t C uL2Sq := by
      unfold coarseCaccioppoliBoundaryRecursionRhs
      exact mul_nonneg
        (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hM_nonneg _)) hLambda_nonneg)
        hu
    have hfirst_nonneg :
        0 ≤ (6561 : ℝ) * 6561 * C ^ (2 : ℕ) * LambdaSq Q s (.finite 1) a *
          uL2Sq := by
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg C)) hLambda_nonneg)
        hu
    have hsecond_nonneg :
        0 ≤ ((9 : ℝ) * Real.rpow (4 : ℝ) p * Real.rpow (81 : ℝ) p) *
          C * coarseCaccioppoliBoundaryRecursionRhs Q a s t C uL2Sq := by
      have hcoeff_nonneg :
          0 ≤ ((9 : ℝ) * Real.rpow (4 : ℝ) p * Real.rpow (81 : ℝ) p) := by
        exact mul_nonneg
          (mul_nonneg (by norm_num : 0 ≤ (9 : ℝ))
            (Real.rpow_nonneg (by norm_num : 0 ≤ (4 : ℝ)) _))
          (Real.rpow_nonneg (by norm_num : 0 ≤ (81 : ℝ)) _)
      exact mul_nonneg (mul_nonneg hcoeff_nonneg hC) hrec_nonneg
    have hcross_sq :
        (coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s C uL2Sq
            (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
            ρ₁ ρ₂) ^ (2 : ℕ) =
          (C * (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) *
            LambdaSq Q s (.finite 1) a * uL2Sq) *
            (C * Real.rpow (3 : ℝ) (2 * s * hNew)) := by
      simpa [hNew] using
        (coarseCaccioppoliBoundaryCrossCoeffOfHeight_sq
          (Q := Q) (a := a) (s := s) (C := C) (uL2Sq := uL2Sq)
          (h := coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
          (ρ₁ := ρ₁) (ρ₂ := ρ₂) hs.le hu)
    have hpow_height :
        Real.rpow (3 : ℝ) (2 * s * hNew) = (6561 : ℝ) := by
      rw [hNew_eq]
      calc
        Real.rpow (3 : ℝ) (2 * s * (4 / s))
            = Real.rpow (3 : ℝ) (8 : ℝ) := by
              congr 1
              field_simp [hs.ne']
              ring
        _ = (6561 : ℝ) := by
              norm_num [Real.rpow_natCast]
    have hscalar :
        C * Real.rpow (3 : ℝ) (2 * s * hNew) ≤
          (6561 : ℝ) * 6561 * C *
            Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (2 * s) := by
      rw [hpow_height]
      nlinarith
    calc
      (coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s C uL2Sq
          (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t C k)
          ρ₁ ρ₂) ^ (2 : ℕ)
          =
        (C * (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) *
            LambdaSq Q s (.finite 1) a * uL2Sq) *
          (C * Real.rpow (3 : ℝ) (2 * s * hNew)) := hcross_sq
      _ ≤
        (C * (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) *
            LambdaSq Q s (.finite 1) a * uL2Sq) *
          ((6561 : ℝ) * 6561 * C *
            Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (2 * s)) := by
            exact mul_le_mul_of_nonneg_left hscalar hprefix_nonneg
      _ =
        ((6561 : ℝ) * 6561 * C ^ (2 : ℕ) *
            LambdaSq Q s (.finite 1) a * uL2Sq) *
          ((coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) *
            Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (2 * s)) := by
            ring
      _ =
        ((6561 : ℝ) * 6561 * C ^ (2 : ℕ) *
            LambdaSq Q s (.finite 1) a * uL2Sq) *
          Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (2 + 2 * s) := by
            rw [hgap_sq, hgap_exp]
      _ ≤
        ((6561 : ℝ) * 6561 * C ^ (2 : ℕ) *
            LambdaSq Q s (.finite 1) a * uL2Sq) *
          Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (coarseCaccioppoliBeta s t) := by
            exact mul_le_mul_of_nonneg_left hgap_beta hfirst_nonneg
      _ =
        ((6561 : ℝ) * 6561 * C ^ (2 : ℕ) *
            LambdaSq Q s (.finite 1) a * uL2Sq) *
          Real.rpow (ρ₂ - ρ₁) (-coarseCaccioppoliBeta s t) := by
            rw [coarseCaccioppoli_gapInv_rpow_eq]
      _ ≤
        coarseCaccioppoliBoundaryExplicitHeightRecursionRhs Q a s t C uL2Sq *
          Real.rpow (ρ₂ - ρ₁) (-coarseCaccioppoliBeta s t) := by
            unfold coarseCaccioppoliBoundaryExplicitHeightRecursionRhs
            exact mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_right hsecond_nonneg)
              (Real.rpow_nonneg (sub_nonneg.mpr hlt.le) _)

theorem coarseCaccioppoli_boundary_noteCrossTermBoundSplit_of_localizedExplicitHeightOfScaleChoice
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (s t Calpha Ccross uL2Sq : ℝ) (k : ℝ → ℝ → ℕ)
    (hCalpha : 0 < Calpha) (hCcross : 0 ≤ Ccross)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂) :
    ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
      (coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s Ccross uL2Sq
          (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice
            Q a s t Calpha k)
          ρ₁ ρ₂) ^ (2 : ℕ) ≤
        coarseCaccioppoliBoundaryExplicitHeightRecursionRhsSplit
            Q a s t Calpha Ccross uL2Sq *
          Real.rpow (ρ₂ - ρ₁) (-coarseCaccioppoliBeta s t) := by
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  let hOld : ℝ :=
    coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t Calpha k ρ₁ ρ₂
  let hNew : ℝ :=
    coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice Q a s t Calpha k
      ρ₁ ρ₂
  by_cases hbranch : (4 : ℝ) / s ≤ hOld
  · have hNew_eq : hNew = hOld := by
      have hbranch' :
          (4 : ℝ) / s ≤
            coarseCaccioppoliBoundaryExplicitHeightAtScale
              Q a s t Calpha (k ρ₁ ρ₂) := by
        simpa [hOld, coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice] using hbranch
      dsimp [hNew, hOld, coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice,
        coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale,
        coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice]
      rw [max_eq_left hbranch']
    have hheight_eval :
        coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice
            Q a s t Calpha k ρ₁ ρ₂ =
          coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice
            Q a s t Calpha k ρ₁ ρ₂ := by
      simpa [hNew, hOld] using hNew_eq
    simpa [coarseCaccioppoliBoundaryCrossCoeffOfHeight, hheight_eval] using
      (coarseCaccioppoli_boundary_noteCrossTermBoundSplit_of_explicitHeightOfScaleChoice
        Q a s t Calpha Ccross uL2Sq k hCalpha hCcross hs ht hst hu hscale
        hρ₁ hlt hρ₂)
  · have hOld_lt : hOld < (4 : ℝ) / s := lt_of_not_ge hbranch
    have hNew_eq : hNew = (4 : ℝ) / s := by
      have hOld_lt' :
          coarseCaccioppoliBoundaryExplicitHeightAtScale
              Q a s t Calpha (k ρ₁ ρ₂) <
            (4 : ℝ) / s := by
        simpa [hOld, coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice] using hOld_lt
      dsimp [hNew, hOld, coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice,
        coarseCaccioppoliBoundaryLocalizedExplicitHeightAtScale,
        coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice]
      rw [max_eq_right hOld_lt'.le]
    let p : ℝ := coarseCaccioppoliPower s t
    let M : ℝ :=
      Calpha / (s * (1 - s)) * Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ)
    have hLambda_nonneg : 0 ≤ LambdaSq Q s (.finite 1) a :=
      multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs.le
    have hgap_pos : 0 < coarseCaccioppoliGapInv ρ₁ ρ₂ := by
      rw [coarseCaccioppoliGapInv_eq_inv]
      exact inv_pos.mpr (sub_pos.mpr hlt)
    have hgap_ge_one : 1 ≤ coarseCaccioppoliGapInv ρ₁ ρ₂ := by
      have hthree_halves : (3 / 2 : ℝ) ≤ coarseCaccioppoliGapInv ρ₁ ρ₂ :=
        coarseCaccioppoliGapInv_ge_three_halves hρ₁ hlt hρ₂
      linarith
    have h2s_nonneg : 0 ≤ 2 * s := by positivity
    have hgap_pow_ge_one :
        1 ≤ Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (2 * s) := by
      simpa using
        Real.rpow_le_rpow (by norm_num : 0 ≤ (1 : ℝ)) hgap_ge_one h2s_nonneg
    have hgap_sq :
        (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) =
          Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (2 : ℝ) := by
      symm
      exact Real.rpow_natCast _ 2
    have hgap_exp :
        Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (2 : ℝ) *
            Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (2 * s) =
          Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (2 + 2 * s) := by
      simpa using
        (Real.rpow_add hgap_pos (2 : ℝ) (2 * s)).symm
    have hgap_beta :
        Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (2 + 2 * s) ≤
          Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (coarseCaccioppoliBeta s t) := by
      exact Real.rpow_le_rpow_of_exponent_le hgap_ge_one
        (coarseCaccioppoli_beta_ge_two_add_two_mul_s hs ht hst)
    have hprefix_nonneg :
        0 ≤ Ccross * (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) *
          LambdaSq Q s (.finite 1) a * uL2Sq := by
      refine mul_nonneg (mul_nonneg ?_ hLambda_nonneg) hu
      exact mul_nonneg hCcross (sq_nonneg _)
    have hp_nonneg : 0 ≤ p := coarseCaccioppoli_power_nonneg hs hst
    have htheta_nonneg : 0 ≤ ThetaRatio Q s t a :=
      thetaRatio_nonneg Q s t a hs.le ht.le
    have hden_nonneg : 0 ≤ s * (1 - s) :=
      mul_one_sub_nonneg hs.le (by linarith)
    have hM_nonneg : 0 ≤ M := by
      dsimp [M]
      exact mul_nonneg
        (div_nonneg hCalpha.le hden_nonneg)
        (Real.rpow_nonneg htheta_nonneg _)
    have hrec_nonneg :
        0 ≤ coarseCaccioppoliBoundaryRecursionRhsSplit
          Q a s t Calpha Ccross uL2Sq := by
      unfold coarseCaccioppoliBoundaryRecursionRhsSplit
      exact mul_nonneg
        (mul_nonneg (mul_nonneg hCcross (Real.rpow_nonneg hM_nonneg _))
          hLambda_nonneg)
        hu
    have hfirst_nonneg :
        0 ≤ (6561 : ℝ) * 6561 * Ccross ^ (2 : ℕ) *
          LambdaSq Q s (.finite 1) a * uL2Sq := by
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg Ccross)) hLambda_nonneg)
        hu
    have hsecond_nonneg :
        0 ≤ ((9 : ℝ) * Real.rpow (4 : ℝ) p * Real.rpow (81 : ℝ) p) *
          Ccross *
            coarseCaccioppoliBoundaryRecursionRhsSplit
              Q a s t Calpha Ccross uL2Sq := by
      have hcoeff_nonneg :
          0 ≤ ((9 : ℝ) * Real.rpow (4 : ℝ) p * Real.rpow (81 : ℝ) p) := by
        exact mul_nonneg
          (mul_nonneg (by norm_num : 0 ≤ (9 : ℝ))
            (Real.rpow_nonneg (by norm_num : 0 ≤ (4 : ℝ)) _))
          (Real.rpow_nonneg (by norm_num : 0 ≤ (81 : ℝ)) _)
      exact mul_nonneg (mul_nonneg hcoeff_nonneg hCcross) hrec_nonneg
    have hcross_sq :
        (coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s Ccross uL2Sq
            (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice
              Q a s t Calpha k)
            ρ₁ ρ₂) ^ (2 : ℕ) =
          (Ccross * (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) *
            LambdaSq Q s (.finite 1) a * uL2Sq) *
            (Ccross * Real.rpow (3 : ℝ) (2 * s * hNew)) := by
      simpa [hNew] using
        (coarseCaccioppoliBoundaryCrossCoeffOfHeight_sq
          (Q := Q) (a := a) (s := s) (C := Ccross) (uL2Sq := uL2Sq)
          (h := coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice
            Q a s t Calpha k)
          (ρ₁ := ρ₁) (ρ₂ := ρ₂) hs.le hu)
    have hpow_height :
        Real.rpow (3 : ℝ) (2 * s * hNew) = (6561 : ℝ) := by
      rw [hNew_eq]
      calc
        Real.rpow (3 : ℝ) (2 * s * (4 / s))
            = Real.rpow (3 : ℝ) (8 : ℝ) := by
              congr 1
              field_simp [hs.ne']
              ring
        _ = (6561 : ℝ) := by
              norm_num [Real.rpow_natCast]
    have hscalar :
        Ccross * Real.rpow (3 : ℝ) (2 * s * hNew) ≤
          (6561 : ℝ) * 6561 * Ccross *
            Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (2 * s) := by
      rw [hpow_height]
      nlinarith
    calc
      (coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s Ccross uL2Sq
          (coarseCaccioppoliBoundaryLocalizedExplicitHeightOfScaleChoice
            Q a s t Calpha k)
          ρ₁ ρ₂) ^ (2 : ℕ)
          =
        (Ccross * (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) *
            LambdaSq Q s (.finite 1) a * uL2Sq) *
          (Ccross * Real.rpow (3 : ℝ) (2 * s * hNew)) := hcross_sq
      _ ≤
        (Ccross * (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) *
            LambdaSq Q s (.finite 1) a * uL2Sq) *
          ((6561 : ℝ) * 6561 * Ccross *
            Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (2 * s)) := by
            exact mul_le_mul_of_nonneg_left hscalar hprefix_nonneg
      _ =
        ((6561 : ℝ) * 6561 * Ccross ^ (2 : ℕ) *
            LambdaSq Q s (.finite 1) a * uL2Sq) *
          ((coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) *
            Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (2 * s)) := by
            ring
      _ =
        ((6561 : ℝ) * 6561 * Ccross ^ (2 : ℕ) *
            LambdaSq Q s (.finite 1) a * uL2Sq) *
          Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (2 + 2 * s) := by
            rw [hgap_sq, hgap_exp]
      _ ≤
        ((6561 : ℝ) * 6561 * Ccross ^ (2 : ℕ) *
            LambdaSq Q s (.finite 1) a * uL2Sq) *
          Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (coarseCaccioppoliBeta s t) := by
            exact mul_le_mul_of_nonneg_left hgap_beta hfirst_nonneg
      _ =
        ((6561 : ℝ) * 6561 * Ccross ^ (2 : ℕ) *
            LambdaSq Q s (.finite 1) a * uL2Sq) *
          Real.rpow (ρ₂ - ρ₁) (-coarseCaccioppoliBeta s t) := by
            rw [coarseCaccioppoli_gapInv_rpow_eq]
      _ ≤
        coarseCaccioppoliBoundaryExplicitHeightRecursionRhsSplit
            Q a s t Calpha Ccross uL2Sq *
          Real.rpow (ρ₂ - ρ₁) (-coarseCaccioppoliBeta s t) := by
            unfold coarseCaccioppoliBoundaryExplicitHeightRecursionRhsSplit
            exact mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_right hsecond_nonneg)
              (Real.rpow_nonneg (sub_nonneg.mpr hlt.le) _)

end

end Homogenization
