/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.CrossTerm.Scalar

/-! # Explicit Height -/

namespace Homogenization

/-!
# Coarse Caccioppoli cross term: explicit height
-/

noncomputable section

open scoped BigOperators

/-- The interior note-specific cross-term bound currently follows from the same
stronger triadic-scale estimate as the boundary version. -/
theorem coarseCaccioppoli_interior_noteCrossTermBound_of_triadicGapScaleChoice
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (h : ℝ → ℝ → ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        ∃ k : ℕ, CoarseCaccioppoliTriadicGapScaleChoice k ρ₁ ρ₂ ∧
          C * Real.rpow (3 : ℝ) (2 * s * h ρ₁ ρ₂) ≤
            Real.rpow
                (C / (s * (1 - s)) *
                  Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ))
                (coarseCaccioppoliPower s t) *
              Real.rpow (((3 : ℝ) ^ k) / 81) (coarseCaccioppoliPower s t)) :
    CoarseCaccioppoliInteriorNoteCrossTermBound Q a s t C uL2Sq h := by
  exact coarseCaccioppoli_boundary_noteCrossTermBound_of_triadicGapScaleChoice
    Q a s t C uL2Sq h hC hs ht hst hu hscale

/-- The note's actual explicit height choice `h = max {k + 4, ceil(...)}` gives
an honest pre-Besov cross-term square bound with a split recursive prefactor:
one branch comes from `k + 4`, the other from the logarithmic ceiling. -/
theorem coarseCaccioppoli_boundary_noteCrossTermBound_of_explicitHeightOfScaleChoice
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s t C uL2Sq : ℝ)
    (k : ℝ → ℝ → ℕ)
    (hC : 0 ≤ C) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hu : 0 ≤ uL2Sq)
    (hscale :
      ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
        CoarseCaccioppoliTriadicGapScaleChoice (k ρ₁ ρ₂) ρ₁ ρ₂) :
    ∀ ⦃ρ₁ ρ₂ : ℝ⦄, (1 / 3 : ℝ) ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ ≤ 1 →
      (coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s C uL2Sq
          (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k) ρ₁ ρ₂) ^ (2 : ℕ) ≤
        coarseCaccioppoliBoundaryExplicitHeightRecursionRhs Q a s t C uL2Sq *
          Real.rpow (ρ₂ - ρ₁) (-coarseCaccioppoliBeta s t) := by
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  let k0 : ℕ := k ρ₁ ρ₂
  let h0 : ℝ := coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k ρ₁ ρ₂
  let p : ℝ := coarseCaccioppoliPower s t
  let M : ℝ := C / (s * (1 - s)) * Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ)
  have hs1 : s < 1 := by linarith
  have hp_nonneg : 0 ≤ p := coarseCaccioppoli_power_nonneg hs hst
  have hden_nonneg : 0 ≤ s * (1 - s) := mul_one_sub_nonneg hs.le hs1.le
  have htheta_nonneg : 0 ≤ ThetaRatio Q s t a :=
    thetaRatio_nonneg Q s t a hs.le ht.le
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg
      (div_nonneg hC hden_nonneg)
      (Real.rpow_nonneg htheta_nonneg _)
  have hkchoice : CoarseCaccioppoliTriadicGapScaleChoice k0 ρ₁ ρ₂ :=
    hscale hρ₁ hlt hρ₂
  have hLambda_nonneg : 0 ≤ LambdaSq Q s (.finite 1) a :=
    multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs.le
  have hgap_nonneg : 0 ≤ coarseCaccioppoliGapInv ρ₁ ρ₂ :=
    coarseCaccioppoliGapInv_nonneg hlt
  have hgap_pos : 0 < coarseCaccioppoliGapInv ρ₁ ρ₂ := by
    rw [coarseCaccioppoliGapInv_eq_inv]
    exact inv_pos.mpr (sub_pos.mpr hlt)
  have hgap_ge_one : 1 ≤ coarseCaccioppoliGapInv ρ₁ ρ₂ := by
    have hthree_halves : (3 / 2 : ℝ) ≤ coarseCaccioppoliGapInv ρ₁ ρ₂ :=
      coarseCaccioppoliGapInv_ge_three_halves hρ₁ hlt hρ₂
    linarith
  have hcross_sq :
      (coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s C uL2Sq
          (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k) ρ₁ ρ₂) ^ (2 : ℕ) =
        (C * (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) *
          LambdaSq Q s (.finite 1) a * uL2Sq) *
          (C * Real.rpow (3 : ℝ) (2 * s * h0)) := by
    simpa [h0] using
      (coarseCaccioppoliBoundaryCrossCoeffOfHeight_sq
        (Q := Q) (a := a) (s := s) (C := C) (uL2Sq := uL2Sq)
        (h := coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k)
        (ρ₁ := ρ₁) (ρ₂ := ρ₂) hs.le hu)
  have hprefix_nonneg :
      0 ≤ C * (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) *
        LambdaSq Q s (.finite 1) a * uL2Sq := by
    refine mul_nonneg (mul_nonneg ?_ hLambda_nonneg) hu
    exact mul_nonneg hC (sq_nonneg _)
  have hgap_sq :
      (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) =
        Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (2 : ℝ) := by
    symm
    exact Real.rpow_natCast _ 2
  have hrec_nonneg :
      0 ≤ coarseCaccioppoliBoundaryRecursionRhs Q a s t C uL2Sq := by
    unfold coarseCaccioppoliBoundaryRecursionRhs
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hM_nonneg _)) hLambda_nonneg)
      hu
  have hfirst_nonneg :
      0 ≤ (6561 : ℝ) * 6561 * C ^ (2 : ℕ) * LambdaSq Q s (.finite 1) a * uL2Sq := by
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
  by_cases hbranch :
      (((Nat.ceil
          (Real.log (coarseCaccioppoliBoundaryHeightLogArg Q a s t C k0) /
            (coarseCaccioppoliSigma s t * Real.log (3 : ℝ)))) : ℕ) : ℝ) ≤ (k0 : ℝ) + 4
  · have hh0 :
        h0 = (k0 : ℝ) + 4 := by
      dsimp [h0, k0, coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice,
        coarseCaccioppoliBoundaryExplicitHeightAtScale]
      rw [max_eq_left hbranch]
    have hscalar :
        C * Real.rpow (3 : ℝ) (2 * s * h0) ≤
          (6561 : ℝ) * 6561 * C *
            Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (2 * s) := by
      rw [hh0]
      exact coarseCaccioppoli_boundary_explicitHeight_leftBranch_scalar
        hC hs hs1 hkchoice hlt
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
    calc
      (coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s C uL2Sq
          (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k) ρ₁ ρ₂) ^ (2 : ℕ)
          = (C * (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) *
              LambdaSq Q s (.finite 1) a * uL2Sq) *
              (C * Real.rpow (3 : ℝ) (2 * s * h0)) := by
                simpa [h0] using hcross_sq
      _ ≤ (C * (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) *
            LambdaSq Q s (.finite 1) a * uL2Sq) *
            ((6561 : ℝ) * 6561 * C *
              Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (2 * s)) := by
              exact mul_le_mul_of_nonneg_left hscalar hprefix_nonneg
      _ = ((6561 : ℝ) * 6561 * C ^ (2 : ℕ) *
            LambdaSq Q s (.finite 1) a * uL2Sq) *
            ((coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) *
              Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (2 * s)) := by
              ring
      _ = ((6561 : ℝ) * 6561 * C ^ (2 : ℕ) *
            LambdaSq Q s (.finite 1) a * uL2Sq) *
            Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (2 + 2 * s) := by
              rw [hgap_sq, hgap_exp]
      _ ≤ ((6561 : ℝ) * 6561 * C ^ (2 : ℕ) *
            LambdaSq Q s (.finite 1) a * uL2Sq) *
            Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (coarseCaccioppoliBeta s t) := by
              exact mul_le_mul_of_nonneg_left hgap_beta hfirst_nonneg
      _ = ((6561 : ℝ) * 6561 * C ^ (2 : ℕ) *
            LambdaSq Q s (.finite 1) a * uL2Sq) *
            Real.rpow (ρ₂ - ρ₁) (-coarseCaccioppoliBeta s t) := by
              rw [coarseCaccioppoli_gapInv_rpow_eq]
      _ ≤ coarseCaccioppoliBoundaryExplicitHeightRecursionRhs Q a s t C uL2Sq *
            Real.rpow (ρ₂ - ρ₁) (-coarseCaccioppoliBeta s t) := by
              unfold coarseCaccioppoliBoundaryExplicitHeightRecursionRhs
              exact mul_le_mul_of_nonneg_right
                (le_add_of_nonneg_right hsecond_nonneg)
                (Real.rpow_nonneg (sub_nonneg.mpr hlt.le) _)
  · have hbranch' :
        (k0 : ℝ) + 4 <
          (((Nat.ceil
            (Real.log (coarseCaccioppoliBoundaryHeightLogArg Q a s t C k0) /
              (coarseCaccioppoliSigma s t * Real.log (3 : ℝ)))) : ℕ) : ℝ) := by
      exact lt_of_not_ge hbranch
    have hh0 :
        h0 =
          (((Nat.ceil
            (Real.log (coarseCaccioppoliBoundaryHeightLogArg Q a s t C k0) /
              (coarseCaccioppoliSigma s t * Real.log (3 : ℝ)))) : ℕ) : ℝ) := by
      dsimp [h0, k0, coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice,
        coarseCaccioppoliBoundaryExplicitHeightAtScale]
      rw [max_eq_right hbranch'.le]
    have hscalar :
        C * Real.rpow (3 : ℝ) (2 * s * h0) ≤
          ((9 : ℝ) * Real.rpow (4 : ℝ) p * Real.rpow (81 : ℝ) p) * C *
            Real.rpow M p *
            Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) p := by
      rw [hh0]
      simpa [k0, p, M] using
        coarseCaccioppoli_boundary_explicitHeight_rightBranch_scalar
          Q a hC hs ht hst hkchoice hlt hbranch'
    have hgap_exp :
        Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (2 : ℝ) *
            Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) p =
          Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (coarseCaccioppoliBeta s t) := by
      rw [coarseCaccioppoli_beta_eq_two_add_power hst]
      simpa using
        (Real.rpow_add hgap_pos (2 : ℝ) p).symm
    calc
      (coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s C uL2Sq
          (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t C k) ρ₁ ρ₂) ^ (2 : ℕ)
          = (C * (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) *
              LambdaSq Q s (.finite 1) a * uL2Sq) *
              (C * Real.rpow (3 : ℝ) (2 * s * h0)) := by
                simpa [h0] using hcross_sq
      _ ≤ (C * (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) *
            LambdaSq Q s (.finite 1) a * uL2Sq) *
            (((9 : ℝ) * Real.rpow (4 : ℝ) p * Real.rpow (81 : ℝ) p) * C *
              Real.rpow M p *
              Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) p) := by
              exact mul_le_mul_of_nonneg_left hscalar hprefix_nonneg
      _ = (((9 : ℝ) * Real.rpow (4 : ℝ) p * Real.rpow (81 : ℝ) p) * C *
            coarseCaccioppoliBoundaryRecursionRhs Q a s t C uL2Sq) *
            ((coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) *
              Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) p) := by
              unfold coarseCaccioppoliBoundaryRecursionRhs
              ring
      _ = (((9 : ℝ) * Real.rpow (4 : ℝ) p * Real.rpow (81 : ℝ) p) * C *
            coarseCaccioppoliBoundaryRecursionRhs Q a s t C uL2Sq) *
            Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (coarseCaccioppoliBeta s t) := by
              rw [hgap_sq, hgap_exp]
      _ = (((9 : ℝ) * Real.rpow (4 : ℝ) p * Real.rpow (81 : ℝ) p) * C *
            coarseCaccioppoliBoundaryRecursionRhs Q a s t C uL2Sq) *
            Real.rpow (ρ₂ - ρ₁) (-coarseCaccioppoliBeta s t) := by
              rw [coarseCaccioppoli_gapInv_rpow_eq]
      _ ≤ coarseCaccioppoliBoundaryExplicitHeightRecursionRhs Q a s t C uL2Sq *
            Real.rpow (ρ₂ - ρ₁) (-coarseCaccioppoliBeta s t) := by
              unfold coarseCaccioppoliBoundaryExplicitHeightRecursionRhs
              exact mul_le_mul_of_nonneg_right
                (le_add_of_nonneg_left hfirst_nonneg)
                (Real.rpow_nonneg (sub_nonneg.mpr hlt.le) _)

theorem coarseCaccioppoli_boundary_noteCrossTermBoundSplit_of_explicitHeightOfScaleChoice
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
          (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice
            Q a s t Calpha k) ρ₁ ρ₂) ^ (2 : ℕ) ≤
        coarseCaccioppoliBoundaryExplicitHeightRecursionRhsSplit
            Q a s t Calpha Ccross uL2Sq *
          Real.rpow (ρ₂ - ρ₁) (-coarseCaccioppoliBeta s t) := by
  intro ρ₁ ρ₂ hρ₁ hlt hρ₂
  let k0 : ℕ := k ρ₁ ρ₂
  let h0 : ℝ :=
    coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice Q a s t Calpha k ρ₁ ρ₂
  let p : ℝ := coarseCaccioppoliPower s t
  let M : ℝ :=
    Calpha / (s * (1 - s)) * Real.rpow (ThetaRatio Q s t a) (1 / 2 : ℝ)
  have hs1 : s < 1 := by linarith
  have hp_nonneg : 0 ≤ p := coarseCaccioppoli_power_nonneg hs hst
  have hden_nonneg : 0 ≤ s * (1 - s) := mul_one_sub_nonneg hs.le hs1.le
  have htheta_nonneg : 0 ≤ ThetaRatio Q s t a :=
    thetaRatio_nonneg Q s t a hs.le ht.le
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg
      (div_nonneg hCalpha.le hden_nonneg)
      (Real.rpow_nonneg htheta_nonneg _)
  have hkchoice : CoarseCaccioppoliTriadicGapScaleChoice k0 ρ₁ ρ₂ :=
    hscale hρ₁ hlt hρ₂
  have hLambda_nonneg : 0 ≤ LambdaSq Q s (.finite 1) a :=
    multiscale_ellipticity_LambdaSq_one_nonneg Q s a hs.le
  have hgap_pos : 0 < coarseCaccioppoliGapInv ρ₁ ρ₂ := by
    rw [coarseCaccioppoliGapInv_eq_inv]
    exact inv_pos.mpr (sub_pos.mpr hlt)
  have hgap_ge_one : 1 ≤ coarseCaccioppoliGapInv ρ₁ ρ₂ := by
    have hthree_halves : (3 / 2 : ℝ) ≤ coarseCaccioppoliGapInv ρ₁ ρ₂ :=
      coarseCaccioppoliGapInv_ge_three_halves hρ₁ hlt hρ₂
    linarith
  have hcross_sq :
      (coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s Ccross uL2Sq
          (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice
            Q a s t Calpha k) ρ₁ ρ₂) ^ (2 : ℕ) =
        (Ccross * (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) *
          LambdaSq Q s (.finite 1) a * uL2Sq) *
          (Ccross * Real.rpow (3 : ℝ) (2 * s * h0)) := by
    simpa [h0] using
      (coarseCaccioppoliBoundaryCrossCoeffOfHeight_sq
        (Q := Q) (a := a) (s := s) (C := Ccross) (uL2Sq := uL2Sq)
        (h := coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice
          Q a s t Calpha k)
        (ρ₁ := ρ₁) (ρ₂ := ρ₂) hs.le hu)
  have hprefix_nonneg :
      0 ≤ Ccross * (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) *
        LambdaSq Q s (.finite 1) a * uL2Sq := by
    refine mul_nonneg (mul_nonneg ?_ hLambda_nonneg) hu
    exact mul_nonneg hCcross (sq_nonneg _)
  have hgap_sq :
      (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) =
        Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (2 : ℝ) := by
    symm
    exact Real.rpow_natCast _ 2
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
  by_cases hbranch :
      (((Nat.ceil
          (Real.log (coarseCaccioppoliBoundaryHeightLogArg Q a s t Calpha k0) /
            (coarseCaccioppoliSigma s t * Real.log (3 : ℝ)))) : ℕ) : ℝ) ≤
        (k0 : ℝ) + 4
  · have hh0 :
        h0 = (k0 : ℝ) + 4 := by
      dsimp [h0, k0, coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice,
        coarseCaccioppoliBoundaryExplicitHeightAtScale]
      rw [max_eq_left hbranch]
    have hscalar :
        Ccross * Real.rpow (3 : ℝ) (2 * s * h0) ≤
          (6561 : ℝ) * 6561 * Ccross *
            Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (2 * s) := by
      rw [hh0]
      exact coarseCaccioppoli_boundary_explicitHeight_leftBranch_scalar
        hCcross hs hs1 hkchoice hlt
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
    calc
      (coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s Ccross uL2Sq
          (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice
            Q a s t Calpha k) ρ₁ ρ₂) ^ (2 : ℕ)
          = (Ccross * (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) *
              LambdaSq Q s (.finite 1) a * uL2Sq) *
              (Ccross * Real.rpow (3 : ℝ) (2 * s * h0)) := by
                simpa [h0] using hcross_sq
      _ ≤ (Ccross * (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) *
            LambdaSq Q s (.finite 1) a * uL2Sq) *
            ((6561 : ℝ) * 6561 * Ccross *
              Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (2 * s)) := by
              exact mul_le_mul_of_nonneg_left hscalar hprefix_nonneg
      _ = ((6561 : ℝ) * 6561 * Ccross ^ (2 : ℕ) *
            LambdaSq Q s (.finite 1) a * uL2Sq) *
            ((coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) *
              Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (2 * s)) := by
              ring
      _ = ((6561 : ℝ) * 6561 * Ccross ^ (2 : ℕ) *
            LambdaSq Q s (.finite 1) a * uL2Sq) *
            Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (2 + 2 * s) := by
              rw [hgap_sq, hgap_exp]
      _ ≤ ((6561 : ℝ) * 6561 * Ccross ^ (2 : ℕ) *
            LambdaSq Q s (.finite 1) a * uL2Sq) *
            Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (coarseCaccioppoliBeta s t) := by
              exact mul_le_mul_of_nonneg_left hgap_beta hfirst_nonneg
      _ = ((6561 : ℝ) * 6561 * Ccross ^ (2 : ℕ) *
            LambdaSq Q s (.finite 1) a * uL2Sq) *
            Real.rpow (ρ₂ - ρ₁) (-coarseCaccioppoliBeta s t) := by
              rw [coarseCaccioppoli_gapInv_rpow_eq]
      _ ≤ coarseCaccioppoliBoundaryExplicitHeightRecursionRhsSplit
              Q a s t Calpha Ccross uL2Sq *
            Real.rpow (ρ₂ - ρ₁) (-coarseCaccioppoliBeta s t) := by
              unfold coarseCaccioppoliBoundaryExplicitHeightRecursionRhsSplit
              exact mul_le_mul_of_nonneg_right
                (le_add_of_nonneg_right hsecond_nonneg)
                (Real.rpow_nonneg (sub_nonneg.mpr hlt.le) _)
  · have hbranch' :
        (k0 : ℝ) + 4 <
          (((Nat.ceil
            (Real.log (coarseCaccioppoliBoundaryHeightLogArg Q a s t Calpha k0) /
              (coarseCaccioppoliSigma s t * Real.log (3 : ℝ)))) : ℕ) : ℝ) := by
      exact lt_of_not_ge hbranch
    have hh0 :
        h0 =
          (((Nat.ceil
            (Real.log (coarseCaccioppoliBoundaryHeightLogArg Q a s t Calpha k0) /
              (coarseCaccioppoliSigma s t * Real.log (3 : ℝ)))) : ℕ) : ℝ) := by
      dsimp [h0, k0, coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice,
        coarseCaccioppoliBoundaryExplicitHeightAtScale]
      rw [max_eq_right hbranch'.le]
    have hscalar :
        Ccross * Real.rpow (3 : ℝ) (2 * s * h0) ≤
          ((9 : ℝ) * Real.rpow (4 : ℝ) p * Real.rpow (81 : ℝ) p) *
            Ccross * Real.rpow M p *
            Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) p := by
      rw [hh0]
      simpa [k0, p, M] using
        coarseCaccioppoli_boundary_explicitHeight_rightBranch_scalar_with_front
          Q a hCalpha hCcross hs ht hst hkchoice hlt hbranch'
    have hgap_exp :
        Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (2 : ℝ) *
            Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) p =
          Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (coarseCaccioppoliBeta s t) := by
      rw [coarseCaccioppoli_beta_eq_two_add_power hst]
      simpa using
        (Real.rpow_add hgap_pos (2 : ℝ) p).symm
    calc
      (coarseCaccioppoliBoundaryCrossCoeffOfHeight Q a s Ccross uL2Sq
          (coarseCaccioppoliBoundaryExplicitHeightOfScaleChoice
            Q a s t Calpha k) ρ₁ ρ₂) ^ (2 : ℕ)
          = (Ccross * (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) *
              LambdaSq Q s (.finite 1) a * uL2Sq) *
              (Ccross * Real.rpow (3 : ℝ) (2 * s * h0)) := by
                simpa [h0] using hcross_sq
      _ ≤ (Ccross * (coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) *
            LambdaSq Q s (.finite 1) a * uL2Sq) *
            (((9 : ℝ) * Real.rpow (4 : ℝ) p * Real.rpow (81 : ℝ) p) *
              Ccross * Real.rpow M p *
              Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) p) := by
              exact mul_le_mul_of_nonneg_left hscalar hprefix_nonneg
      _ = (((9 : ℝ) * Real.rpow (4 : ℝ) p * Real.rpow (81 : ℝ) p) *
            Ccross *
            coarseCaccioppoliBoundaryRecursionRhsSplit
              Q a s t Calpha Ccross uL2Sq) *
            ((coarseCaccioppoliGapInv ρ₁ ρ₂) ^ (2 : ℕ) *
              Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) p) := by
              unfold coarseCaccioppoliBoundaryRecursionRhsSplit
              ring
      _ = (((9 : ℝ) * Real.rpow (4 : ℝ) p * Real.rpow (81 : ℝ) p) *
            Ccross *
            coarseCaccioppoliBoundaryRecursionRhsSplit
              Q a s t Calpha Ccross uL2Sq) *
            Real.rpow (coarseCaccioppoliGapInv ρ₁ ρ₂) (coarseCaccioppoliBeta s t) := by
              rw [hgap_sq, hgap_exp]
      _ = (((9 : ℝ) * Real.rpow (4 : ℝ) p * Real.rpow (81 : ℝ) p) *
            Ccross *
            coarseCaccioppoliBoundaryRecursionRhsSplit
              Q a s t Calpha Ccross uL2Sq) *
            Real.rpow (ρ₂ - ρ₁) (-coarseCaccioppoliBeta s t) := by
              rw [coarseCaccioppoli_gapInv_rpow_eq]
      _ ≤ coarseCaccioppoliBoundaryExplicitHeightRecursionRhsSplit
              Q a s t Calpha Ccross uL2Sq *
            Real.rpow (ρ₂ - ρ₁) (-coarseCaccioppoliBeta s t) := by
              unfold coarseCaccioppoliBoundaryExplicitHeightRecursionRhsSplit
              exact mul_le_mul_of_nonneg_right
                (le_add_of_nonneg_left hfirst_nonneg)
                (Real.rpow_nonneg (sub_nonneg.mpr hlt.le) _)

end

end Homogenization
