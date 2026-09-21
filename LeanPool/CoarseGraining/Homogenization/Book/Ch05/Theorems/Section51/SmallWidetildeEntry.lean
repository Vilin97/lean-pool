/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section51.ShiftedP4
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section55.ShiftedWidetildeTheta.Final

/-! # Small Widetilde Entry -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section51

open Section53.JUpperBoundCoarseFluctuations
open MeasureTheory
open scoped Matrix.Norms.Elementwise

noncomputable section

/-!
# Entry into shifted small contrast

This file combines the Section 5.5 perturbative entry theorem with the shifted
high-moment localization estimate to produce small contrast for the `2β`
shifted `(P4)` data at the algebraic entry scale.
-/

private theorem rpow_three_neg_mul_antitone_nat
    {β : ℝ} (hβ : 0 < β) {h l : ℕ} (hl : h ≤ l) :
    Real.rpow (3 : ℝ) (-β * (l : ℝ)) ≤
      Real.rpow (3 : ℝ) (-β * (h : ℝ)) := by
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) ?_
  have hcast : (h : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  nlinarith

private theorem rpow_three_neg_mul_le_inv_of_log_gap
    {β A : ℝ} {h : ℕ} (hβ : 0 < β) (hA : 1 ≤ A)
    (hh : (β * Real.log 3)⁻¹ * Real.log A ≤ (h : ℝ)) :
    Real.rpow (3 : ℝ) (-β * (h : ℝ)) ≤ A⁻¹ := by
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hβlog : 0 < β * Real.log 3 := mul_pos hβ hlog3
  have hA_pos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hlogA_nonneg : 0 ≤ Real.log A := Real.log_nonneg hA
  have hmain : Real.log A ≤ β * Real.log 3 * (h : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hh hβlog.le
    have hcancel : β * Real.log 3 * ((β * Real.log 3)⁻¹ * Real.log A) =
        Real.log A := by
      field_simp [hβlog.ne']
    nlinarith
  have hexp :
      Real.log (3 : ℝ) * (-β * (h : ℝ)) ≤ -Real.log A := by
    nlinarith
  calc
    Real.rpow (3 : ℝ) (-β * (h : ℝ)) =
        Real.exp (Real.log (3 : ℝ) * (-β * (h : ℝ))) := by
        simpa using
          (Real.rpow_def_of_pos (x := (3 : ℝ))
            (y := -β * (h : ℝ)) (by norm_num : 0 < (3 : ℝ)))
    _ ≤ Real.exp (-Real.log A) := Real.exp_le_exp.mpr hexp
    _ = A⁻¹ := by
        rw [Real.exp_neg, Real.exp_log hA_pos]

private theorem shifted_tail_le_half_delta
    {β Cshift δ W : ℝ} {h : ℕ}
    (hβ : 0 < β) (hCshift : 0 ≤ Cshift) (hδ : 0 < δ) (hW : 0 ≤ W)
    (hh :
      (β * Real.log 3)⁻¹ *
          Real.log (2 + (2 * (Cshift + 1) / δ) * W) ≤ (h : ℝ)) :
    Cshift * Real.rpow (3 : ℝ) (-β * (h : ℝ)) * W ≤ δ / 2 := by
  let A : ℝ := 2 + (2 * (Cshift + 1) / δ) * W
  have hcoef_pos : 0 < 2 * (Cshift + 1) / δ := by
    positivity
  have hA_ge_one : 1 ≤ A := by
    dsimp [A]
    have hprod : 0 ≤ (2 * (Cshift + 1) / δ) * W := by positivity
    nlinarith
  have hdecay : Real.rpow (3 : ℝ) (-β * (h : ℝ)) ≤ A⁻¹ := by
    exact rpow_three_neg_mul_le_inv_of_log_gap hβ hA_ge_one (by simpa [A] using hh)
  have hden_pos : 0 < A := lt_of_lt_of_le zero_lt_one hA_ge_one
  have hmain :
      Cshift * A⁻¹ * W ≤ δ / 2 := by
    by_cases hWzero : W = 0
    · simpa [hWzero] using (show (0 : ℝ) ≤ δ / 2 by positivity)
    · have hW_pos : 0 < W := lt_of_le_of_ne hW (Ne.symm hWzero)
      have hA_lower :
          (2 * (Cshift + 1) / δ) * W ≤ A := by
        dsimp [A]
        nlinarith
      have h_inv_le :
          A⁻¹ ≤ ((2 * (Cshift + 1) / δ) * W)⁻¹ := by
        exact (inv_le_inv₀ hden_pos (mul_pos hcoef_pos hW_pos)).mpr hA_lower
      calc
        Cshift * A⁻¹ * W ≤
            Cshift * (((2 * (Cshift + 1) / δ) * W)⁻¹) * W := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left h_inv_le hCshift) hW
        _ = Cshift / (2 * (Cshift + 1) / δ) := by
              field_simp [hδ.ne', hW_pos.ne']
        _ ≤ δ / 2 := by
              rw [div_le_iff₀ hcoef_pos]
              have hmul :
                  δ / 2 * (2 * (Cshift + 1) / δ) = Cshift + 1 := by
                field_simp [hδ.ne']
              nlinarith
  calc
    Cshift * Real.rpow (3 : ℝ) (-β * (h : ℝ)) * W
        ≤ Cshift * A⁻¹ * W := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hdecay hCshift) hW
    _ ≤ δ / 2 := hmain

/-- Section 5.1 entry into the small-contrast regime for the `2β`-shifted
ellipticity exponents.

The constant is selected before the law.  The target smallness parameter is
explicit so the final theorem can feed in the small-contrast threshold from
Section 5.6. -/
theorem shiftedSmallContrastEntry_homogenizationScale
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d)
    {delta : ℝ} (hdelta_pos : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
      (_hP : Ch04.RestrictionLawCarrier P) (_hStruct : Ch04.RestrictionStructuralLaw P)
      (hP4 : QuantitativeCoarseGrainedEllipticity P),
      hP4.params = params →
        let N := annealedAlgebraicEntryScale P hP4 C
        Section55.shiftedWidetildeThetaAtScale P (N : ℤ) hP4
            (2 * section53CoarseFluctuationBeta hP4) - 1 ≤ delta := by
  classical
  obtain ⟨Centry, hCentry_pos, hentry⟩ :=
    Section55.annealedPerturbativeEntry_homogenizationScale params
  let β : ℝ := section53CoarseFluctuationBetaParams params
  have hβ_pos : 0 < β := by
    simpa [β] using section53CoarseFluctuationBetaParams_pos params
  obtain ⟨Cshift, hCshift_nonneg, hshift⟩ :=
    Section55.shiftedWidetildeThetaBound_homogenizationScale
      (d := d) params.xi β hβ_pos
  let sigma : ℝ := min (delta / 2) (1 / 2)
  have hsigma_pos : 0 < sigma := by
    dsimp [sigma]
    exact lt_min (by positivity) (by norm_num)
  have hsigma_le_half : sigma ≤ 1 / 2 := by
    dsimp [sigma]
    exact min_le_right _ _
  have hsigma_le_delta_half : sigma ≤ delta / 2 := by
    dsimp [sigma]
    exact min_le_left _ _
  let Acoef : ℝ := Centry * sigma⁻¹ ^ (4 : ℕ) * |Real.log sigma|
  let Aarg : ℝ := sigma⁻¹ ^ (4 : ℕ)
  let Bcoef : ℝ := (β * Real.log 3)⁻¹
  let Barg : ℝ := 2 * (Cshift + 1) / delta
  let C : ℝ := max (Centry + 4)
    (max Aarg (max Barg (max (Acoef + Bcoef + 4) 1)))
  have hC_pos : 0 < C := by
    have hC_ge_one : (1 : ℝ) ≤ C := by
      dsimp [C]
      exact
        (le_max_right (Acoef + Bcoef + 4) 1).trans
          ((le_max_right Barg (max (Acoef + Bcoef + 4) 1)).trans
            ((le_max_right Aarg (max Barg (max (Acoef + Bcoef + 4) 1))).trans
              (le_max_right (Centry + 4)
                (max Aarg (max Barg (max (Acoef + Bcoef + 4) 1))))))
    exact lt_of_lt_of_le zero_lt_one hC_ge_one
  refine ⟨C, hC_pos, ?_⟩
  intro P hP hStruct hP4 hparams
  let W : ℝ := widetildeThetaAtScale P (0 : ℤ) hP4
  let N : ℕ := annealedAlgebraicEntryScale P hP4 C
  let k : ℕ := annealedEntryScale P hP4 Centry sigma
  let htail : ℕ := Nat.ceil (Bcoef * Real.log (2 + Barg * W))
  have hW_nonneg : 0 ≤ W := by
    dsimp [W]
    exact widetildeThetaAtScale_nonneg P hP4 0
  have hxi_eq : hP4.xi = params.xi := by
    rw [← hparams]
    rfl
  have hβ_eq : section53CoarseFluctuationBeta hP4 = β := by
    rw [← section53CoarseFluctuationBetaParams_eq_of_P4 hP4, hparams]
  have htheta_k :
      thetaAtScale hP hStruct (k : ℤ) ≤ 1 + sigma := by
    simpa [k] using hentry hP hStruct hP4 hparams sigma hsigma_pos hsigma_le_half
  have hC_ge_Centry4 : Centry + 4 ≤ C := by
    dsimp [C]
    exact le_max_left _ _
  have hC_ge_Aarg : Aarg ≤ C := by
    dsimp [C]
    exact (le_max_left Aarg (max Barg (max (Acoef + Bcoef + 4) 1))).trans
      (le_max_right (Centry + 4)
        (max Aarg (max Barg (max (Acoef + Bcoef + 4) 1))))
  have hC_ge_Barg : Barg ≤ C := by
    dsimp [C]
    exact
      (le_max_left Barg (max (Acoef + Bcoef + 4) 1)).trans
        ((le_max_right Aarg (max Barg (max (Acoef + Bcoef + 4) 1))).trans
          (le_max_right (Centry + 4)
            (max Aarg (max Barg (max (Acoef + Bcoef + 4) 1)))))
  have hC_ge_sum : Acoef + Bcoef + 4 ≤ C := by
    dsimp [C]
    exact
      (le_max_left (Acoef + Bcoef + 4) 1).trans
        ((le_max_right Barg (max (Acoef + Bcoef + 4) 1)).trans
          ((le_max_right Aarg (max Barg (max (Acoef + Bcoef + 4) 1))).trans
            (le_max_right (Centry + 4)
              (max Aarg (max Barg (max (Acoef + Bcoef + 4) 1))))))
  have hAcoef_nonneg : 0 ≤ Acoef := by
    dsimp [Acoef]
    positivity
  have hAarg_nonneg : 0 ≤ Aarg := by
    dsimp [Aarg]
    positivity
  have hBcoef_nonneg : 0 ≤ Bcoef := by
    dsimp [Bcoef]
    positivity
  have hBarg_nonneg : 0 ≤ Barg := by
    dsimp [Barg]
    positivity
  let kEntry : ℕ := annealedConvergenceEntryScaleBound P hP4 Centry
  let kTail : ℕ := annealedConvergenceSigmaTailScale P hP4 Centry sigma
  let NEntry : ℕ := Nat.ceil (C * (Real.log (2 + W)) ^ (2 : ℕ))
  let NTail : ℕ := Nat.ceil (C * (hP4.xi : ℝ) *
    Real.log (2 + C * (hP4.xi : ℝ) * W))
  have hk_decomp : k = kEntry + kTail := by
    dsimp [k, kEntry, kTail, annealedEntryScale]
  have hN_decomp : N = NEntry + NTail := by
    dsimp [N, NEntry, NTail, annealedAlgebraicEntryScale, W]
  have hkEntry_le_NEntry : kEntry ≤ NEntry := by
    have h :=
      natCeil_add_nat_le_natCeil_mul_logSq
        (A := Centry) (C := C) (T := W) (R := 0)
        hW_nonneg hCentry_pos.le (by simpa using hC_ge_Centry4)
    simpa [kEntry, NEntry, annealedConvergenceEntryScaleBound, W] using h
  have hkTail_htail_le_NTail : kTail + htail ≤ NTail := by
    have hxi_ge_one : (1 : ℝ) ≤ (hP4.xi : ℝ) := by
      have htwo : 2 ≤ hP4.xi := hP4.two_le_xi
      exact_mod_cast (show (1 : ℕ) ≤ hP4.xi by omega)
    have h :=
      natCeil_two_log_terms_le_natCeil_large_log
        (Acoef := Acoef) (Aarg := Aarg) (Bcoef := Bcoef)
        (Barg := Barg) (C := C) (xi := (hP4.xi : ℝ)) (T := W)
        hW_nonneg hxi_ge_one hAcoef_nonneg hAarg_nonneg hBcoef_nonneg
        hBarg_nonneg hC_ge_Aarg hC_ge_Barg hC_ge_sum
    have hkTail_eq :
        kTail =
          Nat.ceil (Acoef * (hP4.xi : ℝ) *
            Real.log (2 + Aarg * (hP4.xi : ℝ) * W)) := by
      dsimp [kTail, annealedConvergenceSigmaTailScale, Acoef, Aarg, W]
      congr 1
      ring
    rw [hkTail_eq]
    simpa [htail, NTail, Bcoef, Barg, hxi_eq, W] using h
  have hk_htail_le_N : k + htail ≤ N := by
    rw [hk_decomp, hN_decomp]
    omega
  have hk_le_N : k ≤ N := le_trans (Nat.le_add_right k htail) hk_htail_le_N
  have htail_le_gap : htail ≤ N - k := by
    exact Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using hk_htail_le_N)
  have hshiftN := hshift hP hStruct hP4 hxi_eq hβ_eq hk_le_N
  have hceil_tail :
      Bcoef * Real.log (2 + Barg * W) ≤ (htail : ℝ) := by
    simpa [htail] using Nat.le_ceil (Bcoef * Real.log (2 + Barg * W))
  have htail_decay :
      Cshift *
          Real.rpow (3 : ℝ) (-β * ((N - k : ℕ) : ℝ)) *
          W ≤ delta / 2 := by
    have hdecay_le :
        Real.rpow (3 : ℝ) (-β * ((N - k : ℕ) : ℝ)) ≤
          Real.rpow (3 : ℝ) (-β * (htail : ℝ)) :=
      rpow_three_neg_mul_antitone_nat hβ_pos htail_le_gap
    calc
      Cshift * Real.rpow (3 : ℝ) (-β * ((N - k : ℕ) : ℝ)) * W
          ≤ Cshift * Real.rpow (3 : ℝ) (-β * (htail : ℝ)) * W := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hdecay_le hCshift_nonneg) hW_nonneg
      _ ≤ delta / 2 := by
            exact shifted_tail_le_half_delta hβ_pos hCshift_nonneg hdelta_pos
              hW_nonneg (by simpa [Bcoef, Barg] using hceil_tail)
  calc
    Section55.shiftedWidetildeThetaAtScale P (N : ℤ) hP4
          (2 * section53CoarseFluctuationBeta hP4) - 1
        ≤ (thetaAtScale hP hStruct (k : ℤ) +
            Cshift * Real.rpow (3 : ℝ) (-β * ((N - k : ℕ) : ℝ)) *
              W) - 1 := by
            have hupper :
                Section55.shiftedWidetildeThetaAtScale P (N : ℤ) hP4
                    (2 * section53CoarseFluctuationBeta hP4) ≤
                  thetaAtScale hP hStruct (k : ℤ) +
                    Cshift * Real.rpow (3 : ℝ) (-β * ((N - k : ℕ) : ℝ)) * W := by
              simpa [hβ_eq, W] using hshiftN.2
            linarith
    _ ≤ (1 + sigma + delta / 2) - 1 := by
            nlinarith
    _ ≤ delta := by
            nlinarith

end

end Section51
end Ch05
end Book
end Homogenization
