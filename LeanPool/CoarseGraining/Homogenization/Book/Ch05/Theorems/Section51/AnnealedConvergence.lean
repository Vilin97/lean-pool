/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section51.ExponentAbsorption
public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section56.SmallContrastAlgebraicDecay

/-! # Annealed Convergence -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section51

open MeasureTheory
open Section53.JUpperBoundCoarseFluctuations
open scoped Matrix.Norms.Elementwise

noncomputable section

/-!
# Theorem `t.annealed.convergence`

The main theorem combines the perturbative entry mechanism with the
small-contrast algebraic iteration, applied after shifting the `(P4)` exponents
by the Section 5.3 fluctuation buffer.
-/

private def unitCoordinateVector {d : ℕ} [NeZero d] : Vec d :=
  Pi.single (0 : Fin d) 1

private theorem unitCoordinateVector_vecNormSq {d : ℕ} [NeZero d] :
    vecNormSq (unitCoordinateVector : Vec d) = 1 := by
  rw [unitCoordinateVector, vecNormSq, vecDot, Finset.sum_eq_single (0 : Fin d)]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

/-- Theorem `t.annealed.convergence`: convergence of the annealed contrast.

The constants are selected from the quantitative ellipticity parameter record
before the probability law, hence are independent of the law itself. -/
theorem annealedConvergence_homogenizationScale
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
      (hP : Ch04.RestrictionLawCarrier P)
      (hStruct : Ch04.RestrictionStructuralLaw P)
      (hP4 : QuantitativeCoarseGrainedEllipticity P),
      hP4.params = params →
      ∀ n : ℕ,
        thetaAtScale hP hStruct
          ((annealedAlgebraicEntryScale P hP4 C + n : ℕ) : ℤ) ≤
            1 + Real.rpow (3 : ℝ) (-α * (n : ℝ)) := by
  classical
  obtain ⟨αsc, δ0, K, hαsc_pos, hδ0_pos, hK_pos, hsmallContrast⟩ :=
    Section56.SmallContrastAlgebraicDecay.smallContrastAlgebraicDecay_homogenizationScale
      (twoBetaShiftedParams params)
  let δ : ℝ := min δ0 (1 / 4)
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact lt_min hδ0_pos (by norm_num)
  have hδ_le_δ0 : δ ≤ δ0 := by dsimp [δ]; exact min_le_left _ _
  have hδ_le_quarter : δ ≤ 1 / 4 := by dsimp [δ]; exact min_le_right _ _
  obtain ⟨Centry, hCentry_pos, hentry⟩ :=
    shiftedSmallContrastEntry_homogenizationScale params hδ_pos
  let R : ℕ :=
    Nat.ceil (Real.log (max (4 * K) 1) / ((αsc / 2) * Real.log 3))
  let α : ℝ := min (αsc / 2) (((R + 1 : ℕ) : ℝ)⁻¹)
  have hα_pos : 0 < α := by
    dsimp [α]
    exact lt_min (by positivity) (by positivity)
  refine ⟨Centry, α, hCentry_pos, hα_pos, ?_⟩
  intro P hP hStruct hP4 hparams n

  -- Enter the small-contrast regime for the shifted exponents at `N`.
  let N : ℕ := annealedAlgebraicEntryScale P hP4 Centry
  let PN : Ch04.RestrictionCoeffLaw d := Ch04.restrictionScaleNormalizedLaw N P
  let hPN : Ch04.RestrictionLawCarrier PN := hP.scaleNormalized N
  let hStructN : Ch04.RestrictionStructuralLaw PN := hStruct.scaleNormalized N
  let hP4N : QuantitativeCoarseGrainedEllipticity PN :=
    hP4.scaleNormalized hP hStruct N
  let hP4S : QuantitativeCoarseGrainedEllipticity PN :=
    twoBetaShiftedP4 hPN hStructN hP4N
  have hentryN :
      Section55.shiftedWidetildeThetaAtScale P (N : ℤ) hP4
          (2 * section53CoarseFluctuationBeta hP4) - 1 ≤ δ := by
    have h := hentry hP hStruct hP4 hparams
    simpa [N] using h
  have hwide_eq :
      widetildeThetaAtScale PN (0 : ℤ) hP4S =
        Section55.shiftedWidetildeThetaAtScale P (N : ℤ) hP4
          (2 * section53CoarseFluctuationBeta hP4) := by
    simpa [PN, hPN, hStructN, hP4N, hP4S] using
      widetildeThetaAtScale_zero_scaleNormalized_twoBetaShiftedP4
        hP hStruct hP4 N
  have hsmall0_delta :
      widetildeThetaAtScale PN (0 : ℤ) hP4S - 1 ≤ δ := by
    calc
      widetildeThetaAtScale PN (0 : ℤ) hP4S - 1 =
          Section55.shiftedWidetildeThetaAtScale P (N : ℤ) hP4
            (2 * section53CoarseFluctuationBeta hP4) - 1 := by
            rw [hwide_eq]
      _ ≤ δ := hentryN
  have hsmall0_δ0 :
      widetildeThetaAtScale PN (0 : ℤ) hP4S - 1 ≤ δ0 :=
    hsmall0_delta.trans hδ_le_δ0
  have hsmall0_quarter :
      widetildeThetaAtScale PN (0 : ℤ) hP4S - 1 ≤ 1 / 4 :=
    hsmall0_delta.trans hδ_le_quarter
  have hP4N_params : hP4N.params = params := by
    simpa [hP4N, QuantitativeCoarseGrainedEllipticity.scaleNormalized] using! hparams
  have hparamsS : hP4S.params = twoBetaShiftedParams params := by
    calc
      hP4S.params = twoBetaShiftedParams hP4N.params := by
        simp [hP4S]
      _ = twoBetaShiftedParams params := by rw [hP4N_params]

  -- Apply the Section 5.6 small-contrast theorem to the dilated law.
  have htheta_sub_quarter :
      thetaAtScale hPN hStructN (n : ℤ) - 1 ≤ 1 / 4 := by
    have htheta_delta :
        thetaAtScale hPN hStructN (n : ℤ) - 1 ≤ δ :=
      Section56.SmallContrastAlgebraicDecay.thetaAtScale_sub_one_le_delta_of_widetildeThetaAtScale_zero_sub_one_le_delta
          hPN hStructN hP4S hsmall0_delta n
    exact htheta_delta.trans hδ_le_quarter
  have hwide_two : widetildeThetaAtScale PN (0 : ℤ) hP4S ≤ 2 := by
    linarith
  let e : Vec d := unitCoordinateVector
  have he : vecNormSq e = 1 := by
    simpa [e] using unitCoordinateVector_vecNormSq (d := d)
  have hJ_upper := hsmallContrast hPN hStructN hP4S hparamsS hsmall0_δ0 n e he
  have hJ_lower :=
    Section56.expectedResponseJCubeSet_special_ge_quarter_theta_sub_one
      hPN hStructN hP4S hwide_two n e he
  have htheta_sub_decay :
      thetaAtScale hPN hStructN (n : ℤ) - 1 ≤
        4 * K * Real.rpow (3 : ℝ) (-αsc * (n : ℝ)) := by
    dsimp only at hJ_upper hJ_lower
    nlinarith

  -- Shrink the exponent so the displayed estimate has unit prefactor.
  have htheta_sub_unit_decay :
      thetaAtScale hPN hStructN (n : ℤ) - 1 ≤
        Real.rpow (3 : ℝ) (-α * (n : ℝ)) := by
    by_cases hnR : n ≤ R
    · have hα_le_inv : α ≤ (((R + 1 : ℕ) : ℝ)⁻¹) := by
        dsimp [α]
        exact min_le_right _ _
      have hαn : α * (n : ℝ) ≤ 1 :=
        mul_nat_le_one_of_le_inverse_succ hα_le_inv hnR
      exact htheta_sub_quarter.trans
        (quarter_le_rpow_three_neg_mul_of_mul_nat_le_one hαn)
    · have hR_lt_n : R < n := Nat.lt_of_not_ge hnR
      have hlarge :
          Real.log (max (4 * K) 1) / ((αsc / 2) * Real.log 3) ≤ (n : ℝ) := by
        have hceil :
            Real.log (max (4 * K) 1) / ((αsc / 2) * Real.log 3) ≤ (R : ℝ) := by
          simpa [R] using
            Nat.le_ceil
              (Real.log (max (4 * K) 1) / ((αsc / 2) * Real.log 3))
        exact hceil.trans (by exact_mod_cast (Nat.le_of_lt hR_lt_n))
      have hpref :
          4 * K * Real.rpow (3 : ℝ) (-αsc * (n : ℝ)) ≤
            Real.rpow (3 : ℝ) (-(αsc / 2) * (n : ℝ)) :=
        prefactor_decay_le_half_exponent_decay_of_large
          (α₀ := αsc) (K := K) hαsc_pos hlarge
      have hhalf_to_alpha :
          Real.rpow (3 : ℝ) (-(αsc / 2) * (n : ℝ)) ≤
            Real.rpow (3 : ℝ) (-α * (n : ℝ)) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) ?_
        have hα_le_half : α ≤ αsc / 2 := by
          dsimp [α]
          exact min_le_left _ _
        have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
        nlinarith
      exact htheta_sub_decay.trans (hpref.trans hhalf_to_alpha)
  have hthetaN :
      thetaAtScale hPN hStructN (n : ℤ) ≤
        1 + Real.rpow (3 : ℝ) (-α * (n : ℝ)) := by
    linarith

  -- Undo the scale normalization.
  have hscale :
      thetaAtScale hPN hStructN (n : ℤ) =
        thetaAtScale hP hStruct ((N + n : ℕ) : ℤ) := by
    dsimp [thetaAtScale, hPN, hStructN]
    exact hP.thetaAtScale_restrictionScaleNormalizedLaw hStruct N n
  have htarget_eq :
      thetaAtScale hP hStruct
          ((annealedAlgebraicEntryScale P hP4 Centry + n : ℕ) : ℤ) =
        thetaAtScale hPN hStructN (n : ℤ) := by
    simpa [N] using hscale.symm
  rw [htarget_eq]
  exact hthetaN

end

end Section51
end Ch05
end Book
end Homogenization
