/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section56.SmallContrastAlgebraicDecay.Iteration

/-! # Final -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section56

open MeasureTheory
open scoped BigOperators Matrix.Norms.Elementwise Matrix.Norms.L2Operator

noncomputable section

namespace SmallContrastAlgebraicDecay

open Section53.JUpperBoundCoarseFluctuations

/-!
# Proposition `p.small.contrast.algebraic.decay.homogenization.scale`
-/

/-- Proposition `p.small.contrast.algebraic.decay.homogenization.scale`.

The constants are selected from the parameter record before the probability
law, so they are independent of the measure. -/
theorem smallContrastAlgebraicDecay_homogenizationScale
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ α δ0 C : ℝ, 0 < α ∧ 0 < δ0 ∧ 0 < C ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
      (hP : Ch04.RestrictionLawCarrier P)
      (hStruct : Ch04.RestrictionStructuralLaw P)
      (hP4 : QuantitativeCoarseGrainedEllipticity P),
      hP4.params = params →
      widetildeThetaAtScale P (0 : ℤ) hP4 - 1 ≤ δ0 →
      ∀ m : ℕ, ∀ e : Vec d, vecNormSq e = 1 →
        let p_e := specialPAtScale hP hStruct (m : ℤ) e
        let q_e := specialQAtScale hP hStruct (m : ℤ) e
        Ch04.expectedResponseJCubeSet P (originCube d (m : ℤ)) p_e q_e ≤
          C * Real.rpow (3 : ℝ) (-α * (m : ℝ)) := by
  rcases scalar_contraction_recursion_from_assembly params with
    ⟨Cgap, θ, hCgap_pos, hθ_pos, hθ_lt_one, hscalar⟩
  let L : ℕ := Nat.ceil Cgap + 1
  have hceil_pos : 0 < Nat.ceil Cgap := by
    have hceil_ge : Cgap ≤ (Nat.ceil Cgap : ℝ) := Nat.le_ceil Cgap
    have hceil_real_pos : (0 : ℝ) < (Nat.ceil Cgap : ℝ) :=
      lt_of_lt_of_le hCgap_pos hceil_ge
    exact_mod_cast hceil_real_pos
  have hL_pos : 0 < L := by dsimp [L]; omega
  have hL_ge_two : 2 ≤ L := by dsimp [L]; omega
  have hCgap_le_L : Cgap ≤ (L : ℝ) := by
    have hceil_ge : Cgap ≤ (Nat.ceil Cgap : ℝ) := Nat.le_ceil Cgap
    have hceil_le_L : (Nat.ceil Cgap : ℝ) ≤ (L : ℝ) := by
      dsimp [L]
      exact_mod_cast Nat.le_succ (Nat.ceil Cgap)
    exact hceil_ge.trans hceil_le_L
  let βp : ℝ := section53CoarseFluctuationBetaParams params
  have hβp_pos : 0 < βp := by
    dsimp [βp]
    exact section53CoarseFluctuationBetaParams_pos params
  let α0 : ℝ := min βp (1 / 16 : ℝ)
  have hα0_pos : 0 < α0 := lt_min hβp_pos (by norm_num)
  have hα0_le_βp : α0 ≤ βp := min_le_left _ _
  have hα0_le_sixteen : α0 ≤ (1 / 16 : ℝ) := min_le_right _ _
  obtain ⟨α, δseq, K, hα_pos, hδseq_pos, hK_pos, hseq⟩ :=
    algebraic_decay_of_threeQuarter_recursion
      hL_pos hθ_pos hθ_lt_one hα0_pos (by norm_num : 0 ≤ (2 : ℝ))
  let δ0 : ℝ := min 1 δseq
  have hδ0_pos : 0 < δ0 := by
    dsimp [δ0]
    exact lt_min zero_lt_one hδseq_pos
  have hδ0_le_one : δ0 ≤ 1 := by dsimp [δ0]; exact min_le_left _ _
  have hδ0_le_seq : δ0 ≤ δseq := by dsimp [δ0]; exact min_le_right _ _
  refine ⟨α, δ0, K, hα_pos, hδ0_pos, hK_pos, ?_⟩
  intro P hP hStruct hP4 hparams hsmall0 m e he
  dsimp only
  let F : ℕ → ℝ := fun n => thetaAtScale hP hStruct (n : ℤ) - 1
  have hsmall_two : widetildeThetaAtScale P (0 : ℤ) hP4 ≤ 2 :=
    widetildeThetaAtScale_zero_le_two_of_sub_one_le_delta
      hδ0_le_one hsmall0
  have hF_nonneg : ∀ n, 0 ≤ F n := by
    intro n
    dsimp [F]
    exact thetaAtScale_sub_one_nonneg hP hStruct hP4 n
  have hF_small : ∀ n, F n ≤ δseq := by
    intro n
    have hleδ0 :
        F n ≤ δ0 := by
      dsimp [F]
      exact
        thetaAtScale_sub_one_le_delta_of_widetildeThetaAtScale_zero_sub_one_le_delta
          hP hStruct hP4 hsmall0 n
    exact hleδ0.trans hδ0_le_seq
  have hrec :
      ∀ n, 8 * L + 4 ≤ n →
        F n ≤ θ * F (n - L) + (F (threeQuarterScale n)) ^ (2 : ℕ) +
          2 * Real.rpow (3 : ℝ) (-α0 * (n : ℝ)) := by
    intro n hnlarge
    let ell : ℕ := threeQuarterScale n
    let k : ℕ := n - L
    have hwindow := lagged_scale_window hL_pos hnlarge
    have hellk : ell < k := by simpa [ell, k] using hwindow.1
    have hkn : k < n := by simpa [k] using hwindow.2.1
    have hgap : Cgap ≤ ((n - k : ℕ) : ℝ) := by
      have hL_le_gap : (L : ℝ) ≤ ((n - k : ℕ) : ℝ) := by
        exact_mod_cast hwindow.2.2.1
      exact hCgap_le_L.trans hL_le_gap
    have hβ_eq : section53CoarseFluctuationBeta hP4 = βp := by
      rw [← section53CoarseFluctuationBetaParams_eq_of_P4 hP4, hparams]
    have hscalar_n := hscalar hP hStruct hP4 hparams hsmall_two e he
      (ell := ell) (k := k) (m := n) hellk hkn hgap
    have htail_le :
        Real.rpow (3 : ℝ) (-(section53CoarseFluctuationBeta hP4) * (n : ℝ)) ≤
          Real.rpow (3 : ℝ) (-α0 * (n : ℝ)) := by
      rw [hβ_eq]
      exact Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : ℝ) ≤ 3) (by nlinarith)
    have hgeom_le :
        Real.rpow (3 : ℝ) (-(d : ℝ) * ((k - ell : ℕ) : ℝ)) ≤
          Real.rpow (3 : ℝ) (-α0 * (n : ℝ)) := by
      have hd_ge_one : (1 : ℝ) ≤ (d : ℝ) := by
        have hd_nat : 1 ≤ d := le_trans (by norm_num : 1 ≤ 2) params.two_le_dim
        exact_mod_cast hd_nat
      have hn_ge_sixteen : 16 ≤ n := by nlinarith [hL_ge_two, hnlarge]
      have hfloor :
          (n : ℝ) / 16 ≤ ((n / 8 : ℕ) : ℝ) :=
        scale_div_sixteen_le_nat_div_eight_cast hn_ge_sixteen
      have hgap_floor : ((n / 8 : ℕ) : ℝ) ≤ ((k - ell : ℕ) : ℝ) := by
        exact_mod_cast hwindow.2.2.2
      have hexponent :
          -(d : ℝ) * ((k - ell : ℕ) : ℝ) ≤ -α0 * (n : ℝ) := by
        have hmain : α0 * (n : ℝ) ≤ (d : ℝ) * ((k - ell : ℕ) : ℝ) := by
          calc
            α0 * (n : ℝ) ≤ (1 / 16 : ℝ) * (n : ℝ) :=
              mul_le_mul_of_nonneg_right hα0_le_sixteen (by positivity)
            _ = (n : ℝ) / 16 := by ring
            _ ≤ ((n / 8 : ℕ) : ℝ) := hfloor
            _ ≤ ((k - ell : ℕ) : ℝ) := hgap_floor
            _ ≤ (d : ℝ) * ((k - ell : ℕ) : ℝ) := by
              exact le_mul_of_one_le_left (by positivity) hd_ge_one
        nlinarith
      exact Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : ℝ) ≤ 3) hexponent
    calc
      F n ≤ θ * F k +
          Real.rpow (3 : ℝ) (-(section53CoarseFluctuationBeta hP4) * (n : ℝ)) +
            Real.rpow (3 : ℝ) (-(d : ℝ) * ((k - ell : ℕ) : ℝ)) +
              (F ell) ^ (2 : ℕ) := by
            simpa [F, ell, k] using hscalar_n
      _ ≤ θ * F k + Real.rpow (3 : ℝ) (-α0 * (n : ℝ)) +
            Real.rpow (3 : ℝ) (-α0 * (n : ℝ)) + (F ell) ^ (2 : ℕ) := by
            gcongr
      _ = θ * F (n - L) + (F (threeQuarterScale n)) ^ (2 : ℕ) +
            2 * Real.rpow (3 : ℝ) (-α0 * (n : ℝ)) := by
            dsimp [ell, k]
            ring
  have hF_decay := hseq F hF_nonneg hF_small hrec m
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  have hJ_le_F :
      Ch04.expectedResponseJCubeSet P (originCube d (m : ℤ)) p_e q_e ≤ F m := by
    dsimp [F, p_e, q_e]
    simpa [p_e, q_e] using
      expectedResponseJCubeSet_special_le_thetaAtScale_sub_one_of_vecNormSq_eq_one
        hP hStruct hP4 m e he
  exact hJ_le_F.trans hF_decay

end SmallContrastAlgebraicDecay

end

end Section56
end Ch05
end Book
end Homogenization
