/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.Pigeonhole.Assembly

/-! # Pigeonhole -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section54

/-!
# Pigeonhole lemma

This module is the public entry point for the first result of Section 5.4.
-/

noncomputable section

/-- Section 5.4 pigeonhole lemma for the annealed scalar contrast.  Either
there is a scale `n ∈ {h, ..., N}` at which both scalar chains are nearly
stationary across the gap `h`, or the contrast has already contracted by
`sigma`. -/
theorem pigeonhole_homogenizationScale
    {d : ℕ} [NeZero d] {P : Ch04.RestrictionCoeffLaw d}
    (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
    (hP4 : QuantitativeCoarseGrainedEllipticity P)
    {delta sigma : ℝ} (hdelta_pos : 0 < delta)
    (hdelta_le : delta ≤ 1 / 2)
    (hsigma_pos : 0 < sigma) (hsigma_le : sigma ≤ 1 / 2)
    {N h : ℕ}
    (hsep : (Nat.ceil (2 * delta⁻¹ * |Real.log sigma|)) * h ≤ N) :
    (∃ n : ℕ,
      h ≤ n ∧ n ≤ N ∧
      hP.barSigmaAtScale hStruct ((n - h : ℕ) : ℤ) ≤
        (1 + delta) * hP.barSigmaAtScale hStruct (n : ℤ) ∧
      (hP.barSigmaStarAtScale hStruct ((n - h : ℕ) : ℤ))⁻¹ ≤
        (1 + delta) *
          (hP.barSigmaStarAtScale hStruct (n : ℤ))⁻¹) ∨
    thetaAtScale hP hStruct (N : ℤ) ≤
      sigma * thetaAtScale hP hStruct 0 := by
  classical
  let k : ℕ := Nat.ceil (2 * delta⁻¹ * |Real.log sigma|)
  by_cases hh : h = 0
  · subst h
    left
    refine ⟨0, by simp, Nat.zero_le N, ?_, ?_⟩
    · have hfactor : (1 : ℝ) ≤ 1 + delta := by linarith
      have hnonneg : 0 ≤ hP.barSigmaAtScale hStruct (0 : ℤ) :=
        (Pigeonhole.barSigmaAtScale_pos_of_P4 hP hStruct hP4 0).le
      simpa using mul_le_mul_of_nonneg_right hfactor hnonneg
    · have hfactor : (1 : ℝ) ≤ 1 + delta := by linarith
      have hnonneg : 0 ≤ (hP.barSigmaStarAtScale hStruct (0 : ℤ))⁻¹ :=
        (Pigeonhole.barSigmaStarAtScale_inv_pos_of_P4 hP hStruct hP4 0).le
      simpa using mul_le_mul_of_nonneg_right hfactor hnonneg
  · by_cases hgood : ∃ n : ℕ,
        h ≤ n ∧ n ≤ N ∧
        hP.barSigmaAtScale hStruct ((n - h : ℕ) : ℤ) ≤
          (1 + delta) * hP.barSigmaAtScale hStruct (n : ℤ) ∧
        (hP.barSigmaStarAtScale hStruct ((n - h : ℕ) : ℤ))⁻¹ ≤
          (1 + delta) *
            (hP.barSigmaStarAtScale hStruct (n : ℤ))⁻¹
    · exact Or.inl hgood
    · right
      let a : ℕ → ℝ := fun m => hP.barSigmaAtScale hStruct (m : ℤ)
      let b : ℕ → ℝ := fun m => (hP.barSigmaStarAtScale hStruct (m : ℤ))⁻¹
      let A : ℕ → ℝ := fun j => a (j * h) * b (j * h)
      let r : ℝ := (1 + delta)⁻¹
      have hr_nonneg : 0 ≤ r := by dsimp [r]; positivity
      have hstep : ∀ j : ℕ, 1 ≤ j → j ≤ k → A j ≤ r * A (j - 1) := by
        intro j hj_pos hj_le
        have hprev_eq : j * h - h = (j - 1) * h := by
          cases j with
          | zero => omega
          | succ j => simp [Nat.succ_mul]
        have h_le_now : h ≤ j * h := by
          calc
            h = 1 * h := by simp
            _ ≤ j * h := Nat.mul_le_mul_right h hj_pos
        have hnow_le_kh : j * h ≤ k * h := Nat.mul_le_mul_right h hj_le
        have hnow_le_N : j * h ≤ N :=
          Nat.le_trans hnow_le_kh (by simpa [k] using hsep)
        have hbad_step : ¬
            (a ((j - 1) * h) ≤ (1 + delta) * a (j * h) ∧
              b ((j - 1) * h) ≤ (1 + delta) * b (j * h)) := by
          intro hpair
          apply hgood
          refine ⟨j * h, h_le_now, hnow_le_N, ?_, ?_⟩
          · simpa [a, hprev_eq] using hpair.1
          · simpa [b, hprev_eq] using hpair.2
        have hprev_le_now : (j - 1) * h ≤ j * h :=
          Nat.mul_le_mul_right h (Nat.sub_le j 1)
        have hchain := Pigeonhole.scalarChain_of_P4 hP hStruct hP4 hprev_le_now
        have ha_mono : a (j * h) ≤ a ((j - 1) * h) := by
          simpa [a] using hchain.2.2
        have hb_mono : b (j * h) ≤ b ((j - 1) * h) := by
          simpa [b] using hchain.2.1
        have ha_now_nonneg : 0 ≤ a (j * h) :=
          (Pigeonhole.barSigmaAtScale_pos_of_P4 hP hStruct hP4 (j * h)).le
        have hb_now_nonneg : 0 ≤ b (j * h) :=
          (Pigeonhole.barSigmaStarAtScale_inv_pos_of_P4 hP hStruct hP4 (j * h)).le
        simpa [A, a, b, r] using
          Pigeonhole.product_step_le_inv_mul_of_not_good hdelta_pos
            ha_now_nonneg hb_now_nonneg ha_mono hb_mono hbad_step
      have hgeom : A k ≤ r ^ k * A 0 :=
        Pigeonhole.iterate_le_geometric_of_step hr_nonneg k hstep
      have hchainN :=
        Pigeonhole.scalarChain_of_P4 hP hStruct hP4 (by simpa [k] using hsep)
      have hthetaN_le_Ak : thetaAtScale hP hStruct (N : ℤ) ≤ A k := by
        have ha_mono :
            hP.barSigmaAtScale hStruct (N : ℤ) ≤
              hP.barSigmaAtScale hStruct ((k * h : ℕ) : ℤ) := by
          simpa using hchainN.2.2
        have hb_mono :
            (hP.barSigmaStarAtScale hStruct (N : ℤ))⁻¹ ≤
              (hP.barSigmaStarAtScale hStruct ((k * h : ℕ) : ℤ))⁻¹ := by
          simpa using hchainN.2.1
        have hbN_nonneg : 0 ≤ (hP.barSigmaStarAtScale hStruct (N : ℤ))⁻¹ :=
          (Pigeonhole.barSigmaStarAtScale_inv_pos_of_P4 hP hStruct hP4 N).le
        have haK_nonneg : 0 ≤ hP.barSigmaAtScale hStruct ((k * h : ℕ) : ℤ) :=
          (Pigeonhole.barSigmaAtScale_pos_of_P4 hP hStruct hP4 (k * h)).le
        have hprod := mul_le_mul ha_mono hb_mono hbN_nonneg haK_nonneg
        simpa [thetaAtScale, Ch04.RestrictionLawCarrier.thetaAtScale, A, a, b] using hprod
      have hA0_nonneg : 0 ≤ A 0 := by
        have ha0 := Pigeonhole.barSigmaAtScale_pos_of_P4 hP hStruct hP4 0
        have hb0 := Pigeonhole.barSigmaStarAtScale_inv_pos_of_P4 hP hStruct hP4 0
        simpa [A, a, b] using (mul_pos ha0 hb0).le
      have hsigma_le_one : sigma ≤ 1 := by linarith
      have htail : r ^ k ≤ sigma := by
        simpa [r, k] using
          Pigeonhole.inv_one_add_delta_pow_natCeil_two_delta_inv_abs_log_le
            hdelta_pos hdelta_le hsigma_pos hsigma_le_one
      have hAk_le_sigma : A k ≤ sigma * A 0 := by
        calc
          A k ≤ r ^ k * A 0 := hgeom
          _ ≤ sigma * A 0 := mul_le_mul_of_nonneg_right htail hA0_nonneg
      calc
        thetaAtScale hP hStruct (N : ℤ) ≤ A k := hthetaN_le_Ak
        _ ≤ sigma * A 0 := hAk_le_sigma
        _ = sigma * thetaAtScale hP hStruct 0 := by
          simp [A, a, b, thetaAtScale, Ch04.RestrictionLawCarrier.thetaAtScale]

end

end Section54
end Ch05
end Book
end Homogenization
