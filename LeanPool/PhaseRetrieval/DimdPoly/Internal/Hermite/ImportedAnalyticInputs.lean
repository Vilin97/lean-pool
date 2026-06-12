/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
/-
  # ImportedAnalyticInputs.lean
  Black-box analytic inputs reused from the verified Fock-space development.

  Scaffolding notes: `Imported/analytic_inputs.md`
-/
import LeanPool.PhaseRetrieval.DimdPoly.Internal.Hermite.Definitions
import LeanPool.PhaseRetrieval.Constant.Internal.LocalCircleEstimate
import LeanPool.PhaseRetrieval.Constant.Internal.HighFreqBandEstimate

/-! # ImportedAnalyticInputs -/


open Complex MeasureTheory Real Finset
open scoped BigOperators

noncomputable section

namespace HermiteLEAN

-- to_mathlib: Mathlib/Algebra/BigOperators/Intervals
/-- Reindex a finite sum over `Icc N (N + L - 1)` to `Fin L`. -/
private theorem sum_Icc_eq_sum_Fin {α : Type*} [AddCommMonoid α]
    (N L : ℕ) (hL : 1 ≤ L) (f : ℕ → α) :
    ∑ n ∈ Finset.Icc N (N + L - 1), f n =
      ∑ m : Fin L, f (N + m.val) := by
  symm
  apply Finset.sum_nbij (fun (m : Fin L) => N + m.val)
  · intro m _
    exact Finset.mem_Icc.mpr ⟨Nat.le_add_right N m.val, by omega⟩
  · intro a _ b _ hab
    exact Fin.ext (Nat.add_left_cancel hab)
  · intro n hn
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
    refine ⟨⟨n - N, by omega⟩, Finset.mem_univ _, ?_⟩
    change N + (n - N) = n
    omega
  · intro _ _
    rfl

/-- Imported theorem A: local circle estimate for positive frequencies. -/
theorem local_circle_estimate
    (E : Finset ℕ)
    (hpos : ∀ n ∈ E, 1 ≤ n)
    (c : ℕ → ℂ) :
    circleL2Sq (positiveTrigonometricPolynomial E c)
      ≤ 144 * E.card * circleRhoNormSq (positiveTrigonometricPolynomial E c) := by
  by_cases hE0 : E.card = 0
  · have hE_empty : E = ∅ := Finset.card_eq_zero.mp hE0
    simp [circleL2Sq, circleRhoNormSq, positiveTrigonometricPolynomial, hE_empty, rho]
  · have hcard : 1 ≤ E.card := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hE0)
    have h := FockSPR.local_circle_estimate (L := E.card) hcard rfl hpos c
        (positiveTrigonometricPolynomial E c) rfl
    simp only [T, FockSPR.T, circleL2Sq, circleRhoNormSq, positiveTrigonometricPolynomial,
      FockSPR.circleNormSq, rho, FockSPR.rho, sq_abs] at h ⊢
    exact h

/-- Imported theorem B: high-frequency circle estimate. -/
theorem high_frequency_circle_estimate
    (N L : ℕ)
    (hN : 1 ≤ N)
    (hL : 1 ≤ L)
    (c : ℕ → ℂ)
    (hband : 1343 * (L : ℝ) ^ 2 ≤ (N : ℝ) ^ 2) :
    circleL2Sq (positiveTrigonometricPolynomial (frequencyBand N L) c)
      ≤ 32 * circleRhoNormSq (positiveTrigonometricPolynomial (frequencyBand N L) c) := by
  have hband_nat : 1343 * L ^ 2 ≤ N ^ 2 := by
    exact_mod_cast hband
  have hpoly :
      positiveTrigonometricPolynomial (frequencyBand N L) c =
        fun t => ∑ m : Fin L, c (N + m.val) * fourier ((N + m.val : ℕ) : ℤ) t := by
    ext t
    rw [positiveTrigonometricPolynomial, frequencyBand, sum_Icc_eq_sum_Fin N L hL]
  have h := FockSPR.high_freq_band_estimate hN hL hband_nat (fun m => c (N + m.val))
      (positiveTrigonometricPolynomial (frequencyBand N L) c) hpoly
  simp only [T, FockSPR.T, circleL2Sq, circleRhoNormSq, positiveTrigonometricPolynomial,
    frequencyBand, FockSPR.circleNormSq, rho, FockSPR.rho, sq_abs] at h ⊢
  exact h

/-- Imported theorem C: phase-normalized orthogonal reduction. -/
theorem phase_normalized_orthogonal_reduction
    {H : Type*}
    [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    (defect : H → ℝ)
    (hdefect_nonneg : ∀ h : H, 0 ≤ defect h)
    (f0 : H)
    (hf0 : ‖f0‖ = 1)
    (C : ℝ)
    (hC : 0 < C)
    (horth : ∀ g : H, inner ℂ g f0 = (0 : ℂ) → ‖g‖ ≤ C * defect g)
    (hscalar :
      ∀ h : H, (inner ℂ h f0).im = 0 →
        |(2 : ℝ) * (inner ℂ h f0).re + ‖h‖ ^ 2| ≤ defect h * (2 + ‖h‖))
    (hcompare :
      ∀ h : H, ∀ a : ℝ, defect (h - (a : ℂ) • f0) ≤ |a| + defect h) :
    ∃ δ Mloc : ℝ, 0 < δ ∧ 0 < Mloc ∧
      ∀ h : H, ‖h‖ ≤ δ → (inner ℂ h f0).im = 0 → ‖h‖ ≤ Mloc * defect h := by
  /-
  Scaffolding guidance:
  - this is the reusable phase-normalized local reduction step;
  - the orthogonal coercivity hypothesis is passed in as `horth`;
  - `hscalar` and `hcompare` package the two modulus estimates coming from the
    underlying `L²` embedding in the scaffolding-note proof;
  - the conclusion is local in `h`, with the phase normalization encoded by
    `(inner h f0).im = 0`.
  -/
  refine ⟨1 / (C + 1), 5 * C + 3, ?_, ?_, ?_⟩
  · have hCp1 : 0 < C + 1 := by linarith
    exact one_div_pos.mpr hCp1
  · nlinarith
  · intro h hhδ him
    set a : ℝ := (inner ℂ h f0).re
    set g : H := h - (a : ℂ) • f0
    have hinner_real : inner ℂ h f0 = (a : ℂ) := by
      apply Complex.ext <;> simp [a, him]
    have hf0_inner : inner ℂ f0 f0 = (1 : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K, hf0]
      simp
    have hsmul : inner ℂ ((a : ℂ) • f0) f0 = (a : ℂ) := by
      rw [inner_smul_left, hf0_inner]
      simp
    have hgorth : inner ℂ g f0 = (0 : ℂ) := by
      dsimp [g]
      rw [inner_sub_left, hinner_real]
      exact sub_eq_zero.mpr hsmul.symm
    have hg_bound : ‖g‖ ≤ C * (|a| + defect h) := by
      have h1 : ‖g‖ ≤ C * defect g := horth g hgorth
      have h2 : C * defect g ≤ C * (|a| + defect h) := by
        exact mul_le_mul_of_nonneg_left (hcompare h a) (le_of_lt hC)
      exact h1.trans h2
    have hscalar_h := hscalar h him
    have htwoa : 2 * |a| ≤ defect h * (2 + ‖h‖) + ‖h‖ ^ 2 := by
      have htri :
          2 * |a| ≤ |(2 : ℝ) * a + ‖h‖ ^ 2| + ‖h‖ ^ 2 := by
        have hnorm0 := norm_add_le ((2 : ℝ) * a + ‖h‖ ^ 2) (-‖h‖ ^ 2)
        have hnorm1 :
            |(2 : ℝ) * a + ‖h‖ ^ 2 + -‖h‖ ^ 2| ≤
              |(2 : ℝ) * a + ‖h‖ ^ 2| + ‖h‖ ^ 2 := by
          simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖h‖)] using
            hnorm0
        have hnorm2 : |(2 : ℝ) * a| ≤ |(2 : ℝ) * a + ‖h‖ ^ 2| + ‖h‖ ^ 2 := by
          simpa [show (2 : ℝ) * a + ‖h‖ ^ 2 + -‖h‖ ^ 2 = (2 : ℝ) * a by ring] using
            hnorm1
        simpa [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using hnorm2
      exact htri.trans (by nlinarith)
    have ha_bound : |a| ≤ (defect h * (2 + ‖h‖) + ‖h‖ ^ 2) / 2 := by
      nlinarith
    have hg_add : g + (a : ℂ) • f0 = h := by
      simp [g]
    have hsplit : ‖h‖ ≤ ‖g‖ + |a| := by
      calc
        ‖h‖ = ‖g + (a : ℂ) • f0‖ := by rw [← hg_add]
        _ ≤ ‖g‖ + ‖(a : ℂ) • f0‖ := norm_add_le _ _
        _ = ‖g‖ + |a| := by simp [norm_smul, hf0, Real.norm_eq_abs]
    have hh_main : ‖h‖ ≤ (C + 1) * |a| + C * defect h := by
      nlinarith
    have hδ_le_one : (1 / (C + 1 : ℝ)) ≤ 1 := by
      have hCp1 : 0 < C + 1 := by linarith
      rw [div_le_iff₀ hCp1]
      nlinarith
    have hx_le_one : ‖h‖ ≤ 1 := hhδ.trans hδ_le_one
    have ha_simple : |a| ≤ (3 : ℝ) / 2 * defect h + ‖h‖ ^ 2 / 2 := by
      nlinarith [ha_bound, hx_le_one, hdefect_nonneg h]
    have hh_quad :
        ‖h‖ ≤ ((5 * C + 3) / 2) * defect h + ((C + 1) / 2) * ‖h‖ ^ 2 := by
      nlinarith [hh_main, ha_simple, hdefect_nonneg h, hC]
    have hx_sq : ‖h‖ ^ 2 ≤ (1 / (C + 1 : ℝ)) * ‖h‖ := by
      nlinarith [hhδ, norm_nonneg h]
    have hCp1_nonneg : 0 ≤ C + 1 := by linarith
    have hx_sq' : (C + 1) * ‖h‖ ^ 2 ≤ ‖h‖ := by
      calc
        (C + 1) * ‖h‖ ^ 2 ≤ (C + 1) * ((1 / (C + 1 : ℝ)) * ‖h‖) :=
          mul_le_mul_of_nonneg_left hx_sq hCp1_nonneg
        _ = ‖h‖ := by
          field_simp [show (C + 1 : ℝ) ≠ 0 by linarith]
    have habsorb : ((C + 1) / 2) * ‖h‖ ^ 2 ≤ ‖h‖ / 2 := by
      have hhalf := mul_le_mul_of_nonneg_right hx_sq' (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hhalf
    have hh_half : ‖h‖ ≤ ((5 * C + 3) / 2) * defect h + ‖h‖ / 2 := by
      exact hh_quad.trans <|
        by simpa [add_assoc, add_left_comm, add_comm] using
          add_le_add_left habsorb (((5 * C + 3) / 2) * defect h)
    have hh_final : ‖h‖ / 2 ≤ ((5 * C + 3) / 2) * defect h := by
      nlinarith [hh_half]
    nlinarith [hh_final, hdefect_nonneg h]

end HermiteLEAN
