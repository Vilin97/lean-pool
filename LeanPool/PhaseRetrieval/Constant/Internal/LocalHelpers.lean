/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
/-
  # LocalHelpers.lean
  Helper lemmas for the local phase-aligned Fock-space phase retrieval estimate.

  The public entry point is `Local.lean`. This file contains the technical phase
  alignment argument used to pass from the real-anchored local theorem in
  `LocalCore.lean` to an existential unit-phase formulation.
-/
import LeanPool.PhaseRetrieval.Constant.Internal.LocalCore

/-! # LocalHelpers -/


open FockSPR MeasureTheory Complex Real Polynomial Finset
open scoped ENNReal ComplexConjugate

noncomputable section

namespace FockSPR

/-- Gaussian `L²` distance from `1 + p` to the unit phase `lam`. -/
def phaseDistanceSq (p : Polynomial ℂ) (lam : ℂ) : ℝ :=
  ∫ z : ℂ, ‖(1 : ℂ) + p.eval z - lam‖ ^ 2 * Real.exp (-‖z‖ ^ 2)

/-- Normalized Gaussian `L²` distance from `1 + p` to the unit phase `lam`. -/
def phaseDistanceSqNorm (p : Polynomial ℂ) (lam : ℂ) : ℝ :=
  (1 / Real.pi) * phaseDistanceSq p lam

private def phaseAnchor (w : ℂ) : ℂ :=
  if _hw : w = 0 then 1 else w / ‖w‖

private lemma norm_phaseAnchor (w : ℂ) : ‖phaseAnchor w‖ = 1 := by
  by_cases hw : w = 0
  · simp [phaseAnchor, hw]
  · rw [phaseAnchor, dif_neg hw, norm_div]
    simp [Complex.norm_real, hw]

private lemma phaseAnchor_mul_norm (w : ℂ) : phaseAnchor w * ‖w‖ = w := by
  by_cases hw : w = 0
  · simp [phaseAnchor, hw]
  · rw [phaseAnchor, dif_neg hw]
    field_simp [norm_ne_zero_iff.mpr hw]

private lemma conj_phaseAnchor_mul (w : ℂ) : conj (phaseAnchor w) * w = ‖w‖ := by
  calc
    conj (phaseAnchor w) * w
        = conj (phaseAnchor w) * (phaseAnchor w * ‖w‖) := by rw [phaseAnchor_mul_norm]
    _ = (conj (phaseAnchor w) * phaseAnchor w) * ‖w‖ := by ring
    _ = ‖w‖ := by
          rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, norm_phaseAnchor]
          simp

private lemma norm_sub_phaseAnchor_le (w lam : ℂ) (hlam : ‖lam‖ = 1) :
    ‖w - phaseAnchor w‖ ≤ ‖w - lam‖ := by
  have hw_eq : w = phaseAnchor w * ‖w‖ := (phaseAnchor_mul_norm w).symm
  calc
    ‖w - phaseAnchor w‖ = |‖w‖ - 1| := by
      calc
        ‖w - phaseAnchor w‖ = ‖phaseAnchor w * ((‖w‖ : ℂ) - 1)‖ := by
          have hw_sub : w - phaseAnchor w = phaseAnchor w * ‖w‖ - phaseAnchor w := by
            nth_rewrite 1 [hw_eq]
            rfl
          calc
            ‖w - phaseAnchor w‖ = ‖phaseAnchor w * ‖w‖ - phaseAnchor w‖ := by rw [hw_sub]
            _ = ‖phaseAnchor w * ((‖w‖ : ℂ) - 1)‖ := by
              congr 1
              ring
        _ = ‖phaseAnchor w‖ * ‖((‖w‖ : ℂ) - 1)‖ := norm_mul _ _
        _ = ‖phaseAnchor w‖ * ‖(((‖w‖ - 1 : ℝ) : ℂ))‖ := by
              rw [show ((‖w‖ : ℂ) - 1) = (((‖w‖ - 1 : ℝ) : ℂ)) by simp]
        _ = ‖phaseAnchor w‖ * |‖w‖ - 1| := by rw [Complex.norm_real, Real.norm_eq_abs]
        _ = |‖w‖ - 1| := by rw [norm_phaseAnchor, one_mul]
    _ = |‖w‖ - ‖lam‖| := by rw [hlam]
    _ ≤ ‖w - lam‖ := abs_norm_sub_norm_le _ _

private lemma phaseDistanceSqNorm_eq_centered
    (p : Polynomial ℂ) (lam : ℂ) :
    phaseDistanceSqNorm p lam =
      ‖((1 : ℂ) + p.eval 0) - lam‖ ^ 2 +
        (1 / Real.pi) * ∫ z : ℂ,
          ‖(p - Polynomial.C (p.eval 0)).eval z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) := by
  set q : Polynomial ℂ := p - Polynomial.C (p.eval 0)
  have hq0 : q.eval 0 = 0 := by simp [q]
  have hcoeff0 : q.coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero]
    exact hq0
  set D := q.natDegree
  set a : Fin D → ℂ := fun k => q.coeff (k.val + 1)
  have hq_eval : ∀ z, q.eval z = polyEval a z := by
    intro z
    rw [eval_eq_sum_range, polyEval, Finset.sum_range_succ' (fun i => q.coeff i * z ^ i)]
    simp only [hcoeff0, zero_mul, pow_zero]
    rw [← Fin.sum_univ_eq_sum_range]
    ring
  have hp_eval : ∀ z, p.eval z = p.eval 0 + polyEval a z := by
    intro z
    calc
      p.eval z = q.eval z + p.eval 0 := by simp [q]
      _ = p.eval 0 + polyEval a z := by
        rw [hq_eval]
        ring
  have hq_gauss :
      (1 / Real.pi) * ∫ z : ℂ, ‖q.eval z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) = fockNormSq a := by
    simpa [hq_eval] using fockNorm_eq_gaussian_integral a
  calc
    phaseDistanceSqNorm p lam
        = (1 / Real.pi) * ∫ z : ℂ, ‖(((1 : ℂ) + p.eval 0) - lam) + polyEval a z‖ ^ 2 *
            Real.exp (-‖z‖ ^ 2) := by
              unfold phaseDistanceSqNorm phaseDistanceSq
              congr 1
              apply integral_congr_ae
              filter_upwards with z
              rw [hp_eval]
              ring_nf
    _ = ‖((1 : ℂ) + p.eval 0) - lam‖ ^ 2 + fockNormSq a := by
          simpa using gaussian_integral_const_add_polyEval a (((1 : ℂ) + p.eval 0) - lam)
    _ = ‖((1 : ℂ) + p.eval 0) - lam‖ ^ 2 +
          (1 / Real.pi) * ∫ z : ℂ, ‖q.eval z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) := by rw [← hq_gauss]
    _ = ‖((1 : ℂ) + p.eval 0) - lam‖ ^ 2 +
          (1 / Real.pi) * ∫ z : ℂ, ‖(p - Polynomial.C (p.eval 0)).eval z‖ ^ 2 *
            Real.exp (-‖z‖ ^ 2) := by simp [q]

private lemma phaseDistanceSqNorm_one_eq
    (p : Polynomial ℂ) :
    phaseDistanceSqNorm p 1 =
      (1 / Real.pi) * ∫ z : ℂ, ‖p.eval z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) := by
  unfold phaseDistanceSqNorm phaseDistanceSq
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  have hz : (1 : ℂ) + p.eval z - 1 = p.eval z := by ring
  rw [hz]

theorem LocalFockSPR_of_small_norm_exists_phase
    (p : Polynomial ℂ)
    (hsmall :
      (1 / Real.pi) * ∫ z : ℂ, ‖p.eval z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) ≤
        (1 / 4601 : ℝ) ^ 2) :
    ∃ w : ℂ, ‖w‖ = 1 ∧
      ∫ z : ℂ, ‖w * ((1 : ℂ) + p.eval z) - 1‖ ^ 2 * Real.exp (-‖z‖ ^ 2) ≤
      23003 ^ 2 *
        ∫ z : ℂ, (|‖1 + p.eval z‖ - 1|) ^ 2 * Real.exp (-‖z‖ ^ 2) := by
  let w0 : ℂ := (1 : ℂ) + p.eval 0
  let lam0 : ℂ := phaseAnchor w0
  have hlam0 : ‖lam0‖ = 1 := by simpa [lam0] using norm_phaseAnchor w0
  have hphase_le_one : phaseDistanceSqNorm p lam0 ≤ phaseDistanceSqNorm p 1 := by
    have hnorm : ‖w0 - lam0‖ ≤ ‖w0 - 1‖ := by
      simpa [lam0] using norm_sub_phaseAnchor_le w0 1 (by simp)
    have hsq : ‖w0 - lam0‖ ^ 2 ≤ ‖w0 - 1‖ ^ 2 := by
      nlinarith [hnorm, norm_nonneg (w0 - lam0), norm_nonneg (w0 - 1)]
    rw [phaseDistanceSqNorm_eq_centered, phaseDistanceSqNorm_eq_centered]
    nlinarith
  have hsmall0 : phaseDistanceSqNorm p lam0 ≤ (1 / 4601 : ℝ) ^ 2 :=
    le_trans (le_trans hphase_le_one (by rw [phaseDistanceSqNorm_one_eq])) hsmall
  let q : Polynomial ℂ :=
    Polynomial.C (conj lam0) * (p + Polynomial.C 1) - Polynomial.C 1
  have hunit0 : conj lam0 * lam0 = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hlam0]
    norm_num
  have hq_eval_mul :
      ∀ z : ℂ, q.eval z = conj lam0 * ((1 : ℂ) + p.eval z) - 1 := by
    intro z
    simp [q, mul_add, add_comm]
  have hq_eval :
      ∀ z : ℂ, q.eval z = conj lam0 * (((1 : ℂ) + p.eval z) - lam0) := by
    intro z
    calc
      q.eval z = conj lam0 * ((1 : ℂ) + p.eval z) - 1 := hq_eval_mul z
      _ = conj lam0 * (((1 : ℂ) + p.eval z) - lam0) := by
        rw [mul_sub]
        simp [hunit0]
  have hdist_eq :
      phaseDistanceSq p lam0 =
        ∫ z : ℂ, ‖q.eval z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) := by
    unfold phaseDistanceSq
    apply integral_congr_ae
    filter_upwards with z
    rw [hq_eval z, norm_mul, Complex.norm_conj, hlam0, one_mul]
  have hdistNorm_eq :
      phaseDistanceSqNorm p lam0 =
        (1 / Real.pi) * ∫ z : ℂ, ‖q.eval z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) := by
    unfold phaseDistanceSqNorm
    rw [hdist_eq]
  have hw0_phase : conj lam0 * w0 = ‖w0‖ := by simpa [lam0] using conj_phaseAnchor_mul w0
  have hq_real : Complex.im (q.eval 0) = 0 := by
    have hq0 :
        q.eval 0 = ((‖w0‖ - 1 : ℝ) : ℂ) := by
      calc
        q.eval 0 = conj lam0 * w0 - 1 := by simpa [w0] using hq_eval_mul 0
        _ = (‖w0‖ : ℂ) - 1 := by rw [hw0_phase]
        _ = ((‖w0‖ - 1 : ℝ) : ℂ) := by simp
    rw [hq0]
    simp
  have hsmallq :
      (1 / Real.pi) * ∫ z : ℂ, ‖q.eval z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) ≤
        (1 / 4601 : ℝ) ^ 2 := by
    rw [← hdistNorm_eq]
    exact hsmall0
  have hlocal := LocalFockSPR_of_small_norm q hq_real hsmallq
  have hrho_eq :
      ∫ z : ℂ, (|‖1 + q.eval z‖ - 1|) ^ 2 * Real.exp (-‖z‖ ^ 2) =
        ∫ z : ℂ, (|‖1 + p.eval z‖ - 1|) ^ 2 * Real.exp (-‖z‖ ^ 2) := by
    apply integral_congr_ae
    filter_upwards with z
    have hone :
        (1 : ℂ) + q.eval z = conj lam0 * ((1 : ℂ) + p.eval z) := by simp [q, mul_add, add_comm]
    rw [hone, norm_mul, Complex.norm_conj, hlam0, one_mul]
  refine ⟨conj lam0, by simpa [Complex.norm_conj] using hlam0, ?_⟩
  calc
    ∫ z : ℂ, ‖conj lam0 * ((1 : ℂ) + p.eval z) - 1‖ ^ 2 * Real.exp (-‖z‖ ^ 2)
        = ∫ z : ℂ, ‖q.eval z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) := by
            apply integral_congr_ae
            filter_upwards with z
            rw [hq_eval_mul z]
    _ ≤ 23003 ^ 2 *
          ∫ z : ℂ, (|‖1 + q.eval z‖ - 1|) ^ 2 * Real.exp (-‖z‖ ^ 2) := hlocal
    _ = 23003 ^ 2 *
          ∫ z : ℂ, (|‖1 + p.eval z‖ - 1|) ^ 2 * Real.exp (-‖z‖ ^ 2) := by rw [hrho_eq]

end FockSPR
