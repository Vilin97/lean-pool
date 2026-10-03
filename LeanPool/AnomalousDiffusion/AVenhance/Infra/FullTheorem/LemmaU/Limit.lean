/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.Real.Pi.Bounds

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.LemmaU.ModeCoefficients

/-!
# Lemma U: Parseval as a limit, and the low/high eigenvalue thresholds
-/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization Filter
open scoped Topology
open AVenhance.Infra.Parabolic.FourierGalerkin
open AVenhance.Infra.Parabolic.WeakUniqueness
open AVenhance.Infra.Classical

namespace AVenhance.Infra.FullTheorem.LemmaU

/-- Parseval: the sum of squared cell coefficients converges to the squared `L²` norm. -/
theorem sum_cellCoeff_sq_tendsto {d : Vec 2 → ℝ} (hd : MemL2On AVenhance.unitCube d) :
    Tendsto (fun M : ℕ => ∑ a : RealFourierIndex M, cellCoeff M d a ^ 2) atTop
      (𝓝 (AVenhance.l2NormSq d)) := by
  have ht := weakFourierProjectionL2_tendsto (u := fun _ : ℝ => d) (t := 0) hd
  have hn := ((continuous_norm.pow 2).continuousAt.tendsto).comp ht
  have hlim := weakProjection_scalarTransfer_normSq hd
  have hfun : (fun M : ℕ => ∑ a : RealFourierIndex M, cellCoeff M d a ^ 2) =
      (fun x => ‖x‖ ^ 2) ∘ (fun M => weakFourierProjectionL2 M (fun _ : ℝ => d) 0) := by
    funext M
    simp only [Function.comp]
    unfold weakFourierProjectionL2
    rw [realFourierScalarMap_norm, EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs, weakFourierCoefficientPath, PiLp.toLp_apply]
    rw [← Equiv.sum_comp (realFourierIndexEquivFin M)]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    simp only [Equiv.symm_apply_apply]
    rfl
  rw [hfun, ← hlim]
  exact hn

/-- Low modes: the eigenvalue is at most `80 K²`. -/
theorem modeLam_le_of_low (M : ℕ) (K : ℝ) (a : RealFourierIndex M)
    (h : ∀ i, |realFourierModeDerivativeScale a i| ≤ 2 * Real.pi * K) :
    modeLam M a ≤ 80 * K ^ 2 := by
  have hK : 0 ≤ 2 * Real.pi * K := (abs_nonneg _).trans (h 0)
  have hsq : ∀ i, realFourierModeDerivativeScale a i ^ 2 ≤ (2 * Real.pi * K) ^ 2 := fun i => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2
  have hpi : Real.pi ^ 2 ≤ 10 := by
    have := Real.pi_lt_d2
    nlinarith [Real.pi_pos]
  have hK2 : 0 ≤ K ^ 2 := sq_nonneg K
  calc modeLam M a ≤ ∑ _i : Fin 2, (2 * Real.pi * K) ^ 2 :=
        Finset.sum_le_sum (fun i _ => hsq i)
    _ = 8 * Real.pi ^ 2 * K ^ 2 := by simp; ring
    _ ≤ 80 * K ^ 2 := by nlinarith

/-- High modes: the eigenvalue is at least `36 K²`. -/
theorem modeLam_ge_of_high (M : ℕ) {K : ℝ} (hK : 0 ≤ K) (a : RealFourierIndex M)
    (h : ¬ ∀ i, |realFourierModeDerivativeScale a i| ≤ 2 * Real.pi * K) :
    36 * K ^ 2 ≤ modeLam M a := by
  simp only [not_forall, not_le] at h
  obtain ⟨i, hi⟩ := h
  have hpi : 9 ≤ Real.pi ^ 2 := by
    have := Real.pi_gt_three
    nlinarith
  have h1 : (2 * Real.pi * K) ^ 2 ≤ realFourierModeDerivativeScale a i ^ 2 := by
    rw [← sq_abs (realFourierModeDerivativeScale a i)]
    exact pow_le_pow_left₀ (by positivity) hi.le 2
  have h2 : realFourierModeDerivativeScale a i ^ 2 ≤ modeLam M a :=
    Finset.single_le_sum (f := fun j => realFourierModeDerivativeScale a j ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hK2 : 0 ≤ K ^ 2 := sq_nonneg K
  nlinarith

end AVenhance.Infra.FullTheorem.LemmaU

end
