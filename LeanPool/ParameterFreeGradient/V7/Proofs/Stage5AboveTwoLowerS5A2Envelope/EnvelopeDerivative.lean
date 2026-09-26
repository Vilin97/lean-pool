/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5A2Envelope.DimensionControl

/-!
Selection of minimizing displacements and differentiation of the resulting envelope.
-/

@[expose] public section

namespace V7.Stage5AboveTwoLowerS5A2Envelope

open Asymptotics
open Stage5AboveTwoLower
open Stage5AboveTwoLower.S5ARepair
open Stage5AboveTwoLower.S5AFinalRepair

/-- A total classical selector.  Under the concrete Stage-5 hypotheses its
selected displacement is a minimizer with the already proved uniform margin. -/
noncomputable def selectedDisplacement (kernel : SmoothingKernelData p d)
    (chi : ℝ) (ell : Point d → ℝ) (x : Point d) : Point d :=
  by
    classical
    exact if h : ∃ v : Point d,
        IsInfimalMinimizer kernel chi ell x v ∧
          lpNorm p v ≤ chi - chi / 4 then Classical.choose h else 0

lemma selectedDisplacement_spec (kernel : SmoothingKernelData p d)
    (chi : ℝ) (ell : Point d → ℝ) (x : Point d)
    (hex : ∃ v : Point d,
      IsInfimalMinimizer kernel chi ell x v ∧
        lpNorm p v ≤ chi - chi / 4) :
    IsInfimalMinimizer kernel chi ell x
        (selectedDisplacement kernel chi ell x) ∧
      lpNorm p (selectedDisplacement kernel chi ell x) ≤ chi - chi / 4 := by
  classical
  rw [selectedDisplacement, dite_eq_left hex]
  exact Classical.choose_spec hex

/-- The envelope gradient obtained from a selected minimizing displacement. -/
noncomputable def selectedEnvelopeGradient
    (kernel : SmoothingKernelData p d) (chi : ℝ)
    (ell : Point d → ℝ) (x : Point d) : Point d :=
  -kernel.gradPhi ((1 / chi) • selectedDisplacement kernel chi ell x)

/-- A globally supporting, locally Lipschitz vector field is the genuine
Fréchet derivative of its value function.  This is the specialized primal
Danskin replacement needed by the frozen construction. -/
lemma hasFDerivAt_of_global_support_and_lp_lipschitz
    {p L : ℝ} (hp : 1 < p) (hL : 0 ≤ L)
    (f : Point d → ℝ) (g : Point d → Point d)
    (hsupport : ∀ x y,
      f x + O3.pairing (g x) (y - x) ≤ f y)
    (hlip : ∀ x y,
      lpNorm (conjugateExponent p) (g x - g y) ≤
        L * lpNorm p (x - y)) (x : Point d) :
    HasFDerivAt f (pairingCLM (g x)) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro c hc
  let C : ℝ := lpAmbientConstant p d
  let A : ℝ := L * C ^ (2 : ℕ)
  have hC : 0 ≤ C := lpAmbientConstant_nonneg _ _
  have hA : 0 ≤ A := mul_nonneg hL (sq_nonneg C)
  have hradius : 0 < c / (A + 1) := div_pos hc (by linarith)
  have hevent : ∀ᶠ h in nhds (0 : Point d), ‖h‖ < c / (A + 1) := by
    simpa only [dist_zero_right] using
      (Metric.eventually_nhds_iff_ball.2 ⟨c / (A + 1), hradius, by
        intro h hh
        simpa [Metric.mem_ball] using hh⟩)
  filter_upwards [hevent] with h hh
  let R : ℝ := f (x + h) - f x - pairingCLM (g x) h
  have hlower := hsupport x (x + h)
  have hupper := hsupport (x + h) x
  have hdiff : x - (x + h) = -h := by module
  have hsub : x + h - x = h := by module
  have hRnonneg : 0 ≤ R := by
    dsimp [R]
    rw [hsub] at hlower
    rw [pairingCLM_apply]
    linarith
  have hRupper : R ≤ O3.pairing (g (x + h) - g x) h := by
    dsimp [R]
    rw [hdiff] at hupper
    rw [pairingCLM_apply]
    simp only [O3.pairing, Pi.neg_apply, mul_neg,
      Finset.sum_neg_distrib] at hupper ⊢
    simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    linarith
  have hholder := O3.pairing_le_lpNorm_mul
    (O3.holderConjugate_conjugateExponent (by linarith : 1 < p)).symm
      (g (x + h) - g x) h
  have hsmooth := hlip (x + h) x
  rw [hsub] at hsmooth
  have hpambient : lpNorm p h ≤ C * ‖h‖ :=
    lpNorm_le_ambientConstant hp.le h
  have hrem : ‖R‖ ≤ A * ‖h‖ ^ (2 : ℕ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hRnonneg]
    have hpair : O3.pairing (g (x + h) - g x) h ≤
        L * lpNorm p h ^ (2 : ℕ) := by
      calc
        O3.pairing (g (x + h) - g x) h ≤
            lpNorm (conjugateExponent p) (g (x + h) - g x) * lpNorm p h :=
          hholder
        _ ≤ (L * lpNorm p h) * lpNorm p h := by
          gcongr
          exact O3.lpNorm_nonneg p h
        _ = L * lpNorm p h ^ (2 : ℕ) := by ring
    have hnormsq : lpNorm p h ^ (2 : ℕ) ≤ (C * ‖h‖) ^ (2 : ℕ) := by
      nlinarith [O3.lpNorm_nonneg p h]
    dsimp [A]
    nlinarith [mul_le_mul_of_nonneg_left hnormsq hL]
  change ‖R‖ ≤ c * ‖h‖
  calc
    ‖R‖ ≤ A * ‖h‖ ^ (2 : ℕ) := hrem
    _ ≤ c * ‖h‖ := by
      have hn : 0 ≤ ‖h‖ := norm_nonneg _
      have hsmall : A * ‖h‖ ≤ c := by
        have : (A + 1) * ‖h‖ < c := by
          simpa [mul_comm] using
            ((lt_div_iff₀ (by linarith : 0 < A + 1)).mp hh)
        nlinarith
      nlinarith

end V7.Stage5AboveTwoLowerS5A2Envelope
