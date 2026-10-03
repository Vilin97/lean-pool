/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.VelocityHigherOrders

/-! Quantitative all-order differentiation of a small linear fixed equation. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- Constants for successive derivatives of a Jacobian fixed equation.
They depend only on the finite primitive derivative bound and the order. -/
def amnrJacobianJetConstant (C : ℝ) : ℕ → ℝ
  | 0 => 2
  | n + 1 => amnrJacobianJetConstant C n + 2 +
      2 * ((n + 1).factorial : ℝ) * max 1 C *
        amnrJacobianJetConstant C n ^ (n + 2) * (2 : ℝ) ^ (n + 1)

theorem amnrJacobianJetConstant_two_le (C : ℝ) (n : ℕ) :
    2 ≤ amnrJacobianJetConstant C n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [amnrJacobianJetConstant]
    have hp : 0 ≤ 2 * ((n + 1).factorial : ℝ) * max 1 C *
        amnrJacobianJetConstant C n ^ (n + 2) * (2 : ℝ) ^ (n + 1) := by
      have h := le_max_left (1 : ℝ) C
      positivity
    linarith

theorem amnrJacobianJetConstant_mono (C : ℝ) : Monotone (amnrJacobianJetConstant C) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [amnrJacobianJetConstant]
  have h := amnrJacobianJetConstant_two_le C n
  have hm := le_max_left (1 : ℝ) C
  have hp : 0 ≤ 2 * ((n + 1).factorial : ℝ) * max 1 C *
      amnrJacobianJetConstant C n ^ (n + 2) * (2 : ℝ) ^ (n + 1) := by positivity
  linarith

/-- Absorb the undifferentiated small coefficient after differentiating an
actual linear fixed equation. Higher coefficient and lower solution jets
are used only in the strictly lower terms of Leibniz's formula. -/
theorem amnrJacobianJet_absorb {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {J : E → E →L[ℝ] F} {W : E → F →L[ℝ] F}
    (hJ : ContDiff ℝ (⊤ : ℕ∞) J) (hW : ContDiff ℝ (⊤ : ℕ∞) W)
    (R : E →L[ℝ] F) (heq : ∀ y, J y = R + (W y).comp (J y))
    (x : E) (n : ℕ) (hn : 1 ≤ n) (hsmall : ‖W x‖ ≤ 1 / 2)
    {B K : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hcoeff : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i W x‖ ≤ B)
    (hlower : ∀ i, i < n → ‖iteratedFDeriv ℝ i J x‖ ≤ K) :
    ‖iteratedFDeriv ℝ n J x‖ ≤ 2 * (2 : ℝ) ^ n * B * K := by
  let P := fun y => (W y).comp (J y)
  have hP : ContDiff ℝ (⊤ : ℕ∞) P :=
    (ContinuousLinearMap.compL ℝ E F F).isBoundedBilinearMap.contDiff.comp
      (hW.prodMk hJ)
  have he : J = (fun _ => R) + P := funext heq
  have hd : iteratedFDeriv ℝ n J x = iteratedFDeriv ℝ n P x := by
    rw [he, iteratedFDeriv_add (contDiff_const : ContDiff ℝ (n : WithTop ℕ∞) (fun _ : E => R))
      (hP.of_le (by simp))]
    simp [iteratedFDeriv_const_of_ne (by omega : n ≠ 0)]
  have hh := (ContinuousLinearMap.compL ℝ E F F).norm_iteratedFDeriv_le_of_bilinear_of_le_one
    hW hJ x (n := n) (by simp) (ContinuousLinearMap.norm_compL_le ℝ E F F)
  change ‖iteratedFDeriv ℝ n P x‖ ≤ _ at hh
  rw [← hd] at hh
  have hterm : ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i W x‖ * ‖iteratedFDeriv ℝ (n - i) J x‖ ≤
      ‖iteratedFDeriv ℝ n J x‖ / 2 + (2 : ℝ) ^ n * B * K := by
    rw [Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero,
      norm_iteratedFDeriv_zero]
    have htail : ∑ i ∈ Finset.range n,
        (n.choose (i + 1) : ℝ) * ‖iteratedFDeriv ℝ (i + 1) W x‖ *
          ‖iteratedFDeriv ℝ (n - (i + 1)) J x‖ ≤ (2 : ℝ) ^ n * B * K := by
      calc
        _ ≤ ∑ i ∈ Finset.range n, (n.choose (i + 1) : ℝ) * B * K := by
          apply Finset.sum_le_sum
          intro i hi
          have hi' := Finset.mem_range.mp hi
          exact mul_le_mul (mul_le_mul_of_nonneg_left (hcoeff (i + 1) (by omega) (by omega))
            (Nat.cast_nonneg _)) (hlower _ (by omega)) (norm_nonneg _) (by positivity)
        _ = (∑ i ∈ Finset.range n, (n.choose (i + 1) : ℝ)) * B * K := by
          rw [Finset.sum_mul, Finset.sum_mul]
        _ ≤ (2 : ℝ) ^ n * B * K := by
          apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hB) hK
          have hs : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) = (2 : ℝ) ^ n := by
            exact_mod_cast Nat.sum_range_choose n
          rw [Finset.sum_range_succ'] at hs
          simpa using le_of_le_of_eq (le_add_of_nonneg_right (by positivity)) hs
    have hzero := mul_le_mul_of_nonneg_right hsmall (norm_nonneg (iteratedFDeriv ℝ n J x))
    linarith
  have ha := hh.trans hterm
  linarith

/-- All Jacobian jets of a smooth solution of the actual small linear fixed
 equation are bounded by finite primitive constants. This induction does
 not assume a bound for the highest derivative it proves. -/
theorem amnrJacobianJet_norm_le_of_fixed_equation {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Q : E → F} {A : F → F →L[ℝ] F}
    (hQ : ContDiff ℝ (⊤ : ℕ∞) Q) (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (R : E →L[ℝ] F) (hR : ‖R‖ ≤ 1)
    (heq : ∀ y, fderiv ℝ Q y = R + (A (Q y)).comp (fderiv ℝ Q y))
    (x : E) (hsmall : ‖A (Q x)‖ ≤ 1 / 2) {C : ℝ} {N : ℕ}
    (hprimitive : ∀ i, i ≤ N → ‖iteratedFDeriv ℝ i A (Q x)‖ ≤ C)
    (n : ℕ) (hbudget : n ≤ N) :
    ‖iteratedFDeriv ℝ n (fderiv ℝ Q) x‖ ≤ amnrJacobianJetConstant C n := by
  have hC : 0 ≤ C := (norm_nonneg (iteratedFDeriv ℝ 0 A (Q x))).trans (hprimitive 0 (Nat.zero_le N))
  have hJ : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ Q) := hQ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      rw [norm_iteratedFDeriv_zero, amnrJacobianJetConstant]
      have hh := norm_add_le R ((A (Q x)).comp (fderiv ℝ Q x))
      rw [← heq x] at hh
      have hc := (A (Q x)).opNorm_comp_le (fderiv ℝ Q x)
      have hm := mul_le_mul_of_nonneg_right hsmall (norm_nonneg (fderiv ℝ Q x))
      linarith
    | succ m =>
      let K := amnrJacobianJetConstant C m
      have hK : 2 ≤ K := amnrJacobianJetConstant_two_le C m
      have hk0 : 0 ≤ K := by linarith
      have hlower : ∀ i, i ≤ m → ‖iteratedFDeriv ℝ i (fderiv ℝ Q) x‖ ≤ K := by
        intro i hi
        exact (ih i (by omega) (by omega)).trans (amnrJacobianJetConstant_mono C hi)
      have hD : ∀ i, 1 ≤ i → i ≤ m + 1 → ‖iteratedFDeriv ℝ i Q x‖ ≤ K ^ i := by
        intro i hi hi'
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
        rw [← norm_iteratedFDeriv_fderiv]
        exact (hlower j (by omega)).trans (le_self_pow₀ (by linarith) (by omega))
      let B := ((m + 1).factorial : ℝ) * max 1 C * K ^ (m + 1)
      have hB : 0 ≤ B := by
        have := le_max_left (1 : ℝ) C
        dsimp [B]
        positivity
      have hcoeff : ∀ i, 1 ≤ i → i ≤ m + 1 →
          ‖iteratedFDeriv ℝ i (A ∘ Q) x‖ ≤ B := by
        intro i hi hi'
        have hh := norm_iteratedFDeriv_comp_le (n := i) hA hQ (by simp) x
          (fun j hj => hprimitive j (by omega)) (fun j hj hj' => hD j hj (by omega))
        refine hh.trans ?_
        dsimp [B]
        apply mul_le_mul
        · exact mul_le_mul (by exact_mod_cast Nat.factorial_le hi')
            (le_max_right 1 C) hC
            (by positivity)
        · exact pow_le_pow_right₀ (by linarith) hi'
        · positivity
        · have := le_max_left (1 : ℝ) C
          positivity
      have hh := amnrJacobianJet_absorb hJ (hA.comp hQ) R heq x (m + 1) (by omega)
        hsmall hB hk0 hcoeff (fun i hi => hlower i (by omega))
      refine hh.trans ?_
      rw [amnrJacobianJetConstant]
      have he : 2 * (2 : ℝ) ^ (m + 1) * B * K =
          2 * ((m + 1).factorial : ℝ) * max 1 C * K ^ (m + 2) * (2 : ℝ) ^ (m + 1) := by
        dsimp [B]
        rw [show m + 2 = m + 1 + 1 by omega, pow_succ]
        ring
      rw [he]
      change _ ≤ K + 2 + _
      linarith

end AVenhance.Infra.Section4
