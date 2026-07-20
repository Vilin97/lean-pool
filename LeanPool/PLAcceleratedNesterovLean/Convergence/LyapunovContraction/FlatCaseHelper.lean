/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.Core.NesterovScheme

/-!
# Algebraic helper lemmas for the flat-case Lyapunov bound

Provides norm expansions, Pythagorean decompositions, inner product
decompositions, and cross-term vanishing for orthogonal projectors.
-/


noncomputable section

namespace PLAcceleratedNesterovLean
open scoped Topology NNReal

variable {d : ℕ}

/-! ## Orthogonality from self-adjoint + idempotent -/

theorem proj_orth_inner (P : E d →L[ℝ] E d)
    (hP_self_adj : ∀ x y : E d, @inner ℝ _ _ (P x) y = @inner ℝ _ _ x (P y))
    (hP_idem : ∀ x : E d, P (P x) = P x) (v : E d) :
    @inner ℝ _ _ (P v) (v - P v) = (0 : ℝ) := by
  simp_all

/-! ## Pythagorean decomposition -/

theorem pythagorean_proj (P : E d →L[ℝ] E d)
    (hP_self_adj : ∀ x y : E d, @inner ℝ _ _ (P x) y = @inner ℝ _ _ x (P y))
    (hP_idem : ∀ x : E d, P (P x) = P x) (v : E d) :
    ‖v‖ ^ 2 = ‖P v‖ ^ 2 + ‖v - P v‖ ^ 2 := by
  have h : P v + (v - P v) = v := by abel
  have horth := proj_orth_inner P hP_self_adj hP_idem v
  calc ‖v‖ ^ 2 = ‖P v + (v - P v)‖ ^ 2 := by rw [h]
    _ = ‖P v‖ ^ 2 + 2 * @inner ℝ _ _ (P v) (v - P v) + ‖v - P v‖ ^ 2 :=
        norm_add_sq_real _ _
    _ = ‖P v‖ ^ 2 + ‖v - P v‖ ^ 2 := by rw [horth, mul_zero, add_zero]

/-! ## Cross-term vanishing -/

theorem cross_term_Pg_b (P : E d →L[ℝ] E d)
    (hP_self_adj : ∀ x y : E d, @inner ℝ _ _ (P x) y = @inner ℝ _ _ x (P y))
    (hP_idem : ∀ x : E d, P (P x) = P x)
    (g v : E d) :
    @inner ℝ _ _ (P g) (v - P v) = (0 : ℝ) := by
  simp_all

theorem cross_term_Pperpg_Pv (P : E d →L[ℝ] E d)
    (hP_self_adj : ∀ x y : E d, @inner ℝ _ _ (P x) y = @inner ℝ _ _ x (P y))
    (hP_idem : ∀ x : E d, P (P x) = P x)
    (g v : E d) :
    @inner ℝ _ _ (g - P g) (P v) = (0 : ℝ) := by
  rw [inner_sub_left]
  simp_all

/-! ## Inner product decomposition -/

theorem inner_proj_decomp (P : E d →L[ℝ] E d)
    (hP_self_adj : ∀ x y : E d, @inner ℝ _ _ (P x) y = @inner ℝ _ _ x (P y))
    (hP_idem : ∀ x : E d, P (P x) = P x)
    (g v : E d) :
    @inner ℝ _ _ g v =
      @inner ℝ _ _ (P g) (P v) + @inner ℝ _ _ (g - P g) (v - P v) := by
  have h_expand : @inner ℝ _ _ (g - P g) (v - P v) =
      @inner ℝ _ _ g v - @inner ℝ _ _ g (P v) -
      @inner ℝ _ _ (P g) v + @inner ℝ _ _ (P g) (P v) := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right]; ring
  simp_all

/-! ## Norm of wn = (1-a)•b + √μ'•en - √η•P⊥g -/

theorem norm_three_term_sq (b en ppg : E d) (c1 c2 c3 : ℝ)
    (hc2_nn : 0 ≤ c2) (hc3_nn : 0 ≤ c3) :
    ‖c1 • b + Real.sqrt c2 • en - Real.sqrt c3 • ppg‖ ^ 2 =
      c1 ^ 2 * ‖b‖ ^ 2 + c2 * ‖en‖ ^ 2 + c3 * ‖ppg‖ ^ 2
      + 2 * c1 * Real.sqrt c2 * @inner ℝ _ _ b en
      - 2 * c1 * Real.sqrt c3 * @inner ℝ _ _ b ppg
      - 2 * Real.sqrt c2 * Real.sqrt c3 * @inner ℝ _ _ en ppg := by
  have hsub : c1 • b + Real.sqrt c2 • en - Real.sqrt c3 • ppg =
    (c1 • b + Real.sqrt c2 • en) + (-(Real.sqrt c3 • ppg)) := by abel
  rw [hsub, norm_add_sq_real, norm_add_sq_real (c1 • b)]
  simp only [norm_smul, norm_neg, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg c2), abs_of_nonneg (Real.sqrt_nonneg c3),
    inner_add_left, inner_neg_right,
    real_inner_smul_left, real_inner_smul_right,
    mul_pow, sq_abs, Real.sq_sqrt hc2_nn, Real.sq_sqrt hc3_nn]
  ring

/-! ## Norm of un = b + √μ'•en -/

theorem norm_two_term_sq (b en : E d) (c : ℝ) (hc : 0 ≤ c) :
    ‖b + Real.sqrt c • en‖ ^ 2 =
      ‖b‖ ^ 2 + c * ‖en‖ ^ 2 + 2 * Real.sqrt c * @inner ℝ _ _ b en := by
  rw [norm_add_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg c),
    real_inner_smul_right, mul_pow, Real.sq_sqrt hc]
  ring

/-! ## Segment-based combined bound -/

/-- From strong aiming and segment estimate:
    F(xn) + √η·⟨g,v⟩ - ⟨g,e⟩ + μ'/2·‖e‖² ≥ -εη/2·‖v‖² -/
theorem combined_aim_segment
    (Fn ipGE sqη_ipGV μ'_half_Esq εη_half_Vsq : ℝ)
    (h_seg : Fn + sqη_ipGV ≥ ipGE - μ'_half_Esq - εη_half_Vsq) :
    Fn + sqη_ipGV - ipGE + μ'_half_Esq ≥ -εη_half_Vsq := by linarith

end PLAcceleratedNesterovLean
