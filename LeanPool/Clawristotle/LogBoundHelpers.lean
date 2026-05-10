/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import LeanPool.Clawristotle.Defs
import LeanPool.Clawristotle.TorusDefs
import LeanPool.Clawristotle.TorusInstance
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Order.Compact

open ContinuousLinearMap Real Set VML

-- ============================================================================
-- Derivation of Logarithmic Growth from Polynomial Score Bound via MVT
-- ============================================================================

lemma op_norm_bound_from_basis (L : (Fin 3 → ℝ) →L[ℝ] ℝ) {C : ℝ}
    (hC : 0 ≤ C)
    (bound : ∀ i : Fin 3, ‖L (Pi.single i 1 : Fin 3 → ℝ)‖ ≤ C) :
    ‖L‖ ≤ 3 * C := by
  apply ContinuousLinearMap.opNorm_le_bound
  · positivity
  · intro x
    have hx : x = ∑ i : Fin 3, x i • (Pi.single i 1 : Fin 3 → ℝ) := by
      ext j
      simp_rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hneq
        simp [Pi.single_eq_of_ne hneq.symm]
      · intro hj; exfalso; exact hj (Finset.mem_univ j)
    have eq1 : L x = ∑ i : Fin 3, x i * L (Pi.single i 1 : Fin 3 → ℝ) := by
      calc L x = L (∑ i : Fin 3, x i • (Pi.single i 1 : Fin 3 → ℝ)) := by conv_lhs => rw [hx]
           _ = ∑ i : Fin 3, L (x i • (Pi.single i 1 : Fin 3 → ℝ)) := by rw [map_sum]
           _ = ∑ i : Fin 3, x i * L (Pi.single i 1 : Fin 3 → ℝ) := by
             congr 1; ext i
             rw [L.map_smul, smul_eq_mul]
    rw [eq1]
    calc ‖∑ i : Fin 3, x i * L (Pi.single i 1 : Fin 3 → ℝ)‖
        ≤ ∑ i : Fin 3, ‖x i * L (Pi.single i 1 : Fin 3 → ℝ)‖ := norm_sum_le _ _
         _ = ∑ i : Fin 3, ‖x i‖ * ‖L (Pi.single i 1 : Fin 3 → ℝ)‖ := by simp_rw [norm_mul]
         _ ≤ ∑ i : Fin 3, ‖x‖ * C := by
           apply Finset.sum_le_sum
           intro i _
           apply mul_le_mul
           · exact norm_le_pi_norm x i
           · exact bound i
           · positivity
           · positivity
         _ = 3 * (‖x‖ * C) := by simp
         _ = 3 * C * ‖x‖ := by ring

lemma mvt_test (g : (Fin 3 → ℝ) → ℝ) (hg_diff : Differentiable ℝ g)
    (Cg : ℝ) (Kg : ℕ) (hCg : 0 ≤ Cg)
    (bound : ∀ v, ‖fderiv ℝ g v‖ ≤ Cg * (1 + ‖v‖) ^ Kg) :
    ∀ v, |g v| ≤ |g 0| + Cg * (1 + ‖v‖)^(Kg + 1) := by
  intro v
  have H : ‖g v - g 0‖ ≤ Cg * (1 + ‖v‖)^Kg * ‖v - 0‖ := by
    refine Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (s := segment ℝ 0 v) ?_ ?_ ?_ ?_ ?_
    · intro x _
      exact hg_diff x
    · intro x hx
      have hw : ‖x‖ ≤ ‖v‖ := by
        rw [segment_eq_image] at hx
        rcases hx with ⟨t, ht, rfl⟩
        simp only [smul_zero, zero_add]
        calc ‖t • v‖ = |t| * ‖v‖ := norm_smul t v
             _ = t * ‖v‖ := by rw [abs_of_nonneg ht.1]
             _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg v)
             _ = ‖v‖ := one_mul ‖v‖
      have hb := bound x
      calc ‖fderiv ℝ g x‖ ≤ Cg * (1 + ‖x‖)^Kg := hb
           _ ≤ Cg * (1 + ‖v‖)^Kg := by gcongr
    · exact convex_segment 0 v
    · exact left_mem_segment ℝ 0 v
    · exact right_mem_segment ℝ 0 v
  have h_norm_g : |g v - g 0| = ‖g v - g 0‖ := by rfl
  rw [← h_norm_g] at H
  have h_norm_v : ‖v - 0‖ = ‖v‖ := by simp
  rw [h_norm_v] at H
  have h1 : |g v| - |g 0| ≤ |g v - g 0| := abs_sub_abs_le_abs_sub (g v) (g 0)
  calc |g v| ≤ |g 0| + |g v - g 0| := by linarith
       _ ≤ |g 0| + Cg * (1 + ‖v‖)^Kg * ‖v‖ := by linarith
       _ ≤ |g 0| + Cg * (1 + ‖v‖)^Kg * (1 + ‖v‖) := by
         have hX : (0:ℝ) ≤ Cg * (1 + ‖v‖)^Kg :=
           mul_nonneg hCg (pow_nonneg (by positivity) _)
         nlinarith [hX, norm_nonneg v]
       _ = |g 0| + Cg * (1 + ‖v‖)^(Kg + 1) := by ring

lemma log_f_zero_bound (f : Torus3 → (Fin 3 → ℝ) → ℝ)
    (hf_pos : ∀ x v, 0 < f x v)
    (hf_smooth_x : ∀ v, ContDiff ℝ 2 (periodicLift (fun x => f x v))) :
    ∃ C > 0, ∀ x, |Real.log (f x 0)| ≤ C := by
  have h_diff : FlatTorus3.IsSpatiallySmooth 2 (fun x => f x 0) := hf_smooth_x 0
  have h_cont : Continuous (fun x => f x 0) := FlatTorus3.hDiff_continuous 1 _ h_diff
  have h_log_cont : Continuous (fun x => Real.log (f x 0)) := by
    apply Continuous.log h_cont
    intro x
    exact ne_of_gt (hf_pos x 0)
  have h_comp : IsCompact (univ : Set Torus3) := isCompact_univ
  have h_ne : (univ : Set Torus3).Nonempty := univ_nonempty
  -- Extreme value theorem
  obtain ⟨x_min, _, h_min⟩ := h_comp.exists_isMinOn h_ne h_log_cont.continuousOn
  obtain ⟨x_max, _, h_max⟩ := h_comp.exists_isMaxOn h_ne h_log_cont.continuousOn
  use |Real.log (f x_min 0)| + |Real.log (f x_max 0)| + 1
  constructor
  · positivity
  · intro x
    have h1 : Real.log (f x_min 0) ≤ Real.log (f x 0) := h_min (mem_univ x)
    have h2 : Real.log (f x 0) ≤ Real.log (f x_max 0) := h_max (mem_univ x)
    have h3 : |Real.log (f x 0)| ≤ max |Real.log (f x_min 0)| |Real.log (f x_max 0)| := by
      rw [abs_le]
      constructor
      · have h_neg : -Real.log (f x 0) ≤ max |Real.log (f x_min 0)| |Real.log (f x_max 0)| := by
          calc -Real.log (f x 0) ≤ -Real.log (f x_min 0) := neg_le_neg h1
            _ ≤ |Real.log (f x_min 0)| := neg_le_abs (Real.log (f x_min 0))
            _ ≤ max |Real.log (f x_min 0)| |Real.log (f x_max 0)| := le_max_left _ _
        exact neg_le.mp h_neg
      · calc Real.log (f x 0) ≤ Real.log (f x_max 0) := h2
          _ ≤ |Real.log (f x_max 0)| := le_abs_self _
          _ ≤ max |Real.log (f x_min 0)| |Real.log (f x_max 0)| := le_max_right _ _
    apply le_trans h3
    have h_max_le : max |Real.log (f x_min 0)| |Real.log (f x_max 0)| ≤
        |Real.log (f x_min 0)| + |Real.log (f x_max 0)| :=
      max_le_add_of_nonneg (abs_nonneg _) (abs_nonneg _)
    calc max |Real.log (f x_min 0)| |Real.log (f x_max 0)|
        ≤ |Real.log (f x_min 0)| + |Real.log (f x_max 0)| :=
          h_max_le
      _ ≤ |Real.log (f x_min 0)| + |Real.log (f x_max 0)| + 1 := by linarith

lemma log_bound_from_grad (f : Torus3 → (Fin 3 → ℝ) → ℝ)
    (hf_pos : ∀ x v, 0 < f x v)
    (hf_smooth_v : ∀ x, ContDiff ℝ 3 (f x))
    (hf_smooth_x : ∀ v, ContDiff ℝ 2 (periodicLift (fun x => f x v)))
    (Cg : ℝ) (Kg : ℕ)
    (hGradBound : ∀ x v i, |fderiv ℝ (f x) v (Pi.single i 1)| ≤ Cg * (1 + ‖v‖) ^ Kg * f x v) :
    ∃ (C_log : ℝ) (K_log : ℕ), ∀ (x : Torus3) (v : Fin 3 → ℝ),
      |Real.log (f x v)| ≤ C_log * (1 + ‖v‖) ^ K_log := by
  rcases log_f_zero_bound f hf_pos hf_smooth_x with ⟨C0, hC0_pos, hC0⟩
  let Cg' := 3 * max 0 Cg
  use C0 + Cg', Kg + 1
  intro x v
  have h_diff_f : Differentiable ℝ (f x) := (hf_smooth_v x).differentiable (by decide)
  have hg_diff : Differentiable ℝ (fun v => log (f x v)) := by
    apply Differentiable.log h_diff_f
    intro w
    exact (hf_pos x w).ne'
  have h_fderiv : ∀ w, ‖fderiv ℝ (fun v => log (f x v)) w‖ ≤ Cg' * (1 + ‖w‖) ^ Kg := by
    intro w
    have hw_pos : 0 < f x w := hf_pos x w
    have h1 : HasFDerivAt (f x) (fderiv ℝ (f x) w) w := (h_diff_f w).hasFDerivAt
    have h2 : HasDerivAt log (f x w)⁻¹ (f x w) := hasDerivAt_log hw_pos.ne'
    have h3 : HasFDerivAt (fun v => log (f x v)) ((f x w)⁻¹ • fderiv ℝ (f x) w) w :=
      HasDerivAt.comp_hasFDerivAt w h2 h1
    have h_fderiv_eq : fderiv ℝ (fun v => log (f x v)) w = (f x w)⁻¹ • fderiv ℝ (f x) w :=
      h3.fderiv
    rw [h_fderiv_eq, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hw_pos]
    have hC_nonneg : 0 ≤ max 0 Cg * (1 + ‖w‖) ^ Kg * f x w := by
      positivity
    have h_bound_L : ‖fderiv ℝ (f x) w‖ ≤ 3 * (max 0 Cg * (1 + ‖w‖) ^ Kg * f x w) := by
      apply op_norm_bound_from_basis (fderiv ℝ (f x) w) hC_nonneg
      intro i
      calc
        ‖(fderiv ℝ (f x) w) (Pi.single i 1)‖ = |(fderiv ℝ (f x) w) (Pi.single i 1)| := rfl
        _ ≤ Cg * (1 + ‖w‖) ^ Kg * f x w := hGradBound x w i
        _ ≤ max 0 Cg * (1 + ‖w‖) ^ Kg * f x w := by
          gcongr
          exact le_max_right 0 Cg
    calc
      (f x w)⁻¹ * ‖fderiv ℝ (f x) w‖ ≤ (f x w)⁻¹ * (3 * (max 0 Cg * (1 + ‖w‖) ^ Kg * f x w)) := by
        gcongr
      _ = (f x w)⁻¹ * f x w * Cg' * (1 + ‖w‖) ^ Kg := by
        dsimp [Cg']
        ring
      _ = Cg' * (1 + ‖w‖) ^ Kg := by
        rw [inv_mul_cancel₀ hw_pos.ne', one_mul]
  have h_mvt := mvt_test (fun v => log (f x v)) hg_diff Cg' Kg (by positivity) h_fderiv v
  have hpow : (1 : ℝ) ≤ (1 + ‖v‖) ^ (Kg + 1) := by
    calc (1 : ℝ) = 1 ^ (Kg + 1) := by ring
      _ ≤ (1 + ‖v‖) ^ (Kg + 1) := by
        gcongr; exact le_add_of_nonneg_right (norm_nonneg v)
  calc
    |log (f x v)|
      ≤ |log (f x 0)| + Cg' * (1 + ‖v‖) ^ (Kg + 1) :=
        h_mvt
    _ ≤ C0 + Cg' * (1 + ‖v‖) ^ (Kg + 1) := by
        gcongr; exact hC0 x
    _ ≤ C0 * (1 + ‖v‖) ^ (Kg + 1) +
        Cg' * (1 + ‖v‖) ^ (Kg + 1) := by
        gcongr; nlinarith [hpow]
    _ = (C0 + Cg') * (1 + ‖v‖) ^ (Kg + 1) := by ring
