/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import LeanPool.Clawristotle.CoulombPSDHelpers

/-!
# PSD Integrability and Fubini Symmetrization for Coulomb

Inner and outer integrability of the PSD integrand, and the Fubini
symmetrization needed for the H-theorem entropy dissipation identity.
Depends on continuity and pointwise bounds from CoulombPSDHelpers.
-/

open MeasureTheory Matrix Finset BigOperators Real

noncomputable section
namespace VML

/-- PSD integrand is integrable for Coulomb kernel (inner integral, fixing v).
    Uses element-wise Coulomb matrix bound |A_{ij}| ≤ ‖z‖⁻¹ combined with
    polynomial score bound and Newtonian potential of Schwartz functions. -/
lemma psd_inner_integrable_coulomb
    (f : (Fin 3 → ℝ) → ℝ) (hf_pos : ∀ v, 0 < f v) (hf_smooth : ContDiff ℝ 3 f)
    (hf_schwartz : ∀ (N : ℕ) {k : ℕ}, k ≤ 2 →
      ∃ C > 0, ∀ v,
        ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
    {Cg : ℝ} {Kg : ℕ}
    (hGrad : ∀ v i, |fderiv ℝ f v (Pi.single i 1)| ≤
      Cg * (1 + ‖v‖) ^ Kg * f v)
    (v : Fin 3 → ℝ) :
    Integrable (PSDIntegrand coulombKernel f v) := by
  -- Score bound: |∂_i log f(u)| ≤ Cg * (1+‖u‖)^Kg
  have h_score := score_bound_of_grad_bound hf_pos hf_smooth hGrad
  have hf_decay := schwartz_pointwise_decay hf_schwartz
  -- Schwartz decay of (1+‖w‖)^{2Kg} * f(w)
  have hpf_decay := schwartz_poly_weighted_decay hf_decay (2 * Kg)
  -- Newtonian potential integrability
  have h_int_f : Integrable (fun w => ‖v - w‖⁻¹ * f w) :=
    inv_norm_schwartz_integrable f hf_decay hf_smooth.continuous.aestronglyMeasurable v
  have h_int_pf : Integrable (fun w => ‖v - w‖⁻¹ * ((1 + ‖w‖) ^ (2 * Kg) * f w)) :=
    inv_norm_schwartz_integrable _ hpf_decay
      ((continuous_const.add continuous_norm).pow _ |>.mul
        hf_smooth.continuous).aestronglyMeasurable v
  -- AEStronglyMeasurable of PSD integrand
  have h_meas : AEStronglyMeasurable (PSDIntegrand coulombKernel f v) volume :=
    ((psd_continuous_coulomb f hf_pos hf_smooth).comp
      (continuous_const.prodMk continuous_id')).aestronglyMeasurable
  -- Dominating constant
  set C_dom := 18 * Cg ^ 2 * f v
  -- Apply Integrable.mono' with dominating function
  refine ((h_int_f.const_mul ((1 + ‖v‖) ^ (2 * Kg))).add h_int_pf
    |>.const_mul C_dom).mono' h_meas (Filter.Eventually.of_forall fun w => ?_)
  -- Pointwise bound via extracted lemma
  rw [Real.norm_eq_abs]
  exact psd_pointwise_bound_coulomb f hf_pos h_score v w


/-- PSD integrand is integrable for Coulomb kernel (outer integral).
    Uses pointwise bound + Newtonian uniform bounds + Schwartz decay. -/
lemma psd_outer_integrable_coulomb
    (f : (Fin 3 → ℝ) → ℝ) (hf_pos : ∀ v, 0 < f v) (hf_smooth : ContDiff ℝ 3 f)
    (hf_schwartz : ∀ (N : ℕ) {k : ℕ}, k ≤ 2 →
      ∃ C > 0, ∀ v,
        ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
    {Cg : ℝ} {Kg : ℕ}
    (hGrad : ∀ v i, |fderiv ℝ f v (Pi.single i 1)| ≤
      Cg * (1 + ‖v‖) ^ Kg * f v) :
    Integrable (fun v =>
      ∫ w, PSDIntegrand coulombKernel f v w) := by
  have h_score := score_bound_of_grad_bound hf_pos hf_smooth hGrad
  have hf_decay := schwartz_pointwise_decay hf_schwartz
  have hpf_decay := schwartz_poly_weighted_decay hf_decay (2 * Kg)
  -- Newtonian uniform bounds
  obtain ⟨M₁, hM₁, hM₁b⟩ := newtonian_schwartz_uniform_bound f hf_decay
    hf_smooth.continuous.aestronglyMeasurable
  obtain ⟨M₂, hM₂, hM₂b⟩ := newtonian_schwartz_uniform_bound
    (fun w => (1 + ‖w‖) ^ (2 * Kg) * f w) hpf_decay
    ((continuous_const.add continuous_norm).pow _ |>.mul hf_smooth.continuous).aestronglyMeasurable
  -- Integrability of Newtonian terms
  have h_int_f := fun v => inv_norm_schwartz_integrable f hf_decay
    hf_smooth.continuous.aestronglyMeasurable v
  have h_int_pf := fun v => inv_norm_schwartz_integrable
    (fun w => (1 + ‖w‖) ^ (2 * Kg) * f w) hpf_decay
    ((continuous_const.add continuous_norm).pow _ |>.mul
      hf_smooth.continuous).aestronglyMeasurable v
  -- Dominating function: C_out * (1+‖v‖)^{2Kg} * f(v), integrable by Schwartz decay
  set C_out := 18 * Cg ^ 2 * (M₁ + M₂) with hC_out_def
  have h_poly_int : Integrable (fun v => (1 + ‖v‖) ^ (2 * Kg) * f v) :=
    schwartz_poly_mul_integrable hf_pos hf_smooth.continuous hf_decay (2 * Kg)
  -- AEStronglyMeasurable of parametric integral
  have h_meas : AEStronglyMeasurable
      (fun v => ∫ w, PSDIntegrand coulombKernel f v w) volume :=
    (psd_continuous_coulomb f hf_pos hf_smooth).aestronglyMeasurable.integral_prod_right'
  -- Apply Integrable.mono'
  apply (h_poly_int.const_mul C_out).mono' h_meas
  filter_upwards with v
  rw [Real.norm_eq_abs]
  -- Dominating function for inner integral
  have hdom_w : Integrable (fun w =>
      18 * Cg ^ 2 * f v * ((1 + ‖v‖) ^ (2 * Kg) * (‖v - w‖⁻¹ * f w) +
                            ‖v - w‖⁻¹ * ((1 + ‖w‖) ^ (2 * Kg) * f w))) :=
    ((h_int_f v).const_mul ((1 + ‖v‖) ^ (2 * Kg))).add (h_int_pf v)
      |>.const_mul (18 * Cg ^ 2 * f v)
  calc |∫ w, PSDIntegrand coulombKernel f v w|
      ≤ ∫ w, |PSDIntegrand coulombKernel f v w| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ w, (18 * Cg ^ 2 * f v * ((1 + ‖v‖) ^ (2 * Kg) * (‖v - w‖⁻¹ * f w) +
                                     ‖v - w‖⁻¹ * ((1 + ‖w‖) ^ (2 * Kg) * f w))) :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) hdom_w
          (ae_of_all _ fun w => psd_pointwise_bound_coulomb f hf_pos h_score v w)
    _ = 18 * Cg ^ 2 * f v * ∫ w, ((1 + ‖v‖) ^ (2 * Kg) * (‖v - w‖⁻¹ * f w) +
                                    ‖v - w‖⁻¹ * ((1 + ‖w‖) ^ (2 * Kg) * f w)) :=
        integral_const_mul _ _
    _ ≤ 18 * Cg ^ 2 * f v * ((1 + ‖v‖) ^ (2 * Kg) * M₁ + M₂) := by
        conv_lhs => rw [show ∫ w, (1 + ‖v‖) ^ (2 * Kg) * (‖v - w‖⁻¹ * f w) +
              ‖v - w‖⁻¹ * ((1 + ‖w‖) ^ (2 * Kg) * f w) =
            (1 + ‖v‖) ^ (2 * Kg) * (∫ w, ‖v - w‖⁻¹ * f w) +
              ∫ w, ‖v - w‖⁻¹ * ((1 + ‖w‖) ^ (2 * Kg) * f w) from
          by rw [integral_add ((h_int_f v).const_mul _) (h_int_pf v), integral_const_mul]]
        apply mul_le_mul_of_nonneg_left _
          (by nlinarith [sq_nonneg Cg, hf_pos v])
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left _
            (pow_nonneg (by linarith [norm_nonneg v]) _)
          calc ∫ w, ‖v - w‖⁻¹ * f w
              = ∫ w, ‖v - w‖⁻¹ * |f w| :=
                integral_congr_ae (ae_of_all _ fun w => by
                  change ‖v - w‖⁻¹ * f w = ‖v - w‖⁻¹ * |f w|
                  rw [abs_of_pos (hf_pos w)])
            _ ≤ M₁ := hM₁b v
        · calc ∫ w, ‖v - w‖⁻¹ * ((1 + ‖w‖) ^ (2 * Kg) * f w)
              = ∫ w, ‖v - w‖⁻¹ * |(1 + ‖w‖) ^ (2 * Kg) * f w| :=
                integral_congr_ae (ae_of_all _ fun w => by
                  change ‖v - w‖⁻¹ * ((1 + ‖w‖) ^ (2 * Kg) * f w) =
                    ‖v - w‖⁻¹ * |(1 + ‖w‖) ^ (2 * Kg) * f w|
                  rw [abs_of_nonneg (mul_nonneg
                    (pow_nonneg (by linarith [norm_nonneg w]) _)
                    (le_of_lt (hf_pos w)))])
            _ ≤ M₂ := hM₂b v
    _ ≤ C_out * ((1 + ‖v‖) ^ (2 * Kg) * f v) := by
        have h1 : (1 : ℝ) ≤ (1 + ‖v‖) ^ (2 * Kg) :=
          one_le_pow₀ (by linarith [norm_nonneg v])
        have h2 : M₂ ≤ (1 + ‖v‖) ^ (2 * Kg) * M₂ :=
          le_mul_of_one_le_left (le_of_lt hM₂) h1
        simp only [C_out]
        calc 18 * Cg ^ 2 * f v * ((1 + ‖v‖) ^ (2 * Kg) * M₁ + M₂)
            ≤ 18 * Cg ^ 2 * f v *
              ((M₁ + M₂) * (1 + ‖v‖) ^ (2 * Kg)) := by
              apply mul_le_mul_of_nonneg_left _
                (by nlinarith [sq_nonneg Cg, hf_pos v])
              nlinarith
          _ = 18 * Cg ^ 2 * (M₁ + M₂) *
              ((1 + ‖v‖) ^ (2 * Kg) * f v) := by ring


/-- The `∫_w ‖score · flux‖ ≤ C·(1+‖v‖)^{2Kg}·f(v)` bound used in
    `fubini_double_integrable_coulomb`; split out to keep that proof under the
    size limit. -/
private lemma fubini_double_int_bound_coulomb
    {f : (Fin 3 → ℝ) → ℝ} (hf_pos : ∀ v, 0 < f v)
    {Cg : ℝ} {Kg : ℕ} (hCg_nn : 0 ≤ Cg)
    (hGrad : ∀ v i, |fderiv ℝ f v (Pi.single i 1)| ≤ Cg * (1 + ‖v‖) ^ Kg * f v)
    {F : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ}
    (h_pw_bound : ∀ v w, |F (v, w)| ≤
      3 * Cg * (1 + ‖v‖) ^ Kg * (‖v - w‖⁻¹ *
        (∑ j : Fin 3, (f w * |vGrad f v j| + f v * |vGrad f w j|))))
    {M₁ Md₀ Md₁ Md₂ : ℝ} (hMd_pos : 0 ≤ Md₀ + Md₁ + Md₂)
    (hM₁b : ∀ v, ∫ w, ‖v - w‖⁻¹ * |f w| ≤ M₁)
    (hMd₀b : ∀ v, ∫ w, ‖v - w‖⁻¹ * |vGrad f w 0| ≤ Md₀)
    (hMd₁b : ∀ v, ∫ w, ‖v - w‖⁻¹ * |vGrad f w 1| ≤ Md₁)
    (hMd₂b : ∀ v, ∫ w, ‖v - w‖⁻¹ * |vGrad f w 2| ≤ Md₂)
    (h_f_abs : ∀ v, Integrable (fun w => ‖v - w‖⁻¹ * |f w|))
    (h_dj_abs : ∀ j : Fin 3, ∀ v, Integrable (fun w => ‖v - w‖⁻¹ * |vGrad f w j|)) :
    ∀ v, ∫ w, ‖F (v, w)‖ ≤
      (9 * Cg ^ 2 * M₁ + 3 * Cg * (Md₀ + Md₁ + Md₂)) * ((1 + ‖v‖) ^ (2 * Kg) * f v) := by
      intro v
      -- Rearrange: ‖v-w‖⁻¹*(f w*A + f v*B) = A*(‖v-w‖⁻¹*|f w|) + f v*(‖v-w‖⁻¹*B)
      have hrearrange : ∀ j : Fin 3,
          (fun w => ‖v - w‖⁻¹ * (f w * |vGrad f v j| + f v * |vGrad f w j|)) =
          (fun w => |vGrad f v j| * (‖v - w‖⁻¹ * |f w|) +
            f v * (‖v - w‖⁻¹ * |vGrad f w j|)) := fun j => by
        ext w
        rw [abs_of_pos (hf_pos w)]
        ring
      have h_each_int : ∀ j : Fin 3, Integrable
          (fun w => ‖v - w‖⁻¹ * (f w * |vGrad f v j| + f v * |vGrad f w j|)) := fun j => by
        rw [hrearrange j]
        exact ((h_f_abs v).const_mul _).add ((h_dj_abs j v).const_mul _)
      -- Each ∫ splits into const * ∫ + const * ∫
      have h_split : ∀ j : Fin 3,
          ∫ w, ‖v - w‖⁻¹ * (f w * |vGrad f v j| + f v * |vGrad f w j|) =
          |vGrad f v j| * (∫ w, ‖v - w‖⁻¹ * |f w|) +
          f v * (∫ w, ‖v - w‖⁻¹ * |vGrad f w j|) := fun j => by
        rw [hrearrange j, integral_add ((h_f_abs v).const_mul _) ((h_dj_abs j v).const_mul _),
          integral_const_mul, integral_const_mul]
      calc ∫ w, ‖F (v, w)‖
          = ∫ w, |F (v, w)| :=
            integral_congr_ae (ae_of_all _ fun w => Real.norm_eq_abs _)
        _ ≤ ∫ w, 3 * Cg * (1 + ‖v‖) ^ Kg * (‖v - w‖⁻¹ *
              ∑ j : Fin 3,
                (f w * |vGrad f v j| + f v * |vGrad f w j|)) := by
            apply integral_mono_of_nonneg
              (ae_of_all _ fun _ => abs_nonneg _)
            · apply Integrable.const_mul
              have : (fun w => ‖v - w‖⁻¹ * ∑ j : Fin 3,
                    (f w * |vGrad f v j| +
                     f v * |vGrad f w j|)) =
                  (fun w => ∑ j : Fin 3, ‖v - w‖⁻¹ *
                    (f w * |vGrad f v j| +
                     f v * |vGrad f w j|)) := by
                ext w; rw [Finset.mul_sum]
              rw [this]
              exact integrable_finsetSum _ fun j _ =>
                h_each_int j
            · exact ae_of_all _ (h_pw_bound v)
        _ = 3 * Cg * (1 + ‖v‖) ^ Kg * ∫ w, ‖v - w‖⁻¹ *
              ∑ j : Fin 3,
                (f w * |vGrad f v j| +
                 f v * |vGrad f w j|) := by
            rw [integral_const_mul]
        _ = 3 * Cg * (1 + ‖v‖) ^ Kg *
              ∑ j : Fin 3,
                (|vGrad f v j| * (∫ w, ‖v - w‖⁻¹ * |f w|) +
                 f v * (∫ w, ‖v - w‖⁻¹ * |vGrad f w j|)) := by
            congr 1
            rw [show (fun w => ‖v - w‖⁻¹ * ∑ j : Fin 3,
                    (f w * |vGrad f v j| +
                     f v * |vGrad f w j|)) =
                (fun w => ∑ j : Fin 3, ‖v - w‖⁻¹ *
                    (f w * |vGrad f v j| +
                     f v * |vGrad f w j|)) from by
                  ext w; rw [Finset.mul_sum],
              integral_finsetSum _ fun j _ => h_each_int j]
            congr 1; ext j; exact h_split j
        _ ≤ (9 * Cg ^ 2 * M₁ + 3 * Cg * (Md₀ + Md₁ + Md₂)) * ((1 + ‖v‖) ^ (2 * Kg) * f v) := by
            -- Use Finset.sum_le_sum to bound the sum
            have hpow : (1 : ℝ) ≤ (1 + ‖v‖) ^ Kg :=
              one_le_pow₀ (by linarith [norm_nonneg v])
            have hv_nn : (0 : ℝ) ≤ (1 + ‖v‖) ^ Kg := le_trans zero_le_one hpow
            have hint_nn : 0 ≤ ∫ w, ‖v - w‖⁻¹ * |f w| :=
              integral_nonneg fun w => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (abs_nonneg _)
            have hfv := le_of_lt (hf_pos v)
            -- Bound each summand
            have hMd_sum : ∑ j : Fin 3, (∫ w, ‖v - w‖⁻¹ * |vGrad f w j|) ≤ Md₀ + Md₁ + Md₂ := by
              simp only [Fin.sum_univ_three]
              linarith [hMd₀b v, hMd₁b v, hMd₂b v]
            have htotal : ∑ j : Fin 3,
                (|vGrad f v j| * (∫ w, ‖v - w‖⁻¹ * |f w|) +
                 f v * (∫ w, ‖v - w‖⁻¹ * |vGrad f w j|)) ≤
                3 * (Cg * (1 + ‖v‖) ^ Kg * f v * M₁) +
                f v * (Md₀ + Md₁ + Md₂) := by
              have hj : ∀ j : Fin 3,
                  |vGrad f v j| * (∫ w, ‖v - w‖⁻¹ * |f w|) ≤
                  Cg * (1 + ‖v‖) ^ Kg * f v * M₁ :=
                fun j => mul_le_mul (hGrad v j) (hM₁b v) hint_nn
                  (mul_nonneg (mul_nonneg hCg_nn hv_nn) hfv)
              simp only [Fin.sum_univ_three]
              linarith [hj 0, hj 1, hj 2,
                mul_le_mul_of_nonneg_left (hMd₀b v) hfv,
                mul_le_mul_of_nonneg_left (hMd₁b v) hfv,
                mul_le_mul_of_nonneg_left (hMd₂b v) hfv]
            calc 3 * Cg * (1 + ‖v‖) ^ Kg *
                ∑ j : Fin 3, ((|vGrad f v j| *
                  (∫ w, ‖v - w‖⁻¹ * |f w|)) +
                  f v * (∫ w, ‖v - w‖⁻¹ * |vGrad f w j|))
              ≤ 3 * Cg * (1 + ‖v‖) ^ Kg *
                (3 * (Cg * (1 + ‖v‖) ^ Kg * f v * M₁) +
                 f v * (Md₀ + Md₁ + Md₂)) :=
                mul_le_mul_of_nonneg_left htotal
                  (mul_nonneg (mul_nonneg (by norm_num) hCg_nn) hv_nn)
              _ ≤ (9 * Cg ^ 2 * M₁ + 3 * Cg * (Md₀ + Md₁ + Md₂)) *
                    ((1 + ‖v‖) ^ (2 * Kg) * f v) := by
                rw [show 2 * Kg = Kg + Kg from by omega, pow_add]
                have hPP : (1 + ‖v‖) ^ Kg ≤
                    (1 + ‖v‖) ^ Kg * (1 + ‖v‖) ^ Kg :=
                  le_mul_of_one_le_left hv_nn hpow
                nlinarith [sq_nonneg Cg, hf_pos v,
                  mul_nonneg hCg_nn hv_nn,
                  mul_nonneg hfv hMd_pos,
                  mul_nonneg (mul_nonneg hCg_nn hv_nn) (mul_nonneg hfv hMd_pos),
                  mul_le_mul_of_nonneg_right hPP
                    (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 3)
                      (mul_nonneg hCg_nn hfv)) hMd_pos)]

/-- The Fubini integrand (score · flux) is jointly integrable on the product space
    for the Coulomb kernel. Uses `integrable_prod_iff` with:
    - Joint measurability from measurability of each factor
    - Inner integrability from `landau_flux_integrable_coulomb`
    - Norm integral bound from PSD pointwise bound + Newtonian uniform bounds -/
lemma fubini_double_integrable_coulomb
    (f : (Fin 3 → ℝ) → ℝ) (hf_pos : ∀ v, 0 < f v)
    (hf_smooth : ContDiff ℝ 3 f)
    (hf_schwartz : ∀ (N : ℕ) {k : ℕ}, k ≤ 2 →
      ∃ C > 0, ∀ v,
        ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
    {Cg : ℝ} {Kg : ℕ}
    (hGrad : ∀ v i,
      |fderiv ℝ f v (Pi.single i 1)| ≤
        Cg * (1 + ‖v‖) ^ Kg * f v) :
    Integrable (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      dotProduct (vGrad (Real.log ∘ f) p.1)
        (mulVec (landauMatrix coulombKernel (p.1 - p.2))
          (f p.2 • vGrad f p.1 - f p.1 • vGrad f p.2))) := by
  have h_score := score_bound_of_grad_bound hf_pos hf_smooth hGrad
  have hf_decay := schwartz_pointwise_decay hf_schwartz
  have hpf_decay := schwartz_poly_weighted_decay hf_decay (2 * Kg)
  -- Flux integrability
  have hFlux : ∀ v, Integrable (fun w => mulVec (landauMatrix coulombKernel (v - w))
      (f w • vGrad f v - f v • vGrad f w)) :=
    fun v => landau_flux_integrable_coulomb f hf_pos hf_smooth hf_schwartz v
  -- Newtonian uniform bounds
  obtain ⟨M₁, hM₁, hM₁b⟩ := newtonian_schwartz_uniform_bound f hf_decay
    hf_smooth.continuous.aestronglyMeasurable
  obtain ⟨M₂, hM₂, hM₂b⟩ := newtonian_schwartz_uniform_bound
    (fun w => (1 + ‖w‖) ^ (2 * Kg) * f w) hpf_decay
    ((continuous_const.add continuous_norm).pow _ |>.mul hf_smooth.continuous).aestronglyMeasurable
  -- Integrability of Newtonian terms
  have h_int_f := fun v => inv_norm_schwartz_integrable f hf_decay
    hf_smooth.continuous.aestronglyMeasurable v
  have h_int_pf := fun v => inv_norm_schwartz_integrable
    (fun w => (1 + ‖w‖) ^ (2 * Kg) * f w) hpf_decay
    ((continuous_const.add continuous_norm).pow _ |>.mul
      hf_smooth.continuous).aestronglyMeasurable v
  -- Cg ≥ 0
  have hCg_nn : 0 ≤ Cg := by
    by_contra h_neg; push Not at h_neg
    have : Cg * (1 + ‖(0 : Fin 3 → ℝ)‖) ^ Kg * f 0 < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos h_neg (by positivity)) (hf_pos 0)
    linarith [hGrad 0 0, abs_nonneg (fderiv ℝ f 0 (Pi.single 0 1))]
  -- The integrand as a function on product space
  set F : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ := fun p =>
    dotProduct (vGrad (Real.log ∘ f) p.1)
      (mulVec (landauMatrix coulombKernel (p.1 - p.2))
        (f p.2 • vGrad f p.1 - f p.1 • vGrad f p.2)) with hF_def
  -- Step 1: AEStronglyMeasurable on product space (via extracted helper)
  have h_meas : AEStronglyMeasurable F (volume.prod volume) :=
    fubini_double_aestronglyMeasurable hf_pos hf_smooth
  -- Step 2: Inner integrability (for a.e. v, w ↦ F(v,w) integrable)
  have h_inner : ∀ v, Integrable (fun w => F (v, w)) := fun v => by
    -- F(v,w) = dotProduct(score(v), A(v-w) · flux(v,w))
    -- = ∑_i score_i(v) * (A(v-w) · flux(v,w))_i
    -- Each (A·flux)_i is integrable by landau_flux_integrable_coulomb
    simp only [F, dotProduct, Fin.sum_univ_three]
    exact ((integrable_pi_iff.mp (hFlux v) 0).const_mul _).add
      ((integrable_pi_iff.mp (hFlux v) 1).const_mul _) |>.add
      ((integrable_pi_iff.mp (hFlux v) 2).const_mul _)
  -- Step 3: ∫ ‖F(v,·)‖ is integrable in v
  -- Strategy: bound ∫‖F(v,w)‖ ≤ C_out * (1+‖v‖)^{2Kg} * f(v), integrable by Schwartz decay
  have h_norm_int : Integrable (fun v => ∫ w, ‖F (v, w)‖) := by
    have hdg_decay := schwartz_fderiv_component_decay hf_schwartz
    -- Newtonian bounds for partial derivatives
    have hMj : ∀ j, ∃ M > 0, ∀ v,
        ∫ w, ‖v - w‖⁻¹ * |fderiv ℝ f w (Pi.single j 1)| ≤ M :=
      fun j => newtonian_schwartz_uniform_bound _ (hdg_decay j)
        ((hf_smooth.continuous_fderiv (by norm_num)).clm_apply
          continuous_const).aestronglyMeasurable
    obtain ⟨Md₀, hMd₀, hMd₀b⟩ := hMj 0
    obtain ⟨Md₁, hMd₁, hMd₁b⟩ := hMj 1
    obtain ⟨Md₂, hMd₂, hMd₂b⟩ := hMj 2
    set M_df := Md₀ + Md₁ + Md₂
    -- Integrability helpers
    have h_f_abs : ∀ v, Integrable (fun w => ‖v - w‖⁻¹ * |f w|) := fun v =>
      (h_int_f v).norm.congr (Filter.Eventually.of_forall fun w => by
        simp [Real.norm_eq_abs])
    have h_dj_abs : ∀ j : Fin 3, ∀ v,
        Integrable (fun w => ‖v - w‖⁻¹ * |vGrad f w j|) := fun j v =>
      (inv_norm_schwartz_integrable _ (hdg_decay j)
        ((hf_smooth.continuous_fderiv (by norm_num)).clm_apply
          continuous_const).aestronglyMeasurable v).norm.congr
        (Filter.Eventually.of_forall fun w => by
          change ‖‖v - w‖⁻¹ * fderiv ℝ f w (Pi.single j 1)‖ = ‖v - w‖⁻¹ * |vGrad f w j|
          rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), Real.norm_eq_abs]
          rfl)
    -- Dominating function
    set C_out := 9 * Cg ^ 2 * M₁ + 3 * Cg * M_df
    have h_poly_int : Integrable (fun v => (1 + ‖v‖) ^ (2 * Kg) * f v) :=
      schwartz_poly_mul_integrable hf_pos hf_smooth.continuous hf_decay (2 * Kg)
    -- Measurability of norm integral
    have h_norm_meas : AEStronglyMeasurable (fun v => ∫ w, ‖F (v, w)‖) volume :=
      h_meas.norm.integral_prod_right'
    -- Pointwise bound on |F(v,w)| via extracted helper
    have h_pw_bound : ∀ v w, |F (v, w)| ≤
        3 * Cg * (1 + ‖v‖) ^ Kg * (‖v - w‖⁻¹ *
          (∑ j : Fin 3, (f w * |vGrad f v j| + f v * |vGrad f w j|))) :=
      fun v w => fubini_double_pointwise_bound hf_pos h_score v w
    -- Bound on ∫_w |F(v,w)|
    have h_int_bound := fubini_double_int_bound_coulomb hf_pos hCg_nn hGrad h_pw_bound
      (by linarith [hMd₀, hMd₁, hMd₂]) hM₁b hMd₀b hMd₁b hMd₂b h_f_abs h_dj_abs
    exact (h_poly_int.const_mul C_out).mono' h_norm_meas
      (ae_of_all _ fun v => by
        rw [Real.norm_eq_abs, abs_of_nonneg
          (integral_nonneg fun w => norm_nonneg _)]
        exact h_int_bound v)
  -- Apply integrable_prod_iff
  rw [MeasureTheory.Measure.volume_eq_prod]
  exact (integrable_prod_iff h_meas).mpr
    ⟨ae_of_all _ h_inner, h_norm_int⟩

end VML
