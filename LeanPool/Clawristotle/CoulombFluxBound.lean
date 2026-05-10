/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import LeanPool.Clawristotle.CoulombFlux

/-!
# Flux Component Bounds and Flux × Log Integrability for Coulomb

Proves:
- `flux_times_log_integrable_coulomb`: The flux × log(f) product is integrable.
- `coulomb_flux_component_bound`: Pointwise |flux_i(v)| ≤ Cf * g(v) * (1+‖v‖)^Kg.
-/

open MeasureTheory Matrix Finset BigOperators Real

noncomputable section
namespace VML

/-- Pointwise bound on the `i`-th component of the Coulomb Landau flux:
    `|flux_i(v)| ≤ M₀·(3‖∇g(v)‖) + (M₁+M₂+M₃)·‖g(v)‖`, where the `Mⱼ` are
    uniform Newtonian bounds. Split out of `flux_times_log_integrable_coulomb`
    to keep that proof under the size limit. -/
private lemma coulomb_flux_component_pointwise_le
    {g : (Fin 3 → ℝ) → ℝ}
    (hg_smooth : ContDiff ℝ 3 g)
    (hg_decay : ∀ N : ℕ, ∃ C > 0, ∀ w, |g w| * (1 + ‖w‖) ^ N ≤ C)
    (hdg_decay : ∀ j : Fin 3, ∀ N : ℕ, ∃ C > 0, ∀ w,
      |fderiv ℝ g w (Pi.single j 1)| * (1 + ‖w‖) ^ N ≤ C)
    (hFlux : ∀ v, Integrable (fun w => mulVec (landauMatrix coulombKernel (v - w))
      (g w • vGrad g v - g v • vGrad g w)))
    (M₀ M₁ M₂ M₃ : ℝ)
    (hM₀_pos : 0 < M₀) (hM₁_pos : 0 < M₁) (hM₂_pos : 0 < M₂) (hM₃_pos : 0 < M₃)
    (hM₀ : ∀ v, ∫ w, ‖v - w‖⁻¹ * |g w| ≤ M₀)
    (hM₁ : ∀ v, ∫ w, ‖v - w‖⁻¹ * |vGrad g w 0| ≤ M₁)
    (hM₂ : ∀ v, ∫ w, ‖v - w‖⁻¹ * |vGrad g w 1| ≤ M₂)
    (hM₃ : ∀ v, ∫ w, ‖v - w‖⁻¹ * |vGrad g w 2| ≤ M₃)
    (i : Fin 3) :
    ∀ v, |(∫ w, mulVec (landauMatrix coulombKernel (v - w))
        (g w • vGrad g v - g v • vGrad g w)) i| ≤
      M₀ * (3 * ‖iteratedFDeriv ℝ 1 g v‖) +
      (M₁ + M₂ + M₃) * ‖iteratedFDeriv ℝ 0 g v‖ := by
  intro v
  -- Step 1: pull component i out of the integral
  rw [eval_integral (fun j => (hFlux v).eval j)]
  -- Step 2: pointwise bound on |(mulVec A u) i|
  set u := fun w => g w • vGrad g v - g v • vGrad g w with hu_def
  have h_pw : ∀ w, |(landauMatrix coulombKernel (v - w) *ᵥ (u w)) i| ≤
      ‖v - w‖⁻¹ * ∑ j : Fin 3, |u w j| := by
    intro w
    by_cases hvw : v - w = 0
    · have : v = w := sub_eq_zero.mp hvw
      subst this; simp [mulVec, dotProduct, landauMatrix, innerLandauMatrix,
        normSq, vecMulVec, eucNorm, coulombKernel]
    · simp only [mulVec, dotProduct]
      calc |∑ j : Fin 3, landauMatrix coulombKernel (v - w) i j * u w j|
          ≤ ∑ j : Fin 3, |landauMatrix coulombKernel (v - w) i j * u w j| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j : Fin 3, |landauMatrix coulombKernel (v - w) i j| * |u w j| := by
            congr 1
            ext j
            exact abs_mul _ _
        _ ≤ ∑ j : Fin 3, ‖v - w‖⁻¹ * |u w j| :=
            Finset.sum_le_sum fun j _ =>
              mul_le_mul_of_nonneg_right (coulomb_landauMatrix_entry_le_pi _ _ _ hvw)
                (abs_nonneg _)
        _ = ‖v - w‖⁻¹ * ∑ j : Fin 3, |u w j| := (Finset.mul_sum _ _ _).symm
  calc |∫ w, (landauMatrix coulombKernel (v - w) *ᵥ (u w)) i|
      ≤ ∫ w, |(landauMatrix coulombKernel (v - w) *ᵥ (u w)) i| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ w, ‖v - w‖⁻¹ * ∑ j : Fin 3, |u w j| :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => abs_nonneg _)
          (by
            simp_rw [Finset.mul_sum]
            refine integrable_finset_sum _ fun j _ => ?_
            have h_uj_int : Integrable (fun w => ‖v - w‖⁻¹ * (u w j)) := by
              have h_f := inv_norm_schwartz_integrable g hg_decay
                hg_smooth.continuous.aestronglyMeasurable v
              have h_dj := inv_norm_schwartz_integrable
                (fun w => fderiv ℝ g w (Pi.single j 1)) (hdg_decay j)
                ((hg_smooth.continuous_fderiv (by norm_num)).clm_apply
                  continuous_const).aestronglyMeasurable v
              convert h_f.mul_const (vGrad g v j) |>.sub
                (h_dj.const_mul (g v)) using 1
              ext w; simp only [hu_def, vGrad, Pi.smul_apply, Pi.sub_apply,
                smul_eq_mul, mul_assoc, mul_comm (‖v - w‖⁻¹)]
              ring
            exact h_uj_int.norm.congr (Filter.Eventually.of_forall fun w => by
              change ‖‖v - w‖⁻¹ * u w j‖ = ‖v - w‖⁻¹ * |u w j|
              rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
                Real.norm_eq_abs]))
          (Filter.Eventually.of_forall h_pw)
    _ ≤ M₀ * (3 * ‖iteratedFDeriv ℝ 1 g v‖) +
        (M₁ + M₂ + M₃) * ‖iteratedFDeriv ℝ 0 g v‖ := by
        have h_f_abs : Integrable (fun w => ‖v - w‖⁻¹ * |g w|) :=
          (inv_norm_schwartz_integrable g hg_decay
            hg_smooth.continuous.aestronglyMeasurable v).norm.congr
            (Filter.Eventually.of_forall fun w => by
              change ‖‖v - w‖⁻¹ * g w‖ = ‖v - w‖⁻¹ * |g w|
              rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
                Real.norm_eq_abs])
        have h_dj_abs : ∀ j : Fin 3,
            Integrable (fun w => ‖v - w‖⁻¹ * |vGrad g w j|) := by
          intro j
          exact (inv_norm_schwartz_integrable
            (fun w => fderiv ℝ g w (Pi.single j 1)) (hdg_decay j)
            ((hg_smooth.continuous_fderiv (by norm_num)).clm_apply
              continuous_const).aestronglyMeasurable v).norm.congr
            (Filter.Eventually.of_forall fun w => by
              change ‖‖v - w‖⁻¹ * fderiv ℝ g w (Pi.single j 1)‖ =
                ‖v - w‖⁻¹ * |vGrad g w j|
              rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
                Real.norm_eq_abs]; rfl)
        have h_tri : ∀ w j, |u w j| ≤
            |g w| * |vGrad g v j| + |g v| * |vGrad g w j| := by
          intro w j
          simp only [hu_def, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
          have := norm_sub_le (g w * vGrad g v j) (g v * vGrad g w j)
          rwa [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul] at this
        have h_sum_tri : ∀ w, ∑ j : Fin 3, |u w j| ≤
            |g w| * ∑ j : Fin 3, |vGrad g v j| +
            |g v| * ∑ j : Fin 3, |vGrad g w j| := by
          intro w
          calc ∑ j : Fin 3, |u w j|
              ≤ ∑ j, (|g w| * |vGrad g v j| + |g v| * |vGrad g w j|) :=
                Finset.sum_le_sum fun j _ => h_tri w j
            _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        have hvg : ∀ j : Fin 3, |vGrad g v j| ≤
            ‖iteratedFDeriv ℝ 1 g v‖ := by
          intro j; simp only [vGrad]
          have h1 : ‖(Pi.single j (1:ℝ) : Fin 3 → ℝ)‖ ≤ 1 := by
            rw [Pi.norm_single, norm_one]
          calc |fderiv ℝ g v (Pi.single j 1)|
              = ‖fderiv ℝ g v (Pi.single j 1)‖ := (Real.norm_eq_abs _).symm
            _ ≤ ‖fderiv ℝ g v‖ * ‖(Pi.single j (1:ℝ) : Fin 3 → ℝ)‖ :=
                ContinuousLinearMap.le_opNorm _ _
            _ ≤ ‖fderiv ℝ g v‖ * 1 := by gcongr
            _ = ‖fderiv ℝ g v‖ := mul_one _
            _ = ‖iteratedFDeriv ℝ 1 g v‖ := norm_fderiv_eq_iteratedFDeriv_one _ _
        have hf0 : |g v| = ‖iteratedFDeriv ℝ 0 g v‖ := by
          rw [iteratedFDeriv_zero_eq_comp]; simp [Real.norm_eq_abs]
        have h_pw2 : ∀ w, ‖v - w‖⁻¹ * ∑ j : Fin 3, |u w j| ≤
            (∑ j : Fin 3, |vGrad g v j|) * (‖v - w‖⁻¹ * |g w|) +
            |g v| * ∑ j : Fin 3, (‖v - w‖⁻¹ * |vGrad g w j|) := by
          intro w
          calc ‖v - w‖⁻¹ * ∑ j, |u w j|
              ≤ ‖v - w‖⁻¹ * (|g w| * ∑ j, |vGrad g v j| +
                  |g v| * ∑ j, |vGrad g w j|) :=
                mul_le_mul_of_nonneg_left (h_sum_tri w) (inv_nonneg.mpr (norm_nonneg _))
            _ = _ := by simp only [← Finset.mul_sum]; ring
        calc ∫ w, ‖v - w‖⁻¹ * ∑ j : Fin 3, |u w j|
            ≤ ∫ w, ((∑ j, |vGrad g v j|) * (‖v - w‖⁻¹ * |g w|) +
                |g v| * ∑ j, (‖v - w‖⁻¹ * |vGrad g w j|)) :=
              integral_mono_of_nonneg
                (Filter.Eventually.of_forall fun w => mul_nonneg
                  (inv_nonneg.mpr (norm_nonneg _))
                  (Finset.sum_nonneg fun j _ => abs_nonneg _))
                ((h_f_abs.const_mul _).add
                  ((integrable_finset_sum _ fun j _ => h_dj_abs j).const_mul _))
                (Filter.Eventually.of_forall h_pw2)
          _ ≤ (∑ j, |vGrad g v j|) * M₀ +
              |g v| * (M₁ + M₂ + M₃) := by
              rw [integral_add (h_f_abs.const_mul _)
                ((integrable_finset_sum _ fun j _ => h_dj_abs j).const_mul _),
                integral_const_mul, integral_const_mul]
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left (hM₀ v)
                  (Finset.sum_nonneg fun j _ => abs_nonneg _)
              · apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
                rw [integral_finset_sum _ fun j _ => h_dj_abs j]
                simp only [Fin.sum_univ_three]
                linarith [hM₁ v, hM₂ v, hM₃ v]
          _ ≤ 3 * ‖iteratedFDeriv ℝ 1 g v‖ * M₀ +
              ‖iteratedFDeriv ℝ 0 g v‖ * (M₁ + M₂ + M₃) := by
              gcongr
              · simp only [Fin.sum_univ_three]
                linarith [hvg 0, hvg 1, hvg 2]
              · rw [← hf0]
          _ = M₀ * (3 * ‖iteratedFDeriv ℝ 1 g v‖) +
              (M₁ + M₂ + M₃) * ‖iteratedFDeriv ℝ 0 g v‖ := by ring

/-- The Landau flux × log(f) is integrable for the Coulomb kernel.
    Uses the uniform Newtonian bound to control the flux pointwise. -/
lemma flux_times_log_integrable_coulomb
    {f : Torus3 → (Fin 3 → ℝ) → ℝ}
    (hf_pos : ∀ x v, 0 < f x v)
    (hf_smooth_v : ∀ x, ContDiff ℝ 3 (f x))
    (hSchwartz : UniformSchwartzDecay f)
    (hLogBound : ∃ (C_log : ℝ) (K_log : ℕ), ∀ (x : Torus3) (v : Fin 3 → ℝ),
      |Real.log (f x v)| ≤ C_log * (1 + ‖v‖) ^ K_log)
    (x : Torus3) (i : Fin 3) :
    Integrable (fun v =>
      (∫ w, mulVec (landauMatrix coulombKernel (v - w))
        (f x w • vGrad (f x) v - f x v • vGrad (f x) w)) i *
        (Real.log ∘ f x) v) := by
  obtain ⟨C_log, K_log, hLB⟩ := hLogBound
  -- Schwartz decay for f(x) and ∂_j(f(x))
  have hf_decay : ∀ N : ℕ, ∃ C > 0, ∀ w, |f x w| * (1 + ‖w‖) ^ N ≤ C := by
    intro N; obtain ⟨C, hC, hb⟩ := hSchwartz.hDecay N (k := 0) (by omega)
    exact ⟨C, hC, fun w => by simpa using hb x w⟩
  have hdf_decay : ∀ j : Fin 3, ∀ N : ℕ, ∃ C > 0, ∀ w,
      |fderiv ℝ (f x) w (Pi.single j 1)| * (1 + ‖w‖) ^ N ≤ C :=
    fun j N => schwartz_partial_decay hSchwartz x j N
  -- Uniform Newtonian bounds
  obtain ⟨M₀, hM₀, hM₀_bound⟩ := newtonian_schwartz_uniform_bound (fun w => f x w)
    (fun N => by obtain ⟨C, hC, hb⟩ := hf_decay N; exact ⟨C, hC, fun w => by
      show |(fun w => f x w) w| * _ ≤ C; exact hb w⟩)
    (hf_smooth_v x).continuous.aestronglyMeasurable
  have hMj : ∀ j : Fin 3, ∃ M > 0, ∀ v,
      ∫ w, ‖v - w‖⁻¹ * |fderiv ℝ (f x) w (Pi.single j 1)| ≤ M := by
    intro j
    exact newtonian_schwartz_uniform_bound _ (hdf_decay j)
      ((hf_smooth_v x).continuous_fderiv (by norm_num)
        |>.eval_const (Pi.single j 1)).aestronglyMeasurable
  obtain ⟨M₁, hM₁, hM₁b⟩ := hMj 0
  obtain ⟨M₂, hM₂, hM₂b⟩ := hMj 1
  obtain ⟨M₃, hM₃, hM₃b⟩ := hMj 2
  -- Dominating function: C_bound / (1+‖v‖)^4
  -- |flux_i(v)| ≤ M₀ * ∑|∂_jf(v)| + M_df * f(v)
  -- |flux_i(v) * log(f(v))| ≤ (M₀ * ∑|∂_jf(v)| + M_df * f(v)) * C_log * (1+‖v‖)^K
  -- Each term like |∂_jf(v)| * (1+‖v‖)^K ≤ C_{j,K+4}/(1+‖v‖)^4
  obtain ⟨C_f, hC_f, hC_f_bound⟩ := hSchwartz.hDecay (K_log + 4) (k := 0) (by omega)
  obtain ⟨C_df, hC_df, hC_df_bound⟩ := hSchwartz.hDecay (K_log + 4) (k := 1) (by omega)
  set C_bound := (M₀ * 3 * C_df + (M₁ + M₂ + M₃) * C_f) * C_log + 1
  -- Flux integrability for eval_integral
  have hf_schwartz_x : ∀ (N : ℕ) {k : ℕ}, k ≤ 2 → ∃ C > 0, ∀ v,
      ‖iteratedFDeriv ℝ k (f x) v‖ * (1 + ‖v‖) ^ N ≤ C :=
    fun N {k} hk => (hSchwartz.hDecay N hk).imp fun C hC => ⟨hC.1, fun v => hC.2 x v⟩
  have hFlux : ∀ v, Integrable (fun w => mulVec (landauMatrix coulombKernel (v - w))
      (f x w • vGrad (f x) v - f x v • vGrad (f x) w)) :=
    fun v => landau_flux_integrable_coulomb (f x) (fun v => hf_pos x v)
      (hf_smooth_v x) hf_schwartz_x v
  have h_flux_bound := coulomb_flux_component_pointwise_le (hf_smooth_v x) hf_decay hdf_decay
    hFlux M₀ M₁ M₂ M₃ hM₀ hM₁ hM₂ hM₃ hM₀_bound hM₁b hM₂b hM₃b i
  -- Apply Integrable.mono' with C_bound / (1+‖v‖)^4
  refine (inverse_poly_integrable C_bound).mono' ?_ (Filter.Eventually.of_forall fun v => ?_)
  · -- AEStronglyMeasurable of flux_i × log(f)
    refine AEStronglyMeasurable.mul ?_ ?_
    · -- flux_i is AEStronglyMeasurable: parametric integral of jointly measurable integrand
      exact flux_component_aestronglyMeasurable (f x) (hf_smooth_v x) hFlux i
    · -- log ∘ f x is continuous hence AEStronglyMeasurable
      exact ((hf_smooth_v x).continuous.log (fun v => ne_of_gt (hf_pos x v))).aestronglyMeasurable
  · -- Pointwise bound: ‖flux_i(v) * log(f x v)‖ ≤ C_bound / (1+‖v‖)^4
    rw [Real.norm_eq_abs, abs_mul]
    have hv_pos : (0 : ℝ) < 1 + ‖v‖ := by linarith [norm_nonneg v]
    have h_pow_pos : (0 : ℝ) < (1 + ‖v‖) ^ (K_log + 4) := by positivity
    have h_iterfd0_le : ‖iteratedFDeriv ℝ 0 (f x) v‖ ≤
        C_f / (1 + ‖v‖) ^ (K_log + 4) :=
      (le_div_iff₀ h_pow_pos).mpr (hC_f_bound x v)
    have h_iterfd1_le : ‖iteratedFDeriv ℝ 1 (f x) v‖ ≤
        C_df / (1 + ‖v‖) ^ (K_log + 4) :=
      (le_div_iff₀ h_pow_pos).mpr (hC_df_bound x v)
    have hlog : |(Real.log ∘ f x) v| ≤ C_log * (1 + ‖v‖) ^ K_log := hLB x v
    -- Chain: |flux| * |log| ≤ bound1 * |log| ≤ bound1 * bound2 ≤ ... ≤ C_bound/(1+‖v‖)^4
    have h_Clog_nn : (0:ℝ) ≤ C_log * (1 + ‖v‖) ^ K_log :=
      le_trans (abs_nonneg _) hlog
    calc |(∫ w, mulVec (landauMatrix coulombKernel (v - w))
            (f x w • vGrad (f x) v - f x v • vGrad (f x) w)) i| *
          |(Real.log ∘ f x) v|
        ≤ (M₀ * (3 * ‖iteratedFDeriv ℝ 1 (f x) v‖) +
           (M₁ + M₂ + M₃) * ‖iteratedFDeriv ℝ 0 (f x) v‖) *
          |(Real.log ∘ f x) v| :=
          mul_le_mul_of_nonneg_right (h_flux_bound v) (abs_nonneg _)
      _ ≤ (M₀ * (3 * ‖iteratedFDeriv ℝ 1 (f x) v‖) +
           (M₁ + M₂ + M₃) * ‖iteratedFDeriv ℝ 0 (f x) v‖) *
          (C_log * (1 + ‖v‖) ^ K_log) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ (M₀ * (3 * (C_df / (1 + ‖v‖) ^ (K_log + 4))) +
           (M₁ + M₂ + M₃) * (C_f / (1 + ‖v‖) ^ (K_log + 4))) *
          (C_log * (1 + ‖v‖) ^ K_log) := by
          gcongr
      _ = (M₀ * 3 * C_df + (M₁ + M₂ + M₃) * C_f) * C_log / (1 + ‖v‖) ^ 4 := by
          rw [pow_add (1 + ‖v‖) K_log 4]; field_simp
      _ ≤ C_bound / (1 + ‖v‖) ^ 4 := by
          gcongr
          simp only [C_bound]
          linarith

-- ============================================================================
-- Flux component bound with polynomial gradient hypothesis
-- ============================================================================


/-- Pointwise bound on the Coulomb flux component: |flux_i(v)| ≤ Cf * g(v) * (1+‖v‖)^Kg.
    Combines the Newtonian potential bound (∫ ‖v-w‖⁻¹ |g| ≤ M) with the polynomial
    gradient bound |∂_j g(v)| ≤ Cg * (1+‖v‖)^Kg * g(v). -/
lemma coulomb_flux_component_bound
    (g : (Fin 3 → ℝ) → ℝ)
    (hg_pos : ∀ v, 0 < g v)
    (hg_smooth : ContDiff ℝ 3 g)
    (hg_schwartz : ∀ (N : ℕ) {k : ℕ}, k ≤ 2 → ∃ C > 0, ∀ v,
      ‖iteratedFDeriv ℝ k g v‖ * (1 + ‖v‖) ^ N ≤ C)
    {Cg : ℝ} {Kg : ℕ}
    (hGrad : ∀ (v : Fin 3 → ℝ) (j : Fin 3),
      |fderiv ℝ g v (Pi.single j 1)| ≤ Cg * (1 + ‖v‖) ^ Kg * g v)
    (i : Fin 3) :
    ∃ Cf > 0, ∀ v,
    |(∫ w, mulVec (landauMatrix coulombKernel (v - w))
      (g w • vGrad g v - g v • vGrad g w)) i| ≤ Cf * g v * (1 + ‖v‖) ^ Kg := by
  -- Schwartz decay for g and ∂_j g
  have hg_decay := schwartz_pointwise_decay hg_schwartz
  have hdg_decay := schwartz_fderiv_component_decay hg_schwartz
  -- Newtonian uniform bounds
  obtain ⟨M₀, hM₀, hM₀_bound⟩ := newtonian_schwartz_uniform_bound g hg_decay
    hg_smooth.continuous.aestronglyMeasurable
  have hMj : ∀ j, ∃ M > 0, ∀ v,
      ∫ w, ‖v - w‖⁻¹ * |fderiv ℝ g w (Pi.single j 1)| ≤ M :=
    fun j => newtonian_schwartz_uniform_bound _ (hdg_decay j)
      ((hg_smooth.continuous_fderiv (by norm_num)).clm_apply continuous_const).aestronglyMeasurable
  obtain ⟨M₁, hM₁, hM₁b⟩ := hMj 0
  obtain ⟨M₂, hM₂, hM₂b⟩ := hMj 1
  obtain ⟨M₃, hM₃, hM₃b⟩ := hMj 2
  set M_df := M₁ + M₂ + M₃
  -- Flux integrability
  have hFlux : ∀ v, Integrable (fun w => mulVec (landauMatrix coulombKernel (v - w))
      (g w • vGrad g v - g v • vGrad g w)) :=
    fun v => landau_flux_integrable_coulomb g hg_pos hg_smooth hg_schwartz v
  -- Integrability of ‖v-w‖⁻¹ * |g| and ‖v-w‖⁻¹ * |∂_j g|
  have h_f_abs : ∀ v, Integrable (fun w => ‖v - w‖⁻¹ * |g w|) := fun v =>
    (inv_norm_schwartz_integrable g hg_decay
      hg_smooth.continuous.aestronglyMeasurable v).norm.congr
      (Filter.Eventually.of_forall fun w => by
        change ‖‖v - w‖⁻¹ * g w‖ = ‖v - w‖⁻¹ * |g w|
        rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), Real.norm_eq_abs])
  have h_dj_abs : ∀ j : Fin 3, ∀ v,
      Integrable (fun w => ‖v - w‖⁻¹ * |vGrad g w j|) := fun j v =>
    (inv_norm_schwartz_integrable _ (hdg_decay j)
      ((hg_smooth.continuous_fderiv (by norm_num)).clm_apply continuous_const).aestronglyMeasurable
      v).norm.congr (Filter.Eventually.of_forall fun w => by
        change ‖‖v - w‖⁻¹ * fderiv ℝ g w (Pi.single j 1)‖ = ‖v - w‖⁻¹ * |vGrad g w j|
        rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
          Real.norm_eq_abs]; rfl)
  -- Cg ≥ 0 from the gradient bound (|∂_j g| ≤ Cg * poly * g, all nonneg)
  have hCg_nn : 0 ≤ Cg := by
    by_contra h_neg; push Not at h_neg
    have : Cg * (1 + ‖(0 : Fin 3 → ℝ)‖) ^ Kg * g 0 < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos h_neg (by positivity)) (hg_pos 0)
    linarith [hGrad 0 0, abs_nonneg (fderiv ℝ g 0 (Pi.single 0 1))]
  -- Target constant
  refine ⟨3 * Cg * M₀ + M_df + 1, by nlinarith, fun v => ?_⟩
  set u := fun w => g w • vGrad g v - g v • vGrad g w with hu_def
  -- Step 1: pull component i out of integral
  rw [eval_integral (fun j => (hFlux v).eval j)]
  -- Step 2: pointwise bound |(A *ᵥ u)_i| ≤ ‖v-w‖⁻¹ * ∑ |u_j|
  have h_pw : ∀ w, |(landauMatrix coulombKernel (v - w) *ᵥ u w) i| ≤
      ‖v - w‖⁻¹ * ∑ j : Fin 3, |u w j| := by
    intro w
    by_cases hvw : v - w = 0
    · have : v = w := sub_eq_zero.mp hvw
      subst this; simp [mulVec, dotProduct, landauMatrix, innerLandauMatrix,
        normSq, vecMulVec, eucNorm, coulombKernel]
    · simp only [mulVec, dotProduct]
      calc |∑ j, landauMatrix coulombKernel (v - w) i j * u w j|
          ≤ ∑ j, |landauMatrix coulombKernel (v - w) i j * u w j| :=
            Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j, |landauMatrix coulombKernel (v - w) i j| * |u w j| := by
            congr 1
            ext j
            exact abs_mul _ _
        _ ≤ ∑ j, ‖v - w‖⁻¹ * |u w j| :=
            Finset.sum_le_sum fun j _ =>
              mul_le_mul_of_nonneg_right (coulomb_landauMatrix_entry_le_pi _ _ _ hvw)
                (abs_nonneg _)
        _ = ‖v - w‖⁻¹ * ∑ j, |u w j| := (Finset.mul_sum _ _ _).symm
  -- Step 3: triangle inequality |u_j(w)| ≤ g(w)*|∂_jg(v)| + g(v)*|∂_jg(w)|
  have h_tri : ∀ w j, |u w j| ≤
      g w * |vGrad g v j| + g v * |vGrad g w j| := by
    intro w j
    simp only [hu_def, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    have := norm_sub_le (g w * vGrad g v j) (g v * vGrad g w j)
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_mul, abs_mul, abs_of_pos (hg_pos w), abs_of_pos (hg_pos v)] at this
  have h_sum_tri : ∀ w, ∑ j : Fin 3, |u w j| ≤
      g w * ∑ j : Fin 3, |vGrad g v j| + g v * ∑ j : Fin 3, |vGrad g w j| := by
    intro w
    calc ∑ j, |u w j|
        ≤ ∑ j, (g w * |vGrad g v j| + g v * |vGrad g w j|) :=
          Finset.sum_le_sum fun j _ => h_tri w j
      _ = g w * ∑ j, |vGrad g v j| + g v * ∑ j, |vGrad g w j| := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  -- Step 4: pointwise bound for integral_mono
  have h_pw2 : ∀ w, ‖v - w‖⁻¹ * ∑ j : Fin 3, |u w j| ≤
      (∑ j : Fin 3, |vGrad g v j|) * (‖v - w‖⁻¹ * |g w|) +
      g v * ∑ j : Fin 3, (‖v - w‖⁻¹ * |vGrad g w j|) := by
    intro w
    calc ‖v - w‖⁻¹ * ∑ j, |u w j|
        ≤ ‖v - w‖⁻¹ * (g w * ∑ j, |vGrad g v j| +
            g v * ∑ j, |vGrad g w j|) :=
          mul_le_mul_of_nonneg_left (h_sum_tri w) (inv_nonneg.mpr (norm_nonneg _))
      _ = _ := by
          rw [abs_of_pos (hg_pos w)]
          simp only [← Finset.mul_sum]; ring
  -- Step 5: integrate and apply newtonian bounds
  have h_rhs_int : Integrable (fun w =>
      (∑ j : Fin 3, |vGrad g v j|) * (‖v - w‖⁻¹ * |g w|) +
      g v * ∑ j : Fin 3, (‖v - w‖⁻¹ * |vGrad g w j|)) :=
    ((h_f_abs v).const_mul _).add
      ((integrable_finset_sum _ fun j _ => h_dj_abs j v).const_mul _)
  calc |∫ w, (landauMatrix coulombKernel (v - w) *ᵥ u w) i|
      ≤ ∫ w, |(landauMatrix coulombKernel (v - w) *ᵥ u w) i| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ w, ((∑ j : Fin 3, |vGrad g v j|) * (‖v - w‖⁻¹ * |g w|) +
        g v * ∑ j : Fin 3, (‖v - w‖⁻¹ * |vGrad g w j|)) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun w => abs_nonneg _)
          h_rhs_int
          (Filter.Eventually.of_forall fun w => le_trans (h_pw w) (h_pw2 w))
    _ ≤ (∑ j : Fin 3, |vGrad g v j|) * M₀ + g v * M_df := by
        rw [integral_add ((h_f_abs v).const_mul _)
          ((integrable_finset_sum _ fun j _ => h_dj_abs j v).const_mul _),
          integral_const_mul, integral_const_mul,
          integral_finset_sum _ fun j _ => h_dj_abs j v]
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (hM₀_bound v)
            (Finset.sum_nonneg fun j _ => abs_nonneg _)
        · apply mul_le_mul_of_nonneg_left _ (le_of_lt (hg_pos v))
          simp only [Fin.sum_univ_three, vGrad, M_df]
          linarith [hM₁b v, hM₂b v, hM₃b v]
    _ ≤ 3 * (Cg * (1 + ‖v‖) ^ Kg * g v) * M₀ + g v * M_df := by
        gcongr
        simp only [Fin.sum_univ_three, vGrad]
        linarith [hGrad v 0, hGrad v 1, hGrad v 2]
    _ ≤ (3 * Cg * M₀ + M_df) * g v * (1 + ‖v‖) ^ Kg := by
        have h1 : (1 : ℝ) ≤ (1 + ‖v‖) ^ Kg :=
          one_le_pow₀ (by linarith [norm_nonneg v])
        have hgv : (0 : ℝ) < g v := hg_pos v
        have hMdf : (0 : ℝ) < M_df := by simp only [M_df]; linarith
        -- Need: 3*Cg*M₀*(g v)*(1+‖v‖)^Kg + M_df*(g v)*(1+‖v‖)^Kg
        --     ≥ 3*(Cg*(1+‖v‖)^Kg*(g v))*M₀ + (g v)*M_df
        -- i.e., M_df*(g v)*((1+‖v‖)^Kg - 1) ≥ 0
        nlinarith [mul_nonneg (mul_nonneg hMdf.le hgv.le) (sub_nonneg.mpr h1)]
    _ ≤ (3 * Cg * M₀ + M_df + 1) * g v * (1 + ‖v‖) ^ Kg := by
        have h1 : (1 : ℝ) ≤ (1 + ‖v‖) ^ Kg :=
          one_le_pow₀ (by linarith [norm_nonneg v])
        nlinarith [hg_pos v]

/-- The product flux_i(v) * score_i(v) is integrable for the Coulomb kernel.
    Uses coulomb_flux_component_bound (|flux_i| ≤ Cf*f*(1+‖v‖)^Kg) and
    score_bound_of_grad_bound (|score_i| ≤ Cg*(1+‖v‖)^Kg), giving a
    Cf*Cg*(1+‖v‖)^{2Kg}*f(v) dominator which is integrable by Schwartz decay. -/
lemma coulomb_ibp_f_dg_integrable
    (f : (Fin 3 → ℝ) → ℝ) (hf_pos : ∀ v, 0 < f v) (hf_smooth : ContDiff ℝ 3 f)
    (hf_schwartz : ∀ (N : ℕ) {k : ℕ}, k ≤ 2 → ∃ C > 0, ∀ v,
      ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
    {Cg : ℝ} {Kg : ℕ}
    (hGrad : ∀ v i, |fderiv ℝ f v (Pi.single i 1)| ≤ Cg * (1 + ‖v‖) ^ Kg * f v)
    (i : Fin 3) :
    Integrable (fun v =>
      (∫ w, mulVec (landauMatrix coulombKernel (v - w))
        (f w • vGrad f v - f v • vGrad f w)) i *
      fderiv ℝ (Real.log ∘ f) v (Pi.single i 1)) := by
  have h_score : ∀ v, |fderiv ℝ (Real.log ∘ f) v (Pi.single i 1)| ≤
      Cg * (1 + ‖v‖) ^ Kg := fun v =>
    score_bound_of_grad_bound hf_pos hf_smooth hGrad v i
  obtain ⟨Cf, hCf_pos, hCf⟩ :=
    coulomb_flux_component_bound f hf_pos hf_smooth hf_schwartz hGrad i
  -- Polynomial-weighted integrability of f from Schwartz decay
  have h_poly_int : Integrable (fun v => (1 + ‖v‖) ^ (2 * Kg) * f v) :=
    schwartz_poly_mul_integrable hf_pos hf_smooth.continuous
      (schwartz_pointwise_decay hf_schwartz) (2 * Kg)
  -- Combine: |flux_i * score_i| ≤ Cf*Cg * (1+‖v‖)^{2Kg} * f(v)
  apply (h_poly_int.const_mul (Cf * Cg)).mono'
  · exact AEStronglyMeasurable.mul
      (flux_component_aestronglyMeasurable f hf_smooth
        (fun v => landau_flux_integrable_coulomb f hf_pos hf_smooth hf_schwartz v) i)
      ((ContDiff.log hf_smooth (fun v => ne_of_gt (hf_pos v))).continuous_fderiv (by norm_num)
        |>.clm_apply continuous_const).aestronglyMeasurable
  · filter_upwards with v
    rw [Real.norm_eq_abs, abs_mul]
    have hCf_nn : (0 : ℝ) ≤ Cf * f v * (1 + ‖v‖) ^ Kg :=
      mul_nonneg (mul_nonneg (le_of_lt hCf_pos) (le_of_lt (hf_pos v)))
        (pow_nonneg (by linarith [norm_nonneg v]) _)
    calc |(∫ w, mulVec (landauMatrix coulombKernel (v - w))
            (f w • vGrad f v - f v • vGrad f w)) i| *
          |fderiv ℝ (Real.log ∘ f) v (Pi.single i 1)|
        ≤ (Cf * f v * (1 + ‖v‖) ^ Kg) * (Cg * (1 + ‖v‖) ^ Kg) :=
          mul_le_mul (hCf v) (h_score v) (abs_nonneg _) hCf_nn
      _ = Cf * Cg * ((1 + ‖v‖) ^ (2 * Kg) * f v) := by
          rw [show 2 * Kg = Kg + Kg from by omega, pow_add]; ring

end VML
