/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import LeanPool.Clawristotle.CoulombFlux
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Coulomb Entry Convolution: Differentiability and Bounds

Establishes that partial derivatives of functions with C² decay are C² decay,
Coulomb kernel entry convolutions are differentiable with uniform derivative bounds,
and the full Coulomb flux component is differentiable with a decomposition formula.
-/

open MeasureTheory Matrix Finset BigOperators Real

noncomputable section
namespace VML

private lemma landauMatrix_coulombKernel_zero (i j : Fin 3) :
    landauMatrix coulombKernel 0 i j = 0 := by
  simp [landauMatrix, innerLandauMatrix, normSq, eucNorm, coulombKernel,
    dotProduct, vecMulVec]

/-- ‖·‖⁻¹ times a bounded integrable function is integrable.
    Near v: the function is bounded, ‖·‖⁻¹ is locally integrable.
    Far from v: ‖v-w‖⁻¹ ≤ 1, so the product ≤ |g w| which is integrable. -/
private lemma inv_norm_bounded_integrable
    {g : (Fin 3 → ℝ) → ℝ} {M : ℝ}
    (hg_bounded : ∀ w, |g w| ≤ M)
    (hg_int : Integrable g)
    (hg_meas : AEStronglyMeasurable g volume)
    (v : Fin 3 → ℝ) :
    Integrable (fun w => ‖v - w‖⁻¹ * g w) := by
  have h_near : IntegrableOn (fun w => ‖v - w‖⁻¹ * g w) (Metric.closedBall v 1) := by
    have hK_local := inv_norm_local_integrable 1 one_pos
    have h_inv_ball : IntegrableOn (fun w => ‖v - w‖⁻¹) (Metric.closedBall v 1) := by
      rw [← integrable_indicator_iff measurableSet_closedBall] at *
      convert hK_local.comp_sub_left v using 1
      ext w; simp [Set.indicator, dist_eq_norm', norm_sub_rev]
    exact (h_inv_ball.const_mul M).mono'
      ((Measurable.aestronglyMeasurable (Measurable.inv
        (measurable_norm.comp (measurable_const.sub measurable_id')))).mul
        (hg_meas.mono_measure Measure.restrict_le_self))
      (by filter_upwards [ae_restrict_mem measurableSet_closedBall] with w _
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
          exact (mul_le_mul_of_nonneg_left (hg_bounded w)
            (inv_nonneg.mpr (norm_nonneg _))).trans (by rw [mul_comm]))
  have h_far : IntegrableOn (fun w => ‖v - w‖⁻¹ * g w)
      (Set.univ \ Metric.closedBall v 1) := by
    exact hg_int.norm.integrableOn.mono'
      ((Measurable.aestronglyMeasurable (Measurable.inv
        (measurable_norm.comp (measurable_const.sub measurable_id')))).mul
        (hg_meas.mono_measure Measure.restrict_le_self))
      (by filter_upwards [ae_restrict_mem (MeasurableSet.univ.diff measurableSet_closedBall)]
          with w hw
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
          have hw_far : 1 ≤ ‖v - w‖ := by
            rw [Set.mem_diff] at hw
            by_contra h_lt; rw [not_le] at h_lt
            exact hw.2 (Metric.mem_closedBall.mpr (by rw [dist_comm, dist_eq_norm]; linarith))
          calc ‖v - w‖⁻¹ * |g w| ≤ 1 * |g w| :=
                mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hw_far) (abs_nonneg _)
            _ = |g w| := one_mul _
            _ = ‖g w‖ := (Real.norm_eq_abs _).symm)
  rw [← integrableOn_univ]
  rw [show (Set.univ : Set (Fin 3 → ℝ)) =
    Metric.closedBall v 1 ∪ (Set.univ \ Metric.closedBall v 1) from by
    simp [Set.union_diff_cancel (Set.subset_univ _)]]
  exact h_near.union h_far

/-- Partial derivatives of a Schwartz function are Schwartz. Uses
    `ContinuousLinearMap.iteratedFDeriv_comp_left` + `norm_iteratedFDeriv_fderiv`. -/
lemma schwartz_fderiv_component_schwartz
    (f : (Fin 3 → ℝ) → ℝ) (hf_smooth : ContDiff ℝ 3 f)
    (hf_schwartz : ∀ (N : ℕ) {k : ℕ}, k ≤ 2 →
      ∃ C > 0, ∀ v, ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
    (j : Fin 3) (N : ℕ) {k : ℕ} (hk : k + 1 ≤ 2) :
    ∃ C > 0, ∀ v : Fin 3 → ℝ,
      ‖iteratedFDeriv ℝ k (fun w => fderiv ℝ f w (Pi.single j 1)) v‖ *
        (1 + ‖v‖) ^ N ≤ C := by
  obtain ⟨C, hC_pos, hC⟩ := hf_schwartz N hk
  refine ⟨C, hC_pos, fun v => ?_⟩
  have h1 : (fun w => fderiv ℝ f w (Pi.single j 1)) =
      (ContinuousLinearMap.apply ℝ ℝ (Pi.single j 1 : Fin 3 → ℝ)) ∘ (fderiv ℝ f) := rfl
  have h_cont_diff : ContDiff ℝ k (fderiv ℝ f) :=
    hf_smooth.fderiv_right (by exact_mod_cast (by omega : k + 1 ≤ 3))
  rw [h1, ContinuousLinearMap.iteratedFDeriv_comp_left
    (ContinuousLinearMap.apply ℝ ℝ (Pi.single j 1)) h_cont_diff.contDiffAt le_rfl]
  have h_norm_eval : ‖(ContinuousLinearMap.apply ℝ ℝ (Pi.single j 1 : Fin 3 → ℝ))‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro L
    simp only [ContinuousLinearMap.apply_apply]
    exact le_trans (L.le_opNorm _) (by simp [Pi.norm_single])
  calc ‖(ContinuousLinearMap.apply ℝ ℝ (Pi.single j 1 : Fin 3 → ℝ)).compContinuousMultilinearMap
        (iteratedFDeriv ℝ k (fderiv ℝ f) v)‖ * (1 + ‖v‖) ^ N
      ≤ ‖ContinuousLinearMap.apply ℝ ℝ (Pi.single j 1 : Fin 3 → ℝ)‖ *
        ‖iteratedFDeriv ℝ k (fderiv ℝ f) v‖ * (1 + ‖v‖) ^ N := by
          gcongr; exact ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ 1 * ‖iteratedFDeriv ℝ k (fderiv ℝ f) v‖ * (1 + ‖v‖) ^ N := by gcongr
    _ = ‖iteratedFDeriv ℝ (k + 1) f v‖ * (1 + ‖v‖) ^ N := by
          rw [one_mul, norm_iteratedFDeriv_fderiv]
    _ ≤ C := hC v

/-- Coulomb matrix entry times Schwartz function is integrable in ℝ³.
    Domination: |A_{ij}(v-w) * g(w)| ≤ ‖v-w‖⁻¹ * |g(w)| by entry bound. -/
lemma coulomb_entry_schwartz_integrable
    (g : (Fin 3 → ℝ) → ℝ) (hg_smooth : ContDiff ℝ 2 g)
    (hg_decay : ∀ N : ℕ, ∃ C > 0, ∀ v, |g v| * (1 + ‖v‖) ^ N ≤ C)
    (v : Fin 3 → ℝ) (i j : Fin 3) :
    Integrable (fun w => landauMatrix coulombKernel (v - w) i j * g w) := by
  refine (inv_norm_schwartz_integrable g hg_decay hg_smooth.continuous.aestronglyMeasurable v).mono
    ?_ (ae_of_all _ fun w => ?_)
  · -- AEStronglyMeasurable: matrix entry is measurable, g is continuous
    change AEStronglyMeasurable (fun w => coulombKernel (eucNorm (v - w)) *
        innerLandauMatrix (v - w) i j * g w) volume
    exact ((((Measurable.ite measurableSet_Iic measurable_const
      (measurable_id.pow_const _)).comp ((Continuous.measurable (Continuous.dotProduct
        (continuous_const.sub continuous_id')
        (continuous_const.sub continuous_id'))).sqrt)).mul
      (by apply Continuous.measurable; unfold innerLandauMatrix
          simp only [normSq, dotProduct_sub, sub_dotProduct, vecMulVec, Pi.sub_apply, sub_apply,
            smul_apply, smul_eq_mul, of_apply]
          fun_prop (disch := norm_num)
      )).aestronglyMeasurable).mul hg_smooth.continuous.aestronglyMeasurable
  · -- Domination bound
    rw [norm_mul, norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    by_cases hvw : v - w = 0
    · simp [hvw, landauMatrix_coulombKernel_zero]
    · exact mul_le_mul_of_nonneg_right
        (le_trans (le_of_eq (Real.norm_eq_abs _)) (coulomb_landauMatrix_entry_le_pi _ _ _ hvw))
        (norm_nonneg _)

/-- Core helper: the derivative of the Coulomb entry convolution at v₀ equals
    ∫ A(u) • fderiv(g)(v₀-u) du, with HasFDerivAt witness. -/
private lemma coulomb_entry_conv_hasFDerivAt_aux
    (g : (Fin 3 → ℝ) → ℝ) (hg_smooth : ContDiff ℝ 2 g)
    (hg_schwartz : ∀ (N : ℕ) {k : ℕ}, k ≤ 1 → ∃ C > 0, ∀ v,
      ‖iteratedFDeriv ℝ k g v‖ * (1 + ‖v‖) ^ N ≤ C)
    (i j : Fin 3) (v₀ : Fin 3 → ℝ) :
    HasFDerivAt (fun v => ∫ u, landauMatrix coulombKernel u i j * g (v - u))
      (∫ u, landauMatrix coulombKernel u i j • fderiv ℝ g (v₀ - u)) v₀ := by
  have hg_decay : ∀ N : ℕ, ∃ C > 0, ∀ v, |g v| * (1 + ‖v‖) ^ N ≤ C :=
    fun N => (hg_schwartz N (by norm_num : 0 ≤ 1)).imp fun C ⟨hC, hb⟩ =>
      ⟨hC, fun v => by simpa [iteratedFDeriv_zero_eq_comp] using hb v⟩
  have hfderiv_decay : ∀ N : ℕ, ∃ C > 0, ∀ w, ‖fderiv ℝ g w‖ * (1 + ‖w‖) ^ N ≤ C :=
    fun N => (hg_schwartz N le_rfl).imp fun C ⟨hC, hb⟩ =>
      ⟨hC, fun w => by rw [norm_fderiv_eq_iteratedFDeriv_one]; exact hb w⟩
  -- Shift bound: for v ∈ ball(v₀, 1), ‖fderiv g(v-u)‖ ≤ D/(1+‖v₀-u‖)^4
  -- Uses Schwartz decay with N=8 and triangle inequality: 1+‖v-u‖ ≥ (1+‖v₀-u‖)/2
  obtain ⟨D, hD_pos, hD_bound⟩ : ∃ D > 0, ∀ u : Fin 3 → ℝ, ∀ v ∈ Metric.ball v₀ 1,
      ‖fderiv ℝ g (v - u)‖ ≤ D / (1 + ‖v₀ - u‖) ^ 4 := by
    obtain ⟨C8, hC8_pos, hC8⟩ := hfderiv_decay 8
    refine ⟨C8 * 2 ^ 8, by positivity, fun u v hv => ?_⟩
    have hv_dist : ‖v - v₀‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hv
    -- Key inequality: 1 + ‖v-u‖ ≥ (1 + ‖v₀-u‖)/2
    have h_half : (1 + ‖v₀ - u‖) / 2 ≤ 1 + ‖v - u‖ := by
      have : ‖v₀ - u‖ ≤ ‖v - u‖ + ‖v - v₀‖ := by
        calc ‖v₀ - u‖ = ‖(v - u) - (v - v₀)‖ := by congr 1; abel
          _ ≤ ‖v - u‖ + ‖v - v₀‖ := norm_sub_le _ _
      linarith [norm_nonneg (v - u)]
    have h_pos : 0 < 1 + ‖v - u‖ := by linarith [norm_nonneg (v - u)]
    have h_pos2 : 0 < 1 + ‖v₀ - u‖ := by linarith [norm_nonneg (v₀ - u)]
    calc ‖fderiv ℝ g (v - u)‖
        ≤ C8 / (1 + ‖v - u‖) ^ 8 := by
          exact (le_div_iff₀ (by positivity)).mpr (hC8 (v - u))
      _ ≤ C8 / ((1 + ‖v₀ - u‖) / 2) ^ 8 := by
          gcongr
      _ = C8 * 2 ^ 8 / (1 + ‖v₀ - u‖) ^ 8 := by
          rw [div_pow]; field_simp
      _ ≤ C8 * 2 ^ 8 / (1 + ‖v₀ - u‖) ^ 4 := by
          gcongr
          · linarith [norm_nonneg (v₀ - u)]
          · omega
  have hg_diff : ∀ w, HasFDerivAt g (fderiv ℝ g w) w :=
    fun w => (hg_smooth.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  -- Use the shifted-Schwartz bound for the dominator
  have h_int_shift : ∀ x, Integrable (fun u => landauMatrix coulombKernel u i j * g (x - u)) :=
    fun x => ((coulomb_entry_schwartz_integrable g hg_smooth hg_decay x i j).comp_sub_left x).congr
      (ae_of_all _ fun u => by abel_nf)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun v u => landauMatrix coulombKernel u i j • fderiv ℝ g (v - u))
    (bound := fun u => ‖u‖⁻¹ * (D / (1 + ‖v₀ - u‖) ^ 4))
    (s := Metric.ball v₀ 1) (Metric.ball_mem_nhds v₀ one_pos)
    ?_ ?_ ?_ ?_ ?_ ?_
  · -- F measurable
    exact Filter.Eventually.of_forall fun v => (h_int_shift v).aestronglyMeasurable
  · -- F integrable at v₀
    exact h_int_shift v₀
  · -- F' measurable at v₀
    have h_sc : AEStronglyMeasurable (fun u => landauMatrix coulombKernel u i j) volume := by
      change AEStronglyMeasurable (fun u => coulombKernel (eucNorm u) *
        innerLandauMatrix u i j) volume
      exact ((((Measurable.ite measurableSet_Iic measurable_const
        (measurable_id.pow_const _)).comp ((Continuous.measurable (Continuous.dotProduct
          continuous_id' continuous_id')).sqrt)).mul
        (by apply Continuous.measurable; unfold innerLandauMatrix
            simp only [normSq, vecMulVec, sub_apply, smul_apply, smul_eq_mul, of_apply]
            fun_prop (disch := norm_num)
        )).aestronglyMeasurable)
    exact h_sc.smul
      ((ContDiff.continuous (n := 1) (hg_smooth.fderiv_right (by norm_num))).comp
        (continuous_const.sub continuous_id')).aestronglyMeasurable
  · -- Bound: ‖F'(v, u)‖ ≤ bound(u) for v ∈ ball(v₀, 1)
    apply ae_of_all
    intro u v hv
    simp only [norm_smul]
    by_cases hu : u = 0
    · simp [hu, landauMatrix_coulombKernel_zero]
    · calc ‖landauMatrix coulombKernel u i j‖ * ‖fderiv ℝ g (v - u)‖
          ≤ ‖u‖⁻¹ * ‖fderiv ℝ g (v - u)‖ := by
            gcongr
            rw [Real.norm_eq_abs]
            exact coulomb_landauMatrix_entry_le_pi u i j hu
        _ ≤ ‖u‖⁻¹ * (D / (1 + ‖v₀ - u‖) ^ 4) := by
            gcongr
            exact hD_bound u v hv
  · -- Dominator integrable: ‖u‖⁻¹ * (D / (1+‖v₀-u‖)^4) is integrable
    -- Change variables w = v₀ - u: integrand becomes ‖v₀-w‖⁻¹ * D/(1+‖w‖)^4.
    have h_bound_fun : ∀ w : Fin 3 → ℝ, |D / (1 + ‖w‖) ^ 4| ≤ D := fun w => by
      rw [abs_of_nonneg (by positivity)]
      exact div_le_self hD_pos.le (one_le_pow₀ (by linarith [norm_nonneg w]))
    have h_bound_int : Integrable (fun w : Fin 3 → ℝ => D / (1 + ‖w‖) ^ 4) :=
      inverse_poly_integrable D
    have h_w_int := inv_norm_bounded_integrable h_bound_fun h_bound_int
      h_bound_int.aestronglyMeasurable v₀
    exact (h_w_int.comp_sub_left v₀).congr (ae_of_all _ fun u => by
      change ‖v₀ - (v₀ - u)‖⁻¹ * (D / (1 + ‖v₀ - u‖) ^ 4) =
        ‖u‖⁻¹ * (D / (1 + ‖v₀ - u‖) ^ 4)
      congr 1; congr 1; abel_nf)
  · -- HasFDerivAt pointwise
    apply ae_of_all
    intro u v _
    have h1 := (hg_diff (v - u)).comp v (hasFDerivAt_sub_const u)
    simp only [ContinuousLinearMap.comp_id] at h1
    exact h1.const_mul (landauMatrix coulombKernel u i j)

lemma coulomb_entry_conv_differentiable
    (g : (Fin 3 → ℝ) → ℝ) (hg_smooth : ContDiff ℝ 2 g)
    (hg_schwartz : ∀ (N : ℕ) {k : ℕ}, k ≤ 1 → ∃ C > 0, ∀ v,
      ‖iteratedFDeriv ℝ k g v‖ * (1 + ‖v‖) ^ N ≤ C)
    (i j : Fin 3) :
    Differentiable ℝ (fun v => ∫ w, landauMatrix coulombKernel (v - w) i j * g w) := by
  -- Rewrite in u-coordinates and use HasFDerivAt
  suffices h : Differentiable ℝ (fun v => ∫ u, landauMatrix coulombKernel u i j * g (v - u)) by
    rwa [show (fun v => ∫ u, landauMatrix coulombKernel u i j * g (v - u)) =
        (fun v => ∫ w, landauMatrix coulombKernel (v - w) i j * g w) from
      funext fun v => by
        rw [← integral_sub_left_eq_self (fun w => landauMatrix coulombKernel w i j * g (v - w))
          volume v]; simp [sub_sub_cancel]] at h
  exact fun v₀ =>
    (coulomb_entry_conv_hasFDerivAt_aux g hg_smooth hg_schwartz i j v₀).differentiableAt

/-- The derivative of a Coulomb entry convolution with a Schwartz function is uniformly bounded.
    After substituting u = v - w, the fderiv acts only on g(v-u), giving
    fderiv(conv)(v) = ∫ A(u) • fderiv(g)(v-u) du. The bound follows from
    |A(u)| ≤ ‖u‖⁻¹ and integrability of ‖u‖⁻¹ * ‖fderiv g(·)‖ via
    newtonian_schwartz_uniform_bound.

    NOTE: The convolution does NOT have Schwartz decay (only O(‖v‖⁻²) since the
    Coulomb kernel is degree -1 homogeneous). But the uniform bound suffices because
    in `coulomb_flux_deriv_schwartz_decay`, convolution derivatives are multiplied by
    Schwartz-decaying factors (f, ∂_j f). -/
lemma coulomb_entry_conv_deriv_bounded
    (g : (Fin 3 → ℝ) → ℝ) (hg_smooth : ContDiff ℝ 2 g)
    (hg_schwartz : ∀ (N : ℕ) {k : ℕ}, k ≤ 1 → ∃ C > 0, ∀ v,
      ‖iteratedFDeriv ℝ k g v‖ * (1 + ‖v‖) ^ N ≤ C)
    (i j : Fin 3) :
    ∃ C > 0, ∀ v,
        ‖fderiv ℝ (fun v => ∫ w, landauMatrix coulombKernel (v - w) i j * g w) v‖ ≤ C := by
  -- Schwartz decay of fderiv g (absolute value form)
  have hfderiv_abs_decay : ∀ N : ℕ, ∃ C > 0, ∀ w,
      |‖fderiv ℝ g w‖| * (1 + ‖w‖) ^ N ≤ C := by
    intro N; obtain ⟨C, hC, hb⟩ := hg_schwartz N (k := 1) le_rfl
    exact ⟨C, hC, fun w => by
      rw [abs_of_nonneg (norm_nonneg _), norm_fderiv_eq_iteratedFDeriv_one]
      exact hb w⟩
  -- Uniform bound on convolution via newtonian_schwartz_uniform_bound
  have h_g_fderiv_cont : Continuous (fderiv ℝ g) := by
    have : ContDiff ℝ 1 (fderiv ℝ g) := hg_smooth.fderiv_right (by decide)
    exact this.continuous
  have h_meas : AEStronglyMeasurable (fun w => ‖fderiv ℝ g w‖) volume :=
    h_g_fderiv_cont.norm.aestronglyMeasurable
  obtain ⟨M, hM_pos, hM⟩ := newtonian_schwartz_uniform_bound
    (fun w => ‖fderiv ℝ g w‖) hfderiv_abs_decay h_meas
  refine ⟨M + 1, by linarith, fun v => ?_⟩
  -- The fderiv in u-coordinates equals ∫ A(u) • fderiv(g)(v-u)
  -- We use HasFDerivAt.fderiv to get the concrete representation
  have h_conv_eq : (fun v => ∫ w, landauMatrix coulombKernel (v - w) i j * g w) =
      (fun v => ∫ u, landauMatrix coulombKernel u i j * g (v - u)) :=
    funext fun v => by
      rw [← integral_sub_left_eq_self (fun w => landauMatrix coulombKernel w i j * g (v - w))
        volume v]; simp [sub_sub_cancel]
  rw [h_conv_eq]
  have h_hfd := coulomb_entry_conv_hasFDerivAt_aux g hg_smooth hg_schwartz i j v
  rw [h_hfd.fderiv]
  -- Bound ‖∫ A(u) • fderiv(g)(v-u) du‖ ≤ ∫ ‖u‖⁻¹ * ‖fderiv(g)(v-u)‖ du ≤ M
  have h_dom : Integrable (fun u => ‖u‖⁻¹ * ‖fderiv ℝ g (v - u)‖) :=
    (inv_norm_schwartz_integrable (fun w => ‖fderiv ℝ g w‖) hfderiv_abs_decay
      h_g_fderiv_cont.norm.aestronglyMeasurable v).comp_sub_left v
      |>.congr (ae_of_all _ fun u => by
        change ‖v - (v - u)‖⁻¹ * ‖fderiv ℝ g (v - u)‖ = ‖u‖⁻¹ * ‖fderiv ℝ g (v - u)‖
        congr 2; congr 1; abel)
  calc ‖∫ u, landauMatrix coulombKernel u i j • fderiv ℝ g (v - u)‖
      ≤ ∫ u, ‖landauMatrix coulombKernel u i j • fderiv ℝ g (v - u)‖ :=
          norm_integral_le_integral_norm _
    _ = ∫ u, ‖landauMatrix coulombKernel u i j‖ * ‖fderiv ℝ g (v - u)‖ := by
        congr 1
        ext u
        exact norm_smul _ _
    _ ≤ ∫ u, ‖u‖⁻¹ * ‖fderiv ℝ g (v - u)‖ :=
        integral_mono_of_nonneg (ae_of_all _ fun u => by positivity) h_dom
          (ae_of_all _ fun u => by
            by_cases hu : u = 0
            · simp [hu, landauMatrix_coulombKernel_zero]
            · exact mul_le_mul_of_nonneg_right
                (by rw [Real.norm_eq_abs]; exact coulomb_landauMatrix_entry_le_pi u i j hu)
                (norm_nonneg _))
    _ = ∫ w, ‖v - w‖⁻¹ * ‖fderiv ℝ g w‖ := by
        rw [← integral_sub_left_eq_self (fun u => ‖u‖⁻¹ * ‖fderiv ℝ g (v - u)‖) volume v]
        congr 1; ext u; congr 2; congr 1; abel
    _ ≤ M := by simp only [abs_norm] at hM; exact hM v
    _ ≤ M + 1 := le_add_of_nonneg_right one_pos.le

/-- The Coulomb flux component equals the K/L decomposition pointwise:
    (∫ w, mulVec A(v-w) (f(w)•∇f(v) - f(v)•∇f(w)))_i = Σ_j [∂_j f(v) * K_j(v) - f(v) * L_j(v)]
    where K_j(v) = ∫ A_{ij}(v-w) f(w) dw and L_j(v) = ∫ A_{ij}(v-w) ∂_j f(w) dw. -/
lemma coulomb_flux_eq_decomposed
    (f : (Fin 3 → ℝ) → ℝ) (hf_pos : ∀ v, 0 < f v) (hf_smooth : ContDiff ℝ 3 f)
    (hf_schwartz : ∀ (N : ℕ) {k : ℕ}, k ≤ 2 →
      ∃ C > 0, ∀ v, ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
    (i : Fin 3) (v : Fin 3 → ℝ) :
    (∫ w, mulVec (landauMatrix coulombKernel (v - w))
      (f w • vGrad f v - f v • vGrad f w)) i =
    ∑ j : Fin 3,
      (fderiv ℝ f v (Pi.single j 1) *
        (∫ w, landauMatrix coulombKernel (v - w) i j * f w) -
       f v * (∫ w, landauMatrix coulombKernel (v - w) i j *
        fderiv ℝ f w (Pi.single j 1))) := by
  have hf_decay : ∀ N : ℕ, ∃ C > 0, ∀ v, |f v| * (1 + ‖v‖) ^ N ≤ C :=
    schwartz_pointwise_decay hf_schwartz
  have hdf_decay : ∀ j, ∀ N : ℕ, ∃ C > 0, ∀ v,
      |fderiv ℝ f v (Pi.single j 1)| * (1 + ‖v‖) ^ N ≤ C :=
    fun jj N => schwartz_fderiv_component_decay hf_schwartz jj N
  have h_Af : ∀ j, Integrable (fun w => landauMatrix coulombKernel (v - w) i j * f w) :=
    fun j => coulomb_entry_schwartz_integrable f (hf_smooth.of_le (by decide)) hf_decay v i j
  have h_Adf : ∀ j, Integrable (fun w => landauMatrix coulombKernel (v - w) i j *
      fderiv ℝ f w (Pi.single j 1)) := fun j =>
    coulomb_entry_schwartz_integrable _ ((hf_smooth.fderiv_right (by decide)).clm_apply
      contDiff_const) (hdf_decay j) v i j
  have h_eq : ∀ j w, landauMatrix coulombKernel (v - w) i j *
      (f w • vGrad f v - f v • vGrad f w) j =
      fderiv ℝ f v (Pi.single j 1) * (landauMatrix coulombKernel (v - w) i j * f w) -
      f v * (landauMatrix coulombKernel (v - w) i j * fderiv ℝ f w (Pi.single j 1)) := by
    intro j w
    simp [vGrad, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [eval_integral (fun k =>
    (landau_flux_integrable_coulomb f hf_pos hf_smooth hf_schwartz v).eval k) i]
  simp only [mulVec, dotProduct]
  rw [integral_finset_sum _ (fun j _ => by
    simp_rw [h_eq j]; exact ((h_Af j).const_mul _).sub ((h_Adf j).const_mul _))]
  congr 1
  ext j
  simp_rw [h_eq j]
  rw [integral_sub ((h_Af j).const_mul _) ((h_Adf j).const_mul _),
      integral_const_mul_of_integrable (h_Af j),
      integral_const_mul_of_integrable (h_Adf j)]

/-- The Coulomb flux component v ↦ (∫_w A(v-w)·[f(w)∇f(v)-f(v)∇f(w)])_i is differentiable.

    Proof strategy: Decompose the flux as
      flux_i(v) = Σ_j (∂_j f)(v) * K_{ij}(v) - f(v) * Σ_j L_{ij}(v)
    where K_{ij}(v) = ∫ A_{ij}(v-w) f(w) dw and L_{ij}(v) = ∫ A_{ij}(v-w) (∂_j f)(w) dw.
    Each K_{ij} and L_{ij} is differentiable by coulomb_entry_conv_differentiable.
    Then flux_i is differentiable by product/sum rules. -/
lemma coulomb_flux_differentiable
    (f : (Fin 3 → ℝ) → ℝ) (hf_pos : ∀ v, 0 < f v) (hf_smooth : ContDiff ℝ 3 f)
    (hf_schwartz : ∀ (N : ℕ) {k : ℕ}, k ≤ 2 →
      ∃ C > 0, ∀ v, ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
    (i : Fin 3) :
    Differentiable ℝ (fun v =>
      (∫ w, mulVec (landauMatrix coulombKernel (v - w))
        (f w • vGrad f v - f v • vGrad f w)) i) := by
  have hf_schwartz_le1 : ∀ (N : ℕ) {k : ℕ}, k ≤ 1 → ∃ C > 0, ∀ v,
      ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C :=
    fun N k hk => hf_schwartz N (le_trans hk (by linarith))
  have hK_diff : ∀ j, Differentiable ℝ
      (fun v => ∫ w, landauMatrix coulombKernel (v - w) i j * f w) :=
    fun j => coulomb_entry_conv_differentiable f (hf_smooth.of_le (by decide)) hf_schwartz_le1 i j
  have hdf_schwartz := fun j => schwartz_fderiv_component_schwartz f hf_smooth hf_schwartz j
  have hL_diff : ∀ j, Differentiable ℝ
      (fun v => ∫ w, landauMatrix coulombKernel (v - w) i j *
        fderiv ℝ f w (Pi.single j 1)) := fun j =>
    coulomb_entry_conv_differentiable _
      ((hf_smooth.fderiv_right (by decide)).clm_apply contDiff_const)
      (fun N k hk => hdf_schwartz j N (by exact_mod_cast (by omega : k + 1 ≤ 2))) i j
  have h_df_diff : ∀ j, Differentiable ℝ (fun v => fderiv ℝ f v (Pi.single j 1)) :=
    fun j => (show ContDiff ℝ 1 (fun v => fderiv ℝ f v (Pi.single j 1)) from
      (hf_smooth.fderiv_right (by exact_mod_cast (by omega : 1 + 1 ≤ 3))).clm_apply
        contDiff_const).differentiable (by decide)
  have h_fn_eq : ∀ v, (∫ w, mulVec (landauMatrix coulombKernel (v - w))
        (f w • vGrad f v - f v • vGrad f w)) i =
      ∑ j : Fin 3,
        (fderiv ℝ f v (Pi.single j 1) *
          (∫ w, landauMatrix coulombKernel (v - w) i j * f w) -
         f v * (∫ w, landauMatrix coulombKernel (v - w) i j *
          fderiv ℝ f w (Pi.single j 1))) :=
    fun v => coulomb_flux_eq_decomposed f hf_pos hf_smooth hf_schwartz i v
  simp_rw [h_fn_eq]
  change Differentiable ℝ (Finset.univ.sum fun j => fun v =>
    fderiv ℝ f v (Pi.single j 1) *
      (∫ w, landauMatrix coulombKernel (v - w) i j * f w) -
     f v * (∫ w, landauMatrix coulombKernel (v - w) i j *
      fderiv ℝ f w (Pi.single j 1)))
  apply Differentiable.sum
  intro j _
  exact (h_df_diff j |>.mul (hK_diff j)).sub
    (hf_smooth.differentiable (by decide) |>.mul (hL_diff j))


/-- Coulomb convolution of a Schwartz-decaying function is uniformly bounded:
    |∫ A_{ij}(v-w) * g(w) dw| ≤ M for all v. Uses |A_{ij}(z)| ≤ ‖z‖⁻¹ and the
    Newtonian potential uniform bound. -/
lemma coulomb_entry_conv_uniform_bound
    {g : (Fin 3 → ℝ) → ℝ}
    (hg_decay : ∀ M : ℕ, ∃ C > 0, ∀ w, |g w| * (1 + ‖w‖) ^ M ≤ C)
    (hg_meas : AEStronglyMeasurable g)
    (i j : Fin 3) :
    ∃ M > 0, ∀ v, |∫ w, landauMatrix coulombKernel (v - w) i j * g w| ≤ M := by
  obtain ⟨M, hM, hMb⟩ := newtonian_schwartz_uniform_bound g hg_decay hg_meas
  exact ⟨M, hM, fun v => by
    calc |∫ w, landauMatrix coulombKernel (v - w) i j * g w|
        = ‖∫ w, landauMatrix coulombKernel (v - w) i j * g w‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ∫ w, ‖landauMatrix coulombKernel (v - w) i j * g w‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ w, ‖v - w‖⁻¹ * |g w| := by
          apply integral_mono_of_nonneg
            (ae_of_all _ fun w => norm_nonneg _)
            ((inv_norm_schwartz_integrable g hg_decay hg_meas v).norm.congr
              (ae_of_all _ fun w => by
                change ‖‖v - w‖⁻¹ * g w‖ = ‖v - w‖⁻¹ * |g w|
                rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
                    Real.norm_eq_abs]))
            (ae_of_all _ fun w => by
              change ‖landauMatrix coulombKernel (v - w) i j * g w‖ ≤ ‖v - w‖⁻¹ * |g w|
              rw [norm_mul, Real.norm_eq_abs (g w)]
              by_cases hvw : v - w = 0
              · simp [hvw, landauMatrix_coulombKernel_zero]
              · exact mul_le_mul_of_nonneg_right
                  (by rw [Real.norm_eq_abs]
                      exact coulomb_landauMatrix_entry_le_pi _ i j hvw)
                  (abs_nonneg _))
      _ ≤ M := hMb v⟩

end VML
