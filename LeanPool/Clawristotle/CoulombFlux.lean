/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import LeanPool.Clawristotle.NewtonianPotential
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Flux Integrability and Measurability Helpers for Coulomb

Proves integrability of the Landau collision flux, Schwartz partial decay,
and AEStronglyMeasurability of flux components for the Coulomb kernel.
-/

open MeasureTheory Matrix Finset BigOperators Real

noncomputable section
namespace VML

-- ============================================================================
-- Landau flux integrability for Coulomb kernel (proved by Aristotle, job aabe3f3d)
-- Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-- ============================================================================

/-- The Landau collision flux is integrable for the Coulomb kernel. -/
lemma landau_flux_integrable_coulomb
    (f : (Fin 3 → ℝ) → ℝ)
    (_hf_pos : ∀ v, 0 < f v)
    (hf_smooth : ContDiff ℝ 3 f)
    (hf_schwartz : ∀ (N : ℕ) {k : ℕ}, k ≤ 2 → ∃ C > 0, ∀ (v : Fin 3 → ℝ),
      ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
    (v : Fin 3 → ℝ) :
    Integrable (fun w =>
      mulVec (landauMatrix coulombKernel (v - w))
        (f w • vGrad f v - f v • vGrad f w)) := by
  -- Each component (i,j) is integrable via ‖v-w‖⁻¹ × Schwartz bound
  have h_comp : ∀ i j : Fin 3, Integrable (fun w =>
      (landauMatrix coulombKernel (v - w)) i j *
      (f w • vGrad f v - f v • vGrad f w) j) := by
    have h_inv : ∀ i j : Fin 3, Integrable (fun w =>
        ‖v - w‖⁻¹ * (f w • vGrad f v - f v • vGrad f w) j) := by
      intro i j
      have h_int : Integrable (fun w => ‖v - w‖⁻¹ * f w) ∧
          Integrable (fun w => ‖v - w‖⁻¹ * (vGrad f w) j) := by
        constructor
        · apply inv_norm_schwartz_integrable
          · intro N
            obtain ⟨C, hC, hb⟩ := hf_schwartz (k := 0) N (by omega)
            exact ⟨C, hC, fun w => by simpa [iteratedFDeriv_zero_eq_comp] using hb w⟩
          · exact hf_smooth.continuous.aestronglyMeasurable
        · apply inv_norm_schwartz_integrable
          · intro N
            obtain ⟨C, hC_pos, hC⟩ := hf_schwartz (k := 1) N (by omega)
            use C, hC_pos; intro w
            have h_deriv_bound : |vGrad f w j| ≤ ‖iteratedFDeriv ℝ 1 f w‖ := by
              have : |fderiv ℝ f w (Pi.single j 1)| ≤ ‖fderiv ℝ f w‖ := by
                simpa using (ContinuousLinearMap.le_opNorm (fderiv ℝ f w) (Pi.single j 1))
                  |> le_trans <| mul_le_of_le_one_right (norm_nonneg _) <|
                  by simp [Pi.norm_single]
              rw [norm_iteratedFDeriv_one]
              simpa [VML.vGrad] using this
            exact le_trans (mul_le_mul_of_nonneg_right h_deriv_bound (by positivity)) (hC w)
          · exact ((hf_smooth.continuous_fderiv (by norm_num)).eval_const
              (Pi.single j 1)).aestronglyMeasurable
      convert h_int.1.mul_const ((vGrad f v) j) |>.sub (h_int.2.const_mul (f v)) using 2
      · rfl
      · simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
    intro i j
    refine (h_inv i j).norm.mono' ?_ ?_
    · refine AEStronglyMeasurable.mul ?_ ?_
      · refine Measurable.aestronglyMeasurable ?_
        refine Measurable.mul ?_ ?_
        · refine Measurable.ite ?_ ?_ ?_ <;> norm_num [eucNorm, coulombKernel]
          · exact measurableSet_Iic.mem.comp (Real.continuous_sqrt.measurable.comp
              (show Measurable fun a : Fin 3 → ℝ => normSq (v - a) from
                Continuous.measurable (Continuous.dotProduct
                  (continuous_const.sub continuous_id') (continuous_const.sub continuous_id'))))
          · exact Measurable.pow_const (Measurable.sqrt <| Continuous.measurable <|
              Continuous.dotProduct (continuous_const.sub continuous_id')
                (continuous_const.sub continuous_id')) _
        · unfold innerLandauMatrix
          simp only [normSq, dotProduct_sub, sub_dotProduct, vecMulVec, Pi.sub_apply,
            Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, of_apply]
          fun_prop (disch := norm_num)
      · exact AEStronglyMeasurable.sub
          (Continuous.aestronglyMeasurable (hf_smooth.continuous.mul continuous_const))
          (AEStronglyMeasurable.mul aestronglyMeasurable_const
            ((hf_smooth.continuous_fderiv (by norm_num)).eval_const
              (Pi.single j 1)).aestronglyMeasurable)
    · filter_upwards [] with w
      by_cases hw : v - w = 0
      · simp_all [sub_eq_zero, landauMatrix, innerLandauMatrix, normSq, vecMulVec,
          eucNorm, coulombKernel]
      · simp only [norm_mul, Real.norm_eq_abs, abs_inv, abs_norm]
        exact mul_le_mul_of_nonneg_right
          (coulomb_landauMatrix_entry_le_pi _ _ _ hw) (abs_nonneg _)
  exact integrable_pi_iff.mpr fun i => by
    simp only [mulVec, dotProduct]
    exact integrable_finsetSum Finset.univ fun j _ => by
      convert h_comp i j using 2 with w

-- ============================================================================
-- Schwartz partial decay helper
-- ============================================================================

/-- Schwartz decay of partial derivatives: |∂_j f(x,w)| * (1+‖w‖)^N ≤ C.
    Follows from ‖iteratedFDeriv 1 f w‖ bounds and
    |∂_jf| ≤ ‖fderiv f w‖ ≤ ‖iteratedFDeriv 1 f w‖. -/
lemma schwartz_partial_decay
    {f : Torus3 → (Fin 3 → ℝ) → ℝ}
    (hSchwartz : UniformSchwartzDecay f) (x : Torus3) (j : Fin 3) :
    ∀ N : ℕ, ∃ C > 0, ∀ w : Fin 3 → ℝ,
      |fderiv ℝ (f x) w (Pi.single j 1)| * (1 + ‖w‖) ^ N ≤ C := by
  intro N
  obtain ⟨C, hC_pos, hC⟩ := hSchwartz.hDecay (k := 1) N (by omega)
  refine ⟨C, hC_pos, fun w => ?_⟩
  have h1 : |fderiv ℝ (f x) w (Pi.single j 1)| ≤ ‖fderiv ℝ (f x) w‖ := by
    rw [← Real.norm_eq_abs]
    exact le_trans (ContinuousLinearMap.le_opNorm _ _)
      (mul_le_of_le_one_right (norm_nonneg _) (by simp [Pi.norm_single]))
  rw [norm_fderiv_eq_iteratedFDeriv_one] at h1
  exact le_trans (mul_le_mul_of_nonneg_right h1 (by positivity)) (hC x w)


/-- The Landau flux component is AEStronglyMeasurable as a parametric integral.
    Uses joint measurability on the product space + integral_prod_right'. -/
lemma flux_component_aestronglyMeasurable
    (φ : (Fin 3 → ℝ) → ℝ)
    (hφ_smooth : ContDiff ℝ 3 φ)
    (hFlux : ∀ v, Integrable (fun w => mulVec (landauMatrix coulombKernel (v - w))
      (φ w • vGrad φ v - φ v • vGrad φ w)))
    (i : Fin 3) :
    AEStronglyMeasurable (fun v =>
      (∫ w, mulVec (landauMatrix coulombKernel (v - w))
        (φ w • vGrad φ v - φ v • vGrad φ w)) i) volume := by
  have heval2 : (fun v => (∫ w, mulVec (landauMatrix coulombKernel (v - w))
      (φ w • vGrad φ v - φ v • vGrad φ w)) i) =
    (fun v => ∫ w, (mulVec (landauMatrix coulombKernel (v - w))
      (φ w • vGrad φ v - φ v • vGrad φ w)) i) :=
    funext fun v => eval_integral (hFlux v).eval i
  rw [heval2]
  let g : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ :=
    fun p => (mulVec (landauMatrix coulombKernel (p.1 - p.2))
      (φ p.2 • vGrad φ p.1 - φ p.1 • vGrad φ p.2)) i
  change AEStronglyMeasurable (fun v => ∫ w, g (v, w)) volume
  apply AEStronglyMeasurable.integral_prod_right'
  apply Measurable.aestronglyMeasurable
  change Measurable g
  simp only [g, mulVec, dotProduct]
  apply Finset.measurable_sum
  intro j _
  apply Measurable.mul
  · -- landauMatrix coulombKernel (p.1-p.2) i j is measurable
    show Measurable (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      landauMatrix coulombKernel (p.1 - p.2) i j)
    simp only [landauMatrix, Matrix.smul_apply, smul_eq_mul]
    apply Measurable.mul
    · -- coulombKernel (eucNorm (p.1-p.2)) is measurable
      apply ((Measurable.ite measurableSet_Iic measurable_const
        (measurable_id.pow measurable_const)) : Measurable coulombKernel).comp
      simp only [eucNorm, normSq, dotProduct]
      exact (continuous_sqrt.comp (continuous_finsetSum _ fun k _ =>
        ((continuous_apply k).comp (continuous_fst.sub continuous_snd)).mul
        ((continuous_apply k).comp (continuous_fst.sub continuous_snd)))).measurable
    · -- innerLandauMatrix (p.1-p.2) i j is continuous
      simp only [innerLandauMatrix_apply]
      apply Continuous.measurable
      apply Continuous.sub
      · by_cases h : i = j
        · simp only [h, ↓reduceIte, normSq, dotProduct]
          exact continuous_finsetSum _ fun k _ =>
            ((continuous_apply k).comp (continuous_fst.sub continuous_snd)).mul
            ((continuous_apply k).comp (continuous_fst.sub continuous_snd))
        · simp only [h, ↓reduceIte]
          exact continuous_const
      · exact ((continuous_apply i).comp (continuous_fst.sub continuous_snd)).mul
              ((continuous_apply j).comp (continuous_fst.sub continuous_snd))
  · -- The vector part is continuous
    have hf_cont := hφ_smooth.continuous
    have hdf_cont := hφ_smooth.continuous_fderiv (by norm_num)
    apply Continuous.measurable
    apply Continuous.sub
    · exact (hf_cont.comp continuous_snd).mul
        ((hdf_cont.comp continuous_fst).clm_apply continuous_const)
    · exact (hf_cont.comp continuous_fst).mul
        ((hdf_cont.comp continuous_snd).clm_apply continuous_const)

end VML
