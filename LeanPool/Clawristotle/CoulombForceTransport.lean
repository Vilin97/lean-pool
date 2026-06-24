/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import LeanPool.Clawristotle.CoulombKernel
import LeanPool.Clawristotle.VelocityDecayInstance

/-!
# Force Transport and IBP Integrability for Coulomb

Proves integrability of the spatial transport term (v · ∇ₓf · log f), force transport
term ((E + v × B) · ∇ᵥf · log f), and force IBP terms for the Coulomb kernel.
Uses Schwartz decay, log growth bounds, and the Lorentz force component bound.
-/

open MeasureTheory Matrix Finset BigOperators Real

noncomputable section
namespace VML

/-- Spatial gradient of f w.r.t. x is AEStronglyMeasurable in v, via difference quotient limits. -/
lemma torusGradX_aestronglyMeasurable
    {f : Torus3 → (Fin 3 → ℝ) → ℝ}
    (hf_smooth_v : ∀ x, ContDiff ℝ 3 (f x))
    (hf_smooth_x : ∀ v, ContDiff ℝ 2 (periodicLift (fun x => f x v)))
    (x : Torus3) (i : Fin 3) :
    AEStronglyMeasurable
      (fun v => torusGradX (fun y => f y v) x i) volume := by
  set x₀ := (torusMk_surjective x).choose
  set ei := (Pi.single i (1 : ℝ) : Fin 3 → ℝ)
  set G : ℕ → (Fin 3 → ℝ) → ℝ := fun n v =>
    (↑n + 1 : ℝ) * (f (torusMk (x₀ + (↑n + 1 : ℝ)⁻¹ • ei)) v - f (torusMk x₀) v)
  have hG_meas : ∀ n, AEStronglyMeasurable (G n) volume := fun n =>
    ((hf_smooth_v (torusMk (x₀ + _))).continuous.sub
      (hf_smooth_v (torusMk x₀)).continuous).aestronglyMeasurable.const_mul _
  have hG_lim : ∀ v, Filter.Tendsto (fun n => G n v) Filter.atTop
      (nhds (torusGradX (fun y => f y v) x i)) := by
    intro v
    unfold torusGradX
    set F := periodicLift (fun y => f y v)
    have hF_diff : DifferentiableAt ℝ F x₀ :=
      (hf_smooth_x v).differentiable (by decide) |>.differentiableAt
    have hg : HasDerivAt (fun t : ℝ => x₀ + t • (Pi.single i (1 : ℝ) : Fin 3 → ℝ))
        (Pi.single i (1 : ℝ) : Fin 3 → ℝ) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
        (Pi.single i (1 : ℝ) : Fin 3 → ℝ)).const_add x₀
    have h_eq : x₀ + (0 : ℝ) • (Pi.single i (1 : ℝ) : Fin 3 → ℝ) = x₀ := by simp
    have hF_at : HasFDerivAt F (fderiv ℝ F x₀)
        (x₀ + (0 : ℝ) • (Pi.single i (1 : ℝ) : Fin 3 → ℝ)) := by
      rw [h_eq]; exact hF_diff.hasFDerivAt
    have hline : HasDerivAt (fun t : ℝ => F (x₀ + t • ei)) (fderiv ℝ F x₀ ei) 0 := by
      convert hF_at.comp_hasDerivAt (x := (0 : ℝ)) hg using 1 <;> rfl
    have htendsto_inv : Filter.Tendsto (fun n : ℕ => ((↑n + 1 : ℝ))⁻¹) Filter.atTop
        (nhdsWithin 0 (Set.Ioi 0)) :=
      tendsto_nhdsWithin_iff.mpr ⟨
        Filter.Tendsto.comp tendsto_inv_atTop_zero
          (Filter.Tendsto.atTop_add (tendsto_natCast_atTop_atTop (R := ℝ)) tendsto_const_nhds),
        Filter.Eventually.of_forall fun n => Set.mem_Ioi.mpr (by positivity)⟩
    have h := Filter.Tendsto.comp hline.tendsto_slope_zero_right htendsto_inv
    simp only [smul_eq_mul, Function.comp_def, inv_inv, zero_smul, add_zero, zero_add] at h
    convert h using 1
    rfl
  exact aestronglyMeasurable_of_tendsto_ae Filter.atTop hG_meas
    (Filter.Eventually.of_forall hG_lim)


/-- Spatial transport integrand is dominated by inverse polynomial
    (from Schwartz grad decay + log bound). -/
lemma spatial_transport_integrable
    {f : Torus3 → (Fin 3 → ℝ) → ℝ}
    (hf_pos : ∀ x v, 0 < f x v)
    (hf_smooth_v : ∀ x, ContDiff ℝ 3 (f x))
    (hf_smooth_x : ∀ v, ContDiff ℝ 2 (periodicLift (fun x => f x v)))
    (hSchwartz : UniformSchwartzDecay f)
    (hLogBound : ∃ (C_log : ℝ) (K_log : ℕ), ∀ (x : Torus3) (v : Fin 3 → ℝ),
      |Real.log (f x v)| ≤ C_log * (1 + ‖v‖) ^ K_log)
    (x : Torus3) :
    Integrable (fun v =>
      v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x * Real.log (f x v)) := by
  obtain ⟨C_log, K_log, hLB⟩ := hLogBound
  -- Suffices to show each component v i * gradX(f)_i * log(f) is integrable
  suffices h : ∀ i : Fin 3,
      Integrable (fun v => v i * FlatTorus3.gradX (fun y => f y v) x i *
        Real.log (f x v)) by
    have heq : (fun v => v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x * Real.log (f x v)) =
        fun v => ∑ i : Fin 3, v i * FlatTorus3.gradX (fun y => f y v) x i *
          Real.log (f x v) := by
      ext v
      simp only [dotProduct, Fin.sum_univ_three]
      ring
    rw [heq]; exact integrable_finsetSum _ fun i _ => h i
  intro i
  obtain ⟨Ci, hCi, hGi⟩ := hSchwartz.hGradDecay (K_log + 6) i
  apply (inverse_poly_integrable (Ci * (|C_log| + 1))).mono'
  · -- AEStronglyMeasurable — product of measurable/continuous functions
    -- v ↦ v i is continuous, v ↦ log(f x v) is continuous, v ↦ gradX is AEStronglyMeasurable
    exact ((continuous_apply i).aestronglyMeasurable.mul
      (torusGradX_aestronglyMeasurable hf_smooth_v hf_smooth_x x i)).mul
      ((hf_smooth_v x).continuous.log (fun v => ne_of_gt (hf_pos x v))).aestronglyMeasurable
  · filter_upwards [] with v
    rw [Real.norm_eq_abs, le_div_iff₀ (pow_pos (by linarith [norm_nonneg v] : (0:ℝ) < 1 + ‖v‖) 4)]
    have h1v : (1 : ℝ) ≤ 1 + ‖v‖ := le_add_of_nonneg_right (norm_nonneg v)
    have hvi : |v i| ≤ 1 + ‖v‖ :=
      le_trans ((Real.norm_eq_abs _) ▸ norm_le_pi_norm v i) (le_add_of_nonneg_left zero_le_one)
    have hlog : |Real.log (f x v)| ≤ |C_log| * (1 + ‖v‖) ^ K_log :=
      le_trans (hLB x v) (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg (by linarith) _))
    have h1v_nn : (0 : ℝ) ≤ 1 + ‖v‖ := le_trans zero_le_one h1v
    have hpow_mono : (1 + ‖v‖) ^ (K_log + 5) ≤ (1 + ‖v‖) ^ (K_log + 6) :=
      pow_le_pow_right₀ h1v (by omega)
    have hgrad : |FlatTorus3.gradX (fun y => f y v) x i| * (1 + ‖v‖) ^ (K_log + 5) ≤ Ci :=
      le_trans (mul_le_mul_of_nonneg_left hpow_mono (abs_nonneg _)) (hGi x v)
    set g_i := |FlatTorus3.gradX (fun y => f y v) x i| with hg_i_def
    calc |v i * FlatTorus3.gradX (fun y => f y v) x i * Real.log (f x v)| * (1 + ‖v‖) ^ 4
        = |v i| * g_i * |Real.log (f x v)| *
            (1 + ‖v‖) ^ 4 := by rw [abs_mul, abs_mul]
      _ ≤ (1 + ‖v‖) * g_i *
            (|C_log| * (1 + ‖v‖) ^ K_log) * (1 + ‖v‖) ^ 4 := by gcongr
      _ = |C_log| * (g_i * ((1 + ‖v‖) * (1 + ‖v‖) ^ K_log * (1 + ‖v‖) ^ 4)) := by ring
      _ = |C_log| * (g_i * (1 + ‖v‖) ^ (K_log + 5)) := by
          congr 2; rw [← pow_succ', ← pow_add]
      _ ≤ |C_log| * Ci := by gcongr
      _ ≤ Ci * (|C_log| + 1) := by nlinarith [abs_nonneg C_log, hCi.le]


/-- Each force × fderiv × log component is integrable (shared helper for
    force_transport and force_ibp_f_dg). -/
lemma force_fderiv_log_component_integrable
    {f : Torus3 → (Fin 3 → ℝ) → ℝ}
    (E B : Torus3 → Fin 3 → ℝ)
    (hf_pos : ∀ x v, 0 < f x v)
    (hf_smooth : ∀ x, ContDiff ℝ 3 (f x))
    (hSchwartz : UniformSchwartzDecay f)
    (C_log : ℝ) (K_log : ℕ)
    (hLB : ∀ (x : Torus3) (v : Fin 3 → ℝ),
      |Real.log (f x v)| ≤ C_log * (1 + ‖v‖) ^ K_log)
    (x : Torus3) (i : Fin 3) :
    Integrable (fun v => (E x + cross v (B x)) i *
      fderiv ℝ (f x) v (Pi.single i 1) * Real.log (f x v)) := by
  obtain ⟨CL, hCL_nn, hCL⟩ := lorentz_component_bound (E x) (B x)
  obtain ⟨C_fder, hC_fder_pos, hbound_fder⟩ := hSchwartz.hDecay (k := 1) (K_log + 6) (by omega)
  apply (inverse_poly_integrable (CL * |C_log| * C_fder + 1)).mono'
  · -- AEStronglyMeasurable: each factor is continuous in v
    refine Continuous.aestronglyMeasurable ?_
    have h1 : Continuous (fun v => (E x + cross v (B x)) i) := by
      change Continuous (fun v => E x i + (cross v (B x)) i)
      apply Continuous.add continuous_const
      unfold cross
      fin_cases i <;>
        simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val,
          cons_val_zero, cons_val_one] <;>
        exact (continuous_apply _ |>.mul continuous_const).sub
          (continuous_apply _ |>.mul continuous_const)
    have h2 : Continuous (fun v => fderiv ℝ (f x) v (Pi.single i 1)) :=
      ((hf_smooth x).continuous_fderiv (by norm_num)).clm_apply continuous_const
    have h3 : Continuous (fun v => Real.log (f x v)) :=
      (hf_smooth x).continuous.log (fun v => ne_of_gt (hf_pos x v))
    exact (h1.mul h2).mul h3
  · filter_upwards [] with v
    rw [Real.norm_eq_abs, le_div_iff₀ (pow_pos (by linarith [norm_nonneg v] : (0:ℝ) < 1 + ‖v‖) 4)]
    have h1v : (1 : ℝ) ≤ 1 + ‖v‖ := le_add_of_nonneg_right (norm_nonneg v)
    have h1v_nn : (0 : ℝ) ≤ 1 + ‖v‖ := le_trans zero_le_one h1v
    have hfder_le : |fderiv ℝ (f x) v (Pi.single i 1)| ≤ ‖iteratedFDeriv ℝ 1 (f x) v‖ := by
      rw [← Real.norm_eq_abs, ← norm_fderiv_eq_iteratedFDeriv_one]
      exact (ContinuousLinearMap.le_opNorm _ _).trans (by simp [Pi.norm_single])
    have hfder := hbound_fder x v
    have hlog : |Real.log (f x v)| ≤ |C_log| * (1 + ‖v‖) ^ K_log :=
      le_trans (hLB x v) (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg h1v_nn _))
    have hpow_mono : (1 + ‖v‖) ^ (K_log + 5) ≤ (1 + ‖v‖) ^ (K_log + 6) :=
      pow_le_pow_right₀ h1v (by omega)
    set D := ‖iteratedFDeriv ℝ 1 (f x) v‖ with hD_def
    calc |(E x + cross v (B x)) i * fderiv ℝ (f x) v (Pi.single i 1) *
              Real.log (f x v)| * (1 + ‖v‖) ^ 4
        = |(E x + cross v (B x)) i| * |fderiv ℝ (f x) v (Pi.single i 1)| *
            |Real.log (f x v)| * (1 + ‖v‖) ^ 4 := by rw [abs_mul, abs_mul]
      _ ≤ (CL * (1 + ‖v‖)) * D * (|C_log| * (1 + ‖v‖) ^ K_log) *
            (1 + ‖v‖) ^ 4 := by gcongr; exact hCL v i
      _ = CL * |C_log| * (D * ((1 + ‖v‖) * (1 + ‖v‖) ^ K_log *
            (1 + ‖v‖) ^ 4)) := by ring
      _ = CL * |C_log| * (D * (1 + ‖v‖) ^ (K_log + 5)) := by
          congr 2; rw [← pow_succ', ← pow_add]
      _ ≤ CL * |C_log| * (D * (1 + ‖v‖) ^ (K_log + 6)) := by gcongr
      _ ≤ CL * |C_log| * C_fder := by gcongr
      _ ≤ CL * |C_log| * C_fder + 1 := le_add_of_nonneg_right zero_le_one

/-- Force transport integrand is integrable
    (from Schwartz derivative decay + log bound + Lorentz bound). -/
lemma force_transport_integrable_coulomb
    {f : Torus3 → (Fin 3 → ℝ) → ℝ}
    (E B : Torus3 → Fin 3 → ℝ)
    (hf_pos : ∀ x v, 0 < f x v)
    (hf_smooth : ∀ x, ContDiff ℝ 3 (f x))
    (hSchwartz : UniformSchwartzDecay f)
    (hLogBound : ∃ (C_log : ℝ) (K_log : ℕ), ∀ (x : Torus3) (v : Fin 3 → ℝ),
      |Real.log (f x v)| ≤ C_log * (1 + ‖v‖) ^ K_log)
    (x : Torus3) :
    Integrable (fun v =>
      (E x + cross v (B x)) ⬝ᵥ vGrad (f x) v * Real.log (f x v)) := by
  obtain ⟨C_log, K_log, hLB⟩ := hLogBound
  have heq : (fun v => (E x + cross v (B x)) ⬝ᵥ vGrad (f x) v * Real.log (f x v)) =
      fun v => ∑ i : Fin 3, (E x + cross v (B x)) i *
        fderiv ℝ (f x) v (Pi.single i 1) * Real.log (f x v) := by
    ext v
    simp only [dotProduct, vGrad, Fin.sum_univ_three]
    ring
  rw [heq]; exact integrable_finsetSum _ fun i _ =>
    force_fderiv_log_component_integrable E B hf_pos hf_smooth hSchwartz C_log K_log hLB x i


/-- Force IBP (f·dg form) integrand is integrable.
    Uses chain rule: d/dv(f·log f - f) = f'·log f. -/
lemma force_ibp_f_dg_integrable_coulomb
    {f : Torus3 → (Fin 3 → ℝ) → ℝ}
    (E B : Torus3 → Fin 3 → ℝ)
    (hf_pos : ∀ x v, 0 < f x v)
    (hf_smooth : ∀ x, ContDiff ℝ 3 (f x))
    (hSchwartz : UniformSchwartzDecay f)
    (hLogBound : ∃ (C_log : ℝ) (K_log : ℕ), ∀ (x : Torus3) (v : Fin 3 → ℝ),
      |Real.log (f x v)| ≤ C_log * (1 + ‖v‖) ^ K_log)
    (x : Torus3) (i : Fin 3) :
    Integrable (fun v =>
      (E x + cross v (B x)) i *
        fderiv ℝ (fun w => f x w * Real.log (f x w) - f x w) v (Pi.single i 1)) := by
  obtain ⟨C_log, K_log, hLB⟩ := hLogBound
  -- Chain rule: fderiv(f·log f - f) = log(f) • fderiv(f)
  have hfder_eq : ∀ v,
      fderiv ℝ (fun w => f x w * Real.log (f x w) - f x w) v (Pi.single i 1) =
      Real.log (f x v) * fderiv ℝ (f x) v (Pi.single i 1) := by
    intro v
    have hfx_hfd : HasFDerivAt (f x) (fderiv ℝ (f x) v) v :=
      ((hf_smooth x).differentiable (by norm_num)).differentiableAt.hasFDerivAt
    have hlog_hfd : HasFDerivAt (fun w => Real.log (f x w))
        ((f x v)⁻¹ • fderiv ℝ (f x) v) v :=
      hfx_hfd.log (ne_of_gt (hf_pos x v))
    have h_mul_hfd : HasFDerivAt (fun w => f x w * Real.log (f x w))
        (f x v • ((f x v)⁻¹ • fderiv ℝ (f x) v) +
         Real.log (f x v) • fderiv ℝ (f x) v) v :=
      hfx_hfd.fun_mul hlog_hfd
    have h_sub_hfd := h_mul_hfd.fun_sub hfx_hfd
    rw [h_sub_hfd.fderiv]
    simp only [_root_.sub_apply, _root_.add_apply,
      _root_.smul_apply, smul_eq_mul]
    have hfv_ne : f x v ≠ 0 := ne_of_gt (hf_pos x v)
    rw [← mul_assoc, mul_inv_cancel₀ hfv_ne, one_mul]
    ring
  -- Rewrite integrand using the chain rule
  have heq : (fun v => (E x + cross v (B x)) i *
      fderiv ℝ (fun w => f x w * Real.log (f x w) - f x w) v (Pi.single i 1)) =
      fun v => (E x + cross v (B x)) i *
        fderiv ℝ (f x) v (Pi.single i 1) * Real.log (f x v) := by
    ext v
    rw [hfder_eq]
    ring
  rw [heq]
  exact force_fderiv_log_component_integrable E B hf_pos hf_smooth hSchwartz
    C_log K_log hLB x i

/-- Force IBP (f·g form) integrand is integrable. -/
lemma force_ibp_fg_integrable_coulomb
    {f : Torus3 → (Fin 3 → ℝ) → ℝ}
    (E B : Torus3 → Fin 3 → ℝ)
    (hf_pos : ∀ x v, 0 < f x v)
    (hf_smooth : ∀ x, ContDiff ℝ 3 (f x))
    (hSchwartz : UniformSchwartzDecay f)
    (hLogBound : ∃ (C_log : ℝ) (K_log : ℕ), ∀ (x : Torus3) (v : Fin 3 → ℝ),
      |Real.log (f x v)| ≤ C_log * (1 + ‖v‖) ^ K_log)
    (x : Torus3) (i : Fin 3) :
    Integrable (fun v =>
      (E x + cross v (B x)) i * (f x v * Real.log (f x v) - f x v)) := by
  obtain ⟨C_log, K_log, hLB⟩ := hLogBound
  obtain ⟨CL, hCL_nn, hCL⟩ := lorentz_component_bound (E x) (B x)
  apply integrable_of_schwartz_bound
    (fun k => schwartz_norm_pow_integrable hf_pos hf_smooth hSchwartz x k)
  · -- AEStronglyMeasurable: force term * entropy density is continuous in v
    refine Continuous.aestronglyMeasurable ?_
    have h1 : Continuous (fun v => (E x + cross v (B x)) i) := by
      change Continuous (fun v => E x i + (cross v (B x)) i)
      apply Continuous.add continuous_const
      unfold cross
      fin_cases i <;>
        simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val,
          cons_val_zero, cons_val_one] <;>
        exact (continuous_apply _ |>.mul continuous_const).sub
          (continuous_apply _ |>.mul continuous_const)
    have h2 : Continuous (fun v => f x v * Real.log (f x v) - f x v) :=
      ((hf_smooth x).continuous.mul
        ((hf_smooth x).continuous.log (fun v => ne_of_gt (hf_pos x v)))).sub
        (hf_smooth x).continuous
    exact h1.mul h2
  · exact mul_nonneg hCL_nn (by positivity : 0 ≤ |C_log| + 1)
  · intro v
    rw [Real.norm_eq_abs]
    have hfv := hf_pos x v
    -- |F_i * (f * log f - f)| = |F_i| * f * |log f - 1|
    have hab : |f x v * Real.log (f x v) - f x v| = f x v * |Real.log (f x v) - 1| := by
      rw [show f x v * Real.log (f x v) - f x v = f x v * (Real.log (f x v) - 1) from by ring,
        abs_mul, abs_of_pos hfv]
    -- |log f - 1| ≤ |log f| + 1 ≤ (|C_log| + 1) * (1+‖v‖)^K_log
    have h1v : (1 : ℝ) ≤ (1 + ‖v‖) ^ K_log := one_le_pow₀ (by linarith [norm_nonneg v])
    have hlog_sub : |Real.log (f x v) - 1| ≤ (|C_log| + 1) * (1 + ‖v‖) ^ K_log := by
      have htri : |Real.log (f x v) - 1| ≤ |Real.log (f x v)| + 1 := by
        have := abs_sub (Real.log (f x v)) 1
        simpa using this
      have hbnd := le_trans (hLB x v) (mul_le_mul_of_nonneg_right (le_abs_self _)
        (pow_nonneg (by linarith [norm_nonneg v]) _))
      nlinarith
    calc |(E x + cross v (B x)) i * (f x v * Real.log (f x v) - f x v)|
        = |(E x + cross v (B x)) i| * |f x v * Real.log (f x v) - f x v| := abs_mul _ _
      _ = |(E x + cross v (B x)) i| * (f x v * |Real.log (f x v) - 1|) := by rw [hab]
      _ ≤ CL * (1 + ‖v‖) * (f x v * ((|C_log| + 1) * (1 + ‖v‖) ^ K_log)) := by
          gcongr; exact hCL v i
      _ = CL * (|C_log| + 1) * (1 + ‖v‖) ^ (K_log + 1) * |f x v| := by
          rw [abs_of_pos hfv]
          have h_pow : (1 + ‖v‖) * (1 + ‖v‖) ^ K_log = (1 + ‖v‖) ^ (K_log + 1) :=
            (pow_succ' _ _).symm
          calc CL * (1 + ‖v‖) * (f x v * ((|C_log| + 1) * (1 + ‖v‖) ^ K_log))
              = CL * (|C_log| + 1) * ((1 + ‖v‖) * (1 + ‖v‖) ^ K_log) * f x v := by ring
            _ = CL * (|C_log| + 1) * (1 + ‖v‖) ^ (K_log + 1) * f x v := by rw [h_pow]


end VML
