/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import LeanPool.Clawristotle.CoulombForceTransport

/-\!
# Spatial Transport: Measurability, Joint Integrability, and Continuity

Proves measurability of the spatial gradient component, joint integrability of
the spatial transport term on the product space T³ × ℝ³, and continuity of the
spatial transport integrand. Depends on force transport lemmas from CoulombForceTransport.
-/

open MeasureTheory Matrix Finset BigOperators Real

noncomputable section
namespace VML

/-- The spatial gradient component `v ↦ gradX(fun y => f y v)(x)(i)` is strongly measurable
    in `v`. Proved via difference quotient approximation: each quotient is continuous in `v`
    (since `f(x,·)` is smooth for each torus point), and the fderiv is their pointwise limit. -/
lemma gradX_stronglyMeasurable_v
    (f : Torus3 → (Fin 3 → ℝ) → ℝ)
    (hf_smooth_v : ∀ x, ContDiff ℝ 3 (f x))
    (hf_smooth_x : ∀ v, ContDiff ℝ 2 (periodicLift (fun x => f x v)))
    (x : Torus3) (i : Fin 3) :
    StronglyMeasurable (fun v => FlatTorus3.gradX (fun y => f y v) x i) := by
  -- Unfold to torusGradX on concrete torus
  change StronglyMeasurable (fun v => torusGradX (fun y => f y v) x i)
  unfold torusGradX
  set x₀ := (torusMk_surjective x).choose
  set ei := (Pi.single i (1 : ℝ) : Fin 3 → ℝ)
  -- Approximate fderiv by difference quotients
  set G : ℕ → (Fin 3 → ℝ) → ℝ := fun n v =>
    (↑n + 1 : ℝ) * (f (torusMk (x₀ + (↑n + 1 : ℝ)⁻¹ • ei)) v - f (torusMk x₀) v)
  have hG_sm : ∀ n, StronglyMeasurable (G n) := fun n =>
    ((hf_smooth_v (torusMk (x₀ + _))).continuous.sub
      (hf_smooth_v (torusMk x₀)).continuous).stronglyMeasurable.const_mul _
  apply stronglyMeasurable_of_tendsto Filter.atTop hG_sm
  rw [tendsto_pi_nhds]
  intro v
  set F := periodicLift (fun y => f y v)
  have hF_diff : DifferentiableAt ℝ F x₀ :=
    (hf_smooth_x v).differentiable (by decide) |>.differentiableAt
  have hg : HasDerivAt (fun t : ℝ => x₀ + t • ei) ei 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ei).const_add x₀
  have h_eq : x₀ + (0 : ℝ) • ei = x₀ := by simp
  have hF_at : HasFDerivAt F (fderiv ℝ F x₀) (x₀ + (0 : ℝ) • ei) := by
    rw [h_eq]; exact hF_diff.hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => F (x₀ + t • ei)) (fderiv ℝ F x₀ ei) 0 := by
    convert hF_at.comp_hasDerivAt (x := (0 : ℝ)) hg using 1
  have htendsto_inv : Filter.Tendsto (fun n : ℕ => ((↑n + 1 : ℝ))⁻¹) Filter.atTop
      (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨
      Filter.Tendsto.comp tendsto_inv_atTop_zero
        (Filter.Tendsto.atTop_add (tendsto_natCast_atTop_atTop (R := ℝ)) tendsto_const_nhds),
      Filter.Eventually.of_forall fun n => Set.mem_Ioi.mpr (by positivity)⟩
  have h := Filter.Tendsto.comp hline.tendsto_slope_zero_right htendsto_inv
  simp only [smul_eq_mul, Function.comp_def, inv_inv, zero_smul, add_zero, zero_add] at h
  convert h using 1


/-- Spatial transport joint integrability (Fubini on compact torus × ℝ³).
    Uses: uniform Schwartz grad decay → uniform velocity integral bound,
    combined with finite measure on compact T³ → joint integrability. -/
lemma spatial_transport_joint_integrable
    {f : Torus3 → (Fin 3 → ℝ) → ℝ}
    (hf_pos : ∀ x v, 0 < f x v)
    (hf_smooth_v : ∀ x, ContDiff ℝ 3 (f x))
    (hf_smooth_x : ∀ v, ContDiff ℝ 2 (periodicLift (fun x => f x v)))
    (hSchwartz : UniformSchwartzDecay f)
    (hLogBound : ∃ (C_log : ℝ) (K_log : ℕ), ∀ (x : Torus3) (v : Fin 3 → ℝ),
      |Real.log (f x v)| ≤ C_log * (1 + ‖v‖) ^ K_log) :
    Integrable (Function.uncurry (fun x v =>
      v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x * Real.log (f x v)))
      (volume.prod volume) := by
  obtain ⟨C_log, K_log, hLB⟩ := hLogBound
  set g : Torus3 → (Fin 3 → ℝ) → ℝ :=
    fun x v => v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x * Real.log (f x v) with hg_def
  -- Uniform bound: |g x v| ≤ C_total / (1+‖v‖)^4 for all x, v
  -- from Schwartz grad decay + log bound
  have h_unif_bound : ∃ C_total > 0, ∀ (x : Torus3) (v : Fin 3 → ℝ),
      |g x v| ≤ C_total / (1 + ‖v‖) ^ 4 := by
    -- Get gradient decay bounds for each component
    have hLB' : ∀ (x : Torus3) (v : Fin 3 → ℝ),
        |Real.log (f x v)| ≤ |C_log| * (1 + ‖v‖) ^ K_log :=
      fun x v => le_trans (hLB x v) (mul_le_mul_of_nonneg_right (le_abs_self _)
        (pow_nonneg (by linarith [norm_nonneg v]) _))
    -- Sum of 3 components bound
    obtain ⟨C0, hC0, hG0⟩ := hSchwartz.hGradDecay (K_log + 6) 0
    obtain ⟨C1, hC1, hG1⟩ := hSchwartz.hGradDecay (K_log + 6) 1
    obtain ⟨C2, hC2, hG2⟩ := hSchwartz.hGradDecay (K_log + 6) 2
    refine ⟨(C0 + C1 + C2) * (|C_log| + 1) + 1, by positivity, fun x v => ?_⟩
    have h1v : (1 : ℝ) ≤ 1 + ‖v‖ := le_add_of_nonneg_right (norm_nonneg v)
    have h1v_nn : (0 : ℝ) ≤ 1 + ‖v‖ := le_trans zero_le_one h1v
    -- Decompose g into 3 components
    have hg_eq : g x v = ∑ i : Fin 3, v i *
        FlatTorus3.gradX (fun y => f y v) x i * Real.log (f x v) := by
      simp only [hg_def, dotProduct, Fin.sum_univ_three]; ring
    rw [hg_eq]
    -- |∑ᵢ comp_i| ≤ ∑ᵢ |comp_i|
    calc |∑ i : Fin 3, v i * FlatTorus3.gradX (fun y => f y v) x i * Real.log (f x v)|
        ≤ ∑ i : Fin 3, |v i * FlatTorus3.gradX (fun y => f y v) x i *
            Real.log (f x v)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin 3, (1 + ‖v‖) *
            (if i = 0 then C0 else if i = 1 then C1 else C2) /
            (1 + ‖v‖) ^ (K_log + 6) *
            (|C_log| * (1 + ‖v‖) ^ K_log) := by
          apply Finset.sum_le_sum; intro i _
          rw [abs_mul, abs_mul]
          have hvi : |v i| ≤ 1 + ‖v‖ := le_trans
            ((Real.norm_eq_abs _) ▸ norm_le_pi_norm v i) (le_add_of_nonneg_left zero_le_one)
          have hlog := hLB' x v
          have hgrad : |FlatTorus3.gradX (fun y => f y v) x i| ≤
              (if i = 0 then C0 else if i = 1 then C1 else C2) /
              (1 + ‖v‖) ^ (K_log + 6) := by
            rw [le_div_iff₀ (pow_pos (by linarith : (0 : ℝ) < 1 + ‖v‖) _)]
            fin_cases i
            · exact hG0 x v
            · exact hG1 x v
            · exact hG2 x v
          calc |v i| * |FlatTorus3.gradX (fun y => f y v) x i| * |Real.log (f x v)|
              ≤ (1 + ‖v‖) * ((if i = 0 then C0 else if i = 1 then C1 else C2) /
                (1 + ‖v‖) ^ (K_log + 6)) * (|C_log| * (1 + ‖v‖) ^ K_log) := by
                gcongr
            _ = _ := by ring
      _ ≤ (C0 + C1 + C2) * (|C_log| + 1) / (1 + ‖v‖) ^ 4 := by
          simp only [Fin.sum_univ_three, Fin.isValue, ↓reduceIte, Fin.reduceEq]
          have hpow_bound : (1 + ‖v‖) * (1 + ‖v‖) ^ K_log / (1 + ‖v‖) ^ (K_log + 6) ≤
              1 / (1 + ‖v‖) ^ 4 := by
            rw [div_le_div_iff₀ (pow_pos (by linarith) _) (pow_pos (by linarith) _)]
            rw [one_mul, show K_log + 6 = (K_log + 1) + 5 from by omega, pow_add,
              show (1 + ‖v‖) * (1 + ‖v‖) ^ K_log = (1 + ‖v‖) ^ (K_log + 1) from
                (pow_succ' _ _).symm]
            exact mul_le_mul_of_nonneg_left (by nlinarith [pow_nonneg h1v_nn 4])
              (pow_nonneg h1v_nn _)
          -- Each summand bounded via hpow_bound
          have h_factor : ∀ Ci : ℝ, 0 < Ci →
              (1 + ‖v‖) * Ci / (1 + ‖v‖) ^ (K_log + 6) * (|C_log| * (1 + ‖v‖) ^ K_log) ≤
              Ci * |C_log| / (1 + ‖v‖) ^ 4 := by
            intro Ci hCi
            rw [show (1 + ‖v‖) * Ci / (1 + ‖v‖) ^ (K_log + 6) * (|C_log| * (1 + ‖v‖) ^ K_log) =
                Ci * |C_log| * ((1 + ‖v‖) * (1 + ‖v‖) ^ K_log / (1 + ‖v‖) ^ (K_log + 6))
                from by ring,
              show Ci * |C_log| / (1 + ‖v‖) ^ 4 =
                Ci * |C_log| * (1 / (1 + ‖v‖) ^ 4) from by ring]
            exact mul_le_mul_of_nonneg_left hpow_bound (by positivity)
          have hp4 : (0 : ℝ) < (1 + ‖v‖) ^ 4 := pow_pos (by linarith) 4
          have h_sum_bound : C0 * |C_log| / (1 + ‖v‖) ^ 4 + C1 * |C_log| / (1 + ‖v‖) ^ 4 +
              C2 * |C_log| / (1 + ‖v‖) ^ 4 ≤
              (C0 + C1 + C2) * (|C_log| + 1) / (1 + ‖v‖) ^ 4 := by
            rw [show C0 * |C_log| / (1 + ‖v‖) ^ 4 + C1 * |C_log| / (1 + ‖v‖) ^ 4 +
                C2 * |C_log| / (1 + ‖v‖) ^ 4 =
                (C0 + C1 + C2) * |C_log| / (1 + ‖v‖) ^ 4 from by ring,
              div_le_div_iff₀ hp4 hp4]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (by linarith [abs_nonneg C_log]) (by linarith)) hp4.le
          linarith [h_factor C0 hC0, h_factor C1 hC1, h_factor C2 hC2]
      _ ≤ ((C0 + C1 + C2) * (|C_log| + 1) + 1) / (1 + ‖v‖) ^ 4 := by
          gcongr; linarith
  obtain ⟨C_total, hC_total_pos, h_bound⟩ := h_unif_bound
  -- Use integrable_prod_iff
  refine (integrable_prod_iff ?_).mpr ⟨?_, ?_⟩
  · -- AEStronglyMeasurable on product (joint regularity)
    -- Use stronglyMeasurable_uncurry: need ∀ v, Continuous(x ↦ g x v) and ∀ x, SM(v ↦ g x v)
    have hg_cont_x : ∀ v, Continuous (fun x => g x v) := by
      intro v
      have hcont_f : Continuous (fun x => f x v) :=
        FlatTorus3.hDiff_continuous 0 _ ((hf_smooth_x v).of_le (by decide))
      have hcont_log : Continuous (fun x => Real.log (f x v)) :=
        hcont_f.log (fun x => ne_of_gt (hf_pos x v))
      have hcont_grad : ∀ i, Continuous (fun x =>
          FlatTorus3.gradX (fun y => f y v) x i) :=
        fun i => FlatTorus3.hDiff_continuous 0 _
          (FlatTorus3.hDiff_grad 1 _ i
            ((hf_smooth_x v).of_le (by decide)))
      have hcont_dot : Continuous (fun x =>
          v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x) := by
        simp only [dotProduct, Fin.sum_univ_three]
        exact ((continuous_const.mul (hcont_grad 0)).add
          (continuous_const.mul (hcont_grad 1))).add (continuous_const.mul (hcont_grad 2))
      exact hcont_dot.mul hcont_log
    have hg_sm_v : ∀ x, StronglyMeasurable (fun v => g x v) := by
      intro x
      have hlog_sm : StronglyMeasurable (fun v => Real.log (f x v)) :=
        ((hf_smooth_v x).continuous.log (fun v => ne_of_gt (hf_pos x v))).stronglyMeasurable
      have hgrad_sm : ∀ i, StronglyMeasurable
          (fun v => FlatTorus3.gradX (fun y => f y v) x i) :=
        fun i => gradX_stronglyMeasurable_v f hf_smooth_v hf_smooth_x x i
      have hdot_sm : StronglyMeasurable
          (fun v => v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x) := by
        simp only [dotProduct, Fin.sum_univ_three]
        exact (((continuous_apply 0).stronglyMeasurable.mul (hgrad_sm 0)).add
          ((continuous_apply 1).stronglyMeasurable.mul (hgrad_sm 1))).add
          ((continuous_apply 2).stronglyMeasurable.mul (hgrad_sm 2))
      exact hdot_sm.mul hlog_sm
    exact (stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
      hg_cont_x hg_sm_v).aestronglyMeasurable
  · -- ∀ᵐ x, Integrable (fun v => g x v)
    exact Filter.Eventually.of_forall (fun x =>
      spatial_transport_integrable hf_pos hf_smooth_v hf_smooth_x hSchwartz ⟨C_log, K_log, hLB⟩ x)
  · -- Integrable (fun x => ∫ v, ‖g x v‖) on compact T³
    -- The velocity integral is uniformly bounded by C_total * M
    -- where M = ∫ v, 1/(1+‖v‖)^4, so the function is bounded on T³ (finite measure)
    apply (integrable_const (C_total * ∫ v : Fin 3 → ℝ, (1 + ‖v‖)⁻¹ ^ 4)).mono'
    · -- AEStronglyMeasurable (x ↦ ∫ v, ‖g x v‖) via dominated convergence → continuous
      have hg_cont : ∀ v, Continuous (fun x => g x v) := by
        intro v
        have hcont_f : Continuous (fun x => f x v) :=
          FlatTorus3.hDiff_continuous 0 _ ((hf_smooth_x v).of_le (by decide))
        have hcont_log : Continuous (fun x => Real.log (f x v)) :=
          hcont_f.log (fun x => ne_of_gt (hf_pos x v))
        have hcont_grad : ∀ i, Continuous (fun x =>
            FlatTorus3.gradX (fun y => f y v) x i) :=
          fun i => FlatTorus3.hDiff_continuous 0 _
            (FlatTorus3.hDiff_grad 1 _ i
              ((hf_smooth_x v).of_le (by decide)))
        have hcont_dot : Continuous (fun x =>
            v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x) := by
          simp only [dotProduct, Fin.sum_univ_three]
          exact ((continuous_const.mul (hcont_grad 0)).add
            (continuous_const.mul (hcont_grad 1))).add (continuous_const.mul (hcont_grad 2))
        exact hcont_dot.mul hcont_log
      exact (continuous_of_dominated
        (fun x => (spatial_transport_integrable hf_pos hf_smooth_v hf_smooth_x hSchwartz
          ⟨C_log, K_log, hLB⟩ x).norm.aestronglyMeasurable)
        (fun x => Filter.Eventually.of_forall fun v => by
          change ‖‖g x v‖‖ ≤ C_total / (1 + ‖v‖) ^ 4
          rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), Real.norm_eq_abs]
          exact h_bound x v)
        (inverse_poly_integrable C_total)
        (Filter.Eventually.of_forall fun v => (hg_cont v).norm)).aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun v => norm_nonneg _))]
      calc ∫ v, ‖g x v‖
          ≤ ∫ v, C_total / (1 + ‖v‖) ^ 4 := by
            apply integral_mono_of_nonneg
            · exact Filter.Eventually.of_forall (fun v => norm_nonneg _)
            · exact inverse_poly_integrable C_total
            · exact Filter.Eventually.of_forall (fun v => by
                change ‖g x v‖ ≤ C_total / (1 + ‖v‖) ^ 4
                rw [Real.norm_eq_abs]; exact h_bound x v)
        _ = C_total * ∫ v, (1 + ‖v‖)⁻¹ ^ 4 := by
            simp_rw [div_eq_mul_inv, inv_pow]; exact integral_const_mul _ _


/-- The parametric integral `x ↦ ∫ v, v ⬝ᵥ gradX(f)(x) * log(f(x,v))` is continuous
    on the torus. Proved via `continuous_of_dominated` using the uniform Schwartz+log bound
    from `spatial_transport_joint_integrable`. -/
lemma spatial_transport_continuous
    {f : Torus3 → (Fin 3 → ℝ) → ℝ}
    (hf_pos : ∀ x v, 0 < f x v)
    (hf_smooth_v : ∀ x, ContDiff ℝ 3 (f x))
    (hf_smooth_x : ∀ v, ContDiff ℝ 2 (periodicLift (fun x => f x v)))
    (hSchwartz : UniformSchwartzDecay f)
    (hLogBound : ∃ (C_log : ℝ) (K_log : ℕ), ∀ (x : Torus3) (v : Fin 3 → ℝ),
      |Real.log (f x v)| ≤ C_log * (1 + ‖v‖) ^ K_log) :
    Continuous (fun x => ∫ v, v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x *
      Real.log (f x v)) := by
  obtain ⟨C_log, K_log, hLB⟩ := hLogBound
  set g : Torus3 → (Fin 3 → ℝ) → ℝ :=
    fun x v => v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x * Real.log (f x v) with hg_def
  -- Reuse the uniform bound from spatial_transport_joint_integrable
  have hLB' : ∀ (x : Torus3) (v : Fin 3 → ℝ),
      |Real.log (f x v)| ≤ |C_log| * (1 + ‖v‖) ^ K_log :=
    fun x v => le_trans (hLB x v) (mul_le_mul_of_nonneg_right (le_abs_self _)
      (pow_nonneg (by linarith [norm_nonneg v]) _))
  obtain ⟨C0, hC0, hG0⟩ := hSchwartz.hGradDecay (K_log + 6) 0
  obtain ⟨C1, hC1, hG1⟩ := hSchwartz.hGradDecay (K_log + 6) 1
  obtain ⟨C2, hC2, hG2⟩ := hSchwartz.hGradDecay (K_log + 6) 2
  set C_total := (C0 + C1 + C2) * (|C_log| + 1) + 1
  have hC_total_pos : 0 < C_total := by positivity
  have h_bound : ∀ (x : Torus3) (v : Fin 3 → ℝ),
      |g x v| ≤ C_total / (1 + ‖v‖) ^ 4 := by
    intro x v
    have h1v : (1 : ℝ) ≤ 1 + ‖v‖ := le_add_of_nonneg_right (norm_nonneg v)
    have h1v_nn : (0 : ℝ) ≤ 1 + ‖v‖ := le_trans zero_le_one h1v
    have hg_eq : g x v = ∑ i : Fin 3, v i *
        FlatTorus3.gradX (fun y => f y v) x i * Real.log (f x v) := by
      simp only [hg_def, dotProduct, Fin.sum_univ_three]; ring
    rw [hg_eq]
    calc |∑ i : Fin 3, v i * FlatTorus3.gradX (fun y => f y v) x i * Real.log (f x v)|
        ≤ ∑ i : Fin 3, |v i * FlatTorus3.gradX (fun y => f y v) x i *
            Real.log (f x v)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin 3, (1 + ‖v‖) *
            (if i = 0 then C0 else if i = 1 then C1 else C2) /
            (1 + ‖v‖) ^ (K_log + 6) *
            (|C_log| * (1 + ‖v‖) ^ K_log) := by
          apply Finset.sum_le_sum; intro i _
          rw [abs_mul, abs_mul]
          have hvi : |v i| ≤ 1 + ‖v‖ := le_trans
            ((Real.norm_eq_abs _) ▸ norm_le_pi_norm v i) (le_add_of_nonneg_left zero_le_one)
          have hlog := hLB' x v
          have hgrad : |FlatTorus3.gradX (fun y => f y v) x i| ≤
              (if i = 0 then C0 else if i = 1 then C1 else C2) /
              (1 + ‖v‖) ^ (K_log + 6) := by
            rw [le_div_iff₀ (pow_pos (by linarith : (0 : ℝ) < 1 + ‖v‖) _)]
            fin_cases i
            · exact hG0 x v
            · exact hG1 x v
            · exact hG2 x v
          calc |v i| * |FlatTorus3.gradX (fun y => f y v) x i| * |Real.log (f x v)|
              ≤ (1 + ‖v‖) * ((if i = 0 then C0 else if i = 1 then C1 else C2) /
                (1 + ‖v‖) ^ (K_log + 6)) * (|C_log| * (1 + ‖v‖) ^ K_log) := by
                gcongr
            _ = _ := by ring
      _ ≤ (C0 + C1 + C2) * (|C_log| + 1) / (1 + ‖v‖) ^ 4 := by
          simp only [Fin.sum_univ_three, Fin.isValue, ↓reduceIte, Fin.reduceEq]
          have hpow_bound : (1 + ‖v‖) * (1 + ‖v‖) ^ K_log / (1 + ‖v‖) ^ (K_log + 6) ≤
              1 / (1 + ‖v‖) ^ 4 := by
            rw [div_le_div_iff₀ (pow_pos (by linarith) _) (pow_pos (by linarith) _)]
            rw [one_mul, show K_log + 6 = (K_log + 1) + 5 from by omega, pow_add,
              show (1 + ‖v‖) * (1 + ‖v‖) ^ K_log = (1 + ‖v‖) ^ (K_log + 1) from
                (pow_succ' _ _).symm]
            exact mul_le_mul_of_nonneg_left (by nlinarith [pow_nonneg h1v_nn 4])
              (pow_nonneg h1v_nn _)
          have h_factor : ∀ Ci : ℝ, 0 < Ci →
              (1 + ‖v‖) * Ci / (1 + ‖v‖) ^ (K_log + 6) * (|C_log| * (1 + ‖v‖) ^ K_log) ≤
              Ci * |C_log| / (1 + ‖v‖) ^ 4 := by
            intro Ci hCi
            rw [show (1 + ‖v‖) * Ci / (1 + ‖v‖) ^ (K_log + 6) * (|C_log| * (1 + ‖v‖) ^ K_log) =
                Ci * |C_log| * ((1 + ‖v‖) * (1 + ‖v‖) ^ K_log / (1 + ‖v‖) ^ (K_log + 6))
                from by ring,
              show Ci * |C_log| / (1 + ‖v‖) ^ 4 =
                Ci * |C_log| * (1 / (1 + ‖v‖) ^ 4) from by ring]
            exact mul_le_mul_of_nonneg_left hpow_bound (by positivity)
          have hp4 : (0 : ℝ) < (1 + ‖v‖) ^ 4 := pow_pos (by linarith) 4
          have h_sum_bound : C0 * |C_log| / (1 + ‖v‖) ^ 4 + C1 * |C_log| / (1 + ‖v‖) ^ 4 +
              C2 * |C_log| / (1 + ‖v‖) ^ 4 ≤
              (C0 + C1 + C2) * (|C_log| + 1) / (1 + ‖v‖) ^ 4 := by
            rw [show C0 * |C_log| / (1 + ‖v‖) ^ 4 + C1 * |C_log| / (1 + ‖v‖) ^ 4 +
                C2 * |C_log| / (1 + ‖v‖) ^ 4 =
                (C0 + C1 + C2) * |C_log| / (1 + ‖v‖) ^ 4 from by ring,
              div_le_div_iff₀ hp4 hp4]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (by linarith [abs_nonneg C_log]) (by linarith)) hp4.le
          linarith [h_factor C0 hC0, h_factor C1 hC1, h_factor C2 hC2]
      _ ≤ C_total / (1 + ‖v‖) ^ 4 := by
          gcongr; linarith
  -- Apply continuous_of_dominated
  exact continuous_of_dominated
    (fun x => (spatial_transport_integrable hf_pos hf_smooth_v hf_smooth_x hSchwartz
      ⟨C_log, K_log, hLB⟩ x).aestronglyMeasurable)
    (fun x => Filter.Eventually.of_forall fun v => by
      change ‖g x v‖ ≤ C_total / (1 + ‖v‖) ^ 4
      rw [Real.norm_eq_abs]; exact h_bound x v)
    (inverse_poly_integrable C_total)
    (Filter.Eventually.of_forall fun v => by
      change Continuous (fun x => g x v)
      have hcont_f : Continuous (fun x => f x v) :=
        FlatTorus3.hDiff_continuous 0 _ ((hf_smooth_x v).of_le (by decide))
      have hcont_log : Continuous (fun x => Real.log (f x v)) :=
        hcont_f.log (fun x => ne_of_gt (hf_pos x v))
      have hcont_grad : ∀ i, Continuous (fun x =>
          FlatTorus3.gradX (fun y => f y v) x i) :=
        fun i => FlatTorus3.hDiff_continuous 0 _
          (FlatTorus3.hDiff_grad 1 _ i
            ((hf_smooth_x v).of_le (by decide)))
      have hcont_dot : Continuous (fun x =>
          v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x) := by
        simp only [dotProduct, Fin.sum_univ_three]
        exact ((continuous_const.mul (hcont_grad 0)).add
          (continuous_const.mul (hcont_grad 1))).add (continuous_const.mul (hcont_grad 2))
      exact hcont_dot.mul hcont_log)

/-- Continuity of entropy dissipation for the Coulomb kernel.
    Derives from the Vlasov equation: force transport vanishes by IBP,
    so D(f x) = ν⁻¹ ∫ spatial·log f, which is continuous by `spatial_transport_continuous`. -/
lemma entropy_dissipation_continuous_coulomb
    (f : Torus3 → (Fin 3 → ℝ) → ℝ)
    (E B : Torus3 → Fin 3 → ℝ)
    (ν : ℝ) (hν : 0 < ν)
    (hf_pos : ∀ x v, 0 < f x v)
    (hf_smooth_v : ∀ x, ContDiff ℝ 3 (f x))
    (hf_smooth_x : ∀ v, ContDiff ℝ 2 (periodicLift (fun x => f x v)))
    (hSchwartz : UniformSchwartzDecay f)
    (hLogBound : ∃ (C : ℝ) (K : ℕ), ∀ (x : Torus3) (v : Fin 3 → ℝ),
      |Real.log (f x v)| ≤ C * (1 + ‖v‖) ^ K)
    (hVlasov : ∀ x v,
      dotProduct v (torusGradX (fun y => f y v) x) +
      dotProduct (E x + cross v (B x)) (vGrad (f x) v) =
      ν * LandauOperator coulombKernel (f x) v) :
    Continuous (fun x => entropyDissipation coulombKernel (f x)) := by
  obtain ⟨C_log, K_log, hLB⟩ := hLogBound
  have hLB' : ∃ C K, ∀ x v, |Real.log (f x v)| ≤ C * (1 + ‖v‖) ^ K :=
    ⟨C_log, K_log, hLB⟩
  have hST_int := fun x =>
    spatial_transport_integrable hf_pos hf_smooth_v hf_smooth_x hSchwartz hLB' x
  have hFT_int := fun x =>
    force_transport_integrable_coulomb E B hf_pos hf_smooth_v hSchwartz hLB' x
  have h_key : ∀ x, ν * entropyDissipation coulombKernel (f x) =
      ∫ v, v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x * Real.log (f x v) := by
    intro x
    unfold entropyDissipation
    rw [← integral_const_mul]
    have hrw : (fun v => ν * (LandauOperator coulombKernel (f x) v * Real.log (f x v))) =
        (fun v => v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x * Real.log (f x v) +
          (E x + cross v (B x)) ⬝ᵥ vGrad (f x) v * Real.log (f x v)) := by
      ext v; have hV := hVlasov x v
      have : ν * (LandauOperator coulombKernel (f x) v * Real.log (f x v)) =
          (ν * LandauOperator coulombKernel (f x) v) * Real.log (f x v) := by ring
      rw [this, ← hV]
      have : v ⬝ᵥ torusGradX (fun y => f y v) x =
          v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x := rfl
      rw [this]; ring
    rw [hrw, integral_add (hST_int x) (hFT_int x)]
    rw [force_transport_zero (f x) (E x) (B x) (hf_pos x) ((hf_smooth_v x).of_le (by norm_num))
      ((hSchwartz.integrable hf_smooth_v) x)
      (fun i => force_ibp_f_dg_integrable_coulomb E B hf_pos hf_smooth_v hSchwartz hLB' x i)
      (fun i => force_ibp_fg_integrable_coulomb E B hf_pos hf_smooth_v hSchwartz hLB' x i)]
    simp [add_zero]
  have h_eq : (fun x => entropyDissipation coulombKernel (f x)) =
      (fun x => ν⁻¹ * ∫ v, v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x *
        Real.log (f x v)) := by
    ext x
    have := h_key x
    field_simp at this ⊢
    linarith
  rw [h_eq]
  exact continuous_const.mul
    (spatial_transport_continuous hf_pos hf_smooth_v hf_smooth_x hSchwartz hLB')

end VML
