/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import LeanPool.Clawristotle.CoulombFluxConv

/-!
# Flux Derivative Decay and IBP Integrability for Coulomb

Proves the Coulomb flux derivative has Schwartz-class decay (from the convolution
decomposition) and the IBP integrability condition for the flux derivative times log f.
Depends on differentiability and decomposition results from CoulombFluxConv.
-/

open MeasureTheory Matrix Finset BigOperators Real

noncomputable section
namespace VML

/-- The directional derivative of a differentiable function is measurable.
    Uses the fact that fderiv(f)(v)(h) = lim_{n→∞} (n+1)*(f(v+(n+1)⁻¹*h) - f(v)),
    which is a pointwise limit of continuous (hence measurable) functions. -/
private lemma aestronglyMeasurable_fderiv_apply
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasureSpace E] [OpensMeasurableSpace E] [SecondCountableTopology E]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {f : E → F} (hf : Differentiable ℝ f) (h : E) :
    AEStronglyMeasurable (fun v => fderiv ℝ f v h) := by
  have h_meas : Measurable (fun v => fderiv ℝ f v h) := by
    apply measurable_of_tendsto_metrizable
      (f := fun (n : ℕ) (v : E) => ((n : ℝ) + 1) • (f (v + ((n : ℝ) + 1)⁻¹ • h) - f v))
    · intro n
      exact (continuous_const.smul
        ((hf.continuous.comp (continuous_id.add continuous_const)).sub
          hf.continuous)).measurable
    · rw [tendsto_pi_nhds]
      intro v
      have hc : Filter.Tendsto (fun n : ℕ => ‖((n : ℝ) + 1)‖) Filter.atTop Filter.atTop := by
        have : (fun n : ℕ => ‖((n : ℝ) + 1)‖) = (fun n : ℕ => ((n : ℝ) + 1)) := by
          ext n; exact Real.norm_of_nonneg (by positivity)
        rw [this]
        exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
      exact (hf v).hasFDerivAt.lim h hc
  exact h_meas.aestronglyMeasurable

/-- The derivative of the Coulomb flux component has Schwartz-class decay.
    Since the flux decomposes into convolutions of Coulomb entries with Schwartz functions,
    its derivatives inherit Schwartz decay via coulomb_entry_conv_deriv_decay. -/
lemma coulomb_flux_deriv_schwartz_decay
    (f : (Fin 3 → ℝ) → ℝ) (hf_pos : ∀ v, 0 < f v) (hf_smooth : ContDiff ℝ 3 f)
    (hf_schwartz : ∀ (N : ℕ) {k : ℕ}, k ≤ 2 →
      ∃ C > 0, ∀ v, ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
    (i : Fin 3) (N : ℕ) :
    ∃ C > 0, ∀ v, ‖fderiv ℝ (fun v =>
      (∫ w, mulVec (landauMatrix coulombKernel (v - w))
        (f w • vGrad f v - f v • vGrad f w)) i) v‖ * (1 + ‖v‖) ^ N ≤ C := by
  -- ∂_j f is Schwartz
  have hdf_schwartz := fun j => schwartz_fderiv_component_schwartz f hf_smooth hf_schwartz j
  -- Each convolution K_{ij}, L_{ij} has uniformly bounded derivatives
  -- Lift hf_schwartz to the ∀ N {k}, k ≤ 1 form needed by conv lemmas
  have hf_schwartz_le1 : ∀ (N : ℕ) {k : ℕ}, k ≤ 1 → ∃ C > 0, ∀ v,
      ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C :=
    fun N k hk => hf_schwartz N (le_trans hk (by linarith))
  have hK_fderiv_bdd : ∀ j, ∃ C > 0, ∀ v,
      ‖fderiv ℝ (fun v => ∫ w, landauMatrix coulombKernel (v - w) i j * f w) v‖ ≤ C :=
    fun j => coulomb_entry_conv_deriv_bounded f (hf_smooth.of_le (by decide)) hf_schwartz_le1 i j
  have hL_fderiv_bdd : ∀ j, ∃ C > 0, ∀ v,
      ‖fderiv ℝ (fun v => ∫ w, landauMatrix coulombKernel (v - w) i j *
        fderiv ℝ f w (Pi.single j 1)) v‖ ≤ C :=
    fun j => coulomb_entry_conv_deriv_bounded _ (hf_smooth.fderiv_right (by decide) |>.clm_apply
      contDiff_const)
      (fun N {k} (hk : k ≤ 1) => hdf_schwartz j N (by exact_mod_cast (by omega : k + 1 ≤ 2))) i j
  -- Replace flux with K/L decomposition
  have h_fn_eq : (fun v => (∫ w, mulVec (landauMatrix coulombKernel (v - w))
      (f w • vGrad f v - f v • vGrad f w)) i) =
    (fun v => ∑ j : Fin 3,
      (fderiv ℝ f v (Pi.single j 1) *
        (∫ w, landauMatrix coulombKernel (v - w) i j * f w) -
       f v * (∫ w, landauMatrix coulombKernel (v - w) i j *
        fderiv ℝ f w (Pi.single j 1)))) :=
    funext (coulomb_flux_eq_decomposed f hf_pos hf_smooth hf_schwartz i)
  rw [h_fn_eq]
  -- Differentiability of components
  have hK_diff : ∀ j, Differentiable ℝ
      (fun v => ∫ w, landauMatrix coulombKernel (v - w) i j * f w) :=
    fun j => coulomb_entry_conv_differentiable f (hf_smooth.of_le (by decide)) hf_schwartz_le1 i j
  have hL_diff : ∀ j, Differentiable ℝ
      (fun v => ∫ w, landauMatrix coulombKernel (v - w) i j *
        fderiv ℝ f w (Pi.single j 1)) :=
    fun j => coulomb_entry_conv_differentiable _
      (hf_smooth.fderiv_right (by exact_mod_cast (by omega : 2 + 1 ≤ 3))
        |>.clm_apply contDiff_const)
      (fun N {k} (hk : k ≤ 1) => hdf_schwartz j N (by exact_mod_cast (by omega : k + 1 ≤ 2))) i j
  have ha_diff : ∀ j, Differentiable ℝ (fun v => fderiv ℝ f v (Pi.single j 1)) := by
    intro j
    have h_cont_diff_df : ContDiff ℝ 1 (fun v => fderiv ℝ f v (Pi.single j 1)) :=
      (hf_smooth.fderiv_right (by exact_mod_cast (by omega : 1 + 1 ≤ 3))).clm_apply contDiff_const
    exact h_cont_diff_df.differentiable (by decide)
  have hf_diff := hf_smooth.differentiable (by decide)
  -- Schwartz decay facts: f and ∂_j f bounded, their fderiv decays
  have hf_decay := schwartz_pointwise_decay hf_schwartz
  -- K_j and L_j uniformly bounded via coulomb_entry_conv_uniform_bound
  have hdf_decay_abs := schwartz_fderiv_component_decay hf_schwartz
  have hK_bdd : ∀ j, ∃ MK > 0, ∀ v,
      |∫ w, landauMatrix coulombKernel (v - w) i j * f w| ≤ MK :=
    fun j => coulomb_entry_conv_uniform_bound hf_decay
      hf_smooth.continuous.aestronglyMeasurable i j
  have hL_bdd : ∀ j, ∃ ML > 0, ∀ v, |∫ w, landauMatrix coulombKernel (v - w) i j *
      fderiv ℝ f w (Pi.single j 1)| ≤ ML :=
    fun j => coulomb_entry_conv_uniform_bound (hdf_decay_abs j)
      ((ContDiff.continuous (n := 2)
          ((hf_smooth.fderiv_right (by exact_mod_cast (by omega : 2 + 1 ≤ 3))).clm_apply
            (contDiff_const (c := (Pi.single j 1 : Fin 3 → ℝ))))).aestronglyMeasurable) i j
  -- f is bounded
  obtain ⟨Mf, hMf_pos, hMf⟩ := hf_decay 0
  have hf_sup : ∀ v, |f v| ≤ Mf := fun v => by simpa using hMf v
  -- ∂_j f is bounded
  have hdf_sup : ∀ j, ∃ M, ∀ v, |fderiv ℝ f v (Pi.single j 1)| ≤ M := by
    intro j; obtain ⟨C, _, h⟩ := hdf_decay_abs j 0
    exact ⟨C, fun v => by simpa using h v⟩
  obtain ⟨Mdf, hMdf⟩ := hdf_sup 0  -- use as proxy; bound for all j by taking max
  -- fderiv(f) Schwartz decay: ‖fderiv f v‖ * (1+‖v‖)^N ≤ Cf
  obtain ⟨Cf, hCf_pos, hCf⟩ := hf_schwartz N (k := 1) (by decide)
  -- fderiv(∂_j f) Schwartz decay
  -- Per-component fderiv decay: for each j, bound ‖fderiv(∂_j f * K_j - f * L_j)(v)‖ * (1+‖v‖)^N
  -- by product rule: ≤ |∂_j f(v)| * ‖fderiv(K_j)(v)‖ + |K_j(v)| * ‖fderiv(∂_j f)(v)‖
  --                    + |f(v)| * ‖fderiv(L_j)(v)‖ + |L_j(v)| * ‖fderiv(f)(v)‖
  -- Each pair is (bounded) * (Schwartz decay) so (bounded) * (Schwartz) ≤ const
  have h_per_term : ∀ j, ∃ C > 0, ∀ v,
      ‖fderiv ℝ (fun v => fderiv ℝ f v (Pi.single j 1) *
        (∫ w, landauMatrix coulombKernel (v - w) i j * f w) -
       f v * (∫ w, landauMatrix coulombKernel (v - w) i j *
        fderiv ℝ f w (Pi.single j 1))) v‖ * (1 + ‖v‖) ^ N ≤ C := by
    intro j
    -- Per-j uniform bounds on K and L convolutions
    obtain ⟨MKj, hMKj_pos, hMKj⟩ := hK_bdd j
    obtain ⟨MLj, hMLj_pos, hMLj⟩ := hL_bdd j
    -- Schwartz decay of ∂_j f with polynomial weight N
    obtain ⟨Mdj_N, hMdj_N_pos, hMdj_N⟩ := hdf_decay_abs j N
    obtain ⟨Cdj, hCdj_pos, hCdj⟩ :=
      schwartz_fderiv_component_schwartz f hf_smooth hf_schwartz j N
        (show 1 + 1 ≤ 2 by norm_num)
    -- Uniform bounds on fderiv of K and L convolutions
    obtain ⟨CKj, hCKj_pos, hCKj⟩ := hK_fderiv_bdd j
    obtain ⟨CLj, hCLj_pos, hCLj⟩ := hL_fderiv_bdd j
    -- Schwartz decay of f with polynomial weight N
    obtain ⟨Mf_N, hMf_N_pos, hMf_N⟩ := hf_decay N
    refine ⟨Mdj_N * CKj + MKj * Cdj + Mf_N * CLj + MLj * Cf + 1, by positivity, fun v => ?_⟩
    -- Product rule: fderiv (a * b - c * d) =
    --   a • fderiv b + b • fderiv a - (c • fderiv d + d • fderiv c)
    have h_ab := (ha_diff j v).hasFDerivAt.mul (hK_diff j v).hasFDerivAt
    have h_cd := (hf_diff v).hasFDerivAt.mul (hL_diff j v).hasFDerivAt
    have h_fderiv := (h_ab.sub h_cd).fderiv
    have h_fn_eq' : (fun v => fderiv ℝ f v (Pi.single j 1) *
        (∫ w, landauMatrix coulombKernel (v - w) i j * f w) -
       f v * (∫ w, landauMatrix coulombKernel (v - w) i j *
        fderiv ℝ f w (Pi.single j 1))) =
      (((fun v => fderiv ℝ f v (Pi.single j 1)) *
        (fun v => ∫ w, landauMatrix coulombKernel (v - w) i j * f w)) -
       (f * (fun v => ∫ w, landauMatrix coulombKernel (v - w) i j *
        fderiv ℝ f w (Pi.single j 1)))) := by
      ext v; simp [Pi.mul_apply, Pi.sub_apply]
    rw [h_fn_eq', h_fderiv]
    -- ‖a•K' + K•a' - (f•L' + L•f')‖ * (1+‖v‖)^N
    calc ‖fderiv ℝ f v (Pi.single j 1) • fderiv ℝ (fun v => ∫ w,
            landauMatrix coulombKernel (v - w) i j * f w) v +
          (∫ w, landauMatrix coulombKernel (v - w) i j * f w) •
            fderiv ℝ (fun v => fderiv ℝ f v (Pi.single j 1)) v -
          (f v • fderiv ℝ (fun v => ∫ w, landauMatrix coulombKernel (v - w) i j *
            fderiv ℝ f w (Pi.single j 1)) v +
          (∫ w, landauMatrix coulombKernel (v - w) i j *
            fderiv ℝ f w (Pi.single j 1)) • fderiv ℝ f v)‖ * (1 + ‖v‖) ^ N
        ≤ (‖fderiv ℝ f v (Pi.single j 1) • fderiv ℝ (fun v => ∫ w,
              landauMatrix coulombKernel (v - w) i j * f w) v‖ +
           ‖(∫ w, landauMatrix coulombKernel (v - w) i j * f w) •
              fderiv ℝ (fun v => fderiv ℝ f v (Pi.single j 1)) v‖ +
           ‖f v • fderiv ℝ (fun v => ∫ w, landauMatrix coulombKernel (v - w) i j *
              fderiv ℝ f w (Pi.single j 1)) v‖ +
           ‖(∫ w, landauMatrix coulombKernel (v - w) i j *
              fderiv ℝ f w (Pi.single j 1)) • fderiv ℝ f v‖) * (1 + ‖v‖) ^ N := by
          gcongr
          have h_tri := norm_sub_le
            ((fderiv ℝ f v) (Pi.single j 1) •
              fderiv ℝ (fun v => ∫ w, landauMatrix coulombKernel (v - w) i j * f w) v +
             (∫ w, landauMatrix coulombKernel (v - w) i j * f w) •
              fderiv ℝ (fun v => fderiv ℝ f v (Pi.single j 1)) v)
            (f v • fderiv ℝ (fun v => ∫ w, landauMatrix coulombKernel (v - w) i j *
              fderiv ℝ f w (Pi.single j 1)) v +
             (∫ w, landauMatrix coulombKernel (v - w) i j *
              fderiv ℝ f w (Pi.single j 1)) • fderiv ℝ f v)
          linarith [norm_add_le
            ((fderiv ℝ f v) (Pi.single j 1) •
              fderiv ℝ (fun v => ∫ w, landauMatrix coulombKernel (v - w) i j * f w) v)
            ((∫ w, landauMatrix coulombKernel (v - w) i j * f w) •
              fderiv ℝ (fun v => fderiv ℝ f v (Pi.single j 1)) v),
            norm_add_le
            (f v • fderiv ℝ (fun v => ∫ w, landauMatrix coulombKernel (v - w) i j *
              fderiv ℝ f w (Pi.single j 1)) v)
            ((∫ w, landauMatrix coulombKernel (v - w) i j *
              fderiv ℝ f w (Pi.single j 1)) • fderiv ℝ f v)]
      _ = (|fderiv ℝ f v (Pi.single j 1)| * ‖fderiv ℝ (fun v => ∫ w,
              landauMatrix coulombKernel (v - w) i j * f w) v‖ +
           |∫ w, landauMatrix coulombKernel (v - w) i j * f w| *
              ‖fderiv ℝ (fun v => fderiv ℝ f v (Pi.single j 1)) v‖ +
           |f v| * ‖fderiv ℝ (fun v => ∫ w, landauMatrix coulombKernel (v - w) i j *
              fderiv ℝ f w (Pi.single j 1)) v‖ +
           |∫ w, landauMatrix coulombKernel (v - w) i j *
              fderiv ℝ f w (Pi.single j 1)| * ‖fderiv ℝ f v‖) * (1 + ‖v‖) ^ N := by
          simp [norm_smul, Real.norm_eq_abs]
      _ ≤ (Mdj_N * CKj + MKj * Cdj + Mf_N * CLj + MLj * Cf) * 1 + 0 := by
          rw [mul_one, add_zero]
          -- Convert fderiv norms to iteratedFDeriv 1 norms, then apply Schwartz bounds
          have hCf_v : ‖fderiv ℝ f v‖ * (1 + ‖v‖) ^ N ≤ Cf := by
            rw [norm_fderiv_eq_iteratedFDeriv_one]; exact hCf v
          have hCdj_v : ‖fderiv ℝ (fun v => fderiv ℝ f v (Pi.single j 1)) v‖ *
              (1 + ‖v‖) ^ N ≤ Cdj := by
            rw [norm_fderiv_eq_iteratedFDeriv_one]; exact hCdj v
          -- Each term: one factor has Schwartz decay × P, the other is bounded
          -- t1: |∂_j f(v)| * ‖DK(v)‖ * P ≤ (|∂_j f(v)| * P) * ‖DK(v)‖ ≤ Mdj_N * CKj
          have hMdj_N_v := hMdj_N v
          have t1 := mul_le_mul hMdj_N_v (hCKj v)
            (by positivity) (le_trans (by positivity) hMdj_N_v)
          -- t2: |K(v)| * ‖D(∂_j f)(v)‖ * P ≤ |K(v)| * (‖D(∂_j f)(v)‖ * P) ≤ MKj * Cdj
          have t2 := mul_le_mul (hMKj v) hCdj_v
            (by positivity) (le_trans (abs_nonneg _) (hMKj v))
          -- t3: |f(v)| * ‖DL(v)‖ * P ≤ (|f(v)| * P) * ‖DL(v)‖ ≤ Mf_N * CLj
          have hMf_N_v := hMf_N v
          have t3 := mul_le_mul hMf_N_v (hCLj v)
            (by positivity) (le_trans (by positivity) hMf_N_v)
          -- t4: |L(v)| * ‖Df(v)‖ * P ≤ |L(v)| * (‖Df(v)‖ * P) ≤ MLj * Cf
          have t4 := mul_le_mul (hMLj v) hCf_v
            (by positivity) (le_trans (abs_nonneg _) (hMLj v))
          nlinarith [t1, t2, t3, t4]
      _ ≤ Mdj_N * CKj + MKj * Cdj + Mf_N * CLj + MLj * Cf + 1 := by linarith
  -- Sum over j
  obtain ⟨C0, hC0, h0⟩ := h_per_term 0
  obtain ⟨C1, hC1, h1⟩ := h_per_term 1
  obtain ⟨C2, hC2, h2⟩ := h_per_term 2
  refine ⟨C0 + C1 + C2 + 1, by positivity, fun v => ?_⟩
  -- fderiv of sum
  have h_sum_diff : ∀ j, DifferentiableAt ℝ (fun v => fderiv ℝ f v (Pi.single j 1) *
      (∫ w, landauMatrix coulombKernel (v - w) i j * f w) -
     f v * (∫ w, landauMatrix coulombKernel (v - w) i j *
      fderiv ℝ f w (Pi.single j 1))) v :=
    fun j => ((ha_diff j v).hasFDerivAt.mul (hK_diff j v).hasFDerivAt).differentiableAt.sub
      ((hf_diff v).hasFDerivAt.mul (hL_diff j v).hasFDerivAt).differentiableAt
  have h_fderiv_sum : fderiv ℝ (fun v => ∑ j : Fin 3, (fderiv ℝ f v (Pi.single j 1) *
      (∫ w, landauMatrix coulombKernel (v - w) i j * f w) -
     f v * (∫ w, landauMatrix coulombKernel (v - w) i j *
      fderiv ℝ f w (Pi.single j 1)))) v =
    ∑ j : Fin 3, fderiv ℝ (fun v => fderiv ℝ f v (Pi.single j 1) *
      (∫ w, landauMatrix coulombKernel (v - w) i j * f w) -
     f v * (∫ w, landauMatrix coulombKernel (v - w) i j *
      fderiv ℝ f w (Pi.single j 1))) v := by
    simp only [Fin.sum_univ_three]
    exact ((h_sum_diff 0).hasFDerivAt.add (h_sum_diff 1).hasFDerivAt |>.add
      (h_sum_diff 2).hasFDerivAt).fderiv
  rw [h_fderiv_sum]
  calc ‖∑ j : Fin 3, fderiv ℝ _ v‖ * (1 + ‖v‖) ^ N
      ≤ (∑ j : Fin 3, ‖fderiv ℝ (fun v => fderiv ℝ f v (Pi.single j 1) *
          (∫ w, landauMatrix coulombKernel (v - w) i j * f w) -
         f v * (∫ w, landauMatrix coulombKernel (v - w) i j *
          fderiv ℝ f w (Pi.single j 1))) v‖) * (1 + ‖v‖) ^ N := by
        gcongr; exact norm_sum_le _ _
    _ = ∑ j : Fin 3, ‖fderiv ℝ (fun v => fderiv ℝ f v (Pi.single j 1) *
          (∫ w, landauMatrix coulombKernel (v - w) i j * f w) -
         f v * (∫ w, landauMatrix coulombKernel (v - w) i j *
          fderiv ℝ f w (Pi.single j 1))) v‖ * (1 + ‖v‖) ^ N := by
        rw [Finset.sum_mul]
    _ ≤ C0 + C1 + C2 := by
        rw [Fin.sum_univ_three]; linarith [h0 v, h1 v, h2 v]
    _ ≤ C0 + C1 + C2 + 1 := le_add_of_nonneg_right (by positivity)

/-- The product fderiv(flux_i)(v) * log(f(v)) is integrable for the Coulomb kernel.
    Uses Schwartz decay of the flux derivative and polynomial growth of log(f). -/
lemma coulomb_ibp_df_g_integrable
    (f : (Fin 3 → ℝ) → ℝ) (hf_pos : ∀ v, 0 < f v) (hf_smooth : ContDiff ℝ 3 f)
    (hf_schwartz : ∀ (N : ℕ) {k : ℕ}, k ≤ 2 →
      ∃ C > 0, ∀ v, ‖iteratedFDeriv ℝ k f v‖ * (1 + ‖v‖) ^ N ≤ C)
    (hLogBound : ∃ C K, ∀ v, |Real.log (f v)| ≤ C * (1 + ‖v‖) ^ K)
    (i : Fin 3) :
    Integrable (fun v =>
      fderiv ℝ (fun v' => (∫ w, mulVec (landauMatrix coulombKernel (v' - w))
        (f w • vGrad f v' - f v' • vGrad f w)) i) v (Pi.single i 1) *
      (Real.log ∘ f) v) := by
  obtain ⟨C_log, K_log, hLB⟩ := hLogBound
  -- Flux derivative Schwartz decay: ‖fderiv(flux_i)(v)‖ * (1+‖v‖)^(K_log+4) ≤ C_fd
  obtain ⟨C_fd, hC_fd, hfd_bound⟩ := coulomb_flux_deriv_schwartz_decay f hf_pos hf_smooth
    hf_schwartz i (K_log + 4)
  -- Apply domination by C_fd * C_log / (1+‖v‖)^4
  apply (inverse_poly_integrable (C_fd * C_log)).mono'
  · apply AEStronglyMeasurable.mul
    · exact aestronglyMeasurable_fderiv_apply
        (coulomb_flux_differentiable f hf_pos hf_smooth hf_schwartz i) _
    · exact (hf_smooth.continuous.log (fun v => ne_of_gt (hf_pos v))).aestronglyMeasurable
  · filter_upwards with v
    rw [Real.norm_eq_abs, abs_mul, Function.comp_apply]
    have hv_pos : (0 : ℝ) < (1 + ‖v‖) ^ 4 := by positivity
    rw [le_div_iff₀ hv_pos]
    -- |fderiv(flux)(v)(e_i)| ≤ ‖fderiv(flux)(v)‖ ≤ C_fd / (1+‖v‖)^(K_log+4)
    have h1 : |fderiv ℝ (fun v' => (∫ w, mulVec (landauMatrix coulombKernel (v' - w))
        (f w • vGrad f v' - f v' • vGrad f w)) i) v (Pi.single i 1)| ≤
        C_fd / (1 + ‖v‖) ^ (K_log + 4) := by
      have hv_pos' : (0 : ℝ) < (1 + ‖v‖) ^ (K_log + 4) := by positivity
      rw [le_div_iff₀ hv_pos']
      have h_abs_le : |fderiv ℝ (fun v' => (∫ w, mulVec (landauMatrix coulombKernel (v' - w))
          (f w • vGrad f v' - f v' • vGrad f w)) i) v (Pi.single i 1)| ≤
          ‖fderiv ℝ (fun v' => (∫ w, mulVec (landauMatrix coulombKernel (v' - w))
          (f w • vGrad f v' - f v' • vGrad f w)) i) v‖ := by
        have h_le := ContinuousLinearMap.le_opNorm (fderiv ℝ (fun v' => (∫ w,
          mulVec (landauMatrix coulombKernel (v' - w))
          (f w • vGrad f v' - f v' • vGrad f w)) i) v) (Pi.single i (1 : ℝ))
        rw [Pi.norm_single, norm_one, mul_one] at h_le
        rwa [Real.norm_eq_abs] at h_le
      calc |fderiv ℝ _ v (Pi.single i 1)| * (1 + ‖v‖) ^ (K_log + 4)
          ≤ ‖fderiv ℝ _ v‖ * (1 + ‖v‖) ^ (K_log + 4) := by gcongr
        _ ≤ C_fd := hfd_bound v
    -- Combine: |deriv| * |log f| * P^4 ≤ (C_fd/P^(K+4)) * (C_log*P^K) * P^4 = C_fd*C_log
    have hP : (0 : ℝ) < 1 + ‖v‖ := by linarith [norm_nonneg v]
    have h2 : |Real.log (f v)| ≤ C_log * (1 + ‖v‖) ^ K_log := hLB v
    calc |fderiv ℝ _ v (Pi.single i 1)| * |Real.log (f v)| * (1 + ‖v‖) ^ 4
        ≤ (C_fd / (1 + ‖v‖) ^ (K_log + 4)) * (C_log * (1 + ‖v‖) ^ K_log) * (1 + ‖v‖) ^ 4 := by
          gcongr
      _ = C_fd * C_log := by
          have hPne : (1 + ‖v‖) ^ (K_log + 4) ≠ 0 := ne_of_gt (by positivity)
          rw [pow_add] at hPne ⊢
          field_simp

end VML
