/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wiygul
-/
module


/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
public import Mathlib.Tactic
public import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Periodization
public import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Mollifier
public import LeanPool.NashEmbedding.NashEmbedding.Sobolev.PositionSpace
public import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Inequalities
public import LeanPool.NashEmbedding.NashEmbedding.Torus.Basic

/-!
# NashEmbedding: Theorem A (convex-combination approximation)

Wassermann's Theorem A: smooth realizable metrics are dense in the
space of all smooth metrics on the flat torus, in every Sobolev
norm $H^s$ with $2s > n$.

Convex-combination approximation form: given a smooth metric $g$, an
exponent $s$ with $2s > n$, and a tolerance $\eta > 0$, there exist a
grid resolution $M$, non-negative smooth periodic scalar functions
$f_k$ indexed by $k \in (\Z/M\Z)^n$, and constant positive
semi-definite matrices $B_k$ such that the matrix-valued sum
$\sum_k f_k \cdot B_k$ approximates $g$ to within $\eta^2$ in the
entrywise sum of $H^s$ semi-norms.

Proof assembles the position-space analytic toolkit
(`NashEmbedding.Sobolev.Periodization`, `Mollifier`, `PositionSpace`,
`Inequalities`) together with the two convergence theorems
`NashEmbedding.Sobolev.Convolution.mollifier_convergence` and
`NashEmbedding.Sobolev.RiemannSum.riemannSum_convergence`.

The local helper `perEntry_residual_bound` packages the quasi-triangle
bound applied per entry (combining Bridge Lemma 2, Fourier inversion,
real-imaginary decomposition of `periodicExtension`, linearity of
`integrationEmbed`, and `sobolevNormSqDistrib_triangle`).
-/

@[expose] public section

open scoped BigOperators ContDiff
open Complex Real NashEmbedding.Sobolev MeasureTheory Matrix

noncomputable
section

namespace NashEmbedding

variable {n : ℕ}

/-! ## Local helper: per-entry quasi-triangle bound -/

/-- Per-entry quasi-triangle bound for the convex-combination assembly.
    Given a kernel `φ ∈ C^∞_c(ℝⁿ; ℂ)` with cube support and a smooth
    `2πℤⁿ`-periodic real-valued `g`, the `H^s` semi-norm of the residual
    `(δⁿ · ∑_k (φ^per(x - z_k)).re · g(z_k) - g(x) : ℂ)` is at most twice
    the Riemann-vs-convolution discrepancy plus twice the
    convolution-vs-target discrepancy. Internally combines
    `riemann_positionSpace` (Bridge Lemma 2), Fourier inversion for
    smooth periodic functions, the real-imaginary decomposition of
    `periodicExtension` of a real-valued function, linearity of
    `integrationEmbed`, and `sobolevNormSqDistrib_triangle`. -/
private lemma perEntry_residual_bound
    (hn : 0 < n) {s : ℝ} (hs : (n : ℝ) < 2 * s)
    {φ : (Fin n → ℝ) → ℂ}
    (hφ_sm : ContDiff ℝ ∞ φ) (hφ_supp : HasCompactSupport φ)
    (hφ_cube : ∀ x, φ x ≠ 0 → ∀ j : Fin n, |x j| < Real.pi)
    (hφ_im : ∀ x, (φ x).im = 0)
    {g : (Fin n → ℝ) → ℝ} (hg_sm : ContDiff ℝ ∞ g) (hg_per : IsPeriodic2Pi g)
    {M : ℕ} :
    sobolevNormSqDistrib n s
      (integrationEmbed n (fun x : (Fin n → ℝ) =>
        (((2 * Real.pi / (M : ℝ)) ^ n
            * ∑ k : Fin n → Fin M,
                (periodicExtension n φ
                  (fun j => x j - meshPoint n M k j)).re
                * g (meshPoint n M k) - g x : ℝ) : ℂ)))
      ≤ 2 * sobolevNormSqDistrib n s
          (riemannSumDistrib n φ
              (integrationEmbed n (fun y => (g y : ℂ))) M
            - convDistrib n φ
                (integrationEmbed n (fun y => (g y : ℂ))))
      + 2 * sobolevNormSqDistrib n s
          (convDistrib n φ
              (integrationEmbed n (fun y => (g y : ℂ)))
            - integrationEmbed n (fun y => (g y : ℂ))) := by
  -- Setup: smooth periodic complexified g, in H^s.
  have hgC_sm : ContDiff ℝ ∞ (fun y : (Fin n → ℝ) => (g y : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hg_sm
  have hgC_per : IsPeriodic2Pi (fun y : (Fin n → ℝ) => (g y : ℂ)) := by
    intro x k
    change ((g (x + periodicShift n k) : ℝ) : ℂ) = ((g x : ℝ) : ℂ)
    rw [hg_per x k]
  have hgC_memSob : MemSobolevDistrib n s (integrationEmbed n (fun y : (Fin n → ℝ) => (g y : ℂ))) :=
    smooth_periodic_memSobolevDistrib hn hgC_sm hgC_per s
  have hφ_int : Integrable φ :=
    hφ_sm.continuous.integrable_of_hasCompactSupport hφ_supp
  have hφ_rd : FTRapidDecay n φ := cinfty_rapidDecay hn hφ_sm hφ_supp
  -- Step 1: pointwise equality `positionSpaceRiemann = (convex-combo : ℂ)`.
  have h_pe_im : ∀ y, (periodicExtension n φ y).im = 0 :=
    periodicExtension_im_zero hφ_im
  have h_fs_mesh : ∀ k : Fin n → Fin M,
      fourierSynthesis n
        (fourierCoeffDistrib (integrationEmbed n (fun y : (Fin n → ℝ) => (g y : ℂ))))
        (meshPoint n M k)
      = ((g (meshPoint n M k) : ℝ) : ℂ) := by
    intro k
    rw [fourierCoeffDistrib_integrationEmbed]
    exact fourierSynthesis_stdFourierCoeff_of_smoothPeriodic hn hgC_sm hgC_per _
  have h_psr_pt : ∀ x : (Fin n → ℝ),
      positionSpaceRiemann n φ
        (integrationEmbed n (fun y : (Fin n → ℝ) => (g y : ℂ))) M x
        = (((2 * Real.pi / (M : ℝ)) ^ n
            * ∑ k : Fin n → Fin M,
                (periodicExtension n φ (fun j => x j - meshPoint n M k j)).re
                * g (meshPoint n M k) : ℝ) : ℂ) := by
    intro x
    unfold positionSpaceRiemann
    simp only [h_fs_mesh]
    push_cast
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    have h_eq : periodicExtension n φ (fun j => x j - meshPoint n M k j)
        = ((periodicExtension n φ (fun j => x j - meshPoint n M k j)).re : ℂ) := by
      apply Complex.ext
      · simp
      · rw [Complex.ofReal_im]; exact h_pe_im _
    rw [h_eq]
    simp only [Complex.ofReal_re]
  -- Step 2: integrationEmbed equality.
  have h_iE_eq :
      integrationEmbed n
        (positionSpaceRiemann n φ
          (integrationEmbed n (fun y : (Fin n → ℝ) => (g y : ℂ))) M)
      = integrationEmbed n (fun x : (Fin n → ℝ) =>
          (((2 * Real.pi / (M : ℝ)) ^ n
            * ∑ k : Fin n → Fin M,
                (periodicExtension n φ (fun j => x j - meshPoint n M k j)).re
                * g (meshPoint n M k) : ℝ) : ℂ)) := by
    congr 1
    funext x
    exact h_psr_pt x
  -- Step 3: Bridge Lemma 2 gives R = integrationEmbed (positionSpaceRiemann).
  have hBridge := riemann_positionSpace hφ_sm hφ_supp hφ_cube
    (integrationEmbed n (fun y : (Fin n → ℝ) => (g y : ℂ))) M
  -- Combined: R = integrationEmbed (convex_combo_cast).
  have h_R_eq :
      riemannSumDistrib n φ (integrationEmbed n (fun y : (Fin n → ℝ) => (g y : ℂ))) M
        = integrationEmbed n (fun x : (Fin n → ℝ) =>
            (((2 * Real.pi / (M : ℝ)) ^ n
              * ∑ k : Fin n → Fin M,
                  (periodicExtension n φ (fun j => x j - meshPoint n M k j)).re
                  * g (meshPoint n M k) : ℝ) : ℂ)) := by
    rw [hBridge, h_iE_eq]
  -- Step 4: A = R - C via linearity of integrationEmbed.
  have h_LHS_split : (fun x : (Fin n → ℝ) =>
        (((2 * Real.pi / (M : ℝ)) ^ n
            * ∑ k : Fin n → Fin M,
                (periodicExtension n φ (fun j => x j - meshPoint n M k j)).re
                * g (meshPoint n M k) - g x : ℝ) : ℂ))
      = (fun x : (Fin n → ℝ) =>
          (((2 * Real.pi / (M : ℝ)) ^ n
            * ∑ k : Fin n → Fin M,
                (periodicExtension n φ (fun j => x j - meshPoint n M k j)).re
                * g (meshPoint n M k) : ℝ) : ℂ) - ((g x : ℝ) : ℂ)) := by
    funext x; push_cast; ring
  -- Continuity of the two split operands, required by `integrationEmbed_sub`
  -- (its `integral_add`/`integral_sub` step demands integrability of each
  -- integrand on the compact period cube).
  have h_pe_contDiff : ContDiff ℝ ∞ (periodicExtension n φ) :=
    periodicExtension_contDiff hφ_sm hφ_supp
  have h_convex_combo_cts : Continuous (fun x : (Fin n → ℝ) =>
      (((2 * Real.pi / (M : ℝ)) ^ n
          * ∑ k : Fin n → Fin M,
              (periodicExtension n φ (fun j => x j - meshPoint n M k j)).re
              * g (meshPoint n M k) : ℝ) : ℂ)) := by
    refine Complex.ofRealCLM.continuous.comp ?_
    refine continuous_const.mul ?_
    apply continuous_finsetSum
    intro k _
    refine Continuous.mul ?_ continuous_const
    refine Complex.reCLM.continuous.comp ?_
    refine h_pe_contDiff.continuous.comp ?_
    exact continuous_pi (fun j => (continuous_apply j).sub continuous_const)
  have h_gC_cts : Continuous (fun x : (Fin n → ℝ) => ((g x : ℝ) : ℂ)) :=
    hgC_sm.continuous
  rw [h_LHS_split, integrationEmbed_sub h_convex_combo_cts h_gC_cts, ← h_R_eq]
  -- Step 5: apply quasi-triangle with midpoint convDistrib.
  have hR_memSob :
      MemSobolevDistrib n s
        (riemannSumDistrib n φ (integrationEmbed n (fun y : (Fin n → ℝ) => (g y : ℂ))) M) :=
    riemannSumDistrib_memSobolevDistrib hφ_rd hn hs hgC_memSob M
  have hB_memSob :
      MemSobolevDistrib n s
        (convDistrib n φ (integrationEmbed n (fun y : (Fin n → ℝ) => (g y : ℂ)))) :=
    convDistrib_memSobolevDistrib hφ_int hgC_memSob
  exact sobolevNormSqDistrib_triangle s _ _ _
    (hR_memSob.sub hB_memSob) (hB_memSob.sub hgC_memSob)

/-! ## Theorem A: convex-combination approximation -/

/-- One mollifier scale controls every complexified metric entry. -/
private theorem metric_mollifier_uniform_error {s ηSq : ℝ}
    {ψc : (Fin n → ℝ) → ℂ} (hψc_int : Integrable ψc) (hψc_ft0 : ftRn n ψc 0 = 1)
    {gC : Fin n → Fin n → (Fin n → ℝ) → ℂ}
    (hgC_memSob : ∀ i j, MemSobolevDistrib n s (integrationEmbed n (gC i j)))
    (hηSq_pos : 0 < ηSq) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ∀ i j : Fin n,
        sobolevNormSqDistrib n s
          (convDistrib n (rescale n ψc ε) (integrationEmbed n (gC i j))
            - integrationEmbed n (gC i j)) < ηSq := by
  have h_each : ∀ (ij : Fin n × Fin n),
      ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        sobolevNormSqDistrib n s
          (convDistrib n (rescale n ψc ε) (integrationEmbed n (gC ij.1 ij.2))
            - integrationEmbed n (gC ij.1 ij.2)) < ηSq := by
    rintro ⟨i, j⟩
    have h := mollifier_convergence ψc hψc_int (hu := hgC_memSob i j) (s := s)
    have h' : Filter.Tendsto
        (fun ε => sobolevNormSqDistrib n s
          (convDistrib n (rescale n ψc ε) (integrationEmbed n (gC i j))
            - integrationEmbed n (gC i j)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      convert h using 2 with ε
      rw [hψc_ft0, one_smul]
    exact h'.eventually_lt_const hηSq_pos
  have h_all : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ (ij : Fin n × Fin n),
        sobolevNormSqDistrib n s
          (convDistrib n (rescale n ψc ε) (integrationEmbed n (gC ij.1 ij.2))
            - integrationEmbed n (gC ij.1 ij.2)) < ηSq :=
    Filter.eventually_all.mpr h_each
  obtain ⟨δ, hδ_pos, hδ⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp h_all
  refine ⟨min (δ / 2) 1, ?_, ?_, ?_⟩
  · exact lt_min (by linarith) (by norm_num)
  · exact min_le_right _ _
  · intro i j
    exact hδ ⟨lt_min (by linarith) (by norm_num),
              lt_of_le_of_lt (min_le_left _ _) (by linarith)⟩ ⟨i, j⟩

/-- **Theorem A (convex-combination approximation).** -/
theorem convex_combination_approx (hn : 0 < n)
    {g : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ}
    (hg : IsSmoothMetric g) {s : ℝ} (hs : (n : ℝ) < 2 * s) {η : ℝ} (hη : 0 < η) :
    ∃ (M : ℕ) (_ : 0 < M)
      (f : (Fin n → Fin M) → ((Fin n → ℝ) → ℝ))
      (B : (Fin n → Fin M) → Matrix (Fin n) (Fin n) ℝ),
      (∀ k, SmoothPeriodic (f k)) ∧
      (∀ k x, 0 ≤ f k x) ∧
      (∀ k, (B k).PosSemidef) ∧
      (∀ i j : Fin n, MemSobolevDistrib n s
          (integrationEmbed n
            (fun x => (((∑ k : Fin n → Fin M, f k x * B k i j) - g x i j : ℝ) : ℂ)))) ∧
      ∑ i : Fin n, ∑ j : Fin n,
        sobolevNormSqDistrib n s
          (integrationEmbed n
            (fun x => (((∑ k : Fin n → Fin M, f k x * B k i j) - g x i j : ℝ) : ℂ)))
        < η ^ 2 := by
  -- ──── Step 1: extract a mollifier ψ : ℝⁿ → ℝ via `mollifier_exists`. ────
  obtain ⟨ψ, hψ_smooth, hψ_supp, hψ_int, hψ_nn, hψ_cube, hψ_unit⟩ :=
    mollifier_exists (n := n)
  let ψc : (Fin n → ℝ) → ℂ := fun x => (ψ x : ℂ)
  have hψc_smooth : ContDiff ℝ ∞ ψc :=
    Complex.ofRealCLM.contDiff.comp hψ_smooth
  have hψc_supp : HasCompactSupport ψc :=
    hψ_supp.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hψc_int : Integrable ψc :=
    hψc_smooth.continuous.integrable_of_hasCompactSupport hψc_supp
  have hψc_cube : ∀ x, ψc x ≠ 0 → ∀ j : Fin n, |x j| < Real.pi := by
    intro x hx j; apply hψ_cube; intro h0; apply hx; simp [ψc, h0]
  have hψc_ft0 : ftRn n ψc 0 = 1 := by
    rw [ftRn_at_zero]
    change ∫ y, ((ψ y : ℝ) : ℂ) = 1
    rw [integral_complex_ofReal, hψ_unit]
    simp
  -- ──── Step 2: complexified entries of g lie in H^s_* via
  -- `smooth_periodic_memSobolevDistrib`. ────
  let gC : Fin n → Fin n → (Fin n → ℝ) → ℂ :=
    fun i j x => ((g x i j : ℝ) : ℂ)
  have hgC_smooth : ∀ i j, ContDiff ℝ ∞ (gC i j) := by
    intro i j
    have h_entry : ContDiff ℝ ∞ (fun x : (Fin n → ℝ) => g x i j) :=
      ((contDiff_apply ℝ ℝ j).comp
        ((contDiff_apply ℝ (Fin n → ℝ) i).comp hg.smoothPeriodic.smooth))
    exact Complex.ofRealCLM.contDiff.comp h_entry
  have hgC_periodic : ∀ i j, IsPeriodic2Pi (gC i j) := by
    intro i j x k
    have := hg.smoothPeriodic.periodic x k
    simp [gC, this]
  have hgC_memSob : ∀ i j, MemSobolevDistrib n s (integrationEmbed n (gC i j)) :=
    fun i j =>
      smooth_periodic_memSobolevDistrib hn (hgC_smooth i j) (hgC_periodic i j) s
  -- ──── Step 3: per-entry tolerance ηSq := η² / (4 n²). ────
  let nR : ℝ := (n : ℝ)
  have hnR_pos : 0 < nR := Nat.cast_pos.mpr hn
  let ηSq : ℝ := η ^ 2 / (4 * nR ^ 2)
  have hηSq_pos : 0 < ηSq :=
    div_pos (pow_pos hη 2) (by positivity)
  -- ──── Step 4: choose ε > 0 via `mollifier_convergence` + finite intersection. ────
  have h_ε := metric_mollifier_uniform_error hψc_int hψc_ft0 hgC_memSob hηSq_pos
  obtain ⟨ε, hε_pos, hε_le_one, hε_bound⟩ := h_ε
  -- ──── Step 5: properties of ψc_ε := rescale n ψc ε (via `rescale_contDiff`,
  -- `rescale_hasCompactSupport`, `rescale_support_in_cube`). ────
  let ψc_ε : (Fin n → ℝ) → ℂ := rescale n ψc ε
  have hψc_ε_smooth : ContDiff ℝ ∞ ψc_ε :=
    rescale_contDiff hψc_smooth ε
  have hψc_ε_supp : HasCompactSupport ψc_ε :=
    rescale_hasCompactSupport hψc_supp hε_pos
  have hψc_ε_cube : ∀ x, ψc_ε x ≠ 0 → ∀ j : Fin n, |x j| < Real.pi :=
    rescale_support_in_cube hψc_cube hε_pos hε_le_one
  -- `ψc_ε` is the complex cast of a real-valued function, made explicit:
  have h_ψc_ε_eq : ∀ z, ψc_ε z = ((ε⁻¹ ^ n * ψ (ε⁻¹ • z) : ℝ) : ℂ) := by
    intro z
    change rescale n ψc ε z = _
    unfold rescale
    change (((ε⁻¹ ^ n : ℝ) : ℂ) * ((ψ (ε⁻¹ • z) : ℝ) : ℂ)) = _
    push_cast; ring
  have hψc_ε_re_nn : ∀ x, 0 ≤ (ψc_ε x).re := fun z => by
    rw [h_ψc_ε_eq z, Complex.ofReal_re]
    exact mul_nonneg (by positivity) (hψ_nn _)
  have hψc_ε_im : ∀ x, (ψc_ε x).im = 0 := fun z => by
    rw [h_ψc_ε_eq z, Complex.ofReal_im]
  have hψc_ε_rd : FTRapidDecay n ψc_ε :=
    cinfty_rapidDecay hn hψc_ε_smooth hψc_ε_supp
  -- ──── Step 6: choose M via `riemannSum_convergence` + finite intersection. ────
  have h_M : ∃ M : ℕ, 0 < M ∧
      ∀ i j : Fin n,
        sobolevNormSqDistrib n s
          (riemannSumDistrib n ψc_ε (integrationEmbed n (gC i j)) M
            - convDistrib n ψc_ε (integrationEmbed n (gC i j))) < ηSq := by
    have h_each : ∀ (ij : Fin n × Fin n), ∀ᶠ M : ℕ in Filter.atTop,
        sobolevNormSqDistrib n s
          (riemannSumDistrib n ψc_ε (integrationEmbed n (gC ij.1 ij.2)) M
            - convDistrib n ψc_ε (integrationEmbed n (gC ij.1 ij.2))) < ηSq := by
      rintro ⟨i, j⟩
      exact (riemannSum_convergence ψc_ε hψc_ε_rd hn hs
        (hu := hgC_memSob i j)).eventually_lt_const hηSq_pos
    have h_all : ∀ᶠ M : ℕ in Filter.atTop, ∀ (ij : Fin n × Fin n),
        sobolevNormSqDistrib n s
          (riemannSumDistrib n ψc_ε (integrationEmbed n (gC ij.1 ij.2)) M
            - convDistrib n ψc_ε (integrationEmbed n (gC ij.1 ij.2))) < ηSq :=
      Filter.eventually_all.mpr h_each
    rw [Filter.eventually_atTop] at h_all
    obtain ⟨N, hN⟩ := h_all
    refine ⟨max N 1, ?_, ?_⟩
    · exact lt_of_lt_of_le Nat.one_pos (le_max_right _ _)
    · intro i j
      exact hN _ (le_max_left _ _) ⟨i, j⟩
  obtain ⟨M, hM_pos, hM_bound⟩ := h_M
  -- ──── Step 7: define f_k and B_k. ────
  let f : (Fin n → Fin M) → ((Fin n → ℝ) → ℝ) := convexComboScalar n ψc_ε M
  let B : (Fin n → Fin M) → Matrix (Fin n) (Fin n) ℝ := fun k => g (meshPoint n M k)
  have h_f_smooth : ∀ k, ContDiff ℝ ∞ (f k) :=
    fun k => convexComboScalar_contDiff hψc_ε_smooth hψc_ε_supp M k
  have h_f_periodic : ∀ k, IsPeriodic2Pi (f k) :=
    fun k => convexComboScalar_isPeriodic2Pi ψc_ε M k
  have h_f_nn : ∀ k x, 0 ≤ f k x :=
    fun k x => convexComboScalar_nonneg hψc_ε_re_nn hM_pos k x
  -- ──── Step 8: package the witnesses. ────
  refine ⟨M, hM_pos, f, B, ?_, ?_, ?_, ?_, ?_⟩
  -- (1) f k smooth periodic.
  · exact fun k => ⟨h_f_smooth k, h_f_periodic k⟩
  -- (2) f k ≥ 0.
  · exact h_f_nn
  -- (3) B k = g (meshPoint k) is PSD by hg.
  · intro k
    exact hg.posSemidef _
  -- (4) Entrywise residual ∈ MemSobolevDistrib via smooth_periodic_memSobolevDistrib.
  · intro i j
    apply smooth_periodic_memSobolevDistrib hn
    · have h_g_entry : ContDiff ℝ ∞ (fun x : (Fin n → ℝ) => g x i j) :=
        ((contDiff_apply ℝ ℝ j).comp
          ((contDiff_apply ℝ (Fin n → ℝ) i).comp hg.smoothPeriodic.smooth))
      have h_sum : ContDiff ℝ ∞
          (fun x : (Fin n → ℝ) => ∑ k : Fin n → Fin M, f k x * B k i j) := by
        apply ContDiff.sum
        intro k _
        exact (h_f_smooth k).mul contDiff_const
      exact Complex.ofRealCLM.contDiff.comp (h_sum.sub h_g_entry)
    · intro x kk
      change (((∑ k : Fin n → Fin M, f k (x + periodicShift n kk) * B k i j)
              - g (x + periodicShift n kk) i j : ℝ) : ℂ)
        = (((∑ k : Fin n → Fin M, f k x * B k i j) - g x i j : ℝ) : ℂ)
      congr 1
      have h_g_per : g (x + periodicShift n kk) i j = g x i j := by
        rw [hg.smoothPeriodic.periodic x kk]
      have h_sum_per : (∑ k : Fin n → Fin M, f k (x + periodicShift n kk) * B k i j)
          = (∑ k : Fin n → Fin M, f k x * B k i j) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [h_f_periodic k x kk]
      rw [h_sum_per, h_g_per]
  -- (5) The sum bound: Bridge 2 + quasi-triangle assembly.
  · have h_per : ∀ i j : Fin n,
        sobolevNormSqDistrib n s
          (integrationEmbed n
            (fun x => (((∑ k : Fin n → Fin M, f k x * B k i j) - g x i j : ℝ) : ℂ)))
          ≤ 2 * sobolevNormSqDistrib n s
              (riemannSumDistrib n ψc_ε (integrationEmbed n (gC i j)) M
                - convDistrib n ψc_ε (integrationEmbed n (gC i j)))
          + 2 * sobolevNormSqDistrib n s
              (convDistrib n ψc_ε (integrationEmbed n (gC i j))
                - integrationEmbed n (gC i j)) := by
      intro i j
      have hg_ij_smooth : ContDiff ℝ ∞ (fun x : (Fin n → ℝ) => g x i j) :=
        ((contDiff_apply ℝ ℝ j).comp
          ((contDiff_apply ℝ (Fin n → ℝ) i).comp hg.smoothPeriodic.smooth))
      have hg_ij_per : IsPeriodic2Pi (fun x : (Fin n → ℝ) => g x i j) := by
        intro x kk
        change g (x + periodicShift n kk) i j = g x i j
        rw [hg.smoothPeriodic.periodic x kk]
      have h_form : (fun x : (Fin n → ℝ) =>
            (((∑ k : Fin n → Fin M, f k x * B k i j) - g x i j : ℝ) : ℂ))
          = (fun x : (Fin n → ℝ) =>
            (((2 * Real.pi / (M : ℝ)) ^ n
                * ∑ k : Fin n → Fin M,
                    (periodicExtension n ψc_ε
                      (fun j => x j - meshPoint n M k j)).re
                    * g (meshPoint n M k) i j - g x i j : ℝ) : ℂ)) := by
        funext x
        congr 2
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        change convexComboScalar n ψc_ε M k x * g (meshPoint n M k) i j = _
        unfold convexComboScalar
        ring
      rw [h_form]
      exact perEntry_residual_bound hn hs hψc_ε_smooth hψc_ε_supp hψc_ε_cube
        hψc_ε_im hg_ij_smooth hg_ij_per
    have h_per_strict : ∀ i j : Fin n,
        sobolevNormSqDistrib n s
          (integrationEmbed n
            (fun x => (((∑ k : Fin n → Fin M, f k x * B k i j) - g x i j : ℝ) : ℂ)))
          < 4 * ηSq := by
      intro i j
      have hRie := hM_bound i j
      have hMol := hε_bound i j
      have := h_per i j
      linarith
    have h_univ_nonempty : (Finset.univ : Finset (Fin n)).Nonempty :=
      ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    have h_sum_strict :
        ∑ i : Fin n, ∑ j : Fin n,
          sobolevNormSqDistrib n s
            (integrationEmbed n
              (fun x => (((∑ k : Fin n → Fin M, f k x * B k i j) - g x i j : ℝ) : ℂ)))
          < ∑ i : Fin n, ∑ j : Fin n, (4 * ηSq) := by
      apply Finset.sum_lt_sum_of_nonempty h_univ_nonempty
      intro i _
      apply Finset.sum_lt_sum_of_nonempty h_univ_nonempty
      intro j _
      exact h_per_strict i j
    have h_sum_eq : (∑ i : Fin n, ∑ j : Fin n, (4 * ηSq : ℝ)) = η ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      change (n : ℝ) * ((n : ℝ) * (4 * (η ^ 2 / (4 * (n : ℝ) ^ 2)))) = η ^ 2
      have hnR_ne : (n : ℝ) ≠ 0 := ne_of_gt hnR_pos
      field_simp
    linarith

end NashEmbedding

end
