/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
import LeanPool.Malliavin.Malliavin.DualDerivative

/-!
# The chain rule in `𝔻₁,₂`

For `φ : ℝ → ℝ` of class `C¹` with bounded derivative and `F ∈ 𝔻₁,₂`, the composite `φ ∘ F`
belongs to `𝔻₁,₂` and

  `D_cl (φ ∘ F) = φ' (F) • D_cl F`  (`comp_mem_domD12`),

the `C¹` case of Nualart, *The Malliavin calculus and related topics*, Proposition 1.2.3.
The file also contains the product rule `D_cl (F G) = G • D_cl F + F • D G` for `F ∈ 𝔻₁,₂` and
smooth bounded `G` (`mul_mem_domD12`), the multivariate chain rule
`D_cl f(F₁, …, Fₙ) = ∑ᵢ ∂ᵢ f (F) • D_cl Fᵢ` (`comp_pi_mem_domD12`), the norm bounds
`‖D_cl (φ ∘ F)‖ ≤ K ‖D_cl F‖` and `‖D_cl f(F)‖ ≤ K ∑ᵢ ‖D_cl Fᵢ‖`, the bounded arctan truncations
`cutoff m ∘ F ∈ 𝔻₁,₂` (`cutoff_comp_mem_domD12`), the corresponding operations on the subtype
`D12 μ` (`D12.comp`, `D12.mulSmooth`, `D12.compPi`), and the time forms: the chain rules
`Dₜ φ (F) = φ' (F) Dₜ F` and `Dₜ f (F₁, …, Fₙ) = ∑ᵢ ∂ᵢ f (F) Dₜ Fᵢ`
(`timeDerivative_mderivClosure_comp`, `timeDerivative_mderivClosure_comp_pi`), the product rule
with a cylindrical factor (`timeDerivative_mderivClosure_mul_cylinder`), and the Wiener-integral
formulas `Dₜ φ (∫ g dB) = φ' (∫ g dB) g(t)`, `Dₜ f (∫ g₁ dB, …) = ∑ᵢ ∂ᵢ f (∫ g dB) gᵢ(t)`
(`timeDerivative_mderivClosure_comp_wienerIntegral`,
`timeDerivative_mderivClosure_comp_pi_wienerIntegral`).

## Proof

Pick smooth bounded cylindrical `Fₖ` with `Fₖ → F` and `D Fₖ → D_cl F` in `L²` (the definition of
the graph closure), and pass to a subsequence converging almost everywhere.  Each `φ ∘ Fₖ` is
smooth bounded with derivative `φ' (Fₖ) • D Fₖ` (`IsSmoothBounded.comp_of_deriv_le`,
`mderiv_comp`).  Since `φ` is `K`-Lipschitz, `φ ∘ Fₖ → φ ∘ F` in `L²`.  For the derivatives,
`‖φ' (Fₖ) • D Fₖ - φ' (Fₖ) • D_cl F‖ ≤ K ‖D Fₖ - D_cl F‖ → 0`, while
`φ' (Fₖ) • D_cl F → φ' (F) • D_cl F`
by dominated convergence (`tendsto_toLp_of_dominated`, bound `(2K)² ‖D_cl F‖²`) along the almost
everywhere convergent subsequence.  Closedness of the graph (`mem_domD12_of_tendsto`) concludes.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace

namespace Malliavin

section Chain

open CameronMartin

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]

variable {φ : ℝ → ℝ} {K : ℝ≥0}

omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  [IsGaussian μ] in
/-- The derivative of `φ ∘ F` is `φ' (F x) • F'(x)`. -/
theorem fderiv_comp_real {F : W → ℝ} {x : W} (hφ : DifferentiableAt ℝ φ (F x))
    (hF : DifferentiableAt ℝ F x) :
    fderiv ℝ (fun y ↦ φ (F y)) x = deriv φ (F x) • fderiv ℝ F x := by
  have hcomp : (fun y ↦ φ (F y)) = φ ∘ F := rfl
  rw [hcomp, fderiv_comp x hφ hF]
  ext v
  simp only [ContinuousLinearMap.comp_apply, fderiv_eq_smul_deriv, smul_eq_mul, mul_comm,
    smul_apply]

omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  [IsGaussian μ] in
/-- Post-composition with a `C¹` function of bounded derivative preserves smooth boundedness. -/
theorem IsSmoothBounded.comp_of_deriv_le (hφ : ContDiff ℝ 1 φ) (hK : ∀ x, ‖deriv φ x‖₊ ≤ K)
    {F : W → ℝ} (hF : IsSmoothBounded F) : IsSmoothBounded (fun x ↦ φ (F x)) where
  contDiff := hφ.comp hF.contDiff
  bounded := by
    obtain ⟨C, hC⟩ := hF.bounded
    have hlip := lipschitzWith_of_nnnorm_deriv_le (hφ.differentiable one_ne_zero) hK
    refine ⟨|φ 0| + K * C, fun x ↦ ?_⟩
    calc |φ (F x)| = |φ (F x) - φ 0 + φ 0| := by ring_nf
      _ ≤ |φ (F x) - φ 0| + |φ 0| := abs_add_le _ _
      _ ≤ K * |F x - 0| + |φ 0| := by
          gcongr
          simpa [Real.dist_eq] using hlip.dist_le_mul (F x) 0
      _ ≤ K * C + |φ 0| := by
          gcongr
          simpa using hC x
      _ = |φ 0| + K * C := by ring
  bounded_fderiv := by
    obtain ⟨C, hC⟩ := hF.bounded_fderiv
    refine ⟨K * C, fun x ↦ ?_⟩
    rw [fderiv_comp_real (hφ.differentiable one_ne_zero _) (hF.differentiable x), norm_smul]
    have h1 : ‖deriv φ (F x)‖ ≤ K := by exact_mod_cast hK (F x)
    have h0 : 0 ≤ C := (norm_nonneg _).trans (hC x)
    calc ‖deriv φ (F x)‖ * ‖fderiv ℝ F x‖ ≤ K * C :=
      mul_le_mul h1 (hC x) (norm_nonneg _) K.coe_nonneg

omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  [IsGaussian μ] in
theorem abs_le_of_deriv_le (hφ : ContDiff ℝ 1 φ) (hK : ∀ x, ‖deriv φ x‖₊ ≤ K) (x : ℝ) :
    |φ x| ≤ |φ 0| + K * |x| := by
  have hlip := lipschitzWith_of_nnnorm_deriv_le (hφ.differentiable one_ne_zero) hK
  have h := hlip.dist_le_mul x 0
  rw [Real.dist_eq, Real.dist_eq, sub_zero] at h
  calc |φ x| = |φ x - φ 0 + φ 0| := by rw [sub_add_cancel]
    _ ≤ |φ x - φ 0| + |φ 0| := abs_add_le _ _
    _ ≤ K * |x| + |φ 0| := add_le_add_left h _
    _ = |φ 0| + K * |x| := add_comm _ _

omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- `φ ∘ F` is square integrable for Lipschitz `φ` and `F ∈ L²`. -/
theorem memLp_comp_of_deriv_le (hφ : ContDiff ℝ 1 φ) (hK : ∀ x, ‖deriv φ x‖₊ ≤ K)
    (F : Lp ℝ 2 μ) : MemLp (fun x ↦ φ (F x)) 2 μ := by
  have h1 : MemLp (fun _ : W ↦ |φ 0|) 2 μ := memLp_const _
  have h2 : MemLp (fun x ↦ (K : ℝ) * ‖F x‖) 2 μ := (Lp.memLp F).norm.const_mul _
  refine MemLp.of_le (h1.add h2)
    (hφ.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable F))
    (Filter.Eventually.of_forall fun x ↦ ?_)
  have hb := abs_le_of_deriv_le hφ hK (F x)
  rw [← Real.norm_eq_abs (F x)] at hb
  have h0 : 0 ≤ |φ 0| + (K : ℝ) * ‖F x‖ := (abs_nonneg _).trans hb
  rw [Pi.add_apply, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0]
  exact hb

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- `φ' (F) • η` is square integrable for bounded `φ'` and `η ∈ L²(μ; H)`. -/
theorem memLp_deriv_smul_of_deriv_le' (hφ : ContDiff ℝ 1 φ) (hK : ∀ x, ‖deriv φ x‖₊ ≤ K)
    {G : W → ℝ} (hG : AEStronglyMeasurable G μ) (η : Lp (Space μ) 2 μ) :
    MemLp (fun x ↦ deriv φ (G x) • η x) 2 μ := by
  have hg : MemLp (fun x ↦ (K : ℝ) * ‖η x‖) 2 μ := (Lp.memLp η).norm.const_mul _
  refine MemLp.of_le hg ((hφ.continuous_deriv_one.comp_aestronglyMeasurable hG).smul
    (Lp.aestronglyMeasurable η)) (Filter.Eventually.of_forall fun x ↦ ?_)
  have h1 : ‖deriv φ (G x)‖ ≤ K := by exact_mod_cast hK (G x)
  have h0 : (0 : ℝ) ≤ K * ‖η x‖ := mul_nonneg K.coe_nonneg (norm_nonneg _)
  rw [norm_smul, Real.norm_eq_abs (K * ‖η x‖), abs_of_nonneg h0]
  exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- `φ' (F) • η` is square integrable for bounded `φ'` and `η ∈ L²(μ; H)`. -/
theorem memLp_deriv_smul_of_deriv_le (hφ : ContDiff ℝ 1 φ) (hK : ∀ x, ‖deriv φ x‖₊ ≤ K)
    (F : Lp ℝ 2 μ) (η : Lp (Space μ) 2 μ) :
    MemLp (fun x ↦ deriv φ (F x) • η x) 2 μ :=
  memLp_deriv_smul_of_deriv_le' μ hφ hK (Lp.aestronglyMeasurable F) η

/-- **Chain rule in `𝔻₁,₂`** (Nualart, Proposition 1.2.3, `C¹` case): for `φ` of class `C¹` with
bounded derivative and `F ∈ 𝔻₁,₂`, `φ ∘ F ∈ 𝔻₁,₂` with `D_cl (φ ∘ F) = φ' (F) • D_cl F`. -/
theorem comp_mem_domD12 (hφ : ContDiff ℝ 1 φ) (hK : ∀ x, ‖deriv φ x‖₊ ≤ K)
    {F : Lp ℝ 2 μ} (hF : F ∈ domD12 μ) :
    (memLp_comp_of_deriv_le μ hφ hK F).toLp _ ∈ domD12 μ ∧
      mderivClosure μ ((memLp_comp_of_deriv_le μ hφ hK F).toLp _) =
        (memLp_deriv_smul_of_deriv_le μ hφ hK F (mderivClosure μ F)).toLp _ := by
  obtain ⟨η, hcl⟩ := hF
  have hη : mderivClosure μ F = η := mderivClosure_eq μ hcl
  obtain ⟨Fk, hFk, hDk⟩ := hcl
  have hlip := lipschitzWith_of_nnnorm_deriv_le (hφ.differentiable one_ne_zero) hK
  -- a subsequence converging almost everywhere
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hFk).exists_seq_tendsto_ae
  have hae' : ∀ᵐ x ∂μ, Tendsto (fun i ↦ (Fk (ns i)).1 x) atTop (𝓝 (F x)) := by
    have h := ae_all_iff.2 fun i ↦ MemLp.coeFn_toLp ((Fk (ns i)).2.memLp μ 2)
    filter_upwards [hae, h] with x hx hx'
    exact hx.congr fun i ↦ hx' i
  have hFk' : Tendsto (fun i ↦ (Fk (ns i)).2.toLp μ) atTop (𝓝 F) := hFk.comp hns.tendsto_atTop
  have hDk' : Tendsto (fun i ↦ (Fk (ns i)).2.mderivLp μ) atTop (𝓝 η) := hDk.comp hns.tendsto_atTop
  rw [hη]
  refine mem_domD12_of_tendsto μ
    (F := fun i ↦ ((Fk (ns i)).2.comp_of_deriv_le hφ hK).toLp μ)
    (fun i ↦ IsSmoothBounded.toLp_mem_domD12 μ _) ?_ ?_
  · -- convergence of the values: Lipschitz
    simp only [IsSmoothBounded.toLp] at hFk' ⊢
    rw [tendsto_iff_norm_sub_tendsto_zero]
    rw [tendsto_iff_norm_sub_tendsto_zero] at hFk'
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun i ↦ ?_)
      (by simpa using hFk'.const_mul (K : ℝ))
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [Lp.coeFn_sub ((((Fk (ns i)).2.comp_of_deriv_le hφ hK).memLp μ 2).toLp _)
        ((memLp_comp_of_deriv_le μ hφ hK F).toLp _),
      Lp.coeFn_sub (((Fk (ns i)).2.memLp μ 2).toLp _) F,
      MemLp.coeFn_toLp (((Fk (ns i)).2.comp_of_deriv_le hφ hK).memLp μ 2),
      MemLp.coeFn_toLp (memLp_comp_of_deriv_le μ hφ hK F),
      MemLp.coeFn_toLp ((Fk (ns i)).2.memLp μ 2)] with x h1 h2 h3 h4 h5
    rw [h1, h2, Pi.sub_apply, Pi.sub_apply, h3, h4, h5]
    simpa [Real.dist_eq] using hlip.dist_le_mul ((Fk (ns i)).1 x) (F x)
  · -- convergence of the derivatives
    simp_rw [mderivClosure_toLp]
    set target := (memLp_deriv_smul_of_deriv_le μ hφ hK F η).toLp _ with htarget
    -- the intermediate classes `φ' (Fᵢ) • η`
    have hM : ∀ i, MemLp (fun x ↦ deriv φ ((Fk (ns i)).1 x) • η x) 2 μ := fun i ↦
      memLp_deriv_smul_of_deriv_le' μ hφ hK (Fk (ns i)).2.continuous.aestronglyMeasurable η
    -- `φ' (Fᵢ) • η → φ' (F) • η` by dominated convergence
    have hMt : Tendsto (fun i ↦ (hM i).toLp _) atTop (𝓝 target) := by
      refine tendsto_toLp_of_dominated hM (memLp_deriv_smul_of_deriv_le μ hφ hK F η)
        (bound := fun x ↦ (2 * K) ^ 2 * ‖η x‖ ^ 2)
        (((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable η)).mp
          (Lp.memLp η)).const_mul _) (fun i ↦ Filter.Eventually.of_forall fun x ↦ ?_) ?_
      · rw [← sub_smul, norm_smul, mul_pow, Real.norm_eq_abs]
        gcongr
        have h1 : |deriv φ ((Fk (ns i)).1 x)| ≤ K := by
          rw [← Real.norm_eq_abs]; exact_mod_cast hK _
        have h2 : |deriv φ (F x)| ≤ K := by
          rw [← Real.norm_eq_abs]; exact_mod_cast hK _
        calc |deriv φ ((Fk (ns i)).1 x) - deriv φ (F x)|
            ≤ |deriv φ ((Fk (ns i)).1 x)| + |deriv φ (F x)| := abs_sub _ _
          _ ≤ K + K := add_le_add h1 h2
          _ = 2 * K := by ring
      · filter_upwards [hae'] with x hx
        exact ((hφ.continuous_deriv_one.tendsto _).comp hx).smul_const _
    -- `‖D(φ ∘ Fᵢ) - φ' (Fᵢ) • η‖ ≤ K ‖DFᵢ - η‖`
    have hA : ∀ i, ‖((Fk (ns i)).2.comp_of_deriv_le hφ hK).mderivLp μ - (hM i).toLp _‖ ≤
        K * ‖(Fk (ns i)).2.mderivLp μ - η‖ := by
      intro i
      refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
      filter_upwards [Lp.coeFn_sub (((Fk (ns i)).2.comp_of_deriv_le hφ hK).mderivLp μ)
          ((hM i).toLp _),
        Lp.coeFn_sub ((Fk (ns i)).2.mderivLp μ) η,
        MemLp.coeFn_toLp (((Fk (ns i)).2.comp_of_deriv_le hφ hK).memLp_mderiv μ 2),
        MemLp.coeFn_toLp (hM i),
        MemLp.coeFn_toLp ((Fk (ns i)).2.memLp_mderiv μ 2)] with x h1 h2 h3 h4 h5
      rw [h1, h2, Pi.sub_apply, Pi.sub_apply, IsSmoothBounded.mderivLp, h3, h4,
        IsSmoothBounded.mderivLp, h5,
        mderiv_comp μ (hφ.differentiable one_ne_zero _) ((Fk (ns i)).2.differentiable x),
        ← smul_sub, norm_smul, Real.norm_eq_abs]
      have h1' : |deriv φ ((Fk (ns i)).1 x)| ≤ K := by
        rw [← Real.norm_eq_abs]; exact_mod_cast hK _
      exact mul_le_mul_of_nonneg_right h1' (norm_nonneg _)
    rw [tendsto_iff_norm_sub_tendsto_zero]
    rw [tendsto_iff_norm_sub_tendsto_zero] at hDk' hMt
    refine squeeze_zero
      (fun i ↦ norm_nonneg (((Fk (ns i)).2.comp_of_deriv_le hφ hK).mderivLp μ - target))
      (fun i ↦ ?_) (by simpa using (hDk'.const_mul (K : ℝ)).add hMt)
    have htri : ‖((Fk (ns i)).2.comp_of_deriv_le hφ hK).mderivLp μ - target‖ ≤
        ‖((Fk (ns i)).2.comp_of_deriv_le hφ hK).mderivLp μ - (hM i).toLp _‖ +
          ‖(hM i).toLp _ - target‖ := by
      have := norm_add_le (((Fk (ns i)).2.comp_of_deriv_le hφ hK).mderivLp μ - (hM i).toLp _)
        ((hM i).toLp _ - target)
      rwa [sub_add_sub_cancel] at this
    exact htri.trans (add_le_add_left (hA i) _)

/-- The closed derivative of `φ ∘ F` is controlled by that of `F`: `‖D_cl (φ ∘ F)‖ ≤ K ‖D_cl F‖`. -/
theorem norm_mderivClosure_comp_le (hφ : ContDiff ℝ 1 φ) (hK : ∀ x, ‖deriv φ x‖₊ ≤ K)
    {F : Lp ℝ 2 μ} (hF : F ∈ domD12 μ) :
    ‖mderivClosure μ ((memLp_comp_of_deriv_le μ hφ hK F).toLp _)‖ ≤ K * ‖mderivClosure μ F‖ := by
  rw [(comp_mem_domD12 μ hφ hK hF).2]
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_deriv_smul_of_deriv_le μ hφ hK F (mderivClosure μ F))]
    with x hx
  rw [hx, norm_smul]
  have h1 : ‖deriv φ (F x)‖ ≤ K := by exact_mod_cast hK (F x)
  exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)

/-- `φ ∘ F` as an element of the submodule `D12 μ`. -/
noncomputable def D12.comp (hφ : ContDiff ℝ 1 φ) (hK : ∀ x, ‖deriv φ x‖₊ ≤ K) (F : D12 μ) :
    D12 μ :=
  ⟨(memLp_comp_of_deriv_le μ hφ hK F).toLp _, (comp_mem_domD12 μ hφ hK F.2).1⟩

theorem D12.coe_comp (hφ : ContDiff ℝ 1 φ) (hK : ∀ x, ‖deriv φ x‖₊ ≤ K) (F : D12 μ) :
    (D12.comp μ hφ hK F : Lp ℝ 2 μ) = (memLp_comp_of_deriv_le μ hφ hK F).toLp _ := rfl

/-- The chain rule for the subtype map `mderivD12`. -/
theorem mderivD12_comp (hφ : ContDiff ℝ 1 φ) (hK : ∀ x, ‖deriv φ x‖₊ ≤ K) (F : D12 μ) :
    mderivD12 μ (D12.comp μ hφ hK F) =
      (memLp_deriv_smul_of_deriv_le μ hφ hK F (mderivD12 μ F)).toLp _ :=
  (comp_mem_domD12 μ hφ hK F.2).2

/-- The arctan truncations `cutoff m` have derivative bounded by `1`. -/
theorem nnnorm_deriv_cutoff_le (m : ℕ) (x : ℝ) : ‖deriv (cutoff m) x‖₊ ≤ 1 := by
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_one]
  exact abs_deriv_cutoff_le m x

/-- **Bounded truncations stay in `𝔻₁,₂`**: `cutoff m ∘ F ∈ 𝔻₁,₂` for every `F ∈ 𝔻₁,₂`, with
derivative `cutoff m' (F) • D_cl F`; these are bounded by `(m + 1) π / 2`. -/
theorem cutoff_comp_mem_domD12 (m : ℕ) {F : Lp ℝ 2 μ} (hF : F ∈ domD12 μ) :
    (memLp_comp_of_deriv_le μ (cutoff_contDiff m) (nnnorm_deriv_cutoff_le m) F).toLp _ ∈
        domD12 μ ∧
      mderivClosure μ
          ((memLp_comp_of_deriv_le μ (cutoff_contDiff m) (nnnorm_deriv_cutoff_le m) F).toLp _) =
        (memLp_deriv_smul_of_deriv_le μ (cutoff_contDiff m) (nnnorm_deriv_cutoff_le m) F
          (mderivClosure μ F)).toLp _ :=
  comp_mem_domD12 μ (cutoff_contDiff m) (nnnorm_deriv_cutoff_le m) hF

end Chain

/-! ### The product rule

`𝔻₁,₂` is stable under multiplication by smooth bounded functionals, with the Leibniz rule
`D_cl (F G) = G • D_cl F + F • D G` (`mul_mem_domD12`): the approximating products `Fₖ G` converge
since `G` is bounded, and their derivatives `Fₖ • DG + G • DFₖ` converge since `G` and `DG` are
bounded. -/

section Product

open CameronMartin

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]

variable {G : W → ℝ}

omit [CompleteSpace W] [SecondCountableTopology W] [IsGaussian μ] in
/-- `F · G` is square integrable for `F ∈ L²` and bounded continuous `G`. -/
theorem memLp_mul_smoothBounded (hG : IsSmoothBounded G) (F : Lp ℝ 2 μ) :
    MemLp (fun x ↦ F x * G x) 2 μ := by
  obtain ⟨D, hD⟩ := hG.bounded
  have hg : MemLp (fun x ↦ D * ‖F x‖) 2 μ := (Lp.memLp F).norm.const_mul _
  refine MemLp.of_le hg ((Lp.aestronglyMeasurable F).mul hG.continuous.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x ↦ ?_)
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD x)
  have h0 : 0 ≤ D * ‖F x‖ := mul_nonneg hD0 (norm_nonneg _)
  rw [Real.norm_eq_abs (D * ‖F x‖), abs_of_nonneg h0, norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (by rw [Real.norm_eq_abs]; exact hD x) (norm_nonneg _)

/-- `G • η + F • DG` is square integrable. -/
theorem memLp_mul_deriv (hG : IsSmoothBounded G) (F : Lp ℝ 2 μ) (η : Lp (Space μ) 2 μ) :
    MemLp (fun x ↦ G x • η x + F x • mderiv μ G x) 2 μ := by
  obtain ⟨D, hD⟩ := hG.bounded
  obtain ⟨D', hD'⟩ := hG.exists_norm_mderiv_le (μ := μ)
  have h1 : MemLp (fun x ↦ G x • η x) 2 μ := by
    have hg : MemLp (fun x ↦ D * ‖η x‖) 2 μ := (Lp.memLp η).norm.const_mul _
    refine MemLp.of_le hg (hG.continuous.aestronglyMeasurable.smul (Lp.aestronglyMeasurable η))
      (Filter.Eventually.of_forall fun x ↦ ?_)
    have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD x)
    have h0 : 0 ≤ D * ‖η x‖ := mul_nonneg hD0 (norm_nonneg _)
    rw [Real.norm_eq_abs (D * ‖η x‖), abs_of_nonneg h0, norm_smul]
    exact mul_le_mul_of_nonneg_right (by rw [Real.norm_eq_abs]; exact hD x) (norm_nonneg _)
  have h2 : MemLp (fun x ↦ F x • mderiv μ G x) 2 μ := by
    have hg : MemLp (fun x ↦ D' * ‖F x‖) 2 μ := (Lp.memLp F).norm.const_mul _
    refine MemLp.of_le hg
      ((Lp.aestronglyMeasurable F).smul hG.continuous_mderiv.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x ↦ ?_)
    have hD0 : 0 ≤ D' := (norm_nonneg _).trans (hD' x)
    have h0 : 0 ≤ D' * ‖F x‖ := mul_nonneg hD0 (norm_nonneg _)
    rw [Real.norm_eq_abs (D' * ‖F x‖), abs_of_nonneg h0, norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hD' x) (norm_nonneg _)
  exact h1.add h2

/-- **Product rule in `𝔻₁,₂`**: for `F ∈ 𝔻₁,₂` and a smooth bounded `G`, the product `F · G`
lies in `𝔻₁,₂` with `D_cl (F G) = G • D_cl F + F • D G`. -/
theorem mul_mem_domD12 (hG : IsSmoothBounded G) {F : Lp ℝ 2 μ} (hF : F ∈ domD12 μ) :
    (memLp_mul_smoothBounded μ hG F).toLp _ ∈ domD12 μ ∧
      mderivClosure μ ((memLp_mul_smoothBounded μ hG F).toLp _) =
        (memLp_mul_deriv μ hG F (mderivClosure μ F)).toLp _ := by
  obtain ⟨η, hcl⟩ := hF
  have hη : mderivClosure μ F = η := mderivClosure_eq μ hcl
  obtain ⟨Fk, hFk, hDk⟩ := hcl
  obtain ⟨D, hD⟩ := hG.bounded
  obtain ⟨D', hD'⟩ := hG.exists_norm_mderiv_le (μ := μ)
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  have hD'0 : 0 ≤ D' := (norm_nonneg _).trans (hD' 0)
  rw [hη]
  refine mem_domD12_of_tendsto μ (F := fun k ↦ ((Fk k).2.mul hG).toLp μ)
    (fun k ↦ IsSmoothBounded.toLp_mem_domD12 μ _) ?_ ?_
  · -- values
    simp only [IsSmoothBounded.toLp] at hFk ⊢
    rw [tendsto_iff_norm_sub_tendsto_zero]
    rw [tendsto_iff_norm_sub_tendsto_zero] at hFk
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun k ↦ ?_) (by simpa using hFk.const_mul D)
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [Lp.coeFn_sub ((((Fk k).2.mul hG).memLp μ 2).toLp _)
        ((memLp_mul_smoothBounded μ hG F).toLp _),
      Lp.coeFn_sub (((Fk k).2.memLp μ 2).toLp _) F,
      MemLp.coeFn_toLp (((Fk k).2.mul hG).memLp μ 2),
      MemLp.coeFn_toLp (memLp_mul_smoothBounded μ hG F),
      MemLp.coeFn_toLp ((Fk k).2.memLp μ 2)] with x h1 h2 h3 h4 h5
    rw [h1, h2, Pi.sub_apply, Pi.sub_apply, h3, h4, h5, ← sub_mul, norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (by rw [Real.norm_eq_abs]; exact hD x) (norm_nonneg _)
  · -- derivatives
    simp_rw [mderivClosure_toLp]
    set target := (memLp_mul_deriv μ hG F η).toLp _ with htarget
    have hM : ∀ k, MemLp (fun x ↦ G x • η x + (Fk k).1 x • mderiv μ G x) 2 μ := fun k ↦
      MemLp.ae_eq (by
        filter_upwards [MemLp.coeFn_toLp ((Fk k).2.memLp μ 2)] with x hx
        rw [IsSmoothBounded.toLp, hx]) (memLp_mul_deriv μ hG ((Fk k).2.toLp μ) η)
    -- `‖D(Fₖ G) - Mₖ‖ ≤ D ‖DFₖ - η‖`
    have hA : ∀ k, ‖((Fk k).2.mul hG).mderivLp μ - (hM k).toLp _‖ ≤
        D * ‖(Fk k).2.mderivLp μ - η‖ := by
      intro k
      refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
      filter_upwards [Lp.coeFn_sub (((Fk k).2.mul hG).mderivLp μ) ((hM k).toLp _),
        Lp.coeFn_sub ((Fk k).2.mderivLp μ) η,
        MemLp.coeFn_toLp (((Fk k).2.mul hG).memLp_mderiv μ 2),
        MemLp.coeFn_toLp (hM k),
        MemLp.coeFn_toLp ((Fk k).2.memLp_mderiv μ 2)] with x h1 h2 h3 h4 h5
      rw [h1, h2, Pi.sub_apply, Pi.sub_apply, IsSmoothBounded.mderivLp, h3, h4,
        IsSmoothBounded.mderivLp, h5,
        mderiv_mul μ ((Fk k).2.differentiable x) (hG.differentiable x)]
      have : (Fk k).1 x • mderiv μ G x + G x • mderiv μ (Fk k).1 x -
          (G x • η x + (Fk k).1 x • mderiv μ G x) = G x • (mderiv μ (Fk k).1 x - η x) := by
        rw [smul_sub]; abel
      rw [this, norm_smul]
      exact mul_le_mul_of_nonneg_right (by rw [Real.norm_eq_abs]; exact hD x) (norm_nonneg _)
    -- `‖Mₖ - target‖ ≤ D' ‖Fₖ - F‖`
    have hB : ∀ k, ‖(hM k).toLp _ - target‖ ≤ D' * ‖(Fk k).2.toLp μ - F‖ := by
      intro k
      refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
      filter_upwards [Lp.coeFn_sub ((hM k).toLp _) target,
        Lp.coeFn_sub ((Fk k).2.toLp μ) F,
        MemLp.coeFn_toLp (hM k),
        MemLp.coeFn_toLp (memLp_mul_deriv μ hG F η),
        MemLp.coeFn_toLp ((Fk k).2.memLp μ 2)] with x h1 h2 h3 h4 h5
      rw [h1, h2, Pi.sub_apply, Pi.sub_apply, h3, htarget, h4, IsSmoothBounded.toLp, h5]
      have : G x • η x + (Fk k).1 x • mderiv μ G x - (G x • η x + F x • mderiv μ G x) =
          ((Fk k).1 x - F x) • mderiv μ G x := by
        rw [sub_smul]; abel
      rw [this, norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hD' x) (norm_nonneg _)
    rw [tendsto_iff_norm_sub_tendsto_zero]
    rw [tendsto_iff_norm_sub_tendsto_zero] at hDk hFk
    refine squeeze_zero (fun k ↦ norm_nonneg (((Fk k).2.mul hG).mderivLp μ - target))
      (fun k ↦ ?_) (by simpa using (hDk.const_mul D).add (hFk.const_mul D'))
    have htri : ‖((Fk k).2.mul hG).mderivLp μ - target‖ ≤
        ‖((Fk k).2.mul hG).mderivLp μ - (hM k).toLp _‖ + ‖(hM k).toLp _ - target‖ := by
      have := norm_add_le (((Fk k).2.mul hG).mderivLp μ - (hM k).toLp _) ((hM k).toLp _ - target)
      rwa [sub_add_sub_cancel] at this
    exact htri.trans (add_le_add (hA k) (hB k))

/-- Norm bound for the product rule: `‖D_cl (F G)‖ ≤ D' ‖F‖ + D ‖D_cl F‖` where `|G| ≤ D` and
`‖D G‖ ≤ D'`. -/
theorem norm_mderivClosure_mul_le (hG : IsSmoothBounded G) {F : Lp ℝ 2 μ} (hF : F ∈ domD12 μ)
    {D D' : ℝ} (hD : ∀ x, |G x| ≤ D) (hD' : ∀ x, ‖mderiv μ G x‖ ≤ D') :
    ‖mderivClosure μ ((memLp_mul_smoothBounded μ hG F).toLp _)‖ ≤
      D' * ‖F‖ + D * ‖mderivClosure μ F‖ := by
  rw [(mul_mem_domD12 μ hG hF).2]
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  have hD'0 : 0 ≤ D' := (norm_nonneg _).trans (hD' 0)
  have h1 : MemLp (fun x ↦ G x • (mderivClosure μ F) x) 2 μ := by
    have hg : MemLp (fun x ↦ D * ‖(mderivClosure μ F) x‖) 2 μ :=
      (Lp.memLp (mderivClosure μ F)).norm.const_mul _
    refine MemLp.of_le hg (hG.continuous.aestronglyMeasurable.smul
      (Lp.aestronglyMeasurable _)) (Filter.Eventually.of_forall fun x ↦ ?_)
    have h0 : 0 ≤ D * ‖(mderivClosure μ F) x‖ := mul_nonneg hD0 (norm_nonneg _)
    rw [Real.norm_eq_abs (D * _), abs_of_nonneg h0, norm_smul]
    exact mul_le_mul_of_nonneg_right (by rw [Real.norm_eq_abs]; exact hD x) (norm_nonneg _)
  have h2 : MemLp (fun x ↦ F x • mderiv μ G x) 2 μ := by
    have hg : MemLp (fun x ↦ D' * ‖F x‖) 2 μ := (Lp.memLp F).norm.const_mul _
    refine MemLp.of_le hg ((Lp.aestronglyMeasurable F).smul
      hG.continuous_mderiv.aestronglyMeasurable) (Filter.Eventually.of_forall fun x ↦ ?_)
    have h0 : 0 ≤ D' * ‖F x‖ := mul_nonneg hD'0 (norm_nonneg _)
    rw [Real.norm_eq_abs (D' * _), abs_of_nonneg h0, norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hD' x) (norm_nonneg _)
  have hsplit : (memLp_mul_deriv μ hG F (mderivClosure μ F)).toLp _ =
      h1.toLp _ + h2.toLp _ := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x ↦ rfl)
  rw [hsplit]
  refine (norm_add_le (h1.toLp _) (h2.toLp _)).trans ?_
  rw [add_comm (D' * ‖F‖)]
  refine add_le_add ?_ ?_
  · refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [MemLp.coeFn_toLp h1] with x hx
    rw [hx, norm_smul]
    exact mul_le_mul_of_nonneg_right (by rw [Real.norm_eq_abs]; exact hD x) (norm_nonneg _)
  · refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [MemLp.coeFn_toLp h2] with x hx
    rw [hx, norm_smul, mul_comm ‖F x‖]
    exact mul_le_mul_of_nonneg_right (hD' x) (norm_nonneg _)

/-- `F · G` as an element of the submodule `D12 μ`. -/
noncomputable def D12.mulSmooth (hG : IsSmoothBounded G) (F : D12 μ) : D12 μ :=
  ⟨(memLp_mul_smoothBounded μ hG F).toLp _, (mul_mem_domD12 μ hG F.2).1⟩

theorem D12.coe_mulSmooth (hG : IsSmoothBounded G) (F : D12 μ) :
    (D12.mulSmooth μ hG F : Lp ℝ 2 μ) = (memLp_mul_smoothBounded μ hG F).toLp _ := rfl

/-- The product rule for the subtype map `mderivD12`. -/
theorem mderivD12_mulSmooth (hG : IsSmoothBounded G) (F : D12 μ) :
    mderivD12 μ (D12.mulSmooth μ hG F) = (memLp_mul_deriv μ hG F (mderivD12 μ F)).toLp _ :=
  (mul_mem_domD12 μ hG F.2).2

end Product

/-! ### The multivariate chain rule

`f (F₁, …, Fₙ) ∈ 𝔻₁,₂` with `D_cl f(F) = ∑ᵢ ∂ᵢ f (F) • D_cl Fᵢ` for `f : ℝⁿ → ℝ` of class `C¹` with
bounded derivative and `Fᵢ ∈ 𝔻₁,₂` (`comp_pi_mem_domD12`).  The proof follows the scalar case;
the almost everywhere convergent subsequence is extracted from convergence in measure of the
tuple `(Fₖ,ᵢ)ᵢ` (`tendstoInMeasure_pi`), and the `L²` estimates are carried out on `eLpNorm`. -/

section PiChain

open CameronMartin

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]

omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  [IsGaussian μ] in
/-- The derivative of a tuple of functions, applied to a vector. -/
theorem fderiv_pi_apply_eq_sum {n : ℕ} {G : Fin n → W → ℝ} {x : W}
    (hG : ∀ i, DifferentiableAt ℝ (G i) x) (w : W) :
    fderiv ℝ (fun y i ↦ G i y) x w = ∑ i, fderiv ℝ (G i) x w • Pi.single i (1 : ℝ) := by
  rw [fderiv_pi hG]
  ext j
  rw [ContinuousLinearMap.pi_apply, Finset.sum_apply]
  simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]

/-- **Chain rule for a `C¹` function of finitely many differentiable functionals**:
`D f(G₁, …, Gₙ) = ∑ᵢ ∂ᵢ f (G) • D Gᵢ`. -/
theorem mderiv_comp_pi {n : ℕ} {f : (Fin n → ℝ) → ℝ} {G : Fin n → W → ℝ} {x : W}
    (hf : DifferentiableAt ℝ f (fun i ↦ G i x)) (hG : ∀ i, DifferentiableAt ℝ (G i) x) :
    mderiv μ (fun y ↦ f (fun i ↦ G i y)) x =
      ∑ i, fderiv ℝ f (fun i ↦ G i x) (Pi.single i 1) • mderiv μ (G i) x := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_mderiv, Submodule.coe_inner, Submodule.coe_sum, sum_inner]
  simp only [Submodule.coe_smul, real_inner_smul_left]
  simp_rw [← Submodule.coe_inner, inner_mderiv]
  have hcomp : (fun y ↦ f (fun i ↦ G i y)) = f ∘ fun y i ↦ G i y := rfl
  rw [hcomp, fderiv_comp x hf (differentiableAt_pi.mpr hG), ContinuousLinearMap.comp_apply,
    fderiv_pi_apply_eq_sum hG, map_sum]
  simp_rw [map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  [IsGaussian μ] in
/-- A `C¹` function with bounded derivative of finitely many smooth bounded functionals is smooth
bounded. -/
theorem IsSmoothBounded.comp_pi {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {K : ℝ} (hK : ∀ y, ‖fderiv ℝ f y‖ ≤ K) {G : Fin n → W → ℝ}
    (hG : ∀ i, IsSmoothBounded (G i)) : IsSmoothBounded (fun x ↦ f (fun i ↦ G i x)) where
  contDiff := hf.comp (contDiff_pi.mpr fun i ↦ (hG i).contDiff)
  bounded := by
    have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
    have hlip : LipschitzWith (Real.toNNReal K) f :=
      lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable one_ne_zero) fun y ↦ by
        rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal K hK0]; exact hK y
    choose C hC using fun i ↦ (hG i).bounded
    refine ⟨|f 0| + K * ∑ i, C i, fun x ↦ ?_⟩
    have h := hlip.dist_le_mul (fun i ↦ G i x) 0
    rw [Real.dist_eq, dist_zero_right, Real.coe_toNNReal K hK0] at h
    have hnorm : ‖fun i ↦ G i x‖ ≤ ∑ i, C i := by
      rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ ↦ (abs_nonneg _).trans (hC i x))]
      intro i
      rw [Real.norm_eq_abs]
      exact (hC i x).trans (Finset.single_le_sum (fun j _ ↦ (abs_nonneg _).trans (hC j x))
        (Finset.mem_univ i))
    calc |f (fun i ↦ G i x)| = |f (fun i ↦ G i x) - f 0 + f 0| := by rw [sub_add_cancel]
      _ ≤ |f (fun i ↦ G i x) - f 0| + |f 0| := abs_add_le _ _
      _ ≤ K * ‖fun i ↦ G i x‖ + |f 0| := add_le_add_left h _
      _ ≤ K * ∑ i, C i + |f 0| := by gcongr
      _ = |f 0| + K * ∑ i, C i := add_comm _ _
  bounded_fderiv := by
    have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
    choose C hC using fun i ↦ (hG i).bounded_fderiv
    refine ⟨K * ∑ i, C i, fun x ↦ ?_⟩
    have hcomp : (fun x ↦ f (fun i ↦ G i x)) = f ∘ fun y i ↦ G i y := rfl
    rw [hcomp, fderiv_comp x (hf.differentiable one_ne_zero _)
      (differentiableAt_pi.mpr fun i ↦ (hG i).differentiable x)]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have hC0 : 0 ≤ ∑ i, C i := Finset.sum_nonneg fun i _ ↦ (norm_nonneg _).trans (hC i x)
    refine mul_le_mul (hK _) ?_ (norm_nonneg _) hK0
    refine ContinuousLinearMap.opNorm_le_bound _ hC0 fun w ↦ ?_
    rw [fderiv_pi fun i ↦ (hG i).differentiable x, pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    rw [ContinuousLinearMap.pi_apply]
    refine ((fderiv ℝ (G i) x).le_opNorm w).trans ?_
    gcongr
    exact (hC i x).trans
      (Finset.single_le_sum (fun j _ ↦ (norm_nonneg _).trans (hC j x)) (Finset.mem_univ i))

omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  [IsGaussian μ] in
theorem norm_pi_le_sum_abs {n : ℕ} (y : Fin n → ℝ) : ‖y‖ ≤ ∑ i, |y i| := by
  rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)]
  intro i
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (fun j _ ↦ abs_nonneg (y j)) (Finset.mem_univ i)

omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  [IsGaussian μ] in
/-- A `C¹` function with `‖f'‖ ≤ K` is `K`-Lipschitz. -/
theorem abs_sub_le_of_fderiv_le {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ}
    (hK : ∀ y, ‖fderiv ℝ f y‖ ≤ K) (y z : Fin n → ℝ) : |f y - f z| ≤ K * ‖y - z‖ := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have hlip : LipschitzWith (Real.toNNReal K) f :=
    lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable one_ne_zero) fun y ↦ by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal K hK0]; exact hK y
  have h := hlip.dist_le_mul y z
  rwa [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal K hK0] at h

omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- `f (F₁, …, Fₙ)` is square integrable for Lipschitz `f` and `Fᵢ ∈ L²`. -/
theorem memLp_comp_pi {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ}
    (hK : ∀ y, ‖fderiv ℝ f y‖ ≤ K) (F : Fin n → Lp ℝ 2 μ) :
    MemLp (fun x ↦ f (fun i ↦ F i x)) 2 μ := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have h1 : MemLp (fun _ : W ↦ |f 0|) 2 μ := memLp_const _
  have h2 : MemLp (fun x ↦ K * ∑ i, ‖F i x‖) 2 μ :=
    (memLp_finsetSum (f := fun i x ↦ ‖F i x‖) Finset.univ fun i _ ↦
      (Lp.memLp (F i)).norm).const_mul _
  refine MemLp.of_le (h1.add h2)
    (hf.continuous.comp_aestronglyMeasurable (aemeasurable_pi_iff.mpr fun i ↦
      (Lp.aestronglyMeasurable (F i)).aemeasurable).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x ↦ ?_)
  have hb : |f (fun i ↦ F i x)| ≤ |f 0| + K * ∑ i, ‖F i x‖ := by
    calc |f (fun i ↦ F i x)| = |f (fun i ↦ F i x) - f 0 + f 0| := by rw [sub_add_cancel]
      _ ≤ |f (fun i ↦ F i x) - f 0| + |f 0| := abs_add_le _ _
      _ ≤ K * ‖(fun i ↦ F i x) - 0‖ + |f 0| := add_le_add_left (abs_sub_le_of_fderiv_le hf hK _ _) _
      _ ≤ K * ∑ i, ‖F i x‖ + |f 0| := by
          rw [sub_zero]
          gcongr
          simpa [Real.norm_eq_abs] using norm_pi_le_sum_abs (fun i ↦ F i x)
      _ = |f 0| + K * ∑ i, ‖F i x‖ := add_comm _ _
  have h0 : 0 ≤ |f 0| + K * ∑ i, ‖F i x‖ := (abs_nonneg _).trans hb
  rw [Pi.add_apply, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0]
  exact hb

omit [CompleteSpace W] [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  [IsGaussian μ] in
theorem abs_fderiv_pi_single_le {n : ℕ} {f : (Fin n → ℝ) → ℝ} {K : ℝ}
    (hK : ∀ y, ‖fderiv ℝ f y‖ ≤ K) (y : Fin n → ℝ) (i : Fin n) :
    |fderiv ℝ f y (Pi.single i 1)| ≤ K := by
  rw [← Real.norm_eq_abs]
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  refine (mul_le_of_le_one_right (norm_nonneg _) ?_).trans (hK y)
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro j
  by_cases hij : j = i <;> simp [hij]

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- `∑ᵢ ∂ᵢ f (F) • ηᵢ` is square integrable for bounded `f'`. -/
theorem memLp_grad_smul {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ}
    (hK : ∀ y, ‖fderiv ℝ f y‖ ≤ K) {G : Fin n → W → ℝ} (hG : ∀ i, AEStronglyMeasurable (G i) μ)
    (η : Fin n → Lp (Space μ) 2 μ) :
    MemLp (fun x ↦ ∑ i, fderiv ℝ f (fun i ↦ G i x) (Pi.single i 1) • η i x) 2 μ := by
  refine memLp_finsetSum (f := fun i x ↦ fderiv ℝ f (fun i ↦ G i x) (Pi.single i 1) • η i x)
    Finset.univ fun i _ ↦ ?_
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have hg : MemLp (fun x ↦ K * ‖η i x‖) 2 μ := (Lp.memLp (η i)).norm.const_mul _
  have hmeas : AEStronglyMeasurable (fun x ↦ fderiv ℝ f (fun i ↦ G i x) (Pi.single i (1 : ℝ))) μ :=
    ((hf.continuous_fderiv one_ne_zero).comp_aestronglyMeasurable
      (aemeasurable_pi_iff.mpr fun i ↦ (hG i).aemeasurable).aestronglyMeasurable
      |>.apply_continuousLinearMap _)
  refine MemLp.of_le hg (hmeas.smul (Lp.aestronglyMeasurable (η i)))
    (Filter.Eventually.of_forall fun x ↦ ?_)
  have h0 : 0 ≤ K * ‖η i x‖ := mul_nonneg hK0 (norm_nonneg _)
  rw [norm_smul, Real.norm_eq_abs (K * ‖η i x‖), abs_of_nonneg h0, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (abs_fderiv_pi_single_le hK _ i) (norm_nonneg _)

variable {α ι : Type*} [MeasurableSpace α] {ν : Measure α} [Fintype ι] in
/-- Convergence in measure of a finite family of coordinates gives convergence in measure of
the tuple. -/
theorem tendstoInMeasure_pi {f : ℕ → α → ι → ℝ} {g : α → ι → ℝ}
    (h : ∀ i, TendstoInMeasure ν (fun n x ↦ f n x i) atTop (fun x ↦ g x i)) :
    TendstoInMeasure ν f atTop g := by
  rw [tendstoInMeasure_iff_dist]
  simp_rw [tendstoInMeasure_iff_dist] at h
  intro ε hε
  have hsub : ∀ n, {x | ε ≤ dist (f n x) (g x)} ⊆ ⋃ i, {x | ε ≤ dist (f n x i) (g x i)} := by
    intro n x hx
    simp only [Set.mem_ofPred_eq] at hx
    by_contra hcon
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_le] at hcon
    have hlt : dist (f n x) (g x) < ε := by
      rw [dist_pi_lt_iff hε]
      exact hcon
    exact absurd hx (not_le.mpr hlt)
  have hle : ∀ n, ν {x | ε ≤ dist (f n x) (g x)} ≤
      ∑ i, ν {x | ε ≤ dist (f n x i) (g x i)} := fun n ↦
    (measure_mono (hsub n)).trans (measure_iUnion_fintype_le _ _)
  have hsum : Tendsto (fun n ↦ ∑ i, ν {x | ε ≤ dist (f n x i) (g x i)}) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ fun i _ ↦ h i ε hε
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ ↦ zero_le) hle

omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- `L²` convergence of the values `f (Fₖ) → f (F)` from the coordinates, via `eLpNorm`. -/
theorem tendsto_comp_pi_of_tendsto {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ}
    (hK : ∀ y, ‖fderiv ℝ f y‖ ≤ K) {G : ℕ → Fin n → W → ℝ}
    (hG : ∀ k i, MemLp (G k i) 2 μ) {F : Fin n → Lp ℝ 2 μ}
    (hconv : ∀ i, Tendsto (fun k ↦ (hG k i).toLp _) atTop (𝓝 (F i)))
    (hGk : ∀ k, MemLp (fun x ↦ f (fun i ↦ G k i x)) 2 μ) :
    Tendsto (fun k ↦ (hGk k).toLp _) atTop (𝓝 ((memLp_comp_pi μ hf hK F).toLp _)) := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have hbound : ∀ k, eLpNorm (⇑((hGk k).toLp _) - ⇑((memLp_comp_pi μ hf hK F).toLp _)) 2 μ ≤
      ‖K‖ₑ * ∑ i, eLpNorm (⇑((hG k i).toLp _) - ⇑(F i)) 2 μ := by
    intro k
    calc eLpNorm (⇑((hGk k).toLp _) - ⇑((memLp_comp_pi μ hf hK F).toLp _)) 2 μ
        = eLpNorm (fun x ↦ f (fun i ↦ G k i x) - f (fun i ↦ F i x)) 2 μ := by
          refine eLpNorm_congr_ae ?_
          filter_upwards [MemLp.coeFn_toLp (hGk k), MemLp.coeFn_toLp (memLp_comp_pi μ hf hK F)]
            with x h1 h2
          rw [Pi.sub_apply, h1, h2]
      _ ≤ eLpNorm (K • ∑ i, fun x ↦ ‖(⇑((hG k i).toLp _) - ⇑(F i)) x‖) 2 μ := by
          refine eLpNorm_mono_ae ((hGk k).aestronglyMeasurable.sub
            (memLp_comp_pi μ hf hK F).aestronglyMeasurable) ?_
          have hae := ae_all_iff.2 fun i ↦ MemLp.coeFn_toLp (hG k i)
          filter_upwards [hae] with x hx
          rw [Pi.smul_apply, Finset.sum_apply, Real.norm_eq_abs, smul_eq_mul]
          have h0 : 0 ≤ K * ∑ i, ‖(⇑((hG k i).toLp _) - ⇑(F i)) x‖ :=
            mul_nonneg hK0 (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
          rw [Real.norm_eq_abs, abs_of_nonneg h0]
          refine (abs_sub_le_of_fderiv_le hf hK _ _).trans ?_
          gcongr
          refine (norm_pi_le_sum_abs _).trans (le_of_eq ?_)
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [Pi.sub_apply, Pi.sub_apply, hx i, Real.norm_eq_abs]
      _ = ‖K‖ₑ * eLpNorm (∑ i, fun x ↦ ‖(⇑((hG k i).toLp _) - ⇑(F i)) x‖) 2 μ :=
          eLpNorm_const_smul _ _ _ _
      _ ≤ ‖K‖ₑ * ∑ i, eLpNorm (fun x ↦ ‖(⇑((hG k i).toLp _) - ⇑(F i)) x‖) 2 μ := by
          gcongr
          exact eLpNorm_sum_le one_le_two
      _ = ‖K‖ₑ * ∑ i, eLpNorm (⇑((hG k i).toLp _) - ⇑(F i)) 2 μ := by
          congr 1
          exact Finset.sum_congr rfl fun i _ ↦ eLpNorm_norm _
            ((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _))
  have hlim : Tendsto (fun k ↦ ‖K‖ₑ * ∑ i, eLpNorm (⇑((hG k i).toLp _) - ⇑(F i)) 2 μ) atTop
      (𝓝 0) := by
    have h := tendsto_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) ↦
      (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp (hconv i)
    simp only [Finset.sum_const_zero] at h
    simpa using ENNReal.Tendsto.const_mul h (Or.inr enorm_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ ↦ zero_le) hbound

/-- **Multivariate chain rule in `𝔻₁,₂`** (Nualart, Proposition 1.2.3): for `f : ℝⁿ → ℝ` of
class `C¹` with bounded derivative and `F₁, …, Fₙ ∈ 𝔻₁,₂`, `f (F₁, …, Fₙ) ∈ 𝔻₁,₂` with
`D_cl f(F) = ∑ᵢ ∂ᵢ f (F) • D_cl Fᵢ`. -/
theorem comp_pi_mem_domD12 {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ}
    (hK : ∀ y, ‖fderiv ℝ f y‖ ≤ K) {F : Fin n → Lp ℝ 2 μ} (hF : ∀ i, F i ∈ domD12 μ) :
    (memLp_comp_pi μ hf hK F).toLp _ ∈ domD12 μ ∧
      mderivClosure μ ((memLp_comp_pi μ hf hK F).toLp _) =
        (memLp_grad_smul μ hf hK (fun i ↦ Lp.aestronglyMeasurable (F i))
          (fun i ↦ mderivClosure μ (F i))).toLp _ := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  choose η hcl using hF
  have hη : ∀ i, mderivClosure μ (F i) = η i := fun i ↦ mderivClosure_eq μ (hcl i)
  choose Fk hFk hDk using hcl
  -- an almost everywhere convergent subsequence of the tuples
  have hmeas : TendstoInMeasure μ (fun k x i ↦ (Fk i k).1 x) atTop (fun x i ↦ F i x) := by
    refine tendstoInMeasure_pi fun i ↦ ?_
    exact (tendstoInMeasure_of_tendsto_Lp (hFk i)).congr_left fun k ↦
      MemLp.coeFn_toLp ((Fk i k).2.memLp μ 2)
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  have hFk' : ∀ i, Tendsto (fun j ↦ (Fk i (ns j)).2.toLp μ) atTop (𝓝 (F i)) := fun i ↦
    (hFk i).comp hns.tendsto_atTop
  have hDk' : ∀ i, Tendsto (fun j ↦ (Fk i (ns j)).2.mderivLp μ) atTop (𝓝 (η i)) := fun i ↦
    (hDk i).comp hns.tendsto_atTop
  simp_rw [hη]
  refine mem_domD12_of_tendsto μ
    (F := fun j ↦ (IsSmoothBounded.comp_pi hf hK fun i ↦ (Fk i (ns j)).2).toLp μ)
    (fun j ↦ IsSmoothBounded.toLp_mem_domD12 μ _) ?_ ?_
  · -- values
    simp only [IsSmoothBounded.toLp]
    exact tendsto_comp_pi_of_tendsto μ hf hK (G := fun j i ↦ (Fk i (ns j)).1)
      (fun j i ↦ (Fk i (ns j)).2.memLp μ 2) (fun i ↦ by simpa [IsSmoothBounded.toLp] using hFk' i)
      (fun j ↦ (IsSmoothBounded.comp_pi hf hK fun i ↦ (Fk i (ns j)).2).memLp μ 2)
  · -- derivatives
    simp_rw [mderivClosure_toLp]
    set target := (memLp_grad_smul μ hf hK (fun i ↦ Lp.aestronglyMeasurable (F i)) η).toLp _
      with htarget
    have hM : ∀ j, MemLp (fun x ↦ ∑ i, fderiv ℝ f (fun i ↦ (Fk i (ns j)).1 x) (Pi.single i 1) •
        η i x) 2 μ := fun j ↦
      memLp_grad_smul μ hf hK (fun i ↦ (Fk i (ns j)).2.continuous.aestronglyMeasurable) η
    -- `Mⱼ → target` by dominated convergence
    have hMt : Tendsto (fun j ↦ (hM j).toLp _) atTop (𝓝 target) := by
      have hS : MemLp (fun x ↦ ∑ i, ‖η i x‖) 2 μ :=
        memLp_finsetSum (f := fun i x ↦ ‖η i x‖) Finset.univ fun i _ ↦ (Lp.memLp (η i)).norm
      refine tendsto_toLp_of_dominated hM
        (memLp_grad_smul μ hf hK (fun i ↦ Lp.aestronglyMeasurable (F i)) η)
        (bound := fun x ↦ (2 * K) ^ 2 * (∑ i, ‖η i x‖) ^ 2)
        (((memLp_two_iff_integrable_sq_norm hS.aestronglyMeasurable).mp hS |>.congr
          (Filter.Eventually.of_forall fun x ↦ by
            simp [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)]))
          |>.const_mul _)
        (fun j ↦ Filter.Eventually.of_forall fun x ↦ ?_) ?_
      · rw [← Finset.sum_sub_distrib, ← mul_pow]
        simp_rw [← sub_smul]
        gcongr
        refine (norm_sum_le _ _).trans ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun i _ ↦ ?_
        rw [norm_smul, Real.norm_eq_abs]
        gcongr
        calc |fderiv ℝ f (fun i ↦ (Fk i (ns j)).1 x) (Pi.single i 1) -
              fderiv ℝ f (fun i ↦ F i x) (Pi.single i 1)|
            ≤ |fderiv ℝ f (fun i ↦ (Fk i (ns j)).1 x) (Pi.single i 1)| +
                |fderiv ℝ f (fun i ↦ F i x) (Pi.single i 1)| := abs_sub _ _
          _ ≤ K + K := add_le_add (abs_fderiv_pi_single_le hK _ i) (abs_fderiv_pi_single_le hK _ i)
          _ = 2 * K := by ring
      · filter_upwards [hae] with x hx
        refine tendsto_finsetSum _ fun i _ ↦ Tendsto.smul_const ?_ _
        have hc : Continuous fun y ↦ fderiv ℝ f y (Pi.single i (1 : ℝ)) :=
          (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
        exact (hc.tendsto _).comp hx
    -- `‖Aⱼ - Mⱼ‖ → 0`
    have hAM : Tendsto (fun j ↦ (IsSmoothBounded.comp_pi hf hK fun i ↦ (Fk i (ns j)).2).mderivLp μ
        - (hM j).toLp _) atTop (𝓝 0) := by
      rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
      have hbound : ∀ j, eLpNorm
          (⇑((IsSmoothBounded.comp_pi hf hK fun i ↦ (Fk i (ns j)).2).mderivLp μ
          - (hM j).toLp _) - ⇑(0 : Lp (Space μ) 2 μ)) 2 μ ≤
          ‖K‖ₑ * ∑ i, eLpNorm (⇑((Fk i (ns j)).2.mderivLp μ) - ⇑(η i)) 2 μ := by
        intro j
        calc eLpNorm (⇑((IsSmoothBounded.comp_pi hf hK fun i ↦ (Fk i (ns j)).2).mderivLp μ
                - (hM j).toLp _) - ⇑(0 : Lp (Space μ) 2 μ)) 2 μ
            = eLpNorm (∑ i, fun x ↦ fderiv ℝ f (fun i ↦ (Fk i (ns j)).1 x) (Pi.single i 1) •
                (⇑((Fk i (ns j)).2.mderivLp μ) - ⇑(η i)) x) 2 μ := by
              refine eLpNorm_congr_ae ?_
              have hae := ae_all_iff.2 fun i ↦ MemLp.coeFn_toLp ((Fk i (ns j)).2.memLp_mderiv μ 2)
              filter_upwards [Lp.coeFn_sub
                  ((IsSmoothBounded.comp_pi hf hK fun i ↦ (Fk i (ns j)).2).mderivLp μ)
                  ((hM j).toLp _), Lp.coeFn_zero (E := Space μ) 2 μ,
                MemLp.coeFn_toLp
                  ((IsSmoothBounded.comp_pi hf hK fun i ↦ (Fk i (ns j)).2).memLp_mderiv μ 2),
                MemLp.coeFn_toLp (hM j), hae] with x h1 h2 h3 h4 h5
              rw [Pi.sub_apply, h1, h2, Pi.sub_apply, IsSmoothBounded.mderivLp, h3, h4,
                mderiv_comp_pi μ (hf.differentiable one_ne_zero _)
                  (fun i ↦ (Fk i (ns j)).2.differentiable x),
                Finset.sum_apply, Pi.zero_apply, sub_zero, ← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl fun i _ ↦ ?_
              rw [IsSmoothBounded.mderivLp, Pi.sub_apply, h5 i, smul_sub]
          _ ≤ ∑ i, eLpNorm (fun x ↦ fderiv ℝ f (fun i ↦ (Fk i (ns j)).1 x) (Pi.single i 1) •
                (⇑((Fk i (ns j)).2.mderivLp μ) - ⇑(η i)) x) 2 μ := by
              exact eLpNorm_sum_le one_le_two
          _ ≤ ∑ i, eLpNorm (K • (⇑((Fk i (ns j)).2.mderivLp μ) - ⇑(η i))) 2 μ := by
              refine Finset.sum_le_sum fun i _ ↦ ?_
              have hc : AEStronglyMeasurable
                  (fun x ↦ fderiv ℝ f (fun i ↦ (Fk i (ns j)).1 x) (Pi.single i (1 : ℝ))) μ :=
                (((hf.continuous_fderiv one_ne_zero).comp (continuous_pi fun i ↦
                  (Fk i (ns j)).2.continuous)).clm_apply continuous_const).aestronglyMeasurable
              refine eLpNorm_mono
                (hc.smul ((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _))) ?_
              intro x
              rw [norm_smul, Pi.smul_apply, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
                abs_of_nonneg hK0]
              exact mul_le_mul_of_nonneg_right (abs_fderiv_pi_single_le hK _ i) (norm_nonneg _)
          _ ≤ ‖K‖ₑ * ∑ i, eLpNorm (⇑((Fk i (ns j)).2.mderivLp μ) - ⇑(η i)) 2 μ := by
              rw [Finset.mul_sum]
              exact Finset.sum_le_sum fun i _ ↦ eLpNorm_const_smul_le
      have hlim : Tendsto (fun j ↦ ‖K‖ₑ * ∑ i, eLpNorm (⇑((Fk i (ns j)).2.mderivLp μ) - ⇑(η i)) 2 μ)
          atTop (𝓝 0) := by
        have h := tendsto_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) ↦
          (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp (hDk' i)
        simp only [Finset.sum_const_zero] at h
        simpa using ENNReal.Tendsto.const_mul h (Or.inr enorm_ne_top)
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ ↦ zero_le)
        hbound
    have := hAM.add hMt
    simp only [sub_add_cancel, zero_add] at this
    exact this

/-- `‖D_cl f(F)‖ ≤ K ∑ᵢ ‖D_cl Fᵢ‖`. -/
theorem norm_mderivClosure_comp_pi_le {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f)
    {K : ℝ} (hK : ∀ y, ‖fderiv ℝ f y‖ ≤ K) {F : Fin n → Lp ℝ 2 μ} (hF : ∀ i, F i ∈ domD12 μ) :
    ‖mderivClosure μ ((memLp_comp_pi μ hf hK F).toLp _)‖ ≤
      K * ∑ i, ‖mderivClosure μ (F i)‖ := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  rw [(comp_pi_mem_domD12 μ hf hK hF).2, Lp.norm_toLp]
  have hmeas : ∀ i, AEStronglyMeasurable
      (fun x ↦ fderiv ℝ f (fun i ↦ F i x) (Pi.single i (1 : ℝ)) • (mderivClosure μ (F i)) x) μ :=
    fun i ↦ by
      have hpi : AEStronglyMeasurable (fun x i ↦ F i x) μ :=
        (aemeasurable_pi_iff.mpr fun i ↦
          (Lp.aestronglyMeasurable (F i)).aemeasurable).aestronglyMeasurable
      exact (((hf.continuous_fderiv one_ne_zero).comp_aestronglyMeasurable hpi)
        |>.apply_continuousLinearMap _).smul (Lp.aestronglyMeasurable _)
  have hbound : eLpNorm (fun x ↦ ∑ i, fderiv ℝ f (fun i ↦ F i x) (Pi.single i 1) •
      (mderivClosure μ (F i)) x) 2 μ ≤ ∑ i, ‖K‖ₑ * eLpNorm (⇑(mderivClosure μ (F i))) 2 μ := by
    calc eLpNorm (fun x ↦ ∑ i, fderiv ℝ f (fun i ↦ F i x) (Pi.single i 1) •
          (mderivClosure μ (F i)) x) 2 μ
        = eLpNorm (∑ i, fun x ↦ fderiv ℝ f (fun i ↦ F i x) (Pi.single i 1) •
            (mderivClosure μ (F i)) x) 2 μ := by
          congr 1
          funext x
          simp only [Finset.sum_apply]
      _ ≤ ∑ i, eLpNorm (fun x ↦ fderiv ℝ f (fun i ↦ F i x) (Pi.single i 1) •
            (mderivClosure μ (F i)) x) 2 μ := eLpNorm_sum_le one_le_two
      _ ≤ ∑ i, eLpNorm (K • ⇑(mderivClosure μ (F i))) 2 μ := by
          refine Finset.sum_le_sum fun i _ ↦ eLpNorm_mono (hmeas i) fun x ↦ ?_
          rw [norm_smul, Pi.smul_apply, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg hK0]
          exact mul_le_mul_of_nonneg_right (abs_fderiv_pi_single_le hK _ i) (norm_nonneg _)
      _ ≤ ∑ i, ‖K‖ₑ * eLpNorm (⇑(mderivClosure μ (F i))) 2 μ :=
          Finset.sum_le_sum fun i _ ↦ eLpNorm_const_smul_le
  have hfin : ∀ i, ‖K‖ₑ * eLpNorm (⇑(mderivClosure μ (F i))) 2 μ ≠ ∞ := fun i ↦
    ENNReal.mul_ne_top enorm_ne_top (Lp.eLpNorm_ne_top _)
  refine (ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr fun i _ ↦ hfin i) hbound).trans
    (le_of_eq ?_)
  rw [ENNReal.toReal_sum (fun i _ ↦ hfin i), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [ENNReal.toReal_mul, toReal_enorm, Real.norm_eq_abs, abs_of_nonneg hK0, Lp.norm_def]

/-- `f (F₁, …, Fₙ)` as an element of the submodule `D12 μ`. -/
noncomputable def D12.compPi {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ}
    (hK : ∀ y, ‖fderiv ℝ f y‖ ≤ K) (F : Fin n → D12 μ) : D12 μ :=
  ⟨(memLp_comp_pi μ hf hK fun i ↦ (F i : Lp ℝ 2 μ)).toLp _,
    (comp_pi_mem_domD12 μ hf hK fun i ↦ (F i).2).1⟩

/-- The multivariate chain rule for the subtype map `mderivD12`. -/
theorem mderivD12_compPi {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ}
    (hK : ∀ y, ‖fderiv ℝ f y‖ ≤ K) (F : Fin n → D12 μ) :
    mderivD12 μ (D12.compPi μ hf hK F) =
      (memLp_grad_smul μ hf hK (fun i ↦ Lp.aestronglyMeasurable (F i : Lp ℝ 2 μ))
        (fun i ↦ mderivD12 μ (F i))).toLp _ :=
  (comp_pi_mem_domD12 μ hf hK fun i ↦ (F i).2).2

end PiChain

/-! ### Functions of Wiener integrals

For `φ` of class `C¹` with bounded derivative, `φ (∫ g dB) ∈ 𝔻₁,₂` with the textbook time
derivative `Dₜ φ (∫ g dB) = φ' (∫ g dB) g(t)`. -/

section WienerSpace

open CameronMartin

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P] {B : ℝ≥0 → W → ℝ}
  {φ : ℝ → ℝ} {K : ℝ≥0}

omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- `φ' ∘ F` is square integrable for bounded `φ'`. -/
theorem memLp_deriv_comp (hφ : ContDiff ℝ 1 φ) (hK : ∀ x, ‖deriv φ x‖₊ ≤ K) (F : Lp ℝ 2 P) :
    MemLp (fun x ↦ deriv φ (F x)) 2 P :=
  MemLp.of_bound (hφ.continuous_deriv_one.comp_aestronglyMeasurable (Lp.aestronglyMeasurable F))
    K (Filter.Eventually.of_forall fun x ↦ by exact_mod_cast hK (F x))

/-- The closed derivative of `φ ∘ F` for `F` in the Cameron--Martin space is the rank-one element
`φ' (F) • h`. -/
theorem mderivClosure_comp_space (hφ : ContDiff ℝ 1 φ) (hK : ∀ x, ‖deriv φ x‖₊ ≤ K)
    (h : Space P) :
    mderivClosure P ((memLp_comp_of_deriv_le P hφ hK (h : Lp ℝ 2 P)).toLp _) =
      smulLp h ((memLp_deriv_comp hφ hK (h : Lp ℝ 2 P)).toLp _) := by
  rw [(comp_mem_domD12 P hφ hK (coe_space_mem_domD12 P h).1).2]
  have hc : (mderivClosure P (h : Lp ℝ 2 P) : W → Space P) =ᵐ[P] fun _ ↦ h := by
    rw [(coe_space_mem_domD12 P h).2, constLp_apply]
    exact Lp.coeFn_const 2 P h
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp
      (memLp_deriv_smul_of_deriv_le P hφ hK (h : Lp ℝ 2 P) (mderivClosure P (h : Lp ℝ 2 P))),
    coeFn_smulLp h ((memLp_deriv_comp hφ hK (h : Lp ℝ 2 P)).toLp _),
    MemLp.coeFn_toLp (memLp_deriv_comp hφ hK (h : Lp ℝ 2 P)), hc] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]

/-- **`Dₜ φ (∫ g dB) = φ' (∫ g dB) g(t)`** for `φ` of class `C¹` with bounded derivative. -/
theorem timeDerivative_mderivClosure_comp_wienerIntegral (hB : IsPreBrownianReal B P)
    (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    (hφ : ContDiff ℝ 1 φ) (hK : ∀ x, ‖deriv φ x‖₊ ≤ K) (g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    timeDerivative hB L hL hgen
        (mderivClosure P ((memLp_comp_of_deriv_le P hφ hK (wienerIntegral hB g)).toLp _)) =
      tensor g ((memLp_deriv_comp hφ hK (wienerIntegral hB g)).toLp _) := by
  have hmem := wienerIntegral_mem_space hB L hL hgen g
  rw [mderivClosure_comp_space hφ hK ⟨_, hmem⟩, timeDerivative_smulLp hB L hL hgen]
  congr 1
  apply (wienerIntegralEquiv hB).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

/-! #### The time-form chain rule -/

/-- `D_cl (φ ∘ F)` as a bounded multiple of `D_cl F`:
`D_cl (φ ∘ F) = φ' (F) • D_cl F` in `L²(P; H)`. -/
theorem mderivClosure_comp_eq_boundedSMul (hφ : ContDiff ℝ 1 φ) (hK : ∀ x, ‖deriv φ x‖₊ ≤ K)
    {F : Lp ℝ 2 P} (hF : F ∈ domD12 P) :
    mderivClosure P ((memLp_comp_of_deriv_le P hφ hK F).toLp _) =
      boundedSMul (hφ.continuous_deriv_one.comp_aestronglyMeasurable (Lp.aestronglyMeasurable F))
        (C := K) (fun x ↦ by rw [← Real.norm_eq_abs]; exact_mod_cast hK (F x))
        (mderivClosure P F) := by
  rw [(comp_mem_domD12 P hφ hK hF).2]
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (memLp_deriv_smul_of_deriv_le P hφ hK F (mderivClosure P F)),
    coeFn_boundedSMul (hφ.continuous_deriv_one.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable F)) (C := K) (fun x ↦ by
        rw [← Real.norm_eq_abs]; exact_mod_cast hK (F x)) (mderivClosure P F)] with x h1 h2
  rw [h1, h2]

/-- **The time-form chain rule**: `Dₜ φ (F) = φ' (F) Dₜ F` for every `F ∈ 𝔻₁,₂` and `φ` of class
`C¹` with bounded derivative, as an identity in `L²(ℝ≥0 × W)`. -/
theorem timeDerivative_mderivClosure_comp (hB : IsPreBrownianReal B P)
    (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    (hφ : ContDiff ℝ 1 φ) (hK : ∀ x, ‖deriv φ x‖₊ ≤ K) {F : Lp ℝ 2 P} (hF : F ∈ domD12 P) :
    timeDerivative hB L hL hgen (mderivClosure P ((memLp_comp_of_deriv_le P hφ hK F).toLp _)) =
      boundedSMul (aestronglyMeasurable_comp_snd (ν := nonnegativeLebesgueMeasure)
          (hφ.continuous_deriv_one.comp_aestronglyMeasurable (Lp.aestronglyMeasurable F)))
        (C := K) (fun p ↦ by rw [← Real.norm_eq_abs]; exact_mod_cast hK (F p.2))
        (timeDerivative hB L hL hgen (mderivClosure P F)) := by
  rw [mderivClosure_comp_eq_boundedSMul hφ hK hF, timeDerivative_boundedSMul hB L hL hgen]

/-! #### The time-form product rule with a cylindrical factor -/

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- `F · ∂ᵢ f (B)` is square integrable for `F ∈ L²` and bounded `f'`. -/
theorem memLp_mul_cylinderPartial (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w)
    {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) (hb' : ∃ C, ∀ y, ‖fderiv ℝ f y‖ ≤ C)
    (t : Fin n → ℝ≥0) (F : Lp ℝ 2 P) (i : Fin n) :
    MemLp (fun w ↦ F w * fderiv ℝ f (fun j ↦ B (t j) w) (Pi.single i 1)) 2 P := by
  obtain ⟨C, hC⟩ := hb'
  have hpart := memLp_cylinderPartial (P := P) L hL f hf ⟨C, hC⟩ t i
  refine MemLp.of_le ((Lp.memLp F).norm.const_mul C)
    ((Lp.aestronglyMeasurable F).mul hpart.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun w ↦ ?_)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have h1 : ‖fderiv ℝ f (fun j ↦ B (t j) w) (Pi.single i (1 : ℝ))‖ ≤ C := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    refine (mul_le_of_le_one_right (norm_nonneg _) ?_).trans (hC _)
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro j
    by_cases hij : j = i <;> simp [hij]
  rw [norm_mul, Real.norm_eq_abs (C * ‖F w‖), abs_of_nonneg (mul_nonneg hC0 (norm_nonneg _)),
    mul_comm]
  exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)

/-- **Time-form product rule with a cylindrical factor**:
`Dₜ (F · f (B t₁, …, B tₙ)) = f (B) Dₜ F + F ∑ᵢ ∂ᵢ f (B) 1_{(0, tᵢ]}(t)` for every `F ∈ 𝔻₁,₂`. -/
theorem timeDerivative_mderivClosure_mul_cylinder (hB : IsPreBrownianReal B P)
    (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    {n : ℕ} (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) {C : ℝ} (hb : ∀ y, |f y| ≤ C)
    (hb' : ∃ C, ∀ y, ‖fderiv ℝ f y‖ ≤ C) (t : Fin n → ℝ≥0) {F : Lp ℝ 2 P} (hF : F ∈ domD12 P) :
    timeDerivative hB L hL hgen (mderivClosure P
        ((memLp_mul_smoothBounded P (isSmoothBounded_cylinder L hL f hf ⟨C, hb⟩ hb' t) F).toLp
          _)) =
      boundedSMul (G := fun p : ℝ≥0 × W ↦ f (fun i ↦ B (t i) p.2))
          (aestronglyMeasurable_comp_snd (ν := nonnegativeLebesgueMeasure)
            (isSmoothBounded_cylinder L hL f hf ⟨C, hb⟩ hb' t).continuous.aestronglyMeasurable)
          (fun _ ↦ hb _) (timeDerivative hB L hL hgen (mderivClosure P F)) +
        ∑ i, tensor (intervalIndicator (t i))
          ((memLp_mul_cylinderPartial L hL f hf hb' t F i).toLp _) := by
  set G := fun w ↦ f (fun i ↦ B (t i) w) with hGdef
  have hG : IsSmoothBounded G := isSmoothBounded_cylinder L hL f hf ⟨C, hb⟩ hb' t
  rw [(mul_mem_domD12 P hG hF).2]
  -- split the derivative
  have hsplit : (memLp_mul_deriv P hG F (mderivClosure P F)).toLp _ =
      boundedSMul (G := G) hG.continuous.aestronglyMeasurable (fun x ↦ hb _)
          (mderivClosure P F) +
        ∑ i, smulLp (ofDual P (L (t i)))
          ((memLp_mul_cylinderPartial L hL f hf hb' t F i).toLp _) := by
    apply Lp.ext
    have h4 := ae_all_iff.2 fun i ↦ coeFn_smulLp (ofDual P (L (t i)))
      ((memLp_mul_cylinderPartial L hL f hf hb' t F i).toLp _)
    have h5 := ae_all_iff.2 fun i ↦
      MemLp.coeFn_toLp (memLp_mul_cylinderPartial L hL f hf hb' t F i)
    filter_upwards [MemLp.coeFn_toLp (memLp_mul_deriv P hG F (mderivClosure P F)),
      Lp.coeFn_add (boundedSMul (G := G) hG.continuous.aestronglyMeasurable (fun x ↦ hb _)
        (mderivClosure P F)) (∑ i, smulLp (ofDual P (L (t i)))
          ((memLp_mul_cylinderPartial L hL f hf hb' t F i).toLp _)),
      coeFn_boundedSMul (G := G) hG.continuous.aestronglyMeasurable (fun x ↦ hb _)
        (mderivClosure P F),
      Lp.coeFn_finsetSum Finset.univ (fun i ↦ smulLp (ofDual P (L (t i)))
        ((memLp_mul_cylinderPartial L hL f hf hb' t F i).toLp _)), h4, h5]
      with w h1 h2 h3 h6 h4 h5
    rw [h1, h2, Pi.add_apply, h3, h6, Finset.sum_apply]
    simp_rw [h4, h5]
    congr 1
    have hF' : G = fun w ↦ f (fun i ↦ L (t i) w) := by
      funext w
      simp only [hGdef, hL]
    have hBL : (fun j ↦ B (t j) w) = fun j ↦ L (t j) w := by
      funext j
      simp only [hL]
    rw [hF', mderiv_cylindrical P f (fun i ↦ L (t i)) w ((hf.differentiable one_ne_zero) _),
      hBL, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [smul_smul]
  rw [hsplit, map_add, timeDerivative_boundedSMul hB L hL hgen]
  congr 1
  have hsum := map_sum (timeDerivative hB L hL hgen).toLinearMap
    (fun i ↦ smulLp (ofDual P (L (t i)))
      ((memLp_mul_cylinderPartial L hL f hf hb' t F i).toLp _)) Finset.univ
  simp only [LinearIsometry.coe_toLinearMap] at hsum
  rw [hsum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [timeDerivative_smulLp hB L hL hgen, wienerIntegralEquiv_symm_ofDual hB L hL hgen]

/-! #### Functions of several Wiener integrals -/

omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- `∂ᵢ f (F)` is square integrable for bounded `f'`. -/
theorem memLp_fderiv_pi_comp {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ}
    (hK : ∀ y, ‖fderiv ℝ f y‖ ≤ K) (F : Fin n → Lp ℝ 2 P) (i : Fin n) :
    MemLp (fun x ↦ fderiv ℝ f (fun i ↦ F i x) (Pi.single i 1)) 2 P := by
  have hpi : AEStronglyMeasurable (fun x i ↦ F i x) P :=
    (aemeasurable_pi_iff.mpr fun i ↦
      (Lp.aestronglyMeasurable (F i)).aemeasurable).aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun x ↦ fderiv ℝ f (fun i ↦ F i x) (Pi.single i (1 : ℝ))) P :=
    ((hf.continuous_fderiv one_ne_zero).comp_aestronglyMeasurable hpi).apply_continuousLinearMap _
  exact MemLp.of_bound hmeas K (Filter.Eventually.of_forall fun x ↦ by
    rw [Real.norm_eq_abs]; exact abs_fderiv_pi_single_le hK _ i)

/-- `D_cl f(F)` as a sum of bounded multiples of the `D_cl Fᵢ`. -/
theorem mderivClosure_comp_pi_eq_sum_boundedSMul {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ 1 f) {K : ℝ} (hK : ∀ y, ‖fderiv ℝ f y‖ ≤ K) {F : Fin n → Lp ℝ 2 P}
    (hF : ∀ i, F i ∈ domD12 P) :
    mderivClosure P ((memLp_comp_pi P hf hK F).toLp _) =
      ∑ i, boundedSMul (G := fun x ↦ fderiv ℝ f (fun i ↦ F i x) (Pi.single i 1))
        (memLp_fderiv_pi_comp hf hK F i).aestronglyMeasurable (C := K)
        (fun _ ↦ abs_fderiv_pi_single_le hK _ i) (mderivClosure P (F i)) := by
  rw [(comp_pi_mem_domD12 P hf hK hF).2]
  apply Lp.ext
  have h2 := ae_all_iff.2 fun i ↦ coeFn_boundedSMul
    (G := fun x ↦ fderiv ℝ f (fun i ↦ F i x) (Pi.single i 1))
    (memLp_fderiv_pi_comp hf hK F i).aestronglyMeasurable (C := K)
    (fun x ↦ abs_fderiv_pi_single_le hK _ i) (mderivClosure P (F i))
  filter_upwards [MemLp.coeFn_toLp (memLp_grad_smul P hf hK
      (fun i ↦ Lp.aestronglyMeasurable (F i)) fun i ↦ mderivClosure P (F i)),
    Lp.coeFn_finsetSum Finset.univ (fun i ↦ boundedSMul
      (G := fun x ↦ fderiv ℝ f (fun i ↦ F i x) (Pi.single i 1))
      (memLp_fderiv_pi_comp hf hK F i).aestronglyMeasurable (C := K)
      (fun x ↦ abs_fderiv_pi_single_le hK _ i) (mderivClosure P (F i))), h2] with x h1 h2 h3
  rw [h1, h2, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i _ ↦ (h3 i).symm

/-- **The multivariate time-form chain rule**: `Dₜ f (F₁, …, Fₙ) = ∑ᵢ ∂ᵢ f (F) Dₜ Fᵢ` for
`F₁, …, Fₙ ∈ 𝔻₁,₂`. -/
theorem timeDerivative_mderivClosure_comp_pi (hB : IsPreBrownianReal B P)
    (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ}
    (hK : ∀ y, ‖fderiv ℝ f y‖ ≤ K) {F : Fin n → Lp ℝ 2 P} (hF : ∀ i, F i ∈ domD12 P) :
    timeDerivative hB L hL hgen (mderivClosure P ((memLp_comp_pi P hf hK F).toLp _)) =
      ∑ i, boundedSMul (G := fun p : ℝ≥0 × W ↦ fderiv ℝ f (fun i ↦ F i p.2) (Pi.single i 1))
          (aestronglyMeasurable_comp_snd (ν := nonnegativeLebesgueMeasure)
            (memLp_fderiv_pi_comp hf hK F i).aestronglyMeasurable) (C := K)
        (fun _ ↦ abs_fderiv_pi_single_le hK _ i)
        (timeDerivative hB L hL hgen (mderivClosure P (F i))) := by
  rw [mderivClosure_comp_pi_eq_sum_boundedSMul hf hK hF]
  have hsum := map_sum (timeDerivative hB L hL hgen).toLinearMap
    (fun i ↦ boundedSMul (G := fun x ↦ fderiv ℝ f (fun i ↦ F i x) (Pi.single i 1))
      (memLp_fderiv_pi_comp hf hK F i).aestronglyMeasurable (C := K)
      (fun x ↦ abs_fderiv_pi_single_le hK _ i) (mderivClosure P (F i))) Finset.univ
  simp only [LinearIsometry.coe_toLinearMap] at hsum
  rw [hsum]
  exact Finset.sum_congr rfl fun i _ ↦ timeDerivative_boundedSMul hB L hL hgen _ _ _

/-- The closed derivative of `f (h₁, …, hₙ)` for `hᵢ` in the Cameron--Martin space is
`∑ᵢ ∂ᵢ f (h) • hᵢ`, a sum of rank-one elements. -/
theorem mderivClosure_comp_pi_space {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ}
    (hK : ∀ y, ‖fderiv ℝ f y‖ ≤ K) (h : Fin n → Space P) :
    mderivClosure P ((memLp_comp_pi P hf hK fun i ↦ (h i : Lp ℝ 2 P)).toLp _) =
      ∑ i, smulLp (h i) ((memLp_fderiv_pi_comp hf hK (fun i ↦ (h i : Lp ℝ 2 P)) i).toLp _) := by
  rw [(comp_pi_mem_domD12 P hf hK fun i ↦ (coe_space_mem_domD12 P (h i)).1).2]
  have hc : ∀ i, (mderivClosure P (h i : Lp ℝ 2 P) : W → Space P) =ᵐ[P] fun _ ↦ h i := fun i ↦ by
    rw [(coe_space_mem_domD12 P (h i)).2, constLp_apply]
    exact Lp.coeFn_const 2 P (h i)
  apply Lp.ext
  have h4 := ae_all_iff.2 fun i ↦ coeFn_smulLp (h i)
    ((memLp_fderiv_pi_comp hf hK (fun i ↦ (h i : Lp ℝ 2 P)) i).toLp _)
  have h5 := ae_all_iff.2 fun i ↦
    MemLp.coeFn_toLp (memLp_fderiv_pi_comp hf hK (fun i ↦ (h i : Lp ℝ 2 P)) i)
  filter_upwards [MemLp.coeFn_toLp (memLp_grad_smul P hf hK
      (fun i ↦ Lp.aestronglyMeasurable (h i : Lp ℝ 2 P)) fun i ↦ mderivClosure P (h i : Lp ℝ 2 P)),
    Lp.coeFn_finsetSum Finset.univ (fun i ↦ smulLp (h i)
      ((memLp_fderiv_pi_comp hf hK (fun i ↦ (h i : Lp ℝ 2 P)) i).toLp _)),
    ae_all_iff.2 hc, h4, h5] with x h1 h2 h3 h4 h5
  rw [h1, h2, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [h4 i, h5 i, h3 i]

/-- **`Dₜ f (∫ g₁ dB, …, ∫ gₙ dB) = ∑ᵢ ∂ᵢ f (∫ g dB) gᵢ(t)`** for `f` of class `C¹` with bounded
derivative. -/
theorem timeDerivative_mderivClosure_comp_pi_wienerIntegral (hB : IsPreBrownianReal B P)
    (L : ℝ≥0 → StrongDual ℝ W) (hL : ∀ t w, B t w = L t w) (hgen : IsWienerGenerated B)
    {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ}
    (hK : ∀ y, ‖fderiv ℝ f y‖ ≤ K) (g : Fin n → Lp ℝ 2 nonnegativeLebesgueMeasure) :
    timeDerivative hB L hL hgen (mderivClosure P
        ((memLp_comp_pi P hf hK fun i ↦ wienerIntegral hB (g i)).toLp _)) =
      ∑ i, tensor (g i)
        ((memLp_fderiv_pi_comp hf hK (fun i ↦ wienerIntegral hB (g i)) i).toLp _) := by
  have hmem : ∀ i, wienerIntegral hB (g i) ∈ Space P := fun i ↦
    wienerIntegral_mem_space hB L hL hgen (g i)
  rw [mderivClosure_comp_pi_space hf hK fun i ↦ ⟨_, hmem i⟩]
  have hsum := map_sum (timeDerivative hB L hL hgen).toLinearMap
    (fun i ↦ smulLp (⟨_, hmem i⟩ : Space P)
      ((memLp_fderiv_pi_comp hf hK (fun i ↦ wienerIntegral hB (g i)) i).toLp _)) Finset.univ
  simp only [LinearIsometry.coe_toLinearMap] at hsum
  rw [hsum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [timeDerivative_smulLp hB L hL hgen]
  congr 1
  apply (wienerIntegralEquiv hB).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

end WienerSpace

end Malliavin

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
