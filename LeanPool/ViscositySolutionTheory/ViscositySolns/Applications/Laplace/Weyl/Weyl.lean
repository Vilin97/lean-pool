/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Applications.Laplace.Weyl.MeanValue

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Weyl's lemma

Let `E` be a finite-dimensional real inner product space with an additive Haar measure `μ`. A
function `u : E → ℝ` that is continuous on an open set `U` and weakly harmonic there
(`∫ Δχ · u dμ = 0` for all smooth `χ` with compact support in `U`, `WeaklyHarmonicOn`) is `C^∞`
in `U` and satisfies `Δu = 0` pointwise in `U` (`weyl_of_weaklyHarmonicOn`).

## Proof

1. *Reproduction by a radial kernel*: for a smooth radial kernel `ρ` with `∫ ρ = 1` supported in
   `closedBall 0 r` (`exists_radial_kernel`), the mean value property
   (`integral_radial_smul_eq_of_weaklyHarmonic`) gives `u = (B.indicator u) ⋆ ρ` on `ball x₀ r`,
   where `B = closedBall x₀ (2 r) ⊆ U`. The right side is `C^∞`.
2. *Harmonicity*: `Δ (f ⋆ ρ) = f ⋆ Δρ` (`laplacian_convolution`), and `(f ⋆ Δρ)(x₀) = ∫ Δψ · u`
   for the test function `ψ = ρ(· - x₀)`, which vanishes by weak harmonicity.
3. In dimension zero every function is constant.

This file imports only Mathlib and the TauCeti ports `Weyl/{LaplacianInvariance,
DuBoisReymond, PolarCoord, MeanValue}.lean`, so that it can be reused elsewhere. The mean value
property is the TauCeti port in `Weyl/MeanValue.lean`; the code in this file is new.
-/

@[expose] public section

open InnerProductSpace MeasureTheory Metric Set Filter Topology ContinuousLinearMap
open scoped ContDiff Laplacian Convolution

namespace ViscositySolns

namespace Analysis

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The Laplacian as a sum of iterated directional derivatives along an orthonormal basis. -/
theorem laplacian_eq_sum_fderiv_fderiv {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x : E) :
    Δ f x = ∑ i, fderiv ℝ (fun y ↦ fderiv ℝ f y (b i)) x (b i) := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f b]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [iteratedFDeriv_two_apply]
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- Directional derivative of a convolution with a `C¹` compactly supported kernel. -/
theorem fderiv_convolution_apply {f g : E → ℝ} (hf : LocallyIntegrable f μ)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (x v : E) :
    fderiv ℝ (f ⋆[lsmul ℝ ℝ, μ] g) x v = (f ⋆[lsmul ℝ ℝ, μ] fun y ↦ fderiv ℝ g y v) x := by
  rw [(hgc.hasFDerivAt_convolution_right (lsmul ℝ ℝ) hf hg x).fderiv]
  exact convolution_precompR_apply (𝕜 := ℝ) (L := lsmul ℝ ℝ) hf (hgc.fderiv (𝕜 := ℝ))
    (hg.continuous_fderiv (by simp)) x v

/-- `Δ (f ⋆ g) = f ⋆ Δg` for a smooth compactly supported kernel `g`. -/
theorem laplacian_convolution {f g : E → ℝ} (hf : LocallyIntegrable f μ)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (x : E) :
    Δ (f ⋆[lsmul ℝ ℝ, μ] g) x = (f ⋆[lsmul ℝ ℝ, μ] Δ g) x := by
  set b := stdOrthonormalBasis ℝ E
  have hD : ∀ h : E → ℝ, ContDiff ℝ ∞ h → HasCompactSupport h → ∀ v : E,
      ContDiff ℝ ∞ (fun y ↦ fderiv ℝ h y v) ∧ HasCompactSupport (fun y ↦ fderiv ℝ h y v) :=
    fun h hh hhc v ↦ ⟨(hh.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const,
      hhc.fderiv_apply (𝕜 := ℝ) v⟩
  have hconv : ContDiff ℝ ∞ (f ⋆[lsmul ℝ ℝ, μ] g) :=
    hgc.contDiff_convolution_right (n := ⊤) (lsmul ℝ ℝ) hf hg
  have hΔg : Δ g = fun y ↦ ∑ i, fderiv ℝ (fun z ↦ fderiv ℝ g z (b i)) y (b i) :=
    funext fun y ↦ laplacian_eq_sum_fderiv_fderiv b (hg.of_le (by norm_cast)) y
  rw [laplacian_eq_sum_fderiv_fderiv b (hconv.of_le (by norm_cast)) x, hΔg]
  -- the convolution of a finite sum
  have hsum : (f ⋆[lsmul ℝ ℝ, μ] fun y ↦ ∑ i, fderiv ℝ (fun z ↦ fderiv ℝ g z (b i)) y (b i)) x =
      ∑ i, (f ⋆[lsmul ℝ ℝ, μ] fun y ↦ fderiv ℝ (fun z ↦ fderiv ℝ g z (b i)) y (b i)) x := by
    simp only [convolution_def, lsmul_apply, smul_eq_mul, Finset.mul_sum]
    refine integral_finsetSum _ fun i _ ↦ ?_
    obtain ⟨h1, h1c⟩ := hD g hg hgc (b i)
    obtain ⟨h2, h2c⟩ := hD _ h1 h1c (b i)
    exact h2c.convolutionExists_right (lsmul ℝ ℝ) hf h2.continuous x
  rw [hsum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  obtain ⟨h1, h1c⟩ := hD g hg hgc (b i)
  have hfun : (fun y ↦ fderiv ℝ (f ⋆[lsmul ℝ ℝ, μ] g) y (b i)) =
      f ⋆[lsmul ℝ ℝ, μ] fun y ↦ fderiv ℝ g y (b i) :=
    funext fun y ↦ fderiv_convolution_apply hf (hg.of_le (by exact_mod_cast le_top)) hgc y (b i)
  rw [hfun, fderiv_convolution_apply hf (h1.of_le (by exact_mod_cast le_top)) h1c x (b i)]

variable (μ) in
/-- A smooth radial kernel of integral one: `g` is smooth, vanishes on `[r², ∞)`, and
`∫ g (‖y‖²) dμ = 1`. -/
theorem exists_radial_kernel {r : ℝ} (hr : 0 < r) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ (∀ t, r ^ 2 ≤ t → g t = 0) ∧ ∫ y, g (‖y‖ ^ 2) ∂μ = 1 := by
  set h : E → ℝ := fun y ↦ expNegInvGlue (r ^ 2 - ‖y‖ ^ 2) with hh
  have hhc : HasCompactSupport h := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : E) r) fun y hy ↦ ?_
    rw [mem_closedBall_zero_iff, not_le] at hy
    exact expNegInvGlue.zero_of_nonpos (by nlinarith [norm_nonneg y])
  have hcont : Continuous h :=
    (expNegInvGlue.contDiff (n := 0)).continuous.comp (by fun_prop)
  have hpos : 0 < ∫ y, h y ∂μ :=
    hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hhc
      (fun y ↦ expNegInvGlue.nonneg _) (x := 0) (by
        simp only [hh, norm_zero]
        exact (expNegInvGlue.pos_of_pos (by nlinarith)).ne')
  refine ⟨fun t ↦ (∫ y, h y ∂μ)⁻¹ * expNegInvGlue (r ^ 2 - t), ?_, fun t ht ↦ ?_, ?_⟩
  · exact contDiff_const.mul (expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id))
  · simp [expNegInvGlue.zero_of_nonpos (sub_nonpos.mpr ht)]
  · rw [integral_const_mul]
    exact inv_mul_cancel₀ hpos.ne'

/-- **Local Weyl lemma.** A continuous weakly harmonic function agrees near each point of `U`
with a smooth function whose Laplacian vanishes at that point. -/
theorem exists_contDiff_eventuallyEq_laplacian_eq_zero [Nontrivial E] {U : Set E} {u : E → ℝ}
    (hU : IsOpen U) (hcont : ContinuousOn u U) (hu : WeaklyHarmonicOn μ u U) {x₀ : E}
    (hx₀ : x₀ ∈ U) :
    ∃ w : E → ℝ, ContDiff ℝ ∞ w ∧ u =ᶠ[𝓝 x₀] w ∧ Δ w x₀ = 0 := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  set r := ε / 3 with hr_def
  have hr : 0 < r := by positivity
  set B := closedBall x₀ (2 * r) with hB_def
  have hBU : B ⊆ U := (closedBall_subset_ball (by linarith)).trans hεU
  obtain ⟨g, hg, hg0, hg1⟩ := exists_radial_kernel μ hr
  set ρ : E → ℝ := fun y ↦ g (‖y‖ ^ 2) with hρ_def
  have hρ : ContDiff ℝ ∞ ρ := hg.comp (contDiff_norm_sq ℝ)
  have hρ0 : ∀ y, r < ‖y‖ → ρ y = 0 := fun y hy ↦
    hg0 _ (pow_le_pow_left₀ hr.le hy.le 2)
  have hρc : HasCompactSupport ρ :=
    HasCompactSupport.intro (isCompact_closedBall (0 : E) r) fun y hy ↦
      hρ0 y (by rwa [mem_closedBall_zero_iff, not_le] at hy)
  set f := B.indicator u with hf_def
  have hf : LocallyIntegrable f μ :=
    (((hcont.mono hBU).integrableOn_compact (isCompact_closedBall _ _)).integrable_indicator
      measurableSet_closedBall).locallyIntegrable
  refine ⟨f ⋆[lsmul ℝ ℝ, μ] ρ, hρc.contDiff_convolution_right (n := ⊤) (lsmul ℝ ℝ) hf hρ,
    ?_, ?_⟩
  · -- reproduction by the kernel, via the mean value property
    filter_upwards [ball_mem_nhds x₀ hr] with x hx
    have hxB : closedBall x r ⊆ B := closedBall_subset_closedBall' (by
      rw [mem_ball] at hx
      linarith)
    have hk : Continuous fun s : ℝ ↦ g (s ^ 2) := hg.continuous.comp (continuous_pow 2)
    have hmvp := integral_radial_smul_eq_of_weaklyHarmonic hU hcont hu (hxB.trans hBU) hk
      (fun s hs ↦ hg0 _ (pow_le_pow_left₀ hr.le hs.le 2))
    rw [hg1, one_smul] at hmvp
    rw [← hmvp, convolution_def]
    conv_rhs => rw [← integral_add_left_eq_self _ x]
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    simp only [lsmul_apply, smul_eq_mul, sub_add_cancel_left, norm_neg, hρ_def]
    by_cases hy : ‖y‖ ≤ r
    · rw [hf_def, indicator_of_mem (hxB (by simpa [mem_closedBall, dist_eq_norm] using hy)),
        mul_comm]
    · have := hg0 (‖y‖ ^ 2) (pow_le_pow_left₀ hr.le (not_le.mp hy).le 2)
      simp [this]
  · -- harmonicity of the mollification at `x₀`
    set ψ : E → ℝ := fun t ↦ ρ (t + -x₀) with hψ_def
    have hψ : ContDiff ℝ ∞ ψ := hρ.comp (contDiff_id.add contDiff_const)
    have hψc : HasCompactSupport ψ := hρc.comp_homeomorph (Homeomorph.addRight (-x₀))
    have hψs : tsupport ψ ⊆ closedBall x₀ r := by
      refine closure_minimal (fun t ht ↦ ?_) isClosed_closedBall
      by_contra h
      rw [mem_closedBall, dist_eq_norm, not_le, sub_eq_add_neg] at h
      exact ht (hρ0 _ h)
    have hball : closedBall x₀ r ⊆ B := closedBall_subset_closedBall (by linarith)
    have hweak := hu ψ hψ hψc (hψs.trans (hball.trans hBU))
    have hΔψ : Δ ψ = fun t ↦ Δ ρ (t + -x₀) := laplacian_comp_add_right ρ (-x₀)
    have hΔρ : ∀ y, Δ ρ y = 4 * ‖y‖ ^ 2 * deriv (deriv g) (‖y‖ ^ 2) +
        2 * (Module.finrank ℝ E : ℝ) * deriv g (‖y‖ ^ 2) :=
      fun y ↦ (hg.of_le (by norm_cast)).laplacian_comp_norm_sq y
    rw [laplacian_convolution hf hρ hρc, convolution_def, ← hweak]
    refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
    simp only [lsmul_apply, smul_eq_mul]
    by_cases ht : t ∈ B
    · rw [hf_def, indicator_of_mem ht]
      simp only [hΔψ]
      rw [hΔρ, hΔρ, ← sub_eq_add_neg, norm_sub_rev, mul_comm]
    · have h0 : Δ ψ t = 0 := image_eq_zero_of_notMem_tsupport fun h ↦
        ht (hball (hψs (tsupport_laplacian_subset _ h)))
      rw [hf_def, indicator_of_notMem ht, h0, zero_mul, zero_mul]

/-- **Weyl's lemma.** A continuous weakly harmonic function on an open set `U` is `C^∞` in `U`
and classically harmonic there. -/
theorem weyl_of_weaklyHarmonicOn {U : Set E} {u : E → ℝ} (hU : IsOpen U)
    (hcont : ContinuousOn u U) (hu : WeaklyHarmonicOn μ u U) :
    ContDiffOn ℝ ∞ u U ∧ ∀ x ∈ U, Δ u x = 0 := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- in dimension zero every function is constant
    have hconst : u = fun _ ↦ u 0 := funext fun x ↦ congrArg u (Subsingleton.elim x 0)
    rw [hconst]
    exact ⟨contDiffOn_const, fun x _ ↦ by simp⟩
  · refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩ <;>
      obtain ⟨w, hw, huw, hΔ⟩ := exists_contDiff_eventuallyEq_laplacian_eq_zero hU hcont hu hx
    · exact (hw.contDiffAt.congr_of_eventuallyEq huw).contDiffWithinAt
    · rw [(laplacian_congr_nhds huw).eq_of_nhds]
      exact hΔ

end General

end Analysis

end ViscositySolns
