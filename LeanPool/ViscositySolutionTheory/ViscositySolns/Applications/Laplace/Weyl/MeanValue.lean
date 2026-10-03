/-
Copyright (c) 2026 The Tau Ceti contributors, William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Applications.Laplace.Weyl.DuBoisReymond
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Applications.Laplace.Weyl.LaplacianInvariance
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Applications.Laplace.Weyl.PolarCoord

/-!
# The mean-value property of continuous weakly harmonic functions

Let `E` be a nontrivial finite-dimensional real inner product space with an additive Haar measure
`μ`, `U ⊆ E` open, and `u : E → F` continuous on `U` and **weakly harmonic** in `U`:
`∫ Δχ • u ∂μ = 0` for every smooth `χ` with compact support in `U`. If `closedBall x₀ R ⊆ U`,
then `u x₀` is the average of `u` over the sphere of radius `R` about `x₀`:

`∫ θ ∈ S, u (x₀ + R • θ) ∂μ.toSphere = μ.toSphere(S) • u x₀`
(`integral_toSphere_eq_of_weaklyHarmonic`).

As a consequence, integrating against a radial kernel `k (‖y‖)` supported in `closedBall 0 R`
reproduces `u x₀` (`integral_radial_smul_eq_of_weaklyHarmonic`):
`∫ k ‖y‖ • u (x₀ + y) ∂μ = (∫ k ‖y‖ ∂μ) • u x₀`.

## The argument (TauCeti)

Write `Φ s = ∫ θ ∈ S, u (s • θ) ∂μ.toSphere`. For a test function `ψ` on `(0, R)`, the radial
test function `χ x = ρ (‖x‖²)`, with `ρ` the primitive of `t ↦ ψ (√t) / (√t) ^ n`, has
`Δχ x = 4 ‖x‖² ρ'' (‖x‖²) + 2 n ρ' (‖x‖²)`. In polar coordinates the weak harmonicity
`∫ Δχ • u = 0` becomes `∫ 2 ψ' • Φ = 0`, so `Φ` is constant on `(0, R)` by the du Bois-Reymond
lemma, and `Φ R = Φ 0 = μ.toSphere(S) • u 0` by continuity. No divergence theorem is needed.

## Provenance

Pool port: imports relocated under `LeanPool.ViscositySolutionTheory`; original
mathematical namespaces and copyright retained; checked with Lean/Mathlib v4.34.0.


* Upstream: TauCeti, https://github.com/TauCetiProject/TauCeti
* Path: `TauCeti/Analysis/InnerProductSpace/Harmonic/MeanValue.lean`
* Commit: 91f66a0514e6523efdccddb9e35fb82c96dd6405 (2026-09-24)
* License: Apache-2.0. Upstream `NOTICE`: none.
* Upstream notice: `Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.`;
  upstream authors: The Tau Ceti contributors.
* Extent: `integral_deriv_smul_integral_toSphere_eq_zero` and
  `integral_toSphere_eq_of_harmonicOnNhd_zero` (adapted), `HarmonicOnNhd.integral_toSphere_eq`
  (adapted as `integral_toSphere_eq_of_weaklyHarmonic`).
* Changes: ported from Lean v4.34.0-rc2 to Lean/Mathlib v4.30.0; `module`/`public import`
  removed; namespace `TauCeti` → `ViscositySolns.Analysis`. The hypothesis "`u` harmonic on a
  neighbourhood of the closed ball" is replaced by "`u` continuous and weakly harmonic on an open
  set containing the closed ball" (upstream derives weak harmonicity from harmonicity via
  `HarmonicOnNhd.integral_laplacian_smul_eq_zero`; here it is the hypothesis), test functions
  `𝓓(Ω, ℝ)` are replaced by smooth compactly supported functions, and the recentring uses
  translation invariance of the weak formulation instead of upstream's
  `harmonicOnNhd_comp_add_right_closedBall_zero_iff`. The ball forms are not ported. New
  (W. M. Feldman): `weaklyHarmonic_comp_add_right`, `integral_radial_smul_eq_of_weaklyHarmonic`.
-/

@[expose] public section

open InnerProductSpace MeasureTheory Metric Set Filter Topology
open scoped ContDiff Laplacian

namespace ViscositySolns

namespace Analysis

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {u : E → F} {R : ℝ} {U : Set E}

/-- `u` is weakly harmonic in `U` (for the measure `μ`): `∫ Δχ • u ∂μ = 0` for every smooth
`χ : E → ℝ` with compact support in `U`. -/
def WeaklyHarmonicOn (μ : Measure E) (u : E → F) (U : Set E) : Prop :=
  ∀ χ : E → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ U →
    ∫ x, Δ χ x • u x ∂μ = 0

omit [CompleteSpace F] in
/-- Weak harmonicity is translation invariant. -/
theorem weaklyHarmonic_comp_add_right (hu : WeaklyHarmonicOn μ u U) (x₀ : E) :
    WeaklyHarmonicOn μ (fun y ↦ u (y + x₀)) ((· + x₀) ⁻¹' U) := by
  intro χ hχ hχc hχU
  set χ' : E → ℝ := fun z ↦ χ (z + -x₀) with hχ'_def
  have hχ' : ContDiff ℝ ∞ χ' := hχ.comp (contDiff_id.add contDiff_const)
  have htsupp : tsupport χ' = (· + -x₀) ⁻¹' tsupport χ :=
    tsupport_comp_eq_preimage χ (Homeomorph.addRight (-x₀))
  have hχ'c : HasCompactSupport χ' := hχc.comp_homeomorph (Homeomorph.addRight (-x₀))
  have hχ'U : tsupport χ' ⊆ U := by
    rw [htsupp]
    intro z hz
    simpa using hχU hz
  have h := hu χ' hχ' hχ'c hχ'U
  rw [hχ'_def, laplacian_comp_add_right χ (-x₀)] at h
  rw [← integral_add_right_eq_self _ x₀] at h
  simpa using h

variable [Nontrivial E]

omit [CompleteSpace F] in
/-- The distributional derivative of the sphere integrals `s ↦ ∫ θ, u (s • θ) ∂μ.toSphere` of a
continuous weakly harmonic function vanishes on `(0, R)`: `∫ ψ' • Φ = 0` for every test function
`ψ` on `(0, R)`. -/
theorem integral_deriv_smul_integral_toSphere_eq_zero (hU : IsOpen U)
    (hcont : ContinuousOn u U) (hu : WeaklyHarmonicOn μ u U) (hΩ : closedBall (0 : E) R ⊆ U)
    (hR : 0 < R) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψs : tsupport ψ ⊆ Ioo 0 R) :
    ∫ s, deriv ψ s • ∫ θ : sphere (0 : E) 1, u (s • (θ : E)) ∂μ.toSphere = 0 := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_one_of_ne_zero (Module.finrank_pos (R := ℝ) (M := E)).ne'
  have hψ0 : ∀ r, r ∉ Ioo (0 : ℝ) R → ψ r = 0 := fun r hr ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ hr (hψs h)
  -- The radial profile `σ`, chosen so that `ψ s = s ^ n * σ (s ^ 2)` for `s > 0`.
  set σ : ℝ → ℝ := fun t ↦ ψ (√t) / (√t) ^ Module.finrank ℝ E with hσ_def
  have hσ0 : ∀ t, R ^ 2 ≤ t → σ t = 0 := by
    intro t ht
    have : R ≤ √t := by
      rw [← Real.sqrt_sq hR.le]
      exact Real.sqrt_le_sqrt ht
    simp [hσ_def, hψ0 (√t) fun h ↦ h.2.not_ge this]
  have hσ : ContDiff ℝ ∞ σ := by
    rw [contDiff_iff_contDiffAt]
    intro t
    by_cases ht : √t ∈ tsupport ψ
    · have ht0 : 0 < t := Real.sqrt_pos.mp (hψs ht).1
      exact ((hψ.contDiffAt.comp t (Real.contDiffAt_sqrt ht0.ne')).div
        ((Real.contDiffAt_sqrt ht0.ne').pow _) (pow_ne_zero _ (Real.sqrt_pos.mpr ht0).ne'))
    · have hev : ∀ᶠ s in 𝓝 t, σ s = 0 := by
        have : ∀ᶠ s in 𝓝 t, √s ∉ tsupport ψ :=
          Real.continuous_sqrt.continuousAt.preimage_mem_nhds
            ((isClosed_tsupport ψ).isOpen_compl.mem_nhds ht)
        filter_upwards [this] with s hs
        simp [hσ_def, image_eq_zero_of_notMem_tsupport hs]
      exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev
  have hσc : Continuous σ := hσ.continuous
  -- Its primitive `ρ`, vanishing beyond `R ^ 2`.
  set ρ : ℝ → ℝ := fun t ↦ ∫ s in R ^ 2..t, σ s with hρ_def
  have hρderiv : ∀ t, HasDerivAt ρ (σ t) t := fun t ↦
    intervalIntegral.integral_hasDerivAt_right (hσc.intervalIntegrable _ _)
      (hσc.stronglyMeasurableAtFilter _ _) hσc.continuousAt
  have hρ' : deriv ρ = σ := funext fun t ↦ (hρderiv t).deriv
  have hρ : ContDiff ℝ ∞ ρ :=
    contDiff_infty_iff_deriv.mpr ⟨fun t ↦ (hρderiv t).differentiableAt, hρ' ▸ hσ⟩
  have hρ0 : ∀ t, R ^ 2 ≤ t → ρ t = 0 := by
    intro t ht
    simp only [hρ_def]
    refine (intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun s hs ↦ ?_).trans
      intervalIntegral.integral_zero
    rw [uIcc_of_le ht] at hs
    exact hσ0 s hs.1
  -- The radial test function `χ x = ρ (‖x‖ ^ 2)`, supported in the closed ball.
  set χ : E → ℝ := fun x ↦ ρ (‖x‖ ^ 2) with hχ
  have hχ_supp : tsupport χ ⊆ closedBall (0 : E) R := by
    refine (closure_mono fun x hx ↦ ?_).trans closure_ball_subset_closedBall
    rw [mem_ball_zero_iff]
    by_contra h
    exact hx (hρ0 _ (pow_le_pow_left₀ hR.le (not_lt.mp h) 2))
  have hχs : ContDiff ℝ ∞ χ := hρ.comp (contDiff_norm_sq ℝ)
  have hχc : HasCompactSupport χ :=
    (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) hχ_supp
  have hΔ : Δ χ = fun x ↦
      4 * ‖x‖ ^ 2 * deriv σ (‖x‖ ^ 2) + 2 * (Module.finrank ℝ E : ℝ) * σ (‖x‖ ^ 2) := by
    funext x
    rw [hχ, (hρ.of_le (by norm_cast)).laplacian_comp_norm_sq, hρ']
  -- Weak harmonicity against `χ`, in polar coordinates.
  have hgreen := hu χ hχs hχc (hχ_supp.trans hΩ)
  have hΔcont : Continuous (Δ χ) := by
    rw [hΔ]
    have hσ' : Continuous (deriv σ) := hσ.continuous_deriv (by simp)
    fun_prop
  have hf_cont : Continuous fun x ↦ Δ χ x • u x :=
    (hΔcont.continuousOn.smul hcont).continuous_of_tsupport_subset hU
      ((tsupport_smul_subset_left _ _).trans
        ((tsupport_laplacian_subset _).trans (hχ_supp.trans hΩ)))
  have hf_supp : HasCompactSupport fun x ↦ Δ χ x • u x :=
    (HasCompactSupport.intro hχc fun x hx ↦
      image_eq_zero_of_notMem_tsupport fun h ↦ hx (tsupport_laplacian_subset _ h)).smul_right
  rw [integral_eq_integral_Ioi_integral_toSphere _
    (hf_cont.integrable_of_hasCompactSupport hf_supp)] at hgreen
  -- On the sphere of radius `s`, the weight is `2 ψ' s`.
  have hinner : ∀ s ∈ Ioi (0 : ℝ), s ^ (Module.finrank ℝ E - 1) •
      ∫ θ : sphere (0 : E) 1, Δ χ (s • (θ : E)) • u (s • (θ : E)) ∂μ.toSphere =
        (2 * deriv ψ s) • ∫ θ : sphere (0 : E) 1, u (s • (θ : E)) ∂μ.toSphere := by
    intro s hs
    have hs : 0 < s := hs
    have hnorm : ∀ θ : sphere (0 : E) 1, ‖s • (θ : E)‖ = s := fun θ ↦ by
      rw [norm_smul, norm_eq_of_mem_sphere θ, mul_one, Real.norm_of_nonneg hs.le]
    have hΔs : ∀ θ : sphere (0 : E) 1, Δ χ (s • (θ : E)) =
        4 * s ^ 2 * deriv σ (s ^ 2) + 2 * (Module.finrank ℝ E : ℝ) * σ (s ^ 2) := fun θ ↦ by
      rw [hΔ]
      dsimp only
      rw [hnorm]
    simp_rw [hΔs]
    rw [MeasureTheory.integral_smul, smul_smul]
    congr 1
    have hψeq : ψ =ᶠ[𝓝 s] fun r ↦ r ^ Module.finrank ℝ E * σ (r ^ 2) := by
      filter_upwards [Ioi_mem_nhds hs] with r hr
      have hr : 0 < r := hr
      simp only [hσ_def, Real.sqrt_sq hr.le]
      rw [mul_div_cancel₀ _ (pow_ne_zero _ hr.ne')]
    have hd : HasDerivAt (fun r ↦ r ^ Module.finrank ℝ E * σ (r ^ 2))
        ((Module.finrank ℝ E : ℝ) * s ^ (Module.finrank ℝ E - 1) * σ (s ^ 2) +
          s ^ Module.finrank ℝ E * (deriv σ (s ^ 2) * ((2 : ℕ) * s ^ (2 - 1)))) s :=
      (hasDerivAt_pow _ s).mul ((hσ.differentiable (by simp) _).hasDerivAt.comp s
        (hasDerivAt_pow 2 s))
    rw [hψeq.deriv_eq, hd.deriv, hm]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hinner,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs ↦ ?_] at hgreen
  · simp_rw [mul_smul] at hgreen
    rw [MeasureTheory.integral_smul] at hgreen
    exact (smul_eq_zero.mp hgreen).resolve_left two_ne_zero
  · have : deriv ψ s = 0 := by
      by_contra h
      exact hs (hψs (support_deriv_subset h)).1
    simp [this]

/-- The mean-value property on spheres about the origin. -/
theorem integral_toSphere_eq_of_weaklyHarmonic_zero (hU : IsOpen U)
    (hcont : ContinuousOn u U) (hu : WeaklyHarmonicOn μ u U) (hΩ : closedBall (0 : E) R ⊆ U)
    (hR : 0 ≤ R) :
    ∫ θ : sphere (0 : E) 1, u (R • (θ : E)) ∂μ.toSphere = μ.toSphere.real univ • u 0 := by
  rcases hR.eq_or_lt with rfl | hR
  · simp [integral_const]
  set Φ : ℝ → F := fun s ↦ ∫ θ : sphere (0 : E) 1, u (s • (θ : E)) ∂μ.toSphere with hΦ_def
  have hΦc : ContinuousOn Φ (Icc 0 R) := continuousOn_integral_toSphere_smul (hcont.mono hΩ)
  obtain ⟨c, hc⟩ :=
    exists_eqOn_const_Ioo_of_integral_deriv_smul_eq_zero (hΦc.mono Ioo_subset_Icc_self)
      fun ψ hψ hψs ↦ integral_deriv_smul_integral_toSphere_eq_zero hU hcont hu hΩ hR hψ hψs
  have hIcc : EqOn Φ (fun _ ↦ c) (Icc 0 R) :=
    hc.of_subset_closure hΦc continuousOn_const Ioo_subset_Icc_self (by rw [closure_Ioo hR.ne])
  calc Φ R = c := hIcc ⟨hR.le, le_rfl⟩
    _ = Φ 0 := (hIcc ⟨le_rfl, hR.le⟩).symm
    _ = μ.toSphere.real univ • u 0 := by simp [hΦ_def, integral_const]

/-- **The mean-value property on spheres** for a continuous weakly harmonic function: if
`closedBall x₀ R ⊆ U` and `0 ≤ R`, the integral of `u` over the sphere of radius `R` about `x₀`,
parametrized by the unit sphere with the surface measure `μ.toSphere`, is the total surface
measure times `u x₀`. -/
theorem integral_toSphere_eq_of_weaklyHarmonic (hU : IsOpen U) (hcont : ContinuousOn u U)
    (hu : WeaklyHarmonicOn μ u U) {x₀ : E} (hΩ : closedBall x₀ R ⊆ U) (hR : 0 ≤ R) :
    ∫ θ : sphere (0 : E) 1, u (x₀ + R • (θ : E)) ∂μ.toSphere = μ.toSphere.real univ • u x₀ := by
  have hU' : IsOpen ((· + x₀) ⁻¹' U) := hU.preimage (continuous_id.add continuous_const)
  have hcont' : ContinuousOn (fun y ↦ u (y + x₀)) ((· + x₀) ⁻¹' U) :=
    hcont.comp (continuous_id.add continuous_const).continuousOn fun y hy ↦ hy
  have hΩ' : closedBall (0 : E) R ⊆ (· + x₀) ⁻¹' U := fun y hy ↦ hΩ (by
    rw [mem_closedBall, dist_eq_norm] at hy ⊢
    simpa using hy)
  have h := integral_toSphere_eq_of_weaklyHarmonic_zero hU' hcont'
    (weaklyHarmonic_comp_add_right hu x₀) hΩ' hR
  simpa [add_comm] using h

/-- **Reproduction by radial kernels.** If `u` is continuous and weakly harmonic in `U`,
`closedBall x₀ R ⊆ U`, and `k : ℝ → ℝ` is continuous and vanishes on `(R, ∞)`, then
`∫ k ‖y‖ • u (x₀ + y) ∂μ = (∫ k ‖y‖ ∂μ) • u x₀`. -/
theorem integral_radial_smul_eq_of_weaklyHarmonic (hU : IsOpen U) (hcont : ContinuousOn u U)
    (hu : WeaklyHarmonicOn μ u U) {x₀ : E} (hΩ : closedBall x₀ R ⊆ U) {k : ℝ → ℝ}
    (hk : Continuous k) (hkR : ∀ r, R < r → k r = 0) :
    ∫ y, k ‖y‖ • u (x₀ + y) ∂μ = (∫ y, k ‖y‖ ∂μ) • u x₀ := by
  have hsupp : ∀ y : E, k ‖y‖ ≠ 0 → y ∈ closedBall (0 : E) R := fun y hy ↦ by
    rw [mem_closedBall_zero_iff]
    by_contra h
    exact hy (hkR _ (not_le.mp h))
  have hkc : HasCompactSupport fun y : E ↦ k ‖y‖ :=
    HasCompactSupport.intro (isCompact_closedBall (0 : E) R) fun y hy ↦ by
      by_contra h
      exact hy (hsupp y h)
  have hki : Integrable (fun y : E ↦ k ‖y‖) μ :=
    (hk.comp continuous_norm).integrable_of_hasCompactSupport hkc
  -- `y ↦ k ‖y‖ • u (x₀ + y)` is continuous with compact support.
  have hU' : IsOpen ((x₀ + ·) ⁻¹' U) := hU.preimage (continuous_const.add continuous_id)
  have hcont' : ContinuousOn (fun y ↦ u (x₀ + y)) ((x₀ + ·) ⁻¹' U) :=
    hcont.comp (continuous_const.add continuous_id).continuousOn fun y hy ↦ hy
  have htsupp : tsupport (fun y : E ↦ k ‖y‖) ⊆ (x₀ + ·) ⁻¹' U := by
    refine (closure_minimal (fun y hy ↦ hsupp y hy) isClosed_closedBall).trans fun y hy ↦ hΩ ?_
    rw [mem_closedBall, dist_eq_norm]
    simpa using hy
  have hfi : Integrable (fun y ↦ k ‖y‖ • u (x₀ + y)) μ :=
    (((hk.comp continuous_norm).continuousOn.smul hcont').continuous_of_tsupport_subset hU'
      ((tsupport_smul_subset_left _ _).trans htsupp)).integrable_of_hasCompactSupport
      hkc.smul_right
  rw [integral_eq_integral_Ioi_integral_toSphere _ hfi,
    integral_eq_integral_Ioi_integral_toSphere _ hki, ← integral_smul_const]
  refine setIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) ↦ ?_
  have hnorm : ∀ θ : sphere (0 : E) 1, ‖s • (θ : E)‖ = s := fun θ ↦ by
    rw [norm_smul, norm_eq_of_mem_sphere θ, mul_one, Real.norm_of_nonneg hs.le]
  simp only [hnorm, MeasureTheory.integral_smul, integral_const, smul_eq_mul, smul_smul]
  by_cases hsR : s ≤ R
  · have hball : closedBall x₀ s ⊆ U := (closedBall_subset_closedBall hsR).trans hΩ
    rw [integral_toSphere_eq_of_weaklyHarmonic hU hcont hu hball hs.le, smul_smul]
    ring_nf
  · rw [hkR s (not_le.mp hsR)]
    simp

end Analysis

end ViscositySolns
