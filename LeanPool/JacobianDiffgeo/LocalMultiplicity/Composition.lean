/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

/-
Blueprint unit: local-multiplicity (CC4). Composition law and multiplicity-one criteria.
-/
import LeanPool.JacobianDiffgeo.LocalMultiplicity.AdaptedCharts
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Composition law and multiplicity-one criteria

* `RS.multiplicityENat_comp` / `RS.multiplicity_comp` — multiplicities multiply under
  composition: `mult (G ∘ F) x = mult G (F x) * mult F x` (the ℕ version is junk-robust
  thanks to `ENat.toNat_mul`).
* `RS.multiplicityENat_comp_chart_symm` (+ ℕ version) — precomposition with an admissible
  chart does not change the multiplicity.
* `RS.multiplicity_eq_one_iff_injOn` — `mult = 1` iff `F` is injective near `x`;
  `RS.exists_openPartialHomeomorph_of_multiplicity_eq_one` — `mult = 1` gives a local
  homeomorphism agreeing with `F` (Forster 2.5 germ); `RS.isRamifiedAt_iff_not_injOn`.
* `RS.eventually_multiplicity_eq_one` — ramification is isolated: near `x` (off `x`),
  `mult F y = 1` (mapping-degree's "critical values are discrete" seed).
-/

open Filter Set OpenPartialHomeomorph Metric
open scoped ContDiff Manifold Topology

namespace RS

variable {X Y Z : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [TopologicalSpace Z] [ChartedSpace ℂ Z]

section Composition

/-- Multiplicities multiply under composition (ℕ∞ version; honest, no junk interference). -/
theorem multiplicityENat_comp {G : Y → Z} {F : X → Y} {x : X}
    (hG : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω G (F x)) (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x) :
    multiplicityENat (G ∘ F) x = multiplicityENat G (F x) * multiplicityENat F x := by
  obtain ⟨hFc, hFa⟩ := LMCompat.contMDiffAt_iff_analyticAt_inChartAt.mp hF
  obtain ⟨-, hGa⟩ := LMCompat.contMDiffAt_iff_analyticAt_inChartAt.mp hG
  have hxc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have hxc' : F x ∈ (chartAt ℂ (F x)).source := mem_chart_source ℂ (F x)
  -- the uncentered composite of `F` in the standard charts
  set g : ℂ → ℂ := fun z ↦ chartAt ℂ (F x) (F ((chartAt ℂ x).symm z)) with hg_def
  have hg : AnalyticAt ℂ g (chartAt ℂ x x) := analyticAt_inChartAt_iff.mp hFa
  have hgz₀ : g (chartAt ℂ x x) = chartAt ℂ (F x) (F x) := by
    rw [hg_def]
    simp only
    rw [(chartAt ℂ x).left_inv hxc]
  -- the middle charts cancel on a neighborhood of the base point
  have hev : inChartAt (G ∘ F) x =ᶠ[𝓝 (chartAt ℂ x x)] (inChartAt G (F x)) ∘ g := by
    have hcF : ContinuousAt (F ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) := by
      apply ContinuousAt.comp ?_
        ((chartAt ℂ x).continuousAt_symm ((chartAt ℂ x).map_source hxc))
      rw [(chartAt ℂ x).left_inv hxc]
      exact hFc
    have h2 : ∀ᶠ z in 𝓝 (chartAt ℂ x x),
        F ((chartAt ℂ x).symm z) ∈ (chartAt ℂ (F x)).source := by
      apply hcF.preimage_mem_nhds
      simp only [Function.comp_apply]
      rw [(chartAt ℂ x).left_inv hxc]
      exact (chartAt ℂ (F x)).open_source.mem_nhds hxc'
    filter_upwards [h2] with z h2z
    simp only [inChartAt, Function.comp_apply, hg_def]
    rw [(chartAt ℂ (F x)).left_inv h2z]
  calc multiplicityENat (G ∘ F) x
      = analyticOrderAt ((inChartAt G (F x)) ∘ g) (chartAt ℂ x x) :=
        analyticOrderAt_congr hev
    _ = analyticOrderAt (inChartAt G (F x)) (g (chartAt ℂ x x))
          * analyticOrderAt (fun z ↦ g z - g (chartAt ℂ x x)) (chartAt ℂ x x) := by
        refine AnalyticAt.analyticOrderAt_comp ?_ hg
        rw [hgz₀]
        exact hGa
    _ = multiplicityENat G (F x) * multiplicityENat F x := by
        congr 1
        · rw [hgz₀, multiplicityENat_def]
        · rw [multiplicityENat_def]
          apply analyticOrderAt_congr
          apply Eventually.of_forall
          intro z
          rw [hgz₀]
          simp only [inChartAt, hg_def]

/-- Multiplicities multiply under composition (ℕ version; junk-robust thanks to
`ENat.toNat_mul`). -/
theorem multiplicity_comp {G : Y → Z} {F : X → Y} {x : X}
    (hG : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω G (F x)) (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x) :
    multiplicity (G ∘ F) x = multiplicity G (F x) * multiplicity F x := by
  simp only [multiplicity_def, multiplicityENat_comp hG hF, ENat.toNat_mul]

end Composition

section ChartPrecomposition

variable [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]

/-- Behavior under precomposition with charts: reading a map through any admissible chart
does not change the multiplicity. (`F ∘ e.symm : ℂ → Y`, multiplicity at a planar point.) -/
theorem multiplicityENat_comp_chart_symm {F : X → Y}
    {e : OpenPartialHomeomorph X ℂ} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X)
    {z : ℂ} (hz : z ∈ e.target) (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F (e.symm z)) :
    multiplicityENat (F ∘ e.symm) z = multiplicityENat F (e.symm z) := by
  have hinv := analyticOrderAt_charts_eq_multiplicityENat hF he (e.map_target hz)
    (IsManifold.chart_mem_maximalAtlas (F (e.symm z))) (mem_chart_source ℂ (F (e.symm z)))
  rw [e.right_inv hz] at hinv
  rw [← hinv]
  rfl

/-- ℕ version of `multiplicityENat_comp_chart_symm`. -/
theorem multiplicity_comp_chart_symm {F : X → Y}
    {e : OpenPartialHomeomorph X ℂ} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X)
    {z : ℂ} (hz : z ∈ e.target) (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F (e.symm z)) :
    multiplicity (F ∘ e.symm) z = multiplicity F (e.symm z) := by
  simp only [multiplicity_def, multiplicityENat_comp_chart_symm he hz hF]

end ChartPrecomposition

section MultiplicityOne

variable [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]

variable {F : X → Y} {x : X}

/-- `multiplicity = 1` ↔ local injectivity (Forster 2.5 direction of the normal form). -/
theorem multiplicity_eq_one_iff_injOn (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x)
    (hnc : ¬ EventuallyConst F (𝓝 x)) :
    multiplicity F x = 1 ↔ ∃ U ∈ 𝓝 x, Set.InjOn F U := by
  constructor
  · -- in adapted charts `F` is `z ↦ z ^ 1`, hence injective on the chart source
    intro h1
    obtain ⟨A, -⟩ := exists_adaptedChartsAt hF hnc univ_mem
    rw [h1] at A
    refine ⟨A.e.source, A.e.open_source.mem_nhds A.mem_source, ?_⟩
    intro z₁ hz₁ z₂ hz₂ hFz
    apply A.e.injOn hz₁ hz₂
    have h₁ := A.eqOn_pow z₁ hz₁
    have h₂ := A.eqOn_pow z₂ hz₂
    rw [pow_one] at h₁ h₂
    rw [← h₁, ← h₂, hFz]
  · -- if `k ≥ 2`, a primitive `k`-th root of unity produces two nearby points in the same fibre
    rintro ⟨U, hU, hinj⟩
    by_contra hne
    have hk1 : 1 ≤ multiplicity F x := one_le_multiplicity hF hnc
    have hk2 : 1 < multiplicity F x := by omega
    have hk0 : multiplicity F x ≠ 0 := by omega
    obtain ⟨A, hAU⟩ := exists_adaptedChartsAt hF hnc hU
    obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ (multiplicity F x) :=
      ⟨_, Complex.isPrimitiveRoot_exp _ hk0⟩
    have hζk : ζ ^ multiplicity F x = 1 := hζ.pow_eq_one
    have hζ1 : ζ ≠ 1 := hζ.ne_one hk2
    have hζnorm : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζk hk0
    set δ : ℝ := A.radius / 2 with hδ_def
    have hδ0 : 0 < δ := half_pos A.radius_pos
    have hδρ : δ < A.radius := by
      rw [hδ_def]
      linarith [A.radius_pos]
    -- the two points `e.symm δ` and `e.symm (δζ)` are distinct but have the same image
    have hw₁ : (δ : ℂ) ∈ A.e.target := by
      rw [A.target_eq, mem_ball_zero_iff, Complex.norm_of_nonneg hδ0.le]
      exact hδρ
    have hw₂ : (δ : ℂ) * ζ ∈ A.e.target := by
      rw [A.target_eq, mem_ball_zero_iff, norm_mul, Complex.norm_of_nonneg hδ0.le,
        hζnorm, mul_one]
      exact hδρ
    have hz₁ : A.e.symm (δ : ℂ) ∈ A.e.source := A.e.map_target hw₁
    have hz₂ : A.e.symm ((δ : ℂ) * ζ) ∈ A.e.source := A.e.map_target hw₂
    have hFeq : F (A.e.symm (δ : ℂ)) = F (A.e.symm ((δ : ℂ) * ζ)) := by
      rw [A.eqOn_symm _ hz₁, A.eqOn_symm _ hz₂, A.e.right_inv hw₁, A.e.right_inv hw₂,
        mul_pow, hζk, mul_one]
    have heq := hinj (hAU hz₁) (hAU hz₂) hFeq
    have hδζ := congrArg (⇑A.e) heq
    rw [A.e.right_inv hw₁, A.e.right_inv hw₂] at hδζ
    have hδne : (δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hδ0.ne'
    apply hζ1
    have h1 : (δ : ℂ) * 1 = (δ : ℂ) * ζ := by
      rw [mul_one]
      exact hδζ
    exact (mul_left_cancel₀ hδne h1).symm

/-- `multiplicity = 1` gives a local homeomorphism agreeing with `F` (Forster 2.5 germ). -/
theorem exists_openPartialHomeomorph_of_multiplicity_eq_one
    (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x) (hnc : ¬ EventuallyConst F (𝓝 x))
    (h1 : multiplicity F x = 1) :
    ∃ h : OpenPartialHomeomorph X Y, x ∈ h.source ∧ ∀ z ∈ h.source, h z = F z := by
  obtain ⟨A, -⟩ := exists_adaptedChartsAt hF hnc univ_mem
  rw [h1] at A
  refine ⟨A.e ≫ₕ A.e'.symm, ?_, ?_⟩
  · rw [trans_source]
    refine ⟨A.mem_source, ?_⟩
    rw [mem_preimage, symm_source, A.map_eq_zero, A.target_eq']
    exact mem_ball_self (pow_pos A.radius_pos 1)
  · intro z hz
    rw [trans_source] at hz
    simp only [coe_trans, Function.comp_apply]
    have h := (A.eqOn_symm z hz.1).symm
    rwa [pow_one] at h

theorem isRamifiedAt_iff_not_injOn (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x)
    (hnc : ¬ EventuallyConst F (𝓝 x)) :
    IsRamifiedAt F x ↔ ¬ ∃ U ∈ 𝓝 x, Set.InjOn F U := by
  rw [← multiplicity_eq_one_iff_injOn hF hnc]
  have h1 := one_le_multiplicity hF hnc
  unfold IsRamifiedAt
  omega

/-- Ramification is isolated: nearby points are unramified (mapping-degree's
"critical values are discrete" seed). -/
theorem eventually_multiplicity_eq_one (hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F x)
    (hnc : ¬ EventuallyConst F (𝓝 x)) : ∀ᶠ y in 𝓝[≠] x, multiplicity F y = 1 := by
  obtain ⟨A, -⟩ := exists_adaptedChartsAt hF hnc univ_mem
  have hk0 : multiplicity F x ≠ 0 := Nat.one_le_iff_ne_zero.mp (one_le_multiplicity hF hnc)
  have hFev : ∀ᶠ y in 𝓝 x, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F y :=
    (contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hF
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hFev, A.e.open_source.mem_nhds A.mem_source] with y hFy hy hyx
  have hyne : y ≠ x := by simpa using hyx
  have hey : A.e y ≠ 0 := by
    rw [← A.map_eq_zero]
    exact fun h ↦ hyne (A.e.injOn hy A.mem_source h)
  -- in the adapted charts at `x`, the order of `F` at `y ≠ x` is that of `z ↦ z ^ k` at a
  -- nonzero point, where the derivative does not vanish
  have hinv := analyticOrderAt_charts_eq_multiplicityENat hFy A.mem_maximalAtlas hy
    A.mem_maximalAtlas' (A.mapsTo hy)
  have hev : (fun z ↦ A.e' (F (A.e.symm z)) - A.e' (F y)) =ᶠ[𝓝 (A.e y)]
      fun z ↦ z ^ multiplicity F x - A.e y ^ multiplicity F x := by
    filter_upwards [A.e.open_target.mem_nhds (A.e.map_source hy)] with z hz
    rw [A.eqOn_pow _ (A.e.map_target hz), A.e.right_inv hz, A.eqOn_pow y hy]
  have hpow : AnalyticAt ℂ (fun z : ℂ ↦ z ^ multiplicity F x) (A.e y) := by fun_prop
  have hder : deriv (fun z : ℂ ↦ z ^ multiplicity F x) (A.e y) ≠ 0 := by
    rw [deriv_pow_field]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hk0) (pow_ne_zero _ hey)
  have h1 : analyticOrderAt
      (fun z : ℂ ↦ z ^ multiplicity F x - A.e y ^ multiplicity F x) (A.e y) = 1 := by
    simpa using hpow.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hder
  rw [analyticOrderAt_congr hev, h1] at hinv
  rw [multiplicity_def, ← hinv]
  rfl

end MultiplicityOne

end RS
