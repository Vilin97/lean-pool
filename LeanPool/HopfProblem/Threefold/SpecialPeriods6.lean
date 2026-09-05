/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.PeriodFamily.Core2
public import LeanPool.HopfProblem.CuspFibre.CuspCentralHomology4
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.Toric.ToricSpace1
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.Uniformization.CuspUniformization1
import all LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.Threefold.SpecialPeriods1
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods2
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods3
import all LeanPool.HopfProblem.Threefold.SpecialPeriods4
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods4
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods5
import all LeanPool.HopfProblem.PeriodFamily.Core1
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods6
import all LeanPool.HopfProblem.PeriodFamily.Core2
import all LeanPool.HopfProblem.CuspFibre.CuspCentralHomology4

/-!
# Hopf problem: threefold · special periods 6

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private structure SpecialPeriods.Construction.PeriodFunctions where
  data : SpecialPeriods.BetaTorsor.Data
  beta : ℍ → ℂ
  beta_holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω beta
  beta_generators : data.GeneratorLaws beta
  tau_cusp :
    ∃ h : ℂ → ℂ,
      AnalyticAt ℂ h 0 ∧
        ∀ᶠ z in UpperHalfPlane.atImInfty,
          (data.tau z : ℂ) =
            (z : ℂ) / SpecialPeriods.Triangle.width + h (SpecialPeriods.Triangle.cuspQ z)
  mu_cusp : SpecialPeriods.MuTorsor.CuspRegular data.mu
  beta_cusp : SpecialPeriods.MuTorsor.CuspRegular (fun z => beta z + (data.tau z : ℂ))

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Construction.eventually_norm_cuspQ_lt_mo1973_18146 {r : ℝ}
    (hr : 0 < r) : ∀ᶠ z in UpperHalfPlane.atImInfty, ‖SpecialPeriods.Triangle.cuspQ z‖ < r := by
  have ht := SpecialPeriods.Triangle.cuspQ_tendsto_atImInfty.mono_right nhdsWithin_le_nhds
  simpa only [Metric.mem_ball, dist_zero_right] using
    ht.eventually (Metric.ball_mem_nhds (0 : ℂ) hr)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Construction.exists_periodFunctions_of_sphere
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere)) :
    ∃ F : PeriodFunctions, F.data.tau = SpecialPeriods.TriangleSource.tauOfSphere π hπ h₀ h₁ := by
  let τ := SpecialPeriods.TriangleSource.tauOfSphere π hπ h₀ h₁
  have hτa := SpecialPeriods.TriangleSource.tauOfSphere_holomorphic π hπ h₀ h₁
  have hτc := SpecialPeriods.TriangleSource.tauOfSphere_covariant π hπ h₀ h₁
  have hJ := SpecialPeriods.TriangleSource.tauOfSphere_modular π hπ h₀ h₁
  obtain ⟨r, hr, _, h, hh, hτformula⟩ := SpecialPeriods.TriangleSource.tauOfSphere_cusp π hπ h₀ h₁
  have hh0 : AnalyticAt ℂ h 0 := hh 0 (Metric.mem_ball_self hr)
  have hτformula' :
    ∀ᶠ z in UpperHalfPlane.atImInfty,
      (τ z : ℂ) = (z : ℂ) / SpecialPeriods.Triangle.width + h (SpecialPeriods.Triangle.cuspQ z) :=
    by
    filter_upwards [eventually_norm_cuspQ_lt_mo1973_18146 hr] with z hz
    exact hτformula z hz
  obtain ⟨ru, hru, u, hu, hu0, hqu⟩ :=
    SpecialPeriods.TriangleSource.tauOfSphere_cusp_unit π hπ h₀ h₁
  have hu0a : AnalyticAt ℂ u 0 := hu 0 (Metric.mem_ball_self hru)
  have hqu' :
    ∀ᶠ z in UpperHalfPlane.atImInfty,
      Function.Periodic.qParam 1 (τ z) =
        SpecialPeriods.Triangle.cuspQ z * u (SpecialPeriods.Triangle.cuspQ z) := by
    filter_upwards [eventually_norm_cuspQ_lt_mo1973_18146 hru] with z hz
    exact hqu z hz
  obtain ⟨μ, hμ, _⟩ :=
    SpecialPeriods.MuTorsor.exists_unique_solution π hπ h₀ h₁ hτc hτa hJ hu0a hu0 hqu'
  let D : SpecialPeriods.BetaTorsor.Data :=
    { tau := τ
      mu := μ
      tau_holomorphic := hτa
      mu_holomorphic := hμ.holomorphic
      tau_covariant := hτc
      mu_one := hμ.generatorOne
      mu_two := hμ.generatorTwo }
  obtain ⟨β, b, hβ, hb, _, Y, hβformula⟩ := D.exists_solution_with_cusp_extension π hπ
  have hβformula' :
    ∀ᶠ z in UpperHalfPlane.atImInfty, β z + (D.tau z : ℂ) = b (SpecialPeriods.Triangle.cuspQ z) :=
    by
    apply (UpperHalfPlane.atImInfty_mem _).mpr
    exact ⟨Y + 1, fun z hz => hβformula z (by linarith)⟩
  exact
    ⟨{  data := D
        beta := β
        beta_holomorphic := hβ.holomorphic
        beta_generators := hβ.generators
        tau_cusp := ⟨h, hh0, hτformula'⟩
        mu_cusp := hμ.cuspRegular
        beta_cusp := ⟨b, hb, hβformula'⟩ }, rfl⟩

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Construction.periodFunctionsOfSphere
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere)) :
    PeriodFunctions :=
  (exists_periodFunctions_of_sphere π hπ h₀ h₁).choose

private theorem SpecialPeriods.Construction.triangle_invariant_of_generators {A : Type*} (f : ℍ → A)
    (h₁ : ∀ z, f (SpecialPeriods.Triangle.generatorOneSL • z) = f z)
    (h₂ : ∀ z, f (SpecialPeriods.Triangle.generatorTwoSL • z) = f z)
    (g : SpecialPeriods.TriangleGroup) :
    ∀ z, f (SpecialPeriods.triangleGeometricRepresentation g z) = f z := by
  let := SpecialPeriods.triangleGeometricAction
  have hg :
    g ∈
      Subgroup.closure
        ({ SpecialPeriods.triangleGenerator₁, SpecialPeriods.triangleGenerator₂ } :
          Set SpecialPeriods.TriangleGroup) := by
    rw [SpecialPeriods.triangle_generators_generate]
    trivial
  change ∀ z, f (g • z) = f z
  induction hg using Subgroup.closure_induction with
  | mem a ha =>
    rcases ha with rfl | rfl
    · intro z
      change
        f (SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleGenerator₁ z) =
          f z
      simpa only [SpecialPeriods.triangleGeometricRepresentation_generator₁_apply] using h₁ z
    · intro z
      change
        f (SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleGenerator₂ z) =
          f z
      simpa only [SpecialPeriods.triangleGeometricRepresentation_generator₂_apply] using h₂ z
  | one => intro z; rw [one_smul]
  | mul g h _ _ ihg ihh => intro z; rw [SemigroupAction.mul_smul, ihg, ihh]
  | inv g _ ih =>
    intro z
    simpa only [smul_inv_smul] using (ih (g⁻¹ • z)).symm

private theorem
    SpecialPeriods.Construction.discriminant_invariant_of_generator_laws (P : ℍ → PeriodPoint)
    (hτ : ∀ z, 0 < (P z).τ.im)
    (h₁ : ∀ z, P (SpecialPeriods.Triangle.generatorOneSL • z) = (P z).step₁)
    (h₂ : ∀ z, P (SpecialPeriods.Triangle.generatorTwoSL • z) = (P z).step₂) :
    ∀ (g : SpecialPeriods.TriangleGroup) (z : ℍ),
      (P (SpecialPeriods.triangleGeometricRepresentation g z)).discriminant =
        (P z).discriminant := by
  apply triangle_invariant_of_generators (fun z => (P z).discriminant)
  · intro z
    rw [h₁ z, PeriodPoint.step₁_discriminant (P z) (ne_of_gt (hτ z))]
  · intro z
    rw [h₂ z, PeriodPoint.step₂_discriminant (P z) (ne_of_gt (hτ z))]

private theorem
    SpecialPeriods.Construction.periodPoint_im_tau_pos (D : SpecialPeriods.BetaTorsor.Data)
    (β : ℍ → ℂ) (z : ℍ) : 0 < (D.periodPoint β z).τ.im :=
  (D.tau z).im_pos

private theorem SpecialPeriods.Construction.periodPoint_generator₁_iff
    (D : SpecialPeriods.BetaTorsor.Data) {β : ℍ → ℂ} (z : ℍ) :
    D.periodPoint β (SpecialPeriods.Triangle.generatorOneSL • z) = (D.periodPoint β z).step₁ ↔
      β (SpecialPeriods.Triangle.generatorOneSL • z) =
        β z + SpecialPeriods.BetaTorsor.phiOne D.tau D.mu z := by
  constructor
  · intro h
    have hb := congrArg PeriodPoint.β h
    simpa only [SpecialPeriods.BetaTorsor.Data.periodPoint, PeriodPoint.step₁,
      SpecialPeriods.BetaTorsor.phiOne, sub_eq_add_neg, add_assoc] using hb
  · intro hb
    apply PeriodPoint.ext
    · exact D.tau_covariant.1 z
    · exact D.mu_one z
    · simpa only [SpecialPeriods.BetaTorsor.Data.periodPoint, PeriodPoint.step₁,
        SpecialPeriods.BetaTorsor.phiOne, sub_eq_add_neg, add_assoc] using hb

private theorem SpecialPeriods.Construction.periodPoint_generator₂_iff
    (D : SpecialPeriods.BetaTorsor.Data) {β : ℍ → ℂ} (z : ℍ) :
    D.periodPoint β (SpecialPeriods.Triangle.generatorTwoSL • z) = (D.periodPoint β z).step₂ ↔
      β (SpecialPeriods.Triangle.generatorTwoSL • z) =
        β z + SpecialPeriods.BetaTorsor.phiTwo D.tau D.mu z := by
  constructor
  · intro h
    have hb := congrArg PeriodPoint.β h
    simpa only [SpecialPeriods.BetaTorsor.Data.periodPoint, PeriodPoint.step₂,
      SpecialPeriods.BetaTorsor.phiTwo, sub_eq_add_neg, add_assoc] using hb
  · intro hb
    apply PeriodPoint.ext
    · exact D.tau_covariant.2 z
    · exact D.mu_two z
    · simpa only [SpecialPeriods.BetaTorsor.Data.periodPoint, PeriodPoint.step₂,
        SpecialPeriods.BetaTorsor.phiTwo, sub_eq_add_neg, add_assoc] using hb

private theorem
    SpecialPeriods.Construction.periodPoint_generator₁ (D : SpecialPeriods.BetaTorsor.Data)
    {β : ℍ → ℂ} (hβ : D.GeneratorLaws β) (z : ℍ) :
    D.periodPoint β (SpecialPeriods.Triangle.generatorOneSL • z) = (D.periodPoint β z).step₁ :=
  (periodPoint_generator₁_iff D z).mpr (hβ.1 z)

private theorem
    SpecialPeriods.Construction.periodPoint_generator₂ (D : SpecialPeriods.BetaTorsor.Data)
    {β : ℍ → ℂ} (hβ : D.GeneratorLaws β) (z : ℍ) :
    D.periodPoint β (SpecialPeriods.Triangle.generatorTwoSL • z) = (D.periodPoint β z).step₂ :=
  (periodPoint_generator₂_iff D z).mpr (hβ.2 z)

private theorem
    SpecialPeriods.Construction.continuous_discriminant (D : SpecialPeriods.BetaTorsor.Data)
    {β : ℍ → ℂ} (hβ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω β) :
    Continuous (fun z => (D.periodPoint β z).discriminant) := by
  exact
    continuousOn_univ.mp
      (PeriodPoint.continuousOn_discriminant (D.periodPoint β)
        (UpperHalfPlane.contMDiff_coe.comp D.tau_holomorphic).continuous.continuousOn
        D.mu_holomorphic.continuous.continuousOn hβ.continuous.continuousOn
        (fun z _ => (D.tau z).im_pos.ne'))

private theorem
    SpecialPeriods.Construction.discriminant_invariant (D : SpecialPeriods.BetaTorsor.Data)
    {β : ℍ → ℂ} (hβ : D.GeneratorLaws β) (g : SpecialPeriods.TriangleGroup) (z : ℍ) :
    (D.periodPoint β (SpecialPeriods.triangleGeometricRepresentation g z)).discriminant =
      (D.periodPoint β z).discriminant :=
  discriminant_invariant_of_generator_laws (D.periodPoint β) (periodPoint_im_tau_pos D β)
    (periodPoint_generator₁ D hβ) (periodPoint_generator₂ D hβ) g z

private theorem
    SpecialPeriods.Construction.periodMap_generator₁ (D : SpecialPeriods.BetaTorsor.Data)
    {β : ℍ → ℂ} (hβ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω β) (hAdm : ∀ z : ℍ, (D.periodPoint β z).Admissible)
    (hgen : D.GeneratorLaws β) (z : ℍ) :
    (D.periodMap β hβ hAdm).point (SpecialPeriods.Triangle.generatorOneSL • z) =
      ((D.periodMap β hβ hAdm).point z).step₁ :=
  Subtype.ext (periodPoint_generator₁ D hgen z)

private theorem
    SpecialPeriods.Construction.periodMap_generator₂ (D : SpecialPeriods.BetaTorsor.Data)
    {β : ℍ → ℂ} (hβ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω β) (hAdm : ∀ z : ℍ, (D.periodPoint β z).Admissible)
    (hgen : D.GeneratorLaws β) (z : ℍ) :
    (D.periodMap β hβ hAdm).point (SpecialPeriods.Triangle.generatorTwoSL • z) =
      ((D.periodMap β hβ hAdm).point z).step₂ :=
  Subtype.ext (periodPoint_generator₂ D hgen z)

private theorem SpecialPeriods.Construction.shiftedPeriodMap_generator₁
    (D : SpecialPeriods.BetaTorsor.Data) {β : ℍ → ℂ} (hβ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω β) (c : ℂ)
    (hAdm : ∀ z : ℍ, ((D.periodPoint β z).shiftBeta c).Admissible) (hgen : D.GeneratorLaws β)
    (z : ℍ) :
    (D.shiftedPeriodMap β hβ c hAdm).point (SpecialPeriods.Triangle.generatorOneSL • z) =
      ((D.shiftedPeriodMap β hβ c hAdm).point z).step₁ :=
  periodMap_generator₁ D (hβ.add contMDiff_const) hAdm (hgen.add_const D c) z

private theorem SpecialPeriods.Construction.shiftedPeriodMap_generator₂
    (D : SpecialPeriods.BetaTorsor.Data) {β : ℍ → ℂ} (hβ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω β) (c : ℂ)
    (hAdm : ∀ z : ℍ, ((D.periodPoint β z).shiftBeta c).Admissible) (hgen : D.GeneratorLaws β)
    (z : ℍ) :
    (D.shiftedPeriodMap β hβ c hAdm).point (SpecialPeriods.Triangle.generatorTwoSL • z) =
      ((D.shiftedPeriodMap β hβ c hAdm).point z).step₂ :=
  periodMap_generator₂ D (hβ.add contMDiff_const) hAdm (hgen.add_const D c) z

private theorem SpecialPeriods.Construction.exponential_normalized_eq_cuspQ (z : ℍ) :
    CuspUniformization.exponential ((z : ℂ) / SpecialPeriods.Triangle.width) =
      SpecialPeriods.Triangle.cuspQ z := by
  simp only [CuspUniformization.exponential, SpecialPeriods.Triangle.cuspQ_eq_exp, mul_div_assoc]

private theorem
    SpecialPeriods.Construction.cusp_analytic_tendsto {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    Filter.Tendsto (fun z : ℍ => f (SpecialPeriods.Triangle.cuspQ z)) UpperHalfPlane.atImInfty
      (𝓝 (f 0)) :=
  hf.continuousAt.tendsto.comp
    (SpecialPeriods.Triangle.cuspQ_tendsto_atImInfty.mono_right nhdsWithin_le_nhds)

private theorem
    SpecialPeriods.Construction.tau_im_tendsto_atTop_of_cusp_formula {τ : ℍ → ℍ} {h : ℂ → ℂ}
    (hh : AnalyticAt ℂ h 0)
    (hτ :
      ∀ᶠ z in UpperHalfPlane.atImInfty,
        (τ z : ℂ) =
          (z : ℂ) / SpecialPeriods.Triangle.width + h (SpecialPeriods.Triangle.cuspQ z)) :
    Filter.Tendsto (fun z : ℍ => (τ z).im) UpperHalfPlane.atImInfty Filter.atTop := by
  have hheight :
    Filter.Tendsto (fun z : ℍ => z.im / SpecialPeriods.Triangle.width) UpperHalfPlane.atImInfty
      Filter.atTop :=
    (show Filter.Tendsto UpperHalfPlane.im UpperHalfPlane.atImInfty Filter.atTop from
          Filter.tendsto_comap).atTop_div_const
      SpecialPeriods.Triangle.width_pos
  have hremainder :
    Filter.Tendsto (fun z : ℍ => (h (SpecialPeriods.Triangle.cuspQ z)).im)
      UpperHalfPlane.atImInfty (𝓝 (h 0).im) :=
    Complex.continuous_im.continuousAt.tendsto.comp (cusp_analytic_tendsto hh)
  apply (hheight.atTop_add hremainder).congr'
  filter_upwards [hτ] with z hz
  simpa only [Complex.add_im, Complex.div_ofReal_im, UpperHalfPlane.coe_im] using
    (congrArg Complex.im hz).symm

private theorem SpecialPeriods.Construction.periodPoint_eventually_eq_cuspPeriodPoint {τ : ℍ → ℍ}
    {μ β : ℍ → ℂ} {m b h : ℂ → ℂ}
    (hτ :
      ∀ᶠ z in UpperHalfPlane.atImInfty,
        (τ z : ℂ) = (z : ℂ) / SpecialPeriods.Triangle.width + h (SpecialPeriods.Triangle.cuspQ z))
    (hμ : ∀ᶠ z in UpperHalfPlane.atImInfty, μ z = m (SpecialPeriods.Triangle.cuspQ z))
    (hβ :
      ∀ᶠ z in UpperHalfPlane.atImInfty, β z + (τ z : ℂ) = b (SpecialPeriods.Triangle.cuspQ z)) :
    ∀ᶠ z in UpperHalfPlane.atImInfty,
      (⟨(τ z : ℂ), μ z, β z⟩ : PeriodPoint) =
        SpecialPeriods.cuspPeriodPoint m b h ((z : ℂ) / SpecialPeriods.Triangle.width) := by
  filter_upwards [hτ, hμ, hβ] with z hτz hμz hβz
  apply PeriodPoint.ext
  · simpa only [SpecialPeriods.cuspPeriodPoint, exponential_normalized_eq_cuspQ] using hτz
  · simpa only [SpecialPeriods.cuspPeriodPoint, exponential_normalized_eq_cuspQ] using hμz
  · change
      β z =
        b (CuspUniformization.exponential ((z : ℂ) / SpecialPeriods.Triangle.width)) -
            (z : ℂ) / SpecialPeriods.Triangle.width -
          h (CuspUniformization.exponential ((z : ℂ) / SpecialPeriods.Triangle.width))
    rw [exponential_normalized_eq_cuspQ]
    calc
      β z = b (SpecialPeriods.Triangle.cuspQ z) - (τ z : ℂ) := eq_sub_of_add_eq hβz
      _ =
          b (SpecialPeriods.Triangle.cuspQ z) - (z : ℂ) / SpecialPeriods.Triangle.width -
            h (SpecialPeriods.Triangle.cuspQ z) := by
        rw [hτz]
        ring

private theorem SpecialPeriods.Construction.eventual_cuspQ_radius {P : ℍ → Prop}
    (hP : ∀ᶠ z in UpperHalfPlane.atImInfty, P z) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : ℍ, ‖SpecialPeriods.Triangle.cuspQ z‖ < r → P z := by
  obtain ⟨Y, hY⟩ := (UpperHalfPlane.atImInfty_mem _).mp hP
  refine ⟨Real.exp (-2 * Real.pi * Y / SpecialPeriods.Triangle.width), Real.exp_pos _, ?_⟩
  intro z hz
  exact hY z ((SpecialPeriods.Triangle.cuspQ_norm_lt_exp_iff Y z).mp hz).le

private theorem SpecialPeriods.Construction.eventual_cuspQ_radius_lt {P : ℍ → Prop} {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hP : ∀ᶠ z in UpperHalfPlane.atImInfty, P z) :
    ∃ r : ℝ, 0 < r ∧ r < r₀ ∧ ∀ z : ℍ, ‖SpecialPeriods.Triangle.cuspQ z‖ < r → P z := by
  obtain ⟨r, hr, h⟩ := eventual_cuspQ_radius hP
  refine
    ⟨Min.min r (r₀ / 2), lt_min hr (half_pos hr₀), (min_le_right _ _).trans_lt (half_lt_self hr₀),
      ?_⟩
  intro z hz
  exact h z (hz.trans_le (min_le_left _ _))

private theorem SpecialPeriods.Construction.beta_add_const_cusp_formula {τ : ℍ → ℍ} {β : ℍ → ℂ}
    {b : ℂ → ℂ}
    (hβ : ∀ᶠ z in UpperHalfPlane.atImInfty, β z + (τ z : ℂ) = b (SpecialPeriods.Triangle.cuspQ z))
    (c : ℂ) :
    ∀ᶠ z in UpperHalfPlane.atImInfty,
      (β z + c) + (τ z : ℂ) = (fun q => b q + c) (SpecialPeriods.Triangle.cuspQ z) := by
  filter_upwards [hβ] with z hz
  simpa only [add_right_comm] using congrArg (fun w : ℂ => w + c) hz

private def SpecialPeriods.Construction.orbitDescend (f : ℍ → ℝ)
    (hinv :
      ∀ (g : SpecialPeriods.TriangleGroup) (z : ℍ),
        f (SpecialPeriods.triangleGeometricRepresentation g z) = f z) :
    SpecialPeriods.TriangleOrbitSpace → ℝ :=
  Quotient.lift f fun x y hxy =>
    by
    change
      ∃ g : SpecialPeriods.TriangleGroup,
        SpecialPeriods.triangleGeometricRepresentation g y = x at hxy
    obtain ⟨g, hg⟩ := hxy
    exact (congrArg f hg).symm.trans (hinv g y)

private theorem SpecialPeriods.Construction.orbitDescend_continuous (f : ℍ → ℝ)
    (hinv :
      ∀ (g : SpecialPeriods.TriangleGroup) (z : ℍ),
        f (SpecialPeriods.triangleGeometricRepresentation g z) = f z)
    (hf : Continuous f) : Continuous (orbitDescend f hinv) :=
  hf.quotient_lift _

private def SpecialPeriods.Construction.compactDescend (f : ℍ → ℝ)
    (hinv :
      ∀ (g : SpecialPeriods.TriangleGroup) (z : ℍ),
        f (SpecialPeriods.triangleGeometricRepresentation g z) = f z)
    (c : ℝ) : SpecialPeriods.TriangleCompactifiedOrbitSpace → ℝ :=
  OnePoint.rec c (orbitDescend f hinv)

@[simp]
private theorem SpecialPeriods.Construction.compactDescend_projection (f : ℍ → ℝ)
    (hinv :
      ∀ (g : SpecialPeriods.TriangleGroup) (z : ℍ),
        f (SpecialPeriods.triangleGeometricRepresentation g z) = f z)
    (c : ℝ) (z : ℍ) :
    compactDescend f hinv c
        (SpecialPeriods.triangleOpenInclusion (SpecialPeriods.triangleOrbitProjection z)) =
      f z :=
  rfl

private theorem SpecialPeriods.Construction.compactDescend_continuousAt_openInclusion (f : ℍ → ℝ)
    (hinv :
      ∀ (g : SpecialPeriods.TriangleGroup) (z : ℍ),
        f (SpecialPeriods.triangleGeometricRepresentation g z) = f z)
    (c : ℝ) (hf : Continuous f) (q : SpecialPeriods.TriangleOrbitSpace) :
    ContinuousAt (compactDescend f hinv c) (SpecialPeriods.triangleOpenInclusion q) :=
  OnePoint.continuousAt_coe.mpr (orbitDescend_continuous f hinv hf).continuousAt

private theorem SpecialPeriods.Construction.compactDescend_continuousOn (f : ℍ → ℝ)
    (hinv :
      ∀ (g : SpecialPeriods.TriangleGroup) (z : ℍ),
        f (SpecialPeriods.triangleGeometricRepresentation g z) = f z)
    (c : ℝ) (hf : Continuous f) :
    ContinuousOn (compactDescend f hinv c)
      ({ SpecialPeriods.triangleCuspPoint } :
          Set SpecialPeriods.TriangleCompactifiedOrbitSpace)ᶜ := by
  intro x hx
  induction x using OnePoint.rec with
  | infty => exact (hx rfl).elim
  | coe q => exact (compactDescend_continuousAt_openInclusion f hinv c hf q).continuousWithinAt

private theorem SpecialPeriods.Construction.compactDescend_eventually_of_atImInfty (f : ℍ → ℝ)
    (hinv :
      ∀ (g : SpecialPeriods.TriangleGroup) (z : ℍ),
        f (SpecialPeriods.triangleGeometricRepresentation g z) = f z)
    (c : ℝ) (P : ℝ → Prop) (hP : ∀ᶠ z in UpperHalfPlane.atImInfty, P (f z)) :
    ∀ᶠ x in 𝓝[≠] SpecialPeriods.triangleCuspPoint, P (compactDescend f hinv c x) := by
  obtain ⟨Y, hY⟩ := (UpperHalfPlane.atImInfty_mem _).mp hP
  filter_upwards [nhdsWithin_le_nhds (SpecialPeriods.Triangle.cuspNeighborhood_mem_nhds Y),
    self_mem_nhdsWithin] with x hx hxne
  induction x using OnePoint.rec with
  | infty => exact (hxne rfl).elim
  | coe
    q =>
    obtain ⟨z, hz, rfl⟩ :=
      (SpecialPeriods.Triangle.mem_cuspImage Y q).mp
        ((SpecialPeriods.Triangle.openInclusion_mem_cuspNeighborhood Y q).mp hx)
    exact hY z hz.le

private theorem SpecialPeriods.Construction.compactDescend_tendsto_atBot (f : ℍ → ℝ)
    (hinv :
      ∀ (g : SpecialPeriods.TriangleGroup) (z : ℍ),
        f (SpecialPeriods.triangleGeometricRepresentation g z) = f z)
    (c : ℝ) (hlim : Filter.Tendsto f UpperHalfPlane.atImInfty Filter.atBot) :
    Filter.Tendsto (compactDescend f hinv c) (𝓝[≠] SpecialPeriods.triangleCuspPoint)
      Filter.atBot := by
  refine Filter.tendsto_atBot.mpr fun R => ?_
  exact
    compactDescend_eventually_of_atImInfty f hinv c (fun t => t ≤ R) (hlim.eventually_le_atBot R)

private theorem
    SpecialPeriods.Construction.bddAbove_range_of_triangle_invariant_tendsto_atBot (f : ℍ → ℝ)
    (hf : Continuous f)
    (hinv :
      ∀ (g : SpecialPeriods.TriangleGroup) (z : ℍ),
        f (SpecialPeriods.triangleGeometricRepresentation g z) = f z)
    (hlim : Filter.Tendsto f UpperHalfPlane.atImInfty Filter.atBot) : BddAbove (Set.range f) := by
  apply
    (SpecialPeriods.bddAbove_image_punctured_of_tendsto_atBot SpecialPeriods.triangleCuspPoint
        (compactDescend f hinv 0) (compactDescend_continuousOn f hinv 0 hf)
        (compactDescend_tendsto_atBot f hinv 0 hlim)).mono
  rintro _ ⟨z, rfl⟩
  exact
    ⟨SpecialPeriods.triangleOpenInclusion (SpecialPeriods.triangleOrbitProjection z),
      SpecialPeriods.triangleOpenInclusion_ne_cusp _, compactDescend_projection f hinv 0 z⟩

private theorem SpecialPeriods.Construction.PeriodFunctions.tau_im_tendsto_atTop
    (F : SpecialPeriods.Construction.PeriodFunctions) :
    Filter.Tendsto (fun z : ℍ => (F.data.tau z).im) UpperHalfPlane.atImInfty Filter.atTop := by
  obtain ⟨h, hh, hτ⟩ := F.tau_cusp
  exact SpecialPeriods.Construction.tau_im_tendsto_atTop_of_cusp_formula hh hτ

private theorem SpecialPeriods.Construction.PeriodFunctions.beta_add_tau_im_eventually_bounded
    (F : SpecialPeriods.Construction.PeriodFunctions) :
    ∃ M : ℝ, ∀ᶠ z in UpperHalfPlane.atImInfty, (F.beta z + (F.data.tau z : ℂ)).im ≤ M := by
  obtain ⟨M, Y, hM⟩ := UpperHalfPlane.isBoundedAtImInfty_iff.mp F.beta_cusp.bounded
  refine ⟨M, (UpperHalfPlane.atImInfty_mem _).mpr ⟨Y, ?_⟩⟩
  intro z hz
  exact ((le_abs_self _).trans (Complex.abs_im_le_norm _)).trans (hM z hz)

private theorem SpecialPeriods.Construction.PeriodFunctions.discriminant_tendsto_atBot
    (F : SpecialPeriods.Construction.PeriodFunctions) :
    Filter.Tendsto (fun z => (F.data.periodPoint F.beta z).discriminant) UpperHalfPlane.atImInfty
      Filter.atBot :=
  PeriodPoint.tendsto_discriminant_atBot (F.data.periodPoint F.beta)
    (Filter.Eventually.of_forall fun z => (F.data.tau z).im_pos) F.tau_im_tendsto_atTop
    F.beta_add_tau_im_eventually_bounded

private theorem SpecialPeriods.Construction.PeriodFunctions.discriminant_bddAbove
    (F : SpecialPeriods.Construction.PeriodFunctions) :
    BddAbove (Set.range fun z => (F.data.periodPoint F.beta z).discriminant) :=
  SpecialPeriods.Construction.bddAbove_range_of_triangle_invariant_tendsto_atBot _
    (SpecialPeriods.Construction.continuous_discriminant F.data F.beta_holomorphic)
    (SpecialPeriods.Construction.discriminant_invariant F.data F.beta_generators)
    F.discriminant_tendsto_atBot

private theorem SpecialPeriods.Construction.PeriodFunctions.exists_negative_imaginary_shift
    (F : SpecialPeriods.Construction.PeriodFunctions) :
    ∃ M : ℝ,
      0 < M ∧
        ∀ z : ℍ, ((F.data.periodPoint F.beta z).shiftBeta (-((M : ℂ) * Complex.I))).Admissible :=
  PeriodPoint.exists_negative_imaginary_shift_of_bddAbove (F.data.periodPoint F.beta)
    (fun z => (F.data.tau z).im_pos) F.discriminant_bddAbove

private def SpecialPeriods.Construction.PeriodFunctions.shiftHeight
    (F : SpecialPeriods.Construction.PeriodFunctions) : ℝ :=
  F.exists_negative_imaginary_shift.choose

private def SpecialPeriods.Construction.PeriodFunctions.shiftConstant
    (F : SpecialPeriods.Construction.PeriodFunctions) : ℂ :=
  -((F.shiftHeight : ℂ) * Complex.I)

private theorem SpecialPeriods.Construction.PeriodFunctions.shifted_admissible
    (F : SpecialPeriods.Construction.PeriodFunctions) (z : ℍ) :
    ((F.data.periodPoint F.beta z).shiftBeta F.shiftConstant).Admissible :=
  F.exists_negative_imaginary_shift.choose_spec.2 z

private def SpecialPeriods.Construction.PeriodFunctions.admissiblePeriods
    (F : SpecialPeriods.Construction.PeriodFunctions) : HolomorphicPeriodMap ℂ ℍ :=
  F.data.shiftedPeriodMap F.beta F.beta_holomorphic F.shiftConstant F.shifted_admissible

@[simp]
private theorem SpecialPeriods.Construction.PeriodFunctions.admissiblePeriods_tau
    (F : SpecialPeriods.Construction.PeriodFunctions) (z : ℍ) :
    (F.admissiblePeriods.point z).val.τ = (F.data.tau z : ℂ) :=
  rfl

@[simp]
private theorem SpecialPeriods.Construction.PeriodFunctions.admissiblePeriods_beta
    (F : SpecialPeriods.Construction.PeriodFunctions) (z : ℍ) :
    (F.admissiblePeriods.point z).val.β = F.beta z + F.shiftConstant :=
  rfl

private theorem SpecialPeriods.Construction.PeriodFunctions.admissiblePeriods_generator₁
    (F : SpecialPeriods.Construction.PeriodFunctions) (z : ℍ) :
    F.admissiblePeriods.point (SpecialPeriods.Triangle.generatorOneSL • z) =
      (F.admissiblePeriods.point z).step₁ :=
  SpecialPeriods.Construction.shiftedPeriodMap_generator₁ F.data F.beta_holomorphic
    F.shiftConstant F.shifted_admissible F.beta_generators z

private theorem SpecialPeriods.Construction.PeriodFunctions.admissiblePeriods_generator₂
    (F : SpecialPeriods.Construction.PeriodFunctions) (z : ℍ) :
    F.admissiblePeriods.point (SpecialPeriods.Triangle.generatorTwoSL • z) =
      (F.admissiblePeriods.point z).step₂ :=
  SpecialPeriods.Construction.shiftedPeriodMap_generator₂ F.data F.beta_holomorphic
    F.shiftConstant F.shifted_admissible F.beta_generators z

private theorem SpecialPeriods.Construction.PeriodFunctions.admissiblePeriods_beta_cusp
    (F : SpecialPeriods.Construction.PeriodFunctions) :
    SpecialPeriods.MuTorsor.CuspRegular
      (fun z => (F.admissiblePeriods.point z).val.β + (F.admissiblePeriods.point z).val.τ) := by
  obtain ⟨b, hb, hβ⟩ := F.beta_cusp
  exact
    ⟨fun q => b q + F.shiftConstant, hb.add analyticAt_const,
      SpecialPeriods.Construction.beta_add_const_cusp_formula hβ F.shiftConstant⟩

private theorem SpecialPeriods.Construction.PeriodFunctions.exists_cusp_data
    (F : SpecialPeriods.Construction.PeriodFunctions) :
    ∃ C : SpecialPeriods.CuspFamily.Data,
      ∀ z : ℍ,
        ‖SpecialPeriods.Triangle.cuspQ z‖ < C.radius →
          (F.admissiblePeriods.point z).val =
            SpecialPeriods.cuspPeriodPoint C.μ C.b C.h
              ((z : ℂ) / SpecialPeriods.Triangle.width) := by
  obtain ⟨h, hh, hτ⟩ := F.tau_cusp
  obtain ⟨m, hm, hμ⟩ := F.mu_cusp
  obtain ⟨b, hb, hβ⟩ := F.admissiblePeriods_beta_cusp
  have hβ' :
    ∀ᶠ z in UpperHalfPlane.atImInfty,
      (F.beta z + F.shiftConstant) + (F.data.tau z : ℂ) = b (SpecialPeriods.Triangle.cuspQ z) := by
    simpa only [admissiblePeriods_beta, admissiblePeriods_tau] using hβ
  have hpoint :
    ∀ᶠ z in UpperHalfPlane.atImInfty,
      (F.admissiblePeriods.point z).val =
        SpecialPeriods.cuspPeriodPoint m b h ((z : ℂ) / SpecialPeriods.Triangle.width) :=
    SpecialPeriods.Construction.periodPoint_eventually_eq_cuspPeriodPoint hτ hμ hβ'
  obtain ⟨ε, hε, hε1, hR, hC⟩ :=
    SpecialPeriods.exists_cuspCorrection_admissible_radius_of_analyticAt hm hb hh
  obtain ⟨r, hr, hrε, hmatch⟩ := SpecialPeriods.Construction.eventual_cuspQ_radius_lt hε hpoint
  refine
    ⟨{  μ := m
        b := b
        h := h
        radius := r
        radius_pos := hr
        radius_lt_one := hrε.trans hε1
        holomorphic := fun i j => (hC i j).mono (Metric.ball_subset_ball hrε.le)
        smallDrift := fun t ht0 htr => hR t ht0 (htr.trans hrε) }, hmatch⟩

private def SpecialPeriods.Construction.PeriodFunctions.cuspData
    (F : SpecialPeriods.Construction.PeriodFunctions) : SpecialPeriods.CuspFamily.Data :=
  F.exists_cusp_data.choose

private theorem SpecialPeriods.Construction.PeriodFunctions.cuspData_periodPoint
    (F : SpecialPeriods.Construction.PeriodFunctions) (z : ℍ)
    (hz : ‖SpecialPeriods.Triangle.cuspQ z‖ < F.cuspData.radius) :
    (F.admissiblePeriods.point z).val =
      SpecialPeriods.cuspPeriodPoint F.cuspData.μ F.cuspData.b F.cuspData.h
        ((z : ℂ) / SpecialPeriods.Triangle.width) :=
  F.exists_cusp_data.choose_spec z hz

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Construction.periodMapOfSphere
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere)) :
    HolomorphicPeriodMap ℂ ℍ :=
  (periodFunctionsOfSphere π hπ h₀ h₁).admissiblePeriods

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Construction.periodMapOfSphere_generator₁
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere))
    (z : ℍ) :
    (periodMapOfSphere π hπ h₀ h₁).point (SpecialPeriods.Triangle.generatorOneSL • z) =
      ((periodMapOfSphere π hπ h₀ h₁).point z).step₁ :=
  (periodFunctionsOfSphere π hπ h₀ h₁).admissiblePeriods_generator₁ z

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Construction.periodMapOfSphere_generator₂
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere))
    (z : ℍ) :
    (periodMapOfSphere π hπ h₀ h₁).point (SpecialPeriods.Triangle.generatorTwoSL • z) =
      ((periodMapOfSphere π hπ h₀ h₁).point z).step₂ :=
  (periodFunctionsOfSphere π hπ h₀ h₁).admissiblePeriods_generator₂ z

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Construction.cuspDataOfSphere
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere)) :
    SpecialPeriods.CuspFamily.Data :=
  (periodFunctionsOfSphere π hπ h₀ h₁).cuspData

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Construction.cuspDataOfSphere_periodPoint
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere))
    (z : ℍ) (hz : ‖SpecialPeriods.Triangle.cuspQ z‖ < (cuspDataOfSphere π hπ h₀ h₁).radius) :
    ((periodMapOfSphere π hπ h₀ h₁).point z).val =
      SpecialPeriods.cuspPeriodPoint (cuspDataOfSphere π hπ h₀ h₁).μ
        (cuspDataOfSphere π hπ h₀ h₁).b (cuspDataOfSphere π hπ h₀ h₁).h
        ((z : ℂ) / SpecialPeriods.Triangle.width) :=
  (periodFunctionsOfSphere π hπ h₀ h₁).cuspData_periodPoint z hz

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private structure SpecialPeriods.Threefold.BaseCover where
  radius : Puncture → ℝ
  radius_pos : ∀ i, 0 < radius i
  radius_lt_chart : ∀ i, radius i < punctureChartRadius i
  pairwise_disjoint :
    Pairwise
      (fun i j =>
        Disjoint
          (coordinateDisc (punctureChart i) (radius i) :
            Set SpecialPeriods.TriangleCompactifiedOrbitSpace)
          (coordinateDisc (punctureChart j) (radius j) :
            Set SpecialPeriods.TriangleCompactifiedOrbitSpace))

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Threefold.BaseCover.fillingPatch (C : SpecialPeriods.Threefold.BaseCover)
    (i : SpecialPeriods.Threefold.Puncture) :
    TopologicalSpace.Opens SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  SpecialPeriods.Threefold.coordinateDisc (SpecialPeriods.Threefold.punctureChart i) (C.radius i)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
private theorem SpecialPeriods.Threefold.BaseCover.mem_fillingPatch
    (C : SpecialPeriods.Threefold.BaseCover) (i : SpecialPeriods.Threefold.Puncture)
    (x : SpecialPeriods.TriangleCompactifiedOrbitSpace) :
    x ∈ C.fillingPatch i ↔
      x ∈ (SpecialPeriods.Threefold.punctureChart i).source ∧
        ‖SpecialPeriods.Threefold.punctureChart i x‖ < C.radius i := by
  simp only [fillingPatch, SpecialPeriods.Threefold.mem_coordinateDisc, Metric.mem_ball,
    dist_zero_right]

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.BaseCover.fillingPatch_subset_chart
    (C : SpecialPeriods.Threefold.BaseCover) (i : SpecialPeriods.Threefold.Puncture) :
    (C.fillingPatch i : Set SpecialPeriods.TriangleCompactifiedOrbitSpace) ⊆
      (SpecialPeriods.Threefold.punctureChart i).source :=
  Set.inter_subset_left

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.BaseCover.coordinateBall_subset_target
    (C : SpecialPeriods.Threefold.BaseCover) (i : SpecialPeriods.Threefold.Puncture) :
    Metric.ball (0 : ℂ) (C.radius i) ⊆ (SpecialPeriods.Threefold.punctureChart i).target := by
  rw [SpecialPeriods.Threefold.punctureChart_target]
  exact Metric.ball_subset_ball (C.radius_lt_chart i).le

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.BaseCover.fillingPatch_eq_inverse_image
    (C : SpecialPeriods.Threefold.BaseCover) (i : SpecialPeriods.Threefold.Puncture) :
    (C.fillingPatch i : Set SpecialPeriods.TriangleCompactifiedOrbitSpace) =
      (SpecialPeriods.Threefold.punctureChart i).symm '' Metric.ball 0 (C.radius i) :=
  SpecialPeriods.Threefold.coordinateDisc_eq_symm_image (SpecialPeriods.Threefold.punctureChart i)
    (C.coordinateBall_subset_target i)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.BaseCover.point_mem_fillingPatch
    (C : SpecialPeriods.Threefold.BaseCover) (i : SpecialPeriods.Threefold.Puncture) :
    SpecialPeriods.Threefold.puncturePoint i ∈ C.fillingPatch i :=
  SpecialPeriods.Threefold.center_mem_coordinateDisc (SpecialPeriods.Threefold.punctureChart i)
    (SpecialPeriods.Threefold.puncturePoint_mem_source i)
    (SpecialPeriods.Threefold.punctureChart_point i) (C.radius_pos i)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.BaseCover.fillingPatch_disjoint
    (C : SpecialPeriods.Threefold.BaseCover) {i j : SpecialPeriods.Threefold.Puncture}
    (hij : i ≠ j) :
    Disjoint (C.fillingPatch i : Set SpecialPeriods.TriangleCompactifiedOrbitSpace)
      (C.fillingPatch j : Set SpecialPeriods.TriangleCompactifiedOrbitSpace) :=
  C.pairwise_disjoint hij

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.BaseCover.point_mem_fillingPatch_iff
    (C : SpecialPeriods.Threefold.BaseCover) (i j : SpecialPeriods.Threefold.Puncture) :
    SpecialPeriods.Threefold.puncturePoint i ∈ C.fillingPatch j ↔ i = j := by
  constructor
  · intro h
    by_contra hij
    exact Set.disjoint_left.mp (C.fillingPatch_disjoint hij) (C.point_mem_fillingPatch i) h
  · rintro rfl
    exact C.point_mem_fillingPatch i

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.BaseCover.chart_eq_zero_iff
    (C : SpecialPeriods.Threefold.BaseCover) (i : SpecialPeriods.Threefold.Puncture)
    {x : SpecialPeriods.TriangleCompactifiedOrbitSpace} (hx : x ∈ C.fillingPatch i) :
    SpecialPeriods.Threefold.punctureChart i x = 0 ↔
      x = SpecialPeriods.Threefold.puncturePoint i :=
  SpecialPeriods.Threefold.punctureChart_eq_zero_iff i (C.fillingPatch_subset_chart i hx)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.BaseCover.inverse_mem_fillingPatch
    (C : SpecialPeriods.Threefold.BaseCover) (i : SpecialPeriods.Threefold.Puncture) {z : ℂ}
    (hz : z ∈ Metric.ball 0 (C.radius i)) :
    (SpecialPeriods.Threefold.punctureChart i).symm z ∈ C.fillingPatch i := by
  have ht := C.coordinateBall_subset_target i hz
  refine ⟨(SpecialPeriods.Threefold.punctureChart i).map_target ht, ?_⟩
  change
    SpecialPeriods.Threefold.punctureChart i ((SpecialPeriods.Threefold.punctureChart i).symm z) ∈
      Metric.ball 0 (C.radius i)
  rw [(SpecialPeriods.Threefold.punctureChart i).right_inv ht]
  exact hz

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem
    SpecialPeriods.Threefold.exists_baseCover_below (R : Puncture → ℝ) (hR : ∀ i, 0 < R i) :
    ∃ C : BaseCover, ∀ i, C.radius i < R i := by
  obtain ⟨r, hr, _, _, hdisj⟩ :=
    exists_pairwise_disjoint_coordinateDiscs puncturePoint puncturePoint_injective punctureChart
      puncturePoint_mem_source punctureChart_point (fun _ => ⊤) (fun _ => trivial)
      (fun i => Min.min (R i) (punctureChartRadius i))
      (fun i => lt_min (hR i) (punctureChartRadius_pos i))
  exact
    ⟨{  radius := r
        radius_pos := fun i => (hr i).1
        radius_lt_chart := fun i => (hr i).2.trans_le (min_le_right _ _)
        pairwise_disjoint := hdisj }, fun i => (hr i).2.trans_le (min_le_left _ _)⟩

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Threefold.sphereRadiusCap
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere)) :
    Puncture → ℝ
  | none => (SpecialPeriods.Construction.cuspDataOfSphere π hπ h₀ h₁).radius
  | some _ => 1

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.sphereRadiusCap_pos
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere))
    (i : Puncture) : 0 < sphereRadiusCap π hπ h₀ h₁ i := by
  cases i with
  | none => exact (SpecialPeriods.Construction.cuspDataOfSphere π hπ h₀ h₁).radius_pos
  | some j => norm_num [sphereRadiusCap]

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Threefold.baseCoverOfSphere
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere)) :
    BaseCover :=
  (exists_baseCover_below (sphereRadiusCap π hπ h₀ h₁) (sphereRadiusCap_pos π hπ h₀ h₁)).choose

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.baseCoverOfSphere_radius_lt_cap
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere))
    (i : Puncture) : (baseCoverOfSphere π hπ h₀ h₁).radius i < sphereRadiusCap π hπ h₀ h₁ i :=
  (exists_baseCover_below (sphereRadiusCap π hπ h₀ h₁)
        (sphereRadiusCap_pos π hπ h₀ h₁)).choose_spec
    i

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.baseCoverOfSphere_cusp_radius_bounds
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere)) :
    0 < (baseCoverOfSphere π hπ h₀ h₁).radius Option.none ∧
      (baseCoverOfSphere π hπ h₀ h₁).radius Option.none <
          (SpecialPeriods.Construction.cuspDataOfSphere π hπ h₀ h₁).radius ∧
        (baseCoverOfSphere π hπ h₀ h₁).radius Option.none <
          SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width :=
  ⟨(baseCoverOfSphere π hπ h₀ h₁).radius_pos Option.none,
    baseCoverOfSphere_radius_lt_cap π hπ h₀ h₁ Option.none,
    (baseCoverOfSphere π hπ h₀ h₁).radius_lt_chart Option.none⟩

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Threefold.regularPatch :
    TopologicalSpace.Opens SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  ⟨({ SpecialPeriods.triangleCuspPoint, SpecialPeriods.triangleCompactifiedCenterOne,
          SpecialPeriods.triangleCompactifiedCenterTwo } :
        Set SpecialPeriods.TriangleCompactifiedOrbitSpace)ᶜ,
    (((Set.finite_singleton SpecialPeriods.triangleCompactifiedCenterTwo).insert
            SpecialPeriods.triangleCompactifiedCenterOne).insert
        SpecialPeriods.triangleCuspPoint).isClosed.isOpen_compl⟩

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
private theorem SpecialPeriods.Threefold.mem_regularPatch
    (x : SpecialPeriods.TriangleCompactifiedOrbitSpace) :
    x ∈ regularPatch ↔
      x ≠ SpecialPeriods.triangleCuspPoint ∧
        x ≠ SpecialPeriods.triangleCompactifiedCenterOne ∧
          x ≠ SpecialPeriods.triangleCompactifiedCenterTwo := by
  simp only [regularPatch, TopologicalSpace.Opens.mem_mk, Set.mem_compl_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff, not_or]

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.openInclusion_mem_regularPatch_iff
    (q : SpecialPeriods.TriangleOrbitSpace) :
    SpecialPeriods.triangleOpenInclusion q ∈ regularPatch ↔
      q ∈ SpecialPeriods.triangleOrbitRegularDomain := by
  rw [mem_regularPatch, SpecialPeriods.triangleOrbitRegularDomain_mem_iff]
  constructor
  · rintro ⟨_, h₁, h₂⟩
    exact
      ⟨fun h => h₁ (congrArg SpecialPeriods.triangleOpenInclusion h), fun h =>
        h₂ (congrArg SpecialPeriods.triangleOpenInclusion h)⟩
  · rintro ⟨h₁, h₂⟩
    exact
      ⟨SpecialPeriods.triangleOpenInclusion_ne_cusp q, fun h => h₁ (OnePoint.coe_injective h),
        fun h => h₂ (OnePoint.coe_injective h)⟩

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Threefold.regularInclusion :
    SpecialPeriods.TriangleRegularQuotient → SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  SpecialPeriods.triangleOpenInclusion ∘ SpecialPeriods.triangleRegularToOrbit

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.regularInclusion_isOpenEmbedding :
    Topology.IsOpenEmbedding regularInclusion :=
  SpecialPeriods.triangleOpenInclusion_isOpenEmbedding.comp
    SpecialPeriods.triangleRegularToOrbit_isOpenEmbedding

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.regularInclusion_mem
    (q : SpecialPeriods.TriangleRegularQuotient) : regularInclusion q ∈ regularPatch := by
  apply (openInclusion_mem_regularPatch_iff (SpecialPeriods.triangleRegularToOrbit q)).mpr
  exact Set.mem_range_self q

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.regularInclusion_range :
    Set.range regularInclusion =
      (regularPatch : Set SpecialPeriods.TriangleCompactifiedOrbitSpace) := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    exact regularInclusion_mem q
  · intro hx
    obtain ⟨q, hq⟩ := OnePoint.ne_infty_iff_exists.mp ((mem_regularPatch x).mp hx).1
    have hq' : SpecialPeriods.triangleOpenInclusion q = x := hq
    have hreg : q ∈ SpecialPeriods.triangleOrbitRegularDomain :=
      (openInclusion_mem_regularPatch_iff q).mp (hq' ▸ hx)
    obtain ⟨r, hr⟩ := hreg
    exact ⟨r, (congrArg SpecialPeriods.triangleOpenInclusion hr).trans hq'⟩

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.regularInclusion_isLocalDiffeomorph :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω regularInclusion := by
  intro q
  have hreg : IsLocalDiffeomorphAt 𝓘(ℂ) 𝓘(ℂ) ω SpecialPeriods.triangleRegularToOrbit q :=
    (SpecialPeriods.triangleRegularOrbitBiholomorph.isLocalDiffeomorph q).comp (K := 𝓘(ℂ)) (P :=
      SpecialPeriods.TriangleOrbitSpace)
      (isLocalDiffeomorph_subtypeVal 𝓘(ℂ) SpecialPeriods.triangleOrbitRegularDomain
        (SpecialPeriods.triangleRegularOrbitBiholomorph q))
  exact
    hreg.comp (K := 𝓘(ℂ)) (P := SpecialPeriods.TriangleCompactifiedOrbitSpace)
      (SpecialPeriods.triangleOpenInclusion_isLocalDiffeomorph
        (SpecialPeriods.triangleRegularToOrbit q))

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Threefold.regularInclusionToPatch
    (q : SpecialPeriods.TriangleRegularQuotient) : regularPatch :=
  ⟨regularInclusion q, regularInclusion_mem q⟩

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.regularInclusionToPatch_isLocalDiffeomorph :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω regularInclusionToPatch :=
  isLocalDiffeomorph_codRestrictOpens 𝓘(ℂ) 𝓘(ℂ) regularInclusion_isLocalDiffeomorph regularPatch
    regularInclusion_mem

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.regularInclusionToPatch_bijective :
    Function.Bijective regularInclusionToPatch := by
  constructor
  · intro q r h
    exact regularInclusion_isOpenEmbedding.injective (congrArg Subtype.val h)
  · intro x
    have hx : x.val ∈ Set.range regularInclusion := by
      rw [regularInclusion_range]
      exact x.property
    obtain ⟨q, hq⟩ := hx
    exact ⟨q, Subtype.ext hq⟩

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Threefold.regularBiholomorph :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleRegularQuotient regularPatch ω :=
  regularInclusionToPatch_isLocalDiffeomorph.diffeomorphOfBijective
    regularInclusionToPatch_bijective

private abbrev SpecialPeriods.Threefold.Index :=
  Option Puncture

private theorem SpecialPeriods.Threefold.mem_regularPatch_iff_ne_puncture
    (x : SpecialPeriods.TriangleCompactifiedOrbitSpace) :
    x ∈ regularPatch ↔ ∀ i : Puncture, x ≠ puncturePoint i := by
  rw [mem_regularPatch]
  constructor
  · rintro ⟨hc, h₁, h₂⟩ i
    cases i with
    | none => exact hc
    | some j => cases j <;> assumption
  · intro h
    exact ⟨h Option.none, h (Option.some .three), h (Option.some .four)⟩

private theorem SpecialPeriods.Threefold.not_mem_regularPatch_iff
    (x : SpecialPeriods.TriangleCompactifiedOrbitSpace) :
    x ∉ regularPatch ↔ ∃ i : Puncture, x = puncturePoint i := by
  classical
  rw [mem_regularPatch_iff_ne_puncture]
  simp only [Classical.not_forall, ne_eq, Classical.not_not]

private def SpecialPeriods.Threefold.BaseCover.patch (C : SpecialPeriods.Threefold.BaseCover) :
    SpecialPeriods.Threefold.Index →
      TopologicalSpace.Opens SpecialPeriods.TriangleCompactifiedOrbitSpace
  | none => SpecialPeriods.Threefold.regularPatch
  | some i => C.fillingPatch i

private theorem
    SpecialPeriods.Threefold.BaseCover.exists_patch (C : SpecialPeriods.Threefold.BaseCover)
    (x : SpecialPeriods.TriangleCompactifiedOrbitSpace) :
    ∃ i : SpecialPeriods.Threefold.Index, x ∈ C.patch i := by
  classical
  by_cases hx : x ∈ SpecialPeriods.Threefold.regularPatch
  · exact ⟨Option.none, hx⟩
  · obtain ⟨i, rfl⟩ := (SpecialPeriods.Threefold.not_mem_regularPatch_iff x).mp hx
    exact ⟨Option.some i, C.point_mem_fillingPatch i⟩

private theorem
    SpecialPeriods.Threefold.BaseCover.isOpenCover (C : SpecialPeriods.Threefold.BaseCover) :
    TopologicalSpace.IsOpenCover C.patch := by
  change (⨆ i, C.patch i) = ⊤
  apply top_unique
  intro x _
  obtain ⟨i, hi⟩ := C.exists_patch x
  exact (le_iSup C.patch i) hi

private theorem
    SpecialPeriods.Threefold.BaseCover.patch_iUnion (C : SpecialPeriods.Threefold.BaseCover) :
    ⋃ i : SpecialPeriods.Threefold.Index,
        (C.patch i : Set SpecialPeriods.TriangleCompactifiedOrbitSpace) =
      Set.univ :=
  C.isOpenCover.iSup_set_eq_univ

private theorem SpecialPeriods.Threefold.BaseCover.fillingPatch_regular_iff
    (C : SpecialPeriods.Threefold.BaseCover) (i : SpecialPeriods.Threefold.Puncture)
    {x : SpecialPeriods.TriangleCompactifiedOrbitSpace} (hx : x ∈ C.fillingPatch i) :
    x ∈ SpecialPeriods.Threefold.regularPatch ↔ x ≠ SpecialPeriods.Threefold.puncturePoint i := by
  constructor
  · intro h
    exact (SpecialPeriods.Threefold.mem_regularPatch_iff_ne_puncture x).mp h i
  · intro hne
    apply (SpecialPeriods.Threefold.mem_regularPatch_iff_ne_puncture x).mpr
    intro j hxj
    have hji : j = i := (C.point_mem_fillingPatch_iff j i).mp (hxj ▸ hx)
    exact hne (hxj.trans (congrArg SpecialPeriods.Threefold.puncturePoint hji))

private theorem SpecialPeriods.Threefold.BaseCover.fillingPatch_regular_iff_coordinate_ne_zero
    (C : SpecialPeriods.Threefold.BaseCover) (i : SpecialPeriods.Threefold.Puncture)
    {x : SpecialPeriods.TriangleCompactifiedOrbitSpace} (hx : x ∈ C.fillingPatch i) :
    x ∈ SpecialPeriods.Threefold.regularPatch ↔ SpecialPeriods.Threefold.punctureChart i x ≠ 0 :=
  (C.fillingPatch_regular_iff i hx).trans (not_congr (C.chart_eq_zero_iff i hx)).symm

private theorem SpecialPeriods.Threefold.BaseCover.inverse_mem_regular_iff
    (C : SpecialPeriods.Threefold.BaseCover) (i : SpecialPeriods.Threefold.Puncture) {z : ℂ}
    (hz : z ∈ Metric.ball 0 (C.radius i)) :
    (SpecialPeriods.Threefold.punctureChart i).symm z ∈ SpecialPeriods.Threefold.regularPatch ↔
      z ≠ 0 := by
  rw [C.fillingPatch_regular_iff_coordinate_ne_zero i (C.inverse_mem_fillingPatch i hz),
    (SpecialPeriods.Threefold.punctureChart i).right_inv (C.coordinateBall_subset_target i hz)]

/-- The open complex coordinate ball of radius `r`. -/
public
def SpecialPeriods.Threefold.coordinateBall (r : ℝ) : TopologicalSpace.Opens ℂ :=
  ⟨Metric.ball 0 r, Metric.isOpen_ball⟩

@[simp]
public
theorem SpecialPeriods.Threefold.mem_coordinateBall (r : ℝ) (z : ℂ) :
    z ∈ coordinateBall r ↔ z ∈ Metric.ball 0 r :=
  Iff.rfl

private def SpecialPeriods.Threefold.coordinateDiscForward {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] (e : PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) X ℂ ω) (r : ℝ) :
    coordinateDisc e.toOpenPartialHomeomorph r → coordinateBall r := fun x => ⟨e x, x.property.2⟩

private def SpecialPeriods.Threefold.coordinateDiscInverse {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] (e : PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) X ℂ ω) (r : ℝ)
    (hball : Metric.ball 0 r ⊆ e.target) :
    coordinateBall r → coordinateDisc e.toOpenPartialHomeomorph r := fun z =>
  ⟨e.symm z, e.map_target (hball z.property),
    by
    change e (e.symm (z : ℂ)) ∈ Metric.ball 0 r
    have he : e (e.symm (z : ℂ)) = (z : ℂ) := e.right_inv (hball z.property)
    exact he.symm ▸ z.property⟩

private theorem SpecialPeriods.Threefold.coordinateDiscForward_holomorphic {X : Type*}
    [TopologicalSpace X] [ChartedSpace ℂ X] (e : PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) X ℂ ω) (r : ℝ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (coordinateDiscForward e r) := by
  have hf :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun x : coordinateDisc e.toOpenPartialHomeomorph r => e (x : X)) :=
    e.contMDiffOn.comp_contMDiff contMDiff_subtype_val (fun x => x.property.1)
  intro x
  have h :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun y => (coordinateDiscForward e r y : ℂ)) x ↔
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (coordinateDiscForward e r) x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact h.mp (hf x)

private theorem SpecialPeriods.Threefold.coordinateDiscInverse_holomorphic {X : Type*}
    [TopologicalSpace X] [ChartedSpace ℂ X] (e : PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) X ℂ ω) (r : ℝ)
    (hball : Metric.ball 0 r ⊆ e.target) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (coordinateDiscInverse e r hball) := by
  have hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z : coordinateBall r => e.symm (z : ℂ)) :=
    e.symm.contMDiffOn.comp_contMDiff contMDiff_subtype_val (fun z => hball z.property)
  intro z
  have h :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun w => (coordinateDiscInverse e r hball w : X)) z ↔
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (coordinateDiscInverse e r hball) z :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact h.mp (hf z)

private def SpecialPeriods.Threefold.coordinateDiscBiholomorph {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] (e : PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) X ℂ ω) (r : ℝ)
    (hball : Metric.ball 0 r ⊆ e.target) :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (coordinateDisc e.toOpenPartialHomeomorph r) (coordinateBall r) ω
    where
  toFun := coordinateDiscForward e r
  invFun := coordinateDiscInverse e r hball
  left_inv x := Subtype.ext (e.left_inv x.property.1)
  right_inv z := Subtype.ext (e.right_inv (hball z.property))
  contMDiff_toFun := coordinateDiscForward_holomorphic e r
  contMDiff_invFun := coordinateDiscInverse_holomorphic e r hball

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Threefold.BaseCover.fillingChart (C : SpecialPeriods.Threefold.BaseCover)
    (i : SpecialPeriods.Threefold.Puncture) :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (C.fillingPatch i)
      (SpecialPeriods.Threefold.coordinateBall (C.radius i)) ω :=
  SpecialPeriods.Threefold.coordinateDiscBiholomorph (SpecialPeriods.Threefold.puncturePartial i)
    (C.radius i) (C.coordinateBall_subset_target i)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def
    SpecialPeriods.Threefold.BaseCover.fillingEmbedding (C : SpecialPeriods.Threefold.BaseCover)
    (i : SpecialPeriods.Threefold.Puncture) :
    SpecialPeriods.Threefold.coordinateBall (C.radius i) →
      SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  fun z => ((C.fillingChart i).symm z : SpecialPeriods.TriangleCompactifiedOrbitSpace)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
private theorem SpecialPeriods.Threefold.BaseCover.punctureChart_fillingEmbedding
    (C : SpecialPeriods.Threefold.BaseCover) (i : SpecialPeriods.Threefold.Puncture)
    (z : SpecialPeriods.Threefold.coordinateBall (C.radius i)) :
    SpecialPeriods.Threefold.punctureChart i (C.fillingEmbedding i z) = (z : ℂ) :=
  (SpecialPeriods.Threefold.punctureChart i).right_inv
    (C.coordinateBall_subset_target i z.property)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.BaseCover.fillingEmbedding_mem_regular_iff
    (C : SpecialPeriods.Threefold.BaseCover) (i : SpecialPeriods.Threefold.Puncture)
    (z : SpecialPeriods.Threefold.coordinateBall (C.radius i)) :
    C.fillingEmbedding i z ∈ SpecialPeriods.Threefold.regularPatch ↔ (z : ℂ) ≠ 0 :=
  C.inverse_mem_regular_iff i z.property

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.BaseCover.fillingEmbedding_eq_point_iff
    (C : SpecialPeriods.Threefold.BaseCover) (i : SpecialPeriods.Threefold.Puncture)
    (z : SpecialPeriods.Threefold.coordinateBall (C.radius i)) :
    C.fillingEmbedding i z = SpecialPeriods.Threefold.puncturePoint i ↔ (z : ℂ) = 0 := by
  constructor
  · intro h
    have he := congrArg (SpecialPeriods.Threefold.punctureChart i) h
    simpa only [C.punctureChart_fillingEmbedding,
      SpecialPeriods.Threefold.punctureChart_point] using he
  · intro h
    change
      (SpecialPeriods.Threefold.punctureChart i).symm (z : ℂ) =
        SpecialPeriods.Threefold.puncturePoint i
    rw [h, SpecialPeriods.Threefold.punctureChart_symm_zero]

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
private abbrev SpecialPeriods.Threefold.regularFamilyData (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint :=
  PeriodFamily.regularData P h₁ h₂

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
private abbrev SpecialPeriods.Threefold.RegularFamily (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    Type :=
  (regularFamilyData P h₁ h₂).Space

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
@[instance_reducible]
private def SpecialPeriods.Threefold.regularFamilyChartedSpace (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    ChartedSpace (ℂ × ComplexPlane₂) (RegularFamily P h₁ h₂) :=
  (regularFamilyData P h₁ h₂).chartedSpace (PeriodFamily.regularCovering P h₁ h₂)

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.regularFamily_t2Space (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    T2Space (RegularFamily P h₁ h₂) :=
  (regularFamilyData P h₁ h₂).spaceT2Space_of_properlyDiscontinuous
    (PeriodFamily.regularCovering P h₁ h₂)

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem
    SpecialPeriods.Threefold.regularFamily_secondCountable (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    SecondCountableTopology (RegularFamily P h₁ h₂) :=
  (regularFamilyData P h₁ h₂).spaceSecondCountable (PeriodFamily.regularCovering P h₁ h₂)

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.regularFamily_isManifold (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    letI := regularFamilyChartedSpace P h₁ h₂
    IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (RegularFamily P h₁ h₂) :=
  (regularFamilyData P h₁ h₂).isManifold (PeriodFamily.regularCovering P h₁ h₂)

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Threefold.regularFamilyProjection (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    RegularFamily P h₁ h₂ → regularPatch :=
  regularBiholomorph ∘ (regularFamilyData P h₁ h₂).projection

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem
    SpecialPeriods.Threefold.regularFamilyProjection_proper (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    IsProperMap (regularFamilyProjection P h₁ h₂) :=
  regularBiholomorph.toHomeomorph.isProperMap.comp
    ((regularFamilyData P h₁ h₂).projection_proper (PeriodFamily.regularCovering P h₁ h₂))

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Threefold.regularFamilyProjectionToBase (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    RegularFamily P h₁ h₂ → SpecialPeriods.TriangleCompactifiedOrbitSpace := fun x =>
  (regularFamilyProjection P h₁ h₂ x : SpecialPeriods.TriangleCompactifiedOrbitSpace)

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.Threefold.regularFamilyZeroSection (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    regularPatch → RegularFamily P h₁ h₂ :=
  (regularFamilyData P h₁ h₂).zeroSection ∘ regularBiholomorph.symm

attribute [local instance] SpecialPeriods.triangleRegularQuotientChartedSpace
    SpecialPeriods.triangleOrbitChartedSpace SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.Threefold.regularFamilyZeroSection_continuous
    (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    Continuous (regularFamilyZeroSection P h₁ h₂) :=
  (regularFamilyData P h₁ h₂).zeroSection_continuous.comp regularBiholomorph.symm.continuous

end Mathoverflow1973

end
