/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Threefold.SpecialPeriods5
public import LeanPool.HopfProblem.CuspFibre.CuspCentralHomology1
import all LeanPool.HopfProblem.Uniformization.HolomorphicCousin
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.Uniformization.CuspUniformization1
import all LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods1
import all LeanPool.HopfProblem.Foundations.LocalOrbitQuotient
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods2
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods3
import all LeanPool.HopfProblem.Threefold.SpecialPeriods4
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods4
import all LeanPool.HopfProblem.Threefold.SpecialPeriods5
import all LeanPool.HopfProblem.CuspFibre.CuspCentralHomology1

/-!
# Hopf problem: uniformization · special periods 5

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

private theorem SpecialPeriods.exists_covariant_tau_of_triangle_source (F : ℍ → ℂ)
    (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (h₃ :
      ∀ a : ℍ,
        F a = 0 → ∃ k : ℕ, analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (a : ℂ) = (3 * k : ℕ))
    (h₂ :
      ∀ a : ℍ,
        F a = 1728 →
          ∃ k : ℕ,
            analyticOrderAt (fun z => F (UpperHalfPlane.ofComplex z) - 1728) (a : ℂ) =
              (2 * k : ℕ))
    (hF₁ : ∀ z : ℍ, F (Triangle.generatorOneSL • z) = F z)
    (hF₂ : ∀ z : ℍ, F (Triangle.generatorTwoSL • z) = F z)
    (horder₁ : analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (Triangle.centerOne : ℂ) = 3)
    (horder₂ :
      analyticOrderAt (fun z : ℂ => F (UpperHalfPlane.ofComplex z) - 1728)
          (Triangle.centerTwo : ℂ) =
        4)
    (Fc : ℂ → ℂ) (hFc : MeromorphicAt Fc 0) (hFcorder : meromorphicOrderAt Fc 0 = (-1 : ℤ))
    {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hsource :
      ∀ z : ℍ,
        ‖Function.Periodic.qParam Triangle.width (z : ℂ)‖ < r₀ →
          F z = Fc (Function.Periodic.qParam Triangle.width (z : ℂ))) :
    ∃ τ : ℍ → ℍ,
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ ∧
        (∀ z : ℍ, modularJ (τ z) = F z) ∧
          TauCovariant τ ∧
            τ Triangle.centerOne = rhoPoint ∧
              τ Triangle.centerTwo = UpperHalfPlane.I ∧
                ∃ r > 0,
                  r < r₀ ∧
                    r < 1 ∧
                      ∃ h : ℂ → ℂ,
                        AnalyticOnNhd ℂ h (Metric.ball 0 r) ∧
                          ∀ z : ℍ,
                            ‖Function.Periodic.qParam Triangle.width (z : ℂ)‖ < r →
                              (τ z : ℂ) =
                                TauCusp.correctedLogarithmWidth Triangle.width h (z : ℂ) := by
  have hFa : F Triangle.centerOne = 0 := by
    have hh :=
      (analyticOrderAt_ne_zero.mp
          (show analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (Triangle.centerOne : ℂ) ≠ 0 by
            rw [horder₁]; norm_num)).2
    simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using hh
  have hFb : F Triangle.centerTwo = 1728 := by
    have hh :=
      (analyticOrderAt_ne_zero.mp
          (show
            analyticOrderAt (fun z : ℂ => F (UpperHalfPlane.ofComplex z) - 1728)
                (Triangle.centerTwo : ℂ) ≠
              0
            by rw [horder₂]; norm_num)).2
    exact sub_eq_zero.mp (by simpa only [UpperHalfPlane.ofComplex_apply] using hh)
  obtain ⟨_, _, _, τ, hτ, hJ, r, hr, hrr₀, hr1, h, hh, _, hformula⟩ :=
    TauCusp.exists_global_normalized_lift_of_simplePole_cusp F hF h₃ h₂ Triangle.width
      Triangle.width_pos Fc hFc hFcorder hr₀ hsource
  have hC := tau_cusp_monodromy_of_formula hτ hr hformula
  have hCtr :
    Matrix.trace (ModularGroup.T⁻¹).val = 2 ∨ Matrix.trace (ModularGroup.T⁻¹).val = -2 := by
    left
    rw [modularSL_trace_inv]
    norm_num [Matrix.trace_fin_two, ModularGroup.T]
  obtain ⟨γ, hcov, hγa, hγb⟩ :=
    exists_normalized_covariant_modular_translate F hτ hJ hFa hFb hF₁ hF₂ horder₁ horder₂
      ModularGroup.T⁻¹ hCtr hC
  have hab : τ Triangle.centerOne ≠ τ Triangle.centerTwo := by
    intro he
    have hj := congrArg modularJ he
    rw [hJ, hJ, hFa, hFb] at hj
    norm_num at hj
  have hcomm :=
    modular_translate_commutes_Tinv_of_cusp_covariance γ hC hcov Triangle.centerOne
      Triangle.centerTwo hab
  obtain ⟨n, hn⟩ := modularSL_integer_translation_coe_of_commutes_T_inv_action γ hcomm
  refine
    ⟨fun z => γ • τ z, (modularSL_holomorphic γ).comp hτ,
      (fun z => (modularJ_SL_invariant γ (τ z)).trans (hJ z)), hcov, hγa, hγb, r, hr, hrr₀, hr1,
      fun q => h q + (n : ℂ), hh.add analyticOnNhd_const, ?_⟩
  intro z hz
  rw [hn, hformula z hz]
  simp only [TauCusp.correctedLogarithmWidth]
  ring

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.TriangleSource.exists_tau_of_normalized_sphere_equivalence
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere)) :
    ∃ τ : ℍ → ℍ,
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ ∧
        (∀ z : ℍ,
            SpecialPeriods.modularJ (τ z) = SpecialPeriods.MuTorsor.SourceOrders.sourceJ π z) ∧
          SpecialPeriods.TauCovariant τ ∧
            τ SpecialPeriods.Triangle.centerOne = SpecialPeriods.rhoPoint ∧
              τ SpecialPeriods.Triangle.centerTwo = UpperHalfPlane.I ∧
                ∃ r > 0,
                  r < 1 ∧
                    ∃ h : ℂ → ℂ,
                      AnalyticOnNhd ℂ h (Metric.ball 0 r) ∧
                        ∀ z : ℍ,
                          ‖Function.Periodic.qParam SpecialPeriods.Triangle.width (z : ℂ)‖ < r →
                            (τ z : ℂ) =
                              SpecialPeriods.TauCusp.correctedLogarithmWidth
                                SpecialPeriods.Triangle.width h (z : ℂ) := by
  have h₃ :
    ∀ z : ℍ,
      SpecialPeriods.MuTorsor.SourceOrders.sourceJ π z = 0 →
        ∃ k : ℕ,
          analyticOrderAt
              (SpecialPeriods.MuTorsor.SourceOrders.sourceJ π ∘ UpperHalfPlane.ofComplex)
              (z : ℂ) =
            (3 * k : ℕ) := by
    intro z hz
    exact
      ⟨1, by
        simpa using SpecialPeriods.MuTorsor.SourceOrders.sourceJ_order_of_eq_zero π hπ h₀ z hz⟩
  have h₂ :
    ∀ z : ℍ,
      SpecialPeriods.MuTorsor.SourceOrders.sourceJ π z = 1728 →
        ∃ k : ℕ,
          analyticOrderAt
              (fun w =>
                SpecialPeriods.MuTorsor.SourceOrders.sourceJ π (UpperHalfPlane.ofComplex w) -
                  1728)
              (z : ℂ) =
            (2 * k : ℕ) := by
    intro z hz
    exact
      ⟨2, by
        simpa using
          SpecialPeriods.MuTorsor.SourceOrders.sourceJ_sub_1728_order_of_eq π hπ h₁ z hz⟩
  have hG₁ :
    ∀ z : ℍ,
      SpecialPeriods.MuTorsor.SourceOrders.sourceJ π
          (SpecialPeriods.Triangle.generatorOneSL • z) =
        SpecialPeriods.MuTorsor.SourceOrders.sourceJ π z := by
    intro z
    simpa only [SpecialPeriods.triangleGeometricRepresentation_generator₁_apply] using
      SpecialPeriods.MuTorsor.SourceOrders.sourceJ_invariant π SpecialPeriods.triangleGenerator₁ z
  have hG₂ :
    ∀ z : ℍ,
      SpecialPeriods.MuTorsor.SourceOrders.sourceJ π
          (SpecialPeriods.Triangle.generatorTwoSL • z) =
        SpecialPeriods.MuTorsor.SourceOrders.sourceJ π z := by
    intro z
    simpa only [SpecialPeriods.triangleGeometricRepresentation_generator₂_apply] using
      SpecialPeriods.MuTorsor.SourceOrders.sourceJ_invariant π SpecialPeriods.triangleGenerator₂ z
  obtain ⟨r₀, hr₀, hsource⟩ := exists_cusp_formula_radius π hπ
  obtain ⟨τ, hτ, hJ, hcov, ha, hb, r, hr, _, hr1, h, hh, hformula⟩ :=
    SpecialPeriods.exists_covariant_tau_of_triangle_source
      (SpecialPeriods.MuTorsor.SourceOrders.sourceJ π)
      ((SpecialPeriods.MuTorsor.SourceOrders.sourceJ_holomorphic π hπ).mdifferentiable (by simp))
      h₃ h₂ hG₁ hG₂ (SpecialPeriods.MuTorsor.SourceOrders.sourceJ_order_centerOne π hπ h₀)
      (SpecialPeriods.MuTorsor.SourceOrders.sourceJ_sub_1728_order_centerTwo π hπ h₁)
      (meromorphicCuspJ π) (meromorphicCuspJ_meromorphicAt π hπ) (meromorphicCuspJ_order π hπ) hr₀
      hsource
  exact ⟨τ, hτ, hJ, hcov, ha, hb, r, hr, hr1, h, hh, hformula⟩

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.TriangleSource.tauOfSphere
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere)) :
    ℍ → ℍ :=
  (exists_tau_of_normalized_sphere_equivalence π hπ h₀ h₁).choose

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.TriangleSource.tauOfSphere_holomorphic
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere)) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (tauOfSphere π hπ h₀ h₁) :=
  (exists_tau_of_normalized_sphere_equivalence π hπ h₀ h₁).choose_spec.1

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.TriangleSource.tauOfSphere_modular
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere))
    (z : ℍ) :
    SpecialPeriods.modularJ (tauOfSphere π hπ h₀ h₁ z) =
      1728 * SpecialPeriods.BetaTorsor.finiteProjection π z :=
  (exists_tau_of_normalized_sphere_equivalence π hπ h₀ h₁).choose_spec.2.1 z

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.TriangleSource.tauOfSphere_covariant
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere)) :
    SpecialPeriods.TauCovariant (tauOfSphere π hπ h₀ h₁) :=
  (exists_tau_of_normalized_sphere_equivalence π hπ h₀ h₁).choose_spec.2.2.1

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.TriangleSource.tauOfSphere_cusp
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere)) :
    ∃ r > 0,
      r < 1 ∧
        ∃ h : ℂ → ℂ,
          AnalyticOnNhd ℂ h (Metric.ball 0 r) ∧
            ∀ z : ℍ,
              ‖Function.Periodic.qParam SpecialPeriods.Triangle.width (z : ℂ)‖ < r →
                (tauOfSphere π hπ h₀ h₁ z : ℂ) =
                  SpecialPeriods.TauCusp.correctedLogarithmWidth SpecialPeriods.Triangle.width h
                    (z : ℂ) :=
  (exists_tau_of_normalized_sphere_equivalence π hπ h₀ h₁).choose_spec.2.2.2.2.2

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.TriangleSource.cuspCorrectionUnit (h : ℂ → ℂ) (q : ℂ) : ℂ :=
  CuspUniformization.exponential (h q)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.TriangleSource.cuspCorrectionUnit_analyticOnNhd {h : ℂ → ℂ} {r : ℝ}
    (hh : AnalyticOnNhd ℂ h (Metric.ball 0 r)) :
    AnalyticOnNhd ℂ (cuspCorrectionUnit h) (Metric.ball 0 r) := by
  intro q hq
  exact CuspUniformization.exponential_holomorphic.contDiffAt.analyticAt.comp (hh q hq)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
private theorem SpecialPeriods.TriangleSource.cuspCorrectionUnit_ne_zero (h : ℂ → ℂ) (q : ℂ) :
    cuspCorrectionUnit h q ≠ 0 :=
  CuspUniformization.exponential_ne_zero _

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.TriangleSource.tauOfSphere_cusp_unit
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere)) :
    ∃ r > 0,
      ∃ u : ℂ → ℂ,
        AnalyticOnNhd ℂ u (Metric.ball 0 r) ∧
          u 0 ≠ 0 ∧
            ∀ z : ℍ,
              ‖Function.Periodic.qParam SpecialPeriods.Triangle.width (z : ℂ)‖ < r →
                Function.Periodic.qParam 1 (tauOfSphere π hπ h₀ h₁ z : ℂ) =
                  Function.Periodic.qParam SpecialPeriods.Triangle.width (z : ℂ) *
                    u (Function.Periodic.qParam SpecialPeriods.Triangle.width (z : ℂ)) := by
  obtain ⟨r, hr, _, h, hh, hformula⟩ := tauOfSphere_cusp π hπ h₀ h₁
  refine
    ⟨r, hr, cuspCorrectionUnit h, cuspCorrectionUnit_analyticOnNhd hh,
      cuspCorrectionUnit_ne_zero h 0, ?_⟩
  intro z hz
  rw [← SpecialPeriods.TauCusp.exponential_eq_qParam_one, hformula z hz]
  exact
    SpecialPeriods.TauCusp.correctedLogarithmWidth_exponential SpecialPeriods.Triangle.width h z

private def SpecialPeriods.MuTorsor.affinePermutation {B : Type*} (e : Equiv.Perm B) (a : B → ℂˣ)
    (b : B → ℂ) : Equiv.Perm (B × ℂ)
    where
  toFun p := (e p.1, (a p.1 : ℂ) * p.2 + b p.1)
  invFun p := (e.symm p.1, (a (e.symm p.1) : ℂ)⁻¹ * (p.2 - b (e.symm p.1)))
  left_inv := by
    rintro ⟨z, u⟩
    apply Prod.ext
    · exact e.symm_apply_apply z
    · simp only [Equiv.symm_apply_apply]
      rw [add_sub_cancel_right, ← mul_assoc, inv_mul_cancel₀ (a z).ne_zero, one_mul]
  right_inv := by
    rintro ⟨z, u⟩
    apply Prod.ext
    · exact e.apply_symm_apply z
    · dsimp
      rw [← mul_assoc, mul_inv_cancel₀ (a (e.symm z)).ne_zero, one_mul, sub_add_cancel]

private def SpecialPeriods.MuTorsor.generatorOneScale (τ : ℍ → ℍ) (z : ℍ) : ℂˣ :=
  Units.mk0 (-1 / (τ z : ℂ)) (div_ne_zero (neg_ne_zero.mpr one_ne_zero) (τ z).ne_zero)

private def SpecialPeriods.MuTorsor.generatorTwoScale (τ : ℍ → ℍ) (z : ℍ) : ℂˣ :=
  Units.mk0 (1 / (τ z : ℂ)) (div_ne_zero one_ne_zero (τ z).ne_zero)

private def SpecialPeriods.MuTorsor.generatorOneShift (τ : ℍ → ℍ) (z : ℍ) : ℂ :=
  1 / (τ z : ℂ)

private def SpecialPeriods.MuTorsor.generatorTwoShift (_z : ℍ) : ℂ :=
  1

@[simp]
private theorem SpecialPeriods.MuTorsor.generatorOneScale_val (τ : ℍ → ℍ) (z : ℍ) :
    (generatorOneScale τ z : ℂ) = -1 / (τ z : ℂ) :=
  rfl

@[simp]
private theorem SpecialPeriods.MuTorsor.generatorTwoScale_val (τ : ℍ → ℍ) (z : ℍ) :
    (generatorTwoScale τ z : ℂ) = 1 / (τ z : ℂ) :=
  rfl

private def SpecialPeriods.MuTorsor.generatorOne (τ : ℍ → ℍ) : Equiv.Perm (ℍ × ℂ) :=
  affinePermutation SpecialPeriods.Triangle.generatorOnePerm (generatorOneScale τ)
    (generatorOneShift τ)

private def SpecialPeriods.MuTorsor.generatorTwo (τ : ℍ → ℍ) : Equiv.Perm (ℍ × ℂ) :=
  affinePermutation SpecialPeriods.Triangle.generatorTwoPerm (generatorTwoScale τ)
    generatorTwoShift

@[simp]
private theorem SpecialPeriods.MuTorsor.generatorOne_apply (τ : ℍ → ℍ) (z : ℍ) (u : ℂ) :
    generatorOne τ (z, u) = (SpecialPeriods.Triangle.generatorOneSL • z, (1 - u) / (τ z : ℂ)) := by
  apply Prod.ext
  · rfl
  · change (-1 / (τ z : ℂ)) * u + 1 / (τ z : ℂ) = _
    ring

@[simp]
private theorem SpecialPeriods.MuTorsor.generatorTwo_apply (τ : ℍ → ℍ) (z : ℍ) (u : ℂ) :
    generatorTwo τ (z, u) = (SpecialPeriods.Triangle.generatorTwoSL • z, 1 + u / (τ z : ℂ)) := by
  apply Prod.ext
  · rfl
  · change (1 / (τ z : ℂ)) * u + 1 = _
    ring

private theorem SpecialPeriods.MuTorsor.generatorOne_cube {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) : generatorOne τ ^ 3 = 1 := by
  apply Equiv.ext
  rintro ⟨z, u⟩
  change generatorOne τ (generatorOne τ (generatorOne τ (z, u))) = (z, u)
  simp only [generatorOne_apply]
  apply Prod.ext
  · exact congrArg (fun e : Equiv.Perm ℍ => e z) SpecialPeriods.Triangle.generatorOnePerm_cube
  · dsimp
    rw [hτ.1 (SpecialPeriods.Triangle.generatorOneSL • z), hτ.1 z]
    have ht : (τ z : ℂ) ≠ 0 := (τ z).ne_zero
    have ht1 : (τ z : ℂ) - 1 ≠ 0 :=
      sub_ne_zero.mpr (by simpa only [Int.cast_one] using (τ z).ne_intCast 1)
    field_simp [ht, ht1]
    ring

private theorem SpecialPeriods.MuTorsor.generatorTwo_fourth {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) : generatorTwo τ ^ 4 = 1 := by
  apply Equiv.ext
  rintro ⟨z, u⟩
  change generatorTwo τ (generatorTwo τ (generatorTwo τ (generatorTwo τ (z, u)))) = (z, u)
  simp only [generatorTwo_apply]
  apply Prod.ext
  · exact congrArg (fun e : Equiv.Perm ℍ => e z) SpecialPeriods.Triangle.generatorTwoPerm_fourth
  · dsimp
    rw [hτ.2
        (SpecialPeriods.Triangle.generatorTwoSL • (SpecialPeriods.Triangle.generatorTwoSL • z)),
      hτ.2 (SpecialPeriods.Triangle.generatorTwoSL • z), hτ.2 z]
    field_simp [(τ z).ne_zero]
    ring

private def
    SpecialPeriods.MuTorsor.representation {τ : ℍ → ℍ} (hτ : SpecialPeriods.TauCovariant τ) :
    SpecialPeriods.TriangleGroup →* Equiv.Perm (ℍ × ℂ) :=
  SpecialPeriods.triangleLift (generatorOne τ) (generatorTwo τ) (generatorOne_cube hτ)
    (generatorTwo_fourth hτ)

@[simp]
private theorem SpecialPeriods.MuTorsor.representation_generator₁ {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) :
    representation hτ SpecialPeriods.triangleGenerator₁ = generatorOne τ :=
  SpecialPeriods.triangleLift_generator₁ ..

@[simp]
private theorem SpecialPeriods.MuTorsor.representation_generator₂ {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) :
    representation hτ SpecialPeriods.triangleGenerator₂ = generatorTwo τ :=
  SpecialPeriods.triangleLift_generator₂ ..

private theorem SpecialPeriods.MuTorsor.generatorOne_mul_generatorTwo_apply {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (z : ℍ) (u : ℂ) :
    (generatorOne τ * generatorTwo τ) (z, u) =
      (SpecialPeriods.Triangle.generatorOneSL • (SpecialPeriods.Triangle.generatorTwoSL • z),
        u) := by
  change generatorOne τ (generatorTwo τ (z, u)) = _
  rw [generatorTwo_apply, generatorOne_apply, hτ.2 z]
  congr 1
  field_simp [(τ z).ne_zero]
  ring

private theorem SpecialPeriods.MuTorsor.representation_cusp_snd {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (z : ℍ) (u : ℂ) :
    (representation hτ SpecialPeriods.triangleCuspGenerator (z, u)).2 = u := by
  rw [representation, SpecialPeriods.triangleLift_cusp]
  have he := (generatorOne τ * generatorTwo τ).apply_symm_apply (z, u)
  have hc := congrArg Prod.snd he
  rw [generatorOne_mul_generatorTwo_apply hτ] at hc
  exact hc

private theorem SpecialPeriods.MuTorsor.generatorOneScale_holomorphic {τ : ℍ → ℍ}
    (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => (generatorOneScale τ z : ℂ)) :=
  contMDiff_const.div₀ (UpperHalfPlane.contMDiff_coe.comp hτa) (fun z => (τ z).ne_zero)

private theorem SpecialPeriods.MuTorsor.generatorTwoScale_holomorphic {τ : ℍ → ℍ}
    (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => (generatorTwoScale τ z : ℂ)) :=
  contMDiff_const.div₀ (UpperHalfPlane.contMDiff_coe.comp hτa) (fun z => (τ z).ne_zero)

private theorem SpecialPeriods.MuTorsor.generatorOneShift_holomorphic {τ : ℍ → ℍ}
    (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (generatorOneShift τ) :=
  contMDiff_const.div₀ (UpperHalfPlane.contMDiff_coe.comp hτa) (fun z => (τ z).ne_zero)

private theorem SpecialPeriods.MuTorsor.generatorTwoShift_holomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω generatorTwoShift :=
  contMDiff_const

private def
    SpecialPeriods.MuTorsor.AffineFibres {G B : Type*} [Group G] (ρ : G →* Equiv.Perm (B × ℂ))
    (β : G →* Equiv.Perm B) (g : G) : Prop :=
  ∃ a : B → ℂˣ, ∃ b : B → ℂ, ∀ z u, ρ g (z, u) = (β g z, (a z : ℂ) * u + b z)

private theorem SpecialPeriods.MuTorsor.affine_coefficients_unique {G B : Type*} [Group G]
    (ρ : G →* Equiv.Perm (B × ℂ)) (β : G →* Equiv.Perm B) {g : G} {a c : B → ℂˣ} {b d : B → ℂ}
    (hf : ∀ z u, ρ g (z, u) = (β g z, (a z : ℂ) * u + b z))
    (hf' : ∀ z u, ρ g (z, u) = (β g z, (c z : ℂ) * u + d z)) : a = c ∧ b = d := by
  have hb : ∀ z, b z = d z := by
    intro z
    have h := congrArg Prod.snd ((hf z 0).symm.trans (hf' z 0))
    simpa only [MulZeroClass.mul_zero, zero_add] using h
  refine ⟨?_, funext hb⟩
  funext z
  apply Units.ext
  have h : (a z : ℂ) + b z = (c z : ℂ) + d z := by
    simpa only [mul_one] using congrArg Prod.snd ((hf z 1).symm.trans (hf' z 1))
  rw [hb z] at h
  exact add_right_cancel h

private theorem SpecialPeriods.MuTorsor.affine_one_formula {G B : Type*} [Group G]
    (ρ : G →* Equiv.Perm (B × ℂ)) (β : G →* Equiv.Perm B) (z : B) (u : ℂ) :
    ρ 1 (z, u) = (β 1 z, ((1 : ℂˣ) : ℂ) * u + 0) := by simp

private theorem SpecialPeriods.MuTorsor.affine_mul_formula {G B : Type*} [Group G]
    (ρ : G →* Equiv.Perm (B × ℂ)) (β : G →* Equiv.Perm B) {g h : G} {a c : B → ℂˣ} {b d : B → ℂ}
    (hg : ∀ z u, ρ g (z, u) = (β g z, (a z : ℂ) * u + b z))
    (hh : ∀ z u, ρ h (z, u) = (β h z, (c z : ℂ) * u + d z)) (z : B) (u : ℂ) :
    ρ (g * h) (z, u) =
      (β (g * h) z, ((a (β h z) * c z : ℂˣ) : ℂ) * u + ((a (β h z) : ℂ) * d z + b (β h z))) := by
  rw [map_mul, Equiv.Perm.mul_apply, hh, hg]
  apply Prod.ext
  · simp only [map_mul, Equiv.Perm.mul_apply]
  · simp only [Units.val_mul]
    ring

private theorem SpecialPeriods.MuTorsor.affine_inv_formula {G B : Type*} [Group G]
    (ρ : G →* Equiv.Perm (B × ℂ)) (β : G →* Equiv.Perm B) {g : G} {a : B → ℂˣ} {b : B → ℂ}
    (hg : ∀ z u, ρ g (z, u) = (β g z, (a z : ℂ) * u + b z)) (z : B) (u : ℂ) :
    ρ g⁻¹ (z, u) =
      (β g⁻¹ z, (((a (β g⁻¹ z))⁻¹ : ℂˣ) : ℂ) * u + (-((a (β g⁻¹ z) : ℂ)⁻¹ * b (β g⁻¹ z)))) := by
  apply (ρ g).injective
  have hc : ρ g (ρ g⁻¹ (z, u)) = (z, u) := by
    rw [map_inv, Equiv.Perm.inv_def]
    exact (ρ g).apply_symm_apply _
  rw [hc, hg]
  apply Prod.ext
  · rw [map_inv, Equiv.Perm.inv_def]
    exact ((β g).apply_symm_apply z).symm
  · simp only [Units.val_inv_eq_inv_val, mul_add, mul_neg, ← mul_assoc,
      mul_inv_cancel₀ (a (β g⁻¹ z)).ne_zero, one_mul, neg_add_cancel_right]

private theorem SpecialPeriods.MuTorsor.affineFibres_one {G B : Type*} [Group G]
    (ρ : G →* Equiv.Perm (B × ℂ)) (β : G →* Equiv.Perm B) : AffineFibres ρ β 1 :=
  ⟨fun _ => 1, fun _ => 0, affine_one_formula ρ β⟩

private theorem SpecialPeriods.MuTorsor.affineFibres_mul {G B : Type*} [Group G]
    (ρ : G →* Equiv.Perm (B × ℂ)) (β : G →* Equiv.Perm B) {g h : G} (hg : AffineFibres ρ β g)
    (hh : AffineFibres ρ β h) : AffineFibres ρ β (g * h) := by
  obtain ⟨a, b, ha⟩ := hg
  obtain ⟨c, d, hc⟩ := hh
  exact
    ⟨fun z => a (β h z) * c z, fun z => (a (β h z) : ℂ) * d z + b (β h z),
      affine_mul_formula ρ β ha hc⟩

private theorem SpecialPeriods.MuTorsor.affineFibres_inv {G B : Type*} [Group G]
    (ρ : G →* Equiv.Perm (B × ℂ)) (β : G →* Equiv.Perm B) {g : G} (hg : AffineFibres ρ β g) :
    AffineFibres ρ β g⁻¹ := by
  obtain ⟨a, b, ha⟩ := hg
  exact
    ⟨fun z => (a (β g⁻¹ z))⁻¹, fun z => -((a (β g⁻¹ z) : ℂ)⁻¹ * b (β g⁻¹ z)),
      affine_inv_formula ρ β ha⟩

private def
    SpecialPeriods.MuTorsor.affineSubgroup {G B : Type*} [Group G] (ρ : G →* Equiv.Perm (B × ℂ))
    (β : G →* Equiv.Perm B) : Subgroup G
    where
  carrier := AffineFibres ρ β
  one_mem' := affineFibres_one ρ β
  mul_mem' := affineFibres_mul ρ β
  inv_mem' := affineFibres_inv ρ β

private def SpecialPeriods.MuTorsor.scale {G B : Type*} [Group G] (ρ : G →* Equiv.Perm (B × ℂ))
    (β : G →* Equiv.Perm B) (h_all : ∀ g, AffineFibres ρ β g) (g : G) : B → ℂˣ :=
  (h_all g).choose

private def SpecialPeriods.MuTorsor.shift {G B : Type*} [Group G] (ρ : G →* Equiv.Perm (B × ℂ))
    (β : G →* Equiv.Perm B) (h_all : ∀ g, AffineFibres ρ β g) (g : G) : B → ℂ :=
  (h_all g).choose_spec.choose

private theorem SpecialPeriods.MuTorsor.action_formula {G B : Type*} [Group G]
    (ρ : G →* Equiv.Perm (B × ℂ)) (β : G →* Equiv.Perm B) (h_all : ∀ g, AffineFibres ρ β g)
    (g : G) (z : B) (u : ℂ) :
    ρ g (z, u) = (β g z, (scale ρ β h_all g z : ℂ) * u + shift ρ β h_all g z) :=
  (h_all g).choose_spec.choose_spec z u

private theorem SpecialPeriods.MuTorsor.scale_eq_of_formula {G B : Type*} [Group G]
    (ρ : G →* Equiv.Perm (B × ℂ)) (β : G →* Equiv.Perm B) (h_all : ∀ g, AffineFibres ρ β g)
    {g : G} {a : B → ℂˣ} {b : B → ℂ} (hg : ∀ z u, ρ g (z, u) = (β g z, (a z : ℂ) * u + b z)) :
    scale ρ β h_all g = a :=
  (affine_coefficients_unique ρ β (action_formula ρ β h_all g) hg).1

private theorem SpecialPeriods.MuTorsor.shift_eq_of_formula {G B : Type*} [Group G]
    (ρ : G →* Equiv.Perm (B × ℂ)) (β : G →* Equiv.Perm B) (h_all : ∀ g, AffineFibres ρ β g)
    {g : G} {a : B → ℂˣ} {b : B → ℂ} (hg : ∀ z u, ρ g (z, u) = (β g z, (a z : ℂ) * u + b z)) :
    shift ρ β h_all g = b :=
  (affine_coefficients_unique ρ β (action_formula ρ β h_all g) hg).2

@[simp]
private theorem
    SpecialPeriods.MuTorsor.scale_one {G B : Type*} [Group G] (ρ : G →* Equiv.Perm (B × ℂ))
    (β : G →* Equiv.Perm B) (h_all : ∀ g, AffineFibres ρ β g) (z : B) : scale ρ β h_all 1 z = 1 :=
  congrFun (scale_eq_of_formula ρ β h_all (affine_one_formula ρ β)) z

@[simp]
private theorem
    SpecialPeriods.MuTorsor.shift_one {G B : Type*} [Group G] (ρ : G →* Equiv.Perm (B × ℂ))
    (β : G →* Equiv.Perm B) (h_all : ∀ g, AffineFibres ρ β g) (z : B) : shift ρ β h_all 1 z = 0 :=
  congrFun (shift_eq_of_formula ρ β h_all (affine_one_formula ρ β)) z

private theorem
    SpecialPeriods.MuTorsor.scale_mul {G B : Type*} [Group G] (ρ : G →* Equiv.Perm (B × ℂ))
    (β : G →* Equiv.Perm B) (h_all : ∀ g, AffineFibres ρ β g) (g h : G) (z : B) :
    scale ρ β h_all (g * h) z = scale ρ β h_all g (β h z) * scale ρ β h_all h z :=
  congrFun
    (scale_eq_of_formula ρ β h_all
      (affine_mul_formula ρ β (action_formula ρ β h_all g) (action_formula ρ β h_all h)))
    z

private theorem
    SpecialPeriods.MuTorsor.shift_mul {G B : Type*} [Group G] (ρ : G →* Equiv.Perm (B × ℂ))
    (β : G →* Equiv.Perm B) (h_all : ∀ g, AffineFibres ρ β g) (g h : G) (z : B) :
    shift ρ β h_all (g * h) z =
      (scale ρ β h_all g (β h z) : ℂ) * shift ρ β h_all h z + shift ρ β h_all g (β h z) :=
  congrFun
    (shift_eq_of_formula ρ β h_all
      (affine_mul_formula ρ β (action_formula ρ β h_all g) (action_formula ρ β h_all h)))
    z

private def SpecialPeriods.MuTorsor.HolomorphicAffineFibres {G B : Type*} [Group G]
    (ρ : G →* Equiv.Perm (B × ℂ)) (β : G →* Equiv.Perm B) {E H : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
    (I : ModelWithCorners ℂ E H) (g : G) : Prop :=
  ∃ a : B → ℂˣ,
    ∃ b : B → ℂ,
      (∀ z u, ρ g (z, u) = (β g z, (a z : ℂ) * u + b z)) ∧
        ContMDiff I (modelWithCornersSelf ℂ ℂ) ω (fun z => (a z : ℂ)) ∧
          ContMDiff I (modelWithCornersSelf ℂ ℂ) ω b

private theorem SpecialPeriods.MuTorsor.holomorphicAffineFibres_one {G B : Type*} [Group G]
    (ρ : G →* Equiv.Perm (B × ℂ)) (β : G →* Equiv.Perm B) {E H : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
    (I : ModelWithCorners ℂ E H) : HolomorphicAffineFibres ρ β I 1 :=
  ⟨fun _ => 1, fun _ => 0, affine_one_formula ρ β, contMDiff_const, contMDiff_const⟩

private theorem SpecialPeriods.MuTorsor.holomorphicAffineFibres_mul {G B : Type*} [Group G]
    (ρ : G →* Equiv.Perm (B × ℂ)) (β : G →* Equiv.Perm B) {E H : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
    (I : ModelWithCorners ℂ E H) (hβ : ∀ g, ContMDiff I I ω (β g)) {g h : G}
    (hg : HolomorphicAffineFibres ρ β I g) (hh : HolomorphicAffineFibres ρ β I h) :
    HolomorphicAffineFibres ρ β I (g * h) := by
  obtain ⟨a, b, hf, ha, hb⟩ := hg
  obtain ⟨c, d, hf', hc, hd⟩ := hh
  refine
    ⟨fun z => a (β h z) * c z, fun z => (a (β h z) : ℂ) * d z + b (β h z),
      affine_mul_formula ρ β hf hf', ?_, ?_⟩
  · change ContMDiff I (modelWithCornersSelf ℂ ℂ) ω (fun z => (a (β h z) : ℂ) * (c z : ℂ))
    exact (ha.comp (hβ h)).mul hc
  · exact ((ha.comp (hβ h)).mul hd).add (hb.comp (hβ h))

private theorem SpecialPeriods.MuTorsor.holomorphicAffineFibres_inv {G B : Type*} [Group G]
    (ρ : G →* Equiv.Perm (B × ℂ)) (β : G →* Equiv.Perm B) {E H : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
    (I : ModelWithCorners ℂ E H) (hβ : ∀ g, ContMDiff I I ω (β g)) {g : G}
    (hg : HolomorphicAffineFibres ρ β I g) : HolomorphicAffineFibres ρ β I g⁻¹ := by
  obtain ⟨a, b, hf, ha, hb⟩ := hg
  have hInv : ContMDiff I (modelWithCornersSelf ℂ ℂ) ω (fun z => (a (β g⁻¹ z) : ℂ)⁻¹) :=
    (ha.comp (hβ g⁻¹)).inv₀ (fun z => (a (β g⁻¹ z)).ne_zero)
  refine
    ⟨fun z => (a (β g⁻¹ z))⁻¹, fun z => -((a (β g⁻¹ z) : ℂ)⁻¹ * b (β g⁻¹ z)),
      affine_inv_formula ρ β hf, ?_, ?_⟩
  · simpa only [Units.val_inv_eq_inv_val] using hInv
  · exact (hInv.mul (hb.comp (hβ g⁻¹))).neg

private def SpecialPeriods.MuTorsor.holomorphicAffineSubgroup {G B : Type*} [Group G]
    (ρ : G →* Equiv.Perm (B × ℂ)) (β : G →* Equiv.Perm B) {E H : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
    (I : ModelWithCorners ℂ E H) (hβ : ∀ g, ContMDiff I I ω (β g)) : Subgroup G
    where
  carrier := HolomorphicAffineFibres ρ β I
  one_mem' := holomorphicAffineFibres_one ρ β I
  mul_mem' := holomorphicAffineFibres_mul ρ β I hβ
  inv_mem' := holomorphicAffineFibres_inv ρ β I hβ

private theorem SpecialPeriods.MuTorsor.scale_holomorphic {G B : Type*} [Group G]
    (ρ : G →* Equiv.Perm (B × ℂ)) (β : G →* Equiv.Perm B) {E H : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
    (I : ModelWithCorners ℂ E H) (h_all : ∀ g, AffineFibres ρ β g) (g : G)
    (hg : HolomorphicAffineFibres ρ β I g) :
    ContMDiff I (modelWithCornersSelf ℂ ℂ) ω (fun z => (scale ρ β h_all g z : ℂ)) := by
  obtain ⟨a, b, hf, ha, _⟩ := hg
  rw [scale_eq_of_formula ρ β h_all hf]
  exact ha

private theorem SpecialPeriods.MuTorsor.shift_holomorphic {G B : Type*} [Group G]
    (ρ : G →* Equiv.Perm (B × ℂ)) (β : G →* Equiv.Perm B) {E H : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
    (I : ModelWithCorners ℂ E H) (h_all : ∀ g, AffineFibres ρ β g) (g : G)
    (hg : HolomorphicAffineFibres ρ β I g) :
    ContMDiff I (modelWithCornersSelf ℂ ℂ) ω (shift ρ β h_all g) := by
  obtain ⟨a, b, hf, _, hb⟩ := hg
  rw [shift_eq_of_formula ρ β h_all hf]
  exact hb

private structure SpecialPeriods.MuTorsor.AffineCocycle where
  scale : SpecialPeriods.TriangleGroup → ℍ → ℂˣ
  shift : SpecialPeriods.TriangleGroup → ℍ → ℂ
  scale_one : ∀ z, scale 1 z = 1
  shift_one : ∀ z, shift 1 z = 0
  scale_mul :
    ∀ g h z,
      scale (g * h) z = scale g (SpecialPeriods.triangleGeometricRepresentation h z) * scale h z
  shift_mul :
    ∀ g h z,
      shift (g * h) z =
        (scale g (SpecialPeriods.triangleGeometricRepresentation h z) : ℂ) * shift h z +
          shift g (SpecialPeriods.triangleGeometricRepresentation h z)
  scale_holomorphic : ∀ g, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => (scale g z : ℂ))
  shift_holomorphic : ∀ g, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (shift g)

private def
    SpecialPeriods.MuTorsor.AffineCocycle.fibreMap (c : SpecialPeriods.MuTorsor.AffineCocycle)
    (g : SpecialPeriods.TriangleGroup) (z : ℍ) (u : ℂ) : ℂ :=
  (c.scale g z : ℂ) * u + c.shift g z

@[simp]
private theorem SpecialPeriods.MuTorsor.AffineCocycle.fibreMap_one
    (c : SpecialPeriods.MuTorsor.AffineCocycle) (z : ℍ) (u : ℂ) : c.fibreMap 1 z u = u := by
  simp only [fibreMap, c.scale_one, c.shift_one, Units.val_one, one_mul, add_zero]

private theorem SpecialPeriods.MuTorsor.AffineCocycle.fibreMap_mul
    (c : SpecialPeriods.MuTorsor.AffineCocycle) (g h : SpecialPeriods.TriangleGroup) (z : ℍ)
    (u : ℂ) :
    c.fibreMap (g * h) z u =
      c.fibreMap g (SpecialPeriods.triangleGeometricRepresentation h z) (c.fibreMap h z u) := by
  simp only [fibreMap, c.scale_mul, c.shift_mul, Units.val_mul]
  ring

private theorem SpecialPeriods.MuTorsor.AffineCocycle.fibreMap_inv
    (c : SpecialPeriods.MuTorsor.AffineCocycle) (g : SpecialPeriods.TriangleGroup) (z : ℍ)
    (u : ℂ) :
    c.fibreMap g⁻¹ (SpecialPeriods.triangleGeometricRepresentation g z) (c.fibreMap g z u) = u := by
  rw [← c.fibreMap_mul, inv_mul_cancel, c.fibreMap_one]

private theorem SpecialPeriods.MuTorsor.AffineCocycle.fibreMap_injective
    (c : SpecialPeriods.MuTorsor.AffineCocycle) (g : SpecialPeriods.TriangleGroup) (z : ℍ) :
    Function.Injective (c.fibreMap g z) := by
  intro u v huv
  exact mul_left_cancel₀ (c.scale g z).ne_zero (add_right_cancel huv)

private theorem SpecialPeriods.MuTorsor.AffineCocycle.fibreMap_sub
    (c : SpecialPeriods.MuTorsor.AffineCocycle) (g : SpecialPeriods.TriangleGroup) (z : ℍ)
    (u v : ℂ) : c.fibreMap g z u - c.fibreMap g z v = (c.scale g z : ℂ) * (u - v) := by
  simp only [fibreMap]
  ring

private def SpecialPeriods.MuTorsor.AffineCocycle.EquivariantOn
    (c : SpecialPeriods.MuTorsor.AffineCocycle) (f : ℍ → ℂ) (V : Set ℍ) : Prop :=
  ∀ g z, z ∈ V → f (SpecialPeriods.triangleGeometricRepresentation g z) = c.fibreMap g z (f z)

private structure SpecialPeriods.MuTorsor.PreciselyInvariantPatch where
  sheet : TopologicalSpace.Opens ℍ
  stabilizer : Subgroup SpecialPeriods.TriangleGroup
  mapsTo :
    ∀ g : stabilizer,
      Set.MapsTo
        (SpecialPeriods.triangleGeometricRepresentation (g : SpecialPeriods.TriangleGroup)) sheet
        sheet
  returning :
    ∀ g : SpecialPeriods.TriangleGroup,
      ((SpecialPeriods.triangleGeometricRepresentation g '' (sheet : Set ℍ)) ∩ sheet).Nonempty →
        g ∈ stabilizer

private def SpecialPeriods.MuTorsor.PreciselyInvariantPatch.saturation
    (P : SpecialPeriods.MuTorsor.PreciselyInvariantPatch) : Set ℍ :=
  {z |
    ∃ g : SpecialPeriods.TriangleGroup,
      ∃ x : ℍ, x ∈ P.sheet ∧ SpecialPeriods.triangleGeometricRepresentation g x = z}

private theorem SpecialPeriods.MuTorsor.PreciselyInvariantPatch.saturation_invariant
    (P : SpecialPeriods.MuTorsor.PreciselyInvariantPatch) (g : SpecialPeriods.TriangleGroup)
    (z : ℍ) :
    SpecialPeriods.triangleGeometricRepresentation g z ∈ P.saturation ↔ z ∈ P.saturation := by
  constructor
  · rintro ⟨h, x, hx, he⟩
    refine ⟨g⁻¹ * h, x, hx, ?_⟩
    rw [map_mul]
    change
      SpecialPeriods.triangleGeometricRepresentation g⁻¹
          (SpecialPeriods.triangleGeometricRepresentation h x) =
        z
    rw [he, map_inv]
    exact (SpecialPeriods.triangleGeometricRepresentation g).symm_apply_apply z
  · rintro ⟨h, x, hx, rfl⟩
    exact ⟨g * h, x, hx, by simp⟩

private theorem SpecialPeriods.MuTorsor.PreciselyInvariantPatch.saturation_isOpen
    (P : SpecialPeriods.MuTorsor.PreciselyInvariantPatch) : IsOpen P.saturation := by
  have he :
    P.saturation =
      ⋃ g : SpecialPeriods.TriangleGroup,
        SpecialPeriods.triangleGeometricRepresentation g '' (P.sheet : Set ℍ) := by
    ext z
    simp only [saturation, Set.mem_iUnion, Set.mem_image]
    rfl
  rw [he]
  exact
    isOpen_iUnion fun g =>
      (SpecialPeriods.triangleGeometricBiholomorph g).toHomeomorph.isOpenMap _ P.sheet.isOpen

private theorem SpecialPeriods.MuTorsor.PreciselyInvariantPatch.saturation_eq_preimage_image
    (P : SpecialPeriods.MuTorsor.PreciselyInvariantPatch) :
    P.saturation =
      SpecialPeriods.triangleOrbitProjection ⁻¹'
        (SpecialPeriods.triangleOrbitProjection '' P.sheet) := by
  ext z
  constructor
  · rintro ⟨g, x, hx, rfl⟩
    exact ⟨x, hx, (SpecialPeriods.triangleOrbitProjection_smul g x).symm⟩
  · rintro ⟨x, hx, he⟩
    obtain ⟨g, hg⟩ := (SpecialPeriods.triangleOrbitProjection_eq_iff z x).mp he.symm
    exact ⟨g, x, hx, hg⟩

private theorem SpecialPeriods.MuTorsor.PreciselyInvariantPatch.stabilizer_mem_iff
    (P : SpecialPeriods.MuTorsor.PreciselyInvariantPatch) (g : SpecialPeriods.TriangleGroup)
    (x : ℍ) (hx : x ∈ P.sheet) :
    SpecialPeriods.triangleGeometricRepresentation g x ∈ P.sheet ↔ g ∈ P.stabilizer := by
  constructor
  · intro hgx
    exact P.returning g ⟨_, ⟨x, hx, rfl⟩, hgx⟩
  · intro hg
    exact P.mapsTo ⟨g, hg⟩ hx

private structure SpecialPeriods.MuTorsor.PreciselyInvariantPatch.Seed
    (P : SpecialPeriods.MuTorsor.PreciselyInvariantPatch)
    (c : SpecialPeriods.MuTorsor.AffineCocycle) where
  toFun : ℍ → ℂ
  holomorphic : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω toFun P.sheet
  equivariant :
    ∀ g : P.stabilizer,
      ∀ z ∈ P.sheet,
        toFun
            (SpecialPeriods.triangleGeometricRepresentation (g : SpecialPeriods.TriangleGroup)
              z) =
          c.fibreMap g z (toFun z)

private def SpecialPeriods.MuTorsor.AffineCocycle.sectionStabilizer
    (c : SpecialPeriods.MuTorsor.AffineCocycle) (f : ℍ → ℂ) :
    Subgroup SpecialPeriods.TriangleGroup
    where
  carrier :=
    {g | ∀ z, f (SpecialPeriods.triangleGeometricRepresentation g z) = c.fibreMap g z (f z)}
  one_mem' := by
    intro z
    simp only [map_one, Equiv.Perm.one_apply, c.fibreMap_one]
  mul_mem' := by
    intro g h hg hh z
    calc
      f (SpecialPeriods.triangleGeometricRepresentation (g * h) z) =
          f
            (SpecialPeriods.triangleGeometricRepresentation g
              (SpecialPeriods.triangleGeometricRepresentation h z)) := by
        rw [map_mul, Equiv.Perm.mul_apply]
      _ =
          c.fibreMap g (SpecialPeriods.triangleGeometricRepresentation h z)
            (f (SpecialPeriods.triangleGeometricRepresentation h z)) :=
        (hg _)
      _ =
          c.fibreMap g (SpecialPeriods.triangleGeometricRepresentation h z)
            (c.fibreMap h z (f z)) := by rw [hh z]
      _ = c.fibreMap (g * h) z (f z) := (c.fibreMap_mul g h z (f z)).symm
  inv_mem' := by
    intro g hg z
    apply c.fibreMap_injective g (SpecialPeriods.triangleGeometricRepresentation g⁻¹ z)
    have hbase :
      SpecialPeriods.triangleGeometricRepresentation g
          (SpecialPeriods.triangleGeometricRepresentation g⁻¹ z) =
        z := by
      rw [map_inv, Equiv.Perm.inv_def]
      exact (SpecialPeriods.triangleGeometricRepresentation g).apply_symm_apply z
    calc
      c.fibreMap g (SpecialPeriods.triangleGeometricRepresentation g⁻¹ z)
            (f (SpecialPeriods.triangleGeometricRepresentation g⁻¹ z)) =
          f
            (SpecialPeriods.triangleGeometricRepresentation g
              (SpecialPeriods.triangleGeometricRepresentation g⁻¹ z)) :=
        (hg _).symm
      _ = f z := (congrArg f hbase)
      _ =
          c.fibreMap g (SpecialPeriods.triangleGeometricRepresentation g⁻¹ z)
            (c.fibreMap g⁻¹ z (f z)) := by
        simpa only [inv_inv] using (c.fibreMap_inv g⁻¹ z (f z)).symm

private theorem SpecialPeriods.MuTorsor.AffineCocycle.zpowers_le_sectionStabilizer
    (c : SpecialPeriods.MuTorsor.AffineCocycle) (f : ℍ → ℂ) (g : SpecialPeriods.TriangleGroup)
    (hg : ∀ z, f (SpecialPeriods.triangleGeometricRepresentation g z) = c.fibreMap g z (f z)) :
    Subgroup.zpowers g ≤ c.sectionStabilizer f :=
  Subgroup.zpowers_le.mpr hg

private theorem SpecialPeriods.MuTorsor.AffineCocycle.equivariant_of_mem_zpowers
    (c : SpecialPeriods.MuTorsor.AffineCocycle) (f : ℍ → ℂ) (g : SpecialPeriods.TriangleGroup)
    (hg : ∀ z, f (SpecialPeriods.triangleGeometricRepresentation g z) = c.fibreMap g z (f z))
    {h : SpecialPeriods.TriangleGroup} (hh : h ∈ Subgroup.zpowers g) (z : ℍ) :
    f (SpecialPeriods.triangleGeometricRepresentation h z) = c.fibreMap h z (f z) :=
  c.zpowers_le_sectionStabilizer f g hg hh z

private theorem SpecialPeriods.MuTorsor.mem_subgroup_of_triangle_generators_mo1973_17509
    (K : Subgroup SpecialPeriods.TriangleGroup) (h₁ : SpecialPeriods.triangleGenerator₁ ∈ K)
    (h₂ : SpecialPeriods.triangleGenerator₂ ∈ K) (g : SpecialPeriods.TriangleGroup) : g ∈ K := by
  have hle :
    Subgroup.closure
        ({ SpecialPeriods.triangleGenerator₁, SpecialPeriods.triangleGenerator₂ } :
          Set SpecialPeriods.TriangleGroup) ≤
      K :=
    (Subgroup.closure_le _).mpr
      (by
        intro x hx
        rcases hx with rfl | rfl
        · exact h₁
        · exact h₂)
  rw [SpecialPeriods.triangle_generators_generate] at hle
  exact hle (Subgroup.mem_top g)

private theorem SpecialPeriods.MuTorsor.representation_generatorOne_formula {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (z : ℍ) (u : ℂ) :
    representation hτ SpecialPeriods.triangleGenerator₁ (z, u) =
      (SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleGenerator₁ z,
        (generatorOneScale τ z : ℂ) * u + generatorOneShift τ z) := by
  rw [representation_generator₁, SpecialPeriods.triangleGeometricRepresentation_generator₁]
  rfl

private theorem SpecialPeriods.MuTorsor.representation_generatorTwo_formula {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (z : ℍ) (u : ℂ) :
    representation hτ SpecialPeriods.triangleGenerator₂ (z, u) =
      (SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleGenerator₂ z,
        (generatorTwoScale τ z : ℂ) * u + generatorTwoShift z) := by
  rw [representation_generator₂, SpecialPeriods.triangleGeometricRepresentation_generator₂]
  rfl

private theorem SpecialPeriods.MuTorsor.representation_affine {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (g : SpecialPeriods.TriangleGroup) :
    AffineFibres (representation hτ) SpecialPeriods.triangleGeometricRepresentation g := by
  apply
    mem_subgroup_of_triangle_generators_mo1973_17509
      (affineSubgroup (representation hτ) SpecialPeriods.triangleGeometricRepresentation)
  · exact ⟨generatorOneScale τ, generatorOneShift τ, representation_generatorOne_formula hτ⟩
  · exact ⟨generatorTwoScale τ, generatorTwoShift, representation_generatorTwo_formula hτ⟩

private theorem SpecialPeriods.MuTorsor.representation_fst {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (g : SpecialPeriods.TriangleGroup) (z : ℍ) (u : ℂ) :
    (representation hτ g (z, u)).1 = SpecialPeriods.triangleGeometricRepresentation g z :=
  congrArg Prod.fst
    (action_formula (representation hτ) SpecialPeriods.triangleGeometricRepresentation
      (representation_affine hτ) g z u)

private theorem SpecialPeriods.MuTorsor.representation_cusp_formula {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (z : ℍ) (u : ℂ) :
    representation hτ SpecialPeriods.triangleCuspGenerator (z, u) =
      (SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleCuspGenerator z,
        u) :=
  Prod.ext (representation_fst hτ _ z u) (representation_cusp_snd hτ z u)

private theorem SpecialPeriods.MuTorsor.representation_holomorphic_affine {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ)
    (g : SpecialPeriods.TriangleGroup) :
    HolomorphicAffineFibres (representation hτ) SpecialPeriods.triangleGeometricRepresentation
      𝓘(ℂ) g := by
  apply
    mem_subgroup_of_triangle_generators_mo1973_17509
      (holomorphicAffineSubgroup (representation hτ)
        SpecialPeriods.triangleGeometricRepresentation 𝓘(ℂ)
        SpecialPeriods.triangleGeometricRepresentation_holomorphic)
  · exact
      ⟨generatorOneScale τ, generatorOneShift τ, representation_generatorOne_formula hτ,
        generatorOneScale_holomorphic hτa, generatorOneShift_holomorphic hτa⟩
  · exact
      ⟨generatorTwoScale τ, generatorTwoShift, representation_generatorTwo_formula hτ,
        generatorTwoScale_holomorphic hτa, generatorTwoShift_holomorphic⟩

private def SpecialPeriods.MuTorsor.cocycle {τ : ℍ → ℍ} (hτ : SpecialPeriods.TauCovariant τ)
    (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) : AffineCocycle
    where
  scale :=
    scale (representation hτ) SpecialPeriods.triangleGeometricRepresentation
      (representation_affine hτ)
  shift :=
    shift (representation hτ) SpecialPeriods.triangleGeometricRepresentation
      (representation_affine hτ)
  scale_one :=
    scale_one (representation hτ) SpecialPeriods.triangleGeometricRepresentation
      (representation_affine hτ)
  shift_one :=
    shift_one (representation hτ) SpecialPeriods.triangleGeometricRepresentation
      (representation_affine hτ)
  scale_mul :=
    scale_mul (representation hτ) SpecialPeriods.triangleGeometricRepresentation
      (representation_affine hτ)
  shift_mul :=
    shift_mul (representation hτ) SpecialPeriods.triangleGeometricRepresentation
      (representation_affine hτ)
  scale_holomorphic
    g :=
    scale_holomorphic (representation hτ) SpecialPeriods.triangleGeometricRepresentation 𝓘(ℂ)
      (representation_affine hτ) g (representation_holomorphic_affine hτ hτa g)
  shift_holomorphic
    g :=
    shift_holomorphic (representation hτ) SpecialPeriods.triangleGeometricRepresentation 𝓘(ℂ)
      (representation_affine hτ) g (representation_holomorphic_affine hτ hτa g)

@[simp]
private theorem SpecialPeriods.MuTorsor.cocycle_scale_generator₁ {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (z : ℍ) :
    (cocycle hτ hτa).scale SpecialPeriods.triangleGenerator₁ z = generatorOneScale τ z :=
  congrFun
    (scale_eq_of_formula (representation hτ) SpecialPeriods.triangleGeometricRepresentation
      (representation_affine hτ) (representation_generatorOne_formula hτ))
    z

@[simp]
private theorem SpecialPeriods.MuTorsor.cocycle_scale_generator₂ {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (z : ℍ) :
    (cocycle hτ hτa).scale SpecialPeriods.triangleGenerator₂ z = generatorTwoScale τ z :=
  congrFun
    (scale_eq_of_formula (representation hτ) SpecialPeriods.triangleGeometricRepresentation
      (representation_affine hτ) (representation_generatorTwo_formula hτ))
    z

@[simp]
private theorem SpecialPeriods.MuTorsor.cocycle_shift_generator₁ {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (z : ℍ) :
    (cocycle hτ hτa).shift SpecialPeriods.triangleGenerator₁ z = 1 / (τ z : ℂ) :=
  congrFun
    (shift_eq_of_formula (representation hτ) SpecialPeriods.triangleGeometricRepresentation
      (representation_affine hτ) (representation_generatorOne_formula hτ))
    z

@[simp]
private theorem SpecialPeriods.MuTorsor.cocycle_shift_generator₂ {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (z : ℍ) :
    (cocycle hτ hτa).shift SpecialPeriods.triangleGenerator₂ z = 1 :=
  congrFun
    (shift_eq_of_formula (representation hτ) SpecialPeriods.triangleGeometricRepresentation
      (representation_affine hτ) (representation_generatorTwo_formula hτ))
    z

private theorem SpecialPeriods.MuTorsor.cocycle_scale_generator₁_val {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (z : ℍ) :
    ((cocycle hτ hτa).scale SpecialPeriods.triangleGenerator₁ z : ℂ) = -1 / (τ z : ℂ) := by
  rw [cocycle_scale_generator₁, generatorOneScale_val]

private theorem SpecialPeriods.MuTorsor.cocycle_scale_generator₂_val {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (z : ℍ) :
    ((cocycle hτ hτa).scale SpecialPeriods.triangleGenerator₂ z : ℂ) = 1 / (τ z : ℂ) := by
  rw [cocycle_scale_generator₂, generatorTwoScale_val]

private theorem SpecialPeriods.MuTorsor.cocycle_fibreMap_generator₁ {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (z : ℍ) (u : ℂ) :
    (cocycle hτ hτa).fibreMap SpecialPeriods.triangleGenerator₁ z u = (1 - u) / (τ z : ℂ) := by
  rw [AffineCocycle.fibreMap, cocycle_scale_generator₁_val, cocycle_shift_generator₁]
  ring

private theorem SpecialPeriods.MuTorsor.cocycle_fibreMap_generator₂ {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (z : ℍ) (u : ℂ) :
    (cocycle hτ hτa).fibreMap SpecialPeriods.triangleGenerator₂ z u = 1 + u / (τ z : ℂ) := by
  rw [AffineCocycle.fibreMap, cocycle_scale_generator₂_val, cocycle_shift_generator₂]
  ring

private theorem SpecialPeriods.MuTorsor.representation_cusp_affine_formula_mo1973_17526
    {τ : ℍ → ℍ} (hτ : SpecialPeriods.TauCovariant τ) (z : ℍ) (u : ℂ) :
    representation hτ SpecialPeriods.triangleCuspGenerator (z, u) =
      (SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleCuspGenerator z,
        ((1 : ℂˣ) : ℂ) * u + 0) := by
  simpa only [Units.val_one, one_mul, add_zero] using representation_cusp_formula hτ z u

@[simp]
private theorem SpecialPeriods.MuTorsor.cocycle_scale_cusp {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (z : ℍ) :
    (cocycle hτ hτa).scale SpecialPeriods.triangleCuspGenerator z = 1 :=
  congrFun
    (scale_eq_of_formula (representation hτ) SpecialPeriods.triangleGeometricRepresentation
      (representation_affine hτ) (representation_cusp_affine_formula_mo1973_17526 hτ))
    z

@[simp]
private theorem SpecialPeriods.MuTorsor.cocycle_shift_cusp {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (z : ℍ) :
    (cocycle hτ hτa).shift SpecialPeriods.triangleCuspGenerator z = 0 :=
  congrFun
    (shift_eq_of_formula (representation hτ) SpecialPeriods.triangleGeometricRepresentation
      (representation_affine hτ) (representation_cusp_affine_formula_mo1973_17526 hτ))
    z

@[simp]
private theorem SpecialPeriods.MuTorsor.cocycle_fibreMap_cusp {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (z : ℍ) (u : ℂ) :
    (cocycle hτ hτa).fibreMap SpecialPeriods.triangleCuspGenerator z u = u := by
  simp only [AffineCocycle.fibreMap, cocycle_scale_cusp, cocycle_shift_cusp, Units.val_one,
    one_mul, add_zero]

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private def SpecialPeriods.MuTorsor.Cover.regularRepresentative
    (x : SpecialPeriods.TriangleRegularQuotient) : SpecialPeriods.TriangleRegularPoint :=
  CoveringQuotient.representative SpecialPeriods.triangleRegularProject_covering x

attribute [local instance] SpecialPeriods.triangleGeometricAction in
@[simp]
private theorem SpecialPeriods.MuTorsor.Cover.regularRepresentative_project
    (x : SpecialPeriods.TriangleRegularQuotient) :
    SpecialPeriods.triangleRegularProject (regularRepresentative x) = x :=
  CoveringQuotient.project_representative SpecialPeriods.triangleRegularProject_covering x

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private def SpecialPeriods.MuTorsor.Cover.regularLift (x : SpecialPeriods.TriangleRegularQuotient) :
    OpenPartialHomeomorph SpecialPeriods.TriangleRegularQuotient
      SpecialPeriods.TriangleRegularPoint :=
  CoveringQuotient.localInverse SpecialPeriods.triangleRegularProject_covering
    (regularRepresentative x)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
@[simp]
private theorem SpecialPeriods.MuTorsor.Cover.regularLift_symm
    (x : SpecialPeriods.TriangleRegularQuotient) :
    (regularLift x).symm = SpecialPeriods.triangleRegularProject :=
  CoveringQuotient.localInverse_symm SpecialPeriods.triangleRegularProject_covering
    (regularRepresentative x)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.MuTorsor.Cover.regularRepresentative_mem_target
    (x : SpecialPeriods.TriangleRegularQuotient) :
    regularRepresentative x ∈ (regularLift x).target :=
  IsLocalHomeomorph.self_mem_localInverseAt_target
    SpecialPeriods.triangleRegularProject_covering.isCoveringMap.isLocalHomeomorph

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private def
    SpecialPeriods.MuTorsor.Cover.regularSheet (x : SpecialPeriods.TriangleRegularQuotient) :
    TopologicalSpace.Opens ℍ :=
  ⟨Subtype.val '' (regularLift x).target,
    SpecialPeriods.triangleRegularDomain.isOpen.isOpenMap_subtype_val _
      (regularLift x).open_target⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.MuTorsor.Cover.regularSheet_subset_regularLocus
    (x : SpecialPeriods.TriangleRegularQuotient) :
    (regularSheet x : Set ℍ) ⊆ SpecialPeriods.triangleRegularLocus := by
  rintro z ⟨a, ha, rfl⟩
  exact a.property

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.MuTorsor.Cover.regularRepresentative_mem_sheet
    (x : SpecialPeriods.TriangleRegularQuotient) :
    (regularRepresentative x).val ∈ regularSheet x :=
  ⟨regularRepresentative x, regularRepresentative_mem_target x, rfl⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.MuTorsor.Cover.regularSheet_no_return
    (x : SpecialPeriods.TriangleRegularQuotient) (g : SpecialPeriods.TriangleGroup)
    (hg :
      ((SpecialPeriods.triangleGeometricRepresentation g '' (regularSheet x : Set ℍ)) ∩
          regularSheet x).Nonempty) :
    g = 1 := by
  rcases hg with ⟨z, ⟨w, ⟨a, ha, rfl⟩, hga⟩, ⟨b, hb, rfl⟩⟩
  have hab : g • a = b := Subtype.ext hga
  have hproj :
    SpecialPeriods.triangleRegularProject b = SpecialPeriods.triangleRegularProject a := by
    rw [← hab]
    exact SpecialPeriods.triangleRegularProject_covering.map_smul g
  have hba : b = a :=
    (regularLift x).symm.injOn hb ha (by simpa only [regularLift_symm] using hproj)
  exact
    (SpecialPeriods.mem_triangleRegularLocus_iff a.val).mp a.property g
      (congrArg Subtype.val (hab.trans hba))

attribute [local instance] SpecialPeriods.triangleGeometricAction in
@[simp]
private theorem SpecialPeriods.MuTorsor.Cover.regularRepresentative_orbitProjection
    (x : SpecialPeriods.TriangleRegularQuotient) :
    SpecialPeriods.triangleOrbitProjection (regularRepresentative x).val =
      SpecialPeriods.triangleRegularToOrbit x := by
  rw [← SpecialPeriods.triangleRegularToOrbit_project, regularRepresentative_project]

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private def
    SpecialPeriods.MuTorsor.Cover.regularImage (x : SpecialPeriods.TriangleRegularQuotient) :
    TopologicalSpace.Opens SpecialPeriods.TriangleOrbitSpace :=
  ⟨SpecialPeriods.triangleOrbitProjection '' (regularSheet x : Set ℍ),
    SpecialPeriods.triangleOrbitProjection_isOpenMap _ (regularSheet x).isOpen⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.MuTorsor.Cover.regularImage_subset_regularDomain
    (x : SpecialPeriods.TriangleRegularQuotient) :
    (regularImage x : Set SpecialPeriods.TriangleOrbitSpace) ⊆
      SpecialPeriods.triangleOrbitRegularDomain := by
  rintro y ⟨z, hz, rfl⟩
  exact
    (SpecialPeriods.triangleOrbitProjection_mem_regularDomain_iff z).mpr
      (regularSheet_subset_regularLocus x hz)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.MuTorsor.Cover.regularImage_mem
    (x : SpecialPeriods.TriangleRegularQuotient) :
    SpecialPeriods.triangleRegularToOrbit x ∈ regularImage x :=
  ⟨(regularRepresentative x).val, regularRepresentative_mem_sheet x,
    regularRepresentative_orbitProjection x⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem
    SpecialPeriods.MuTorsor.Cover.exists_regularImage (y : SpecialPeriods.TriangleOrbitSpace)
    (hy : y ∈ SpecialPeriods.triangleOrbitRegularDomain) :
    ∃ x : SpecialPeriods.TriangleRegularQuotient, y ∈ regularImage x := by
  obtain ⟨x, rfl⟩ := hy
  exact ⟨x, regularImage_mem x⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
private abbrev SpecialPeriods.MuTorsor.Cover.Index :=
  Option (SpecialPeriods.TriangleRegularQuotient ⊕ Elliptic.Kind)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.MuTorsor.Cover.cuspIndex : Index :=
  Option.none

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
private def
    SpecialPeriods.MuTorsor.Cover.regularIndex (x : SpecialPeriods.TriangleRegularQuotient) :
    Index :=
  Option.some (.inl x)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.MuTorsor.Cover.ellipticIndex (j : Elliptic.Kind) : Index :=
  Option.some (.inr j)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
private def
    SpecialPeriods.MuTorsor.Cover.cuspPatch : SpecialPeriods.MuTorsor.PreciselyInvariantPatch
    where
  sheet := SpecialPeriods.Triangle.horodisc SpecialPeriods.Triangle.width
  stabilizer := Subgroup.zpowers SpecialPeriods.triangleCuspGenerator
  mapsTo := SpecialPeriods.Triangle.cusp_horodisc_invariant SpecialPeriods.Triangle.width
  returning :=
    SpecialPeriods.Triangle.triangle_horodisc_overlap_mem_cusp SpecialPeriods.Triangle.width
      le_rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
private def
    SpecialPeriods.MuTorsor.Cover.regularPatch (x : SpecialPeriods.TriangleRegularQuotient) :
    SpecialPeriods.MuTorsor.PreciselyInvariantPatch
    where
  sheet := regularSheet x
  stabilizer := ⊥
  mapsTo := by
    intro g z hz
    have hg : (g : SpecialPeriods.TriangleGroup) = 1 := Subgroup.mem_bot.mp g.property
    simpa only [hg, map_one, Equiv.Perm.one_apply] using hz
  returning := fun g hg => Subgroup.mem_bot.mpr (regularSheet_no_return x g hg)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.MuTorsor.Cover.ellipticPatch (j : Elliptic.Kind) :
    SpecialPeriods.MuTorsor.PreciselyInvariantPatch
    where
  sheet := SpecialPeriods.Triangle.ellipticNeighborhood j
  stabilizer := SpecialPeriods.Triangle.ellipticStabilizer j
  mapsTo := SpecialPeriods.Triangle.ellipticNeighborhood_mapsTo j
  returning := SpecialPeriods.Triangle.ellipticNeighborhood_return j

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
private def
    SpecialPeriods.MuTorsor.Cover.patch : Index → SpecialPeriods.MuTorsor.PreciselyInvariantPatch
  | none => cuspPatch
  | some (.inl x) => regularPatch x
  | some (.inr j) => ellipticPatch j

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.MuTorsor.Cover.compactImage
    (V : TopologicalSpace.Opens SpecialPeriods.TriangleOrbitSpace) :
    TopologicalSpace.Opens SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  ⟨SpecialPeriods.triangleOpenInclusion '' (V : Set SpecialPeriods.TriangleOrbitSpace),
    SpecialPeriods.triangleOpenInclusion_isOpenEmbedding.isOpenMap _ V.isOpen⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
private theorem SpecialPeriods.MuTorsor.Cover.openInclusion_mem_compactImage
    (V : TopologicalSpace.Opens SpecialPeriods.TriangleOrbitSpace)
    (q : SpecialPeriods.TriangleOrbitSpace) :
    SpecialPeriods.triangleOpenInclusion q ∈ compactImage V ↔ q ∈ V :=
  SpecialPeriods.triangleOpenInclusion_isOpenEmbedding.injective.mem_set_image

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.MuTorsor.Cover.compactPatch :
    Index → TopologicalSpace.Opens SpecialPeriods.TriangleCompactifiedOrbitSpace
  | none => SpecialPeriods.Triangle.cuspNeighborhood SpecialPeriods.Triangle.width
  | some (.inl x) => compactImage (regularImage x)
  | some (.inr j) => compactImage (SpecialPeriods.Triangle.ellipticNeighborhoodImage j)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.Cover.compactPatch_preimage_openInclusion (i : Index) :
    SpecialPeriods.triangleOpenInclusion ⁻¹'
        (compactPatch i : Set SpecialPeriods.TriangleCompactifiedOrbitSpace) =
      SpecialPeriods.triangleOrbitProjection '' ((patch i).sheet : Set ℍ) := by
  cases i with
  | none => exact SpecialPeriods.Triangle.cuspNeighborhood_preimage SpecialPeriods.Triangle.width
  | some i =>
    cases i with
    | inl x =>
      ext q
      exact openInclusion_mem_compactImage (regularImage x) q
    | inr j =>
      ext q
      exact openInclusion_mem_compactImage (SpecialPeriods.Triangle.ellipticNeighborhoodImage j) q

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.Cover.compactPatch_preimage_projection (i : Index) :
    SpecialPeriods.triangleCompactifiedProjection ⁻¹'
        (compactPatch i : Set SpecialPeriods.TriangleCompactifiedOrbitSpace) =
      (patch i).saturation := by
  change
    SpecialPeriods.triangleOrbitProjection ⁻¹'
        (SpecialPeriods.triangleOpenInclusion ⁻¹'
          (compactPatch i : Set SpecialPeriods.TriangleCompactifiedOrbitSpace)) =
      _
  rw [compactPatch_preimage_openInclusion, (patch i).saturation_eq_preimage_image]

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
@[simp]
private theorem SpecialPeriods.MuTorsor.Cover.compactifiedProjection_mem_compactPatch (i : Index)
    (z : ℍ) :
    SpecialPeriods.triangleCompactifiedProjection z ∈ compactPatch i ↔ z ∈ (patch i).saturation :=
  by
  change
    z ∈
        SpecialPeriods.triangleCompactifiedProjection ⁻¹'
          (compactPatch i : Set SpecialPeriods.TriangleCompactifiedOrbitSpace) ↔
      _
  rw [compactPatch_preimage_projection]

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.Cover.exists_compactPatch
    (q : SpecialPeriods.TriangleCompactifiedOrbitSpace) : ∃ i : Index, q ∈ compactPatch i := by
  induction q using OnePoint.rec with
  | infty =>
    exact
      ⟨cuspIndex,
        SpecialPeriods.Triangle.cuspPoint_mem_cuspNeighborhood SpecialPeriods.Triangle.width⟩
  | coe q =>
    by_cases h₁ : q = SpecialPeriods.triangleOrbitCenterOne
    · subst q
      exact
        ⟨ellipticIndex .three, SpecialPeriods.triangleOrbitCenterOne,
          SpecialPeriods.Triangle.ellipticOrbitCenter_mem_neighborhoodImage .three, rfl⟩
    by_cases h₂ : q = SpecialPeriods.triangleOrbitCenterTwo
    · subst q
      exact
        ⟨ellipticIndex .four, SpecialPeriods.triangleOrbitCenterTwo,
          SpecialPeriods.Triangle.ellipticOrbitCenter_mem_neighborhoodImage .four, rfl⟩
    obtain ⟨x, hx⟩ :=
      exists_regularImage q ((SpecialPeriods.triangleOrbitRegularDomain_mem_iff q).mpr ⟨h₁, h₂⟩)
    exact ⟨regularIndex x, q, hx, rfl⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.Cover.ellipticOrbitCenter_not_mem_regularDomain
    (j : Elliptic.Kind) :
    SpecialPeriods.Triangle.ellipticOrbitCenter j ∉ SpecialPeriods.triangleOrbitRegularDomain := by
  cases j with
  | three => exact fun h => ((SpecialPeriods.triangleOrbitRegularDomain_mem_iff _).mp h).1 rfl
  | four => exact fun h => ((SpecialPeriods.triangleOrbitRegularDomain_mem_iff _).mp h).2 rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.Cover.ellipticOrbitCenter_mem_neighborhoodImage_iff
    (j k : Elliptic.Kind) :
    SpecialPeriods.Triangle.ellipticOrbitCenter j ∈
        SpecialPeriods.Triangle.ellipticNeighborhoodImage k ↔
      j = k := by
  by_cases h : j = k
  · subst j
    exact iff_of_true (SpecialPeriods.Triangle.ellipticOrbitCenter_mem_neighborhoodImage k) rfl
  · have hj : j = SpecialPeriods.Triangle.ellipticOtherKind k := by
      cases j <;> cases k <;> simp_all [SpecialPeriods.Triangle.ellipticOtherKind]
    exact
      iff_of_false
        (by
          rw [hj]
          exact SpecialPeriods.Triangle.ellipticOtherOrbitCenter_not_mem_neighborhoodImage k)
        h

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem
    SpecialPeriods.MuTorsor.Cover.compactPatch_center_unique (j : Elliptic.Kind) (i : Index) :
    SpecialPeriods.triangleOpenInclusion (SpecialPeriods.Triangle.ellipticOrbitCenter j) ∈
        compactPatch i ↔
      i = ellipticIndex j := by
  cases i with
  | none =>
    apply iff_of_false
    · intro h
      exact
        ellipticOrbitCenter_not_mem_regularDomain j
          (SpecialPeriods.Triangle.cuspImage_subset_regularDomain SpecialPeriods.Triangle.width
            le_rfl
            ((SpecialPeriods.Triangle.openInclusion_mem_cuspNeighborhood
                  SpecialPeriods.Triangle.width _).mp
              h))
    · intro h
      cases h
  | some i =>
    cases i with
    | inl x =>
      apply iff_of_false
      · intro h
        exact
          ellipticOrbitCenter_not_mem_regularDomain j
            (regularImage_subset_regularDomain x
              ((openInclusion_mem_compactImage (regularImage x) _).mp h))
      · intro h
        cases h
    | inr
      k =>
      change
        SpecialPeriods.triangleOpenInclusion (SpecialPeriods.Triangle.ellipticOrbitCenter j) ∈
            compactImage (SpecialPeriods.Triangle.ellipticNeighborhoodImage k) ↔
          Option.some (Sum.inr k) = Option.some (Sum.inr j)
      rw [openInclusion_mem_compactImage, ellipticOrbitCenter_mem_neighborhoodImage_iff]
      simp only [Option.some.injEq, Sum.inr.injEq, eq_comm]

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem
    SpecialPeriods.MuTorsor.Cover.distinct_compactPatch_overlap_avoids_center {i k : Index}
    (hik : i ≠ k) (j : Elliptic.Kind) :
    SpecialPeriods.triangleOpenInclusion (SpecialPeriods.Triangle.ellipticOrbitCenter j) ∉
      (compactPatch i : Set SpecialPeriods.TriangleCompactifiedOrbitSpace) ∩ compactPatch k := by
  intro h
  exact
    hik
      (((compactPatch_center_unique j i).mp h.1).trans
        ((compactPatch_center_unique j k).mp h.2).symm)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.Cover.distinct_saturation_overlap_subset_regularLocus
    {i k : Index} (hik : i ≠ k) :
    (patch i).saturation ∩ (patch k).saturation ⊆ SpecialPeriods.triangleRegularLocus := by
  intro z hz
  have hq :
    SpecialPeriods.triangleCompactifiedProjection z ∈
      (compactPatch i : Set SpecialPeriods.TriangleCompactifiedOrbitSpace) ∩ compactPatch k :=
    ⟨(compactifiedProjection_mem_compactPatch i z).mpr hz.1,
      (compactifiedProjection_mem_compactPatch k z).mpr hz.2⟩
  apply (SpecialPeriods.triangleOrbitProjection_mem_regularDomain_iff z).mp
  apply (SpecialPeriods.triangleOrbitRegularDomain_mem_iff _).mpr
  constructor
  · intro h
    have he :
      SpecialPeriods.triangleCompactifiedProjection z =
        SpecialPeriods.triangleOpenInclusion
          (SpecialPeriods.Triangle.ellipticOrbitCenter .three) :=
      congrArg SpecialPeriods.triangleOpenInclusion h
    exact distinct_compactPatch_overlap_avoids_center hik .three (he ▸ hq)
  · intro h
    have he :
      SpecialPeriods.triangleCompactifiedProjection z =
        SpecialPeriods.triangleOpenInclusion
          (SpecialPeriods.Triangle.ellipticOrbitCenter .four) :=
      congrArg SpecialPeriods.triangleOpenInclusion h
    exact distinct_compactPatch_overlap_avoids_center hik .four (he ▸ hq)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.MuTorsor.Cover.finitePatch
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (i : Index) : TopologicalSpace.Opens ℂ :=
  finitePullback π (compactPatch i)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.Cover.exists_finitePatch
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (z : ℂ) : ∃ i : Index, z ∈ finitePatch π i :=
  exists_compactPatch (finiteInverse π z)

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.Cover.finitePatch_cusp_contains_exterior
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) :
    ∃ R : ℝ, 0 < R ∧ (Metric.ball (0 : ℂ) R)ᶜ ⊆ finitePatch π cuspIndex :=
  finitePullback_contains_exterior π hπ
    (SpecialPeriods.Triangle.cuspNeighborhood SpecialPeriods.Triangle.width)
    (SpecialPeriods.Triangle.cuspPoint_mem_cuspNeighborhood SpecialPeriods.Triangle.width)

private theorem SpecialPeriods.MuTorsor.PreciselyInvariantPatch.Seed.translated_values_agree
    {P : SpecialPeriods.MuTorsor.PreciselyInvariantPatch}
    {c : SpecialPeriods.MuTorsor.AffineCocycle} (s : P.Seed c)
    (g h : SpecialPeriods.TriangleGroup) (x y : ℍ) (hx : x ∈ P.sheet) (hy : y ∈ P.sheet)
    (he :
      SpecialPeriods.triangleGeometricRepresentation g x =
        SpecialPeriods.triangleGeometricRepresentation h y) :
    c.fibreMap g x (s.toFun x) = c.fibreMap h y (s.toFun y) := by
  have hxy : SpecialPeriods.triangleGeometricRepresentation (h⁻¹ * g) x = y := by
    rw [map_mul]
    change
      SpecialPeriods.triangleGeometricRepresentation h⁻¹
          (SpecialPeriods.triangleGeometricRepresentation g x) =
        y
    rw [he, map_inv]
    exact (SpecialPeriods.triangleGeometricRepresentation h).symm_apply_apply y
  have hk : h⁻¹ * g ∈ P.stabilizer := (P.stabilizer_mem_iff (h⁻¹ * g) x hx).mp (hxy ▸ hy)
  have hs := s.equivariant ⟨h⁻¹ * g, hk⟩ x hx
  change
    s.toFun (SpecialPeriods.triangleGeometricRepresentation (h⁻¹ * g) x) =
      c.fibreMap (h⁻¹ * g) x (s.toFun x) at hs
  rw [hxy] at hs
  calc
    c.fibreMap g x (s.toFun x) = c.fibreMap (h * (h⁻¹ * g)) x (s.toFun x) := by
      rw [mul_inv_cancel_left]
    _ =
        c.fibreMap h (SpecialPeriods.triangleGeometricRepresentation (h⁻¹ * g) x)
          (c.fibreMap (h⁻¹ * g) x (s.toFun x)) :=
      c.fibreMap_mul ..
    _ = c.fibreMap h y (s.toFun y) := by rw [hxy, ← hs]

private def SpecialPeriods.MuTorsor.PreciselyInvariantPatch.representative
    (P : SpecialPeriods.MuTorsor.PreciselyInvariantPatch) (z : P.saturation) :
    SpecialPeriods.TriangleGroup × P.sheet :=
  let hg := z.property.choose_spec
  ⟨z.property.choose, ⟨hg.choose, hg.choose_spec.1⟩⟩

private theorem SpecialPeriods.MuTorsor.PreciselyInvariantPatch.representative_spec
    (P : SpecialPeriods.MuTorsor.PreciselyInvariantPatch) (z : P.saturation) :
    SpecialPeriods.triangleGeometricRepresentation (P.representative z).1 (P.representative z).2 =
      z :=
  z.property.choose_spec.choose_spec.2

private def SpecialPeriods.MuTorsor.PreciselyInvariantPatch.Seed.extend
    {P : SpecialPeriods.MuTorsor.PreciselyInvariantPatch}
    {c : SpecialPeriods.MuTorsor.AffineCocycle} (s : P.Seed c) (z : ℍ) : ℂ := by
  classical
    exact
    if hz : z ∈ P.saturation then
      let r := P.representative ⟨z, hz⟩
      c.fibreMap r.1 r.2 (s.toFun r.2)
    else 0

private theorem SpecialPeriods.MuTorsor.PreciselyInvariantPatch.Seed.extend_translate
    {P : SpecialPeriods.MuTorsor.PreciselyInvariantPatch}
    {c : SpecialPeriods.MuTorsor.AffineCocycle} (s : P.Seed c) (g : SpecialPeriods.TriangleGroup)
    (x : ℍ) (hx : x ∈ P.sheet) :
    s.extend (SpecialPeriods.triangleGeometricRepresentation g x) = c.fibreMap g x (s.toFun x) := by
  have hz : SpecialPeriods.triangleGeometricRepresentation g x ∈ P.saturation := ⟨g, x, hx, rfl⟩
  rw [SpecialPeriods.MuTorsor.PreciselyInvariantPatch.Seed.extend, dite_eq_left hz]
  exact
    s.translated_values_agree _ g _ x (P.representative ⟨_, hz⟩).2.property hx
      (P.representative_spec ⟨_, hz⟩)

private theorem SpecialPeriods.MuTorsor.PreciselyInvariantPatch.Seed.extend_eq
    {P : SpecialPeriods.MuTorsor.PreciselyInvariantPatch}
    {c : SpecialPeriods.MuTorsor.AffineCocycle} (s : P.Seed c) (x : ℍ) (hx : x ∈ P.sheet) :
    s.extend x = s.toFun x := by
  simpa only [map_one, Equiv.Perm.one_apply, c.fibreMap_one] using s.extend_translate 1 x hx

private theorem SpecialPeriods.MuTorsor.PreciselyInvariantPatch.Seed.extend_equivariant
    {P : SpecialPeriods.MuTorsor.PreciselyInvariantPatch}
    {c : SpecialPeriods.MuTorsor.AffineCocycle} (s : P.Seed c) :
    c.EquivariantOn s.extend P.saturation := by
  intro g z hz
  obtain ⟨h, x, hx, rfl⟩ := hz
  have hmul :
    SpecialPeriods.triangleGeometricRepresentation g
        (SpecialPeriods.triangleGeometricRepresentation h x) =
      SpecialPeriods.triangleGeometricRepresentation (g * h) x := by simp
  rw [hmul, s.extend_translate (g * h) x hx, s.extend_translate h x hx, c.fibreMap_mul]

private theorem SpecialPeriods.MuTorsor.PreciselyInvariantPatch.Seed.extend_holomorphic
    {P : SpecialPeriods.MuTorsor.PreciselyInvariantPatch}
    {c : SpecialPeriods.MuTorsor.AffineCocycle} (s : P.Seed c) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω s.extend P.saturation := by
  rintro z ⟨g, x, hx, rfl⟩
  apply ContMDiffAt.contMDiffWithinAt
  let v : ℍ → ℍ := SpecialPeriods.triangleGeometricRepresentation g⁻¹
  have hv : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω v :=
    SpecialPeriods.triangleGeometricRepresentation_holomorphic g⁻¹
  have hvx : v (SpecialPeriods.triangleGeometricRepresentation g x) = x := by simp [v, map_inv]
  have hsx : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω s.toFun x :=
    s.holomorphic.contMDiffAt (P.sheet.isOpen.mem_nhds hx)
  have hcomp :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (s.toFun ∘ v) (SpecialPeriods.triangleGeometricRepresentation g x) :=
    hsx.comp_of_eq (hv _) hvx
  have ha :=
    ((c.scale_holomorphic g).comp hv) (SpecialPeriods.triangleGeometricRepresentation g x)
  have hb :=
    ((c.shift_holomorphic g).comp hv) (SpecialPeriods.triangleGeometricRepresentation g x)
  apply (ha.mul hcomp |>.add hb).congr_of_eventuallyEq
  have hnear : ∀ᶠ y in 𝓝 (SpecialPeriods.triangleGeometricRepresentation g x), v y ∈ P.sheet := by
    apply hv.continuous.continuousAt.preimage_mem_nhds
    rw [hvx]
    exact P.sheet.isOpen.mem_nhds hx
  filter_upwards [hnear] with y hy
  have hgy : SpecialPeriods.triangleGeometricRepresentation g (v y) = y := by simp [v, map_inv]
  have he := s.extend_translate g (v y) hy
  rw [hgy] at he
  exact he

private def SpecialPeriods.MuTorsor.ellipticFormula (τ : ℍ → ℍ) : Elliptic.Kind → ℍ → ℂ
  | .three, z => (2 - (τ z : ℂ)) / 3
  | .four, z => (1 - (τ z : ℂ)) / 2

private theorem SpecialPeriods.MuTorsor.ellipticFormula_holomorphic {τ : ℍ → ℍ}
    (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (j : Elliptic.Kind) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (ellipticFormula τ j) := by
  have ht := UpperHalfPlane.contMDiff_coe.comp hτa
  cases j
  · exact (contMDiff_const.sub ht).div₀ contMDiff_const (fun _ => by norm_num)
  · exact (contMDiff_const.sub ht).div₀ contMDiff_const (fun _ => by norm_num)

private theorem SpecialPeriods.MuTorsor.ellipticFormula_generator {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (j : Elliptic.Kind)
    (z : ℍ) :
    ellipticFormula τ j
        (SpecialPeriods.triangleGeometricRepresentation
          (SpecialPeriods.Triangle.ellipticGenerator j) z) =
      (cocycle hτ hτa).fibreMap (SpecialPeriods.Triangle.ellipticGenerator j) z
        (ellipticFormula τ j z) := by
  cases j
  · change
      (2 -
            (τ
                (SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleGenerator₁
                  z) :
              ℂ)) /
          3 =
        _
    dsimp only [SpecialPeriods.Triangle.ellipticGenerator]
    rw [SpecialPeriods.triangleGeometricRepresentation_generator₁_apply, hτ.1 z,
      cocycle_fibreMap_generator₁]
    dsimp only [ellipticFormula]
    field_simp [(τ z).ne_zero]
    ring
  · change
      (1 -
            (τ
                (SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleGenerator₂
                  z) :
              ℂ)) /
          2 =
        _
    dsimp only [SpecialPeriods.Triangle.ellipticGenerator]
    rw [SpecialPeriods.triangleGeometricRepresentation_generator₂_apply, hτ.2 z,
      cocycle_fibreMap_generator₂]
    dsimp only [ellipticFormula]
    field_simp [(τ z).ne_zero]
    ring

private def SpecialPeriods.MuTorsor.regularSeed {τ : ℍ → ℍ} (hτ : SpecialPeriods.TauCovariant τ)
    (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (x : SpecialPeriods.TriangleRegularQuotient) :
    (Cover.regularPatch x).Seed (cocycle hτ hτa)
    where
  toFun _ := 0
  holomorphic := contMDiffOn_const
  equivariant := by
    intro g z _
    have hg : (g : SpecialPeriods.TriangleGroup) = 1 := Subgroup.mem_bot.mp g.property
    simp only [hg, AffineCocycle.fibreMap_one]

private def SpecialPeriods.MuTorsor.cuspSeed {τ : ℍ → ℍ} (hτ : SpecialPeriods.TauCovariant τ)
    (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) : Cover.cuspPatch.Seed (cocycle hτ hτa)
    where
  toFun _ := 0
  holomorphic := contMDiffOn_const
  equivariant := by
    intro g z _
    exact
      (cocycle hτ hτa).equivariant_of_mem_zpowers (fun _ => 0)
        SpecialPeriods.triangleCuspGenerator (fun w => (cocycle_fibreMap_cusp hτ hτa w 0).symm)
        g.property z

private def SpecialPeriods.MuTorsor.ellipticSeed {τ : ℍ → ℍ} (hτ : SpecialPeriods.TauCovariant τ)
    (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (j : Elliptic.Kind) :
    (Cover.ellipticPatch j).Seed (cocycle hτ hτa)
    where
  toFun := ellipticFormula τ j
  holomorphic := (ellipticFormula_holomorphic hτa j).contMDiffOn
  equivariant := by
    intro g z _
    have hg :
      (g : SpecialPeriods.TriangleGroup) ∈
        Subgroup.zpowers (SpecialPeriods.Triangle.ellipticGenerator j) := by
      rw [← SpecialPeriods.Triangle.ellipticStabilizer_eq_zpowers]
      exact g.property
    exact
      (cocycle hτ hτa).equivariant_of_mem_zpowers (ellipticFormula τ j)
        (SpecialPeriods.Triangle.ellipticGenerator j) (ellipticFormula_generator hτ hτa j) hg z

private def SpecialPeriods.MuTorsor.seed {τ : ℍ → ℍ} (hτ : SpecialPeriods.TauCovariant τ)
    (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) : (i : Cover.Index) → (Cover.patch i).Seed (cocycle hτ hτa)
  | none => cuspSeed hτ hτa
  | some (.inl x) => regularSeed hτ hτa x
  | some (.inr j) => ellipticSeed hτ hτa j

private def SpecialPeriods.MuTorsor.localSection {τ : ℍ → ℍ} (hτ : SpecialPeriods.TauCovariant τ)
    (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (i : Cover.Index) : ℍ → ℂ :=
  (seed hτ hτa i).extend

private theorem SpecialPeriods.MuTorsor.localSection_holomorphic {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (i : Cover.Index) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (localSection hτ hτa i) (Cover.patch i).saturation :=
  (seed hτ hτa i).extend_holomorphic

private theorem SpecialPeriods.MuTorsor.localSection_equivariant {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (i : Cover.Index) :
    (cocycle hτ hτa).EquivariantOn (localSection hτ hτa i) (Cover.patch i).saturation :=
  (seed hτ hτa i).extend_equivariant

private theorem
    SpecialPeriods.MuTorsor.localSection_cusp {τ : ℍ → ℍ} (hτ : SpecialPeriods.TauCovariant τ)
    (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (z : ℍ)
    (hz : z ∈ SpecialPeriods.Triangle.horodisc SpecialPeriods.Triangle.width) :
    localSection hτ hτa Cover.cuspIndex z = 0 :=
  (cuspSeed hτ hτa).extend_eq z hz

private def SpecialPeriods.MuGenerator.FiniteEvenZeros (τ : ℍ → ℍ) : Prop :=
  ∀ a : ℍ,
    ModularForm.E₆ (τ a) = 0 →
      ∃ n : ℕ,
        analyticOrderAt (fun z : ℂ => ModularForm.E₆ (τ (UpperHalfPlane.ofComplex z))) (a : ℂ) =
          (2 * n : ℕ)

private theorem
    SpecialPeriods.MuGenerator.finiteEvenZeros_of_modular_equation {τ : ℍ → ℍ} {J : ℍ → ℂ}
    (hτ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) τ) (hJ : ∀ a : ℍ, SpecialPeriods.modularJ (τ a) = J a)
    (hsource :
      ∀ a : ℍ,
        J a = 1728 →
          ∃ k : ℕ,
            analyticOrderAt (fun z : ℂ => J (UpperHalfPlane.ofComplex z) - 1728) (a : ℂ) =
              (4 * k : ℕ)) :
    FiniteEvenZeros τ :=
  SpecialPeriods.ModularGermLift.native_E₆_finite_even_zeros hτ hJ hsource

private structure SpecialPeriods.MuGenerator.Root (τ : ℍ → ℍ) where
  toFun : ℍ → ℂ
  holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω toFun
  square : ∀ a : ℍ, toFun a ^ 2 = ModularForm.E₆ (τ a)

private instance
    SpecialPeriods.MuGenerator.instCoeFun1 {τ : ℍ → ℍ} : CoeFun (Root τ) (fun _ => ℍ → ℂ) :=
  ⟨Root.toFun⟩

private theorem
    SpecialPeriods.MuGenerator.nonempty_root {τ : ℍ → ℍ} (hτ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) τ)
    (hzero : FiniteEvenZeros τ) : Nonempty (Root τ) := by
  obtain ⟨r, hr, hrsq, _⟩ :=
    AnalyticRootCover.exists_holomorphic_square_root_upperHalfPlane
      (fun a => ModularForm.E₆ (τ a)) (ModularForm.E₆.holo'.comp hτ) hzero
  exact ⟨⟨r, hr, hrsq⟩⟩

private def SpecialPeriods.MuGenerator.root (τ : ℍ → ℍ) (hτ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) τ)
    (hzero : FiniteEvenZeros τ) : Root τ :=
  Classical.choice (nonempty_root hτ hzero)

private theorem SpecialPeriods.MuGenerator.modularForm_holomorphic {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f := by
  intro a
  exact UpperHalfPlane.contMDiffAt_iff.mpr (SpecialPeriods.modularForm_analyticAt f a).contDiffAt

private theorem SpecialPeriods.MuGenerator.Root.analyticAt {τ : ℍ → ℍ}
    (r : SpecialPeriods.MuGenerator.Root τ) (a : ℍ) :
    AnalyticAt ℂ (r ∘ UpperHalfPlane.ofComplex) (a : ℂ) :=
  (UpperHalfPlane.contMDiffAt_iff.mp (r.holomorphic a)).analyticAt

@[simp]
private theorem SpecialPeriods.MuGenerator.Root.eq_zero_iff {τ : ℍ → ℍ}
    (r : SpecialPeriods.MuGenerator.Root τ) (a : ℍ) : r a = 0 ↔ ModularForm.E₆ (τ a) = 0 := by
  rw [← r.square a]
  exact (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).symm

private theorem SpecialPeriods.MuGenerator.Root.order_of_square_order {τ : ℍ → ℍ}
    (r : SpecialPeriods.MuGenerator.Root τ) (a : ℍ) (n : ℕ)
    (horder :
      analyticOrderAt (fun z : ℂ => ModularForm.E₆ (τ (UpperHalfPlane.ofComplex z))) (a : ℂ) =
        (2 * n : ℕ)) :
    analyticOrderAt (r ∘ UpperHalfPlane.ofComplex) (a : ℂ) = n := by
  apply AnalyticRootCover.square_root_order (r.analyticAt a) _ horder
  filter_upwards with z
  exact r.square (UpperHalfPlane.ofComplex z)

private def SpecialPeriods.MuGenerator.Root.generator {τ : ℍ → ℍ}
    (r : SpecialPeriods.MuGenerator.Root τ) : ℍ → ℂ := fun a =>
  ModularForm.E₄ (τ a) ^ 2 * r a / ModularForm.discriminant (τ a)

private theorem SpecialPeriods.MuGenerator.Root.generator_holomorphic {τ : ℍ → ℍ}
    (r : SpecialPeriods.MuGenerator.Root τ) (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω r.generator := by
  have h4 : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun a => ModularForm.E₄ (τ a)) :=
    (SpecialPeriods.MuGenerator.modularForm_holomorphic ModularForm.E₄).comp hτ
  have hD : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun a => ModularForm.discriminant (τ a)) :=
    (SpecialPeriods.MuGenerator.modularForm_holomorphic
          (CuspForm.discriminant : ModularForm 𝒮ℒ 12)).comp
      hτ
  exact ((h4.pow 2).mul r.holomorphic).div₀ hD (fun a => ModularForm.discriminant_ne_zero (τ a))

private theorem SpecialPeriods.MuGenerator.Root.generator_eq_zero_iff {τ : ℍ → ℍ}
    (r : SpecialPeriods.MuGenerator.Root τ) (a : ℍ) :
    r.generator a = 0 ↔ ModularForm.E₄ (τ a) = 0 ∨ ModularForm.E₆ (τ a) = 0 := by
  simp only [generator, div_eq_zero_iff, ModularForm.discriminant_ne_zero, or_false, mul_eq_zero,
    pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0), r.eq_zero_iff]

private theorem SpecialPeriods.MuGenerator.Root.generator_eq_zero_iff_modularJ {τ : ℍ → ℍ}
    (r : SpecialPeriods.MuGenerator.Root τ) (a : ℍ) :
    r.generator a = 0 ↔
      SpecialPeriods.modularJ (τ a) = 0 ∨ SpecialPeriods.modularJ (τ a) = 1728 := by
  rw [r.generator_eq_zero_iff, SpecialPeriods.modularJ_eq_zero_iff,
    SpecialPeriods.modularJ_eq_1728_iff]

private theorem SpecialPeriods.MuGenerator.modularForm_pullback_analyticAt {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) {k : ℤ} (f : ModularForm 𝒮ℒ k) (a : ℍ) :
    AnalyticAt ℂ (fun z : ℂ => f (τ (UpperHalfPlane.ofComplex z))) (a : ℂ) :=
  (UpperHalfPlane.contMDiffAt_iff.mp ((modularForm_holomorphic f).comp hτ a)).analyticAt

private theorem SpecialPeriods.MuGenerator.Root.generator_order {τ : ℍ → ℍ}
    (r : SpecialPeriods.MuGenerator.Root τ) (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (a : ℍ) :
    analyticOrderAt (r.generator ∘ UpperHalfPlane.ofComplex) (a : ℂ) =
      2 • analyticOrderAt (fun z : ℂ => ModularForm.E₄ (τ (UpperHalfPlane.ofComplex z))) (a : ℂ) +
        analyticOrderAt (r ∘ UpperHalfPlane.ofComplex) (a : ℂ) := by
  let f4 : ℂ → ℂ := fun z => ModularForm.E₄ (τ (UpperHalfPlane.ofComplex z))
  let fD : ℂ → ℂ := fun z => ModularForm.discriminant (τ (UpperHalfPlane.ofComplex z))
  have h4 : AnalyticAt ℂ f4 (a : ℂ) :=
    SpecialPeriods.MuGenerator.modularForm_pullback_analyticAt hτ ModularForm.E₄ a
  have hD : AnalyticAt ℂ fD (a : ℂ) :=
    SpecialPeriods.MuGenerator.modularForm_pullback_analyticAt hτ
      (CuspForm.discriminant : ModularForm 𝒮ℒ 12) a
  have hD0 : fD (a : ℂ) ≠ 0 := by
    simpa only [fD, UpperHalfPlane.ofComplex_apply] using ModularForm.discriminant_ne_zero (τ a)
  have hDi := hD.inv hD0
  have hDiorder : analyticOrderAt fD⁻¹ (a : ℂ) = 0 :=
    hDi.analyticOrderAt_eq_zero.mpr (inv_ne_zero hD0)
  have he :
    r.generator ∘ UpperHalfPlane.ofComplex = (f4 ^ 2 * (r ∘ UpperHalfPlane.ofComplex)) * fD⁻¹ := by
    funext z
    exact div_eq_mul_inv _ _
  rw [he, analyticOrderAt_mul ((h4.pow 2).mul (r.analyticAt a)) hDi,
    analyticOrderAt_mul (h4.pow 2) (r.analyticAt a), analyticOrderAt_pow h4, hDiorder, add_zero]

private theorem SpecialPeriods.MuGenerator.Root.generator_order_of_pullback_orders {τ : ℍ → ℍ}
    (r : SpecialPeriods.MuGenerator.Root τ) (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (a : ℍ) (m n : ℕ)
    (h4 :
      analyticOrderAt (fun z : ℂ => ModularForm.E₄ (τ (UpperHalfPlane.ofComplex z))) (a : ℂ) = m)
    (h6 :
      analyticOrderAt (fun z : ℂ => ModularForm.E₆ (τ (UpperHalfPlane.ofComplex z))) (a : ℂ) =
        (2 * n : ℕ)) :
    analyticOrderAt (r.generator ∘ UpperHalfPlane.ofComplex) (a : ℂ) = (2 * m + n : ℕ) := by
  rw [r.generator_order hτ, h4, r.order_of_square_order a n h6]
  simp only [two_nsmul, ← Nat.cast_add]
  congr 1
  omega

private theorem SpecialPeriods.MuGenerator.Root.order_centerTwo_of_tau_order {τ : ℍ → ℍ}
    (r : SpecialPeriods.MuGenerator.Root τ) (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ)
    (hc : SpecialPeriods.TauCovariant τ)
    (ho :
      analyticOrderAt (fun z : ℂ => (τ (UpperHalfPlane.ofComplex z) : ℂ) - Complex.I)
          (SpecialPeriods.Triangle.centerTwo : ℂ) =
        2) :
    analyticOrderAt (r ∘ UpperHalfPlane.ofComplex) (SpecialPeriods.Triangle.centerTwo : ℂ) = 1 := by
  have hv := (SpecialPeriods.tau_covariant_values hc).2
  have h6 :=
    SpecialPeriods.ModularGermLift.native_E₆_lift_order_of_zero (hτ.mdifferentiable (by simp))
      (a := SpecialPeriods.Triangle.centerTwo) (by rw [hv, SpecialPeriods.E₆_I])
  rw [hv, UpperHalfPlane.coe_I] at h6
  apply r.order_of_square_order SpecialPeriods.Triangle.centerTwo 1
  simpa only [Nat.mul_one, Nat.cast_ofNat] using h6.trans ho

private theorem SpecialPeriods.MuGenerator.Root.generator_order_centerOne_of_tau_order {τ : ℍ → ℍ}
    (r : SpecialPeriods.MuGenerator.Root τ) (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ)
    (hc : SpecialPeriods.TauCovariant τ)
    (ho :
      analyticOrderAt (fun z : ℂ => (τ (UpperHalfPlane.ofComplex z) : ℂ) - SpecialPeriods.rho)
          (SpecialPeriods.Triangle.centerOne : ℂ) =
        1) :
    analyticOrderAt (r.generator ∘ UpperHalfPlane.ofComplex)
        (SpecialPeriods.Triangle.centerOne : ℂ) =
      2 := by
  have hv := (SpecialPeriods.tau_covariant_values hc).1
  have h4 :=
    SpecialPeriods.ModularGermLift.native_E₄_lift_order_of_zero (hτ.mdifferentiable (by simp))
      (a := SpecialPeriods.Triangle.centerOne) (by rw [hv, SpecialPeriods.E₄_rhoPoint])
  rw [hv, SpecialPeriods.coe_rhoPoint] at h4
  have h6 :
    analyticOrderAt (fun z : ℂ => ModularForm.E₆ (τ (UpperHalfPlane.ofComplex z)))
        (SpecialPeriods.Triangle.centerOne : ℂ) =
      (2 * 0 : ℕ) := by
    apply analyticOrderAt_eq_zero.mpr
    right
    simpa only [UpperHalfPlane.ofComplex_apply, hv] using SpecialPeriods.E₆_rhoPoint_ne_zero
  simpa only [Nat.mul_one, Nat.add_zero, Nat.cast_ofNat] using
    r.generator_order_of_pullback_orders hτ SpecialPeriods.Triangle.centerOne 1 0 (h4.trans ho) h6

private theorem SpecialPeriods.MuGenerator.Root.generator_order_centerTwo_of_tau_order {τ : ℍ → ℍ}
    (r : SpecialPeriods.MuGenerator.Root τ) (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ)
    (hc : SpecialPeriods.TauCovariant τ)
    (ho :
      analyticOrderAt (fun z : ℂ => (τ (UpperHalfPlane.ofComplex z) : ℂ) - Complex.I)
          (SpecialPeriods.Triangle.centerTwo : ℂ) =
        2) :
    analyticOrderAt (r.generator ∘ UpperHalfPlane.ofComplex)
        (SpecialPeriods.Triangle.centerTwo : ℂ) =
      1 := by
  have hv := (SpecialPeriods.tau_covariant_values hc).2
  have h4 :
    analyticOrderAt (fun z : ℂ => ModularForm.E₄ (τ (UpperHalfPlane.ofComplex z)))
        (SpecialPeriods.Triangle.centerTwo : ℂ) =
      0 := by
    apply analyticOrderAt_eq_zero.mpr
    right
    simpa only [UpperHalfPlane.ofComplex_apply, hv] using SpecialPeriods.E₄_I_ne_zero
  rw [r.generator_order hτ, h4, r.order_centerTwo_of_tau_order hτ hc ho, smul_zero, zero_add]

private theorem SpecialPeriods.upperHalfPlane_holomorphic_sq_eq_sq_dichotomy {f g : ℍ → ℂ}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) (hsq : ∀ z, f z ^ 2 = g z ^ 2) :
    f = g ∨ f = -g := by
  have hprod : (f - g) * (f + g) = 0 := by
    funext z
    change (f z - g z) * (f z + g z) = 0
    calc
      _ = f z ^ 2 - g z ^ 2 := by ring
      _ = 0 := sub_eq_zero.mpr (hsq z)
  rcases
    (UpperHalfPlane.mul_eq_zero_iff ((hf.sub hg).mdifferentiable (by simp))
          ((hf.add hg).mdifferentiable (by simp))).mp
      hprod with
    h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

private theorem SpecialPeriods.eisensteinSix_root_generatorOne_sq {τ : ℍ → ℍ} {r : ℍ → ℂ}
    (hτc : TauCovariant τ) (hrsq : ∀ z, r z ^ 2 = ModularForm.E₆ (τ z)) (z : ℍ) :
    r (Triangle.generatorOneSL • z) ^ 2 = ((τ z : ℂ) ^ 3 * r z) ^ 2 := by
  have hτg : τ (Triangle.generatorOneSL • z) = (ModularGroup.T * ModularGroup.S) • τ z := by
    apply UpperHalfPlane.ext
    rw [← modularRhoAction_coe]
    exact hτc.1 z
  have hd : UpperHalfPlane.denom (ModularGroup.T * ModularGroup.S : SL(2, ℤ)) (τ z) = (τ z : ℂ) :=
    by
    have h10 : (ModularGroup.T * ModularGroup.S : SL(2, ℤ)) 1 0 = 1 := by decide
    have h11 : (ModularGroup.T * ModularGroup.S : SL(2, ℤ)) 1 1 = 0 := by decide
    rw [ModularGroup.denom_apply, h10, h11]
    simp
  calc
    _ = ModularForm.E₆ (τ (Triangle.generatorOneSL • z)) := hrsq _
    _ = (τ z : ℂ) ^ 6 * ModularForm.E₆ (τ z) := by rw [hτg, levelOne_transform, hd, zpow_ofNat]
    _ = ((τ z : ℂ) ^ 3 * r z) ^ 2 := by
      rw [← hrsq z]
      ring

private theorem SpecialPeriods.eisensteinSix_root_generatorTwo_sq {τ : ℍ → ℍ} {r : ℍ → ℂ}
    (hτc : TauCovariant τ) (hrsq : ∀ z, r z ^ 2 = ModularForm.E₆ (τ z)) (z : ℍ) :
    r (Triangle.generatorTwoSL • z) ^ 2 = ((τ z : ℂ) ^ 3 * r z) ^ 2 := by
  have hτg : τ (Triangle.generatorTwoSL • z) = ModularGroup.S • τ z := by
    apply UpperHalfPlane.ext
    rw [← modularIAction_coe]
    exact hτc.2 z
  calc
    _ = ModularForm.E₆ (τ (Triangle.generatorTwoSL • z)) := hrsq _
    _ = (τ z : ℂ) ^ 6 * ModularForm.E₆ (τ z) := by
      rw [hτg, levelOne_transform, ModularGroup.denom_S, zpow_ofNat]
    _ = ((τ z : ℂ) ^ 3 * r z) ^ 2 := by
      rw [← hrsq z]
      ring

private theorem SpecialPeriods.eisensteinSix_root_centerOne_ne_zero {τ : ℍ → ℍ} {r : ℍ → ℂ}
    (hτc : TauCovariant τ) (hrsq : ∀ z, r z ^ 2 = ModularForm.E₆ (τ z)) :
    r Triangle.centerOne ≠ 0 := by
  intro hrzero
  have h := hrsq Triangle.centerOne
  rw [hrzero, zero_pow (by decide), (tau_covariant_values hτc).1] at h
  exact E₆_rhoPoint_ne_zero h.symm

private theorem SpecialPeriods.eisensteinSix_root_generatorOne {τ : ℍ → ℍ} {r : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hτc : TauCovariant τ) (hr : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω r)
    (hrsq : ∀ z, r z ^ 2 = ModularForm.E₆ (τ z)) :
    ∀ z, r (Triangle.generatorOneSL • z) = -(τ z : ℂ) ^ 3 * r z := by
  have hweight : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => (τ z : ℂ) ^ 3 * r z) :=
    ((UpperHalfPlane.contMDiff_coe.comp hτ).pow 3).mul hr
  rcases
    upperHalfPlane_holomorphic_sq_eq_sq_dichotomy
      (hr.comp (Triangle.specialLinear_holomorphic Triangle.generatorOneSL)) hweight
      (eisensteinSix_root_generatorOne_sq hτc hrsq) with
    hpos | hneg
  · exfalso
    have h := congrFun hpos Triangle.centerOne
    change
      r (Triangle.generatorOneSL • Triangle.centerOne) =
        (τ Triangle.centerOne : ℂ) ^ 3 * r Triangle.centerOne at h
    rw [Triangle.generatorOne_fix, (tau_covariant_values hτc).1, coe_rhoPoint, rho_cube,
      neg_one_mul] at h
    apply eisensteinSix_root_centerOne_ne_zero hτc hrsq
    linear_combination h / 2
  · intro z
    simpa only [Function.comp_apply, Pi.neg_apply, neg_mul] using congrFun hneg z

private theorem SpecialPeriods.eisensteinSix_root_generatorTwo_dichotomy {τ : ℍ → ℍ} {r : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hτc : TauCovariant τ) (hr : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω r)
    (hrsq : ∀ z, r z ^ 2 = ModularForm.E₆ (τ z)) :
    (∀ z, r (Triangle.generatorTwoSL • z) = (τ z : ℂ) ^ 3 * r z) ∨
      (∀ z, r (Triangle.generatorTwoSL • z) = -(τ z : ℂ) ^ 3 * r z) := by
  have hweight : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => (τ z : ℂ) ^ 3 * r z) :=
    ((UpperHalfPlane.contMDiff_coe.comp hτ).pow 3).mul hr
  rcases
    upperHalfPlane_holomorphic_sq_eq_sq_dichotomy
      (hr.comp (Triangle.specialLinear_holomorphic Triangle.generatorTwoSL)) hweight
      (eisensteinSix_root_generatorTwo_sq hτc hrsq) with
    hpos | hneg
  · exact Or.inl (congrFun hpos)
  · right
    intro z
    simpa only [Function.comp_apply, Pi.neg_apply, neg_mul] using congrFun hneg z

private theorem
    SpecialPeriods.holomorphic_simple_zero_not_generatorTwo_negative {τ : ℍ → ℍ} {r : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hτc : TauCovariant τ) (hr : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω r)
    (horder : analyticOrderAt (r ∘ UpperHalfPlane.ofComplex) (Triangle.centerTwo : ℂ) = 1) :
    ¬(∀ z, r (Triangle.generatorTwoSL • z) = -(τ z : ℂ) ^ 3 * r z) := by
  intro hneg
  let R : ℂ → ℂ := r ∘ UpperHalfPlane.ofComplex
  let T : ℂ → ℂ := fun z => (τ (UpperHalfPlane.ofComplex z) : ℂ)
  let B : ℂ → ℂ := fun z => ((Triangle.generatorTwoSL • UpperHalfPlane.ofComplex z : ℍ) : ℂ)
  let c : ℂ := (Triangle.centerTwo : ℂ)
  have hRA : AnalyticAt ℂ R c :=
    (UpperHalfPlane.contMDiffAt_iff.mp (hr Triangle.centerTwo)).analyticAt
  have hTA : AnalyticAt ℂ T c :=
    (UpperHalfPlane.contMDiffAt_iff.mp
        ((UpperHalfPlane.contMDiff_coe.comp hτ) Triangle.centerTwo)).analyticAt
  have hRorder : analyticOrderAt R c = 1 := horder
  have hRzero : R c = 0 :=
    apply_eq_zero_of_analyticOrderAt_ne_zero (by rw [hRorder]; exact one_ne_zero)
  have hdOrder : analyticOrderAt (deriv R) c = 0 :=
    analyticOrderAt_deriv_of_pos hRA (n := 0) (by simpa using hRorder)
  have hd : deriv R c ≠ 0 := hRA.deriv.analyticOrderAt_eq_zero.mp hdOrder
  have hBc : B c = c := by
    dsimp only [B, c]
    rw [UpperHalfPlane.ofComplex_apply, Triangle.generatorTwo_fix]
  have hTc : T c = Complex.I := by
    dsimp only [T, c]
    rw [UpperHalfPlane.ofComplex_apply, (tau_covariant_values hτc).2]
    rfl
  have hB : HasDerivAt B (-Complex.I) c := Triangle.generatorTwo_hasStrictDerivAt.hasDerivAt
  have hRder : HasDerivAt R (deriv R c) (B c) := by
    rw [hBc]
    exact hRA.differentiableAt.hasDerivAt
  have hleft :
    HasDerivAt (fun z : ℂ => r (Triangle.generatorTwoSL • UpperHalfPlane.ofComplex z))
      (deriv R c * -Complex.I) c := by
    simpa only [Function.comp_def, R, B, UpperHalfPlane.ofComplex_apply] using hRder.comp c hB
  have hright : HasDerivAt (fun z : ℂ => -(T z) ^ 3 * R z) _ c :=
    ((hTA.differentiableAt.hasDerivAt.pow 3).neg).mul hRA.differentiableAt.hasDerivAt
  have hright' : HasDerivAt (fun z : ℂ => -(T z) ^ 3 * R z) (Complex.I * deriv R c) c := by
    simpa [hRzero, hTc, Complex.I_sq, pow_succ] using hright
  have hfun :
    (fun z : ℂ => r (Triangle.generatorTwoSL • UpperHalfPlane.ofComplex z)) =
      (fun z : ℂ => -(T z) ^ 3 * R z) := by
    funext z
    exact hneg (UpperHalfPlane.ofComplex z)
  rw [hfun] at hleft
  have heq := hleft.unique hright'
  have hI : -Complex.I = Complex.I := by
    apply mul_right_cancel₀ hd
    simpa only [mul_comm] using heq
  have him := congrArg Complex.im hI
  norm_num at him

private theorem SpecialPeriods.eisensteinSix_root_generatorTwo {τ : ℍ → ℍ} {r : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hτc : TauCovariant τ) (hr : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω r)
    (hrsq : ∀ z, r z ^ 2 = ModularForm.E₆ (τ z))
    (horder : analyticOrderAt (r ∘ UpperHalfPlane.ofComplex) (Triangle.centerTwo : ℂ) = 1) :
    ∀ z, r (Triangle.generatorTwoSL • z) = (τ z : ℂ) ^ 3 * r z := by
  rcases eisensteinSix_root_generatorTwo_dichotomy hτ hτc hr hrsq with hpos | hneg
  · exact hpos
  · exact (holomorphic_simple_zero_not_generatorTwo_negative hτ hτc hr horder hneg).elim

private theorem SpecialPeriods.MuGenerator.modularForm_generatorOne {τ : ℍ → ℍ} {k : ℤ}
    (f : ModularForm 𝒮ℒ k) (hτc : SpecialPeriods.TauCovariant τ) (z : ℍ) :
    f (τ (SpecialPeriods.Triangle.generatorOneSL • z)) = (τ z : ℂ) ^ k * f (τ z) := by
  have hτg :
    τ (SpecialPeriods.Triangle.generatorOneSL • z) = (ModularGroup.T * ModularGroup.S) • τ z := by
    apply UpperHalfPlane.ext
    rw [← SpecialPeriods.modularRhoAction_coe]
    exact hτc.1 z
  have hd : UpperHalfPlane.denom (ModularGroup.T * ModularGroup.S : SL(2, ℤ)) (τ z) = (τ z : ℂ) :=
    by
    have h10 : (ModularGroup.T * ModularGroup.S : SL(2, ℤ)) 1 0 = 1 := by decide
    have h11 : (ModularGroup.T * ModularGroup.S : SL(2, ℤ)) 1 1 = 0 := by decide
    rw [ModularGroup.denom_apply, h10, h11]
    simp
  rw [hτg, SpecialPeriods.levelOne_transform, hd]

private theorem SpecialPeriods.MuGenerator.modularForm_generatorTwo {τ : ℍ → ℍ} {k : ℤ}
    (f : ModularForm 𝒮ℒ k) (hτc : SpecialPeriods.TauCovariant τ) (z : ℍ) :
    f (τ (SpecialPeriods.Triangle.generatorTwoSL • z)) = (τ z : ℂ) ^ k * f (τ z) := by
  have hτg : τ (SpecialPeriods.Triangle.generatorTwoSL • z) = ModularGroup.S • τ z := by
    apply UpperHalfPlane.ext
    rw [← SpecialPeriods.modularIAction_coe]
    exact hτc.2 z
  rw [hτg, SpecialPeriods.levelOne_transform, ModularGroup.denom_S]

private theorem SpecialPeriods.MuGenerator.triangle_invariant_of_generators (f : ℍ → ℂ)
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
  | mem x hx =>
    rcases hx with rfl | rfl
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

private theorem SpecialPeriods.MuGenerator.Root.generator_generatorOne {τ : ℍ → ℍ}
    (r : SpecialPeriods.MuGenerator.Root τ) (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ)
    (hτc : SpecialPeriods.TauCovariant τ) (z : ℍ) :
    r.generator (SpecialPeriods.Triangle.generatorOneSL • z) = -r.generator z / (τ z : ℂ) := by
  have h4 :
    ModularForm.E₄ (τ (SpecialPeriods.Triangle.generatorOneSL • z)) =
      (τ z : ℂ) ^ 4 * ModularForm.E₄ (τ z) := by
    simpa only [zpow_ofNat] using
      SpecialPeriods.MuGenerator.modularForm_generatorOne ModularForm.E₄ hτc z
  have hD :
    ModularForm.discriminant (τ (SpecialPeriods.Triangle.generatorOneSL • z)) =
      (τ z : ℂ) ^ 12 * ModularForm.discriminant (τ z) := by
    have h :=
      SpecialPeriods.MuGenerator.modularForm_generatorOne
        (CuspForm.discriminant : ModularForm 𝒮ℒ 12) hτc z
    change
      ModularForm.discriminant (τ (SpecialPeriods.Triangle.generatorOneSL • z)) =
        (τ z : ℂ) ^ (12 : ℤ) * ModularForm.discriminant (τ z) at h
    simpa only [zpow_ofNat] using h
  rw [generator, h4, hD,
    SpecialPeriods.eisensteinSix_root_generatorOne hτ hτc r.holomorphic r.square z]
  dsimp only [generator]
  field_simp [(τ z).ne_zero, ModularForm.discriminant_ne_zero (τ z)]

private theorem SpecialPeriods.MuGenerator.Root.generator_generatorTwo {τ : ℍ → ℍ}
    (r : SpecialPeriods.MuGenerator.Root τ) (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ)
    (hτc : SpecialPeriods.TauCovariant τ)
    (horder :
      analyticOrderAt (r ∘ UpperHalfPlane.ofComplex) (SpecialPeriods.Triangle.centerTwo : ℂ) = 1)
    (z : ℍ) :
    r.generator (SpecialPeriods.Triangle.generatorTwoSL • z) = r.generator z / (τ z : ℂ) := by
  have h4 :
    ModularForm.E₄ (τ (SpecialPeriods.Triangle.generatorTwoSL • z)) =
      (τ z : ℂ) ^ 4 * ModularForm.E₄ (τ z) := by
    simpa only [zpow_ofNat] using
      SpecialPeriods.MuGenerator.modularForm_generatorTwo ModularForm.E₄ hτc z
  have hD :
    ModularForm.discriminant (τ (SpecialPeriods.Triangle.generatorTwoSL • z)) =
      (τ z : ℂ) ^ 12 * ModularForm.discriminant (τ z) := by
    have h :=
      SpecialPeriods.MuGenerator.modularForm_generatorTwo
        (CuspForm.discriminant : ModularForm 𝒮ℒ 12) hτc z
    change
      ModularForm.discriminant (τ (SpecialPeriods.Triangle.generatorTwoSL • z)) =
        (τ z : ℂ) ^ (12 : ℤ) * ModularForm.discriminant (τ z) at h
    simpa only [zpow_ofNat] using h
  rw [generator, h4, hD,
    SpecialPeriods.eisensteinSix_root_generatorTwo hτ hτc r.holomorphic r.square horder z]
  dsimp only [generator]
  field_simp [(τ z).ne_zero, ModularForm.discriminant_ne_zero (τ z)]

private theorem HolomorphicCousin.analyticOnNhd_dslope_zero {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (Metric.ball 0 R)) : AnalyticOnNhd ℂ (dslope f 0) (Metric.ball 0 R) :=
  (Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).mpr
    ((Complex.differentiableOn_dslope (Metric.ball_mem_nhds (0 : ℂ) hR)).mpr hf.differentiableOn)

private theorem HolomorphicCousin.zero_mul_dslope {f : ℂ → ℂ} (hf : f 0 = 0) (z : ℂ) :
    z * dslope f 0 z = f z := by
  simpa only [sub_zero, smul_eq_mul] using sub_smul_dslope_of_zero hf z

private theorem
    SpecialPeriods.MuGenerator.scalar_analyticAt {f : ℍ → ℂ} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (a : ℍ) : AnalyticAt ℂ (f ∘ UpperHalfPlane.ofComplex) (a : ℂ) :=
  (UpperHalfPlane.mdifferentiable_iff.mp (hf.mdifferentiable (by simp))).analyticAt
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds a.im_pos)

private theorem SpecialPeriods.MuGenerator.homogeneous_centerOne_eq_zero {τ : ℍ → ℍ} {ν : ℍ → ℂ}
    (hν₁ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorOneSL • z) = -ν z / (τ z : ℂ)) :
    ν SpecialPeriods.Triangle.centerOne = 0 := by
  have he := hν₁ SpecialPeriods.Triangle.centerOne
  rw [SpecialPeriods.Triangle.generatorOne_fix] at he
  have hmul :
    ν SpecialPeriods.Triangle.centerOne * (τ SpecialPeriods.Triangle.centerOne : ℂ) =
      -ν SpecialPeriods.Triangle.centerOne :=
    (eq_div_iff (τ SpecialPeriods.Triangle.centerOne).ne_zero).mp he
  have hz :
    ν SpecialPeriods.Triangle.centerOne * ((τ SpecialPeriods.Triangle.centerOne : ℂ) + 1) = 0 := by
    calc
      _ =
          ν SpecialPeriods.Triangle.centerOne * (τ SpecialPeriods.Triangle.centerOne : ℂ) +
            ν SpecialPeriods.Triangle.centerOne := by ring
      _ = 0 := by rw [hmul]; ring
  apply (mul_eq_zero.mp hz).resolve_right
  intro hc
  have hi := congrArg Complex.im hc
  simp only [Complex.add_im, Complex.one_im, add_zero, Complex.zero_im] at hi
  exact (τ SpecialPeriods.Triangle.centerOne).im_ne_zero hi

private theorem SpecialPeriods.MuGenerator.homogeneous_centerTwo_eq_zero {τ : ℍ → ℍ} {ν : ℍ → ℂ}
    (hν₂ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorTwoSL • z) = ν z / (τ z : ℂ)) :
    ν SpecialPeriods.Triangle.centerTwo = 0 := by
  have he := hν₂ SpecialPeriods.Triangle.centerTwo
  rw [SpecialPeriods.Triangle.generatorTwo_fix] at he
  have hmul :
    ν SpecialPeriods.Triangle.centerTwo * (τ SpecialPeriods.Triangle.centerTwo : ℂ) =
      ν SpecialPeriods.Triangle.centerTwo :=
    (eq_div_iff (τ SpecialPeriods.Triangle.centerTwo).ne_zero).mp he
  have hz :
    ν SpecialPeriods.Triangle.centerTwo * ((τ SpecialPeriods.Triangle.centerTwo : ℂ) - 1) = 0 := by
    calc
      _ =
          ν SpecialPeriods.Triangle.centerTwo * (τ SpecialPeriods.Triangle.centerTwo : ℂ) -
            ν SpecialPeriods.Triangle.centerTwo := by ring
      _ = 0 := by rw [hmul]; ring
  apply (mul_eq_zero.mp hz).resolve_right
  intro hc
  have hi := congrArg Complex.im hc
  simp only [Complex.sub_im, Complex.one_im, sub_zero, Complex.zero_im] at hi
  exact (τ SpecialPeriods.Triangle.centerTwo).im_ne_zero hi

private theorem
    SpecialPeriods.MuGenerator.homogeneous_fixed_derivative_identity {τ : ℍ → ℍ} {ν : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hν : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ν) (g : SL(2, ℝ)) (a : ℍ) (c : ℂ)
    (hfix : g • a = a) (hzero : ν a = 0) (hlaw : ∀ z : ℍ, ν (g • z) * (τ z : ℂ) = c * ν z) :
    (deriv (ν ∘ UpperHalfPlane.ofComplex) (a : ℂ) * SpecialPeriods.Triangle.slMultiplier g a) *
        (τ a : ℂ) =
      c * deriv (ν ∘ UpperHalfPlane.ofComplex) (a : ℂ) := by
  let V : ℂ → ℂ := ν ∘ UpperHalfPlane.ofComplex
  let T : ℂ → ℂ := fun z => (τ (UpperHalfPlane.ofComplex z) : ℂ)
  let A : ℂ → ℂ := fun z => ((g • UpperHalfPlane.ofComplex z : ℍ) : ℂ)
  have hV := (scalar_analyticAt hν a).differentiableAt.hasDerivAt
  have hTa := scalar_analyticAt (UpperHalfPlane.contMDiff_coe.comp hτ) a
  have hT := hTa.differentiableAt.hasDerivAt
  have hA : HasDerivAt A (SpecialPeriods.Triangle.slMultiplier g a) (a : ℂ) :=
    (SpecialPeriods.Triangle.sl_hasStrictDerivAt_smul g a).hasDerivAt
  have hAa : A (a : ℂ) = (a : ℂ) := by simp [A, hfix]
  have hVo : HasDerivAt V (deriv V (a : ℂ)) (A (a : ℂ)) := by
    rw [hAa]
    exact hV
  have hcomp :
    HasDerivAt (fun z : ℂ => ν (g • UpperHalfPlane.ofComplex z))
      (deriv V (a : ℂ) * SpecialPeriods.Triangle.slMultiplier g a) (a : ℂ) := by
    simpa only [V, A, Function.comp_def, UpperHalfPlane.ofComplex_apply] using hVo.comp (a : ℂ) hA
  have hprod :
    HasDerivAt (fun z : ℂ => ν (g • UpperHalfPlane.ofComplex z) * T z)
      ((deriv V (a : ℂ) * SpecialPeriods.Triangle.slMultiplier g a) * (τ a : ℂ)) (a : ℂ) := by
    simpa only [T, Function.comp_def, Pi.mul_def, UpperHalfPlane.ofComplex_apply, hfix, hzero,
      MulZeroClass.zero_mul, add_zero] using hcomp.mul hT
  have he : (fun z : ℂ => ν (g • UpperHalfPlane.ofComplex z) * T z) = fun z => c * V z := by
    funext z
    exact hlaw (UpperHalfPlane.ofComplex z)
  rw [he] at hprod
  exact hprod.unique (hV.const_mul c)

private theorem
    SpecialPeriods.MuGenerator.homogeneous_centerOne_deriv_eq_zero {τ : ℍ → ℍ} {ν : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hτc : SpecialPeriods.TauCovariant τ)
    (hν : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ν)
    (hν₁ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorOneSL • z) = -ν z / (τ z : ℂ)) :
    deriv (ν ∘ UpperHalfPlane.ofComplex) (SpecialPeriods.Triangle.centerOne : ℂ) = 0 := by
  have hzero := homogeneous_centerOne_eq_zero hν₁
  have hprod :
    ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorOneSL • z) * (τ z : ℂ) = (-1 : ℂ) * ν z := by
    intro z
    rw [hν₁, div_mul_cancel₀ _ (τ z).ne_zero, neg_one_mul]
  have hd :=
    homogeneous_fixed_derivative_identity hτ hν SpecialPeriods.Triangle.generatorOneSL
      SpecialPeriods.Triangle.centerOne (-1) SpecialPeriods.Triangle.generatorOne_fix hzero hprod
  rw [SpecialPeriods.Triangle.generatorOne_multiplier,
    (SpecialPeriods.tau_covariant_values hτc).1] at hd
  change
    (deriv (ν ∘ UpperHalfPlane.ofComplex) (SpecialPeriods.Triangle.centerOne : ℂ) *
          -SpecialPeriods.rho) *
        SpecialPeriods.rho =
      -1 * deriv (ν ∘ UpperHalfPlane.ofComplex) (SpecialPeriods.Triangle.centerOne : ℂ) at hd
  have hz :
    deriv (ν ∘ UpperHalfPlane.ofComplex) (SpecialPeriods.Triangle.centerOne : ℂ) *
        (SpecialPeriods.rho ^ 2 - 1) =
      0 := by linear_combination -hd
  apply (mul_eq_zero.mp hz).resolve_right
  intro hc
  rw [SpecialPeriods.rho_sq] at hc
  have hi := congrArg Complex.im hc
  simp only [Complex.sub_im, Complex.one_im, sub_zero, Complex.zero_im] at hi
  exact SpecialPeriods.rho_im_pos.ne' hi

private theorem SpecialPeriods.MuGenerator.exists_analytic_factor_of_order_le {ν f : ℂ → ℂ} {a : ℂ}
    {n : ℕ} (hν : AnalyticAt ℂ ν a) (hf : AnalyticAt ℂ f a)
    (hforder : analyticOrderAt f a = (n : ℕ∞)) (hνorder : (n : ℕ∞) ≤ analyticOrderAt ν a) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h a ∧ ν =ᶠ[𝓝 a] fun z => f z * h z := by
  obtain ⟨u, hu, hu0, hfu⟩ := hf.analyticOrderAt_eq_natCast.mp hforder
  obtain ⟨v, hv, hνv⟩ := (natCast_le_analyticOrderAt hν).mp hνorder
  refine ⟨fun z => v z / u z, hv.div hu hu0, ?_⟩
  filter_upwards [hfu, hνv, hu.continuousAt.eventually_ne hu0] with z hfz hνz huz
  simp only [smul_eq_mul] at hfz hνz
  rw [hfz, hνz]
  field_simp

private theorem
    SpecialPeriods.MuGenerator.homogeneous_centerOne_order_ge_two {τ : ℍ → ℍ} {ν : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hτc : SpecialPeriods.TauCovariant τ)
    (hν : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ν)
    (hν₁ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorOneSL • z) = -ν z / (τ z : ℂ)) :
    (2 : ℕ∞) ≤
      analyticOrderAt (ν ∘ UpperHalfPlane.ofComplex) (SpecialPeriods.Triangle.centerOne : ℂ) := by
  rw [show (2 : ℕ∞) = (2 : ℕ) by rfl,
    natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (scalar_analyticAt hν _)]
  intro k hk
  have hk01 : k = 0 ∨ k = 1 := by omega
  rcases hk01 with rfl | rfl
  · simpa only [iteratedDeriv_zero, Function.comp_apply, UpperHalfPlane.ofComplex_apply] using
      homogeneous_centerOne_eq_zero hν₁
  · simpa only [iteratedDeriv_one] using homogeneous_centerOne_deriv_eq_zero hτ hτc hν hν₁

private theorem
    SpecialPeriods.MuGenerator.homogeneous_centerTwo_order_ge_one {τ : ℍ → ℍ} {ν : ℍ → ℂ}
    (hν : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ν)
    (hν₂ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorTwoSL • z) = ν z / (τ z : ℂ)) :
    (1 : ℕ∞) ≤
      analyticOrderAt (ν ∘ UpperHalfPlane.ofComplex) (SpecialPeriods.Triangle.centerTwo : ℂ) := by
  rw [show (1 : ℕ∞) = (1 : ℕ) by rfl,
    natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (scalar_analyticAt hν _)]
  intro k hk
  have hk0 : k = 0 := by omega
  subst k
  simpa only [iteratedDeriv_zero, Function.comp_apply, UpperHalfPlane.ofComplex_apply] using
    homogeneous_centerTwo_eq_zero hν₂

private theorem SpecialPeriods.MuGenerator.exists_division_at_centerOne {τ : ℍ → ℍ} {ν f : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hτc : SpecialPeriods.TauCovariant τ)
    (hν : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ν)
    (hν₁ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorOneSL • z) = -ν z / (τ z : ℂ))
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hforder :
      analyticOrderAt (f ∘ UpperHalfPlane.ofComplex) (SpecialPeriods.Triangle.centerOne : ℂ) =
        2) :
    ∃ h : ℂ → ℂ,
      AnalyticAt ℂ h (SpecialPeriods.Triangle.centerOne : ℂ) ∧
        (ν ∘ UpperHalfPlane.ofComplex) =ᶠ[𝓝 (SpecialPeriods.Triangle.centerOne : ℂ)] fun z =>
          (f ∘ UpperHalfPlane.ofComplex) z * h z :=
  exists_analytic_factor_of_order_le (scalar_analyticAt hν _) (scalar_analyticAt hf _) (n := 2)
    hforder (homogeneous_centerOne_order_ge_two hτ hτc hν hν₁)

private theorem SpecialPeriods.MuGenerator.exists_division_at_centerTwo {τ : ℍ → ℍ} {ν f : ℍ → ℂ}
    (hν : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ν)
    (hν₂ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorTwoSL • z) = ν z / (τ z : ℂ))
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hforder :
      analyticOrderAt (f ∘ UpperHalfPlane.ofComplex) (SpecialPeriods.Triangle.centerTwo : ℂ) =
        1) :
    ∃ h : ℂ → ℂ,
      AnalyticAt ℂ h (SpecialPeriods.Triangle.centerTwo : ℂ) ∧
        (ν ∘ UpperHalfPlane.ofComplex) =ᶠ[𝓝 (SpecialPeriods.Triangle.centerTwo : ℂ)] fun z =>
          (f ∘ UpperHalfPlane.ofComplex) z * h z :=
  exists_analytic_factor_of_order_le (scalar_analyticAt hν _) (scalar_analyticAt hf _) (n := 1)
    hforder (homogeneous_centerTwo_order_ge_one hν hν₂)

private def SpecialPeriods.MuGenerator.Homogeneous (τ : ℍ → ℍ) (F : ℍ → ℂ) : Prop :=
  (∀ z, F (SpecialPeriods.Triangle.generatorOneSL • z) = -F z / (τ z : ℂ)) ∧
    (∀ z, F (SpecialPeriods.Triangle.generatorTwoSL • z) = F z / (τ z : ℂ))

private theorem SpecialPeriods.MuGenerator.Root.generator_eq_zero_iff_normalized_source {τ : ℍ → ℍ}
    (r : SpecialPeriods.MuGenerator.Root τ) {π : ℍ → ℂ}
    (hJ : ∀ z, SpecialPeriods.modularJ (τ z) = 1728 * π z) (z : ℍ) :
    r.generator z = 0 ↔ π z = 0 ∨ π z = 1 := by
  rw [r.generator_eq_zero_iff_modularJ, hJ z]
  have h1728 : (1728 : ℂ) ≠ 0 := by norm_num
  constructor
  · rintro (h | h)
    · exact Or.inl ((mul_eq_zero.mp h).resolve_left h1728)
    · right
      apply mul_left_cancel₀ h1728
      simpa only [mul_one] using h
  · rintro (h | h)
    · left
      rw [h, MulZeroClass.mul_zero]
    · right
      rw [h, mul_one]

private theorem SpecialPeriods.MuGenerator.Root.generator_homogeneous {τ : ℍ → ℍ}
    (r : SpecialPeriods.MuGenerator.Root τ) (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ)
    (hc : SpecialPeriods.TauCovariant τ)
    (ho₂ :
      analyticOrderAt (fun z : ℂ => (τ (UpperHalfPlane.ofComplex z) : ℂ) - Complex.I)
          (SpecialPeriods.Triangle.centerTwo : ℂ) =
        2) :
    SpecialPeriods.MuGenerator.Homogeneous τ r.generator :=
  ⟨r.generator_generatorOne hτ hc,
    r.generator_generatorTwo hτ hc (r.order_centerTwo_of_tau_order hτ hc ho₂)⟩

private theorem SpecialPeriods.MuGenerator.exists_homogeneous_generator {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hc : SpecialPeriods.TauCovariant τ)
    (heven : FiniteEvenZeros τ)
    (ho₁ :
      analyticOrderAt (fun z : ℂ => (τ (UpperHalfPlane.ofComplex z) : ℂ) - SpecialPeriods.rho)
          (SpecialPeriods.Triangle.centerOne : ℂ) =
        1)
    (ho₂ :
      analyticOrderAt (fun z : ℂ => (τ (UpperHalfPlane.ofComplex z) : ℂ) - Complex.I)
          (SpecialPeriods.Triangle.centerTwo : ℂ) =
        2) :
    ∃ F : ℍ → ℂ,
      (∃ r : Root τ, F = r.generator) ∧
        ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F ∧
          Homogeneous τ F ∧
            (∀ z,
                F z = 0 ↔
                  SpecialPeriods.modularJ (τ z) = 0 ∨ SpecialPeriods.modularJ (τ z) = 1728) ∧
              analyticOrderAt (F ∘ UpperHalfPlane.ofComplex)
                    (SpecialPeriods.Triangle.centerOne : ℂ) =
                  2 ∧
                analyticOrderAt (F ∘ UpperHalfPlane.ofComplex)
                    (SpecialPeriods.Triangle.centerTwo : ℂ) =
                  1 := by
  let r := root τ (hτ.mdifferentiable (by simp)) heven
  exact
    ⟨r.generator, ⟨r, rfl⟩, r.generator_holomorphic hτ, r.generator_homogeneous hτ hc ho₂,
      r.generator_eq_zero_iff_modularJ, r.generator_order_centerOne_of_tau_order hτ hc ho₁,
      r.generator_order_centerTwo_of_tau_order hτ hc ho₂⟩

private theorem
    SpecialPeriods.MuGenerator.exists_homogeneous_generator_of_modular_equation {τ : ℍ → ℍ}
    {J : ℍ → ℂ} (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hc : SpecialPeriods.TauCovariant τ)
    (hJ : ∀ a : ℍ, SpecialPeriods.modularJ (τ a) = J a)
    (hzero : ∀ a : ℍ, J a = 0 → analyticOrderAt (J ∘ UpperHalfPlane.ofComplex) (a : ℂ) = 3)
    (h1728 :
      ∀ a : ℍ,
        J a = 1728 →
          analyticOrderAt (fun z : ℂ => J (UpperHalfPlane.ofComplex z) - 1728) (a : ℂ) = 4) :
    ∃ F : ℍ → ℂ,
      (∃ r : Root τ, F = r.generator) ∧
        ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F ∧
          Homogeneous τ F ∧
            (∀ z, F z = 0 ↔ J z = 0 ∨ J z = 1728) ∧
              analyticOrderAt (F ∘ UpperHalfPlane.ofComplex)
                    (SpecialPeriods.Triangle.centerOne : ℂ) =
                  2 ∧
                analyticOrderAt (F ∘ UpperHalfPlane.ofComplex)
                    (SpecialPeriods.Triangle.centerTwo : ℂ) =
                  1 := by
  have hτd := hτ.mdifferentiable (by simp)
  have heven : FiniteEvenZeros τ :=
    finiteEvenZeros_of_modular_equation hτd hJ
      (fun a ha => ⟨1, by simpa only [Nat.mul_one, Nat.cast_ofNat] using h1728 a ha⟩)
  have hJ₁ : J SpecialPeriods.Triangle.centerOne = 0 := by
    rw [← hJ, (SpecialPeriods.tau_covariant_values hc).1, SpecialPeriods.modularJ_rhoPoint]
  have hJ₂ : J SpecialPeriods.Triangle.centerTwo = 1728 := by
    rw [← hJ, (SpecialPeriods.tau_covariant_values hc).2, SpecialPeriods.modularJ_I]
  have ho₁ :=
    SpecialPeriods.ModularGermLift.native_modularJ_lift_order_of_zero hτd hJ (a :=
      SpecialPeriods.Triangle.centerOne) (n := 1) hJ₁
      (by
        simpa only [Nat.mul_one, Nat.cast_ofNat] using
          hzero SpecialPeriods.Triangle.centerOne hJ₁)
  rw [(SpecialPeriods.tau_covariant_values hc).1, SpecialPeriods.coe_rhoPoint] at ho₁
  have ho₂ :=
    SpecialPeriods.ModularGermLift.native_modularJ_lift_order_of_1728 hτd hJ (a :=
      SpecialPeriods.Triangle.centerTwo) (n := 2) hJ₂
      (by simpa using h1728 SpecialPeriods.Triangle.centerTwo hJ₂)
  rw [(SpecialPeriods.tau_covariant_values hc).2, UpperHalfPlane.coe_I] at ho₂
  obtain ⟨F, hFroot, hF, hFc, hFzero, hF₁, hF₂⟩ :=
    exists_homogeneous_generator hτ hc heven ho₁ ho₂
  exact ⟨F, hFroot, hF, hFc, fun z => by rw [hFzero z, hJ z], hF₁, hF₂⟩

private def
    SpecialPeriods.MuTorsor.AffineCocycle.linearPart (c : SpecialPeriods.MuTorsor.AffineCocycle) :
    SpecialPeriods.MuTorsor.AffineCocycle
    where
  scale := c.scale
  shift _ _ := 0
  scale_one := c.scale_one
  shift_one _ := rfl
  scale_mul := c.scale_mul
  shift_mul _ _ _ := by simp
  scale_holomorphic := c.scale_holomorphic
  shift_holomorphic _ := contMDiff_const

@[simp]
private theorem SpecialPeriods.MuTorsor.AffineCocycle.linearPart_fibreMap
    (c : SpecialPeriods.MuTorsor.AffineCocycle) (g : SpecialPeriods.TriangleGroup) (z : ℍ)
    (u : ℂ) : c.linearPart.fibreMap g z u = (c.scale g z : ℂ) * u := by exact add_zero _

private theorem SpecialPeriods.MuTorsor.homogeneous_scale_law {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) {F : ℍ → ℂ}
    (hF : SpecialPeriods.MuGenerator.Homogeneous τ F) (g : SpecialPeriods.TriangleGroup) (z : ℍ) :
    F (SpecialPeriods.triangleGeometricRepresentation g z) =
      ((cocycle hτ hτa).scale g z : ℂ) * F z := by
  let K := (cocycle hτ hτa).linearPart.sectionStabilizer F
  have h₁ : SpecialPeriods.triangleGenerator₁ ∈ K := by
    intro w
    rw [SpecialPeriods.triangleGeometricRepresentation_generator₁_apply,
      AffineCocycle.linearPart_fibreMap, cocycle_scale_generator₁_val, hF.1 w]
    ring
  have h₂ : SpecialPeriods.triangleGenerator₂ ∈ K := by
    intro w
    rw [SpecialPeriods.triangleGeometricRepresentation_generator₂_apply,
      AffineCocycle.linearPart_fibreMap, cocycle_scale_generator₂_val, hF.2 w]
    ring
  have hle :
    Subgroup.closure
        ({ SpecialPeriods.triangleGenerator₁, SpecialPeriods.triangleGenerator₂ } :
          Set SpecialPeriods.TriangleGroup) ≤
      K :=
    (Subgroup.closure_le _).mpr
      (by
        intro x hx
        rcases hx with rfl | rfl
        · exact h₁
        · exact h₂)
  rw [SpecialPeriods.triangle_generators_generate] at hle
  have hz := hle (Subgroup.mem_top g) z
  simpa only [AffineCocycle.linearPart_fibreMap] using hz

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous SpecialPeriods.triangleOrbitChartedSpace in
private def SpecialPeriods.MuTorsor.descentDomain (V : TopologicalSpace.Opens ℍ) :
    TopologicalSpace.Opens SpecialPeriods.TriangleOrbitSpace :=
  LocalOrbitQuotient.imageOpen (G := SpecialPeriods.TriangleGroup) V

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous SpecialPeriods.triangleOrbitChartedSpace in
private theorem
    SpecialPeriods.MuTorsor.project_mem_descentDomain (V : TopologicalSpace.Opens ℍ) {z : ℍ}
    (hz : z ∈ V) : SpecialPeriods.triangleOrbitProjection z ∈ descentDomain V :=
  ⟨z, hz, rfl⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous SpecialPeriods.triangleOrbitChartedSpace in
private def SpecialPeriods.MuTorsor.descentProjection (V : TopologicalSpace.Opens ℍ) :
    V → descentDomain V :=
  LocalOrbitQuotient.imageProjection (G := SpecialPeriods.TriangleGroup) V

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous SpecialPeriods.triangleOrbitChartedSpace in
private theorem SpecialPeriods.MuTorsor.descentProjection_isOpenQuotientMap
    (V : TopologicalSpace.Opens ℍ) : IsOpenQuotientMap (descentProjection V) :=
  LocalOrbitQuotient.imageProjection_isOpenQuotientMap V

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous SpecialPeriods.triangleOrbitChartedSpace in
private def
    SpecialPeriods.MuTorsor.orbitRepresentative (q : SpecialPeriods.TriangleOrbitSpace) : ℍ :=
  (SpecialPeriods.triangleOrbitProjection_surjective q).choose

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous SpecialPeriods.triangleOrbitChartedSpace in
@[simp]
private theorem SpecialPeriods.MuTorsor.project_orbitRepresentative
    (q : SpecialPeriods.TriangleOrbitSpace) :
    SpecialPeriods.triangleOrbitProjection (orbitRepresentative q) = q :=
  (SpecialPeriods.triangleOrbitProjection_surjective q).choose_spec

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous SpecialPeriods.triangleOrbitChartedSpace in
private def SpecialPeriods.MuTorsor.descend (V : TopologicalSpace.Opens ℍ) (f : ℍ → ℂ)
    (q : SpecialPeriods.TriangleOrbitSpace) : ℂ := by
  classical exact if orbitRepresentative q ∈ V then f (orbitRepresentative q) else 0

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous SpecialPeriods.triangleOrbitChartedSpace in
private theorem SpecialPeriods.MuTorsor.project_mem_descentDomain_iff (V : TopologicalSpace.Opens ℍ)
    (hV :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z : ℍ, SpecialPeriods.triangleGeometricRepresentation g z ∈ V ↔ z ∈ V)
    (z : ℍ) : SpecialPeriods.triangleOrbitProjection z ∈ descentDomain V ↔ z ∈ V := by
  constructor
  · rintro ⟨w, hw, h⟩
    obtain ⟨g, hg⟩ := (SpecialPeriods.triangleOrbitProjection_eq_iff w z).mp h
    exact (hV g z).mp (hg ▸ hw)
  · exact project_mem_descentDomain V

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous SpecialPeriods.triangleOrbitChartedSpace in
private theorem SpecialPeriods.MuTorsor.orbitRepresentative_mem_iff (V : TopologicalSpace.Opens ℍ)
    (hV :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z : ℍ, SpecialPeriods.triangleGeometricRepresentation g z ∈ V ↔ z ∈ V)
    (q : SpecialPeriods.TriangleOrbitSpace) : orbitRepresentative q ∈ V ↔ q ∈ descentDomain V := by
  rw [← project_mem_descentDomain_iff V hV, project_orbitRepresentative]

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous SpecialPeriods.triangleOrbitChartedSpace in
private theorem SpecialPeriods.MuTorsor.descend_project (V : TopologicalSpace.Opens ℍ) (f : ℍ → ℂ)
    (hV :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z : ℍ, SpecialPeriods.triangleGeometricRepresentation g z ∈ V ↔ z ∈ V)
    (hInv :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z ∈ V, f (SpecialPeriods.triangleGeometricRepresentation g z) = f z)
    {z : ℍ} (hz : z ∈ V) : descend V f (SpecialPeriods.triangleOrbitProjection z) = f z := by
  have hr : orbitRepresentative (SpecialPeriods.triangleOrbitProjection z) ∈ V :=
    (orbitRepresentative_mem_iff V hV _).mpr (project_mem_descentDomain V hz)
  obtain ⟨g, hg⟩ :=
    (SpecialPeriods.triangleOrbitProjection_eq_iff
          (orbitRepresentative (SpecialPeriods.triangleOrbitProjection z)) z).mp
      (project_orbitRepresentative (SpecialPeriods.triangleOrbitProjection z))
  simp only [descend, ite_eq_left hr]
  rw [← hg]
  exact hInv g z hz

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous SpecialPeriods.triangleOrbitChartedSpace in
private theorem
    SpecialPeriods.MuTorsor.descend_continuousOn (V : TopologicalSpace.Opens ℍ) (f : ℍ → ℂ)
    (hV :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z : ℍ, SpecialPeriods.triangleGeometricRepresentation g z ∈ V ↔ z ∈ V)
    (hInv :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z ∈ V, f (SpecialPeriods.triangleGeometricRepresentation g z) = f z)
    (hf : ContinuousOn f V) : ContinuousOn (descend V f) (descentDomain V) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply (descentProjection_isOpenQuotientMap V).isQuotientMap.continuous_iff.mpr
  have he : (fun q : descentDomain V => descend V f q) ∘ descentProjection V = fun z : V => f z :=
    by
    funext z
    exact descend_project V f hV hInv z.property
  change Continuous ((fun q : descentDomain V => descend V f q) ∘ descentProjection V)
  rw [he]
  exact hf.domRestrict

attribute [local instance] SpecialPeriods.triangleGeometricAction
    SpecialPeriods.triangleGeometricAction_continuous SpecialPeriods.triangleOrbitChartedSpace in
private theorem
    SpecialPeriods.MuTorsor.descend_contMDiffAt_of_not_elliptic (V : TopologicalSpace.Opens ℍ)
    (f : ℍ → ℂ)
    (hV :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z : ℍ, SpecialPeriods.triangleGeometricRepresentation g z ∈ V ↔ z ∈ V)
    (hInv :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z ∈ V, f (SpecialPeriods.triangleGeometricRepresentation g z) = f z)
    (hf : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω f V) {q : SpecialPeriods.TriangleOrbitSpace}
    (hq : q ∈ descentDomain V) (h₁ : q ≠ SpecialPeriods.triangleOrbitCenterOne)
    (h₂ : q ≠ SpecialPeriods.triangleOrbitCenterTwo) : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (descend V f) q := by
  obtain ⟨z, hz, rfl⟩ := hq
  have hp := SpecialPeriods.triangleOrbitProjection_isLocalDiffeomorphAt_of_not_elliptic h₁ h₂
  have hcomp : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (descend V f ∘ SpecialPeriods.triangleOrbitProjection) z :=
    by
    apply (hf.contMDiffAt (V.isOpen.mem_nhds hz)).congr_of_eventuallyEq
    filter_upwards [V.isOpen.mem_nhds hz] with w hw
    exact descend_project V f hV hInv hw
  have h :=
    hcomp.comp_of_eq hp.localInverse_contMDiffAt
      (hp.localInverse_left_inv hp.localInverse_mem_target)
  apply h.congr_of_eventuallyEq
  filter_upwards [hp.localInverse_eventuallyEq_right] with r hr
  change descend V f r = descend V f (SpecialPeriods.triangleOrbitProjection (hp.localInverse r))
  rw [show SpecialPeriods.triangleOrbitProjection (hp.localInverse r) = r from hr]

private theorem
    SpecialPeriods.MuTorsor.contMDiffAt_of_continuousAt_of_eventually_punctured {M : Type*}
    [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M] {f : M → ℂ} {x : M}
    (hc : ContinuousAt f x) (hd : ∀ᶠ y in 𝓝[≠] x, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f y) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x := by
  let e := chartAt ℂ x
  have hx : x ∈ e.source := mem_chart_source ℂ x
  have hxe : e x ∈ e.target := e.map_source hx
  have hc' : ContinuousAt (f ∘ e.symm) (e x) :=
    (e.symm.continuousAt_iff_continuousAt_comp_right hx).mp hc
  have hp : Filter.Tendsto e.symm (𝓝[≠] e x) (𝓝[≠] x) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨(e.tendsto_symm hx).mono_left nhdsWithin_le_nhds, ?_⟩
    simpa only [e.left_inv hx, Set.mem_compl_iff, Set.mem_singleton_iff] using
      e.symm.eventually_ne_nhdsWithin hxe
  have hd' : ∀ᶠ z in 𝓝[≠] e x, DifferentiableAt ℂ (f ∘ e.symm) z := by
    filter_upwards [hp.eventually hd,
      eventually_nhdsWithin_of_eventually_nhds (e.open_target.eventually_mem hxe)] with z hz hzt
    have he : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω e.symm z :=
      contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) (n := ω) x) hzt
    exact (hz.comp z he).contDiffAt.differentiableAt (by simp)
  have ha := Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hd' hc'
  have he : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω e x :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) (n := ω) x) hx
  apply (ha.contDiffAt.contMDiffAt.comp x he).congr_of_eventuallyEq
  filter_upwards [e.eventually_left_inverse hx] with y hy
  exact (congrArg f hy).symm

private theorem SpecialPeriods.MuTorsor.contMDiffOn_of_continuousOn_of_finite {M : Type*}
    [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M] {f : M → ℂ} [T1Space M]
    {U s : Set M} (hU : IsOpen U) (hs : s.Finite) (hc : ContinuousOn f U)
    (hd : ∀ x ∈ U, x ∉ s → ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x) : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω f U := by
  intro x hx
  apply ContMDiffAt.contMDiffWithinAt
  apply
    contMDiffAt_of_continuousAt_of_eventually_punctured ((hc x hx).continuousAt (hU.mem_nhds hx))
  have hclosed : IsClosed (s \ { x }) := (hs.subset Set.sdiff_subset).isClosed
  have havoid : (s \ { x })ᶜ ∈ 𝓝 x := hclosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hx), nhdsWithin_le_nhds havoid,
    self_mem_nhdsWithin] with y hy hyavoid hyne
  apply hd y hy
  intro hys
  exact hyavoid ⟨hys, hyne⟩

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
private theorem SpecialPeriods.MuTorsor.instIsManifold1 :
    IsManifold 𝓘(ℂ) ω SpecialPeriods.TriangleOrbitSpace :=
  SpecialPeriods.triangleOrbit_isManifold

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
attribute [local instance] SpecialPeriods.MuTorsor.instIsManifold1 in
private theorem
    SpecialPeriods.MuTorsor.descend_holomorphic (V : TopologicalSpace.Opens ℍ) (f : ℍ → ℂ)
    (hV :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z : ℍ, SpecialPeriods.triangleGeometricRepresentation g z ∈ V ↔ z ∈ V)
    (hInv :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z ∈ V, f (SpecialPeriods.triangleGeometricRepresentation g z) = f z)
    (hf : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω f V) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (descend V f) (descentDomain V) := by
  apply
    contMDiffOn_of_continuousOn_of_finite (s :=
      { SpecialPeriods.triangleOrbitCenterOne, SpecialPeriods.triangleOrbitCenterTwo })
      (descentDomain V).isOpen
      ((Set.finite_singleton SpecialPeriods.triangleOrbitCenterTwo).insert
        SpecialPeriods.triangleOrbitCenterOne)
      (descend_continuousOn V f hV hInv hf.continuousOn)
  intro q hq hnot
  have h₁ : q ≠ SpecialPeriods.triangleOrbitCenterOne := fun h => hnot (by simp [h])
  have h₂ : q ≠ SpecialPeriods.triangleOrbitCenterTwo := fun h => hnot (by simp [h])
  exact descend_contMDiffAt_of_not_elliptic V f hV hInv hf hq h₁ h₂

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
attribute [local instance] SpecialPeriods.MuTorsor.instIsManifold1 in
private theorem
    SpecialPeriods.MuTorsor.descend_holomorphicAt (V : TopologicalSpace.Opens ℍ) (f : ℍ → ℂ)
    (hV :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z : ℍ, SpecialPeriods.triangleGeometricRepresentation g z ∈ V ↔ z ∈ V)
    (hInv :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z ∈ V, f (SpecialPeriods.triangleGeometricRepresentation g z) = f z)
    (hf : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω f V) {q : SpecialPeriods.TriangleOrbitSpace}
    (hq : q ∈ descentDomain V) : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (descend V f) q :=
  (descend_holomorphic V f hV hInv hf).contMDiffAt ((descentDomain V).isOpen.mem_nhds hq)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.BetaTorsor.finiteDescentDomain
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (V : TopologicalSpace.Opens ℍ) : TopologicalSpace.Opens ℂ :=
  ⟨finiteOrbitInverse π hπ ⁻¹'
      (SpecialPeriods.MuTorsor.descentDomain V : Set SpecialPeriods.TriangleOrbitSpace),
    (SpecialPeriods.MuTorsor.descentDomain V).isOpen.preimage
      (finiteOrbitInverse_holomorphic π hπ).continuous⟩

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.BetaTorsor.finiteDescent
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (V : TopologicalSpace.Opens ℍ) (f : ℍ → ℂ) : ℂ → ℂ :=
  SpecialPeriods.MuTorsor.descend V f ∘ finiteOrbitInverse π hπ

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.BetaTorsor.finiteDescentDomain_projection
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (V : TopologicalSpace.Opens ℍ)
    (hV :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z : ℍ, SpecialPeriods.triangleGeometricRepresentation g z ∈ V ↔ z ∈ V)
    (z : ℍ) : finiteProjection π z ∈ finiteDescentDomain π hπ V ↔ z ∈ V := by
  change
    finiteOrbitInverse π hπ (finiteOrbitCoordinate π (SpecialPeriods.triangleOrbitProjection z)) ∈
        SpecialPeriods.MuTorsor.descentDomain V ↔
      z ∈ V
  rw [finiteOrbitInverse_coordinate]
  exact SpecialPeriods.MuTorsor.project_mem_descentDomain_iff V hV z

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.BetaTorsor.finiteDescent_projection
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (V : TopologicalSpace.Opens ℍ) (f : ℍ → ℂ)
    (hV :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z : ℍ, SpecialPeriods.triangleGeometricRepresentation g z ∈ V ↔ z ∈ V)
    (hInv :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z ∈ V, f (SpecialPeriods.triangleGeometricRepresentation g z) = f z)
    {z : ℍ} (hz : z ∈ V) : finiteDescent π hπ V f (finiteProjection π z) = f z := by
  simp only [finiteDescent, finiteProjection, Function.comp_apply, finiteOrbitInverse_coordinate]
  exact SpecialPeriods.MuTorsor.descend_project V f hV hInv hz

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.BetaTorsor.finiteDescent_analytic
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (V : TopologicalSpace.Opens ℍ) (f : ℍ → ℂ)
    (hV :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z : ℍ, SpecialPeriods.triangleGeometricRepresentation g z ∈ V ↔ z ∈ V)
    (hInv :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z ∈ V, f (SpecialPeriods.triangleGeometricRepresentation g z) = f z)
    (hf : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω f V) :
    AnalyticOnNhd ℂ (finiteDescent π hπ V f) (finiteDescentDomain π hπ V) :=
  analyticOnNhd_finite_pullback π hπ (SpecialPeriods.MuTorsor.descentDomain V)
    (SpecialPeriods.MuTorsor.descend_holomorphic V f hV hInv hf)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.MuTorsor.overlap (i j : Cover.Index) : TopologicalSpace.Opens ℍ :=
  ⟨(Cover.patch i).saturation ∩ (Cover.patch j).saturation,
    (Cover.patch i).saturation_isOpen.inter (Cover.patch j).saturation_isOpen⟩

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.overlap_invariant (i j : Cover.Index)
    (g : SpecialPeriods.TriangleGroup) (z : ℍ) :
    SpecialPeriods.triangleGeometricRepresentation g z ∈ overlap i j ↔ z ∈ overlap i j := by
  change (_ ∈ (Cover.patch i).saturation ∧ _ ∈ (Cover.patch j).saturation) ↔ _
  rw [(Cover.patch i).saturation_invariant, (Cover.patch j).saturation_invariant]
  rfl

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private def SpecialPeriods.MuTorsor.overlapQuotient {τ : ℍ → ℍ} (hτ : SpecialPeriods.TauCovariant τ)
    (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (F : ℍ → ℂ) (i j : Cover.Index) (z : ℍ) : ℂ :=
  (localSection hτ hτa i z - localSection hτ hτa j z) / F z

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.overlapQuotient_invariant {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (F : ℍ → ℂ)
    (hFc : SpecialPeriods.MuGenerator.Homogeneous τ F) (i j : Cover.Index)
    (g : SpecialPeriods.TriangleGroup) (z : ℍ) (hz : z ∈ overlap i j) :
    overlapQuotient hτ hτa F i j (SpecialPeriods.triangleGeometricRepresentation g z) =
      overlapQuotient hτ hτa F i j z := by
  unfold overlapQuotient
  rw [localSection_equivariant hτ hτa i g z hz.1, localSection_equivariant hτ hτa j g z hz.2,
    AffineCocycle.fibreMap_sub, homogeneous_scale_law hτ hτa hFc]
  exact mul_div_mul_left _ _ (cocycle hτ hτa |>.scale g z).ne_zero

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.overlap_generator_ne_zero (F : ℍ → ℂ)
    (hFzero :
      ∀ z,
        F z = 0 ↔
          SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterOne ∨
            SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterTwo)
    {i j : Cover.Index} (hij : i ≠ j) {z : ℍ} (hz : z ∈ overlap i j) : F z ≠ 0 := by
  have hr := Cover.distinct_saturation_overlap_subset_regularLocus hij hz
  have hq :=
    (SpecialPeriods.triangleOrbitRegularDomain_mem_iff _).mp
      ((SpecialPeriods.triangleOrbitProjection_mem_regularDomain_iff z).mpr hr)
  intro hf
  rcases (hFzero z).mp hf with h | h
  · exact hq.1 h
  · exact hq.2 h

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.overlapQuotient_holomorphic {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (F : ℍ → ℂ)
    (hFzero :
      ∀ z,
        F z = 0 ↔
          SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterOne ∨
            SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterTwo)
    (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) (i j : Cover.Index) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (overlapQuotient hτ hτa F i j) (overlap i j) := by
  by_cases hij : i = j
  · subst j
    have he : overlapQuotient hτ hτa F i i = fun _ => 0 := by
      funext z
      simp only [overlapQuotient, sub_self, zero_div]
    rw [he]
    exact contMDiffOn_const
  · have h₁ :=
      (localSection_holomorphic hτ hτa i).mono
        (show (overlap i j : Set ℍ) ⊆ (Cover.patch i).saturation from Set.inter_subset_left)
    have h₂ :=
      (localSection_holomorphic hτ hτa j).mono
        (show (overlap i j : Set ℍ) ⊆ (Cover.patch j).saturation from Set.inter_subset_right)
    exact (h₁.sub h₂).div₀ hF.contMDiffOn (fun z hz => overlap_generator_ne_zero F hFzero hij hz)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.localSection_eq_at_generator_zero {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (F : ℍ → ℂ)
    (hFzero :
      ∀ z,
        F z = 0 ↔
          SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterOne ∨
            SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterTwo)
    (i j : Cover.Index) (z : ℍ) (hi : z ∈ (Cover.patch i).saturation)
    (hj : z ∈ (Cover.patch j).saturation) (hz : F z = 0) :
    localSection hτ hτa i z = localSection hτ hτa j z := by
  have hij : i = j := by
    by_contra h
    exact overlap_generator_ne_zero F hFzero h ⟨hi, hj⟩ hz
  rw [hij]

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.finiteProjection_mem_patch
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (i : Cover.Index) (z : ℍ) :
    SpecialPeriods.BetaTorsor.finiteProjection π z ∈ Cover.finitePatch π i ↔
      z ∈ (Cover.patch i).saturation :=
  (SpecialPeriods.BetaTorsor.finiteProjection_mem_pullback π hπ (Cover.compactPatch i) z).trans
    (Cover.compactifiedProjection_mem_compactPatch i z)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.finiteProjection_preimage_patch
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (i : Cover.Index) :
    SpecialPeriods.BetaTorsor.finiteProjection π ⁻¹' (Cover.finitePatch π i : Set ℂ) =
      (Cover.patch i).saturation := by
  ext z
  exact finiteProjection_mem_patch π hπ i z

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.finiteDescentDomain_overlap
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (i j : Cover.Index) :
    (SpecialPeriods.BetaTorsor.finiteDescentDomain π hπ (overlap i j) : Set ℂ) =
      (Cover.finitePatch π i : Set ℂ) ∩ Cover.finitePatch π j := by
  ext w
  obtain ⟨z, rfl⟩ := SpecialPeriods.BetaTorsor.finiteProjection_surjective π hπ w
  change
    SpecialPeriods.BetaTorsor.finiteProjection π z ∈
        SpecialPeriods.BetaTorsor.finiteDescentDomain π hπ (overlap i j) ↔
      SpecialPeriods.BetaTorsor.finiteProjection π z ∈ Cover.finitePatch π i ∧
        SpecialPeriods.BetaTorsor.finiteProjection π z ∈ Cover.finitePatch π j
  rw [SpecialPeriods.BetaTorsor.finiteDescentDomain_projection π hπ (overlap i j)
      (overlap_invariant i j)]
  rw [finiteProjection_mem_patch π hπ, finiteProjection_mem_patch π hπ]
  rfl

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private def
    SpecialPeriods.MuTorsor.descendedOverlap {τ : ℍ → ℍ} (hτ : SpecialPeriods.TauCovariant τ)
    (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (F : ℍ → ℂ)
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (i j : Cover.Index) : ℂ → ℂ :=
  SpecialPeriods.BetaTorsor.finiteDescent π hπ (overlap i j) (overlapQuotient hτ hτa F i j)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.descendedOverlap_projection {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (F : ℍ → ℂ)
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (hFc : SpecialPeriods.MuGenerator.Homogeneous τ F) (i j : Cover.Index) (z : ℍ)
    (hi : SpecialPeriods.BetaTorsor.finiteProjection π z ∈ Cover.finitePatch π i)
    (hj : SpecialPeriods.BetaTorsor.finiteProjection π z ∈ Cover.finitePatch π j) :
    descendedOverlap hτ hτa F π hπ i j (SpecialPeriods.BetaTorsor.finiteProjection π z) =
      (localSection hτ hτa i z - localSection hτ hτa j z) / F z := by
  exact
    SpecialPeriods.BetaTorsor.finiteDescent_projection π hπ (overlap i j)
      (overlapQuotient hτ hτa F i j) (overlap_invariant i j)
      (overlapQuotient_invariant hτ hτa F hFc i j)
      ⟨(finiteProjection_mem_patch π hπ i z).mp hi, (finiteProjection_mem_patch π hπ j z).mp hj⟩

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.descendedOverlap_analytic {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (F : ℍ → ℂ)
    (hFzero :
      ∀ z,
        F z = 0 ↔
          SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterOne ∨
            SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterTwo)
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) (hFc : SpecialPeriods.MuGenerator.Homogeneous τ F)
    (i j : Cover.Index) :
    AnalyticOnNhd ℂ (descendedOverlap hτ hτa F π hπ i j)
      ((Cover.finitePatch π i : Set ℂ) ∩ Cover.finitePatch π j) := by
  rw [← finiteDescentDomain_overlap π hπ]
  exact
    SpecialPeriods.BetaTorsor.finiteDescent_analytic π hπ (overlap i j)
      (overlapQuotient hτ hτa F i j) (overlap_invariant i j)
      (overlapQuotient_invariant hτ hτa F hFc i j)
      (overlapQuotient_holomorphic hτ hτa F hFzero hF i j)

private def HolomorphicCousin.partitionCochain {ι E H M F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ρ : SmoothPartitionOfUnity ι I M Set.univ) (h : ι → ι → M → F) (i : ι) (x : M) : F :=
  ∑ᶠ k, ρ k x • h i k x

private theorem
    HolomorphicCousin.mem_cover_of_mem_finsupport {ι E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] {U : ι → Set M} {ρ : SmoothPartitionOfUnity ι I M Set.univ}
    (hρ : ρ.IsSubordinate U) {x : M} {k : ι} (hk : k ∈ ρ.finsupport x) : x ∈ U k := by
  apply hρ k
  apply subset_tsupport
  simpa only [ρ.mem_finsupport, Function.mem_support] using hk

private theorem
    HolomorphicCousin.partitionCochain_contMDiffOn {ι E H M F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [NormedAddCommGroup F] [NormedSpace ℝ F] {U : ι → Set M}
    (hU : ∀ i, IsOpen (U i)) {ρ : SmoothPartitionOfUnity ι I M Set.univ} (hρ : ρ.IsSubordinate U)
    {h : ι → ι → M → F} (hh : ∀ i j, ContMDiffOn I 𝓘(ℝ, F) ∞ (h i j) (U i ∩ U j)) (i : ι) :
    ContMDiffOn I 𝓘(ℝ, F) ∞ (partitionCochain ρ h i) (U i) := by
  intro x hx
  apply ContMDiffAt.contMDiffWithinAt
  apply ρ.contMDiffAt_finsum
  intro k hk
  exact (hh i k).contMDiffAt ((hU i).inter (hU k) |>.mem_nhds ⟨hx, hρ k hk⟩)

private theorem HolomorphicCousin.partitionCochain_sub_eq {ι E H M F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] [NormedAddCommGroup F] [NormedSpace ℝ F] {U : ι → Set M}
    {ρ : SmoothPartitionOfUnity ι I M Set.univ} (hρ : ρ.IsSubordinate U) {h : ι → ι → M → F}
    (hc : ∀ i j k x, x ∈ U i → x ∈ U j → x ∈ U k → h i j x + h j k x = h i k x) (i j : ι) {x : M}
    (hi : x ∈ U i) (hj : x ∈ U j) :
    partitionCochain ρ h i x - partitionCochain ρ h j x = h i j x := by
  classical
  unfold partitionCochain
  rw [← ρ.sum_finsupport_smul_eq_finsum x (h i), ← ρ.sum_finsupport_smul_eq_finsum x (h j), ←
    Finset.sum_sub_distrib]
  calc
    (∑ k ∈ ρ.finsupport x, (ρ k x • h i k x - ρ k x • h j k x)) =
        ∑ k ∈ ρ.finsupport x, ρ k x • h i j x := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← smul_sub,
        sub_eq_iff_eq_add.mpr (hc i j k x hi hj (mem_cover_of_mem_finsupport hρ hk)).symm]
    _ = (∑ k ∈ ρ.finsupport x, ρ k x) • h i j x := (Finset.sum_smul ..).symm
    _ = h i j x := by rw [ρ.sum_finsupport x (Set.mem_univ x), one_smul]

private theorem HolomorphicCousin.partitionCochain_eq_zero_of_weights_single {ι E H M F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : ι → Set M} {ρ : SmoothPartitionOfUnity ι I M Set.univ} {h : ι → ι → M → F}
    (hc : ∀ i j k x, x ∈ U i → x ∈ U j → x ∈ U k → h i j x + h j k x = h i k x) (j : ι) {x : M}
    (hj : x ∈ U j) (hρ0 : ∀ k, k ≠ j → ρ k x = 0) : partitionCochain ρ h j x = 0 := by
  have hdiag : h j j x = 0 := add_eq_left.mp (hc j j j x hj hj hj)
  have hz : ∀ k, ρ k x • h j k x = 0 := by
    intro k
    by_cases hkj : k = j
    · subst k
      rw [hdiag, smul_zero]
    · rw [hρ0 k hkj, zero_smul]
  simp only [partitionCochain, hz, finsum_zero]

private theorem HolomorphicCousin.partitionCochain_eq_overlap_of_weights_single {ι E H M F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : ι → Set M} {ρ : SmoothPartitionOfUnity ι I M Set.univ} (hρ : ρ.IsSubordinate U)
    {h : ι → ι → M → F}
    (hc : ∀ i j k x, x ∈ U i → x ∈ U j → x ∈ U k → h i j x + h j k x = h i k x) (i j : ι) {x : M}
    (hi : x ∈ U i) (hj : x ∈ U j) (hρ0 : ∀ k, k ≠ j → ρ k x = 0) :
    partitionCochain ρ h i x = h i j x := by
  have he := partitionCochain_sub_eq hρ hc i j hi hj
  rwa [partitionCochain_eq_zero_of_weights_single hc j hj hρ0, sub_zero] at he

private theorem HolomorphicCousin.exists_normalized_smooth_cocycle_cochain {ι E H M F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] {U : ι → Set M}
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i) {h : ι → ι → M → F}
    (hh : ∀ i j, ContMDiffOn I 𝓘(ℝ, F) ∞ (h i j) (U i ∩ U j))
    (hc : ∀ i j k x, x ∈ U i → x ∈ U j → x ∈ U k → h i j x + h j k x = h i k x) (i₀ : ι)
    {K : Set M} (hK : IsClosed K) (hKU : K ⊆ U i₀) :
    ∃ (V : Set M) (s : ι → M → F),
      IsOpen V ∧
        K ⊆ V ∧
          V ⊆ U i₀ ∧
            (∀ i, ContMDiffOn I 𝓘(ℝ, F) ∞ (s i) (U i)) ∧
              (∀ i j x, x ∈ U i → x ∈ U j → s i x - s j x = h i j x) ∧
                Set.EqOn (s i₀) (fun _ => 0) V ∧ ∀ i, Set.EqOn (s i) (h i i₀) (U i ∩ V) := by
  obtain ⟨V, hVo, hKV, hVU, ρ, hρ, _, hρ0, _⟩ :=
    exists_smoothPartitionOfUnity_eq_one_near_closed I U hU
      (fun x _ => Set.mem_iUnion.mpr (hcover x)) i₀ hK hKU
  refine
    ⟨V, partitionCochain ρ h, hVo, hKV, hVU, partitionCochain_contMDiffOn hU hρ hh,
      fun i j _ hi hj => partitionCochain_sub_eq hρ hc i j hi hj, ?_, ?_⟩
  · intro x hx
    exact partitionCochain_eq_zero_of_weights_single hc i₀ (hVU hx) (fun k hk => hρ0 k hk x hx)
  · intro i x hx
    exact
      partitionCochain_eq_overlap_of_weights_single hρ hc i i₀ hx.1 (hVU hx.2)
        (fun k hk => hρ0 k hk x hx.2)

private def HolomorphicCousin.dbarLinear : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (1 / (2 : ℂ)) •
    (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ) + Complex.I • ContinuousLinearMap.apply ℝ ℂ Complex.I)

@[simp]
private theorem HolomorphicCousin.dbarLinear_apply (L : ℂ →L[ℝ] ℂ) :
    dbarLinear L = (L 1 + Complex.I * L Complex.I) / 2 := by
  simp only [dbarLinear, smul_apply, add_apply, ContinuousLinearMap.apply_apply, smul_eq_mul]
  ring

private def HolomorphicCousin.dbar (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I) / 2

private theorem HolomorphicCousin.dbar_eq_dbarLinear (f : ℂ → ℂ) (z : ℂ) :
    dbar f z = dbarLinear (fderiv ℝ f z) :=
  (dbarLinear_apply _).symm

private theorem HolomorphicCousin.dbarLinear_complex_smul (c : ℂ) (L : ℂ →L[ℝ] ℂ) :
    dbarLinear (c • L) = c * dbarLinear L := by
  simp only [dbarLinear_apply, smul_apply, smul_eq_mul]
  ring

private theorem HolomorphicCousin.dbar_eq_zero_iff (f : ℂ → ℂ) (z : ℂ) :
    dbar f z = 0 ↔ fderiv ℝ f z Complex.I = Complex.I * fderiv ℝ f z 1 := by
  constructor
  · intro h
    have hs : fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I = 0 := by
      simpa only [dbar, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false] using h
    have hm := congrArg (fun w : ℂ => -Complex.I * w) hs
    simp only [mul_add, neg_mul, ← mul_assoc, Complex.I_mul_I, neg_neg,
      MulZeroClass.mul_zero] at hm
    linear_combination hm
  · intro h
    rw [dbar, h, ← mul_assoc, Complex.I_mul_I, neg_one_mul, add_neg_cancel, zero_div]

private theorem HolomorphicCousin.differentiableAt_complex_iff_dbar {f : ℂ → ℂ} {z : ℂ} :
    DifferentiableAt ℂ f z ↔ DifferentiableAt ℝ f z ∧ dbar f z = 0 := by
  rw [differentiableAt_complex_iff_differentiableAt_real, dbar_eq_zero_iff]
  rfl

private theorem HolomorphicCousin.dbar_eq_zero_of_differentiableAt {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) : dbar f z = 0 :=
  (differentiableAt_complex_iff_dbar.mp hf).2

private theorem
    HolomorphicCousin.analyticOnNhd_of_dbar_eq_zero {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℝ f U) (hd : ∀ z ∈ U, dbar f z = 0) : AnalyticOnNhd ℂ f U := by
  apply (Complex.analyticOnNhd_iff_differentiableOn hU).mpr
  intro z hz
  exact
    ((differentiableAt_complex_iff_dbar).mpr
        ⟨(hf z hz).differentiableAt (hU.mem_nhds hz), hd z hz⟩).differentiableWithinAt

private theorem HolomorphicCousin.dbar_sub {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) : dbar (fun w => f w - g w) z = dbar f z - dbar g z := by
  simp only [dbar_eq_dbarLinear, fderiv_fun_sub hf hg, map_sub]

private theorem HolomorphicCousin.dbar_comp_const_sub {f : ℂ → ℂ} (a z : ℂ)
    (hf : DifferentiableAt ℝ f (a - z)) : dbar (fun w => f (a - w)) z = -dbar f (a - z) := by
  have hi : HasFDerivAt (fun w : ℂ => a - w) (-ContinuousLinearMap.id ℝ ℂ) z :=
    (hasFDerivAt_id z).const_sub a
  have he := (hf.hasFDerivAt.comp z hi).fderiv
  change fderiv ℝ (fun w => f (a - w)) z = _ at he
  simp only [dbar, he, ContinuousLinearMap.comp_apply, neg_apply, ContinuousLinearMap.id_apply,
    map_neg]
  ring

private theorem HolomorphicCousin.contDiffAt_dbar {f : ℂ → ℂ} {z : ℂ} (hf : ContDiffAt ℝ ∞ f z) :
    ContDiffAt ℝ ∞ (dbar f) z := by
  have he : dbar f = dbarLinear ∘ fderiv ℝ f := funext (dbar_eq_dbarLinear f)
  rw [he]
  exact dbarLinear.contDiff.contDiffAt.comp z (hf.fderiv_right (by simp))

private theorem HolomorphicCousin.dbar_eq_of_sub_differentiableAt {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z)
    (hfg : DifferentiableAt ℂ (fun w => f w - g w) z) : dbar f z = dbar g z := by
  have he := dbar_eq_zero_of_differentiableAt hfg
  rw [dbar_sub hf hg] at he
  exact sub_eq_zero.mp he

private structure HolomorphicCousin.LocalPotential (ι : Type*) where
  domain : ι → Set ℂ
  isOpen_domain : ∀ i, IsOpen (domain i)
  cover : ∀ z : ℂ, ∃ i, z ∈ domain i
  potential : ι → ℂ → ℂ
  smooth : ∀ i, ContDiffOn ℝ ∞ (potential i) (domain i)
  analytic_difference :
    ∀ i j, AnalyticOnNhd ℂ (fun z => potential i z - potential j z) (domain i ∩ domain j)

private def
    HolomorphicCousin.LocalPotential.indexAt {ι : Type*} (P : HolomorphicCousin.LocalPotential ι)
    (z : ℂ) : ι :=
  (P.cover z).choose

private theorem HolomorphicCousin.LocalPotential.mem_domain_indexAt {ι : Type*}
    (P : HolomorphicCousin.LocalPotential ι) (z : ℂ) : z ∈ P.domain (P.indexAt z) :=
  (P.cover z).choose_spec

private theorem HolomorphicCousin.LocalPotential.smoothAt {ι : Type*}
    (P : HolomorphicCousin.LocalPotential ι) {i : ι} {z : ℂ} (hz : z ∈ P.domain i) :
    ContDiffAt ℝ ∞ (P.potential i) z :=
  (P.smooth i z hz).contDiffAt ((P.isOpen_domain i).mem_nhds hz)

private def
    HolomorphicCousin.LocalPotential.forcing {ι : Type*} (P : HolomorphicCousin.LocalPotential ι)
    (z : ℂ) : ℂ :=
  HolomorphicCousin.dbar (P.potential (P.indexAt z)) z

private theorem HolomorphicCousin.LocalPotential.forcing_eq {ι : Type*}
    (P : HolomorphicCousin.LocalPotential ι) {i : ι} {z : ℂ} (hz : z ∈ P.domain i) :
    P.forcing z = HolomorphicCousin.dbar (P.potential i) z := by
  exact
    HolomorphicCousin.dbar_eq_of_sub_differentiableAt
      ((P.smoothAt (P.mem_domain_indexAt z)).differentiableAt (by simp))
      ((P.smoothAt hz).differentiableAt (by simp))
      (P.analytic_difference (P.indexAt z) i z ⟨P.mem_domain_indexAt z, hz⟩).differentiableAt

private theorem HolomorphicCousin.LocalPotential.forcing_eventuallyEq {ι : Type*}
    (P : HolomorphicCousin.LocalPotential ι) {i : ι} {z : ℂ} (hz : z ∈ P.domain i) :
    P.forcing =ᶠ[𝓝 z] HolomorphicCousin.dbar (P.potential i) := by
  filter_upwards [(P.isOpen_domain i).mem_nhds hz] with w hw
  exact P.forcing_eq hw

private theorem HolomorphicCousin.LocalPotential.forcing_contDiff {ι : Type*}
    (P : HolomorphicCousin.LocalPotential ι) : ContDiff ℝ ∞ P.forcing := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  exact
    (HolomorphicCousin.contDiffAt_dbar
          (P.smoothAt (P.mem_domain_indexAt z))).congr_of_eventuallyEq
      (P.forcing_eventuallyEq (P.mem_domain_indexAt z))

private theorem HolomorphicCousin.LocalPotential.forcing_eq_zero {ι : Type*}
    (P : HolomorphicCousin.LocalPotential ι) {i : ι} {z : ℂ} (hz : z ∈ P.domain i)
    (hs : DifferentiableAt ℂ (P.potential i) z) : P.forcing z = 0 := by
  rw [P.forcing_eq hz]
  exact HolomorphicCousin.dbar_eq_zero_of_differentiableAt hs

private theorem HolomorphicCousin.LocalPotential.corrected_difference {ι : Type*}
    (P : HolomorphicCousin.LocalPotential ι) (u : ℂ → ℂ) (i j : ι) (z : ℂ) :
    (P.potential i z - u z) - (P.potential j z - u z) = P.potential i z - P.potential j z := by
  ring

private theorem HolomorphicCousin.LocalPotential.corrected_analytic {ι : Type*}
    (P : HolomorphicCousin.LocalPotential ι) {u : ℂ → ℂ} (hu : Differentiable ℝ u)
    (hsolve : ∀ z, HolomorphicCousin.dbar u z = P.forcing z) (i : ι) :
    AnalyticOnNhd ℂ (fun z => P.potential i z - u z) (P.domain i) := by
  apply HolomorphicCousin.analyticOnNhd_of_dbar_eq_zero (P.isOpen_domain i)
  · exact ((P.smooth i).differentiableOn (by simp)).sub hu.differentiableOn
  · intro z hz
    rw [HolomorphicCousin.dbar_sub ((P.smoothAt hz).differentiableAt (by simp)) (hu z), hsolve,
      P.forcing_eq hz, sub_self]

private theorem HolomorphicCousin.LocalPotential.forcing_eq_zero_on_normalization {ι : Type*}
    (P : HolomorphicCousin.LocalPotential ι) {i : ι} {V : Set ℂ} (hV : IsOpen V)
    (hVi : V ⊆ P.domain i) (hzero : Set.EqOn (P.potential i) (fun _ => 0) V) :
    Set.EqOn P.forcing (fun _ => 0) V := by
  intro z hz
  apply P.forcing_eq_zero (hVi hz)
  apply (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq
  filter_upwards [hV.mem_nhds hz] with w hw
  exact hzero hw

private theorem
    HolomorphicCousin.LocalPotential.forcing_tsupport_subset_of_normalization {ι : Type*}
    (P : HolomorphicCousin.LocalPotential ι) {i : ι} {V : Set ℂ} (hV : IsOpen V)
    (hVi : V ⊆ P.domain i) (hzero : Set.EqOn (P.potential i) (fun _ => 0) V) :
    tsupport P.forcing ⊆ Vᶜ := by
  apply closure_minimal ?_ hV.isClosed_compl
  intro z hz hzV
  exact hz (P.forcing_eq_zero_on_normalization hV hVi hzero hzV)

private theorem
    HolomorphicCousin.exists_normalized_cocycle_localPotential {ι : Type*} {U : ι → Set ℂ}
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ z, ∃ i, z ∈ U i) {h : ι → ι → ℂ → ℂ}
    (hh : ∀ i j, AnalyticOnNhd ℂ (h i j) (U i ∩ U j))
    (hc : ∀ i j k z, z ∈ U i → z ∈ U j → z ∈ U k → h i j z + h j k z = h i k z) (i₀ : ι) (R : ℝ)
    (hRU : (Metric.ball (0 : ℂ) R)ᶜ ⊆ U i₀) :
    ∃ P : LocalPotential ι,
      P.domain = U ∧
        (∀ i j z, z ∈ U i → z ∈ U j → P.potential i z - P.potential j z = h i j z) ∧
          (∃ V : Set ℂ,
              IsOpen V ∧
                (Metric.ball (0 : ℂ) R)ᶜ ⊆ V ∧
                  V ⊆ U i₀ ∧
                    Set.EqOn (P.potential i₀) (fun _ => 0) V ∧
                      ∀ i, Set.EqOn (P.potential i) (h i i₀) (U i ∩ V)) ∧
            tsupport P.forcing ⊆ Metric.ball (0 : ℂ) R ∧ HasCompactSupport P.forcing := by
  have hsmooth i j : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (h i j) (U i ∩ U j) :=
    ((hh i j).contDiffOn_of_completeSpace (n := ∞)).restrict_scalars ℝ |>.contMDiffOn
  obtain ⟨V, s, hVo, hRV, hVU, hs, htrans, hs0, hsOverlap⟩ :=
    exists_normalized_smooth_cocycle_cochain hU hcover hsmooth hc i₀
      Metric.isOpen_ball.isClosed_compl hRU
  let P : LocalPotential ι :=
    { domain := U
      isOpen_domain := hU
      cover := hcover
      potential := s
      smooth := fun i => (hs i).contDiffOn
      analytic_difference := fun i j =>
        (hh i j).congr ((hU i).inter (hU j)) (fun z hz => (htrans i j z hz.1 hz.2).symm) }
  have hsupport : tsupport P.forcing ⊆ Metric.ball (0 : ℂ) R := by
    have hsub := P.forcing_tsupport_subset_of_normalization hVo hVU hs0
    intro z hz
    by_contra hzR
    exact hsub hz (hRV hzR)
  have hcompact : HasCompactSupport P.forcing := by
    apply
      HasCompactSupport.of_support_subset_isCompact (ProperSpace.isCompact_closedBall (0 : ℂ) R)
    exact (subset_tsupport P.forcing).trans (hsupport.trans Metric.ball_subset_closedBall)
  exact ⟨P, rfl, htrans, ⟨V, hVo, hRV, hVU, hs0, hsOverlap⟩, hsupport, hcompact⟩

private theorem HolomorphicCousin.locallyIntegrable_complex_inv :
    MeasureTheory.LocallyIntegrable (fun z : ℂ => z⁻¹) := by
  refine
    MeasureTheory.locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1)
      (by simp [Complex.finrank_real_complex]) (by norm_num [Complex.finrank_real_complex]) ?_ ?_
  · filter_upwards with z
    simp only [norm_inv, Real.rpow_neg_one, one_mul, le_refl]
  · exact Measurable.aestronglyMeasurable (by fun_prop)

private def HolomorphicCousin.cauchyGreen (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / (Real.pi : ℂ)) * ∫ w : ℂ, w⁻¹ * f (z - w)

private theorem HolomorphicCousin.contDiff_cauchyGreen {n : ℕ∞} {f : ℂ → ℂ} (hf : ContDiff ℝ n f)
    (hcf : HasCompactSupport f) : ContDiff ℝ n (cauchyGreen f) := by
  change
    ContDiff ℝ n
      (fun z => (1 / (Real.pi : ℂ)) * ((fun w : ℂ => w⁻¹) ⋆[ContinuousLinearMap.mul ℝ ℂ] f) z)
  exact
    contDiff_const.mul
      (hcf.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ) locallyIntegrable_complex_inv
        hf)

private theorem HolomorphicCousin.hasFDerivAt_cauchyGreen {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (hcf : HasCompactSupport f) (z : ℂ) :
    HasFDerivAt (cauchyGreen f)
      ((1 / (Real.pi : ℂ)) •
        ((fun w : ℂ => w⁻¹) ⋆[(ContinuousLinearMap.mul ℝ ℂ).precompR ℂ] fderiv ℝ f) z)
      z := by
  convert!
    (hcf.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℂ) locallyIntegrable_complex_inv
          hf z).const_mul
      (1 / (Real.pi : ℂ)) using
    1

private theorem HolomorphicCousin.dbarLinear_precompR_mul (a : ℂ) (L : ℂ →L[ℝ] ℂ) :
    dbarLinear ((ContinuousLinearMap.mul ℝ ℂ).precompR ℂ a L) = a * dbarLinear L := by
  change dbarLinear (a • L) = a * dbarLinear L
  exact dbarLinear_complex_smul a L

private theorem
    HolomorphicCousin.dbar_cauchyGreen_eq_cauchyGreen_dbar {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (hcf : HasCompactSupport f) (z : ℂ) : dbar (cauchyGreen f) z = cauchyGreen (dbar f) z := by
  have hi :
    MeasureTheory.Integrable
      (fun w : ℂ => (ContinuousLinearMap.mul ℝ ℂ).precompR ℂ w⁻¹ (fderiv ℝ f (z - w))) :=
    (hcf.fderiv ℝ).convolutionExists_right ((ContinuousLinearMap.mul ℝ ℂ).precompR ℂ)
      locallyIntegrable_complex_inv (hf.continuous_fderiv one_ne_zero) z
  rw [dbar_eq_dbarLinear, (hasFDerivAt_cauchyGreen hf hcf z).fderiv, dbarLinear_complex_smul,
    MeasureTheory.convolution_def, ← dbarLinear.integral_comp_comm hi]
  simp only [dbarLinear_precompR_mul, ← dbar_eq_dbarLinear, cauchyGreen]

private def HolomorphicCousin.greenUnit (θ : ℝ) : ℂ :=
  circleMap 0 1 θ

private theorem HolomorphicCousin.greenUnit_eq (θ : ℝ) :
    greenUnit θ = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
  simp [greenUnit, circleMap, Complex.exp_mul_I]

@[simp]
private theorem HolomorphicCousin.norm_greenUnit (θ : ℝ) : ‖greenUnit θ‖ = 1 := by simp [greenUnit]

private theorem HolomorphicCousin.continuous_greenUnit : Continuous greenUnit := by
  exact continuous_circleMap 0 1

private theorem HolomorphicCousin.polarCoord_symm_eq_greenUnit (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = (p.1 : ℂ) * greenUnit p.2 := by
  simp [Complex.polarCoord_symm_apply, greenUnit_eq]

private theorem HolomorphicCousin.realLinear_apply_complex (D : ℂ →L[ℝ] ℂ) (z : ℂ) :
    D z = (z.re : ℂ) * D 1 + (z.im : ℂ) * D Complex.I := by
  calc
    D z = D (z.re • (1 : ℂ) + z.im • Complex.I) := by
      congr 1
      simp [Complex.real_smul]
    _ = (z.re : ℂ) * D 1 + (z.im : ℂ) * D Complex.I := by
      rw [map_add, map_smul, map_smul]
      simp [Complex.real_smul]

private theorem HolomorphicCousin.polar_realLinear_identity (D : ℂ →L[ℝ] ℂ) (z : ℂ) :
    D z + Complex.I * D (Complex.I * z) = Star.star z * (D 1 + Complex.I * D Complex.I) := by
  have hc : Star.star z = (z.re : ℂ) - (z.im : ℂ) * Complex.I := by apply Complex.ext <;> simp
  rw [realLinear_apply_complex D z, realLinear_apply_complex D (Complex.I * z), hc]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, MulZeroClass.zero_mul,
    one_mul, zero_sub, zero_add, Complex.ofReal_neg]
  ring_nf
  simp [Complex.I_sq]

private def HolomorphicCousin.greenRadial (φ : ℂ → ℂ) (p : ℝ × ℝ) : ℂ :=
  fderiv ℝ φ ((p.1 : ℂ) * greenUnit p.2) (greenUnit p.2)

private def HolomorphicCousin.greenAngular (φ : ℂ → ℂ) (p : ℝ × ℝ) : ℂ :=
  fderiv ℝ φ ((p.1 : ℂ) * greenUnit p.2) (Complex.I * greenUnit p.2)

private theorem HolomorphicCousin.continuous_greenRadial {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) :
    Continuous (greenRadial φ) := by
  exact
    (hφ.continuous_fderiv_apply one_ne_zero).comp
      (((Complex.continuous_ofReal.comp continuous_fst).mul
            (continuous_greenUnit.comp continuous_snd)).prodMk
        (continuous_greenUnit.comp continuous_snd))

private theorem HolomorphicCousin.continuous_greenAngular {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) :
    Continuous (greenAngular φ) := by
  exact
    (hφ.continuous_fderiv_apply one_ne_zero).comp
      (((Complex.continuous_ofReal.comp continuous_fst).mul
            (continuous_greenUnit.comp continuous_snd)).prodMk
        (continuous_const.mul (continuous_greenUnit.comp continuous_snd)))

private theorem HolomorphicCousin.hasDerivAt_green_radial {φ : ℂ → ℂ} (hφ : Differentiable ℝ φ)
    (r θ : ℝ) : HasDerivAt (fun t : ℝ => φ ((t : ℂ) * greenUnit θ)) (greenRadial φ (r, θ)) r := by
  apply (hφ _).hasFDerivAt.comp_hasDerivAt
  simpa using (Complex.ofRealCLM.hasDerivAt (x := r)).mul_const (greenUnit θ)

private theorem HolomorphicCousin.hasDerivAt_green_angular {φ : ℂ → ℂ} (hφ : Differentiable ℝ φ)
    (r θ : ℝ) :
    HasDerivAt (fun t : ℝ => φ ((r : ℂ) * greenUnit t)) ((r : ℂ) * greenAngular φ (r, θ)) θ := by
  have hu : HasDerivAt greenUnit (Complex.I * greenUnit θ) θ := by
    change HasDerivAt (circleMap 0 1) (Complex.I * circleMap 0 1 θ) θ
    simpa [mul_comm] using hasDerivAt_circleMap 0 1 θ
  have hd := (hφ _).hasFDerivAt.comp_hasDerivAt θ (hu.const_mul (r : ℂ))
  simpa only [Function.comp_def, ← Complex.real_smul, map_smul, greenAngular] using hd

private theorem HolomorphicCousin.integral_greenRadial {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) (R θ : ℝ) :
    (∫ r in 0..R, greenRadial φ (r, θ)) = φ ((R : ℂ) * greenUnit θ) - φ 0 := by
  have hint :
    IntervalIntegrable (fun r => greenRadial φ (r, θ)) MeasureTheory.MeasureSpace.volume 0 R :=
    ((continuous_greenRadial hφ).comp (continuous_id.prodMk continuous_const)).intervalIntegrable
      _ _
  simpa using
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r _ => hasDerivAt_green_radial (hφ.differentiable one_ne_zero) r θ) hint

private theorem HolomorphicCousin.integral_greenAngular {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ) {r : ℝ}
    (hr : r ≠ 0) : (∫ θ in (-Real.pi)..Real.pi, greenAngular φ (r, θ)) = 0 := by
  have hint :
    IntervalIntegrable (fun θ => (r : ℂ) * greenAngular φ (r, θ))
      MeasureTheory.MeasureSpace.volume (-Real.pi) Real.pi :=
    (continuous_const.mul
          ((continuous_greenAngular hφ).comp
            (continuous_const.prodMk continuous_id))).intervalIntegrable
      _ _
  have heq :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun θ _ => hasDerivAt_green_angular (hφ.differentiable one_ne_zero) r θ) hint
  have hend : greenUnit Real.pi = greenUnit (-Real.pi) := by simp [greenUnit_eq]
  have hz : (r : ℂ) * (∫ θ in (-Real.pi)..Real.pi, greenAngular φ (r, θ)) = 0 := by
    simpa only [intervalIntegral.integral_const_mul, hend, sub_self] using heq
  exact (mul_eq_zero.mp hz).resolve_left (Complex.ofReal_ne_zero.mpr hr)

private theorem
    HolomorphicCousin.exists_green_support_radius {φ : ℂ → ℂ} (hφ : HasCompactSupport φ) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, R ≤ ‖z‖ → φ z = 0 ∧ fderiv ℝ φ z = 0 := by
  obtain ⟨R, hR, hs⟩ := hφ.isBounded.subset_ball_lt 0 (0 : ℂ)
  refine ⟨R, hR, ?_⟩
  intro z hz
  have hn : z ∉ tsupport φ := by
    intro hmem
    have hlt : ‖z‖ < R := by simpa using hs hmem
    exact not_lt_of_ge hz hlt
  exact ⟨image_eq_zero_of_notMem_tsupport hn, fderiv_of_notMem_tsupport ℝ hn⟩

private theorem HolomorphicCousin.integrableOn_polarRectangle_mo1973_17804 {G : ℝ × ℝ → ℂ} {R : ℝ}
    (hG : ContinuousOn G (Set.Icc 0 R ×ˢ Set.Icc (-Real.pi) Real.pi)) :
    MeasureTheory.IntegrableOn G (Set.Ioc 0 R ×ˢ Set.Ioo (-Real.pi) Real.pi) := by
  apply
    (hG.integrableOn_compact
        (CompactIccSpace.isCompact_Icc.prod CompactIccSpace.isCompact_Icc)).mono_set
  rintro ⟨r, θ⟩ ⟨hr, hθ⟩
  exact ⟨⟨hr.1.le, hr.2⟩, ⟨hθ.1.le, hθ.2.le⟩⟩

private theorem HolomorphicCousin.integrableOn_polarTarget_of_radial_support {G : ℝ × ℝ → ℂ} {R : ℝ}
    (hG : ContinuousOn G (Set.Icc 0 R ×ˢ Set.Icc (-Real.pi) Real.pi))
    (hzero : ∀ p, R < p.1 → G p = 0) : MeasureTheory.IntegrableOn G polarCoord.target := by
  apply
    (integrableOn_polarRectangle_mo1973_17804 hG).of_forall_sdiff_eq_zero
      polarCoord.open_target.measurableSet
  rintro ⟨r, θ⟩ ⟨hp, hnot⟩
  apply hzero
  by_contra hr
  exact hnot ⟨⟨hp.1, le_of_not_gt hr⟩, hp.2⟩

private theorem HolomorphicCousin.integral_polarTarget_eq_rectangle {G : ℝ × ℝ → ℂ} {R : ℝ}
    (hzero : ∀ p, R < p.1 → G p = 0) :
    (∫ p in polarCoord.target, G p) = ∫ p in Set.Ioc 0 R ×ˢ Set.Ioo (-Real.pi) Real.pi, G p := by
  apply
    MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      polarCoord.open_target.measurableSet
  · rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    exact ⟨hr.1, hθ⟩
  · rintro ⟨r, θ⟩ ⟨hp, hnot⟩
    apply hzero
    by_contra hr
    exact hnot ⟨⟨hp.1, le_of_not_gt hr⟩, hp.2⟩

private theorem HolomorphicCousin.integral_polarTarget_eq_radius_angle {G : ℝ × ℝ → ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hG : ContinuousOn G (Set.Icc 0 R ×ˢ Set.Icc (-Real.pi) Real.pi))
    (hzero : ∀ p, R < p.1 → G p = 0) :
    (∫ p in polarCoord.target, G p) = ∫ r in 0..R, ∫ θ in (-Real.pi)..Real.pi, G (r, θ) := by
  rw [integral_polarTarget_eq_rectangle hzero]
  rw [MeasureTheory.Measure.volume_eq_prod]
  rw [MeasureTheory.setIntegral_prod G
      (by
        simpa only [MeasureTheory.Measure.volume_eq_prod] using
          integrableOn_polarRectangle_mo1973_17804 hG)]
  simp_rw [intervalIntegral.integral_of_le hR,
    intervalIntegral.integral_of_le (neg_le_self Real.pi_pos.le),
    MeasureTheory.integral_Ioc_eq_integral_Ioo]

private theorem HolomorphicCousin.integral_polarTarget_eq_angle_radius {G : ℝ × ℝ → ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hG : ContinuousOn G (Set.Icc 0 R ×ˢ Set.Icc (-Real.pi) Real.pi))
    (hzero : ∀ p, R < p.1 → G p = 0) :
    (∫ p in polarCoord.target, G p) = ∫ θ in (-Real.pi)..Real.pi, ∫ r in 0..R, G (r, θ) := by
  rw [integral_polarTarget_eq_rectangle hzero, MeasureTheory.Measure.volume_eq_prod, ←
    MeasureTheory.Measure.prod_restrict]
  rw [MeasureTheory.integral_prod_symm G
      (by
        simpa only [MeasureTheory.IntegrableOn, MeasureTheory.Measure.prod_restrict,
          ← MeasureTheory.Measure.volume_eq_prod] using
          integrableOn_polarRectangle_mo1973_17804 hG)]
  simp_rw [intervalIntegral.integral_of_le hR,
    intervalIntegral.integral_of_le (neg_le_self Real.pi_pos.le),
    MeasureTheory.integral_Ioc_eq_integral_Ioo]

private theorem HolomorphicCousin.green_polar_integrand (φ : ℂ → ℂ) (p : ℝ × ℝ) (hp : 0 < p.1) :
    p.1 • ((Complex.polarCoord.symm p)⁻¹ * dbar φ (Complex.polarCoord.symm p)) =
      (greenRadial φ p + Complex.I * greenAngular φ p) / 2 := by
  have hr : (p.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
  rw [polarCoord_symm_eq_greenUnit, Complex.real_smul, dbar]
  unfold greenRadial greenAngular
  rw [polar_realLinear_identity, Complex.star_def, ← Complex.inv_eq_conj (norm_greenUnit p.2)]
  field_simp

private theorem HolomorphicCousin.greenRadial_radius_vanish_mo1973_17810 {φ : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hz : ∀ z : ℂ, R ≤ ‖z‖ → fderiv ℝ φ z = 0) :
    ∀ p : ℝ × ℝ, R < p.1 → greenRadial φ p = 0 := by
  intro p hp
  have hn : R ≤ ‖(p.1 : ℂ) * greenUnit p.2‖ := by
    simpa only [norm_mul, norm_greenUnit, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hR.trans hp)] using hp.le
  simp only [greenRadial, hz _ hn, zero_apply]

private theorem HolomorphicCousin.greenAngular_radius_vanish_mo1973_17811 {φ : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hz : ∀ z : ℂ, R ≤ ‖z‖ → fderiv ℝ φ z = 0) :
    ∀ p : ℝ × ℝ, R < p.1 → greenAngular φ p = 0 := by
  intro p hp
  have hn : R ≤ ‖(p.1 : ℂ) * greenUnit p.2‖ := by
    simpa only [norm_mul, norm_greenUnit, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hR.trans hp)] using hp.le
  simp only [greenAngular, hz _ hn, zero_apply]

private theorem HolomorphicCousin.integrableOn_greenRadial {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) : MeasureTheory.IntegrableOn (greenRadial φ) polarCoord.target := by
  obtain ⟨R, hR, hz⟩ := exists_green_support_radius hc
  exact
    integrableOn_polarTarget_of_radial_support (continuous_greenRadial hφ).continuousOn
      (greenRadial_radius_vanish_mo1973_17810 hR (fun z h => (hz z h).2))

private theorem HolomorphicCousin.integrableOn_greenAngular {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) : MeasureTheory.IntegrableOn (greenAngular φ) polarCoord.target := by
  obtain ⟨R, hR, hz⟩ := exists_green_support_radius hc
  exact
    integrableOn_polarTarget_of_radial_support (continuous_greenAngular hφ).continuousOn
      (greenAngular_radius_vanish_mo1973_17811 hR (fun z h => (hz z h).2))

private theorem HolomorphicCousin.integral_greenRadial_polarTarget {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) :
    (∫ p in polarCoord.target, greenRadial φ p) = -(2 * (Real.pi : ℂ)) * φ 0 := by
  obtain ⟨R, hR, hz⟩ := exists_green_support_radius hc
  rw [integral_polarTarget_eq_angle_radius hR.le (continuous_greenRadial hφ).continuousOn
      (greenRadial_radius_vanish_mo1973_17810 hR (fun z h => (hz z h).2))]
  have hend (θ : ℝ) : φ ((R : ℂ) * greenUnit θ) = 0 := by
    apply (hz _ _).1
    simp [abs_of_pos hR]
  simp_rw [integral_greenRadial hφ, hend, zero_sub]
  simp only [intervalIntegral.integral_const, Complex.real_smul, sub_neg_eq_add,
    Complex.ofReal_add]
  ring

private theorem
    HolomorphicCousin.integral_greenAngular_polarTarget {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) : (∫ p in polarCoord.target, greenAngular φ p) = 0 := by
  obtain ⟨R, hR, hz⟩ := exists_green_support_radius hc
  rw [integral_polarTarget_eq_radius_angle hR.le (continuous_greenAngular hφ).continuousOn
      (greenAngular_radius_vanish_mo1973_17811 hR (fun z h => (hz z h).2))]
  apply intervalIntegral.integral_zero_ae
  filter_upwards with r hr
  have hr' : r ∈ Set.Ioc 0 R := by simpa only [Set.uIoc_of_le hR.le] using hr
  exact integral_greenAngular hφ hr'.1.ne'

private theorem HolomorphicCousin.integral_inv_mul_dbar {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) : (∫ w : ℂ, w⁻¹ * dbar φ w) = -(Real.pi : ℂ) * φ 0 := by
  rw [← Complex.integral_comp_polarCoord_symm]
  calc
    (∫ p in polarCoord.target,
          p.1 • ((Complex.polarCoord.symm p)⁻¹ * dbar φ (Complex.polarCoord.symm p))) =
        ∫ p in polarCoord.target, (greenRadial φ p + Complex.I * greenAngular φ p) / 2 := by
      apply MeasureTheory.setIntegral_congr_fun polarCoord.open_target.measurableSet
      intro p hp
      exact green_polar_integrand φ p hp.1
    _ =
        ((∫ p in polarCoord.target, greenRadial φ p) +
            Complex.I * (∫ p in polarCoord.target, greenAngular φ p)) /
          2 := by
      rw [MeasureTheory.integral_div,
        MeasureTheory.integral_add (integrableOn_greenRadial hφ hc)
          ((integrableOn_greenAngular hφ hc).const_mul Complex.I),
        MeasureTheory.integral_const_mul]
    _ = -(Real.pi : ℂ) * φ 0 := by
      rw [integral_greenRadial_polarTarget hφ hc, integral_greenAngular_polarTarget hφ hc]
      ring

private theorem HolomorphicCousin.cauchyGreen_dbar {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (hcf : HasCompactSupport f) (z : ℂ) : cauchyGreen (dbar f) z = f z := by
  let φ : ℂ → ℂ := fun w => f (z - w)
  have hφ : ContDiff ℝ 1 φ := hf.comp (contDiff_const.sub contDiff_id)
  have hcφ : HasCompactSupport φ := hcf.comp_homeomorph (Homeomorph.subLeft z)
  have hd : dbar φ = fun w => -dbar f (z - w) := by
    funext w
    exact dbar_comp_const_sub z w ((hf.differentiable one_ne_zero) (z - w))
  have he := integral_inv_mul_dbar hφ hcφ
  have he' : -(∫ w : ℂ, w⁻¹ * dbar f (z - w)) = -((Real.pi : ℂ) * f z) := by
    simpa only [hd, mul_neg, MeasureTheory.integral_neg, φ, sub_zero, neg_mul] using he
  have hi := neg_injective he'
  unfold cauchyGreen
  rw [hi, one_div, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero

private theorem HolomorphicCousin.dbar_cauchyGreen {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (hcf : HasCompactSupport f) (z : ℂ) : dbar (cauchyGreen f) z = f z := by
  rw [dbar_cauchyGreen_eq_cauchyGreen_dbar hf hcf, cauchyGreen_dbar hf hcf]

private theorem HolomorphicCousin.cauchyGreen_smooth_dbar_solution {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hcf : HasCompactSupport f) :
    ContDiff ℝ ∞ (cauchyGreen f) ∧ ∀ z, dbar (cauchyGreen f) z = f z := by
  refine ⟨contDiff_cauchyGreen hf hcf, ?_⟩
  exact dbar_cauchyGreen (hf.of_le (by simp)) hcf

private def HolomorphicCousin.cauchyGreenInfinity (f : ℂ → ℂ) (u : ℂ) : ℂ :=
  (1 / (Real.pi : ℂ)) * ∫ w : ℂ, u * (1 - w * u)⁻¹ * f w

@[simp]
private theorem
    HolomorphicCousin.cauchyGreenInfinity_zero (f : ℂ → ℂ) : cauchyGreenInfinity f 0 = 0 := by
  simp [cauchyGreenInfinity]

private theorem HolomorphicCousin.area_denominator_ne_zero_mo1973_17824 {R : ℝ} (hR : 0 < R)
    {u w : ℂ} (hu : u ∈ Metric.ball 0 R⁻¹) (hw : ‖w‖ ≤ R) : 1 - w * u ≠ 0 := by
  have hu' : ‖u‖ < R⁻¹ := by simpa using hu
  have hmul : ‖w * u‖ < 1 := by
    rw [norm_mul]
    calc
      ‖w‖ * ‖u‖ ≤ R * ‖u‖ := mul_le_mul_of_nonneg_right hw (norm_nonneg u)
      _ < R * R⁻¹ := (mul_lt_mul_of_pos_left hu' hR)
      _ = 1 := mul_inv_cancel₀ hR.ne'
  intro heq
  have hwu : w * u = 1 := (sub_eq_zero.mp heq).symm
  simp [hwu] at hmul

private theorem HolomorphicCousin.area_denominator_lower_bound_mo1973_17825 {R r : ℝ} (hR : 0 < R)
    {x w : ℂ} (hx : x ∈ Metric.ball 0 r) (hw : ‖w‖ ≤ R) : 1 - R * r ≤ ‖1 - w * x‖ := by
  have hx' : ‖x‖ ≤ r := le_of_lt (by simpa using hx)
  have hmul : ‖w * x‖ ≤ R * r := by
    rw [norm_mul]
    exact mul_le_mul hw hx' (norm_nonneg x) hR.le
  calc
    1 - R * r ≤ 1 - ‖w * x‖ := sub_le_sub_left hmul 1
    _ = ‖(1 : ℂ)‖ - ‖w * x‖ := by rw [NormOneClass.norm_one]
    _ ≤ ‖1 - w * x‖ := norm_sub_norm_le _ _

private theorem HolomorphicCousin.area_reciprocal_kernel_hasDerivAt_mo1973_17826 {w x : ℂ}
    (hne : 1 - w * x ≠ 0) : HasDerivAt (fun y : ℂ => y * (1 - w * y)⁻¹) (1 / (1 - w * x) ^ 2) x :=
  by
  have hn : HasDerivAt (fun y : ℂ => y) 1 x := hasDerivAt_id x
  have hd : HasDerivAt (fun y : ℂ => 1 - w * y) (-w) x := by
    simpa only [mul_one, id_eq] using! ((hasDerivAt_id x).const_mul w).const_sub 1
  have hnum : (1 : ℂ) * (1 - w * x) - x * -w = 1 := by ring
  simpa only [Pi.div_apply, hnum, div_eq_mul_inv] using! hn.div hd hne

private theorem HolomorphicCousin.hasDerivAt_cauchyGreenInfinity {f : ℂ → ℂ} {R : ℝ}
    (hf : MeasureTheory.Integrable f) (hR : 0 < R) (hbound : ∀ w ∈ Function.support f, ‖w‖ ≤ R)
    {u : ℂ} (hu : u ∈ Metric.ball 0 R⁻¹) :
    HasDerivAt (cauchyGreenInfinity f)
      ((1 / (Real.pi : ℂ)) * ∫ w : ℂ, (1 / (1 - w * u) ^ 2) * f w) u := by
  have hu' : ‖u‖ < R⁻¹ := by simpa using hu
  obtain ⟨r, hur, hrR⟩ := exists_between hu'
  have hsub : Metric.ball (0 : ℂ) r ⊆ Metric.ball 0 R⁻¹ := Metric.ball_subset_ball hrR.le
  have humem : u ∈ Metric.ball (0 : ℂ) r := by simpa using hur
  have hd : 0 < 1 - R * r := by
    have hlt : R * r < 1 := by
      calc
        R * r < R * R⁻¹ := mul_lt_mul_of_pos_left hrR hR
        _ = 1 := mul_inv_cancel₀ hR.ne'
    linarith
  have hmeas (x : ℂ) :
    MeasureTheory.AEStronglyMeasurable (fun w : ℂ => x * (1 - w * x)⁻¹ * f w)
      MeasureTheory.MeasureSpace.volume := by
    apply MeasureTheory.AEStronglyMeasurable.mul _ hf.aestronglyMeasurable
    exact Measurable.aestronglyMeasurable (by fun_prop)
  have hint : MeasureTheory.Integrable (fun w : ℂ => u * (1 - w * u)⁻¹ * f w) := by
    refine (hf.norm.const_mul (‖u‖ * (1 - R * r)⁻¹)).mono' (hmeas u) ?_
    filter_upwards with w
    by_cases hw : f w = 0
    · simp [hw]
    · have hwb := hbound w hw
      simp only [norm_mul, norm_inv]
      gcongr
      exact area_denominator_lower_bound_mo1973_17825 hR humem hwb
  change HasDerivAt (fun x => cauchyGreenInfinity f x) _ u
  simp only [cauchyGreenInfinity]
  apply HasDerivAt.const_mul
  refine
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F' := fun x w : ℂ =>
        (1 / (1 - w * x) ^ 2) * f w) (bound := fun w : ℂ => ((1 - R * r) ^ 2)⁻¹ * ‖f w‖)
        (Metric.isOpen_ball.mem_nhds humem) (Filter.Eventually.of_forall hmeas) hint ?_ ?_ ?_
        ?_).2
  · apply MeasureTheory.AEStronglyMeasurable.mul _ hf.aestronglyMeasurable
    exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards with w x hx
    by_cases hw : f w = 0
    · simp [hw]
    · have hwb := hbound w hw
      simp only [norm_mul, norm_inv, norm_pow, one_div]
      gcongr
      exact area_denominator_lower_bound_mo1973_17825 hR hx hwb
  · exact hf.norm.const_mul _
  · filter_upwards with w x hx
    by_cases hw : f w = 0
    · simpa only [hw, MulZeroClass.mul_zero] using hasDerivAt_const x (0 : ℂ)
    · exact
        (area_reciprocal_kernel_hasDerivAt_mo1973_17826
              (area_denominator_ne_zero_mo1973_17824 hR (hsub hx) (hbound w hw))).mul_const
          (f w)

private theorem
    HolomorphicCousin.analyticOnNhd_cauchyGreenInfinity_of_integrable {f : ℂ → ℂ} {R : ℝ}
    (hf : MeasureTheory.Integrable f) (hR : 0 < R) (hbound : ∀ w ∈ Function.support f, ‖w‖ ≤ R) :
    AnalyticOnNhd ℂ (cauchyGreenInfinity f) (Metric.ball 0 R⁻¹) := by
  apply DifferentiableOn.analyticOnNhd _ Metric.isOpen_ball
  intro u hu
  exact (hasDerivAt_cauchyGreenInfinity hf hR hbound hu).differentiableAt.differentiableWithinAt

private theorem HolomorphicCousin.analyticOnNhd_cauchyGreenInfinity {f : ℂ → ℂ} {R : ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hR : 0 < R)
    (hbound : ∀ w ∈ Function.support f, ‖w‖ ≤ R) :
    AnalyticOnNhd ℂ (cauchyGreenInfinity f) (Metric.ball 0 R⁻¹) :=
  analyticOnNhd_cauchyGreenInfinity_of_integrable (hf.integrable_of_hasCompactSupport hfc) hR
    hbound

private theorem HolomorphicCousin.cauchyGreenInfinity_inv (f : ℂ → ℂ) {z : ℂ} (hz : z ≠ 0) :
    cauchyGreenInfinity f z⁻¹ = cauchyGreen f z := by
  unfold cauchyGreenInfinity cauchyGreen
  congr 1
  calc
    (∫ w : ℂ, z⁻¹ * (1 - w * z⁻¹)⁻¹ * f w) = ∫ w : ℂ, (z - w)⁻¹ * f w := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with w
      have hden : 1 - w * z⁻¹ = (z - w) * z⁻¹ := by rw [sub_mul, mul_inv_cancel₀ hz]
      rw [hden, mul_inv_rev, inv_inv, ← mul_assoc, inv_mul_cancel₀ hz, one_mul]
    _ = ∫ w : ℂ, w⁻¹ * f (z - w) := by
      simpa only [sub_sub_self] using
        MeasureTheory.integral_sub_left_eq_self (fun w : ℂ => w⁻¹ * f (z - w))
          MeasureTheory.MeasureSpace.volume z

private def HolomorphicCousin.LocalPotential.correctedPart {ι : Type*}
    (P : HolomorphicCousin.LocalPotential ι) (i : ι) (z : ℂ) : ℂ :=
  P.potential i z - HolomorphicCousin.cauchyGreen P.forcing z

private theorem HolomorphicCousin.LocalPotential.correctedPart_analytic {ι : Type*}
    (P : HolomorphicCousin.LocalPotential ι) (hc : HasCompactSupport P.forcing) (i : ι) :
    AnalyticOnNhd ℂ (P.correctedPart i) (P.domain i) := by
  obtain ⟨hs, he⟩ := HolomorphicCousin.cauchyGreen_smooth_dbar_solution P.forcing_contDiff hc
  exact P.corrected_analytic (hs.differentiable (by simp)) he i

private theorem HolomorphicCousin.LocalPotential.correctedPart_sub {ι : Type*}
    (P : HolomorphicCousin.LocalPotential ι) (i j : ι) (z : ℂ) :
    P.correctedPart i z - P.correctedPart j z = P.potential i z - P.potential j z :=
  P.corrected_difference (HolomorphicCousin.cauchyGreen P.forcing) i j z

private def HolomorphicCousin.LocalPotential.correctedInfinity {ι : Type*}
    (P : HolomorphicCousin.LocalPotential ι) (u : ℂ) : ℂ :=
  -HolomorphicCousin.cauchyGreenInfinity P.forcing u

@[simp]
private theorem HolomorphicCousin.LocalPotential.correctedInfinity_zero {ι : Type*}
    (P : HolomorphicCousin.LocalPotential ι) : P.correctedInfinity 0 = 0 := by
  simp [correctedInfinity]

private theorem HolomorphicCousin.LocalPotential.correctedInfinity_analytic {ι : Type*}
    (P : HolomorphicCousin.LocalPotential ι) (hc : HasCompactSupport P.forcing) {R : ℝ}
    (hR : 0 < R) (hbound : ∀ z ∈ Function.support P.forcing, ‖z‖ ≤ R) :
    AnalyticOnNhd ℂ P.correctedInfinity (Metric.ball 0 R⁻¹) :=
  (HolomorphicCousin.analyticOnNhd_cauchyGreenInfinity P.forcing_contDiff.continuous hc hR
      hbound).neg

private theorem HolomorphicCousin.LocalPotential.correctedPart_eq_infinity {ι : Type*}
    (P : HolomorphicCousin.LocalPotential ι) {i : ι} {z : ℂ} (hz : z ≠ 0)
    (hs : P.potential i z = 0) : P.correctedPart i z = P.correctedInfinity z⁻¹ := by
  simp only [correctedPart, hs, zero_sub, correctedInfinity,
    HolomorphicCousin.cauchyGreenInfinity_inv P.forcing hz]

private structure HolomorphicCousin.NormalizedCocycleSolution {ι : Type*} (U : ι → Set ℂ)
    (h : ι → ι → ℂ → ℂ) (i₀ : ι) (R : ℝ) where
  localPart : ι → ℂ → ℂ
  infinityPart : ℂ → ℂ
  local_analytic : ∀ i, AnalyticOnNhd ℂ (localPart i) (U i)
  infinity_analytic : AnalyticOnNhd ℂ infinityPart (Metric.ball 0 R⁻¹)
  infinity_zero : infinityPart 0 = 0
  equation : ∀ i j z, z ∈ U i → z ∈ U j → localPart i z - localPart j z = h i j z
  atInfinity : ∀ z, R < ‖z‖ → localPart i₀ z = infinityPart z⁻¹

private theorem HolomorphicCousin.exists_normalized_holomorphic_cocycle_solution {ι : Type*}
    {U : ι → Set ℂ} (hU : ∀ i, IsOpen (U i)) (hcover : ∀ z, ∃ i, z ∈ U i) {h : ι → ι → ℂ → ℂ}
    (hh : ∀ i j, AnalyticOnNhd ℂ (h i j) (U i ∩ U j))
    (hc : ∀ i j k z, z ∈ U i → z ∈ U j → z ∈ U k → h i j z + h j k z = h i k z) (i₀ : ι) {R : ℝ}
    (hR : 0 < R) (hRU : (Metric.ball (0 : ℂ) R)ᶜ ⊆ U i₀) :
    Nonempty (NormalizedCocycleSolution U h i₀ R) := by
  obtain ⟨P, hPU, htrans, ⟨V, _, hRV, _, hs0, _⟩, hsupport, hcompact⟩ :=
    exists_normalized_cocycle_localPotential hU hcover hh hc i₀ R hRU
  have hbound : ∀ z ∈ Function.support P.forcing, ‖z‖ ≤ R := by
    intro z hz
    have hzR := hsupport (subset_tsupport P.forcing hz)
    exact (show ‖z‖ < R by simpa only [Metric.mem_ball, dist_zero_right] using hzR).le
  refine
    ⟨{  localPart := P.correctedPart
        infinityPart := P.correctedInfinity
        local_analytic := ?_
        infinity_analytic := P.correctedInfinity_analytic hcompact hR hbound
        infinity_zero := P.correctedInfinity_zero
        equation := ?_
        atInfinity := ?_ }⟩
  · intro i
    simpa only [hPU] using P.correctedPart_analytic hcompact i
  · intro i j z hi hj
    exact (P.correctedPart_sub i j z).trans (htrans i j z hi hj)
  · intro z hz
    apply P.correctedPart_eq_infinity (norm_pos_iff.mp (hR.trans hz))
    apply hs0
    apply hRV
    simpa only [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hz.le

private structure HolomorphicCousin.NegativeOneCocycleSolution {ι : Type*} (U : ι → Set ℂ)
    (h : ι → ι → ℂ → ℂ) (i₀ : ι) (R : ℝ) where
  localPart : ι → ℂ → ℂ
  infinityPart : ℂ → ℂ
  local_analytic : ∀ i, AnalyticOnNhd ℂ (localPart i) (U i)
  infinity_analytic : AnalyticOnNhd ℂ infinityPart (Metric.ball 0 R⁻¹)
  equation : ∀ i j z, z ∈ U i → z ∈ U j → localPart i z - localPart j z = h i j z
  atInfinity : ∀ z, R < ‖z‖ → localPart i₀ z = z⁻¹ * infinityPart z⁻¹

private def HolomorphicCousin.NormalizedCocycleSolution.negativeOne {ι : Type*} {U : ι → Set ℂ}
    {h : ι → ι → ℂ → ℂ} {i₀ : ι} {R : ℝ} (hR : 0 < R)
    (s : HolomorphicCousin.NormalizedCocycleSolution U h i₀ R) :
    HolomorphicCousin.NegativeOneCocycleSolution U h i₀ R
    where
  localPart := s.localPart
  infinityPart := dslope s.infinityPart 0
  local_analytic := s.local_analytic
  infinity_analytic :=
    HolomorphicCousin.analyticOnNhd_dslope_zero (inv_pos.mpr hR) s.infinity_analytic
  equation := s.equation
  atInfinity := by
    intro z hz
    rw [s.atInfinity z hz]
    exact (HolomorphicCousin.zero_mul_dslope s.infinity_zero z⁻¹).symm

private theorem HolomorphicCousin.exists_negativeOne_holomorphic_cocycle_solution {ι : Type*}
    {U : ι → Set ℂ} (hU : ∀ i, IsOpen (U i)) (hcover : ∀ z, ∃ i, z ∈ U i) {h : ι → ι → ℂ → ℂ}
    (hh : ∀ i j, AnalyticOnNhd ℂ (h i j) (U i ∩ U j))
    (hc : ∀ i j k z, z ∈ U i → z ∈ U j → z ∈ U k → h i j z + h j k z = h i k z) (i₀ : ι) {R : ℝ}
    (hR : 0 < R) (hRU : (Metric.ball (0 : ℂ) R)ᶜ ⊆ U i₀) :
    Nonempty (NegativeOneCocycleSolution U h i₀ R) := by
  obtain ⟨s⟩ := exists_normalized_holomorphic_cocycle_solution hU hcover hh hc i₀ hR hRU
  exact ⟨s.negativeOne hR⟩

private theorem SpecialPeriods.MuTorsor.Gluing.descended_quotient_cocycle {X ι : Type*} {p : X → ℂ}
    (hp : Function.Surjective p) {U : ι → Set ℂ} {μ : ι → X → ℂ} {F : X → ℂ} {h : ι → ι → ℂ → ℂ}
    (hq : ∀ i j z, p z ∈ U i → p z ∈ U j → h i j (p z) = (μ i z - μ j z) / F z) :
    ∀ i j k w, w ∈ U i → w ∈ U j → w ∈ U k → h i j w + h j k w = h i k w := by
  intro i j k w hi hj hk
  obtain ⟨z, rfl⟩ := hp w
  rw [hq i j z hi hj, hq j k z hj hk, hq i k z hi hk]
  ring

private theorem SpecialPeriods.MuTorsor.Gluing.difference_eq_mul_quotient {X ι : Type*} {p : X → ℂ}
    {U : ι → Set ℂ} {μ : ι → X → ℂ} {F : X → ℂ} {h : ι → ι → ℂ → ℂ}
    (hq : ∀ i j z, p z ∈ U i → p z ∈ U j → h i j (p z) = (μ i z - μ j z) / F z)
    (hz : ∀ i j z, p z ∈ U i → p z ∈ U j → F z = 0 → μ i z = μ j z) (i j : ι) (z : X)
    (hi : p z ∈ U i) (hj : p z ∈ U j) : μ i z - μ j z = F z * h i j (p z) := by
  rw [hq i j z hi hj]
  by_cases hF : F z = 0
  · rw [hz i j z hi hj hF, sub_self, zero_div, MulZeroClass.mul_zero]
  · exact (mul_div_cancel₀ (μ i z - μ j z) hF).symm

private def SpecialPeriods.MuTorsor.Gluing.correctedGlue {X ι : Type*} (p : X → ℂ) (U : ι → Set ℂ)
    (hcover : ∀ w, ∃ i, w ∈ U i) (μ : ι → X → ℂ) (F : X → ℂ) {h : ι → ι → ℂ → ℂ} {i₀ : ι} {R : ℝ}
    (s : HolomorphicCousin.NegativeOneCocycleSolution U h i₀ R) (z : X) : ℂ :=
  μ (hcover (p z)).choose z - F z * s.localPart (hcover (p z)).choose (p z)

private theorem
    SpecialPeriods.MuTorsor.Gluing.correctedGlue_eq {X ι : Type*} {p : X → ℂ} {U : ι → Set ℂ}
    {hcover : ∀ w, ∃ i, w ∈ U i} {μ : ι → X → ℂ} {F : X → ℂ} {h : ι → ι → ℂ → ℂ} {i₀ : ι} {R : ℝ}
    (s : HolomorphicCousin.NegativeOneCocycleSolution U h i₀ R)
    (hdiff : ∀ i j z, p z ∈ U i → p z ∈ U j → μ i z - μ j z = F z * h i j (p z)) {i : ι} {z : X}
    (hz : p z ∈ U i) : correctedGlue p U hcover μ F s z = μ i z - F z * s.localPart i (p z) := by
  let j := (hcover (p z)).choose
  have hj : p z ∈ U j := (hcover (p z)).choose_spec
  change μ j z - F z * s.localPart j (p z) = μ i z - F z * s.localPart i (p z)
  have hd := hdiff j i z hj hz
  have hs := s.equation j i (p z) hj hz
  linear_combination hd - F z * hs

private theorem SpecialPeriods.MuTorsor.Gluing.correctedGlue_eventuallyEq {X ι : Type*}
    [TopologicalSpace X] {p : X → ℂ} (hp : Continuous p) {U : ι → Set ℂ} (hU : ∀ i, IsOpen (U i))
    {hcover : ∀ w, ∃ i, w ∈ U i} {μ : ι → X → ℂ} {F : X → ℂ} {h : ι → ι → ℂ → ℂ} {i₀ : ι} {R : ℝ}
    (s : HolomorphicCousin.NegativeOneCocycleSolution U h i₀ R)
    (hdiff : ∀ i j z, p z ∈ U i → p z ∈ U j → μ i z - μ j z = F z * h i j (p z)) {i : ι} {z : X}
    (hz : p z ∈ U i) :
    correctedGlue p U hcover μ F s =ᶠ[𝓝 z] fun w => μ i w - F w * s.localPart i (p w) := by
  filter_upwards [((hU i).preimage hp).mem_nhds hz] with w hw
  exact correctedGlue_eq s hdiff hw

private theorem SpecialPeriods.MuTorsor.Gluing.correctedGlue_holomorphic {ι : Type*} {p : ℍ → ℂ}
    (hp : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω p) {U : ι → Set ℂ} (hU : ∀ i, IsOpen (U i))
    {hcover : ∀ w, ∃ i, w ∈ U i} {μ : ι → ℍ → ℂ}
    (hμ : ∀ i, ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (μ i) (p ⁻¹' U i)) {F : ℍ → ℂ}
    (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) {h : ι → ι → ℂ → ℂ} {i₀ : ι} {R : ℝ}
    (s : HolomorphicCousin.NegativeOneCocycleSolution U h i₀ R)
    (hdiff : ∀ i j z, p z ∈ U i → p z ∈ U j → μ i z - μ j z = F z * h i j (p z)) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (correctedGlue p U hcover μ F s) := by
  intro z
  obtain ⟨i, hi⟩ := hcover (p z)
  have hm : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (μ i) z :=
    (hμ i).contMDiffAt (((hU i).preimage hp.continuous).mem_nhds hi)
  have hs : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun w => s.localPart i (p w)) z :=
    (s.local_analytic i (p z) hi).contDiffAt.contMDiffAt.comp z (hp z)
  exact
    (hm.sub ((hF z).mul hs)).congr_of_eventuallyEq
      (correctedGlue_eventuallyEq hp.continuous hU s hdiff hi)

private theorem SpecialPeriods.MuTorsor.Gluing.correctedGlue_affine_law {ι : Type*} {p : ℍ → ℂ}
    {U : ι → Set ℂ} {hcover : ∀ w, ∃ i, w ∈ U i} {μ : ι → ℍ → ℂ} {F : ℍ → ℂ} {h : ι → ι → ℂ → ℂ}
    {i₀ : ι} {R : ℝ} (s : HolomorphicCousin.NegativeOneCocycleSolution U h i₀ R)
    (hdiff : ∀ i j z, p z ∈ U i → p z ∈ U j → μ i z - μ j z = F z * h i j (p z))
    (c : SpecialPeriods.MuTorsor.AffineCocycle)
    (hp : ∀ g z, p (SpecialPeriods.triangleGeometricRepresentation g z) = p z)
    (hμ : ∀ i, c.EquivariantOn (μ i) (p ⁻¹' U i))
    (hF : ∀ g z, F (SpecialPeriods.triangleGeometricRepresentation g z) = (c.scale g z : ℂ) * F z)
    (g : SpecialPeriods.TriangleGroup) (z : ℍ) :
    correctedGlue p U hcover μ F s (SpecialPeriods.triangleGeometricRepresentation g z) =
      c.fibreMap g z (correctedGlue p U hcover μ F s z) := by
  obtain ⟨i, hi⟩ := hcover (p z)
  have hig : p (SpecialPeriods.triangleGeometricRepresentation g z) ∈ U i := by rwa [hp g z]
  rw [correctedGlue_eq s hdiff hig, correctedGlue_eq s hdiff hi, hp g z, hμ i g z hi, hF g z]
  simp only [SpecialPeriods.MuTorsor.AffineCocycle.fibreMap]
  ring

private theorem SpecialPeriods.MuTorsor.Gluing.correctedGlue_cusp {X ι : Type*} {p : X → ℂ}
    {U : ι → Set ℂ} {hcover : ∀ w, ∃ i, w ∈ U i} {μ : ι → X → ℂ} {F : X → ℂ} {h : ι → ι → ℂ → ℂ}
    {i₀ : ι} {R : ℝ} (s : HolomorphicCousin.NegativeOneCocycleSolution U h i₀ R)
    (hdiff : ∀ i j z, p z ∈ U i → p z ∈ U j → μ i z - μ j z = F z * h i j (p z))
    (hRU : (Metric.ball (0 : ℂ) R)ᶜ ⊆ U i₀) {W : Set X} (hμ₀ : ∀ z ∈ W, μ i₀ z = 0) {z : X}
    (hz : z ∈ W) (hlarge : R < ‖p z‖) :
    correctedGlue p U hcover μ F s z = -F z * (p z)⁻¹ * s.infinityPart (p z)⁻¹ := by
  have hzU : p z ∈ U i₀ :=
    hRU
      (by
        simpa only [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hlarge.le)
  rw [correctedGlue_eq s hdiff hzU, hμ₀ z hz, s.atInfinity (p z) hlarge]
  ring

private theorem SpecialPeriods.MuTorsor.Gluing.exists_corrected_gluing {ι : Type*} {p : ℍ → ℂ}
    (hp : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω p) (hps : Function.Surjective p) {U : ι → Set ℂ}
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ w, ∃ i, w ∈ U i) {μ : ι → ℍ → ℂ}
    (hμ : ∀ i, ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (μ i) (p ⁻¹' U i)) {F : ℍ → ℂ}
    (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) {h : ι → ι → ℂ → ℂ}
    (hh : ∀ i j, AnalyticOnNhd ℂ (h i j) (U i ∩ U j))
    (hq : ∀ i j z, p z ∈ U i → p z ∈ U j → h i j (p z) = (μ i z - μ j z) / F z)
    (hz : ∀ i j z, p z ∈ U i → p z ∈ U j → F z = 0 → μ i z = μ j z) (i₀ : ι) {R : ℝ} (hR : 0 < R)
    (hRU : (Metric.ball (0 : ℂ) R)ᶜ ⊆ U i₀) :
    ∃ s : HolomorphicCousin.NegativeOneCocycleSolution U h i₀ R,
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (correctedGlue p U hcover μ F s) ∧
        ∀ i,
          Set.EqOn (correctedGlue p U hcover μ F s) (fun z => μ i z - F z * s.localPart i (p z))
            (p ⁻¹' U i) := by
  obtain ⟨s⟩ :=
    HolomorphicCousin.exists_negativeOne_holomorphic_cocycle_solution hU hcover hh
      (descended_quotient_cocycle hps hq) i₀ hR hRU
  have hd := difference_eq_mul_quotient hq hz
  exact ⟨s, correctedGlue_holomorphic hp hU hμ hF s hd, fun _ _ hi => correctedGlue_eq s hd hi⟩

private def SpecialPeriods.MuTorsor.CuspRegular (f : ℍ → ℂ) : Prop :=
  ∃ M : ℂ → ℂ,
    AnalyticAt ℂ M 0 ∧ ∀ᶠ z in UpperHalfPlane.atImInfty, f z = M (SpecialPeriods.Triangle.cuspQ z)

private theorem SpecialPeriods.MuTorsor.CuspRegular.sub {f g : ℍ → ℂ}
    (hf : SpecialPeriods.MuTorsor.CuspRegular f) (hg : SpecialPeriods.MuTorsor.CuspRegular g) :
    SpecialPeriods.MuTorsor.CuspRegular (f - g) := by
  obtain ⟨M, hM, hfM⟩ := hf
  obtain ⟨N, hN, hgN⟩ := hg
  refine ⟨M - N, hM.sub hN, ?_⟩
  filter_upwards [hfM, hgN] with z hfz hgz
  simp only [Pi.sub_apply, hfz, hgz]

private theorem
    SpecialPeriods.MuTorsor.factor_cusp_germ {ν F H : ℍ → ℂ} {v : ℂ → ℂ} (hνc : CuspRegular ν)
    (hv : AnalyticAt ℂ v 0) (hv0 : v 0 ≠ 0)
    (hF :
      ∀ᶠ z in UpperHalfPlane.atImInfty,
        F z = (SpecialPeriods.Triangle.cuspQ z)⁻¹ * v (SpecialPeriods.Triangle.cuspQ z))
    (hfac : ∀ z : ℍ, ν z = F z * H z) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g 0 ∧
        g 0 = 0 ∧ ∀ᶠ z in UpperHalfPlane.atImInfty, H z = g (SpecialPeriods.Triangle.cuspQ z) := by
  obtain ⟨M, hM, hνM⟩ := hνc
  refine ⟨fun q => q * M q / v q, (analyticAt_id.mul hM).div hv hv0, by simp, ?_⟩
  have hvne : ∀ᶠ z in UpperHalfPlane.atImInfty, v (SpecialPeriods.Triangle.cuspQ z) ≠ 0 :=
    (SpecialPeriods.Triangle.cuspQ_tendsto_atImInfty.mono_right nhdsWithin_le_nhds).eventually
      (hv.continuousAt.eventually_ne hv0)
  filter_upwards [hνM, hF, hvne] with z hνz hFz hvz
  apply (eq_div_iff hvz).mpr
  have he := hfac z
  rw [hνz, hFz] at he
  calc
    H z * v (SpecialPeriods.Triangle.cuspQ z) = v (SpecialPeriods.Triangle.cuspQ z) * H z :=
      mul_comm _ _
    _ =
        (SpecialPeriods.Triangle.cuspQ z * (SpecialPeriods.Triangle.cuspQ z)⁻¹) *
          (v (SpecialPeriods.Triangle.cuspQ z) * H z) := by
      rw [mul_inv_cancel₀ (SpecialPeriods.Triangle.cuspQ_ne_zero z), one_mul]
    _ =
        SpecialPeriods.Triangle.cuspQ z *
          ((SpecialPeriods.Triangle.cuspQ z)⁻¹ * v (SpecialPeriods.Triangle.cuspQ z) * H z) := by
      ring
    _ = SpecialPeriods.Triangle.cuspQ z * M (SpecialPeriods.Triangle.cuspQ z) := by rw [← he]

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.correctedGlue_cuspRegular
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) {F : ℍ → ℂ}
    {h : Cover.Index → Cover.Index → ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hRU : (Metric.ball (0 : ℂ) R)ᶜ ⊆ Cover.finitePatch π Cover.cuspIndex)
    (s :
      HolomorphicCousin.NegativeOneCocycleSolution (fun i => (Cover.finitePatch π i : Set ℂ)) h
        Cover.cuspIndex R)
    (hdiff :
      ∀ i j z,
        SpecialPeriods.BetaTorsor.finiteProjection π z ∈ Cover.finitePatch π i →
          SpecialPeriods.BetaTorsor.finiteProjection π z ∈ Cover.finitePatch π j →
            localSection hτ hτa i z - localSection hτ hτa j z =
              F z * h i j (SpecialPeriods.BetaTorsor.finiteProjection π z))
    (hFpole :
      ∃ v : ℂ → ℂ,
        AnalyticAt ℂ v 0 ∧
          v 0 ≠ 0 ∧
            ∀ᶠ z in UpperHalfPlane.atImInfty,
              F z = (SpecialPeriods.Triangle.cuspQ z)⁻¹ * v (SpecialPeriods.Triangle.cuspQ z)) :
    CuspRegular
      (Gluing.correctedGlue (SpecialPeriods.BetaTorsor.finiteProjection π)
        (fun i => (Cover.finitePatch π i : Set ℂ)) (Cover.exists_finitePatch π)
        (localSection hτ hτa) F s) := by
  obtain ⟨v, hv, _hv0, hFv⟩ := hFpole
  have hS : AnalyticAt ℂ s.infinityPart 0 :=
    s.infinity_analytic 0 (Metric.mem_ball_self (inv_pos.mpr hR))
  refine
    ⟨fun q => -v q * CuspCoordinates.tDivQ π q * s.infinityPart (CuspCoordinates.t π q),
      CuspCoordinates.analyticAt_correction π hπ hv hS, ?_⟩
  filter_upwards [hFv, CuspCoordinates.eventually_mem_horodisc SpecialPeriods.Triangle.width,
    CuspCoordinates.eventually_lt_norm_finiteProjection π hπ R,
    CuspCoordinates.t_cuspQ_eq_inv_finiteProjection π hπ] with z hFz hz hlarge ht
  rw [Gluing.correctedGlue_cusp s hdiff hRU (fun z hz => localSection_cusp hτ hτa z hz) hz hlarge,
    hFz, ← ht]
  have hc :
    -((SpecialPeriods.Triangle.cuspQ z)⁻¹ * v (SpecialPeriods.Triangle.cuspQ z)) *
        CuspCoordinates.t π (SpecialPeriods.Triangle.cuspQ z) =
      -v (SpecialPeriods.Triangle.cuspQ z) *
        CuspCoordinates.tDivQ π (SpecialPeriods.Triangle.cuspQ z) := by
    rw [CuspCoordinates.t_eq_mul_tDivQ π hπ]
    field_simp [SpecialPeriods.Triangle.cuspQ_ne_zero z]
  rw [hc]

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.exists_holomorphic_affine_cuspRegular
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (F : ℍ → ℂ)
    (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) (hFc : SpecialPeriods.MuGenerator.Homogeneous τ F)
    (hFzero :
      ∀ z,
        F z = 0 ↔
          SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterOne ∨
            SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterTwo)
    (hFpole :
      ∃ v : ℂ → ℂ,
        AnalyticAt ℂ v 0 ∧
          v 0 ≠ 0 ∧
            ∀ᶠ z in UpperHalfPlane.atImInfty,
              F z = (SpecialPeriods.Triangle.cuspQ z)⁻¹ * v (SpecialPeriods.Triangle.cuspQ z)) :
    ∃ μ : ℍ → ℂ,
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω μ ∧
        (∀ g z,
            μ (SpecialPeriods.triangleGeometricRepresentation g z) =
              (cocycle hτ hτa).fibreMap g z (μ z)) ∧
          (∀ z, μ (SpecialPeriods.Triangle.generatorOneSL • z) = (1 - μ z) / (τ z : ℂ)) ∧
            (∀ z, μ (SpecialPeriods.Triangle.generatorTwoSL • z) = 1 + μ z / (τ z : ℂ)) ∧
              CuspRegular μ := by
  let U : Cover.Index → Set ℂ := fun i => Cover.finitePatch π i
  let h := descendedOverlap hτ hτa F π hπ
  have hlocal :
    ∀ i,
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (localSection hτ hτa i)
        (SpecialPeriods.BetaTorsor.finiteProjection π ⁻¹' U i) := by
    intro i
    change
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (localSection hτ hτa i)
        (SpecialPeriods.BetaTorsor.finiteProjection π ⁻¹' (Cover.finitePatch π i : Set ℂ))
    rw [finiteProjection_preimage_patch π hπ]
    exact localSection_holomorphic hτ hτa i
  have hq :
    ∀ i j z,
      SpecialPeriods.BetaTorsor.finiteProjection π z ∈ U i →
        SpecialPeriods.BetaTorsor.finiteProjection π z ∈ U j →
          h i j (SpecialPeriods.BetaTorsor.finiteProjection π z) =
            (localSection hτ hτa i z - localSection hτ hτa j z) / F z :=
    descendedOverlap_projection hτ hτa F π hπ hFc
  have hz :
    ∀ i j z,
      SpecialPeriods.BetaTorsor.finiteProjection π z ∈ U i →
        SpecialPeriods.BetaTorsor.finiteProjection π z ∈ U j →
          F z = 0 → localSection hτ hτa i z = localSection hτ hτa j z := by
    intro i j z hi hj hzero
    exact
      localSection_eq_at_generator_zero hτ hτa F hFzero i j z
        ((finiteProjection_mem_patch π hπ i z).mp hi)
        ((finiteProjection_mem_patch π hπ j z).mp hj) hzero
  have hd := Gluing.difference_eq_mul_quotient hq hz
  obtain ⟨R, hR, hRU⟩ := Cover.finitePatch_cusp_contains_exterior π hπ
  obtain ⟨s, hs, _⟩ :=
    Gluing.exists_corrected_gluing (SpecialPeriods.BetaTorsor.finiteProjection_holomorphic π hπ)
      (SpecialPeriods.BetaTorsor.finiteProjection_surjective π hπ)
      (fun i => (Cover.finitePatch π i).isOpen) (Cover.exists_finitePatch π) hlocal hF
      (descendedOverlap_analytic hτ hτa F hFzero π hπ hF hFc) hq hz Cover.cuspIndex hR hRU
  let μ :=
    Gluing.correctedGlue (SpecialPeriods.BetaTorsor.finiteProjection π) U
      (Cover.exists_finitePatch π) (localSection hτ hτa) F s
  have hlocalLaw :
    ∀ i,
      (cocycle hτ hτa).EquivariantOn (localSection hτ hτa i)
        (SpecialPeriods.BetaTorsor.finiteProjection π ⁻¹' U i) := by
    intro i
    change
      (cocycle hτ hτa).EquivariantOn (localSection hτ hτa i)
        (SpecialPeriods.BetaTorsor.finiteProjection π ⁻¹' (Cover.finitePatch π i : Set ℂ))
    rw [finiteProjection_preimage_patch π hπ]
    exact localSection_equivariant hτ hτa i
  have hμ :
    ∀ g z,
      μ (SpecialPeriods.triangleGeometricRepresentation g z) =
        (cocycle hτ hτa).fibreMap g z (μ z) :=
    Gluing.correctedGlue_affine_law s hd (cocycle hτ hτa)
      (SpecialPeriods.BetaTorsor.finiteProjection_invariant π) hlocalLaw
      (homogeneous_scale_law hτ hτa hFc)
  refine ⟨μ, hs, hμ, ?_, ?_, ?_⟩
  · intro z
    simpa only [SpecialPeriods.triangleGeometricRepresentation_generator₁_apply,
      cocycle_fibreMap_generator₁] using hμ SpecialPeriods.triangleGenerator₁ z
  · intro z
    simpa only [SpecialPeriods.triangleGeometricRepresentation_generator₂_apply,
      cocycle_fibreMap_generator₂] using hμ SpecialPeriods.triangleGenerator₂ z
  · exact correctedGlue_cuspRegular π hπ hτ hτa hR hRU s hd hFpole

private theorem SpecialPeriods.MuTorsor.Division.quotient_invariant {τ : ℍ → ℍ} {ν F : ℍ → ℂ}
    (hν₁ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorOneSL • z) = -ν z / (τ z : ℂ))
    (hν₂ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorTwoSL • z) = ν z / (τ z : ℂ))
    (hF₁ : ∀ z : ℍ, F (SpecialPeriods.Triangle.generatorOneSL • z) = -F z / (τ z : ℂ))
    (hF₂ : ∀ z : ℍ, F (SpecialPeriods.Triangle.generatorTwoSL • z) = F z / (τ z : ℂ))
    (g : SpecialPeriods.TriangleGroup) (z : ℍ) :
    ν (SpecialPeriods.triangleGeometricRepresentation g z) /
        F (SpecialPeriods.triangleGeometricRepresentation g z) =
      ν z / F z := by
  apply SpecialPeriods.MuGenerator.triangle_invariant_of_generators (fun w => ν w / F w) _ _ g z
  · intro w
    rw [hν₁, hF₁, div_div_div_cancel_right₀ (τ w).ne_zero, neg_div_neg_eq]
  · intro w
    rw [hν₂, hF₂, div_div_div_cancel_right₀ (τ w).ne_zero]

private theorem SpecialPeriods.MuTorsor.Division.zero_invariant {τ : ℍ → ℍ} {ν : ℍ → ℂ}
    (hν₁ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorOneSL • z) = -ν z / (τ z : ℂ))
    (hν₂ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorTwoSL • z) = ν z / (τ z : ℂ))
    (g : SpecialPeriods.TriangleGroup) (z : ℍ) :
    ν (SpecialPeriods.triangleGeometricRepresentation g z) = 0 ↔ ν z = 0 := by
  have h := quotient_invariant hν₁ hν₂ hν₁ hν₂ g z
  have hz :
    ν (SpecialPeriods.triangleGeometricRepresentation g z) /
          ν (SpecialPeriods.triangleGeometricRepresentation g z) =
        0 ↔
      ν z / ν z = 0 := by rw [h]
  simpa only [div_eq_zero_iff, or_self] using hz

private theorem SpecialPeriods.MuTorsor.Division.zero_of_centerOneOrbit {τ : ℍ → ℍ} {ν : ℍ → ℂ}
    (hν₁ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorOneSL • z) = -ν z / (τ z : ℂ))
    (hν₂ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorTwoSL • z) = ν z / (τ z : ℂ)) {z : ℍ}
    (hz : SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterOne) :
    ν z = 0 := by
  obtain ⟨g, hg⟩ :=
    (SpecialPeriods.triangleOrbitProjection_eq_iff z SpecialPeriods.Triangle.centerOne).mp hz
  rw [← hg]
  exact
    (zero_invariant hν₁ hν₂ g SpecialPeriods.Triangle.centerOne).mpr
      (SpecialPeriods.MuGenerator.homogeneous_centerOne_eq_zero hν₁)

private theorem SpecialPeriods.MuTorsor.Division.zero_of_centerTwoOrbit {τ : ℍ → ℍ} {ν : ℍ → ℂ}
    (hν₁ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorOneSL • z) = -ν z / (τ z : ℂ))
    (hν₂ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorTwoSL • z) = ν z / (τ z : ℂ)) {z : ℍ}
    (hz : SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterTwo) :
    ν z = 0 := by
  obtain ⟨g, hg⟩ :=
    (SpecialPeriods.triangleOrbitProjection_eq_iff z SpecialPeriods.Triangle.centerTwo).mp hz
  rw [← hg]
  exact
    (zero_invariant hν₁ hν₂ g SpecialPeriods.Triangle.centerTwo).mpr
      (SpecialPeriods.MuGenerator.homogeneous_centerTwo_eq_zero hν₂)

private theorem SpecialPeriods.MuTorsor.Division.zero_of_ellipticOrbit {τ : ℍ → ℍ} {ν : ℍ → ℂ}
    (hν₁ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorOneSL • z) = -ν z / (τ z : ℂ))
    (hν₂ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorTwoSL • z) = ν z / (τ z : ℂ)) {z : ℍ}
    (hz :
      SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterOne ∨
        SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterTwo) :
    ν z = 0 :=
  hz.elim (zero_of_centerOneOrbit hν₁ hν₂) (zero_of_centerTwoOrbit hν₁ hν₂)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.MuTorsor.Division.ellipticNeighborhood_projection_eq_iff
    (j : Elliptic.Kind) (z : ℍ) (hz : z ∈ SpecialPeriods.Triangle.ellipticNeighborhood j) :
    SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.Triangle.ellipticOrbitCenter j ↔
      z = SpecialPeriods.Triangle.ellipticCenter j := by
  constructor
  · intro he
    obtain ⟨g, hg⟩ :=
      (SpecialPeriods.triangleOrbitProjection_eq_iff z
            (SpecialPeriods.Triangle.ellipticCenter j)).mp
        he
    have hr : g ∈ SpecialPeriods.Triangle.ellipticStabilizer j :=
      SpecialPeriods.Triangle.ellipticNeighborhood_return j g
        ⟨z,
          ⟨SpecialPeriods.Triangle.ellipticCenter j,
            SpecialPeriods.Triangle.ellipticCenter_mem_neighborhood j, hg⟩,
          hz⟩
    have hfix :
      SpecialPeriods.triangleGeometricRepresentation g
          (SpecialPeriods.Triangle.ellipticCenter j) =
        SpecialPeriods.Triangle.ellipticCenter j :=
      hr
    exact hg.symm.trans hfix
  · rintro rfl
    rfl

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.MuTorsor.Division.ellipticNeighborhood_projection_ne_centers
    (j : Elliptic.Kind) (z : ℍ) (hz : z ∈ SpecialPeriods.Triangle.ellipticNeighborhood j)
    (hne : z ≠ SpecialPeriods.Triangle.ellipticCenter j) :
    SpecialPeriods.triangleOrbitProjection z ≠ SpecialPeriods.triangleOrbitCenterOne ∧
      SpecialPeriods.triangleOrbitProjection z ≠ SpecialPeriods.triangleOrbitCenterTwo := by
  have hself :
    SpecialPeriods.triangleOrbitProjection z ≠ SpecialPeriods.Triangle.ellipticOrbitCenter j :=
    fun h => hne ((ellipticNeighborhood_projection_eq_iff j z hz).mp h)
  have hother := SpecialPeriods.Triangle.ellipticNeighborhood_avoids_other j z hz
  cases j
  · exact ⟨hself, hother⟩
  · exact ⟨hother, hself⟩

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private def SpecialPeriods.MuTorsor.Division.completedQuotient (ν F : ℍ → ℂ) (v : Elliptic.Kind → ℂ)
    (z : ℍ) : ℂ := by
  classical
    exact
    if SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterOne then
      v .three
    else
      if SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterTwo then
        v .four
      else ν z / F z

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.MuTorsor.Division.completedQuotient_center (ν F : ℍ → ℂ)
    (v : Elliptic.Kind → ℂ) (j : Elliptic.Kind) :
    completedQuotient ν F v (SpecialPeriods.Triangle.ellipticCenter j) = v j := by
  cases j
  · simp only [SpecialPeriods.Triangle.ellipticCenter, completedQuotient,
      SpecialPeriods.triangleOrbitCenterOne, ite_true]
  · have hne :
      SpecialPeriods.triangleOrbitProjection SpecialPeriods.Triangle.centerTwo ≠
        SpecialPeriods.triangleOrbitCenterOne :=
      SpecialPeriods.triangleOrbitCenterOne_ne_centerTwo.symm
    simp only [SpecialPeriods.Triangle.ellipticCenter, completedQuotient, hne, ite_false,
      SpecialPeriods.triangleOrbitCenterTwo, ite_true]

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.MuTorsor.Division.completedQuotient_eq_div (ν F : ℍ → ℂ)
    (v : Elliptic.Kind → ℂ) (z : ℍ)
    (h₁ : SpecialPeriods.triangleOrbitProjection z ≠ SpecialPeriods.triangleOrbitCenterOne)
    (h₂ : SpecialPeriods.triangleOrbitProjection z ≠ SpecialPeriods.triangleOrbitCenterTwo) :
    completedQuotient ν F v z = ν z / F z := by simp only [completedQuotient, h₁, h₂, ite_false]

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.MuTorsor.Division.completedQuotient_eventuallyEq_germ {ν F : ℍ → ℂ}
    (hFzero :
      ∀ z : ℍ,
        F z = 0 ↔
          SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterOne ∨
            SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterTwo)
    (v : Elliptic.Kind → ℂ) (j : Elliptic.Kind) (h : ℂ → ℂ)
    (hv : v j = h (SpecialPeriods.Triangle.ellipticCenter j : ℂ))
    (hfactor :
      (ν ∘ UpperHalfPlane.ofComplex) =ᶠ[𝓝 (SpecialPeriods.Triangle.ellipticCenter j : ℂ)] fun w =>
        (F ∘ UpperHalfPlane.ofComplex) w * h w) :
    completedQuotient ν F v =ᶠ[𝓝 (SpecialPeriods.Triangle.ellipticCenter j)] fun z => h (z : ℂ) :=
  by
  have he : ∀ᶠ z : ℍ in 𝓝 (SpecialPeriods.Triangle.ellipticCenter j), ν z = F z * h (z : ℂ) := by
    simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using
      UpperHalfPlane.continuous_coe.continuousAt.eventually hfactor
  filter_upwards [he, SpecialPeriods.Triangle.ellipticNeighborhood_mem_nhds j] with z hez hzn
  by_cases hz : z = SpecialPeriods.Triangle.ellipticCenter j
  · subst z
    exact (completedQuotient_center ν F v j).trans hv
  · obtain ⟨h₁, h₂⟩ := ellipticNeighborhood_projection_ne_centers j z hzn hz
    have hFz : F z ≠ 0 := fun hzero => (hFzero z).mp hzero |>.elim h₁ h₂
    rw [completedQuotient_eq_div ν F v z h₁ h₂, hez]
    exact mul_div_cancel_left₀ _ hFz

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.MuTorsor.Division.completedQuotient_contMDiffAt_center {ν F : ℍ → ℂ}
    (hFzero :
      ∀ z : ℍ,
        F z = 0 ↔
          SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterOne ∨
            SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterTwo)
    (v : Elliptic.Kind → ℂ) (j : Elliptic.Kind) (h : ℂ → ℂ)
    (hh : AnalyticAt ℂ h (SpecialPeriods.Triangle.ellipticCenter j : ℂ))
    (hv : v j = h (SpecialPeriods.Triangle.ellipticCenter j : ℂ))
    (hfactor :
      (ν ∘ UpperHalfPlane.ofComplex) =ᶠ[𝓝 (SpecialPeriods.Triangle.ellipticCenter j : ℂ)] fun w =>
        (F ∘ UpperHalfPlane.ofComplex) w * h w) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (completedQuotient ν F v)
      (SpecialPeriods.Triangle.ellipticCenter j) := by
  exact
    (hh.contDiffAt.contMDiffAt.comp _ (UpperHalfPlane.contMDiff_coe _)).congr_of_eventuallyEq
      (completedQuotient_eventuallyEq_germ hFzero v j h hv hfactor)

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem
    SpecialPeriods.MuTorsor.Division.completedQuotient_contMDiffAt_of_ne_zero {ν F : ℍ → ℂ}
    (hν : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ν) (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hFzero :
      ∀ z : ℍ,
        F z = 0 ↔
          SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterOne ∨
            SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterTwo)
    (v : Elliptic.Kind → ℂ) (z : ℍ) (hz : F z ≠ 0) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (completedQuotient ν F v) z := by
  apply ((hν z).div₀ (hF z) hz).congr_of_eventuallyEq
  filter_upwards [(hF z).continuousAt.eventually_ne hz] with w hw
  have hn :
    ¬(SpecialPeriods.triangleOrbitProjection w = SpecialPeriods.triangleOrbitCenterOne ∨
        SpecialPeriods.triangleOrbitProjection w = SpecialPeriods.triangleOrbitCenterTwo) :=
    fun he => hw ((hFzero w).mpr he)
  exact completedQuotient_eq_div ν F v w (fun h => hn (.inl h)) (fun h => hn (.inr h))

attribute [local instance] SpecialPeriods.triangleGeometricAction in
private theorem SpecialPeriods.MuTorsor.Division.contMDiffAt_orbit {H : ℍ → ℂ}
    (hH :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z : ℍ, H (SpecialPeriods.triangleGeometricRepresentation g z) = H z)
    {a : ℍ} (ha : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω H a) (g : SpecialPeriods.TriangleGroup) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω H (SpecialPeriods.triangleGeometricRepresentation g a) := by
  have hi :
    SpecialPeriods.triangleGeometricRepresentation g⁻¹
        (SpecialPeriods.triangleGeometricRepresentation g a) =
      a := by
    rw [map_inv]
    exact (SpecialPeriods.triangleGeometricRepresentation g).symm_apply_apply a
  have hh :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω H
      (SpecialPeriods.triangleGeometricRepresentation g⁻¹
        (SpecialPeriods.triangleGeometricRepresentation g a)) :=
    hi.symm ▸ ha
  apply
    (hh.comp _
        (SpecialPeriods.triangleGeometricRepresentation_holomorphic g⁻¹ _)).congr_of_eventuallyEq
  filter_upwards with z
  exact (hH g⁻¹ z).symm

private theorem SpecialPeriods.MuTorsor.Division.completedQuotient_invariant {ν F : ℍ → ℂ}
    (v : Elliptic.Kind → ℂ)
    (hinv :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z : ℍ,
          ν (SpecialPeriods.triangleGeometricRepresentation g z) /
              F (SpecialPeriods.triangleGeometricRepresentation g z) =
            ν z / F z)
    (g : SpecialPeriods.TriangleGroup) (z : ℍ) :
    completedQuotient ν F v (SpecialPeriods.triangleGeometricRepresentation g z) =
      completedQuotient ν F v z := by
  unfold completedQuotient
  rw [SpecialPeriods.triangleOrbitProjection_smul g z, hinv g z]

private theorem SpecialPeriods.MuTorsor.Division.completedQuotient_factorization {ν F : ℍ → ℂ}
    (hFzero :
      ∀ z : ℍ,
        F z = 0 ↔
          SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterOne ∨
            SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterTwo)
    (hνzero : ∀ z : ℍ, F z = 0 → ν z = 0) (v : Elliptic.Kind → ℂ) (z : ℍ) :
    ν z = F z * completedQuotient ν F v z := by
  by_cases hz : F z = 0
  · rw [hz, hνzero z hz, MulZeroClass.zero_mul]
  · have hn :
      ¬(SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterOne ∨
          SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterTwo) :=
      fun he => hz ((hFzero z).mpr he)
    rw [completedQuotient_eq_div ν F v z (fun h => hn (.inl h)) (fun h => hn (.inr h))]
    exact (mul_div_cancel₀ (ν z) hz).symm.trans (by ring)

private theorem SpecialPeriods.MuTorsor.Division.completedQuotient_holomorphic {ν F : ℍ → ℂ}
    (hν : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ν) (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hFzero :
      ∀ z : ℍ,
        F z = 0 ↔
          SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterOne ∨
            SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterTwo)
    (v : Elliptic.Kind → ℂ)
    (hinv :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z : ℍ,
          completedQuotient ν F v (SpecialPeriods.triangleGeometricRepresentation g z) =
            completedQuotient ν F v z)
    (hcenter :
      ∀ j : Elliptic.Kind,
        ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (completedQuotient ν F v)
          (SpecialPeriods.Triangle.ellipticCenter j)) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (completedQuotient ν F v) := by
  intro z
  by_cases hz : F z = 0
  · rcases (hFzero z).mp hz with h₁ | h₂
    · obtain ⟨g, hg⟩ :=
        (SpecialPeriods.triangleOrbitProjection_eq_iff z SpecialPeriods.Triangle.centerOne).mp h₁
      rw [← hg]
      exact contMDiffAt_orbit hinv (hcenter .three) g
    · obtain ⟨g, hg⟩ :=
        (SpecialPeriods.triangleOrbitProjection_eq_iff z SpecialPeriods.Triangle.centerTwo).mp h₂
      rw [← hg]
      exact contMDiffAt_orbit hinv (hcenter .four) g
  · exact completedQuotient_contMDiffAt_of_ne_zero hν hF hFzero v z hz

private theorem SpecialPeriods.MuTorsor.Division.exists_holomorphic_invariant_factor {τ : ℍ → ℍ}
    {ν F : ℍ → ℂ} (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hτc : SpecialPeriods.TauCovariant τ)
    (hν : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ν)
    (hν₁ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorOneSL • z) = -ν z / (τ z : ℂ))
    (hν₂ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorTwoSL • z) = ν z / (τ z : ℂ))
    (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hF₁ : ∀ z : ℍ, F (SpecialPeriods.Triangle.generatorOneSL • z) = -F z / (τ z : ℂ))
    (hF₂ : ∀ z : ℍ, F (SpecialPeriods.Triangle.generatorTwoSL • z) = F z / (τ z : ℂ))
    (hFzero :
      ∀ z : ℍ,
        F z = 0 ↔
          SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterOne ∨
            SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterTwo)
    (hForder₁ :
      analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (SpecialPeriods.Triangle.centerOne : ℂ) = 2)
    (hForder₂ :
      analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (SpecialPeriods.Triangle.centerTwo : ℂ) =
        1) :
    ∃ H : ℍ → ℂ,
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω H ∧
        (∀ g : SpecialPeriods.TriangleGroup,
            ∀ z : ℍ, H (SpecialPeriods.triangleGeometricRepresentation g z) = H z) ∧
          ∀ z : ℍ, ν z = F z * H z := by
  obtain ⟨h₁, hh₁, he₁⟩ :=
    SpecialPeriods.MuGenerator.exists_division_at_centerOne hτ hτc hν hν₁ hF hForder₁
  obtain ⟨h₂, hh₂, he₂⟩ :=
    SpecialPeriods.MuGenerator.exists_division_at_centerTwo hν hν₂ hF hForder₂
  let v : Elliptic.Kind → ℂ
    | .three => h₁ (SpecialPeriods.Triangle.centerOne : ℂ)
    | .four => h₂ (SpecialPeriods.Triangle.centerTwo : ℂ)
  have hinv := completedQuotient_invariant v (quotient_invariant hν₁ hν₂ hF₁ hF₂)
  refine ⟨completedQuotient ν F v, ?_, hinv, ?_⟩
  · apply completedQuotient_holomorphic hν hF hFzero v hinv
    intro j
    cases j
    · exact completedQuotient_contMDiffAt_center hFzero v .three h₁ hh₁ rfl he₁
    · exact completedQuotient_contMDiffAt_center hFzero v .four h₂ hh₂ rfl he₂
  · apply completedQuotient_factorization hFzero
    intro z hz
    exact zero_of_ellipticOrbit hν₁ hν₂ ((hFzero z).mp hz)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.instIsManifold2 :
    IsManifold 𝓘(ℂ) ω SpecialPeriods.TriangleOrbitSpace :=
  SpecialPeriods.triangleOrbit_isManifold

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.MuTorsor.instIsManifold2 in
private theorem SpecialPeriods.MuTorsor.instIsManifold3 :
    IsManifold 𝓘(ℂ) ω SpecialPeriods.TriangleCompactifiedOrbitSpace :=
  SpecialPeriods.triangleCompactified_isManifold

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.MuTorsor.instIsManifold2
    SpecialPeriods.MuTorsor.instIsManifold3 in
private def
    SpecialPeriods.MuTorsor.compactExtension (f : SpecialPeriods.TriangleOrbitSpace → ℂ) (c : ℂ) :
    SpecialPeriods.TriangleCompactifiedOrbitSpace → ℂ :=
  OnePoint.rec c f

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.MuTorsor.instIsManifold2
    SpecialPeriods.MuTorsor.instIsManifold3 in
private theorem SpecialPeriods.MuTorsor.compactExtension_holomorphicAt_openInclusion
    (f : SpecialPeriods.TriangleOrbitSpace → ℂ) (c : ℂ) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (q : SpecialPeriods.TriangleOrbitSpace) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (compactExtension f c) (SpecialPeriods.triangleOpenInclusion q) := by
  have hp := SpecialPeriods.triangleOpenInclusion_isLocalDiffeomorph q
  have hcomp :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (compactExtension f c ∘ SpecialPeriods.triangleOpenInclusion) q :=
    hf q
  have h :=
    hcomp.comp_of_eq hp.localInverse_contMDiffAt
      (hp.localInverse_left_inv hp.localInverse_mem_target)
  apply h.congr_of_eventuallyEq
  filter_upwards [hp.localInverse_eventuallyEq_right] with x hx
  change
    compactExtension f c x =
      compactExtension f c (SpecialPeriods.triangleOpenInclusion (hp.localInverse x))
  rw [show SpecialPeriods.triangleOpenInclusion (hp.localInverse x) = x from hx]

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.MuTorsor.instIsManifold2
    SpecialPeriods.MuTorsor.instIsManifold3 in
private theorem SpecialPeriods.MuTorsor.compactExtension_eventuallyEq_cuspChart
    (f : SpecialPeriods.TriangleOrbitSpace → ℂ) (g : ℂ → ℂ) (Y : ℝ)
    (h :
      ∀ q ∈ SpecialPeriods.Triangle.cuspImage Y,
        f q =
          g
            (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl
              (SpecialPeriods.triangleOpenInclusion q))) :
    compactExtension f (g 0) =ᶠ[𝓝 SpecialPeriods.triangleCuspPoint]
      g ∘ SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl := by
  filter_upwards [SpecialPeriods.Triangle.cuspNeighborhood_mem_nhds Y] with x hx
  induction x using OnePoint.rec with
  |
    infty =>
    change
      g 0 =
        g
          (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl
            SpecialPeriods.triangleCuspPoint)
    rw [SpecialPeriods.Triangle.cuspFullChart_cuspPoint]
  | coe
    q =>
    change
      f q =
        g
          (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl
            (SpecialPeriods.triangleOpenInclusion q))
    exact h q ((SpecialPeriods.Triangle.openInclusion_mem_cuspNeighborhood Y q).mp hx)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.MuTorsor.instIsManifold2
    SpecialPeriods.MuTorsor.instIsManifold3 in
private theorem SpecialPeriods.MuTorsor.compactExtension_holomorphicAt_cusp_of_cuspImage
    (f : SpecialPeriods.TriangleOrbitSpace → ℂ) (g : ℂ → ℂ) (Y : ℝ) (hg : AnalyticAt ℂ g 0)
    (h :
      ∀ q ∈ SpecialPeriods.Triangle.cuspImage Y,
        f q =
          g
            (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl
              (SpecialPeriods.triangleOpenInclusion q))) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (compactExtension f (g 0)) SpecialPeriods.triangleCuspPoint := by
  have hc :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
      (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl)
      SpecialPeriods.triangleCuspPoint :=
    SpecialPeriods.triangleCompactified_cuspChart_holomorphic.contMDiffAt
      (SpecialPeriods.Triangle.cuspNeighborhood_mem_nhds SpecialPeriods.Triangle.width)
  have hgc :=
    hg.contDiffAt.contMDiffAt.comp_of_eq hc
      (SpecialPeriods.Triangle.cuspFullChart_cuspPoint SpecialPeriods.Triangle.width le_rfl)
  exact hgc.congr_of_eventuallyEq (compactExtension_eventuallyEq_cuspChart f g Y h)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.MuTorsor.instIsManifold2
    SpecialPeriods.MuTorsor.instIsManifold3 in
private theorem SpecialPeriods.MuTorsor.compactExtension_holomorphic_of_cuspImage
    (f : SpecialPeriods.TriangleOrbitSpace → ℂ) (g : ℂ → ℂ) (Y : ℝ) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hg : AnalyticAt ℂ g 0)
    (h :
      ∀ q ∈ SpecialPeriods.Triangle.cuspImage Y,
        f q =
          g
            (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl
              (SpecialPeriods.triangleOpenInclusion q))) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (compactExtension f (g 0)) := by
  intro x
  induction x using OnePoint.rec with
  | infty => exact compactExtension_holomorphicAt_cusp_of_cuspImage f g Y hg h
  | coe q => exact compactExtension_holomorphicAt_openInclusion f (g 0) hf q

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
attribute [local instance] SpecialPeriods.MuTorsor.instIsManifold2
    SpecialPeriods.MuTorsor.instIsManifold3 in
private theorem
    SpecialPeriods.MuTorsor.eq_const_of_cuspImage (f : SpecialPeriods.TriangleOrbitSpace → ℂ)
    (g : ℂ → ℂ) (Y : ℝ) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hg : AnalyticAt ℂ g 0)
    (h :
      ∀ q ∈ SpecialPeriods.Triangle.cuspImage Y,
        f q =
          g
            (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl
              (SpecialPeriods.triangleOpenInclusion q))) :
    ∀ q, f q = g 0 := by
  let := SpecialPeriods.triangleCompactifiedOrbitSpace_compact
  let := SpecialPeriods.triangleCompactifiedOrbitSpace_connected
  have he := compactExtension_holomorphic_of_cuspImage f g Y hf hg h
  intro q
  exact
    (he.mdifferentiable (by simp)).apply_eq_of_compactSpace
      (SpecialPeriods.triangleOpenInclusion q) SpecialPeriods.triangleCuspPoint

private theorem SpecialPeriods.MuTorsor.exists_cuspImage_eq_of_eventually_atImInfty
    {f : SpecialPeriods.TriangleOrbitSpace → ℂ} {g : ℂ → ℂ}
    (h :
      ∀ᶠ z in UpperHalfPlane.atImInfty,
        f (SpecialPeriods.triangleOrbitProjection z) = g (SpecialPeriods.Triangle.cuspQ z)) :
    ∃ Y : ℝ,
      SpecialPeriods.Triangle.width ≤ Y ∧
        ∀ q ∈ SpecialPeriods.Triangle.cuspImage Y,
          f q =
            g
              (SpecialPeriods.Triangle.cuspFullChart SpecialPeriods.Triangle.width le_rfl
                (SpecialPeriods.triangleOpenInclusion q)) := by
  obtain ⟨A, hA⟩ := (UpperHalfPlane.atImInfty_mem _).mp h
  refine ⟨Max.max SpecialPeriods.Triangle.width A, le_max_left _ _, ?_⟩
  intro q hq
  obtain ⟨z, hz, rfl⟩ := (SpecialPeriods.Triangle.mem_cuspImage _ _).mp hq
  have hzwidth : z ∈ SpecialPeriods.Triangle.horodisc SpecialPeriods.Triangle.width :=
    (le_max_left _ _).trans_lt hz
  rw [SpecialPeriods.Triangle.cuspFullChart_mk SpecialPeriods.Triangle.width le_rfl ⟨z, hzwidth⟩]
  exact hA z ((le_max_right _ _).trans hz.le)

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.eq_const_of_eventually_cusp
    (f : SpecialPeriods.TriangleOrbitSpace → ℂ) (g : ℂ → ℂ) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hg : AnalyticAt ℂ g 0)
    (h :
      ∀ᶠ z in UpperHalfPlane.atImInfty,
        f (SpecialPeriods.triangleOrbitProjection z) = g (SpecialPeriods.Triangle.cuspQ z)) :
    ∀ q, f q = g 0 := by
  obtain ⟨Y, _, hY⟩ := exists_cuspImage_eq_of_eventually_atImInfty h
  exact eq_const_of_cuspImage f g Y hf hg hY

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace
    SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.eq_zero_of_eventually_cusp
    (f : SpecialPeriods.TriangleOrbitSpace → ℂ) (g : ℂ → ℂ) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0)
    (h :
      ∀ᶠ z in UpperHalfPlane.atImInfty,
        f (SpecialPeriods.triangleOrbitProjection z) = g (SpecialPeriods.Triangle.cuspQ z)) :
    f = 0 := by
  funext q
  exact (eq_const_of_eventually_cusp f g hf hg h q).trans hg0

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
private theorem SpecialPeriods.MuTorsor.descend_top_project {H : ℍ → ℂ}
    (hInv :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z : ℍ, H (SpecialPeriods.triangleGeometricRepresentation g z) = H z)
    (z : ℍ) : descend ⊤ H (SpecialPeriods.triangleOrbitProjection z) = H z := by
  apply descend_project ⊤ H
  · intro g w
    rfl
  · intro g w _
    exact hInv g w
  · trivial

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
private theorem
    SpecialPeriods.MuTorsor.descend_top_holomorphic {H : ℍ → ℂ} (hH : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω H)
    (hInv :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z : ℍ, H (SpecialPeriods.triangleGeometricRepresentation g z) = H z) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (descend ⊤ H) := by
  intro q
  apply descend_holomorphicAt ⊤ H
  · intro g w
    rfl
  · intro g w _
    exact hInv g w
  · exact hH.contMDiffOn
  · exact ⟨orbitRepresentative q, trivial, project_orbitRepresentative q⟩

attribute [local instance] SpecialPeriods.triangleOrbitChartedSpace in
private theorem SpecialPeriods.MuTorsor.invariant_eq_zero_of_eventually_cusp {H : ℍ → ℂ}
    (hH : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω H)
    (hInv :
      ∀ g : SpecialPeriods.TriangleGroup,
        ∀ z : ℍ, H (SpecialPeriods.triangleGeometricRepresentation g z) = H z)
    {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0)
    (he : ∀ᶠ z in UpperHalfPlane.atImInfty, H z = g (SpecialPeriods.Triangle.cuspQ z)) : H = 0 := by
  have hd : descend ⊤ H = 0 := by
    apply eq_zero_of_eventually_cusp (descend ⊤ H) g (descend_top_holomorphic hH hInv) hg hg0
    filter_upwards [he] with z hz
    exact (descend_top_project hInv z).trans hz
  funext z
  exact
    (descend_top_project hInv z).symm.trans
      (congrFun hd (SpecialPeriods.triangleOrbitProjection z))

private theorem SpecialPeriods.MuTorsor.homogeneous_eq_zero_of_cuspRegular {τ : ℍ → ℍ} {ν F : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hτc : SpecialPeriods.TauCovariant τ)
    (hν : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ν)
    (hν₁ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorOneSL • z) = -ν z / (τ z : ℂ))
    (hν₂ : ∀ z : ℍ, ν (SpecialPeriods.Triangle.generatorTwoSL • z) = ν z / (τ z : ℂ))
    (hνc : CuspRegular ν) (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hF₁ : ∀ z : ℍ, F (SpecialPeriods.Triangle.generatorOneSL • z) = -F z / (τ z : ℂ))
    (hF₂ : ∀ z : ℍ, F (SpecialPeriods.Triangle.generatorTwoSL • z) = F z / (τ z : ℂ))
    (hFzero :
      ∀ z : ℍ,
        F z = 0 ↔
          SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterOne ∨
            SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterTwo)
    (hForder₁ :
      analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (SpecialPeriods.Triangle.centerOne : ℂ) = 2)
    (hForder₂ :
      analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (SpecialPeriods.Triangle.centerTwo : ℂ) = 1)
    (hFcusp :
      ∃ v : ℂ → ℂ,
        AnalyticAt ℂ v 0 ∧
          v 0 ≠ 0 ∧
            ∀ᶠ z in UpperHalfPlane.atImInfty,
              F z = (SpecialPeriods.Triangle.cuspQ z)⁻¹ * v (SpecialPeriods.Triangle.cuspQ z)) :
    ν = 0 := by
  obtain ⟨H, hH, hInv, hfactor⟩ :=
    Division.exists_holomorphic_invariant_factor hτ hτc hν hν₁ hν₂ hF hF₁ hF₂ hFzero hForder₁
      hForder₂
  obtain ⟨v, hv, hv0, hFv⟩ := hFcusp
  obtain ⟨g, hg, hg0, hHg⟩ := factor_cusp_germ hνc hv hv0 hFv hfactor
  have hH0 : H = 0 := invariant_eq_zero_of_eventually_cusp hH hInv hg hg0 hHg
  funext z
  calc
    ν z = F z * H z := hfactor z
    _ = 0 := by simp only [hH0, Pi.zero_apply, MulZeroClass.mul_zero]

private theorem SpecialPeriods.MuTorsor.affine_sub_homogeneous {τ : ℍ → ℍ} {μ μ' : ℍ → ℂ}
    (hμ₁ : ∀ z : ℍ, μ (SpecialPeriods.Triangle.generatorOneSL • z) = (1 - μ z) / (τ z : ℂ))
    (hμ₂ : ∀ z : ℍ, μ (SpecialPeriods.Triangle.generatorTwoSL • z) = 1 + μ z / (τ z : ℂ))
    (hμ'₁ : ∀ z : ℍ, μ' (SpecialPeriods.Triangle.generatorOneSL • z) = (1 - μ' z) / (τ z : ℂ))
    (hμ'₂ : ∀ z : ℍ, μ' (SpecialPeriods.Triangle.generatorTwoSL • z) = 1 + μ' z / (τ z : ℂ)) :
    (∀ z : ℍ, (μ - μ') (SpecialPeriods.Triangle.generatorOneSL • z) = -(μ - μ') z / (τ z : ℂ)) ∧
      (∀ z : ℍ, (μ - μ') (SpecialPeriods.Triangle.generatorTwoSL • z) = (μ - μ') z / (τ z : ℂ)) :=
  by
  constructor
  · intro z
    simp only [Pi.sub_apply, hμ₁ z, hμ'₁ z]
    ring
  · intro z
    simp only [Pi.sub_apply, hμ₂ z, hμ'₂ z]
    ring

private theorem SpecialPeriods.MuTorsor.affine_eq_of_cuspRegular {τ : ℍ → ℍ} {μ μ' F : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hτc : SpecialPeriods.TauCovariant τ)
    (hμ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω μ) (hμ' : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω μ')
    (hμ₁ : ∀ z : ℍ, μ (SpecialPeriods.Triangle.generatorOneSL • z) = (1 - μ z) / (τ z : ℂ))
    (hμ₂ : ∀ z : ℍ, μ (SpecialPeriods.Triangle.generatorTwoSL • z) = 1 + μ z / (τ z : ℂ))
    (hμ'₁ : ∀ z : ℍ, μ' (SpecialPeriods.Triangle.generatorOneSL • z) = (1 - μ' z) / (τ z : ℂ))
    (hμ'₂ : ∀ z : ℍ, μ' (SpecialPeriods.Triangle.generatorTwoSL • z) = 1 + μ' z / (τ z : ℂ))
    (hμc : CuspRegular μ) (hμ'c : CuspRegular μ') (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hF₁ : ∀ z : ℍ, F (SpecialPeriods.Triangle.generatorOneSL • z) = -F z / (τ z : ℂ))
    (hF₂ : ∀ z : ℍ, F (SpecialPeriods.Triangle.generatorTwoSL • z) = F z / (τ z : ℂ))
    (hFzero :
      ∀ z : ℍ,
        F z = 0 ↔
          SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterOne ∨
            SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterTwo)
    (hForder₁ :
      analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (SpecialPeriods.Triangle.centerOne : ℂ) = 2)
    (hForder₂ :
      analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (SpecialPeriods.Triangle.centerTwo : ℂ) = 1)
    (hFcusp :
      ∃ v : ℂ → ℂ,
        AnalyticAt ℂ v 0 ∧
          v 0 ≠ 0 ∧
            ∀ᶠ z in UpperHalfPlane.atImInfty,
              F z = (SpecialPeriods.Triangle.cuspQ z)⁻¹ * v (SpecialPeriods.Triangle.cuspQ z)) :
    μ = μ' := by
  obtain ⟨hν₁, hν₂⟩ := affine_sub_homogeneous hμ₁ hμ₂ hμ'₁ hμ'₂
  exact
    sub_eq_zero.mp
      (homogeneous_eq_zero_of_cuspRegular hτ hτc (hμ.sub hμ') hν₁ hν₂ (hμc.sub hμ'c) hF hF₁ hF₂
        hFzero hForder₁ hForder₂ hFcusp)

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private structure SpecialPeriods.MuTorsor.IsSolution (τ : ℍ → ℍ) (μ : ℍ → ℂ) : Prop where
  holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω μ
  generatorOne : ∀ z : ℍ, μ (SpecialPeriods.Triangle.generatorOneSL • z) = (1 - μ z) / (τ z : ℂ)
  generatorTwo : ∀ z : ℍ, μ (SpecialPeriods.Triangle.generatorTwoSL • z) = 1 + μ z / (τ z : ℂ)
  cuspRegular : CuspRegular μ

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.exists_unique_solution_from_generator
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere)) {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (F : ℍ → ℂ)
    (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) (hFc : SpecialPeriods.MuGenerator.Homogeneous τ F)
    (hFzero :
      ∀ z : ℍ,
        F z = 0 ↔
          SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterOne ∨
            SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterTwo)
    (hForder₁ :
      analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (SpecialPeriods.Triangle.centerOne : ℂ) = 2)
    (hForder₂ :
      analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (SpecialPeriods.Triangle.centerTwo : ℂ) = 1)
    (hFcusp :
      ∃ v : ℂ → ℂ,
        AnalyticAt ℂ v 0 ∧
          v 0 ≠ 0 ∧
            ∀ᶠ z in UpperHalfPlane.atImInfty,
              F z = (SpecialPeriods.Triangle.cuspQ z)⁻¹ * v (SpecialPeriods.Triangle.cuspQ z)) :
    ∃! μ : ℍ → ℂ, IsSolution τ μ := by
  obtain ⟨μ, hμ, _, hμ₁, hμ₂, hμc⟩ :=
    exists_holomorphic_affine_cuspRegular π hπ hτ hτa F hF hFc hFzero hFcusp
  refine ⟨μ, ⟨hμ, hμ₁, hμ₂, hμc⟩, ?_⟩
  intro μ' hμ'
  exact
    affine_eq_of_cuspRegular hτa hτ hμ'.holomorphic hμ hμ'.generatorOne hμ'.generatorTwo hμ₁ hμ₂
      hμ'.cuspRegular hμc hF hFc.1 hFc.2 hFzero hForder₁ hForder₂ hFcusp

private theorem SpecialPeriods.MuGenerator.E₆_cuspFunction_zero :
    UpperHalfPlane.cuspFunction 1 ModularForm.E₆ 0 = 1 := by
  have h :=
    EisensteinSeries.E_qExpansion_coeff_zero (show 3 ≤ 6 by decide) (show Even 6 by decide)
  simpa [UpperHalfPlane.qExpansion_coeff] using h

private def SpecialPeriods.MuGenerator.cuspModularParameter (u : ℂ → ℂ) (t : ℂ) : ℂ :=
  t * u t

@[simp]
private theorem SpecialPeriods.MuGenerator.cuspModularParameter_zero (u : ℂ → ℂ) :
    cuspModularParameter u 0 = 0 := by simp [cuspModularParameter]

private theorem SpecialPeriods.MuGenerator.cuspModularParameter_analyticAt {u : ℂ → ℂ}
    (hu : AnalyticAt ℂ u 0) : AnalyticAt ℂ (cuspModularParameter u) 0 :=
  analyticAt_id.mul hu

private def SpecialPeriods.MuGenerator.cuspEisensteinFour (u : ℂ → ℂ) (t : ℂ) : ℂ :=
  UpperHalfPlane.cuspFunction 1 ModularForm.E₄ (cuspModularParameter u t)

private def SpecialPeriods.MuGenerator.cuspEisensteinSix (u : ℂ → ℂ) (t : ℂ) : ℂ :=
  UpperHalfPlane.cuspFunction 1 ModularForm.E₆ (cuspModularParameter u t)

private def SpecialPeriods.MuGenerator.cuspDiscriminantUnit (u : ℂ → ℂ) (t : ℂ) : ℂ :=
  u t * SpecialPeriods.discriminantUnit (cuspModularParameter u t)

@[simp]
private theorem SpecialPeriods.MuGenerator.cuspEisensteinFour_zero (u : ℂ → ℂ) :
    cuspEisensteinFour u 0 = 1 := by
  simp [cuspEisensteinFour, SpecialPeriods.E₄_cuspFunction_zero]

@[simp]
private theorem SpecialPeriods.MuGenerator.cuspEisensteinSix_zero (u : ℂ → ℂ) :
    cuspEisensteinSix u 0 = 1 := by simp [cuspEisensteinSix, E₆_cuspFunction_zero]

@[simp]
private theorem SpecialPeriods.MuGenerator.cuspDiscriminantUnit_zero (u : ℂ → ℂ) :
    cuspDiscriminantUnit u 0 = u 0 := by simp [cuspDiscriminantUnit]

private theorem SpecialPeriods.MuGenerator.cuspEisensteinFour_analyticAt {u : ℂ → ℂ}
    (hu : AnalyticAt ℂ u 0) : AnalyticAt ℂ (cuspEisensteinFour u) 0 := by
  have h :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 ModularForm.E₄) (cuspModularParameter u 0) := by
    rw [cuspModularParameter_zero]
    exact
      ModularFormClass.analyticAt_cuspFunction_zero ModularForm.E₄ zero_lt_one
        one_mem_strictPeriods_SL
  exact h.comp (cuspModularParameter_analyticAt hu)

private theorem SpecialPeriods.MuGenerator.cuspEisensteinSix_analyticAt {u : ℂ → ℂ}
    (hu : AnalyticAt ℂ u 0) : AnalyticAt ℂ (cuspEisensteinSix u) 0 := by
  have h :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 ModularForm.E₆) (cuspModularParameter u 0) := by
    rw [cuspModularParameter_zero]
    exact
      ModularFormClass.analyticAt_cuspFunction_zero ModularForm.E₆ zero_lt_one
        one_mem_strictPeriods_SL
  exact h.comp (cuspModularParameter_analyticAt hu)

private theorem SpecialPeriods.MuGenerator.cuspDiscriminantUnit_analyticAt {u : ℂ → ℂ}
    (hu : AnalyticAt ℂ u 0) : AnalyticAt ℂ (cuspDiscriminantUnit u) 0 := by
  have h : AnalyticAt ℂ SpecialPeriods.discriminantUnit (cuspModularParameter u 0) := by
    rw [cuspModularParameter_zero]
    exact SpecialPeriods.discriminantUnit_analyticAt_zero
  exact hu.mul (h.comp (cuspModularParameter_analyticAt hu))

private def SpecialPeriods.MuGenerator.cuspGeneratorUnit (u b : ℂ → ℂ) (t : ℂ) : ℂ :=
  cuspEisensteinFour u t ^ 2 * b t / cuspDiscriminantUnit u t

@[simp]
private theorem SpecialPeriods.MuGenerator.cuspGeneratorUnit_zero (u b : ℂ → ℂ) :
    cuspGeneratorUnit u b 0 = b 0 / u 0 := by simp [cuspGeneratorUnit]

private theorem SpecialPeriods.MuGenerator.cuspGeneratorUnit_analyticAt {u b : ℂ → ℂ}
    (hu : AnalyticAt ℂ u 0) (hb : AnalyticAt ℂ b 0) (hu0 : u 0 ≠ 0) :
    AnalyticAt ℂ (cuspGeneratorUnit u b) 0 :=
  ((cuspEisensteinFour_analyticAt hu).pow 2 |>.mul hb).div (cuspDiscriminantUnit_analyticAt hu)
    (by simpa only [cuspDiscriminantUnit_zero] using hu0)

private theorem
    SpecialPeriods.MuGenerator.cuspGeneratorUnit_zero_ne_zero {u b : ℂ → ℂ} (hu0 : u 0 ≠ 0)
    (hb0 : b 0 ≠ 0) : cuspGeneratorUnit u b 0 ≠ 0 := by
  rw [cuspGeneratorUnit_zero]
  exact div_ne_zero hb0 hu0

private theorem SpecialPeriods.MuGenerator.Root.square_eq_cuspEisensteinSix {τ : ℍ → ℍ}
    (r : SpecialPeriods.MuGenerator.Root τ) (u : ℂ → ℂ) (z : ℍ)
    (hq :
      Function.Periodic.qParam 1 (τ z) =
        SpecialPeriods.Triangle.cuspQ z * u (SpecialPeriods.Triangle.cuspQ z)) :
    r z ^ 2 = SpecialPeriods.MuGenerator.cuspEisensteinSix u (SpecialPeriods.Triangle.cuspQ z) := by
  rw [r.square z, ←
    SlashInvariantFormClass.eq_cuspFunction ModularForm.E₆ (τ z) one_mem_strictPeriods_SL
      one_ne_zero,
    hq]
  rfl

private theorem SpecialPeriods.MuGenerator.Root.generator_eq_inv_q_mul_unit {τ : ℍ → ℍ}
    (r : SpecialPeriods.MuGenerator.Root τ) (u b : ℂ → ℂ) (z : ℍ)
    (hq :
      Function.Periodic.qParam 1 (τ z) =
        SpecialPeriods.Triangle.cuspQ z * u (SpecialPeriods.Triangle.cuspQ z))
    (hr : r z = b (SpecialPeriods.Triangle.cuspQ z)) :
    r.generator z =
      (SpecialPeriods.Triangle.cuspQ z)⁻¹ *
        SpecialPeriods.MuGenerator.cuspGeneratorUnit u b (SpecialPeriods.Triangle.cuspQ z) := by
  have hE :
    ModularForm.E₄ (τ z) =
      SpecialPeriods.MuGenerator.cuspEisensteinFour u (SpecialPeriods.Triangle.cuspQ z) := by
    rw [←
      SlashInvariantFormClass.eq_cuspFunction ModularForm.E₄ (τ z) one_mem_strictPeriods_SL
        one_ne_zero,
      hq]
    rfl
  have hD :
    ModularForm.discriminant (τ z) =
      SpecialPeriods.Triangle.cuspQ z *
        SpecialPeriods.MuGenerator.cuspDiscriminantUnit u (SpecialPeriods.Triangle.cuspQ z) := by
    have h := ModularForm.discriminant_eq_q_prod (τ z)
    change
      ModularForm.discriminant (τ z) =
        Function.Periodic.qParam 1 (τ z) *
          SpecialPeriods.discriminantUnit (Function.Periodic.qParam 1 (τ z)) at h
    rw [h, hq, SpecialPeriods.MuGenerator.cuspDiscriminantUnit,
      SpecialPeriods.MuGenerator.cuspModularParameter]
    ring
  rw [generator, hE, hr, hD, SpecialPeriods.MuGenerator.cuspGeneratorUnit]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem SpecialPeriods.MuGenerator.exists_analytic_sqrt_germ_one {h : ℂ → ℂ}
    (hh : AnalyticAt ℂ h 0) (h0 : h 0 = 1) :
    ∃ b : ℂ → ℂ, AnalyticAt ℂ b 0 ∧ b 0 = 1 ∧ ∀ᶠ t in 𝓝 0, b t ^ 2 = h t := by
  obtain ⟨r, hr, hr0, hrpow⟩ :=
    SpecialPeriods.exists_analytic_unit_root hh (by simp [h0]) (by norm_num : 0 < (2 : ℕ))
  have hr02 : r 0 ^ 2 = 1 := by simpa only [h0] using hrpow.self_of_nhds
  refine ⟨fun t => r t / r 0, hr.div analyticAt_const hr0, div_self hr0, ?_⟩
  filter_upwards [hrpow] with t ht
  simp only [div_pow, hr02, div_one, ht]

private theorem SpecialPeriods.MuGenerator.exists_analytic_sqrt_ball_one {h : ℂ → ℂ}
    (hh : AnalyticAt ℂ h 0) (h0 : h 0 = 1) :
    ∃ ε > 0,
      ∃ b : ℂ → ℂ,
        AnalyticOnNhd ℂ b (Metric.ball 0 ε) ∧
          b 0 = 1 ∧
            (∀ t ∈ Metric.ball 0 ε, b t ≠ 0) ∧ Set.EqOn (fun t => b t ^ 2) h (Metric.ball 0 ε) := by
  obtain ⟨b, hb, hb0, hbpow⟩ := exists_analytic_sqrt_germ_one hh h0
  have hbne : ∀ᶠ t in 𝓝 0, b t ≠ 0 := hb.continuousAt.eventually_ne (by simp [hb0])
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hb.eventually_analyticAt.and (hbne.and hbpow))
  refine ⟨ε, hε, b, ?_, hb0, ?_, ?_⟩
  · exact fun t ht => (hball ht).1
  · exact fun t ht => (hball ht).2.1
  · exact fun t ht => (hball ht).2.2

private theorem SpecialPeriods.MuGenerator.cuspHorodisc_isPreconnected (Y : ℝ) (hY : 0 ≤ Y) :
    IsPreconnected (SpecialPeriods.Triangle.horodisc Y : Set ℍ) := by
  apply UpperHalfPlane.isOpenEmbedding_coe.toIsEmbedding.toIsInducing.isPreconnected_image.mp
  have he :
    (UpperHalfPlane.coe '' (SpecialPeriods.Triangle.horodisc Y : Set ℍ)) = {w : ℂ | Y < w.im} := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hw
      exact ⟨⟨w, hY.trans_lt hw⟩, hw, rfl⟩
  rw [he]
  exact (convex_halfSpace_im_gt Y).isPreconnected

private theorem SpecialPeriods.MuGenerator.Root.exists_cusp_root_unit {τ : ℍ → ℍ}
    (r : SpecialPeriods.MuGenerator.Root τ) {u : ℂ → ℂ} (hu : AnalyticAt ℂ u 0)
    (hq :
      ∀ᶠ z in UpperHalfPlane.atImInfty,
        Function.Periodic.qParam 1 (τ z) =
          SpecialPeriods.Triangle.cuspQ z * u (SpecialPeriods.Triangle.cuspQ z)) :
    ∃ b : ℂ → ℂ,
      AnalyticAt ℂ b 0 ∧
        (b 0 = 1 ∨ b 0 = -1) ∧
          ∀ᶠ z in UpperHalfPlane.atImInfty, r z = b (SpecialPeriods.Triangle.cuspQ z) := by
  obtain ⟨R, hR, b, hb, hb0, hbne, hbsq⟩ :=
    SpecialPeriods.MuGenerator.exists_analytic_sqrt_ball_one
      (SpecialPeriods.MuGenerator.cuspEisensteinSix_analyticAt hu)
      (SpecialPeriods.MuGenerator.cuspEisensteinSix_zero u)
  have hsmall :
    ∀ᶠ z in UpperHalfPlane.atImInfty, SpecialPeriods.Triangle.cuspQ z ∈ Metric.ball 0 R :=
    (UpperHalfPlane.qParam_tendsto_atImInfty SpecialPeriods.Triangle.width_pos).eventually
      (Metric.ball_mem_nhds 0 hR)
  obtain ⟨A, hA⟩ := (UpperHalfPlane.atImInfty_mem _).mp (hq.and hsmall)
  let Y := Max.max A SpecialPeriods.Triangle.width
  have hY : 0 ≤ Y := SpecialPeriods.Triangle.width_pos.le.trans (le_max_right _ _)
  have hhigh :
    ∀ z ∈ SpecialPeriods.Triangle.horodisc Y,
      Function.Periodic.qParam 1 (τ z) =
          SpecialPeriods.Triangle.cuspQ z * u (SpecialPeriods.Triangle.cuspQ z) ∧
        SpecialPeriods.Triangle.cuspQ z ∈ Metric.ball 0 R := by
    intro z hz
    change Y < z.im at hz
    exact hA z ((le_max_left _ _).trans hz.le)
  have hcont :
    ContinuousOn (b ∘ SpecialPeriods.Triangle.cuspQ)
      (SpecialPeriods.Triangle.horodisc Y : Set ℍ) :=
    hb.continuousOn.comp SpecialPeriods.Triangle.cuspQ_continuous.continuousOn
      (fun z hz => (hhigh z hz).2)
  have hsq :
    Set.EqOn ((r : ℍ → ℂ) ^ 2) ((b ∘ SpecialPeriods.Triangle.cuspQ) ^ 2)
      (SpecialPeriods.Triangle.horodisc Y : Set ℍ) := by
    intro z hz
    change r z ^ 2 = b (SpecialPeriods.Triangle.cuspQ z) ^ 2
    exact (r.square_eq_cuspEisensteinSix u z (hhigh z hz).1).trans (hbsq (hhigh z hz).2).symm
  have hne :
    ∀ {z : ℍ},
      z ∈ SpecialPeriods.Triangle.horodisc Y → (b ∘ SpecialPeriods.Triangle.cuspQ) z ≠ 0 :=
    fun {z} hz => hbne _ (hhigh z hz).2
  have hYe : ∀ᶠ z in UpperHalfPlane.atImInfty, z ∈ SpecialPeriods.Triangle.horodisc Y := by
    apply (UpperHalfPlane.atImInfty_mem _).mpr
    refine ⟨Y + 1, fun z hz => ?_⟩
    change Y < z.im
    linarith
  have hbAt : AnalyticAt ℂ b 0 := hb 0 (Metric.mem_ball_self hR)
  rcases
    (SpecialPeriods.MuGenerator.cuspHorodisc_isPreconnected Y hY).eq_or_eq_neg_of_sq_eq
      r.holomorphic.continuous.continuousOn hcont hsq hne with
    h | h
  · exact ⟨b, hbAt, Or.inl hb0, hYe.mono fun z hz => h hz⟩
  · refine ⟨-b, hbAt.neg, Or.inr ?_, ?_⟩
    · simp only [Pi.neg_apply, hb0]
    · filter_upwards [hYe] with z hz
      simpa only [Pi.neg_apply, Function.comp_apply] using h hz

private theorem SpecialPeriods.MuGenerator.Root.exists_cusp_unit {τ : ℍ → ℍ}
    (r : SpecialPeriods.MuGenerator.Root τ) {u : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hq :
      ∀ᶠ z in UpperHalfPlane.atImInfty,
        Function.Periodic.qParam 1 (τ z) =
          SpecialPeriods.Triangle.cuspQ z * u (SpecialPeriods.Triangle.cuspQ z)) :
    ∃ v : ℂ → ℂ,
      AnalyticAt ℂ v 0 ∧
        v 0 ≠ 0 ∧
          ∀ᶠ z in UpperHalfPlane.atImInfty,
            r.generator z =
              (SpecialPeriods.Triangle.cuspQ z)⁻¹ * v (SpecialPeriods.Triangle.cuspQ z) := by
  obtain ⟨b, hb, hb0, hrb⟩ := r.exists_cusp_root_unit hu hq
  have hbne : b 0 ≠ 0 := by rcases hb0 with h | h <;> simp [h]
  refine
    ⟨SpecialPeriods.MuGenerator.cuspGeneratorUnit u b,
      SpecialPeriods.MuGenerator.cuspGeneratorUnit_analyticAt hu hb hu0,
      SpecialPeriods.MuGenerator.cuspGeneratorUnit_zero_ne_zero hu0 hbne, ?_⟩
  filter_upwards [hq, hrb] with z hqz hrz
  exact r.generator_eq_inv_q_mul_unit u b z hqz hrz

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.generator_zero_iff_orbits
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere))
    {τ : ℍ → ℍ}
    (hJ :
      ∀ z, SpecialPeriods.modularJ (τ z) = 1728 * SpecialPeriods.BetaTorsor.finiteProjection π z)
    (r : SpecialPeriods.MuGenerator.Root τ) (z : ℍ) :
    r.generator z = 0 ↔
      SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterOne ∨
        SpecialPeriods.triangleOrbitProjection z = SpecialPeriods.triangleOrbitCenterTwo := by
  rw [r.generator_eq_zero_iff_normalized_source hJ,
    SourceOrders.finiteProjection_eq_zero_iff π hπ h₀,
    SourceOrders.finiteProjection_eq_one_iff π hπ h₁]

private theorem SpecialPeriods.MuTorsor.CuspRegular.bounded {f : ℍ → ℂ}
    (hf : SpecialPeriods.MuTorsor.CuspRegular f) : UpperHalfPlane.IsBoundedAtImInfty f := by
  obtain ⟨M, hM, he⟩ := hf
  have he' : f =ᶠ[UpperHalfPlane.atImInfty] fun z => M (SpecialPeriods.Triangle.cuspQ z) := he
  have ht : Filter.Tendsto f UpperHalfPlane.atImInfty (𝓝 (M 0)) :=
    (hM.continuousAt.tendsto.comp
          (SpecialPeriods.Triangle.cuspQ_tendsto_atImInfty.mono_right nhdsWithin_le_nhds)).congr'
      he'.symm
  exact ht.isBigO_one ℝ

attribute [local instance] SpecialPeriods.triangleCompactifiedChartedSpace in
private theorem SpecialPeriods.MuTorsor.exists_unique_solution
    (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) SpecialPeriods.TriangleCompactifiedOrbitSpace RiemannSphere ω)
    (hπ : π SpecialPeriods.triangleCuspPoint = ((OnePoint.infty) : RiemannSphere))
    (h₀ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterOne) =
        ((0 : ℂ) : RiemannSphere))
    (h₁ :
      π (SpecialPeriods.triangleOpenInclusion SpecialPeriods.triangleOrbitCenterTwo) =
        ((1 : ℂ) : RiemannSphere))
    {τ : ℍ → ℍ} (hτ : SpecialPeriods.TauCovariant τ) (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ)
    (hJ :
      ∀ z, SpecialPeriods.modularJ (τ z) = 1728 * SpecialPeriods.BetaTorsor.finiteProjection π z)
    {u : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hq :
      ∀ᶠ z in UpperHalfPlane.atImInfty,
        Function.Periodic.qParam 1 (τ z) =
          SpecialPeriods.Triangle.cuspQ z * u (SpecialPeriods.Triangle.cuspQ z)) :
    ∃! μ : ℍ → ℂ, IsSolution τ μ := by
  have hJ' : ∀ z, SpecialPeriods.modularJ (τ z) = SourceOrders.sourceJ π z := hJ
  obtain ⟨F, ⟨r, rfl⟩, hF, hFc, _, hF₁, hF₂⟩ :=
    SpecialPeriods.MuGenerator.exists_homogeneous_generator_of_modular_equation hτa hτ hJ'
      (SourceOrders.sourceJ_order_of_eq_zero π hπ h₀)
      (SourceOrders.sourceJ_sub_1728_order_of_eq π hπ h₁)
  exact
    exists_unique_solution_from_generator π hπ hτ hτa r.generator hF hFc
      (generator_zero_iff_orbits π hπ h₀ h₁ hJ r) hF₁ hF₂ (r.exists_cusp_unit hu hu0 hq)

private def SpecialPeriods.phiThree (p : PeriodPoint) : ℂ :=
  2 - 6 * (1 - p.μ) ^ 2 / p.τ

private def SpecialPeriods.phiFour (p : PeriodPoint) : ℂ :=
  -3 - 6 * p.μ ^ 2 / p.τ

private theorem
    SpecialPeriods.phiThree_eq_beta_sub (p : PeriodPoint) : phiThree p = p.step₁.β - p.β := by
  simp only [phiThree, PeriodPoint.step₁]
  ring

private theorem
    SpecialPeriods.phiFour_eq_beta_sub (p : PeriodPoint) : phiFour p = p.step₂.β - p.β := by
  simp only [phiFour, PeriodPoint.step₂]
  ring

private theorem
    SpecialPeriods.phiThree_cyclic_sum (p : PeriodPoint) (h₀ : p.τ ≠ 0) (h₁ : p.τ - 1 ≠ 0) :
    phiThree p + phiThree p.step₁ + phiThree p.step₁.step₁ = 0 := by
  simp only [phiThree_eq_beta_sub]
  rw [p.step₁_cube h₀ h₁]
  ring

private theorem SpecialPeriods.phiFour_cyclic_sum (p : PeriodPoint) (h₀ : p.τ ≠ 0) :
    phiFour p + phiFour p.step₂ + phiFour p.step₂.step₂ + phiFour p.step₂.step₂.step₂ = 0 := by
  simp only [phiFour_eq_beta_sub]
  rw [p.step₂_fourth h₀]
  ring

private def SpecialPeriods.betaAverageThree (p : PeriodPoint) : ℂ :=
  (phiThree p.step₁ + 2 * phiThree p.step₁.step₁) / 3

private def SpecialPeriods.betaAverageFour (p : PeriodPoint) : ℂ :=
  (phiFour p.step₂ + 2 * phiFour p.step₂.step₂ + 3 * phiFour p.step₂.step₂.step₂) / 4

private theorem SpecialPeriods.betaAverageThree_difference (p : PeriodPoint) (h₀ : p.τ ≠ 0)
    (h₁ : p.τ - 1 ≠ 0) : betaAverageThree p.step₁ - betaAverageThree p = phiThree p := by
  unfold betaAverageThree
  rw [p.step₁_cube h₀ h₁]
  linear_combination -(1 / 3 : ℂ) * phiThree_cyclic_sum p h₀ h₁

private theorem SpecialPeriods.betaAverageFour_difference (p : PeriodPoint) (h₀ : p.τ ≠ 0) :
    betaAverageFour p.step₂ - betaAverageFour p = phiFour p := by
  unfold betaAverageFour
  rw [p.step₂_fourth h₀]
  linear_combination -(1 / 4 : ℂ) * phiFour_cyclic_sum p h₀

private def SpecialPeriods.betaPrimitiveThree (τ μ : ℂ) : ℂ :=
  (2 - 6 * (τ - 1 + μ) ^ 2 / (τ * (τ - 1)) + 2 * (2 + 6 * μ ^ 2 / (τ - 1))) / 3

private def SpecialPeriods.betaPrimitiveFour (τ μ : ℂ) : ℂ :=
  ((-3 + 6 * (τ + μ) ^ 2 / τ) + 2 * (-3 - 6 * (1 - τ - μ) ^ 2 / τ) +
      3 * (-3 + 6 * (1 - μ) ^ 2 / τ)) /
    4

private theorem SpecialPeriods.phiThree_step (p : PeriodPoint) (h₀ : p.τ ≠ 0) (h₁ : p.τ - 1 ≠ 0) :
    phiThree p.step₁ = 2 - 6 * (p.τ - 1 + p.μ) ^ 2 / (p.τ * (p.τ - 1)) := by
  simp only [phiThree, PeriodPoint.step₁]
  field_simp
  ring

private theorem
    SpecialPeriods.phiThree_step_sq (p : PeriodPoint) (h₀ : p.τ ≠ 0) (h₁ : p.τ - 1 ≠ 0) :
    phiThree p.step₁.step₁ = 2 + 6 * p.μ ^ 2 / (p.τ - 1) := by
  rw [p.step₁_sq h₀ h₁]
  simp only [phiThree]
  field_simp
  ring

private theorem SpecialPeriods.phiFour_step (p : PeriodPoint) (h₀ : p.τ ≠ 0) :
    phiFour p.step₂ = -3 + 6 * (p.τ + p.μ) ^ 2 / p.τ := by
  simp only [phiFour, PeriodPoint.step₂]
  field_simp
  ring

private theorem SpecialPeriods.phiFour_step_sq (p : PeriodPoint) (h₀ : p.τ ≠ 0) :
    phiFour p.step₂.step₂ = -3 - 6 * (1 - p.τ - p.μ) ^ 2 / p.τ := by
  rw [p.step₂_sq h₀]
  rfl

private theorem SpecialPeriods.phiFour_step_cube (p : PeriodPoint) (h₀ : p.τ ≠ 0) :
    phiFour p.step₂.step₂.step₂ = -3 + 6 * (1 - p.μ) ^ 2 / p.τ := by
  rw [phiFour_step _ (by simpa only [p.step₂_sq h₀] using h₀), p.step₂_sq h₀]
  ring

private theorem SpecialPeriods.betaAverageThree_eq_primitive (p : PeriodPoint) (h₀ : p.τ ≠ 0)
    (h₁ : p.τ - 1 ≠ 0) : betaAverageThree p = betaPrimitiveThree p.τ p.μ := by
  rw [betaAverageThree, phiThree_step p h₀ h₁, phiThree_step_sq p h₀ h₁]
  rfl

private theorem SpecialPeriods.betaAverageFour_eq_primitive (p : PeriodPoint) (h₀ : p.τ ≠ 0) :
    betaAverageFour p = betaPrimitiveFour p.τ p.μ := by
  rw [betaAverageFour, phiFour_step p h₀, phiFour_step_sq p h₀, phiFour_step_cube p h₀]
  rfl

private theorem
    SpecialPeriods.betaPrimitiveThree_difference (τ μ : ℂ) (h₀ : τ ≠ 0) (h₁ : τ - 1 ≠ 0) :
    betaPrimitiveThree ((τ - 1) / τ) ((1 - μ) / τ) - betaPrimitiveThree τ μ =
      2 - 6 * (1 - μ) ^ 2 / τ := by
  let p : PeriodPoint := ⟨τ, μ, 0⟩
  have hs₀ : p.step₁.τ ≠ 0 := div_ne_zero h₁ h₀
  have hs₁ : p.step₁.τ - 1 ≠ 0 := by
    have he : p.step₁.τ - 1 = -1 / τ := by
      dsimp [p, PeriodPoint.step₁]
      field_simp
      ring
    rw [he]
    exact div_ne_zero (by norm_num) h₀
  change betaPrimitiveThree p.step₁.τ p.step₁.μ - betaPrimitiveThree p.τ p.μ = phiThree p
  rw [← betaAverageThree_eq_primitive p.step₁ hs₀ hs₁, ← betaAverageThree_eq_primitive p h₀ h₁]
  exact betaAverageThree_difference p h₀ h₁

private theorem SpecialPeriods.betaPrimitiveFour_difference (τ μ : ℂ) (h₀ : τ ≠ 0) :
    betaPrimitiveFour (-1 / τ) (1 + μ / τ) - betaPrimitiveFour τ μ = -3 - 6 * μ ^ 2 / τ := by
  let p : PeriodPoint := ⟨τ, μ, 0⟩
  have hs₀ : p.step₂.τ ≠ 0 := div_ne_zero (by norm_num) h₀
  change betaPrimitiveFour p.step₂.τ p.step₂.μ - betaPrimitiveFour p.τ p.μ = phiFour p
  rw [← betaAverageFour_eq_primitive p.step₂ hs₀, ← betaAverageFour_eq_primitive p h₀]
  exact betaAverageFour_difference p h₀

private def SpecialPeriods.BetaTorsor.phiOne (τ : ℍ → ℍ) (μ : ℍ → ℂ) (z : ℍ) : ℂ :=
  2 - 6 * (1 - μ z) ^ 2 / (τ z : ℂ)

private def SpecialPeriods.BetaTorsor.phiTwo (τ : ℍ → ℍ) (μ : ℍ → ℂ) (z : ℍ) : ℂ :=
  -3 - 6 * μ z ^ 2 / (τ z : ℂ)

private def SpecialPeriods.BetaTorsor.primitiveOne (τ : ℍ → ℍ) (μ : ℍ → ℂ) (z : ℍ) : ℂ :=
  SpecialPeriods.betaPrimitiveThree (τ z) (μ z)

private def SpecialPeriods.BetaTorsor.primitiveTwo (τ : ℍ → ℍ) (μ : ℍ → ℂ) (z : ℍ) : ℂ :=
  SpecialPeriods.betaPrimitiveFour (τ z) (μ z)

public
theorem SpecialPeriods.BetaTorsor.tau_sub_one_ne_zero_mo1973_17984 (τ : ℍ → ℍ) (z : ℍ) :
    (τ z : ℂ) - 1 ≠ 0 :=
  sub_ne_zero.mpr (by simpa only [Complex.ofReal_one] using (τ z).ne_ofReal 1)

private theorem SpecialPeriods.BetaTorsor.phiOne_holomorphic {τ : ℍ → ℍ} {μ : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hμ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω μ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (phiOne τ μ) := by
  have ht : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => (τ z : ℂ)) := UpperHalfPlane.contMDiff_coe.comp hτ
  exact
    contMDiff_const.sub
      ((contMDiff_const.mul ((contMDiff_const.sub hμ).pow 2)).div₀ ht (fun z => (τ z).ne_zero))

private theorem SpecialPeriods.BetaTorsor.phiTwo_holomorphic {τ : ℍ → ℍ} {μ : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hμ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω μ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (phiTwo τ μ) := by
  have ht : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => (τ z : ℂ)) := UpperHalfPlane.contMDiff_coe.comp hτ
  exact contMDiff_const.sub ((contMDiff_const.mul (hμ.pow 2)).div₀ ht (fun z => (τ z).ne_zero))

private theorem SpecialPeriods.BetaTorsor.primitiveOne_holomorphic {τ : ℍ → ℍ} {μ : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hμ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω μ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (primitiveOne τ μ) := by
  have ht : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => (τ z : ℂ)) := UpperHalfPlane.contMDiff_coe.comp hτ
  have ha :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      (fun z => 6 * ((τ z : ℂ) - 1 + μ z) ^ 2 / ((τ z : ℂ) * ((τ z : ℂ) - 1))) :=
    (contMDiff_const.mul (((ht.sub contMDiff_const).add hμ).pow 2)).div₀
      (ht.mul (ht.sub contMDiff_const))
      (fun z => mul_ne_zero (τ z).ne_zero (tau_sub_one_ne_zero_mo1973_17984 τ z))
  have hb : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => 6 * μ z ^ 2 / ((τ z : ℂ) - 1)) :=
    (contMDiff_const.mul (hμ.pow 2)).div₀ (ht.sub contMDiff_const)
      (tau_sub_one_ne_zero_mo1973_17984 τ)
  exact ((contMDiff_const.sub ha).add (contMDiff_const.mul (contMDiff_const.add hb))).div_const 3

private theorem SpecialPeriods.BetaTorsor.primitiveTwo_holomorphic {τ : ℍ → ℍ} {μ : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hμ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω μ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (primitiveTwo τ μ) := by
  have ht : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => (τ z : ℂ)) := UpperHalfPlane.contMDiff_coe.comp hτ
  have ha : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => 6 * ((τ z : ℂ) + μ z) ^ 2 / (τ z : ℂ)) :=
    (contMDiff_const.mul ((ht.add hμ).pow 2)).div₀ ht (fun z => (τ z).ne_zero)
  have hb : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => 6 * (1 - (τ z : ℂ) - μ z) ^ 2 / (τ z : ℂ)) :=
    (contMDiff_const.mul (((contMDiff_const.sub ht).sub hμ).pow 2)).div₀ ht
      (fun z => (τ z).ne_zero)
  have hc : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => 6 * (1 - μ z) ^ 2 / (τ z : ℂ)) :=
    (contMDiff_const.mul ((contMDiff_const.sub hμ).pow 2)).div₀ ht (fun z => (τ z).ne_zero)
  exact
    (((contMDiff_const.add ha).add (contMDiff_const.mul (contMDiff_const.sub hb))).add
          (contMDiff_const.mul (contMDiff_const.add hc))).div_const
      4

private theorem SpecialPeriods.BetaTorsor.primitiveOne_difference {τ : ℍ → ℍ} {μ : ℍ → ℂ}
    (hτ : SpecialPeriods.TauCovariant τ)
    (hμ : ∀ z : ℍ, μ (SpecialPeriods.Triangle.generatorOneSL • z) = (1 - μ z) / (τ z : ℂ))
    (z : ℍ) :
    primitiveOne τ μ (SpecialPeriods.Triangle.generatorOneSL • z) - primitiveOne τ μ z =
      phiOne τ μ z := by
  simp only [primitiveOne, phiOne, hτ.1, hμ]
  exact
    SpecialPeriods.betaPrimitiveThree_difference (τ z) (μ z) (τ z).ne_zero
      (tau_sub_one_ne_zero_mo1973_17984 τ z)

private theorem SpecialPeriods.BetaTorsor.primitiveTwo_difference {τ : ℍ → ℍ} {μ : ℍ → ℂ}
    (hτ : SpecialPeriods.TauCovariant τ)
    (hμ : ∀ z : ℍ, μ (SpecialPeriods.Triangle.generatorTwoSL • z) = 1 + μ z / (τ z : ℂ)) (z : ℍ) :
    primitiveTwo τ μ (SpecialPeriods.Triangle.generatorTwoSL • z) - primitiveTwo τ μ z =
      phiTwo τ μ z := by
  simp only [primitiveTwo, phiTwo, hτ.2, hμ]
  exact SpecialPeriods.betaPrimitiveFour_difference (τ z) (μ z) (τ z).ne_zero

private theorem SpecialPeriods.BetaTorsor.generatorOne_triple_mo1973_17991 (z : ℍ) :
    SpecialPeriods.Triangle.generatorOneSL •
        (SpecialPeriods.Triangle.generatorOneSL • (SpecialPeriods.Triangle.generatorOneSL • z)) =
      z := by
  have he := congrArg (fun g : Equiv.Perm ℍ => g z) SpecialPeriods.Triangle.generatorOnePerm_cube
  simpa only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
    SpecialPeriods.Triangle.generatorOnePerm,
    SpecialPeriods.Triangle.realSLPermutation_apply] using he

private theorem SpecialPeriods.BetaTorsor.generatorTwo_quadruple_mo1973_17992 (z : ℍ) :
    SpecialPeriods.Triangle.generatorTwoSL •
        (SpecialPeriods.Triangle.generatorTwoSL •
          (SpecialPeriods.Triangle.generatorTwoSL •
            (SpecialPeriods.Triangle.generatorTwoSL • z))) =
      z := by
  have he :=
    congrArg (fun g : Equiv.Perm ℍ => g z) SpecialPeriods.Triangle.generatorTwoPerm_fourth
  simpa only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, Equiv.Perm.one_apply,
    SpecialPeriods.Triangle.generatorTwoPerm,
    SpecialPeriods.Triangle.realSLPermutation_apply] using he

private theorem SpecialPeriods.BetaTorsor.phiOne_cyclic_sum {τ : ℍ → ℍ} {μ : ℍ → ℂ}
    (hτ : SpecialPeriods.TauCovariant τ)
    (hμ : ∀ z : ℍ, μ (SpecialPeriods.Triangle.generatorOneSL • z) = (1 - μ z) / (τ z : ℂ))
    (z : ℍ) :
    phiOne τ μ z + phiOne τ μ (SpecialPeriods.Triangle.generatorOneSL • z) +
        phiOne τ μ
          (SpecialPeriods.Triangle.generatorOneSL •
            (SpecialPeriods.Triangle.generatorOneSL • z)) =
      0 := by
  have h₀ := primitiveOne_difference hτ hμ z
  have h₁ := primitiveOne_difference hτ hμ (SpecialPeriods.Triangle.generatorOneSL • z)
  have h₂ :=
    primitiveOne_difference hτ hμ
      (SpecialPeriods.Triangle.generatorOneSL • (SpecialPeriods.Triangle.generatorOneSL • z))
  rw [generatorOne_triple_mo1973_17991] at h₂
  linear_combination -h₀ - h₁ - h₂

private theorem SpecialPeriods.BetaTorsor.phiTwo_cyclic_sum {τ : ℍ → ℍ} {μ : ℍ → ℂ}
    (hτ : SpecialPeriods.TauCovariant τ)
    (hμ : ∀ z : ℍ, μ (SpecialPeriods.Triangle.generatorTwoSL • z) = 1 + μ z / (τ z : ℂ)) (z : ℍ) :
    phiTwo τ μ z + phiTwo τ μ (SpecialPeriods.Triangle.generatorTwoSL • z) +
          phiTwo τ μ
            (SpecialPeriods.Triangle.generatorTwoSL •
              (SpecialPeriods.Triangle.generatorTwoSL • z)) +
        phiTwo τ μ
          (SpecialPeriods.Triangle.generatorTwoSL •
            (SpecialPeriods.Triangle.generatorTwoSL •
              (SpecialPeriods.Triangle.generatorTwoSL • z))) =
      0 := by
  have h₀ := primitiveTwo_difference hτ hμ z
  have h₁ := primitiveTwo_difference hτ hμ (SpecialPeriods.Triangle.generatorTwoSL • z)
  have h₂ :=
    primitiveTwo_difference hτ hμ
      (SpecialPeriods.Triangle.generatorTwoSL • (SpecialPeriods.Triangle.generatorTwoSL • z))
  have h₃ :=
    primitiveTwo_difference hτ hμ
      (SpecialPeriods.Triangle.generatorTwoSL •
        (SpecialPeriods.Triangle.generatorTwoSL • (SpecialPeriods.Triangle.generatorTwoSL • z)))
  rw [generatorTwo_quadruple_mo1973_17992] at h₃
  linear_combination -h₀ - h₁ - h₂ - h₃

private theorem SpecialPeriods.BetaTorsor.phiOne_sum_range {τ : ℍ → ℍ} {μ : ℍ → ℂ}
    (hτ : SpecialPeriods.TauCovariant τ)
    (hμ : ∀ z : ℍ, μ (SpecialPeriods.Triangle.generatorOneSL • z) = (1 - μ z) / (τ z : ℂ))
    (z : ℍ) :
    (∑ k ∈ Finset.range 3, phiOne τ μ ((SpecialPeriods.Triangle.generatorOnePerm ^ k) z)) = 0 := by
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_succ, pow_zero, one_mul,
    Equiv.Perm.mul_apply, Equiv.Perm.one_apply, SpecialPeriods.Triangle.generatorOnePerm,
    SpecialPeriods.Triangle.realSLPermutation_apply] using phiOne_cyclic_sum hτ hμ z

private theorem SpecialPeriods.BetaTorsor.phiTwo_sum_range {τ : ℍ → ℍ} {μ : ℍ → ℂ}
    (hτ : SpecialPeriods.TauCovariant τ)
    (hμ : ∀ z : ℍ, μ (SpecialPeriods.Triangle.generatorTwoSL • z) = 1 + μ z / (τ z : ℂ)) (z : ℍ) :
    (∑ k ∈ Finset.range 4, phiTwo τ μ ((SpecialPeriods.Triangle.generatorTwoPerm ^ k) z)) = 0 := by
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_succ, pow_zero, one_mul,
    Equiv.Perm.mul_apply, Equiv.Perm.one_apply, SpecialPeriods.Triangle.generatorTwoPerm,
    SpecialPeriods.Triangle.realSLPermutation_apply] using phiTwo_cyclic_sum hτ hμ z

private theorem SpecialPeriods.BetaTorsor.phi_product_relation {τ : ℍ → ℍ} {μ : ℍ → ℂ}
    (hτ : SpecialPeriods.TauCovariant τ)
    (hμ : ∀ z : ℍ, μ (SpecialPeriods.Triangle.generatorTwoSL • z) = 1 + μ z / (τ z : ℂ)) (z : ℍ) :
    phiOne τ μ (SpecialPeriods.Triangle.generatorTwoSL • z) + phiTwo τ μ z = -1 := by
  let p : PeriodPoint := ⟨τ z, μ z, 0⟩
  have hp : SpecialPeriods.phiThree p.step₂ + SpecialPeriods.phiFour p = -1 := by
    rw [SpecialPeriods.phiThree_eq_beta_sub, SpecialPeriods.phiFour_eq_beta_sub,
      p.step₁_step₂ (τ z).ne_zero]
    simp only
    ring
  simp only [phiOne, phiTwo, hτ.2, hμ]
  exact hp

private def SpecialPeriods.BetaTorsor.cuspPrimitive (τ : ℍ → ℍ) (z : ℍ) : ℂ :=
  -(τ z : ℂ)

private theorem SpecialPeriods.BetaTorsor.cuspPrimitive_holomorphic {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (cuspPrimitive τ) :=
  (UpperHalfPlane.contMDiff_coe.comp hτ).neg

private theorem SpecialPeriods.BetaTorsor.cuspPrimitive_difference {τ : ℍ → ℍ}
    (hτ : SpecialPeriods.TauCovariant τ) (z : ℍ) :
    cuspPrimitive τ
          (SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleCuspGenerator
            z) -
        cuspPrimitive τ z =
      1 := by
  rw [cuspPrimitive, cuspPrimitive, SpecialPeriods.tau_covariant_cusp_coe hτ]
  ring

private def SpecialPeriods.BetaTorsor.skewPerm {X : Type*} (e : Equiv.Perm X) (φ : X → ℂ) :
    Equiv.Perm (X × ℂ) where
  toFun x := (e x.1, x.2 + φ x.1)
  invFun x := (e.symm x.1, x.2 - φ (e.symm x.1))
  left_inv := by
    rintro ⟨z, b⟩
    simp
  right_inv := by
    rintro ⟨z, b⟩
    simp

@[simp]
private theorem SpecialPeriods.BetaTorsor.skewPerm_apply {X : Type*} (e : Equiv.Perm X) (φ : X → ℂ)
    (z : X) (b : ℂ) : skewPerm e φ (z, b) = (e z, b + φ z) :=
  rfl

private theorem
    SpecialPeriods.BetaTorsor.skewPerm_pow_apply {X : Type*} (e : Equiv.Perm X) (φ : X → ℂ)
    (n : ℕ) (z : X) (b : ℂ) :
    (skewPerm e φ ^ n) (z, b) = ((e ^ n) z, b + ∑ k ∈ Finset.range n, φ ((e ^ k) z)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, skewPerm_apply]
    rw [pow_succ', Equiv.Perm.mul_apply, Finset.sum_range_succ]
    simp only [add_assoc]

private theorem
    SpecialPeriods.BetaTorsor.skewPerm_pow_eq_one {X : Type*} (e : Equiv.Perm X) (φ : X → ℂ)
    (m : ℕ) (he : e ^ m = 1) (hφ : ∀ z, (∑ k ∈ Finset.range m, φ ((e ^ k) z)) = 0) :
    skewPerm e φ ^ m = 1 := by
  apply Equiv.ext
  rintro ⟨z, b⟩
  rw [skewPerm_pow_apply, he, hφ z]
  simp

private def SpecialPeriods.BetaTorsor.IsAdditiveSkewOver {X : Type*} (e : Equiv.Perm X)
    (p : Equiv.Perm (X × ℂ)) : Prop :=
  ∀ z b, p (z, b) = (e z, b + (p (z, 0)).2)

private theorem SpecialPeriods.BetaTorsor.isAdditiveSkewOver_skewPerm {X : Type*} (e : Equiv.Perm X)
    (φ : X → ℂ) : IsAdditiveSkewOver e (skewPerm e φ) := by
  intro z b
  simp

private theorem SpecialPeriods.BetaTorsor.isAdditiveSkewOver_one {X : Type*} :
    IsAdditiveSkewOver (1 : Equiv.Perm X) (1 : Equiv.Perm (X × ℂ)) := by
  intro z b
  simp

private theorem SpecialPeriods.BetaTorsor.IsAdditiveSkewOver.mul {X : Type*} {e f : Equiv.Perm X}
    {p q : Equiv.Perm (X × ℂ)} (hp : SpecialPeriods.BetaTorsor.IsAdditiveSkewOver e p)
    (hq : SpecialPeriods.BetaTorsor.IsAdditiveSkewOver f q) :
    SpecialPeriods.BetaTorsor.IsAdditiveSkewOver (e * f) (p * q) := by
  intro z b
  have hzero : ((p * q) (z, 0)).2 = (q (z, 0)).2 + (p (f z, 0)).2 := by
    change (p (q (z, 0))).2 = _
    rw [hq z 0]
    simpa only [zero_add] using congrArg Prod.snd (hp (f z) ((q (z, 0)).2))
  change p (q (z, b)) = (e (f z), b + ((p * q) (z, 0)).2)
  rw [hq z b, hp (f z) (b + (q (z, 0)).2), hzero]
  simp only [add_assoc]

private theorem SpecialPeriods.BetaTorsor.IsAdditiveSkewOver.inv {X : Type*} {e : Equiv.Perm X}
    {p : Equiv.Perm (X × ℂ)} (hp : SpecialPeriods.BetaTorsor.IsAdditiveSkewOver e p) :
    SpecialPeriods.BetaTorsor.IsAdditiveSkewOver e⁻¹ p⁻¹ := by
  have hpi (z : X) (b : ℂ) : p.symm (z, b) = (e.symm z, b - (p (e.symm z, 0)).2) := by
    apply p.injective
    rw [p.apply_symm_apply, hp]
    simp
  intro z b
  change p.symm (z, b) = (e.symm z, b + (p.symm (z, 0)).2)
  rw [hpi z b, hpi z 0]
  simp only [sub_eq_add_neg, zero_add]

private def SpecialPeriods.BetaTorsor.triangleAdditiveRepresentation (φ₁ φ₂ : ℍ → ℂ)
    (h₁ : ∀ z, (∑ k ∈ Finset.range 3, φ₁ ((SpecialPeriods.Triangle.generatorOnePerm ^ k) z)) = 0)
    (h₂ :
      ∀ z, (∑ k ∈ Finset.range 4, φ₂ ((SpecialPeriods.Triangle.generatorTwoPerm ^ k) z)) = 0) :
    SpecialPeriods.TriangleGroup →* Equiv.Perm (ℍ × ℂ) :=
  SpecialPeriods.triangleLift (skewPerm SpecialPeriods.Triangle.generatorOnePerm φ₁)
    (skewPerm SpecialPeriods.Triangle.generatorTwoPerm φ₂)
    (skewPerm_pow_eq_one _ _ _ SpecialPeriods.Triangle.generatorOnePerm_cube h₁)
    (skewPerm_pow_eq_one _ _ _ SpecialPeriods.Triangle.generatorTwoPerm_fourth h₂)

@[simp]
private theorem SpecialPeriods.BetaTorsor.triangleAdditiveRepresentation_generator₁ (φ₁ φ₂ : ℍ → ℂ)
    (h₁ : ∀ z, (∑ k ∈ Finset.range 3, φ₁ ((SpecialPeriods.Triangle.generatorOnePerm ^ k) z)) = 0)
    (h₂ :
      ∀ z, (∑ k ∈ Finset.range 4, φ₂ ((SpecialPeriods.Triangle.generatorTwoPerm ^ k) z)) = 0) :
    triangleAdditiveRepresentation φ₁ φ₂ h₁ h₂ SpecialPeriods.triangleGenerator₁ =
      skewPerm SpecialPeriods.Triangle.generatorOnePerm φ₁ :=
  SpecialPeriods.triangleLift_generator₁ ..

@[simp]
private theorem SpecialPeriods.BetaTorsor.triangleAdditiveRepresentation_generator₂ (φ₁ φ₂ : ℍ → ℂ)
    (h₁ : ∀ z, (∑ k ∈ Finset.range 3, φ₁ ((SpecialPeriods.Triangle.generatorOnePerm ^ k) z)) = 0)
    (h₂ :
      ∀ z, (∑ k ∈ Finset.range 4, φ₂ ((SpecialPeriods.Triangle.generatorTwoPerm ^ k) z)) = 0) :
    triangleAdditiveRepresentation φ₁ φ₂ h₁ h₂ SpecialPeriods.triangleGenerator₂ =
      skewPerm SpecialPeriods.Triangle.generatorTwoPerm φ₂ :=
  SpecialPeriods.triangleLift_generator₂ ..

end Mathoverflow1973

end
