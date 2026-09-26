/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.Dirichlet.Transform
public import LeanPool.CarlsonFunctions.Dirichlet.Average.Deriv
public import LeanPool.CarlsonFunctions.Dirichlet.Average.Bridge
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.AnalyticUniqueness

public import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Analytic continuation of Carlson's Dirichlet averages

This file develops Carlson's regularized Dirichlet average as an entire function of the
Dirichlet parameters. It contains the abstract continuation predicate, the polynomial
construction, and the native resolvent average. R-polynomial Taylor-series constructions
are developed in `Carlson.RPolynomial.PowerSeries`.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Chapter 6,
  Academic Press, 1977.
-/

open Complex MeasureTheory ProbabilityTheory

@[expose] public noncomputable section CarlsonDirichletAverage

namespace DirichletTransform

variable {ι : Type*} [Fintype ι]

/-- A function of `b` is a regularized Carlson continuation for `f` and `z` if it is entire
and agrees with the native regularized Dirichlet integral on its domain of absolute
convergence. -/
def IsRegCarlsonContinuation (f : ℂ → ℂ) (z : ι → ℂ)
    (G : (ι → ℂ) → ℂ) : Prop :=
  AnalyticOnNhd ℂ G Set.univ ∧
    Set.EqOn G (fun b ↦ regCarlsonDirichletAverage b z f) mvBetaConvergent

/-- Construct a regularized Carlson continuation from entire dependence on `b` and agreement
with the native integral on the convergence region. -/
theorem IsRegCarlsonContinuation.mk' {f : ℂ → ℂ} {z : ι → ℂ}
    {G : (ι → ℂ) → ℂ} (hG : AnalyticOnNhd ℂ G Set.univ)
    (hEq : Set.EqOn G (fun b ↦ regCarlsonDirichletAverage b z f) mvBetaConvergent) :
    IsRegCarlsonContinuation f z G :=
  ⟨hG, hEq⟩

/-- A regularized Carlson continuation is entire in the Dirichlet parameters. -/
theorem IsRegCarlsonContinuation.analyticOnNhd {f : ℂ → ℂ} {z : ι → ℂ}
    {G : (ι → ℂ) → ℂ} (hG : IsRegCarlsonContinuation f z G) :
    AnalyticOnNhd ℂ G Set.univ :=
  hG.1

/-- A regularized Carlson continuation agrees with the native integral wherever that integral
is absolutely convergent. -/
theorem IsRegCarlsonContinuation.eq_native {f : ℂ → ℂ} {z : ι → ℂ}
    {G : (ι → ℂ) → ℂ} (hG : IsRegCarlsonContinuation f z G)
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    G b = regCarlsonDirichletAverage b z f :=
  hG.2 hb

/-- Two entire functions of the Dirichlet parameters that agree throughout the ordinary
convergence region agree everywhere. This is the common continuation step for the identities
proved from Carlson's native integral. -/
theorem analyticOnNhd_eq_of_eqOn_mvBetaConvergent
    {G H : (ι → ℂ) → ℂ} (hG : AnalyticOnNhd ℂ G Set.univ)
    (hH : AnalyticOnNhd ℂ H Set.univ) (hEq : Set.EqOn G H mvBetaConvergent) :
    G = H := by
  let b₀ : ι → ℂ := fun _ ↦ 1
  have hb₀ : b₀ ∈ mvBetaConvergent := by
    intro i
    simp [b₀]
  apply hG.eq_of_eventuallyEq hH (z₀ := b₀)
  filter_upwards [isOpen_mvBetaConvergent.eventually_mem hb₀] with b hb
  exact hEq hb

/-- The entire regularized Carlson continuation, if it exists, is unique. -/
theorem IsRegCarlsonContinuation.eq {f : ℂ → ℂ} {z : ι → ℂ}
    {G H : (ι → ℂ) → ℂ} (hG : IsRegCarlsonContinuation f z G)
    (hH : IsRegCarlsonContinuation f z H) : G = H := by
  apply analyticOnNhd_eq_of_eqOn_mvBetaConvergent hG.1 hH.1
  intro b hb
  exact (hG.2 hb).trans (hH.2 hb).symm

/-- Two entire candidates which agree for every strictly positive real Dirichlet parameter
agree globally. This is the uniqueness principle used to lift probability identities without
first proving them on the full complex convergence region. -/
theorem analyticOnNhd_eq_of_eqOn_realDirichletDomain
    {G H : (ι → ℂ) → ℂ} (hG : AnalyticOnNhd ℂ G Set.univ)
    (hH : AnalyticOnNhd ℂ H Set.univ)
    (hEq : ∀ b : ι → ℝ, b ∈ mvRealBetaDomain →
      G (fun i ↦ (b i : ℂ)) = H (fun i ↦ (b i : ℂ))) : G = H := by
  apply analyticOnNhd_eq_of_eqOn_posReal_piCarlson hG hH
  intro b hb
  exact hEq b hb

/-- An entire candidate can be recognized as a Carlson continuation by comparison on positive
real parameters with any already established continuation. -/
theorem IsRegCarlsonContinuation.mk_of_eqOn_realDirichletDomain
    {f : ℂ → ℂ} {z : ι → ℂ} {G H : (ι → ℂ) → ℂ}
    (hG : AnalyticOnNhd ℂ G Set.univ) (hH : IsRegCarlsonContinuation f z H)
    (hEq : ∀ b : ι → ℝ, b ∈ mvRealBetaDomain →
      G (fun i ↦ (b i : ℂ)) = H (fun i ↦ (b i : ℂ))) :
    IsRegCarlsonContinuation f z G := by
  have hGH := analyticOnNhd_eq_of_eqOn_realDirichletDomain hG hH.1 hEq
  rw [hGH]
  exact hH

/-- An entire candidate which has the probability-average values on positive real parameters
is a Carlson continuation, provided one continuation is already known to exist. The reference
continuation is used only for uniqueness. -/
theorem IsRegCarlsonContinuation.mk_of_eq_realCarlsonDirichletAverage [Nonempty ι]
    {f : ℂ → ℂ} {z : ι → ℂ} {G H : (ι → ℂ) → ℂ}
    (hG : AnalyticOnNhd ℂ G Set.univ) (hH : IsRegCarlsonContinuation f z H)
    (hEq : ∀ b : ι → ℝ, b ∈ mvRealBetaDomain →
      G (fun i ↦ (b i : ℂ)) =
        realCarlsonDirichletAverage b z f / Gamma (∑ i, (b i : ℂ))) :
    IsRegCarlsonContinuation f z G := by
  apply IsRegCarlsonContinuation.mk_of_eqOn_realDirichletDomain hG hH
  intro b hb
  rw [hEq b hb, hH.eq_native]
  · exact (regCarlsonDirichletAverage_ofReal hb z f).symm
  · simpa [mvBetaConvergent, mvRealBetaDomain] using hb

/-- A holomorphic scalar function on a convex open set admits an entire regularized
Dirichlet-parameter continuation at every node vector in that set. -/
theorem exists_isRegCarlsonContinuation
    {Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω) {z : ι → ℂ} (hz : Set.range z ⊆ Ω) :
    ∃ G, IsRegCarlsonContinuation f z G := by
  apply exists_entire_regDirichletContinuation_of_contDiffNear
  intro N
  have haffine : ContDiff ℝ N (fun u : ι → ℝ => carlsonAffineForm z u) := by
    unfold carlsonAffineForm
    exact ContDiff.sum fun i _ =>
      (Complex.ofRealCLM.contDiff.comp
        (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).contDiff).mul contDiff_const
  refine ⟨carlsonAffineForm z ⁻¹' Ω, hΩopen.preimage (continuous_carlsonAffineForm z),
    fun u hu => convexHull_min hz hΩconv (carlsonAffineForm_mem_convexHull z hu), ?_⟩
  exact (hf.contDiffOn_of_completeSpace.restrict_scalars ℝ).comp haffine.contDiffOn
    (fun _ hu => hu)

end DirichletTransform

end CarlsonDirichletAverage
