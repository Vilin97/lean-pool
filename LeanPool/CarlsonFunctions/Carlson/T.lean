/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.Dirichlet.Average.Continuation

import Mathlib.Topology.Maps.Proper.Basic

/-!
# Carlson's multivariate T-function

Carlson's Definition 5.12-1 defines `T(b,z)` as the Dirichlet average of
`w ↦ exp (1 / w)`.  Carlson immediately turns to a limiting two-variable case; this file keeps
the short general multivariate theory separate from that specialization.

The intrinsic variable domain used here says that the convex hull of the variables avoids
zero.  Carlson's assumption that all variables lie in a common open half-plane not containing
zero implies this condition.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, §5.12,
  Academic Press, 1977.
-/

open Complex MeasureTheory ProbabilityTheory
@[expose] public noncomputable section CarlsonT

namespace DirichletTransform

variable {ι : Type*} [Fintype ι]

/-- The scalar kernel defining Carlson's T-function. -/
def carlsonTKernel (w : ℂ) : ℂ := exp w⁻¹

/-- The intrinsic multivariate domain on which every convex combination of the variables is
nonzero. -/
def carlsonTVariableDomain : Set (ι → ℂ) :=
  {z | (0 : ℂ) ∉ convexHull ℝ (Set.range z)}

omit [Fintype ι] in
/-- Any convex zero-avoiding set containing all variables certifies membership in the
intrinsic T-variable domain.  Carlson applies this with an open half-plane not containing
zero. -/
theorem mem_carlsonTVariableDomain_of_range_subset {H : Set ℂ}
    (hH : Convex ℝ H) (hzero : (0 : ℂ) ∉ H) {z : ι → ℂ}
    (hz : Set.range z ⊆ H) : z ∈ carlsonTVariableDomain := by
  intro hconv
  exact hzero (convexHull_min hz hH hconv)

/-- On the T-variable domain, Carlson's affine form never vanishes on the standard simplex. -/
theorem carlsonAffineForm_ne_zero_of_mem_carlsonTVariableDomain
    {z : ι → ℂ} (hz : z ∈ carlsonTVariableDomain)
    {u : ι → ℝ} (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) :
    carlsonAffineForm z u ≠ 0 := by
  intro hzero
  apply hz
  rw [← hzero]
  exact carlsonAffineForm_mem_convexHull z hu

/-- The T-kernel composed with Carlson's affine form is continuous on the simplex whenever
the convex hull of the variables avoids zero. -/
theorem continuousOn_carlsonTKernel_carlsonAffineForm
    {z : ι → ℂ} (hz : z ∈ carlsonTVariableDomain) :
    ContinuousOn (fun u : ι → ℝ => carlsonTKernel (carlsonAffineForm z u))
      (Convexity.StdSimplex.coordinateSet ℝ ι) := by
  intro u hu
  exact Complex.continuous_exp.continuousAt.comp_continuousWithinAt
    ((continuous_carlsonAffineForm z).continuousAt.inv₀
      (carlsonAffineForm_ne_zero_of_mem_carlsonTVariableDomain hz hu)).continuousWithinAt

/-- For a fixed simplex point, the T-kernel is analytic in all variables throughout the
intrinsic zero-avoiding domain. -/
theorem analyticOnNhd_carlsonTKernel_carlsonAffineForm
    (u : ι → ℝ) (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) :
    AnalyticOnNhd ℂ (fun z : ι → ℂ => carlsonTKernel (carlsonAffineForm z u))
      carlsonTVariableDomain := by
  intro z hz
  have haffine : AnalyticAt ℂ (fun z : ι → ℂ => carlsonAffineForm z u) z := by
    unfold carlsonAffineForm
    apply Finset.analyticAt_fun_sum
    intro i _
    exact analyticAt_const.mul
      ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt z)
  unfold carlsonTKernel
  exact analyticAt_cexp.comp_of_eq
    ((analyticAt_inv
      (carlsonAffineForm_ne_zero_of_mem_carlsonTVariableDomain hz hu)).comp_of_eq
        haffine rfl) rfl

/-- Carlson's native regularized multivariate T-integral. -/
def regCarlsonTIntegral (b z : ι → ℂ) : ℂ :=
  regCarlsonDirichletAverage b z carlsonTKernel

/-- Carlson's native, unregularized multivariate T-integral from Definition 5.12-1. -/
def carlsonTIntegral (b z : ι → ℂ) : ℂ :=
  Gamma (∑ i, b i) * regCarlsonTIntegral b z

/-- The native T-integrand is integrable under Carlson's parameter and variable hypotheses. -/
theorem integrableOn_regDirichletDensity_mul_carlsonTKernel
    {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent)
    (hz : z ∈ carlsonTVariableDomain) :
    IntegrableOn (fun u : ι → ℝ =>
      regDirichletDensity b u * carlsonTKernel (carlsonAffineForm z u))
      (Convexity.StdSimplex.coordinateSet ℝ ι) MeasureTheory.Measure.stdSimplexMeasure :=
  integrableOn_regDirichletDensity_mul b hb
    (continuousOn_carlsonTKernel_carlsonAffineForm hz)

/-- Simultaneous permutation of parameters and variables leaves the native regularized
T-integral unchanged. -/
theorem regCarlsonTIntegral_perm (b z : ι → ℂ) (σ : Equiv.Perm ι) :
    regCarlsonTIntegral (b ∘ σ) (z ∘ σ) = regCarlsonTIntegral b z :=
  regCarlsonDirichletAverage_perm b z carlsonTKernel σ

/-- A candidate is an entire regularized continuation of Carlson's T-function in the
Dirichlet parameters if it agrees with the native integral on `mvBetaConvergent`. -/
def IsRegCarlsonTContinuation (z : ι → ℂ) (G : (ι → ℂ) → ℂ) : Prop :=
  IsRegCarlsonContinuation carlsonTKernel z G

/-- A regularized T-continuation is entire in the Dirichlet parameters. -/
theorem IsRegCarlsonTContinuation.analyticOnNhd {z : ι → ℂ} {G : (ι → ℂ) → ℂ}
    (hG : IsRegCarlsonTContinuation z G) : AnalyticOnNhd ℂ G Set.univ :=
  hG.1

/-- A regularized T-continuation agrees with Carlson's native integral on its convergence
domain. -/
theorem IsRegCarlsonTContinuation.eq_integral {z : ι → ℂ} {G : (ι → ℂ) → ℂ}
    (hG : IsRegCarlsonTContinuation z G) {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) : G b = regCarlsonTIntegral b z :=
  hG.2 hb

/-- The entire regularized continuation of T, if it exists, is unique. -/
theorem IsRegCarlsonTContinuation.eq {z : ι → ℂ} {G H : (ι → ℂ) → ℂ}
    (hG : IsRegCarlsonTContinuation z G) (hH : IsRegCarlsonTContinuation z H) :
    G = H :=
  IsRegCarlsonContinuation.eq hG hH

/-- The smooth-kernel Dirichlet continuation theorem supplies an entire regularized
T-continuation whenever the convex hull of the variables avoids zero. This proof does not
construct a contour representation. -/
theorem exists_isRegCarlsonTContinuation {z : ι → ℂ}
    (hz : z ∈ carlsonTVariableDomain) :
    ∃ G : (ι → ℂ) → ℂ, IsRegCarlsonTContinuation z G := by
  have hsmooth : ∀ N, ContDiffNearStdSimplex N
      (fun u : ι → ℝ ↦ carlsonTKernel (carlsonAffineForm z u)) := by
    intro N
    let U : Set (ι → ℝ) := {u | carlsonAffineForm z u ≠ 0}
    have hU : IsOpen U := by
      have hclosed : IsClosed {u : ι → ℝ | carlsonAffineForm z u = 0} :=
        isClosed_eq (continuous_carlsonAffineForm z) continuous_const
      simpa [U, Set.compl_ofPred] using hclosed.isOpen_compl
    refine ⟨U, hU, fun u hu ↦
      carlsonAffineForm_ne_zero_of_mem_carlsonTVariableDomain hz hu, ?_⟩
    have haffine : ContDiff ℝ N (fun u : ι → ℝ ↦ carlsonAffineForm z u) := by
      unfold carlsonAffineForm
      exact ContDiff.sum fun i _ ↦
        (Complex.ofRealCLM.contDiff.comp
          (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).contDiff).mul contDiff_const
    unfold carlsonTKernel
    exact (haffine.contDiffOn.inv (fun u hu ↦ hu)).cexp
  obtain ⟨G, hG, hEq⟩ :=
    exists_entire_regDirichletContinuation_of_contDiffNear hsmooth
  refine ⟨G, hG, ?_⟩
  intro b hb
  exact hEq hb

omit [Fintype ι] in
/-- The intrinsic T-variable domain is open. -/
theorem isOpen_carlsonTVariableDomain [Finite ι] :
    IsOpen (carlsonTVariableDomain : Set (ι → ℂ)) := by
  classical
  let _ := Fintype.ofFinite ι
  rw [← isClosed_compl_iff]
  let π : (ι → ℂ) × Convexity.StdSimplex ℝ ι → ι → ℂ := Prod.fst
  have hcont : Continuous (fun p : (ι → ℂ) × Convexity.StdSimplex ℝ ι =>
      carlsonAffineForm p.1 p.2.coordinates) := by
    unfold carlsonAffineForm
    refine continuous_finsetSum _ fun i _ => ?_
    exact (Complex.continuous_ofReal.comp
        ((continuous_apply i).comp
          (Convexity.StdSimplex.continuous_coordinates.comp continuous_snd))).mul
      ((continuous_apply i).comp continuous_fst)
  have hZ : IsClosed {p : (ι → ℂ) × Convexity.StdSimplex ℝ ι |
      carlsonAffineForm p.1 p.2.coordinates = 0} :=
    isClosed_singleton.preimage hcont
  have himage : (carlsonTVariableDomain : Set (ι → ℂ))ᶜ =
      π '' {p | carlsonAffineForm p.1 p.2.coordinates = 0} := by
    ext z
    constructor
    · intro hz
      have hz' : (0 : ℂ) ∈ convexHull ℝ (Set.range z) := by
        simpa [carlsonTVariableDomain] using hz
      obtain ⟨u, hzero⟩ := (zero_mem_convexHull_range_iff z).1 hz'
      exact ⟨⟨z, u⟩, hzero, rfl⟩
    · rintro ⟨⟨z', u⟩, hp, rfl⟩
      simpa [carlsonTVariableDomain] using
        (zero_mem_convexHull_range_iff z').2 ⟨u, hp⟩
  rw [himage]
  exact (isClosedMap_fst_of_compactSpace (X := ι → ℂ) (Y := Convexity.StdSimplex ℝ ι)) _ hZ

end DirichletTransform

end CarlsonT
