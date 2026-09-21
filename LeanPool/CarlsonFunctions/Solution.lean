/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams -/
import LeanPool.CarlsonFunctions.Pochhammer
import LeanPool.CarlsonFunctions.SeveralComplexVariables
import LeanPool.CarlsonFunctions.StdSimplexMeasure
import LeanPool.CarlsonFunctions.Dirichlet
import LeanPool.CarlsonFunctions.Carlson

/-!
# Proved counterparts of Statement.lean

This module imports all five mathematical libraries, never Statement.
Comparator compares the PalomarSnapshot declarations in these two independent
environments. The elementary definitions are intentionally repeated verbatim;
each theorem below points to an existing project proof. See PALOMAR.md.
-/

open Complex MeasureTheory Set
open scoped Classical Topology Matrix
noncomputable section
namespace PalomarSnapshot
variable {ι : Type*} [Fintype ι]

/-- Nonnegative coordinates summing to one: the ambient standard simplex. -/
def simplex : Set (ι → ℝ) := {u | (∀ i, 0 ≤ u i) ∧ ∑ i, u i = 1}

/-- The positive-coordinate part of the simplex. -/
def interior : Set (ι → ℝ) := {u | u ∈ simplex ∧ ∀ i, 0 < u i}

/-- Recover coordinate i as one minus the sum of the remaining coordinates. -/
def chart (i : ι) (x : {j : ι // j ≠ i} → ℝ) : ι → ℝ :=
  (Equiv.funSplitAt i ℝ).symm (1 - ∑ j, x j, x)

/-- Coordinate Lebesgue measure on the whole sum-one hyperplane; zero for no coordinates.
There is no Euclidean square-root-of-cardinality factor in this normalization. -/
def simplexMeasure : Measure (ι → ℝ) :=
  if h : Nonempty ι then Measure.map (chart (Classical.choice h)) volume else 0

/-- Gamma-regularized complex density, zero outside the positive simplex. -/
def density (b : ι → ℂ) (u : ι → ℝ) : ℂ :=
  interior.indicator (fun u => ∏ i, (u i : ℂ) ^ (b i - 1) / Gamma (b i)) u

/-- The native regularized average of f at the affine combination of the nodes.
This totalized integral is not itself the continuation outside convergence. -/
def average (b z : ι → ℂ) (f : ℂ → ℂ) : ℂ :=
  ∫ u in simplex, density b u * f (∑ i, (u i : ℂ) * z i) ∂simplexMeasure

/-- Real Dirichlet distribution: the normalized power density on the positive simplex.
Its probability interpretation requires positive parameters and a nonempty index type. -/
def realDirichlet (b : ι → ℝ) : Measure (ι → ℝ) :=
  simplexMeasure.withDensity (fun u => ENNReal.ofReal
    ((1 / ((∏ i, Real.Gamma (b i)) / Real.Gamma (∑ i, b i))) *
      interior.indicator (fun u => ∏ i, u i ^ (b i - 1)) u))

/-- Ordinary coordinate differentiation, holding all other coordinates fixed. -/
def coordDeriv (i : ι) (f : (ι → ℂ) → ℂ) (z : ι → ℂ) : ℂ :=
  deriv (fun w => f (Function.update z i w)) (z i)

/-- Reciprocal Gamma shift, including its zeros at nonpositive integers. -/
theorem gamma_shift (z : ℂ) (n : ℕ) :
    (Gamma z)⁻¹ = (ascPochhammer ℂ n).eval z * (Gamma (z + n))⁻¹ := by
  exact Complex.one_div_Gamma_eq_ascPochhammer_mul_one_div_Gamma_add_nat z n

/-- Chu–Vandermonde for rising factorials over any commutative semiring. -/
theorem vandermonde {A : Type*} [CommSemiring A] (r s : A) (n : ℕ) :
    (ascPochhammer A n).eval (r + s) =
      ∑ ij ∈ Finset.antidiagonal n, (n.choose ij.1 : A) *
        ((ascPochhammer A ij.1).eval r * (ascPochhammer A ij.2).eval s) := by
  exact ascPochhammer_eval_add r s n

/-- Complex Fréchet differentiability on an open finite-dimensional domain implies analyticity. -/
theorem holomorphic_analytic {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {U : Set E} {f : E → F} (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) :
    AnalyticOnNhd ℂ f U := by
  exact hf.analyticOnNhd_finiteDimensional hU

/-- Joint continuity and separate holomorphy imply joint analyticity (not Hartogs without continuity). -/
theorem osgood {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {U : Set (ι → ℂ)} {f : (ι → ℂ) → F} (hU : IsOpen U) (hc : ContinuousOn f U)
    (hf : ∀ z ∈ U, ∀ i, AnalyticAt ℂ (fun w => f (Function.update z i w)) (z i)) :
    AnalyticOnNhd ℂ f U := by
  exact SeveralComplexVariables.analyticOnNhd_pi_of_analyticOnNhd_update hU hc hf

/-- Cauchy's formula for every derivative at any interior point, requiring only boundary continuity. -/
theorem cauchy_derivatives {c : ℂ} {r : ℝ} {f : ℂ → ℂ} (hf : DiffContOnCl ℂ f (Metric.ball c r))
    (hr : 0 < r) (n : ℕ) {w : ℂ} (hw : w ∈ Metric.ball c r) :
    iteratedDeriv n f w = (n.factorial : ℂ) * (2 * (Real.pi : ℂ) * I)⁻¹ *
      ∮ s in C(c, r), (s - w) ^ (-(n + 1 : ℤ)) * f s := by
  exact hf.iteratedDeriv_eq_circleIntegral_sub_zpow_mul hr n hw

/-- Every omitted-coordinate chart defines the same ambient measure. -/
theorem simplex_chart_independent [Nonempty ι] (i : ι) :
    simplexMeasure (ι := ι) = Measure.map (chart i) volume := by
  exact MeasureTheory.Measure.stdSimplexMeasure_eq_at i

/-- Simplex monomial integral with coordinate-volume normalization, including the singleton case. -/
theorem simplex_monomial [Nonempty ι] (m : ι → ℕ) :
    ∫ u in simplex, (∏ i, u i ^ m i) ∂simplexMeasure =
      (∏ i, Nat.factorial (m i)) / (Nat.factorial (Fintype.card ι + (∑ i, m i) - 1) : ℝ) := by
  exact MeasureTheory.integral_stdSimplex_explicit_monomial m

/-- Absolutely convergent multivariate beta integral; each parameter has positive real part. -/
theorem complex_beta_integral {b : ι → ℂ} (hb : ∀ i, 0 < (b i).re) :
    (∏ i, Gamma (b i)) / Gamma (∑ i, b i) =
      ∫ u in simplex, ∏ i, (u i : ℂ) ^ (b i - 1) ∂simplexMeasure := by
  exact Complex.mvBeta_eq_integral hb

/-- Positive real parameters on a nonempty simplex define a probability measure. -/
theorem dirichlet_probability [Nonempty ι] {b : ι → ℝ} (hb : ∀ i, 0 < b i) :
    IsProbabilityMeasure (realDirichlet b) := by
  exact ProbabilityTheory.isProbabilityMeasure_dirichletMeasure hb

/-- All natural mixed moments of the real Dirichlet distribution. -/
theorem dirichlet_moments [Nonempty ι] {b : ι → ℝ} (hb : ∀ i, 0 < b i) (m : ι → ℕ) :
    ∫ u, (∏ i, u i ^ m i) ∂(realDirichlet b) =
      (∏ i, (ascPochhammer ℝ (m i)).eval (b i)) /
        (ascPochhammer ℝ (∑ i, m i)).eval (∑ i, b i) := by
  exact ProbabilityTheory.integral_dirichletMeasure_monomial hb m

/-- Summing coordinates in surjective blocks sums the corresponding Dirichlet parameters. -/
theorem dirichlet_aggregation {κ : Type*} [Fintype κ] {q : ι → κ} (hq : Function.Surjective q)
    {b : ι → ℝ} (hb : ∀ i, 0 < b i) :
    MeasurePreserving (FunOnFinite.linearMap ℝ ℝ q)
      (realDirichlet b) (realDirichlet (FunOnFinite.linearMap ℝ ℝ q b)) := by
  exact ProbabilityTheory.measurePreserving_stdSimplexAggregate_dirichletMeasure hq hb

/-- Carlson 1977, 6.3-6: joint entire-parameter continuation on every convex open scalar domain. -/
theorem joint_average_continuation {D : Set ℂ} (hD : IsOpen D) (hconv : Convex ℝ D)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f D) :
    ∃ G : ((ι → ℂ) × (ι → ℂ)) → ℂ,
      AnalyticOnNhd ℂ G {p | Set.range p.2 ⊆ D} ∧
      ∀ z, Set.range z ⊆ D → ∀ b, (∀ i, 0 < (b i).re) → G (b, z) = average b z f := by
  obtain ⟨G, hG, hnative⟩ := DirichletTransform.exists_joint_isRegCarlsonContinuation hD hconv hf (ι := ι)
  exact ⟨G, hG, fun z hz b hb => (hnative z hz).eq_native hb⟩

/-- Gamma-regularized Carlson R on the principal slit domain.
The solution supplies its construction; r_joint and r_native fix its mathematical meaning. -/
def regR {ι : Type*} [Fintype ι] (t : ℂ) (b z : ι → ℂ) : ℂ :=
  DirichletTransform.regCarlsonRSlit t b z

/-- Gamma-regularized Carlson L is the exponent derivative of the same R-function. -/
abbrev regL (t : ℂ) (b z : ι → ℂ) : ℂ := deriv (fun s => regR s b z) t

/-- Carlson 6.8-2: joint holomorphy in all exponents, all Dirichlet parameters, and slit-plane nodes. -/
theorem r_joint :
    AnalyticOnNhd ℂ (fun p : Option (ι ⊕ ι) → ℂ =>
      regR (p none) (fun i => p (some (.inl i))) (fun i => p (some (.inr i))))
      {p | ∀ i, p (some (.inr i)) ∈ slitPlane} := by
  exact DirichletTransform.analyticOnNhd_regCarlsonRSlit_joint

/-- R equals its native power average when the entire node convex hull stays in the slit plane. -/
theorem r_native (t : ℂ) {b z : ι → ℂ} (hb : ∀ i, 0 < (b i).re)
    (hz : convexHull ℝ (Set.range z) ⊆ slitPlane) :
    regR t b z = average b z (fun w => w ^ t) := by
  exact DirichletTransform.regCarlsonRSlit_eq_integral_of_convexHull t hb hz

/-- Carlson 6.8-3: Euler inversion on all slit-plane nodes and all complex parameters. -/
theorem r_euler (t : ℂ) (b : ι → ℂ) {z : ι → ℂ} (hz : ∀ i, z i ∈ slitPlane) :
    regR t b z = (∏ i, z i ^ (-b i)) * regR (-(∑ i, b i) - t) b (fun i => (z i)⁻¹) := by
  exact DirichletTransform.regCarlsonRSlit_euler t b hz

/-- Euler–Poisson on the full slit domain, including repeated indices and coincident nodes. -/
theorem r_euler_poisson (t : ℂ) (b : ι → ℂ) {z : ι → ℂ} (hz : ∀ i, z i ∈ slitPlane) (i j : ι) :
    (z i - z j) * coordDeriv i (coordDeriv j (regR t b)) z +
      b i * coordDeriv j (regR t b) z - b j * coordDeriv i (regR t b) z = 0 := by
  exact DirichletTransform.carlsonEulerPoissonOperator_regCarlsonRSlit t b hz i j

/-- First quadratic transformation (6.9): all t, beta, with positive-real-part unsquared variables. -/
theorem r_first_quadratic (t β x y : ℂ) (hx : 0 < x.re) (hy : 0 < y.re) :
    regR (2 * t) ![β, β] ![x, y] =
      ((2 : ℂ) ^ (1 - 2 * β) * (Real.sqrt Real.pi : ℂ) * (Gamma β)⁻¹) *
        regR t ![β + t, 1 / 2 - t] ![((x + y) / 2) ^ 2, x * y] := by
  exact DirichletTransform.TwoVariable.regRSlit_firstQuadratic t β x y hx hy

/-- Second quadratic transformation (6.10): squared and transformed nodes need not have positive real parts. -/
theorem r_second_quadratic (t β x y : ℂ) (hx : 0 < x.re) (hy : 0 < y.re) :
    regR t ![β, β] ![x ^ 2, y ^ 2] =
      ((2 : ℂ) ^ (1 - 2 * β) * (Real.sqrt Real.pi : ℂ) * (Gamma β)⁻¹) *
        regR t ![2 * β + t, 1 / 2 - β - t] ![((x + y) / 2) ^ 2, x * y] := by
  exact DirichletTransform.TwoVariable.regRSlit_secondQuadratic t β x y hx hy

/-- Carlson 1987, (2.1): L is jointly holomorphic on the same full parameter and slit-node domain. -/
theorem l_joint :
    AnalyticOnNhd ℂ (fun p : Option (ι ⊕ ι) → ℂ =>
      regL (p none) (fun i => p (some (.inl i))) (fun i => p (some (.inr i))))
      {p | ∀ i, p (some (.inr i)) ∈ slitPlane} := by
  exact DirichletTransform.analyticOnNhd_regCarlsonLSlit_joint

/-- L equals the native power-logarithm average on the hull-admissible slit domain. -/
theorem l_native (t : ℂ) {b z : ι → ℂ} (hb : ∀ i, 0 < (b i).re)
    (hz : convexHull ℝ (Set.range z) ⊆ slitPlane) :
    regL t b z = average b z (fun w => w ^ t * log w) := by
  exact DirichletTransform.regCarlsonLSlit_eq_integral_of_convexHull t hb hz

/-- The exponent derivative of R exists and equals L for all complex parameters and slit nodes. -/
theorem l_exponent_derivative (t : ℂ) (b : ι → ℂ) {z : ι → ℂ} (hz : ∀ i, z i ∈ slitPlane) :
    HasDerivAt (fun s => regR s b z) (regL t b z) t := by
  exact DirichletTransform.hasDerivAt_regCarlsonRSlit_L t b hz

end PalomarSnapshot
end
