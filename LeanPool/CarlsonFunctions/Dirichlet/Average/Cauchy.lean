/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.Dirichlet.Average.Basic
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.CauchyDerivatives
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.ParametricIntegral
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Averages of Cauchy's integral formula

This file develops the foundational part of [Carl77, Section 5.11].  We use Mathlib's circle
integral formulation of Cauchy's theorem.  Carlson works more generally with positively
oriented rectifiable Jordan curves.

The integer resolvent kernel and its regularized integral are analytic away from the convex
hull of the Carlson variables. A compact-domain differentiation lemma handles the possibly
singular Dirichlet density. A separate product-integrability estimate justifies the interchange
of circle and simplex integrals, giving the circle version of Carlson's Representation 5.11-2
for every derivative order. Joint continuation on a general convex holomorphy domain is
proved separately in `Dirichlet.Average.JointContinuation` by integration by parts.
The general Jordan-curve representation, including its continued-parameter version,
remains to be proved.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Section 5.11,
  Academic Press, 1977.
-/

open Complex MeasureTheory ProbabilityTheory Metric
open scoped Classical

@[expose] public noncomputable section CarlsonCauchyAverage

namespace DirichletTransform

variable {ι : Type*} [Fintype ι]

/-- The integer Cauchy kernel occurring in Carlson's Theorem 5.11-1 and
Representation 5.11-2. -/
def carlsonCauchyKernel (n : ℕ) (z : ι → ℂ) (u : ι → ℝ) (s : ℂ) : ℂ :=
  (s - carlsonAffineForm z u) ^ (-(n + 1 : ℤ))

/-- The native regularized average of Carlson's integer Cauchy kernel. -/
def regCarlsonResolvent (n : ℕ) (b z : ι → ℂ) (s : ℂ) : ℂ :=
  regCarlsonDirichletAverage b z (fun w ↦ (s - w) ^ (-(n + 1 : ℤ)))

/-- The regularized resolvent is the Dirichlet integral of the corresponding pointwise
Cauchy kernel. -/
theorem regCarlsonResolvent_eq_regDirichletIntegral
    (n : ℕ) (b z : ι → ℂ) (s : ℂ) :
    regCarlsonResolvent n b z s =
      regDirichletIntegral b (fun u ↦ carlsonCauchyKernel n z u s) := by
  rfl

/-- The denominator of Carlson's Cauchy kernel does not vanish when `s` lies outside the
convex hull of the Carlson variables. -/
theorem sub_carlsonAffineForm_ne_zero_of_mem_compl_convexHull
    (z : ι → ℂ) {u : ι → ℝ} (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι)
    {s : ℂ} (hs : s ∈ (convexHull ℝ (Set.range z))ᶜ) :
    s - carlsonAffineForm z u ≠ 0 :=
  sub_carlsonAffineForm_ne_zero hs hu

/-- For a fixed simplex point, Carlson's integer Cauchy kernel is analytic in `s` outside
the convex hull of the variables.  Integer powers make this statement branch-independent. -/
theorem analyticOnNhd_carlsonCauchyKernel (n : ℕ) (z : ι → ℂ)
    {u : ι → ℝ} (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) :
    AnalyticOnNhd ℂ (carlsonCauchyKernel n z u)
      ((convexHull ℝ (Set.range z))ᶜ) := by
  intro s hs
  unfold carlsonCauchyKernel
  exact (analyticAt_id.sub analyticAt_const).zpow
    (sub_carlsonAffineForm_ne_zero_of_mem_compl_convexHull z hu hs)

/-- Joint continuity of the Cauchy kernel outside the node convex hull and on the simplex. -/
theorem continuousOn_carlsonCauchyKernel (n : ℕ) (z : ι → ℂ) :
    ContinuousOn (fun p : ℂ × (ι → ℝ) => carlsonCauchyKernel n z p.2 p.1)
      ((convexHull ℝ (Set.range z))ᶜ ×ˢ Convexity.StdSimplex.coordinateSet ℝ ι) := by
  exact (continuous_fst.sub ((continuous_carlsonAffineForm z).comp
    continuous_snd)).continuousOn.zpow₀ _ (fun p hp =>
      Or.inl (sub_carlsonAffineForm_ne_zero hp.1 hp.2))

/-- Differentiation raises the order of the integer resolvent kernel. -/
theorem hasDerivAt_carlsonCauchyKernel (n : ℕ) (z : ι → ℂ)
    {u : ι → ℝ} (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι)
    {s : ℂ} (hs : s ∈ (convexHull ℝ (Set.range z))ᶜ) :
    HasDerivAt (carlsonCauchyKernel n z u)
      (-((n : ℂ) + 1) * carlsonCauchyKernel (n + 1) z u s) s := by
  unfold carlsonCauchyKernel
  have h := (hasDerivAt_zpow (-(n + 1 : ℤ)) (s - carlsonAffineForm z u)
    (Or.inl (sub_carlsonAffineForm_ne_zero hs hu))).comp s
      ((hasDerivAt_id s).sub_const (carlsonAffineForm z u))
  have hexp : -(n + 1 : ℤ) - 1 = -((n + 1 : ℕ) + 1 : ℤ) := by omega
  simpa only [Function.comp_def, id_eq, hexp, Int.cast_neg,
    Int.cast_add, Int.cast_natCast, Int.cast_one, mul_one] using h

/-- Carlson 5.11-1 on the native Dirichlet domain, with the derivative identified:
the integrated integer resolvent is holomorphic outside the convex hull of its nodes. -/
theorem hasDerivAt_regCarlsonResolvent (n : ℕ) {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (z : ι → ℂ)
    {s : ℂ} (hs : s ∈ (convexHull ℝ (Set.range z))ᶜ) :
    HasDerivAt (regCarlsonResolvent n b z)
      (-((n : ℂ) + 1) * regCarlsonResolvent (n + 1) b z s) s := by
  have hd : IntegrableOn (regDirichletDensity b)
      (Convexity.StdSimplex.coordinateSet ℝ ι) MeasureTheory.Measure.stdSimplexMeasure := by
    simpa only [mul_one] using integrableOn_regDirichletDensity_mul b hb
      (continuousOn_const : ContinuousOn (fun _ : ι → ℝ => (1 : ℂ))
        (Convexity.StdSimplex.coordinateSet ℝ ι))
  have h := hasDerivAt_integral_mul_of_continuousOn_compact
    (F := fun w u => carlsonCauchyKernel n z u w)
    (F' := fun w u => -((n : ℂ) + 1) * carlsonCauchyKernel (n + 1) z u w)
    (Convexity.StdSimplex.isCompact_coordinateSet ℝ ι) hd
    ((Set.finite_range z).isCompact_convexHull ℝ).isClosed.isOpen_compl hs
    (continuousOn_carlsonCauchyKernel n z)
    (continuousOn_const.mul (continuousOn_carlsonCauchyKernel (n + 1) z))
    (fun w hw u hu => hasDerivAt_carlsonCauchyKernel n z hu hw)
  change HasDerivAt (fun w => regDirichletIntegral b
    (fun u => carlsonCauchyKernel n z u w)) _ s
  simpa only [regCarlsonResolvent, regCarlsonDirichletAverage, regDirichletIntegral,
    carlsonCauchyKernel, ← integral_const_mul, mul_left_comm] using h

/-- The regularized resolvent is analytic on the entire complement of the node convex
hull, not merely a half-plane. Integer powers require no choice of logarithmic branch. -/
theorem analyticOnNhd_regCarlsonResolvent (n : ℕ) {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (z : ι → ℂ) :
    AnalyticOnNhd ℂ (regCarlsonResolvent n b z) ((convexHull ℝ (Set.range z))ᶜ) := by
  apply DifferentiableOn.analyticOnNhd _
    ((Set.finite_range z).isCompact_convexHull ℝ).isClosed.isOpen_compl
  intro s hs
  exact (hasDerivAt_regCarlsonResolvent n hb z hs).differentiableAt.differentiableWithinAt

/-- The first Cauchy kernel is the usual reciprocal kernel. -/
@[simp] theorem carlsonCauchyKernel_zero (z : ι → ℂ) (u : ι → ℝ) (s : ℂ) :
    carlsonCauchyKernel 0 z u s = (s - carlsonAffineForm z u)⁻¹ := by
  simp [carlsonCauchyKernel]

/-- Cauchy's integral formula at a Carlson affine combination contained in a circle. -/
theorem two_pi_I_inv_mul_circleIntegral_carlsonCauchyKernel_zero
    {c : ℂ} {R : ℝ} {f : ℂ → ℂ} (hf : DiffContOnCl ℂ f (ball c R))
    (z : ι → ℂ) {u : ι → ℝ} (hu : carlsonAffineForm z u ∈ ball c R) :
    (2 * (Real.pi : ℂ) * I)⁻¹ *
        (∮ s in C(c, R), carlsonCauchyKernel 0 z u s * f s) =
      f (carlsonAffineForm z u) := by
  simpa [carlsonCauchyKernel, smul_eq_mul] using
    hf.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hu

/-- Circle form of the first step in Carlson's Representation 5.11-2: average Cauchy's
formula over the simplex, before applying Fubini to interchange the two integrals. -/
theorem regCarlsonDirichletAverage_eq_average_circleIntegral
    {b : ι → ℂ} (z : ι → ℂ) {c : ℂ} {R : ℝ} {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (ball c R))
    (hz : ∀ u, u ∈ Convexity.StdSimplex.coordinateSet ℝ ι → carlsonAffineForm z u ∈ ball c R) :
    regCarlsonDirichletAverage b z f =
      (2 * (Real.pi : ℂ) * I)⁻¹ * regDirichletIntegral b
        (fun u ↦ ∮ s in C(c, R), carlsonCauchyKernel 0 z u s * f s) := by
  unfold regCarlsonDirichletAverage regDirichletIntegral
  rw [← integral_const_mul]
  apply setIntegral_congr_fun (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
  intro u hu
  dsimp only
  have hcauchy := two_pi_I_inv_mul_circleIntegral_carlsonCauchyKernel_zero
    hf z (hz u hu)
  rw [← hcauchy]
  ring

/-- The circle-contour expression on the right side of Carlson's Representation 5.11-2,
specialized to the zeroth derivative. -/
def regCarlsonCauchyRepresentation
    (b z : ι → ℂ) (c : ℂ) (R : ℝ) (f : ℂ → ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * I)⁻¹ *
    ∮ s in C(c, R), regCarlsonResolvent 0 b z s * f s

/-- A continuous kernel on the circle times the simplex may be integrated in either
order against a native regularized Dirichlet density. Compactness bounds the kernel;
the density itself need not be continuous at the boundary. -/
theorem circleIntegral_regDirichletIntegral
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) (c : ℂ) {R : ℝ} (hR : 0 ≤ R)
    {F : ℂ → (ι → ℝ) → ℂ}
    (hF : ContinuousOn (fun p : ℂ × (ι → ℝ) => F p.1 p.2)
      (sphere c R ×ˢ Convexity.StdSimplex.coordinateSet ℝ ι)) :
    (∮ s in C(c, R), regDirichletIntegral b (F s)) =
      regDirichletIntegral b (fun u => ∮ s in C(c, R), F s u) := by
  let K := Convexity.StdSimplex.coordinateSet ℝ ι
  let μ := MeasureTheory.Measure.stdSimplexMeasure (ι := ι)
  have hK : IsCompact K := Convexity.StdSimplex.isCompact_coordinateSet ℝ ι
  have hd : IntegrableOn (regDirichletDensity b) K μ := by
    simpa only [mul_one] using integrableOn_regDirichletDensity_mul b hb
      (continuousOn_const : ContinuousOn (fun _ : ι → ℝ => (1 : ℂ)) K)
  have hbase : IntegrableOn (fun p : ℝ × (ι → ℝ) => regDirichletDensity b p.2)
      (Set.Icc 0 (2 * Real.pi) ×ˢ K) (volume.prod μ) := by
    rw [IntegrableOn, ← Measure.prod_restrict]
    simpa only [one_mul] using
      (integrableOn_const isCompact_Icc.measure_ne_top :
        IntegrableOn (fun _ : ℝ => (1 : ℂ)) (Set.Icc 0 (2 * Real.pi))).mul_prod hd
  have hkernel : ContinuousOn (fun p : ℝ × (ι → ℝ) =>
      deriv (circleMap c R) p.1 * F (circleMap c R p.1) p.2)
      (Set.Icc 0 (2 * Real.pi) ×ˢ K) := by
    apply ContinuousOn.mul
    · simp only [deriv_circleMap]
      fun_prop
    · exact hF.comp
        (((continuous_circleMap c R).comp continuous_fst).prodMk continuous_snd).continuousOn
        (fun p hp => ⟨circleMap_mem_sphere c hR p.1, hp.2⟩)
  have hint := hbase.mul_continuousOn hkernel (isCompact_Icc.prod hK)
  rw [IntegrableOn, ← Measure.prod_restrict] at hint
  have hswap := integral_integral_swap
    (f := fun θ u => regDirichletDensity b u *
      (deriv (circleMap c R) θ * F (circleMap c R θ) u)) hint
  simpa only [circleIntegral_def_Icc, regDirichletIntegral, smul_eq_mul,
    ← integral_const_mul, mul_left_comm, K, μ] using hswap

/-- Moving the integrated resolvent through a circle integral. -/
theorem circleIntegral_regCarlsonResolvent_mul
    (n : ℕ) {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) (z : ι → ℂ)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R) {f : ℂ → ℂ}
    (hf : ContinuousOn f (sphere c R)) (hz : Set.range z ⊆ ball c R) :
    (∮ s in C(c, R), regCarlsonResolvent n b z s * f s) =
      regDirichletIntegral b (fun u => ∮ s in C(c, R), carlsonCauchyKernel n z u s * f s) := by
  have hout {s : ℂ} (hs : s ∈ sphere c R) : s ∈ (convexHull ℝ (Set.range z))ᶜ := by
    intro h
    have hl := mem_ball.mp (convexHull_min hz (convex_ball c R) h)
    have he := mem_sphere.mp hs
    linarith
  have hF : ContinuousOn (fun p : ℂ × (ι → ℝ) => carlsonCauchyKernel n z p.2 p.1 * f p.1)
      (sphere c R ×ˢ Convexity.StdSimplex.coordinateSet ℝ ι) :=
    ((continuousOn_carlsonCauchyKernel n z).mono (fun _ hp => ⟨hout hp.1, hp.2⟩)).mul
      (hf.comp continuous_fst.continuousOn (fun _ hp => hp.1))
  rw [← circleIntegral_regDirichletIntegral hb c hR hF]
  apply circleIntegral.integral_congr hR
  intro s _
  unfold regCarlsonResolvent regCarlsonDirichletAverage regDirichletIntegral
  dsimp only
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with u
  simp only [carlsonCauchyKernel]
  ring

/-- Carlson's Representation 5.11-2 on a circle, for every derivative order.
The native integral requires positive real parts of the Dirichlet parameters; no derivatives
of `f` on the boundary circle are assumed. -/
theorem regCarlsonDirichletAverage_iteratedDeriv_eq_circleIntegral
    (n : ℕ) {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) (z : ι → ℂ)
    {c : ℂ} {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (ball c R)) (hz : Set.range z ⊆ ball c R) :
    regCarlsonDirichletAverage b z (iteratedDeriv n f) =
      (n.factorial : ℂ) * (2 * (Real.pi : ℂ) * I)⁻¹ *
        ∮ s in C(c, R), regCarlsonResolvent n b z s * f s := by
  rw [circleIntegral_regCarlsonResolvent_mul n hb z hR.le
    (hf.continuousOn_ball.mono sphere_subset_closedBall) hz]
  unfold regCarlsonDirichletAverage regDirichletIntegral
  rw [← integral_const_mul]
  apply setIntegral_congr_fun (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
  intro u hu
  dsimp only
  rw [hf.iteratedDeriv_eq_circleIntegral_sub_zpow_mul hR n
    (convexHull_min hz (convex_ball c R) (carlsonAffineForm_mem_convexHull z hu))]
  simp only [carlsonCauchyKernel]
  ring

/-- Carlson's averaged Cauchy representation on a circle, for the zeroth derivative.
The native integral requires positive real parts of the Dirichlet parameters. -/
theorem regCarlsonDirichletAverage_eq_cauchyRepresentation
    {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) (z : ι → ℂ)
    {c : ℂ} {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (ball c R))
    (hz : Set.range z ⊆ ball c R) :
    regCarlsonDirichletAverage b z f = regCarlsonCauchyRepresentation b z c R f := by
  simpa [regCarlsonCauchyRepresentation] using
    regCarlsonDirichletAverage_iteratedDeriv_eq_circleIntegral 0 hb z hR hf hz

end DirichletTransform

end CarlsonCauchyAverage
