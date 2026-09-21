/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.Dirichlet.Average.Associated
public import LeanPool.CarlsonFunctions.Dirichlet.Transform

/-!
# Euler--Poisson equations for Carlson's Dirichlet averages

Tangential integration by parts proves the Euler--Poisson system first for large real
parts of the parameters. Analytic uniqueness extends it to the native convergence domain.
-/

open Complex MeasureTheory ProbabilityTheory

@[expose] public noncomputable section CarlsonDirichletAverage

namespace DirichletTransform

variable {ι : Type*} [Fintype ι]



open scoped Classical in
private lemma carlson_tangent_fderiv
    {Ω : Set ℂ} (hΩconv : Convex ℝ Ω) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    {z : ι → ℂ} (hz : Set.range z ⊆ Ω) (i j : ι)
    {u : ι → ℝ} (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) :
    fderiv ℝ (fun u => f (carlsonAffineForm z u)) u (Pi.single i 1 - Pi.single j 1) =
      (z i - z j) * deriv f (carlsonAffineForm z u) := by
  have hmem := convexHull_min hz hΩconv (carlsonAffineForm_mem_convexHull z hu)
  have hd := (hf _ hmem).differentiableAt.hasDerivAt.comp_hasFDerivAt u
    (hasFDerivAt_carlsonSimplex z u)
  erw [hd.fderiv]
  simp [carlsonSimplexCLM_tangent, mul_comm]

private lemma continuousOn_carlson_comp
    {Ω : Set ℂ} (hΩconv : Convex ℝ Ω) {f : ℂ → ℂ} (hf : ContinuousOn f Ω)
    {z : ι → ℂ} (hz : Set.range z ⊆ Ω) :
    ContinuousOn (fun u => f (carlsonAffineForm z u)) (Convexity.StdSimplex.coordinateSet ℝ ι) :=
  hf.comp (continuous_carlsonAffineForm z).continuousOn
    (fun _ hu => convexHull_min hz hΩconv (carlsonAffineForm_mem_convexHull z hu))

omit [Fintype ι] in
open scoped Classical in
private lemma addDirichletUnit_eq_add_single (b : ι → ℂ) (i : ι) :
    addDirichletUnit b i = b + Pi.single i 1 := by
  ext k
  by_cases h : k = i <;> simp [addDirichletUnit, h]

open scoped Classical in
/-- The tangential contiguous relation, on the native convergence domain. -/
theorem regCarlsonDirichletAverage_tangent
    {Ω : Set ℂ} (hΩconv : Convex ℝ Ω) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent) (hz : Set.range z ⊆ Ω)
    (i j : ι) (hij : i ≠ j) :
    (z i - z j) * regCarlsonDirichletAverage (addDirichletUnit (addDirichletUnit b j) i)
      z (deriv f) =
      regCarlsonDirichletAverage (addDirichletUnit b i) z f -
        regCarlsonDirichletAverage (addDirichletUnit b j) z f := by
  have hc := continuousOn_carlson_comp hΩconv hf.continuousOn hz
  have hdc := continuousOn_carlson_comp hΩconv hf.deriv.continuousOn hz
  have ha (g : ℂ → ℂ) (hg : ContinuousOn (fun u => g (carlsonAffineForm z u))
      (Convexity.StdSimplex.coordinateSet ℝ ι)) : AnalyticOnNhd ℂ
      (fun b => regCarlsonDirichletAverage b z g) mvBetaConvergent :=
    isOpen_mvBetaConvergent.analyticOn_iff_analyticOnNhd.mp (regDirichletIntegral_analyticOn hg)
  have hs (k : ι) (c : ι → ℂ) : AnalyticAt ℂ (fun b => addDirichletUnit b k) c := by
    simp_rw [addDirichletUnit_eq_add_single]
    exact analyticAt_id.add analyticAt_const
  have hleft : AnalyticOnNhd ℂ (fun b => (z i - z j) *
      regCarlsonDirichletAverage (addDirichletUnit (addDirichletUnit b j) i) z (deriv f))
      mvBetaConvergent := by
    intro b hb
    exact analyticAt_const.mul (((ha _ hdc) _
      (addDirichletUnit_mem_mvBetaConvergent (addDirichletUnit_mem_mvBetaConvergent hb j)
        i)).comp_of_eq
        ((hs i _).comp_of_eq (hs j b) rfl) rfl)
  have hright : AnalyticOnNhd ℂ (fun b =>
      regCarlsonDirichletAverage (addDirichletUnit b i) z f -
      regCarlsonDirichletAverage (addDirichletUnit b j) z f) mvBetaConvergent := by
    intro b hb
    exact (((ha _ hc) _ (addDirichletUnit_mem_mvBetaConvergent hb i)).comp_of_eq (hs i b) rfl).sub
      (((ha _ hc) _ (addDirichletUnit_mem_mvBetaConvergent hb j)).comp_of_eq (hs j b) rfl)
  apply hleft.eqOn_of_preconnected_of_eventuallyEq hright
    (by simpa using isPreconnected_dirichletConvergenceRegion (ι := ι) 0)
    (z₀ := fun _ => 3) (by intro k; norm_num) _ hb
  have hev : ∀ᶠ b : ι → ℂ in nhds (fun _ => 3), ∀ k, 2 < (b k).re := by
    apply Filter.eventually_all.mpr
    intro k
    exact (isOpen_lt continuous_const (Complex.continuous_re.comp (continuous_apply
      k))).eventually_mem
      (by norm_num)
  filter_upwards [hev] with b hb
  let q := addDirichletUnit (addDirichletUnit b j) i
  have hraise (c : ι → ℂ) (k : ι) (hc : ∀ l, 2 < (c l).re) :
      ∀ l, 2 < (addDirichletUnit c k l).re := by
    intro l
    by_cases hl : l = k
    · subst l
      simp only [addDirichletUnit, Function.update_self, add_re, one_re]
      linarith [hc k]
    · simpa [addDirichletUnit, hl] using hc l
  have hq : ∀ k, 2 < (q k).re := by
    exact hraise _ i (hraise _ j hb)
  have hdiff : ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι,
      DifferentiableAt ℝ (fun u => f (carlsonAffineForm z u)) u := by
    intro u hu
    have hd := (hf _ (convexHull_min hz hΩconv (carlsonAffineForm_mem_convexHull z
      hu))).differentiableAt
    exact (hd.restrictScalars ℝ).comp u (hasFDerivAt_carlsonSimplex z u).differentiableAt
  have heq {u : ι → ℝ} (hu : u ∈ Convexity.StdSimplex.coordinateSet ℝ ι) :=
    carlson_tangent_fderiv hΩconv hf hz i j hu
  have hdf : ContinuousOn (fun u => fderiv ℝ (fun u => f (carlsonAffineForm z u)) u
      (Pi.single i 1 - Pi.single j 1)) (Convexity.StdSimplex.coordinateSet ℝ ι) :=
    (continuousOn_const.mul hdc).congr (fun u hu => heq hu)
  have H := regDirichletIntegral_tangent_ibp j ⟨i, hij⟩ q hq hdiff hdf
  have hqi : q - Pi.single i 1 = addDirichletUnit b j := by
    simp [q, addDirichletUnit_eq_add_single]
  have hqj : q - Pi.single j 1 = addDirichletUnit b i := by
    simp [q, addDirichletUnit_eq_add_single]; abel
  rw [hqi, hqj] at H
  rw [show regDirichletIntegral q (fun u => fderiv ℝ (fun u => f (carlsonAffineForm z u)) u
      (Pi.single i 1 - Pi.single j 1)) =
      (z i - z j) * regCarlsonDirichletAverage q z (deriv f) from by
    unfold regCarlsonDirichletAverage regDirichletIntegral
    rw [← integral_const_mul]
    apply setIntegral_congr_fun (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
    intro u hu
    calc
      _ = regDirichletDensity q u * ((z i - z j) * deriv f (carlsonAffineForm z u)) := by
        exact congrArg (fun w : ℂ => regDirichletDensity q u * w) (heq hu)
      _ = _ := by ring] at H
  exact H

/-- **Carlson 5.4-1, regularized form.** A regularized Carlson average of a function
holomorphic on a convex domain satisfies the Euler--Poisson system on node vectors contained
in that domain. -/
theorem carlsonEulerPoissonOperator_regCarlsonDirichletAverage
    {Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent) (hz : Set.range z ⊆ Ω)
    (i j : ι) :
    carlsonEulerPoissonOperator i j b z
      (fun w => regCarlsonDirichletAverage b w f) = 0 := by
  by_cases hij : i = j
  · subst j
    exact carlsonEulerPoissonOperator_self i b z _
  have hbj := addDirichletUnit_mem_mvBetaConvergent hb j
  have hsecond : carlsonPartialDeriv i
      (carlsonPartialDeriv j (fun w => regCarlsonDirichletAverage b w f)) z =
      b i * b j * regCarlsonDirichletAverage (addDirichletUnit (addDirichletUnit b j) i)
        z (deriv (deriv f)) := by
    have H := carlsonIteratedPartialDeriv_regCarlsonDirichletAverage hΩopen hΩconv hf hb hz [i, j]
    simp only [carlsonIteratedPartialDeriv, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, List.length_cons, List.length_nil, iteratedDeriv_succ,
      iteratedDeriv_zero] at H
    rw [H]
    calc
      _ = regDirichletIntegral b (fun u => (u j : ℂ) *
          ((u i : ℂ) * deriv (deriv f) (carlsonAffineForm z u))) := by
        congr 1
        funext u
        ring
      _ = b j * regDirichletIntegral (addDirichletUnit b j)
          (fun u => (u i : ℂ) * deriv (deriv f) (carlsonAffineForm z u)) :=
        (mul_regDirichletIntegral_addDirichletUnit hb j _).symm
      _ = b j * (addDirichletUnit b j i *
          regCarlsonDirichletAverage (addDirichletUnit (addDirichletUnit b j) i)
            z (deriv (deriv f))) := by
        rw [← mul_regDirichletIntegral_addDirichletUnit hbj i]
        rfl
      _ = _ := by simp [addDirichletUnit, hij]; ring
  rw [carlsonEulerPoissonOperator, hsecond,
    carlsonPartialDeriv_regCarlsonDirichletAverage_of_analyticOnNhd hΩopen hΩconv hf hb hz j,
    carlsonPartialDeriv_regCarlsonDirichletAverage_of_analyticOnNhd hΩopen hΩconv hf hb hz i]
  have H := regCarlsonDirichletAverage_tangent hΩconv hf.deriv hb hz i j hij
  linear_combination b i * b j * H

/-- **Carlson 5.4-1.** The native Carlson Dirichlet average satisfies the Euler--Poisson
system on its convergence domain. -/
theorem carlsonEulerPoissonOperator_carlsonDirichletAverage
    {Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent) (hz : Set.range z ⊆ Ω)
    (i j : ι) :
    carlsonEulerPoissonOperator i j b z
      (fun w => Gamma (∑ k, b k) * regCarlsonDirichletAverage b w f) = 0 := by
  rw [carlsonEulerPoissonOperator_const_mul,
    carlsonEulerPoissonOperator_regCarlsonDirichletAverage hΩopen hΩconv hf hb hz,
    mul_zero]

end DirichletTransform

end CarlsonDirichletAverage
