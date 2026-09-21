/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.Dirichlet.Average.Continuation

/-!
# Associated relations on the full parameter space

The regularized identities of Carlson, Section 5.6, persist under analytic
continuation. All Dirichlet parameters below are arbitrary complex numbers.
The derivative appearing here is the derivative of the function being averaged.
-/

open Complex Set MeasureTheory ProbabilityTheory
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

open scoped Classical in
/-- Parameter shifts are translations, hence entire. -/
theorem analyticAt_addDirichletUnit (i : ι) (b : ι → ℂ) :
    AnalyticAt ℂ (fun c => addDirichletUnit c i) b := by
  have h (c : ι → ℂ) : addDirichletUnit c i = c + Pi.single i 1 := by
    ext k
    by_cases hk : k = i <;> simp [addDirichletUnit, hk]
  simp_rw [h]
  exact analyticAt_id.add analyticAt_const

/-- Entire-parameter version of Carlson's relation 5.6-1(4). -/
theorem IsRegCarlsonContinuation.sum_shift {f : ℂ → ℂ} {z : ι → ℂ}
    {G : (ι → ℂ) → ℂ} (hG : IsRegCarlsonContinuation f z G)
    (hf : ContinuousOn (fun u => f (carlsonAffineForm z u)) (Convexity.StdSimplex.coordinateSet ℝ
      ι))
    (b : ι → ℂ) : G b = ∑ i, b i * G (addDirichletUnit b i) := by
  apply congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent hG.1 ?_ ?_) b
  · intro c _
    exact Finset.analyticAt_fun_sum _ fun i _ =>
      ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt c).mul
      ((hG.1 _ (mem_univ _)).comp_of_eq (analyticAt_addDirichletUnit i c) rfl)
  · intro c hc
    dsimp only
    rw [hG.eq_native hc, regCarlsonDirichletAverage_eq_sum_addDirichletUnit hc z f hf]
    apply Finset.sum_congr rfl
    intro i _
    rw [hG.eq_native (addDirichletUnit_mem_mvBetaConvergent hc i)]

/-- The tangential associated relation, with no restrictions on the parameters.
The coincident-index case is included. -/
theorem IsRegCarlsonContinuation.tangent
    {Ω : Set ℂ} (hΩconv : Convex ℝ Ω) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    {z : ι → ℂ} (hz : range z ⊆ Ω) {G D : (ι → ℂ) → ℂ}
    (hG : IsRegCarlsonContinuation f z G) (hD : IsRegCarlsonContinuation (deriv f) z D)
    (b : ι → ℂ) (i j : ι) :
    (z i - z j) * D (addDirichletUnit (addDirichletUnit b j) i) =
      G (addDirichletUnit b i) - G (addDirichletUnit b j) := by
  by_cases hij : i = j
  · subst j; simp
  apply congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent ?_ ?_ ?_) b
  · intro c _
    exact analyticAt_const.mul ((hD.1 _ (mem_univ _)).comp_of_eq
      ((analyticAt_addDirichletUnit i _).comp_of_eq (analyticAt_addDirichletUnit j c) rfl) rfl)
  · intro c _
    exact ((hG.1 _ (mem_univ _)).comp_of_eq (analyticAt_addDirichletUnit i c) rfl).sub
      ((hG.1 _ (mem_univ _)).comp_of_eq (analyticAt_addDirichletUnit j c) rfl)
  · intro c hc
    dsimp only
    rw [hD.eq_native (addDirichletUnit_mem_mvBetaConvergent
      (addDirichletUnit_mem_mvBetaConvergent hc j) i),
      hG.eq_native (addDirichletUnit_mem_mvBetaConvergent hc i),
      hG.eq_native (addDirichletUnit_mem_mvBetaConvergent hc j)]
    exact regCarlsonDirichletAverage_tangent hΩconv hf hc hz i j hij

open scoped Classical in
/-- Carlson's backward-shift relation 5.6-2, in entire regularized form. -/
theorem IsRegCarlsonContinuation.tangent_sub
    {Ω : Set ℂ} (hΩconv : Convex ℝ Ω) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    {z : ι → ℂ} (hz : range z ⊆ Ω) {G D : (ι → ℂ) → ℂ}
    (hG : IsRegCarlsonContinuation f z G) (hD : IsRegCarlsonContinuation (deriv f) z D)
    (b : ι → ℂ) (i j : ι) :
    (z i - z j) * D b = G (b - Pi.single j 1) - G (b - Pi.single i 1) := by
  by_cases hij : i = j
  · subst j; simp
  have h := hG.tangent hΩconv hf hz hD (b - Pi.single i 1 - Pi.single j 1) i j
  have hi : addDirichletUnit (b - Pi.single i 1 - Pi.single j 1) i = b - Pi.single j 1 := by
    ext k
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp_all [addDirichletUnit, sub_add_cancel]
  have hj : addDirichletUnit (b - Pi.single i 1 - Pi.single j 1) j = b - Pi.single i 1 := by
    ext k
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp_all [addDirichletUnit, sub_add_cancel]
  have hij' : addDirichletUnit (b - Pi.single i 1) i = b := by
    ext k
    by_cases hk : k = i <;> simp [addDirichletUnit, hk]
  simpa only [hi, hj, hij'] using h

open scoped Classical in
/-- Carlson's three-node associated relation 5.6-3. No distinctness assumptions
on the nodes, indices, or Dirichlet parameters are needed. -/
theorem IsRegCarlsonContinuation.three_node
    {Ω : Set ℂ} (hΩconv : Convex ℝ Ω) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    {z : ι → ℂ} (hz : range z ⊆ Ω) {G : (ι → ℂ) → ℂ}
    (hG : IsRegCarlsonContinuation f z G) (hΩopen : IsOpen Ω)
    (b : ι → ℂ) (i j k : ι) :
    (z i - z j) * G (b - Pi.single k 1) +
      (z j - z k) * G (b - Pi.single i 1) +
      (z k - z i) * G (b - Pi.single j 1) = 0 := by
  obtain ⟨D, hD⟩ := exists_isRegCarlsonContinuation hΩopen hΩconv hf.deriv hz
  have hij := hG.tangent_sub hΩconv hf hz hD b i j
  have hjk := hG.tangent_sub hΩconv hf hz hD b j k
  linear_combination (z j - z k) * hij - (z i - z j) * hjk

/-- Multiplication of the function being averaged by its argument is a weighted
sum of parameter shifts, on the native integral domain. -/
theorem regCarlsonDirichletAverage_mul_arg {b z : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) (f : ℂ → ℂ)
    (hf : ContinuousOn (fun u => f (carlsonAffineForm z u)) (Convexity.StdSimplex.coordinateSet ℝ
      ι)) :
    regCarlsonDirichletAverage b z (fun w => w * f w) =
      ∑ i, z i * (b i * regCarlsonDirichletAverage (addDirichletUnit b i) z f) := by
  simp_rw [regCarlsonDirichletAverage, mul_regDirichletIntegral_addDirichletUnit hb,
    ← regDirichletIntegral_smul]
  unfold regDirichletIntegral
  rw [← integral_finsetSum]
  · apply setIntegral_congr_fun (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
    intro u _
    dsimp only
    rw [← Finset.mul_sum]
    congr 1
    simp only [carlsonAffineForm, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · intro i _
    exact integrableOn_regDirichletDensity_mul b hb
      (continuousOn_const.mul
        ((Complex.continuous_ofReal.comp (continuous_apply i)).continuousOn.mul hf))

/-- Entire-parameter multiplication-by-argument identity. -/
theorem IsRegCarlsonContinuation.mul_arg {f : ℂ → ℂ} {z : ι → ℂ}
    {G H : (ι → ℂ) → ℂ} (hG : IsRegCarlsonContinuation f z G)
    (hH : IsRegCarlsonContinuation (fun w => w * f w) z H)
    (hf : ContinuousOn (fun u => f (carlsonAffineForm z u)) (Convexity.StdSimplex.coordinateSet ℝ
      ι))
    (b : ι → ℂ) : H b = ∑ i, z i * (b i * G (addDirichletUnit b i)) := by
  apply congrFun (analyticOnNhd_eq_of_eqOn_mvBetaConvergent hH.1 ?_ ?_) b
  · intro c _
    exact Finset.analyticAt_fun_sum _ fun i _ => analyticAt_const.mul
      (((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt c).mul
        ((hG.1 _ (mem_univ _)).comp_of_eq (analyticAt_addDirichletUnit i c) rfl))
  · intro c hc
    dsimp only
    rw [hH.eq_native hc, regCarlsonDirichletAverage_mul_arg hc f hf]
    apply Finset.sum_congr rfl
    intro i _
    rw [hG.eq_native (addDirichletUnit_mem_mvBetaConvergent hc i)]

/-- Carlson's relation 5.6-4, in regularized form on the entire parameter space.
`D` averages `f'`, while `H` averages `w * f'(w)`. -/
theorem IsRegCarlsonContinuation.associated
    {Ω : Set ℂ} (hΩconv : Convex ℝ Ω) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    {z : ι → ℂ} (hz : range z ⊆ Ω) {G D H : (ι → ℂ) → ℂ}
    (hG : IsRegCarlsonContinuation f z G) (hD : IsRegCarlsonContinuation (deriv f) z D)
    (hH : IsRegCarlsonContinuation (fun w => w * deriv f w) z H)
    (b : ι → ℂ) (i : ι) :
    G b = H (addDirichletUnit b i) - z i * D (addDirichletUnit b i) +
      (∑ j, b j) * G (addDirichletUnit b i) := by
  have hc : ContinuousOn (fun u => f (carlsonAffineForm z u)) (Convexity.StdSimplex.coordinateSet
    ℝ ι) :=
    hf.continuousOn.comp (continuous_carlsonAffineForm z).continuousOn
      (fun _ hu => convexHull_min hz hΩconv (carlsonAffineForm_mem_convexHull z hu))
  have hdc : ContinuousOn (fun u => deriv f (carlsonAffineForm z u))
    (Convexity.StdSimplex.coordinateSet ℝ ι) :=
    hf.deriv.continuousOn.comp (continuous_carlsonAffineForm z).continuousOn
      (fun _ hu => convexHull_min hz hΩconv (carlsonAffineForm_mem_convexHull z hu))
  have ht (j : ι) : (z j - z i) *
      (addDirichletUnit b i j * D (addDirichletUnit (addDirichletUnit b i) j)) =
      b j * (G (addDirichletUnit b j) - G (addDirichletUnit b i)) := by
    by_cases hji : j = i
    · subst j; simp
    rw [show addDirichletUnit b i j = b j by simp [addDirichletUnit, hji]]
    calc
      _ = b j * ((z j - z i) * D (addDirichletUnit (addDirichletUnit b i) j)) := by ring
      _ = _ := congrArg (b j * ·) (hG.tangent hΩconv hf hz hD b j i)
  have heq : H (addDirichletUnit b i) - z i * D (addDirichletUnit b i) =
      G b - (∑ j, b j) * G (addDirichletUnit b i) := by
    rw [hD.mul_arg hH hdc, hD.sum_shift hdc (addDirichletUnit b i),
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    simp_rw [← sub_mul, ht]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, ← hG.sum_shift hc b]
  linear_combination -heq

end DirichletTransform
end
