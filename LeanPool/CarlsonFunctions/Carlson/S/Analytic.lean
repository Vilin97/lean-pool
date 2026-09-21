/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Carlson.S.Series

/-! # Joint holomorphy and locally uniform S-series convergence -/

open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- Each exponential-series term is jointly entire in its parameters and nodes. -/
private theorem analyticOnNhd_regCarlsonSTerm_joint (n : ℕ) :
    AnalyticOnNhd ℂ (fun q : Sum ι ι → ℂ =>
      (Nat.factorial n : ℂ)⁻¹ * regCarlsonR n (fun i => q (.inr i)) (fun i => q (.inl i)))
      Set.univ := by
  intro q _
  exact analyticAt_const.mul (analyticAt_regCarlsonR_comp
    (b := fun q : Sum ι ι → ℂ => fun i => q (.inl i))
    (z := fun q : Sum ι ι → ℂ => fun i => q (.inr i)) (x := q)
    (fun i => (ContinuousLinearMap.proj (R := ℂ) (.inl i)).analyticAt q)
    (fun i => (ContinuousLinearMap.proj (R := ℂ) (.inr i)).analyticAt q) n)

/-- The exponential series converges locally uniformly jointly in parameters and nodes.
The coordinates `Sum.inl i` represent parameters and `Sum.inr i` represent nodes. -/
theorem hasSumLocallyUniformlyOn_regCarlsonSSeries_joint :
    HasSumLocallyUniformlyOn
      (fun (n : ℕ) (q : Sum ι ι → ℂ) =>
        (Nat.factorial n : ℂ)⁻¹ * regCarlsonR n (fun i => q (.inr i)) (fun i => q (.inl i)))
      (fun q => regCarlsonSSeries (fun i => q (.inr i)) (fun i => q (.inl i))) Set.univ := by
  have hs : SummableLocallyUniformlyOn
      (fun (n : ℕ) (q : Sum ι ι → ℂ) =>
        (Nat.factorial n : ℂ)⁻¹ * regCarlsonR n (fun i => q (.inr i)) (fun i => q (.inl i)))
      Set.univ := by
    apply SummableLocallyUniformlyOn_of_locally_bounded isOpen_univ
    intro K hKuniv hK
    have hc : Continuous (fun q : Sum ι ι → ℂ => ∑ i, ‖q (.inr i)‖) := by fun_prop
    obtain ⟨Z₀, hZ₀⟩ := hK.bddAbove_image hc.continuousOn
    have hp : Continuous (fun q : Sum ι ι → ℂ => fun i => q (.inl i)) := by fun_prop
    obtain ⟨M, hM, hbound⟩ :=
      exists_summable_norm_regCarlsonR_div_factorial_bounded_variables
        (hK.image hp) (le_max_right Z₀ 0)
    refine ⟨M, hM, fun n q hq => hbound n _ (Set.mem_image_of_mem _ hq) _ ?_⟩
    exact (hZ₀ (Set.mem_image_of_mem _ hq)).trans (le_max_left _ _)
  simpa only [regCarlsonSSeries_eq_tsum_regCarlsonR] using hs.hasSumLocallyUniformlyOn

/-- The continued S-function is jointly entire in parameters and nodes, by locally uniform
convergence of the R-polynomial expansion. A sum index encodes the two vectors. -/
theorem analyticOnNhd_regCarlsonSSeries_joint :
    AnalyticOnNhd ℂ (fun q : Sum ι ι → ℂ =>
      regCarlsonSSeries (fun i => q (.inr i)) (fun i => q (.inl i))) Set.univ :=
  hasSumLocallyUniformlyOn_regCarlsonSSeries_joint.analyticOnNhd_pi
    analyticOnNhd_regCarlsonSTerm_joint isOpen_univ

/-- Carlson's finite exponential sums are jointly entire in parameters and nodes. -/
theorem analyticOnNhd_regCarlsonSPartialSum_joint (N : ℕ) :
    AnalyticOnNhd ℂ (fun q : Sum ι ι → ℂ =>
      regCarlsonSPartialSum N (fun i => q (.inr i)) (fun i => q (.inl i))) Set.univ :=
  Finset.analyticOnNhd_fun_sum _ (fun n _ => analyticOnNhd_regCarlsonSTerm_joint n)

/-- Carlson's partial sums converge locally uniformly jointly in all parameters and nodes. -/
theorem tendstoLocallyUniformlyOn_regCarlsonSPartialSum_joint :
    TendstoLocallyUniformlyOn (fun N (q : Sum ι ι → ℂ) =>
      regCarlsonSPartialSum N (fun i => q (.inr i)) (fun i => q (.inl i)))
      (fun q => regCarlsonSSeries (fun i => q (.inr i)) (fun i => q (.inl i)))
      Filter.atTop Set.univ :=
  hasSumLocallyUniformlyOn_regCarlsonSSeries_joint.tendstoLocallyUniformlyOn_finsetRange

/-- Arbitrary mixed parameter/node derivatives of the exponential series may be taken
term by term, retaining locally uniform convergence. -/
theorem hasSumLocallyUniformlyOn_carlsonIteratedPartialDeriv_regCarlsonSSeries_joint
    (is : List (Sum ι ι)) :
    HasSumLocallyUniformlyOn
      (fun n : ℕ => carlsonIteratedPartialDeriv is (fun q : Sum ι ι → ℂ =>
        (Nat.factorial n : ℂ)⁻¹ * regCarlsonR n (fun i => q (.inr i)) (fun i => q (.inl i))))
      (carlsonIteratedPartialDeriv is (fun q : Sum ι ι → ℂ =>
        regCarlsonSSeries (fun i => q (.inr i)) (fun i => q (.inl i)))) Set.univ := by
  simp only [carlsonIteratedPartialDeriv_eq_iteratedPartialDeriv]
  exact hasSumLocallyUniformlyOn_regCarlsonSSeries_joint.iteratedPartialDeriv
    analyticOnNhd_regCarlsonSTerm_joint isOpen_univ is

/-- All mixed parameter/node derivatives of the partial sums converge locally uniformly. -/
theorem tendstoLocallyUniformlyOn_carlsonIteratedPartialDeriv_regCarlsonSPartialSum_joint
    (is : List (Sum ι ι)) :
    TendstoLocallyUniformlyOn (fun N => carlsonIteratedPartialDeriv is
      (fun q : Sum ι ι → ℂ => regCarlsonSPartialSum N (fun i => q (.inr i)) (fun i => q (.inl i))))
      (carlsonIteratedPartialDeriv is (fun q : Sum ι ι → ℂ =>
        regCarlsonSSeries (fun i => q (.inr i)) (fun i => q (.inl i)))) Filter.atTop Set.univ := by
  simp only [carlsonIteratedPartialDeriv_eq_iteratedPartialDeriv]
  exact tendstoLocallyUniformlyOn_regCarlsonSPartialSum_joint.iteratedPartialDeriv
    (Filter.Eventually.of_forall analyticOnNhd_regCarlsonSPartialSum_joint) isOpen_univ is

/-- The iterated Fréchet derivatives of the partial sums converge in multilinear operator
norm, locally uniformly jointly in the parameters and nodes. -/
theorem tendstoLocallyUniformlyOn_iteratedFDeriv_regCarlsonSPartialSum_joint (k : ℕ) :
    TendstoLocallyUniformlyOn (fun N => iteratedFDeriv ℂ k
      (fun q : Sum ι ι → ℂ => regCarlsonSPartialSum N (fun i => q (.inr i)) (fun i => q (.inl i))))
      (iteratedFDeriv ℂ k (fun q : Sum ι ι → ℂ =>
        regCarlsonSSeries (fun i => q (.inr i)) (fun i => q (.inl i)))) Filter.atTop Set.univ :=
  tendstoLocallyUniformlyOn_regCarlsonSPartialSum_joint.iteratedFDeriv_pi
    (Filter.Eventually.of_forall analyticOnNhd_regCarlsonSPartialSum_joint) isOpen_univ k

/-- The continued S-function is entire in its node vector. -/
theorem analyticOnNhd_regCarlsonSSeries_variables (b : ι → ℂ) :
    AnalyticOnNhd ℂ (fun z : ι → ℂ => regCarlsonSSeries z b) Set.univ := by
  intro z _
  have hmap : AnalyticAt ℂ (fun z : ι → ℂ => Sum.elim b z) z := by
    apply AnalyticAt.pi
    intro k
    cases k with
    | inl i => exact analyticAt_const
    | inr i => exact (ContinuousLinearMap.proj (R := ℂ) i).analyticAt z
  have H := (analyticOnNhd_regCarlsonSSeries_joint (Sum.elim b z)
    (Set.mem_univ _)).comp_of_eq hmap rfl
  simpa only [Sum.elim_inl, Sum.elim_inr] using! H

/-- On the native Dirichlet convergence region, the regularized integral is jointly entire
in the Carlson variables. -/
theorem analyticOnNhd_regCarlsonSIntegral_variables {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) :
    AnalyticOnNhd ℂ (regCarlsonSIntegral b) Set.univ := by
  change AnalyticOnNhd ℂ (fun z => regCarlsonDirichletAverage b z exp) Set.univ
  simpa using
    (analyticOnNhd_regCarlsonDirichletAverage_nodes
      (Ω := Set.univ) isOpen_univ (convex_univ : Convex ℝ (Set.univ : Set ℂ))
      analyticOnNhd_cexp hb)

end DirichletTransform
