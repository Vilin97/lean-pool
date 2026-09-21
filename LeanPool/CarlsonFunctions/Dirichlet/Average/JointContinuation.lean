/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/

/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import LeanPool.CarlsonFunctions.Dirichlet.Average.Continuation
public import LeanPool.CarlsonFunctions.Dirichlet.Transform.Parametric

/-!
# Joint continuation of general Carlson averages

The continuation assertion of Carlson's Theorem 6.3-6 (1977, p. 138): if `f` is
holomorphic on a convex open set `Ω`, its Gamma-regularized Dirichlet average is jointly
holomorphic in all Dirichlet parameters and all nodes in `Ω`. The same holds for averages
of every derivative of `f`. No common disk containing the nodes is required.

The proof uses parametric tangential integration by parts, not Carlson's contour
construction. The general rectifiable Jordan-curve representation in that theorem is
a separate remaining assertion; this file does not prove that representation.
-/

open Complex MeasureTheory ProbabilityTheory Set
@[expose] public noncomputable section
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- **Carlson 6.3-6, continuation assertion for `n = 0`.** A regularized Dirichlet
average has a continuation jointly holomorphic on `ℂ^ι × Ω^ι`, where `Ω` is any convex
open set on which the averaged scalar function is holomorphic. -/
theorem exists_joint_isRegCarlsonContinuation
    {Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω) :
    ∃ G : ((ι → ℂ) × (ι → ℂ)) → ℂ,
      AnalyticOnNhd ℂ G {p | Set.range p.2 ⊆ Ω} ∧
      ∀ z, Set.range z ⊆ Ω → IsRegCarlsonContinuation f z (fun b => G (b, z)) := by
  let U : Set (ι → ℂ) := {z | Set.range z ⊆ Ω}
  have hU : IsOpen U := by
    simp only [U, Set.range_subset_iff, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => hΩopen.preimage (continuous_apply i)
  let A := fun p : (ι → ℂ) × (ι → ℂ) => ∑ i, p.2 i * p.1 i
  have hA : AnalyticOnNhd ℂ A univ := by
    intro p _
    apply Finset.analyticAt_fun_sum
    intro i _
    exact (((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt p.2).comp_of_eq
      analyticAt_snd rfl).mul
      (((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).analyticAt p.1).comp_of_eq analyticAt_fst rfl)
  have hWo : IsOpen (A ⁻¹' Ω) := hΩopen.preimage (continuousOn_univ.mp hA.continuousOn)
  have hH : AnalyticOnNhd ℂ (fun p => f (A p)) (A ⁻¹' Ω) :=
    fun p hp => (hf (A p) hp).comp_of_eq (hA p (mem_univ _)) rfl
  have hW : ∀ z ∈ U, ∀ u ∈ Convexity.StdSimplex.coordinateSet ℝ ι,
      (z, fun i => (u i : ℂ)) ∈ A ⁻¹' Ω := by
    intro z hz u hu
    exact convexHull_min hz hΩconv (carlsonAffineForm_mem_convexHull z hu)
  obtain ⟨G, hG, hGeq⟩ := exists_entire_joint_regDirichletContinuation_kernel hU hWo hH hW
  refine ⟨G, hG.mono (fun p hp => ⟨mem_univ _, hp⟩), ?_⟩
  intro z hz
  refine ⟨?_, hGeq z hz⟩
  intro b _
  exact (hG (b, z) ⟨mem_univ _, hz⟩).comp_of_eq (analyticAt_id.prod analyticAt_const) rfl

/-- Any family already characterized by the native integral and entire parameter
dependence inherits joint holomorphy. No change of its definition is necessary. -/
theorem analyticOnNhd_joint_of_isRegCarlsonContinuation
    {Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω)
    {G : ((ι → ℂ) × (ι → ℂ)) → ℂ}
    (hG : ∀ z, Set.range z ⊆ Ω → IsRegCarlsonContinuation f z (fun b => G (b, z))) :
    AnalyticOnNhd ℂ G {p | Set.range p.2 ⊆ Ω} := by
  obtain ⟨F, hF, hFc⟩ := exists_joint_isRegCarlsonContinuation hΩopen hΩconv hf (ι := ι)
  have hU : IsOpen {p : (ι → ℂ) × (ι → ℂ) | Set.range p.2 ⊆ Ω} := by
    simp only [Set.range_subset_iff, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => hΩopen.preimage
      ((continuous_apply i).comp continuous_snd)
  exact hF.congr hU (fun p hp => congrFun ((hFc p.2 hp).eq (hG p.2 hp)) p.1)

/-- **Carlson 6.3-6, continuation assertion for every derivative order.** This is the
joint holomorphic extension of `F⁽ⁿ⁾(b,z) / Γ(∑ bᵢ)` to all complex Dirichlet parameters. -/
theorem exists_joint_isRegCarlsonContinuation_iteratedDeriv
    {Ω : Set ℂ} (hΩopen : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Ω) (n : ℕ) :
    ∃ G : ((ι → ℂ) × (ι → ℂ)) → ℂ,
      AnalyticOnNhd ℂ G {p | Set.range p.2 ⊆ Ω} ∧
      ∀ z, Set.range z ⊆ Ω → IsRegCarlsonContinuation (iteratedDeriv n f) z (fun b => G (b, z)) := by
  apply exists_joint_isRegCarlsonContinuation hΩopen hΩconv
  induction n with
  | zero => simpa using hf
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv

end DirichletTransform
end
