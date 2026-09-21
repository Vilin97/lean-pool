/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.SeveralComplexVariables.FunctionSpace
public import LeanPool.CarlsonFunctions.SeveralComplexVariables.LocallyBounded
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Topology.UniformSpace.Ascoli

/-!
# Montel's theorem

A family of holomorphic maps which is bounded uniformly on each compact subset of its
domain is equicontinuous. For finite-dimensional targets it has compact closure in the
compact-open topology. Compactness is supplied by Mathlib's Arzelà–Ascoli theorem.
-/

public section

open Complex Filter Function Metric Set
open scoped Topology

namespace CarlsonFunctions.SeveralComplexVariables

variable {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
open scoped Classical in
/-- Compact-local bounds on a holomorphic family give equicontinuity. Banach targets
are allowed here; finite dimensionality is needed only for compactness in Montel's theorem. -/
theorem equicontinuous_of_holomorphic_bounded_on_compacts
    {U : TopologicalSpace.Opens (ι → ℂ)} {S : Set (HolomorphicMap U F)}
    (hb : ∀ K ⊆ (U : Set (ι → ℂ)), IsCompact K → ∃ M : ℝ,
      ∀ f ∈ S, ∀ z ∈ K, ‖openExtension U f.val z‖ ≤ M) :
    Equicontinuous (fun f : S => (f.val.val : U → F)) := by
  intro c
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨R, hR, hRU⟩ := nhds_basis_closedBall.mem_iff.mp (U.isOpen.mem_nhds c.property)
  obtain ⟨M, hM⟩ := hb (closedBall (c : ι → ℂ) R) hRU (isCompact_closedBall _ _)
  let r := R / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have htwo : 2 * r = R := by dsimp [r]; ring
  let C : ℝ := (Fintype.card ι : ℝ) * (max M 0 / r)
  have hC : 0 ≤ C := mul_nonneg (Nat.cast_nonneg _) (div_nonneg (le_max_right _ _) hr.le)
  refine ⟨min r (ε / (C + 1)), lt_min hr (div_pos hε (by positivity)), ?_⟩
  intro w hw f
  have hwr : dist (w : ι → ℂ) c < r := (lt_min_iff.mp hw).1
  have hwe : dist (w : ι → ℂ) c < ε / (C + 1) := (lt_min_iff.mp hw).2
  have ha : ∀ z ∈ closedBall (c : ι → ℂ) (2 * r), ∀ i,
      AnalyticAt ℂ (fun v => openExtension U f.val.val (update z i v)) (z i) := by
    intro z hz i
    exact f.val.property.analyticAt_updateCarlson (hRU (by simpa only [htwo] using hz)) i
  have hbound : ∀ z ∈ closedBall (c : ι → ℂ) (2 * r),
      ‖openExtension U f.val.val z‖ ≤ max M 0 := by
    intro z hz
    exact (hM f.val f.property z (by simpa only [htwo] using hz)).trans (le_max_left _ _)
  have hn := norm_sub_le_of_separately_analytic_bounded hr ha hbound
    (mem_closedBall_self hr.le) (mem_closedBall.mpr hwr.le)
  simp only [openExtension_coe] at hn
  rw [dist_comm, dist_eq_norm]
  have hlt : (C + 1) * dist (w : ι → ℂ) c < ε := by
    nlinarith [(lt_div_iff₀ (by positivity : 0 < C + 1)).mp hwe]
  have hn' : ‖f.val.val w - f.val.val c‖ ≤ C * dist (w : ι → ℂ) c := by
    simpa only [C, dist_eq_norm] using hn
  nlinarith [show 0 ≤ dist (w : ι → ℂ) (c : ι → ℂ) from dist_nonneg]

/-- **Montel's theorem.** A compact-locally bounded family of holomorphic maps into a
finite-dimensional complex normed space has compact closure in the compact-open topology. -/
theorem isCompact_closure_of_holomorphic_bounded_on_compacts
    [FiniteDimensional ℂ F] {U : TopologicalSpace.Opens (ι → ℂ)}
    {S : Set (HolomorphicMap U F)}
    (hb : ∀ K ⊆ (U : Set (ι → ℂ)), IsCompact K → ∃ M : ℝ,
      ∀ f ∈ S, ∀ z ∈ K, ‖openExtension U f.val z‖ ≤ M) : IsCompact (closure S) := by
  let := FiniteDimensional.proper ℂ F
  let := UniformOnFun.t2Space_of_covering (β := F)
    (𝔖 := {K : Set U | IsCompact K}) (by
      apply eq_univ_iff_forall.mpr
      intro z
      exact mem_sUnion_of_mem (mem_singleton z) isCompact_singleton)
  have he : Topology.IsClosedEmbedding
      (UniformOnFun.ofFun {K : Set U | IsCompact K} ∘
        (fun f : HolomorphicMap U F => (f.val : U → F))) := by
    exact (ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.comp
      isUniformEmbedding_subtype_val).isClosedEmbedding
  apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding (fun K hK => hK) he
  · intro K hK
    exact (equicontinuous_of_holomorphic_bounded_on_compacts hb).equicontinuousOn K
  · intro K hK z hz
    obtain ⟨M, hM⟩ := hb {(z : ι → ℂ)} (singleton_subset_iff.mpr z.property) isCompact_singleton
    refine ⟨closedBall (0 : F) (max M 0), isCompact_closedBall _ _, ?_⟩
    intro f hf
    have h := (hM f hf z (mem_singleton _)).trans (le_max_left M 0)
    simpa using h

end CarlsonFunctions.SeveralComplexVariables

end
