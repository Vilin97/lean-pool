/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.PeriodFamily.Core7
import all LeanPool.HopfProblem.PeriodFamily.Core7

/-!
# Hopf problem: main theorem · six sphere cube 1

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

/-- The map collapsing a subset to the point at infinity of its complement. -/
public
def SixSphereCube.collapse {K : Type*} (F : Set K) (a : K) : OnePoint ↥Fᶜ := by
  classical exact if h : a ∈ F then (OnePoint.infty) else ((⟨a, h⟩ : ↥Fᶜ) : OnePoint ↥Fᶜ)

@[simp]
private theorem SixSphereCube.collapse_of_mem {K : Type*} (F : Set K) {a : K} (ha : a ∈ F) :
    collapse F a = (OnePoint.infty) := by classical simp only [collapse, dite_eq_left ha]

private theorem SixSphereCube.collapse_of_not_mem {K : Type*} (F : Set K) {a : K} (ha : a ∉ F) :
    collapse F a = ((⟨a, ha⟩ : ↥Fᶜ) : OnePoint ↥Fᶜ) := by
  classical simp only [collapse, dite_eq_right ha]

@[simp]
private theorem SixSphereCube.collapse_coe {K : Type*} (F : Set K) (a : ↥Fᶜ) :
    collapse F a.val = (a : OnePoint ↥Fᶜ) :=
  collapse_of_not_mem F a.property

@[simp]
private theorem SixSphereCube.collapse_eq_infty_iff {K : Type*} (F : Set K) (a : K) :
    collapse F a = (OnePoint.infty) ↔ a ∈ F := by
  classical
  by_cases ha : a ∈ F
  · simp only [SixSphereCube.collapse_of_mem F ha, ha]
  · simp only [collapse_of_not_mem F ha, OnePoint.coe_ne_infty, ha]

public
theorem SixSphereCube.collapse_eq_iff {K : Type*} (F : Set K) (a b : K) :
    collapse F a = collapse F b ↔ a = b ∨ a ∈ F ∧ b ∈ F := by
  classical
  constructor
  · intro h
    by_cases ha : a ∈ F
    · exact
        Or.inr
          ⟨ha, (collapse_eq_infty_iff F b).mp (h.symm.trans (SixSphereCube.collapse_of_mem F ha))⟩
    · have hb : b ∉ F := fun hb =>
        ha ((collapse_eq_infty_iff F a).mp (h.trans (SixSphereCube.collapse_of_mem F hb)))
      rw [collapse_of_not_mem F ha, collapse_of_not_mem F hb] at h
      exact Or.inl (congrArg Subtype.val (OnePoint.coe_injective h))
  · rintro (rfl | ⟨ha, hb⟩)
    · rfl
    · rw [SixSphereCube.collapse_of_mem F ha, SixSphereCube.collapse_of_mem F hb]

private theorem SixSphereCube.collapse_surjective {K : Type*} (F : Set K) (hne : F.Nonempty) :
    Function.Surjective (collapse F) := by
  intro z
  induction z using OnePoint.rec with
  | infty =>
    obtain ⟨a, ha⟩ := hne
    exact ⟨a, SixSphereCube.collapse_of_mem F ha⟩
  | coe a => exact ⟨a.val, collapse_coe F a⟩

private theorem SixSphereCube.collapse_preimage_of_not_mem {K : Type*} (F : Set K)
    (s : Set (OnePoint ↥Fᶜ)) (hs : (OnePoint.infty) ∉ s) :
    collapse F ⁻¹' s = Subtype.val '' (((↑) : ↥Fᶜ → OnePoint ↥Fᶜ) ⁻¹' s) := by
  ext a
  constructor
  · intro ha
    change collapse F a ∈ s at ha
    have haF : a ∉ F := by
      intro haF
      exact hs (by simpa only [SixSphereCube.collapse_of_mem F haF] using ha)
    exact ⟨⟨a, haF⟩, by simpa only [Set.mem_preimage, collapse_of_not_mem F haF] using ha, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    simpa only [Set.mem_preimage, collapse_coe] using hb

private theorem SixSphereCube.collapse_preimage_compl_of_mem {K : Type*} (F : Set K)
    (s : Set (OnePoint ↥Fᶜ)) (hs : (OnePoint.infty) ∈ s) :
    (collapse F ⁻¹' s)ᶜ = Subtype.val '' ((((↑) : ↥Fᶜ → OnePoint ↥Fᶜ) ⁻¹' s)ᶜ) :=
  collapse_preimage_of_not_mem F sᶜ (fun h => h hs)

private theorem
    SixSphereCube.continuous_collapse {K : Type*} [TopologicalSpace K] [T2Space K] (F : Set K)
    (hF : IsClosed F) : Continuous (collapse F) := by
  classical
  apply continuous_def.mpr
  intro s hs
  by_cases hinf : (OnePoint.infty) ∈ s
  · apply isClosed_compl_iff.mp
    rw [collapse_preimage_compl_of_mem F s hinf]
    exact (((OnePoint.isOpen_def.mp hs).1 hinf).image continuous_subtype_val).isClosed
  · rw [collapse_preimage_of_not_mem F s hinf]
    exact hF.isOpen_compl.isOpenMap_subtype_val _ (OnePoint.isOpen_def.mp hs).2

private def SixSphereCube.collapseMap {K : Type*} [TopologicalSpace K] [T2Space K] (F : Set K)
    (hF : IsClosed F) : C(K, OnePoint ↥Fᶜ) :=
  ⟨collapse F, continuous_collapse F hF⟩

private theorem SixSphereCube.isQuotientMap_collapse {K : Type*} [TopologicalSpace K] [T2Space K]
    (F : Set K) [CompactSpace K] (hF : IsClosed F) (hne : F.Nonempty) :
    Topology.IsQuotientMap (collapse F) := by
  let : LocallyCompactSpace ↥Fᶜ := hF.isOpen_compl.locallyCompactSpace
  exact
    Topology.IsQuotientMap.of_surjective_continuous (collapse_surjective F hne)
      (continuous_collapse F hF)

end Mathoverflow1973

end
