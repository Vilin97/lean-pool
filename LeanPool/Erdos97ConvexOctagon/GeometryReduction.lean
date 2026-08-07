/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.Basic
import LeanPool.Erdos97ConvexOctagon.Incidence
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Convex.Independent
import Mathlib.Geometry.Euclidean.PerpBisector

/-! # Erdős 97 convex-octagon formalization: Geometry Reduction -/

namespace Erdos97Octagon

open scoped RealInnerProductSpace

/-- A vertex has four other labelled vertices at one common distance. -/
def HasFourEquidistant (p : Vertex → Plane) (v : Vertex) : Prop :=
  ∃ S : Finset Vertex, S.card = 4 ∧ v ∉ S ∧
    ∃ r : ℝ, ∀ w ∈ S, dist (p v) (p w) = r

/-- A labelled incidence system is realised by equal-distance rows in the plane. -/
def Realises (p : Vertex → Plane) (Q : OctagonIncidence) : Prop :=
  ∀ v, ∃ r : ℝ, ∀ w ∈ Q.targets v, dist (p v) (p w) = r

private lemma three_centres_collinear
    {a b v₁ v₂ v₃ : Plane} (hab : a ≠ b)
    (h1 : dist v₁ a = dist v₁ b)
    (h2 : dist v₂ a = dist v₂ b)
    (h3 : dist v₃ a = dist v₃ b) :
    Collinear ℝ ({v₁, v₂, v₃} : Set Plane) := by
  have hne : b -ᵥ a ≠ 0 := fun h => hab (vsub_eq_zero_iff_eq.mp h).symm
  have h1' : dist a v₁ = dist b v₁ := by
    rw [dist_comm a, dist_comm b]
    exact h1
  have h2' : dist a v₂ = dist b v₂ := by
    rw [dist_comm a, dist_comm b]
    exact h2
  have h3' : dist a v₃ = dist b v₃ := by
    rw [dist_comm a, dist_comm b]
    exact h3
  have hinn₁₂ : ⟪v₂ -ᵥ v₁, b -ᵥ a⟫ = (0 : ℝ) :=
    EuclideanGeometry.inner_vsub_vsub_of_dist_eq_of_dist_eq h1' h2'
  have hinn₁₃ : ⟪v₃ -ᵥ v₁, b -ᵥ a⟫ = (0 : ℝ) :=
    EuclideanGeometry.inner_vsub_vsub_of_dist_eq_of_dist_eq h1' h3'
  have hfd : Module.finrank ℝ Plane = 1 + 1 := by
    rw [finrank_euclideanSpace]
    norm_num
  let : Fact (Module.finrank ℝ Plane = 1 + 1) := ⟨hfd⟩
  have hfo : Module.finrank ℝ ((ℝ ∙ (b -ᵥ a) : Submodule ℝ Plane))ᗮ = 1 :=
    Submodule.finrank_orthogonal_span_singleton hne
  have horth : vectorSpan ℝ ({v₁, v₂, v₃} : Set Plane) ≤
      (ℝ ∙ (b -ᵥ a) : Submodule ℝ Plane)ᗮ := by
    rw [vectorSpan_eq_span_vsub_set_right_ne ℝ (Set.mem_insert v₁ _)]
    rw [Submodule.span_le]
    intro w hw
    rw [Set.mem_image] at hw
    obtain ⟨q, hq, rfl⟩ := hw
    have hq_ne : q ≠ v₁ := fun h => hq.2 (by simpa using h)
    have hq_cases : q = v₂ ∨ q = v₃ := by
      rcases hq.1 with hq | hq
      · exact absurd hq hq_ne
      rcases hq with hq | hq
      · exact Or.inl hq
      · simpa using Or.inr hq
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left]
    rcases hq_cases with rfl | rfl
    · exact hinn₁₂
    · exact hinn₁₃
  let : FiniteDimensional ℝ (vectorSpan ℝ ({v₁, v₂, v₃} : Set Plane)) :=
    Submodule.finiteDimensional_of_le horth
  rw [collinear_iff_finrank_le_one]
  calc
    Module.finrank ℝ (vectorSpan ℝ ({v₁, v₂, v₃} : Set Plane)) ≤
        Module.finrank ℝ ((ℝ ∙ (b -ᵥ a) : Submodule ℝ Plane))ᗮ :=
      Submodule.finrank_mono horth
    _ = 1 := hfo

/-- Three distinct members of a convex-independent family cannot be collinear. -/
theorem three_collinear_not_convexIndependent
    {p : Vertex → Plane} (hC : ConvexIndependent ℝ p)
    {i j k : Vertex} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hCol : Collinear ℝ ({p i, p j, p k} : Set Plane)) :
    False := by
  rcases hCol.wbtw_or_wbtw_or_wbtw with hW | hW | hW
  · have hj : j ∈ ({i, k} : Set Vertex) := hC {i, k} j (by
      simpa only [Set.image_insert_eq, Set.image_singleton, convexHull_pair] using hW.mem_segment)
    simp [hij.symm, hjk] at hj
  · have hk : k ∈ ({j, i} : Set Vertex) := hC {j, i} k (by
      simpa only [Set.image_insert_eq, Set.image_singleton, convexHull_pair] using hW.mem_segment)
    simp [hjk.symm, hik.symm] at hk
  · have hi : i ∈ ({k, j} : Set Vertex) := hC {k, j} i (by
      simpa only [Set.image_insert_eq, Set.image_singleton, convexHull_pair] using hW.mem_segment)
    simp [hij, hik] at hi

/-- At most two vertices of a convex-independent planar family are equidistant
from any fixed pair of distinct vertices. -/
theorem equidistantCentres_card_le_two
    {p : Vertex → Plane} (hC : ConvexIndependent ℝ p)
    {a b : Vertex} (hab : a ≠ b) :
    (Finset.univ.filter fun v => dist (p v) (p a) = dist (p v) (p b)).card ≤ 2 := by
  classical
  by_contra hgt
  let S := Finset.univ.filter fun v => dist (p v) (p a) = dist (p v) (p b)
  change ¬ S.card ≤ 2 at hgt
  have h3 : 3 ≤ S.card := by omega
  obtain ⟨v₁, v₂, v₃, hv₁S, hv₂S, hv₃S, h12, h13, h23⟩ :
      ∃ v₁ v₂ v₃ : Vertex, v₁ ∈ S ∧ v₂ ∈ S ∧ v₃ ∈ S ∧
        v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃ := by
    obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq h3
    rw [Finset.card_eq_three] at hTcard
    obtain ⟨v₁, v₂, v₃, h12, h13, h23, rfl⟩ := hTcard
    exact ⟨v₁, v₂, v₃, hTS (by simp), hTS (by simp), hTS (by simp), h12, h13, h23⟩
  have e1 : dist (p v₁) (p a) = dist (p v₁) (p b) := (Finset.mem_filter.mp hv₁S).2
  have e2 : dist (p v₂) (p a) = dist (p v₂) (p b) := (Finset.mem_filter.mp hv₂S).2
  have e3 : dist (p v₃) (p a) = dist (p v₃) (p b) := (Finset.mem_filter.mp hv₃S).2
  have hCol : Collinear ℝ ({p v₁, p v₂, p v₃} : Set Plane) :=
    three_centres_collinear (hC.injective.ne hab) e1 e2 e3
  exact three_collinear_not_convexIndependent hC h12 h13 h23 hCol

/-- A realisation in convex position has pair multiplicity at most two. -/
theorem pairSparse_of_realises
    {p : Vertex → Plane} (hC : ConvexIndependent ℝ p)
    (Q : OctagonIncidence) (hR : Realises p Q) :
    Q.PairSparse := by
  classical
  intro a b hab
  have hsubset :
      (Finset.univ.filter fun v => a ∈ Q.targets v ∧ b ∈ Q.targets v) ⊆
        Finset.univ.filter fun v => dist (p v) (p a) = dist (p v) (p b) := by
    intro v hv
    rw [Finset.mem_filter] at hv ⊢
    obtain ⟨r, hr⟩ := hR v
    exact ⟨Finset.mem_univ _, (hr a hv.2.1).trans (hr b hv.2.2).symm⟩
  unfold OctagonIncidence.pairMultiplicity
  rw [Finset.sum_boole]
  norm_num
  exact (Finset.card_le_card hsubset).trans (equidistantCentres_card_le_two hC hab)

/-- Failure at every vertex canonically yields a four-target incidence system. -/
theorem incidence_of_all_hasFour
    {p : Vertex → Plane} (h : ∀ v, HasFourEquidistant p v) :
    ∃ Q : OctagonIncidence, Realises p Q := by
  classical
  let Q : OctagonIncidence :=
    { targets := fun v => (h v).choose
      card_targets := fun v => (h v).choose_spec.1
      centre_not_mem := fun v => (h v).choose_spec.2.1 }
  refine ⟨Q, ?_⟩
  intro v
  exact (h v).choose_spec.2.2

/-- Any failed convex octagon produces a balanced, pair-sparse incidence system. -/
theorem reduction_of_all_hasFour
    {p : Vertex → Plane} (hC : ConvexIndependent ℝ p)
    (h : ∀ v, HasFourEquidistant p v) :
    ∃ Q : OctagonIncidence, Realises p Q ∧ Q.PairSparse ∧ Q.Balanced := by
  obtain ⟨Q, hR⟩ := incidence_of_all_hasFour h
  have hS := pairSparse_of_realises hC Q hR
  exact ⟨Q, hR, hS, Q.balanced_of_pairSparse hS⟩

end Erdos97Octagon
