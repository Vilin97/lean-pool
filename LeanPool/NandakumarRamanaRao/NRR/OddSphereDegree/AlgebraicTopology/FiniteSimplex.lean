/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudryashov, Yaël Dillies, Joël Riou
-/

import Mathlib.Analysis.Convex.Combination
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.Topology.Algebra.Monoid.FunOnFinite
import Mathlib.Tactic

/-! # Finite coordinate simplices

The subdivision construction uses a simplex as a subset of a finite coordinate
space. The equivalence below identifies these coordinates with Mathlib's
finitely supported simplex without changing their pointwise values.
-/

open Set Convexity

namespace SphereOddDegree

/-- Nonnegative finite coordinate functions whose coordinates sum to one. -/
def finiteSimplex (R X : Type*) [Semiring R] [PartialOrder R] [Fintype X] : Set (X → R) :=
  {f | (∀ x, 0 ≤ f x) ∧ ∑ x, f x = 1}

namespace FiniteSimplex

variable {S : Type*} [Semiring S] [PartialOrder S]
  {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

instance : FunLike (finiteSimplex S X) X S where
  coe s := s.val
  coe_injective := Subtype.val_injective

/-- Applying a coordinate subtype reads its underlying function. -/
@[simp] theorem mk_apply (f : X → S) (h : f ∈ finiteSimplex S X) (x : X) :
    (⟨f, h⟩ : finiteSimplex S X) x = f x := rfl

/-- Coordinate equality determines a point of the finite simplex. -/
@[ext] theorem ext {s t : finiteSimplex S X} (h : (s : X → S) = t) : s = t :=
  Subtype.ext h

/-- Conversion to finitely supported weights preserves every coordinate. -/
noncomputable def equivalence : finiteSimplex S X ≃ StdSimplex S X where
  toFun s :=
    { weights := Finsupp.equivFunOnFinite.symm s.val
      nonneg x := by simpa using s.property.1 x
      total := by simpa [Finsupp.sum_fintype] using s.property.2 }
  invFun s := ⟨s.weights, s.weights_nonneg, s.total_of_fintype⟩
  left_inv s := by apply Subtype.ext; funext x; simp
  right_inv s := by apply StdSimplex.ext; ext x; simp

/-- The finitely supported representation has the same coordinates. -/
@[simp] theorem equivalence_weights (s : finiteSimplex S X) (x : X) :
    (equivalence s).weights x = s x := by
  simp [equivalence]
  rfl

/-- Returning to finite coordinates reads the original finitely supported weights. -/
@[simp] theorem equivalence_symm_apply (s : StdSimplex S X) (x : X) :
    equivalence.symm s x = s.weights x := rfl

/-- Every coordinate of a finite simplex point is nonnegative. -/
@[simp] theorem zero_le (s : finiteSimplex S X) (x : X) : 0 ≤ s x := s.2.1 x

/-- The coordinates of a finite simplex point sum to one. -/
@[simp] theorem sum_eq_one (s : finiteSimplex S X) : ∑ x, s x = 1 := s.2.2

instance [Subsingleton X] : Subsingleton (finiteSimplex S X) :=
  equivalence.injective.subsingleton

variable [IsOrderedRing S]

/-- Each nonnegative coordinate is bounded by the total mass. -/
theorem le_one (s : finiteSimplex S X) (x : X) : s x ≤ 1 := by
  rw [← sum_eq_one s]
  exact Finset.single_le_sum (fun i _ => zero_le s i) (Finset.mem_univ x)

/-- Summing coordinates along fibers preserves nonnegativity and total mass. -/
theorem image_linearMap (f : X → Y) :
    Set.image (FunOnFinite.linearMap S S f) (finiteSimplex S X) ⊆ finiteSimplex S Y := by
  classical
  rintro _ ⟨s, ⟨hs₀, hs₁⟩, rfl⟩
  refine ⟨fun y => ?_, ?_⟩
  · rw [FunOnFinite.linearMap_apply_apply]
    exact Finset.sum_nonneg (fun x _ => hs₀ x)
  · simp only [FunOnFinite.linearMap_apply_apply, ← hs₁]
    exact Finset.sum_fiberwise Finset.univ f s

/-- Push a finite simplex point forward by summing weights over each fiber. -/
noncomputable def map (f : X → Y) (s : finiteSimplex S X) : finiteSimplex S Y :=
  ⟨FunOnFinite.linearMap S S f s, image_linearMap f ⟨s, s.property, rfl⟩⟩

/-- The underlying coordinate function is the finite fiber-sum linear map. -/
@[simp] theorem map_coe (f : X → Y) (s : finiteSimplex S X) :
    ⇑(map f s) = FunOnFinite.linearMap S S f s := rfl

/-- Pushing weights through two maps agrees with pushing them through their composition. -/
theorem map_comp_apply (f : X → Y) (g : Y → Z) (x : finiteSimplex S X) :
    map g (map f x) = map (g.comp f) x := by
  apply ext
  simp [FunOnFinite.linearMap_comp]

/-- Unit mass at one coordinate lies in the finite simplex. -/
theorem single_mem [DecidableEq X] (x : X) : Pi.single x 1 ∈ finiteSimplex S X :=
  ⟨le_update_iff.2 ⟨zero_le_one, fun _ _ => le_rfl⟩, by simp⟩

/-- The finite simplex vertex carrying unit mass at the chosen coordinate. -/
abbrev vertex [DecidableEq X] (x : X) : finiteSimplex S X :=
  ⟨Pi.single x 1, single_mem x⟩

/-- A vertex has its unit-coordinate function as underlying coordinates. -/
@[simp] theorem vertex_coe [DecidableEq X] (x : X) :
    ⇑(vertex (S := S) x) = Pi.single x 1 := rfl

/-- A vertex is sent to the vertex indexed by the image coordinate. -/
@[simp] theorem map_vertex [DecidableEq X] [DecidableEq Y] (f : X → Y) (x : X) :
    map (S := S) f (vertex x) = vertex (f x) := by
  apply ext
  change FunOnFinite.linearMap S S f (Pi.single x 1) = Pi.single (f x) 1
  ext y
  simp [FunOnFinite.linearMap_apply_apply, Pi.single_apply, eq_comm]

/-- Fiber sums give continuous maps between finite coordinate simplices. -/
theorem continuous_map [TopologicalSpace S] [IsTopologicalSemiring S] (f : X → Y) :
    Continuous (map (S := S) f) :=
  Continuous.subtype_mk ((FunOnFinite.continuous_linearMap S S f).comp continuous_induced_dom) _

end FiniteSimplex

namespace FiniteSimplex

variable {𝕜 X : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [Fintype X] [Nonempty X]

/-- The finite simplex point assigning the same mass to every coordinate. -/
def barycenter : finiteSimplex 𝕜 X :=
  ⟨fun _ => (Fintype.card X : 𝕜)⁻¹, by simp [finiteSimplex]⟩

/-- Every barycenter coordinate is the reciprocal of the number of vertices. -/
@[simp] theorem barycenter_apply (x : X) :
    (barycenter : finiteSimplex 𝕜 X).val x = (Fintype.card X : 𝕜)⁻¹ := rfl

end FiniteSimplex

/-- Unit-coordinate vectors belong to the finite coordinate simplex. -/
theorem single_mem_finiteSimplex (S : Type*) {X : Type*} [Fintype X] [DecidableEq X]
    [Semiring S] [PartialOrder S] [IsOrderedRing S] (x : X) :
    Pi.single x 1 ∈ finiteSimplex S X := FiniteSimplex.single_mem x

/-- Convex combinations preserve the nonnegative coordinates and their total mass. -/
theorem convex_finiteSimplex (S X : Type*) [Semiring S] [PartialOrder S]
    [IsOrderedRing S] [Fintype X] : Convex S (finiteSimplex S X) := by
  intro f hf g hg a b ha hb hab
  refine ⟨fun x => add_nonneg (mul_nonneg ha (hf.1 x)) (mul_nonneg hb (hg.1 x)), ?_⟩
  simp_rw [Pi.add_apply, Pi.smul_apply]
  rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, hf.2, hg.2,
    smul_eq_mul, smul_eq_mul, mul_one, mul_one]
  exact hab

/-- The finite coordinate simplex is exactly the convex hull of its unit-coordinate vertices. -/
theorem convexHull_range_single_eq_finiteSimplex (R X : Type*)
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype X] [DecidableEq X] :
    convexHull R (range fun i : X => Pi.single i 1) = finiteSimplex R X := by
  refine Subset.antisymm (convexHull_min ?_ (convex_finiteSimplex R X)) ?_
  · rintro _ ⟨i, rfl⟩
    exact single_mem_finiteSimplex R i
  · rintro w ⟨hw₀, hw₁⟩
    have hsum : w = ∑ i : X, w i • Pi.single i (1 : R) := by
      ext x
      simp [Pi.single_apply]
    rw [hsum, ← Finset.univ.centerMass_eq_of_sum_1 _ hw₁]
    exact Finset.univ.centerMass_mem_convexHull (fun i _ => hw₀ i) (hw₁.symm ▸ zero_lt_one)
      (fun i _ => mem_range_self i)

/-- Finite coordinate simplices are compact in an ordered topological semiring. -/
theorem isCompact_finiteSimplex (S X : Type*) [Fintype X] [TopologicalSpace S]
    [Semiring S] [PartialOrder S] [OrderClosedTopology S] [ContinuousAdd S]
    [CompactIccSpace S] [IsOrderedRing S] : IsCompact (finiteSimplex S X) := by
  have hclosed : IsClosed (finiteSimplex S X) := by
    have hset : finiteSimplex S X =
        (⋂ x, {f : X → S | 0 ≤ f x}) ∩ {f | ∑ x, f x = 1} := by
      ext f
      simp [finiteSimplex]
    rw [hset]
    exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_eq (by fun_prop) continuous_const)
  apply IsCompact.of_isClosed_subset isCompact_Icc hclosed
  intro s hs
  exact ⟨hs.1, fun x => FiniteSimplex.le_one ⟨s, hs⟩ x⟩

instance FiniteSimplex.compactSpace (S X : Type*) [Fintype X] [TopologicalSpace S]
    [Semiring S] [PartialOrder S] [OrderClosedTopology S] [ContinuousAdd S]
    [CompactIccSpace S] [IsOrderedRing S] : CompactSpace (finiteSimplex S X) :=
  isCompact_iff_compactSpace.mp (isCompact_finiteSimplex S X)

/-- A compact finite coordinate simplex is bounded in real coordinate space. -/
theorem bounded_finiteSimplex (X : Type*) [Fintype X] :
    Bornology.IsBounded (finiteSimplex ℝ X) :=
  (isCompact_finiteSimplex ℝ X).isBounded


/-- The one-dimensional finite coordinate simplex is the unit interval. -/
noncomputable def FiniteSimplex.homeomorphUnitInterval :
    finiteSimplex ℝ (Fin 2) ≃ₜ unitInterval where
  toFun s := ⟨s.val 1, s.2.1 1, FiniteSimplex.le_one s 1⟩
  invFun t := ⟨![1 - t, t], Fin.forall_fin_two.2
    ⟨sub_nonneg.mpr t.2.2, t.2.1⟩, by simp⟩
  left_inv s := by
    apply Subtype.ext
    funext i
    have hsum : s.val 0 + s.val 1 = 1 := by simpa using s.2.2
    fin_cases i <;> simp <;> linarith
  right_inv t := by apply Subtype.ext; rfl
  continuous_toFun := ((continuous_apply 1).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by fun_prop

/-- The last endpoint corresponds to unit mass at coordinate one. -/
@[simp] theorem FiniteSimplex.homeomorphUnitInterval_one :
    FiniteSimplex.homeomorphUnitInterval (FiniteSimplex.vertex 1) = 1 := rfl

/-- The first endpoint corresponds to unit mass at coordinate zero. -/
@[simp] theorem FiniteSimplex.homeomorphUnitInterval_zero :
    FiniteSimplex.homeomorphUnitInterval (FiniteSimplex.vertex 0) = 0 := rfl

end SphereOddDegree
