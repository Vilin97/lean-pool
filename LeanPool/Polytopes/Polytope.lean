/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/

import LeanPool.Polytopes.Cutspace

/-!
Definitions and basic properties of V-polytopes and H-polytopes.
-/

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
open Pointwise Module


/-- The V-polytope of a finite point set `S`: its convex hull.

The finiteness witness is recorded as it characterises the polytope and is used by the
surrounding API, even though the convex hull itself does not depend on it. -/
def Vpolytope {S : Set E} (hS : S.Finite) : Set E :=
  (fun _ : S.Finite => convexHull ℝ S) hS

omit [CompleteSpace E] in
@[simp]
lemma Vpolytope_def {S : Set E} (hS : S.Finite) : Vpolytope hS = convexHull ℝ S := rfl

omit [CompleteSpace E] in
lemma Convex_Vpolytope {S : Set E} (hS : S.Finite) :
  Convex ℝ (Vpolytope hS) := convex_convexHull ℝ S

omit [CompleteSpace E] in
lemma Closed_Vpolytope {S : Set E} (hS : S.Finite) :
  IsClosed (Vpolytope hS) := hS.isClosed_convexHull ℝ

omit [CompleteSpace E] in
lemma Compact_Vpolytope {S : Set E} (hS : S.Finite) :
  IsCompact (Vpolytope hS) := hS.isCompact_convexHull ℝ


/-- The H-polytope of a finite set of halfspaces `H_`: the intersection of those halfspaces.

The finiteness witness is recorded as it characterises the polytope and is used by the
surrounding API, even though the intersection itself does not depend on it. -/
def Hpolytope {H_ : Set (Halfspace E)} (hH_ : H_.Finite) : Set E :=
  (fun _ : H_.Finite => ⋂₀ (SetLike.coe '' H_)) hH_

@[simp]
lemma Hpolytope_def {H_ : Set (Halfspace E)} (hH_ : H_.Finite) :
    Hpolytope hH_ = ⋂₀ (SetLike.coe '' H_) := rfl

lemma Convex_Hpolytope {H_ : Set (Halfspace E)} (hH_ : H_.Finite) :
  Convex ℝ (Hpolytope hH_) := by
  apply convex_sInter
  rintro _ ⟨ Hi_, _, rfl ⟩
  exact Halfspace_convex Hi_

lemma Closed_Hpolytope {H : Set (Halfspace E)} (hH_ : H.Finite) :
  IsClosed (Hpolytope hH_) := by
  apply isClosed_sInter
  rintro _ ⟨ Hi_, _, rfl ⟩
  exact Halfspace_closed Hi_

lemma Hpolytope_same {H_ : Set (Halfspace E)} (hH_1 hH_2 : H_.Finite) :
  Hpolytope hH_1 = Hpolytope hH_2 := by
  unfold Hpolytope
  rfl

lemma mem_Hpolytope {H_ : Set (Halfspace E)} (hH_ : H_.Finite) (x : E) :
  x ∈ Hpolytope hH_ ↔ ∀ Hi, Hi ∈ H_ → Hi.f.1 x ≤ Hi.α := by
  constructor <;> intro h
  · -- 1.
    intro Hi HiH
    unfold Hpolytope at h
    rw [Set.mem_sInter] at h
    specialize h Hi ⟨ Hi, HiH, rfl ⟩
    rw [Halfspace_mem] at h
    exact h
  · -- 2.
    unfold Hpolytope
    rw [Set.mem_sInter]
    rintro _ ⟨ Hi_, hHi_, rfl ⟩
    specialize h Hi_ hHi_
    rw [Halfspace_mem]
    exact h

lemma empty_Hpolytope [Nontrivial E] :
  ∃ (H_ : Set (Halfspace E)) (hH_ : H_.Finite), Hpolytope hH_ = ∅ := by
  have h := exists_ne (0:E)
  rcases h with ⟨ x, hx ⟩
  let xhat := (norm x)⁻¹ • x
  let fval : StrongDual ℝ E := InnerProductSpace.toDualMap ℝ _ xhat
  let f : {f : (StrongDual ℝ E) // norm f = 1} := ⟨ fval , (by
    change norm (innerSL ℝ ((norm x)⁻¹ • x)) = 1
    have := @norm_smul_inv_norm ℝ _ E _ _ x hx
    rw [RCLike.ofReal_real_eq_id, id_eq] at this
    rw [innerSL_apply_norm, this]
  ) ⟩
  refine ⟨ {Halfspace.mk f (-1), Halfspace.mk (-f) (-1)} ,
    (by simp only [Set.finite_singleton, Set.Finite.insert]) , ?_ ⟩
  ext x
  rw [Set.mem_empty_iff_false, iff_false, mem_Hpolytope]
  intro h
  have h1 := h (Halfspace.mk f (-1)) (by simp)
  have h2 := h (Halfspace.mk (-f) (-1)) (by simp)
  rw [unitSphereDual_neg, ContinuousLinearMap.neg_apply, neg_le, neg_neg] at h2
  change f.1 x ≤ -1 at h1
  linarith

lemma origin_Hpolytope [FiniteDimensional ℝ E] :
    ∃ (H_ : Set (Halfspace E)) (hH_ : H_.Finite), Hpolytope hH_ = ({0} : Set E) := by
  refine ⟨ ⋃₀ (orthoHyperplane '' (Subtype.val ⁻¹' Set.range (Module.finBasis ℝ E))), ?_, ?_ ⟩
  · -- 1.
    apply Set.Finite.sUnion ?_ (fun t ht => by
      rcases ht with ⟨ x, _, rfl ⟩
      exact orthoHyperplane.Finite _)
    apply Set.Finite.image
    apply Set.Finite.preimage (Set.injOn_of_injective Subtype.val_injective)
    exact Set.finite_range _
  · -- 2.
    ext x
    rw [Set.mem_singleton_iff]
    change x ∈ cutSpace
      (⋃₀ (orthoHyperplane '' (Subtype.val ⁻¹' Set.range ↑(Module.finBasis ℝ E)))) ↔ x = 0
    rw [orthoHyperplanes_mem]
    constructor
    · -- 1.
      intro h
      apply InnerProductSpace.ext_inner_left_basis (Module.finBasis ℝ E)
      intro i
      rw [inner_zero_right]
      simp only [Set.mem_preimage, Set.mem_range, forall_exists_index, Subtype.forall] at h
      exact h (Module.finBasis ℝ E i) (Basis.ne_zero (Module.finBasis ℝ E) i) i rfl
    · -- 2.
      rintro rfl x _
      rw [inner_zero_right]

lemma hyperplane_Hpolytope : ∀ (f : {f : (StrongDual ℝ E) // norm f = 1}) (c : ℝ),
  ∃ (H_ : Set (Halfspace E)) (hH_ : H_.Finite), Hpolytope hH_ = {x | f.1 x = c} := by
  intro f c
  refine ⟨ {Halfspace.mk f c, Halfspace.mk (-f) (-c)},
    (by simp only [Set.finite_singleton, Set.Finite.insert]) , ?_ ⟩
  ext x
  rw [mem_Hpolytope, Set.mem_setOf]
  constructor
  · -- 1.
    intro h
    have h1 := h (Halfspace.mk f c) (by simp)
    have h2 := h (Halfspace.mk (-f) (-c)) (by simp)
    rw [unitSphereDual_neg, ContinuousLinearMap.neg_apply, neg_le, neg_neg] at h2
    change f.1 x ≤ c at h1
    exact le_antisymm h1 h2
  · -- 2.
    intro h Hi hHi
    simp only [Set.mem_singleton_iff, Set.mem_insert_iff] at hHi
    rcases hHi with rfl | rfl
    · exact le_of_eq h
    · rw [unitSphereDual_neg, ContinuousLinearMap.neg_apply, neg_le, neg_neg]
      exact le_of_eq h.symm

lemma inter_Hpolytope (H_1 H_2 : Set (Halfspace E)) (hH_1 : H_1.Finite) (hH_2 : H_2.Finite) :
  Hpolytope (Set.Finite.union hH_1 hH_2) = Hpolytope hH_1 ∩ Hpolytope hH_2 := by
  ext x
  rw [mem_Hpolytope, Set.mem_inter_iff, mem_Hpolytope, mem_Hpolytope]
  constructor
  · -- 1
    intro h
    constructor <;> intro Hi_ hH_ <;>
      exact h Hi_ (by simp only [Set.mem_union, hH_, true_or, or_true])
  · -- 2
    intro h Hi hHi
    rw [Set.mem_union] at hHi
    rcases hHi with hHi | hHi
    · -- 2.1
      exact h.1 Hi hHi
    · -- 2.2
      exact h.2 Hi hHi

omit [CompleteSpace E] in
lemma Vpolytope_translation {S : Set E} (hS : S.Finite) (x : E) :
  Vpolytope (hS.translation x) = (Vpolytope hS) + {x} := by
  rw [Vpolytope, convexHull_add, convexHull_singleton]
  rfl

lemma Hpolytope_translation {H_ : Set (Halfspace E)} (hH_ : H_.Finite) (x : E) :
  Hpolytope (Set.Finite.image (halfspaceTranslation x) hH_) = (Hpolytope hH_) + {x}:= by
  rw [Hpolytope, Hpolytope, Set.sInter_image, Set.sInter_image]
  ext y
  rw [Set.mem_iInter, Set.add_singleton]
  simp only [Set.mem_iInter, SetLike.mem_coe, Set.image_add_right, Set.mem_preimage]
  constructor
  · -- 1.
    intro h Hi_ hHi_
    specialize h (halfspaceTranslation x Hi_) (Set.mem_image_of_mem _ hHi_)
    rw [← SetLike.mem_coe, mem_halfspaceTranslation, sub_eq_add_neg] at h
    exact h
  · -- 2.
    intro h Hi_ hHi_
    rw [Set.mem_image] at hHi_
    rcases hHi_ with ⟨ Hi_', hHi_', rfl ⟩
    rw [← SetLike.mem_coe, mem_halfspaceTranslation, sub_eq_add_neg]
    exact h Hi_' hHi_'
