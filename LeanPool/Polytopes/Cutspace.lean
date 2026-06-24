/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/

import LeanPool.Polytopes.Polar

/-!
Cut spaces obtained by intersecting collections of halfspaces.
-/

open Module

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The cut space of a set of halfspaces: the intersection of all of them. -/
def cutSpace (H_ : Set (Halfspace E)) : Set E := ⋂₀ (SetLike.coe '' H_)

lemma Convex_cutSpace (H_ : Set (Halfspace E)) : Convex ℝ (cutSpace H_) := by
  apply convex_sInter
  rintro _ ⟨ Hi_, _, rfl ⟩
  exact Halfspace_convex Hi_

lemma Closed_cutSpace (H_ : Set (Halfspace E)) : IsClosed (cutSpace H_) := by
  apply isClosed_sInter
  rintro _ ⟨ Hi_, _, rfl ⟩
  exact Halfspace_closed Hi_

lemma mem_cutSpace (H_ : Set (Halfspace E)) (x : E) :
  x ∈ cutSpace H_ ↔ ∀ Hi, Hi ∈ H_ → Hi.f.1 x ≤ Hi.α := by
  constructor <;> intro h
  · -- 1.
    intro Hi HiH
    unfold cutSpace at h
    rw [Set.mem_sInter] at h
    specialize h Hi ⟨ Hi, HiH, rfl ⟩
    rwa [Halfspace_mem] at h
  · -- 2.
    unfold cutSpace
    rw [Set.mem_sInter]
    rintro _ ⟨ Hi_, hHi_, rfl ⟩
    specialize h Hi_ hHi_
    rwa [Halfspace_mem]

lemma empty_cutSpace (h : ∃ x : E, x ≠ 0) : ∃ (H_ : Set (Halfspace E)), cutSpace H_ = ∅ := by
  rcases h with ⟨ x, hx ⟩
  let xhat := (norm x)⁻¹ • x
  let fval : StrongDual ℝ E := InnerProductSpace.toDualMap ℝ _ xhat
  let f : {f : (StrongDual ℝ E) // norm f = 1} := ⟨ fval , (by
    change norm (innerSL ℝ ((norm x)⁻¹ • x)) = 1
    have := @norm_smul_inv_norm ℝ _ E _ _ x hx
    rw [RCLike.ofReal_real_eq_id, id_eq] at this
    rw [innerSL_apply_norm, this]
  ) ⟩
  refine ⟨ {Halfspace.mk f (-1), Halfspace.mk (-f) (-1)} , ?_ ⟩
  ext x
  rw [Set.mem_empty_iff_false, iff_false, mem_cutSpace]
  intro h
  have h1 := h (Halfspace.mk f (-1)) (by simp)
  have h2 := h (Halfspace.mk (-f) (-1)) (by simp)
  rw [unitSphereDual_neg, neg_apply, neg_le, neg_neg] at h2
  change f.1 x ≤ -1 at h1
  linarith

lemma hyperplane_cutSpace (f : {f : (StrongDual ℝ E) // norm f = 1}) (c : ℝ) :
  ∃ (H_ : Set (Halfspace E)), cutSpace H_ = {x | f.1 x = c} := by
  refine ⟨ {Halfspace.mk f c, Halfspace.mk (-f) (-c)}, ?_ ⟩
  ext x
  rw [mem_cutSpace, Set.mem_setOf]
  constructor
  · -- 1.
    intro h
    have h1 := h (Halfspace.mk f c) (by simp)
    have h2 := h (Halfspace.mk (-f) (-c)) (by simp)
    rw [unitSphereDual_neg, neg_apply, neg_le, neg_neg] at h2
    change f.1 x ≤ c at h1
    exact le_antisymm h1 h2
  · -- 2.
    intro h Hi hHi
    simp only [Set.mem_singleton_iff, Set.mem_insert_iff] at hHi
    rcases hHi with rfl | rfl
    · exact le_of_eq h
    · rw [unitSphereDual_neg, neg_apply, neg_le, neg_neg]
      exact le_of_eq h.symm

lemma inter_cutSpace (H_1 H_2 : Set (Halfspace E)) :
  cutSpace (H_1 ∪ H_2) = cutSpace H_1 ∩ cutSpace H_2 := by
  ext x
  rw [mem_cutSpace, Set.mem_inter_iff, mem_cutSpace, mem_cutSpace]
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


/-- The pair of halfspaces whose intersection is the hyperplane orthogonal to `x`. -/
def orthoHyperplane (x : {x : E // x ≠ 0}) : Set (Halfspace E) :=
  { Halfspace.mk (pointDualLin x) 0,
    Halfspace.mk (pointDualLin ⟨ -x.1, by rw [neg_ne_zero]; exact x.2 ⟩) 0 }

lemma orthoHyperplane.Finite (x : {x : E // x ≠ 0}) : (orthoHyperplane x).Finite := by
  unfold orthoHyperplane
  simp only [Set.finite_singleton, Set.Finite.insert]

lemma orthoHyperplane_mem (x : {x : E // x ≠ 0}) :
    ∀ (y : E), y ∈ cutSpace (orthoHyperplane x) ↔ inner ℝ x.1 y = (0:ℝ) := by
  intro y
  rw [mem_cutSpace]
  constructor
  · -- 1.
    intro h
    have h1 := h (Halfspace.mk (pointDualLin x) 0)
    simp only [pointDualLin, ne_eq, map_inv₀, RCLike.conj_to_real, orthoHyperplane,
      Set.mem_singleton_iff, Halfspace.mk.injEq, and_true, Set.mem_insert_iff, true_or,
      forall_true_left, InnerProductSpace.toDual_apply_apply, inner_smul_left] at h1
    have h2 := h (Halfspace.mk (pointDualLin ⟨ -x.1, by rw [neg_ne_zero]; exact x.2 ⟩) 0)
    simp only [pointDualLin, ne_eq, norm_neg, smul_neg, map_inv₀, RCLike.conj_to_real,
      orthoHyperplane, Set.mem_singleton_iff, Halfspace.mk.injEq, Subtype.mk.injEq, and_true,
      Set.mem_insert_iff, or_true, forall_true_left, InnerProductSpace.toDual_apply_apply,
      inner_neg_left, inner_smul_left] at h2
    rw [neg_le, neg_zero] at h2
    have := le_antisymm h1 h2
    rw [mul_eq_zero] at this
    rcases this with h3 | h4
    · rw [inv_eq_zero, norm_eq_zero] at h3
      exfalso
      exact x.2 h3
    · exact h4
  · -- 2.
    intro h H hH
    unfold orthoHyperplane at hH
    simp only [ne_eq, Set.mem_singleton_iff, Set.mem_insert_iff] at hH
    rcases hH with H | H <;>
    simp only [H, pointDualLin, norm_neg, smul_neg, map_inv₀, RCLike.conj_to_real,
      InnerProductSpace.toDual_apply_apply, inner_neg_left, inner_smul_left, neg_zero, h,
      mul_zero, le_refl]

lemma cutSpace_sUnion_orthoHyperplane (X : Set {x : E // x ≠ 0}) : ∀ (y : E),
    y ∈ cutSpace (⋃₀ (orthoHyperplane '' X)) ↔
    ∀ (i : ↑(orthoHyperplane '' X)), y ∈ cutSpace ↑i := by
  intro y
  unfold cutSpace
  rw [Set.sUnion_eq_iUnion, Set.image_iUnion, Set.sInter_iUnion, Set.mem_iInter]

lemma orthoHyperplanes_mem (X : Set {x : E // x ≠ 0}) :
    ∀ (y : E), y ∈ cutSpace (⋃₀ (orthoHyperplane '' X)) ↔ ∀ x ∈ X, inner ℝ x.1 y = (0:ℝ) := by
  intro y
  rw [cutSpace_sUnion_orthoHyperplane]
  constructor
  · -- 1.
    intro h x hx
    have hmem : orthoHyperplane x ∈ orthoHyperplane '' X := Set.mem_image_of_mem _ hx
    exact (orthoHyperplane_mem x y).mp (h ⟨orthoHyperplane x, hmem⟩)
  · -- 2.
    rintro h ⟨a, ha⟩
    rcases ha with ⟨x, hx, rfl⟩
    exact (orthoHyperplane_mem x y).mpr (h x hx)


/-- A finite set of halfspaces whose cut space is the subspace `p`, built from a basis of `pᗮ`. -/
def submoduleCut [FiniteDimensional ℝ E] (p : Subspace ℝ E) : Set (Halfspace E) :=
  ⋃₀ (orthoHyperplane '' (Subtype.val ⁻¹' (Set.range (Subtype.val ∘ Module.finBasis ℝ pᗮ))))

lemma Submodule_cut_finite [FiniteDimensional ℝ E] (p : Subspace ℝ E) :
    (submoduleCut p).Finite := by
  apply Set.Finite.sUnion ?_ (fun t ht => by
    rcases ht with ⟨ x, _, rfl ⟩
    exact orthoHyperplane.Finite _)
  apply Set.Finite.image
  apply Set.Finite.preimage (Set.injOn_of_injective Subtype.val_injective)
  apply Set.finite_range

lemma Submodule_cutspace [FiniteDimensional ℝ E] (p : Subspace ℝ E) :
    ∃ H_ : Set (Halfspace E), H_.Finite ∧ ↑p = cutSpace H_ := by
  use submoduleCut p
  use Submodule_cut_finite p
  ext x
  constructor
  · -- 1.
    rintro hx Hi_ ⟨ H, ⟨ _, ⟨ v, ⟨ i, hi ⟩, rfl ⟩ , hHHalfpair ⟩, rfl ⟩
    rw [Halfspace_mem]
    revert hHHalfpair H
    rw [← mem_cutSpace,  orthoHyperplane_mem, ← hi, Submodule.inner_left_of_mem_orthogonal hx]
    exact Submodule.coe_mem ((Module.finBasis ℝ { x // x ∈ pᗮ }) i)
  · -- 2.
    rintro hHi_
    rw [submoduleCut, orthoHyperplanes_mem] at hHi_
    rw [SetLike.mem_coe, ← Submodule.orthogonal_orthogonal p]
    intro y hy
    have : ∀ i, inner ℝ (Subtype.val (Module.finBasis ℝ { x // x ∈ pᗮ } i)) x = (0:ℝ) := by
      intro i
      let v : E := (Module.finBasis ℝ { x // x ∈ pᗮ }) i
      let v' : { x : E // x ≠ 0 } := ⟨ v, fun hv =>
        (Basis.ne_zero (Module.finBasis ℝ { x // x ∈ pᗮ }) i) (Submodule.coe_eq_zero.mp hv) ⟩
      exact hHi_ v' ⟨ i, rfl ⟩
    rw [← Submodule.mem_orthogonal_Basis] at this
    exact this _ hy
