/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
import LeanPool.Quasicategory.TopCatModelCategory.SSet.Horn

namespace SSet

open CategoryTheory SSet Subcomplex

def image_monotone {X Y : SSet} (f : X ⟶ Y) :
    Monotone (fun (A : Subcomplex X) ↦ A.image f) := by
  refine Monotone.apply₂ (Monotone.of_map_sup ?_) f
  intro A B
  ext
  aesop

def preimage_monotone {X Y : SSet} (f : X ⟶ Y) :
    Monotone (fun (B : Subcomplex Y) ↦ B.preimage f) := by
  refine Monotone.apply₂ (Monotone.of_map_sup ?_) f
  intro A B
  ext
  aesop

/-- if X ≅ Y, then we have an order isomorphism of their subcomplexes -/
@[simps!]
def subcomplex_orderIso {X Y : SSet} (f : X ⟶ Y) [IsIso f] : X.Subcomplex ≃o Y.Subcomplex where
  toFun A := A.image f
  invFun B := B.preimage f
  left_inv A := image_preimage_of_isIso f A
  right_inv B := preimage_image_of_isIso f B
  map_rel_iff' := ⟨fun h ↦ by simpa using preimage_monotone f h, fun h ↦ image_monotone f h⟩

@[simps!]
def range_orderIso {X Y : SSet} (f : X ⟶ Y) [hf : Mono f] :
    X.Subcomplex ≃o (range f).toSSet.Subcomplex :=
  subcomplex_orderIso (toRangeSubcomplex f)

@[simp]
lemma subcomplex_orderIso.symm_apply_eq' {X Y : SSet} (f : X ⟶ Y) [hf : IsIso f] (A : Subcomplex X) :
    (subcomplex_orderIso f).symm (A.image f) = A := (OrderIso.symm_apply_eq _).2 rfl

/-- if f : X ⟶ Y, then we have an order hom from subcomplexes of the range into
 subcomplexes of Y -/
 @[simps!]
def subcomplex_orderHom {X Y : SSet} (f : X ⟶ Y) :
    (Subcomplex.range f).toSSet.Subcomplex →o (Y.Subcomplex) where
  toFun A := A.image (range f).ι
  monotone' := image_monotone _

@[simp]
lemma image_inter_range_ι_eq {X : SSet} (R : X.Subcomplex) (A : R.toSSet.Subcomplex) :
    A.image R.ι ⊓ range R.ι = A.image R.ι := by
  apply le_antisymm
  simp [Subpresheaf.range_ι, inf_le_left]
  apply le_inf (le_rfl) (image_le_range A _)

/-- if f : X ⟶ Y is a mono, then we have an order embedding from subcomplexes of the range
into subcomplexes of Y -/
@[simps!]
def subcomplex_orderEmbedding {X Y : SSet} (f : X ⟶ Y) [Mono f] :
    (range f).toSSet.Subcomplex ↪o (Y.Subcomplex) where
  toFun A := A.image (range f).ι
  inj' := by
    intro A A' h
    dsimp at h
    apply_fun (fun A ↦ Subcomplex.preimage A (range f).ι) at h
    rwa [(preimage_eq_iff _ _ _).2 (image_inter_range_ι_eq (range f) A),
      (preimage_eq_iff _ _ _).2 (image_inter_range_ι_eq (range f) A')] at h
  map_rel_iff' := by
    intro A A'
    dsimp
    constructor
    · intro h
      have := preimage_monotone (range f).ι h
      dsimp at this
      rwa [(preimage_eq_iff _ _ _).2 (image_inter_range_ι_eq (range f) A),
        (preimage_eq_iff _ _ _).2 (image_inter_range_ι_eq (range f) A')] at this
    · apply image_monotone

/-- if R ≤ X, then we have an order isomorphism between subcomplexes of R and subcomplexes of X
contained in R -/
@[simps!]
def subset_orderIso {X : SSet} (R : X.Subcomplex) :
    (R.toSSet.Subcomplex) ≃o {p : X.Subcomplex // p ≤ R} where
  toFun A := ⟨A.image R.ι, by simpa only [Subpresheaf.range_ι] using image_le_range A R.ι⟩
  invFun := fun ⟨A, hA⟩ ↦ range (homOfLE hA)
  left_inv A := by aesop
  right_inv := fun ⟨B, hB⟩ ↦ by
    simp [Subcomplex.homOfLE, Subpresheaf.homOfLe]
    ext
    aesop
  map_rel_iff' := by
    intro A A'
    simp
    constructor
    · intro h
      have := preimage_monotone R.ι h
      dsimp at this
      rwa [(preimage_eq_iff _ _ _).2 (image_inter_range_ι_eq R A), (preimage_eq_iff _ _ _).2 (image_inter_range_ι_eq R A')] at this
    · intro h
      exact image_monotone _ h

/-
lemma subcomplex_le_boundary_image_iff' {n} {X : SSet} (f : Δ[n] ⟶ X) [Mono f]
      (A : (range f).toSSet.Subcomplex) :
    A ≤ ((boundary n).image (toRangeSubcomplex f)) ↔ A ≠ ⊤ := by
  constructor
  · intro h h'
    rw [← (range_orderIso f).symm.map_rel_iff'] at h
    simp [range_orderIso, subcomplex_orderIso.symm_apply_eq'] at h
    rw [subcomplex_le_boundary_iff, h'] at h
    exact h rfl
  · intro h
    have : A.preimage (toRangeSubcomplex f) ≠ ⊤ := by
      intro h'
      apply h
      rw [preimage_eq_top_iff] at h'
      simp_all only [ne_eq, Subpresheaf.range_toRange, top_le_iff]
    rw [← subcomplex_le_boundary_iff] at this
    apply_fun (fun A ↦ Subcomplex.image A (toRangeSubcomplex f)) at this
    dsimp at this
    rw [preimage_image_of_isIso] at this
    exact this
    refine Monotone.apply₂ ?_ (toRangeSubcomplex f)
    refine Monotone.of_le_map_sup ?_
    intro j k l p i o
    aesop
-/

lemma range_orderIso_symm_subset_orderIso_symm_eq {X Y : SSet} (f : X ⟶ Y) (A : Subcomplex X) :
    range (Subcomplex.homOfLE (image_le_range A f)) = A.image (toRangeSubcomplex f) := by
  aesop

lemma range_orderIso_symm_subset_orderIso_symm_apply {X Y : SSet} (f : X ⟶ Y) [Mono f] (A : Subcomplex X) :
    (range_orderIso f).symm ((subset_orderIso (range f)).symm ⟨A.image f, image_le_range A f⟩) = A := by
  dsimp [range_orderIso, subcomplex_orderIso, subset_orderIso, OrderIso.symm]
  rw [range_orderIso_symm_subset_orderIso_symm_eq]
  exact image_preimage_of_isIso (toRangeSubcomplex f) A

open Simplicial stdSimplex

-- bad proof
lemma subcomplex_le_boundary_image_iff {n} {X : SSet} (f : Δ[n] ⟶ X) [Mono f]
    (A : X.Subcomplex) (hA : A ≤ range f) :
      A ≤ (boundary n).image f ↔ A ≠ (range f) := by
  let iso := OrderIso.trans (subset_orderIso (range f)).symm (range_orderIso f).symm
  have : iso ⟨∂Δ[n].image f, image_le_range _ _⟩ = ∂Δ[n] := range_orderIso_symm_subset_orderIso_symm_apply _ _
  constructor
  · intro h
    replace h : (⟨A, hA⟩ : {p : X.Subcomplex // p ≤ range f}) ≤
      ⟨∂Δ[n].image f, image_le_range _ _⟩ := h
    rw [← iso.map_rel_iff', RelIso.coe_fn_toEquiv, this, subcomplex_le_boundary_iff] at h
    intro h'
    subst h'
    apply h
    simp [iso, subset_orderIso, OrderIso.symm, range_eq_top_iff]
    infer_instance
  · intro h
    change (⟨A, hA⟩ : {p : X.Subcomplex // p ≤ range f}) ≤
      ⟨∂Δ[n].image f, image_le_range _ _⟩
    rw [← iso.map_rel_iff']
    dsimp
    rw [this, subcomplex_le_boundary_iff]
    intro h'
    apply h
    apply_fun (fun A ↦ A.image f) at h'
    rw [image_top] at h'
    rw [← h']
    simp [iso, OrderIso.symm, subset_orderIso, range_orderIso, subcomplex_orderIso]
    have := toRangeSubcomplex_ι f
    simp_rw [← this]
    rw [image_comp, preimage_image_of_isIso]
    simp [Subcomplex.homOfLE, Subpresheaf.homOfLe]
    ext k x
    simp
    intro a
    apply hA
    exact a

-- need to add extra lemmas to make this simple
lemma subcomplex_le_horn_image_iff {n} {X : SSet} (f : Δ[n + 1] ⟶ X) [Mono f]
    (A : X.Subcomplex) (hA : A ≤ range f) (i : Fin (n + 2)) :
      A ≤ Λ[n + 1, i].image f ↔ ¬ (face {i}ᶜ).image f ≤ A := by
  let iso := OrderIso.trans (subset_orderIso (range f)).symm (range_orderIso f).symm
  have : iso ⟨Λ[n + 1, i].image f, image_le_range _ _⟩ = Λ[n + 1, i] := range_orderIso_symm_subset_orderIso_symm_apply _ _
  constructor
  · intro h
    replace h : (⟨A, hA⟩ : {p : X.Subcomplex // p ≤ range f}) ≤
      ⟨Λ[n + 1, i].image f, image_le_range _ _⟩ := h
    rw [← iso.map_rel_iff', RelIso.coe_fn_toEquiv, this, stdSimplex.subcomplex_le_horn_iff] at h
    intro h'
    apply h
    have := preimage_monotone f h'
    dsimp at this
    have g := (preimage_eq_iff f (face {i}ᶜ) ((face {i}ᶜ).image f)).2 (by simp only [image_le_range, inf_of_le_left])
    rw [g] at this
    convert this
    ext
    simp [iso, OrderIso.symm, subset_orderIso, range_orderIso, subcomplex_orderIso,
      Subcomplex.homOfLE, Subpresheaf.homOfLe, toRangeSubcomplex, Subpresheaf.toRange,
      Subpresheaf.lift]
  · intro h
    change (⟨A, hA⟩ : {p : X.Subcomplex // p ≤ range f}) ≤
      ⟨Λ[n + 1, i].image f, image_le_range _ _⟩
    rw [← iso.map_rel_iff']
    dsimp
    rw [this, subcomplex_le_horn_iff]
    intro h'
    apply h
    convert image_monotone f h'
    simp [iso, OrderIso.symm, subset_orderIso, range_orderIso, subcomplex_orderIso]
    have := toRangeSubcomplex_ι f
    simp_rw [← this]
    rw [image_comp, preimage_image_of_isIso]
    simp [Subcomplex.homOfLE, Subpresheaf.homOfLe]
    ext k x
    simp
    intro a
    apply hA
    exact a
