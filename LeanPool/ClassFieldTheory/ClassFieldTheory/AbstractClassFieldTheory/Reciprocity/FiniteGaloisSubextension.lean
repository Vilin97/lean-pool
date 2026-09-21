/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient

/-! # Finite Galois Subextension -/
namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# Finite Galois extensions above an abstract field

The norm topology is indexed by the actual finite Galois extensions
of a fixed abstract field.  This file packages those extensions and their
composita contravariantly as intersections of closed subgroups.
-/

noncomputable section

universe u

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- A finite Galois extension `L / K`, represented by `G_L ≤ G_K`. -/
structure FiniteGaloisSubextension (K : ClosedSubgroup G) where
  /-- The closed subgroup representing the top field. -/
  field : ClosedSubgroup G
  /-- The top-field subgroup is contained in the base-field subgroup. -/
  below : field.toSubgroup ≤ K.toSubgroup
  /-- The top-field subgroup is normal inside the base-field subgroup. -/
  normal : (extensionSubgroup K field below).Normal
  /-- The relative Galois quotient is finite. -/
  finite : Finite (K.toSubgroup ⧸ extensionSubgroup K field below)

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-- Forget only finiteness from a finite Galois subextension. -/
def toGaloisSubextension (L : FiniteGaloisSubextension K) :
    DegreeData.GaloisSubextension K where
  field := L.field
  below := L.below
  normal := L.normal

/-- Forget normality, retaining the underlying finite abstract extension.
This is the canonical bridge from a finite Galois subextension to the degree
and ramification API. -/
def toFiniteAbstractExtension (L : FiniteGaloisSubextension K) :
    DegreeData.FiniteAbstractExtension G where
  field := L.field
  base := K
  below := L.below
  finiteQuotient := L.finite

/-- The actual finite quotient `G(L/K)`, kept behind a named object
boundary. -/
def extensionQuotient (L : FiniteGaloisSubextension K) : Type u :=
  K.toSubgroup ⧸ extensionSubgroup K L.field L.below

/-- Structural unramifiedness of the underlying finite extension. -/
def IsUnramified (L : FiniteGaloisSubextension K) (D : DegreeData G) : Prop :=
  L.toFiniteAbstractExtension.IsUnramified D

/-- Structural total ramification of the underlying finite extension. -/
def IsTotallyRamified (L : FiniteGaloisSubextension K)
    (D : DegreeData G) : Prop :=
  L.toFiniteAbstractExtension.IsTotallyRamified D

/-- A finite Galois subextension is represented by a normal subgroup. -/
instance extensionSubgroup_normalInstance (L : FiniteGaloisSubextension K) :
    (extensionSubgroup K L.field L.below).Normal :=
  L.normal

/-- The group structure transported across the named finite quotient
boundary. -/
instance extensionQuotient_groupInstance (L : FiniteGaloisSubextension K) :
    Group L.extensionQuotient := by
  change Group
    (K.toSubgroup ⧸ extensionSubgroup K L.field L.below)
  infer_instance

/-- The quotient represented by a finite Galois subextension is finite. -/
instance extensionQuotient_finiteInstance (L : FiniteGaloisSubextension K) :
    Finite L.extensionQuotient :=
  L.finite

/-- Comparison with the quotient presentation used by the underlying group
library. -/
def extensionQuotientMulEquiv (L : FiniteGaloisSubextension K) :
    L.extensionQuotient ≃*
      (K.toSubgroup ⧸ extensionSubgroup K L.field L.below) :=
  MulEquiv.refl _

/-- The canonical quotient projection for a finite Galois subextension. -/
def extensionQuotientMk (L : FiniteGaloisSubextension K) :
    K.toSubgroup →* L.extensionQuotient :=
  QuotientGroup.mk' (extensionSubgroup K L.field L.below)

/-- The named finite Galois quotient projection agrees with `QuotientGroup.mk`. -/
@[simp]
theorem extensionQuotientMk_apply (L : FiniteGaloisSubextension K)
    (k : K.toSubgroup) :
    L.extensionQuotientMulEquiv (L.extensionQuotientMk k) =
      (QuotientGroup.mk k :
        K.toSubgroup ⧸ extensionSubgroup K L.field L.below) :=
  rfl

/-- A quotient representative is trivial exactly when it lies in the extension subgroup. -/
@[simp]
theorem extensionQuotientMk_eq_one_iff (L : FiniteGaloisSubextension K)
    (k : K.toSubgroup) :
    L.extensionQuotientMk k = 1 ↔
      k ∈ extensionSubgroup K L.field L.below := by
  constructor
  · intro h
    apply (QuotientGroup.eq_one_iff k).1
    calc
      (QuotientGroup.mk k :
          K.toSubgroup ⧸ extensionSubgroup K L.field L.below) =
          L.extensionQuotientMulEquiv (L.extensionQuotientMk k) :=
        (L.extensionQuotientMk_apply k).symm
      _ = L.extensionQuotientMulEquiv 1 := congrArg L.extensionQuotientMulEquiv h
      _ = 1 := L.extensionQuotientMulEquiv.map_one
  · intro hk
    apply L.extensionQuotientMulEquiv.injective
    rw [L.extensionQuotientMk_apply, L.extensionQuotientMulEquiv.map_one]
    exact (QuotientGroup.eq_one_iff k).2 hk

/-- The canonical projection onto the finite Galois quotient is surjective. -/
theorem extensionQuotientMk_surjective (L : FiniteGaloisSubextension K) :
    Function.Surjective L.extensionQuotientMk := by
  intro q
  obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective
    (extensionSubgroup K L.field L.below) (L.extensionQuotientMulEquiv q)
  refine ⟨k, L.extensionQuotientMulEquiv.injective ?_⟩
  rw [L.extensionQuotientMk_apply]
  exact hk

/-- The finite and non-finite Galois bundles have the same quotient; this
named equivalence is the only public comparison needed by clients. -/
def toGaloisExtensionQuotientMulEquiv (L : FiniteGaloisSubextension K) :
    L.extensionQuotient ≃* L.toGaloisSubextension.extensionQuotient :=
  L.extensionQuotientMulEquiv.trans
    L.toGaloisSubextension.extensionQuotientMulEquiv.symm

/-- Eliminate a finite Galois quotient without exposing a chosen
representative. -/
protected theorem extensionQuotient_inductionOn
    (L : FiniteGaloisSubextension K) {motive : L.extensionQuotient → Prop}
    (q : L.extensionQuotient)
    (mk : ∀ k : K.toSubgroup, motive (L.extensionQuotientMk k)) :
    motive q := by
  exact @Quotient.inductionOn' K.toSubgroup
    (QuotientGroup.leftRel (extensionSubgroup K L.field L.below))
    motive q mk

/-- Bundling a finite Galois extension preserves its unramified predicate. -/
@[simp]
theorem toGaloisSubextension_isUnramified_iff
    (L : FiniteGaloisSubextension K) (D : DegreeData G) :
    L.toGaloisSubextension.IsUnramified D ↔ L.IsUnramified D :=
  Iff.rfl

/-- Bundling a finite Galois extension preserves its total-ramification predicate. -/
@[simp]
theorem toGaloisSubextension_isTotallyRamified_iff
    (L : FiniteGaloisSubextension K) (D : DegreeData G) :
    L.toGaloisSubextension.IsTotallyRamified D ↔ L.IsTotallyRamified D :=
  Iff.rfl

/-- Transport an unramifiedness proof through the finite-to-Galois
forgetful map. -/
theorem isUnramified_toGaloisSubextension
    (L : FiniteGaloisSubextension K) (D : DegreeData G)
    (hL : L.IsUnramified D) :
    L.toGaloisSubextension.IsUnramified D :=
  (L.toGaloisSubextension_isUnramified_iff D).2 hL

/-- Transport a total-ramification proof through the finite-to-Galois
forgetful map. -/
theorem isTotallyRamified_toGaloisSubextension
    (L : FiniteGaloisSubextension K) (D : DegreeData G)
    (hL : L.IsTotallyRamified D) :
    L.toGaloisSubextension.IsTotallyRamified D :=
  (L.toGaloisSubextension_isTotallyRamified_iff D).2 hL

/-- Unramifiedness is the canonical inertia-containment condition. -/
theorem isUnramified_iff_inertia_le (L : FiniteGaloisSubextension K)
    (D : DegreeData G) :
    L.IsUnramified D ↔
      K.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ L.field.toSubgroup :=
  L.toFiniteAbstractExtension.isUnramified_iff_inertia_le D

/-- Total ramification is the canonical equality of degree images. -/
theorem isTotallyRamified_iff_image_le (L : FiniteGaloisSubextension K)
    (D : DegreeData G) :
    L.IsTotallyRamified D ↔
      K.toSubgroup.map D.degree.toMonoidHom ≤
        L.field.toSubgroup.map D.degree.toMonoidHom :=
  L.toFiniteAbstractExtension.isTotallyRamified_iff_image_le D

/-- Retain the finite-over-base endpoint bundles of a finite Galois
subextension of an abstract field which is finite over the distinguished
base. -/
noncomputable def toFiniteAbstractFieldExtension
    {K : FiniteAbstractField G} (L : FiniteGaloisSubextension K.field) :
    FiniteAbstractFieldExtension G := by
  letI : Finite
      (K.field.toSubgroup ⧸
        extensionSubgroup K.field L.field L.below) :=
    L.finite
  exact FiniteAbstractFieldExtension.ofInclusion L.field K L.below

/-- Finiteness is transitive in a tower of abstract fields. -/
theorem finite_extension_trans
    {P L K : ClosedSubgroup G}
    (hPL : P.toSubgroup ≤ L.toSubgroup)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hPLfinite : Finite
      (L.toSubgroup ⧸ extensionSubgroup L P hPL)]
    [hLKfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    Finite (K.toSubgroup ⧸ extensionSubgroup K P (hPL.trans hLK)) := by
  have hPL0 : P.toSubgroup.relIndex L.toSubgroup ≠ 0 := by
    rw [Subgroup.relIndex]
    exact @Subgroup.index_ne_zero_of_finite L.toSubgroup _
      (extensionSubgroup L P hPL) hPLfinite
  have hLK0 : L.toSubgroup.relIndex K.toSubgroup ≠ 0 := by
    rw [Subgroup.relIndex]
    exact @Subgroup.index_ne_zero_of_finite K.toSubgroup _
      (extensionSubgroup K L hLK) hLKfinite
  apply Nat.finite_of_card_ne_zero
  change (extensionSubgroup K P (hPL.trans hLK)).index ≠ 0
  simpa [Subgroup.relIndex] using
    Subgroup.relIndex_ne_zero_trans hPL0 hLK0

/-- A finite extension remains finite over every intermediate field. -/
theorem finite_extension_over_intermediate
    {P M K : ClosedSubgroup G}
    (hPK : P.toSubgroup ≤ K.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    (hPM : P.toSubgroup ≤ M.toSubgroup)
    [hPKfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K P hPK)] :
    Finite (M.toSubgroup ⧸ extensionSubgroup M P hPM) := by
  have hPK0 : P.toSubgroup.relIndex K.toSubgroup ≠ 0 := by
    rw [Subgroup.relIndex]
    exact @Subgroup.index_ne_zero_of_finite K.toSubgroup _
      (extensionSubgroup K P hPK) hPKfinite
  have hPM0 : P.toSubgroup.relIndex M.toSubgroup ≠ 0 := by
    intro hzero
    have hmul := Subgroup.relIndex_mul_relIndex
      P.toSubgroup M.toSubgroup K.toSubgroup hPM hMK
    rw [hzero, zero_mul] at hmul
    exact hPK0 hmul.symm
  apply Nat.finite_of_card_ne_zero
  change (extensionSubgroup M P hPM).index ≠ 0
  simpa [Subgroup.relIndex] using hPM0

/-- Every intermediate field of a finite extension is finite over the
base.  No normality hypothesis is needed: this is the finite-index
statement for an arbitrary subgroup between the two endpoint subgroups. -/
theorem finite_intermediate_extension
    {P M K : ClosedSubgroup G}
    (hPK : P.toSubgroup ≤ K.toSubgroup)
    (hPM : P.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hPKfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K P hPK)] :
    Finite (K.toSubgroup ⧸ extensionSubgroup K M hMK) := by
  have hPK0 : P.toSubgroup.relIndex K.toSubgroup ≠ 0 := by
    rw [Subgroup.relIndex]
    exact @Subgroup.index_ne_zero_of_finite K.toSubgroup _
      (extensionSubgroup K P hPK) hPKfinite
  have hMK0 : M.toSubgroup.relIndex K.toSubgroup ≠ 0 := by
    intro hzero
    have hmul := Subgroup.relIndex_mul_relIndex
      P.toSubgroup M.toSubgroup K.toSubgroup hPM hMK
    rw [hzero, mul_zero] at hmul
    exact hPK0 hmul.symm
  apply Nat.finite_of_card_ne_zero
  change (extensionSubgroup K M hMK).index ≠ 0
  simpa [Subgroup.relIndex] using hMK0

/-- Base change of a finite Galois extension `M / K` to an arbitrary
intermediate field `L / K`.  Contravariantly, the compositum `ML` is the
intersection `G_M ∩ G_L`; normality and finite index are pulled back from
`G_M ◁ G_K`. -/
def baseChange (M : FiniteGaloisSubextension K) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) : FiniteGaloisSubextension L where
  field := L ⊓ M.field
  below := inf_le_left
  normal := by
    let f : L.toSubgroup →* K.toSubgroup := Subgroup.inclusion hLK
    have heq : extensionSubgroup L (L ⊓ M.field) inf_le_left =
        (extensionSubgroup K M.field M.below).comap f := by
      ext x
      rw [mem_extensionSubgroup_iff, Subgroup.mem_comap,
        mem_extensionSubgroup_iff]
      change (x : G) ∈ L ⊓ M.field ↔ (x : G) ∈ M.field
      exact ⟨fun hx => hx.2, fun hx => ⟨x.property, hx⟩⟩
    rw [heq]
    let : (extensionSubgroup K M.field M.below).Normal := M.normal
    infer_instance
  finite := by
    let f : L.toSubgroup →* K.toSubgroup := Subgroup.inclusion hLK
    let E := extensionSubgroup K M.field M.below
    have heq : extensionSubgroup L (L ⊓ M.field) inf_le_left = E.comap f := by
      ext x
      rw [mem_extensionSubgroup_iff, Subgroup.mem_comap]
      dsimp only [E, f, Subgroup.inclusion]
      rw [mem_extensionSubgroup_iff]
      change (x : G) ∈ L ⊓ M.field ↔ (x : G) ∈ M.field
      exact ⟨fun hx => hx.2, fun hx => ⟨x.property, hx⟩⟩
    let : Finite (K.toSubgroup ⧸ E) := M.finite
    let : E.Normal := M.normal
    have hE0 : E.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hrel0 : E.relIndex f.range ≠ 0 := by
      intro hzero
      have hdvd : E.relIndex f.range ∣ E.index :=
        E.relIndex_dvd_index_of_normal f.range
      rw [hzero, zero_dvd_iff] at hdvd
      exact hE0 hdvd
    apply Nat.finite_of_card_ne_zero
    change (extensionSubgroup L (L ⊓ M.field) inf_le_left).index ≠ 0
    rw [heq, E.index_comap f]
    exact hrel0

/-- The trivial extension `K / K`. -/
def refl (K : ClosedSubgroup G) : FiniteGaloisSubextension K where
  field := K
  below := le_rfl
  normal := by
    have htop : extensionSubgroup K K le_rfl = ⊤ := by
      rw [eq_top_iff]
      intro x _
      exact x.2
    rw [htop]
    infer_instance
  finite := by
    have htop : extensionSubgroup K K le_rfl = ⊤ := by
      rw [eq_top_iff]
      intro x _
      exact x.2
    rw [htop]
    infer_instance

/-- The compositum `L₁L₂`, represented by `G_{L₁} ∩ G_{L₂}`. -/
def compositum (L₁ L₂ : FiniteGaloisSubextension K) :
    FiniteGaloisSubextension K where
  field := L₁.field ⊓ L₂.field
  below := fun _ h => L₁.below h.1
  normal := by
    have heq : extensionSubgroup K (L₁.field ⊓ L₂.field)
        (fun _ h => L₁.below h.1) =
        extensionSubgroup K L₁.field L₁.below ⊓
          extensionSubgroup K L₂.field L₂.below := by
      ext k
      simp only [Subgroup.mem_inf, mem_extensionSubgroup_iff]
      constructor
      · intro hk
        exact ⟨hk.1, hk.2⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨h₁, h₂⟩
    rw [heq]
    let : (extensionSubgroup K L₁.field L₁.below).Normal := L₁.normal
    let : (extensionSubgroup K L₂.field L₂.below).Normal := L₂.normal
    infer_instance
  finite := by
    have heq : extensionSubgroup K (L₁.field ⊓ L₂.field)
        (fun _ h => L₁.below h.1) =
        extensionSubgroup K L₁.field L₁.below ⊓
          extensionSubgroup K L₂.field L₂.below := by
      ext k
      simp only [Subgroup.mem_inf, mem_extensionSubgroup_iff]
      constructor
      · intro hk
        exact ⟨hk.1, hk.2⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨h₁, h₂⟩
    let : (extensionSubgroup K L₁.field L₁.below).FiniteIndex :=
      @Subgroup.finiteIndex_of_finite_quotient K.toSubgroup _
        (extensionSubgroup K L₁.field L₁.below) L₁.finite
    let : (extensionSubgroup K L₂.field L₂.below).FiniteIndex :=
      @Subgroup.finiteIndex_of_finite_quotient K.toSubgroup _
        (extensionSubgroup K L₂.field L₂.below) L₂.finite
    rw [heq]
    exact Subgroup.finite_quotient_of_finiteIndex

/-- The constructed Galois compositum satisfies the left comparison bound. -/
theorem compositum_le_left (L₁ L₂ : FiniteGaloisSubextension K) :
    (L₁.compositum L₂).field.toSubgroup ≤ L₁.field.toSubgroup :=
  inf_le_left

/-- The constructed Galois compositum satisfies the right comparison bound. -/
theorem compositum_le_right (L₁ L₂ : FiniteGaloisSubextension K) :
    (L₁.compositum L₂).field.toSubgroup ≤ L₂.field.toSubgroup :=
  inf_le_right

end FiniteGaloisSubextension

end GroupOnly

section Representation

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-- The norm group from a compositum is contained in the norm group from
its first factor. -/
theorem finiteNormSubgroup_compositum_le_left
    (A : Rep ℤ G) (L₁ L₂ : FiniteGaloisSubextension K) :
    letI := (L₁.compositum L₂).finite
    letI := L₁.finite
    finiteNormSubgroup A K (L₁.compositum L₂).field
        (L₁.compositum L₂).below ≤
      finiteNormSubgroup A K L₁.field L₁.below := by
  let P := L₁.compositum L₂
  let hPL₁ := L₁.compositum_le_left L₂
  let : Finite (K.toSubgroup ⧸
      extensionSubgroup K P.field P.below) := P.finite
  let : Finite (K.toSubgroup ⧸
      extensionSubgroup K L₁.field L₁.below) := L₁.finite
  have hPKindex : P.field.toSubgroup.relIndex K.toSubgroup ≠ 0 := by
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite
  have hPLindex : P.field.toSubgroup.relIndex L₁.field.toSubgroup ≠ 0 := by
    intro hzero
    have hmul := Subgroup.relIndex_mul_relIndex
      P.field.toSubgroup L₁.field.toSubgroup K.toSubgroup hPL₁ L₁.below
    rw [hzero, zero_mul] at hmul
    exact hPKindex hmul.symm
  let hPLfinite : Finite (L₁.field.toSubgroup ⧸
      extensionSubgroup L₁.field P.field hPL₁) := by
    apply Nat.finite_of_card_ne_zero
    change (extensionSubgroup L₁.field P.field hPL₁).index ≠ 0
    simpa [Subgroup.relIndex] using hPLindex
  let T : DegreeData.FiniteTower G := {
    top := P.field
    middle := L₁.field
    base := K
    top_le_middle := hPL₁
    middle_le_base := L₁.below
    finiteTopQuotient := hPLfinite
    finiteBaseQuotient := L₁.finite }
  rintro x ⟨a, rfl⟩
  refine ⟨relativeNorm A L₁.field P.field hPL₁ a, ?_⟩
  exact T.norm_trans_apply A a

/-- The symmetric norm-group containment for the second factor. -/
theorem finiteNormSubgroup_compositum_le_right
    (A : Rep ℤ G) (L₁ L₂ : FiniteGaloisSubextension K) :
    letI := (L₁.compositum L₂).finite
    letI := L₂.finite
    finiteNormSubgroup A K (L₁.compositum L₂).field
        (L₁.compositum L₂).below ≤
      finiteNormSubgroup A K L₂.field L₂.below := by
  simpa [compositum, inf_comm] using
    finiteNormSubgroup_compositum_le_left A L₂ L₁

end FiniteGaloisSubextension

end Representation

end
end ClassFormation
