/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.GroupTheory.QuotientGroup.Basic
public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.IntegralRepUniverse
public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.NormKernelVanishing
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Degree.Indices
public import LeanPool.ClassFieldTheory.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger

/-! # Fields -/

@[expose] public section
namespace ClassFormation

open CyclicCohomology

/-!
# normalized degree and Frobenius theory: the initial datum and abstract fields

This file records the opening datum of abstract valuation theory and the
residue and ramification indices attached to inclusions of abstract fields.
As in, a field is represented contravariantly by a closed subgroup of the
ambient profinite group.
-/

noncomputable section

universe u

/-- The multiplicative presentation of `ℤ̂`; multiplication here is addition
in the profinite integers. -/
abbrev ZHatMul : Type 0 := Multiplicative ZHat

/-- The degree datum on a topological group: a continuous surjection
`d : G → ℤ̂`.  Profinite hypotheses belong to the ambient group and are
requested only by results that use them; they are not duplicated as proof
fields inside this datum. -/
structure DegreeData (G : Type*) [Group G] [TopologicalSpace G] where
  /-- The continuous degree homomorphism to the profinite integers. -/
  degree : G →ₜ* ZHatMul
  /-- The degree homomorphism is surjective. -/
  degree_surjective : Function.Surjective degree

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The distinguished base field, represented contravariantly by the full
ambient group. -/
def baseField (G : Type u) [Group G] [TopologicalSpace G] : ClosedSubgroup G where
  toSubgroup := ⊤
  isClosed' := isClosed_univ

/-- The distinguished base field is represented by the full ambient subgroup. -/
@[simp]
theorem baseField_toSubgroup (G : Type u) [Group G] [TopologicalSpace G] :
    (baseField G).toSubgroup = ⊤ :=
  rfl

/-- Every abstract field lies over the distinguished base field. -/
theorem le_baseField (K : ClosedSubgroup G) :
    K.toSubgroup ≤ (baseField G).toSubgroup :=
  le_top

namespace DegreeData

/-- The inertia group `I = ker d`, including its closedness. -/
def inertia (D : DegreeData G) : ClosedSubgroup G where
  toSubgroup := D.degree.toMonoidHom.ker
  isClosed' := by
    change IsClosed {g : G | (D.degree g).toAdd = 0}
    exact isClosed_eq D.degree.continuous_toFun continuous_const

/-- An element is inertial exactly when its degree is the multiplicative identity. -/
@[simp]
theorem mem_inertia_iff (D : DegreeData G) (g : G) :
    g ∈ D.inertia ↔ D.degree g = 1 :=
  Iff.rfl

/-- The restriction of `d` to the subgroup representing an abstract field. -/
def restrictedDegree (D : DegreeData G) (K : ClosedSubgroup G) :
    K.toSubgroup →ₜ* ZHatMul where
  toMonoidHom := D.degree.toMonoidHom.comp K.toSubgroup.subtype
  continuous_toFun := D.degree.continuous_toFun.comp continuous_subtype_val

/-- The restricted degree map evaluates through the underlying ambient element. -/
@[simp]
theorem restrictedDegree_apply (D : DegreeData G) (K : ClosedSubgroup G)
    (k : K.toSubgroup) : D.restrictedDegree K k = D.degree k.1 :=
  rfl

/-- The image `d(G_K)` in `ℤ̂`. -/
def fieldImage (D : DegreeData G) (K : ClosedSubgroup G) : Subgroup ZHatMul :=
  (D.restrictedDegree K).toMonoidHom.range

/-- The field's degree image is the image of its subgroup under the ambient degree map. -/
theorem fieldImage_eq_map (D : DegreeData G) (K : ClosedSubgroup G) :
    D.fieldImage K = K.toSubgroup.map D.degree.toMonoidHom := by
  ext z
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k.1, k.2, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩

/-- The inertia group `I_K = G_K ∩ I` over `K`. -/
def fieldInertia (D : DegreeData G) (K : ClosedSubgroup G) : ClosedSubgroup G :=
  K ⊓ D.inertia

/-- Field inertia consists of field elements whose ambient degree is one. -/
@[simp]
theorem mem_fieldInertia_iff (D : DegreeData G) (K : ClosedSubgroup G) (g : G) :
    g ∈ D.fieldInertia K ↔ g ∈ K ∧ D.degree g = 1 :=
  Iff.rfl

/-- `I_K` viewed inside `G_K`; equivalently, the kernel of `d|G_K`. -/
def fieldInertiaWithin (D : DegreeData G) (K : ClosedSubgroup G) :
    Subgroup K.toSubgroup :=
  (D.restrictedDegree K).toMonoidHom.ker

/-- The degree kernel defining inertia inside a field subgroup is normal. -/
instance fieldInertiaWithin_normal (D : DegreeData G) (K : ClosedSubgroup G) :
    (D.fieldInertiaWithin K).Normal := by
  rw [fieldInertiaWithin]
  infer_instance

/-- Membership in internal field inertia is equivalent to having ambient degree one. -/
@[simp]
theorem mem_fieldInertiaWithin_iff (D : DegreeData G) (K : ClosedSubgroup G)
    (k : K.toSubgroup) : k ∈ D.fieldInertiaWithin K ↔ D.degree k.1 = 1 :=
  Iff.rfl

/-- The absolute residue degree as the cardinality of the actual quotient of
`ZHat` by the degree image. -/
noncomputable def residueDegreeCardinal (D : DegreeData G)
    (K : ClosedSubgroup G) : Cardinal :=
  relativeIndexCardinal
    (show D.fieldImage K ≤ (⊤ : Subgroup ZHatMul) from le_top)

/-- The actual quotient whose cardinality is the absolute residue degree. -/
def residueQuotient (D : DegreeData G) (K : ClosedSubgroup G) : Type :=
  (⊤ : Subgroup ZHatMul) ⧸ (D.fieldImage K).subgroupOf ⊤

/-- The cardinal residue degree is the cardinality of the concrete residue quotient. -/
@[simp] theorem residueDegreeCardinal_eq_mk_residueQuotient
    (D : DegreeData G) (K : ClosedSubgroup G) :
    D.residueDegreeCardinal K = Cardinal.mk (D.residueQuotient K) :=
  rfl

/-- The distinguished base field has absolute residue degree one, without
passing through a natural-valued subgroup index. -/
theorem residueDegreeCardinal_baseField (D : DegreeData G) :
    D.residueDegreeCardinal (baseField G) = 1 := by
  change
    intersectionIndexCardinal (D.fieldImage (baseField G))
      (⊤ : Subgroup ZHatMul) = 1
  rw [D.fieldImage_eq_map, baseField_toSubgroup,
    Subgroup.map_top_of_surjective _ D.degree_surjective]
  change Cardinal.mk (↥(⊤ : Subgroup ZHatMul) ⧸ ⊤) = 1
  let : Subsingleton (↥(⊤ : Subgroup ZHatMul) ⧸
      (⊤ : Subgroup ↥(⊤ : Subgroup ZHatMul))) :=
    QuotientGroup.subsingleton_quotient_top
  exact Cardinal.mk_eq_one _

/-- An abstract field together with finiteness of its actual degree-image
quotient.  Its numerical residue degree is therefore genuinely positive. -/
structure FiniteResidueAbstractField (D : DegreeData G) where
  /-- The closed subgroup representing the abstract field. -/
  field : ClosedSubgroup G
  /-- The field's residue quotient is finite. -/
  finiteResidueQuotient : Finite (D.residueQuotient field)

namespace FiniteResidueAbstractField

variable {D : DegreeData G}

/-- Bundle a field at the boundary where its actual residue quotient is known
to be finite. -/
def ofField (D : DegreeData G) (K : ClosedSubgroup G)
    [hfinite : Finite (D.residueQuotient K)] :
    FiniteResidueAbstractField D where
  field := K
  finiteResidueQuotient := hfinite

/-- The underlying subgroup. -/
@[implicit_reducible]
def toSubgroup (K : FiniteResidueAbstractField D) : Subgroup G :=
  K.field.toSubgroup

/-- A finite-residue abstract field supplies finiteness of its residue quotient. -/
instance (K : FiniteResidueAbstractField D) :
    Finite (D.residueQuotient K.field) :=
  K.finiteResidueQuotient

/-- The positive absolute residue degree. -/
noncomputable def residueDegree (K : FiniteResidueAbstractField D) : ℕ+ := by
  letI : Nonempty (D.residueQuotient K.field) := ⟨QuotientGroup.mk 1⟩
  exact ⟨Nat.card (D.residueQuotient K.field), Nat.card_pos⟩

/-- The natural value of the positive residue degree is the quotient's `Nat.card`. -/
@[simp] theorem residueDegree_coe (K : FiniteResidueAbstractField D) :
    (K.residueDegree : ℕ) = Nat.card (D.residueQuotient K.field) :=
  rfl

/-- Cardinal-to-positive-natural specialization at the finite boundary. -/
theorem residueDegreeCardinal_eq_coe
    (K : FiniteResidueAbstractField D) :
    D.residueDegreeCardinal K.field = ((K.residueDegree : ℕ) : Cardinal) := by
  change Cardinal.mk (D.residueQuotient K.field) =
    (Nat.card (D.residueQuotient K.field) : Cardinal)
  exact Nat.cast_card.symm

end FiniteResidueAbstractField

end DegreeData

namespace DegreeData

/-- An abstract field extension, including the containment which makes the
notation `L / K` meaningful in the closed-subgroup model.  Keeping this proof
in the object prevents predicates for extensions from being formed for
unrelated closed subgroups. -/
structure AbstractExtension (G : Type*) [Group G] [TopologicalSpace G] where
  /-- The closed subgroup contravariantly representing the extension field. -/
  field : ClosedSubgroup G
  /-- The closed subgroup contravariantly representing the base field. -/
  base : ClosedSubgroup G
  /-- Contravariance turns the field inclusion into this subgroup inclusion. -/
  below : field.toSubgroup ≤ base.toSubgroup

namespace AbstractExtension

/-- The subgroup of the base group represented by the extension field.  This
projection packages the proof-dependent `subgroupOf` construction behind the
extension object. -/
def subgroup (E : AbstractExtension G) : Subgroup E.base.toSubgroup :=
  extensionSubgroup E.base E.field E.below

/-- The actual relative coset space of an abstract extension. -/
def quotient (E : AbstractExtension G) : Type u :=
  E.base.toSubgroup ⧸ E.subgroup

/-- The honest cardinal degree of an arbitrary abstract extension.  Unlike
the raw natural-valued subgroup index, this does not encode infinity as zero. -/
noncomputable def degreeCardinal (E : AbstractExtension G) : Cardinal :=
  relativeIndexCardinal E.below

/-- The cardinal degree of an abstract extension is the cardinality of its coset space. -/
@[simp] theorem degreeCardinal_eq_mk_quotient (E : AbstractExtension G) :
    E.degreeCardinal = Cardinal.mk E.quotient :=
  rfl

/-- The relative residue degree of an arbitrary abstract extension, as the
cardinality of the actual coset type of degree images.  This is the canonical
general API: an infinite residue degree remains an infinite cardinal. -/
noncomputable def relativeResidueDegreeCardinal
    (E : AbstractExtension G) (D : DegreeData G) : Cardinal :=
  relativeIndexCardinal (Subgroup.map_mono (f := D.degree.toMonoidHom) E.below)

/-- The relative ramification index of an arbitrary abstract extension, as
the cardinality of the actual coset type inside the degree kernel.  In
particular, infinity is not encoded as zero. -/
noncomputable def relativeRamificationIndexCardinal
    (E : AbstractExtension G) (D : DegreeData G) : Cardinal :=
  relativeIndexCardinal
    (show E.field.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤
      E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker from
        inf_le_inf E.below le_rfl)

/-- The cardinal-valued fundamental identity for an arbitrary abstract
extension.  The residue cardinal is lifted from the universe of `ZHat`; no
finiteness assumption or infinite-index convention is involved. -/
theorem degreeCardinal_eq_relativeResidueDegreeCardinal_mul_relativeRamificationIndexCardinal
    (E : AbstractExtension G) (D : DegreeData G) :
    E.degreeCardinal =
      Cardinal.lift.{u} (E.relativeResidueDegreeCardinal D) *
        E.relativeRamificationIndexCardinal D := by
  simpa [degreeCardinal, relativeResidueDegreeCardinal,
    relativeRamificationIndexCardinal] using
    (relativeIndexCardinal_eq_map_mul_inf_ker
      D.degree.toMonoidHom E.below)

/-- Cardinal Frobenius residue-degree compatibility: the relative residue
cardinal times the absolute residue cardinal of the base is the absolute
residue cardinal of the extension field. -/
theorem relativeResidueDegreeCardinal_mul_residueDegreeCardinal
    (E : AbstractExtension G) (D : DegreeData G) :
    E.relativeResidueDegreeCardinal D * D.residueDegreeCardinal E.base =
      D.residueDegreeCardinal E.field := by
  change
    intersectionIndexCardinal
        (E.field.toSubgroup.map D.degree.toMonoidHom)
        (E.base.toSubgroup.map D.degree.toMonoidHom) *
      intersectionIndexCardinal (D.fieldImage E.base) (⊤ : Subgroup ZHatMul) =
        intersectionIndexCardinal (D.fieldImage E.field) (⊤ : Subgroup ZHatMul)
  rw [D.fieldImage_eq_map,
    D.fieldImage_eq_map]
  simpa only [relativeIndexCardinal] using
    (relativeIndexCardinal_mul
      (Subgroup.map_mono (f := D.degree.toMonoidHom) E.below)
      (show E.base.toSubgroup.map D.degree.toMonoidHom ≤
        (⊤ : Subgroup ZHatMul) from le_top))

/-- A composable tower of abstract extensions, represented by three closed
subgroups and the two adjacent containments. -/
structure Tower (G : Type*) [Group G] [TopologicalSpace G] where
  /-- The closed subgroup representing the top field. -/
  top : ClosedSubgroup G
  /-- The closed subgroup representing the middle field. -/
  middle : ClosedSubgroup G
  /-- The closed subgroup representing the base field. -/
  base : ClosedSubgroup G
  /-- Contravariant containment for the top-to-middle extension. -/
  top_le_middle : top.toSubgroup ≤ middle.toSubgroup
  /-- Contravariant containment for the middle-to-base extension. -/
  middle_le_base : middle.toSubgroup ≤ base.toSubgroup

namespace Tower

variable (T : Tower G)

/-- The upper extension in a tower. -/
def topExtension : AbstractExtension G where
  field := T.top
  base := T.middle
  below := T.top_le_middle

/-- The lower extension in a tower. -/
def baseExtension : AbstractExtension G where
  field := T.middle
  base := T.base
  below := T.middle_le_base

/-- The composite extension in a tower. -/
def totalExtension : AbstractExtension G where
  field := T.top
  base := T.base
  below := T.top_le_middle.trans T.middle_le_base

/-- Cardinal degrees multiply in an arbitrary abstract-extension tower. -/
theorem degreeCardinal_mul :
    T.topExtension.degreeCardinal * T.baseExtension.degreeCardinal =
      T.totalExtension.degreeCardinal := by
  exact relativeIndexCardinal_mul T.top_le_middle T.middle_le_base

/-- Cardinal residue degrees multiply in an arbitrary abstract-extension
tower. -/
theorem relativeResidueDegreeCardinal_mul (D : DegreeData G) :
    T.topExtension.relativeResidueDegreeCardinal D *
        T.baseExtension.relativeResidueDegreeCardinal D =
      T.totalExtension.relativeResidueDegreeCardinal D := by
  exact relativeIndexCardinal_mul
    (Subgroup.map_mono (f := D.degree.toMonoidHom) T.top_le_middle)
    (Subgroup.map_mono (f := D.degree.toMonoidHom) T.middle_le_base)

/-- Cardinal ramification indices multiply in an arbitrary
abstract-extension tower. -/
theorem relativeRamificationIndexCardinal_mul (D : DegreeData G) :
    T.topExtension.relativeRamificationIndexCardinal D *
        T.baseExtension.relativeRamificationIndexCardinal D =
      T.totalExtension.relativeRamificationIndexCardinal D := by
  exact relativeIndexCardinal_mul
    (show T.top.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤
      T.middle.toSubgroup ⊓ D.degree.toMonoidHom.ker from
        inf_le_inf T.top_le_middle le_rfl)
    (show T.middle.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤
      T.base.toSubgroup ⊓ D.degree.toMonoidHom.ker from
        inf_le_inf T.middle_le_base le_rfl)

end Tower

/-- An abstract extension is unramified when the inertia subgroup of its base
is already contained in the subgroup representing its field.  This
containment is the definition; it does not pass through a natural-valued index
that would encode an infinite index as zero. -/
def IsUnramified (E : AbstractExtension G) (D : DegreeData G) : Prop :=
  E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ E.field.toSubgroup

/-- An abstract extension is totally ramified when the degree image of its
base is contained in the degree image of its field. -/
def IsTotallyRamified (E : AbstractExtension G) (D : DegreeData G) : Prop :=
  E.base.toSubgroup.map D.degree.toMonoidHom ≤
    E.field.toSubgroup.map D.degree.toMonoidHom

/-- An extension is unramified exactly when the inertia subgroup of its base
is contained in the subgroup representing its field.  The containment needed
to form the extension is carried by `E`. -/
theorem isUnramified_iff_inertia_le (E : AbstractExtension G) (D : DegreeData G) :
    E.IsUnramified D ↔
      E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ E.field.toSubgroup :=
  Iff.rfl

/-- An extension is totally ramified exactly when the degree image of its
base is contained in the degree image of its field. -/
theorem isTotallyRamified_iff_image_le (E : AbstractExtension G) (D : DegreeData G) :
    E.IsTotallyRamified D ↔
      E.base.toSubgroup.map D.degree.toMonoidHom ≤
        E.field.toSubgroup.map D.degree.toMonoidHom :=
  Iff.rfl

/-- An unramified extension has cardinal ramification index one. -/
theorem relativeRamificationIndexCardinal_eq_one_of_isUnramified
    (E : AbstractExtension G) (D : DegreeData G) (hE : E.IsUnramified D) :
    E.relativeRamificationIndexCardinal D = 1 := by
  have heq :
      E.field.toSubgroup ⊓ D.degree.toMonoidHom.ker =
        E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker := by
    apply le_antisymm
    · exact inf_le_inf E.below le_rfl
    · intro x hx
      exact ⟨hE hx, hx.2⟩
  change
    intersectionIndexCardinal
      (E.field.toSubgroup ⊓ D.degree.toMonoidHom.ker)
      (E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker) = 1
  rw [heq]
  exact relativeIndexCardinal_self _

/-- A totally ramified extension has cardinal residue degree one. -/
theorem relativeResidueDegreeCardinal_eq_one_of_isTotallyRamified
    (E : AbstractExtension G) (D : DegreeData G)
    (hE : E.IsTotallyRamified D) :
    E.relativeResidueDegreeCardinal D = 1 := by
  have heq :
      E.field.toSubgroup.map D.degree.toMonoidHom =
        E.base.toSubgroup.map D.degree.toMonoidHom :=
    le_antisymm (Subgroup.map_mono (f := D.degree.toMonoidHom) E.below) hE
  change
    intersectionIndexCardinal
      (E.field.toSubgroup.map D.degree.toMonoidHom)
      (E.base.toSubgroup.map D.degree.toMonoidHom) = 1
  rw [heq]
  exact relativeIndexCardinal_self _

/-- For an unramified extension, its cardinal degree is its lifted residue
degree. -/
theorem degreeCardinal_eq_lift_relativeResidueDegreeCardinal_of_isUnramified
    (E : AbstractExtension G) (D : DegreeData G) (hE : E.IsUnramified D) :
    E.degreeCardinal =
      Cardinal.lift.{u} (E.relativeResidueDegreeCardinal D) := by
  rw [E.degreeCardinal_eq_relativeResidueDegreeCardinal_mul_relativeRamificationIndexCardinal D,
    E.relativeRamificationIndexCardinal_eq_one_of_isUnramified D hE, mul_one]

/-- For a totally ramified extension, its cardinal degree is its
ramification cardinal. -/
theorem degreeCardinal_eq_relativeRamificationIndexCardinal_of_isTotallyRamified
    (E : AbstractExtension G) (D : DegreeData G)
    (hE : E.IsTotallyRamified D) :
    E.degreeCardinal = E.relativeRamificationIndexCardinal D := by
  rw [E.degreeCardinal_eq_relativeResidueDegreeCardinal_mul_relativeRamificationIndexCardinal D,
    E.relativeResidueDegreeCardinal_eq_one_of_isTotallyRamified D hE]
  simp

end AbstractExtension

/-- A (not necessarily finite) Galois extension above `K`.  Normality and
the inclusion of the upper field are carried by the object, while no
finiteness assumption is introduced. -/
structure GaloisSubextension (K : ClosedSubgroup G) where
  /-- The closed subgroup representing the top field. -/
  field : ClosedSubgroup G
  /-- The top-field subgroup is contained in the base-field subgroup. -/
  below : field.toSubgroup ≤ K.toSubgroup
  /-- The relative subgroup is normal in the base-field subgroup. -/
  normal : (extensionSubgroup K field below).Normal

namespace GaloisSubextension

variable {K : ClosedSubgroup G}

/-- Forget normality while retaining the underlying abstract extension. -/
def toAbstractExtension (L : GaloisSubextension K) :
    DegreeData.AbstractExtension G where
  field := L.field
  base := K
  below := L.below

/-- The actual quotient represented by a Galois subextension.  This is a
named object boundary rather than a transparent abbreviation. -/
def extensionQuotient (L : GaloisSubextension K) : Type u :=
  K.toSubgroup ⧸ extensionSubgroup K L.field L.below

/-- Structural unramifiedness of a Galois subextension. -/
def IsUnramified (L : GaloisSubextension K) (D : DegreeData G) : Prop :=
  L.toAbstractExtension.IsUnramified D

/-- Structural total ramification of a Galois subextension. -/
def IsTotallyRamified (L : GaloisSubextension K) (D : DegreeData G) : Prop :=
  L.toAbstractExtension.IsTotallyRamified D

/-- A Galois subextension has a normal subgroup inside its base subgroup. -/
instance extensionSubgroup_normalInstance (L : GaloisSubextension K) :
    (extensionSubgroup K L.field L.below).Normal :=
  L.normal

/-- The group structure transported across the named quotient boundary. -/
instance extensionQuotientGroupInstance (L : GaloisSubextension K) :
    Group L.extensionQuotient := by
  change Group
    (K.toSubgroup ⧸ extensionSubgroup K L.field L.below)
  infer_instance

/-- Comparison with the quotient presentation used by the underlying group
library. -/
def extensionQuotientMulEquiv (L : GaloisSubextension K) :
    L.extensionQuotient ≃*
      (K.toSubgroup ⧸ extensionSubgroup K L.field L.below) :=
  MulEquiv.refl _

/-- The canonical quotient projection for a Galois subextension. -/
def extensionQuotientMk (L : GaloisSubextension K) :
    K.toSubgroup →* L.extensionQuotient :=
  QuotientGroup.mk' (extensionSubgroup K L.field L.below)

/-- The named quotient projection agrees with `QuotientGroup.mk` under the
comparison equivalence. -/
@[simp]
theorem extensionQuotientMk_apply (L : GaloisSubextension K)
    (k : K.toSubgroup) :
    L.extensionQuotientMulEquiv (L.extensionQuotientMk k) =
      (QuotientGroup.mk k :
        K.toSubgroup ⧸ extensionSubgroup K L.field L.below) :=
  rfl

/-- Eliminate a Galois quotient without exposing a chosen representative. -/
protected theorem extensionQuotient_inductionOn
    (L : GaloisSubextension K) {motive : L.extensionQuotient → Prop}
    (q : L.extensionQuotient)
    (mk : ∀ k : K.toSubgroup, motive (L.extensionQuotientMk k)) :
    motive q := by
  exact @Quotient.inductionOn' K.toSubgroup
    (QuotientGroup.leftRel (extensionSubgroup K L.field L.below))
    motive q mk

/-- Unramifiedness is the canonical inertia-containment condition. -/
theorem isUnramified_iff_inertia_le (L : GaloisSubextension K)
    (D : DegreeData G) :
    L.IsUnramified D ↔
      K.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ L.field.toSubgroup :=
  L.toAbstractExtension.isUnramified_iff_inertia_le D

/-- Total ramification is the canonical equality of degree images. -/
theorem isTotallyRamified_iff_image_le (L : GaloisSubextension K)
    (D : DegreeData G) :
    L.IsTotallyRamified D ↔
      K.toSubgroup.map D.degree.toMonoidHom ≤
        L.field.toSubgroup.map D.degree.toMonoidHom :=
  L.toAbstractExtension.isTotallyRamified_iff_image_le D

end GaloisSubextension

/-- A finite abstract extension.  Finiteness is carried by the extension
object, so its public numerical invariants can be positive naturals rather than
using the raw subgroup-index convention in which an infinite index is encoded
as `0`. -/
structure FiniteAbstractExtension (G : Type*) [Group G] [TopologicalSpace G]
    extends AbstractExtension G where
  /-- The relative quotient of the base subgroup by the extension subgroup is finite. -/
  finiteQuotient :
    Finite
      (toAbstractExtension.base.toSubgroup ⧸
        extensionSubgroup toAbstractExtension.base toAbstractExtension.field
          toAbstractExtension.below)

namespace FiniteAbstractExtension

variable (E : FiniteAbstractExtension G)

/-- The subgroup of the base represented by a finite extension. -/
def subgroup : Subgroup E.base.toSubgroup :=
  extensionSubgroup E.base E.field E.below

/-- The finite extension's actual relative coset space. -/
def quotient : Type u :=
  E.base.toSubgroup ⧸ E.subgroup

/-- Bundle an inclusion once its actual relative coset type is known to be
finite.  This is the canonical boundary from subgroup data to the finite
extension API; numerical invariants are obtained only from the resulting
object. -/
def ofInclusion (field base : ClosedSubgroup G)
    (below : field.toSubgroup ≤ base.toSubgroup)
    [hfinite : Finite
      (base.toSubgroup ⧸ extensionSubgroup base field below)] :
    FiniteAbstractExtension G where
  field := field
  base := base
  below := below
  finiteQuotient := hfinite

/-- The field endpoint of an extension bundled from an inclusion is the supplied field. -/
@[simp] theorem ofInclusion_field (field base : ClosedSubgroup G)
    (below : field.toSubgroup ≤ base.toSubgroup)
    [Finite (base.toSubgroup ⧸ extensionSubgroup base field below)] :
    (ofInclusion field base below).field = field :=
  rfl

/-- The base endpoint of an extension bundled from an inclusion is the supplied base. -/
@[simp] theorem ofInclusion_base (field base : ClosedSubgroup G)
    (below : field.toSubgroup ≤ base.toSubgroup)
    [Finite (base.toSubgroup ⧸ extensionSubgroup base field below)] :
    (ofInclusion field base below).base = base :=
  rfl

/-- The unramified predicate for a finite extension is the predicate on its
underlying abstract extension. -/
def IsUnramified (D : DegreeData G) : Prop :=
  E.toAbstractExtension.IsUnramified D

/-- The totally ramified predicate for a finite extension is the predicate on
its underlying abstract extension. -/
def IsTotallyRamified (D : DegreeData G) : Prop :=
  E.toAbstractExtension.IsTotallyRamified D

/-- Finite-extension unramifiedness is exactly unramifiedness of the underlying
abstract extension. -/
@[simp] theorem isUnramified_iff (D : DegreeData G) :
    E.IsUnramified D ↔ E.toAbstractExtension.IsUnramified D :=
  Iff.rfl

/-- Finite-extension total ramification is inherited from the underlying abstract extension. -/
@[simp] theorem isTotallyRamified_iff (D : DegreeData G) :
    E.IsTotallyRamified D ↔ E.toAbstractExtension.IsTotallyRamified D :=
  Iff.rfl

/-- Finite unramified extensions satisfy the same inertia-containment
characterization as their underlying abstract extensions. -/
theorem isUnramified_iff_inertia_le (D : DegreeData G) :
    E.IsUnramified D ↔
      E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ E.field.toSubgroup :=
  E.toAbstractExtension.isUnramified_iff_inertia_le D

/-- Finite totally ramified extensions satisfy the same degree-image
characterization as their underlying abstract extensions. -/
theorem isTotallyRamified_iff_image_le (D : DegreeData G) :
    E.IsTotallyRamified D ↔
      E.base.toSubgroup.map D.degree.toMonoidHom ≤
        E.field.toSubgroup.map D.degree.toMonoidHom :=
  E.toAbstractExtension.isTotallyRamified_iff_image_le D

/-- The coset space carried by a finite abstract extension is finite. -/
instance quotientFinite :
    Finite E.quotient := by
  simpa [quotient, subgroup] using E.finiteQuotient

/-- The finite instance in the concrete quotient presentation used by norm
maps. -/
instance representedQuotientFinite :
    Finite
      (E.base.toSubgroup ⧸
        extensionSubgroup E.base E.field E.below) :=
  E.finiteQuotient

private theorem degreeCardinal_lt_aleph0 :
    E.toAbstractExtension.degreeCardinal < Cardinal.aleph0 := by
  change Cardinal.mk
      (E.base.toSubgroup ⧸ extensionSubgroup E.base E.field E.below) <
    Cardinal.aleph0
  exact Cardinal.lt_aleph0_of_finite _

private theorem relativeDegreeCardinals_lt_aleph0 (D : DegreeData G) :
    Cardinal.lift.{u}
          (E.toAbstractExtension.relativeResidueDegreeCardinal D) <
        Cardinal.aleph0 ∧
      E.toAbstractExtension.relativeRamificationIndexCardinal D <
        Cardinal.aleph0 := by
  have hresidueUnlifted :
      E.toAbstractExtension.relativeResidueDegreeCardinal D ≠ 0 := by
    rw [AbstractExtension.relativeResidueDegreeCardinal,
      relativeIndexCardinal, intersectionIndexCardinal]
    exact Cardinal.mk_ne_zero _
  have hresidue :
      Cardinal.lift.{u}
          (E.toAbstractExtension.relativeResidueDegreeCardinal D) ≠ 0 := by
    intro hzero
    exact hresidueUnlifted (Cardinal.lift_eq_zero.mp hzero)
  have hramification :
      E.toAbstractExtension.relativeRamificationIndexCardinal D ≠ 0 := by
    rw [AbstractExtension.relativeRamificationIndexCardinal,
      relativeIndexCardinal, intersectionIndexCardinal]
    exact Cardinal.mk_ne_zero _
  apply (Cardinal.mul_lt_aleph0_iff_of_ne_zero
    hresidue hramification).mp
  rw [←
    E.toAbstractExtension.degreeCardinal_eq_relativeResidueDegreeCardinal_mul_relativeRamificationIndexCardinal D]
  exact E.degreeCardinal_lt_aleph0

private theorem relativeResidueDegreeCardinal_lt_aleph0
    (D : DegreeData G) :
    E.toAbstractExtension.relativeResidueDegreeCardinal D <
      Cardinal.aleph0 :=
  Cardinal.lift_lt_aleph0.mp (E.relativeDegreeCardinals_lt_aleph0 D).1

private theorem relativeRamificationIndexCardinal_lt_aleph0
    (D : DegreeData G) :
    E.toAbstractExtension.relativeRamificationIndexCardinal D <
      Cardinal.aleph0 :=
  (E.relativeDegreeCardinals_lt_aleph0 D).2

/-- The residue coset type of a finite extension is finite.  This is derived
from the cardinal fundamental identity, rather than from a natural-valued
index whose infinite case would be represented by zero. -/
noncomputable instance residueQuotientFinite (D : DegreeData G) :
    Finite
      (↥(E.base.toSubgroup.map D.degree.toMonoidHom) ⧸
        (E.field.toSubgroup.map D.degree.toMonoidHom).subgroupOf
          (E.base.toSubgroup.map D.degree.toMonoidHom)) := by
  apply Cardinal.lt_aleph0_iff_finite.mp
  simpa [AbstractExtension.relativeResidueDegreeCardinal,
    relativeIndexCardinal, intersectionIndexCardinal] using
      E.relativeResidueDegreeCardinal_lt_aleph0 D

/-- The inertia coset type of a finite extension is finite.  As for the
residue quotient, this is a consequence of the cardinal fundamental identity. -/
noncomputable instance ramificationQuotientFinite (D : DegreeData G) :
    Finite
      (↥(E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker) ⧸
        (E.field.toSubgroup ⊓ D.degree.toMonoidHom.ker).subgroupOf
          (E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker)) := by
  apply Cardinal.lt_aleph0_iff_finite.mp
  simpa [AbstractExtension.relativeRamificationIndexCardinal,
    relativeIndexCardinal, intersectionIndexCardinal] using
      E.relativeRamificationIndexCardinal_lt_aleph0 D

/-- The positive degree of a finite abstract extension. -/
def degree : ℕ+ :=
  by
    letI : Nonempty E.quotient :=
      ⟨QuotientGroup.mk 1⟩
    exact ⟨Nat.card E.quotient, Nat.card_pos⟩

/-- The positive relative residue degree of a finite abstract extension. -/
def residueDegree (D : DegreeData G) : ℕ+ :=
  ⟨Nat.card
      (↥(E.base.toSubgroup.map D.degree.toMonoidHom) ⧸
        (E.field.toSubgroup.map D.degree.toMonoidHom).subgroupOf
          (E.base.toSubgroup.map D.degree.toMonoidHom)),
    Nat.card_pos⟩

/-- The positive relative ramification index of a finite abstract extension. -/
def ramificationIndex (D : DegreeData G) : ℕ+ :=
  ⟨Nat.card
      (↥(E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker) ⧸
        (E.field.toSubgroup ⊓ D.degree.toMonoidHom.ker).subgroupOf
          (E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker)),
    Nat.card_pos⟩

/-- The natural value of the positive extension degree is the cardinality of its quotient. -/
@[simp] theorem degree_coe :
    (E.degree : ℕ) = Nat.card E.quotient :=
  rfl

/-- The positive residue degree coerces to the cardinality of the mapped-subgroup quotient. -/
@[simp] theorem residueDegree_coe (D : DegreeData G) :
    (E.residueDegree D : ℕ) =
      Nat.card
        (↥(E.base.toSubgroup.map D.degree.toMonoidHom) ⧸
          (E.field.toSubgroup.map D.degree.toMonoidHom).subgroupOf
            (E.base.toSubgroup.map D.degree.toMonoidHom)) :=
  rfl

/-- The positive ramification index coerces to the cardinality of the inertia quotient. -/
@[simp] theorem ramificationIndex_coe (D : DegreeData G) :
    (E.ramificationIndex D : ℕ) =
      Nat.card
        (↥(E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker) ⧸
          (E.field.toSubgroup ⊓ D.degree.toMonoidHom.ker).subgroupOf
            (E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker)) :=
  rfl

/-- The underlying subgroup index of a finite extension is the natural
coercion of its positive degree.  This theorem is a finite-only bridge, not a
general natural-valued degree definition. -/
@[simp] theorem relIndex_eq_degree :
    E.field.toSubgroup.relIndex E.base.toSubgroup = (E.degree : ℕ) := by
  rw [Subgroup.relIndex, Subgroup.index, E.degree_coe]
  rfl

/-- The index of the represented extension subgroup is the finite extension
degree. -/
@[simp] theorem extensionSubgroup_index_eq_degree :
    (extensionSubgroup E.base E.field E.below).index = (E.degree : ℕ) := by
  rw [Subgroup.index, E.degree_coe]
  rfl

/-- The relative index of the mapped field subgroups is the positive residue
degree of a finite extension. -/
theorem mapped_relIndex_eq_residueDegree (D : DegreeData G) :
    (E.field.toSubgroup.map D.degree.toMonoidHom).relIndex
        (E.base.toSubgroup.map D.degree.toMonoidHom) =
      (E.residueDegree D : ℕ) := by
  rw [Subgroup.relIndex, Subgroup.index, E.residueDegree_coe]

/-- The relative index inside the degree kernel is the positive ramification
index of a finite extension. -/
theorem inertia_relIndex_eq_ramificationIndex (D : DegreeData G) :
    (E.field.toSubgroup ⊓ D.degree.toMonoidHom.ker).relIndex
        (E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker) =
      (E.ramificationIndex D : ℕ) := by
  rw [Subgroup.relIndex, Subgroup.index, E.ramificationIndex_coe]

/-- The finite fundamental identity, stated only in terms of the positive
invariants carried by a finite extension object. -/
theorem degree_eq_residueDegree_mul_ramificationIndex (D : DegreeData G) :
    (E.degree : ℕ) =
      (E.residueDegree D : ℕ) * (E.ramificationIndex D : ℕ) := by
  rw [← E.relIndex_eq_degree, ← E.mapped_relIndex_eq_residueDegree D,
    ← E.inertia_relIndex_eq_ramificationIndex D]
  exact relIndex_eq_map_relIndex_mul_inf_ker_relIndex
    D.degree.toMonoidHom E.below

/-- An unramified finite extension has ramification index one. -/
theorem ramificationIndex_eq_one_of_isUnramified (D : DegreeData G)
    (hE : E.IsUnramified D) :
    (E.ramificationIndex D : ℕ) = 1 := by
  rw [← E.inertia_relIndex_eq_ramificationIndex D,
    Subgroup.relIndex_eq_one]
  intro x hx
  exact ⟨hE hx, hx.2⟩

/-- A totally ramified finite extension has residue degree one. -/
theorem residueDegree_eq_one_of_isTotallyRamified (D : DegreeData G)
    (hE : E.IsTotallyRamified D) :
    (E.residueDegree D : ℕ) = 1 := by
  rw [← E.mapped_relIndex_eq_residueDegree D,
    Subgroup.relIndex_eq_one]
  exact hE

/-- A finite extension has residue degree one exactly when it is totally
ramified.  This keeps callers on the structural predicate API instead of
unfolding the image-index implementation. -/
theorem isTotallyRamified_iff_residueDegree_eq_one (D : DegreeData G) :
    E.IsTotallyRamified D ↔ (E.residueDegree D : ℕ) = 1 := by
  constructor
  · exact E.residueDegree_eq_one_of_isTotallyRamified D
  · intro h
    rw [isTotallyRamified_iff_image_le]
    rw [← E.mapped_relIndex_eq_residueDegree D,
      Subgroup.relIndex_eq_one] at h
    exact h

/-- Converse form convenient for constructing the structural predicate from
the positive finite invariant. -/
theorem isTotallyRamified_of_residueDegree_eq_one (D : DegreeData G)
    (h : (E.residueDegree D : ℕ) = 1) : E.IsTotallyRamified D :=
  (E.isTotallyRamified_iff_residueDegree_eq_one D).2 h

/-- In an unramified finite extension, residue degree equals extension
degree. -/
theorem residueDegree_eq_degree_of_isUnramified (D : DegreeData G)
    (hE : E.IsUnramified D) :
    (E.residueDegree D : ℕ) = (E.degree : ℕ) := by
  rw [E.degree_eq_residueDegree_mul_ramificationIndex D,
    E.ramificationIndex_eq_one_of_isUnramified D hE, mul_one]

/-- In a totally ramified finite extension, ramification index equals
extension degree. -/
theorem ramificationIndex_eq_degree_of_isTotallyRamified (D : DegreeData G)
    (hE : E.IsTotallyRamified D) :
    (E.ramificationIndex D : ℕ) = (E.degree : ℕ) := by
  rw [E.degree_eq_residueDegree_mul_ramificationIndex D,
    E.residueDegree_eq_one_of_isTotallyRamified D hE, one_mul]

/-- For a finite extension, its cardinal-valued degree is the cardinal cast
of its positive natural degree. -/
theorem degreeCardinal_eq_coe :
    E.toAbstractExtension.degreeCardinal =
      ((E.degree : ℕ) : Cardinal) := by
  change Cardinal.mk
      (E.base.toSubgroup ⧸ extensionSubgroup E.base E.field E.below) =
    (Nat.card
      (E.base.toSubgroup ⧸ extensionSubgroup E.base E.field E.below) : Cardinal)
  simpa [quotient, subgroup] using
    ((Nat.cast_card :
      (Nat.card E.quotient : Cardinal) = Cardinal.mk E.quotient).symm)

/-- For a finite extension, the cardinal-valued relative residue degree is
the cardinal cast of the positive natural residue degree. -/
@[simp] theorem relativeResidueDegreeCardinal_eq_coe (D : DegreeData G) :
    E.toAbstractExtension.relativeResidueDegreeCardinal D =
      ((E.residueDegree D : ℕ) : Cardinal) := by
  change Cardinal.mk
    (↥(E.base.toSubgroup.map D.degree.toMonoidHom) ⧸
      (E.field.toSubgroup.map D.degree.toMonoidHom).subgroupOf
        (E.base.toSubgroup.map D.degree.toMonoidHom)) =
      (Nat.card
        (↥(E.base.toSubgroup.map D.degree.toMonoidHom) ⧸
          (E.field.toSubgroup.map D.degree.toMonoidHom).subgroupOf
            (E.base.toSubgroup.map D.degree.toMonoidHom)) : Cardinal)
  exact (Nat.cast_card).symm

/-- For a finite extension, the cardinal-valued relative ramification index
is the cardinal cast of the positive natural ramification index. -/
@[simp] theorem relativeRamificationIndexCardinal_eq_coe (D : DegreeData G) :
    E.toAbstractExtension.relativeRamificationIndexCardinal D =
      ((E.ramificationIndex D : ℕ) : Cardinal) := by
  change Cardinal.mk
    (↥(E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker) ⧸
      (E.field.toSubgroup ⊓ D.degree.toMonoidHom.ker).subgroupOf
        (E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker)) =
      (Nat.card
        (↥(E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker) ⧸
          (E.field.toSubgroup ⊓ D.degree.toMonoidHom.ker).subgroupOf
            (E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker)) : Cardinal)
  exact (Nat.cast_card).symm

end FiniteAbstractExtension

/-- A finite composable tower of abstract extensions.  The two adjacent
finite quotient proofs belong to the tower object, so downstream norm and
degree laws do not thread subgroup containments and finiteness instances as
independent arguments. -/
structure FiniteTower (G : Type*) [Group G] [TopologicalSpace G]
    extends AbstractExtension.Tower G where
  /-- The quotient for the top-to-middle extension is finite. -/
  finiteTopQuotient : Finite toTower.topExtension.quotient
  /-- The quotient for the middle-to-base extension is finite. -/
  finiteBaseQuotient : Finite toTower.baseExtension.quotient

namespace FiniteTower

variable (T : FiniteTower G)

/-- The upper relative quotient in a finite tower is finite. -/
instance topQuotientFinite :
    Finite (T.middle.toSubgroup ⧸
      extensionSubgroup T.middle T.top T.top_le_middle) :=
  T.finiteTopQuotient

/-- The lower relative quotient in a finite tower is finite. -/
instance baseQuotientFinite :
    Finite (T.base.toSubgroup ⧸
      extensionSubgroup T.base T.middle T.middle_le_base) :=
  T.finiteBaseQuotient

/-- The upper finite extension represented by a finite tower. -/
def topExtension : FiniteAbstractExtension G where
  toAbstractExtension := T.toTower.topExtension
  finiteQuotient := T.finiteTopQuotient

/-- The lower finite extension represented by a finite tower. -/
def baseExtension : FiniteAbstractExtension G where
  toAbstractExtension := T.toTower.baseExtension
  finiteQuotient := T.finiteBaseQuotient

end FiniteTower

namespace FiniteResidueAbstractField

variable {D : DegreeData G}

/-- If the relative residue quotient over a field with finite absolute
residue quotient is finite, then the upper field also has finite absolute
residue quotient.  This is the minimal honest boundary constructor: it uses
the actual quotient types and the cardinal tower identity. -/
noncomputable def ofRelativeInclusion (D : DegreeData G)
    (field : ClosedSubgroup G) (base : FiniteResidueAbstractField D)
    (below : field.toSubgroup ≤ base.field.toSubgroup)
    [finiteRelativeResidueQuotient : Finite
      (↥(base.field.toSubgroup.map D.degree.toMonoidHom) ⧸
        (field.toSubgroup.map D.degree.toMonoidHom).subgroupOf
          (base.field.toSubgroup.map D.degree.toMonoidHom))] :
    FiniteResidueAbstractField D where
  field := field
  finiteResidueQuotient := by
    apply Cardinal.lt_aleph0_iff_finite.mp
    rw [← D.residueDegreeCardinal_eq_mk_residueQuotient]
    let E : AbstractExtension G := {
      field := field
      base := base.field
      below := below
    }
    rw [← E.relativeResidueDegreeCardinal_mul_residueDegreeCardinal D]
    apply Cardinal.mul_lt_aleph0_iff.mpr
    exact Or.inr (Or.inr ⟨by
      change Cardinal.mk
          (↥(base.field.toSubgroup.map D.degree.toMonoidHom) ⧸
            (field.toSubgroup.map D.degree.toMonoidHom).subgroupOf
              (base.field.toSubgroup.map D.degree.toMonoidHom)) <
        Cardinal.aleph0
      exact Cardinal.lt_aleph0_of_finite _, by
      rw [D.residueDegreeCardinal_eq_mk_residueQuotient]
      exact Cardinal.lt_aleph0_of_finite _⟩)

end FiniteResidueAbstractField

/-- A finite extension whose base and field both carry their honest finite
absolute residue quotients.  The proof-dependent relative quotient is stored
once in the object and exposed through `toFiniteAbstractExtension`. -/
structure FiniteResidueAbstractExtension (D : DegreeData G) where
  /-- The top endpoint with its finite residue quotient. -/
  field : FiniteResidueAbstractField D
  /-- The base endpoint with its finite residue quotient. -/
  base : FiniteResidueAbstractField D
  /-- The top-field subgroup is contained in the base-field subgroup. -/
  below : field.field.toSubgroup ≤ base.field.toSubgroup
  /-- The relative extension quotient is finite. -/
  finiteQuotient :
    Finite
      (base.field.toSubgroup ⧸
        extensionSubgroup base.field field.field below)

namespace FiniteResidueAbstractExtension

variable {D : DegreeData G}

/-- Enrich a finite extension of a field with finite absolute residue quotient
with the corresponding honest residue data on its upper endpoint.  Finiteness
of the upper absolute residue quotient is deduced from the cardinal-valued
tower identity, which is the source of truth for arbitrary-index data. -/
noncomputable def ofInclusion (D : DegreeData G)
    (field : ClosedSubgroup G) (base : FiniteResidueAbstractField D)
    (below : field.toSubgroup ≤ base.field.toSubgroup)
    [finiteQuotient : Finite
      (base.field.toSubgroup ⧸
        extensionSubgroup base.field field below)] :
    FiniteResidueAbstractExtension D where
  field := {
    field := field
    finiteResidueQuotient := by
      apply Cardinal.lt_aleph0_iff_finite.mp
      rw [← D.residueDegreeCardinal_eq_mk_residueQuotient]
      let E : FiniteAbstractExtension G := {
        field := field
        base := base.field
        below := below
        finiteQuotient := finiteQuotient
      }
      rw [← E.toAbstractExtension.relativeResidueDegreeCardinal_mul_residueDegreeCardinal D]
      apply Cardinal.mul_lt_aleph0_iff.mpr
      exact Or.inr (Or.inr ⟨E.relativeResidueDegreeCardinal_lt_aleph0 D, by
        rw [D.residueDegreeCardinal_eq_mk_residueQuotient]
        exact Cardinal.lt_aleph0_of_finite (D.residueQuotient base.field)⟩) }
  base := base
  below := below
  finiteQuotient := finiteQuotient

/-- Forget only the endpoint residue-finiteness data. -/
def toFiniteAbstractExtension (E : FiniteResidueAbstractExtension D) :
    FiniteAbstractExtension G where
  field := E.field.field
  base := E.base.field
  below := E.below
  finiteQuotient := E.finiteQuotient

/-- A finite-residue extension supplies finiteness of its represented relative quotient. -/
instance (E : FiniteResidueAbstractExtension D) :
    Finite
      (E.base.field.toSubgroup ⧸
        extensionSubgroup E.base.field E.field.field E.below) :=
  E.finiteQuotient

/-- The positive relative degree. -/
noncomputable def degree (E : FiniteResidueAbstractExtension D) : ℕ+ :=
  E.toFiniteAbstractExtension.degree

/-- The positive relative residue degree. -/
noncomputable def residueDegree (E : FiniteResidueAbstractExtension D) : ℕ+ :=
  E.toFiniteAbstractExtension.residueDegree D

/-- The positive relative ramification index. -/
noncomputable def ramificationIndex
    (E : FiniteResidueAbstractExtension D) : ℕ+ :=
  E.toFiniteAbstractExtension.ramificationIndex D

/-- The residue-enriched extension degree agrees with the underlying finite-extension degree. -/
@[simp] theorem degree_coe (E : FiniteResidueAbstractExtension D) :
    (E.degree : ℕ) = (E.toFiniteAbstractExtension.degree : ℕ) :=
  rfl

/-- The residue-enriched residue degree agrees with the underlying finite-extension invariant. -/
@[simp] theorem residueDegree_coe (E : FiniteResidueAbstractExtension D) :
    (E.residueDegree : ℕ) =
      (E.toFiniteAbstractExtension.residueDegree D : ℕ) :=
  rfl

/-- The residue-enriched ramification index agrees with the underlying
finite-extension invariant. -/
@[simp] theorem ramificationIndex_coe
    (E : FiniteResidueAbstractExtension D) :
    (E.ramificationIndex : ℕ) =
      (E.toFiniteAbstractExtension.ramificationIndex D : ℕ) :=
  rfl

end FiniteResidueAbstractExtension

end DegreeData

/-! ## Fields finite over the distinguished base -/

/-- An abstract field finite over the distinguished base field. -/
structure FiniteAbstractField (G : Type u) [Group G] [TopologicalSpace G] where
  /-- The closed subgroup representing the abstract field. -/
  field : ClosedSubgroup G
  /-- The field has finite degree over the distinguished base. -/
  finite : Finite ((baseField G).toSubgroup ⧸
    extensionSubgroup (baseField G) field (le_baseField field))

namespace FiniteAbstractField

/-- A finite abstract field is determined by its underlying closed subgroup;
the finiteness component is proof-irrelevant. -/
theorem eq_of_field_eq (K L : FiniteAbstractField G)
    (h : K.field = L.field) : K = L := by
  cases K with
  | mk K hK =>
    cases L with
    | mk L hL =>
      cases h
      rfl

/-- The distinguished base field, bundled with its trivial finite quotient. -/
noncomputable def base (G : Type u) [Group G] [TopologicalSpace G] :
    FiniteAbstractField G where
  field := baseField G
  finite := by
    let : (extensionSubgroup (baseField G) (baseField G)
        (le_baseField (baseField G))).Normal := by
      rw [show extensionSubgroup (baseField G) (baseField G)
          (le_baseField (baseField G)) = ⊤ by
        ext x
        exact Iff.rfl]
      infer_instance
    let : Subsingleton
        ((baseField G).toSubgroup ⧸
          extensionSubgroup (baseField G) (baseField G)
            (le_baseField (baseField G))) := by
      constructor
      intro x y
      refine Quotient.inductionOn₂' x y ?_
      intro a b
      apply QuotientGroup.eq_iff_div_mem.mpr
      exact Subgroup.mem_top _
    infer_instance

/-- Regard a finite abstract field as its finite extension of the
distinguished base field. -/
def toFiniteAbstractExtension (K : FiniteAbstractField G) :
    DegreeData.FiniteAbstractExtension G where
  field := K.field
  base := baseField G
  below := le_baseField K.field
  finiteQuotient := K.finite

/-- A finite abstract field supplies finiteness of its quotient over the distinguished base. -/
instance (K : FiniteAbstractField G) :
    Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) K.field (le_baseField K.field)) :=
  K.finite

/-- A finite field over the distinguished base has a finite absolute residue
quotient.  This is derived from the finite relative quotient and the
surjectivity of the ambient degree map. -/
@[implicit_reducible]
noncomputable def toFiniteResidueAbstractField
    (K : FiniteAbstractField G) (D : DegreeData G) :
    DegreeData.FiniteResidueAbstractField D where
  field := K.field
  finiteResidueQuotient := by
    apply Cardinal.lt_aleph0_iff_finite.mp
    change
      intersectionIndexCardinal (D.fieldImage K.field)
        (⊤ : Subgroup ZHatMul) < Cardinal.aleph0
    rw [D.fieldImage_eq_map]
    have htop :
        (baseField G).toSubgroup.map D.degree.toMonoidHom = ⊤ := by
      rw [baseField_toSubgroup]
      exact Subgroup.map_top_of_surjective _ D.degree_surjective
    rw [← htop]
    simpa only [FiniteAbstractField.toFiniteAbstractExtension,
      DegreeData.AbstractExtension.relativeResidueDegreeCardinal, relativeIndexCardinal] using
      K.toFiniteAbstractExtension.relativeResidueDegreeCardinal_lt_aleph0 D

/-- The positive absolute residue degree of a field finite over the
distinguished base. -/
noncomputable def residueDegree (K : FiniteAbstractField G)
    (D : DegreeData G) : ℕ+ :=
  (K.toFiniteResidueAbstractField D).residueDegree

/-- Positive-natural specialization of the base-field residue degree. -/
@[simp] theorem base_residueDegree (D : DegreeData G) :
    (FiniteAbstractField.base G).residueDegree D = 1 := by
  apply Subtype.ext
  change (((FiniteAbstractField.base G).toFiniteResidueAbstractField D).residueDegree : ℕ) = 1
  apply Nat.cast_injective (R := Cardinal)
  rw [← DegreeData.FiniteResidueAbstractField.residueDegreeCardinal_eq_coe]
  exact D.residueDegreeCardinal_baseField

/-- The field residue degree is inherited from its finite-residue-field enrichment. -/
@[simp] theorem residueDegree_coe (K : FiniteAbstractField G)
    (D : DegreeData G) :
    (K.residueDegree D : ℕ) =
      ((K.toFiniteResidueAbstractField D).residueDegree : ℕ) :=
  rfl

end FiniteAbstractField

/-- A finite extension between two fields that are themselves finite over the
distinguished base.  Both endpoint finiteness proofs and the relative quotient
belong to the object. -/
structure FiniteAbstractFieldExtension (G : Type u)
    [Group G] [TopologicalSpace G] where
  /-- The top endpoint, finite over the distinguished base. -/
  field : FiniteAbstractField G
  /-- The base endpoint, finite over the distinguished base. -/
  base : FiniteAbstractField G
  /-- The top-field subgroup is contained in the base-field subgroup. -/
  below : field.field.toSubgroup ≤ base.field.toSubgroup
  /-- The relative extension quotient is finite. -/
  finiteQuotient :
    Finite
      (base.field.toSubgroup ⧸
        extensionSubgroup base.field field.field below)

namespace FiniteAbstractFieldExtension

/-- Canonically bundle a finite relative extension of a field already finite
over the distinguished base.  Finiteness of the upper field follows from the
actual quotient tower. -/
@[implicit_reducible]
noncomputable def ofInclusion (field : ClosedSubgroup G)
    (base : FiniteAbstractField G)
    (below : field.toSubgroup ≤ base.field.toSubgroup)
    [finiteQuotient : Finite
      (base.field.toSubgroup ⧸
        extensionSubgroup base.field field below)] :
    FiniteAbstractFieldExtension G where
  field := {
    field := field
    finite := by
      apply Cardinal.lt_aleph0_iff_finite.mp
      let T : DegreeData.AbstractExtension.Tower G := {
        top := field
        middle := base.field
        base := baseField G
        top_le_middle := below
        middle_le_base := le_baseField base.field }
      change T.totalExtension.degreeCardinal < Cardinal.aleph0
      rw [← T.degreeCardinal_mul]
      apply Cardinal.mul_lt_aleph0
      · change Cardinal.mk
          (base.field.toSubgroup ⧸
            extensionSubgroup base.field field below) < Cardinal.aleph0
        exact Cardinal.lt_aleph0_of_finite _
      · change Cardinal.mk
          ((baseField G).toSubgroup ⧸
            extensionSubgroup (baseField G) base.field
              (le_baseField base.field)) < Cardinal.aleph0
        exact Cardinal.lt_aleph0_of_finite _ }
  base := base
  below := below
  finiteQuotient := finiteQuotient

/-- Forget endpoint finiteness over the distinguished base. -/
@[implicit_reducible]
def toFiniteAbstractExtension (E : FiniteAbstractFieldExtension G) :
    DegreeData.FiniteAbstractExtension G where
  field := E.field.field
  base := E.base.field
  below := E.below
  finiteQuotient := E.finiteQuotient

/-- Structural unramifiedness of the represented relative extension. -/
@[implicit_reducible]
def IsUnramified (E : FiniteAbstractFieldExtension G) (D : DegreeData G) : Prop :=
  E.toFiniteAbstractExtension.IsUnramified D

/-- Structural total ramification of the represented relative extension. -/
def IsTotallyRamified (E : FiniteAbstractFieldExtension G)
    (D : DegreeData G) : Prop :=
  E.toFiniteAbstractExtension.IsTotallyRamified D

/-- The positive relative degree. -/
noncomputable def degree (E : FiniteAbstractFieldExtension G) : ℕ+ :=
  E.toFiniteAbstractExtension.degree

/-- The positive relative residue degree. -/
noncomputable def residueDegree (E : FiniteAbstractFieldExtension G)
    (D : DegreeData G) : ℕ+ :=
  E.toFiniteAbstractExtension.residueDegree D

/-- The positive relative ramification index. -/
noncomputable def ramificationIndex (E : FiniteAbstractFieldExtension G)
    (D : DegreeData G) : ℕ+ :=
  E.toFiniteAbstractExtension.ramificationIndex D

/-- In an unramified finite field extension, the positive relative residue
degree is the positive extension degree. -/
theorem residueDegree_eq_degree_of_isUnramified
    (E : FiniteAbstractFieldExtension G) (D : DegreeData G)
    (hE : E.IsUnramified D) :
    (E.residueDegree D : ℕ) = (E.degree : ℕ) :=
  E.toFiniteAbstractExtension.residueDegree_eq_degree_of_isUnramified D hE

/-- A finite abstract field extension supplies finiteness of its relative quotient. -/
instance (E : FiniteAbstractFieldExtension G) :
    Finite
      (E.base.field.toSubgroup ⧸
        extensionSubgroup E.base.field E.field.field E.below) :=
  E.finiteQuotient

/-- Canonically enrich both endpoints with their finite residue quotients. -/
noncomputable def toFiniteResidueAbstractExtension
    (E : FiniteAbstractFieldExtension G) (D : DegreeData G) :
    DegreeData.FiniteResidueAbstractExtension D where
  field := E.field.toFiniteResidueAbstractField D
  base := E.base.toFiniteResidueAbstractField D
  below := E.below
  finiteQuotient := E.finiteQuotient

end FiniteAbstractFieldExtension

end
end ClassFormation
