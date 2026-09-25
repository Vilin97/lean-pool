/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.NumberField.EverywhereUnramifiedTower
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianClassification
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassFormation
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.FiniteAbelianClassFieldCorrespondence
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertNormCharacterization
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.SmallHilbertClassFieldNaturality
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.PrincipalIdealTower
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicIdeleClassValuation
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitNormQuotient
/-!
# Conjugation of the small Hilbert class-field tower

For a finite abelian tower, conjugation by the lower base carries the
relative norm subgroup of the upper extension to the relative norm subgroup
of the conjugate extension.  In the rational absolute idele-class formation,
the subgroup defining the small Hilbert class field is intrinsic under the
corresponding automorphism of its actual fixed field.  Finite abelian
classification therefore identifies every conjugate of the second small
Hilbert class field with the original field.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open ClassFormation KummerTheory
open GlobalClassFields LocalClassFieldTheory Reciprocity

private theorem addSubgroup_map_map_eq_of_comp_eq
    {A B C : Type*} [AddGroup A] [AddGroup B] [AddGroup C]
    (S : AddSubgroup A) (f : A →+ B) (g : B →+ C) (h : A →+ C)
    (hcomp : g.comp f = h) :
    (S.map f).map g = S.map h := by
  rw [AddSubgroup.map_map, hcomp]

private theorem addSubgroup_map_addEquiv_then_symm
    {A B : Type*} [AddGroup A] [AddGroup B]
    (S : AddSubgroup A) (e : A ≃+ B) :
    (S.map e.toAddMonoidHom).map e.symm.toAddMonoidHom = S := by
  have hcomp :
      e.symm.toAddMonoidHom.comp e.toAddMonoidHom =
        AddMonoidHom.id A := by
    apply AddMonoidHom.ext
    intro a
    exact e.symm_apply_apply a
  calc
    (S.map e.toAddMonoidHom).map e.symm.toAddMonoidHom =
        S.map (AddMonoidHom.id A) :=
      addSubgroup_map_map_eq_of_comp_eq
        S e.toAddMonoidHom e.symm.toAddMonoidHom
          (AddMonoidHom.id A) hcomp
    _ = S := AddSubgroup.map_id S

private theorem addSubgroup_map_le_of_le_map_symm
    {A B : Type*} [AddGroup A] [AddGroup B]
    (H : AddSubgroup A) (N : AddSubgroup B) (e : A ≃+ B)
    (h : H ≤ N.map e.symm.toAddMonoidHom) :
    H.map e.toAddMonoidHom ≤ N := by
  rintro _ ⟨a, ha, rfl⟩
  have haBack :
      e.symm (e a) ∈ N.map e.symm.toAddMonoidHom := by
    simpa only [e.symm_apply_apply] using h ha
  obtain ⟨b, hb, hba⟩ := haBack
  have hb_eq : b = e a := e.symm.injective hba
  rw [hb_eq] at hb
  change e a ∈ N
  exact hb

private theorem addSubgroup_map_eq_of_comp_eq_of_map_eq
    {A B : Type*} [AddGroup A] [AddGroup B]
    (S : AddSubgroup A) (e : A →+ B) (g : A →+ A) (t : B →+ B)
    (hcomp : t.comp e = e.comp g) (hg : S.map g = S) :
    (S.map e).map t = S.map e := by
  calc
    (S.map e).map t = S.map (e.comp g) :=
      addSubgroup_map_map_eq_of_comp_eq S e t (e.comp g) hcomp
    _ = (S.map g).map e :=
      (addSubgroup_map_map_eq_of_comp_eq S g e (e.comp g) rfl).symm
    _ = S.map e := congrArg (fun H => H.map e) hg

private theorem subgroup_toAddSubgroup_map_toAdditive_eq_self
    {G : Type*} [Group G]
    (S : Subgroup G) (f : G →* G) (hf : S.map f = S) :
    S.toAddSubgroup.map (MonoidHom.toAdditive f) =
      S.toAddSubgroup := by
  simpa only [MonoidHom.coe_toAdditive_map] using
    congrArg Subgroup.toAddSubgroup hf

section AbstractConjugation

variable
    {G : IntegralRepGroupType}
    [Group G] [TopologicalSpace G] [ContinuousMul G]

/-- A finite Galois field in an abelian tower is stable under conjugation
by every element of its base subgroup. -/
theorem conjugateFiniteAbelianSubextensionField_eq_self
    {K : ClosedSubgroup G}
    (L : FiniteAbelianSubextension K)
    (s : K.toSubgroup) :
    conjugateClosedSubgroup L.field s.1 = L.field := by
  ext x
  constructor
  · intro hx
    have hx' : s.1 * x * s.1⁻¹ ∈ L.field :=
      (conjugateClosedSubgroup_mem L.field s.1 x).1 hx
    let y : L.field.toSubgroup :=
      ⟨s.1 * x * s.1⁻¹, hx'⟩
    let yK : K.toSubgroup :=
      Subgroup.inclusion L.below y
    have hy :
        s⁻¹ * yK * s ∈
          CyclicCohomology.extensionSubgroup K L.field L.below := by
      simpa only [inv_inv] using
        L.normal.conj_mem yK
          ((mem_extensionSubgroup_iff
            K L.field L.below yK).2 y.2) s⁻¹
    have hyL :
        ((s⁻¹ * yK * s : K.toSubgroup) : G) ∈
          L.field.toSubgroup :=
      (mem_extensionSubgroup_iff K L.field L.below
        (s⁻¹ * yK * s)).1 hy
    change x ∈ L.field.toSubgroup
    simpa [y, yK, mul_assoc] using hyL
  · intro hx
    let xK : K.toSubgroup :=
      ⟨x, L.below hx⟩
    have hxConj :
        s * xK * s⁻¹ ∈
          CyclicCohomology.extensionSubgroup K L.field L.below := by
      exact
        L.normal.conj_mem xK
          ((mem_extensionSubgroup_iff
            K L.field L.below xK).2 hx) s
    apply (conjugateClosedSubgroup_mem L.field s.1 x).2
    simpa [xK] using
      (mem_extensionSubgroup_iff K L.field L.below
        (s * xK * s⁻¹)).1 hxConj

/-- Conjugation gives an additive equivalence between the two actual fixed
parts of a coefficient representation. -/
private noncomputable def conjugateFixedAddEquiv
    (A : Rep ℤ G) (K : ClosedSubgroup G) (s : G) :
    ambientFixedAddSubgroup A K ≃+
      ambientFixedAddSubgroup A (conjugateClosedSubgroup K s) where
  toFun := conjugateFixedElement A K s
  invFun := fun b => by
    refine ⟨A.ρ s b.1, ?_⟩
    intro k
    let kConj :
        (conjugateClosedSubgroup K s).toSubgroup :=
      ⟨s⁻¹ * k.1 * s,
        (conjugateClosedSubgroup_mem K s _).2 (by
          simp [mul_assoc])⟩
    calc
      A.ρ k.1 (A.ρ s b.1) =
          A.ρ (k.1 * s) b.1 := by
            exact congrArg (fun φ => φ b.1)
              (map_mul A.ρ k.1 s).symm
      _ = A.ρ (s * kConj.1) b.1 := by
            congr 2
            simp [kConj, mul_assoc]
      _ = A.ρ s (A.ρ kConj.1 b.1) := by
            exact congrArg (fun φ => φ b.1)
              (map_mul A.ρ s kConj.1)
      _ = A.ρ s b.1 := by rw [b.2 kConj]
  left_inv := by
    intro a
    apply Subtype.ext
    change A.ρ s (A.ρ s⁻¹ a.1) = a.1
    calc
      A.ρ s (A.ρ s⁻¹ a.1) =
          A.ρ (s * s⁻¹) a.1 := by
            exact congrArg (fun φ => φ a.1)
              (map_mul A.ρ s s⁻¹).symm
      _ = a.1 := by simp
  right_inv := by
    intro b
    apply Subtype.ext
    change A.ρ s⁻¹ (A.ρ s b.1) = b.1
    calc
      A.ρ s⁻¹ (A.ρ s b.1) =
          A.ρ (s⁻¹ * s) b.1 := by
            exact congrArg (fun φ => φ b.1)
              (map_mul A.ρ s⁻¹ s).symm
      _ = b.1 := by simp
  map_add' := by
    intro a b
    apply Subtype.ext
    exact map_add (A.ρ s⁻¹) a.1 b.1

/-- Relative norm images are carried exactly to the norm images of the
conjugate extension. -/
theorem finiteNormSubgroup_map_conjugateFixed
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (s : G)
    [Finite
      (K.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup K L hLK)] :
    letI : Finite
        ((conjugateClosedSubgroup K s).toSubgroup ⧸
          CyclicCohomology.extensionSubgroup
            (conjugateClosedSubgroup K s)
            (conjugateClosedSubgroup L s)
            (conjugateClosedSubgroup_mono hLK s)) :=
      finite_conjugateExtension K L hLK s
    (finiteNormSubgroup A K L hLK).map
        (conjugateFixedElementHom A K s) =
      finiteNormSubgroup A
        (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s) := by
  let : Finite
      ((conjugateClosedSubgroup K s).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup L s)
          (conjugateClosedSubgroup_mono hLK s)) :=
    finite_conjugateExtension K L hLK s
  ext y
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    refine ⟨conjugateFixedElement A L s a, ?_⟩
    exact relativeNorm_conjugate_apply A K L hLK s a
  · rintro ⟨b, rfl⟩
    let a :=
      (conjugateFixedAddEquiv A L s).symm b
    refine
      ⟨relativeNorm A K L hLK a, ⟨a, rfl⟩, ?_⟩
    change
      conjugateFixedElement A K s
          (relativeNorm A K L hLK a) =
        relativeNorm A
          (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup L s)
          (conjugateClosedSubgroup_mono hLK s) b
    calc
      conjugateFixedElement A K s
          (relativeNorm A K L hLK a) =
          relativeNorm A
            (conjugateClosedSubgroup K s)
            (conjugateClosedSubgroup L s)
            (conjugateClosedSubgroup_mono hLK s)
            (conjugateFixedElement A L s a) :=
        (relativeNorm_conjugate_apply
          A K L hLK s a).symm
      _ =
          relativeNorm A
            (conjugateClosedSubgroup K s)
            (conjugateClosedSubgroup L s)
            (conjugateClosedSubgroup_mono hLK s) b := by
        rw [show conjugateFixedElement A L s a = b by
          exact
            (conjugateFixedAddEquiv A L s).apply_symm_apply b]

private noncomputable def rebaseFiniteAbelianSubextension
    {K K' : ClosedSubgroup G} (h : K = K')
    (L : FiniteAbelianSubextension K) :
    FiniteAbelianSubextension K' :=
  h ▸ L

omit [ContinuousMul G] in
@[simp]
private theorem rebaseFiniteAbelianSubextension_field
    {K K' : ClosedSubgroup G} (h : K = K')
    (L : FiniteAbelianSubextension K) :
    (rebaseFiniteAbelianSubextension h L).field = L.field := by
  cases h
  rfl

private noncomputable def rebaseFixedCodomainHom
    (A : Rep ℤ G)
    {X : Type*} [AddGroup X]
    {K K' : ClosedSubgroup G} (h : K = K')
    (f : X →+ ambientFixedAddSubgroup A K) :
    X →+
      ambientFixedAddSubgroup A K' := by
  cases h
  exact f

omit [ContinuousMul G] in
@[simp]
private theorem rebaseFixedCodomainHom_coe
    (A : Rep ℤ G)
    {X : Type*} [AddGroup X]
    {K K' : ClosedSubgroup G} (h : K = K')
    (f : X →+ ambientFixedAddSubgroup A K)
    (a : X) :
    ((rebaseFixedCodomainHom A h f a :
      ambientFixedAddSubgroup A K') : A.V) =
      (f a : A.V) := by
  cases h
  rfl

private noncomputable def rebaseFixedAddSubgroup
    (A : Rep ℤ G) {K K' : ClosedSubgroup G}
    (h : K = K')
    (H : AddSubgroup (ambientFixedAddSubgroup A K)) :
    AddSubgroup (ambientFixedAddSubgroup A K') := by
  cases h
  exact H

omit [ContinuousMul G] in
private theorem rebaseFixedAddSubgroup_map
    (A : Rep ℤ G) {K K' : ClosedSubgroup G}
    (h : K = K')
    {X : Type*} [AddGroup X] (H : AddSubgroup X)
    (f : X →+ ambientFixedAddSubgroup A K) :
    rebaseFixedAddSubgroup A h (H.map f) =
      H.map (rebaseFixedCodomainHom A h f) := by
  cases h
  rfl

omit [ContinuousMul G] in
private theorem rebaseFiniteAbelianSubextension_normSubgroup
    (A : Rep ℤ G) {K K' : ClosedSubgroup G}
    (h : K = K') (L : FiniteAbelianSubextension K) :
    (rebaseFiniteAbelianSubextension h L).normSubgroup A =
      rebaseFixedAddSubgroup A h (L.normSubgroup A) := by
  cases h
  rfl

/-- Conjugation of the upper extension, transported back across the
conjugation-stability equality of its abelian base. -/
noncomputable def conjugateFiniteAbelianSubextensionOverBase
    {K : ClosedSubgroup G}
    (L : FiniteAbelianSubextension K)
    (M : FiniteAbelianSubextension L.field)
    (s : K.toSubgroup) :
    FiniteAbelianSubextension L.field :=
  rebaseFiniteAbelianSubextension
    (conjugateFiniteAbelianSubextensionField_eq_self L s)
    (conjugateFiniteAbelianSubextension M s.1)

@[simp]
theorem conjugateFiniteAbelianSubextensionOverBase_field
    {K : ClosedSubgroup G}
    (L : FiniteAbelianSubextension K)
    (M : FiniteAbelianSubextension L.field)
    (s : K.toSubgroup) :
    (conjugateFiniteAbelianSubextensionOverBase L M s).field =
      conjugateClosedSubgroup M.field s.1 :=
  by
    simp only [
      conjugateFiniteAbelianSubextensionOverBase,
      rebaseFiniteAbelianSubextension_field,
      conjugateFiniteAbelianSubextension_field]

/-- The canonical conjugation map on the fixed part, transported along
the conjugation-stability equality of the abelian base. -/
noncomputable def stableBaseConjugationHom
    (A : Rep ℤ G)
    {K : ClosedSubgroup G}
    (L : FiniteAbelianSubextension K)
    (s : K.toSubgroup) :
    ambientFixedAddSubgroup A L.field →+
      ambientFixedAddSubgroup A L.field :=
  rebaseFixedCodomainHom A
    (conjugateFiniteAbelianSubextensionField_eq_self L s)
    (conjugateFixedElementHom A L.field s.1)

@[simp]
theorem stableBaseConjugationHom_coe
    (A : Rep ℤ G)
    {K : ClosedSubgroup G}
    (L : FiniteAbelianSubextension K)
    (s : K.toSubgroup)
    (a : ambientFixedAddSubgroup A L.field) :
    ((stableBaseConjugationHom A L s a :
      ambientFixedAddSubgroup A L.field) : A.V) =
      A.ρ s.1⁻¹ a.1 := by
  calc
    ((stableBaseConjugationHom A L s a :
      ambientFixedAddSubgroup A L.field) : A.V) =
        ((conjugateFixedElementHom A L.field s.1 a :
          ambientFixedAddSubgroup A
            (conjugateClosedSubgroup L.field s.1)) : A.V) := by
      exact rebaseFixedCodomainHom_coe A
        (conjugateFiniteAbelianSubextensionField_eq_self L s)
        (conjugateFixedElementHom A L.field s.1) a
    _ = A.ρ s.1⁻¹ a.1 :=
      conjugateFixedElement_coe A L.field s.1 a

/-- The norm subgroup of the conjugate upper extension is the image of
the original norm subgroup under the actual action on the fixed part of
the stable base. -/
theorem conjugateFiniteAbelianSubextensionOverBase_normSubgroup
    (A : Rep ℤ G)
    {K : ClosedSubgroup G}
    (L : FiniteAbelianSubextension K)
    (M : FiniteAbelianSubextension L.field)
    (s : K.toSubgroup) :
    (conjugateFiniteAbelianSubextensionOverBase L M s).normSubgroup A =
      (M.normSubgroup A).map
        (stableBaseConjugationHom A L s) := by
  let : Finite
      (L.field.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          L.field M.field M.below) :=
    M.finite
  let h :=
    conjugateFiniteAbelianSubextensionField_eq_self L s
  let C := conjugateFiniteAbelianSubextension M s.1
  have hnorm :=
    finiteNormSubgroup_map_conjugateFixed
      A L.field M.field M.below s.1
  have hC :
      C.normSubgroup A =
        (M.normSubgroup A).map
          (conjugateFixedElementHom A L.field s.1) := by
    simpa only [
      C, FiniteAbelianSubextension.normSubgroup,
      conjugateFiniteAbelianSubextension_field] using hnorm.symm
  calc
    (conjugateFiniteAbelianSubextensionOverBase L M s).normSubgroup A =
        rebaseFixedAddSubgroup A h (C.normSubgroup A) := by
      exact rebaseFiniteAbelianSubextension_normSubgroup A h C
    _ = rebaseFixedAddSubgroup A h
        ((M.normSubgroup A).map
          (conjugateFixedElementHom A L.field s.1)) :=
      congrArg (rebaseFixedAddSubgroup A h) hC
    _ = (M.normSubgroup A).map
        (stableBaseConjugationHom A L s) := by
      exact rebaseFixedAddSubgroup_map A h
        (M.normSubgroup A)
        (conjugateFixedElementHom A L.field s.1)

end AbstractConjugation

section RationalSmallHilbert

local instance smallHilbertTowerBaseQuotientFinite
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K.field (le_baseField K.field)) :=
  K.finite

local instance smallHilbertTowerRelativeQuotientFinite
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    Finite
      (K.field.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          K.field L.field L.below) :=
  L.finite

noncomputable local instance smallHilbertTowerBaseFiniteDimensional
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field) :=
  abstractFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ) K.field K.finite

noncomputable local instance smallHilbertTowerRelativeFiniteDimensional
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    FiniteDimensional
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  abstractRelativeFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ)
    K.field L.field L.below K.finite L.finite

local instance smallHilbertTowerScalarTower
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    IsScalarTower ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

noncomputable local instance smallHilbertTowerAbsoluteFiniteDimensional
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    FiniteDimensional ℚ
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  FiniteDimensional.trans ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
    (abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) L.below)

noncomputable local instance smallHilbertTowerBaseNumberField
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    NumberField
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field) :=
  NumberField.of_module_finite ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ) K.field)

noncomputable local instance smallHilbertTowerRelativeNumberField
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    NumberField
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  NumberField.of_module_finite ℚ
    (abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) L.below)

noncomputable local instance smallHilbertTowerRelativeIsGalois
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    IsGalois
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
      (abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :=
  abstractRelativeFixedField_isGalois
    ℚ (SeparableClosure ℚ)
    K.field L.field L.below L.normal

/-- The ordinary small-Hilbert norm subgroup of an actual fixed field,
transported into the fixed part of the rational absolute idele-class
representation. -/
noncomputable def smallHilbertNormSubgroupInRationalClassFormation
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    AddSubgroup
      (ambientFixedAddSubgroup
        rationalIdeleClassRepresentation K.field) :=
  (smallHilbertClassFieldNormSubgroup
    (K := abstractFixedField
      ℚ (SeparableClosure ℚ) K.field)).toAddSubgroup.map
      (rationalAbstractFixedFieldIdeleClassEquivFixed
        K.field).toAddMonoidHom

private theorem finiteAbelianNormSubgroup_map_fixedIdeleClassEquiv_symm
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    (L.normSubgroup rationalIdeleClassRepresentation).map
        (rationalAbstractFixedFieldIdeleClassEquivFixed
          K.field).symm.toAddMonoidHom =
      (_root_.ideleClassNorm
        (abstractFixedField
          ℚ (SeparableClosure ℚ) K.field)
        (abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) L.below)).range.toAddSubgroup := by
  simpa only [ordinaryIdeleClassNormSubgroup] using
    (ordinaryIdeleClassNormSubgroup_eq_actualNormRange K L)

private theorem
    smallHilbertNormSubgroupInRationalClassFormation_le_normSubgroup_of_fixedFieldNormRange
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field)
    (hordinary :
      smallHilbertClassFieldNormSubgroup
          (K := abstractFixedField
            ℚ (SeparableClosure ℚ) K.field) ≤
        (_root_.ideleClassNorm
          (abstractFixedField
            ℚ (SeparableClosure ℚ) K.field)
          (abstractRelativeFixedField
            ℚ (SeparableClosure ℚ) L.below)).range) :
    smallHilbertNormSubgroupInRationalClassFormation K ≤
      L.normSubgroup rationalIdeleClassRepresentation := by
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) K.field
  let e :=
    rationalAbstractFixedFieldIdeleClassEquivFixed K.field
  let H :=
    (smallHilbertClassFieldNormSubgroup
      (K := F)).toAddSubgroup
  change H.map e.toAddMonoidHom ≤
      L.normSubgroup rationalIdeleClassRepresentation
  apply
    addSubgroup_map_le_of_le_map_symm
      H (L.normSubgroup rationalIdeleClassRepresentation) e
  rw [finiteAbelianNormSubgroup_map_fixedIdeleClassEquiv_symm K L]
  exact fun c hc => hordinary hc

/-- Maximality of the intrinsic small-Hilbert norm subgroup, transported
from the actual fixed-field extension back into the rational absolute
class formation.  For an extension unramified at every finite and
infinite place, the canonical small-Hilbert subgroup is contained in
its genuine abstract norm subgroup. -/
theorem
    smallHilbertNormSubgroupInRationalClassFormation_le_normSubgroup_of_everywhereUnramified
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    IsUnramifiedAtInfinitePlaces
        (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
        (abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) L.below) →
      _root_.ramifiedBaseFinitePlaces
          (K := abstractFixedField
            ℚ (SeparableClosure ℚ) K.field)
          (L := abstractRelativeFixedField
            ℚ (SeparableClosure ℚ) L.below) = ∅ →
        smallHilbertNormSubgroupInRationalClassFormation K ≤
          L.normSubgroup rationalIdeleClassRepresentation := by
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) K.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) L.below
  intro hunramifiedInfinite hunramifiedFinite
  let : IsUnramifiedAtInfinitePlaces F E :=
    hunramifiedInfinite
  have hordinary :
      smallHilbertClassFieldNormSubgroup (K := F) ≤
        (_root_.ideleClassNorm F E).range :=
    smallHilbertClassFieldNormSubgroup_le_ideleClassNorm_range_of_everywhereUnramified
      (K := F) (L := E) hunramifiedFinite
  exact
    smallHilbertNormSubgroupInRationalClassFormation_le_normSubgroup_of_fixedFieldNormRange
      K L hordinary

/-- Every finite abelian extension of the same actual base which is
unramified at all finite and infinite places lies in any realization of
the small Hilbert class field.  The conclusion is a field-order statement:
it follows from the genuine fixed-field norm comparison and the
order-reversing finite abelian classification. -/
theorem everywhereUnramifiedFiniteAbelianSubextension_le_smallHilbertClassField
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L P : FiniteAbelianSubextension K.field)
    (hL :
      L.normSubgroup rationalIdeleClassRepresentation =
        smallHilbertNormSubgroupInRationalClassFormation K) :
    IsEverywhereUnramified
        (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
        (abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) P.below) →
      P ≤ L := by
  classical
  have hclassification :=
    FiniteAbelianSubextension.le_iff_normSubgroup_le
      rationalCyclotomicIdeleClassValuationData
      rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
      K P L
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) K.field
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  intro hunramified
  apply hclassification.2
  have hsmall :=
    smallHilbertNormSubgroupInRationalClassFormation_le_normSubgroup_of_everywhereUnramified
      K P hunramified.infinitePlaces (by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro v hv
        rw [_root_.mem_ramifiedBaseFinitePlaces_iff] at hv
        obtain ⟨Q, _hQ, hQramified⟩ := hv
        exact hQramified (hunramified.finitePlaces Q))
  intro c hc
  exact hsmall (hL ▸ hc)

/-- The automorphism of the actual upper fixed field induced by the inverse
of an element of the lower base subgroup.  The inverse is the one appearing
in right conjugation and in `conjugateFixedElement`. -/
noncomputable def smallHilbertBaseConjugationAutomorphism
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field)
    (s : K.field.toSubgroup) :
    let E :=
      abstractFixedField ℚ (SeparableClosure ℚ) L.field
    E ≃ₐ[ℚ] E :=
  letI :
      (CyclicCohomology.extensionSubgroup
        K.field L.field L.below).Normal :=
    L.normal
  (abstractExtensionQuotientEquivGaloisGroup
    ℚ (SeparableClosure ℚ)
    K.field L.field L.below L.normal
    (QuotientGroup.mk'
      (CyclicCohomology.extensionSubgroup
        K.field L.field L.below)
      s⁻¹)).restrictScalars ℚ

/-- The fixed-field automorphism used for stable conjugation is induced by
the inverse ambient automorphism on underlying separable-closure elements. -/
private theorem smallHilbertBaseConjugationAutomorphism_apply_val
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field)
    (s : K.field.toSubgroup)
    (x : abstractFixedField ℚ (SeparableClosure ℚ) L.field) :
    ((smallHilbertBaseConjugationAutomorphism K L s x :
        abstractFixedField ℚ (SeparableClosure ℚ) L.field) :
      SeparableClosure ℚ) =
      s.1⁻¹ (x : SeparableClosure ℚ) := by
  let :
      (CyclicCohomology.extensionSubgroup
        K.field L.field L.below).Normal :=
    L.normal
  change
    (((abstractExtensionQuotientEquivGaloisGroup
        ℚ (SeparableClosure ℚ)
        K.field L.field L.below L.normal
        (QuotientGroup.mk'
          (CyclicCohomology.extensionSubgroup
            K.field L.field L.below)
          s⁻¹)) x :
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) L.below) :
      SeparableClosure ℚ) =
        s.1⁻¹ (x : SeparableClosure ℚ)
  exact
    (abstractExtensionQuotientEquivGaloisGroup_mk_apply_val
      ℚ (SeparableClosure ℚ)
      K.field L.field L.below L.normal s⁻¹ x).symm

/-- On the actual fixed part of the rational idele-class formation,
conjugation by an element of the lower base is ordinary idele-class
transport along the induced automorphism of the upper fixed field. -/
theorem rationalSmallHilbertFixedPart_conjugation
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field)
    (s : K.field.toSubgroup) :
    let E :=
      abstractFixedField ℚ (SeparableClosure ℚ) L.field
    letI hLfinite : Finite
        ((baseField
          (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
          CyclicCohomology.extensionSubgroup
            (baseField
              (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
            L.field (le_baseField L.field)) :=
      (L.toFiniteGaloisExtension.toFiniteAbstractFieldExtension).field.finite
    letI : FiniteDimensional ℚ E :=
      abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) L.field hLfinite
    letI : NumberField E :=
      NumberField.of_module_finite ℚ E
    ∀ c : Additive (IdeleClassGroup E),
    stableBaseConjugationHom
        rationalIdeleClassRepresentation L s
        (rationalAbstractFixedFieldIdeleClassEquivFixed
          L.field c) =
      rationalAbstractFixedFieldIdeleClassEquivFixed
        L.field
        (Additive.ofMul
          (ideleClassCongr
            (smallHilbertBaseConjugationAutomorphism K L s)
            (Additive.toMul c))) := by
  dsimp only
  let E :=
    abstractFixedField ℚ (SeparableClosure ℚ) L.field
  let hLfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          L.field (le_baseField L.field)) :=
    (L.toFiniteGaloisExtension.toFiniteAbstractFieldExtension).field.finite
  let : FiniteDimensional ℚ E :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) L.field hLfinite
  let : NumberField E :=
    NumberField.of_module_finite ℚ E
  intro c
  let τ : E ≃ₐ[ℚ] E :=
    smallHilbertBaseConjugationAutomorphism K L s
  have hστ : ∀ x : E,
      ((τ x : E) : SeparableClosure ℚ) =
        s.1⁻¹ (x : SeparableClosure ℚ) := by
    intro x
    exact smallHilbertBaseConjugationAutomorphism_apply_val K L s x
  let cτ : Additive (IdeleClassGroup E) :=
    Additive.ofMul
      (ideleClassCongr τ (Additive.toMul c))
  have haction :
      rationalIdeleClassRepresentation.ρ s.1⁻¹
          (rationalIdeleClassEquivFixed E c).1 =
        (rationalIdeleClassEquivFixed E cτ).1 := by
    simpa only [cτ, ofMul_toMul] using
      (rationalIdeleClassEquivFixed_ambientAlgEquiv
        s.1⁻¹ τ hστ (Additive.toMul c))
  have hstable
      (a : ambientFixedAddSubgroup
        rationalIdeleClassRepresentation L.field) :
      ((stableBaseConjugationHom
          rationalIdeleClassRepresentation L s a :
        ambientFixedAddSubgroup
          rationalIdeleClassRepresentation L.field) :
      rationalIdeleClassRepresentation.V) =
      rationalIdeleClassRepresentation.ρ s.1⁻¹ a.1 := by
    exact stableBaseConjugationHom_coe
      rationalIdeleClassRepresentation L s a
  have hcoe (z : Additive (IdeleClassGroup E)) :
      (rationalAbstractFixedFieldIdeleClassEquivFixed L.field
          (hfinite := hLfinite) z).1 =
        (rationalIdeleClassEquivFixed E z).1 :=
    rationalAbstractFixedFieldIdeleClassEquivFixed_coe
      L.field (hfinite := hLfinite) z
  apply Subtype.ext
  exact
    (hstable
      (rationalAbstractFixedFieldIdeleClassEquivFixed
        L.field (hfinite := hLfinite) c)).trans
      ((congrArg (rationalIdeleClassRepresentation.ρ s.1⁻¹)
        (hcoe c)).trans
        (haction.trans (hcoe cτ).symm))

private theorem
    smallHilbertClassFieldNormSubgroup_toAddSubgroup_map_ideleClassCongr
    (E : Type*) [Field E] [NumberField E]
    (τ : E ≃ₐ[ℚ] E) :
    (smallHilbertClassFieldNormSubgroup
        (K := E)).toAddSubgroup.map
          (MonoidHom.toAdditive
            (ideleClassCongr τ).toMonoidHom) =
      (smallHilbertClassFieldNormSubgroup
        (K := E)).toAddSubgroup := by
  exact
    subgroup_toAddSubgroup_map_toAdditive_eq_self
      (smallHilbertClassFieldNormSubgroup (K := E))
      (ideleClassCongr τ).toMonoidHom
      (smallHilbertClassFieldNormSubgroup_map_ideleClassCongr τ)

private theorem rationalSmallHilbertFixedPart_conjugation_comp
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field)
    (s : K.field.toSubgroup) :
    let E :=
      abstractFixedField ℚ (SeparableClosure ℚ) L.field
    letI hLfinite : Finite
        ((baseField
          (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
          CyclicCohomology.extensionSubgroup
            (baseField
              (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
            L.field (le_baseField L.field)) :=
      (L.toFiniteGaloisExtension.toFiniteAbstractFieldExtension).field.finite
    letI : FiniteDimensional ℚ E :=
      abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) L.field hLfinite
    letI : NumberField E :=
      NumberField.of_module_finite ℚ E
    (stableBaseConjugationHom
        rationalIdeleClassRepresentation L s).comp
        (rationalAbstractFixedFieldIdeleClassEquivFixed
          L.field).toAddMonoidHom =
      (rationalAbstractFixedFieldIdeleClassEquivFixed
        L.field).toAddMonoidHom.comp
        (MonoidHom.toAdditive
          (ideleClassCongr
            (smallHilbertBaseConjugationAutomorphism K L s)).toMonoidHom) := by
  dsimp only
  let E :=
    abstractFixedField ℚ (SeparableClosure ℚ) L.field
  let hLfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          L.field (le_baseField L.field)) :=
    (L.toFiniteGaloisExtension.toFiniteAbstractFieldExtension).field.finite
  let : FiniteDimensional ℚ E :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) L.field hLfinite
  let : NumberField E :=
    NumberField.of_module_finite ℚ E
  apply AddMonoidHom.ext
  intro c
  change
    stableBaseConjugationHom
        rationalIdeleClassRepresentation L s
        (rationalAbstractFixedFieldIdeleClassEquivFixed L.field c) =
      rationalAbstractFixedFieldIdeleClassEquivFixed L.field
        (Additive.ofMul
          (ideleClassCongr
            (smallHilbertBaseConjugationAutomorphism K L s)
            (Additive.toMul c)))
  exact rationalSmallHilbertFixedPart_conjugation K L s c

private theorem
    smallHilbertNormSubgroupInRationalClassFormation_map_conjugation_canonical
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field)
    (s : K.field.toSubgroup) :
    let E :=
      abstractFixedField ℚ (SeparableClosure ℚ) L.field
    letI hLfinite : Finite
        ((baseField
          (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
          CyclicCohomology.extensionSubgroup
            (baseField
              (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
            L.field (le_baseField L.field)) :=
      (L.toFiniteGaloisExtension.toFiniteAbstractFieldExtension).field.finite
    letI : FiniteDimensional ℚ E :=
      abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) L.field hLfinite
    letI : NumberField E :=
      NumberField.of_module_finite ℚ E
    ((smallHilbertClassFieldNormSubgroup
        (K := E)).toAddSubgroup.map
          (rationalAbstractFixedFieldIdeleClassEquivFixed
            L.field).toAddMonoidHom).map
        (stableBaseConjugationHom
          rationalIdeleClassRepresentation L s) =
      (smallHilbertClassFieldNormSubgroup
        (K := E)).toAddSubgroup.map
          (rationalAbstractFixedFieldIdeleClassEquivFixed
            L.field).toAddMonoidHom := by
  dsimp only
  let E :=
    abstractFixedField ℚ (SeparableClosure ℚ) L.field
  let hLfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          L.field (le_baseField L.field)) :=
    (L.toFiniteGaloisExtension.toFiniteAbstractFieldExtension).field.finite
  let : FiniteDimensional ℚ E :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) L.field hLfinite
  let : NumberField E :=
    NumberField.of_module_finite ℚ E
  exact
    addSubgroup_map_eq_of_comp_eq_of_map_eq
      (smallHilbertClassFieldNormSubgroup (K := E)).toAddSubgroup
      (rationalAbstractFixedFieldIdeleClassEquivFixed
        L.field).toAddMonoidHom
      (MonoidHom.toAdditive
        (ideleClassCongr
          (smallHilbertBaseConjugationAutomorphism K L s)).toMonoidHom)
      (stableBaseConjugationHom
        rationalIdeleClassRepresentation L s)
      (rationalSmallHilbertFixedPart_conjugation_comp K L s)
      (smallHilbertClassFieldNormSubgroup_toAddSubgroup_map_ideleClassCongr
        E (smallHilbertBaseConjugationAutomorphism K L s))

/-- The canonical small-Hilbert norm subgroup in the rational absolute
class formation is fixed by every lower-base conjugation. -/
theorem smallHilbertNormSubgroupInRationalClassFormation_map_conjugation
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field)
    (s : K.field.toSubgroup) :
    (smallHilbertNormSubgroupInRationalClassFormation
        (L.toFiniteGaloisExtension.toFiniteAbstractFieldExtension).field).map
        (stableBaseConjugationHom
          rationalIdeleClassRepresentation L s) =
      smallHilbertNormSubgroupInRationalClassFormation
        (L.toFiniteGaloisExtension.toFiniteAbstractFieldExtension).field := by
  exact
    smallHilbertNormSubgroupInRationalClassFormation_map_conjugation_canonical
      K L s

/-- If the upper extension realizes the canonical small-Hilbert norm
subgroup of the middle field, finite abelian classification identifies
its conjugate by every element of the lower base with the original
finite abelian subextension. -/
theorem smallHilbertClassField_conjugateSubextension_eq_self
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field)
    (M : FiniteAbelianSubextension L.field)
    (hM :
      M.normSubgroup rationalIdeleClassRepresentation =
        smallHilbertNormSubgroupInRationalClassFormation
          (L.toFiniteGaloisExtension.toFiniteAbstractFieldExtension).field)
    (s : K.field.toSubgroup) :
    conjugateFiniteAbelianSubextensionOverBase L M s = M := by
  let Ms :=
    conjugateFiniteAbelianSubextensionOverBase L M s
  have hnorm :
      Ms.normSubgroup rationalIdeleClassRepresentation =
        M.normSubgroup rationalIdeleClassRepresentation := by
    calc
      Ms.normSubgroup rationalIdeleClassRepresentation =
          (M.normSubgroup
            rationalIdeleClassRepresentation).map
              (stableBaseConjugationHom
                rationalIdeleClassRepresentation L s) := by
        exact
          conjugateFiniteAbelianSubextensionOverBase_normSubgroup
            rationalIdeleClassRepresentation L M s
      _ = M.normSubgroup rationalIdeleClassRepresentation := by
        rw [hM]
        exact
          smallHilbertNormSubgroupInRationalClassFormation_map_conjugation
            K L s
  change Ms = M
  apply
    FiniteAbelianSubextension.normSubgroupMap_injective
      rationalCyclotomicIdeleClassValuationData
      rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
      (L.toFiniteGaloisExtension.toFiniteAbstractFieldExtension).field
  apply Subtype.ext
  change
    Ms.normSubgroup rationalIdeleClassRepresentation =
      M.normSubgroup rationalIdeleClassRepresentation
  exact hnorm

/-- Field-level conjugation stability of the upper small Hilbert class
field in the two-stage tower. -/
theorem smallHilbertClassField_conjugate_eq_self
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field)
    (M : FiniteAbelianSubextension L.field)
    (hM :
      M.normSubgroup rationalIdeleClassRepresentation =
        smallHilbertNormSubgroupInRationalClassFormation
          (L.toFiniteGaloisExtension.toFiniteAbstractFieldExtension).field)
    (s : K.field.toSubgroup) :
    conjugateClosedSubgroup M.field s.1 = M.field := by
  have hMs :
      conjugateFiniteAbelianSubextensionOverBase L M s = M :=
    smallHilbertClassField_conjugateSubextension_eq_self
      K L M hM s
  have hfield :=
    congrArg
      (fun N : FiniteAbelianSubextension L.field => N.field)
      hMs
  simpa only [
    conjugateFiniteAbelianSubextensionOverBase_field] using hfield

/-- The second small Hilbert class field in a finite abelian tower is
an actual finite Galois extension of the original base. -/
noncomputable def smallHilbertClassFieldGaloisSubextension
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field)
    (M : FiniteAbelianSubextension L.field)
    (hM :
      M.normSubgroup rationalIdeleClassRepresentation =
        smallHilbertNormSubgroupInRationalClassFormation
          (L.toFiniteGaloisExtension.toFiniteAbstractFieldExtension).field) :
    FiniteGaloisSubextension K.field :=
  galoisSubextensionOfConjugateStableAbelianTower
    L M (smallHilbertClassField_conjugate_eq_self K L M hM)

/-- The abelian middle field of the two-stage small-Hilbert tower is
contained in the maximal abelian intermediate field of the resulting
Galois extension over the original base. -/
theorem smallHilbertTowerBase_le_maximalAbelianSubextension
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field)
    (M : FiniteAbelianSubextension L.field)
    (hM :
      M.normSubgroup rationalIdeleClassRepresentation =
        smallHilbertNormSubgroupInRationalClassFormation
          (L.toFiniteGaloisExtension.toFiniteAbstractFieldExtension).field) :
    L ≤
      maximalAbelianSubextension
        (smallHilbertClassFieldGaloisSubextension
          K L M hM) := by
  apply
    finiteAbelianIntermediate_le_maximalAbelianSubextension
      (smallHilbertClassFieldGaloisSubextension
        K L M hM) L
  simpa only [
    smallHilbertClassFieldGaloisSubextension,
    galoisSubextensionOfConjugateStableAbelianTower_field] using
    M.below

/-- If an actual finite Galois extension is everywhere unramified over
its base fixed field, then its maximal abelian intermediate field lies
in every realization of the small Hilbert class field.  Unramifiedness
is first descended to the genuine commutator-fixed intermediate field;
finite abelian classification then gives the field inclusion. -/
theorem
    maximalAbelianSubextension_le_smallHilbertClassField_of_everywhereUnramified
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field)
    (P : FiniteGaloisSubextension K.field)
    (hL :
      L.normSubgroup rationalIdeleClassRepresentation =
        smallHilbertNormSubgroupInRationalClassFormation K) :
    let F :=
      abstractFixedField ℚ (SeparableClosure ℚ) K.field
    let T :=
      abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) P.below
    letI hKfinite : Finite
        ((baseField
          (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
          CyclicCohomology.extensionSubgroup
            (baseField
              (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
            K.field (le_baseField K.field)) :=
      K.finite
    letI hPfinite : Finite
        (K.field.toSubgroup ⧸
          CyclicCohomology.extensionSubgroup
            K.field P.field P.below) :=
      P.finite
    letI : FiniteDimensional ℚ F :=
      abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K.field hKfinite
    letI : FiniteDimensional F T :=
      abstractRelativeFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ)
        K.field P.field P.below hKfinite hPfinite
    letI : IsScalarTower ℚ F T :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional ℚ T :=
      FiniteDimensional.trans ℚ F T
    letI : NumberField F :=
      NumberField.of_module_finite ℚ F
    letI : NumberField T :=
      NumberField.of_module_finite ℚ T
    IsEverywhereUnramified F T →
      maximalAbelianSubextension P ≤ L := by
  classical
  dsimp only
  let F :=
    abstractFixedField ℚ (SeparableClosure ℚ) K.field
  let T :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) P.below
  let A :=
    maximalAbelianSubextension P
  let E :=
    abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) A.below
  let hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K.field (le_baseField K.field)) :=
    K.finite
  let hPfinite : Finite
      (K.field.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          K.field P.field P.below) :=
    P.finite
  let hAfinite : Finite
      (K.field.toSubgroup ⧸
        CyclicCohomology.extensionSubgroup
          K.field A.field A.below) :=
    A.finite
  let : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K.field hKfinite
  let : FiniteDimensional F T :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ)
      K.field P.field P.below hKfinite hPfinite
  let : IsScalarTower ℚ F T :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional ℚ T :=
    FiniteDimensional.trans ℚ F T
  let : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ)
      K.field A.field A.below hKfinite hAfinite
  let : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  let : NumberField F :=
    NumberField.of_module_finite ℚ F
  let : NumberField T :=
    NumberField.of_module_finite ℚ T
  let : NumberField E :=
    NumberField.of_module_finite ℚ E
  intro hunramifiedTop
  have hPA :
      P.field.toSubgroup ≤ A.field.toSubgroup := by
    change
      P.field.toSubgroup ≤
        P.abelianIntermediateField.toSubgroup
    exact
      P.field_le_intermediateField
        (commutator P.extensionQuotient)
  have hET : E ≤ T := by
    intro x hx
    change
      x ∈ abstractFixedField
        ℚ (SeparableClosure ℚ) A.field at hx
    change
      x ∈ abstractFixedField
        ℚ (SeparableClosure ℚ) P.field
    exact
      (abstractFixedField_le
        ℚ (SeparableClosure ℚ) hPA) hx
  let : Algebra E T :=
    (IntermediateField.inclusion hET).toRingHom.toAlgebra
  let : IsScalarTower F E T :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hunramifiedAbelian :
      IsEverywhereUnramified F E :=
    IsEverywhereUnramified.bot hunramifiedTop
  exact
    everywhereUnramifiedFiniteAbelianSubextension_le_smallHilbertClassField
      K L A hL hunramifiedAbelian

end RationalSmallHilbert

end IdealClassFieldTheory
end GlobalClassFieldTheory
