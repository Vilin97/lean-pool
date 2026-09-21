/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.FieldTheory.Galois.Basic
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.IntrinsicBaseEquivalence
/-!
# Embedded extension quotients

This module identifies extension subgroups transported through an embedded finite Galois extension and constructs the resulting ambient quotient equivalence with the actual Galois group.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open scoped ValuativeRel

/-- Under the embedded-field base equivalence, membership in the intrinsic
extension subgroup for `E / F` is equivalent to membership in the ambient
extension subgroup determined by the two field ranges. -/
theorem
    intrinsicExtensionSubgroup_iff_ambientEmbeddedField
    (K F E : Type) [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [FiniteDimensional F E] [IsGalois F E]
    (j : E →ₐ[K] SeparableClosure K) :
    let i :=
      j.comp (IsScalarTower.toAlgHom K F E)
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    ∀ (e : SeparableClosure F ≃ₐ[F] SeparableClosure K)
      (tau : (intrinsicAbstractBase F).toSubgroup),
      let jF : E →ₐ[F] SeparableClosure K :=
        { j with commutes' := fun x => rfl }
      let jI : E →ₐ[F] SeparableClosure F :=
        e.symm.toAlgHom.comp jF
      let EI :=
        finiteGaloisAbstractExtensionOfEmbedding F E jI
      let H₀ :=
        closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange i)
      let J₀ :=
        closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange j)
      let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
        change
          (AlgHom.fieldRange j).fixingSubgroup ≤
            (AlgHom.fieldRange i).fixingSubgroup
        apply (AlgHom.fieldRange i).fixingSubgroup_le
        intro x hx
        rcases hx with ⟨y, rfl⟩
        exact ⟨algebraMap F E y, rfl⟩
      tau ∈ extensionSubgroup
          (intrinsicAbstractBase F) EI.field EI.below ↔
        intrinsicBaseEquivAmbientEmbeddedField K F i e tau ∈
          extensionSubgroup H₀ J₀ hJH := by
  dsimp only
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  let : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  intro e tau
  let jF : E →ₐ[F] SeparableClosure K :=
    { j with commutes' := fun x => rfl }
  let jI : E →ₐ[F] SeparableClosure F :=
    e.symm.toAlgHom.comp jF
  let EI :=
    finiteGaloisAbstractExtensionOfEmbedding F E jI
  let H₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange i)
  let J₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange j)
  let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
    change
      (AlgHom.fieldRange j).fixingSubgroup ≤
        (AlgHom.fieldRange i).fixingSubgroup
    apply (AlgHom.fieldRange i).fixingSubgroup_le
    intro x hx
    rcases hx with ⟨y, rfl⟩
    exact ⟨algebraMap F E y, rfl⟩
  change
    tau.1 ∈ (AlgHom.fieldRange jI).fixingSubgroup ↔
      (intrinsicBaseEquivAmbientEmbeddedField
        K F i e tau).1 ∈
          (AlgHom.fieldRange j).fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff,
    IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro htau x hx
    obtain ⟨y, rfl⟩ := hx
    change
      (intrinsicBaseEquivAmbientEmbeddedField
        K F i e tau).1.1 (j y) = j y
    rw [
      intrinsicBaseEquivAmbientEmbeddedField_apply_val
        K F i e tau]
    change e (tau.1 (jI y)) = j y
    rw [htau (jI y) ⟨y, rfl⟩]
    exact e.apply_symm_apply (j y)
  · intro hpsi x hx
    obtain ⟨y, rfl⟩ := hx
    apply e.injective
    change
      e (tau.1 (e.symm (j y))) =
        e (e.symm (j y))
    rw [e.apply_symm_apply]
    rw [← intrinsicBaseEquivAmbientEmbeddedField_apply_val
      K F i e tau]
    exact hpsi (j y) ⟨y, rfl⟩

/-- The embedded-field base equivalence maps the intrinsic extension subgroup
for `E / F` onto the ambient subgroup fixing the field range of `E`. -/
theorem
    map_intrinsicExtensionSubgroup_eq_ambientEmbeddedField
    (K F E : Type) [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [FiniteDimensional F E] [IsGalois F E]
    (j : E →ₐ[K] SeparableClosure K) :
    let i :=
      j.comp (IsScalarTower.toAlgHom K F E)
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    ∀ e : SeparableClosure F ≃ₐ[F] SeparableClosure K,
      let jF : E →ₐ[F] SeparableClosure K :=
        { j with commutes' := fun x => rfl }
      let jI : E →ₐ[F] SeparableClosure F :=
        e.symm.toAlgHom.comp jF
      let EI :=
        finiteGaloisAbstractExtensionOfEmbedding F E jI
      let H₀ :=
        closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange i)
      let J₀ :=
        closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange j)
      let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
        change
          (AlgHom.fieldRange j).fixingSubgroup ≤
            (AlgHom.fieldRange i).fixingSubgroup
        apply (AlgHom.fieldRange i).fixingSubgroup_le
        intro x hx
        rcases hx with ⟨y, rfl⟩
        exact ⟨algebraMap F E y, rfl⟩
      let psi :=
        intrinsicBaseEquivAmbientEmbeddedField K F i e
      (extensionSubgroup
          (intrinsicAbstractBase F) EI.field EI.below).map
          psi.toMonoidHom =
        extensionSubgroup H₀ J₀ hJH := by
  dsimp only
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  let : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  intro e
  let jF : E →ₐ[F] SeparableClosure K :=
    { j with commutes' := fun x => rfl }
  let jI : E →ₐ[F] SeparableClosure F :=
    e.symm.toAlgHom.comp jF
  let EI :=
    finiteGaloisAbstractExtensionOfEmbedding F E jI
  let H₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange i)
  let J₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange j)
  have hRange :
      AlgHom.fieldRange i ≤ AlgHom.fieldRange j := by
    intro x hx
    rcases hx with ⟨y, rfl⟩
    exact ⟨algebraMap F E y, rfl⟩
  let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
    change
      (AlgHom.fieldRange j).fixingSubgroup ≤
        (AlgHom.fieldRange i).fixingSubgroup
    exact (AlgHom.fieldRange i).fixingSubgroup_le hRange
  let psi :=
    intrinsicBaseEquivAmbientEmbeddedField K F i e
  ext sigma
  constructor
  · rintro ⟨tau, htau, rfl⟩
    exact
      (intrinsicExtensionSubgroup_iff_ambientEmbeddedField
        K F E j e tau).1 htau
  · intro hsigma
    let tau :
        (intrinsicAbstractBase F).toSubgroup :=
      psi.symm sigma
    refine ⟨tau, ?_, psi.apply_symm_apply sigma⟩
    apply
      (intrinsicExtensionSubgroup_iff_ambientEmbeddedField
        K F E j e tau).2
    have htauImage : psi tau = sigma :=
      psi.apply_symm_apply sigma
    rw [htauImage]
    exact hsigma

/-- The fixing subgroup cut out by an embedded finite Galois extension is
normal inside the fixing subgroup of its embedded base field. -/
theorem ambientEmbeddedExtensionSubgroup_normal
    (K F E : Type) [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [FiniteDimensional F E] [IsGalois F E]
    (j : E →ₐ[K] SeparableClosure K) :
    let i :=
      j.comp (IsScalarTower.toAlgHom K F E)
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    ∀ e : SeparableClosure F ≃ₐ[F] SeparableClosure K,
      let _e := e
      let H₀ :=
        closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange i)
      let J₀ :=
        closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange j)
      let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
        change
          (AlgHom.fieldRange j).fixingSubgroup ≤
            (AlgHom.fieldRange i).fixingSubgroup
        apply (AlgHom.fieldRange i).fixingSubgroup_le
        intro x hx
        rcases hx with ⟨y, rfl⟩
        exact ⟨algebraMap F E y, rfl⟩
      (extensionSubgroup H₀ J₀ hJH).Normal := by
  dsimp only
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  let : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  intro e
  let jF : E →ₐ[F] SeparableClosure K :=
    { j with commutes' := fun x => rfl }
  let jI : E →ₐ[F] SeparableClosure F :=
    e.symm.toAlgHom.comp jF
  let EI :=
    finiteGaloisAbstractExtensionOfEmbedding F E jI
  let H₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange i)
  let J₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange j)
  have hRange :
      AlgHom.fieldRange i ≤ AlgHom.fieldRange j := by
    intro x hx
    rcases hx with ⟨y, rfl⟩
    exact ⟨algebraMap F E y, rfl⟩
  let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
    change
      (AlgHom.fieldRange j).fixingSubgroup ≤
        (AlgHom.fieldRange i).fixingSubgroup
    exact (AlgHom.fieldRange i).fixingSubgroup_le hRange
  let psi :=
    intrinsicBaseEquivAmbientEmbeddedField K F i e
  let hSourceNormal :
      (extensionSubgroup
        (intrinsicAbstractBase F) EI.field EI.below).Normal :=
    EI.normal
  have hmap :
      (extensionSubgroup
          (intrinsicAbstractBase F) EI.field EI.below).map
          psi.toMonoidHom =
        extensionSubgroup H₀ J₀ hJH := by
    simpa only [i, jF, jI, EI, H₀, J₀, hJH, psi] using
      map_intrinsicExtensionSubgroup_eq_ambientEmbeddedField
        K F E j e
  rw [← hmap]
  exact
    Subgroup.Normal.map hSourceNormal
      psi.toMonoidHom psi.surjective

/-- The relative quotient of fixing subgroups attached to an embedded
finite Galois extension is finite. -/
theorem ambientEmbeddedExtensionQuotient_finite
    (K F E : Type) [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [FiniteDimensional F E] [IsGalois F E]
    (j : E →ₐ[K] SeparableClosure K) :
    let i :=
      j.comp (IsScalarTower.toAlgHom K F E)
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    ∀ e : SeparableClosure F ≃ₐ[F] SeparableClosure K,
      let H₀ :=
        closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange i)
      let J₀ :=
        closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange j)
      let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
        change
          (AlgHom.fieldRange j).fixingSubgroup ≤
            (AlgHom.fieldRange i).fixingSubgroup
        apply (AlgHom.fieldRange i).fixingSubgroup_le
        intro x hx
        rcases hx with ⟨y, rfl⟩
        exact ⟨algebraMap F E y, rfl⟩
      letI _hTargetNormal :
          (extensionSubgroup H₀ J₀ hJH).Normal :=
        ambientEmbeddedExtensionSubgroup_normal K F E j e
      Finite
        (H₀.toSubgroup ⧸ extensionSubgroup H₀ J₀ hJH) := by
  dsimp only
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  let : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  intro e
  let jF : E →ₐ[F] SeparableClosure K :=
    { j with commutes' := fun x => rfl }
  let jI : E →ₐ[F] SeparableClosure F :=
    e.symm.toAlgHom.comp jF
  let EI :=
    finiteGaloisAbstractExtensionOfEmbedding F E jI
  let H₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange i)
  let J₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange j)
  have hRange :
      AlgHom.fieldRange i ≤ AlgHom.fieldRange j := by
    intro x hx
    rcases hx with ⟨y, rfl⟩
    exact ⟨algebraMap F E y, rfl⟩
  let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
    change
      (AlgHom.fieldRange j).fixingSubgroup ≤
        (AlgHom.fieldRange i).fixingSubgroup
    exact (AlgHom.fieldRange i).fixingSubgroup_le hRange
  let hTargetNormal :
      (extensionSubgroup H₀ J₀ hJH).Normal :=
    ambientEmbeddedExtensionSubgroup_normal K F E j e
  let psi :=
    intrinsicBaseEquivAmbientEmbeddedField K F i e
  let hSourceNormal :
      (extensionSubgroup
        (intrinsicAbstractBase F) EI.field EI.below).Normal :=
    EI.normal
  let hSourceFinite : Finite
      ((intrinsicAbstractBase F).toSubgroup ⧸
        extensionSubgroup
          (intrinsicAbstractBase F) EI.field EI.below) :=
    EI.finite
  have hmap :
      (extensionSubgroup
          (intrinsicAbstractBase F) EI.field EI.below).map
          psi.toMonoidHom =
        extensionSubgroup H₀ J₀ hJH := by
    simpa only [i, jF, jI, EI, H₀, J₀, hJH, psi] using
      map_intrinsicExtensionSubgroup_eq_ambientEmbeddedField
        K F E j e
  exact
    Finite.of_equiv
      ((intrinsicAbstractBase F).toSubgroup ⧸
        extensionSubgroup
          (intrinsicAbstractBase F) EI.field EI.below)
      (QuotientGroup.congr
        (extensionSubgroup
          (intrinsicAbstractBase F) EI.field EI.below)
        (extensionSubgroup H₀ J₀ hJH)
        psi hmap).toEquiv

/-- The quotient of ambient fixing subgroups attached to an embedded
finite Galois extension is canonically its actual Galois group. -/
noncomputable def
    ambientEmbeddedExtensionQuotientEquivGaloisGroup
    (K F E : Type) [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [FiniteDimensional F E] [IsGalois F E]
    (j : E →ₐ[K] SeparableClosure K) :
    let i :=
      j.comp (IsScalarTower.toAlgHom K F E)
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    ∀ e : SeparableClosure F ≃ₐ[F] SeparableClosure K,
      let H₀ :=
        closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange i)
      let J₀ :=
        closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange j)
      let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
        change
          (AlgHom.fieldRange j).fixingSubgroup ≤
            (AlgHom.fieldRange i).fixingSubgroup
        apply (AlgHom.fieldRange i).fixingSubgroup_le
        intro x hx
        rcases hx with ⟨y, rfl⟩
        exact ⟨algebraMap F E y, rfl⟩
      letI hTargetNormal :
          (extensionSubgroup H₀ J₀ hJH).Normal :=
        ambientEmbeddedExtensionSubgroup_normal K F E j e
      (H₀.toSubgroup ⧸ extensionSubgroup H₀ J₀ hJH) ≃*
        Gal(E / F) := by
  dsimp only
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  letI : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  intro e
  let jF : E →ₐ[F] SeparableClosure K :=
    { j with commutes' := fun x => rfl }
  let jI : E →ₐ[F] SeparableClosure F :=
    e.symm.toAlgHom.comp jF
  let EI :=
    finiteGaloisAbstractExtensionOfEmbedding F E jI
  let H₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange i)
  let J₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange j)
  have hRange :
      AlgHom.fieldRange i ≤ AlgHom.fieldRange j := by
    intro x hx
    rcases hx with ⟨y, rfl⟩
    exact ⟨algebraMap F E y, rfl⟩
  let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
    change
      (AlgHom.fieldRange j).fixingSubgroup ≤
        (AlgHom.fieldRange i).fixingSubgroup
    exact (AlgHom.fieldRange i).fixingSubgroup_le hRange
  let psi :=
    intrinsicBaseEquivAmbientEmbeddedField K F i e
  letI hSourceNormal :
      (extensionSubgroup
        (intrinsicAbstractBase F) EI.field EI.below).Normal :=
    EI.normal
  letI hTargetNormal :
      (extensionSubgroup H₀ J₀ hJH).Normal :=
    ambientEmbeddedExtensionSubgroup_normal K F E j e
  have hmap :
      (extensionSubgroup
          (intrinsicAbstractBase F) EI.field EI.below).map
          psi.toMonoidHom =
        extensionSubgroup H₀ J₀ hJH := by
    simpa only [i, jF, jI, EI, H₀, J₀, hJH, psi] using
      map_intrinsicExtensionSubgroup_eq_ambientEmbeddedField
        K F E j e
  exact
    (QuotientGroup.congr
      (extensionSubgroup
        (intrinsicAbstractBase F) EI.field EI.below)
      (extensionSubgroup H₀ J₀ hJH)
      psi hmap).symm.trans
      (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
        F E jI)

/-- The ambient embedded quotient equivalence sends the class of a transported
intrinsic automorphism to its class in the finite Galois quotient. -/
theorem
    ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk
    (K F E : Type) [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [FiniteDimensional F E] [IsGalois F E]
    (j : E →ₐ[K] SeparableClosure K) :
    let i :=
      j.comp (IsScalarTower.toAlgHom K F E)
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    ∀ (e : SeparableClosure F ≃ₐ[F] SeparableClosure K)
      (tau : (intrinsicAbstractBase F).toSubgroup),
      let jF : E →ₐ[F] SeparableClosure K :=
        { j with commutes' := fun x => rfl }
      let jI : E →ₐ[F] SeparableClosure F :=
        e.symm.toAlgHom.comp jF
      let EI :=
        finiteGaloisAbstractExtensionOfEmbedding F E jI
      let H₀ :=
        closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange i)
      let J₀ :=
        closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange j)
      let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
        change
          (AlgHom.fieldRange j).fixingSubgroup ≤
            (AlgHom.fieldRange i).fixingSubgroup
        apply (AlgHom.fieldRange i).fixingSubgroup_le
        intro x hx
        rcases hx with ⟨y, rfl⟩
        exact ⟨algebraMap F E y, rfl⟩
      letI _hSourceNormal :
          (extensionSubgroup
            (intrinsicAbstractBase F) EI.field EI.below).Normal :=
        EI.normal
      letI _hTargetNormal :
          (extensionSubgroup H₀ J₀ hJH).Normal :=
        ambientEmbeddedExtensionSubgroup_normal K F E j e
      ambientEmbeddedExtensionQuotientEquivGaloisGroup
          K F E j e
          (QuotientGroup.mk
            (intrinsicBaseEquivAmbientEmbeddedField
              K F i e tau)) =
        finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
          F E jI (QuotientGroup.mk tau) := by
  dsimp only
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  let : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  intro e tau
  let jF : E →ₐ[F] SeparableClosure K :=
    { j with commutes' := fun x => rfl }
  let jI : E →ₐ[F] SeparableClosure F :=
    e.symm.toAlgHom.comp jF
  let EI :=
    finiteGaloisAbstractExtensionOfEmbedding F E jI
  let H₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange i)
  let J₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange j)
  let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
    change
      (AlgHom.fieldRange j).fixingSubgroup ≤
        (AlgHom.fieldRange i).fixingSubgroup
    apply (AlgHom.fieldRange i).fixingSubgroup_le
    intro x hx
    rcases hx with ⟨y, rfl⟩
    exact ⟨algebraMap F E y, rfl⟩
  let hSourceNormal :
      (extensionSubgroup
        (intrinsicAbstractBase F) EI.field EI.below).Normal :=
    EI.normal
  let hTargetNormal :
      (extensionSubgroup H₀ J₀ hJH).Normal :=
    ambientEmbeddedExtensionSubgroup_normal K F E j e
  let psi :=
    intrinsicBaseEquivAmbientEmbeddedField K F i e
  have hmap :
      (extensionSubgroup
          (intrinsicAbstractBase F) EI.field EI.below).map
          psi.toMonoidHom =
        extensionSubgroup H₀ J₀ hJH := by
    simpa only [i, jF, jI, EI, H₀, J₀, hJH, psi] using
      map_intrinsicExtensionSubgroup_eq_ambientEmbeddedField
        K F E j e
  change
    finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
        F E jI
        ((QuotientGroup.congr
          (extensionSubgroup
            (intrinsicAbstractBase F) EI.field EI.below)
          (extensionSubgroup H₀ J₀ hJH)
          psi hmap).symm
          (QuotientGroup.mk
            (psi tau))) =
      finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
        F E jI (QuotientGroup.mk tau)
  congr 1
  change
    QuotientGroup.mk
        (psi.symm (psi tau)) =
      QuotientGroup.mk tau
  rw [psi.symm_apply_apply]

/-- Evaluating the ambient embedded quotient class on an element of `E`
agrees, after applying the embedding, with the original ambient automorphism. -/
theorem
    ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_apply
    (K F E : Type) [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Algebra K E]
    [IsScalarTower K F E]
    [FiniteDimensional K F] [Algebra.IsSeparable K F]
    [FiniteDimensional F E] [IsGalois F E]
    (j : E →ₐ[K] SeparableClosure K) :
    let i :=
      j.comp (IsScalarTower.toAlgHom K F E)
    letI : Algebra F (SeparableClosure F) :=
      (separableClosure F (AlgebraicClosure F)).algebra
    letI : Algebra F (SeparableClosure K) :=
      i.toRingHom.toAlgebra
    ∀ (e : SeparableClosure F ≃ₐ[F] SeparableClosure K)
      (rho :
        (closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange i)).toSubgroup)
      (x : E),
      let H₀ :=
        closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange i)
      let J₀ :=
        closedFixingSubgroup K (SeparableClosure K)
          (AlgHom.fieldRange j)
      let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
        change
          (AlgHom.fieldRange j).fixingSubgroup ≤
            (AlgHom.fieldRange i).fixingSubgroup
        apply (AlgHom.fieldRange i).fixingSubgroup_le
        intro y hy
        rcases hy with ⟨z, rfl⟩
        exact ⟨algebraMap F E z, rfl⟩
      letI _hTargetNormal :
          (extensionSubgroup H₀ J₀ hJH).Normal :=
        ambientEmbeddedExtensionSubgroup_normal K F E j e
      j
          (ambientEmbeddedExtensionQuotientEquivGaloisGroup
            K F E j e (QuotientGroup.mk rho) x) =
        rho.1.1 (j x) := by
  dsimp only
  let i :=
    j.comp (IsScalarTower.toAlgHom K F E)
  let : Algebra F (SeparableClosure K) :=
    i.toRingHom.toAlgebra
  intro e rho x
  let jF : E →ₐ[F] SeparableClosure K :=
    { j with commutes' := fun y => rfl }
  let jI : E →ₐ[F] SeparableClosure F :=
    e.symm.toAlgHom.comp jF
  let EI :=
    finiteGaloisAbstractExtensionOfEmbedding F E jI
  let H₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange i)
  let J₀ :=
    closedFixingSubgroup K (SeparableClosure K)
      (AlgHom.fieldRange j)
  have hRange :
      AlgHom.fieldRange i ≤ AlgHom.fieldRange j := by
    intro y hy
    rcases hy with ⟨z, rfl⟩
    exact ⟨algebraMap F E z, rfl⟩
  let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
    change
      (AlgHom.fieldRange j).fixingSubgroup ≤
        (AlgHom.fieldRange i).fixingSubgroup
    exact (AlgHom.fieldRange i).fixingSubgroup_le hRange
  let hSourceNormal :
      (extensionSubgroup
        (intrinsicAbstractBase F) EI.field EI.below).Normal :=
    EI.normal
  let hTargetNormal :
      (extensionSubgroup H₀ J₀ hJH).Normal :=
    ambientEmbeddedExtensionSubgroup_normal K F E j e
  let psi :=
    intrinsicBaseEquivAmbientEmbeddedField K F i e
  let tau :
      (intrinsicAbstractBase F).toSubgroup :=
    psi.symm rho
  have hpsi : psi tau = rho :=
    psi.apply_symm_apply rho
  have hquotient :
      ambientEmbeddedExtensionQuotientEquivGaloisGroup
          K F E j e (QuotientGroup.mk rho) =
        finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
          F E jI (QuotientGroup.mk tau) := by
    rw [← hpsi]
    exact
      ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk
        K F E j e tau
  rw [hquotient]
  have haction :=
    finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply
      F E jI tau x
  calc
    j
        (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
          F E jI (QuotientGroup.mk tau) x) =
        e (tau.1 (jI x)) := by
      rw [show
        j
            (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
              F E jI (QuotientGroup.mk tau) x) =
          e
            (jI
              (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
                F E jI (QuotientGroup.mk tau) x)) by
        change
          j
              (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
                F E jI (QuotientGroup.mk tau) x) =
            e
              (e.symm
                (j
                  (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
                    F E jI (QuotientGroup.mk tau) x)))
        rw [e.apply_symm_apply]]
      exact congrArg e haction
    _ = (psi tau).1.1 (j x) := by
      rw [intrinsicBaseEquivAmbientEmbeddedField_apply_val]
      rfl
    _ = rho.1.1 (j x) := by
      rw [hpsi]

end LocalClassFieldTheory
