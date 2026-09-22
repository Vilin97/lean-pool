/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.PrimitiveElement
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableNormProduct
/-!
# Relative norms on actual fixed fields

This file identifies the class-formation relative norm on ambient fixed units
with the ordinary field norm between two concrete fixed fields.  The
intermediate extension need not be normal: relative left cosets are
identified with field embeddings into the common separably closed ambient
field, and both norms are then the same product of conjugates.
-/

noncomputable section

open scoped BigOperators

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation LocalClassFieldTheory

variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
  [IsGalois k Ω] [IsSepClosed Ω]

/-- The embeddings of a finite separable extension into a field form a finite type, enumerated
using a power basis. -/
noncomputable local instance finiteSeparableAlgHomFintypeRelative
    {F E T : Type} [Field F] [Field E] [Field T]
    [Algebra F E] [Algebra F T]
    [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    Fintype (E →ₐ[F] T) :=
  PowerBasis.AlgHom.fintype (Field.powerBasisOfFiniteOfSeparable F E)

/-- A left coset of the abstract fixing subgroup restricts to an embedding
of the upper concrete fixed field into the common ambient field. -/
def abstractFixedFieldCosetToAlgHom
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup) :
    (K.toSubgroup ⧸ extensionSubgroup K L hLK) →
      (abstractRelativeFixedField k Ω hLK →ₐ[
        abstractFixedField k Ω K] Ω) := fun q =>
  Quotient.liftOn' q
    (fun σ => (abstractSubgroupEquivGaloisGroup k Ω K σ).toAlgHom.comp
      (abstractRelativeFixedField k Ω hLK).val)
    (by
      intro σ τ hστ
      have hmem : σ⁻¹ * τ ∈ extensionSubgroup K L hLK :=
        QuotientGroup.leftRel_apply.mp hστ
      let η : L.toSubgroup := ⟨(σ⁻¹ * τ).1, hmem⟩
      have hτ : τ = σ * Subgroup.inclusion hLK η := by
        apply Subtype.ext
        change τ.1 = σ.1 * η.1
        simp [η]
      apply AlgHom.ext
      intro x
      have hηfix : η.1 (x : Ω) = (x : Ω) :=
        (IntermediateField.mem_fixedField_iff L.toSubgroup
          (x : Ω)).1 x.property η.1 η.2
      change σ.1 (x : Ω) = τ.1 (x : Ω)
      calc
        σ.1 (x : Ω) = σ.1 (η.1 (x : Ω)) :=
          congrArg σ.1 hηfix.symm
        _ = (σ.1 * η.1) (x : Ω) := rfl
        _ = τ.1 (x : Ω) := by
          have hτ' := congrArg Subtype.val hτ
          change τ.1 = σ.1 * η.1 at hτ'
          rw [hτ'])

omit [IsSepClosed Ω] in
/-- States the theorem `abstractFixedFieldCosetToAlgHom_mk`. -/
@[simp]
theorem abstractFixedFieldCosetToAlgHom_mk
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup) (σ : K.toSubgroup) :
    abstractFixedFieldCosetToAlgHom k Ω K L hLK
        (QuotientGroup.mk σ) =
      (abstractSubgroupEquivGaloisGroup k Ω K σ).toAlgHom.comp
        (abstractRelativeFixedField k Ω hLK).val :=
  rfl

private theorem abstractFixedFieldCosetToAlgHom_surjective
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [FiniteDimensional (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK)] :
    Function.Surjective
      (abstractFixedFieldCosetToAlgHom k Ω K L hLK) := by
  intro f
  let : Algebra.IsSeparable (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) :=
    Algebra.isSeparable_tower_bot_of_isSeparable
      (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) Ω
  let : Algebra.IsSeparable (abstractRelativeFixedField k Ω hLK) Ω :=
    Algebra.isSeparable_tower_top_of_isSeparable
      (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) Ω
  obtain ⟨φ, hφ⟩ :=
    (IsSepClosed.surjective_domRestrict_of_isSeparable
      (K := abstractFixedField k Ω K)
      (L := abstractRelativeFixedField k Ω hLK)
      (M := Ω) (E := Ω)) f
  let σReal : Gal(Ω/abstractFixedField k Ω K) :=
    AlgEquiv.ofBijective φ
      (Normal.toIsAlgebraic.algHom_bijective₂
        φ (AlgHom.id (abstractFixedField k Ω K) Ω)).1
  let σ : K.toSubgroup :=
    (abstractSubgroupEquivGaloisGroup k Ω K).symm σReal
  refine ⟨QuotientGroup.mk σ, ?_⟩
  apply AlgHom.ext
  intro x
  have hx := congrArg
    (fun ψ : abstractRelativeFixedField k Ω hLK →ₐ[
      abstractFixedField k Ω K] Ω => ψ x) hφ
  change σReal (x : Ω) = f x
  change φ (x : Ω) = f x at hx
  exact hx

omit [IsSepClosed Ω] in
private theorem abstractFixedFieldCosetToAlgHom_injective
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup) :
    Function.Injective
      (abstractFixedFieldCosetToAlgHom k Ω K L hLK) := by
  intro q r hqr
  rw [← Quotient.out_eq q, ← Quotient.out_eq r] at hqr ⊢
  apply Quotient.sound'
  apply QuotientGroup.leftRel_apply.mpr
  apply (mem_extensionSubgroup_iff K L hLK
    ((Quotient.out q)⁻¹ * Quotient.out r)).2
  have hfix : (Quotient.out q).1⁻¹ * (Quotient.out r).1 ∈
      (abstractFixedField k Ω L).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    let y : abstractRelativeFixedField k Ω hLK := ⟨x, hx⟩
    have hy := congrArg
      (fun ψ : abstractRelativeFixedField k Ω hLK →ₐ[
        abstractFixedField k Ω K] Ω => ψ y) hqr
    change (Quotient.out q).1 (y : Ω) =
      (Quotient.out r).1 (y : Ω) at hy
    change (Quotient.out q).1⁻¹ ((Quotient.out r).1 x) = x
    rw [← hy]
    simp [y]
  rw [InfiniteGalois.fixingSubgroup_fixedField L] at hfix
  change (Quotient.out q).1⁻¹ * (Quotient.out r).1 ∈ L.toSubgroup
  exact hfix

/-- Abstract relative left cosets are precisely the embeddings of the upper
concrete fixed field into the ambient separably closed field. -/
def abstractFixedFieldCosetEquivAlgHom
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [FiniteDimensional (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK)] :
    (K.toSubgroup ⧸ extensionSubgroup K L hLK) ≃
      (abstractRelativeFixedField k Ω hLK →ₐ[
        abstractFixedField k Ω K] Ω) :=
  Equiv.ofBijective (abstractFixedFieldCosetToAlgHom k Ω K L hLK)
    ⟨abstractFixedFieldCosetToAlgHom_injective k Ω K L hLK,
      abstractFixedFieldCosetToAlgHom_surjective k Ω K L hLK⟩

omit [IsSepClosed Ω] in
/-- States the theorem `relativeCosetAction_abstractFixedFieldUnit_val`. -/
theorem relativeCosetAction_abstractFixedFieldUnit_val
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (x : (abstractRelativeFixedField k Ω hLK)ˣ)
    (q : K.toSubgroup ⧸ extensionSubgroup K L hLK) :
    ((Additive.toMul
      (relativeCosetAction (galoisAmbientUnitsRep k Ω)
        K L hLK
        (abstractRelativeFixedFieldUnitsEquivGaloisFixed
          k Ω K L hLK (Additive.ofMul x)) q) : Ωˣ) : Ω) =
      abstractFixedFieldCosetToAlgHom k Ω K L hLK q
        (x : abstractRelativeFixedField k Ω hLK) := by
  refine Quotient.inductionOn' q ?_
  intro σ
  rfl

/-- The class-formation relative norm on fixed coefficients is the ordinary
field norm between the two concrete fixed fields, without a normality
assumption on the intermediate extension. -/
theorem relativeNorm_abstractFixedFieldUnit_eq_normUnits
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    [hKabsolute : Finite
      ((baseField Gal(Ω/k)).toSubgroup ⧸
        extensionSubgroup (baseField Gal(Ω/k)) K
          (le_baseField K))]
    (x : (abstractRelativeFixedField k Ω hLK)ˣ) :
    relativeNorm (galoisAmbientUnitsRep k Ω) K L hLK
        (abstractRelativeFixedFieldUnitsEquivGaloisFixed
          k Ω K L hLK (Additive.ofMul x)) =
      abstractFixedFieldUnitsEquivGaloisFixed k Ω K
        (Additive.ofMul
          (normUnits (abstractFixedField k Ω K)
            (abstractRelativeFixedField k Ω hLK) x)) := by
  let : FiniteDimensional (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) :=
    abstractRelativeFixedField_finiteDimensional
      k Ω K L hLK hKabsolute hfinite
  let : Algebra.IsSeparable (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) :=
    Algebra.isSeparable_tower_bot_of_isSeparable
      (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) Ω
  apply Subtype.ext
  apply Additive.ext
  apply Units.ext
  let Q := K.toSubgroup ⧸ extensionSubgroup K L hLK
  let := Fintype.ofFinite Q
  change
    ((Additive.toMul
      (relativeNormValue (galoisAmbientUnitsRep k Ω)
        K L hLK
        (abstractRelativeFixedFieldUnitsEquivGaloisFixed
          k Ω K L hLK (Additive.ofMul x))) : Ωˣ) : Ω) = _
  rw [relativeNormValue]
  change
    (↑(Additive.toMul (∑ q : Q,
      relativeCosetAction (galoisAmbientUnitsRep k Ω)
        K L hLK
        (abstractRelativeFixedFieldUnitsEquivGaloisFixed
          k Ω K L hLK (Additive.ofMul x)) q) : Ωˣ) : Ω) = _
  change (Units.coeHom Ω) (∏ q : Q,
    Additive.toMul
      (relativeCosetAction (galoisAmbientUnitsRep k Ω)
        K L hLK
        (abstractRelativeFixedFieldUnitsEquivGaloisFixed
          k Ω K L hLK (Additive.ofMul x)) q)) = _
  rw [map_prod]
  change
    (∏ q : Q,
      ((Additive.toMul
        (relativeCosetAction (galoisAmbientUnitsRep k Ω)
          K L hLK
          (abstractRelativeFixedFieldUnitsEquivGaloisFixed
            k Ω K L hLK (Additive.ofMul x)) q) : Ωˣ) : Ω)) = _
  calc
    _ = ∏ σ : abstractRelativeFixedField k Ω hLK →ₐ[
        abstractFixedField k Ω K] Ω,
        σ (x : abstractRelativeFixedField k Ω hLK) := by
      exact Fintype.prod_equiv
        (abstractFixedFieldCosetEquivAlgHom k Ω K L hLK)
        (fun q : Q =>
          ((Additive.toMul
            (relativeCosetAction (galoisAmbientUnitsRep k Ω)
              K L hLK
              (abstractRelativeFixedFieldUnitsEquivGaloisFixed
                k Ω K L hLK (Additive.ofMul x)) q) : Ωˣ) : Ω))
        (fun σ : abstractRelativeFixedField k Ω hLK →ₐ[
          abstractFixedField k Ω K] Ω =>
            σ (x : abstractRelativeFixedField k Ω hLK))
        (relativeCosetAction_abstractFixedFieldUnit_val
          k Ω K L hLK x)
    _ = algebraMap (abstractFixedField k Ω K) Ω
        (Algebra.norm (abstractFixedField k Ω K)
          (x : abstractRelativeFixedField k Ω hLK)) :=
      (algebraMap_norm_eq_prod_embeddings_of_isSepClosed
        (abstractFixedField k Ω K) Ω
        (abstractRelativeFixedField k Ω hLK)
        (x : abstractRelativeFixedField k Ω hLK)).symm

end LocalClassFieldTheory
