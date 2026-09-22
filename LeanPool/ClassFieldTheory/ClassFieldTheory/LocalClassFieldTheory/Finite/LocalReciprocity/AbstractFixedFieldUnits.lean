/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.FieldTheory.Galois.Basic
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TateTransport
import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FieldRepresentation

/-! # Abstract Fixed Field Units -/
namespace LocalClassFieldTheory
open RamificationTheory CyclicCohomology KummerTheory

open LocalFieldTheory

open ClassFormation

/-!
# The local class-field-axiom theorem: units in an abstract finite fixed-field tower

For a finite abstract tower represented by closed subgroups `L ≤ K`, this
file identifies the descended coefficient representation on `A_L` with the
ordinary representation of `Gal(L/K)` on the units of the concrete upper
fixed field.  Both the carrier and the action are compared; the latter is
essential for transporting the actual Tate groups rather than only their
underlying norm quotients.
-/

noncomputable section

open CategoryTheory

variable (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]

/-- Units of the concrete fixed field represented by an arbitrary closed
subgroup, identified directly with the corresponding fixed coefficients. -/
def abstractFixedFieldUnitsEquivGaloisFixed
    (H : ClosedSubgroup (Gal(Ω/k))) :
    Additive (abstractFixedField k Ω H)ˣ ≃+
      ambientFixedAddSubgroup (galoisAmbientUnitsRep k Ω) H where
  toFun x := ⟨intermediateFieldUnitsToGaloisAmbient k Ω
      (abstractFixedField k Ω H) x, by
    intro σ
    apply Additive.ext
    apply Units.ext
    exact (IntermediateField.mem_fixedField_iff H.toSubgroup
      ((Additive.toMul x : (abstractFixedField k Ω H)ˣ) : Ω)).1
        (Additive.toMul x : (abstractFixedField k Ω H)ˣ).1.property σ.1 σ.2⟩
  invFun a := by
    have ha : ((Additive.toMul a.1 : Ωˣ) : Ω) ∈
        abstractFixedField k Ω H := by
      rw [IntermediateField.mem_fixedField_iff]
      intro σ hσ
      have hfixed := a.2 ⟨σ, hσ⟩
      exact congrArg
        (fun z : Additive Ωˣ => ((Additive.toMul z : Ωˣ) : Ω)) hfixed
    let y₀ : abstractFixedField k Ω H :=
      ⟨((Additive.toMul a.1 : Ωˣ) : Ω), ha⟩
    have hy₀ : y₀ ≠ 0 := by
      intro h
      have h' : ((Additive.toMul a.1 : Ωˣ) : Ω) = 0 :=
        congrArg (abstractFixedField k Ω H).val h
      exact (Additive.toMul a.1 : Ωˣ).ne_zero h'
    exact Additive.ofMul (Units.mk0 y₀ hy₀)
  left_inv x := by
    apply Additive.ext
    apply Units.ext
    rfl
  right_inv a := by
    apply Subtype.ext
    apply Additive.ext
    apply Units.ext
    rfl
  map_add' _ _ := by
    apply Subtype.ext
    rfl

omit [IsGalois k Ω] in
/-- States the theorem `abstractFixedFieldUnitsEquivGaloisFixed_coe`. -/
@[simp]
theorem abstractFixedFieldUnitsEquivGaloisFixed_coe
    (H : ClosedSubgroup (Gal(Ω/k)))
    (x : Additive (abstractFixedField k Ω H)ˣ) :
    ((abstractFixedFieldUnitsEquivGaloisFixed k Ω H x).1 :
        Additive Ωˣ) =
      intermediateFieldUnitsToGaloisAmbient k Ω
        (abstractFixedField k Ω H) x :=
  rfl

/-- Scalar extension from the lower fixed field does not change the
underlying upper field or its unit group. -/
def abstractRelativeFixedFieldUnitsEquivGaloisFixed
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup) :
    Additive (abstractRelativeFixedField k Ω hLK)ˣ ≃+
      ambientFixedAddSubgroup (galoisAmbientUnitsRep k Ω) L := by
  change Additive (abstractFixedField k Ω L)ˣ ≃+ _
  exact abstractFixedFieldUnitsEquivGaloisFixed k Ω L

omit [IsGalois k Ω] in
/-- States the theorem `abstractRelativeFixedFieldUnitsEquivGaloisFixed_coe`. -/
@[simp]
theorem abstractRelativeFixedFieldUnitsEquivGaloisFixed_coe
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (x : Additive (abstractRelativeFixedField k Ω hLK)ˣ) :
    ((abstractRelativeFixedFieldUnitsEquivGaloisFixed
        k Ω K L hLK x).1 : Additive Ωˣ) =
      intermediateFieldUnitsToGaloisAmbient k Ω
        (abstractFixedField k Ω L) x :=
  rfl

/-- Carrier comparison between the descended class-formation representation and
the actual unit group of the upper concrete fixed field. -/
def abstractExtensionFixedRepresentationUnitsEquiv
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal) :
    (extensionFixedRepresentation (galoisAmbientUnitsRep k Ω)
        K L hLK hnormal).V ≃+
      Additive (abstractRelativeFixedField k Ω hLK)ˣ :=
  (extensionFixedRepresentationEquiv (galoisAmbientUnitsRep k Ω)
      K L hLK hnormal).trans
    (abstractRelativeFixedFieldUnitsEquivGaloisFixed
      k Ω K L hLK).symm

omit [IsGalois k Ω] in
/-- States the theorem `abstractRelativeUnitsEquiv_extensionUnitsEquiv`. -/
@[simp]
theorem abstractRelativeUnitsEquiv_extensionUnitsEquiv
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (x : (extensionFixedRepresentation (galoisAmbientUnitsRep k Ω)
      K L hLK hnormal).V) :
    abstractRelativeFixedFieldUnitsEquivGaloisFixed k Ω K L hLK
        (abstractExtensionFixedRepresentationUnitsEquiv
          k Ω K L hLK hnormal x) =
      extensionFixedRepresentationEquiv
        (galoisAmbientUnitsRep k Ω) K L hLK hnormal x := by
  exact (abstractRelativeFixedFieldUnitsEquivGaloisFixed
    k Ω K L hLK).apply_symm_apply
      (extensionFixedRepresentationEquiv
        (galoisAmbientUnitsRep k Ω) K L hLK hnormal x)

/-- On a quotient representative, the concrete relative Galois
automorphism is restriction of the same ambient automorphism. -/
theorem abstractExtensionQuotientEquivGaloisGroup_mk_apply_val
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (σ : K.toSubgroup)
    (x : abstractRelativeFixedField k Ω hLK) :
    letI := hnormal
    σ.1 (x : Ω) =
      (((abstractExtensionQuotientEquivGaloisGroup
          k Ω K L hLK hnormal
          (QuotientGroup.mk' (extensionSubgroup K L hLK) σ)) x :
        abstractRelativeFixedField k Ω hLK) : Ω) := by
  let := hnormal
  let : (abstractRelativeFixedField k Ω hLK).fixingSubgroup.Normal :=
    abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
  let H : ClosedSubgroup (Gal(Ω/abstractFixedField k Ω K)) :=
    closedFixingSubgroup (abstractFixedField k Ω K) Ω
      (abstractRelativeFixedField k Ω hLK)
  let : H.toSubgroup.Normal :=
    abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
  have hq :
      abstractExtensionQuotientEquivAmbient k Ω K L hLK hnormal
          (QuotientGroup.mk' (extensionSubgroup K L hLK) σ) =
        QuotientGroup.mk'
          (abstractRelativeFixedField k Ω hLK).fixingSubgroup
          (abstractSubgroupEquivGaloisGroup k Ω K σ) := by
    rfl
  rw [abstractExtensionQuotientEquivGaloisGroup, MulEquiv.trans_apply, hq,
    MulEquiv.trans_apply]
  change σ.1 (x : Ω) =
    ((((IntermediateField.equivOfEq
      (InfiniteGalois.fixedField_fixingSubgroup
        (abstractRelativeFixedField k Ω hLK))).autCongr
      (InfiniteGalois.normalAutEquivQuotient
        (closedFixingSubgroup (abstractFixedField k Ω K) Ω
          (abstractRelativeFixedField k Ω hLK))
        ((abstractSubgroupEquivGaloisGroup k Ω K σ :
            Gal(Ω/abstractFixedField k Ω K)) :
          Gal(Ω/abstractFixedField k Ω K) ⧸
            (abstractRelativeFixedField k Ω hLK).fixingSubgroup))) x :
      abstractRelativeFixedField k Ω hLK) : Ω)
  rw [InfiniteGalois.normalAutEquivQuotient_apply,
    AlgEquiv.autCongr_apply]
  simp only [AlgEquiv.trans_apply, IntermediateField.equivOfEq_symm,
    IntermediateField.equivOfEq_apply]
  change σ.1 (x : Ω) =
    (((AlgEquiv.restrictNormalHom
      (IntermediateField.fixedField H.toSubgroup)
      (abstractSubgroupEquivGaloisGroup k Ω K σ))
      ⟨(x : Ω), _⟩ : IntermediateField.fixedField H.toSubgroup) : Ω)
  rw [AlgEquiv.restrictNormalHom_apply]
  rfl

/-- The abstract coset action on an upper fixed-field unit is the ordinary
action of the corresponding concrete relative Galois automorphism. -/
theorem relativeCosetAction_abstractRelativeFixedFieldUnit_val
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (x : Additive (abstractRelativeFixedField k Ω hLK)ˣ)
    (q : K.toSubgroup ⧸ extensionSubgroup K L hLK) :
    letI := hnormal
    ((Additive.toMul
      (relativeCosetAction (galoisAmbientUnitsRep k Ω)
        K L hLK
        (abstractRelativeFixedFieldUnitsEquivGaloisFixed
          k Ω K L hLK x) q) : Ωˣ) : Ω) =
      (((Additive.toMul
        ((Rep.ofAlgebraAutOnUnits (abstractFixedField k Ω K)
          (abstractRelativeFixedField k Ω hLK)).ρ
            (abstractExtensionQuotientEquivGaloisGroup
              k Ω K L hLK hnormal q) x) :
          (abstractRelativeFixedField k Ω hLK)ˣ) :
        abstractRelativeFixedField k Ω hLK) : Ω) := by
  let := hnormal
  refine Quotient.inductionOn' q ?_
  intro σ
  rw [relativeCosetAction_mk]
  change σ.1 ((Additive.toMul x :
      (abstractRelativeFixedField k Ω hLK)ˣ) : Ω) = _
  exact abstractExtensionQuotientEquivGaloisGroup_mk_apply_val
    k Ω K L hLK hnormal σ
      (Additive.toMul x : (abstractRelativeFixedField k Ω hLK)ˣ)

/-- The carrier comparison intertwines the descended quotient action with
the actual relative Galois action. -/
theorem abstractExtensionFixedRepresentationUnitsEquiv_action
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (q : K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (x : (extensionFixedRepresentation (galoisAmbientUnitsRep k Ω)
      K L hLK hnormal).V) :
    letI := hnormal
    abstractExtensionFixedRepresentationUnitsEquiv k Ω K L hLK hnormal
        ((extensionFixedRepresentation (galoisAmbientUnitsRep k Ω)
          K L hLK hnormal).ρ q x) =
      (Rep.ofAlgebraAutOnUnits (abstractFixedField k Ω K)
        (abstractRelativeFixedField k Ω hLK)).ρ
          (abstractExtensionQuotientEquivGaloisGroup
            k Ω K L hLK hnormal q)
          (abstractExtensionFixedRepresentationUnitsEquiv
            k Ω K L hLK hnormal x) := by
  let := hnormal
  let eFixed := abstractRelativeFixedFieldUnitsEquivGaloisFixed
    k Ω K L hLK
  apply eFixed.injective
  rw [abstractRelativeUnitsEquiv_extensionUnitsEquiv]
  apply Subtype.ext
  apply Additive.ext
  apply Units.ext
  have haction := extensionFixedRepresentation_action_coe
    (galoisAmbientUnitsRep k Ω) K L hLK hnormal q x
  change
    ((Additive.toMul
      ((extensionFixedRepresentation (galoisAmbientUnitsRep k Ω)
        K L hLK hnormal).ρ q x).1 : Ωˣ) : Ω) = _
  rw [haction]
  rw [← abstractRelativeUnitsEquiv_extensionUnitsEquiv
    k Ω K L hLK hnormal x]
  exact relativeCosetAction_abstractRelativeFixedFieldUnit_val
    k Ω K L hLK hnormal
      (abstractExtensionFixedRepresentationUnitsEquiv
        k Ω K L hLK hnormal x) q

/-- Representation-level form of the fixed-field unit comparison.  The
concrete unit representation is reindexed along the canonical isomorphism
from the abstract class-formation quotient to the actual relative Galois group. -/
def abstractExtensionFixedRepresentationIsoUnitsRes
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal) :
    letI := hnormal
    extensionFixedRepresentation (galoisAmbientUnitsRep k Ω)
        K L hLK hnormal ≅
      Rep.res
        (abstractExtensionQuotientEquivGaloisGroup
          k Ω K L hLK hnormal).toMonoidHom
        (Rep.ofAlgebraAutOnUnits (abstractFixedField k Ω K)
          (abstractRelativeFixedField k Ω hLK)) := by
  letI := hnormal
  let e := abstractExtensionFixedRepresentationUnitsEquiv
    k Ω K L hLK hnormal
  refine Rep.mkIso (Representation.Equiv.mk e.toIntLinearEquiv ?_)
  intro q
  apply LinearMap.ext
  intro x
  exact abstractExtensionFixedRepresentationUnitsEquiv_action
    k Ω K L hLK hnormal q x

end
end LocalClassFieldTheory
