/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldUnits
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.HenselianValuationBase
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableFixedFieldNorm

/-! # Abstract Fixed Field Norm -/
namespace LocalClassFieldTheory
open RamificationTheory CyclicCohomology KummerTheory ClassFormation

open LocalFieldTheory

/-!
# Finite local reciprocity: the norm of an arbitrary finite abstract field

The abstract class-formation framework indexes finite fields by closed subgroups, whereas the local norm
calculation is stated for their concrete fixed intermediate fields.  This file
identifies the two presentations.  In particular, it does not assume that the
finite fixed field is normal over the local ground field.
-/

noncomputable section

open scoped ValuativeRel
variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω] [IsSepClosed Ω]

/-- The underlying value of a relative norm is unchanged when its two
closed-subgroup indices and its fixed coefficient are transported along
equalities.  Keeping this congruence explicit avoids dependent rewriting
through the inclusion proof carried by `relativeNorm`. -/
theorem relativeNorm_coe_eq_of_closedSubgroup_eq
    {G : Type} [Group G] [TopologicalSpace G]
    (A : Rep ℤ G)
    (B B' C C' : ClosedSubgroup G)
    (hCB : C.toSubgroup ≤ B.toSubgroup)
    (hC'B' : C'.toSubgroup ≤ B'.toSubgroup)
    [hfinite : Finite
      (B.toSubgroup ⧸ extensionSubgroup B C hCB)]
    [hfinite' : Finite
      (B'.toSubgroup ⧸ extensionSubgroup B' C' hC'B')]
    (hB : B = B') (hC : C = C')
    (x : ambientFixedAddSubgroup A C)
    (x' : ambientFixedAddSubgroup A C')
    (hx : x.1 = x'.1) :
    ((relativeNorm A B C hCB x : ambientFixedAddSubgroup A B) : A.V) =
      ((relativeNorm A B' C' hC'B' x' :
        ambientFixedAddSubgroup A B') : A.V) := by
  subst B'
  subst C'
  have hle : hCB = hC'B' := Subsingleton.elim _ _
  subst hC'B'
  have hfin : hfinite = hfinite' := Subsingleton.elim _ _
  subst hfinite'
  have hxx' : x = x' := Subtype.ext hx
  subst x'
  rfl

/-- For an arbitrary finite separable abstract field, the abstract class-formation norm on
fixed coefficients has the same underlying field element as the ordinary
field norm from its concrete fixed field. -/
theorem normToBase_abstractFixedFieldUnit_val_of_isSeparable
    (H : ClosedSubgroup (Gal(Ω / K)))
    [Finite ((baseField (Gal(Ω / K))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(Ω / K))) H (le_baseField H))]
    [FiniteDimensional K (abstractFixedField K Ω H)]
    [Algebra.IsSeparable K (abstractFixedField K Ω H)]
    (x : (abstractFixedField K Ω H)ˣ) :
    ((Additive.toMul
      ((normToBase (galoisAmbientUnitsRep K Ω) H
        (abstractFixedFieldUnitsEquivGaloisFixed K Ω H
          (Additive.ofMul x))).1 : Additive Ωˣ) : Ωˣ) : Ω) =
      algebraMap K Ω (Algebra.norm K
        (x : abstractFixedField K Ω H)) := by
  let E := abstractFixedField K Ω H
  let y : ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω) H :=
    abstractFixedFieldUnitsEquivGaloisFixed K Ω H (Additive.ofMul x)
  let yE := intermediateFieldUnitsEquivGaloisFixed K Ω E (Additive.ofMul x)
  have hy : yE.1 = y.1 := by
    rw [intermediateFieldUnitsEquivGaloisFixed_coe]
    exact (abstractFixedFieldUnitsEquivGaloisFixed_coe
      K Ω H (Additive.ofMul x)).symm
  have hnorm :=
    relativeNorm_intermediateFieldUnit_val_of_isSeparable K Ω E x
  have htransport := relativeNorm_coe_eq_of_closedSubgroup_eq
    (galoisAmbientUnitsRep K Ω)
    (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
    (baseField (Gal(Ω / K)))
    (closedFixingSubgroup K Ω E) H
    (fixingSubgroupLeBase K Ω E) (le_baseField H)
    (closedFixingSubgroup_bot_eq_baseField K Ω)
    (closedFixingSubgroup_abstractFixedField_eq K Ω H)
    yE y hy
  have htransport' := congrArg
    (fun z : Additive Ωˣ => ((Additive.toMul z : Ωˣ) : Ω)) htransport
  change
    ((Additive.toMul
      ((normToBase (galoisAmbientUnitsRep K Ω) H y).1 :
        Additive Ωˣ) : Ωˣ) : Ω) = _
  exact htransport'.symm.trans hnorm

/-- The base normalized valuation of the abstract norm is the ordinary
normalized valuation of the concrete field norm. -/
theorem localBaseValuation_normToBase_abstractFixedFieldUnit
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : ClosedSubgroup (Gal(SeparableClosure K / K)))
    [Finite ((baseField (Gal(SeparableClosure K / K))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(SeparableClosure K / K))) H
        (le_baseField H))]
    [FiniteDimensional K
      (abstractFixedField K (SeparableClosure K) H)]
    (x : (abstractFixedField K (SeparableClosure K) H)ˣ) :
    localBaseValuation K
        (normToBase
          (galoisAmbientUnitsRep K (SeparableClosure K)) H
          (abstractFixedFieldUnitsEquivGaloisFixed
            K (SeparableClosure K) H (Additive.ofMul x))) =
      Int.castRingHom ZHat
        (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
          (Additive.ofMul
            (normUnits K (abstractFixedField K (SeparableClosure K) H) x))) := by
  let E := abstractFixedField K (SeparableClosure K) H
  let a := normToBase
    (galoisAmbientUnitsRep K (SeparableClosure K)) H
    (abstractFixedFieldUnitsEquivGaloisFixed
      K (SeparableClosure K) H (Additive.ofMul x))
  have ha : (baseFieldUnitsEquiv K).symm a =
      Additive.ofMul (normUnits K E x) := by
    apply (baseFieldUnitsEquiv K).injective
    rw [(baseFieldUnitsEquiv K).apply_symm_apply]
    apply Subtype.ext
    apply Additive.ext
    apply Units.ext
    calc
      ((Additive.toMul
          ((normToBase
            (galoisAmbientUnitsRep K (SeparableClosure K)) H
            (abstractFixedFieldUnitsEquivGaloisFixed
              K (SeparableClosure K) H (Additive.ofMul x))).1 :
              Additive (SeparableClosure K)ˣ) :
            (SeparableClosure K)ˣ) : SeparableClosure K) =
          algebraMap K (SeparableClosure K)
            (Algebra.norm K (x : E)) :=
        normToBase_abstractFixedFieldUnit_val_of_isSeparable
          K (SeparableClosure K) H x
      _ = algebraMap K (SeparableClosure K)
          ((normUnits K E x : Kˣ) : K) := by
        rw [LocalFieldTheory.normUnits_apply_coe]
      _ =
          ((Additive.toMul
            ((baseFieldUnitsEquiv K
              (Additive.ofMul (normUnits K E x))).1 :
                Additive (SeparableClosure K)ˣ) :
              (SeparableClosure K)ˣ) : SeparableClosure K) :=
        (baseFieldUnitsEquiv_val K (normUnits K E x)).symm
  rw [show normToBase
      (galoisAmbientUnitsRep K (SeparableClosure K)) H
      (abstractFixedFieldUnitsEquivGaloisFixed
        K (SeparableClosure K) H (Additive.ofMul x)) = a from rfl]
  change Int.castRingHom ZHat
      (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
        ((baseFieldUnitsEquiv K).symm a)) = _
  rw [ha]

/-- For an arbitrary finite separable abstract field, the image of the
base valuation after the abstract class-formation norm is exactly the actual residue-degree
multiple of the base value group. -/
theorem localBaseValuation_comp_normToBase_range_eq_residueFinrank
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : ClosedSubgroup (Gal(SeparableClosure K / K)))
    [Finite ((baseField (Gal(SeparableClosure K / K))).toSubgroup ⧸
      extensionSubgroup (baseField (Gal(SeparableClosure K / K))) H
        (le_baseField H))]
    [FiniteDimensional K
      (abstractFixedField K (SeparableClosure K) H)]
    [ValuativeRel (abstractFixedField K (SeparableClosure K) H)]
    [TopologicalSpace (abstractFixedField K (SeparableClosure K) H)]
    [IsNonarchimedeanLocalField
      (abstractFixedField K (SeparableClosure K) H)]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation
        (abstractFixedField K (SeparableClosure K) H))]
    [hIntegralClosure : IsIntegralClosure
      𝒪[abstractFixedField K (SeparableClosure K) H] 𝒪[K]
      (abstractFixedField K (SeparableClosure K) H)] :
    ((localBaseValuation K).comp
      (normToBase
        (galoisAmbientUnitsRep K (SeparableClosure K)) H)).range =
      nsmulImage (localBaseValuation K).range
        (Module.finrank 𝓀[K]
          𝓀[abstractFixedField K (SeparableClosure K) H]) := by
  let f := Module.finrank 𝓀[K]
    𝓀[abstractFixedField K (SeparableClosure K) H]
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    let x : Additive
        (abstractFixedField K (SeparableClosure K) H)ˣ :=
      (abstractFixedFieldUnitsEquivGaloisFixed
        K (SeparableClosure K) H).symm a
    have hxa : abstractFixedFieldUnitsEquivGaloisFixed
        K (SeparableClosure K) H x = a :=
      (abstractFixedFieldUnitsEquivGaloisFixed
        K (SeparableClosure K) H).apply_symm_apply a
    rw [← hxa]
    change localBaseValuation K
      (normToBase (galoisAmbientUnitsRep K (SeparableClosure K)) H
        (abstractFixedFieldUnitsEquivGaloisFixed
          K (SeparableClosure K) H
            (Additive.ofMul (Additive.toMul x)))) ∈ _
    rw [localBaseValuation_normToBase_abstractFixedFieldUnit]
    have hnorm :=
      @v_normUnits_eq_residue_finrank_mul_of_isSeparable
        K (abstractFixedField K (SeparableClosure K) H)
          _ _ _ _ _ _ _ _ _ _ _ _ hIntegralClosure (Additive.toMul x)
    have hnorm' :
        LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
            (Additive.ofMul
              (normUnits K
                (abstractFixedField K (SeparableClosure K) H)
                (Additive.toMul x))) =
          (f : Int) *
            LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap
              (abstractFixedField K (SeparableClosure K) H) x := by
      exact hnorm
    rw [hnorm', mem_nsmulImage_iff]
    refine ⟨Int.castRingHom ZHat
        (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap
          (abstractFixedField K (SeparableClosure K) H) x),
      intToProCInteger_mem_localBaseValuation_range K _, ?_⟩
    rw [← map_nsmul]
    congr 1
  · rw [mem_nsmulImage_iff]
    rintro ⟨w, hw, hwz⟩
    rw [localBaseValuation_range K] at hw
    obtain ⟨m, rfl⟩ := hw
    obtain ⟨x, hx⟩ :=
      LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_surjective
        (abstractFixedField K (SeparableClosure K) H) m
    refine ⟨abstractFixedFieldUnitsEquivGaloisFixed
      K (SeparableClosure K) H x, ?_⟩
    change localBaseValuation K
      (normToBase (galoisAmbientUnitsRep K (SeparableClosure K)) H
        (abstractFixedFieldUnitsEquivGaloisFixed
          K (SeparableClosure K) H
            (Additive.ofMul (Additive.toMul x)))) = z
    rw [localBaseValuation_normToBase_abstractFixedFieldUnit]
    have hnorm :=
      @v_normUnits_eq_residue_finrank_mul_of_isSeparable
        K (abstractFixedField K (SeparableClosure K) H)
          _ _ _ _ _ _ _ _ _ _ _ _ hIntegralClosure (Additive.toMul x)
    have hnorm' :
        LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
            (Additive.ofMul
              (normUnits K
                (abstractFixedField K (SeparableClosure K) H)
                (Additive.toMul x))) =
          (f : Int) *
            LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap
              (abstractFixedField K (SeparableClosure K) H) x := by
      exact hnorm
    rw [hnorm', hx]
    calc
      Int.castRingHom ZHat
          ((f : Int) * m) =
          f • Int.castRingHom ZHat m := by
        rw [← map_nsmul]
        congr 1
      _ = z := hwz

end
end LocalClassFieldTheory
