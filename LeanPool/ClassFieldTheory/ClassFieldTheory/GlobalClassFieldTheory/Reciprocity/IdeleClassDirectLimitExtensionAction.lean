/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitExtension
/-!
# Galois actions on rational fixed-field idele classes

Naturality of the fixed-field comparison for automorphisms and the
finite-extension Galois action.
-/

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open LocalClassFieldTheory
open CyclicCohomology

/-- The fixed-part comparison intertwines an automorphism of a finite
rational intermediate field with any lift to the rational absolute
Galois group. -/
theorem rationalIdeleClassEquivFixed_action_coe
    (E : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ E]
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (τ : E ≃ₐ[ℚ] E)
    (hστ : ∀ x : E,
      ((τ x : E) : SeparableClosure ℚ) =
        σ (x : SeparableClosure ℚ))
    (c : RelativeIdeleGroup.ClassGroup ℚ E) :
    rationalIdeleClassRepresentation.ρ σ
        (rationalIdeleClassEquivFixed E
          (Additive.ofMul
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := E) c))).1 =
      (rationalIdeleClassEquivFixed E
        (Additive.ofMul
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := E) (τ • c)))).1 := by
  change
    Additive.ofMul
        (σ • rationalIntermediateIdeleClassToDirectLimit E
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := E) c)) =
      Additive.ofMul
        (rationalIntermediateIdeleClassToDirectLimit E
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := E) (τ • c)))
  exact congrArg Additive.ofMul
    (rationalIntermediateIdeleClassToDirectLimit_conjugation
      E σ τ hστ c)

/-- The fixed-part idèle-class realization is natural under an
equivalence between two finite rational intermediate fields induced by
an automorphism of the rational separable closure. -/
theorem rationalIdeleClassEquivFixed_ambientAlgEquiv
    {E F : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ E] [FiniteDimensional ℚ F]
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (e : E ≃ₐ[ℚ] F)
    (hσe : ∀ x : E,
      ((e x : F) : SeparableClosure ℚ) =
        σ (x : SeparableClosure ℚ))
    (c : IdeleClassGroup E) :
    rationalIdeleClassRepresentation.ρ σ
        (rationalIdeleClassEquivFixed E
          (Additive.ofMul c)).1 =
      (rationalIdeleClassEquivFixed F
        (Additive.ofMul (ideleClassCongr e c))).1 := by
  change
    Additive.ofMul
        (σ • rationalIntermediateIdeleClassToDirectLimit E c) =
      Additive.ofMul
        (rationalIntermediateIdeleClassToDirectLimit F
          (ideleClassCongr e c))
  exact congrArg Additive.ofMul
    (rationalIntermediateIdeleClassToDirectLimit_ambientAlgEquiv
      σ e hσe c)

private theorem relativeIdeleClassBaseChangeAddEquiv_apply
    (E : Type) [Field E] [NumberField E]
    (c : Additive (RelativeIdeleGroup.ClassGroup ℚ E)) :
    (MulEquiv.toAdditive
      (_root_.relativeIdeleClassBaseChangeMulEquiv
        (K := ℚ) (L := E))) c =
      Additive.ofMul
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := E) (Additive.toMul c)) := by
  rfl

/-- The relative fixed-field comparison has the same underlying direct-limit
class as the intermediate-field comparison from which it is transported. -/
private theorem
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixed_coe
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [FiniteDimensional ℚ
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK)]
    [FiniteDimensional ℚ
      ((abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hLK).restrictScalars ℚ)]
    [NumberField
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK)]
    (c : Additive
      (IdeleClassGroup
        (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK))) :
    (rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional
        K L hLK c).1 =
      (rationalIdeleClassEquivFixed
        ((abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) hLK).restrictScalars ℚ) c).1 := by
  rfl

private theorem
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixed_baseChange_coe
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [FiniteDimensional ℚ
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK)]
    [FiniteDimensional ℚ
      ((abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hLK).restrictScalars ℚ)]
    [NumberField
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK)]
    (c : Additive
      (RelativeIdeleGroup.ClassGroup ℚ
        (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK))) :
    (rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional
      K L hLK
      ((MulEquiv.toAdditive
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ)
          (L := abstractRelativeFixedField
            ℚ (SeparableClosure ℚ) hLK))) c)).1 =
      (rationalIdeleClassEquivFixed
        ((abstractRelativeFixedField
          ℚ (SeparableClosure ℚ) hLK).restrictScalars ℚ)
        (Additive.ofMul
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ)
            (L := abstractRelativeFixedField
              ℚ (SeparableClosure ℚ) hLK)
            (Additive.toMul c)))).1 := by
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  let eFixed :=
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional
      K L hLK
  let eRelative :=
    MulEquiv.toAdditive
      (_root_.relativeIdeleClassBaseChangeMulEquiv
        (K := ℚ) (L := E))
  calc
    (eFixed (eRelative c)).1 =
        (rationalIdeleClassEquivFixed
          (E.restrictScalars ℚ) (eRelative c)).1 :=
      rationalAbstractRelativeFixedFieldIdeleClassEquivFixed_coe
        K L hLK (eRelative c)
    _ = (rationalIdeleClassEquivFixed
          (E.restrictScalars ℚ)
          (Additive.ofMul
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := E) (Additive.toMul c)))).1 :=
      congrArg
        (fun d =>
          (rationalIdeleClassEquivFixed
            (E.restrictScalars ℚ) d).1)
        (relativeIdeleClassBaseChangeAddEquiv_apply E c)

private theorem
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixed_action_baseChange_coe
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [FiniteDimensional ℚ
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK)]
    [FiniteDimensional ℚ
      ((abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hLK).restrictScalars ℚ)]
    [NumberField
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK)]
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (τ₀ :
      abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK ≃ₐ[ℚ]
        abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK)
    (hστ : ∀ y : abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hLK,
      ((τ₀ y : abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hLK) : SeparableClosure ℚ) =
        σ (y : SeparableClosure ℚ))
    (c : Additive
      (RelativeIdeleGroup.ClassGroup ℚ
        (abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK))) :
    let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
    let eFixed :=
      rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional
        K L hLK
    let eRelative :=
      MulEquiv.toAdditive
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := E))
    rationalIdeleClassRepresentation.ρ σ
        (eFixed (eRelative c)).1 =
      (eFixed
        (eRelative
          (Additive.ofMul
            (τ₀ • Additive.toMul c)))).1 := by
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  let eFixed :=
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional
      K L hLK
  let eRelative :=
    MulEquiv.toAdditive
      (_root_.relativeIdeleClassBaseChangeMulEquiv
        (K := ℚ) (L := E))
  let E₀ := E.restrictScalars ℚ
  let τQ : E₀ ≃ₐ[ℚ] E₀ := τ₀
  let cRelQ : RelativeIdeleGroup.ClassGroup ℚ E₀ :=
    Additive.toMul c
  let cQ : IdeleClassGroup E₀ :=
    _root_.relativeIdeleClassBaseChangeMulEquiv
      (K := ℚ) (L := E₀) cRelQ
  let cτRelQ : RelativeIdeleGroup.ClassGroup ℚ E₀ :=
    τQ • cRelQ
  let cτQ : IdeleClassGroup E₀ :=
    _root_.relativeIdeleClassBaseChangeMulEquiv
      (K := ℚ) (L := E₀) cτRelQ
  have hστQ : ∀ y : E₀,
      ((τQ y : E₀) : SeparableClosure ℚ) =
        σ (y : SeparableClosure ℚ) := by
    exact hστ
  have hAction :=
    rationalIdeleClassEquivFixed_ambientAlgEquiv
      (E := E₀) (F := E₀)
      σ τQ hστQ cQ
  have hLeft :
      (eFixed (eRelative c)).1 =
        (rationalIdeleClassEquivFixed
          E₀ (Additive.ofMul cQ)).1 := by
    exact
      rationalAbstractRelativeFixedFieldIdeleClassEquivFixed_baseChange_coe
        K L hLK c
  have hCongr :
      ideleClassCongr τQ cQ = cτQ := by
    exact
      (_root_.relativeIdeleClassBaseChangeMulEquiv_smul_congr
        τQ cRelQ).symm
  have hcτRaw :
      cτQ =
        _root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := E)
          (τ₀ • Additive.toMul c) := by
    rfl
  have hRight :
      (rationalIdeleClassEquivFixed
        E₀ (Additive.ofMul (ideleClassCongr τQ cQ))).1 =
        (eFixed
          (eRelative
            (Additive.ofMul
              (τ₀ • Additive.toMul c)))).1 := by
    calc
      _ = (rationalIdeleClassEquivFixed
            E₀ (Additive.ofMul cτQ)).1 :=
        congrArg
          (fun d =>
            (rationalIdeleClassEquivFixed
              E₀ (Additive.ofMul d)).1)
          hCongr
      _ = (rationalIdeleClassEquivFixed
            E₀
            (Additive.ofMul
              (_root_.relativeIdeleClassBaseChangeMulEquiv
                (K := ℚ) (L := E)
                (τ₀ • Additive.toMul c)))).1 :=
        congrArg
          (fun d =>
            (rationalIdeleClassEquivFixed
              E₀ (Additive.ofMul d)).1)
          hcτRaw
      _ = _ :=
        (rationalAbstractRelativeFixedFieldIdeleClassEquivFixed_baseChange_coe
          K L hLK
          (Additive.ofMul
            (τ₀ • Additive.toMul c))).symm
  calc
    rationalIdeleClassRepresentation.ρ σ
        (eFixed (eRelative c)).1 =
        rationalIdeleClassRepresentation.ρ σ
          (rationalIdeleClassEquivFixed
            E₀ (Additive.ofMul cQ)).1 :=
      congrArg (rationalIdeleClassRepresentation.ρ σ) hLeft
    _ = (rationalIdeleClassEquivFixed
          E₀
          (Additive.ofMul
            (ideleClassCongr τQ cQ))).1 :=
      hAction
    _ = _ := hRight

private theorem
    rationalAbstractExtensionIdeleClassEquiv_action_fixed_mk
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (σ : K.toSubgroup)
    (x : (extensionFixedRepresentation rationalIdeleClassRepresentation
      K L hLK hnormal).V) :
    let F := abstractFixedField ℚ (SeparableClosure ℚ) K
    let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
    letI := hnormal
    letI : FiniteDimensional ℚ F :=
      abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K hKfinite
    letI : FiniteDimensional F E :=
      abstractRelativeFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
    letI : IsScalarTower ℚ F E :=
      IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
    letI : FiniteDimensional ℚ E :=
      FiniteDimensional.trans ℚ F E
    letI : NumberField F := NumberField.of_module_finite ℚ F
    letI : NumberField E := NumberField.of_module_finite ℚ E
    let M :=
      extensionFixedRepresentation rationalIdeleClassRepresentation
        K L hLK hnormal
    let eAmbient :=
      extensionFixedRepresentationEquiv
        rationalIdeleClassRepresentation K L hLK hnormal
    let eFixed :=
      rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional K L hLK
    let eRelative :=
      MulEquiv.toAdditive
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := E))
    let eQ :=
      abstractExtensionQuotientEquivGaloisGroup
        ℚ (SeparableClosure ℚ) K L hLK hnormal
    let τ : E ≃ₐ[F] E :=
      eQ (QuotientGroup.mk' (extensionSubgroup K L hLK) σ)
    let τ₀ : E ≃ₐ[ℚ] E := τ.restrictScalars ℚ
    let c : Additive (RelativeIdeleGroup.ClassGroup ℚ E) :=
      eRelative.symm (eFixed.symm (eAmbient x))
    eAmbient
        (M.ρ
          (QuotientGroup.mk' (extensionSubgroup K L hLK) σ) x) =
      eFixed
        (eRelative
          (Additive.ofMul (τ₀ • Additive.toMul c))) := by
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  let := hnormal
  let : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  let : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  let : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  let : NumberField F := NumberField.of_module_finite ℚ F
  let : NumberField E := NumberField.of_module_finite ℚ E
  let : FiniteDimensional ℚ (E.restrictScalars ℚ) := by
    change FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) L)
    change FiniteDimensional ℚ E
    infer_instance
  let M :=
    extensionFixedRepresentation rationalIdeleClassRepresentation
      K L hLK hnormal
  let eAmbient :=
    extensionFixedRepresentationEquiv
      rationalIdeleClassRepresentation K L hLK hnormal
  let eFixed :=
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional K L hLK
  let eRelative :=
    MulEquiv.toAdditive
      (_root_.relativeIdeleClassBaseChangeMulEquiv
        (K := ℚ) (L := E))
  let eQ :=
    abstractExtensionQuotientEquivGaloisGroup
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  let τ : E ≃ₐ[F] E :=
    eQ (QuotientGroup.mk' (extensionSubgroup K L hLK) σ)
  let τ₀ : E ≃ₐ[ℚ] E := τ.restrictScalars ℚ
  let c : Additive (RelativeIdeleGroup.ClassGroup ℚ E) :=
    eRelative.symm (eFixed.symm (eAmbient x))
  have hc :
      eFixed (eRelative c) = eAmbient x := by
    calc
      eFixed (eRelative c) =
          eFixed (eFixed.symm (eAmbient x)) :=
        congrArg eFixed
          (eRelative.apply_symm_apply
            (eFixed.symm (eAmbient x)))
      _ = eAmbient x :=
        eFixed.apply_symm_apply (eAmbient x)
  have hστ : ∀ y : E,
      ((τ₀ y : E) : SeparableClosure ℚ) =
        σ.1 (y : SeparableClosure ℚ) := by
    intro y
    change
      ((τ y : E) : SeparableClosure ℚ) =
        σ.1 (y : SeparableClosure ℚ)
    simpa only [τ, eQ] using
      (abstractExtensionQuotientEquivGaloisGroup_mk_apply_val
        ℚ (SeparableClosure ℚ) K L hLK hnormal σ y).symm
  apply Subtype.ext
  calc
    (eAmbient
        (M.ρ
          (QuotientGroup.mk' (extensionSubgroup K L hLK) σ) x)).1 =
        relativeCosetAction rationalIdeleClassRepresentation
          K L hLK (eAmbient x)
          (QuotientGroup.mk'
            (extensionSubgroup K L hLK) σ) :=
      extensionFixedRepresentation_action_coe
        rationalIdeleClassRepresentation K L hLK hnormal
          (QuotientGroup.mk'
            (extensionSubgroup K L hLK) σ) x
    _ =
        rationalIdeleClassRepresentation.ρ σ.1
          (eAmbient x).1 := by
      change
        relativeCosetAction rationalIdeleClassRepresentation
            K L hLK (eAmbient x) (QuotientGroup.mk σ) =
          rationalIdeleClassRepresentation.ρ σ.1
            (eAmbient x).1
      exact
        relativeCosetAction_mk
          rationalIdeleClassRepresentation K L hLK
          (eAmbient x) σ
    _ =
        rationalIdeleClassRepresentation.ρ σ.1
          (eFixed (eRelative c)).1 := by
      rw [hc]
    _ =
        (eFixed
          (eRelative
            (Additive.ofMul
              (τ₀ • Additive.toMul c)))).1 := by
      exact
        rationalAbstractRelativeFixedFieldIdeleClassEquivFixed_action_baseChange_coe
          K L hLK σ.1 τ₀ hστ c

private theorem rationalTowerRelativeIdeleClassBaseChangeAddEquiv_smul
    (F E : Type)
    [Field F] [NumberField F]
    [Field E] [NumberField E]
    [Algebra ℚ F] [Algebra F E] [Algebra ℚ E]
    [IsScalarTower ℚ F E]
    [FiniteDimensional ℚ F] [FiniteDimensional F E]
    (τ : E ≃ₐ[F] E)
    (c : Additive (RelativeIdeleGroup.ClassGroup ℚ E)) :
    let eTower :
        Additive (RelativeIdeleGroup.ClassGroup ℚ E) ≃+
          Additive (RelativeIdeleGroup.ClassGroup F E) :=
      (MulEquiv.toAdditive
        (TowerRelativeIdeleGroup.classGroupEquiv
          ℚ F E).symm).trans
        (MulEquiv.toAdditive
          (towerRelativeIdeleClassBaseChangeMulEquiv
            ℚ F E))
    eTower
        (Additive.ofMul
          ((τ.restrictScalars ℚ) • Additive.toMul c)) =
      Additive.ofMul
        (τ • Additive.toMul (eTower c)) := by
  let eTower :
      Additive (RelativeIdeleGroup.ClassGroup ℚ E) ≃+
        Additive (RelativeIdeleGroup.ClassGroup F E) :=
    (MulEquiv.toAdditive
      (TowerRelativeIdeleGroup.classGroupEquiv
        ℚ F E).symm).trans
      (MulEquiv.toAdditive
        (towerRelativeIdeleClassBaseChangeMulEquiv
          ℚ F E))
  apply Additive.toMul.injective
  change
    towerRelativeIdeleClassBaseChangeMulEquiv ℚ F E
        ((TowerRelativeIdeleGroup.classGroupEquiv ℚ F E).symm
          ((τ.restrictScalars ℚ) • Additive.toMul c)) =
      τ •
        towerRelativeIdeleClassBaseChangeMulEquiv ℚ F E
          ((TowerRelativeIdeleGroup.classGroupEquiv ℚ F E).symm
            (Additive.toMul c))
  exact
    towerRelativeIdeleClassBaseChangeMulEquiv_smul
      ℚ F E τ (Additive.toMul c)

private theorem addEquiv_trans_symm_trans_symm_trans_apply_eq
    {V A B C D : Type*}
    [Add V] [Add A] [Add B] [Add C] [Add D]
    (eV : V ≃+ D) (eB : B ≃+ D)
    (eA : A ≃+ B) (eC : A ≃+ C)
    {y : V} {z : A} {w : C}
    (h : eV y = eB (eA z))
    (ht : eC z = w) :
    (((eV.trans eB.symm).trans eA.symm).trans eC) y = w := by
  change eC (eA.symm (eB.symm (eV y))) = w
  rw [h, eB.symm_apply_apply, eA.symm_apply_apply]
  exact ht

private theorem rationalAbstractExtensionIdeleClassEquiv_action_mk
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (σ : K.toSubgroup)
    (x : (extensionFixedRepresentation rationalIdeleClassRepresentation
      K L hLK hnormal).V) :
    let F := abstractFixedField ℚ (SeparableClosure ℚ) K
    let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
    letI := hnormal
    letI : FiniteDimensional ℚ F :=
      abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K hKfinite
    letI : FiniteDimensional F E :=
      abstractRelativeFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
    letI : IsScalarTower ℚ F E :=
      IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
    letI : FiniteDimensional ℚ E :=
      FiniteDimensional.trans ℚ F E
    letI : NumberField F := NumberField.of_module_finite ℚ F
    letI : NumberField E := NumberField.of_module_finite ℚ E
    letI : IsGalois F E :=
      abstractRelativeFixedField_isGalois
        ℚ (SeparableClosure ℚ) K L hLK hnormal
    letI : MulDistribMulAction (E ≃ₐ[F] E)
        (RelativeIdeleGroup.ClassGroup F E) :=
      RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction F E
    rationalAbstractExtensionIdeleClassEquiv K L hLK hnormal
        ((extensionFixedRepresentation rationalIdeleClassRepresentation
          K L hLK hnormal).ρ
            (QuotientGroup.mk'
              (extensionSubgroup K L hLK) σ) x) =
      (Rep.ofMulDistribMulAction (E ≃ₐ[F] E)
        (RelativeIdeleGroup.ClassGroup F E)).ρ
          (abstractExtensionQuotientEquivGaloisGroup
            ℚ (SeparableClosure ℚ) K L hLK hnormal
            (QuotientGroup.mk'
              (extensionSubgroup K L hLK) σ))
          (rationalAbstractExtensionIdeleClassEquiv
            K L hLK hnormal x) := by
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  let := hnormal
  let : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  let : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  let : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  let : NumberField F := NumberField.of_module_finite ℚ F
  let : NumberField E := NumberField.of_module_finite ℚ E
  let : FiniteDimensional ℚ (E.restrictScalars ℚ) := by
    change FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) L)
    change FiniteDimensional ℚ E
    infer_instance
  let : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  let : MulDistribMulAction (E ≃ₐ[F] E)
      (RelativeIdeleGroup.ClassGroup F E) :=
    RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction F E
  let M :=
    extensionFixedRepresentation rationalIdeleClassRepresentation
      K L hLK hnormal
  let eAmbient :=
    extensionFixedRepresentationEquiv
      rationalIdeleClassRepresentation K L hLK hnormal
  let eFixed :
      Additive (IdeleClassGroup E) ≃+
        KummerTheory.ambientFixedAddSubgroup
          rationalIdeleClassRepresentation L :=
    rationalAbstractRelativeFixedFieldIdeleClassEquivFixedOfFiniteDimensional K L hLK
  let eRelative :
      Additive (RelativeIdeleGroup.ClassGroup ℚ E) ≃+
        Additive (IdeleClassGroup E) :=
    MulEquiv.toAdditive
      (_root_.relativeIdeleClassBaseChangeMulEquiv
        (K := ℚ) (L := E))
  let eTower :
      Additive (RelativeIdeleGroup.ClassGroup ℚ E) ≃+
        Additive (RelativeIdeleGroup.ClassGroup F E) :=
    (MulEquiv.toAdditive
      (TowerRelativeIdeleGroup.classGroupEquiv
        ℚ F E).symm).trans
      (MulEquiv.toAdditive
        (towerRelativeIdeleClassBaseChangeMulEquiv
          ℚ F E))
  let eQ :=
    abstractExtensionQuotientEquivGaloisGroup
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  let τ : E ≃ₐ[F] E :=
    eQ (QuotientGroup.mk' (extensionSubgroup K L hLK) σ)
  let τ₀ : E ≃ₐ[ℚ] E := τ.restrictScalars ℚ
  let c : Additive (RelativeIdeleGroup.ClassGroup ℚ E) :=
    eRelative.symm (eFixed.symm (eAmbient x))
  change
    (((eAmbient.trans eFixed.symm).trans eRelative.symm).trans eTower)
        (M.ρ
          (QuotientGroup.mk'
            (extensionSubgroup K L hLK) σ) x) =
      Additive.ofMul
        (τ • Additive.toMul
          (eTower
            (eRelative.symm
              (eFixed.symm (eAmbient x)))))
  apply addEquiv_trans_symm_trans_symm_trans_apply_eq
      eAmbient eFixed eRelative eTower
      (z := Additive.ofMul (τ₀ • Additive.toMul c))
  · exact
      rationalAbstractExtensionIdeleClassEquiv_action_fixed_mk
        K L hLK hnormal σ x
  · simpa only [eTower, τ₀, c] using
      (rationalTowerRelativeIdeleClassBaseChangeAddEquiv_smul
        F E τ c)

/-- The abstract quotient action on the rational absolute idele-class
representation becomes the ordinary Galois action on the relative idele
class group of the two concrete fixed fields. -/
theorem rationalAbstractExtensionIdeleClassEquiv_action
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    [hKfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          K (le_baseField K))]
    [hfinite : Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)]
    (q : K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (x : (extensionFixedRepresentation rationalIdeleClassRepresentation
      K L hLK hnormal).V) :
    let F := abstractFixedField ℚ (SeparableClosure ℚ) K
    let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
    letI := hnormal
    letI : FiniteDimensional ℚ F :=
      abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K hKfinite
    letI : FiniteDimensional F E :=
      abstractRelativeFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
    letI : IsScalarTower ℚ F E :=
      IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
    letI : FiniteDimensional ℚ E :=
      FiniteDimensional.trans ℚ F E
    letI : NumberField F := NumberField.of_module_finite ℚ F
    letI : NumberField E := NumberField.of_module_finite ℚ E
    letI : IsGalois F E :=
      abstractRelativeFixedField_isGalois
        ℚ (SeparableClosure ℚ) K L hLK hnormal
    letI : MulDistribMulAction (E ≃ₐ[F] E)
        (RelativeIdeleGroup.ClassGroup F E) :=
      RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction F E
    rationalAbstractExtensionIdeleClassEquiv K L hLK hnormal
        ((extensionFixedRepresentation rationalIdeleClassRepresentation
          K L hLK hnormal).ρ q x) =
      (Rep.ofMulDistribMulAction (E ≃ₐ[F] E)
        (RelativeIdeleGroup.ClassGroup F E)).ρ
          (abstractExtensionQuotientEquivGaloisGroup
            ℚ (SeparableClosure ℚ) K L hLK hnormal q)
          (rationalAbstractExtensionIdeleClassEquiv
            K L hLK hnormal x) := by
  let F := abstractFixedField ℚ (SeparableClosure ℚ) K
  let E := abstractRelativeFixedField ℚ (SeparableClosure ℚ) hLK
  let := hnormal
  let : FiniteDimensional ℚ F :=
    abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  let : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  let : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  let : NumberField F := NumberField.of_module_finite ℚ F
  let : NumberField E := NumberField.of_module_finite ℚ E
  let : FiniteDimensional ℚ (E.restrictScalars ℚ) := by
    change FiniteDimensional ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) L)
    change FiniteDimensional ℚ E
    infer_instance
  let : IsGalois F E :=
    abstractRelativeFixedField_isGalois
      ℚ (SeparableClosure ℚ) K L hLK hnormal
  let : MulDistribMulAction (E ≃ₐ[F] E)
      (RelativeIdeleGroup.ClassGroup F E) :=
    RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction F E
  refine Quotient.inductionOn' q ?_
  intro σ
  exact
    rationalAbstractExtensionIdeleClassEquiv_action_mk
      K L hLK hnormal σ x

end Reciprocity
end GlobalClassFieldTheory
