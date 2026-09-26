/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitAbstractFixedField
/-!
# Finite extensions in the rational idele-class representation

The fixed representation of a finite abstract extension is compared with
the relative idele class group of its two actual fixed fields.
-/

@[expose] public section

noncomputable
section

namespace GlobalClassFieldTheory
namespace Reciprocity

private theorem rationalIdeleClassDirectLimit_smul_mk
    (E : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ))
    (c : RelativeIdeleGroup.ClassGroup ℚ E)
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) :
    σ • (⟦⟨E, c⟩⟧ : rationalIdeleClassDirectLimit) =
      (⟦⟨E, σ • c⟩⟧ : rationalIdeleClassDirectLimit) := rfl

open ClassFormation
open LocalClassFieldTheory
open CyclicCohomology

private noncomputable instance
    rationalAbstractTowerClassGroupCommGroup
    (F E : Type)
    [Field F]
    [Field E]
    [Algebra ℚ F] [Algebra F E] [Algebra ℚ E]
    :
    CommGroup (TowerRelativeIdeleGroup.ClassGroup ℚ F E) := by
  letI : CommGroup (TowerRelativeIdeleGroup ℚ F E) :=
    inferInstance
  exact
    QuotientGroup.Quotient.commGroup
      (TowerRelativeIdeleGroup.principalSubgroup ℚ F E)

private noncomputable instance
    rationalAbstractTowerClassGroupMul
    (F E : Type)
    [Field F] [NumberField F]
    [Field E] [NumberField E]
    [Algebra ℚ F] [Algebra F E] [Algebra ℚ E]
    [IsScalarTower ℚ F E]
    [FiniteDimensional ℚ F] [FiniteDimensional F E] :
    Mul (TowerRelativeIdeleGroup.ClassGroup ℚ F E) :=
  (rationalAbstractTowerClassGroupCommGroup F E).toMul

private noncomputable instance
    rationalAbstractTowerClassGroupMulOneClass
    (F E : Type)
    [Field F] [NumberField F]
    [Field E] [NumberField E]
    [Algebra ℚ F] [Algebra F E] [Algebra ℚ E]
    [IsScalarTower ℚ F E]
    [FiniteDimensional ℚ F] [FiniteDimensional F E] :
    MulOneClass (TowerRelativeIdeleGroup.ClassGroup ℚ F E) :=
  (rationalAbstractTowerClassGroupCommGroup F E).toMulOneClass

private noncomputable instance
    rationalAbstractRelativeClassGroupCommGroup
    (F E : Type)
    [Field F] [NumberField F]
    [Field E]
    [Algebra F E] :
    CommGroup (RelativeIdeleGroup.ClassGroup F E) := by
  letI : CommGroup (RelativeIdeleGroup F E) :=
    inferInstance
  exact
    QuotientGroup.Quotient.commGroup
      (RelativeIdeleGroup.principalSubgroup F E)

private noncomputable instance
    rationalAbstractRelativeClassGroupMul
    (F E : Type)
    [Field F] [NumberField F]
    [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] :
    Mul (RelativeIdeleGroup.ClassGroup F E) :=
  (rationalAbstractRelativeClassGroupCommGroup F E).toMul

private noncomputable instance
    rationalAbstractRelativeClassGroupMulOneClass
    (F E : Type)
    [Field F] [NumberField F]
    [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] :
    MulOneClass (RelativeIdeleGroup.ClassGroup F E) :=
  (rationalAbstractRelativeClassGroupCommGroup F E).toMulOneClass

/-- The coefficient representation attached to a finite abstract
extension is the existing relative idele class group of its two actual
fixed fields.  This packages the fixed-part and tower base-change
comparisons into the endpoint used by finite reciprocity. -/
noncomputable def rationalAbstractExtensionIdeleClassEquiv
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
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    let F :=
      LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) K
    let E :=
      LocalClassFieldTheory.abstractRelativeFixedField
        ℚ (SeparableClosure ℚ) hLK
    letI := hnormal
    letI : FiniteDimensional ℚ F :=
      LocalClassFieldTheory.abstractFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K hKfinite
    letI : FiniteDimensional F E :=
      LocalClassFieldTheory.abstractRelativeFixedField_finiteDimensional
        ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
    letI : IsScalarTower ℚ F E :=
      IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
    letI : FiniteDimensional ℚ E :=
      FiniteDimensional.trans ℚ F E
    letI : NumberField F := NumberField.of_module_finite ℚ F
    letI : NumberField E := NumberField.of_module_finite ℚ E
    (extensionFixedRepresentation rationalIdeleClassRepresentation
      K L hLK hnormal).V ≃+
      Additive (RelativeIdeleGroup.ClassGroup F E) := by
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) K
  let E :=
    LocalClassFieldTheory.abstractRelativeFixedField
      ℚ (SeparableClosure ℚ) hLK
  letI := hnormal
  letI : FiniteDimensional ℚ F :=
    LocalClassFieldTheory.abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K hKfinite
  letI : FiniteDimensional F E :=
    LocalClassFieldTheory.abstractRelativeFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) K L hLK hKfinite hfinite
  letI : IsScalarTower ℚ F E :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  letI : FiniteDimensional ℚ E :=
    FiniteDimensional.trans ℚ F E
  letI : NumberField F := NumberField.of_module_finite ℚ F
  letI : NumberField E := NumberField.of_module_finite ℚ E
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
    MulEquiv.toAdditive
      ((TowerRelativeIdeleGroup.classGroupEquiv
        ℚ F E).symm.trans
          (towerRelativeIdeleClassBaseChangeMulEquiv
            ℚ F E))
  exact
    (((extensionFixedRepresentationEquiv
      rationalIdeleClassRepresentation K L hLK hnormal).trans
        eFixed.symm).trans eRelative.symm).trans eTower

/-- In the direct-limit fixed-part comparison, one absolute left-coset
action is the idele-class embedding selected by the corresponding
embedding into the canonical normal closure. -/
theorem rationalIdeleClassEquivFixed_relativeCosetAction_coe
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K]
    (c : RelativeIdeleGroup.ClassGroup ℚ K)
    (q :
      (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ)
          (⊥ : IntermediateField ℚ (SeparableClosure ℚ))).toSubgroup ⧸
        extensionSubgroup
          (RamificationTheory.closedFixingSubgroup
            ℚ (SeparableClosure ℚ)
            (⊥ : IntermediateField ℚ (SeparableClosure ℚ)))
          (RamificationTheory.closedFixingSubgroup
            ℚ (SeparableClosure ℚ) K)
          (LocalClassFieldTheory.fixingSubgroupLeBase
            ℚ (SeparableClosure ℚ) K)) :
    (relativeCosetAction rationalIdeleClassRepresentation
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ)
          (⊥ : IntermediateField ℚ (SeparableClosure ℚ)))
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ) K)
        (LocalClassFieldTheory.fixingSubgroupLeBase
          ℚ (SeparableClosure ℚ) K)
        (rationalIdeleClassEquivFixed K
          (Additive.ofMul
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := K) c))) q :
      rationalIdeleClassRepresentation.V) =
    Additive.ofMul
      (rationalRelativeIdeleClassToDirectLimit
        (rationalNormalClosure K)
        (RelativeIdeleGroup.classEmbedding
          (rationalBaseFixingCosetEquivNormalClosure K q) c)) := by
  let hKN :
      K ≤ (rationalNormalClosure K :
        IntermediateField ℚ (SeparableClosure ℚ)) :=
    IntermediateField.le_normalClosure K
  refine Quotient.inductionOn' q ?_
  intro σ
  have hembedding :
      rationalBaseFixingCosetEquivNormalClosure K
          (QuotientGroup.mk σ) =
        (AlgEquiv.restrictNormalHom
            (rationalNormalClosure K) σ.1).toAlgHom.comp
          (IntermediateField.inclusion
            hKN) := by
    apply AlgHom.ext
    intro x
    apply Subtype.ext
    change
      σ.1 (x : SeparableClosure ℚ) =
        (((AlgEquiv.restrictNormalHom
          (rationalNormalClosure K) σ.1)
            (IntermediateField.inclusion
              hKN x) :
            rationalNormalClosure K) :
          SeparableClosure ℚ)
    exact
      (AlgEquiv.restrictNormal_commutes σ.1
        (rationalNormalClosure K)
        (IntermediateField.inclusion
          hKN x)).symm
  rw [hembedding]
  change
    Additive.ofMul
        (σ.1 •
          rationalIntermediateIdeleClassToDirectLimit K
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := K) c)) =
      Additive.ofMul
        (rationalRelativeIdeleClassToDirectLimit
          (rationalNormalClosure K)
          (RelativeIdeleGroup.classEmbedding
            ((AlgEquiv.restrictNormalHom
                (rationalNormalClosure K) σ.1).toAlgHom.comp
              (IntermediateField.inclusion
                hKN)) c))
  rw [show
      rationalIntermediateIdeleClassToDirectLimit K
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := K) c) =
        (⟦⟨rationalNormalClosure K,
          rationalIntermediateIdeleClassToNormalClosure K
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := K) c)⟩⟧ :
          rationalIdeleClassDirectLimit)
    from rfl,
    rationalIdeleClassDirectLimit_smul_mk]
  apply congrArg Additive.ofMul
  apply congrArg
    (fun d :
        RelativeIdeleGroup.ClassGroup ℚ (rationalNormalClosure K) =>
      (⟦⟨rationalNormalClosure K, d⟩⟧ :
        rationalIdeleClassDirectLimit))
  change
    (AlgEquiv.restrictNormalHom
        (rationalNormalClosure K) σ.1) •
      RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion hKN)
        ((_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := K)).symm
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := K) c)) =
      RelativeIdeleGroup.classEmbedding
        ((AlgEquiv.restrictNormalHom
            (rationalNormalClosure K) σ.1).toAlgHom.comp
          (IntermediateField.inclusion
            hKN)) c
  rw [(_root_.relativeIdeleClassBaseChangeMulEquiv
    (K := ℚ) (L := K)).symm_apply_apply]
  exact
    rationalRelativeIdeleClassEmbedding_smul_eq_classEmbedding
      hKN σ.1 c

/-- The abstract class-formation norm in the rational idele-class
direct limit is the ordinary relative idele-class norm, embedded at the
canonical normal closure. -/
theorem rationalIdeleClassEquivFixed_relativeNorm_coe
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K]
    (c : RelativeIdeleGroup.ClassGroup ℚ K) :
    (relativeNorm rationalIdeleClassRepresentation
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ)
          (⊥ : IntermediateField ℚ (SeparableClosure ℚ)))
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ) K)
        (LocalClassFieldTheory.fixingSubgroupLeBase
          ℚ (SeparableClosure ℚ) K)
        (rationalIdeleClassEquivFixed K
          (Additive.ofMul
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := K) c))) :
      KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ)
          (⊥ : IntermediateField ℚ (SeparableClosure ℚ)))).1 =
      Additive.ofMul
        (rationalRelativeIdeleClassToDirectLimit
          (rationalNormalClosure K)
          (RelativeIdeleGroup.classInclusion
            ℚ (rationalNormalClosure K)
            (RelativeIdeleGroup.Cohomology.ideleClassNorm ℚ K c))) := by
  classical
  let : Algebra K (rationalNormalClosure K) :=
    (IntermediateField.inclusion
      (IntermediateField.le_normalClosure K)).toRingHom.toAlgebra
  let : IsScalarTower ℚ K (rationalNormalClosure K) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let Q :=
    (RamificationTheory.closedFixingSubgroup
        ℚ (SeparableClosure ℚ)
        (⊥ : IntermediateField ℚ (SeparableClosure ℚ))).toSubgroup ⧸
      extensionSubgroup
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ)
          (⊥ : IntermediateField ℚ (SeparableClosure ℚ)))
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ) K)
        (LocalClassFieldTheory.fixingSubgroupLeBase
          ℚ (SeparableClosure ℚ) K)
  let := Fintype.ofFinite Q
  let term : Q → Additive rationalIdeleClassDirectLimit :=
    fun q =>
      (relativeCosetAction rationalIdeleClassRepresentation
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ)
          (⊥ : IntermediateField ℚ (SeparableClosure ℚ)))
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ) K)
        (LocalClassFieldTheory.fixingSubgroupLeBase
          ℚ (SeparableClosure ℚ) K)
        (rationalIdeleClassEquivFixed K
          (Additive.ofMul
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := K) c))) q :
        Additive rationalIdeleClassDirectLimit)
  have hterm (q : Q) :
      Additive.toMul (term q) =
        rationalRelativeIdeleClassToDirectLimit
          (rationalNormalClosure K)
          (RelativeIdeleGroup.classEmbedding
            (rationalBaseFixingCosetEquivNormalClosure K q) c) := by
    have h :=
      congrArg Additive.toMul
        (rationalIdeleClassEquivFixed_relativeCosetAction_coe
          K c q)
    exact h.trans (toMul_ofMul _)
  apply Additive.toMul.injective
  change
    Additive.toMul (∑ q : Q, term q) =
      rationalRelativeIdeleClassToDirectLimit
        (rationalNormalClosure K)
        (RelativeIdeleGroup.classInclusion
          ℚ (rationalNormalClosure K)
          (RelativeIdeleGroup.Cohomology.ideleClassNorm ℚ K c))
  rw [toMul_sum]
  calc
    ∏ q : Q,
        Additive.toMul (term q) =
        ∏ q : Q,
          rationalRelativeIdeleClassToDirectLimit
            (rationalNormalClosure K)
            (RelativeIdeleGroup.classEmbedding
              (rationalBaseFixingCosetEquivNormalClosure K q) c) := by
      apply Finset.prod_congr rfl
      intro q _
      exact hterm q
    _ =
        rationalRelativeIdeleClassToDirectLimit
          (rationalNormalClosure K)
          (∏ q : Q,
            RelativeIdeleGroup.classEmbedding
              (rationalBaseFixingCosetEquivNormalClosure K q) c) := by
      let g :=
        rationalRelativeIdeleClassToDirectLimit
          (rationalNormalClosure K)
      let f := fun q : Q =>
        RelativeIdeleGroup.classEmbedding
          (rationalBaseFixingCosetEquivNormalClosure K q) c
      have hmap (s : Finset Q) :
          g (s.prod f) =
            s.prod (fun q => g (f q)) := by
        induction s using Finset.induction_on with
        | empty =>
            exact g.map_one
        | @insert q s hqs ih =>
            rw [Finset.prod_insert hqs, Finset.prod_insert hqs,
              g.map_mul, ih]
      change
        (∏ q : Q, g (f q)) =
          g (∏ q : Q, f q)
      exact (hmap Finset.univ).symm
    _ =
        rationalRelativeIdeleClassToDirectLimit
          (rationalNormalClosure K)
          (∏ f : K →ₐ[ℚ] rationalNormalClosure K,
            RelativeIdeleGroup.classEmbedding f c) := by
      apply congrArg
        (rationalRelativeIdeleClassToDirectLimit
          (rationalNormalClosure K))
      exact
        Fintype.prod_equiv
          (rationalBaseFixingCosetEquivNormalClosure K)
          (fun q : Q =>
            RelativeIdeleGroup.classEmbedding
              (rationalBaseFixingCosetEquivNormalClosure K q) c)
          (fun f : K →ₐ[ℚ] rationalNormalClosure K =>
            RelativeIdeleGroup.classEmbedding f c)
          (fun _ => rfl)
    _ =
        rationalRelativeIdeleClassToDirectLimit
          (rationalNormalClosure K)
          (RelativeIdeleGroup.classInclusion
            ℚ (rationalNormalClosure K)
            (RelativeIdeleGroup.Cohomology.ideleClassNorm ℚ K c)) := by
      apply congrArg
        (rationalRelativeIdeleClassToDirectLimit
          (rationalNormalClosure K))
      have hnorm :
          RelativeIdeleGroup.Cohomology.ideleClassNorm ℚ K c =
            RelativeIdeleGroup.classNorm ℚ K c := by
        refine QuotientGroup.induction_on c ?_
        intro a
        rfl
      calc
        (∏ f : K →ₐ[ℚ] rationalNormalClosure K,
            RelativeIdeleGroup.classEmbedding f c) =
            RelativeIdeleGroup.classInclusion
              ℚ (rationalNormalClosure K)
              (RelativeIdeleGroup.classNorm ℚ K c) :=
          (RelativeIdeleGroup.classInclusion_ideleClassNorm_eq_prod_embeddings
            c).symm
        _ =
            RelativeIdeleGroup.classInclusion
              ℚ (rationalNormalClosure K)
              (RelativeIdeleGroup.Cohomology.ideleClassNorm ℚ K c) := by
          rw [hnorm]

/-- For a finite abstract rational field, the abstract norm to the base
has the ordinary relative idele-class norm as its underlying direct-limit
class.  The two closed-subgroup indices are transported through their
actual fixed fields; no new norm is introduced. -/
theorem
    rationalAbstractFixedFieldIdeleClassEquivFixed_normToBase_coe
    (H : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    [hfinite : Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          H (le_baseField H))]
    (c : RelativeIdeleGroup.ClassGroup ℚ
      (LocalClassFieldTheory.abstractFixedField
        ℚ (SeparableClosure ℚ) H)) :
    (normToBase rationalIdeleClassRepresentation H
        (rationalAbstractFixedFieldIdeleClassEquivFixed H
          (Additive.ofMul
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ)
              (L := LocalClassFieldTheory.abstractFixedField
                ℚ (SeparableClosure ℚ) H) c))) :
      KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation
        (baseField
          (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))).1 =
      Additive.ofMul
        (rationalRelativeIdeleClassToDirectLimit
          (rationalNormalClosure
            (LocalClassFieldTheory.abstractFixedField
              ℚ (SeparableClosure ℚ) H))
          (RelativeIdeleGroup.classInclusion
            ℚ
            (rationalNormalClosure
              (LocalClassFieldTheory.abstractFixedField
                ℚ (SeparableClosure ℚ) H))
            (RelativeIdeleGroup.Cohomology.ideleClassNorm ℚ
              (LocalClassFieldTheory.abstractFixedField
                ℚ (SeparableClosure ℚ) H) c))) := by
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H
  let : FiniteDimensional ℚ F :=
    LocalClassFieldTheory.abstractFixedField_finiteDimensional
      ℚ (SeparableClosure ℚ) H hfinite
  let x :
      KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ) F) :=
    rationalIdeleClassEquivFixed F
      (Additive.ofMul
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := F) c))
  let x' :
      KummerTheory.ambientFixedAddSubgroup
        rationalIdeleClassRepresentation H :=
    rationalAbstractFixedFieldIdeleClassEquivFixed H
      (Additive.ofMul
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := F) c))
  have hx : x.1 = x'.1 := by
    simpa only [x, x', F] using
      (rationalAbstractFixedFieldIdeleClassEquivFixed_coe H
        (Additive.ofMul
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := F) c))).symm
  have htransport :=
    LocalClassFieldTheory.relativeNorm_coe_eq_of_closedSubgroup_eq
      rationalIdeleClassRepresentation
      (RamificationTheory.closedFixingSubgroup
        ℚ (SeparableClosure ℚ)
        (⊥ : IntermediateField ℚ (SeparableClosure ℚ)))
      (baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
      (RamificationTheory.closedFixingSubgroup
        ℚ (SeparableClosure ℚ) F)
      H
      (LocalClassFieldTheory.fixingSubgroupLeBase
        ℚ (SeparableClosure ℚ) F)
      (le_baseField H)
      (LocalClassFieldTheory.closedFixingSubgroup_bot_eq_baseField
        ℚ (SeparableClosure ℚ))
      (LocalClassFieldTheory.closedFixingSubgroup_abstractFixedField_eq
        ℚ (SeparableClosure ℚ) H)
      x x' hx
  exact htransport.symm.trans
    (rationalIdeleClassEquivFixed_relativeNorm_coe F c)

section AbstractFixedFieldOrdinaryNorm

variable
    (H : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))

local instance rationalFiniteAbstractField_quotient_finite :
    Finite
      ((baseField
        (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)).toSubgroup ⧸
        extensionSubgroup
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
          H.field (le_baseField H.field)) :=
  H.finite

/-- Pulling the abstract base norm of an actual fixed-field idele class
back through the distinguished rational fixed-part equivalence is the
ordinary idele-class norm of that class. -/
theorem
    rationalAbstractFixedFieldNormToBase_eq_ordinaryIdeleClassNorm
    (c : Additive
      (IdeleClassGroup
        (LocalClassFieldTheory.abstractFixedField
          ℚ (SeparableClosure ℚ) H.field))) :
    rationalIdeleClassEquivBaseFixed.symm
        (normToBase rationalIdeleClassRepresentation H.field
          (rationalAbstractFixedFieldIdeleClassEquivFixed
            H.field c)) =
      Additive.ofMul
        (_root_.ideleClassNorm ℚ
          (LocalClassFieldTheory.abstractFixedField
            ℚ (SeparableClosure ℚ) H.field)
          (Additive.toMul c)) := by
  let F :=
    LocalClassFieldTheory.abstractFixedField
      ℚ (SeparableClosure ℚ) H.field
  let d : RelativeIdeleGroup.ClassGroup ℚ F :=
    (_root_.relativeIdeleClassBaseChangeMulEquiv
      (K := ℚ) (L := F)).symm (Additive.toMul c)
  have hc :
      _root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := F) d =
        Additive.toMul c := by
    simpa only [d] using
      ((_root_.relativeIdeleClassBaseChangeMulEquiv
        (K := ℚ) (L := F)).apply_symm_apply
        (Additive.toMul c))
  have hcoe :
      (normToBase rationalIdeleClassRepresentation H.field
          (rationalAbstractFixedFieldIdeleClassEquivFixed
            H.field c) :
        KummerTheory.ambientFixedAddSubgroup
          rationalIdeleClassRepresentation
          (baseField
            (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))).1 =
        Additive.ofMul
          (rationalRelativeIdeleClassToDirectLimit
            (rationalNormalClosure F)
            (RelativeIdeleGroup.classInclusion ℚ
              (rationalNormalClosure F)
              (RelativeIdeleGroup.Cohomology.ideleClassNorm
                ℚ F d))) := by
    have h :=
      rationalAbstractFixedFieldIdeleClassEquivFixed_normToBase_coe
        H.field d
    have hcAdd :
        Additive.ofMul
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := F) d) =
          c := by
      simpa only [ofMul_toMul] using congrArg Additive.ofMul hc
    rw [hcAdd] at h
    exact h
  have hordinary :
      _root_.ideleClassNorm ℚ F (Additive.toMul c) =
        RelativeIdeleGroup.Cohomology.ideleClassNorm ℚ F d := by
    rw [← hc]
    exact
      ordinaryIdeleClassNorm_relativeIdeleClassBaseChange d
  have hbase :=
    rationalIdeleClassEquivBaseFixed_coe
      (rationalNormalClosure F)
      (_root_.ideleClassNorm ℚ F (Additive.toMul c))
  have hcoe' := hcoe.trans
    (congrArg
      (fun x : IdeleClassGroup ℚ =>
        Additive.ofMul
          (rationalRelativeIdeleClassToDirectLimit
            (rationalNormalClosure F)
            (RelativeIdeleGroup.classInclusion ℚ
              (rationalNormalClosure F) x)))
      hordinary.symm)
  apply rationalIdeleClassEquivBaseFixed.injective
  calc
    rationalIdeleClassEquivBaseFixed
        (rationalIdeleClassEquivBaseFixed.symm
          (normToBase rationalIdeleClassRepresentation H.field
            (rationalAbstractFixedFieldIdeleClassEquivFixed H.field c))) =
      normToBase rationalIdeleClassRepresentation H.field
        (rationalAbstractFixedFieldIdeleClassEquivFixed H.field c) :=
      rationalIdeleClassEquivBaseFixed.apply_symm_apply _
    _ = rationalIdeleClassEquivBaseFixed
        (Additive.ofMul
          (_root_.ideleClassNorm ℚ F (Additive.toMul c))) := by
      apply Subtype.ext
      exact hcoe'.trans hbase.symm

end AbstractFixedFieldOrdinaryNorm

end Reciprocity
end GlobalClassFieldTheory
