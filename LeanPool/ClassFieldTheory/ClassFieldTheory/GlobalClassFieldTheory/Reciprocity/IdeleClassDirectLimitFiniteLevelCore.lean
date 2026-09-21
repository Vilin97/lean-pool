/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitCore
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerBaseChange
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup
import Mathlib.GroupTheory.QuotientGroup.Defs
/-!
# Finite levels of the rational idele-class direct limit

Normal closures, finite-level scalar extension, tower base change, and the
canonical embeddings into the rational idele-class direct limit.
-/

open scoped NumberField TensorProduct
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open CyclicCohomology

attribute [local instance]
  relativeAdeleRingIntermediateAlgebra

local instance rationalIntermediateNumberField
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] : NumberField K :=
  NumberField.of_module_finite ℚ K

instance rationalTowerClassGroupCommGroup
    (K N : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ N]
    [Algebra K N] [IsScalarTower ℚ K N] [FiniteDimensional K N] :
    CommGroup (TowerRelativeIdeleGroup.ClassGroup ℚ K N) := by
  letI : CommGroup (TowerRelativeIdeleGroup ℚ K N) := inferInstance
  exact
    QuotientGroup.Quotient.commGroup
      (TowerRelativeIdeleGroup.principalSubgroup ℚ K N)

instance rationalTowerClassGroupMul
    (K N : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ N]
    [Algebra K N] [IsScalarTower ℚ K N] [FiniteDimensional K N] :
    Mul (TowerRelativeIdeleGroup.ClassGroup ℚ K N) := by
  letI : CommGroup (TowerRelativeIdeleGroup ℚ K N) := inferInstance
  exact
    (QuotientGroup.Quotient.commGroup
      (TowerRelativeIdeleGroup.principalSubgroup ℚ K N)).toMul

/-- The canonical finite Galois closure, inside `SeparableClosure ℚ`,
of a finite rational intermediate field. -/
noncomputable def rationalNormalClosure
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] :
    FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ) :=
  { IntermediateField.normalClosure
      ℚ K (SeparableClosure ℚ) with
    finiteDimensional :=
      normalClosure.is_finiteDimensional
        ℚ K (SeparableClosure ℚ)
    isGalois :=
      IsGalois.normalClosure ℚ K (SeparableClosure ℚ) }

/-- Absolute left cosets fixing a finite rational intermediate field,
identified with its embeddings into the canonical normal closure. -/
noncomputable def
    rationalBaseFixingCosetEquivNormalClosure
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] :
    ((RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ)
          (⊥ : IntermediateField ℚ (SeparableClosure ℚ))).toSubgroup ⧸
      extensionSubgroup
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ)
          (⊥ : IntermediateField ℚ (SeparableClosure ℚ)))
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ) K)
        (LocalClassFieldTheory.fixingSubgroupLeBase
          ℚ (SeparableClosure ℚ) K)) ≃
      (K →ₐ[ℚ] rationalNormalClosure K) :=
  (LocalClassFieldTheory.baseFixingCosetEquivAlgHom
      ℚ (SeparableClosure ℚ) K).trans
    (normalClosure.algHomEquiv
      (F := ℚ) (K := K) (L := SeparableClosure ℚ)).symm

/-- Embed the actual idele class group of a finite rational
intermediate field into the relative presentation at its canonical
finite Galois closure. -/
noncomputable def rationalIntermediateIdeleClassToNormalClosure
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] :
    IdeleClassGroup K →*
      RelativeIdeleGroup.ClassGroup ℚ (rationalNormalClosure K) :=
  (RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion (IntermediateField.le_normalClosure K))).comp
    (_root_.relativeIdeleClassBaseChangeMulEquiv
      (K := ℚ) (L := K)).symm.toMonoidHom

/-- The canonical map from the actual idele class group of a finite
rational intermediate field to the absolute idele-class direct limit. -/
noncomputable def rationalIntermediateIdeleClassToDirectLimit
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] :
    IdeleClassGroup K →* rationalIdeleClassDirectLimit :=
  (rationalRelativeIdeleClassToDirectLimit
      (rationalNormalClosure K)).comp
    (rationalIntermediateIdeleClassToNormalClosure K)

/-- Passing from the relative presentation of a finite rational
intermediate field to its ordinary idele class group commutes with the
canonical map to the absolute direct limit. -/
theorem
    rationalIntermediateIdeleClassToDirectLimit_baseChange
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K]
    (c : RelativeIdeleGroup.ClassGroup ℚ K) :
    rationalIntermediateIdeleClassToDirectLimit K
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := K) c) =
      rationalRelativeIdeleClassToDirectLimit
        (rationalNormalClosure K)
        (RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion (IntermediateField.le_normalClosure K)) c) := by
  simp only [rationalIntermediateIdeleClassToDirectLimit,
    rationalIntermediateIdeleClassToNormalClosure]
  change
    rationalRelativeIdeleClassToDirectLimit
        (rationalNormalClosure K)
        (RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion (IntermediateField.le_normalClosure K))
          ((_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := K)).symm
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := K) c))) =
      rationalRelativeIdeleClassToDirectLimit
        (rationalNormalClosure K)
        (RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion (IntermediateField.le_normalClosure K)) c)
  rw [(_root_.relativeIdeleClassBaseChangeMulEquiv
    (K := ℚ) (L := K)).symm_apply_apply]

/-- At a finite Galois rational intermediate field, the ordinary
idele-class comparison followed by the absolute direct-limit map is the
canonical finite-level map itself. -/
theorem
    rationalFiniteGaloisIdeleClassToDirectLimit_baseChange
    (E : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ))
    (c : RelativeIdeleGroup.ClassGroup ℚ E) :
    rationalIntermediateIdeleClassToDirectLimit
        (E : IntermediateField ℚ (SeparableClosure ℚ))
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := E) c) =
      rationalRelativeIdeleClassToDirectLimit E c := by
  rw [rationalIntermediateIdeleClassToDirectLimit_baseChange]
  exact rationalIdeleClassDirectLimit_mk_apply c
    (IntermediateField.le_normalClosure
      (E : IntermediateField ℚ (SeparableClosure ℚ)))

private theorem rationalRelativeIdeleClassEmbedding_commutativeSquare
    {F E N₁ N₂ : IntermediateField ℚ (SeparableClosure ℚ)}
    [NumberField F] [NumberField E] [NumberField N₁] [NumberField N₂]
    (hFE : F ≤ E) (hFN₁ : F ≤ N₁) (hEN₂ : E ≤ N₂) (hN₁N₂ : N₁ ≤ N₂)
    (c : RelativeIdeleGroup.ClassGroup ℚ F) :
    RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E) (M := N₂)
        (IntermediateField.inclusion hEN₂)
        (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := E)
          (IntermediateField.inclusion hFE) c) =
      RelativeIdeleGroup.classEmbedding (K := ℚ) (L := N₁) (M := N₂)
        (IntermediateField.inclusion hN₁N₂)
        (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := N₁)
          (IntermediateField.inclusion hFN₁) c) := by
  calc
    _ = RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := N₂)
        (IntermediateField.inclusion (hFE.trans hEN₂)) c :=
      rationalRelativeIdeleClassEmbedding_comp hFE hEN₂ c
    _ = RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := N₂)
        (IntermediateField.inclusion (hFN₁.trans hN₁N₂)) c := by
      rfl
    _ = _ :=
      (rationalRelativeIdeleClassEmbedding_comp hFN₁ hN₁N₂ c).symm

/-- The canonical maps from nested rational intermediate fields to the
idele-class direct limit agree after scalar extension. -/
theorem
    rationalIntermediateIdeleClassToDirectLimit_extension
    {F E : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ E]
    (hFE : F ≤ E)
    (c : RelativeIdeleGroup.ClassGroup ℚ F) :
    rationalIntermediateIdeleClassToDirectLimit E
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := E)
          (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := E)
            (IntermediateField.inclusion hFE) c)) =
      rationalIntermediateIdeleClassToDirectLimit F
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := F) c) := by
  let hFN :
      F ≤ (rationalNormalClosure F :
        IntermediateField ℚ (SeparableClosure ℚ)) :=
    IntermediateField.le_normalClosure F
  let hEN :
      E ≤ (rationalNormalClosure E :
        IntermediateField ℚ (SeparableClosure ℚ)) :=
    IntermediateField.le_normalClosure E
  let hN : rationalNormalClosure F ≤ rationalNormalClosure E :=
    IntermediateField.normalClosure_mono F E hFE
  have hcomp :
      RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E)
          (M := rationalNormalClosure E) (IntermediateField.inclusion hEN)
          (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := E)
            (IntermediateField.inclusion hFE) c) =
        RelativeIdeleGroup.classEmbedding (K := ℚ)
          (L := rationalNormalClosure F) (M := rationalNormalClosure E)
          (IntermediateField.inclusion hN)
          (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F)
            (M := rationalNormalClosure F)
            (IntermediateField.inclusion hFN) c) := by
    exact rationalRelativeIdeleClassEmbedding_commutativeSquare
      hFE hFN hEN hN c
  calc
    _ = rationalRelativeIdeleClassToDirectLimit (rationalNormalClosure E)
        (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := E)
          (M := rationalNormalClosure E) (IntermediateField.inclusion hEN)
          (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := E)
            (IntermediateField.inclusion hFE) c)) :=
      rationalIntermediateIdeleClassToDirectLimit_baseChange E
        (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F) (M := E)
          (IntermediateField.inclusion hFE) c)
    _ = rationalRelativeIdeleClassToDirectLimit (rationalNormalClosure E)
        (RelativeIdeleGroup.classEmbedding (K := ℚ)
          (L := rationalNormalClosure F) (M := rationalNormalClosure E)
          (IntermediateField.inclusion hN)
          (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F)
            (M := rationalNormalClosure F)
            (IntermediateField.inclusion hFN) c)) := by
      exact congrArg
        (rationalRelativeIdeleClassToDirectLimit (rationalNormalClosure E)) hcomp
    _ = rationalRelativeIdeleClassToDirectLimit (rationalNormalClosure F)
        (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F)
          (M := rationalNormalClosure F)
          (IntermediateField.inclusion hFN) c) :=
      rationalIdeleClassDirectLimit_mk_apply
        (RelativeIdeleGroup.classEmbedding (K := ℚ) (L := F)
          (M := rationalNormalClosure F)
          (IntermediateField.inclusion hFN) c)
        hN
    _ = _ :=
      (rationalIntermediateIdeleClassToDirectLimit_baseChange F c).symm


end Reciprocity
end GlobalClassFieldTheory
