/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalTotalGradedActionCompatibility
import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalOldTangentialFiniteness
import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalTangentialSuccessors

/-!
Tangentially linear equivalences between canonical total pages and graded modules.
-/

namespace Stafford38.Characteristic.CanonicalGradedTangentialEquivalences

open Stafford38.Characteristic
open Stafford38.Characteristic.CanonicalFilteredTwoTerm
open Stafford38.Characteristic.CanonicalTotalGradedBridge
open Stafford38.Characteristic.CanonicalTotalGradedActionCompatibility
open Stafford38.Characteristic.CanonicalTangentialTotalAction
open Stafford38.Characteristic.CanonicalOldTangentialFiniteness
open Stafford38.Characteristic.CanonicalTangentialSymbolFiniteness
open Stafford38.Characteristic.CanonicalTangentialRingEquivalence
open Stafford38.Characteristic.CanonicalNormalSymbolFiniteness
open Stafford38.Characteristic.NormalSymbolPolynomial
open Stafford38.CharacteristicAssociatedGradedModule
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylPBWMonicBridge
open Stafford38.WeylQuotientTransport

noncomputable section

variable (k : Type*) [Field k] [Algebra ℚ k]
variable (n N : ℕ) (d : PresentedWeyl k (n + 1))
variable (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)

/-- The order-associated graded module of the canonical right-ideal quotient. -/
abbrev Graded := OrderAssociatedGradedModule k (presentedCanonicalRightIdeal (k := k) n N d)
/-- The polynomial ring in the tangential coordinate and momentum variables. -/
abbrev T := MvPolynomial (Fin n ⊕ Fin n) k

/-- The tangential polynomial action on the order-associated graded module. -/
local instance gradedModule : Module (T k n) (Graded k n N d) :=
  oldCoeffModule n (Graded k n N d)

attribute [local instance] sourceModule targetModule

omit [Algebra ℚ k] in
theorem graded_C_smul (c : k) (z : Graded k n N d) :
    (MvPolynomial.C c : T k n) • z = c • z := by
  change (((tangentialPolynomialActionHom (k := k) n).comp Polynomial.C).comp
      (oldSymbolTangentialAlgEquiv (k := k) n).toRingHom) (MvPolynomial.C c) • z = _
  have hC : (((tangentialPolynomialActionHom (k := k) n).comp Polynomial.C).comp
      (oldSymbolTangentialAlgEquiv (k := k) n).toRingHom) (MvPolynomial.C c) =
      (MvPolynomial.C c : SymbolRing k (n + 1)) := by
    simp [tangentialPolynomialActionHom, normalPolynomialActionHom,
      normalCoeffTangentialAlgEquiv, normalSymbolAlgEquiv,
      oldSymbolTangentialAlgEquiv]
  rw [hC]
  exact algebraMap_smul (SymbolRing k (n + 1)) c z

theorem sourceEquiv_map_smul (P : T k n)
    (z : (complex k n N d).SourceTotal 0) :
    sourceTotal0LinearEquivOrderAssociatedGraded k n N d (P • z) =
      P • sourceTotal0LinearEquivOrderAssociatedGraded k n N d z := by
  induction P using MvPolynomial.induction_on generalizing z with
  | C c =>
    rw [graded_C_smul]
    change sourceTotal0LinearEquivOrderAssociatedGraded k n N d
      (sourceAction k n N d 0 (MvPolynomial.C c) z) = _
    rw [sourceAction, commutingPolynomialAction_apply_C]
    exact (sourceTotal0LinearEquivOrderAssociatedGraded k n N d).map_smul c z
  | add P Q hP hQ => simp only [add_smul, map_add, hP, hQ]
  | mul_X P i hP =>
    rw [mul_smul, mul_smul, hP]
    congr 1
    change sourceTotal0LinearEquivOrderAssociatedGraded k n N d
      (sourceAction k n N d 0 (MvPolynomial.X i) z) = _
    rw [sourceAction, commutingPolynomialAction_apply_X,
      sourceEquiv_intertwines_generator]
    exact (oldCoeffModule_oldSymbol_X_action n (Graded k n N d) i _).symm

theorem targetEquiv_map_smul (P : T k n)
    (z : (complex k n N d).TargetTotal 0) :
    targetTotal0LinearEquivOrderAssociatedGraded k n N d (P • z) =
      P • targetTotal0LinearEquivOrderAssociatedGraded k n N d z := by
  induction P using MvPolynomial.induction_on generalizing z with
  | C c =>
    rw [graded_C_smul]
    change targetTotal0LinearEquivOrderAssociatedGraded k n N d
      (targetAction k n N d 0 (MvPolynomial.C c) z) = _
    rw [targetAction, commutingPolynomialAction_apply_C]
    exact (targetTotal0LinearEquivOrderAssociatedGraded k n N d).map_smul c z
  | add P Q hP hQ => simp only [add_smul, map_add, hP, hQ]
  | mul_X P i hP =>
    rw [mul_smul, mul_smul, hP]
    congr 1
    change targetTotal0LinearEquivOrderAssociatedGraded k n N d
      (targetAction k n N d 0 (MvPolynomial.X i) z) = _
    rw [targetAction, commutingPolynomialAction_apply_X,
      targetEquiv_intertwines_generator]
    exact (oldCoeffModule_oldSymbol_X_action n (Graded k n N d) i _).symm

/-- The tangential-linear identification of the degree-zero source total with the associated
graded module. -/
def sourceGradedEquiv :
    (complex k n N d).SourceTotal 0 ≃ₗ[T k n] Graded k n N d :=
  { (sourceTotal0LinearEquivOrderAssociatedGraded k n N d).toAddEquiv with
    map_smul' := sourceEquiv_map_smul k n N d }

/-- The tangential-linear identification of the degree-zero target total with the associated
graded module. -/
def targetGradedEquiv :
    (complex k n N d).TargetTotal 0 ≃ₗ[T k n] Graded k n N d :=
  { (targetTotal0LinearEquivOrderAssociatedGraded k n N d).toAddEquiv with
    map_smul' := targetEquiv_map_smul k n N d }


theorem gradedEquiv_drop (z : (complex k n N d).SourceTotal 0) :
    targetGradedEquiv k n N d (tangentialDrop k n N d 0 z) =
      oldCoordinateMap (k := k) n (Graded k n N d) (sourceGradedEquiv k n N d z) :=
  totalDrop_zero_intertwines_coordinate k n N d z

/-- The identification of the degree-zero drop kernel with the kernel of the tangential
coordinate action. -/
def zeroDropKernelEquiv :
    (tangentialDrop k n N d 0).ker ≃ₗ[T k n]
      (oldCoordinateMap (k := k) n (Graded k n N d)).ker :=
  LinearEquiv.ofBijective
    ((sourceGradedEquiv k n N d).toLinearMap.domRestrict
      (tangentialDrop k n N d 0).ker |>.codRestrict
        (oldCoordinateMap (k := k) n (Graded k n N d)).ker (fun z => by
          exact LinearMap.mem_ker.mpr (by
            change oldCoordinateMap (k := k) n (Graded k n N d)
              (sourceGradedEquiv k n N d z.val) = 0
            rw [← gradedEquiv_drop]
            simp only [LinearMap.mem_ker.mp z.property, map_zero])))
    (by
      constructor
      · intro a b hab
        exact Subtype.ext ((sourceGradedEquiv k n N d).injective
          (congrArg Subtype.val hab))
      · intro z
        refine ⟨⟨(sourceGradedEquiv k n N d).symm z, ?_⟩,
          Subtype.ext ((sourceGradedEquiv k n N d).apply_symm_apply z)⟩
        apply LinearMap.mem_ker.mpr
        apply (targetGradedEquiv k n N d).injective
        rw [gradedEquiv_drop, LinearEquiv.apply_symm_apply, map_zero]
        exact LinearMap.mem_ker.mp z.property)

theorem targetGradedEquiv_range :
    Submodule.map (targetGradedEquiv k n N d).toLinearMap
        (tangentialDrop k n N d 0).range =
      (oldCoordinateMap (k := k) n (Graded k n N d)).range := by
  ext z
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨sourceGradedEquiv k n N d a, (gradedEquiv_drop k n N d a).symm⟩
  · rintro ⟨a, rfl⟩
    refine ⟨tangentialDrop k n N d 0 ((sourceGradedEquiv k n N d).symm a),
      ⟨(sourceGradedEquiv k n N d).symm a, rfl⟩, ?_⟩
    simpa only [LinearEquiv.coe_toLinearMap, gradedEquiv_drop,
      LinearEquiv.apply_symm_apply]

/-- The identification of the degree-zero drop cokernel with the cokernel of the tangential
coordinate action. -/
def zeroDropCokernelEquiv :
    ((complex k n N d).TargetTotal 0 ⧸ (tangentialDrop k n N d 0).range)
      ≃ₗ[T k n] (Graded k n N d ⧸ (oldCoordinateMap (k := k) n (Graded k n N d)).range) :=
  Submodule.Quotient.equiv _ _ (targetGradedEquiv k n N d)
    (targetGradedEquiv_range k n N d)

/-- The first source total identified with the kernel of the tangential coordinate action. -/
def firstSourceGradedKernelEquiv :
    (complex k n N d).SourceTotal 1 ≃ₗ[T k n]
      (oldCoordinateMap (k := k) n (Graded k n N d)).ker :=
  tangentialSourceSuccEquiv k n N d 0 ≪≫ₗ zeroDropKernelEquiv k n N d

/-- The first target total identified with the cokernel of the tangential coordinate action. -/
def firstTargetGradedCokernelEquiv :
    (complex k n N d).TargetTotal 1 ≃ₗ[T k n]
      (Graded k n N d ⧸ (oldCoordinateMap (k := k) n (Graded k n N d)).range) :=
  tangentialTargetSuccEquiv k n N d 0 ≪≫ₗ zeroDropCokernelEquiv k n N d

include hd in
theorem first_pages_finite :
    Module.Finite (T k n) ((complex k n N d).SourceTotal 1) ∧
      Module.Finite (T k n) ((complex k n N d).TargetTotal 1) := by
  have hf := canonical_finite_old_coordinate_kernel_cokernel hd
  have : Module.Finite (T k n)
      (oldCoordinateMap (k := k) n (Graded k n N d)).ker := hf.1
  have : Module.Finite (T k n)
      (Graded k n N d ⧸ (oldCoordinateMap (k := k) n (Graded k n N d)).range) := hf.2
  exact ⟨Module.Finite.equiv (firstSourceGradedKernelEquiv k n N d).symm,
    Module.Finite.equiv (firstTargetGradedCokernelEquiv k n N d).symm⟩


end
end Stafford38.Characteristic.CanonicalGradedTangentialEquivalences
