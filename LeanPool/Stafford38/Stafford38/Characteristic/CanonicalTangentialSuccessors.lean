/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalTangentialTotalAction
public import LeanPool.Stafford38.Stafford38.Characteristic.FilteredTwoTermSuccessorNaturality


/-!
# Successor pages over the tangential symbol ring

The actual successor maps are tangential-linear. Their already proved
injectivity, surjectivity and exactness therefore give kernel and cokernel
equivalences over that ring, not just over the ground field.
-/

@[expose] public section

namespace Stafford38.Characteristic.CanonicalTangentialTotalAction

open Stafford38.Characteristic
open Stafford38.Characteristic.FilteredTwoTermPages
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylPBWMonicBridge

noncomputable section

variable (k : Type*) [Field k]
variable (n N : ℕ) (d : PresentedWeyl k (n + 1))

attribute [local instance] sourceModule targetModule

theorem sourceSucc_intertwines_polynomials (r : ℕ)
    (P : MvPolynomial (Fin n ⊕ Fin n) k) :
    (complex k n N d).sourceTotalSuccMap r ∘ₗ sourceAction k n N d (r + 1) P =
      sourceAction k n N d r P ∘ₗ (complex k n N d).sourceTotalSuccMap r :=
  commutingPolynomialAction_intertwines _ _ _ _ _
    (fun i => (generator k n N d i).sourceTotalSuccMap_naturality r) P

theorem targetSucc_intertwines_polynomials (r : ℕ)
    (P : MvPolynomial (Fin n ⊕ Fin n) k) :
    (complex k n N d).targetTotalSuccMap r ∘ₗ targetAction k n N d r P =
      targetAction k n N d (r + 1) P ∘ₗ (complex k n N d).targetTotalSuccMap r :=
  commutingPolynomialAction_intertwines _ _ _ _ _
    (fun i => (generator k n N d i).targetTotalSuccMap_naturality r) P

/-- The source transition map, linear for the tangential polynomial action. -/
def tangentialSourceSucc (r : ℕ) :
    (complex k n N d).SourceTotal (r + 1) →ₗ[MvPolynomial (Fin n ⊕ Fin n) k]
      (complex k n N d).SourceTotal r where
  toFun := (complex k n N d).sourceTotalSuccMap r
  map_add' := map_add _
  map_smul' P z := congrArg (fun f => f z)
    (sourceSucc_intertwines_polynomials k n N d r P)

/-- The target transition map, linear for the tangential polynomial action. -/
def tangentialTargetSucc (r : ℕ) :
    (complex k n N d).TargetTotal r →ₗ[MvPolynomial (Fin n ⊕ Fin n) k]
      (complex k n N d).TargetTotal (r + 1) where
  toFun := (complex k n N d).targetTotalSuccMap r
  map_add' := map_add _
  map_smul' P z := congrArg (fun f => f z)
    (targetSucc_intertwines_polynomials k n N d r P)

theorem tangentialSourceSucc_injective (r : ℕ) :
    Function.Injective (tangentialSourceSucc k n N d r) :=
  (complex k n N d).totalSourceSuccMap_injective r

theorem tangentialSourceSucc_range (r : ℕ) :
    (tangentialSourceSucc k n N d r).range =
      (tangentialDrop k n N d r).ker := by
  ext z
  exact SetLike.ext_iff.mp ((complex k n N d).range_totalSourceSuccMap r) z

theorem tangentialTargetSucc_surjective (r : ℕ) :
    Function.Surjective (tangentialTargetSucc k n N d r) :=
  (DirectSum.lmap_surjective _).mpr ((complex k n N d).targetSuccMap_surjective r)

theorem tangentialTargetSucc_ker (r : ℕ) :
    (tangentialTargetSucc k n N d r).ker =
      (tangentialDrop k n N d r).range := by
  ext z
  exact SetLike.ext_iff.mp ((complex k n N d).ker_totalTargetSuccMap r) z

/-- The source total module identified with the kernel of the tangential drop map. -/
def tangentialSourceSuccEquiv (r : ℕ) :
    (complex k n N d).SourceTotal (r + 1) ≃ₗ[MvPolynomial (Fin n ⊕ Fin n) k]
      (tangentialDrop k n N d r).ker :=
  LinearEquiv.ofInjective (tangentialSourceSucc k n N d r)
      (tangentialSourceSucc_injective k n N d r) ≪≫ₗ
    LinearEquiv.ofEq _ _ (tangentialSourceSucc_range k n N d r)

/-- The next target total module identified with the quotient by the tangential drop image. -/
def tangentialTargetSuccEquiv (r : ℕ) :
    (complex k n N d).TargetTotal (r + 1) ≃ₗ[MvPolynomial (Fin n ⊕ Fin n) k]
      ((complex k n N d).TargetTotal r ⧸ (tangentialDrop k n N d r).range) :=
  ((Submodule.quotEquivOfEq _ _ (tangentialTargetSucc_ker k n N d r).symm) ≪≫ₗ
    (tangentialTargetSucc k n N d r).quotKerEquivOfSurjective
      (tangentialTargetSucc_surjective k n N d r)).symm


end
end Stafford38.Characteristic.CanonicalTangentialTotalAction
