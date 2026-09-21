/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalTangentialTotalAction
import LeanPool.Stafford38.Stafford38.Characteristic.FilteredTwoTermSuccessorNaturality

/-!
# Successor pages over the tangential symbol ring

The actual successor maps are tangential-linear. Their already proved
injectivity, surjectivity and exactness therefore give kernel and cokernel
equivalences over that ring, not just over the ground field.
-/

namespace Stafford38.Characteristic.CanonicalTangentialTotalAction

open Stafford38.Characteristic
open Stafford38.Characteristic.FilteredTwoTermPages
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylPBWMonicBridge

noncomputable section

variable (k : Type*) [Field k] [Algebra ℚ k]
variable (n N : ℕ) (d : PresentedWeyl k (n + 1))
variable (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)

attribute [local instance] sourceModule targetModule

theorem sourceSucc_intertwines_polynomials (r : ℕ)
    (P : MvPolynomial (Fin n ⊕ Fin n) k) :
    (complex k n N d hd).sourceTotalSuccMap r ∘ₗ sourceAction k n N d hd (r + 1) P =
      sourceAction k n N d hd r P ∘ₗ (complex k n N d hd).sourceTotalSuccMap r :=
  commutingPolynomialAction_intertwines _ _ _ _ _
    (fun i => (generator k n N d hd i).sourceTotalSuccMap_naturality r) P

theorem targetSucc_intertwines_polynomials (r : ℕ)
    (P : MvPolynomial (Fin n ⊕ Fin n) k) :
    (complex k n N d hd).targetTotalSuccMap r ∘ₗ targetAction k n N d hd r P =
      targetAction k n N d hd (r + 1) P ∘ₗ (complex k n N d hd).targetTotalSuccMap r :=
  commutingPolynomialAction_intertwines _ _ _ _ _
    (fun i => (generator k n N d hd i).targetTotalSuccMap_naturality r) P

def tangentialSourceSucc (r : ℕ) :
    (complex k n N d hd).SourceTotal (r + 1) →ₗ[MvPolynomial (Fin n ⊕ Fin n) k]
      (complex k n N d hd).SourceTotal r where
  toFun := (complex k n N d hd).sourceTotalSuccMap r
  map_add' := map_add _
  map_smul' P z := congrArg (fun f => f z)
    (sourceSucc_intertwines_polynomials k n N d hd r P)

def tangentialTargetSucc (r : ℕ) :
    (complex k n N d hd).TargetTotal r →ₗ[MvPolynomial (Fin n ⊕ Fin n) k]
      (complex k n N d hd).TargetTotal (r + 1) where
  toFun := (complex k n N d hd).targetTotalSuccMap r
  map_add' := map_add _
  map_smul' P z := congrArg (fun f => f z)
    (targetSucc_intertwines_polynomials k n N d hd r P)

theorem tangentialSourceSucc_injective (r : ℕ) :
    Function.Injective (tangentialSourceSucc k n N d hd r) :=
  (complex k n N d hd).totalSourceSuccMap_injective r

theorem tangentialSourceSucc_range (r : ℕ) :
    (tangentialSourceSucc k n N d hd r).range =
      (tangentialDrop k n N d hd r).ker := by
  ext z
  exact SetLike.ext_iff.mp ((complex k n N d hd).range_totalSourceSuccMap r) z

theorem tangentialTargetSucc_surjective (r : ℕ) :
    Function.Surjective (tangentialTargetSucc k n N d hd r) :=
  (DirectSum.lmap_surjective _).mpr ((complex k n N d hd).targetSuccMap_surjective r)

theorem tangentialTargetSucc_ker (r : ℕ) :
    (tangentialTargetSucc k n N d hd r).ker =
      (tangentialDrop k n N d hd r).range := by
  ext z
  exact SetLike.ext_iff.mp ((complex k n N d hd).ker_totalTargetSuccMap r) z

def tangentialSourceSuccEquiv (r : ℕ) :
    (complex k n N d hd).SourceTotal (r + 1) ≃ₗ[MvPolynomial (Fin n ⊕ Fin n) k]
      (tangentialDrop k n N d hd r).ker :=
  LinearEquiv.ofInjective (tangentialSourceSucc k n N d hd r)
      (tangentialSourceSucc_injective k n N d hd r) ≪≫ₗ
    LinearEquiv.ofEq _ _ (tangentialSourceSucc_range k n N d hd r)

def tangentialTargetSuccEquiv (r : ℕ) :
    (complex k n N d hd).TargetTotal (r + 1) ≃ₗ[MvPolynomial (Fin n ⊕ Fin n) k]
      ((complex k n N d hd).TargetTotal r ⧸ (tangentialDrop k n N d hd r).range) :=
  ((Submodule.quotEquivOfEq _ _ (tangentialTargetSucc_ker k n N d hd r).symm) ≪≫ₗ
    (tangentialTargetSucc k n N d hd r).quotKerEquivOfSurjective
      (tangentialTargetSucc_surjective k n N d hd r)).symm


end
end Stafford38.Characteristic.CanonicalTangentialTotalAction
