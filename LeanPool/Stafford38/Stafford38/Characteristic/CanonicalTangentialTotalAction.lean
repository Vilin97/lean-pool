/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalTangentialPageOperators
import LeanPool.Stafford38.Stafford38.Characteristic.CommutingPolynomialAction

/-!
# Tangential symbol action on the canonical total pages

The commuting polynomial action is constructed from the actual right Weyl
generators. Their commutators have lower order and hence vanish on the pages.
-/

namespace Stafford38.Characteristic.CanonicalTangentialTotalAction

open Stafford38.Characteristic
open Stafford38.Characteristic.FilteredTwoTermPages
open Stafford38.Characteristic.CanonicalFilteredTwoTerm
open Stafford38.Characteristic.CanonicalTangentialPageOperators
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylPBWMonicBridge
open Stafford38.WeylQuotientTransport

noncomputable section

variable (k : Type*) [Field k] [Algebra ℚ k]
variable (n N : ℕ) (d : PresentedWeyl k (n + 1))
variable (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)

abbrev complex := canonicalFilteredTwoTerm k n N d hd

def generator (i : Fin n ⊕ Fin n) :
    (complex k n N d hd).PageOperator (tangentialDegree i : ℤ) :=
  match i with
  | .inl j => tangential_coordinate_pageOperator k n N d hd j
  | .inr j => tangential_momentum_pageOperator k n N d hd j

theorem generator_commutator_lowers (i j : Fin n ⊕ Fin n)
    (p : ℤ) (z : CanonicalQuotient k n N d)
    (hz : z ∈ (complex k n N d hd).G p) :
    (generator k n N d hd i).g ((generator k n N d hd j).g z) -
      (generator k n N d hd j).g ((generator k n N d hd i).g z) ∈
        (complex k n N d hd).G
          (p - (tangentialDegree i : ℤ) - (tangentialDegree j : ℤ) + 1) := by
  have h := tangential_commutator_lower k n N d hd i j p z hz
  cases i <;> cases j <;>
    simpa [generator, tangential_coordinate_pageOperator,
      tangential_momentum_pageOperator, tangentialPageOperator,
      tangentialDegree, show p - 1 - 1 + 1 = p - 2 + 1 by omega] using h

def sourceGenerator (r : ℕ) (i : Fin n ⊕ Fin n) :
    Module.End k ((complex k n N d hd).SourceTotal r) :=
  (generator k n N d hd i).sourceTotalMap r

def targetGenerator (r : ℕ) (i : Fin n ⊕ Fin n) :
    Module.End k ((complex k n N d hd).TargetTotal r) :=
  (generator k n N d hd i).targetTotalMap r

theorem sourceGenerator_commute (r : ℕ) (i j : Fin n ⊕ Fin n) :
    Commute (sourceGenerator k n N d hd r i) (sourceGenerator k n N d hd r j) :=
  (generator k n N d hd i).sourceTotalMap_commute_of_commutator_lowers
    (generator k n N d hd j) (generator_commutator_lowers k n N d hd i j) r

theorem targetGenerator_commute (r : ℕ) (i j : Fin n ⊕ Fin n) :
    Commute (targetGenerator k n N d hd r i) (targetGenerator k n N d hd r j) :=
  (generator k n N d hd i).targetTotalMap_commute_of_commutator_lowers
    (generator k n N d hd j) (generator_commutator_lowers k n N d hd i j) r

def sourceAction (r : ℕ) :
    MvPolynomial (Fin n ⊕ Fin n) k →ₐ[k]
      Module.End k ((complex k n N d hd).SourceTotal r) :=
  commutingPolynomialAction (sourceGenerator k n N d hd r)
    (sourceGenerator_commute k n N d hd r)

def targetAction (r : ℕ) :
    MvPolynomial (Fin n ⊕ Fin n) k →ₐ[k]
      Module.End k ((complex k n N d hd).TargetTotal r) :=
  commutingPolynomialAction (targetGenerator k n N d hd r)
    (targetGenerator_commute k n N d hd r)

theorem totalDrop_intertwines_polynomials (r : ℕ)
    (P : MvPolynomial (Fin n ⊕ Fin n) k) :
    (complex k n N d hd).totalDrop r ∘ₗ sourceAction k n N d hd r P =
      targetAction k n N d hd r P ∘ₗ (complex k n N d hd).totalDrop r :=
  commutingPolynomialAction_intertwines _ _ _ _ _
    (fun i => (generator k n N d hd i).totalDrop_intertwines r) P

@[instance_reducible] def sourceModule (r : ℕ) :
    Module (MvPolynomial (Fin n ⊕ Fin n) k)
      ((complex k n N d hd).SourceTotal r) :=
  Module.compHom _ (sourceAction k n N d hd r).toRingHom

@[instance_reducible] def targetModule (r : ℕ) :
    Module (MvPolynomial (Fin n ⊕ Fin n) k)
      ((complex k n N d hd).TargetTotal r) :=
  Module.compHom _ (targetAction k n N d hd r).toRingHom

attribute [local instance] sourceModule targetModule

/-- The concrete page differential is linear over the tangential symbol ring. -/
def tangentialDrop (r : ℕ) :
    (complex k n N d hd).SourceTotal r →ₗ[MvPolynomial (Fin n ⊕ Fin n) k]
      (complex k n N d hd).TargetTotal r where
  toFun := (complex k n N d hd).totalDrop r
  map_add' := map_add _
  map_smul' P z := by
    exact congrArg (fun f => f z)
      (totalDrop_intertwines_polynomials k n N d hd r P)

@[simp] theorem tangentialDrop_apply (r : ℕ)
    (z : (complex k n N d hd).SourceTotal r) :
    tangentialDrop k n N d hd r z = (complex k n N d hd).totalDrop r z := rfl


end
end Stafford38.Characteristic.CanonicalTangentialTotalAction
