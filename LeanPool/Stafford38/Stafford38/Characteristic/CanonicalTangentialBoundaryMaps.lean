/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalTangentialTotalAction
import LeanPool.Stafford38.Stafford38.Characteristic.FilteredTwoTermBoundaryNaturality

/-!
# Tangential-linear boundary maps for the canonical quotient

These are the actual quotient maps of the filtered complex, with their
linearity over the tangential polynomial ring proved from the Weyl action.
-/

namespace Stafford38.Characteristic.CanonicalTangentialTotalAction

open Stafford38.Characteristic
open Stafford38.Characteristic.FilteredTwoTermPages
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylPBWMonicBridge

noncomputable section

variable (k : Type*) [Field k]
variable (n N : ℕ) (d : PresentedWeyl k (n + 1))
variable (hd : IsPBWMonicAt k (.inr (0 : Fin (n + 1))) N d)

attribute [local instance] sourceModule targetModule

theorem totalBoundaryMap_intertwines_polynomials (r : ℕ)
    (P : MvPolynomial (Fin n ⊕ Fin n) k) :
    (complex k n N d).totalBoundaryMap r ∘ₗ targetAction k n N d 1 P =
      targetAction k n N d (r + 1) P ∘ₗ
        (complex k n N d).totalBoundaryMap r :=
  commutingPolynomialAction_intertwines _ _ _ _ _
    (fun i => (generator k n N d i).totalBoundaryMap_naturality r) P

/-- The total boundary map as a linear map for the commuting tangential polynomial action. -/
def tangentialBoundaryMap (r : ℕ) :
    (complex k n N d).TargetTotal 1 →ₗ[MvPolynomial (Fin n ⊕ Fin n) k]
      (complex k n N d).TargetTotal (r + 1) where
  toFun := (complex k n N d).totalBoundaryMap r
  map_add' := map_add _
  map_smul' P z :=
    congrArg (fun f => f z)
      (totalBoundaryMap_intertwines_polynomials k n N d r P)

theorem tangentialBoundaryMap_surjective (r : ℕ) :
    Function.Surjective (tangentialBoundaryMap k n N d r) :=
  (complex k n N d).totalBoundaryMap_surjective r

theorem tangentialBoundaryMap_ker_mono :
    Monotone (fun r => (tangentialBoundaryMap k n N d r).ker) := by
  intro r s hrs z hz
  exact (complex k n N d).totalBoundaryMap_ker_mono r s hrs hz

include hd in
theorem tangentialBoundaryMap_eventually_zero [Algebra ℚ k]
    (z : (complex k n N d).TargetTotal 1) :
    ∃ r, tangentialBoundaryMap k n N d r z = 0 :=
  (complex k n N d).totalBoundaryMap_eventually_zero
    (CanonicalFilteredTwoTerm.canonicalOrderFiltration_exhaustive k _)
    (CanonicalFilteredTwoTerm.canonicalFilteredTwoTerm_f_surjective k n N hd) z


end
end Stafford38.Characteristic.CanonicalTangentialTotalAction
