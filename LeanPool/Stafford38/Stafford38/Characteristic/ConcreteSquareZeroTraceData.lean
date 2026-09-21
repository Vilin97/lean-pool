/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.FilteredQuotientTwoJet
import LeanPool.Stafford38.Stafford38.Characteristic.OrderReesTwoJetBracket
import LeanPool.Stafford38.Stafford38.Characteristic.SquareZeroTraceData

/-!
# Concrete square-zero trace data for a filtered Weyl quotient

This file assembles the order-Rees two-jet ring and the filtered quotient
two-jet module into the abstract right-module interface used by the trace
argument.  The recorded bracket is the negative standard Poisson bracket,
as forced by the convention `[x,p] = -1`.

No localization, finite-length trace theorem, or radical involutivity theorem
is asserted here.
-/

namespace Stafford38.CharacteristicConcreteSquareZeroTraceData

open Stafford38.Characteristic
open Stafford38.CharacteristicAssociatedGradedModule
open Stafford38.CharacteristicFilteredQuotientTwoJet
open Stafford38.CharacteristicOrderReesTwoJet
open Stafford38.CharacteristicOrderReesTwoJetBracket
open Stafford38.Characteristic.SquareZeroTraceData
open Stafford38.EulerSurjectivity
open Stafford38.WeylFilteredCommutator
open Stafford38.WeylIteratedEquivalence

noncomputable section


universe u

variable (k : Type u) [Field k]
variable {n : ℕ}

/-- The sign-correct first-order bracket as a curried bilinear map. -/
def negativePoissonBracketLinear :
    SymbolRing k n →ₗ[k] SymbolRing k n →ₗ[k] SymbolRing k n where
  toFun f :=
    { toFun := fun g => -poissonBracket f g
      map_add' := by
        intro g h
        change -poissonBracket f (g + h) =
          -poissonBracket f g + -poissonBracket f h
        rw [poissonBracket_add_right, neg_add]
      map_smul' := by
        intro c g
        change -poissonBracket f (c • g) =
          c • (-poissonBracket f g)
        rw [poissonBracket_smul_right, smul_neg] }
  map_add' := by
    intro f g
    apply LinearMap.ext
    intro h
    change -poissonBracket (f + g) h =
      -poissonBracket f h + -poissonBracket g h
    rw [poissonBracket_add_left, neg_add]
  map_smul' := by
    intro c f
    apply LinearMap.ext
    intro g
    change -poissonBracket (c • f) g =
      c • (-poissonBracket f g)
    rw [poissonBracket_smul_left, smul_neg]

@[simp]
theorem negativePoissonBracketLinear_apply
    (f g : SymbolRing k n) :
    negativePoissonBracketLinear (n := n) k f g =
      -poissonBracket f g :=
  rfl

/-- The two-jet action commutes with the original coefficient-field action. -/
theorem filteredQuotientTwoJetSMulCommClass
    (I : RightIdeal (PresentedWeyl k n)) :
    SMulCommClass k (OrderReesTwoJet (n := n) k)ᵐᵒᵖ
      (FilteredQuotientTwoJet k I) where
  smul_comm c b m := by
    change c • quotientOrderReesTwoJetAction k I b m =
      quotientOrderReesTwoJetAction k I b (c • m)
    exact ((quotientOrderReesTwoJetAction k I b).map_smul c m).symm

noncomputable instance filteredQuotientTwoJetSMulCommClassInstance
    (I : RightIdeal (PresentedWeyl k n)) :
    SMulCommClass k (OrderReesTwoJet (n := n) k)ᵐᵒᵖ
      (FilteredQuotientTwoJet k I) :=
  filteredQuotientTwoJetSMulCommClass k I

/-- The concrete order-Rees two-jet deformation of the associated graded
module of `A/I`, packaged with its negative-Poisson first-order bracket. -/
def filteredQuotientTwoJetTraceData
    (I : RightIdeal (PresentedWeyl k n)) :
    RightSquareZeroTraceData k (SymbolRing k n)
      (OrderReesTwoJet (n := n) k)
      (FilteredQuotientTwoJet k I)
      (OrderAssociatedGradedModule k I) where
  c := orderReesTwoJetParameter (n := n) k
  c_center := orderReesTwoJetParameter_mem_center (n := n) k
  c_sq := orderReesTwoJetParameter_sq (n := n) k
  pi := orderReesTwoJetSpecialization (n := n) k
  pi_surjective := orderReesTwoJetSpecialization_surjective (n := n) k
  pi_c := orderReesTwoJetSpecialization_parameter (n := n) k
  cAct := quotientOrderReesTwoJetCAct k I
  cAct_apply := quotientOrderReesTwoJetCAct_apply k I
  c_exact := quotientOrderReesTwoJetCAct_ker_eq_range k I
  rho := filteredQuotientTwoJetRho k I
  rho_surjective := filteredQuotientTwoJetRho_surjective k I
  rho_ker := filteredQuotientTwoJetRho_ker_eq_range_cAct k I
  rho_action := filteredQuotientTwoJetRho_action_compatibility k I
  bracket := negativePoissonBracketLinear (n := n) k
  commutator_factor := by
    intro a b
    obtain ⟨z, hz, hpi⟩ := exists_twoJet_commutatorQuotient k a b
    exact ⟨z, hz, by simpa using hpi⟩

@[simp]
theorem filteredQuotientTwoJetTraceData_bracket
    (I : RightIdeal (PresentedWeyl k n)) (f g : SymbolRing k n) :
    (filteredQuotientTwoJetTraceData k I).bracket f g =
      -poissonBracket f g :=
  rfl


end

end Stafford38.CharacteristicConcreteSquareZeroTraceData
