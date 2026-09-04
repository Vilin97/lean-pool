/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/

import LeanPool.Wallace.ConcreteClosure
import LeanPool.Wallace.SeparationInterface

/-!
# From the local fusions to the Wallace counterexample

This module performs the final global assembly.  Its only input is the output of the countable
fusion: for each nonzero vector, a character on its concrete countable dependency closure which
detects that vector and satisfies the prescribed ultrafilter limits for all codes internal to the
closure.  The transfinite recursion extends each such character to the whole free group and
makes it admissible at every code.  The resulting characters form a separating family, so the
minimal construction interface yields the Wallace semigroup.
-/

open Filter Set Topology

namespace Wallace
namespace GlobalAssembly

noncomputable section

open TriangularPreprocess
open ConcreteData
open ConcreteClosure
open TransfiniteExtension

variable (N : ℕ → ℕ) (hN : ∀ l, 0 < N l) (M : ℕ → ℕ)

/-- The exact local output required from the countable fusion. -/
def HasLocalSeparatingCharacters : Prop :=
  ∀ x : {x : ContinuumFreeGroup // x ≠ 0},
    ∃ χD : (closure N hN M x.1 →₀ ℤ) →+ UnitAddCircle,
      χD (Finsupp.subtypeDomain (closure N hN M x.1) x.1) ≠ 0 ∧
        LocallyAdmissible (transfiniteData N hN M) (closure N hN M x.1) χD

variable (H : HasLocalSeparatingCharacters N hN M)

/-- The chosen local character for a nonzero vector. -/
def localCharacter (x : {x : ContinuumFreeGroup // x ≠ 0}) :
    (closure N hN M x.1 →₀ ℤ) →+ UnitAddCircle :=
  Classical.choose (H x)

theorem localCharacter_self_ne_zero (x : {x : ContinuumFreeGroup // x ≠ 0}) :
    localCharacter N hN M H x
      (Finsupp.subtypeDomain (closure N hN M x.1) x.1) ≠ 0 :=
  (Classical.choose_spec (H x)).1

theorem localCharacter_admissible (x : {x : ContinuumFreeGroup // x ≠ 0}) :
    LocallyAdmissible (transfiniteData N hN M) (closure N hN M x.1)
      (localCharacter N hN M H x) :=
  (Classical.choose_spec (H x)).2

/-- Extend the chosen local character by the well-founded triangular recursion. -/
def globalCharacter (x : {x : ContinuumFreeGroup // x ≠ 0}) :
    ContinuumFreeGroup →+ UnitAddCircle :=
  TransfiniteExtension.globalCharacter (transfiniteData N hN M)
    (closure N hN M x.1) (localCharacter N hN M H x)

theorem globalCharacter_self_ne_zero (x : {x : ContinuumFreeGroup // x ≠ 0}) :
    globalCharacter N hN M H x x.1 ≠ 0 := by
  rw [globalCharacter,
    TransfiniteExtension.globalCharacter_eq_local_restriction]
  · exact localCharacter_self_ne_zero N hN M H x
  · exact support_subset_closure N hN M x.1

theorem globalCharacter_admissible (x : {x : ContinuumFreeGroup // x ≠ 0})
    (a : ContinuumIndex) :
    Tendsto
      (fun n ↦ globalCharacter N hN M H x (prepared N hN M a n))
      (ultrafilter N hN a)
      (nhds (globalCharacter N hN M H x (codeBasisVector a))) := by
  exact TransfiniteExtension.globalCharacter_admissible
    (transfiniteData N hN M) (closure N hN M x.1)
    (localCharacter N hN M H x)
    (closure_closedUnderPreparedSupports N hN M x.1)
    (localCharacter_admissible N hN M H x) a

/-- The completely concrete separating package obtained from the local fusion theorem. -/
def separationPackage : SeparationPackage ContinuumIndex where
  Code := ContinuumIndex
  codeEquiv := sequenceCodeEquiv
  codeIndex := codeIndex
  subsequence := selector N hN M
  subsequence_strictMono := selector_strictMono N hN M
  ultrafilter := ultrafilter N hN
  ultrafilter_free := ultrafilter_free N hN
  character := globalCharacter N hN M H
  character_self_ne_zero := globalCharacter_self_ne_zero N hN M H
  character_limit := by
    intro a x
    exact globalCharacter_admissible N hN M H x a

end

end GlobalAssembly
end Wallace
