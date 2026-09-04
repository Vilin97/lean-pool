/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/

import LeanPool.Wallace.TriangularPreprocess
import Mathlib.Topology.Instances.AddCircle.Real

/-!
# Transfinite extension of a local circle-valued character

This file isolates the transfinite part of the Wallace construction behind a small, reusable
interface.  The only input about the prepared sequences is the triangular support condition:
every coordinate occurring in the sequence coded at `codeIndex c` is strictly smaller than
`codeIndex c`.

At a coordinate in the closed set `D` we use the prescribed local character.  At a code
coordinate outside `D` we take the compact ultrafilter limit of the values of its prepared
sequence, evaluated using coordinates already defined by well-founded recursion.  All other
coordinates receive zero.  The resulting basis assignment extends uniquely to the free Abelian
group, extends the local character, and is admissible for every code.

There are no axioms or omitted proofs in this file.
-/

open Filter Set Topology

namespace Wallace
namespace TransfiniteExtension

noncomputable section

universe u v

/-! ## Abstract triangular input -/

/-- The minimal triangular data needed by the transfinite character extension. -/
structure Data (I : Type u) [LT I] where
  /-- Codes for the prepared sequences. -/
  Code : Type v
  /-- The fresh coordinate assigned to a code. -/
  codeIndex : Code ↪ I
  /-- The sequence after the finite block preprocessing. -/
  prepared : Code → ℕ → I →₀ ℤ
  /-- Every coordinate used by a prepared term precedes its code coordinate. -/
  support_lt : ∀ c n i, i ∈ (prepared c n).support → i < codeIndex c
  /-- The ultrafilter with respect to which the coded limit is imposed. -/
  p : Code → Ultrafilter ℕ

/-- Closure of `D` under the coordinates occurring in codes whose fresh coordinate lies in
`D`.  This is precisely what is needed to transfer the already-established local limits. -/
def ClosedUnderPreparedSupports {I : Type u} [LT I] (E : Data I) (D : Set I) : Prop :=
  ∀ c, E.codeIndex c ∈ D → ∀ n i, i ∈ (E.prepared c n).support → i ∈ D

/-- The local admissibility condition, stated after restricting each prepared term to `D`. -/
def LocallyAdmissible {I : Type u} [LT I] (E : Data I) (D : Set I)
    (χD : (D →₀ ℤ) →+ UnitAddCircle) : Prop :=
  ∀ (c : E.Code) (hc : E.codeIndex c ∈ D),
    Tendsto (fun n ↦ χD (Finsupp.subtypeDomain D (E.prepared c n))) (E.p c)
      (nhds (χD (Finsupp.single ⟨E.codeIndex c, hc⟩ 1)))

/-! ## Evaluation below a recursive stage -/

/-- Turn the values available below stage `i` into a total basis assignment by putting zero
above the stage. -/
def stageBasis {I : Type u} [LT I] [DecidableRel ((· < ·) : I → I → Prop)] (i : I)
    (previous : ∀ j, j < i → UnitAddCircle) : I → UnitAddCircle :=
  fun j ↦ if h : j < i then previous j h else 0

/-- Evaluation of a prepared term using only values available below the current stage. -/
def stageEvaluation {I : Type u} [LT I] [DecidableRel ((· < ·) : I → I → Prop)]
    (E : Data I) (i : I)
    (previous : ∀ j, j < i → UnitAddCircle) (c : E.Code) (n : ℕ) : UnitAddCircle :=
  finsuppAddHomOfBasis (stageBasis i previous) (E.prepared c n)

/-- The compact ultrafilter limit chosen at a code coordinate. -/
def compactStageLimit {I : Type u} [LT I] [DecidableRel ((· < ·) : I → I → Prop)]
    (E : Data I) (i : I)
    (previous : ∀ j, j < i → UnitAddCircle) (c : E.Code) : UnitAddCircle :=
  (Ultrafilter.map (stageEvaluation E i previous c) (E.p c)).lim

/-- Two basis assignments that agree on the support of a vector give the same value. -/
theorem finsuppAddHomOfBasis_eq_of_eq_on_support {I : Type u}
    {z w : I → UnitAddCircle} {x : I →₀ ℤ}
    (h : ∀ i ∈ x.support, z i = w i) :
    finsuppAddHomOfBasis z x = finsuppAddHomOfBasis w x := by
  simp only [finsuppAddHomOfBasis, Finsupp.liftAddHom_apply]
  apply Finsupp.sum_congr
  intro i hi
  rw [h i hi]

/-! ## Well-founded definition of the global basis values -/

/-- One step of the recursion.  Injectivity of `codeIndex` makes the code chosen in the second
branch unique. -/
def basisStep {I : Type u} [LinearOrder I] (E : Data I) (D : Set I)
    (χD : (D →₀ ℤ) →+ UnitAddCircle) (i : I)
    (previous : ∀ j, j < i → UnitAddCircle) : UnitAddCircle := by
  classical
  exact if hi : i ∈ D then
      χD (Finsupp.single ⟨i, hi⟩ 1)
    else if hcode : ∃ c : E.Code, E.codeIndex c = i then
      compactStageLimit E i previous (Classical.choose hcode)
    else
      0

/-- The global values on the standard basis, defined by recursion along the well-order. -/
def globalBasisValue {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (E : Data I) (D : Set I) (χD : (D →₀ ℤ) →+ UnitAddCircle) :
    I → UnitAddCircle :=
  WellFoundedLT.fix fun i previous ↦ basisStep E D χD i previous

theorem globalBasisValue_eq {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (E : Data I) (D : Set I) (χD : (D →₀ ℤ) →+ UnitAddCircle) (i : I) :
    globalBasisValue E D χD i =
      basisStep E D χD i (fun j _ ↦ globalBasisValue E D χD j) := by
  rw [globalBasisValue, WellFoundedLT.fix_eq]

theorem globalBasisValue_of_mem {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (E : Data I) (D : Set I) (χD : (D →₀ ℤ) →+ UnitAddCircle)
    {i : I} (hi : i ∈ D) :
    globalBasisValue E D χD i = χD (Finsupp.single ⟨i, hi⟩ 1) := by
  rw [globalBasisValue_eq]
  simp [basisStep, hi]

theorem globalBasisValue_codeIndex_of_not_mem
    {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (E : Data I) (D : Set I) (χD : (D →₀ ℤ) →+ UnitAddCircle)
    (c : E.Code) (hc : E.codeIndex c ∉ D) :
    globalBasisValue E D χD (E.codeIndex c) =
      compactStageLimit E (E.codeIndex c)
        (fun j _ ↦ globalBasisValue E D χD j) c := by
  rw [globalBasisValue_eq]
  simp only [basisStep, hc, dite_false]
  let hex : ∃ d : E.Code, E.codeIndex d = E.codeIndex c := ⟨c, rfl⟩
  rw [dite_eq_left hex]
  have hchosen : Classical.choose hex = c := by
    apply E.codeIndex.injective
    exact Classical.choose_spec hex
  rw [hchosen]

/-! ## The global character and its extension property -/

/-- The unique additive character determined by the recursively constructed basis values. -/
def globalCharacter {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (E : Data I) (D : Set I) (χD : (D →₀ ℤ) →+ UnitAddCircle) :
    (I →₀ ℤ) →+ UnitAddCircle :=
  finsuppAddHomOfBasis (globalBasisValue E D χD)

@[simp]
theorem globalCharacter_single_one {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (E : Data I) (D : Set I) (χD : (D →₀ ℤ) →+ UnitAddCircle) (i : I) :
    globalCharacter E D χD (Finsupp.single i 1) = globalBasisValue E D χD i := by
  simp [globalCharacter]

/-- On finitely supported vectors on `D`, the global character is exactly the prescribed local
character. -/
theorem globalCharacter_extendDomain {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (E : Data I) (D : Set I) (χD : (D →₀ ℤ) →+ UnitAddCircle)
    (x : D →₀ ℤ) :
    globalCharacter E D χD (Finsupp.embDomain (.subtype D) x) = χD x := by
  let inclusion : (D →₀ ℤ) →+ (I →₀ ℤ) :=
    Finsupp.embDomain.addMonoidHom (.subtype (D : I → Prop))
  have hhom : (globalCharacter E D χD).comp inclusion = χD := by
    apply Finsupp.addHom_ext
    intro i n
    rcases i with ⟨i, hi⟩
    change globalCharacter E D χD
      (Finsupp.embDomain (.subtype (D : I → Prop)) (Finsupp.single ⟨i, hi⟩ n)) =
        χD (Finsupp.single ⟨i, hi⟩ n)
    rw [Finsupp.embDomain_single]
    simp only [globalCharacter, finsuppAddHomOfBasis_single]
    have hbasis := globalBasisValue_of_mem E D χD (i := i) hi
    have hbasis' :
        globalBasisValue E D χD i =
          χD (Finsupp.single ⟨i, hi⟩ 1) := by
      exact hbasis
    calc
      n • globalBasisValue E D χD i =
          n • χD (Finsupp.single ⟨i, hi⟩ 1) := congrArg (fun z ↦ n • z) hbasis'
      _ = χD (n • Finsupp.single ⟨i, hi⟩ 1) := (map_zsmul χD _ _).symm
      _ = χD (Finsupp.single ⟨i, hi⟩ n) := by simp
  exact DFunLike.congr_fun hhom x

/-- Equivalent extension statement for an ambient vector whose support is contained in `D`. -/
theorem globalCharacter_eq_local_restriction {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (E : Data I) (D : Set I) (χD : (D →₀ ℤ) →+ UnitAddCircle)
    (x : I →₀ ℤ) (hx : ∀ i ∈ x.support, i ∈ D) :
    globalCharacter E D χD x = χD (Finsupp.subtypeDomain D x) := by
  have hxrange : (↑x.support : Set I) ⊆
      Set.range (Function.Embedding.subtype D) := by
    intro i hi
    exact ⟨⟨i, hx i hi⟩, rfl⟩
  obtain ⟨y, rfl⟩ :=
    (Finsupp.mem_range_embDomain_iff (Function.Embedding.subtype D) x).2 hxrange
  rw [globalCharacter_extendDomain E D χD y]
  congr 1
  ext i
  exact (Finsupp.embDomain_apply_self (Function.Embedding.subtype D) y i).symm

/-! ## Admissibility at every code -/

theorem stageEvaluation_eq_globalCharacter
    {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (E : Data I) (D : Set I) (χD : (D →₀ ℤ) →+ UnitAddCircle)
    (c : E.Code) (n : ℕ) :
    stageEvaluation E (E.codeIndex c)
        (fun j _ ↦ globalBasisValue E D χD j) c n =
      globalCharacter E D χD (E.prepared c n) := by
  apply finsuppAddHomOfBasis_eq_of_eq_on_support
  intro i hi
  simp [stageBasis, E.support_lt c n i hi]

/-- Compactness of the circle supplies the limit used at each external code coordinate. -/
theorem tendsto_stageEvaluation_compactLimit
    {I : Type u} [LinearOrder I] (E : Data I) (i : I)
    (previous : ∀ j, j < i → UnitAddCircle) (c : E.Code) :
    Tendsto (stageEvaluation E i previous c) (E.p c)
      (nhds (compactStageLimit E i previous c)) := by
  exact (Ultrafilter.map (stageEvaluation E i previous c) (E.p c)).le_nhds_lim

/-- The transfinite extension is admissible for every prepared code, including codes outside
the local closed set. -/
theorem globalCharacter_admissible
    {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (E : Data I) (D : Set I) (χD : (D →₀ ℤ) →+ UnitAddCircle)
    (hclosed : ClosedUnderPreparedSupports E D)
    (hlocal : LocallyAdmissible E D χD) :
    ∀ c : E.Code,
      Tendsto (fun n ↦ globalCharacter E D χD (E.prepared c n)) (E.p c)
        (nhds (globalCharacter E D χD (Finsupp.single (E.codeIndex c) 1))) := by
  intro c
  by_cases hc : E.codeIndex c ∈ D
  · have heval :
        (fun n ↦ globalCharacter E D χD (E.prepared c n)) =
          (fun n ↦ χD (Finsupp.subtypeDomain D (E.prepared c n))) := by
      funext n
      exact globalCharacter_eq_local_restriction E D χD (E.prepared c n)
        (hclosed c hc n)
    have hbasis :
        globalCharacter E D χD (Finsupp.single (E.codeIndex c) 1) =
          χD (Finsupp.single ⟨E.codeIndex c, hc⟩ 1) := by
      rw [globalCharacter_single_one, globalBasisValue_of_mem E D χD hc]
    rw [heval, hbasis]
    exact hlocal c hc
  · have hlim := tendsto_stageEvaluation_compactLimit E (E.codeIndex c)
        (fun j _ ↦ globalBasisValue E D χD j) c
    have heval :
        (fun n ↦ globalCharacter E D χD (E.prepared c n)) =
          stageEvaluation E (E.codeIndex c)
            (fun j _ ↦ globalBasisValue E D χD j) c := by
      funext n
      exact (stageEvaluation_eq_globalCharacter E D χD c n).symm
    rw [heval, globalCharacter_single_one,
      globalBasisValue_codeIndex_of_not_mem E D χD c hc]
    exact hlim

/-! ## Specialization of the index type to the continuum well-order -/

/-- The generic theorem applies directly to the canonical continuum index constructed in
`TriangularPreprocess`.  Concrete fusion data only has to fill the fields of `Data`. -/
abbrev ContinuumData := Data TriangularPreprocess.ContinuumIndex

end

end TransfiniteExtension
end Wallace
