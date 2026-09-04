/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/

import LeanPool.Wallace.MathlibFoundations
import Mathlib.Topology.Instances.AddCircle.Real

/-!
# Coefficient-parametric transfinite character extension

This module contains the recursion shared by the integer and rational Wallace constructions.
The coefficient-specific input is an additive character on one coordinate whose value at one is
a prescribed circle element. The integer specialization uses scalar multiplication; the rational
specialization obtains the character from Baer's extension theorem.
-/

open Filter Set Topology

namespace Wallace
namespace CoefficientTransfiniteExtension

noncomputable section

universe u v w

/-- A way to extend a prescribed circle value to a character on one coefficient coordinate. -/
structure CoordinateExtension (R : Type w) [AddCommMonoid R] [One R] where
  /-- Build a coordinate character with the prescribed value at one. -/
  ofValue : UnitAddCircle → (R →+ UnitAddCircle)
  ofValue_one : ∀ t, ofValue t 1 = t

/-- The triangular data needed by the coefficient-parametric recursion. -/
structure Data (R : Type w) (I : Type u) [Zero R] [LT I] where
  /-- Codes for the prepared sequences. -/
  Code : Type v
  /-- The fresh coordinate assigned to a code. -/
  codeIndex : Code ↪ I
  /-- The sequence after finite block preprocessing. -/
  prepared : Code → ℕ → I →₀ R
  support_lt : ∀ c n i, i ∈ (prepared c n).support → i < codeIndex c
  /-- The ultrafilter along which the coded limit is imposed. -/
  p : Code → Ultrafilter ℕ

/-- Closure under the prepared supports attached to code coordinates in `D`. -/
def ClosedUnderPreparedSupports {R : Type w} {I : Type u} [Zero R] [LT I]
    (E : Data R I) (D : Set I) : Prop :=
  ∀ c, E.codeIndex c ∈ D → ∀ n i, i ∈ (E.prepared c n).support → i ∈ D

/-- The local character already realizes each limit whose code coordinate lies in `D`. -/
def LocallyAdmissible {R : Type w} {I : Type u} [AddCommMonoid R] [One R] [LT I]
    (E : Data R I) (D : Set I) (character : (D →₀ R) →+ UnitAddCircle) : Prop :=
  ∀ (c : E.Code) (hc : E.codeIndex c ∈ D),
    Tendsto (fun n ↦ character (Finsupp.subtypeDomain D (E.prepared c n))) (E.p c)
      (nhds (character (Finsupp.single ⟨E.codeIndex c, hc⟩ 1)))

/-- The character on a direct sum induced by its coordinate characters. -/
private def finsuppAddHom {R : Type w} {I : Type u} [AddCommMonoid R]
    (coordinates : I → (R →+ UnitAddCircle)) : (I →₀ R) →+ UnitAddCircle :=
  Finsupp.liftAddHom coordinates

@[simp]
private theorem finsuppAddHom_single {R : Type w} {I : Type u} [AddCommMonoid R]
    (coordinates : I → (R →+ UnitAddCircle)) (i : I) (r : R) :
    finsuppAddHom coordinates (Finsupp.single i r) = coordinates i r := by
  simp [finsuppAddHom]

/-- Totalize the coordinate characters available below a recursive stage. -/
private def stageCoordinates {R : Type w} {I : Type u} [AddCommMonoid R] [LT I]
    [DecidableRel ((· < ·) : I → I → Prop)] (i : I)
    (previous : ∀ j, j < i → (R →+ UnitAddCircle)) : I → (R →+ UnitAddCircle) :=
  fun j ↦ if h : j < i then previous j h else 0

/-- Evaluate a prepared term using only coordinates below the current stage. -/
private def stageEvaluation {R : Type w} {I : Type u} [AddCommMonoid R] [LT I]
    [DecidableRel ((· < ·) : I → I → Prop)] (E : Data R I) (i : I)
    (previous : ∀ j, j < i → (R →+ UnitAddCircle))
    (c : E.Code) (n : ℕ) : UnitAddCircle :=
  finsuppAddHom (stageCoordinates i previous) (E.prepared c n)

/-- The compact ultrafilter limit selected at a code coordinate. -/
private def compactStageLimit {R : Type w} {I : Type u} [AddCommMonoid R] [LT I]
    [DecidableRel ((· < ·) : I → I → Prop)] (E : Data R I) (i : I)
    (previous : ∀ j, j < i → (R →+ UnitAddCircle))
    (c : E.Code) : UnitAddCircle :=
  (Ultrafilter.map (stageEvaluation E i previous c) (E.p c)).lim

private theorem finsuppAddHom_eq_of_eq_on_support
    {R : Type w} {I : Type u} [AddCommMonoid R]
    {left right : I → (R →+ UnitAddCircle)} {x : I →₀ R}
    (h : ∀ i ∈ x.support, left i = right i) :
    finsuppAddHom left x = finsuppAddHom right x := by
  simp only [finsuppAddHom, Finsupp.liftAddHom_apply]
  apply Finsupp.sum_congr
  intro i hi
  rw [h i hi]

/-- One step of the well-founded coordinate recursion. -/
private def coordinateStep
    {R : Type w} {I : Type u} [AddCommMonoid R] [One R] [LinearOrder I]
    (extension : CoordinateExtension R) (E : Data R I) (D : Set I)
    (character : (D →₀ R) →+ UnitAddCircle) (i : I)
    (previous : ∀ j, j < i → (R →+ UnitAddCircle)) : R →+ UnitAddCircle := by
  classical
  exact if hi : i ∈ D then
      character.comp (Finsupp.singleAddHom ⟨i, hi⟩)
    else if hcode : ∃ c : E.Code, E.codeIndex c = i then
      extension.ofValue (compactStageLimit E i previous (Classical.choose hcode))
    else
      0

/-- The coordinate characters constructed by well-founded recursion. -/
private def globalCoordinate {R : Type w} {I : Type u} [AddCommMonoid R] [One R]
    [LinearOrder I] [WellFoundedLT I] (extension : CoordinateExtension R)
    (E : Data R I) (D : Set I) (character : (D →₀ R) →+ UnitAddCircle) :
    I → (R →+ UnitAddCircle) :=
  WellFoundedLT.fix fun i previous ↦ coordinateStep extension E D character i previous

private theorem globalCoordinate_eq {R : Type w} {I : Type u} [AddCommMonoid R] [One R]
    [LinearOrder I] [WellFoundedLT I] (extension : CoordinateExtension R)
    (E : Data R I) (D : Set I) (character : (D →₀ R) →+ UnitAddCircle) (i : I) :
    globalCoordinate extension E D character i =
      coordinateStep extension E D character i
        (fun j _ ↦ globalCoordinate extension E D character j) := by
  rw [globalCoordinate, WellFoundedLT.fix_eq]

private theorem globalCoordinate_of_mem
    {R : Type w} {I : Type u} [AddCommMonoid R] [One R]
    [LinearOrder I] [WellFoundedLT I] (extension : CoordinateExtension R)
    (E : Data R I) (D : Set I) (character : (D →₀ R) →+ UnitAddCircle)
    {i : I} (hi : i ∈ D) :
    globalCoordinate extension E D character i =
      character.comp (Finsupp.singleAddHom ⟨i, hi⟩) := by
  rw [globalCoordinate_eq]
  simp [coordinateStep, hi]

private theorem globalCoordinate_codeIndex_of_not_mem
    {R : Type w} {I : Type u} [AddCommMonoid R] [One R] [LinearOrder I] [WellFoundedLT I]
    (extension : CoordinateExtension R) (E : Data R I) (D : Set I)
    (character : (D →₀ R) →+ UnitAddCircle)
    (c : E.Code) (hc : E.codeIndex c ∉ D) :
    globalCoordinate extension E D character (E.codeIndex c) =
      extension.ofValue
        (compactStageLimit E (E.codeIndex c)
          (fun j _ ↦ globalCoordinate extension E D character j) c) := by
  rw [globalCoordinate_eq]
  simp only [coordinateStep, hc, dite_false]
  let hex : ∃ d : E.Code, E.codeIndex d = E.codeIndex c := ⟨c, rfl⟩
  rw [dite_eq_left hex]
  have hchosen : Classical.choose hex = c := by
    apply E.codeIndex.injective
    exact Classical.choose_spec hex
  rw [hchosen]

/-- The global character assembled from the recursively constructed coordinates. -/
def globalCharacter {R : Type w} {I : Type u} [AddCommMonoid R] [One R]
    [LinearOrder I] [WellFoundedLT I] (extension : CoordinateExtension R)
    (E : Data R I) (D : Set I) (character : (D →₀ R) →+ UnitAddCircle) :
    (I →₀ R) →+ UnitAddCircle :=
  finsuppAddHom (globalCoordinate extension E D character)

@[simp]
private theorem globalCharacter_single {R : Type w} {I : Type u} [AddCommMonoid R] [One R]
    [LinearOrder I] [WellFoundedLT I] (extension : CoordinateExtension R)
    (E : Data R I) (D : Set I) (character : (D →₀ R) →+ UnitAddCircle)
    (i : I) (r : R) :
    globalCharacter extension E D character (Finsupp.single i r) =
      globalCoordinate extension E D character i r := by
  simp [globalCharacter]

private theorem globalCharacter_extendDomain {R : Type w} {I : Type u}
    [AddCommMonoid R] [One R] [LinearOrder I] [WellFoundedLT I]
    (extension : CoordinateExtension R) (E : Data R I) (D : Set I)
    (character : (D →₀ R) →+ UnitAddCircle) (x : D →₀ R) :
    globalCharacter extension E D character (Finsupp.embDomain (.subtype D) x) = character x := by
  let inclusion : (D →₀ R) →+ (I →₀ R) :=
    Finsupp.embDomain.addMonoidHom (.subtype (D : I → Prop))
  have hhom : (globalCharacter extension E D character).comp inclusion = character := by
    apply Finsupp.addHom_ext
    intro i r
    rcases i with ⟨i, hi⟩
    change globalCharacter extension E D character
      (Finsupp.embDomain (.subtype (D : I → Prop)) (Finsupp.single ⟨i, hi⟩ r)) =
        character (Finsupp.single ⟨i, hi⟩ r)
    rw [Finsupp.embDomain_single, globalCharacter_single]
    have hcoordinate := globalCoordinate_of_mem extension E D character (i := i) hi
    have happly := DFunLike.congr_fun hcoordinate r
    change globalCoordinate extension E D character i r = character (Finsupp.single ⟨i, hi⟩ r)
    simpa only [AddMonoidHom.comp_apply, Finsupp.singleAddHom_apply] using happly
  exact DFunLike.congr_fun hhom x

theorem globalCharacter_eq_local_restriction {R : Type w} {I : Type u}
    [AddCommMonoid R] [One R] [LinearOrder I] [WellFoundedLT I]
    (extension : CoordinateExtension R) (E : Data R I) (D : Set I)
    (character : (D →₀ R) →+ UnitAddCircle)
    (x : I →₀ R) (hx : ∀ i ∈ x.support, i ∈ D) :
    globalCharacter extension E D character x = character (Finsupp.subtypeDomain D x) := by
  have hxrange : (↑x.support : Set I) ⊆ Set.range (Function.Embedding.subtype D) := by
    intro i hi
    exact ⟨⟨i, hx i hi⟩, rfl⟩
  obtain ⟨y, rfl⟩ :=
    (Finsupp.mem_range_embDomain_iff (Function.Embedding.subtype D) x).2 hxrange
  rw [globalCharacter_extendDomain extension E D character y]
  congr 1
  ext i
  exact (Finsupp.embDomain_apply_self (Function.Embedding.subtype D) y i).symm

private theorem stageEvaluation_eq_globalCharacter
    {R : Type w} {I : Type u} [AddCommMonoid R] [One R] [LinearOrder I] [WellFoundedLT I]
    (extension : CoordinateExtension R) (E : Data R I) (D : Set I)
    (character : (D →₀ R) →+ UnitAddCircle) (c : E.Code) (n : ℕ) :
    stageEvaluation E (E.codeIndex c)
        (fun j _ ↦ globalCoordinate extension E D character j) c n =
      globalCharacter extension E D character (E.prepared c n) := by
  apply finsuppAddHom_eq_of_eq_on_support
  intro i hi
  simp [stageCoordinates, E.support_lt c n i hi]

private theorem tendsto_stageEvaluation_compactLimit
    {R : Type w} {I : Type u} [AddCommMonoid R] [LinearOrder I]
    (E : Data R I) (i : I) (previous : ∀ j, j < i → (R →+ UnitAddCircle))
    (c : E.Code) :
    Tendsto (stageEvaluation E i previous c) (E.p c)
      (nhds (compactStageLimit E i previous c)) := by
  exact (Ultrafilter.map (stageEvaluation E i previous c) (E.p c)).le_nhds_lim

/-- The transfinite extension realizes every prescribed ultrafilter limit. -/
theorem globalCharacter_admissible
    {R : Type w} {I : Type u} [AddCommMonoid R] [One R] [LinearOrder I] [WellFoundedLT I]
    (extension : CoordinateExtension R) (E : Data R I) (D : Set I)
    (character : (D →₀ R) →+ UnitAddCircle)
    (hclosed : ClosedUnderPreparedSupports E D)
    (hlocal : LocallyAdmissible E D character) :
    ∀ c : E.Code,
      Tendsto (fun n ↦ globalCharacter extension E D character (E.prepared c n)) (E.p c)
        (nhds (globalCharacter extension E D character (Finsupp.single (E.codeIndex c) 1))) := by
  intro c
  by_cases hc : E.codeIndex c ∈ D
  · have heval :
        (fun n ↦ globalCharacter extension E D character (E.prepared c n)) =
          (fun n ↦ character (Finsupp.subtypeDomain D (E.prepared c n))) := by
      funext n
      exact globalCharacter_eq_local_restriction extension E D character (E.prepared c n)
        (hclosed c hc n)
    have hbasis :
        globalCharacter extension E D character (Finsupp.single (E.codeIndex c) 1) =
          character (Finsupp.single ⟨E.codeIndex c, hc⟩ 1) := by
      rw [globalCharacter_single, globalCoordinate_of_mem extension E D character hc]
      rfl
    rw [heval, hbasis]
    exact hlocal c hc
  · have hlim := tendsto_stageEvaluation_compactLimit E (E.codeIndex c)
        (fun j _ ↦ globalCoordinate extension E D character j) c
    have heval :
        (fun n ↦ globalCharacter extension E D character (E.prepared c n)) =
          stageEvaluation E (E.codeIndex c)
            (fun j _ ↦ globalCoordinate extension E D character j) c := by
      funext n
      exact (stageEvaluation_eq_globalCharacter extension E D character c n).symm
    rw [heval, globalCharacter_single,
      globalCoordinate_codeIndex_of_not_mem extension E D character c hc,
      extension.ofValue_one]
    exact hlim

end
end CoefficientTransfiniteExtension
end Wallace
