/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/

import LeanPool.Wallace.RationalTriangularPreprocess
import Mathlib.Algebra.Category.Grp.Injective

/-!
# Transfinite extension for the rational direct sum

The recursive datum at a coordinate is an additive homomorphism `ℚ →+ 𝕋`, rather than a
single point of the circle.  At a new code coordinate, Baer's extension theorem extends the
homomorphism `n ↦ n • t` from `ℤ` to `ℚ`, where `t` is the compact ultrafilter limit chosen at
that stage.  This is the coefficient-sensitive step in the rational construction.
-/

open Filter Set Topology

namespace Wallace
namespace RationalTransfiniteExtension

noncomputable section

universe u v

/-- The minimal triangular input for rational-valued prepared sequences. -/
structure Data (I : Type u) [LT I] where
  Code : Type v
  codeIndex : Code ↪ I
  prepared : Code → ℕ → I →₀ ℚ
  support_lt : ∀ c n i, i ∈ (prepared c n).support → i < codeIndex c
  p : Code → Ultrafilter ℕ

/-- Closure under all supports needed by a code whose distinguished coordinate is local. -/
def ClosedUnderPreparedSupports {I : Type u} [LT I] (E : Data I) (D : Set I) : Prop :=
  ∀ c, E.codeIndex c ∈ D → ∀ n i, i ∈ (E.prepared c n).support → i ∈ D

/-- The local character already realizes every limit whose code coordinate belongs to `D`. -/
def LocallyAdmissible {I : Type u} [LT I] (E : Data I) (D : Set I)
    (χD : (D →₀ ℚ) →+ UnitAddCircle) : Prop :=
  ∀ (c : E.Code) (hc : E.codeIndex c ∈ D),
    Tendsto (fun n ↦ χD (Finsupp.subtypeDomain D (E.prepared c n))) (E.p c)
      (nhds (χD (Finsupp.single ⟨E.codeIndex c, hc⟩ 1)))

/-! ## Extending one rational coordinate -/

/-- The integer character with prescribed value at one. -/
def integerCircleHom (t : UnitAddCircle) : ℤ →+ UnitAddCircle :=
  (zmultiplesHom UnitAddCircle) t

theorem intCastAddHom_rational_injective :
    Function.Injective (Int.castAddHom ℚ) := by
  intro m n h
  exact Rat.intCast_injective h

/-- An additive homomorphism on `ℚ` extending `n ↦ n • t` on `ℤ`.

Only its value at `1` is constrained at the current stage; the chosen full homomorphism is then
used coherently when later prepared sequences are evaluated. -/
def extendRationalCoordinate (t : UnitAddCircle) : ℚ →+ UnitAddCircle :=
  Classical.choose <|
    (Module.Baer.of_divisible UnitAddCircle).extension_property_addMonoidHom
      (Int.castAddHom ℚ) intCastAddHom_rational_injective (integerCircleHom t)

theorem extendRationalCoordinate_comp_intCast (t : UnitAddCircle) :
    (extendRationalCoordinate t).comp (Int.castAddHom ℚ) = integerCircleHom t :=
  Classical.choose_spec <|
    (Module.Baer.of_divisible UnitAddCircle).extension_property_addMonoidHom
      (Int.castAddHom ℚ) intCastAddHom_rational_injective (integerCircleHom t)

@[simp]
theorem extendRationalCoordinate_one (t : UnitAddCircle) :
    extendRationalCoordinate t 1 = t := by
  have h := DFunLike.congr_fun (extendRationalCoordinate_comp_intCast t) 1
  simpa [integerCircleHom] using h

/-! ## Evaluation below a recursive stage -/

/-- The homomorphism out of a rational direct sum determined coordinatewise. -/
def rationalFinsuppAddHom {I : Type u}
    (θ : I → (ℚ →+ UnitAddCircle)) : (I →₀ ℚ) →+ UnitAddCircle :=
  Finsupp.liftAddHom θ

@[simp]
theorem rationalFinsuppAddHom_single {I : Type u}
    (θ : I → (ℚ →+ UnitAddCircle)) (i : I) (q : ℚ) :
    rationalFinsuppAddHom θ (Finsupp.single i q) = θ i q := by
  simp [rationalFinsuppAddHom]

/-- Totalize the coordinate homomorphisms already available below `i`. -/
def stageCoordinates {I : Type u} [LT I] [DecidableRel ((· < ·) : I → I → Prop)]
    (i : I) (previous : ∀ j, j < i → (ℚ →+ UnitAddCircle)) :
    I → (ℚ →+ UnitAddCircle) :=
  fun j ↦ if h : j < i then previous j h else 0

/-- Evaluate a prepared term using only coordinates below the current stage. -/
def stageEvaluation {I : Type u} [LT I] [DecidableRel ((· < ·) : I → I → Prop)]
    (E : Data I) (i : I)
    (previous : ∀ j, j < i → (ℚ →+ UnitAddCircle))
    (c : E.Code) (n : ℕ) : UnitAddCircle :=
  rationalFinsuppAddHom (stageCoordinates i previous) (E.prepared c n)

/-- Compact ultrafilter limit selected at a code coordinate. -/
def compactStageLimit {I : Type u} [LT I] [DecidableRel ((· < ·) : I → I → Prop)]
    (E : Data I) (i : I)
    (previous : ∀ j, j < i → (ℚ →+ UnitAddCircle))
    (c : E.Code) : UnitAddCircle :=
  (Ultrafilter.map (stageEvaluation E i previous c) (E.p c)).lim

theorem rationalFinsuppAddHom_eq_of_eq_on_support {I : Type u}
    {z w : I → (ℚ →+ UnitAddCircle)} {x : I →₀ ℚ}
    (h : ∀ i ∈ x.support, z i = w i) :
    rationalFinsuppAddHom z x = rationalFinsuppAddHom w x := by
  simp only [rationalFinsuppAddHom, Finsupp.liftAddHom_apply]
  apply Finsupp.sum_congr
  intro i hi
  rw [h i hi]

/-! ## Well-founded construction -/

/-- One step of the coordinate recursion. -/
def coordinateStep {I : Type u} [LinearOrder I] (E : Data I) (D : Set I)
    (χD : (D →₀ ℚ) →+ UnitAddCircle) (i : I)
    (previous : ∀ j, j < i → (ℚ →+ UnitAddCircle)) :
    ℚ →+ UnitAddCircle := by
  classical
  exact if hi : i ∈ D then
      χD.comp (Finsupp.singleAddHom ⟨i, hi⟩)
    else if hcode : ∃ c : E.Code, E.codeIndex c = i then
      extendRationalCoordinate
        (compactStageLimit E i previous (Classical.choose hcode))
    else
      0

/-- The recursively constructed additive homomorphism on each rational coordinate. -/
def globalCoordinate {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (E : Data I) (D : Set I) (χD : (D →₀ ℚ) →+ UnitAddCircle) :
    I → (ℚ →+ UnitAddCircle) :=
  WellFoundedLT.fix fun i previous ↦ coordinateStep E D χD i previous

theorem globalCoordinate_eq {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (E : Data I) (D : Set I) (χD : (D →₀ ℚ) →+ UnitAddCircle) (i : I) :
    globalCoordinate E D χD i =
      coordinateStep E D χD i (fun j _ ↦ globalCoordinate E D χD j) := by
  rw [globalCoordinate, WellFoundedLT.fix_eq]

theorem globalCoordinate_of_mem {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (E : Data I) (D : Set I) (χD : (D →₀ ℚ) →+ UnitAddCircle)
    {i : I} (hi : i ∈ D) :
    globalCoordinate E D χD i = χD.comp (Finsupp.singleAddHom ⟨i, hi⟩) := by
  rw [globalCoordinate_eq]
  simp [coordinateStep, hi]

theorem globalCoordinate_codeIndex_of_not_mem
    {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (E : Data I) (D : Set I) (χD : (D →₀ ℚ) →+ UnitAddCircle)
    (c : E.Code) (hc : E.codeIndex c ∉ D) :
    globalCoordinate E D χD (E.codeIndex c) =
      extendRationalCoordinate
        (compactStageLimit E (E.codeIndex c)
          (fun j _ ↦ globalCoordinate E D χD j) c) := by
  rw [globalCoordinate_eq]
  simp only [coordinateStep, hc, dite_false]
  let hex : ∃ d : E.Code, E.codeIndex d = E.codeIndex c := ⟨c, rfl⟩
  rw [dif_pos hex]
  have hchosen : Classical.choose hex = c := by
    apply E.codeIndex.injective
    exact Classical.choose_spec hex
  rw [hchosen]

/-! ## Global character, extension, and admissibility -/

def globalCharacter {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (E : Data I) (D : Set I) (χD : (D →₀ ℚ) →+ UnitAddCircle) :
    (I →₀ ℚ) →+ UnitAddCircle :=
  rationalFinsuppAddHom (globalCoordinate E D χD)

@[simp]
theorem globalCharacter_single {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (E : Data I) (D : Set I) (χD : (D →₀ ℚ) →+ UnitAddCircle)
    (i : I) (q : ℚ) :
    globalCharacter E D χD (Finsupp.single i q) = globalCoordinate E D χD i q := by
  simp [globalCharacter]

theorem globalCharacter_extendDomain {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (E : Data I) (D : Set I) (χD : (D →₀ ℚ) →+ UnitAddCircle)
    (x : D →₀ ℚ) :
    globalCharacter E D χD (Finsupp.embDomain (.subtype D) x) = χD x := by
  let inclusion : (D →₀ ℚ) →+ (I →₀ ℚ) :=
    Finsupp.embDomain.addMonoidHom (.subtype (D : I → Prop))
  have hhom : (globalCharacter E D χD).comp inclusion = χD := by
    apply Finsupp.addHom_ext
    intro i q
    rcases i with ⟨i, hi⟩
    change globalCharacter E D χD
      (Finsupp.embDomain (.subtype (D : I → Prop)) (Finsupp.single ⟨i, hi⟩ q)) =
        χD (Finsupp.single ⟨i, hi⟩ q)
    rw [Finsupp.embDomain_single, globalCharacter_single]
    have hcoord := globalCoordinate_of_mem E D χD (i := i) hi
    have happly := DFunLike.congr_fun hcoord q
    change globalCoordinate E D χD i q = χD (Finsupp.single ⟨i, hi⟩ q)
    simpa only [AddMonoidHom.comp_apply, Finsupp.singleAddHom_apply] using happly
  exact DFunLike.congr_fun hhom x

theorem globalCharacter_eq_local_restriction {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (E : Data I) (D : Set I) (χD : (D →₀ ℚ) →+ UnitAddCircle)
    (x : I →₀ ℚ) (hx : ∀ i ∈ x.support, i ∈ D) :
    globalCharacter E D χD x = χD (Finsupp.subtypeDomain D x) := by
  have hxrange : (↑x.support : Set I) ⊆ Set.range (Function.Embedding.subtype D) := by
    intro i hi
    exact ⟨⟨i, hx i hi⟩, rfl⟩
  obtain ⟨y, rfl⟩ :=
    (Finsupp.mem_range_embDomain_iff (Function.Embedding.subtype D) x).2 hxrange
  rw [globalCharacter_extendDomain E D χD y]
  congr 1
  ext i
  exact (Finsupp.embDomain_apply_self (Function.Embedding.subtype D) y i).symm

theorem stageEvaluation_eq_globalCharacter
    {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (E : Data I) (D : Set I) (χD : (D →₀ ℚ) →+ UnitAddCircle)
    (c : E.Code) (n : ℕ) :
    stageEvaluation E (E.codeIndex c)
        (fun j _ ↦ globalCoordinate E D χD j) c n =
      globalCharacter E D χD (E.prepared c n) := by
  apply rationalFinsuppAddHom_eq_of_eq_on_support
  intro i hi
  simp [stageCoordinates, E.support_lt c n i hi]

theorem tendsto_stageEvaluation_compactLimit
    {I : Type u} [LinearOrder I] (E : Data I) (i : I)
    (previous : ∀ j, j < i → (ℚ →+ UnitAddCircle)) (c : E.Code) :
    Tendsto (stageEvaluation E i previous c) (E.p c)
      (nhds (compactStageLimit E i previous c)) := by
  exact (Ultrafilter.map (stageEvaluation E i previous c) (E.p c)).le_nhds_lim

/-- The rational transfinite extension realizes every prescribed ultrafilter limit. -/
theorem globalCharacter_admissible
    {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (E : Data I) (D : Set I) (χD : (D →₀ ℚ) →+ UnitAddCircle)
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
      rw [globalCharacter_single, globalCoordinate_of_mem E D χD hc]
      rfl
    rw [heval, hbasis]
    exact hlocal c hc
  · have hlim := tendsto_stageEvaluation_compactLimit E (E.codeIndex c)
        (fun j _ ↦ globalCoordinate E D χD j) c
    have heval :
        (fun n ↦ globalCharacter E D χD (E.prepared c n)) =
          stageEvaluation E (E.codeIndex c)
            (fun j _ ↦ globalCoordinate E D χD j) c := by
      funext n
      exact (stageEvaluation_eq_globalCharacter E D χD c n).symm
    rw [heval, globalCharacter_single,
      globalCoordinate_codeIndex_of_not_mem E D χD c hc,
      extendRationalCoordinate_one]
    exact hlim

abbrev ContinuumData := Data RationalTriangularPreprocess.ContinuumIndex

end
end RationalTransfiniteExtension
end Wallace
