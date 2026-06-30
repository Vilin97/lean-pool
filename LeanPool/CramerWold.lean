/-
Copyright (c) 2026 Lazar Milikic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lazar Milikic
-/

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.IdentDistrib

/-!
# The Cramer-Wold theorem

Source: doi:10.1112/jlms/s1-11.4.290
Authors: Lazar Milikic
Status: verified
Main declarations: `LeanPool.CramerWold.euclideanSpace_measure_eq_of_forall_inner_map_eq`
Tags: probability, measure-theory, characteristic-functions, cramer-wold
MSC: 60B11, 60E10, 28A33
-/

/-!
## Mathematical overview

This file packages the Cramer-Wold theorem as a reusable family of measure and probability-law
extensionality lemmas. The Euclidean-space statements give the classical finite-dimensional
theorem. The Banach-space statements use all continuous linear maps to `ℝ`; the Hilbert-space
statements rewrite those projections as scalar products `x ↦ ⟪t, x⟫_ℝ`.

The proof is a direct characteristic-function argument: equality of all one-dimensional projected
laws gives equality of `charFunDual`, and Mathlib's `Measure.ext_of_charFunDual` recovers the
original finite measure.
-/

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace LeanPool
namespace CramerWold

section DualMeasures

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

/-- Finite measures on a real Banach space are determined by their one-dimensional
continuous-linear projections. -/
theorem measure_eq_of_forall_dual_map_eq {μ ν : Measure E} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (h : ∀ L : StrongDual ℝ E, μ.map L = ν.map L) :
    μ = ν := by
  apply Measure.ext_of_charFunDual
  ext L
  rw [charFunDual_eq_charFun_map_one, h L, charFunDual_eq_charFun_map_one]

/-- Cramer-Wold as an extensionality criterion for finite measures, in continuous-dual form. -/
theorem measure_eq_iff_forall_dual_map_eq {μ ν : Measure E} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    μ = ν ↔ ∀ L : StrongDual ℝ E, μ.map L = ν.map L := by
  constructor
  · intro h L
    rw [h]
  · exact measure_eq_of_forall_dual_map_eq

/-- Probability measures on a real Banach space are determined by all continuous-linear
one-dimensional projections. -/
theorem probabilityMeasure_eq_of_forall_dual_map_eq (μ ν : ProbabilityMeasure E)
    (h : ∀ L : StrongDual ℝ E, (μ : Measure E).map L = (ν : Measure E).map L) :
    μ = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  exact measure_eq_of_forall_dual_map_eq h

/-- Cramer-Wold as an extensionality criterion for probability measures, in continuous-dual form. -/
theorem probabilityMeasure_eq_iff_forall_dual_map_eq (μ ν : ProbabilityMeasure E) :
    μ = ν ↔ ∀ L : StrongDual ℝ E, (μ : Measure E).map L = (ν : Measure E).map L := by
  constructor
  · intro h L
    rw [h]
  · exact probabilityMeasure_eq_of_forall_dual_map_eq μ ν

end DualMeasures

section InnerProductMeasures

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E]

/-- The characteristic function at `t` is the real characteristic function of the scalar projection
`x ↦ ⟪t, x⟫_ℝ` at `1`. -/
lemma charFun_eq_charFun_map_inner_one (μ : Measure E) (t : E) :
    charFun μ t = charFun (μ.map (fun x : E => ⟪t, x⟫_ℝ)) 1 := by
  rw [charFun_eq_charFunDual_toDualMap, charFunDual_eq_charFun_map_one]
  have hfun :
      (⇑((InnerProductSpace.toDualMap ℝ E) t)) = (fun x : E => ⟪t, x⟫_ℝ) := by
    ext x
    rfl
  rw [hfun]

variable [SecondCountableTopology E] [CompleteSpace E]

/-- Finite measures on a real Hilbert space are determined by scalar inner-product projections. -/
theorem measure_eq_of_forall_inner_map_eq {μ ν : Measure E} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν]
    (h :
      ∀ t : E,
        μ.map (fun x : E => ⟪t, x⟫_ℝ) =
          ν.map (fun x : E => ⟪t, x⟫_ℝ)) :
    μ = ν := by
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_eq_charFun_map_inner_one μ t, charFun_eq_charFun_map_inner_one ν t, h t]

/-- Cramer-Wold as an extensionality criterion for finite measures on a real Hilbert space. -/
theorem measure_eq_iff_forall_inner_map_eq {μ ν : Measure E} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    μ = ν ↔
      ∀ t : E,
        μ.map (fun x : E => ⟪t, x⟫_ℝ) =
          ν.map (fun x : E => ⟪t, x⟫_ℝ) := by
  constructor
  · intro h t
    rw [h]
  · exact measure_eq_of_forall_inner_map_eq

/-- Probability measures on a real Hilbert space are determined by scalar inner-product
projections. -/
theorem probabilityMeasure_eq_of_forall_inner_map_eq (μ ν : ProbabilityMeasure E)
    (h :
      ∀ t : E,
        (μ : Measure E).map (fun x : E => ⟪t, x⟫_ℝ) =
          (ν : Measure E).map (fun x : E => ⟪t, x⟫_ℝ)) :
    μ = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  exact measure_eq_of_forall_inner_map_eq h

/-- Cramer-Wold as an extensionality criterion for probability measures on a real Hilbert space. -/
theorem probabilityMeasure_eq_iff_forall_inner_map_eq (μ ν : ProbabilityMeasure E) :
    μ = ν ↔
      ∀ t : E,
        (μ : Measure E).map (fun x : E => ⟪t, x⟫_ℝ) =
          (ν : Measure E).map (fun x : E => ⟪t, x⟫_ℝ) := by
  constructor
  · intro h t
    rw [h]
  · exact probabilityMeasure_eq_of_forall_inner_map_eq μ ν

end InnerProductMeasures

section EuclideanMeasures

variable {n : ℕ}

/-- The classical finite-dimensional Cramer-Wold theorem for finite measures on `ℝ^n`,
represented by `EuclideanSpace ℝ (Fin n)`. -/
theorem euclideanSpace_measure_eq_of_forall_inner_map_eq
    {μ ν : Measure (EuclideanSpace ℝ (Fin n))} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h :
      ∀ t : EuclideanSpace ℝ (Fin n),
        μ.map (fun x : EuclideanSpace ℝ (Fin n) => ⟪t, x⟫_ℝ) =
          ν.map (fun x : EuclideanSpace ℝ (Fin n) => ⟪t, x⟫_ℝ)) :
    μ = ν :=
  measure_eq_of_forall_inner_map_eq h

/-- Cramer-Wold as an extensionality criterion for finite measures on `ℝ^n`, represented by
`EuclideanSpace ℝ (Fin n)`. -/
theorem euclideanSpace_measure_eq_iff_forall_inner_map_eq
    {μ ν : Measure (EuclideanSpace ℝ (Fin n))} [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    μ = ν ↔
      ∀ t : EuclideanSpace ℝ (Fin n),
        μ.map (fun x : EuclideanSpace ℝ (Fin n) => ⟪t, x⟫_ℝ) =
          ν.map (fun x : EuclideanSpace ℝ (Fin n) => ⟪t, x⟫_ℝ) :=
  measure_eq_iff_forall_inner_map_eq

/-- Probability measures on `ℝ^n`, represented by `EuclideanSpace ℝ (Fin n)`, are determined by
all scalar projections. -/
theorem euclideanSpace_probabilityMeasure_eq_of_forall_inner_map_eq
    (μ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (h :
      ∀ t : EuclideanSpace ℝ (Fin n),
        (μ : Measure (EuclideanSpace ℝ (Fin n))).map
            (fun x : EuclideanSpace ℝ (Fin n) => ⟪t, x⟫_ℝ) =
          (ν : Measure (EuclideanSpace ℝ (Fin n))).map
            (fun x : EuclideanSpace ℝ (Fin n) => ⟪t, x⟫_ℝ)) :
    μ = ν :=
  probabilityMeasure_eq_of_forall_inner_map_eq μ ν h

/-- Cramer-Wold as an extensionality criterion for probability measures on `ℝ^n`, represented by
`EuclideanSpace ℝ (Fin n)`. -/
theorem euclideanSpace_probabilityMeasure_eq_iff_forall_inner_map_eq
    (μ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) :
    μ = ν ↔
      ∀ t : EuclideanSpace ℝ (Fin n),
        (μ : Measure (EuclideanSpace ℝ (Fin n))).map
            (fun x : EuclideanSpace ℝ (Fin n) => ⟪t, x⟫_ℝ) =
          (ν : Measure (EuclideanSpace ℝ (Fin n))).map
            (fun x : EuclideanSpace ℝ (Fin n) => ⟪t, x⟫_ℝ) :=
  probabilityMeasure_eq_iff_forall_inner_map_eq μ ν

end EuclideanMeasures

section DualRandomVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
  {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {Q : Measure Ω'} {X : Ω → E} {Y : Ω' → E}
  [IsFiniteMeasure P] [IsFiniteMeasure Q]

/-- If all continuous-linear real projections of two random variables are identically distributed,
then the random variables themselves are identically distributed. -/
theorem identDistrib_of_forall_dual_comp_identDistrib
    (hX : AEMeasurable X P) (hY : AEMeasurable Y Q)
    (h :
      ∀ L : StrongDual ℝ E,
        IdentDistrib (fun ω => L (X ω)) (fun ω => L (Y ω)) P Q) :
    IdentDistrib X Y P Q := by
  refine ⟨hX, hY, ?_⟩
  apply measure_eq_of_forall_dual_map_eq
  intro L
  rw [AEMeasurable.map_map_of_aemeasurable
      (by fun_prop : AEMeasurable L (P.map X)) hX,
    AEMeasurable.map_map_of_aemeasurable
      (by fun_prop : AEMeasurable L (Q.map Y)) hY]
  exact (h L).map_eq

/-- Identical distribution is equivalent to identical distribution of every continuous-linear
real projection. -/
theorem identDistrib_iff_forall_dual_comp_identDistrib
    (hX : AEMeasurable X P) (hY : AEMeasurable Y Q) :
    IdentDistrib X Y P Q ↔
      ∀ L : StrongDual ℝ E,
        IdentDistrib (fun ω => L (X ω)) (fun ω => L (Y ω)) P Q := by
  constructor
  · intro h L
    exact h.comp (by fun_prop : Measurable L)
  · exact identDistrib_of_forall_dual_comp_identDistrib hX hY

/-- Equality of laws follows from identical distribution of all continuous-linear real
projections of random variables with those laws. -/
theorem law_eq_of_forall_dual_comp_identDistrib {μ ν : Measure E}
    (hX : HasLaw X μ P) (hY : HasLaw Y ν Q)
    (h :
      ∀ L : StrongDual ℝ E,
        IdentDistrib (fun ω => L (X ω)) (fun ω => L (Y ω)) P Q) :
    μ = ν := by
  have hXY :
      IdentDistrib X Y P Q :=
    identDistrib_of_forall_dual_comp_identDistrib hX.aemeasurable hY.aemeasurable h
  rw [← hX.map_eq, ← hY.map_eq]
  exact hXY.map_eq

end DualRandomVariables

section InnerProductRandomVariables

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
  {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {Q : Measure Ω'} {X : Ω → E} {Y : Ω' → E}
  [IsFiniteMeasure P] [IsFiniteMeasure Q]

/-- If all scalar inner-product projections of two random variables are identically distributed,
then the random variables themselves are identically distributed. -/
theorem identDistrib_of_forall_inner_comp_identDistrib
    (hX : AEMeasurable X P) (hY : AEMeasurable Y Q)
    (h :
      ∀ t : E,
        IdentDistrib (fun ω => ⟪t, X ω⟫_ℝ) (fun ω => ⟪t, Y ω⟫_ℝ) P Q) :
    IdentDistrib X Y P Q := by
  refine ⟨hX, hY, ?_⟩
  apply measure_eq_of_forall_inner_map_eq
  intro t
  rw [AEMeasurable.map_map_of_aemeasurable
      (by fun_prop : AEMeasurable (fun x : E => ⟪t, x⟫_ℝ) (P.map X)) hX,
    AEMeasurable.map_map_of_aemeasurable
      (by fun_prop : AEMeasurable (fun x : E => ⟪t, x⟫_ℝ) (Q.map Y)) hY]
  exact (h t).map_eq

/-- Identical distribution is equivalent to identical distribution of every scalar inner-product
projection. -/
theorem identDistrib_iff_forall_inner_comp_identDistrib
    (hX : AEMeasurable X P) (hY : AEMeasurable Y Q) :
    IdentDistrib X Y P Q ↔
      ∀ t : E,
        IdentDistrib (fun ω => ⟪t, X ω⟫_ℝ) (fun ω => ⟪t, Y ω⟫_ℝ) P Q := by
  constructor
  · intro h t
    exact h.comp (by fun_prop : Measurable fun x : E => ⟪t, x⟫_ℝ)
  · exact identDistrib_of_forall_inner_comp_identDistrib hX hY

/-- Equality of laws follows from identical distribution of all scalar inner-product projections
of random variables with those laws. -/
theorem law_eq_of_forall_inner_comp_identDistrib {μ ν : Measure E}
    (hX : HasLaw X μ P) (hY : HasLaw Y ν Q)
    (h :
      ∀ t : E,
        IdentDistrib (fun ω => ⟪t, X ω⟫_ℝ) (fun ω => ⟪t, Y ω⟫_ℝ) P Q) :
    μ = ν := by
  have hXY :
      IdentDistrib X Y P Q :=
    identDistrib_of_forall_inner_comp_identDistrib hX.aemeasurable hY.aemeasurable h
  rw [← hX.map_eq, ← hY.map_eq]
  exact hXY.map_eq

end InnerProductRandomVariables

section DualHasLaw

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → E}
  {μ : Measure E} [IsFiniteMeasure P] [IsFiniteMeasure μ]

/-- A random variable has law `μ` if all of its continuous-linear real projections have the
corresponding projected laws of `μ`. -/
theorem hasLaw_of_forall_dual_comp_hasLaw
    (hX : AEMeasurable X P)
    (h : ∀ L : StrongDual ℝ E, HasLaw (fun ω => L (X ω)) (μ.map L) P) :
    HasLaw X μ P where
  aemeasurable := hX
  map_eq := by
    apply measure_eq_of_forall_dual_map_eq
    intro L
    rw [AEMeasurable.map_map_of_aemeasurable
      (by fun_prop : AEMeasurable L (P.map X)) hX]
    exact (h L).map_eq

/-- A random variable has law `μ` iff every continuous-linear real projection has the projected
law of `μ`. -/
theorem hasLaw_iff_forall_dual_comp_hasLaw (hX : AEMeasurable X P) :
    HasLaw X μ P ↔
      ∀ L : StrongDual ℝ E, HasLaw (fun ω => L (X ω)) (μ.map L) P := by
  constructor
  · intro h L
    have hL : HasLaw L (μ.map L) μ := ⟨(by fun_prop), rfl⟩
    exact hL.comp h
  · exact hasLaw_of_forall_dual_comp_hasLaw hX

end DualHasLaw

section InnerProductHasLaw

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → E}
  {μ : Measure E} [IsFiniteMeasure P] [IsFiniteMeasure μ]

/-- A random variable has law `μ` if all of its scalar inner-product projections have the
corresponding projected laws of `μ`. -/
theorem hasLaw_of_forall_inner_comp_hasLaw
    (hX : AEMeasurable X P)
    (h :
      ∀ t : E,
        HasLaw (fun ω => ⟪t, X ω⟫_ℝ) (μ.map (fun x : E => ⟪t, x⟫_ℝ)) P) :
    HasLaw X μ P where
  aemeasurable := hX
  map_eq := by
    apply measure_eq_of_forall_inner_map_eq
    intro t
    rw [AEMeasurable.map_map_of_aemeasurable
      (by fun_prop : AEMeasurable (fun x : E => ⟪t, x⟫_ℝ) (P.map X)) hX]
    exact (h t).map_eq

/-- A random variable has law `μ` iff every scalar inner-product projection has the projected
law of `μ`. -/
theorem hasLaw_iff_forall_inner_comp_hasLaw (hX : AEMeasurable X P) :
    HasLaw X μ P ↔
      ∀ t : E,
        HasLaw (fun ω => ⟪t, X ω⟫_ℝ) (μ.map (fun x : E => ⟪t, x⟫_ℝ)) P := by
  constructor
  · intro h t
    have hproj : HasLaw (fun x : E => ⟪t, x⟫_ℝ)
        (μ.map (fun x : E => ⟪t, x⟫_ℝ)) μ := ⟨(by fun_prop), rfl⟩
    exact hproj.comp h
  · exact hasLaw_of_forall_inner_comp_hasLaw hX

end InnerProductHasLaw

end CramerWold
end LeanPool
