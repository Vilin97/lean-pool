/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockMatrixProperties
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.Translation
import LeanPool.CoarseGraining.Homogenization.Geometry.CubeMeasure
import LeanPool.CoarseGraining.Homogenization.Geometry.ScaleColoring
import LeanPool.CoarseGraining.Homogenization.Probability.LocalObservable
import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-! # Basic -/

open scoped Matrix.Norms.Elementwise

namespace Homogenization

/-!
# Audit tag (Ch4 rebuild contract `CH04_REBUILD_SURFACE_2026-05-16.md`)

**Internal claim:** the product measurable structure on `Mat d` and
`FullBlockMat d` coincides with their Borel σ-algebras, giving the generic
Bochner-integral API a measurable-target for full coarse matrices.

**Consumed by:**
- `Homogenization/Book/Ch04/AnnealedObjects.lean`
- `Homogenization/Book/Ch04/Theorems/CoarseObservables.lean`
  (`aemeasurable_coarseFullBlockMatrix_cubeSet` and entrywise wrappers)
- `Homogenization/Book/Ch04/Internal/CoarseObservableMeasurability/Mu.lean`

If the single-claim summary above grows into three or more distinct claims,
split or refactor per the rebuild contract.
-/

/-- The product measurable structure on `Mat d` agrees with its Borel
sigma-algebra. This lets the generic Bochner-integral API target full coarse
matrices directly. -/
instance instBorelSpaceMat (d : ℕ) : BorelSpace (Mat d) := by
  change BorelSpace (Fin d → Fin d → ℝ)
  infer_instance

instance instMeasurableSpaceFullBlockMat (d : ℕ) : MeasurableSpace (FullBlockMat d) := by
  change MeasurableSpace (BlockCoord d → BlockCoord d → ℝ)
  infer_instance

/-- The unfolded `2d × 2d` block matrices carry the Borel sigma-algebra coming
from their coordinatewise matrix topology. -/
instance instBorelSpaceFullBlockMat (d : ℕ) : BorelSpace (FullBlockMat d) := by
  change BorelSpace (BlockCoord d → BlockCoord d → ℝ)
  infer_instance

/-- `Matrix.instTopologicalSpace` (the ambient, always-active topology on `Matrix m n R`,
coming from the coordinatewise Pi topology) and the elementwise-norm-derived topology from
`open scoped Matrix.Norms.Elementwise` are only defeq once `Matrix` is unfolded to its
underlying Pi type, which instance search will not do on its own. This head-class cache
resolves the resulting `ContinuousENorm` synthesis gap for every `Matrix m n ℝ`-valued
`Measurable`/`Integrable` statement in this file (and its `Mat d`/`FullBlockMat d`
specializations). -/
private instance instContinuousENormMatrix {m n : Type*} [Fintype m] [Fintype n] :
    ContinuousENorm (Matrix m n ℝ) := by
  show ContinuousENorm (m → n → ℝ)
  infer_instance

/-- Strong ambient measurability of the variational quantity `Mu U P a` for
every deterministic block loading `P`. -/
def HasMeasurableMuFamily {d : ℕ} (U : Set (Vec d)) : Prop :=
  ∀ P : BlockVec d, Measurable fun a : CoeffField d => Mu U P a

/-- Transport `HasMeasurableMuFamily` across pointwise identities for the full
`Mu` family. -/
theorem hasMeasurableMuFamily_of_forall_mu_eq
    {d : ℕ} {U V : Set (Vec d)}
    (hMu : HasMeasurableMuFamily V)
    (hEq : ∀ P : BlockVec d, ∀ a : CoeffField d, Mu U P a = Mu V P a) :
    HasMeasurableMuFamily U := by
  intro P
  have hFun :
      (fun a : CoeffField d => Mu U P a) = fun a => Mu V P a := by
    funext a
    exact hEq P a
  rw [hFun]
  exact hMu P

/-- Two domains share the same measurable `Mu` family whenever their `Mu`
values agree pointwise on every deterministic loading. -/
theorem hasMeasurableMuFamily_iff_of_forall_mu_eq
    {d : ℕ} {U V : Set (Vec d)}
    (hEq : ∀ P : BlockVec d, ∀ a : CoeffField d, Mu U P a = Mu V P a) :
    HasMeasurableMuFamily U ↔ HasMeasurableMuFamily V := by
  constructor
  · intro hMu
    exact hasMeasurableMuFamily_of_forall_mu_eq hMu (fun P a => (hEq P a).symm)
  · intro hMu
    exact hasMeasurableMuFamily_of_forall_mu_eq hMu hEq

/-- The `(r,c)` entry of the coarse inverse-star matrix observable
`a ↦ \sigma_*^{-1}(U; a)`. -/
noncomputable def coarseSigmaStarInvEntryObservable {d : ℕ} (U : Set (Vec d))
    (r c : Fin d) : CoeffField d → ℝ :=
  fun a => (coarseBlockMatrix U a).lowerRight r c

/-- The `(r,c)` entry of the coarse upper-left block observable
`a ↦ b(U; a)`. -/
noncomputable def coarseBEntryObservable {d : ℕ} (U : Set (Vec d))
    (r c : Fin d) : CoeffField d → ℝ :=
  fun a => (coarseBlockMatrix U a).upperLeft r c

/-- The `(r,c)` entry of the mean mixed observable
`a ↦ \sigma_*^{-1}(U; a)\kappa(U; a)`. -/
noncomputable def coarseSigmaStarInvKappaMeanEntryObservable {d : ℕ} (U : Set (Vec d))
    (r c : Fin d) : CoeffField d → ℝ :=
  fun a => -((coarseBlockMatrix U a).lowerLeft r c)

/-- The `(r,c)` entry of the upper-right block of the doubled coarse matrix. -/
noncomputable def coarseUpperRightEntryObservable {d : ℕ} (U : Set (Vec d))
    (r c : Fin d) : CoeffField d → ℝ :=
  fun a => (coarseBlockMatrix U a).upperRight r c

/-- The `(r,c)` entry of the lower-left block of the doubled coarse matrix. -/
noncomputable def coarseLowerLeftEntryObservable {d : ℕ} (U : Set (Vec d))
    (r c : Fin d) : CoeffField d → ℝ :=
  fun a => (coarseBlockMatrix U a).lowerLeft r c

/-- The full doubled coarse matrix observable in the unfolded `2d × 2d` form. -/
noncomputable def coarseFullBlockMatrixObservable {d : ℕ} (U : Set (Vec d)) :
    CoeffField d → FullBlockMat d :=
  fun a => toFullBlockMat (coarseBlockMatrix U a)

/-- The upper-left `d × d` block of an unfolded coarse matrix. -/
def fullBlockMatUpperLeft {d : ℕ} : FullBlockMat d → Mat d :=
  fun M i j => M (Sum.inl i) (Sum.inl j)

/-- The upper-right `d × d` block of an unfolded coarse matrix. -/
def fullBlockMatUpperRight {d : ℕ} : FullBlockMat d → Mat d :=
  fun M i j => M (Sum.inl i) (Sum.inr j)

/-- The lower-left `d × d` block of an unfolded coarse matrix. -/
def fullBlockMatLowerLeft {d : ℕ} : FullBlockMat d → Mat d :=
  fun M i j => M (Sum.inr i) (Sum.inl j)

/-- The lower-right `d × d` block of an unfolded coarse matrix. -/
def fullBlockMatLowerRight {d : ℕ} : FullBlockMat d → Mat d :=
  fun M i j => M (Sum.inr i) (Sum.inr j)

/-- The negative lower-left block, matching the note-facing observable
`\sigma_*^{-1}(U; a)\kappa(U; a)`. -/
def fullBlockMatNegLowerLeft {d : ℕ} : FullBlockMat d → Mat d :=
  fun M i j => -M (Sum.inr i) (Sum.inl j)

/-- The full coarse inverse-star matrix observable `a ↦ \sigma_*^{-1}(U; a)`. -/
noncomputable def coarseSigmaStarInvObservable {d : ℕ} (U : Set (Vec d)) :
    CoeffField d → Mat d :=
  fullBlockMatLowerRight ∘ coarseFullBlockMatrixObservable U

/-- The full coarse upper-left block observable `a ↦ b(U; a)`. -/
noncomputable def coarseBObservable {d : ℕ} (U : Set (Vec d)) :
    CoeffField d → Mat d :=
  fullBlockMatUpperLeft ∘ coarseFullBlockMatrixObservable U

/-- The full mean mixed observable `a ↦ \sigma_*^{-1}(U; a)\kappa(U; a)`. -/
noncomputable def coarseSigmaStarInvKappaMeanObservable {d : ℕ} (U : Set (Vec d)) :
    CoeffField d → Mat d :=
  fullBlockMatNegLowerLeft ∘ coarseFullBlockMatrixObservable U

@[simp] theorem fullBlockMatUpperLeft_apply {d : ℕ} (M : FullBlockMat d) (i j : Fin d) :
    fullBlockMatUpperLeft M i j = M (Sum.inl i) (Sum.inl j) :=
  rfl

@[simp] theorem fullBlockMatUpperRight_apply {d : ℕ} (M : FullBlockMat d) (i j : Fin d) :
    fullBlockMatUpperRight M i j = M (Sum.inl i) (Sum.inr j) :=
  rfl

@[simp] theorem fullBlockMatLowerLeft_apply {d : ℕ} (M : FullBlockMat d) (i j : Fin d) :
    fullBlockMatLowerLeft M i j = M (Sum.inr i) (Sum.inl j) :=
  rfl

@[simp] theorem fullBlockMatLowerRight_apply {d : ℕ} (M : FullBlockMat d) (i j : Fin d) :
    fullBlockMatLowerRight M i j = M (Sum.inr i) (Sum.inr j) :=
  rfl

@[simp] theorem fullBlockMatNegLowerLeft_apply {d : ℕ} (M : FullBlockMat d) (i j : Fin d) :
    fullBlockMatNegLowerLeft M i j = -M (Sum.inr i) (Sum.inl j) :=
  rfl

@[simp] theorem coarseSigmaStarInvEntryObservable_apply {d : ℕ} (U : Set (Vec d))
    (r c : Fin d) (a : CoeffField d) :
    coarseSigmaStarInvEntryObservable U r c a =
      (coarseBlockMatrix U a).lowerRight r c :=
  rfl

@[simp] theorem coarseSigmaStarInvObservable_apply {d : ℕ} (U : Set (Vec d))
    (a : CoeffField d) :
    coarseSigmaStarInvObservable U a = (coarseBlockMatrix U a).lowerRight :=
  rfl

@[simp] theorem coarseBEntryObservable_apply {d : ℕ} (U : Set (Vec d))
    (r c : Fin d) (a : CoeffField d) :
    coarseBEntryObservable U r c a =
      (coarseBlockMatrix U a).upperLeft r c :=
  rfl

@[simp] theorem coarseBObservable_apply {d : ℕ} (U : Set (Vec d))
    (a : CoeffField d) :
    coarseBObservable U a = (coarseBlockMatrix U a).upperLeft :=
  rfl

@[simp] theorem coarseSigmaStarInvKappaMeanEntryObservable_apply {d : ℕ} (U : Set (Vec d))
    (r c : Fin d) (a : CoeffField d) :
    coarseSigmaStarInvKappaMeanEntryObservable U r c a =
      -((coarseBlockMatrix U a).lowerLeft r c) :=
  rfl

@[simp] theorem coarseUpperRightEntryObservable_apply {d : ℕ} (U : Set (Vec d))
    (r c : Fin d) (a : CoeffField d) :
    coarseUpperRightEntryObservable U r c a =
      (coarseBlockMatrix U a).upperRight r c :=
  rfl

@[simp] theorem coarseLowerLeftEntryObservable_apply {d : ℕ} (U : Set (Vec d))
    (r c : Fin d) (a : CoeffField d) :
    coarseLowerLeftEntryObservable U r c a =
      (coarseBlockMatrix U a).lowerLeft r c :=
  rfl

@[simp] theorem coarseSigmaStarInvKappaMeanObservable_apply {d : ℕ} (U : Set (Vec d))
    (a : CoeffField d) :
    coarseSigmaStarInvKappaMeanObservable U a = -((coarseBlockMatrix U a).lowerLeft) :=
  rfl

@[simp] theorem coarseFullBlockMatrixObservable_apply {d : ℕ} (U : Set (Vec d))
    (a : CoeffField d) :
    coarseFullBlockMatrixObservable U a = toFullBlockMat (coarseBlockMatrix U a) :=
  rfl

theorem measurable_fullBlockMatUpperLeft {d : ℕ} :
    Measurable (fullBlockMatUpperLeft (d := d)) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine measurable_pi_iff.2 fun j => ?_
  change Measurable fun M : FullBlockMat d => M (Sum.inl i) (Sum.inl j)
  have hRow : Measurable fun M : FullBlockMat d => M (Sum.inl i) :=
    measurable_pi_apply (Sum.inl i)
  exact Measurable.eval hRow

theorem measurable_fullBlockMatUpperRight {d : ℕ} :
    Measurable (fullBlockMatUpperRight (d := d)) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine measurable_pi_iff.2 fun j => ?_
  change Measurable fun M : FullBlockMat d => M (Sum.inl i) (Sum.inr j)
  have hRow : Measurable fun M : FullBlockMat d => M (Sum.inl i) :=
    measurable_pi_apply (Sum.inl i)
  exact Measurable.eval hRow

theorem measurable_fullBlockMatLowerLeft {d : ℕ} :
    Measurable (fullBlockMatLowerLeft (d := d)) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine measurable_pi_iff.2 fun j => ?_
  change Measurable fun M : FullBlockMat d => M (Sum.inr i) (Sum.inl j)
  have hRow : Measurable fun M : FullBlockMat d => M (Sum.inr i) :=
    measurable_pi_apply (Sum.inr i)
  exact Measurable.eval hRow

theorem measurable_fullBlockMatLowerRight {d : ℕ} :
    Measurable (fullBlockMatLowerRight (d := d)) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine measurable_pi_iff.2 fun j => ?_
  change Measurable fun M : FullBlockMat d => M (Sum.inr i) (Sum.inr j)
  have hRow : Measurable fun M : FullBlockMat d => M (Sum.inr i) :=
    measurable_pi_apply (Sum.inr i)
  exact Measurable.eval hRow

theorem measurable_fullBlockMatNegLowerLeft {d : ℕ} :
    Measurable (fullBlockMatNegLowerLeft (d := d)) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine measurable_pi_iff.2 fun j => ?_
  change Measurable fun M : FullBlockMat d => -M (Sum.inr i) (Sum.inl j)
  have hRow : Measurable fun M : FullBlockMat d => M (Sum.inr i) :=
    measurable_pi_apply (Sum.inr i)
  exact (Measurable.eval hRow).neg

/-- Entrywise evaluation of a Bochner integral of matrix-valued functions. -/
theorem integral_matrix_apply {α m n : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} [Fintype m] [Fintype n]
    {f : α → Matrix m n ℝ} (hf : MeasureTheory.Integrable f μ) (i : m) (j : n) :
    (∫ x, f x ∂μ) i j = ∫ x, f x i j ∂μ := by
  have hRow : ∀ i, MeasureTheory.Integrable (fun x => f x i) μ :=
    fun i => MeasureTheory.Integrable.eval hf i
  calc
    (∫ x, f x ∂μ) i j = (∫ x, f x i ∂μ) j := by
      simpa using! congrArg (fun g => g j)
        (MeasureTheory.eval_integral (μ := μ) (f := f) hRow i)
    _ = ∫ x, f x i j ∂μ := by
      simpa using MeasureTheory.eval_integral (μ := μ) (f := fun x => f x i)
        (fun j => MeasureTheory.Integrable.eval (hRow i) j) j

theorem integrable_coarseSigmaStarInvObservable_of_integrable_coarseFullBlockMatrixObservable
    {d : ℕ} {P : MeasureTheory.Measure (CoeffField d)} {U : Set (Vec d)}
    (hInt : MeasureTheory.Integrable (coarseFullBlockMatrixObservable U) P) :
    MeasureTheory.Integrable (coarseSigmaStarInvObservable U) P := by
  refine MeasureTheory.Integrable.of_eval ?_
  intro i
  refine MeasureTheory.Integrable.of_eval ?_
  intro j
  simpa [coarseSigmaStarInvObservable, coarseFullBlockMatrixObservable, fullBlockMatLowerRight]
    using MeasureTheory.Integrable.eval
      (MeasureTheory.Integrable.eval hInt (Sum.inr i)) (Sum.inr j)

theorem integrable_coarseBObservable_of_integrable_coarseFullBlockMatrixObservable
    {d : ℕ} {P : MeasureTheory.Measure (CoeffField d)} {U : Set (Vec d)}
    (hInt : MeasureTheory.Integrable (coarseFullBlockMatrixObservable U) P) :
    MeasureTheory.Integrable (coarseBObservable U) P := by
  refine MeasureTheory.Integrable.of_eval ?_
  intro i
  refine MeasureTheory.Integrable.of_eval ?_
  intro j
  simpa [coarseBObservable, coarseFullBlockMatrixObservable, fullBlockMatUpperLeft]
    using MeasureTheory.Integrable.eval
      (MeasureTheory.Integrable.eval hInt (Sum.inl i)) (Sum.inl j)

theorem integrable_coarseSigmaStarInvKappaMeanObservable_of_integrable_coarseFullBlockMatrixObservable
    {d : ℕ} {P : MeasureTheory.Measure (CoeffField d)} {U : Set (Vec d)}
    (hInt : MeasureTheory.Integrable (coarseFullBlockMatrixObservable U) P) :
    MeasureTheory.Integrable (coarseSigmaStarInvKappaMeanObservable U) P := by
  refine MeasureTheory.Integrable.of_eval ?_
  intro i
  refine MeasureTheory.Integrable.of_eval ?_
  intro j
  simpa [coarseSigmaStarInvKappaMeanObservable, coarseFullBlockMatrixObservable,
    fullBlockMatNegLowerLeft] using
      (MeasureTheory.Integrable.eval
        (MeasureTheory.Integrable.eval hInt (Sum.inr i)) (Sum.inl j)).fun_neg

theorem isLocalObservable_Mu {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U)
    (P : BlockVec d) :
    IsRestrictionLocalObservable U (fun a => Mu U P a) := by
  intro a₁ a₂ hagree
  have hrestrict : restrictCoeffField U a₁ = restrictCoeffField U a₂ :=
    restrictCoeffField_eq_of_forall_mem_eq hagree
  calc
    Mu U P a₁ = Mu U P (restrictCoeffField U a₁) :=
      (Mu_restrictCoeffField_eq hU P a₁).symm
    _ = Mu U P (restrictCoeffField U a₂) := by rw [hrestrict]
    _ = Mu U P a₂ := Mu_restrictCoeffField_eq hU P a₂

theorem isLocalObservable_coarseBlockMatrix {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) :
    IsRestrictionLocalObservable U (fun a => coarseBlockMatrix U a) := by
  intro a₁ a₂ hagree
  have hrestrict : restrictCoeffField U a₁ = restrictCoeffField U a₂ :=
    restrictCoeffField_eq_of_forall_mem_eq hagree
  calc
    coarseBlockMatrix U a₁ = coarseBlockMatrix U (restrictCoeffField U a₁) := by
      symm
      exact coarseBlockMatrix_restrictCoeffField_eq hU a₁
    _ = coarseBlockMatrix U (restrictCoeffField U a₂) := by rw [hrestrict]
    _ = coarseBlockMatrix U a₂ := coarseBlockMatrix_restrictCoeffField_eq hU a₂

theorem isLocalObservable_coarseFullBlockMatrixObservable {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) :
    IsRestrictionLocalObservable U (coarseFullBlockMatrixObservable U) := by
  intro a₁ a₂ hagree
  simpa [coarseFullBlockMatrixObservable] using
    congrArg toFullBlockMat (isLocalObservable_coarseBlockMatrix hU hagree)

theorem isLocalObservable_coarseSigmaStarInvObservable {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) :
    IsRestrictionLocalObservable U (coarseSigmaStarInvObservable U) := by
  intro a₁ a₂ hagree
  simpa [coarseSigmaStarInvObservable, Function.comp] using
    congrArg fullBlockMatLowerRight
      (isLocalObservable_coarseFullBlockMatrixObservable (U := U) hU hagree)

theorem isLocalObservable_coarseBObservable {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) :
    IsRestrictionLocalObservable U (coarseBObservable U) := by
  intro a₁ a₂ hagree
  simpa [coarseBObservable, Function.comp] using
    congrArg fullBlockMatUpperLeft
      (isLocalObservable_coarseFullBlockMatrixObservable (U := U) hU hagree)

theorem isLocalObservable_coarseSigmaStarInvKappaMeanObservable {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) :
    IsRestrictionLocalObservable U (coarseSigmaStarInvKappaMeanObservable U) := by
  intro a₁ a₂ hagree
  simpa [coarseSigmaStarInvKappaMeanObservable, Function.comp] using
    congrArg fullBlockMatNegLowerLeft
      (isLocalObservable_coarseFullBlockMatrixObservable (U := U) hU hagree)

theorem measurable_coarseSigmaStarInvEntryObservable_of_hasMeasurableMuFamily
    {d : ℕ} {U : Set (Vec d)} (hMu : HasMeasurableMuFamily U) (r c : Fin d) :
    Measurable (coarseSigmaStarInvEntryObservable U r c) := by
  by_cases hrc : r = c
  · subst c
    have hEq :
        coarseSigmaStarInvEntryObservable U r r =
          (fun a : CoeffField d => (2 : ℝ) * Mu U (0, Pi.single r 1) a) := by
      funext a
      simp [coarseSigmaStarInvEntryObservable, coarseBlockMatrix_lowerRight_apply]
    rw [hEq]
    exact measurable_const.mul (hMu (0, Pi.single r 1))
  · have hsum : Measurable fun a : CoeffField d =>
        Mu U ((0, Pi.single r 1) + (0, Pi.single c 1)) a :=
      hMu ((0, Pi.single r 1) + (0, Pi.single c 1))
    have hr : Measurable fun a : CoeffField d => Mu U (0, Pi.single r 1) a :=
      hMu (0, Pi.single r 1)
    have hc : Measurable fun a : CoeffField d => Mu U (0, Pi.single c 1) a :=
      hMu (0, Pi.single c 1)
    have hEq :
        coarseSigmaStarInvEntryObservable U r c =
          (fun a : CoeffField d =>
            Mu U ((0, Pi.single r 1) + (0, Pi.single c 1)) a
              - Mu U (0, Pi.single r 1) a
              - Mu U (0, Pi.single c 1) a) := by
      funext a
      simp [coarseSigmaStarInvEntryObservable, coarseBlockMatrix_lowerRight_apply, hrc]
    rw [hEq]
    exact (hsum.sub hr).sub hc

theorem measurable_coarseBEntryObservable_of_hasMeasurableMuFamily
    {d : ℕ} {U : Set (Vec d)} (hMu : HasMeasurableMuFamily U) (r c : Fin d) :
    Measurable (coarseBEntryObservable U r c) := by
  by_cases hrc : r = c
  · subst c
    have hEq :
        coarseBEntryObservable U r r =
          (fun a : CoeffField d => (2 : ℝ) * Mu U (Pi.single r 1, 0) a) := by
      funext a
      simp [coarseBEntryObservable, coarseBlockMatrix_upperLeft_apply]
    rw [hEq]
    exact measurable_const.mul (hMu (Pi.single r 1, 0))
  · have hsum : Measurable fun a : CoeffField d =>
        Mu U ((Pi.single r 1, 0) + (Pi.single c 1, 0)) a :=
      hMu ((Pi.single r 1, 0) + (Pi.single c 1, 0))
    have hr : Measurable fun a : CoeffField d => Mu U (Pi.single r 1, 0) a :=
      hMu (Pi.single r 1, 0)
    have hc : Measurable fun a : CoeffField d => Mu U (Pi.single c 1, 0) a :=
      hMu (Pi.single c 1, 0)
    have hEq :
        coarseBEntryObservable U r c =
          (fun a : CoeffField d =>
            Mu U ((Pi.single r 1, 0) + (Pi.single c 1, 0)) a
              - Mu U (Pi.single r 1, 0) a
              - Mu U (Pi.single c 1, 0) a) := by
      funext a
      simp [coarseBEntryObservable, coarseBlockMatrix_upperLeft_apply, hrc]
    rw [hEq]
    exact (hsum.sub hr).sub hc

theorem measurable_coarseSigmaStarInvKappaMeanEntryObservable_of_hasMeasurableMuFamily
    {d : ℕ} {U : Set (Vec d)} (hMu : HasMeasurableMuFamily U) (r c : Fin d) :
    Measurable (coarseSigmaStarInvKappaMeanEntryObservable U r c) := by
  have hsum : Measurable fun a : CoeffField d =>
      Mu U ((0, Pi.single r 1) + (Pi.single c 1, 0)) a :=
    hMu ((0, Pi.single r 1) + (Pi.single c 1, 0))
  have hr : Measurable fun a : CoeffField d => Mu U (0, Pi.single r 1) a :=
    hMu (0, Pi.single r 1)
  have hc : Measurable fun a : CoeffField d => Mu U (Pi.single c 1, 0) a :=
    hMu (Pi.single c 1, 0)
  have hEq :
      coarseSigmaStarInvKappaMeanEntryObservable U r c =
        (fun a : CoeffField d =>
          -(Mu U ((0, Pi.single r 1) + (Pi.single c 1, 0)) a
            - Mu U (0, Pi.single r 1) a
            - Mu U (Pi.single c 1, 0) a)) := by
    funext a
    simp [coarseSigmaStarInvKappaMeanEntryObservable, coarseBlockMatrix_lowerLeft_apply]
  rw [hEq]
  exact ((hsum.sub hr).sub hc).neg

theorem measurable_coarseUpperRightEntryObservable_of_hasMeasurableMuFamily
    {d : ℕ} {U : Set (Vec d)} (hMu : HasMeasurableMuFamily U) (r c : Fin d) :
    Measurable (coarseUpperRightEntryObservable U r c) := by
  have hsum : Measurable fun a : CoeffField d =>
      Mu U ((Pi.single r 1, 0) + (0, Pi.single c 1)) a :=
    hMu ((Pi.single r 1, 0) + (0, Pi.single c 1))
  have hr : Measurable fun a : CoeffField d => Mu U (Pi.single r 1, 0) a :=
    hMu (Pi.single r 1, 0)
  have hc : Measurable fun a : CoeffField d => Mu U (0, Pi.single c 1) a :=
    hMu (0, Pi.single c 1)
  have hEq :
      coarseUpperRightEntryObservable U r c =
        (fun a : CoeffField d =>
          Mu U ((Pi.single r 1, 0) + (0, Pi.single c 1)) a
            - Mu U (Pi.single r 1, 0) a
            - Mu U (0, Pi.single c 1) a) := by
    funext a
    simp [coarseUpperRightEntryObservable, coarseBlockMatrix_upperRight_apply]
  rw [hEq]
  exact (hsum.sub hr).sub hc

theorem measurable_coarseLowerLeftEntryObservable_of_hasMeasurableMuFamily
    {d : ℕ} {U : Set (Vec d)} (hMu : HasMeasurableMuFamily U) (r c : Fin d) :
    Measurable (coarseLowerLeftEntryObservable U r c) := by
  have hEq :
      coarseLowerLeftEntryObservable U r c =
        (fun a : CoeffField d => -coarseSigmaStarInvKappaMeanEntryObservable U r c a) := by
    funext a
    simp [coarseLowerLeftEntryObservable, coarseSigmaStarInvKappaMeanEntryObservable]
  rw [hEq]
  exact
    (measurable_coarseSigmaStarInvKappaMeanEntryObservable_of_hasMeasurableMuFamily
      (U := U) hMu r c).neg

theorem measurable_coarseFullBlockMatrixObservable_of_hasMeasurableMuFamily
    {d : ℕ} {U : Set (Vec d)} (hMu : HasMeasurableMuFamily U) :
    Measurable (coarseFullBlockMatrixObservable U) := by
  refine measurable_pi_iff.2 fun α => ?_
  refine measurable_pi_iff.2 fun β => ?_
  cases α <;> cases β
  · simpa [coarseFullBlockMatrixObservable, toFullBlockMat] using!
      measurable_coarseBEntryObservable_of_hasMeasurableMuFamily (U := U) hMu _ _
  · simpa [coarseFullBlockMatrixObservable, toFullBlockMat, coarseUpperRightEntryObservable]
      using! measurable_coarseUpperRightEntryObservable_of_hasMeasurableMuFamily (U := U) hMu _ _
  · simpa [coarseFullBlockMatrixObservable, toFullBlockMat, coarseLowerLeftEntryObservable]
      using! measurable_coarseLowerLeftEntryObservable_of_hasMeasurableMuFamily (U := U) hMu _ _
  · simpa [coarseFullBlockMatrixObservable, toFullBlockMat] using!
      measurable_coarseSigmaStarInvEntryObservable_of_hasMeasurableMuFamily (U := U) hMu _ _

theorem measurable_coarseSigmaStarInvObservable_of_hasMeasurableMuFamily
    {d : ℕ} {U : Set (Vec d)} (hMu : HasMeasurableMuFamily U) :
    Measurable (coarseSigmaStarInvObservable U) := by
  simpa [coarseSigmaStarInvObservable, Function.comp] using
    measurable_fullBlockMatLowerRight.comp
      (measurable_coarseFullBlockMatrixObservable_of_hasMeasurableMuFamily (U := U) hMu)

theorem measurable_coarseBObservable_of_hasMeasurableMuFamily
    {d : ℕ} {U : Set (Vec d)} (hMu : HasMeasurableMuFamily U) :
    Measurable (coarseBObservable U) := by
  simpa [coarseBObservable, Function.comp] using
    measurable_fullBlockMatUpperLeft.comp
      (measurable_coarseFullBlockMatrixObservable_of_hasMeasurableMuFamily (U := U) hMu)

theorem measurable_coarseSigmaStarInvKappaMeanObservable_of_hasMeasurableMuFamily
    {d : ℕ} {U : Set (Vec d)} (hMu : HasMeasurableMuFamily U) :
    Measurable (coarseSigmaStarInvKappaMeanObservable U) := by
  simpa [coarseSigmaStarInvKappaMeanObservable, Function.comp] using
    measurable_fullBlockMatNegLowerLeft.comp
      (measurable_coarseFullBlockMatrixObservable_of_hasMeasurableMuFamily (U := U) hMu)

noncomputable def measurableLocalObservable_Mu {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) (hMu : HasMeasurableMuFamily U) (P : BlockVec d) :
    MeasurableRestrictionLocalObservable d U ℝ where
  toFun := fun a => Mu U P a
  measurable_toFun := hMu P
  isLocal_toFun := isLocalObservable_Mu hU P

noncomputable def measurableLocalObservable_coarseSigmaStarInvEntryObservable
    {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U) (hMu : HasMeasurableMuFamily U)
    (r c : Fin d) :
    MeasurableRestrictionLocalObservable d U ℝ where
  toFun := coarseSigmaStarInvEntryObservable U r c
  measurable_toFun :=
    measurable_coarseSigmaStarInvEntryObservable_of_hasMeasurableMuFamily (U := U) hMu r c
  isLocal_toFun := by
    intro a₁ a₂ hagree
    simpa [coarseSigmaStarInvEntryObservable] using
      congrArg (fun B : BlockMat d => B.lowerRight r c)
        (isLocalObservable_coarseBlockMatrix (U := U) hU hagree)

noncomputable def measurableLocalObservable_coarseBEntryObservable
    {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U) (hMu : HasMeasurableMuFamily U)
    (r c : Fin d) :
    MeasurableRestrictionLocalObservable d U ℝ where
  toFun := coarseBEntryObservable U r c
  measurable_toFun :=
    measurable_coarseBEntryObservable_of_hasMeasurableMuFamily (U := U) hMu r c
  isLocal_toFun := by
    intro a₁ a₂ hagree
    simpa [coarseBEntryObservable] using
      congrArg (fun B : BlockMat d => B.upperLeft r c)
        (isLocalObservable_coarseBlockMatrix (U := U) hU hagree)

noncomputable def measurableLocalObservable_coarseSigmaStarInvKappaMeanEntryObservable
    {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U) (hMu : HasMeasurableMuFamily U)
    (r c : Fin d) :
    MeasurableRestrictionLocalObservable d U ℝ where
  toFun := coarseSigmaStarInvKappaMeanEntryObservable U r c
  measurable_toFun :=
    measurable_coarseSigmaStarInvKappaMeanEntryObservable_of_hasMeasurableMuFamily
      (U := U) hMu r c
  isLocal_toFun := by
    intro a₁ a₂ hagree
    simpa [coarseSigmaStarInvKappaMeanEntryObservable] using
      congrArg (fun B : BlockMat d => -(B.lowerLeft r c))
        (isLocalObservable_coarseBlockMatrix (U := U) hU hagree)

noncomputable def measurableLocalObservable_coarseFullBlockMatrixObservable
    {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U) (hMu : HasMeasurableMuFamily U) :
    MeasurableRestrictionLocalObservable d U (FullBlockMat d) where
  toFun := coarseFullBlockMatrixObservable U
  measurable_toFun :=
    measurable_coarseFullBlockMatrixObservable_of_hasMeasurableMuFamily (U := U) hMu
  isLocal_toFun := isLocalObservable_coarseFullBlockMatrixObservable (U := U) hU

noncomputable def measurableLocalObservable_coarseSigmaStarInvObservable
    {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U) (hMu : HasMeasurableMuFamily U) :
    MeasurableRestrictionLocalObservable d U (Mat d) :=
  MeasurableRestrictionLocalObservable.comp
    (measurableLocalObservable_coarseFullBlockMatrixObservable (U := U) hU hMu)
    fullBlockMatLowerRight measurable_fullBlockMatLowerRight

noncomputable def measurableLocalObservable_coarseBObservable
    {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U) (hMu : HasMeasurableMuFamily U) :
    MeasurableRestrictionLocalObservable d U (Mat d) :=
  MeasurableRestrictionLocalObservable.comp
    (measurableLocalObservable_coarseFullBlockMatrixObservable (U := U) hU hMu)
    fullBlockMatUpperLeft measurable_fullBlockMatUpperLeft

noncomputable def measurableLocalObservable_coarseSigmaStarInvKappaMeanObservable
    {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U) (hMu : HasMeasurableMuFamily U) :
    MeasurableRestrictionLocalObservable d U (Mat d) :=
  MeasurableRestrictionLocalObservable.comp
    (measurableLocalObservable_coarseFullBlockMatrixObservable (U := U) hU hMu)
    fullBlockMatNegLowerLeft measurable_fullBlockMatNegLowerLeft


end Homogenization
