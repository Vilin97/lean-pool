/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuQuadratic
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuOperator.CoeffOperator
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuRecovery.CorrectionSpaceEnergy
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Internal.CoarseObservableMeasurability.Mu
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Internal.FixedCompetitorEnergyMeasurability.BlockEnergyAverage
public import LeanPool.CoarseGraining.Homogenization.Probability.LocalEllipticitySlices
public import LeanPool.CoarseGraining.Homogenization.Probability.LocalObservable
public import LeanPool.CoarseGraining.Homogenization.Probability.RandomFieldMeasurability
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.MeasureTheory.Function.UniformIntegrable

/-! # Mu Observable -/

@[expose] public section

namespace Homogenization

open scoped Manifold
open scoped ENNReal
open scoped Topology
open Filter

/-!
# Audit tag (Ch4 rebuild contract `CH04_REBUILD_SURFACE_2026-05-16.md`)

**Internal claim:** measurability of the `Mu` candidate viewed as a
functional of the coefficient field, composed through the measurable
block-energy-average machinery of `BlockEnergyAverage.lean`. This is the
top of the `FixedCompetitorEnergyMeasurability/` chain — every preceding
file in this directory feeds into the proofs here.

**Consumed by:** the umbrella module
`FixedCompetitorEnergyMeasurability.lean`, then
`Internal/AEESliceAssembly/{BlockEnergyAverage, MuFamily}.lean`, then
`Theorems/Mu.lean :: aemeasurable_Mu_cubeSet` (and the AEE-slice variant
`aemeasurable_Mu_cubeSet_of_measurable_aeeQuantitativeSlice`).

If the single-claim summary above grows into three or more distinct
claims, split or refactor per the rebuild contract.
-/

theorem measurable_Mu_comp_of_measurable_blockEnergyAverage_affineField_denseSeq
    {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (A : Ω → CoeffField d)
    (R : MuCorrectionSpaceRecoveryData U)
    [TopologicalSpace.SeparableSpace ↥R.correctionSpace]
    (system : ∀ ω : Ω, MuOperatorSystemData U (A ω))
    (mu_eq_muCandidate :
      ∀ ω : Ω, ∀ P : BlockVec d,
        Mu U P (A ω) =
          ((system ω).toMuOperatorRealization.toMuHilbertRealization
              R.toMuCorrectionSpaceData).muCandidate P)
    (P : BlockVec d)
    (hMeas :
      ∀ n : ℕ,
        Measurable fun ω : Ω =>
          blockEnergyAverage U (A ω)
            (R.affineField P (TopologicalSpace.denseSeq ↥R.correctionSpace n))) :
    Measurable fun ω : Ω => Mu U P (A ω) := by
  rw [show
      (fun ω : Ω => Mu U P (A ω)) =
        fun ω : Ω =>
          ⨅ n : ℕ,
            blockEnergyAverage U (A ω)
              (R.affineField P (TopologicalSpace.denseSeq ↥R.correctionSpace n)) by
        funext ω
        exact R.Mu_eq_iInf_blockEnergyAverage_affineField_denseSeq
          (system ω) (mu_eq_muCandidate ω) P]
  exact Measurable.iInf hMeas

theorem measurable_Mu_of_measurable_blockEnergyAverage_affineField_denseSeq
    {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : MuCorrectionSpaceRecoveryData U)
    [TopologicalSpace.SeparableSpace ↥R.correctionSpace]
    (system : ∀ a : CoeffField d, MuOperatorSystemData U a)
    (mu_eq_muCandidate :
      ∀ a : CoeffField d, ∀ P : BlockVec d,
        Mu U P a =
          ((system a).toMuOperatorRealization.toMuHilbertRealization
              R.toMuCorrectionSpaceData).muCandidate P)
    (P : BlockVec d)
    (hMeas :
      ∀ n : ℕ,
        Measurable fun a : CoeffField d =>
          blockEnergyAverage U a
            (R.affineField P (TopologicalSpace.denseSeq ↥R.correctionSpace n))) :
    Measurable fun a : CoeffField d => Mu U P a := by
  exact measurable_Mu_comp_of_measurable_blockEnergyAverage_affineField_denseSeq
    (A := fun a : CoeffField d => a) R system mu_eq_muCandidate P hMeas

theorem measurable_Mu_of_measurable_weightedFullBlockCoeffEntryIntegrals_denseSeq
    {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : MuCorrectionSpaceRecoveryData U)
    [TopologicalSpace.SeparableSpace ↥R.correctionSpace]
    (system : ∀ a : CoeffField d, MuOperatorSystemData U a)
    (mu_eq_muCandidate :
      ∀ a : CoeffField d, ∀ P : BlockVec d,
        Mu U P a =
          ((system a).toMuOperatorRealization.toMuHilbertRealization
              R.toMuCorrectionSpaceData).muCandidate P)
    (P : BlockVec d)
    (hInt :
      ∀ a : CoeffField d, ∀ n : ℕ, ∀ α β : BlockCoord d,
        MeasureTheory.IntegrableOn
          (fun x =>
            blockEnergyEntryWeight
                (R.affineField P (TopologicalSpace.denseSeq ↥R.correctionSpace n)) α β x *
              toFullBlockMat (blockCoeffField a x) α β)
          U)
    (hMeas :
      ∀ n : ℕ, ∀ α β : BlockCoord d,
        Measurable fun a : CoeffField d =>
          ∫ x in U,
            blockEnergyEntryWeight
                (R.affineField P (TopologicalSpace.denseSeq ↥R.correctionSpace n)) α β x *
              toFullBlockMat (blockCoeffField a x) α β ∂MeasureTheory.volume) :
    Measurable fun a : CoeffField d => Mu U P a := by
  refine measurable_Mu_of_measurable_blockEnergyAverage_affineField_denseSeq
    (U := U) R system mu_eq_muCandidate P ?_
  intro n
  exact measurable_blockEnergyAverage_of_measurable_weightedFullBlockCoeffEntryIntegrals
    (U := U)
    (X := R.affineField P (TopologicalSpace.denseSeq ↥R.correctionSpace n))
    (fun a α β => hInt a n α β)
    (fun α β => hMeas n α β)

theorem measurable_Mu_comp_of_measurable_weightedFullBlockCoeffEntryIntegrals_denseSeq
    {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (A : Ω → CoeffField d)
    (R : MuCorrectionSpaceRecoveryData U)
    [TopologicalSpace.SeparableSpace ↥R.correctionSpace]
    (system : ∀ ω : Ω, MuOperatorSystemData U (A ω))
    (mu_eq_muCandidate :
      ∀ ω : Ω, ∀ P : BlockVec d,
        Mu U P (A ω) =
          ((system ω).toMuOperatorRealization.toMuHilbertRealization
              R.toMuCorrectionSpaceData).muCandidate P)
    (P : BlockVec d)
    (hInt :
      ∀ ω : Ω, ∀ n : ℕ, ∀ α β : BlockCoord d,
        MeasureTheory.IntegrableOn
          (fun x =>
            blockEnergyEntryWeight
                (R.affineField P (TopologicalSpace.denseSeq ↥R.correctionSpace n)) α β x *
              toFullBlockMat (blockCoeffField (A ω) x) α β)
          U)
    (hMeas :
      ∀ n : ℕ, ∀ α β : BlockCoord d,
        Measurable fun ω : Ω =>
          ∫ x in U,
            blockEnergyEntryWeight
                (R.affineField P (TopologicalSpace.denseSeq ↥R.correctionSpace n)) α β x *
              toFullBlockMat (blockCoeffField (A ω) x) α β ∂MeasureTheory.volume) :
    Measurable fun ω : Ω => Mu U P (A ω) := by
  refine measurable_Mu_comp_of_measurable_blockEnergyAverage_affineField_denseSeq
    (A := A) R system mu_eq_muCandidate P ?_
  intro n
  exact measurable_blockEnergyAverage_comp_of_measurable_weightedFullBlockCoeffEntryIntegrals
    (A := A)
    (X := R.affineField P (TopologicalSpace.denseSeq ↥R.correctionSpace n))
    (fun ω α β => hInt ω n α β)
    (fun α β => hMeas n α β)

theorem measurable_Mu_quantitativeSlice_of_measurable_weightedFullBlockCoeffEntryIntegrals_denseSeq
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : MuCorrectionSpaceRecoveryData U)
    [TopologicalSpace.SeparableSpace ↥R.correctionSpace]
    (system :
      ∀ a : {a : CoeffField d // QuantitativeEllipticSlice U k a},
        MuOperatorSystemData U a.1)
    (mu_eq_muCandidate :
      ∀ a : {a : CoeffField d // QuantitativeEllipticSlice U k a}, ∀ P : BlockVec d,
        Mu U P a.1 =
          ((system a).toMuOperatorRealization.toMuHilbertRealization
              R.toMuCorrectionSpaceData).muCandidate P)
    (P : BlockVec d)
    (hMeas :
      ∀ n : ℕ, ∀ α β : BlockCoord d,
        Measurable fun a : {a : CoeffField d // QuantitativeEllipticSlice U k a} =>
          ∫ x in U,
            blockEnergyEntryWeight
                (R.affineField P (TopologicalSpace.denseSeq ↥R.correctionSpace n)) α β x *
              toFullBlockMat (blockCoeffField a.1 x) α β ∂MeasureTheory.volume) :
    Measurable fun a : {a : CoeffField d // QuantitativeEllipticSlice U k a} =>
      Mu U P a.1 := by
  refine measurable_Mu_comp_of_measurable_weightedFullBlockCoeffEntryIntegrals_denseSeq
    (A := fun a : {a : CoeffField d // QuantitativeEllipticSlice U k a} => a.1)
    R system mu_eq_muCandidate P ?_ hMeas
  intro a n α β
  exact a.2.integrableOn_weightedFullBlockCoeffEntry_of_memBlockL2
    (R.affineField_memBlockL2 P (TopologicalSpace.denseSeq ↥R.correctionSpace n)) α β

/-- Note-facing quantitative-slice measurability of `Mu`: once the slice has
the measurable `L²` coefficient realization, fixed competitors are measurable
by the `L¹` entry theorem and `Mu` follows from the dense `iInf` formula. -/
theorem measurable_Mu_quantitativeSlice
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hToL2 :
      @Measurable {a : CoeffField d // QuantitativeEllipticSlice U k a}
        (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
        (QuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
        QuantitativeEllipticSlice.toHilbertMatrixL2)
    (R : MuCorrectionSpaceRecoveryData U)
    [TopologicalSpace.SeparableSpace ↥R.correctionSpace]
    (system :
      ∀ a : {a : CoeffField d // QuantitativeEllipticSlice U k a},
        MuOperatorSystemData U a.1)
    (mu_eq_muCandidate :
      ∀ a : {a : CoeffField d // QuantitativeEllipticSlice U k a}, ∀ P : BlockVec d,
        Mu U P a.1 =
          ((system a).toMuOperatorRealization.toMuHilbertRealization
              R.toMuCorrectionSpaceData).muCandidate P)
    (P : BlockVec d) :
    @Measurable {a : CoeffField d // QuantitativeEllipticSlice U k a}
      ℝ (QuantitativeEllipticSlice.localMeasurableSpace U k) (borel ℝ)
      (fun a => Mu U P a.1) := by
  let : MeasurableSpace {a : CoeffField d // QuantitativeEllipticSlice U k a} :=
    QuantitativeEllipticSlice.localMeasurableSpace U k
  refine measurable_Mu_comp_of_measurable_blockEnergyAverage_affineField_denseSeq
    (A := fun a : {a : CoeffField d // QuantitativeEllipticSlice U k a} => a.1)
    R system mu_eq_muCandidate P ?_
  intro n
  exact measurable_blockEnergyAverage_quantitativeSlice hToL2
    (R.affineField P (TopologicalSpace.denseSeq ↥R.correctionSpace n))
    (R.affineField_memBlockL2 P (TopologicalSpace.denseSeq ↥R.correctionSpace n))

/-- Open finite-measure wrapper for fixed-competitor energy measurability on a
quantitative elliptic slice. -/
theorem measurable_blockEnergyAverage_quantitativeSlice_of_isOpen_volume_ne_top
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hUopen : IsOpen U) (hUfinite : MeasureTheory.volume U ≠ ⊤)
    (X : BlockState d) (hX : MemBlockL2 U X.eval) :
    @Measurable {a : CoeffField d // QuantitativeEllipticSlice U k a}
      ℝ (QuantitativeEllipticSlice.localMeasurableSpace U k) (borel ℝ)
      (fun a => blockEnergyAverage U a.1 X) := by
  exact measurable_blockEnergyAverage_quantitativeSlice
    (measurable_toHilbertMatrixL2_of_isOpen_volume_ne_top hUopen hUfinite) X hX

/-- Open finite-measure wrapper for note-facing quantitative-slice
measurability of `Mu`. -/
theorem measurable_Mu_quantitativeSlice_of_isOpen_volume_ne_top
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hUopen : IsOpen U) (hUfinite : MeasureTheory.volume U ≠ ⊤)
    (R : MuCorrectionSpaceRecoveryData U)
    [TopologicalSpace.SeparableSpace ↥R.correctionSpace]
    (system :
      ∀ a : {a : CoeffField d // QuantitativeEllipticSlice U k a},
        MuOperatorSystemData U a.1)
    (mu_eq_muCandidate :
      ∀ a : {a : CoeffField d // QuantitativeEllipticSlice U k a}, ∀ P : BlockVec d,
        Mu U P a.1 =
          ((system a).toMuOperatorRealization.toMuHilbertRealization
              R.toMuCorrectionSpaceData).muCandidate P)
    (P : BlockVec d) :
    @Measurable {a : CoeffField d // QuantitativeEllipticSlice U k a}
      ℝ (QuantitativeEllipticSlice.localMeasurableSpace U k) (borel ℝ)
      (fun a => Mu U P a.1) := by
  exact measurable_Mu_quantitativeSlice
    (measurable_toHilbertMatrixL2_of_isOpen_volume_ne_top hUopen hUfinite)
    R system mu_eq_muCandidate P

/-- Composition form of quantitative-slice `Mu` measurability for
sample-space-valued coefficient fields landing in one slice. -/
theorem measurable_Mu_comp_quantitativeSlice
    {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hToL2 :
      @Measurable {a : CoeffField d // QuantitativeEllipticSlice U k a}
        (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
        (QuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
        QuantitativeEllipticSlice.toHilbertMatrixL2)
    (A : Ω → CoeffField d) (hA : IsPointwiseLocalSigmaMeasurableOn A U)
    (hSlice : ∀ ω : Ω, QuantitativeEllipticSlice U k (A ω))
    (R : MuCorrectionSpaceRecoveryData U)
    [TopologicalSpace.SeparableSpace ↥R.correctionSpace]
    (system :
      ∀ a : {a : CoeffField d // QuantitativeEllipticSlice U k a},
        MuOperatorSystemData U a.1)
    (mu_eq_muCandidate :
      ∀ a : {a : CoeffField d // QuantitativeEllipticSlice U k a}, ∀ P : BlockVec d,
        Mu U P a.1 =
          ((system a).toMuOperatorRealization.toMuHilbertRealization
              R.toMuCorrectionSpaceData).muCandidate P)
    (P : BlockVec d) :
    Measurable fun ω => Mu U P (A ω) := by
  let As : Ω → {a : CoeffField d // QuantitativeEllipticSlice U k a} :=
    fun ω => ⟨A ω, hSlice ω⟩
  have hAs :
      @Measurable Ω {a : CoeffField d // QuantitativeEllipticSlice U k a}
        _ (QuantitativeEllipticSlice.localMeasurableSpace U k) As :=
    measurable_subtype_mk_quantitativeSlice_of_isLocalSigmaMeasurableOn A hA hSlice
  have hMu :
      @Measurable {a : CoeffField d // QuantitativeEllipticSlice U k a}
        ℝ (QuantitativeEllipticSlice.localMeasurableSpace U k) (borel ℝ)
        (fun a => Mu U P a.1) :=
    measurable_Mu_quantitativeSlice hToL2 R system mu_eq_muCandidate P
  change Measurable ((fun a : {a : CoeffField d // QuantitativeEllipticSlice U k a} =>
    Mu U P a.1) ∘ As)
  exact hMu.comp hAs

/-- Open finite-measure wrapper for the fixed-slice composition theorem for
`Mu`. -/
theorem measurable_Mu_comp_quantitativeSlice_of_isOpen_volume_ne_top
    {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hUopen : IsOpen U) (hUfinite : MeasureTheory.volume U ≠ ⊤)
    (A : Ω → CoeffField d) (hA : IsPointwiseLocalSigmaMeasurableOn A U)
    (hSlice : ∀ ω : Ω, QuantitativeEllipticSlice U k (A ω))
    (R : MuCorrectionSpaceRecoveryData U)
    [TopologicalSpace.SeparableSpace ↥R.correctionSpace]
    (system :
      ∀ a : {a : CoeffField d // QuantitativeEllipticSlice U k a},
        MuOperatorSystemData U a.1)
    (mu_eq_muCandidate :
      ∀ a : {a : CoeffField d // QuantitativeEllipticSlice U k a}, ∀ P : BlockVec d,
        Mu U P a.1 =
          ((system a).toMuOperatorRealization.toMuHilbertRealization
              R.toMuCorrectionSpaceData).muCandidate P)
    (P : BlockVec d) :
    Measurable fun ω => Mu U P (A ω) := by
  exact measurable_Mu_comp_quantitativeSlice
    (measurable_toHilbertMatrixL2_of_isOpen_volume_ne_top hUopen hUfinite)
    A hA hSlice R system mu_eq_muCandidate P

/-- Countable-slice assembly for `Mu`.  On each measurable piece `t k`, the
sample-space coefficient field is only required to land in the corresponding
quantitative ellipticity slice; the countable cover is glued by
`Set.liftCover`. -/
theorem measurable_Mu_comp_countable_quantitativeSlice_cover
    {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hToL2 :
      ∀ k : ℕ,
        @Measurable {a : CoeffField d // QuantitativeEllipticSlice U k a}
          (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
          (QuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
          QuantitativeEllipticSlice.toHilbertMatrixL2)
    (A : Ω → CoeffField d) (hA : IsPointwiseLocalSigmaMeasurableOn A U)
    (t : ℕ → Set Ω) (ht : ∀ k : ℕ, MeasurableSet (t k))
    (hcover : ⋃ k : ℕ, t k = Set.univ)
    (hSlice : ∀ k : ℕ, ∀ ω : Ω, ω ∈ t k → QuantitativeEllipticSlice U k (A ω))
    (R : MuCorrectionSpaceRecoveryData U)
    [TopologicalSpace.SeparableSpace ↥R.correctionSpace]
    (system :
      ∀ k : ℕ, ∀ a : {a : CoeffField d // QuantitativeEllipticSlice U k a},
        MuOperatorSystemData U a.1)
    (mu_eq_muCandidate :
      ∀ k : ℕ, ∀ a : {a : CoeffField d // QuantitativeEllipticSlice U k a},
        ∀ P : BlockVec d,
          Mu U P a.1 =
            (((system k a).toMuOperatorRealization.toMuHilbertRealization
                R.toMuCorrectionSpaceData).muCandidate P))
    (P : BlockVec d) :
    Measurable fun ω => Mu U P (A ω) := by
  classical
  let f : (k : ℕ) → t k → ℝ :=
    fun k ω => Mu U P (A ω.1)
  have hfm : ∀ k : ℕ, Measurable (f k) := by
    intro k
    have hA_sub : IsPointwiseLocalSigmaMeasurableOn (fun ω : t k => A ω.1) U := by
      simpa [IsPointwiseLocalSigmaMeasurableOn, Function.comp] using! hA.comp measurable_subtype_coe
    have hSlice_sub :
        ∀ ω : t k, QuantitativeEllipticSlice U k ((fun ω : t k => A ω.1) ω) := by
      intro ω
      exact hSlice k ω.1 ω.2
    exact measurable_Mu_comp_quantitativeSlice
      (hToL2 k) (fun ω : t k => A ω.1) hA_sub hSlice_sub
      R (system k) (mu_eq_muCandidate k) P
  have hagree :
      ∀ (i j : ℕ) (ω : Ω) (hωi : ω ∈ t i) (hωj : ω ∈ t j),
        f i ⟨ω, hωi⟩ = f j ⟨ω, hωj⟩ := by
    intro i j ω hωi hωj
    rfl
  have hLift : Measurable (Set.liftCover t f hagree hcover) :=
    measurable_liftCover t ht f hfm hagree hcover
  have hEq : Set.liftCover t f hagree hcover =
      (fun ω => Mu U P (A ω)) := by
    funext ω
    obtain ⟨k, hωk⟩ : ∃ k : ℕ, ω ∈ t k := by
      have hω_cover : ω ∈ ⋃ k : ℕ, t k := by
        rw [hcover]
        exact Set.mem_univ ω
      exact Set.mem_iUnion.mp hω_cover
    rw [Set.liftCover_of_mem (S := t) (f := f) (hf := hagree) (hS := hcover) hωk]
  simpa [hEq] using hLift

/-- Almost-everywhere countable-slice assembly for `Mu`.  The theorem adds a
measurable null fallback piece to an AE countable cover and then glues the
slice-wise measurable realizations. -/
theorem aemeasurable_Mu_comp_countable_quantitativeSlice_cover
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hToL2 :
      ∀ k : ℕ,
        @Measurable {a : CoeffField d // QuantitativeEllipticSlice U k a}
          (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
          (QuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
          QuantitativeEllipticSlice.toHilbertMatrixL2)
    (A : Ω → CoeffField d) (hA : IsPointwiseLocalSigmaMeasurableOn A U)
    (t : ℕ → Set Ω) (ht : ∀ k : ℕ, MeasurableSet (t k))
    (hcover_ae : ∀ᵐ ω ∂μ, ω ∈ ⋃ k : ℕ, t k)
    (hSlice : ∀ k : ℕ, ∀ ω : Ω, ω ∈ t k → QuantitativeEllipticSlice U k (A ω))
    (R : MuCorrectionSpaceRecoveryData U)
    [TopologicalSpace.SeparableSpace ↥R.correctionSpace]
    (system :
      ∀ k : ℕ, ∀ a : {a : CoeffField d // QuantitativeEllipticSlice U k a},
        MuOperatorSystemData U a.1)
    (mu_eq_muCandidate :
      ∀ k : ℕ, ∀ a : {a : CoeffField d // QuantitativeEllipticSlice U k a},
        ∀ P : BlockVec d,
          Mu U P a.1 =
            (((system k a).toMuOperatorRealization.toMuHilbertRealization
                R.toMuCorrectionSpaceData).muCandidate P))
    (P : BlockVec d) :
    AEMeasurable (fun ω => Mu U P (A ω)) μ := by
  classical
  let S : Set Ω := ⋃ k : ℕ, t k
  let cover : Option ℕ → Set Ω
    | none => Sᶜ
    | some k => t k
  let f : (i : Option ℕ) → cover i → ℝ
    | none, _ => 0
    | some k, ω => Mu U P (A ω.1)
  have hcover_meas : ∀ i : Option ℕ, MeasurableSet (cover i) := by
    intro i
    cases i with
    | none =>
        exact (MeasurableSet.iUnion ht).compl
    | some k =>
        exact ht k
  have hfm : ∀ i : Option ℕ, Measurable (f i) := by
    intro i
    cases i with
    | none =>
        exact measurable_const
    | some k =>
        have hA_sub : IsPointwiseLocalSigmaMeasurableOn (fun ω : cover (some k) => A ω.1) U := by
          simpa [IsPointwiseLocalSigmaMeasurableOn, Function.comp, cover] using!
            hA.comp measurable_subtype_coe
        have hSlice_sub :
            ∀ ω : cover (some k),
              QuantitativeEllipticSlice U k ((fun ω : cover (some k) => A ω.1) ω) := by
          intro ω
          have hω : ω.1 ∈ t k := by
            simp [cover] at ω
            exact ω.2
          exact hSlice k ω.1 hω
        simpa [f, cover] using
          measurable_Mu_comp_quantitativeSlice
            (hToL2 k) (fun ω : cover (some k) => A ω.1) hA_sub hSlice_sub
            R (system k) (mu_eq_muCandidate k) P
  have hagree :
      ∀ (i j : Option ℕ) (ω : Ω) (hωi : ω ∈ cover i) (hωj : ω ∈ cover j),
        f i ⟨ω, hωi⟩ = f j ⟨ω, hωj⟩ := by
    intro i j ω hωi hωj
    cases i with
    | none =>
        cases j with
        | none =>
            rfl
        | some k =>
            exfalso
            have hωS : ω ∈ S := Set.mem_iUnion.mpr ⟨k, by simpa [cover] using hωj⟩
            have hω_notS : ω ∉ S := by
              simpa [cover] using hωi
            exact hω_notS hωS
    | some k =>
        cases j with
        | none =>
            exfalso
            have hωS : ω ∈ S := Set.mem_iUnion.mpr ⟨k, by simpa [cover] using hωi⟩
            have hω_notS : ω ∉ S := by
              simpa [cover] using hωj
            exact hω_notS hωS
        | some l =>
            rfl
  have hcover : ⋃ i : Option ℕ, cover i = Set.univ := by
    ext ω
    constructor
    · intro _hω
      exact Set.mem_univ ω
    · intro _hω
      by_cases hωS : ω ∈ S
      · obtain ⟨k, hωk⟩ := Set.mem_iUnion.mp hωS
        exact Set.mem_iUnion.mpr ⟨some k, by simpa [cover] using hωk⟩
      · exact Set.mem_iUnion.mpr ⟨none, by simpa [cover] using hωS⟩
  have hLift : Measurable (Set.liftCover cover f hagree hcover) :=
    measurable_liftCover cover hcover_meas f hfm hagree hcover
  have hEq :
      (fun ω => Mu U P (A ω)) =ᵐ[μ] Set.liftCover cover f hagree hcover := by
    filter_upwards [hcover_ae] with ω hωS
    obtain ⟨k, hωk⟩ := Set.mem_iUnion.mp hωS
    rw [Set.liftCover_of_mem
      (S := cover) (f := f) (hf := hagree) (hS := hcover) (i := some k)
      (by simpa [cover] using hωk)]
  exact hLift.aemeasurable.congr hEq.symm

/-- If the raw quantitative-slice membership sets are measurable and cover the
sample space, then the countable-slice `Mu` assembly theorem applies directly
to those sets. -/
theorem measurable_Mu_comp_quantitativeSlice_sets
    {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hToL2 :
      ∀ k : ℕ,
        @Measurable {a : CoeffField d // QuantitativeEllipticSlice U k a}
          (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
          (QuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
          QuantitativeEllipticSlice.toHilbertMatrixL2)
    (A : Ω → CoeffField d) (hA : IsPointwiseLocalSigmaMeasurableOn A U)
    (hSliceMeas :
      ∀ k : ℕ, MeasurableSet {ω : Ω | QuantitativeEllipticSlice U k (A ω)})
    (hcover : ∀ ω : Ω, ∃ k : ℕ, QuantitativeEllipticSlice U k (A ω))
    (R : MuCorrectionSpaceRecoveryData U)
    [TopologicalSpace.SeparableSpace ↥R.correctionSpace]
    (system :
      ∀ k : ℕ, ∀ a : {a : CoeffField d // QuantitativeEllipticSlice U k a},
        MuOperatorSystemData U a.1)
    (mu_eq_muCandidate :
      ∀ k : ℕ, ∀ a : {a : CoeffField d // QuantitativeEllipticSlice U k a},
        ∀ P : BlockVec d,
          Mu U P a.1 =
            (((system k a).toMuOperatorRealization.toMuHilbertRealization
                R.toMuCorrectionSpaceData).muCandidate P))
    (P : BlockVec d) :
    Measurable fun ω => Mu U P (A ω) := by
  classical
  let t : ℕ → Set Ω := fun k => {ω : Ω | QuantitativeEllipticSlice U k (A ω)}
  have ht : ∀ k : ℕ, MeasurableSet (t k) := hSliceMeas
  have hcover_set : ⋃ k : ℕ, t k = Set.univ := by
    ext ω
    constructor
    · intro _hω
      exact Set.mem_univ ω
    · intro _hω
      exact Set.mem_iUnion.mpr (hcover ω)
  exact measurable_Mu_comp_countable_quantitativeSlice_cover
    hToL2 A hA t ht hcover_set (fun k ω hω => hω)
    R system mu_eq_muCandidate P

/-- AE version of `measurable_Mu_comp_quantitativeSlice_sets`.  This is the
selection/assembly handoff from almost-sure slice existence, conditional on
measurability of the raw slice-membership sets. -/
theorem aemeasurable_Mu_comp_quantitativeSlice_sets
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hToL2 :
      ∀ k : ℕ,
        @Measurable {a : CoeffField d // QuantitativeEllipticSlice U k a}
          (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
          (QuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
          QuantitativeEllipticSlice.toHilbertMatrixL2)
    (A : Ω → CoeffField d) (hA : IsPointwiseLocalSigmaMeasurableOn A U)
    (hSliceMeas :
      ∀ k : ℕ, MeasurableSet {ω : Ω | QuantitativeEllipticSlice U k (A ω)})
    (hcover_ae : ∀ᵐ ω ∂μ, ∃ k : ℕ, QuantitativeEllipticSlice U k (A ω))
    (R : MuCorrectionSpaceRecoveryData U)
    [TopologicalSpace.SeparableSpace ↥R.correctionSpace]
    (system :
      ∀ k : ℕ, ∀ a : {a : CoeffField d // QuantitativeEllipticSlice U k a},
        MuOperatorSystemData U a.1)
    (mu_eq_muCandidate :
      ∀ k : ℕ, ∀ a : {a : CoeffField d // QuantitativeEllipticSlice U k a},
        ∀ P : BlockVec d,
          Mu U P a.1 =
            (((system k a).toMuOperatorRealization.toMuHilbertRealization
                R.toMuCorrectionSpaceData).muCandidate P))
    (P : BlockVec d) :
    AEMeasurable (fun ω => Mu U P (A ω)) μ := by
  classical
  let t : ℕ → Set Ω := fun k => {ω : Ω | QuantitativeEllipticSlice U k (A ω)}
  have ht : ∀ k : ℕ, MeasurableSet (t k) := hSliceMeas
  have hcover_set_ae : ∀ᵐ ω ∂μ, ω ∈ ⋃ k : ℕ, t k := by
    filter_upwards [hcover_ae] with ω hω
    exact Set.mem_iUnion.mpr hω
  exact aemeasurable_Mu_comp_countable_quantitativeSlice_cover
    μ hToL2 A hA t ht hcover_set_ae (fun k ω hω => hω)
    R system mu_eq_muCandidate P

/-- Open finite-measure wrapper for the AE `Mu` slice-set assembly theorem. -/
theorem aemeasurable_Mu_comp_quantitativeSlice_sets_of_isOpen_volume_ne_top
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hUopen : IsOpen U) (hUfinite : MeasureTheory.volume U ≠ ⊤)
    (A : Ω → CoeffField d) (hA : IsPointwiseLocalSigmaMeasurableOn A U)
    (hSliceMeas :
      ∀ k : ℕ, MeasurableSet {ω : Ω | QuantitativeEllipticSlice U k (A ω)})
    (hcover_ae : ∀ᵐ ω ∂μ, ∃ k : ℕ, QuantitativeEllipticSlice U k (A ω))
    (R : MuCorrectionSpaceRecoveryData U)
    [TopologicalSpace.SeparableSpace ↥R.correctionSpace]
    (system :
      ∀ k : ℕ, ∀ a : {a : CoeffField d // QuantitativeEllipticSlice U k a},
        MuOperatorSystemData U a.1)
    (mu_eq_muCandidate :
      ∀ k : ℕ, ∀ a : {a : CoeffField d // QuantitativeEllipticSlice U k a},
        ∀ P : BlockVec d,
          Mu U P a.1 =
            (((system k a).toMuOperatorRealization.toMuHilbertRealization
                R.toMuCorrectionSpaceData).muCandidate P))
    (P : BlockVec d) :
    AEMeasurable (fun ω => Mu U P (A ω)) μ := by
  exact aemeasurable_Mu_comp_quantitativeSlice_sets μ
    (fun _k => measurable_toHilbertMatrixL2_of_isOpen_volume_ne_top hUopen hUfinite)
    A hA hSliceMeas hcover_ae R system mu_eq_muCandidate P

/-- Origin-open-cube handoff from almost-sure local uniform ellipticity to
`Mu` `AEMeasurable`, conditional on measurability of the raw quantitative-slice
membership sets. -/
theorem aemeasurable_Mu_comp_openCubeSet_originCube_of_ae_locallyUniformlyElliptic
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    {d : ℕ} (n : ℤ)
    (A : Ω → CoeffField d)
    (hA : IsPointwiseLocalSigmaMeasurableOn A (openCubeSet (originCube d n)))
    (hloc : ∀ᵐ ω ∂μ, IsLocallyUniformlyElliptic (A ω))
    (hSliceMeas :
      ∀ k : ℕ,
        MeasurableSet
          {ω : Ω | QuantitativeEllipticSlice (openCubeSet (originCube d n)) k (A ω)})
    (R : MuCorrectionSpaceRecoveryData (openCubeSet (originCube d n)))
    [TopologicalSpace.SeparableSpace ↥R.correctionSpace]
    (system :
      ∀ k : ℕ,
        ∀ a :
          {a : CoeffField d //
            QuantitativeEllipticSlice (openCubeSet (originCube d n)) k a},
          MuOperatorSystemData (openCubeSet (originCube d n)) a.1)
    (mu_eq_muCandidate :
      ∀ k : ℕ,
        ∀ a :
          {a : CoeffField d //
            QuantitativeEllipticSlice (openCubeSet (originCube d n)) k a},
        ∀ P : BlockVec d,
          Mu (openCubeSet (originCube d n)) P a.1 =
            (((system k a).toMuOperatorRealization.toMuHilbertRealization
                R.toMuCorrectionSpaceData).muCandidate P))
    (P : BlockVec d) :
    AEMeasurable (fun ω => Mu (openCubeSet (originCube d n)) P (A ω)) μ := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube d n))) :=
    (isOpenBoundedConvexDomain_openCubeSet (originCube d n)).isFiniteMeasure_restrict_volume
  have hcover_ae :
      ∀ᵐ ω ∂μ,
        ∃ k : ℕ, QuantitativeEllipticSlice (openCubeSet (originCube d n)) k (A ω) :=
    hloc.mono fun _ω hω => hω.exists_quantitativeEllipticSlice_openCubeSet_originCube n
  exact aemeasurable_Mu_comp_quantitativeSlice_sets_of_isOpen_volume_ne_top
    μ (isOpen_openCubeSet (originCube d n))
    (ne_of_lt (volume_openCubeSet_lt_top (originCube d n)))
    A hA hSliceMeas hcover_ae R system mu_eq_muCandidate P

end Homogenization
