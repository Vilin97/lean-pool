/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuQuadratic
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuOperator.CoeffOperator
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuRecovery.CorrectionSpaceEnergy
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Internal.CoarseObservableMeasurability.Mu
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Internal.FixedCompetitorEnergyMeasurability.Integrals
import LeanPool.CoarseGraining.Homogenization.Probability.LocalEllipticitySlices
import LeanPool.CoarseGraining.Homogenization.Probability.LocalObservable
import LeanPool.CoarseGraining.Homogenization.Probability.RandomFieldMeasurability
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-! # Block Energy Average -/

namespace Homogenization

open scoped Manifold
open scoped ENNReal
open scoped Topology
open Filter

/-!
# Audit tag (Ch4 rebuild contract `CH04_REBUILD_SURFACE_2026-05-16.md`)

**Internal claim:** block-energy-average measurability under quantitative
elliptic slices — combines `Integrals.lean` with the subtype-measurability
of locally σ-measurable coefficient fields landing in a single slice to
produce measurable block-energy-average observables of the form needed by
the `Mu`-candidate construction.

**Consumed by (within `Internal/FixedCompetitorEnergyMeasurability/`):**
`MuObservable.lean`. Upstream chain continues to `Theorems/Mu.lean ::
aemeasurable_Mu_cubeSet`.

If the single-claim summary above grows into three or more distinct
claims, split or refactor per the rebuild contract.
-/

/-- A locally measurable sample-space coefficient field that lands in one
quantitative slice is measurable as a map into that slice subtype. -/
theorem measurable_subtype_mk_quantitativeSlice_of_isLocalSigmaMeasurableOn
    {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    (A : Ω → CoeffField d) (hA : IsPointwiseLocalSigmaMeasurableOn A U)
    (hSlice : ∀ ω : Ω, QuantitativeEllipticSlice U k (A ω)) :
    @Measurable Ω {a : CoeffField d // QuantitativeEllipticSlice U k a}
      _ (QuantitativeEllipticSlice.localMeasurableSpace U k)
      (fun ω => ⟨A ω, hSlice ω⟩) := by
  let As : Ω → {a : CoeffField d // QuantitativeEllipticSlice U k a} :=
    fun ω => ⟨A ω, hSlice ω⟩
  change @Measurable Ω {a : CoeffField d // QuantitativeEllipticSlice U k a}
    _ (QuantitativeEllipticSlice.localMeasurableSpace U k) As
  apply Measurable.of_comap_le
  unfold QuantitativeEllipticSlice.localMeasurableSpace
  rw [MeasurableSpace.comap_comp]
  simpa [As, IsPointwiseLocalSigmaMeasurableOn, Function.comp] using! hA.comap_le

/-- Composition form of fixed-competitor energy measurability on a single
quantitative slice for sample-space-valued coefficient fields. -/
theorem measurable_blockEnergyAverage_comp_quantitativeSlice
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
    (X : BlockState d) (hX : MemBlockL2 U X.eval) :
    Measurable fun ω => blockEnergyAverage U (A ω) X := by
  let As : Ω → {a : CoeffField d // QuantitativeEllipticSlice U k a} :=
    fun ω => ⟨A ω, hSlice ω⟩
  have hAs :
      @Measurable Ω {a : CoeffField d // QuantitativeEllipticSlice U k a}
        _ (QuantitativeEllipticSlice.localMeasurableSpace U k) As :=
    measurable_subtype_mk_quantitativeSlice_of_isLocalSigmaMeasurableOn A hA hSlice
  have hEnergy :
      @Measurable {a : CoeffField d // QuantitativeEllipticSlice U k a}
        ℝ (QuantitativeEllipticSlice.localMeasurableSpace U k) (borel ℝ)
        (fun a => blockEnergyAverage U a.1 X) :=
    measurable_blockEnergyAverage_quantitativeSlice hToL2 X hX
  change Measurable ((fun a : {a : CoeffField d // QuantitativeEllipticSlice U k a} =>
    blockEnergyAverage U a.1 X) ∘ As)
  exact hEnergy.comp hAs

/-- Open finite-measure wrapper for the fixed-slice composition theorem for
fixed-competitor energies. -/
theorem measurable_blockEnergyAverage_comp_quantitativeSlice_of_isOpen_volume_ne_top
    {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hUopen : IsOpen U) (hUfinite : MeasureTheory.volume U ≠ ⊤)
    (A : Ω → CoeffField d) (hA : IsPointwiseLocalSigmaMeasurableOn A U)
    (hSlice : ∀ ω : Ω, QuantitativeEllipticSlice U k (A ω))
    (X : BlockState d) (hX : MemBlockL2 U X.eval) :
    Measurable fun ω => blockEnergyAverage U (A ω) X := by
  exact measurable_blockEnergyAverage_comp_quantitativeSlice
    (measurable_toHilbertMatrixL2_of_isOpen_volume_ne_top hUopen hUfinite)
    A hA hSlice X hX

/-- Countable-slice assembly for fixed-competitor energy averages.  If a
sample-space coefficient field lands on the `k`-th quantitative ellipticity
slice on the measurable piece `t k`, and the pieces cover the whole sample
space, then the energy observable is measurable. -/
theorem measurable_blockEnergyAverage_comp_countable_quantitativeSlice_cover
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
    (X : BlockState d) (hX : MemBlockL2 U X.eval) :
    Measurable fun ω => blockEnergyAverage U (A ω) X := by
  classical
  let f : (k : ℕ) → t k → ℝ :=
    fun k ω => blockEnergyAverage U (A ω.1) X
  have hfm : ∀ k : ℕ, Measurable (f k) := by
    intro k
    have hA_sub : IsPointwiseLocalSigmaMeasurableOn (fun ω : t k => A ω.1) U := by
      simpa [IsPointwiseLocalSigmaMeasurableOn, Function.comp] using!
        hA.comp measurable_subtype_coe
    have hSlice_sub :
        ∀ ω : t k, QuantitativeEllipticSlice U k ((fun ω : t k => A ω.1) ω) := by
      intro ω
      exact hSlice k ω.1 ω.2
    exact measurable_blockEnergyAverage_comp_quantitativeSlice
      (hToL2 k) (fun ω : t k => A ω.1) hA_sub hSlice_sub X hX
  have hagree :
      ∀ (i j : ℕ) (ω : Ω) (hωi : ω ∈ t i) (hωj : ω ∈ t j),
        f i ⟨ω, hωi⟩ = f j ⟨ω, hωj⟩ := by
    intro i j ω hωi hωj
    rfl
  have hLift : Measurable (Set.liftCover t f hagree hcover) :=
    measurable_liftCover t ht f hfm hagree hcover
  have hEq : Set.liftCover t f hagree hcover =
      (fun ω => blockEnergyAverage U (A ω) X) := by
    funext ω
    obtain ⟨k, hωk⟩ : ∃ k : ℕ, ω ∈ t k := by
      have hω_cover : ω ∈ ⋃ k : ℕ, t k := by
        rw [hcover]
        exact Set.mem_univ ω
      exact Set.mem_iUnion.mp hω_cover
    rw [Set.liftCover_of_mem (S := t) (f := f) (hf := hagree) (hS := hcover) hωk]
  simpa [hEq] using hLift

/-- Almost-everywhere countable-slice assembly for fixed-competitor energy
averages.  This is the AE version used after local ellipticity supplies an
almost-sure countable quantitative-slice cover. -/
theorem aemeasurable_blockEnergyAverage_comp_countable_quantitativeSlice_cover
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
    (X : BlockState d) (hX : MemBlockL2 U X.eval) :
    AEMeasurable (fun ω => blockEnergyAverage U (A ω) X) μ := by
  classical
  let S : Set Ω := ⋃ k : ℕ, t k
  let cover : Option ℕ → Set Ω
    | none => Sᶜ
    | some k => t k
  let f : (i : Option ℕ) → cover i → ℝ
    | none, _ => 0
    | some k, ω => blockEnergyAverage U (A ω.1) X
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
          measurable_blockEnergyAverage_comp_quantitativeSlice
            (hToL2 k) (fun ω : cover (some k) => A ω.1) hA_sub hSlice_sub X hX
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
      (fun ω => blockEnergyAverage U (A ω) X) =ᵐ[μ] Set.liftCover cover f hagree hcover := by
    filter_upwards [hcover_ae] with ω hωS
    obtain ⟨k, hωk⟩ := Set.mem_iUnion.mp hωS
    rw [Set.liftCover_of_mem
      (S := cover) (f := f) (hf := hagree) (hS := hcover) (i := some k)
      (by simpa [cover] using hωk)]
  exact hLift.aemeasurable.congr hEq.symm

/-- If the raw quantitative-slice membership sets are measurable and cover the
sample space, then the countable-slice fixed-energy assembly theorem applies
directly to those sets. -/
theorem measurable_blockEnergyAverage_comp_quantitativeSlice_sets
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
    (X : BlockState d) (hX : MemBlockL2 U X.eval) :
    Measurable fun ω => blockEnergyAverage U (A ω) X := by
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
  exact measurable_blockEnergyAverage_comp_countable_quantitativeSlice_cover
    hToL2 A hA t ht hcover_set (fun k ω hω => hω) X hX

/-- AE version of `measurable_blockEnergyAverage_comp_quantitativeSlice_sets`.
This is the immediate handoff from an almost-sure countable slice-existence
statement, provided the raw slice-membership sets are measurable. -/
theorem aemeasurable_blockEnergyAverage_comp_quantitativeSlice_sets
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
    (X : BlockState d) (hX : MemBlockL2 U X.eval) :
    AEMeasurable (fun ω => blockEnergyAverage U (A ω) X) μ := by
  classical
  let t : ℕ → Set Ω := fun k => {ω : Ω | QuantitativeEllipticSlice U k (A ω)}
  have ht : ∀ k : ℕ, MeasurableSet (t k) := hSliceMeas
  have hcover_set_ae : ∀ᵐ ω ∂μ, ω ∈ ⋃ k : ℕ, t k := by
    filter_upwards [hcover_ae] with ω hω
    exact Set.mem_iUnion.mpr hω
  exact aemeasurable_blockEnergyAverage_comp_countable_quantitativeSlice_cover
    μ hToL2 A hA t ht hcover_set_ae (fun k ω hω => hω) X hX

/-- Open finite-measure wrapper for the AE fixed-energy slice-set assembly
theorem. -/
theorem aemeasurable_blockEnergyAverage_comp_quantitativeSlice_sets_of_isOpen_volume_ne_top
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hUopen : IsOpen U) (hUfinite : MeasureTheory.volume U ≠ ⊤)
    (A : Ω → CoeffField d) (hA : IsPointwiseLocalSigmaMeasurableOn A U)
    (hSliceMeas :
      ∀ k : ℕ, MeasurableSet {ω : Ω | QuantitativeEllipticSlice U k (A ω)})
    (hcover_ae : ∀ᵐ ω ∂μ, ∃ k : ℕ, QuantitativeEllipticSlice U k (A ω))
    (X : BlockState d) (hX : MemBlockL2 U X.eval) :
    AEMeasurable (fun ω => blockEnergyAverage U (A ω) X) μ := by
  exact aemeasurable_blockEnergyAverage_comp_quantitativeSlice_sets μ
    (fun _k => measurable_toHilbertMatrixL2_of_isOpen_volume_ne_top hUopen hUfinite)
    A hA hSliceMeas hcover_ae X hX

/-- Origin-open-cube handoff from almost-sure local uniform ellipticity to
fixed-energy `AEMeasurable`, conditional on measurability of the raw
quantitative-slice membership sets. -/
theorem aemeasurable_blockEnergyAverage_comp_openCubeSet_originCube_of_ae_locallyUniformlyElliptic
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    {d : ℕ} (n : ℤ)
    (A : Ω → CoeffField d)
    (hA : IsPointwiseLocalSigmaMeasurableOn A (openCubeSet (originCube d n)))
    (hloc : ∀ᵐ ω ∂μ, IsLocallyUniformlyElliptic (A ω))
    (hSliceMeas :
      ∀ k : ℕ,
        MeasurableSet
          {ω : Ω | QuantitativeEllipticSlice (openCubeSet (originCube d n)) k (A ω)})
    (X : BlockState d) (hX : MemBlockL2 (openCubeSet (originCube d n)) X.eval) :
    AEMeasurable
      (fun ω => blockEnergyAverage (openCubeSet (originCube d n)) (A ω) X) μ := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube d n))) :=
    (isOpenBoundedConvexDomain_openCubeSet (originCube d n)).isFiniteMeasure_restrict_volume
  have hcover_ae :
      ∀ᵐ ω ∂μ,
        ∃ k : ℕ, QuantitativeEllipticSlice (openCubeSet (originCube d n)) k (A ω) :=
    hloc.mono fun _ω hω => hω.exists_quantitativeEllipticSlice_openCubeSet_originCube n
  exact aemeasurable_blockEnergyAverage_comp_quantitativeSlice_sets_of_isOpen_volume_ne_top
    μ (isOpen_openCubeSet (originCube d n))
    (ne_of_lt (volume_openCubeSet_lt_top (originCube d n)))
    A hA hSliceMeas hcover_ae X hX

theorem blockEnergyAverage_restrictCoeffField_eq {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) (a : CoeffField d) (X : BlockState d) :
    blockEnergyAverage U (restrictCoeffField U a) X = blockEnergyAverage U a X := by
  exact volumeAverage_blockEnergyDensity_restrictCoeffField_eq hU a X

theorem blockEnergyAverage_eq_of_forall_mem_eq {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) {a₁ a₂ : CoeffField d} (X : BlockState d)
    (hEq : ∀ x ∈ U, a₁ x = a₂ x) :
    blockEnergyAverage U a₁ X = blockEnergyAverage U a₂ X := by
  unfold blockEnergyAverage volumeAverage
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem hU] with x hx
  have hax : a₁ x = a₂ x := hEq x hx
  simp [blockEnergyDensity, blockCoeffField, hax]

theorem isLocalObservable_blockEnergyAverage {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) (X : BlockState d) :
    IsRestrictionLocalObservable U (fun a : CoeffField d => blockEnergyAverage U a X) := by
  intro a₁ a₂ hEq
  exact blockEnergyAverage_eq_of_forall_mem_eq hU X hEq

theorem measurable_blockEnergyAverage_restrictionSigma_of_measurable
    {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U) (X : BlockState d)
    (hX : Measurable fun a : CoeffField d => blockEnergyAverage U a X) :
    @Measurable (CoeffField d) ℝ (RestrictionSigma U) _
      (fun a => blockEnergyAverage U a X) :=
  measurable_of_isLocalObservable_restrictionSigma hX
    (isLocalObservable_blockEnergyAverage hU X)

noncomputable def measurableLocalObservable_blockEnergyAverage_of_measurable
    {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U) (X : BlockState d)
    (hX : Measurable fun a : CoeffField d => blockEnergyAverage U a X) :
    MeasurableRestrictionLocalObservable d U ℝ where
  toFun := fun a => blockEnergyAverage U a X
  measurable_toFun := hX
  isLocal_toFun := isLocalObservable_blockEnergyAverage hU X
end Homogenization
