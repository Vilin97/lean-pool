/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuOperator.AEEOperator
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Internal.AEESliceAssembly.BlockEnergyAverage
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Internal.FixedCompetitorEnergyMeasurability

/-! # Mu Family -/

@[expose] public section

namespace Homogenization

open scoped ENNReal
open scoped Topology
open Filter

/-!
# Audit tag (Ch4 rebuild contract `CH04_REBUILD_SURFACE_2026-05-16.md`)

**Internal claim:** measurability of the `Mu` operator family restricted
to `AEEQuantitativeEllipticSlice`s, plus the progressive composition
variants (raw `Mu` → composed `Mu` → a.e. `Mu`) needed by the
`Theorems/Mu.lean` and `Theorems/CanonicalSolutions.lean` consumers.
Combines `AEESliceAssembly/BlockEnergyAverage.lean` with the
`FixedCompetitorEnergyMeasurability` chain on the AEE side of the slice
predicate.

**Consumed by:**
- `Theorems/Mu.lean :: aemeasurable_Mu_cubeSet` and
  `aemeasurable_Mu_cubeSet_of_measurable_aeeQuantitativeSlice`
- `Theorems/CanonicalSolutions.lean ::
  aestronglyMeasurable_canonicalMuHilbertMinimizer_cubeSet` and the rest
  of the canonical-solution measurability surface.

If the single-claim summary above grows into three or more distinct
claims, split or refactor per the rebuild contract.
-/

theorem measurable_Mu_aeeQuantitativeSlice
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hToL2 :
      @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
        (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
        (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
        AEEQuantitativeEllipticSlice.toHilbertMatrixL2)
    (R : MuCorrectionSpaceRecoveryData U)
    [TopologicalSpace.SeparableSpace ↥R.correctionSpace]
    (system :
      ∀ a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a},
        MuOperatorSystemData U a.1)
    (mu_eq_muCandidate :
      ∀ a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}, ∀ P : BlockVec d,
        Mu U P a.1 =
          ((system a).toMuOperatorRealization.toMuHilbertRealization
              R.toMuCorrectionSpaceData).muCandidate P)
    (P : BlockVec d) :
    @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
      ℝ (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) (borel ℝ)
      (fun a => Mu U P a.1) := by
  let : MeasurableSpace {a : CoeffField d // AEEQuantitativeEllipticSlice U k a} :=
    AEEQuantitativeEllipticSlice.localMeasurableSpace U k
  refine measurable_Mu_comp_of_measurable_blockEnergyAverage_affineField_denseSeq
    (A := fun a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a} => a.1)
    R system mu_eq_muCandidate P ?_
  intro n
  exact measurable_blockEnergyAverage_aeeQuantitativeSlice hToL2
    (R.affineField P (TopologicalSpace.denseSeq ↥R.correctionSpace n))
    (R.affineField_memBlockL2 P (TopologicalSpace.denseSeq ↥R.correctionSpace n))

/-- Canonical AEE cube-slice measurability of `Mu`, with the Ch4 canonical
operator/generator plumbing supplied internally. -/
theorem measurable_Mu_aeeQuantitativeSlice_canonical_cubeSet
    {d : ℕ} (Q : TriadicCube d) {k : ℕ} (P : BlockVec d) :
    @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a}
      ℝ (AEEQuantitativeEllipticSlice.localMeasurableSpace (cubeSet Q) k) (borel ℝ)
      (fun a => Mu (cubeSet Q) P a.1) := by
  let : MeasurableSpace {a : CoeffField d //
      AEEQuantitativeEllipticSlice (cubeSet Q) k a} :=
    AEEQuantitativeEllipticSlice.localMeasurableSpace (cubeSet Q) k
  have hRewrite :
      (fun a : {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a} =>
        Mu (cubeSet Q) P a.1) =
      fun a =>
        ⨅ n : ℕ,
          blockEnergyAverage (cubeSet Q) a.1
            (canonicalMuGeneratorAffineField (U := cubeSet Q) P
              (TopologicalSpace.denseSeq
                (canonicalMuBlockCorrectionGeneratorSubmodule (cubeSet Q)) n)) := by
    funext a
    exact mu_eq_iInf_blockEnergyAverage_canonicalAEEMuGenerator Q k a P
  rw [hRewrite]
  exact Measurable.iInf fun n =>
    measurable_blockEnergyAverage_aeeQuantitativeSlice
      (measurable_toHilbertMatrixL2_aeeQuantitativeEllipticSlice_cubeSet Q k)
      (canonicalMuGeneratorAffineField (U := cubeSet Q) P
        (TopologicalSpace.denseSeq
          (canonicalMuBlockCorrectionGeneratorSubmodule (cubeSet Q)) n))
      (canonicalMuGeneratorAffineField_memBlockL2 (U := cubeSet Q) P
        (TopologicalSpace.denseSeq
          (canonicalMuBlockCorrectionGeneratorSubmodule (cubeSet Q)) n))

/-- Canonical AEE cube-slice strong measurability of the selected doubled-`Mu`
Hilbert maximizer/minimizer.  The proof selects the first dense generator whose
block energy is within `1 / (m + 1)` of `Mu`, and then passes to the Hilbert
energy-gap limit. -/
theorem stronglyMeasurable_canonicalAEEMuHilbertMinimizer_aeeQuantitativeSlice_cubeSet
    {d : ℕ} (Q : TriadicCube d) {k : ℕ} (P : BlockVec d) :
    letI : MeasurableSpace
      {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a} :=
        AEEQuantitativeEllipticSlice.localMeasurableSpace (cubeSet Q) k
    MeasureTheory.StronglyMeasurable
      (fun a =>
        ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).minimizerMap P) := by
  classical
  let U : Set (Vec d) := cubeSet Q
  let Ωs := {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
  let : MeasurableSpace Ωs := AEEQuantitativeEllipticSlice.localMeasurableSpace U k
  let K : ClosedSubmodule ℝ (HilbertBlockL2 U) :=
    (canonicalAEEMuCorrectionSpaceData Q).correctionSpace
  let ξ : ℕ → canonicalMuBlockCorrectionGeneratorSubmodule U :=
    TopologicalSpace.denseSeq (canonicalMuBlockCorrectionGeneratorSubmodule U)
  let candidate : ℕ → HilbertBlockL2 U := fun n =>
    blockVecToHilbertBlockL2Const (U := U) P +
      (canonicalMuCorrectionGeneratorEmbedding U (ξ n) : HilbertBlockL2 U)
  let energy : Ωs → ℕ → ℝ := fun a n =>
    blockEnergyAverage U a.1 (canonicalMuGeneratorAffineField (U := U) P (ξ n))
  let ε : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
  have hEnergy_meas : ∀ n : ℕ, Measurable fun a : Ωs => energy a n := by
    intro n
    simpa [energy, Ωs, U, ξ] using
      measurable_blockEnergyAverage_aeeQuantitativeSlice
        (measurable_toHilbertMatrixL2_aeeQuantitativeEllipticSlice_cubeSet Q k)
        (canonicalMuGeneratorAffineField (U := cubeSet Q) P
          (TopologicalSpace.denseSeq
            (canonicalMuBlockCorrectionGeneratorSubmodule (cubeSet Q)) n))
        (canonicalMuGeneratorAffineField_memBlockL2 (U := cubeSet Q) P
          (TopologicalSpace.denseSeq
            (canonicalMuBlockCorrectionGeneratorSubmodule (cubeSet Q)) n))
  have hMu_meas : Measurable fun a : Ωs => Mu U P a.1 := by
    simpa [Ωs, U] using measurable_Mu_aeeQuantitativeSlice_canonical_cubeSet Q (k := k) P
  have hExists : ∀ m : ℕ, ∀ a : Ωs, ∃ n : ℕ, energy a n ≤ Mu U P a.1 + ε m := by
    intro m a
    have hmu :
        Mu U P a.1 = ⨅ n : ℕ, energy a n := by
      simpa [energy, Ωs, U, ξ] using
        mu_eq_iInf_blockEnergyAverage_canonicalAEEMuGenerator Q k a P
    have hlt :
        (⨅ n : ℕ, energy a n) < (⨅ n : ℕ, energy a n) + ε m := by
      have hpos : 0 < ε m := by
        simp [ε]
        positivity
      exact lt_add_of_le_of_pos (le_refl (⨅ n : ℕ, energy a n)) hpos
    rcases exists_lt_of_ciInf_lt hlt with ⟨n, hn⟩
    exact ⟨n, le_of_lt (by simpa [hmu] using hn)⟩
  let index : ℕ → Ωs → ℕ := fun m a => Nat.find (hExists m a)
  have hGood_meas :
      ∀ m n : ℕ, MeasurableSet {a : Ωs | energy a n ≤ Mu U P a.1 + ε m} := by
    intro m n
    exact measurableSet_le (hEnergy_meas n) (hMu_meas.add measurable_const)
  have hIndex_meas : ∀ m : ℕ, Measurable (index m) := by
    intro m
    simpa [index] using measurable_find (hExists m) (hGood_meas m)
  have hCandidate_strong : MeasureTheory.StronglyMeasurable candidate :=
    MeasureTheory.StronglyMeasurable.of_discrete
  have hApprox_strong :
      ∀ m : ℕ, MeasureTheory.StronglyMeasurable fun a : Ωs => candidate (index m a) := by
    intro m
    simpa [Function.comp_def] using hCandidate_strong.comp_measurable (hIndex_meas m)
  have hε_tendsto : Tendsto ε atTop (𝓝 0) := by
    have hbase :
        Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [ε] using hbase
  have hlim :
      Tendsto
        (fun m : ℕ => fun a : Ωs => candidate (index m a))
        atTop
        (𝓝 fun a : Ωs =>
          let H := ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization)
          affineMinimizerMap K H.energyBilin H.energyCoercive (H.constantField P)) := by
    rw [tendsto_pi_nhds]
    intro a
    let H := ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization)
    have hmem :
        ∀ m : ℕ, candidate (index m a) - H.constantField P ∈ K := by
      intro m
      change
        candidate (index m a) - H.constantField P ∈
          (canonicalAEEMuCorrectionSpaceData Q).correctionSpace
      have hconst : H.constantField P = blockVecToHilbertBlockL2Const (U := U) P := rfl
      have hcand : candidate (index m a) =
          blockVecToHilbertBlockL2Const (U := U) P +
            (canonicalMuCorrectionGeneratorEmbedding U (ξ (index m a)) : HilbertBlockL2 U) := rfl
      rw [hcand, hconst, add_sub_cancel_left]
      exact (canonicalMuCorrectionGeneratorEmbedding U (ξ (index m a))).2
    have hnear :
        ∀ m : ℕ,
          quadraticEnergy H.energyBilin (candidate (index m a)) ≤
            quadraticEnergy H.energyBilin
              (affineMinimizerMap K H.energyBilin H.energyCoercive (H.constantField P)) +
              ε m := by
      intro m
      have hgood : energy a (index m a) ≤ Mu U P a.1 + ε m := by
        simpa [index] using Nat.find_spec (hExists m a)
      have hqe :
          quadraticEnergy H.energyBilin (candidate (index m a)) =
            energy a (index m a) := by
        simpa [H, candidate, energy, U, ξ] using!
          canonicalAEEMuOperatorSystemData_quadraticEnergy_generatorAffine_eq_blockEnergyAverage
            Q k a P (ξ (index m a))
      have hmu :
          Mu U P a.1 =
            quadraticEnergy H.energyBilin
              (affineMinimizerMap K H.energyBilin H.energyCoercive (H.constantField P)) := by
        simpa [H, K, U, MuHilbertRealization.muCandidate, MuHilbertProblem.muCandidate,
          MuHilbertRealization.minimizerMap, MuHilbertProblem.minimizerMap,
          parameterAffineMinimizerMap] using!
          mu_eq_canonicalAEEMuCandidate Q k a P
      calc
        quadraticEnergy H.energyBilin (candidate (index m a))
            = energy a (index m a) := hqe
        _ ≤ Mu U P a.1 + ε m := hgood
        _ = quadraticEnergy H.energyBilin
              (affineMinimizerMap K H.energyBilin H.energyCoercive (H.constantField P)) +
              ε m := by rw [hmu]
    exact tendsto_of_quadraticEnergy_le_min_add_eps
      K H.energyCoercive H.energySymm (H.constantField P) hmem hε_tendsto hnear
  have hAffine :
      MeasureTheory.StronglyMeasurable
        (fun a : Ωs =>
          let H := ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization)
          affineMinimizerMap K H.energyBilin H.energyCoercive (H.constantField P)) :=
    stronglyMeasurable_of_tendsto atTop hApprox_strong hlim
  simpa [Ωs, U, K, MuHilbertRealization.minimizerMap, MuHilbertProblem.minimizerMap,
    parameterAffineMinimizerMap] using! hAffine

/-- Canonical AEE cube-slice measurability of a fixed block-`L²` test paired
through the Hilbert energy form with the selected canonical doubled-`Mu`
minimizer. This is the source primitive for scalar-response operator-image
averages: the proof uses the same dense-generator selection as the minimizer
measurability theorem, then passes the fixed continuous bilinear functional to
the limit. -/
theorem measurable_energyBilin_fixed_canonicalAEEMuHilbertMinimizer_aeeQuantitativeSlice_cubeSet
    {d : ℕ} (Q : TriadicCube d) {k : ℕ} (P : BlockVec d)
    (Y : BlockState d) (hY : MemBlockL2 (cubeSet Q) Y.eval) :
    letI : MeasurableSpace
      {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a} :=
        AEEQuantitativeEllipticSlice.localMeasurableSpace (cubeSet Q) k
    Measurable
      (fun a =>
        ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).energyBilin
          (toHilbertBlockL2OfBlockField (U := cubeSet Q) hY)
          (((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).minimizerMap P)) := by
  classical
  let U : Set (Vec d) := cubeSet Q
  let Ωs := {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
  let : MeasurableSpace Ωs := AEEQuantitativeEllipticSlice.localMeasurableSpace U k
  let K : ClosedSubmodule ℝ (HilbertBlockL2 U) :=
    (canonicalAEEMuCorrectionSpaceData Q).correctionSpace
  let ξ : ℕ → canonicalMuBlockCorrectionGeneratorSubmodule U :=
    TopologicalSpace.denseSeq (canonicalMuBlockCorrectionGeneratorSubmodule U)
  let y : HilbertBlockL2 U :=
    toHilbertBlockL2OfBlockField (U := U) (by simpa [U] using hY)
  let candidate : ℕ → HilbertBlockL2 U := fun n =>
    blockVecToHilbertBlockL2Const (U := U) P +
      (canonicalMuCorrectionGeneratorEmbedding U (ξ n) : HilbertBlockL2 U)
  let energy : Ωs → ℕ → ℝ := fun a n =>
    blockEnergyAverage U a.1 (canonicalMuGeneratorAffineField (U := U) P (ξ n))
  let ε : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
  have hEnergy_meas : ∀ n : ℕ, Measurable fun a : Ωs => energy a n := by
    intro n
    simpa [energy, Ωs, U, ξ] using
      measurable_blockEnergyAverage_aeeQuantitativeSlice
        (measurable_toHilbertMatrixL2_aeeQuantitativeEllipticSlice_cubeSet Q k)
        (canonicalMuGeneratorAffineField (U := cubeSet Q) P
          (TopologicalSpace.denseSeq
            (canonicalMuBlockCorrectionGeneratorSubmodule (cubeSet Q)) n))
        (canonicalMuGeneratorAffineField_memBlockL2 (U := cubeSet Q) P
          (TopologicalSpace.denseSeq
            (canonicalMuBlockCorrectionGeneratorSubmodule (cubeSet Q)) n))
  have hMu_meas : Measurable fun a : Ωs => Mu U P a.1 := by
    simpa [Ωs, U] using measurable_Mu_aeeQuantitativeSlice_canonical_cubeSet Q (k := k) P
  have hExists : ∀ m : ℕ, ∀ a : Ωs, ∃ n : ℕ, energy a n ≤ Mu U P a.1 + ε m := by
    intro m a
    have hmu :
        Mu U P a.1 = ⨅ n : ℕ, energy a n := by
      simpa [energy, Ωs, U, ξ] using
        mu_eq_iInf_blockEnergyAverage_canonicalAEEMuGenerator Q k a P
    have hlt :
        (⨅ n : ℕ, energy a n) < (⨅ n : ℕ, energy a n) + ε m := by
      have hpos : 0 < ε m := by
        simp [ε]
        positivity
      exact lt_add_of_le_of_pos (le_refl (⨅ n : ℕ, energy a n)) hpos
    rcases exists_lt_of_ciInf_lt hlt with ⟨n, hn⟩
    exact ⟨n, le_of_lt (by simpa [hmu] using hn)⟩
  let index : ℕ → Ωs → ℕ := fun m a => Nat.find (hExists m a)
  have hGood_meas :
      ∀ m n : ℕ, MeasurableSet {a : Ωs | energy a n ≤ Mu U P a.1 + ε m} := by
    intro m n
    exact measurableSet_le (hEnergy_meas n) (hMu_meas.add measurable_const)
  have hApprox_meas :
      ∀ n : ℕ,
        Measurable fun a : Ωs =>
          ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).energyBilin
            y (candidate n) := by
    intro n
    simpa [Ωs, U, y, candidate, ξ] using
      measurable_energyBilin_fixed_canonicalMuGeneratorAffineField_aeeQuantitativeSlice_cubeSet
        Q k P Y hY
        (TopologicalSpace.denseSeq
          (canonicalMuBlockCorrectionGeneratorSubmodule (cubeSet Q)) n)
  have hSelected_meas :
      ∀ m : ℕ,
        Measurable fun a : Ωs =>
          ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).energyBilin
            y (candidate (index m a)) := by
    intro m
    let p : ℕ → Ωs → Prop :=
      fun n a => energy a n ≤ Mu U P a.1 + ε m
    have hp : ∀ n : ℕ, MeasurableSet {a : Ωs | p n a} := by
      intro n
      simpa [p] using hGood_meas m n
    have hexists : ∀ a : Ωs, ∃ n : ℕ, p n a := by
      intro a
      simpa [p] using hExists m a
    simpa [p, index] using
      (Measurable.find
        (f := fun n a =>
          ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).energyBilin
            y (candidate n))
        (p := p) hApprox_meas hp hexists)
  have hSelected_strong :
      ∀ m : ℕ,
        MeasureTheory.StronglyMeasurable fun a : Ωs =>
          ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).energyBilin
            y (candidate (index m a)) :=
    fun m => (hSelected_meas m).stronglyMeasurable
  have hε_tendsto : Tendsto ε atTop (𝓝 0) := by
    have hbase :
        Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [ε] using hbase
  have hlim_scalar :
      Tendsto
        (fun m : ℕ => fun a : Ωs =>
          ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).energyBilin
            y (candidate (index m a)))
        atTop
        (𝓝 fun a : Ωs =>
          let H := ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization)
          H.energyBilin y (H.minimizerMap P)) := by
    rw [tendsto_pi_nhds]
    intro a
    let H := ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization)
    have hmem :
        ∀ m : ℕ, candidate (index m a) - H.constantField P ∈ K := by
      intro m
      change
        candidate (index m a) - H.constantField P ∈
          (canonicalAEEMuCorrectionSpaceData Q).correctionSpace
      have hconst : H.constantField P = blockVecToHilbertBlockL2Const (U := U) P := rfl
      have hcand : candidate (index m a) =
          blockVecToHilbertBlockL2Const (U := U) P +
            (canonicalMuCorrectionGeneratorEmbedding U (ξ (index m a)) : HilbertBlockL2 U) := rfl
      rw [hcand, hconst, add_sub_cancel_left]
      exact (canonicalMuCorrectionGeneratorEmbedding U (ξ (index m a))).2
    have hnear :
        ∀ m : ℕ,
          quadraticEnergy H.energyBilin (candidate (index m a)) ≤
            quadraticEnergy H.energyBilin
              (affineMinimizerMap K H.energyBilin H.energyCoercive (H.constantField P)) +
              ε m := by
      intro m
      have hgood : energy a (index m a) ≤ Mu U P a.1 + ε m := by
        simpa [index] using Nat.find_spec (hExists m a)
      have hqe :
          quadraticEnergy H.energyBilin (candidate (index m a)) =
            energy a (index m a) := by
        simpa [H, candidate, energy, U, ξ] using!
          canonicalAEEMuOperatorSystemData_quadraticEnergy_generatorAffine_eq_blockEnergyAverage
            Q k a P (ξ (index m a))
      have hmu :
          Mu U P a.1 =
            quadraticEnergy H.energyBilin
              (affineMinimizerMap K H.energyBilin H.energyCoercive (H.constantField P)) := by
        simpa [H, K, U, MuHilbertRealization.muCandidate, MuHilbertProblem.muCandidate,
          MuHilbertRealization.minimizerMap, MuHilbertProblem.minimizerMap,
          parameterAffineMinimizerMap] using!
          mu_eq_canonicalAEEMuCandidate Q k a P
      calc
        quadraticEnergy H.energyBilin (candidate (index m a))
            = energy a (index m a) := hqe
        _ ≤ Mu U P a.1 + ε m := hgood
        _ = quadraticEnergy H.energyBilin
              (affineMinimizerMap K H.energyBilin H.energyCoercive (H.constantField P)) +
              ε m := by rw [hmu]
    have hHilbert :
        Tendsto (fun m : ℕ => candidate (index m a)) atTop
          (𝓝 (affineMinimizerMap K H.energyBilin H.energyCoercive (H.constantField P))) :=
      tendsto_of_quadraticEnergy_le_min_add_eps
        K H.energyCoercive H.energySymm (H.constantField P) hmem hε_tendsto hnear
    have hHilbert' :
        Tendsto (fun m : ℕ => candidate (index m a)) atTop
          (𝓝 (H.minimizerMap P)) := by
      simpa [H, K, MuHilbertRealization.minimizerMap, MuHilbertProblem.minimizerMap,
        parameterAffineMinimizerMap] using! hHilbert
    exact (H.energyBilin y).continuous.tendsto
      (H.minimizerMap P) |>.comp hHilbert'
  have hStrong :
      MeasureTheory.StronglyMeasurable
        (fun a : Ωs =>
          let H := ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization)
          H.energyBilin y (H.minimizerMap P)) :=
    stronglyMeasurable_of_tendsto atTop hSelected_strong hlim_scalar
  have hMeas :
      Measurable
        (fun a : Ωs =>
          let H := ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization)
          H.energyBilin y (H.minimizerMap P)) :=
    hStrong.measurable
  simpa [Ωs, U, y] using hMeas

/-- Canonical composed AEE cube-slice measurability of `Mu`. -/
theorem measurable_Mu_comp_aeeQuantitativeSlice_canonical_cubeSet
    {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (Q : TriadicCube d) {k : ℕ}
    (A : Ω → CoeffField d) (hA : IsPointwiseLocalSigmaMeasurableOn A (cubeSet Q))
    (hSlice : ∀ ω : Ω, AEEQuantitativeEllipticSlice (cubeSet Q) k (A ω))
    (P : BlockVec d) :
    Measurable fun ω => Mu (cubeSet Q) P (A ω) := by
  let As : Ω → {a : CoeffField d //
      AEEQuantitativeEllipticSlice (cubeSet Q) k a} :=
    fun ω => ⟨A ω, hSlice ω⟩
  have hAs :
      @Measurable Ω {a : CoeffField d //
          AEEQuantitativeEllipticSlice (cubeSet Q) k a}
        _ (AEEQuantitativeEllipticSlice.localMeasurableSpace (cubeSet Q) k) As :=
    measurable_subtype_mk_aeeQuantitativeSlice_of_isLocalSigmaMeasurableOn A hA hSlice
  have hMu :
      @Measurable {a : CoeffField d //
          AEEQuantitativeEllipticSlice (cubeSet Q) k a}
        ℝ (AEEQuantitativeEllipticSlice.localMeasurableSpace (cubeSet Q) k) (borel ℝ)
        (fun a => Mu (cubeSet Q) P a.1) :=
    measurable_Mu_aeeQuantitativeSlice_canonical_cubeSet Q P
  change Measurable ((fun a : {a : CoeffField d //
      AEEQuantitativeEllipticSlice (cubeSet Q) k a} =>
    Mu (cubeSet Q) P a.1) ∘ As)
  exact hMu.comp hAs

/-- Canonical countable-cover AEE cube-slice measurability of `Mu`. -/
theorem measurable_Mu_comp_countable_aeeQuantitativeSlice_canonical_cubeSet_cover
    {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (Q : TriadicCube d)
    (A : Ω → CoeffField d) (hA : IsPointwiseLocalSigmaMeasurableOn A (cubeSet Q))
    (t : ℕ → Set Ω) (ht : ∀ k : ℕ, MeasurableSet (t k))
    (hcover : ⋃ k : ℕ, t k = Set.univ)
    (hSlice : ∀ k : ℕ, ∀ ω : Ω, ω ∈ t k →
      AEEQuantitativeEllipticSlice (cubeSet Q) k (A ω))
    (P : BlockVec d) :
    Measurable fun ω => Mu (cubeSet Q) P (A ω) := by
  classical
  let f : (k : ℕ) → t k → ℝ :=
    fun k ω => Mu (cubeSet Q) P (A ω.1)
  have hfm : ∀ k : ℕ, Measurable (f k) := by
    intro k
    have hA_sub : IsPointwiseLocalSigmaMeasurableOn
        (fun ω : t k => A ω.1) (cubeSet Q) := by
      simpa [IsPointwiseLocalSigmaMeasurableOn, Function.comp] using! hA.comp measurable_subtype_coe
    have hSlice_sub :
        ∀ ω : t k,
          AEEQuantitativeEllipticSlice (cubeSet Q) k
            ((fun ω : t k => A ω.1) ω) := by
      intro ω
      exact hSlice k ω.1 ω.2
    exact measurable_Mu_comp_aeeQuantitativeSlice_canonical_cubeSet
      Q (fun ω : t k => A ω.1) hA_sub hSlice_sub P
  have hagree :
      ∀ (i j : ℕ) (ω : Ω) (hωi : ω ∈ t i) (hωj : ω ∈ t j),
        f i ⟨ω, hωi⟩ = f j ⟨ω, hωj⟩ := by
    intro i j ω hωi hωj
    rfl
  have hLift : Measurable (Set.liftCover t f hagree hcover) :=
    measurable_liftCover t ht f hfm hagree hcover
  have hEq : Set.liftCover t f hagree hcover =
      (fun ω => Mu (cubeSet Q) P (A ω)) := by
    funext ω
    obtain ⟨k, hωk⟩ : ∃ k : ℕ, ω ∈ t k := by
      have hω_cover : ω ∈ ⋃ k : ℕ, t k := by
        rw [hcover]
        exact Set.mem_univ ω
      exact Set.mem_iUnion.mp hω_cover
    rw [Set.liftCover_of_mem (S := t) (f := f) (hf := hagree) (hS := hcover) hωk]
  simpa [hEq] using hLift

/-- Canonical a.e. countable-cover AEE cube-slice measurability of `Mu`. -/
theorem aemeasurable_Mu_comp_countable_aeeQuantitativeSlice_canonical_cubeSet_cover
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    {d : ℕ} (Q : TriadicCube d)
    (A : Ω → CoeffField d) (hA : IsPointwiseLocalSigmaMeasurableOn A (cubeSet Q))
    (t : ℕ → Set Ω) (ht : ∀ k : ℕ, MeasurableSet (t k))
    (hcover_ae : ∀ᵐ ω ∂μ, ω ∈ ⋃ k : ℕ, t k)
    (hSlice : ∀ k : ℕ, ∀ ω : Ω, ω ∈ t k →
      AEEQuantitativeEllipticSlice (cubeSet Q) k (A ω))
    (P : BlockVec d) :
    AEMeasurable (fun ω => Mu (cubeSet Q) P (A ω)) μ := by
  classical
  let S : Set Ω := ⋃ k : ℕ, t k
  let cover : Option ℕ → Set Ω
    | none => Sᶜ
    | some k => t k
  let f : (i : Option ℕ) → cover i → ℝ
    | none, _ => 0
    | some k, ω => Mu (cubeSet Q) P (A ω.1)
  have hcover_meas : ∀ i : Option ℕ, MeasurableSet (cover i) := by
    intro i
    cases i with
    | none => exact (MeasurableSet.iUnion ht).compl
    | some k => exact ht k
  have hfm : ∀ i : Option ℕ, Measurable (f i) := by
    intro i
    cases i with
    | none => exact measurable_const
    | some k =>
        have hA_sub : IsPointwiseLocalSigmaMeasurableOn
            (fun ω : cover (some k) => A ω.1) (cubeSet Q) := by
          simpa [IsPointwiseLocalSigmaMeasurableOn, Function.comp, cover] using!
            hA.comp measurable_subtype_coe
        have hSlice_sub :
            ∀ ω : cover (some k),
              AEEQuantitativeEllipticSlice (cubeSet Q) k
                ((fun ω : cover (some k) => A ω.1) ω) := by
          intro ω
          have hω : ω.1 ∈ t k := by
            simp [cover] at ω
            exact ω.2
          exact hSlice k ω.1 hω
        simpa [f, cover] using
          measurable_Mu_comp_aeeQuantitativeSlice_canonical_cubeSet
            Q (fun ω : cover (some k) => A ω.1) hA_sub hSlice_sub P
  have hagree :
      ∀ (i j : Option ℕ) (ω : Ω) (hωi : ω ∈ cover i) (hωj : ω ∈ cover j),
        f i ⟨ω, hωi⟩ = f j ⟨ω, hωj⟩ := by
    intro i j ω hωi hωj
    cases i with
    | none =>
        cases j with
        | none => rfl
        | some k =>
            exfalso
            have hωS : ω ∈ S := Set.mem_iUnion.mpr ⟨k, by simpa [cover] using hωj⟩
            have hω_notS : ω ∉ S := by simpa [cover] using hωi
            exact hω_notS hωS
    | some k =>
        cases j with
        | none =>
            exfalso
            have hωS : ω ∈ S := Set.mem_iUnion.mpr ⟨k, by simpa [cover] using hωi⟩
            have hω_notS : ω ∉ S := by simpa [cover] using hωj
            exact hω_notS hωS
        | some _ => rfl
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
      (fun ω => Mu (cubeSet Q) P (A ω)) =ᵐ[μ] Set.liftCover cover f hagree hcover := by
    filter_upwards [hcover_ae] with ω hωS
    obtain ⟨k, hωk⟩ := Set.mem_iUnion.mp hωS
    rw [Set.liftCover_of_mem
      (S := cover) (f := f) (hf := hagree) (hS := hcover) (i := some k)
      (by simpa [cover] using hωk)]
  exact hLift.aemeasurable.congr hEq.symm

/-- Canonical set-cover AEE cube-slice measurability of `Mu`. -/
theorem measurable_Mu_comp_aeeQuantitativeSlice_canonical_cubeSet_sets
    {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (Q : TriadicCube d)
    (A : Ω → CoeffField d) (hA : IsPointwiseLocalSigmaMeasurableOn A (cubeSet Q))
    (hSliceMeas :
      ∀ k : ℕ,
        MeasurableSet {ω : Ω | AEEQuantitativeEllipticSlice (cubeSet Q) k (A ω)})
    (hcover :
      ∀ ω : Ω, ∃ k : ℕ, AEEQuantitativeEllipticSlice (cubeSet Q) k (A ω))
    (P : BlockVec d) :
    Measurable fun ω => Mu (cubeSet Q) P (A ω) := by
  classical
  let t : ℕ → Set Ω :=
    fun k => {ω : Ω | AEEQuantitativeEllipticSlice (cubeSet Q) k (A ω)}
  have ht : ∀ k : ℕ, MeasurableSet (t k) := hSliceMeas
  have hcover_set : ⋃ k : ℕ, t k = Set.univ := by
    ext ω
    constructor
    · intro _hω
      exact Set.mem_univ ω
    · intro _hω
      exact Set.mem_iUnion.mpr (hcover ω)
  exact measurable_Mu_comp_countable_aeeQuantitativeSlice_canonical_cubeSet_cover
    Q A hA t ht hcover_set (fun k ω hω => hω) P

/-- Canonical a.e. set-cover AEE cube-slice measurability of `Mu`. -/
theorem aemeasurable_Mu_comp_aeeQuantitativeSlice_canonical_cubeSet_sets
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    {d : ℕ} (Q : TriadicCube d)
    (A : Ω → CoeffField d) (hA : IsPointwiseLocalSigmaMeasurableOn A (cubeSet Q))
    (hSliceMeas :
      ∀ k : ℕ,
        MeasurableSet {ω : Ω | AEEQuantitativeEllipticSlice (cubeSet Q) k (A ω)})
    (hcover_ae :
      ∀ᵐ ω ∂μ, ∃ k : ℕ, AEEQuantitativeEllipticSlice (cubeSet Q) k (A ω))
    (P : BlockVec d) :
    AEMeasurable (fun ω => Mu (cubeSet Q) P (A ω)) μ := by
  classical
  let t : ℕ → Set Ω :=
    fun k => {ω : Ω | AEEQuantitativeEllipticSlice (cubeSet Q) k (A ω)}
  have ht : ∀ k : ℕ, MeasurableSet (t k) := hSliceMeas
  have hcover_set_ae : ∀ᵐ ω ∂μ, ω ∈ ⋃ k : ℕ, t k := by
    filter_upwards [hcover_ae] with ω hω
    exact Set.mem_iUnion.mpr hω
  exact aemeasurable_Mu_comp_countable_aeeQuantitativeSlice_canonical_cubeSet_cover
    μ Q A hA t ht hcover_set_ae (fun k ω hω => hω) P

/-- Canonical cube-set `HasMeasurableMuFamily` from an AEE quantitative-slice
cover. -/
theorem hasMeasurableMuFamily_of_measurable_aeeQuantitativeSlice_sets_canonical_cubeSet
    {d : ℕ} (Q : TriadicCube d)
    (hLocal : IsPointwiseLocalSigmaMeasurableOn (fun a : CoeffField d => a) (cubeSet Q))
    (hSliceMeas :
      ∀ k : ℕ,
        MeasurableSet {a : CoeffField d |
          AEEQuantitativeEllipticSlice (cubeSet Q) k a})
    (hcover :
      ∀ a : CoeffField d, ∃ k : ℕ, AEEQuantitativeEllipticSlice (cubeSet Q) k a) :
    HasMeasurableMuFamily (cubeSet Q) := by
  intro P
  simpa using
    (measurable_Mu_comp_aeeQuantitativeSlice_canonical_cubeSet_sets
      (Q := Q) (A := fun a : CoeffField d => a) hLocal hSliceMeas hcover P)

/-- Canonical law-facing a.e. AEE cube-slice `Mu` family bridge. -/
theorem aemeasurable_Mu_family_of_aeeQuantitativeSlice_sets_canonical_cubeSet
    {d : ℕ} (Q : TriadicCube d)
    (μ : MeasureTheory.Measure (CoeffField d))
    (hLocal : IsPointwiseLocalSigmaMeasurableOn (fun a : CoeffField d => a) (cubeSet Q))
    (hSliceMeas :
      ∀ k : ℕ,
        MeasurableSet {a : CoeffField d |
          AEEQuantitativeEllipticSlice (cubeSet Q) k a})
    (hcover_ae :
      ∀ᵐ a ∂μ, ∃ k : ℕ, AEEQuantitativeEllipticSlice (cubeSet Q) k a) :
    ∀ P : BlockVec d, AEMeasurable (fun a : CoeffField d => Mu (cubeSet Q) P a) μ := by
  intro P
  simpa using
    (aemeasurable_Mu_comp_aeeQuantitativeSlice_canonical_cubeSet_sets
      μ (Q := Q) (A := fun a : CoeffField d => a) hLocal hSliceMeas hcover_ae P)

theorem measurable_Mu_comp_aeeQuantitativeSlice
    {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {U : Set (Vec d)} {k : ℕ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hToL2 :
      @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
        (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
        (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
        AEEQuantitativeEllipticSlice.toHilbertMatrixL2)
    (A : Ω → CoeffField d) (hA : IsPointwiseLocalSigmaMeasurableOn A U)
    (hSlice : ∀ ω : Ω, AEEQuantitativeEllipticSlice U k (A ω))
    (R : MuCorrectionSpaceRecoveryData U)
    [TopologicalSpace.SeparableSpace ↥R.correctionSpace]
    (system :
      ∀ a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a},
        MuOperatorSystemData U a.1)
    (mu_eq_muCandidate :
      ∀ a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}, ∀ P : BlockVec d,
        Mu U P a.1 =
          ((system a).toMuOperatorRealization.toMuHilbertRealization
              R.toMuCorrectionSpaceData).muCandidate P)
    (P : BlockVec d) :
    Measurable fun ω => Mu U P (A ω) := by
  let As : Ω → {a : CoeffField d // AEEQuantitativeEllipticSlice U k a} :=
    fun ω => ⟨A ω, hSlice ω⟩
  have hAs :
      @Measurable Ω {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
        _ (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) As :=
    measurable_subtype_mk_aeeQuantitativeSlice_of_isLocalSigmaMeasurableOn A hA hSlice
  have hMu :
      @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
        ℝ (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) (borel ℝ)
        (fun a => Mu U P a.1) :=
    measurable_Mu_aeeQuantitativeSlice hToL2 R system mu_eq_muCandidate P
  change Measurable ((fun a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a} =>
    Mu U P a.1) ∘ As)
  exact hMu.comp hAs

theorem measurable_Mu_comp_countable_aeeQuantitativeSlice_cover
    {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hToL2 :
      ∀ k : ℕ,
        @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
          (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
          (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
          AEEQuantitativeEllipticSlice.toHilbertMatrixL2)
    (A : Ω → CoeffField d) (hA : IsPointwiseLocalSigmaMeasurableOn A U)
    (t : ℕ → Set Ω) (ht : ∀ k : ℕ, MeasurableSet (t k))
    (hcover : ⋃ k : ℕ, t k = Set.univ)
    (hSlice : ∀ k : ℕ, ∀ ω : Ω, ω ∈ t k →
      AEEQuantitativeEllipticSlice U k (A ω))
    (R : MuCorrectionSpaceRecoveryData U)
    [TopologicalSpace.SeparableSpace ↥R.correctionSpace]
    (system :
      ∀ k : ℕ, ∀ a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a},
        MuOperatorSystemData U a.1)
    (mu_eq_muCandidate :
      ∀ k : ℕ, ∀ a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a},
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
        ∀ ω : t k,
          AEEQuantitativeEllipticSlice U k ((fun ω : t k => A ω.1) ω) := by
      intro ω
      exact hSlice k ω.1 ω.2
    exact measurable_Mu_comp_aeeQuantitativeSlice
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

theorem aemeasurable_Mu_comp_countable_aeeQuantitativeSlice_cover
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hToL2 :
      ∀ k : ℕ,
        @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
          (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
          (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
          AEEQuantitativeEllipticSlice.toHilbertMatrixL2)
    (A : Ω → CoeffField d) (hA : IsPointwiseLocalSigmaMeasurableOn A U)
    (t : ℕ → Set Ω) (ht : ∀ k : ℕ, MeasurableSet (t k))
    (hcover_ae : ∀ᵐ ω ∂μ, ω ∈ ⋃ k : ℕ, t k)
    (hSlice : ∀ k : ℕ, ∀ ω : Ω, ω ∈ t k →
      AEEQuantitativeEllipticSlice U k (A ω))
    (R : MuCorrectionSpaceRecoveryData U)
    [TopologicalSpace.SeparableSpace ↥R.correctionSpace]
    (system :
      ∀ k : ℕ, ∀ a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a},
        MuOperatorSystemData U a.1)
    (mu_eq_muCandidate :
      ∀ k : ℕ, ∀ a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a},
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
    | none => exact (MeasurableSet.iUnion ht).compl
    | some k => exact ht k
  have hfm : ∀ i : Option ℕ, Measurable (f i) := by
    intro i
    cases i with
    | none => exact measurable_const
    | some k =>
        have hA_sub : IsPointwiseLocalSigmaMeasurableOn (fun ω : cover (some k) => A ω.1) U := by
          simpa [IsPointwiseLocalSigmaMeasurableOn, Function.comp, cover] using!
            hA.comp measurable_subtype_coe
        have hSlice_sub :
            ∀ ω : cover (some k),
              AEEQuantitativeEllipticSlice U k ((fun ω : cover (some k) => A ω.1) ω) := by
          intro ω
          have hω : ω.1 ∈ t k := by
            simp [cover] at ω
            exact ω.2
          exact hSlice k ω.1 hω
        simpa [f, cover] using
          measurable_Mu_comp_aeeQuantitativeSlice
            (hToL2 k) (fun ω : cover (some k) => A ω.1) hA_sub hSlice_sub
            R (system k) (mu_eq_muCandidate k) P
  have hagree :
      ∀ (i j : Option ℕ) (ω : Ω) (hωi : ω ∈ cover i) (hωj : ω ∈ cover j),
        f i ⟨ω, hωi⟩ = f j ⟨ω, hωj⟩ := by
    intro i j ω hωi hωj
    cases i with
    | none =>
        cases j with
        | none => rfl
        | some k =>
            exfalso
            have hωS : ω ∈ S := Set.mem_iUnion.mpr ⟨k, by simpa [cover] using hωj⟩
            have hω_notS : ω ∉ S := by simpa [cover] using hωi
            exact hω_notS hωS
    | some k =>
        cases j with
        | none =>
            exfalso
            have hωS : ω ∈ S := Set.mem_iUnion.mpr ⟨k, by simpa [cover] using hωi⟩
            have hω_notS : ω ∉ S := by simpa [cover] using hωj
            exact hω_notS hωS
        | some _ => rfl
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

theorem measurable_Mu_comp_aeeQuantitativeSlice_sets
    {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hToL2 :
      ∀ k : ℕ,
        @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
          (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
          (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
          AEEQuantitativeEllipticSlice.toHilbertMatrixL2)
    (A : Ω → CoeffField d) (hA : IsPointwiseLocalSigmaMeasurableOn A U)
    (hSliceMeas :
      ∀ k : ℕ, MeasurableSet {ω : Ω | AEEQuantitativeEllipticSlice U k (A ω)})
    (hcover : ∀ ω : Ω, ∃ k : ℕ, AEEQuantitativeEllipticSlice U k (A ω))
    (R : MuCorrectionSpaceRecoveryData U)
    [TopologicalSpace.SeparableSpace ↥R.correctionSpace]
    (system :
      ∀ k : ℕ, ∀ a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a},
        MuOperatorSystemData U a.1)
    (mu_eq_muCandidate :
      ∀ k : ℕ, ∀ a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a},
        ∀ P : BlockVec d,
          Mu U P a.1 =
            (((system k a).toMuOperatorRealization.toMuHilbertRealization
                R.toMuCorrectionSpaceData).muCandidate P))
    (P : BlockVec d) :
    Measurable fun ω => Mu U P (A ω) := by
  classical
  let t : ℕ → Set Ω := fun k => {ω : Ω | AEEQuantitativeEllipticSlice U k (A ω)}
  have ht : ∀ k : ℕ, MeasurableSet (t k) := hSliceMeas
  have hcover_set : ⋃ k : ℕ, t k = Set.univ := by
    ext ω
    constructor
    · intro _hω
      exact Set.mem_univ ω
    · intro _hω
      exact Set.mem_iUnion.mpr (hcover ω)
  exact measurable_Mu_comp_countable_aeeQuantitativeSlice_cover
    hToL2 A hA t ht hcover_set (fun k ω hω => hω)
    R system mu_eq_muCandidate P

theorem aemeasurable_Mu_comp_aeeQuantitativeSlice_sets
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hToL2 :
      ∀ k : ℕ,
        @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
          (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
          (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
          AEEQuantitativeEllipticSlice.toHilbertMatrixL2)
    (A : Ω → CoeffField d) (hA : IsPointwiseLocalSigmaMeasurableOn A U)
    (hSliceMeas :
      ∀ k : ℕ, MeasurableSet {ω : Ω | AEEQuantitativeEllipticSlice U k (A ω)})
    (hcover_ae : ∀ᵐ ω ∂μ, ∃ k : ℕ, AEEQuantitativeEllipticSlice U k (A ω))
    (R : MuCorrectionSpaceRecoveryData U)
    [TopologicalSpace.SeparableSpace ↥R.correctionSpace]
    (system :
      ∀ k : ℕ, ∀ a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a},
        MuOperatorSystemData U a.1)
    (mu_eq_muCandidate :
      ∀ k : ℕ, ∀ a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a},
        ∀ P : BlockVec d,
          Mu U P a.1 =
            (((system k a).toMuOperatorRealization.toMuHilbertRealization
                R.toMuCorrectionSpaceData).muCandidate P))
    (P : BlockVec d) :
    AEMeasurable (fun ω => Mu U P (A ω)) μ := by
  classical
  let t : ℕ → Set Ω := fun k => {ω : Ω | AEEQuantitativeEllipticSlice U k (A ω)}
  have ht : ∀ k : ℕ, MeasurableSet (t k) := hSliceMeas
  have hcover_set_ae : ∀ᵐ ω ∂μ, ω ∈ ⋃ k : ℕ, t k := by
    filter_upwards [hcover_ae] with ω hω
    exact Set.mem_iUnion.mpr hω
  exact aemeasurable_Mu_comp_countable_aeeQuantitativeSlice_cover
    μ hToL2 A hA t ht hcover_set_ae (fun k ω hω => hω)
    R system mu_eq_muCandidate P

theorem aemeasurable_Mu_comp_aeeQuantitativeSlice_sets_of_isOpen_volume_ne_top
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hUopen : IsOpen U) (hUfinite : MeasureTheory.volume U ≠ ⊤)
    (A : Ω → CoeffField d) (hA : IsPointwiseLocalSigmaMeasurableOn A U)
    (hSliceMeas :
      ∀ k : ℕ, MeasurableSet {ω : Ω | AEEQuantitativeEllipticSlice U k (A ω)})
    (hcover_ae : ∀ᵐ ω ∂μ, ∃ k : ℕ, AEEQuantitativeEllipticSlice U k (A ω))
    (R : MuCorrectionSpaceRecoveryData U)
    [TopologicalSpace.SeparableSpace ↥R.correctionSpace]
    (system :
      ∀ k : ℕ, ∀ a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a},
        MuOperatorSystemData U a.1)
    (mu_eq_muCandidate :
      ∀ k : ℕ, ∀ a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a},
        ∀ P : BlockVec d,
          Mu U P a.1 =
            (((system k a).toMuOperatorRealization.toMuHilbertRealization
                R.toMuCorrectionSpaceData).muCandidate P))
    (P : BlockVec d) :
    AEMeasurable (fun ω => Mu U P (A ω)) μ := by
  exact aemeasurable_Mu_comp_aeeQuantitativeSlice_sets μ
    (fun _k => measurable_toHilbertMatrixL2_aee_of_isOpen_volume_ne_top hUopen hUfinite)
    A hA hSliceMeas hcover_ae R system mu_eq_muCandidate P

/-- Build the ambient `HasMeasurableMuFamily U` hypothesis from a measurable
AEE quantitative-slice cover.

The explicit `hLocal` hypothesis records that the sampled coefficient field is
measurable into the local coefficient-field sigma algebra on `U`.  For the
identity map on ambient coefficient fields this is now supplied by the public
coefficient-field measurable-space API. -/
theorem hasMeasurableMuFamily_of_measurable_aeeQuantitativeSlice_sets
    {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hToL2 :
      ∀ k : ℕ,
        @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
          (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
          (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
          AEEQuantitativeEllipticSlice.toHilbertMatrixL2)
    (hLocal : IsPointwiseLocalSigmaMeasurableOn (fun a : CoeffField d => a) U)
    (hSliceMeas :
      ∀ k : ℕ, MeasurableSet {a : CoeffField d | AEEQuantitativeEllipticSlice U k a})
    (hcover : ∀ a : CoeffField d, ∃ k : ℕ, AEEQuantitativeEllipticSlice U k a)
    (R : MuCorrectionSpaceRecoveryData U)
    [TopologicalSpace.SeparableSpace ↥R.correctionSpace]
    (system :
      ∀ k : ℕ, ∀ a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a},
        MuOperatorSystemData U a.1)
    (mu_eq_muCandidate :
      ∀ k : ℕ, ∀ a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a},
        ∀ P : BlockVec d,
          Mu U P a.1 =
            (((system k a).toMuOperatorRealization.toMuHilbertRealization
                R.toMuCorrectionSpaceData).muCandidate P)) :
    HasMeasurableMuFamily U := by
  intro P
  simpa using
    (measurable_Mu_comp_aeeQuantitativeSlice_sets
      (hToL2 := hToL2)
      (A := fun a : CoeffField d => a) hLocal hSliceMeas hcover
      R system mu_eq_muCandidate P)

/-- Open finite-volume version of
`hasMeasurableMuFamily_of_measurable_aeeQuantitativeSlice_sets`, with the
smooth-probe Hilbert `L²` measurability supplied internally. -/
theorem hasMeasurableMuFamily_of_measurable_aeeQuantitativeSlice_sets_of_isOpen_volume_ne_top
    {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hUopen : IsOpen U) (hUfinite : MeasureTheory.volume U ≠ ⊤)
    (hLocal : IsPointwiseLocalSigmaMeasurableOn (fun a : CoeffField d => a) U)
    (hSliceMeas :
      ∀ k : ℕ, MeasurableSet {a : CoeffField d | AEEQuantitativeEllipticSlice U k a})
    (hcover : ∀ a : CoeffField d, ∃ k : ℕ, AEEQuantitativeEllipticSlice U k a)
    (R : MuCorrectionSpaceRecoveryData U)
    [TopologicalSpace.SeparableSpace ↥R.correctionSpace]
    (system :
      ∀ k : ℕ, ∀ a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a},
        MuOperatorSystemData U a.1)
    (mu_eq_muCandidate :
      ∀ k : ℕ, ∀ a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a},
        ∀ P : BlockVec d,
          Mu U P a.1 =
            (((system k a).toMuOperatorRealization.toMuHilbertRealization
                R.toMuCorrectionSpaceData).muCandidate P)) :
    HasMeasurableMuFamily U := by
  exact hasMeasurableMuFamily_of_measurable_aeeQuantitativeSlice_sets
    (fun _k => measurable_toHilbertMatrixL2_aee_of_isOpen_volume_ne_top hUopen hUfinite)
    hLocal hSliceMeas hcover R system mu_eq_muCandidate

/-- Law-facing a.e. version of the AEE-slice `Mu` family bridge.  This is
the form naturally produced by a random law whose fields are only known to be
locally uniformly elliptic almost surely. -/
theorem aemeasurable_Mu_family_of_aeeQuantitativeSlice_sets
    {d : ℕ} {U : Set (Vec d)}
    (μ : MeasureTheory.Measure (CoeffField d))
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hToL2 :
      ∀ k : ℕ,
        @Measurable {a : CoeffField d // AEEQuantitativeEllipticSlice U k a}
          (MeasureTheory.Lp (HilbertMat d) 2 (volumeMeasureOn U))
          (AEEQuantitativeEllipticSlice.localMeasurableSpace U k) (borel _)
          AEEQuantitativeEllipticSlice.toHilbertMatrixL2)
    (hLocal : IsPointwiseLocalSigmaMeasurableOn (fun a : CoeffField d => a) U)
    (hSliceMeas :
      ∀ k : ℕ, MeasurableSet {a : CoeffField d | AEEQuantitativeEllipticSlice U k a})
    (hcover_ae :
      ∀ᵐ a ∂μ, ∃ k : ℕ, AEEQuantitativeEllipticSlice U k a)
    (R : MuCorrectionSpaceRecoveryData U)
    [TopologicalSpace.SeparableSpace ↥R.correctionSpace]
    (system :
      ∀ k : ℕ, ∀ a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a},
        MuOperatorSystemData U a.1)
    (mu_eq_muCandidate :
      ∀ k : ℕ, ∀ a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a},
        ∀ P : BlockVec d,
          Mu U P a.1 =
            (((system k a).toMuOperatorRealization.toMuHilbertRealization
                R.toMuCorrectionSpaceData).muCandidate P)) :
    ∀ P : BlockVec d, AEMeasurable (fun a : CoeffField d => Mu U P a) μ := by
  intro P
  simpa using
    (aemeasurable_Mu_comp_aeeQuantitativeSlice_sets μ
      (hToL2 := hToL2)
      (A := fun a : CoeffField d => a) hLocal hSliceMeas hcover_ae
      R system mu_eq_muCandidate P)

/-- Open finite-volume version of the law-facing a.e. AEE-slice `Mu`
family bridge. -/
theorem aemeasurable_Mu_family_of_aeeQuantitativeSlice_sets_of_isOpen_volume_ne_top
    {d : ℕ} {U : Set (Vec d)}
    (μ : MeasureTheory.Measure (CoeffField d))
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hUopen : IsOpen U) (hUfinite : MeasureTheory.volume U ≠ ⊤)
    (hLocal : IsPointwiseLocalSigmaMeasurableOn (fun a : CoeffField d => a) U)
    (hSliceMeas :
      ∀ k : ℕ, MeasurableSet {a : CoeffField d | AEEQuantitativeEllipticSlice U k a})
    (hcover_ae :
      ∀ᵐ a ∂μ, ∃ k : ℕ, AEEQuantitativeEllipticSlice U k a)
    (R : MuCorrectionSpaceRecoveryData U)
    [TopologicalSpace.SeparableSpace ↥R.correctionSpace]
    (system :
      ∀ k : ℕ, ∀ a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a},
        MuOperatorSystemData U a.1)
    (mu_eq_muCandidate :
      ∀ k : ℕ, ∀ a : {a : CoeffField d // AEEQuantitativeEllipticSlice U k a},
        ∀ P : BlockVec d,
          Mu U P a.1 =
            (((system k a).toMuOperatorRealization.toMuHilbertRealization
                R.toMuCorrectionSpaceData).muCandidate P)) :
    ∀ P : BlockVec d, AEMeasurable (fun a : CoeffField d => Mu U P a) μ := by
  exact aemeasurable_Mu_family_of_aeeQuantitativeSlice_sets μ
    (fun _k => measurable_toHilbertMatrixL2_aee_of_isOpen_volume_ne_top hUopen hUfinite)
    hLocal hSliceMeas hcover_ae R system mu_eq_muCandidate

end Homogenization
