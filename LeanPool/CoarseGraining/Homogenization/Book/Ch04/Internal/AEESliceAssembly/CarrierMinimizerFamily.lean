/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Internal.AEESliceAssembly.CarrierMuFamily

/-! # Carrier Minimizer Family -/

@[expose] public section

namespace Homogenization

open MeasureTheory
open scoped ENNReal
open scoped Topology
open Filter

/-!
# Carrier canonical-minimizer measurability (Packet P5f)

This file re-aims the raw AEE-slice canonical doubled-`Mu` Hilbert-minimizer
measurability spine (`AEESliceAssembly/MuFamily.lean`,
`measurable_energyBilin_fixed_...`,
`stronglyMeasurable_canonicalAEEMuHilbertMinimizer_...`) onto the honest carrier
`RegCoeffField d`, exactly as `CarrierMuFamily.lean` re-aims the coarse-grained
energy `Mu`.

As in `CarrierMuFamily`, the fine local σ-algebra of the raw slice subtype does
**not** reflect into the honest entry-test carrier σ-algebra `LocalSigmaR`, so the
raw primitives cannot be reused as black boxes.  The honest route is identical:
every measurability step factors through the `L²` coefficient realization, whose
carrier measurability is `measurable_toHilbertMatrixL2_carrier_cubeSet` (a finite
sum of localized entry-test generators).  The Hilbert-space selection/limit
scaffolding (dense generators, index selection, energy-gap limit) is entirely
domain-generic and is transcribed here over a generic measurable source
`A : Ω → RegCoeffField d`.

Reference: the paper (Armstrong–Kuusi–Loher, to appear).
-/

noncomputable section

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {d : ℕ} {k : ℕ}

/-- The raw AEE-slice element attached to a carrier source (public local copy of
the `CarrierMuFamily` private helper). -/
def slicePt (Q : TriadicCube d) (A : Ω → RegCoeffField d)
    (hSlice : ∀ ω, AEEQuantitativeEllipticSlice (cubeSet Q) k (A ω).toFun) (ω : Ω) :
    {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a} :=
  ⟨(A ω).toFun, hSlice ω⟩

section CarrierEngine

variable (Q : TriadicCube d) {A : Ω → RegCoeffField d}
  (hSlice : ∀ ω, AEEQuantitativeEllipticSlice (cubeSet Q) k (A ω).toFun)

include hSlice

/-- Carrier block-pairing average measurability from `hF` (mirrors
`measurable_blockEnergyAverage_carrier`). -/
theorem measurable_blockPairingAverage_carrier
    (hEntry : ∀ (i j : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ cubeSet Q →
      @Measurable Ω ℝ mΩ _ (fun ω => entryTestR i j φ (A ω)))
    (X Y : BlockState d) (hX : MemBlockL2 (cubeSet Q) X.eval)
    (hY : MemBlockL2 (cubeSet Q) Y.eval) :
    @Measurable Ω ℝ mΩ _ (fun ω => blockPairingAverage (cubeSet Q) (A ω).toFun X Y) := by
  have hF := measurable_toHilbertMatrixL2_carrier_cubeSet Q hSlice hEntry
  exact measurable_blockPairingAverage_comp_of_measurable_weightedFullBlockCoeffEntryIntegrals
    (A := fun ω => (A ω).toFun) (X := X) (Y := Y)
    (fun ω α β =>
      (hSlice ω).integrableOn_pairingWeightedFullBlockCoeffEntry_of_memBlockL2 hX hY α β)
    (fun α β =>
      measurable_integrableWeightedFullBlockCoeffEntry_carrier hF
        (integrable_blockPairingEntryWeight_of_memBlockL2 hX hY α β) α β)

/-- Carrier version of the fixed-generator energy pairing measurability: it equals
a fixed block-pairing average of the carrier field. -/
theorem measurable_energyBilin_fixed_generator_carrier
    (hEntry : ∀ (i j : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ cubeSet Q →
      @Measurable Ω ℝ mΩ _ (fun ω => entryTestR i j φ (A ω)))
    (P : BlockVec d) (Y : BlockState d) (hY : MemBlockL2 (cubeSet Q) Y.eval)
    (Z : canonicalMuBlockCorrectionGeneratorSubmodule (cubeSet Q)) :
    @Measurable Ω ℝ mΩ _
      (fun ω =>
        ((canonicalAEEMuOperatorSystemData Q k (slicePt Q A hSlice ω)).toMuHilbertRealization).energyBilin
          (toHilbertBlockL2OfBlockField (U := cubeSet Q) hY)
          (blockVecToHilbertBlockL2Const (U := cubeSet Q) P +
            canonicalMuCorrectionGeneratorEmbedding (cubeSet Q) Z)) := by
  let U : Set (Vec d) := cubeSet Q
  let Xstate : BlockState d := canonicalMuGeneratorAffineField (U := U) P Z
  have hX : MemBlockL2 U Xstate.eval := by
    simpa [Xstate] using canonicalMuGeneratorAffineField_memBlockL2 (U := U) P Z
  have hRewrite :
      (fun ω =>
        ((canonicalAEEMuOperatorSystemData Q k (slicePt Q A hSlice ω)).toMuHilbertRealization).energyBilin
          (toHilbertBlockL2OfBlockField (U := cubeSet Q) hY)
          (blockVecToHilbertBlockL2Const (U := cubeSet Q) P +
            canonicalMuCorrectionGeneratorEmbedding (cubeSet Q) Z)) =
        fun ω => blockPairingAverage (cubeSet Q) (A ω).toFun Xstate Y := by
    funext ω
    let a := slicePt Q A hSlice ω
    let system : AEEMuOperatorSystemData U a.1 := canonicalAEEMuOperatorSystemData Q k a
    have hX_hilbert :
        toHilbertBlockL2OfBlockField (U := U) (by simpa [U, Xstate] using hX) =
          blockVecToHilbertBlockL2Const (U := U) P +
            canonicalMuCorrectionGeneratorEmbedding U Z := by
      simpa [U, Xstate] using
        canonicalMuGeneratorAffineField_hilbert_eq_const_add (U := cubeSet Q) P Z
    calc
      ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).energyBilin
          (toHilbertBlockL2OfBlockField (U := cubeSet Q) hY)
          (blockVecToHilbertBlockL2Const (U := cubeSet Q) P +
            canonicalMuCorrectionGeneratorEmbedding (cubeSet Q) Z)
          =
        energyBilinOfOperator system.toMuOperatorRealization.operator
          (toHilbertBlockL2OfBlockField (U := U) (by simpa [U] using hY))
          (toHilbertBlockL2OfBlockField (U := U) (by simpa [U, Xstate] using hX)) := by
            simp [U, system, AEEMuOperatorSystemData.toMuHilbertRealization,
              MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator,
              hX_hilbert]
      _ = blockPairingAverage U a.1 Xstate Y := by
            exact
              system.toMuOperatorRealization.energyBilin_eq_blockPairingAverage_of_blockState
                (X := Xstate) (Y := Y)
                (by simpa [U, Xstate] using hX) (by simpa [U] using hY)
  rw [hRewrite]
  exact measurable_blockPairingAverage_carrier Q hSlice hEntry Xstate Y hX hY

/-- **Carrier canonical doubled-`Mu` Hilbert-minimizer strong measurability.**
Generic re-aim of
`stronglyMeasurable_canonicalAEEMuHilbertMinimizer_aeeQuantitativeSlice_cubeSet`. -/
theorem stronglyMeasurable_canonicalMinimizer_carrier
    (hEntry : ∀ (i j : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ cubeSet Q →
      @Measurable Ω ℝ mΩ _ (fun ω => entryTestR i j φ (A ω)))
    (P : BlockVec d) :
    @MeasureTheory.StronglyMeasurable Ω (HilbertBlockL2 (cubeSet Q)) _ mΩ
      (fun ω =>
        ((canonicalAEEMuOperatorSystemData Q k (slicePt Q A hSlice ω)).toMuHilbertRealization).minimizerMap P) := by
  classical
  let U : Set (Vec d) := cubeSet Q
  have hF := measurable_toHilbertMatrixL2_carrier_cubeSet Q hSlice hEntry
  let K : ClosedSubmodule ℝ (HilbertBlockL2 U) :=
    (canonicalAEEMuCorrectionSpaceData Q).correctionSpace
  let ξ : ℕ → canonicalMuBlockCorrectionGeneratorSubmodule U :=
    TopologicalSpace.denseSeq (canonicalMuBlockCorrectionGeneratorSubmodule U)
  let candidate : ℕ → HilbertBlockL2 U := fun n =>
    blockVecToHilbertBlockL2Const (U := U) P +
      (canonicalMuCorrectionGeneratorEmbedding U (ξ n) : HilbertBlockL2 U)
  let energy : Ω → ℕ → ℝ := fun ω n =>
    blockEnergyAverage U (A ω).toFun (canonicalMuGeneratorAffineField (U := U) P (ξ n))
  let ε : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
  have hEnergy_meas : ∀ n : ℕ, Measurable fun ω : Ω => energy ω n := by
    intro n
    simpa [energy, U, ξ] using
      measurable_blockEnergyAverage_carrier hF
        (canonicalMuGeneratorAffineField (U := U) P (ξ n))
        (canonicalMuGeneratorAffineField_memBlockL2 (U := U) P (ξ n))
  have hMu_meas : Measurable fun ω : Ω => Mu U P (A ω).toFun :=
    measurable_Mu_comp_aeeSlice_of_measurable_entryTest Q hSlice hEntry P
  have hExists : ∀ m : ℕ, ∀ ω : Ω, ∃ n : ℕ, energy ω n ≤ Mu U P (A ω).toFun + ε m := by
    intro m ω
    have hmu : Mu U P (A ω).toFun = ⨅ n : ℕ, energy ω n := by
      simpa [energy, U, ξ] using!
        mu_eq_iInf_blockEnergyAverage_canonicalAEEMuGenerator Q k (slicePt Q A hSlice ω) P
    have hlt : (⨅ n : ℕ, energy ω n) < (⨅ n : ℕ, energy ω n) + ε m := by
      have hpos : 0 < ε m := by simp only [ε]; positivity
      exact lt_add_of_le_of_pos (le_refl (⨅ n : ℕ, energy ω n)) hpos
    rcases exists_lt_of_ciInf_lt hlt with ⟨n, hn⟩
    exact ⟨n, le_of_lt (by simpa [hmu] using hn)⟩
  let index : ℕ → Ω → ℕ := fun m ω => Nat.find (hExists m ω)
  have hGood_meas :
      ∀ m n : ℕ, MeasurableSet {ω : Ω | energy ω n ≤ Mu U P (A ω).toFun + ε m} := by
    intro m n
    exact measurableSet_le (hEnergy_meas n) (hMu_meas.add measurable_const)
  have hIndex_meas : ∀ m : ℕ, Measurable (index m) := by
    intro m
    simpa [index] using measurable_find (hExists m) (hGood_meas m)
  have hCandidate_strong : MeasureTheory.StronglyMeasurable candidate :=
    MeasureTheory.StronglyMeasurable.of_discrete
  have hApprox_strong :
      ∀ m : ℕ, MeasureTheory.StronglyMeasurable fun ω : Ω => candidate (index m ω) := by
    intro m
    simpa [Function.comp_def] using hCandidate_strong.comp_measurable (hIndex_meas m)
  have hε_tendsto : Tendsto ε atTop (𝓝 0) := by
    have hbase : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [ε] using hbase
  have hlim :
      Tendsto
        (fun m : ℕ => fun ω : Ω => candidate (index m ω))
        atTop
        (𝓝 fun ω : Ω =>
          let H := ((canonicalAEEMuOperatorSystemData Q k (slicePt Q A hSlice ω)).toMuHilbertRealization)
          affineMinimizerMap K H.energyBilin H.energyCoercive (H.constantField P)) := by
    rw [tendsto_pi_nhds]
    intro ω
    let a := slicePt Q A hSlice ω
    let H := ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization)
    have hmem : ∀ m : ℕ, candidate (index m ω) - H.constantField P ∈ K := by
      intro m
      change candidate (index m ω) - H.constantField P ∈
        (canonicalAEEMuCorrectionSpaceData Q).correctionSpace
      have hconst : H.constantField P = blockVecToHilbertBlockL2Const (U := U) P := rfl
      have hcand : candidate (index m ω) =
          blockVecToHilbertBlockL2Const (U := U) P +
            (canonicalMuCorrectionGeneratorEmbedding U (ξ (index m ω)) : HilbertBlockL2 U) := rfl
      rw [hcand, hconst, add_sub_cancel_left]
      exact (canonicalMuCorrectionGeneratorEmbedding U (ξ (index m ω))).2
    have hnear :
        ∀ m : ℕ,
          quadraticEnergy H.energyBilin (candidate (index m ω)) ≤
            quadraticEnergy H.energyBilin
              (affineMinimizerMap K H.energyBilin H.energyCoercive (H.constantField P)) +
              ε m := by
      intro m
      have hgood : energy ω (index m ω) ≤ Mu U P (A ω).toFun + ε m := by
        simpa [index] using Nat.find_spec (hExists m ω)
      have hqe :
          quadraticEnergy H.energyBilin (candidate (index m ω)) =
            energy ω (index m ω) := by
        simpa [H, a, candidate, energy, U, ξ] using!
          canonicalAEEMuOperatorSystemData_quadraticEnergy_generatorAffine_eq_blockEnergyAverage
            Q k a P (ξ (index m ω))
      have hmu :
          Mu U P (A ω).toFun =
            quadraticEnergy H.energyBilin
              (affineMinimizerMap K H.energyBilin H.energyCoercive (H.constantField P)) := by
        simpa [H, a, K, U, MuHilbertRealization.muCandidate, MuHilbertProblem.muCandidate,
          MuHilbertRealization.minimizerMap, MuHilbertProblem.minimizerMap,
          parameterAffineMinimizerMap] using!
          mu_eq_canonicalAEEMuCandidate Q k a P
      calc
        quadraticEnergy H.energyBilin (candidate (index m ω))
            = energy ω (index m ω) := hqe
        _ ≤ Mu U P (A ω).toFun + ε m := hgood
        _ = quadraticEnergy H.energyBilin
              (affineMinimizerMap K H.energyBilin H.energyCoercive (H.constantField P)) +
              ε m := by rw [hmu]
    exact tendsto_of_quadraticEnergy_le_min_add_eps
      K H.energyCoercive H.energySymm (H.constantField P) hmem hε_tendsto hnear
  have hAffine :
      MeasureTheory.StronglyMeasurable
        (fun ω : Ω =>
          let H := ((canonicalAEEMuOperatorSystemData Q k (slicePt Q A hSlice ω)).toMuHilbertRealization)
          affineMinimizerMap K H.energyBilin H.energyCoercive (H.constantField P)) :=
    stronglyMeasurable_of_tendsto atTop hApprox_strong hlim
  simpa [U, K, MuHilbertRealization.minimizerMap, MuHilbertProblem.minimizerMap,
    parameterAffineMinimizerMap] using! hAffine

/-- **Carrier fixed-test energy-pairing measurability against the canonical
minimizer.**  Generic re-aim of
`measurable_energyBilin_fixed_canonicalAEEMuHilbertMinimizer_aeeQuantitativeSlice_cubeSet`. -/
theorem measurable_energyBilin_fixed_canonicalMinimizer_carrier
    (hEntry : ∀ (i j : Fin d) {φ : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ → tsupport φ ⊆ cubeSet Q →
      @Measurable Ω ℝ mΩ _ (fun ω => entryTestR i j φ (A ω)))
    (P : BlockVec d) (Y : BlockState d) (hY : MemBlockL2 (cubeSet Q) Y.eval) :
    @Measurable Ω ℝ mΩ _
      (fun ω =>
        ((canonicalAEEMuOperatorSystemData Q k (slicePt Q A hSlice ω)).toMuHilbertRealization).energyBilin
          (toHilbertBlockL2OfBlockField (U := cubeSet Q) hY)
          (((canonicalAEEMuOperatorSystemData Q k (slicePt Q A hSlice ω)).toMuHilbertRealization).minimizerMap P)) := by
  classical
  let U : Set (Vec d) := cubeSet Q
  have hF := measurable_toHilbertMatrixL2_carrier_cubeSet Q hSlice hEntry
  let K : ClosedSubmodule ℝ (HilbertBlockL2 U) :=
    (canonicalAEEMuCorrectionSpaceData Q).correctionSpace
  let ξ : ℕ → canonicalMuBlockCorrectionGeneratorSubmodule U :=
    TopologicalSpace.denseSeq (canonicalMuBlockCorrectionGeneratorSubmodule U)
  let y : HilbertBlockL2 U := toHilbertBlockL2OfBlockField (U := U) (by simpa [U] using hY)
  let candidate : ℕ → HilbertBlockL2 U := fun n =>
    blockVecToHilbertBlockL2Const (U := U) P +
      (canonicalMuCorrectionGeneratorEmbedding U (ξ n) : HilbertBlockL2 U)
  let energy : Ω → ℕ → ℝ := fun ω n =>
    blockEnergyAverage U (A ω).toFun (canonicalMuGeneratorAffineField (U := U) P (ξ n))
  let ε : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
  have hEnergy_meas : ∀ n : ℕ, Measurable fun ω : Ω => energy ω n := by
    intro n
    simpa [energy, U, ξ] using
      measurable_blockEnergyAverage_carrier hF
        (canonicalMuGeneratorAffineField (U := U) P (ξ n))
        (canonicalMuGeneratorAffineField_memBlockL2 (U := U) P (ξ n))
  have hMu_meas : Measurable fun ω : Ω => Mu U P (A ω).toFun :=
    measurable_Mu_comp_aeeSlice_of_measurable_entryTest Q hSlice hEntry P
  have hExists : ∀ m : ℕ, ∀ ω : Ω, ∃ n : ℕ, energy ω n ≤ Mu U P (A ω).toFun + ε m := by
    intro m ω
    have hmu : Mu U P (A ω).toFun = ⨅ n : ℕ, energy ω n := by
      simpa [energy, U, ξ] using!
        mu_eq_iInf_blockEnergyAverage_canonicalAEEMuGenerator Q k (slicePt Q A hSlice ω) P
    have hlt : (⨅ n : ℕ, energy ω n) < (⨅ n : ℕ, energy ω n) + ε m := by
      have hpos : 0 < ε m := by simp only [ε]; positivity
      exact lt_add_of_le_of_pos (le_refl (⨅ n : ℕ, energy ω n)) hpos
    rcases exists_lt_of_ciInf_lt hlt with ⟨n, hn⟩
    exact ⟨n, le_of_lt (by simpa [hmu] using hn)⟩
  let index : ℕ → Ω → ℕ := fun m ω => Nat.find (hExists m ω)
  have hGood_meas :
      ∀ m n : ℕ, MeasurableSet {ω : Ω | energy ω n ≤ Mu U P (A ω).toFun + ε m} := by
    intro m n
    exact measurableSet_le (hEnergy_meas n) (hMu_meas.add measurable_const)
  have hApprox_meas :
      ∀ n : ℕ,
        Measurable fun ω : Ω =>
          ((canonicalAEEMuOperatorSystemData Q k (slicePt Q A hSlice ω)).toMuHilbertRealization).energyBilin
            y (candidate n) := by
    intro n
    simpa [U, y, candidate, ξ] using
      measurable_energyBilin_fixed_generator_carrier Q hSlice hEntry P Y hY (ξ n)
  have hSelected_meas :
      ∀ m : ℕ,
        Measurable fun ω : Ω =>
          ((canonicalAEEMuOperatorSystemData Q k (slicePt Q A hSlice ω)).toMuHilbertRealization).energyBilin
            y (candidate (index m ω)) := by
    intro m
    let p : ℕ → Ω → Prop := fun n ω => energy ω n ≤ Mu U P (A ω).toFun + ε m
    have hp : ∀ n : ℕ, MeasurableSet {ω : Ω | p n ω} := by
      intro n; simpa [p] using hGood_meas m n
    have hexists : ∀ ω : Ω, ∃ n : ℕ, p n ω := by
      intro ω; simpa [p] using hExists m ω
    simpa [p, index] using
      (Measurable.find
        (f := fun n ω =>
          ((canonicalAEEMuOperatorSystemData Q k (slicePt Q A hSlice ω)).toMuHilbertRealization).energyBilin
            y (candidate n))
        (p := p) hApprox_meas hp hexists)
  have hSelected_strong :
      ∀ m : ℕ,
        MeasureTheory.StronglyMeasurable fun ω : Ω =>
          ((canonicalAEEMuOperatorSystemData Q k (slicePt Q A hSlice ω)).toMuHilbertRealization).energyBilin
            y (candidate (index m ω)) :=
    fun m => (hSelected_meas m).stronglyMeasurable
  have hε_tendsto : Tendsto ε atTop (𝓝 0) := by
    have hbase : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [ε] using hbase
  have hlim_scalar :
      Tendsto
        (fun m : ℕ => fun ω : Ω =>
          ((canonicalAEEMuOperatorSystemData Q k (slicePt Q A hSlice ω)).toMuHilbertRealization).energyBilin
            y (candidate (index m ω)))
        atTop
        (𝓝 fun ω : Ω =>
          let H := ((canonicalAEEMuOperatorSystemData Q k (slicePt Q A hSlice ω)).toMuHilbertRealization)
          H.energyBilin y (H.minimizerMap P)) := by
    rw [tendsto_pi_nhds]
    intro ω
    let a := slicePt Q A hSlice ω
    let H := ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization)
    have hmem : ∀ m : ℕ, candidate (index m ω) - H.constantField P ∈ K := by
      intro m
      change candidate (index m ω) - H.constantField P ∈
        (canonicalAEEMuCorrectionSpaceData Q).correctionSpace
      have hconst : H.constantField P = blockVecToHilbertBlockL2Const (U := U) P := rfl
      have hcand : candidate (index m ω) =
          blockVecToHilbertBlockL2Const (U := U) P +
            (canonicalMuCorrectionGeneratorEmbedding U (ξ (index m ω)) : HilbertBlockL2 U) := rfl
      rw [hcand, hconst, add_sub_cancel_left]
      exact (canonicalMuCorrectionGeneratorEmbedding U (ξ (index m ω))).2
    have hnear :
        ∀ m : ℕ,
          quadraticEnergy H.energyBilin (candidate (index m ω)) ≤
            quadraticEnergy H.energyBilin
              (affineMinimizerMap K H.energyBilin H.energyCoercive (H.constantField P)) +
              ε m := by
      intro m
      have hgood : energy ω (index m ω) ≤ Mu U P (A ω).toFun + ε m := by
        simpa [index] using Nat.find_spec (hExists m ω)
      have hqe :
          quadraticEnergy H.energyBilin (candidate (index m ω)) =
            energy ω (index m ω) := by
        simpa [H, a, candidate, energy, U, ξ] using!
          canonicalAEEMuOperatorSystemData_quadraticEnergy_generatorAffine_eq_blockEnergyAverage
            Q k a P (ξ (index m ω))
      have hmu :
          Mu U P (A ω).toFun =
            quadraticEnergy H.energyBilin
              (affineMinimizerMap K H.energyBilin H.energyCoercive (H.constantField P)) := by
        simpa [H, a, K, U, MuHilbertRealization.muCandidate, MuHilbertProblem.muCandidate,
          MuHilbertRealization.minimizerMap, MuHilbertProblem.minimizerMap,
          parameterAffineMinimizerMap] using!
          mu_eq_canonicalAEEMuCandidate Q k a P
      calc
        quadraticEnergy H.energyBilin (candidate (index m ω))
            = energy ω (index m ω) := hqe
        _ ≤ Mu U P (A ω).toFun + ε m := hgood
        _ = quadraticEnergy H.energyBilin
              (affineMinimizerMap K H.energyBilin H.energyCoercive (H.constantField P)) +
              ε m := by rw [hmu]
    have hHilbert :
        Tendsto (fun m : ℕ => candidate (index m ω)) atTop
          (𝓝 (affineMinimizerMap K H.energyBilin H.energyCoercive (H.constantField P))) :=
      tendsto_of_quadraticEnergy_le_min_add_eps
        K H.energyCoercive H.energySymm (H.constantField P) hmem hε_tendsto hnear
    have hHilbert' :
        Tendsto (fun m : ℕ => candidate (index m ω)) atTop
          (𝓝 (H.minimizerMap P)) := by
      simpa [H, K, MuHilbertRealization.minimizerMap, MuHilbertProblem.minimizerMap,
        parameterAffineMinimizerMap] using! hHilbert
    exact (H.energyBilin y).continuous.tendsto (H.minimizerMap P) |>.comp hHilbert'
  have hStrong :
      MeasureTheory.StronglyMeasurable
        (fun ω : Ω =>
          let H := ((canonicalAEEMuOperatorSystemData Q k (slicePt Q A hSlice ω)).toMuHilbertRealization)
          H.energyBilin y (H.minimizerMap P)) :=
    stronglyMeasurable_of_tendsto atTop hSelected_strong hlim_scalar
  simpa [U, y] using hStrong.measurable

end CarrierEngine

end

end Homogenization
