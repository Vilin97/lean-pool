/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuOperator.CoeffOperator
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuAdmissibility
import LeanPool.CoarseGraining.Homogenization.Probability.LocalEllipticitySlices
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuOperator.AEEOperator.CoeffOperatorData
import Mathlib.Topology.Order.IsLUB

/-! # Canonical Cube Set -/

namespace Homogenization

noncomputable section


namespace PotentialSolenoidalL2Data

variable {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}

/-- Build the AEE doubled operator system from a packaged correction space and
a.e.-representative coefficient-operator data. -/
noncomputable def toAEEMuOperatorSystemData (M : PotentialSolenoidalL2Data U)
    (coeffOperatorData : AEEMuCoeffOperatorData U a) :
    AEEMuOperatorSystemData U a where
  correctionSpace := M.toMuCorrectionSpaceData
  coeffOperatorData := coeffOperatorData

/-- Build the AEE doubled operator system from the old pointwise elliptic
constructor.  This is a compatibility bridge; the genuinely new Phase 3
constructor will start from spatial-a.e. ellipticity instead. -/
noncomputable def toAEEMuOperatorSystemDataOfIsEllipticFieldOn
    (M : PotentialSolenoidalL2Data U) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal) :
    AEEMuOperatorSystemData U a :=
  let coeffOperatorData : MuCoeffOperatorData U a :=
    MuCoeffOperatorData.ofIsEllipticFieldOn (U := U) (a := a) hEll
  M.toAEEMuOperatorSystemData
    (AEEMuCoeffOperatorData.ofMuCoeffOperatorDataOfIsEllipticFieldOn
      coeffOperatorData hEll hvol)

@[simp] theorem correctionSpace_toAEEMuOperatorSystemData
    (M : PotentialSolenoidalL2Data U)
    (coeffOperatorData : AEEMuCoeffOperatorData U a) :
    (M.toAEEMuOperatorSystemData coeffOperatorData).correctionSpace =
      M.toMuCorrectionSpaceData :=
  rfl

end PotentialSolenoidalL2Data

section CanonicalCubeSet

/-- Half-open triadic cubes carry finite restricted volume measure. -/
instance (priority := 900) instIsFiniteMeasureVolumeMeasureOnCubeSetAEEOperator
    {d : ℕ} (Q : TriadicCube d) :
    MeasureTheory.IsFiniteMeasure (volumeMeasureOn (cubeSet Q)) := by
  let : Fact (MeasureTheory.volume (cubeSet Q) < ⊤) := ⟨volume_cubeSet_lt_top Q⟩
  change MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict (cubeSet Q))
  infer_instance

/-- Half-open triadic cubes have positive volume in `toReal` form. -/
theorem volume_cubeSet_toReal_pos {d : ℕ} (Q : TriadicCube d) :
    0 < (MeasureTheory.volume (cubeSet Q)).toReal := by
  rw [volume_cubeSet_toReal]
  exact cubeVolume_pos Q

/-- Canonical potential/solenoidal `L²` data used by the AEE cube-set operator
system. -/
noncomputable def canonicalAEEPotentialSolenoidalL2Data {d : ℕ} (Q : TriadicCube d) :
    PotentialSolenoidalL2Data (cubeSet Q) :=
  PotentialSolenoidalL2Data.ofSubmoduleClosures (cubeSet Q)

/-- Canonical Hilbert correction space for the AEE doubled `\mu` problem on a
half-open triadic cube. -/
noncomputable def canonicalAEEMuCorrectionSpaceData {d : ℕ} (Q : TriadicCube d) :
    MuCorrectionSpaceData (cubeSet Q) :=
  (canonicalAEEPotentialSolenoidalL2Data Q).toMuCorrectionSpaceData

instance canonicalAEEMuCorrectionSpaceData_separable {d : ℕ} (Q : TriadicCube d) :
    TopologicalSpace.SeparableSpace
      ↥(canonicalAEEMuCorrectionSpaceData Q).correctionSpace := by
  let : Fact ((1 : ENNReal) ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  infer_instance

/-- Canonical AEE coefficient-operator data on one quantitative AEE cube
slice. -/
noncomputable def canonicalAEEMuCoeffOperatorData
    {d : ℕ} (Q : TriadicCube d) (k : ℕ)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a}) :
    AEEMuCoeffOperatorData (cubeSet Q) a.1 :=
  AEEMuCoeffOperatorData.ofIsAEEllipticFieldOn
    (U := cubeSet Q) (a := a.1) a.2 (volume_cubeSet_toReal_pos Q)

/-- Canonical AEE doubled operator system on one quantitative AEE cube slice. -/
noncomputable def canonicalAEEMuOperatorSystemData
    {d : ℕ} (Q : TriadicCube d) (k : ℕ)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a}) :
    AEEMuOperatorSystemData (cubeSet Q) a.1 where
  correctionSpace := canonicalAEEMuCorrectionSpaceData Q
  coeffOperatorData := canonicalAEEMuCoeffOperatorData Q k a

@[simp] theorem correctionSpace_canonicalAEEMuOperatorSystemData
    {d : ℕ} (Q : TriadicCube d) (k : ℕ)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a}) :
    (canonicalAEEMuOperatorSystemData Q k a).correctionSpace =
      canonicalAEEMuCorrectionSpaceData Q :=
  rfl

@[simp] theorem coeffOperatorData_canonicalAEEMuOperatorSystemData
    {d : ℕ} (Q : TriadicCube d) (k : ℕ)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a}) :
    (canonicalAEEMuOperatorSystemData Q k a).coeffOperatorData =
      canonicalAEEMuCoeffOperatorData Q k a :=
  rfl

/-- The canonical AEE Hilbert bilinear form on dense generator corrections is
the fixed block-pairing average of their chosen pointwise representatives. -/
theorem canonicalAEEMuOperatorSystemData_energyBilin_generator_eq_blockPairingAverage
    {d : ℕ} (Q : TriadicCube d) (k : ℕ)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a})
    (Y Z : canonicalMuBlockCorrectionGeneratorSubmodule (cubeSet Q)) :
    ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).energyBilin
        (canonicalMuCorrectionGeneratorEmbedding (cubeSet Q) Y)
        (canonicalMuCorrectionGeneratorEmbedding (cubeSet Q) Z) =
      blockPairingAverage (cubeSet Q) a.1
        (canonicalMuGeneratorAffineField (U := cubeSet Q) (0 : BlockVec d) Z)
        (canonicalMuGeneratorAffineField (U := cubeSet Q) (0 : BlockVec d) Y) := by
  let U : Set (Vec d) := cubeSet Q
  let system : AEEMuOperatorSystemData U a.1 := canonicalAEEMuOperatorSystemData Q k a
  let HY : MemBlockL2 U
      (canonicalMuGeneratorAffineField (U := U) (0 : BlockVec d) Y).eval :=
    canonicalMuGeneratorAffineField_memBlockL2 (U := U) (0 : BlockVec d) Y
  let HZ : MemBlockL2 U
      (canonicalMuGeneratorAffineField (U := U) (0 : BlockVec d) Z).eval :=
    canonicalMuGeneratorAffineField_memBlockL2 (U := U) (0 : BlockVec d) Z
  have hY :
      toHilbertBlockL2OfBlockField (U := U) HY =
        canonicalMuCorrectionGeneratorEmbedding U Y :=
    canonicalMuGeneratorAffineField_zero_hilbert_eq (U := U) Y
  have hZ :
      toHilbertBlockL2OfBlockField (U := U) HZ =
        canonicalMuCorrectionGeneratorEmbedding U Z :=
    canonicalMuGeneratorAffineField_zero_hilbert_eq (U := U) Z
  calc
    ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).energyBilin
        (canonicalMuCorrectionGeneratorEmbedding (cubeSet Q) Y)
        (canonicalMuCorrectionGeneratorEmbedding (cubeSet Q) Z)
        =
      energyBilinOfOperator system.toMuOperatorRealization.operator
        (toHilbertBlockL2OfBlockField (U := U) HY)
        (toHilbertBlockL2OfBlockField (U := U) HZ) := by
          simp [U, system, AEEMuOperatorSystemData.toMuHilbertRealization,
            MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator,
            hY, hZ]
    _ = blockPairingAverage U a.1
        (canonicalMuGeneratorAffineField (U := U) (0 : BlockVec d) Z)
        (canonicalMuGeneratorAffineField (U := U) (0 : BlockVec d) Y) := by
          exact
            system.toMuOperatorRealization.energyBilin_eq_blockPairingAverage_of_blockState
              (X := canonicalMuGeneratorAffineField (U := U) (0 : BlockVec d) Z)
              (Y := canonicalMuGeneratorAffineField (U := U) (0 : BlockVec d) Y)
              HZ HY

/-- The canonical AEE Hilbert bilinear form on a constant affine shift and a
dense-generator correction is the fixed block-pairing average of their chosen
pointwise representatives. -/
theorem canonicalAEEMuOperatorSystemData_energyBilin_const_generator_eq_blockPairingAverage
    {d : ℕ} (Q : TriadicCube d) (k : ℕ)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a})
    (P : BlockVec d)
    (Y : canonicalMuBlockCorrectionGeneratorSubmodule (cubeSet Q)) :
    ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).energyBilin
        (((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).constantField P)
        (canonicalMuCorrectionGeneratorEmbedding (cubeSet Q) Y) =
      blockPairingAverage (cubeSet Q) a.1
        (canonicalMuGeneratorAffineField (U := cubeSet Q) (0 : BlockVec d) Y)
        (canonicalMuGeneratorAffineField
          (U := cubeSet Q) P (0 : canonicalMuBlockCorrectionGeneratorSubmodule (cubeSet Q))) := by
  let U : Set (Vec d) := cubeSet Q
  let system : AEEMuOperatorSystemData U a.1 := canonicalAEEMuOperatorSystemData Q k a
  let HP : MemBlockL2 U
      (canonicalMuGeneratorAffineField
        (U := U) P (0 : canonicalMuBlockCorrectionGeneratorSubmodule U)).eval :=
    canonicalMuGeneratorAffineField_memBlockL2
      (U := U) P (0 : canonicalMuBlockCorrectionGeneratorSubmodule U)
  let HY : MemBlockL2 U
      (canonicalMuGeneratorAffineField (U := U) (0 : BlockVec d) Y).eval :=
    canonicalMuGeneratorAffineField_memBlockL2 (U := U) (0 : BlockVec d) Y
  have hP :
      toHilbertBlockL2OfBlockField (U := U) HP =
        blockVecToHilbertBlockL2Const (U := U) P :=
    canonicalMuGeneratorAffineField_zeroCorrection_hilbert_eq_const (U := U) P
  have hY :
      toHilbertBlockL2OfBlockField (U := U) HY =
        canonicalMuCorrectionGeneratorEmbedding U Y :=
    canonicalMuGeneratorAffineField_zero_hilbert_eq (U := U) Y
  calc
    ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).energyBilin
        (((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).constantField P)
        (canonicalMuCorrectionGeneratorEmbedding (cubeSet Q) Y)
        =
      energyBilinOfOperator system.toMuOperatorRealization.operator
        (toHilbertBlockL2OfBlockField (U := U) HP)
        (toHilbertBlockL2OfBlockField (U := U) HY) := by
          simp [U, system, AEEMuOperatorSystemData.toMuHilbertRealization,
            MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator,
            hP, hY]
    _ = blockPairingAverage U a.1
        (canonicalMuGeneratorAffineField (U := U) (0 : BlockVec d) Y)
        (canonicalMuGeneratorAffineField
          (U := U) P (0 : canonicalMuBlockCorrectionGeneratorSubmodule U)) := by
          exact
            system.toMuOperatorRealization.energyBilin_eq_blockPairingAverage_of_blockState
              (X := canonicalMuGeneratorAffineField (U := U) (0 : BlockVec d) Y)
              (Y := canonicalMuGeneratorAffineField
                (U := U) P (0 : canonicalMuBlockCorrectionGeneratorSubmodule U))
              HY HP

/-- The variational `Mu` on a quantitative AEE cube slice agrees with the
canonical AEE Hilbert-operator candidate. -/
theorem mu_eq_canonicalAEEMuCandidate
    {d : ℕ} (Q : TriadicCube d) (k : ℕ)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a})
    (P0 : BlockVec d) :
    Mu (cubeSet Q) P0 a.1 =
      ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization).muCandidate P0 := by
  let U : Set (Vec d) := cubeSet Q
  let system : AEEMuOperatorSystemData U a.1 := canonicalAEEMuOperatorSystemData Q k a
  let H : MuHilbertRealization U a.1 := system.toMuHilbertRealization
  let gen : canonicalMuBlockCorrectionGeneratorSubmodule U →
      H.correctionSpace.correctionSpace.toSubmodule := by
    intro Y
    exact canonicalMuCorrectionGeneratorEmbedding U Y
  let s : Set ℝ := Set.range fun Y : canonicalMuBlockCorrectionGeneratorSubmodule U =>
    quadraticEnergy H.energyBilin (H.constantField P0 + (gen Y : HilbertBlockL2 U))
  have hgen_dense : DenseRange gen := by
    dsimp [gen, H, system, U]
    simpa [canonicalAEEMuOperatorSystemData, canonicalAEEMuCorrectionSpaceData,
      canonicalAEEPotentialSolenoidalL2Data, MuCorrectionSpaceData.ofSubmoduleClosures,
      AEEMuOperatorSystemData.toMuHilbertRealization,
      MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator] using!
      denseRange_canonicalMuCorrectionGeneratorEmbedding U
  have hCandidate_sInf : H.muCandidate P0 = sInf s := by
    simpa [s] using
      H.muCandidate_eq_sInf_quadraticEnergy_denseRange P0 gen hgen_dense
  have hCandidateLe :
      ∀ X : BlockState d, IsBlockMuAdmissible U P0 X →
        H.muCandidate P0 ≤ blockEnergyAverage U a.1 X := by
    intro X hX
    have hXmem : MemBlockL2 U X.eval := hX.memBlockL2_eval
    have hcorr_mem :
        toHilbertBlockL2OfBlockField (U := U) hXmem - H.constantField P0 ∈
          H.correctionSpace.correctionSpace := by
      have hsplit := hX.toHilbertBlockL2OfBlockField_eq_blockVecToHilbertBlockL2Const_add
      rw [hsplit]
      have hcorr := hX.toCorrectionFieldData_mem_correctionSpace
      simpa [H, system, U, canonicalAEEMuOperatorSystemData, canonicalAEEMuCorrectionSpaceData,
        canonicalAEEPotentialSolenoidalL2Data, MuCorrectionSpaceData.ofSubmoduleClosures,
        AEEMuOperatorSystemData.toMuHilbertRealization,
        MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator,
        sub_eq_add_neg, add_assoc, add_comm] using hcorr
    have hmin :
        H.muCandidate P0 ≤
          quadraticEnergy H.energyBilin (toHilbertBlockL2OfBlockField (U := U) hXmem) :=
      H.muCandidate_le_quadraticEnergy P0
        (toHilbertBlockL2OfBlockField (U := U) hXmem) hcorr_mem
    calc
      H.muCandidate P0 ≤
          quadraticEnergy H.energyBilin (toHilbertBlockL2OfBlockField (U := U) hXmem) := hmin
      _ = blockEnergyAverage U a.1 X := by
        simpa [H, system, AEEMuOperatorSystemData.toMuHilbertRealization,
          MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator] using
          system.toMuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_of_blockState
            (X := X) hXmem
  have hBddBelow : BddBelow (muValueSet U P0 a.1) := by
    refine ⟨H.muCandidate P0, ?_⟩
    intro m hm
    rcases hm with ⟨X, hX, rfl⟩
    simpa [blockEnergyAverage] using hCandidateLe X hX
  have hCandidate_le_Mu : H.muCandidate P0 ≤ Mu U P0 a.1 := by
    apply le_Mu_of_forall_isBlockMuAdmissible
    intro X hX
    simpa [blockEnergyAverage] using hCandidateLe X hX
  have hs_subset_mu : s ⊆ muValueSet U P0 a.1 := by
    intro m hm
    rcases hm with ⟨Y, rfl⟩
    rcases Y.property with ⟨f, g, hf, hg, hY, hpot, hsol⟩
    let X : BlockState d :=
      { potential := fun x => P0.1 + f x
        flux := fun x => P0.2 + g x }
    have hAdm : IsBlockMuAdmissible U P0 X := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [X, sub_eq_add_neg, add_assoc, add_comm] using hf
      · simpa [X, sub_eq_add_neg, add_assoc, add_comm] using hpot
      · simpa [X, sub_eq_add_neg, add_assoc, add_comm] using hg
      · simpa [X, sub_eq_add_neg, add_assoc, add_comm] using hsol
    have hGen_comp :
        (gen Y : HilbertBlockL2 U) = toHilbertBlockL2OfComponents hf hg := by
      have hblock_to_hilbert :
          blockL2ToHilbertBlockL2 (U := U) (Y : BlockL2 U) =
            toHilbertBlockL2OfComponents hf hg := by
        rw [← hY]
        simpa [toBlockL2OfComponents, toHilbertBlockL2OfComponents] using!
          (blockL2ToHilbertBlockL2_toBlockL2
            (U := U)
            (F := blockField f g)
            (memBlockL2_blockField hf hg))
      dsimp [gen, canonicalMuCorrectionGeneratorEmbedding,
        PotentialSolenoidalL2Data.submoduleClosureToMuCorrectionSpace]
      exact hblock_to_hilbert
    have hAdmCorr :
        (hAdm.toCorrectionFieldDataOfAdmissible).toHilbertBlockL2 =
          toHilbertBlockL2OfComponents hf hg := by
      change toHilbertBlockL2OfComponents
          hAdm.potentialCorrection_memL2 hAdm.fluxCorrection_memL2 =
        toHilbertBlockL2OfComponents hf hg
      apply MeasureTheory.Lp.ext
      filter_upwards
          [coeFn_toHilbertBlockL2OfComponents (U := U)
            (f := fun x => X.potential x - P0.1)
            (g := fun x => X.flux x - P0.2)
            hAdm.potentialCorrection_memL2 hAdm.fluxCorrection_memL2,
           coeFn_toHilbertBlockL2OfComponents (U := U) (f := f) (g := g) hf hg]
        with x hleft hright
      rw [hleft, hright]
      apply HilbertBlockVec.ext
      · ext i
        simp [X, hilbertBlockField]
      · ext i
        simp [X, hilbertBlockField]
    have hsplit :
        toHilbertBlockL2OfBlockField (U := U) hAdm.memBlockL2_eval =
          H.constantField P0 + (gen Y : HilbertBlockL2 U) := by
      calc
        toHilbertBlockL2OfBlockField (U := U) hAdm.memBlockL2_eval
            = blockVecToHilbertBlockL2Const (U := U) P0 +
                (hAdm.toCorrectionFieldDataOfAdmissible).toHilbertBlockL2 :=
              hAdm.toHilbertBlockL2OfBlockField_eq_blockVecToHilbertBlockL2Const_add
        _ = H.constantField P0 + (gen Y : HilbertBlockL2 U) := by
              rw [hAdmCorr, ← hGen_comp]
              simp [H, system, AEEMuOperatorSystemData.toMuHilbertRealization,
                MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator]
    have hEnergy :
        quadraticEnergy H.energyBilin (H.constantField P0 + (gen Y : HilbertBlockL2 U)) =
          blockEnergyAverage U a.1 X := by
      rw [← hsplit]
      simpa [H, system, AEEMuOperatorSystemData.toMuHilbertRealization,
        MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator] using
        system.toMuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_of_blockState
          (X := X) hAdm.memBlockL2_eval
    refine ⟨X, hAdm, ?_⟩
    simpa [blockEnergyAverage] using hEnergy
  have hs_nonempty : s.Nonempty := by
    refine ⟨quadraticEnergy H.energyBilin (H.constantField P0 + (gen 0 : HilbertBlockL2 U)), ?_⟩
    exact ⟨0, rfl⟩
  have hMu_le_sInf : Mu U P0 a.1 ≤ sInf s := by
    apply le_csInf hs_nonempty
    intro m hm
    exact csInf_le hBddBelow (hs_subset_mu hm)
  have hMu_le_candidate : Mu U P0 a.1 ≤ H.muCandidate P0 := by
    calc
      Mu U P0 a.1 ≤ sInf s := hMu_le_sInf
      _ = H.muCandidate P0 := hCandidate_sInf.symm
  have hEq : Mu U P0 a.1 = H.muCandidate P0 :=
    le_antisymm hMu_le_candidate hCandidate_le_Mu
  simpa [H, system, U] using hEq

/-- On a quantitative AEE cube slice, the variational `Mu` is the infimum of
the fixed-competitor block energies along any dense sequence in the canonical
predicate-generated correction submodule.  This is the canonical Ch4 bridge
for Ch5 measurability: the competitors are pointwise block states and no
external recovery witness is part of the interface. -/
theorem mu_eq_iInf_blockEnergyAverage_canonicalAEEMuGenerator_denseSeq
    {d : ℕ} (Q : TriadicCube d) (k : ℕ)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a})
    (P0 : BlockVec d)
    (ξ : ℕ → canonicalMuBlockCorrectionGeneratorSubmodule (cubeSet Q))
    (hξ : DenseRange ξ) :
    Mu (cubeSet Q) P0 a.1 =
      ⨅ n : ℕ,
        blockEnergyAverage (cubeSet Q) a.1
          (canonicalMuGeneratorAffineField (U := cubeSet Q) P0 (ξ n)) := by
  let U : Set (Vec d) := cubeSet Q
  let system : AEEMuOperatorSystemData U a.1 := canonicalAEEMuOperatorSystemData Q k a
  let H : MuHilbertRealization U a.1 := system.toMuHilbertRealization
  let gen : ℕ → H.correctionSpace.correctionSpace.toSubmodule := fun n =>
    canonicalMuCorrectionGeneratorEmbedding U (ξ n)
  have hgen_dense : DenseRange gen := by
    have hEmbDense :
        DenseRange (canonicalMuCorrectionGeneratorEmbedding U) :=
      denseRange_canonicalMuCorrectionGeneratorEmbedding U
    have hEmbCont :
        Continuous (canonicalMuCorrectionGeneratorEmbedding U) :=
      continuous_canonicalMuCorrectionGeneratorEmbedding U
    have hcomp : DenseRange ((canonicalMuCorrectionGeneratorEmbedding U) ∘ ξ) :=
      DenseRange.comp hEmbDense hξ hEmbCont
    dsimp [gen, H, system, U]
    simpa [canonicalAEEMuOperatorSystemData, canonicalAEEMuCorrectionSpaceData,
      canonicalAEEPotentialSolenoidalL2Data, MuCorrectionSpaceData.ofSubmoduleClosures,
      AEEMuOperatorSystemData.toMuHilbertRealization,
      MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator,
      Function.comp_def] using! hcomp
  have hCandidate :
      H.muCandidate P0 =
        sInf (Set.range fun n : ℕ =>
          quadraticEnergy H.energyBilin (H.constantField P0 + (gen n : HilbertBlockL2 U))) := by
    simpa using H.muCandidate_eq_sInf_quadraticEnergy_denseRange P0 gen hgen_dense
  have hEnergy :
      ∀ n : ℕ,
        quadraticEnergy H.energyBilin (H.constantField P0 + (gen n : HilbertBlockL2 U)) =
          blockEnergyAverage U a.1
            (canonicalMuGeneratorAffineField (U := U) P0 (ξ n)) := by
    intro n
    have hsplit :
        toHilbertBlockL2OfBlockField (U := U)
            (canonicalMuGeneratorAffineField_memBlockL2 (U := U) P0 (ξ n)) =
          H.constantField P0 + (gen n : HilbertBlockL2 U) := by
      simpa [gen, H, system, AEEMuOperatorSystemData.toMuHilbertRealization,
        MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator] using
        canonicalMuGeneratorAffineField_hilbert_eq_const_add (U := U) P0 (ξ n)
    calc
      quadraticEnergy H.energyBilin (H.constantField P0 + (gen n : HilbertBlockL2 U))
          = quadraticEnergy H.energyBilin
              (toHilbertBlockL2OfBlockField (U := U)
                (canonicalMuGeneratorAffineField_memBlockL2 (U := U) P0 (ξ n))) := by
            rw [hsplit]
      _ = blockEnergyAverage U a.1
            (canonicalMuGeneratorAffineField (U := U) P0 (ξ n)) := by
            simpa [H, system, AEEMuOperatorSystemData.toMuHilbertRealization,
              MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator] using
              system.toMuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_of_blockState
                (X := canonicalMuGeneratorAffineField (U := U) P0 (ξ n))
                (canonicalMuGeneratorAffineField_memBlockL2 (U := U) P0 (ξ n))
  calc
    Mu (cubeSet Q) P0 a.1 = H.muCandidate P0 := by
      simpa [H, system, U] using mu_eq_canonicalAEEMuCandidate Q k a P0
    _ = ⨅ n : ℕ,
          quadraticEnergy H.energyBilin (H.constantField P0 + (gen n : HilbertBlockL2 U)) := by
      rw [hCandidate, sInf_range]
    _ = ⨅ n : ℕ,
          blockEnergyAverage U a.1
            (canonicalMuGeneratorAffineField (U := U) P0 (ξ n)) :=
      iInf_congr hEnergy

/-- The Hilbert quadratic energy of a canonical dense-generator affine
competitor is exactly its doubled block-energy average.  This is the pointwise
energy identity used by countable near-minimizer selections. -/
theorem canonicalAEEMuOperatorSystemData_quadraticEnergy_generatorAffine_eq_blockEnergyAverage
    {d : ℕ} (Q : TriadicCube d) (k : ℕ)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a})
    (P0 : BlockVec d)
    (Y : canonicalMuBlockCorrectionGeneratorSubmodule (cubeSet Q)) :
    let H := ((canonicalAEEMuOperatorSystemData Q k a).toMuHilbertRealization)
    quadraticEnergy H.energyBilin
        (H.constantField P0 +
          (canonicalMuCorrectionGeneratorEmbedding (cubeSet Q) Y :
            HilbertBlockL2 (cubeSet Q))) =
      blockEnergyAverage (cubeSet Q) a.1
        (canonicalMuGeneratorAffineField (U := cubeSet Q) P0 Y) := by
  let U : Set (Vec d) := cubeSet Q
  let system : AEEMuOperatorSystemData U a.1 := canonicalAEEMuOperatorSystemData Q k a
  let H : MuHilbertRealization U a.1 := system.toMuHilbertRealization
  have hsplit :
      toHilbertBlockL2OfBlockField (U := U)
          (canonicalMuGeneratorAffineField_memBlockL2 (U := U) P0 Y) =
        H.constantField P0 +
          (canonicalMuCorrectionGeneratorEmbedding U Y : HilbertBlockL2 U) := by
    simpa [H, system, AEEMuOperatorSystemData.toMuHilbertRealization,
      MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator] using
      canonicalMuGeneratorAffineField_hilbert_eq_const_add (U := U) P0 Y
  calc
    quadraticEnergy H.energyBilin
        (H.constantField P0 +
          (canonicalMuCorrectionGeneratorEmbedding U Y : HilbertBlockL2 U))
        = quadraticEnergy H.energyBilin
            (toHilbertBlockL2OfBlockField (U := U)
              (canonicalMuGeneratorAffineField_memBlockL2 (U := U) P0 Y)) := by
          rw [hsplit]
    _ = blockEnergyAverage U a.1
          (canonicalMuGeneratorAffineField (U := U) P0 Y) := by
          simpa [H, system, AEEMuOperatorSystemData.toMuHilbertRealization,
            MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator] using
            system.toMuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_of_blockState
              (X := canonicalMuGeneratorAffineField (U := U) P0 Y)
              (canonicalMuGeneratorAffineField_memBlockL2 (U := U) P0 Y)

/-- Canonical dense-sequence form of
`mu_eq_iInf_blockEnergyAverage_canonicalAEEMuGenerator_denseSeq`, using
`TopologicalSpace.denseSeq` on the canonical generator submodule. -/
theorem mu_eq_iInf_blockEnergyAverage_canonicalAEEMuGenerator
    {d : ℕ} (Q : TriadicCube d) (k : ℕ)
    (a : {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a})
    (P0 : BlockVec d) :
    Mu (cubeSet Q) P0 a.1 =
      ⨅ n : ℕ,
        blockEnergyAverage (cubeSet Q) a.1
          (canonicalMuGeneratorAffineField (U := cubeSet Q) P0
            (TopologicalSpace.denseSeq
              (canonicalMuBlockCorrectionGeneratorSubmodule (cubeSet Q)) n)) := by
  exact mu_eq_iInf_blockEnergyAverage_canonicalAEEMuGenerator_denseSeq Q k a P0
    (TopologicalSpace.denseSeq (canonicalMuBlockCorrectionGeneratorSubmodule (cubeSet Q)))
    (TopologicalSpace.denseRange_denseSeq
      (canonicalMuBlockCorrectionGeneratorSubmodule (cubeSet Q)))

end CanonicalCubeSet

end

end Homogenization
