/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Measurability
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.CoarseObservables
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.SolutionIntegrability
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Internal.AEESliceAssembly.MuFamily

import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.CanonicalSolutions.Definitions

/-! # Average Identities -/

namespace Homogenization
namespace Book
namespace Ch04

open scoped ENNReal
open MeasureTheory


private theorem volumeAverage_cubeSet_indicator_of_subset
    {d : ℕ} {Q R : TriadicCube d} (hRQ : cubeSet R ⊆ cubeSet Q)
    (f : Vec d → ℝ) :
    volumeAverage (cubeSet Q) ((cubeSet R).indicator f) =
      (cubeVolume Q)⁻¹ * ∫ x in cubeSet R, f x ∂volume := by
  unfold volumeAverage
  rw [volume_cubeSet_toReal]
  congr 1
  calc
    ∫ x in cubeSet Q, (cubeSet R).indicator f x ∂volume =
        ∫ x, (cubeSet R).indicator f x ∂(volume.restrict (cubeSet Q)) := rfl
    _ = ∫ x in cubeSet R, f x ∂(volume.restrict (cubeSet Q)) := by
          rw [MeasureTheory.integral_indicator (measurableSet_cubeSet R)]
    _ = ∫ x in cubeSet R, f x ∂volume := by
          rw [MeasureTheory.Measure.restrict_restrict_of_subset hRQ]

private theorem blockPairingAverage_lowerIndicator_eq
    {d : ℕ} {Q R : TriadicCube d} (hRQ : cubeSet R ⊆ cubeSet Q)
    (a : CoeffField d) (X : BlockState d) (i : Fin d) :
    blockPairingAverage (cubeSet Q) a X
        (canonicalLowerImageIndicatorTestStateCubeSet R i) =
      (cubeVolume Q)⁻¹ *
        ∫ x in cubeSet R,
          (blockMatVecMul (blockCoeffField a x) (X.eval x)).2 i ∂volume := by
  have hIntegrand :
      blockPairingIntegrand a X (canonicalLowerImageIndicatorTestStateCubeSet R i) =
        (cubeSet R).indicator
          (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2 i) := by
    funext x
    by_cases hx : x ∈ cubeSet R
    · have hcomm :
          blockVecDot (X.eval x)
              (blockMatVecMul (blockCoeffField a x)
                ((canonicalLowerImageIndicatorTestStateCubeSet R i).eval x)) =
            blockVecDot ((canonicalLowerImageIndicatorTestStateCubeSet R i).eval x)
              (blockMatVecMul (blockCoeffField a x) (X.eval x)) := by
          simpa [blockCoeffField] using
            (blockVecDot_blockMatVecMul_blockMatrixOfCoeff_comm (a x)
              (X.eval x) ((canonicalLowerImageIndicatorTestStateCubeSet R i).eval x))
      calc
        blockPairingIntegrand a X (canonicalLowerImageIndicatorTestStateCubeSet R i) x =
            blockVecDot (X.eval x)
              (blockMatVecMul (blockCoeffField a x)
                ((canonicalLowerImageIndicatorTestStateCubeSet R i).eval x)) := rfl
        _ = blockVecDot ((canonicalLowerImageIndicatorTestStateCubeSet R i).eval x)
              (blockMatVecMul (blockCoeffField a x) (X.eval x)) := hcomm
        _ = (blockMatVecMul (blockCoeffField a x) (X.eval x)).2 i := by
              simp [canonicalLowerImageIndicatorTestStateCubeSet, BlockState.eval, hx,
                blockVecDot, vecDot_single_left, vecDot_zero_left]
        _ = (cubeSet R).indicator
              (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2 i) x := by
              simp [hx]
    · calc
        blockPairingIntegrand a X (canonicalLowerImageIndicatorTestStateCubeSet R i) x = 0 := by
          simp [blockPairingIntegrand, canonicalLowerImageIndicatorTestStateCubeSet,
            BlockState.eval, hx, blockMatVecMul, blockVecDot, vecDot, matVecMul_zero]
        _ = (cubeSet R).indicator
              (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2 i) x := by
              simp [hx]
  calc
    blockPairingAverage (cubeSet Q) a X
        (canonicalLowerImageIndicatorTestStateCubeSet R i) =
      volumeAverage (cubeSet Q)
        ((cubeSet R).indicator
          (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2 i)) := by
        simp [blockPairingAverage, hIntegrand]
    _ = (cubeVolume Q)⁻¹ *
        ∫ x in cubeSet R,
          (blockMatVecMul (blockCoeffField a x) (X.eval x)).2 i ∂volume :=
        volumeAverage_cubeSet_indicator_of_subset hRQ _

private theorem blockPairingAverage_upperIndicator_eq
    {d : ℕ} {Q R : TriadicCube d} (hRQ : cubeSet R ⊆ cubeSet Q)
    (a : CoeffField d) (X : BlockState d) (i : Fin d) :
    blockPairingAverage (cubeSet Q) a X
        (canonicalUpperImageIndicatorTestStateCubeSet R i) =
      (cubeVolume Q)⁻¹ *
        ∫ x in cubeSet R,
          (blockMatVecMul (blockCoeffField a x) (X.eval x)).1 i ∂volume := by
  have hIntegrand :
      blockPairingIntegrand a X (canonicalUpperImageIndicatorTestStateCubeSet R i) =
        (cubeSet R).indicator
          (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).1 i) := by
    funext x
    by_cases hx : x ∈ cubeSet R
    · have hcomm :
          blockVecDot (X.eval x)
              (blockMatVecMul (blockCoeffField a x)
                ((canonicalUpperImageIndicatorTestStateCubeSet R i).eval x)) =
            blockVecDot ((canonicalUpperImageIndicatorTestStateCubeSet R i).eval x)
              (blockMatVecMul (blockCoeffField a x) (X.eval x)) := by
          simpa [blockCoeffField] using
            (blockVecDot_blockMatVecMul_blockMatrixOfCoeff_comm (a x)
              (X.eval x) ((canonicalUpperImageIndicatorTestStateCubeSet R i).eval x))
      calc
        blockPairingIntegrand a X (canonicalUpperImageIndicatorTestStateCubeSet R i) x =
            blockVecDot (X.eval x)
              (blockMatVecMul (blockCoeffField a x)
                ((canonicalUpperImageIndicatorTestStateCubeSet R i).eval x)) := rfl
        _ = blockVecDot ((canonicalUpperImageIndicatorTestStateCubeSet R i).eval x)
              (blockMatVecMul (blockCoeffField a x) (X.eval x)) := hcomm
        _ = (blockMatVecMul (blockCoeffField a x) (X.eval x)).1 i := by
              simp [canonicalUpperImageIndicatorTestStateCubeSet, BlockState.eval, hx,
                blockVecDot, vecDot_single_left, vecDot_zero_left]
        _ = (cubeSet R).indicator
              (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).1 i) x := by
              simp [hx]
    · calc
        blockPairingIntegrand a X (canonicalUpperImageIndicatorTestStateCubeSet R i) x = 0 := by
          simp [blockPairingIntegrand, canonicalUpperImageIndicatorTestStateCubeSet,
            BlockState.eval, hx, blockMatVecMul, blockVecDot, vecDot, matVecMul_zero]
        _ = (cubeSet R).indicator
              (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).1 i) x := by
              simp [hx]
  calc
    blockPairingAverage (cubeSet Q) a X
        (canonicalUpperImageIndicatorTestStateCubeSet R i) =
      volumeAverage (cubeSet Q)
        ((cubeSet R).indicator
          (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).1 i)) := by
        simp [blockPairingAverage, hIntegrand]
    _ = (cubeVolume Q)⁻¹ *
        ∫ x in cubeSet R,
          (blockMatVecMul (blockCoeffField a x) (X.eval x)).1 i ∂volume :=
        volumeAverage_cubeSet_indicator_of_subset hRQ _

private theorem canonicalDoubledMuResponsePotentialFieldAverageCubeSet_eq_integral_of_ae_eq
    {d : ℕ} {Q R : TriadicCube d} (hRQ : cubeSet R ⊆ cubeSet Q)
    {a : CoeffField d} {p q : Vec d} {F : Vec d → Vec d}
    (hF :
      canonicalDoubledMuResponsePotentialFieldCubeSet Q p q a
        =ᵐ[volumeMeasureOn (cubeSet Q)]
      fun x => HilbertVec.ofVec (F x))
    (i : Fin d) :
    canonicalDoubledMuResponsePotentialFieldAverageCubeSet Q R p q a i =
      (cubeVolume R)⁻¹ * ∫ x in cubeSet R, F x i ∂volume := by
  have hCoord :
      (fun x => canonicalDoubledMuResponsePotentialFieldCubeSet Q p q a x i)
        =ᵐ[(volumeMeasureOn (cubeSet Q)).restrict (cubeSet R)]
      fun x => F x i := by
    exact
      (hF.filter_mono
        (MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_le_self))).mono
        (fun x hx => by
          simpa using congrArg (fun v : HilbertVec d => v i) hx)
  calc
    canonicalDoubledMuResponsePotentialFieldAverageCubeSet Q R p q a i =
        (cubeVolume R)⁻¹ *
          ∫ x in cubeSet R,
            canonicalDoubledMuResponsePotentialFieldCubeSet Q p q a x i
              ∂volumeMeasureOn (cubeSet Q) := by
          rw [canonicalDoubledMuResponsePotentialFieldAverageCubeSet,
            hilbertVectorL2CoordSetIntegralCLM_apply]
    _ = (cubeVolume R)⁻¹ *
          ∫ x in cubeSet R, F x i ∂volumeMeasureOn (cubeSet Q) := by
          congr 1
          exact MeasureTheory.integral_congr_ae hCoord
    _ = (cubeVolume R)⁻¹ * ∫ x in cubeSet R, F x i ∂volume := by
          congr 1
          rw [MeasureTheory.Measure.restrict_restrict_of_subset hRQ]

private theorem canonicalDoubledMuResponseFluxFieldAverageCubeSet_eq_integral_of_ae_eq
    {d : ℕ} {Q R : TriadicCube d} (hRQ : cubeSet R ⊆ cubeSet Q)
    {a : CoeffField d} {p q : Vec d} {F : Vec d → Vec d}
    (hF :
      canonicalDoubledMuResponseFluxFieldCubeSet Q p q a
        =ᵐ[volumeMeasureOn (cubeSet Q)]
      fun x => HilbertVec.ofVec (F x))
    (i : Fin d) :
    canonicalDoubledMuResponseFluxFieldAverageCubeSet Q R p q a i =
      (cubeVolume R)⁻¹ * ∫ x in cubeSet R, F x i ∂volume := by
  have hCoord :
      (fun x => canonicalDoubledMuResponseFluxFieldCubeSet Q p q a x i)
        =ᵐ[(volumeMeasureOn (cubeSet Q)).restrict (cubeSet R)]
      fun x => F x i := by
    exact
      (hF.filter_mono
        (MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_le_self))).mono
        (fun x hx => by
          simpa using congrArg (fun v : HilbertVec d => v i) hx)
  calc
    canonicalDoubledMuResponseFluxFieldAverageCubeSet Q R p q a i =
        (cubeVolume R)⁻¹ *
          ∫ x in cubeSet R,
            canonicalDoubledMuResponseFluxFieldCubeSet Q p q a x i
              ∂volumeMeasureOn (cubeSet Q) := by
          rw [canonicalDoubledMuResponseFluxFieldAverageCubeSet,
            hilbertVectorL2CoordSetIntegralCLM_apply]
    _ = (cubeVolume R)⁻¹ *
          ∫ x in cubeSet R, F x i ∂volumeMeasureOn (cubeSet Q) := by
          congr 1
          exact MeasureTheory.integral_congr_ae hCoord
    _ = (cubeVolume R)⁻¹ * ∫ x in cubeSet R, F x i ∂volume := by
          congr 1
          rw [MeasureTheory.Measure.restrict_restrict_of_subset hRQ]

private theorem canonicalDoubledMuResponseLowerImageAverageCubeSet_eq_integral_of_energy_eq
    {d : ℕ} {Q R : TriadicCube d} (hRQ : cubeSet R ⊆ cubeSet Q)
    {a : CoeffField d} {p q : Vec d} {X : BlockState d} (i : Fin d)
    (hEnergy :
      canonicalMuHilbertEnergyBilinFixedCubeSet Q (-p, q)
        (canonicalLowerImageIndicatorTestStateCubeSet R i)
        (canonicalLowerImageIndicatorTestStateCubeSet_memBlockL2 Q R i) a =
        blockPairingAverage (cubeSet Q) a X
          (canonicalLowerImageIndicatorTestStateCubeSet R i)) :
    canonicalDoubledMuResponseLowerImageAverageCubeSet Q R p q a i =
      (cubeVolume R)⁻¹ *
        ∫ x in cubeSet R,
          (blockMatVecMul (blockCoeffField a x) (X.eval x)).2 i ∂volume := by
  calc
    canonicalDoubledMuResponseLowerImageAverageCubeSet Q R p q a i =
        cubeVolume Q * (cubeVolume R)⁻¹ *
          canonicalMuHilbertEnergyBilinFixedCubeSet Q (-p, q)
            (canonicalLowerImageIndicatorTestStateCubeSet R i)
            (canonicalLowerImageIndicatorTestStateCubeSet_memBlockL2 Q R i) a := rfl
    _ = cubeVolume Q * (cubeVolume R)⁻¹ *
          blockPairingAverage (cubeSet Q) a X
            (canonicalLowerImageIndicatorTestStateCubeSet R i) := by
          rw [hEnergy]
    _ = cubeVolume Q * (cubeVolume R)⁻¹ *
          ((cubeVolume Q)⁻¹ *
            ∫ x in cubeSet R,
              (blockMatVecMul (blockCoeffField a x) (X.eval x)).2 i ∂volume) := by
          rw [blockPairingAverage_lowerIndicator_eq hRQ a X i]
    _ = (cubeVolume R)⁻¹ *
          ∫ x in cubeSet R,
            (blockMatVecMul (blockCoeffField a x) (X.eval x)).2 i ∂volume := by
          field_simp [ne_of_gt (cubeVolume_pos Q)]

private theorem canonicalDoubledMuResponseUpperImageAverageCubeSet_eq_integral_of_energy_eq
    {d : ℕ} {Q R : TriadicCube d} (hRQ : cubeSet R ⊆ cubeSet Q)
    {a : CoeffField d} {p q : Vec d} {X : BlockState d} (i : Fin d)
    (hEnergy :
      canonicalMuHilbertEnergyBilinFixedCubeSet Q (-p, q)
        (canonicalUpperImageIndicatorTestStateCubeSet R i)
        (canonicalUpperImageIndicatorTestStateCubeSet_memBlockL2 Q R i) a =
        blockPairingAverage (cubeSet Q) a X
          (canonicalUpperImageIndicatorTestStateCubeSet R i)) :
    canonicalDoubledMuResponseUpperImageAverageCubeSet Q R p q a i =
      (cubeVolume R)⁻¹ *
        ∫ x in cubeSet R,
          (blockMatVecMul (blockCoeffField a x) (X.eval x)).1 i ∂volume := by
  calc
    canonicalDoubledMuResponseUpperImageAverageCubeSet Q R p q a i =
        cubeVolume Q * (cubeVolume R)⁻¹ *
          canonicalMuHilbertEnergyBilinFixedCubeSet Q (-p, q)
            (canonicalUpperImageIndicatorTestStateCubeSet R i)
            (canonicalUpperImageIndicatorTestStateCubeSet_memBlockL2 Q R i) a := rfl
    _ = cubeVolume Q * (cubeVolume R)⁻¹ *
          blockPairingAverage (cubeSet Q) a X
            (canonicalUpperImageIndicatorTestStateCubeSet R i) := by
          rw [hEnergy]
    _ = cubeVolume Q * (cubeVolume R)⁻¹ *
          ((cubeVolume Q)⁻¹ *
            ∫ x in cubeSet R,
              (blockMatVecMul (blockCoeffField a x) (X.eval x)).1 i ∂volume) := by
          rw [blockPairingAverage_upperIndicator_eq hRQ a X i]
    _ = (cubeVolume R)⁻¹ *
          ∫ x in cubeSet R,
            (blockMatVecMul (blockCoeffField a x) (X.eval x)).1 i ∂volume := by
          field_simp [ne_of_gt (cubeVolume_pos Q)]

/-- Correctness of the Ch4 scalar-response gradient average: on the a.e.
elliptic support it is the descendant-cube average of the raw Chapter 2
canonical scalar-response maximizer gradient. -/
theorem canonicalScalarResponseGradientAverageCubeSet_eq_cubeAverageVec_canonicalMaximizer
    {d : ℕ} [NeZero d] (aR : RegCoeffField d)
    (ha : AELocallyUniformlyEllipticField aR)
    {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (p q : Vec d) :
    canonicalScalarResponseGradientAverageCubeSet Q R p q aR.toFun =
      cubeAverageVec R
        (fun x =>
          (Ch02.canonicalMaximizer
            (Ch02.responseExistenceTheory (Ch02.cubeDomain Q)
              ((triadicCoeffFamilyOfAELocallyUniformlyEllipticField aR ha).coeffOn Q))
            p q).toSolution.toH1.grad x) := by
  classical
  set a : CoeffField d := aR.toFun with hadef
  let F := triadicCoeffFamilyOfAELocallyUniformlyEllipticField aR ha
  let aQ : Ch02.CoeffOn (Ch02.cubeDomain Q) := F.coeffOn Q
  have haQ : aQ.toCoeffField = a := by
    simp [aQ, F, hadef]
  have hSlice : ∃ k : ℕ, AEEQuantitativeEllipticSlice (cubeSet Q) k a :=
    ha.exists_aeeQuantitativeEllipticSlice_cubeSet Q
  let k : ℕ := Nat.find hSlice
  have hk : AEEQuantitativeEllipticSlice (cubeSet Q) k a := by
    simpa [k] using Nat.find_spec hSlice
  let aSlice : {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a} :=
    ⟨a, hk⟩
  obtain ⟨X, hX⟩ :=
    (Ch02.doubledMuTheory (Ch02.cubeDomain Q) aQ).minimizer_exists (-p, q)
  let Xold : BlockState d := { potential := X.potential, flux := X.flux }
  obtain ⟨hAdm, hHilbert⟩ :=
    exists_isBlockMuAdmissible_cubeSet_and_hilbert_eq_canonicalAEEMuHilbertMinimizer_of_isDoubledMuMinimizer
      Q k aSlice (-p, q) aQ haQ hX
  have hRQ : cubeSet R ⊆ cubeSet Q :=
    cubeSet_subset_of_mem_descendantsAtDepth hR
  have hMinEq :
      canonicalMuHilbertMinimizerCubeSet Q (-p, q) a =
        toHilbertBlockL2OfBlockField (U := cubeSet Q) hAdm.memBlockL2_eval := by
    calc
      canonicalMuHilbertMinimizerCubeSet Q (-p, q) a =
          ((canonicalAEEMuOperatorSystemData Q k aSlice).toMuHilbertRealization).minimizerMap
            (-p, q) := by
            simp only [canonicalMuHilbertMinimizerCubeSet, dif_pos hSlice, k, aSlice]
      _ = toHilbertBlockL2OfBlockField (U := cubeSet Q) hAdm.memBlockL2_eval :=
            hHilbert.symm
  have hPotentialAE :
      canonicalDoubledMuResponsePotentialFieldCubeSet Q p q a
        =ᵐ[volumeMeasureOn (cubeSet Q)]
      fun x => HilbertVec.ofVec (Xold.potential x) := by
    have hProj :
        canonicalDoubledMuResponsePotentialFieldCubeSet Q p q a
          =ᵐ[volumeMeasureOn (cubeSet Q)]
        fun x =>
          (toHilbertBlockL2OfBlockField (U := cubeSet Q) hAdm.memBlockL2_eval x).potential := by
      simpa [canonicalDoubledMuResponsePotentialFieldCubeSet,
        canonicalMuHilbertPotentialCubeSet, hMinEq] using
        coeFn_hilbertBlockL2PotentialCLM
          (U := cubeSet Q)
          (F := toHilbertBlockL2OfBlockField (U := cubeSet Q) hAdm.memBlockL2_eval)
    filter_upwards
        [hProj,
          coeFn_toHilbertBlockL2OfBlockField
            (U := cubeSet Q) (F := Xold.eval) hAdm.memBlockL2_eval]
      with x hproj hblock
    rw [hproj, hblock]
    simp [Xold, hilbertifyBlockField, BlockState.eval]
  have hPotMemQ : MemVectorL2 (cubeSet Q) Xold.potential := by
    simpa [Xold, BlockState.eval] using
      memVectorL2_fst_of_memBlockL2 (U := cubeSet Q) hAdm.memBlockL2_eval
  have hPotMemR : MemVectorL2 (cubeSet R) Xold.potential :=
    hPotMemQ.mono_measure
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hRQ)
  have hGradMemR :
      MemVectorL2 (cubeSet R)
        (fun x =>
          (Ch02.canonicalMaximizer
            (Ch02.responseExistenceTheory (Ch02.cubeDomain Q) aQ)
            p q).toSolution.toH1.grad x) := by
    have hGradOpen :
        MemVectorL2 (Ch02.cubeDomain Q : Set (Vec d))
          (fun x =>
            (Ch02.canonicalMaximizer
              (Ch02.responseExistenceTheory (Ch02.cubeDomain Q) aQ)
              p q).toSolution.toH1.grad x) :=
      (Ch02.canonicalMaximizer
        (Ch02.responseExistenceTheory (Ch02.cubeDomain Q) aQ)
        p q).toSolution.toH1.grad_memVectorL2
    have hGradOpenR :
        MemVectorL2 (openCubeSet R)
          (fun x =>
            (Ch02.canonicalMaximizer
              (Ch02.responseExistenceTheory (Ch02.cubeDomain Q) aQ)
              p q).toSolution.toH1.grad x) := by
      exact hGradOpen.mono_measure
        (by
          simpa [Ch02.cubeDomain_coe, volumeMeasureOn] using
            MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume
              (openCubeSet_subset_of_mem_descendantsAtDepth hR))
    simpa [MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet R] using hGradOpenR
  have hExtractOpen :
      (fun x =>
          Xold.potential x +
            (blockMatVecMul (blockCoeffField a x) (Xold.eval x)).2)
        =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x =>
        (Ch02.canonicalMaximizer
          (Ch02.responseExistenceTheory (Ch02.cubeDomain Q) aQ)
          p q).toSolution.toH1.grad x := by
    simpa only [Xold, haQ, Ch02.cubeDomain_coe] using!
      Ch02.doubledMuMinimizer_neg_left_extracts_canonicalMaximizerGradient
        (Ch02.cubeDomain Q) aQ p q hX
  have hExtractR :
      (fun x =>
          Xold.potential x +
            (blockMatVecMul (blockCoeffField a x) (Xold.eval x)).2)
        =ᵐ[volumeMeasureOn (cubeSet R)]
      fun x =>
        (Ch02.canonicalMaximizer
          (Ch02.responseExistenceTheory (Ch02.cubeDomain Q) aQ)
          p q).toSolution.toH1.grad x :=
    ae_eq_cubeSet_of_mem_descendantsAtDepth_of_ae_eq_openCubeSet hR hExtractOpen
  have hLowerMemR :
      MemVectorL2 (cubeSet R)
        (fun x => (blockMatVecMul (blockCoeffField a x) (Xold.eval x)).2) := by
    have hDiff :
        MemVectorL2 (cubeSet R)
          (fun x =>
            (Ch02.canonicalMaximizer
              (Ch02.responseExistenceTheory (Ch02.cubeDomain Q) aQ)
              p q).toSolution.toH1.grad x - Xold.potential x) :=
      hGradMemR.sub hPotMemR
    refine MeasureTheory.MemLp.ae_eq ?_ hDiff
    filter_upwards [hExtractR] with x hx
    ext i
    have hxi := congrArg (fun v : Vec d => v i) hx
    simp [Pi.add_apply, Pi.sub_apply] at hxi ⊢
    linarith
  have hEnergyLower :
      ∀ i : Fin d,
        canonicalMuHilbertEnergyBilinFixedCubeSet Q (-p, q)
          (canonicalLowerImageIndicatorTestStateCubeSet R i)
          (canonicalLowerImageIndicatorTestStateCubeSet_memBlockL2 Q R i) a =
        blockPairingAverage (cubeSet Q) a Xold
          (canonicalLowerImageIndicatorTestStateCubeSet R i) := by
    intro i
    let Y := canonicalLowerImageIndicatorTestStateCubeSet R i
    let hY := canonicalLowerImageIndicatorTestStateCubeSet_memBlockL2 Q R i
    let system : AEEMuOperatorSystemData (cubeSet Q) a :=
      canonicalAEEMuOperatorSystemData Q k aSlice
    calc
      canonicalMuHilbertEnergyBilinFixedCubeSet Q (-p, q) Y hY a =
          system.toMuHilbertRealization.energyBilin
            (toHilbertBlockL2OfBlockField (U := cubeSet Q) hY)
            (system.toMuHilbertRealization.minimizerMap (-p, q)) := by
            simp [canonicalMuHilbertEnergyBilinFixedCubeSet, hSlice, k, aSlice, system]
      _ = system.toMuHilbertRealization.energyBilin
            (toHilbertBlockL2OfBlockField (U := cubeSet Q) hY)
            (toHilbertBlockL2OfBlockField (U := cubeSet Q) hAdm.memBlockL2_eval) := by
            rw [← hHilbert]
      _ = blockPairingAverage (cubeSet Q) a Xold Y := by
            simpa [system, AEEMuOperatorSystemData.toMuHilbertRealization,
              MuOperatorRealization.toMuHilbertRealization,
              MuHilbertRealization.ofOperator, Xold, Y, aSlice] using
              system.toMuOperatorRealization.energyBilin_eq_blockPairingAverage_of_blockState
                (X := Xold) (Y := Y)
                hAdm.memBlockL2_eval hY
  ext i
  have hPotAvg :=
    canonicalDoubledMuResponsePotentialFieldAverageCubeSet_eq_integral_of_ae_eq
      hRQ (a := a) (p := p) (q := q) (F := Xold.potential) hPotentialAE i
  have hLowerAvg :=
    canonicalDoubledMuResponseLowerImageAverageCubeSet_eq_integral_of_energy_eq
      hRQ (a := a) (p := p) (q := q) (X := Xold) i (hEnergyLower i)
  have hPotInt :
      MeasureTheory.IntegrableOn (fun x => Xold.potential x i) (cubeSet R) :=
    CorrectionFieldData.integrableOn_coord_of_memVectorL2
      (U := cubeSet R) hPotMemR i
  have hLowerInt :
      MeasureTheory.IntegrableOn
        (fun x => (blockMatVecMul (blockCoeffField a x) (Xold.eval x)).2 i)
        (cubeSet R) :=
    CorrectionFieldData.integrableOn_coord_of_memVectorL2
      (U := cubeSet R) hLowerMemR i
  calc
    canonicalScalarResponseGradientAverageCubeSet Q R p q a i =
        canonicalDoubledMuResponsePotentialFieldAverageCubeSet Q R p q a i +
          canonicalDoubledMuResponseLowerImageAverageCubeSet Q R p q a i := rfl
    _ = (cubeVolume R)⁻¹ * ∫ x in cubeSet R, Xold.potential x i ∂volume +
          (cubeVolume R)⁻¹ *
            ∫ x in cubeSet R,
              (blockMatVecMul (blockCoeffField a x) (Xold.eval x)).2 i ∂volume := by
          rw [hPotAvg, hLowerAvg]
    _ = (cubeVolume R)⁻¹ *
          ∫ x in cubeSet R,
            (Xold.potential x +
              (blockMatVecMul (blockCoeffField a x) (Xold.eval x)).2) i ∂volume := by
          rw [show
            (∫ x in cubeSet R,
                (Xold.potential x +
                  (blockMatVecMul (blockCoeffField a x) (Xold.eval x)).2) i ∂volume)
              =
            ∫ x in cubeSet R, Xold.potential x i ∂volume +
              ∫ x in cubeSet R,
                (blockMatVecMul (blockCoeffField a x) (Xold.eval x)).2 i ∂volume by
              simpa [Pi.add_apply] using
                MeasureTheory.integral_add hPotInt hLowerInt]
          ring
    _ = (cubeVolume R)⁻¹ *
          ∫ x in cubeSet R,
            (Ch02.canonicalMaximizer
              (Ch02.responseExistenceTheory (Ch02.cubeDomain Q) aQ)
              p q).toSolution.toH1.grad x i ∂volume := by
          congr 1
          exact MeasureTheory.integral_congr_ae
            (hExtractR.mono fun x hx =>
              congrArg (fun v : Vec d => v i) hx)
    _ = cubeAverageVec R
        (fun x =>
          (Ch02.canonicalMaximizer
            (Ch02.responseExistenceTheory (Ch02.cubeDomain Q)
              ((triadicCoeffFamilyOfAELocallyUniformlyEllipticField aR ha).coeffOn Q))
            p q).toSolution.toH1.grad x) i := by
          rfl

/-- Correctness of the Ch4 scalar-response flux average: on the a.e. elliptic
support it is the descendant-cube average of the raw Chapter 2 canonical
scalar-response maximizer flux. -/
theorem canonicalScalarResponseFluxAverageCubeSet_eq_cubeAverageVec_canonicalMaximizerFlux
    {d : ℕ} [NeZero d] (aR : RegCoeffField d)
    (ha : AELocallyUniformlyEllipticField aR)
    {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (p q : Vec d) :
    canonicalScalarResponseFluxAverageCubeSet Q R p q aR.toFun =
      cubeAverageVec R
        (fun x =>
          matVecMul
            (((triadicCoeffFamilyOfAELocallyUniformlyEllipticField aR ha).coeffOn Q).toCoeffField x)
            ((Ch02.canonicalMaximizer
              (Ch02.responseExistenceTheory (Ch02.cubeDomain Q)
                ((triadicCoeffFamilyOfAELocallyUniformlyEllipticField aR ha).coeffOn Q))
              p q).toSolution.toH1.grad x)) := by
  classical
  set a : CoeffField d := aR.toFun with hadef
  let F := triadicCoeffFamilyOfAELocallyUniformlyEllipticField aR ha
  let aQ : Ch02.CoeffOn (Ch02.cubeDomain Q) := F.coeffOn Q
  have haQ : aQ.toCoeffField = a := by
    simp [aQ, F, hadef]
  have hSlice : ∃ k : ℕ, AEEQuantitativeEllipticSlice (cubeSet Q) k a :=
    ha.exists_aeeQuantitativeEllipticSlice_cubeSet Q
  let k : ℕ := Nat.find hSlice
  have hk : AEEQuantitativeEllipticSlice (cubeSet Q) k a := by
    simpa [k] using Nat.find_spec hSlice
  let aSlice : {a : CoeffField d // AEEQuantitativeEllipticSlice (cubeSet Q) k a} :=
    ⟨a, hk⟩
  obtain ⟨X, hX⟩ :=
    (Ch02.doubledMuTheory (Ch02.cubeDomain Q) aQ).minimizer_exists (-p, q)
  let Xold : BlockState d := { potential := X.potential, flux := X.flux }
  obtain ⟨hAdm, hHilbert⟩ :=
    exists_isBlockMuAdmissible_cubeSet_and_hilbert_eq_canonicalAEEMuHilbertMinimizer_of_isDoubledMuMinimizer
      Q k aSlice (-p, q) aQ haQ hX
  have hRQ : cubeSet R ⊆ cubeSet Q :=
    cubeSet_subset_of_mem_descendantsAtDepth hR
  have hMinEq :
      canonicalMuHilbertMinimizerCubeSet Q (-p, q) a =
        toHilbertBlockL2OfBlockField (U := cubeSet Q) hAdm.memBlockL2_eval := by
    calc
      canonicalMuHilbertMinimizerCubeSet Q (-p, q) a =
          ((canonicalAEEMuOperatorSystemData Q k aSlice).toMuHilbertRealization).minimizerMap
            (-p, q) := by
            simp only [canonicalMuHilbertMinimizerCubeSet, dif_pos hSlice, k, aSlice]
      _ = toHilbertBlockL2OfBlockField (U := cubeSet Q) hAdm.memBlockL2_eval :=
            hHilbert.symm
  have hFluxAE :
      canonicalDoubledMuResponseFluxFieldCubeSet Q p q a
        =ᵐ[volumeMeasureOn (cubeSet Q)]
      fun x => HilbertVec.ofVec (Xold.flux x) := by
    have hProj :
        canonicalDoubledMuResponseFluxFieldCubeSet Q p q a
          =ᵐ[volumeMeasureOn (cubeSet Q)]
        fun x =>
          (toHilbertBlockL2OfBlockField (U := cubeSet Q) hAdm.memBlockL2_eval x).flux := by
      simpa [canonicalDoubledMuResponseFluxFieldCubeSet,
        canonicalMuHilbertFluxCubeSet, hMinEq] using
        coeFn_hilbertBlockL2FluxCLM
          (U := cubeSet Q)
          (F := toHilbertBlockL2OfBlockField (U := cubeSet Q) hAdm.memBlockL2_eval)
    filter_upwards
        [hProj,
          coeFn_toHilbertBlockL2OfBlockField
            (U := cubeSet Q) (F := Xold.eval) hAdm.memBlockL2_eval]
      with x hproj hblock
    rw [hproj, hblock]
    simp [Xold, hilbertifyBlockField, BlockState.eval]
  have hFluxMemQ : MemVectorL2 (cubeSet Q) Xold.flux := by
    simpa [Xold, BlockState.eval] using
      memVectorL2_snd_of_memBlockL2 (U := cubeSet Q) hAdm.memBlockL2_eval
  have hFluxMemR : MemVectorL2 (cubeSet R) Xold.flux :=
    hFluxMemQ.mono_measure
      (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hRQ)
  have hCanonicalFluxMemR :
      MemVectorL2 (cubeSet R)
        (fun x =>
          matVecMul (aQ.toCoeffField x)
            ((Ch02.canonicalMaximizer
              (Ch02.responseExistenceTheory (Ch02.cubeDomain Q) aQ)
              p q).toSolution.toH1.grad x)) := by
    have hFluxOpen :
        MemVectorL2 (Ch02.cubeDomain Q : Set (Vec d))
          (fun x =>
            matVecMul (aQ.toCoeffField x)
              ((Ch02.canonicalMaximizer
                (Ch02.responseExistenceTheory (Ch02.cubeDomain Q) aQ)
                p q).toSolution.toH1.grad x)) :=
      (Ch02.canonicalMaximizer
        (Ch02.responseExistenceTheory (Ch02.cubeDomain Q) aQ)
        p q).toSolution.flux_memVectorL2
    have hFluxOpenR :
        MemVectorL2 (openCubeSet R)
          (fun x =>
            matVecMul (aQ.toCoeffField x)
              ((Ch02.canonicalMaximizer
                (Ch02.responseExistenceTheory (Ch02.cubeDomain Q) aQ)
                p q).toSolution.toH1.grad x)) := by
      exact hFluxOpen.mono_measure
        (by
          simpa [Ch02.cubeDomain_coe, volumeMeasureOn] using
            MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume
              (openCubeSet_subset_of_mem_descendantsAtDepth hR))
    simpa [MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet R] using hFluxOpenR
  have hExtractOpen :
      (fun x =>
          Xold.flux x +
            (blockMatVecMul (blockCoeffField a x) (Xold.eval x)).1)
        =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x =>
        matVecMul (aQ.toCoeffField x)
          ((Ch02.canonicalMaximizer
            (Ch02.responseExistenceTheory (Ch02.cubeDomain Q) aQ)
            p q).toSolution.toH1.grad x) := by
    simpa only [Xold, haQ, Ch02.cubeDomain_coe] using!
      Ch02.doubledMuMinimizer_neg_left_extracts_canonicalMaximizerFlux
        (Ch02.cubeDomain Q) aQ p q hX
  have hExtractR :
      (fun x =>
          Xold.flux x +
            (blockMatVecMul (blockCoeffField a x) (Xold.eval x)).1)
        =ᵐ[volumeMeasureOn (cubeSet R)]
      fun x =>
        matVecMul (aQ.toCoeffField x)
          ((Ch02.canonicalMaximizer
            (Ch02.responseExistenceTheory (Ch02.cubeDomain Q) aQ)
            p q).toSolution.toH1.grad x) :=
    ae_eq_cubeSet_of_mem_descendantsAtDepth_of_ae_eq_openCubeSet hR hExtractOpen
  have hUpperMemR :
      MemVectorL2 (cubeSet R)
        (fun x => (blockMatVecMul (blockCoeffField a x) (Xold.eval x)).1) := by
    have hDiff :
        MemVectorL2 (cubeSet R)
          (fun x =>
            matVecMul (aQ.toCoeffField x)
              ((Ch02.canonicalMaximizer
                (Ch02.responseExistenceTheory (Ch02.cubeDomain Q) aQ)
                p q).toSolution.toH1.grad x) - Xold.flux x) :=
      hCanonicalFluxMemR.sub hFluxMemR
    refine MeasureTheory.MemLp.ae_eq ?_ hDiff
    filter_upwards [hExtractR] with x hx
    ext i
    have hxi := congrArg (fun v : Vec d => v i) hx
    simp [Pi.add_apply, Pi.sub_apply] at hxi ⊢
    linarith
  have hEnergyUpper :
      ∀ i : Fin d,
        canonicalMuHilbertEnergyBilinFixedCubeSet Q (-p, q)
          (canonicalUpperImageIndicatorTestStateCubeSet R i)
          (canonicalUpperImageIndicatorTestStateCubeSet_memBlockL2 Q R i) a =
        blockPairingAverage (cubeSet Q) a Xold
          (canonicalUpperImageIndicatorTestStateCubeSet R i) := by
    intro i
    let Y := canonicalUpperImageIndicatorTestStateCubeSet R i
    let hY := canonicalUpperImageIndicatorTestStateCubeSet_memBlockL2 Q R i
    let system : AEEMuOperatorSystemData (cubeSet Q) a :=
      canonicalAEEMuOperatorSystemData Q k aSlice
    calc
      canonicalMuHilbertEnergyBilinFixedCubeSet Q (-p, q) Y hY a =
          system.toMuHilbertRealization.energyBilin
            (toHilbertBlockL2OfBlockField (U := cubeSet Q) hY)
            (system.toMuHilbertRealization.minimizerMap (-p, q)) := by
            simp [canonicalMuHilbertEnergyBilinFixedCubeSet, hSlice, k, aSlice, system]
      _ = system.toMuHilbertRealization.energyBilin
            (toHilbertBlockL2OfBlockField (U := cubeSet Q) hY)
            (toHilbertBlockL2OfBlockField (U := cubeSet Q) hAdm.memBlockL2_eval) := by
            rw [← hHilbert]
      _ = blockPairingAverage (cubeSet Q) a Xold Y := by
            simpa [system, AEEMuOperatorSystemData.toMuHilbertRealization,
              MuOperatorRealization.toMuHilbertRealization,
              MuHilbertRealization.ofOperator, Xold, Y, aSlice] using
              system.toMuOperatorRealization.energyBilin_eq_blockPairingAverage_of_blockState
                (X := Xold) (Y := Y)
                hAdm.memBlockL2_eval hY
  ext i
  have hFluxAvg :=
    canonicalDoubledMuResponseFluxFieldAverageCubeSet_eq_integral_of_ae_eq
      hRQ (a := a) (p := p) (q := q) (F := Xold.flux) hFluxAE i
  have hUpperAvg :=
    canonicalDoubledMuResponseUpperImageAverageCubeSet_eq_integral_of_energy_eq
      hRQ (a := a) (p := p) (q := q) (X := Xold) i (hEnergyUpper i)
  have hFluxInt :
      MeasureTheory.IntegrableOn (fun x => Xold.flux x i) (cubeSet R) :=
    CorrectionFieldData.integrableOn_coord_of_memVectorL2
      (U := cubeSet R) hFluxMemR i
  have hUpperInt :
      MeasureTheory.IntegrableOn
        (fun x => (blockMatVecMul (blockCoeffField a x) (Xold.eval x)).1 i)
        (cubeSet R) :=
    CorrectionFieldData.integrableOn_coord_of_memVectorL2
      (U := cubeSet R) hUpperMemR i
  calc
    canonicalScalarResponseFluxAverageCubeSet Q R p q a i =
        canonicalDoubledMuResponseFluxFieldAverageCubeSet Q R p q a i +
          canonicalDoubledMuResponseUpperImageAverageCubeSet Q R p q a i := rfl
    _ = (cubeVolume R)⁻¹ * ∫ x in cubeSet R, Xold.flux x i ∂volume +
          (cubeVolume R)⁻¹ *
            ∫ x in cubeSet R,
              (blockMatVecMul (blockCoeffField a x) (Xold.eval x)).1 i ∂volume := by
          rw [hFluxAvg, hUpperAvg]
    _ = (cubeVolume R)⁻¹ *
          ∫ x in cubeSet R,
            (Xold.flux x +
              (blockMatVecMul (blockCoeffField a x) (Xold.eval x)).1) i ∂volume := by
          rw [show
            (∫ x in cubeSet R,
                (Xold.flux x +
                  (blockMatVecMul (blockCoeffField a x) (Xold.eval x)).1) i ∂volume)
              =
            ∫ x in cubeSet R, Xold.flux x i ∂volume +
              ∫ x in cubeSet R,
                (blockMatVecMul (blockCoeffField a x) (Xold.eval x)).1 i ∂volume by
              simpa [Pi.add_apply] using
                MeasureTheory.integral_add hFluxInt hUpperInt]
          ring
    _ = (cubeVolume R)⁻¹ *
          ∫ x in cubeSet R,
            (matVecMul (aQ.toCoeffField x)
              ((Ch02.canonicalMaximizer
                (Ch02.responseExistenceTheory (Ch02.cubeDomain Q) aQ)
                p q).toSolution.toH1.grad x)) i ∂volume := by
          congr 1
          exact MeasureTheory.integral_congr_ae
            (hExtractR.mono fun x hx =>
              congrArg (fun v : Vec d => v i) hx)
    _ = cubeAverageVec R
        (fun x =>
          matVecMul
            (((triadicCoeffFamilyOfAELocallyUniformlyEllipticField aR ha).coeffOn Q).toCoeffField x)
            ((Ch02.canonicalMaximizer
              (Ch02.responseExistenceTheory (Ch02.cubeDomain Q)
                ((triadicCoeffFamilyOfAELocallyUniformlyEllipticField aR ha).coeffOn Q))
              p q).toSolution.toH1.grad x)) i := by
          rfl


end Ch04
end Book
end Homogenization
