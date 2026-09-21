/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuOperator.CoeffOperator
import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalL2OriginCubeBridge

/-! # Mu Admissibility -/

namespace Homogenization

noncomputable section

/-!
Admissibility-plus-integrability bridge lemmas for the doubled `Mu` problem.

`IsBlockMuAdmissible U P X` now packages the correction-field `L²` membership
and the zero-trace / zero-normal-trace conditions. On finite-measure domains,
this is enough to reconstruct the affine state as an ambient `L²` block field.
Ellipticity then upgrades admissible states to the energy-integrability package
needed for the quantitative averaged identities below.
-/

structure BlockMuIntegrabilityData {d : ℕ} (U : Set (Vec d)) (P : BlockVec d)
    (a : CoeffField d) (X : BlockState d) : Prop where
  potentialCorrection_memL2 :
    MemVectorL2 U (fun x => X.potential x - P.1)
  fluxCorrection_memL2 :
    MemVectorL2 U (fun x => X.flux x - P.2)
  energyIntegrable :
    MeasureTheory.IntegrableOn (blockEnergyDensity a X) U

/-- Ambient block `L²` control plus ellipticity is enough to build the
integrability package used by the doubled `Mu` bridge. -/
theorem blockMuIntegrabilityData_of_memBlockL2_of_isEllipticFieldOn
    {d : ℕ} {U : Set (Vec d)} {P : BlockVec d} {a : CoeffField d} {X : BlockState d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {lam Lam : ℝ}
    (hX : MemBlockL2 U X.eval) (hEll : IsEllipticFieldOn lam Lam U a) :
    BlockMuIntegrabilityData U P a X := by
  refine ⟨?_, ?_, ?_⟩
  · have hPot : MemVectorL2 U X.potential := by
      simpa [BlockState.eval] using memVectorL2_fst_of_memBlockL2 (U := U) hX
    simpa [sub_eq_add_neg] using!
      hPot.sub (MeasureTheory.memLp_const (μ := volumeMeasureOn U) (c := P.1))
  · have hFlux : MemVectorL2 U X.flux := by
      simpa [BlockState.eval] using memVectorL2_snd_of_memBlockL2 (U := U) hX
    simpa [sub_eq_add_neg] using!
      hFlux.sub (MeasureTheory.memLp_const (μ := volumeMeasureOn U) (c := P.2))
  · exact
      blockEnergyDensity_integrableOn_of_memBlockL2_of_isEllipticFieldOn
        (U := U) (a := a) hX hEll

namespace IsBlockMuAdmissible

section Generic

variable {d : ℕ} {U : Set (Vec d)} {P : BlockVec d} {a : CoeffField d} {X : BlockState d}

/-- The correction field attached to an admissible block state depends only on
the affine constraints packaged by `IsBlockMuAdmissible`. -/
noncomputable def toCorrectionFieldDataOfAdmissible
    (hX : IsBlockMuAdmissible U P X) :
    CorrectionFieldData U where
  potential := fun x => X.potential x - P.1
  flux := fun x => X.flux x - P.2
  potential_memL2 := hX.potentialCorrection_memL2
  flux_memL2 := hX.fluxCorrection_memL2
  isPotentialZeroTrace := hX.isPotentialZeroTrace
  isSolenoidalZeroNormalTrace := hX.isSolenoidalZeroNormalTrace

noncomputable def toCorrectionFieldData
    (hX : IsBlockMuAdmissible U P X)
    (hInt : BlockMuIntegrabilityData U P a X) :
    CorrectionFieldData U where
  potential := (hX.toCorrectionFieldDataOfAdmissible).potential
  flux := (hX.toCorrectionFieldDataOfAdmissible).flux
  potential_memL2 := hInt.potentialCorrection_memL2
  flux_memL2 := hInt.fluxCorrection_memL2
  isPotentialZeroTrace := (hX.toCorrectionFieldDataOfAdmissible).isPotentialZeroTrace
  isSolenoidalZeroNormalTrace := (hX.toCorrectionFieldDataOfAdmissible).isSolenoidalZeroNormalTrace

@[simp] theorem toCorrectionFieldData_potential
    (hX : IsBlockMuAdmissible U P X)
    (hInt : BlockMuIntegrabilityData U P a X) :
    (hX.toCorrectionFieldData (a := a) hInt).potential = fun x => X.potential x - P.1 :=
  rfl

@[simp] theorem toCorrectionFieldData_flux
    (hX : IsBlockMuAdmissible U P X)
    (hInt : BlockMuIntegrabilityData U P a X) :
    (hX.toCorrectionFieldData (a := a) hInt).flux = fun x => X.flux x - P.2 :=
  rfl

/-- Reconstruct the ambient block `L²` field carried by an admissible state. -/
theorem memBlockL2_eval
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hX : IsBlockMuAdmissible U P X) :
    MemBlockL2 U X.eval := by
  have hPot : MemVectorL2 U X.potential := by
    have hPot' : MemVectorL2 U (fun x => P.1 + (X.potential x - P.1)) :=
      (MeasureTheory.memLp_const (μ := volumeMeasureOn U) (c := P.1)).add
        hX.potentialCorrection_memL2
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hPot'
  have hFlux : MemVectorL2 U X.flux := by
    have hFlux' : MemVectorL2 U (fun x => P.2 + (X.flux x - P.2)) :=
      (MeasureTheory.memLp_const (μ := volumeMeasureOn U) (c := P.2)).add
        hX.fluxCorrection_memL2
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hFlux'
  simpa [BlockState.eval, blockField] using! memBlockL2_blockField hPot hFlux

/-- The admissible correction carried by `X` lands in the canonical closed
correction space `\Lpoto(U) × \Lsolo(U)`. -/
theorem toCorrectionFieldData_mem_correctionSpace
    (hX : IsBlockMuAdmissible U P X) :
    (hX.toCorrectionFieldDataOfAdmissible).toHilbertBlockL2 ∈
      (PotentialSolenoidalL2Data.ofSubmoduleClosures U).toMuCorrectionSpaceData.correctionSpace := by
  exact
    (PotentialSolenoidalL2Data.ofSubmoduleClosures U).toMuCorrectionSpaceData.mem_correctionSpace
      hX.potentialCorrection_memL2
      hX.fluxCorrection_memL2
      hX.isPotentialZeroTrace
      hX.isSolenoidalZeroNormalTrace

/-- The Hilbert image of an admissible block state splits into the constant
datum `P` plus its correction component. -/
theorem toHilbertBlockL2OfBlockField_eq_blockVecToHilbertBlockL2Const_add
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hX : IsBlockMuAdmissible U P X) :
    toHilbertBlockL2OfBlockField (U := U) hX.memBlockL2_eval =
      blockVecToHilbertBlockL2Const (U := U) P +
        (hX.toCorrectionFieldDataOfAdmissible).toHilbertBlockL2 := by
  apply MeasureTheory.Lp.ext
  filter_upwards
      [coeFn_toHilbertBlockL2OfBlockField (U := U) (F := X.eval) hX.memBlockL2_eval,
       coeFn_toHilbertBlockL2OfComponents (U := U)
         (f := fun x => X.potential x - P.1)
         (g := fun x => X.flux x - P.2)
         hX.potentialCorrection_memL2
         hX.fluxCorrection_memL2,
       coeFn_blockVecToHilbertBlockL2Const (U := U) (P := P),
       MeasureTheory.Lp.coeFn_add
         (blockVecToHilbertBlockL2Const (U := U) P)
         (hX.toCorrectionFieldDataOfAdmissible).toHilbertBlockL2]
    with x hfield hcorr hconst hsum
  have hpoint :
      hilbertifyBlockField X.eval x =
        Function.const (Vec d) (HilbertBlockVec.ofBlockVec P) x +
          hilbertBlockField
            (fun y => X.potential y - P.1)
            (fun y => X.flux y - P.2) x := by
    apply HilbertBlockVec.ext
    · ext i
      simp [BlockState.eval, hilbertifyBlockField, hilbertBlockField, blockField]
    · ext i
      simp [BlockState.eval, hilbertifyBlockField, hilbertBlockField, blockField]
  calc
    (toHilbertBlockL2OfBlockField (U := U) hX.memBlockL2_eval) x
      = hilbertifyBlockField X.eval x := hfield
    _ = Function.const (Vec d) (HilbertBlockVec.ofBlockVec P) x +
          hilbertBlockField
            (fun y => X.potential y - P.1)
            (fun y => X.flux y - P.2) x := hpoint
    _ = (blockVecToHilbertBlockL2Const (U := U) P) x +
          hilbertBlockField
            (fun y => X.potential y - P.1)
            (fun y => X.flux y - P.2) x := by
          rw [← hconst]
    _ = (blockVecToHilbertBlockL2Const (U := U) P) x +
          ((hX.toCorrectionFieldDataOfAdmissible).toHilbertBlockL2) x := by
          rw [← hcorr]
          rfl
    _ = ((⇑(blockVecToHilbertBlockL2Const (U := U) P) : Vec d → HilbertBlockVec d) +
          (⇑(hX.toCorrectionFieldDataOfAdmissible).toHilbertBlockL2 : Vec d → HilbertBlockVec d)) x := by
          rfl
    _ =
        (blockVecToHilbertBlockL2Const (U := U) P +
          (hX.toCorrectionFieldDataOfAdmissible).toHilbertBlockL2) x := by
          simpa [Pi.add_apply] using hsum.symm

/-- Package the correction component of an admissible state as an element of
the canonical closed correction space. -/
noncomputable def toCorrectionSpaceElement
    (hX : IsBlockMuAdmissible U P X) :
    (PotentialSolenoidalL2Data.ofSubmoduleClosures U).toMuCorrectionSpaceData.correctionSpace.toSubmodule :=
  ⟨(hX.toCorrectionFieldDataOfAdmissible).toHilbertBlockL2,
    hX.toCorrectionFieldData_mem_correctionSpace⟩

theorem toHilbertBlockL2OfBlockField_eq_blockVecToHilbertBlockL2Const_add_correctionSpace
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hX : IsBlockMuAdmissible U P X) :
    toHilbertBlockL2OfBlockField (U := U) hX.memBlockL2_eval =
      blockVecToHilbertBlockL2Const (U := U) P + hX.toCorrectionSpaceElement := by
  exact hX.toHilbertBlockL2OfBlockField_eq_blockVecToHilbertBlockL2Const_add

theorem toBlockMuIntegrabilityDataOfIsEllipticFieldOn
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {lam Lam : ℝ} (hX : IsBlockMuAdmissible U P X)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    BlockMuIntegrabilityData U P a X := by
  have hPot : MemVectorL2 U X.potential := by
    have hPot' : MemVectorL2 U (fun x => P.1 + (X.potential x - P.1)) :=
      (MeasureTheory.memLp_const (μ := volumeMeasureOn U) (c := P.1)).add
        hX.potentialCorrection_memL2
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hPot'
  have hFlux : MemVectorL2 U X.flux := by
    have hFlux' : MemVectorL2 U (fun x => P.2 + (X.flux x - P.2)) :=
      (MeasureTheory.memLp_const (μ := volumeMeasureOn U) (c := P.2)).add
        hX.fluxCorrection_memL2
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hFlux'
  have hBlock : MemBlockL2 U X.eval := by
    simpa [BlockState.eval, blockField] using! memBlockL2_blockField hPot hFlux
  exact blockMuIntegrabilityData_of_memBlockL2_of_isEllipticFieldOn
    (U := U) (P := P) (a := a) hBlock hEll

theorem pairingIntegrable
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hX : IsBlockMuAdmissible U P X) :
    MeasureTheory.IntegrableOn (fun x => vecDot (X.potential x) (X.flux x)) U := by
  let Y := hX.toCorrectionFieldDataOfAdmissible
  have hpair :
      (fun x => vecDot (P.1 + Y.potential x) (P.2 + Y.flux x)) =
        fun x => vecDot (X.potential x) (X.flux x) := by
    funext x
    congr <;> ext i <;> simp [Y, IsBlockMuAdmissible.toCorrectionFieldDataOfAdmissible,
      sub_eq_add_neg]
  rw [← hpair]
  simpa [Y] using (CorrectionFieldData.integrableOn_pairing_affine (U := U) Y P.1 P.2)

theorem average_pairing_of_integral_eq_zero
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hX : IsBlockMuAdmissible U P X)
    (hpotZero :
      (fun i => ∫ x in U, (X.potential x - P.1) i ∂MeasureTheory.volume) = 0)
    (hfluxZero :
      (fun i => ∫ x in U, (X.flux x - P.2) i ∂MeasureTheory.volume) = 0)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0) :
    volumeAverage U (fun x => vecDot (X.potential x) (X.flux x)) = vecDot P.1 P.2 := by
  let Y := hX.toCorrectionFieldDataOfAdmissible
  have hpair :
      (fun x => vecDot (P.1 + Y.potential x) (P.2 + Y.flux x)) =
        fun x => vecDot (X.potential x) (X.flux x) := by
    funext x
    congr <;> ext i <;> simp [Y, IsBlockMuAdmissible.toCorrectionFieldDataOfAdmissible,
      sub_eq_add_neg]
  have hint :
      ∫ x in U, vecDot (X.potential x) (X.flux x) ∂MeasureTheory.volume =
        (MeasureTheory.volume U).toReal * vecDot P.1 P.2 := by
    rw [← hpair]
    simpa [Y] using
      (CorrectionFieldData.integral_pairing_affine_eq_volume_mul_vecDot_of_integral_eq_zero
        (U := U) Y P.1 P.2 hpotZero hfluxZero)
  unfold volumeAverage
  rw [hint]
  calc
    (MeasureTheory.volume U).toReal⁻¹ * ((MeasureTheory.volume U).toReal * vecDot P.1 P.2)
        = ((MeasureTheory.volume U).toReal⁻¹ * (MeasureTheory.volume U).toReal) *
            vecDot P.1 P.2 := by ring
    _ = vecDot P.1 P.2 := by
        rw [inv_mul_cancel₀ hvol, one_mul]

theorem blockEnergyAverage_ge_vecDot_of_integral_eq_zero_of_isEllipticFieldOn
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {lam Lam : ℝ} (hX : IsBlockMuAdmissible U P X)
    (hInt : BlockMuIntegrabilityData U P a X)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hpotZero :
      (fun i => ∫ x in U, (X.potential x - P.1) i ∂MeasureTheory.volume) = 0)
    (hfluxZero :
      (fun i => ∫ x in U, (X.flux x - P.2) i ∂MeasureTheory.volume) = 0)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0) :
    vecDot P.1 P.2 ≤ blockEnergyAverage U a X := by
  have hPairInt := hX.pairingIntegrable
  have hPairAvg :=
    hX.average_pairing_of_integral_eq_zero hpotZero hfluxZero hvol
  have hnonneg :
      0 ≤ volumeAverage U
        (fun x => blockEnergyDensity a X x - vecDot (X.potential x) (X.flux x)) := by
    unfold volumeAverage
    refine mul_nonneg ?_ ?_
    · exact inv_nonneg.mpr ENNReal.toReal_nonneg
    · apply MeasureTheory.integral_nonneg_of_ae
      exact (MeasureTheory.ae_restrict_iff' (measurableSet_of_isEllipticFieldOn hEll)).2
        (Filter.Eventually.of_forall fun x hx =>
          sub_nonneg.mpr (blockEnergyDensity_ge_vecDot_of_isEllipticFieldOn hEll X hx))
  have hdiff :
      volumeAverage U
          (fun x => blockEnergyDensity a X x - vecDot (X.potential x) (X.flux x)) =
        blockEnergyAverage U a X - vecDot P.1 P.2 := by
    calc
      volumeAverage U
          (fun x => blockEnergyDensity a X x - vecDot (X.potential x) (X.flux x)) =
        volumeAverage U (blockEnergyDensity a X) -
          volumeAverage U (fun x => vecDot (X.potential x) (X.flux x)) := by
            unfold volumeAverage
            rw [MeasureTheory.integral_sub hInt.energyIntegrable hPairInt]
            ring
      _ = blockEnergyAverage U a X - vecDot P.1 P.2 := by
            rw [hPairAvg]
            simp [blockEnergyAverage]
  rw [hdiff] at hnonneg
  linarith

theorem mu_ge_vecDot_of_isEllipticFieldOn_of_integrabilityBridge
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (bridge :
      ∀ X : BlockState d, IsBlockMuAdmissible U P X -> BlockMuIntegrabilityData U P a X)
    (hpotZero :
      ∀ X : BlockState d, ∀ _hX : IsBlockMuAdmissible U P X,
        (fun i => ∫ x in U, (X.potential x - P.1) i ∂MeasureTheory.volume) = 0)
    (hfluxZero :
      ∀ X : BlockState d, ∀ _hX : IsBlockMuAdmissible U P X,
        (fun i => ∫ x in U, (X.flux x - P.2) i ∂MeasureTheory.volume) = 0)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0) :
    vecDot P.1 P.2 ≤ Mu U P a := by
  apply le_Mu_of_forall_isBlockMuAdmissible
  intro Y hY
  exact hY.blockEnergyAverage_ge_vecDot_of_integral_eq_zero_of_isEllipticFieldOn
    (a := a) (bridge Y hY) hEll (hpotZero Y hY) (hfluxZero Y hY) hvol

theorem mu_ge_vecDot_of_isEllipticFieldOn_of_isSobolevRegularDomain
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsSobolevRegularDomain U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0) :
    vecDot P.1 P.2 ≤ Mu U P a := by
  apply mu_ge_vecDot_of_isEllipticFieldOn_of_integrabilityBridge
    (U := U) (P := P) (a := a) hEll
  · intro X hX
    exact hX.toBlockMuIntegrabilityDataOfIsEllipticFieldOn (a := a) hEll
  · intro X hX
    simpa [sub_eq_add_neg] using
      (IsPotentialZeroTraceOn.integral_eq_zero hX.isPotentialZeroTrace)
  · intro X hX
    simpa [sub_eq_add_neg] using
      (IsSolenoidalZeroNormalTraceOn.integral_eq_zero hU hX.isSolenoidalZeroNormalTrace)
  · exact hvol

end Generic

section OriginCube

variable {d : ℕ} [NeZero d] {n : ℤ} {P : BlockVec d} {a : CoeffField d} {X : BlockState d}

theorem average_pairing_openCubeSet_originCube
    (hX : IsBlockMuAdmissible (openCubeSet (originCube d n)) P X) :
    volumeAverage (openCubeSet (originCube d n))
      (fun x => vecDot (X.potential x) (X.flux x)) = vecDot P.1 P.2 := by
  have hpotZero :
      (fun i =>
        ∫ x in openCubeSet (originCube d n), (X.potential x - P.1) i ∂MeasureTheory.volume) = 0 := by
    simpa [sub_eq_add_neg] using
      (IsPotentialZeroTraceOn.integral_eq_zero_openCubeSet_originCube
        (d := d) (n := n) (f := fun x => X.potential x - P.1) hX.isPotentialZeroTrace)
  have hfluxZero :
      (fun i =>
        ∫ x in openCubeSet (originCube d n), (X.flux x - P.2) i ∂MeasureTheory.volume) = 0 := by
    simpa [sub_eq_add_neg] using
      (IsSolenoidalZeroNormalTraceOn.integral_eq_zero_openCubeSet_originCube
        (d := d) (n := n) (g := fun x => X.flux x - P.2) hX.isSolenoidalZeroNormalTrace)
  have hvol : (MeasureTheory.volume (openCubeSet (originCube d n))).toReal ≠ 0 := by
    rw [volume_openCubeSet_toReal]
    exact (cubeVolume_pos (originCube d n)).ne'
  exact hX.average_pairing_of_integral_eq_zero hpotZero hfluxZero hvol

theorem average_pairing_cubeSet_originCube
    (hX : IsBlockMuAdmissible (cubeSet (originCube d n)) P X) :
    volumeAverage (cubeSet (originCube d n))
      (fun x => vecDot (X.potential x) (X.flux x)) = vecDot P.1 P.2 := by
  have hpotZero :
      (fun i =>
        ∫ x in cubeSet (originCube d n), (X.potential x - P.1) i ∂MeasureTheory.volume) = 0 := by
    simpa [sub_eq_add_neg] using
      (IsPotentialZeroTraceOn.integral_eq_zero_cubeSet_originCube
        (d := d) (n := n) (f := fun x => X.potential x - P.1) hX.isPotentialZeroTrace)
  have hfluxZero :
      (fun i =>
        ∫ x in cubeSet (originCube d n), (X.flux x - P.2) i ∂MeasureTheory.volume) = 0 := by
    simpa [sub_eq_add_neg] using
      (IsSolenoidalZeroNormalTraceOn.integral_eq_zero_cubeSet_originCube
        (d := d) (n := n) (g := fun x => X.flux x - P.2) hX.isSolenoidalZeroNormalTrace)
  have hvol : (MeasureTheory.volume (cubeSet (originCube d n))).toReal ≠ 0 := by
    rw [volume_cubeSet_toReal]
    exact (cubeVolume_pos (originCube d n)).ne'
  exact hX.average_pairing_of_integral_eq_zero hpotZero hfluxZero hvol

theorem blockEnergyAverage_ge_vecDot_openCubeSet_originCube_of_isEllipticFieldOn
    {lam Lam : ℝ}
    (hX : IsBlockMuAdmissible (openCubeSet (originCube d n)) P X)
    (hInt : BlockMuIntegrabilityData (openCubeSet (originCube d n)) P a X)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d n)) a) :
    vecDot P.1 P.2 ≤ blockEnergyAverage (openCubeSet (originCube d n)) a X := by
  have hpotZero :
      (fun i =>
        ∫ x in openCubeSet (originCube d n), (X.potential x - P.1) i ∂MeasureTheory.volume) = 0 := by
    simpa [sub_eq_add_neg] using
      (IsPotentialZeroTraceOn.integral_eq_zero_openCubeSet_originCube
        (d := d) (n := n) (f := fun x => X.potential x - P.1) hX.isPotentialZeroTrace)
  have hfluxZero :
      (fun i =>
        ∫ x in openCubeSet (originCube d n), (X.flux x - P.2) i ∂MeasureTheory.volume) = 0 := by
    simpa [sub_eq_add_neg] using
      (IsSolenoidalZeroNormalTraceOn.integral_eq_zero_openCubeSet_originCube
        (d := d) (n := n) (g := fun x => X.flux x - P.2) hX.isSolenoidalZeroNormalTrace)
  have hvol : (MeasureTheory.volume (openCubeSet (originCube d n))).toReal ≠ 0 := by
    rw [volume_openCubeSet_toReal]
    exact (cubeVolume_pos (originCube d n)).ne'
  exact
    hX.blockEnergyAverage_ge_vecDot_of_integral_eq_zero_of_isEllipticFieldOn
      (a := a) hInt hEll hpotZero hfluxZero hvol

theorem blockEnergyAverage_ge_vecDot_cubeSet_originCube_of_isEllipticFieldOn
    {lam Lam : ℝ}
    (hX : IsBlockMuAdmissible (cubeSet (originCube d n)) P X)
    (hInt : BlockMuIntegrabilityData (cubeSet (originCube d n)) P a X)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet (originCube d n)) a) :
    vecDot P.1 P.2 ≤ blockEnergyAverage (cubeSet (originCube d n)) a X := by
  have hpotZero :
      (fun i =>
        ∫ x in cubeSet (originCube d n), (X.potential x - P.1) i ∂MeasureTheory.volume) = 0 := by
    simpa [sub_eq_add_neg] using
      (IsPotentialZeroTraceOn.integral_eq_zero_cubeSet_originCube
        (d := d) (n := n) (f := fun x => X.potential x - P.1) hX.isPotentialZeroTrace)
  have hfluxZero :
      (fun i =>
        ∫ x in cubeSet (originCube d n), (X.flux x - P.2) i ∂MeasureTheory.volume) = 0 := by
    simpa [sub_eq_add_neg] using
      (IsSolenoidalZeroNormalTraceOn.integral_eq_zero_cubeSet_originCube
        (d := d) (n := n) (g := fun x => X.flux x - P.2) hX.isSolenoidalZeroNormalTrace)
  have hvol : (MeasureTheory.volume (cubeSet (originCube d n))).toReal ≠ 0 := by
    rw [volume_cubeSet_toReal]
    exact (cubeVolume_pos (originCube d n)).ne'
  exact
    hX.blockEnergyAverage_ge_vecDot_of_integral_eq_zero_of_isEllipticFieldOn
      (a := a) hInt hEll hpotZero hfluxZero hvol

theorem mu_ge_vecDot_openCubeSet_originCube_of_isEllipticFieldOn_of_integrabilityBridge
    {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d n)) a)
    (bridge :
      ∀ Y : BlockState d,
        IsBlockMuAdmissible (openCubeSet (originCube d n)) P Y ->
          BlockMuIntegrabilityData (openCubeSet (originCube d n)) P a Y) :
    vecDot P.1 P.2 ≤ Mu (openCubeSet (originCube d n)) P a := by
  apply le_Mu_of_forall_isBlockMuAdmissible
  intro Y hY
  exact hY.blockEnergyAverage_ge_vecDot_openCubeSet_originCube_of_isEllipticFieldOn
    (a := a) (bridge Y hY) hEll

theorem mu_ge_vecDot_cubeSet_originCube_of_isEllipticFieldOn_of_integrabilityBridge
    {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet (originCube d n)) a)
    (bridge :
      ∀ Y : BlockState d,
        IsBlockMuAdmissible (cubeSet (originCube d n)) P Y ->
          BlockMuIntegrabilityData (cubeSet (originCube d n)) P a Y) :
    vecDot P.1 P.2 ≤ Mu (cubeSet (originCube d n)) P a := by
  apply le_Mu_of_forall_isBlockMuAdmissible
  intro Y hY
  exact hY.blockEnergyAverage_ge_vecDot_cubeSet_originCube_of_isEllipticFieldOn
    (a := a) (bridge Y hY) hEll

end OriginCube

end IsBlockMuAdmissible

end

end Homogenization
