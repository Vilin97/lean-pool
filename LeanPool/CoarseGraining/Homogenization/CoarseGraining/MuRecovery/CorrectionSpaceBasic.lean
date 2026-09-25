/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuRecovery.Setup

/-! # Correction Space Basic -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
# Mu correction-space recovery -- definitions and pairing identities

Basic defs: correctionPart, recoveredCorrectionField, recoveredField; the
linearity (add, smul) and memBlockL2 / admissible witnesses; pairing
integrability / averages on openCubeSet and cubeSet; the minimizer_eq
identity, and the blockPairingAverage / integral_blockPairing = 0 lemmas
for repr_recoveredField and correction.
-/

namespace MuCorrectionSpaceRecoveryData

variable {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
variable [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]

/-- The correction part of the Hilbert minimizer, viewed inside the recovered
correction subspace. -/
noncomputable def correctionPart
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (P : BlockVec d) : R.correctionSpace.toSubmodule := by
  let H : MuHilbertRealization U a :=
    system.toMuOperatorRealization.toMuHilbertRealization R.toMuCorrectionSpaceData
  exact
    ⟨H.minimizerMap P - H.constantField P,
      H.sub_minimizerMap_apply_mem P⟩

theorem correctionPart_add
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (P Q : BlockVec d) :
    R.correctionPart system (P + Q) =
      R.correctionPart system P + R.correctionPart system Q := by
  let H : MuHilbertRealization U a :=
    system.toMuOperatorRealization.toMuHilbertRealization R.toMuCorrectionSpaceData
  apply Subtype.ext
  change
    H.minimizerMap (P + Q) - H.constantField (P + Q) =
      (H.minimizerMap P - H.constantField P) + (H.minimizerMap Q - H.constantField Q)
  rw [map_add, map_add]
  abel_nf

theorem correctionPart_smul
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (c : ℝ) (P : BlockVec d) :
    R.correctionPart system (c • P) = c • R.correctionPart system P := by
  let H : MuHilbertRealization U a :=
    system.toMuOperatorRealization.toMuHilbertRealization R.toMuCorrectionSpaceData
  apply Subtype.ext
  change
    H.minimizerMap (c • P) - H.constantField (c • P) =
      c • (H.minimizerMap P - H.constantField P)
  rw [map_smul, map_smul, smul_sub]

/-- The recovered correction field realizing the correction part of the Hilbert
minimizer. -/
noncomputable def recoveredCorrectionField
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (P : BlockVec d) : CorrectionFieldData U :=
  R.repr (R.correctionPart system P)

/-- The affine block state built from a fixed datum `P` and an arbitrary
recovered correction-space element. -/
noncomputable def affineField
    (R : MuCorrectionSpaceRecoveryData U)
    (P : BlockVec d)
    (Y : R.correctionSpace.toSubmodule) : BlockState d := by
  let Z := R.repr Y
  exact
    { potential := (fun _ : Vec d => P.1) + Z.potential
      flux := (fun _ : Vec d => P.2) + Z.flux }

/-- The recovered pointwise minimizer field obtained from the recovered
correction part and the constant datum `P`. -/
noncomputable def recoveredField
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (P : BlockVec d) : BlockState d := by
  let Y := R.recoveredCorrectionField system P
  exact
    { potential := (fun _ : Vec d => P.1) + Y.potential
      flux := (fun _ : Vec d => P.2) + Y.flux }

/-- The generic affine field specializes to the minimizer-built recovered
field when the correction is chosen to be `correctionPart`. -/
theorem affineField_correctionPart
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (P : BlockVec d) :
    R.affineField P (R.correctionPart system P) = R.recoveredField system P := by
  rfl

theorem affineField_memBlockL2
    (R : MuCorrectionSpaceRecoveryData U)
    (P : BlockVec d)
    (Y : R.correctionSpace.toSubmodule) :
    MemBlockL2 U (R.affineField P Y).eval := by
  let Z := R.repr Y
  have hpot : MemVectorL2 U ((fun _ : Vec d => P.1) + Z.potential) :=
    (memVectorL2_const (U := U) P.1).add Z.potential_memL2
  have hflux : MemVectorL2 U ((fun _ : Vec d => P.2) + Z.flux) :=
    (memVectorL2_const (U := U) P.2).add Z.flux_memL2
  simpa [MuCorrectionSpaceRecoveryData.affineField, blockField] using!
    memBlockL2_blockField hpot hflux

omit [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] in
theorem affineField_admissible
    (R : MuCorrectionSpaceRecoveryData U)
    (P : BlockVec d)
    (Y : R.correctionSpace.toSubmodule) :
    IsBlockMuAdmissible U P (R.affineField P Y) := by
  let Z := R.repr Y
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [MuCorrectionSpaceRecoveryData.affineField, constVecField] using
      Z.potential_memL2
  · simpa [MuCorrectionSpaceRecoveryData.affineField, constVecField] using
      Z.isPotentialZeroTrace
  · simpa [MuCorrectionSpaceRecoveryData.affineField, constVecField] using
      Z.flux_memL2
  · simpa [MuCorrectionSpaceRecoveryData.affineField, constVecField] using
      Z.isSolenoidalZeroNormalTrace

theorem affineField_hilbert_eq_const_add
    (R : MuCorrectionSpaceRecoveryData U)
    (P : BlockVec d)
    (Y : R.correctionSpace.toSubmodule) :
    toHilbertBlockL2OfBlockField (U := U) (R.affineField_memBlockL2 P Y) =
      blockVecToHilbertBlockL2Const (U := U) P + Y := by
  let Z := R.repr Y
  apply MeasureTheory.Lp.ext
  filter_upwards
      [coeFn_toHilbertBlockL2OfBlockField (U := U)
        (F := (R.affineField P Y).eval)
        (R.affineField_memBlockL2 P Y),
       coeFn_toHilbertBlockL2OfComponents (U := U) (f := Z.potential) (g := Z.flux)
         Z.potential_memL2 Z.flux_memL2,
       coeFn_blockVecToHilbertBlockL2Const (U := U) (P := P),
       MeasureTheory.Lp.coeFn_add
         (blockVecToHilbertBlockL2Const (U := U) P)
         (Y : HilbertBlockL2 U)]
    with x hfield hcorr hconst hsum
  have hpoint :
      hilbertifyBlockField (R.affineField P Y).eval x =
        Function.const (Vec d) (HilbertBlockVec.ofBlockVec P) x +
          hilbertBlockField Z.potential Z.flux x := by
    apply HilbertBlockVec.ext
    · ext i
      simp [MuCorrectionSpaceRecoveryData.affineField, Z,
        BlockState.eval, hilbertifyBlockField, hilbertBlockField, blockField]
    · ext i
      simp [MuCorrectionSpaceRecoveryData.affineField, Z,
        BlockState.eval, hilbertifyBlockField, hilbertBlockField, blockField]
  calc
    (toHilbertBlockL2OfBlockField (U := U) (R.affineField_memBlockL2 P Y)) x
      = hilbertifyBlockField (R.affineField P Y).eval x := hfield
    _ = Function.const (Vec d) (HilbertBlockVec.ofBlockVec P) x +
          hilbertBlockField Z.potential Z.flux x := hpoint
    _ = (blockVecToHilbertBlockL2Const (U := U) P) x +
          hilbertBlockField Z.potential Z.flux x := by
          rw [← hconst]
    _ = (blockVecToHilbertBlockL2Const (U := U) P) x + Z.toHilbertBlockL2 x := by
          rw [← hcorr]
          rfl
    _ = (blockVecToHilbertBlockL2Const (U := U) P) x + (Y : HilbertBlockL2 U) x := by
          rw [show Z.toHilbertBlockL2 = Y by exact R.repr_eq Y]
    _ = ((⇑(blockVecToHilbertBlockL2Const (U := U) P) : Vec d → HilbertBlockVec d) +
          (⇑(Y : HilbertBlockL2 U) : Vec d → HilbertBlockVec d)) x := by
          rfl
    _ = (blockVecToHilbertBlockL2Const (U := U) P + Y) x := by
          simpa [Pi.add_apply] using hsum.symm

theorem recoveredField_add
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (P Q : BlockVec d) :
    R.recoveredField system (P + Q) =
      R.recoveredField system P + R.recoveredField system Q := by
  ext x i
  · have hrepr_fun :=
      show
          (R.repr (R.correctionPart system (P + Q))).toBlockField =
            (R.repr (R.correctionPart system P)).toBlockField +
              (R.repr (R.correctionPart system Q)).toBlockField from
        by
          simpa [MuCorrectionSpaceRecoveryData.correctionPart_add R system P Q] using
            (MuCorrectionSpaceRecoveryData.repr_add R
              (MuCorrectionSpaceRecoveryData.correctionPart R system P)
              (MuCorrectionSpaceRecoveryData.correctionPart R system Q))
    have hrepr_vec :=
      congrArg Prod.fst <| congrFun hrepr_fun x
    have hrepr :
        (R.recoveredCorrectionField system (P + Q)).potential x i =
          (R.repr (R.correctionPart system P)).potential x i +
            (R.repr (R.correctionPart system Q)).potential x i := by
      simpa [MuCorrectionSpaceRecoveryData.recoveredCorrectionField,
        CorrectionFieldData.toBlockField, blockField] using congrFun hrepr_vec i
    calc
      (R.recoveredField system (P + Q)).potential x i
        = (P.1 i + Q.1 i) +
            ((R.repr (R.correctionPart system P)).potential x i +
              (R.repr (R.correctionPart system Q)).potential x i) := by
            simp [MuCorrectionSpaceRecoveryData.recoveredField, hrepr, add_assoc]
      _ = (P.1 i + (R.repr (R.correctionPart system P)).potential x i) +
            (Q.1 i + (R.repr (R.correctionPart system Q)).potential x i) := by
            abel_nf
      _ = ((R.recoveredField system P).potential + (R.recoveredField system Q).potential) x i := by
            simp [MuCorrectionSpaceRecoveryData.recoveredField,
              MuCorrectionSpaceRecoveryData.recoveredCorrectionField]
      _ = (R.recoveredField system P + R.recoveredField system Q).potential x i := by
            rfl
  · have hrepr_fun :=
      show
          (R.repr (R.correctionPart system (P + Q))).toBlockField =
            (R.repr (R.correctionPart system P)).toBlockField +
              (R.repr (R.correctionPart system Q)).toBlockField from
        by
          simpa [MuCorrectionSpaceRecoveryData.correctionPart_add R system P Q] using
            (MuCorrectionSpaceRecoveryData.repr_add R
              (MuCorrectionSpaceRecoveryData.correctionPart R system P)
              (MuCorrectionSpaceRecoveryData.correctionPart R system Q))
    have hrepr_vec :=
      congrArg Prod.snd <| congrFun hrepr_fun x
    have hrepr :
        (R.recoveredCorrectionField system (P + Q)).flux x i =
          (R.repr (R.correctionPart system P)).flux x i +
            (R.repr (R.correctionPart system Q)).flux x i := by
      simpa [MuCorrectionSpaceRecoveryData.recoveredCorrectionField,
        CorrectionFieldData.toBlockField, blockField] using congrFun hrepr_vec i
    calc
      (R.recoveredField system (P + Q)).flux x i
        = (P.2 i + Q.2 i) +
            ((R.repr (R.correctionPart system P)).flux x i +
              (R.repr (R.correctionPart system Q)).flux x i) := by
            simp [MuCorrectionSpaceRecoveryData.recoveredField, hrepr, add_assoc]
      _ = (P.2 i + (R.repr (R.correctionPart system P)).flux x i) +
            (Q.2 i + (R.repr (R.correctionPart system Q)).flux x i) := by
            abel_nf
      _ = ((R.recoveredField system P).flux + (R.recoveredField system Q).flux) x i := by
            simp [MuCorrectionSpaceRecoveryData.recoveredField,
              MuCorrectionSpaceRecoveryData.recoveredCorrectionField]
      _ = (R.recoveredField system P + R.recoveredField system Q).flux x i := by
            rfl

theorem recoveredField_smul
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (c : ℝ) (P : BlockVec d) :
    R.recoveredField system (c • P) = c • R.recoveredField system P := by
  ext x i
  · have hrepr_fun :=
      show
          (R.repr (R.correctionPart system (c • P))).toBlockField =
            c • (R.repr (R.correctionPart system P)).toBlockField from
        by
          simpa [MuCorrectionSpaceRecoveryData.correctionPart_smul R system c P] using
            (MuCorrectionSpaceRecoveryData.repr_smul R c
              (MuCorrectionSpaceRecoveryData.correctionPart R system P))
    have hrepr_vec := congrArg Prod.fst <| congrFun hrepr_fun x
    have hrepr :
        (R.recoveredCorrectionField system (c • P)).potential x i =
          c * (R.repr (R.correctionPart system P)).potential x i := by
      simpa [MuCorrectionSpaceRecoveryData.recoveredCorrectionField,
        CorrectionFieldData.toBlockField, blockField] using congrFun hrepr_vec i
    calc
      (R.recoveredField system (c • P)).potential x i
        = c * P.1 i + c * (R.repr (R.correctionPart system P)).potential x i := by
            simp [MuCorrectionSpaceRecoveryData.recoveredField, hrepr]
      _ = c * (P.1 i + (R.repr (R.correctionPart system P)).potential x i) := by
            rw [← mul_add]
      _ = (c • (R.recoveredField system P).potential) x i := by
            simp [MuCorrectionSpaceRecoveryData.recoveredField,
              MuCorrectionSpaceRecoveryData.recoveredCorrectionField]
      _ = (c • R.recoveredField system P).potential x i := by
            rfl
  · have hrepr_fun :=
      show
          (R.repr (R.correctionPart system (c • P))).toBlockField =
            c • (R.repr (R.correctionPart system P)).toBlockField from
        by
          simpa [MuCorrectionSpaceRecoveryData.correctionPart_smul R system c P] using
            (MuCorrectionSpaceRecoveryData.repr_smul R c
              (MuCorrectionSpaceRecoveryData.correctionPart R system P))
    have hrepr_vec := congrArg Prod.snd <| congrFun hrepr_fun x
    have hrepr :
        (R.recoveredCorrectionField system (c • P)).flux x i =
          c * (R.repr (R.correctionPart system P)).flux x i := by
      simpa [MuCorrectionSpaceRecoveryData.recoveredCorrectionField,
        CorrectionFieldData.toBlockField, blockField] using congrFun hrepr_vec i
    calc
      (R.recoveredField system (c • P)).flux x i
        = c * P.2 i + c * (R.repr (R.correctionPart system P)).flux x i := by
            simp [MuCorrectionSpaceRecoveryData.recoveredField, hrepr]
      _ = c * (P.2 i + (R.repr (R.correctionPart system P)).flux x i) := by
            rw [← mul_add]
      _ = (c • (R.recoveredField system P).flux) x i := by
            simp [MuCorrectionSpaceRecoveryData.recoveredField,
              MuCorrectionSpaceRecoveryData.recoveredCorrectionField]
      _ = (c • R.recoveredField system P).flux x i := by
            rfl

theorem recoveredField_memBlockL2
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (P : BlockVec d) :
    MemBlockL2 U (R.recoveredField system P).eval := by
  let Y := MuCorrectionSpaceRecoveryData.repr R
    (MuCorrectionSpaceRecoveryData.correctionPart R system P)
  have hpot : MemVectorL2 U ((fun _ : Vec d => P.1) + Y.potential) :=
    (memVectorL2_const (U := U) P.1).add Y.potential_memL2
  have hflux : MemVectorL2 U ((fun _ : Vec d => P.2) + Y.flux) :=
    (memVectorL2_const (U := U) P.2).add Y.flux_memL2
  simpa [MuCorrectionSpaceRecoveryData.recoveredField, blockField] using!
    memBlockL2_blockField hpot hflux

theorem recoveredField_admissible
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (P : BlockVec d) :
    IsBlockMuAdmissible U P (R.recoveredField system P) := by
  let Y := MuCorrectionSpaceRecoveryData.repr R
    (MuCorrectionSpaceRecoveryData.correctionPart R system P)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [MuCorrectionSpaceRecoveryData.recoveredField, constVecField] using!
      Y.potential_memL2
  · simpa [MuCorrectionSpaceRecoveryData.recoveredField, constVecField] using!
      Y.isPotentialZeroTrace
  · simpa [MuCorrectionSpaceRecoveryData.recoveredField, constVecField] using!
      Y.flux_memL2
  · simpa [MuCorrectionSpaceRecoveryData.recoveredField, constVecField] using!
      Y.isSolenoidalZeroNormalTrace

theorem recoveredField_integral_pairing_openCubeSet_originCube
    {d : ℕ} [NeZero d] {n : ℤ} {a : CoeffField d}
    (R : MuCorrectionSpaceRecoveryData (openCubeSet (originCube d n)))
    (system : MuOperatorSystemData (openCubeSet (originCube d n)) a)
    (P : BlockVec d) :
    ∫ x in openCubeSet (originCube d n),
        vecDot ((R.recoveredField system P).potential x)
          ((R.recoveredField system P).flux x) ∂MeasureTheory.volume =
      (MeasureTheory.volume (openCubeSet (originCube d n))).toReal * vecDot P.1 P.2 := by
  let Y := MuCorrectionSpaceRecoveryData.repr R
    (MuCorrectionSpaceRecoveryData.correctionPart R system P)
  simpa [MuCorrectionSpaceRecoveryData.recoveredField, Y] using!
    (CorrectionFieldData.integral_pairing_affine_eq_volume_mul_vecDot
      (U := openCubeSet (originCube d n))
      (hU := isSobolevRegularDomain_openCubeSet_originCube_recovery (d := d) n)
      (X := Y) (p := P.1) (q := P.2))

theorem recoveredField_integral_pairing_cubeSet_originCube
    {d : ℕ} [NeZero d] {n : ℤ} {a : CoeffField d}
    (R : MuCorrectionSpaceRecoveryData (cubeSet (originCube d n)))
    (system : MuOperatorSystemData (cubeSet (originCube d n)) a)
    (P : BlockVec d) :
    ∫ x in cubeSet (originCube d n),
        vecDot ((R.recoveredField system P).potential x)
          ((R.recoveredField system P).flux x) ∂MeasureTheory.volume =
      (MeasureTheory.volume (cubeSet (originCube d n))).toReal * vecDot P.1 P.2 := by
  let Y := MuCorrectionSpaceRecoveryData.repr R
    (MuCorrectionSpaceRecoveryData.correctionPart R system P)
  simpa [MuCorrectionSpaceRecoveryData.recoveredField, Y] using!
    (CorrectionFieldData.integral_pairing_affine_eq_volume_mul_vecDot
      (U := cubeSet (originCube d n))
      (hU := isSobolevRegularDomain_cubeSet_originCube_recovery (d := d) n)
      (X := Y) (p := P.1) (q := P.2))

theorem recoveredField_integrableOn_pairing_openCubeSet_originCube
    {d : ℕ} [NeZero d] {n : ℤ} {a : CoeffField d}
    (R : MuCorrectionSpaceRecoveryData (openCubeSet (originCube d n)))
    (system : MuOperatorSystemData (openCubeSet (originCube d n)) a)
    (P : BlockVec d) :
    MeasureTheory.IntegrableOn
      (fun x => vecDot ((R.recoveredField system P).potential x)
        ((R.recoveredField system P).flux x))
      (openCubeSet (originCube d n)) := by
  let Y := MuCorrectionSpaceRecoveryData.repr R
    (MuCorrectionSpaceRecoveryData.correctionPart R system P)
  simpa [MuCorrectionSpaceRecoveryData.recoveredField, Y] using!
    Y.integrableOn_pairing_affine P.1 P.2

theorem recoveredField_integrableOn_pairing_cubeSet_originCube
    {d : ℕ} [NeZero d] {n : ℤ} {a : CoeffField d}
    (R : MuCorrectionSpaceRecoveryData (cubeSet (originCube d n)))
    (system : MuOperatorSystemData (cubeSet (originCube d n)) a)
    (P : BlockVec d) :
    MeasureTheory.IntegrableOn
      (fun x => vecDot ((R.recoveredField system P).potential x)
        ((R.recoveredField system P).flux x))
      (cubeSet (originCube d n)) := by
  let Y := MuCorrectionSpaceRecoveryData.repr R
    (MuCorrectionSpaceRecoveryData.correctionPart R system P)
  simpa [MuCorrectionSpaceRecoveryData.recoveredField, Y] using!
    Y.integrableOn_pairing_affine P.1 P.2

theorem recoveredField_average_pairing_openCubeSet_originCube
    {d : ℕ} [NeZero d] {n : ℤ} {a : CoeffField d}
    (R : MuCorrectionSpaceRecoveryData (openCubeSet (originCube d n)))
    (system : MuOperatorSystemData (openCubeSet (originCube d n)) a)
    (P : BlockVec d) :
    volumeAverage (openCubeSet (originCube d n))
      (fun x => vecDot ((R.recoveredField system P).potential x)
        ((R.recoveredField system P).flux x)) =
      vecDot P.1 P.2 := by
  have hvol :
      (MeasureTheory.volume (openCubeSet (originCube d n))).toReal ≠ 0 := by
    rw [volume_openCubeSet_toReal]
    exact (cubeVolume_pos (originCube d n)).ne'
  unfold volumeAverage
  rw [recoveredField_integral_pairing_openCubeSet_originCube]
  field_simp [hvol]

theorem recoveredField_average_pairing_cubeSet_originCube
    {d : ℕ} [NeZero d] {n : ℤ} {a : CoeffField d}
    (R : MuCorrectionSpaceRecoveryData (cubeSet (originCube d n)))
    (system : MuOperatorSystemData (cubeSet (originCube d n)) a)
    (P : BlockVec d) :
    volumeAverage (cubeSet (originCube d n))
      (fun x => vecDot ((R.recoveredField system P).potential x)
        ((R.recoveredField system P).flux x)) =
      vecDot P.1 P.2 := by
  have hvol :
      (MeasureTheory.volume (cubeSet (originCube d n))).toReal ≠ 0 := by
    rw [volume_cubeSet_toReal]
    exact (cubeVolume_pos (originCube d n)).ne'
  unfold volumeAverage
  rw [recoveredField_integral_pairing_cubeSet_originCube]
  field_simp [hvol]

theorem recoveredField_average_state_openCubeSet_originCube
    {d : ℕ} [NeZero d] {n : ℤ} {a : CoeffField d}
    (R : MuCorrectionSpaceRecoveryData (openCubeSet (originCube d n)))
    (system : MuOperatorSystemData (openCubeSet (originCube d n)) a)
    (P : BlockVec d) :
    ((fun i =>
        volumeAverage (openCubeSet (originCube d n))
          (fun x => (R.recoveredField system P).potential x i)),
      (fun i =>
        volumeAverage (openCubeSet (originCube d n))
          (fun x => (R.recoveredField system P).flux x i))) = P := by
  let Y := MuCorrectionSpaceRecoveryData.repr R
    (MuCorrectionSpaceRecoveryData.correctionPart R system P)
  have hvol :
      (MeasureTheory.volume (openCubeSet (originCube d n))).toReal ≠ 0 :=
    (volume_openCubeSet_originCube_toReal_pos_recovery (d := d) n).ne'
  simpa [MuCorrectionSpaceRecoveryData.recoveredField, Y, volumeAverage, integralAverage] using!
    (CorrectionFieldData.average_state_affine
      (U := openCubeSet (originCube d n))
      (hU := isSobolevRegularDomain_openCubeSet_originCube_recovery (d := d) n)
      (hvol := hvol) (X := Y) (P := P))

theorem recoveredField_average_state_cubeSet_originCube
    {d : ℕ} [NeZero d] {n : ℤ} {a : CoeffField d}
    (R : MuCorrectionSpaceRecoveryData (cubeSet (originCube d n)))
    (system : MuOperatorSystemData (cubeSet (originCube d n)) a)
    (P : BlockVec d) :
    ((fun i =>
        volumeAverage (cubeSet (originCube d n))
          (fun x => (R.recoveredField system P).potential x i)),
      (fun i =>
        volumeAverage (cubeSet (originCube d n))
          (fun x => (R.recoveredField system P).flux x i))) = P := by
  let Y := MuCorrectionSpaceRecoveryData.repr R
    (MuCorrectionSpaceRecoveryData.correctionPart R system P)
  have hvol :
      (MeasureTheory.volume (cubeSet (originCube d n))).toReal ≠ 0 :=
    (volume_cubeSet_originCube_toReal_pos_recovery (d := d) n).ne'
  simpa [MuCorrectionSpaceRecoveryData.recoveredField, Y, volumeAverage, integralAverage] using!
    (CorrectionFieldData.average_state_affine
      (U := cubeSet (originCube d n))
      (hU := isSobolevRegularDomain_cubeSet_originCube_recovery (d := d) n)
      (hvol := hvol) (X := Y) (P := P))

theorem recoveredField_average_state_of_isSobolevRegularDomain
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (hU : IsSobolevRegularDomain U)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (P : BlockVec d) :
    ((fun i => volumeAverage U
        (fun x => (R.recoveredField system P).potential x i)),
      (fun i => volumeAverage U
        (fun x => (R.recoveredField system P).flux x i))) = P := by
  let Y := MuCorrectionSpaceRecoveryData.repr R
    (MuCorrectionSpaceRecoveryData.correctionPart R system P)
  simpa [MuCorrectionSpaceRecoveryData.recoveredField, Y, volumeAverage, integralAverage] using!
    (CorrectionFieldData.average_state_affine
      (U := U)
      (hU := hU)
      (hvol := hvol)
      (X := Y)
      (P := P))

theorem recoveredField_integrableOn_pairing_of_integral_eq_zero
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (P : BlockVec d) :
    MeasureTheory.IntegrableOn
      (fun x => vecDot ((R.recoveredField system P).potential x)
        ((R.recoveredField system P).flux x)) U := by
  let Y := R.recoveredCorrectionField system P
  simpa [MuCorrectionSpaceRecoveryData.recoveredField, MuCorrectionSpaceRecoveryData.recoveredCorrectionField,
    Y] using Y.integrableOn_pairing_affine P.1 P.2

theorem recoveredField_average_pairing_of_integral_eq_zero
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (hpotZero :
      ∀ P : BlockVec d,
        (fun i => ∫ x in U, (R.recoveredCorrectionField system P).potential x i
          ∂MeasureTheory.volume) = 0)
    (hfluxZero :
      ∀ P : BlockVec d,
        (fun i => ∫ x in U, (R.recoveredCorrectionField system P).flux x i
          ∂MeasureTheory.volume) = 0)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (P : BlockVec d) :
    volumeAverage U
      (fun x => vecDot ((R.recoveredField system P).potential x)
        ((R.recoveredField system P).flux x)) =
      vecDot P.1 P.2 := by
  let Y := R.recoveredCorrectionField system P
  have hpair :
      ∫ x in U, vecDot ((R.recoveredField system P).potential x)
          ((R.recoveredField system P).flux x) ∂MeasureTheory.volume =
        (MeasureTheory.volume U).toReal * vecDot P.1 P.2 := by
    simpa [MuCorrectionSpaceRecoveryData.recoveredField, MuCorrectionSpaceRecoveryData.recoveredCorrectionField,
      Y] using
      Y.integral_pairing_affine_eq_volume_mul_vecDot_of_integral_eq_zero
        P.1 P.2 (hpotZero P) (hfluxZero P)
  unfold volumeAverage
  rw [hpair]
  field_simp [hvol]

theorem recoveredField_minimizer_eq
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (P : BlockVec d) :
    toHilbertBlockL2OfBlockField (R.recoveredField_memBlockL2 system P) =
      (system.toMuOperatorRealization.toMuHilbertRealization R.toMuCorrectionSpaceData).minimizerMap P := by
  let H := system.toMuOperatorRealization.toMuHilbertRealization R.toMuCorrectionSpaceData
  let Y := R.recoveredCorrectionField system P
  have hpot : MemVectorL2 U ((fun _ : Vec d => P.1) + Y.potential) :=
    (memVectorL2_const (U := U) P.1).add Y.potential_memL2
  have hflux : MemVectorL2 U ((fun _ : Vec d => P.2) + Y.flux) :=
    (memVectorL2_const (U := U) P.2).add Y.flux_memL2
  have hconst_add :
      toHilbertBlockL2OfBlockField (R.recoveredField_memBlockL2 system P) =
        blockVecToHilbertBlockL2Const (U := U) P + Y.toHilbertBlockL2 := by
    apply MeasureTheory.Lp.ext
    filter_upwards
        [coeFn_toHilbertBlockL2OfBlockField (U := U)
          (F := (R.recoveredField system P).eval)
          (R.recoveredField_memBlockL2 system P),
         coeFn_toHilbertBlockL2OfComponents (U := U) (f := Y.potential) (g := Y.flux)
           Y.potential_memL2 Y.flux_memL2,
         coeFn_blockVecToHilbertBlockL2Const (U := U) (P := P),
         MeasureTheory.Lp.coeFn_add
           (blockVecToHilbertBlockL2Const (U := U) P)
           Y.toHilbertBlockL2]
      with x hfield hcorr hconst hsum
    have hpoint :
        hilbertifyBlockField (R.recoveredField system P).eval x =
          Function.const (Vec d) (HilbertBlockVec.ofBlockVec P) x +
            hilbertBlockField Y.potential Y.flux x := by
      apply HilbertBlockVec.ext
      · ext i
        simp [Y, BlockState.eval, MuCorrectionSpaceRecoveryData.recoveredField, hilbertifyBlockField,
          hilbertBlockField, blockField]
      · ext i
        simp [Y, BlockState.eval, MuCorrectionSpaceRecoveryData.recoveredField, hilbertifyBlockField,
          hilbertBlockField, blockField]
    calc
      (toHilbertBlockL2OfBlockField (R.recoveredField_memBlockL2 system P)) x
        = hilbertifyBlockField (R.recoveredField system P).eval x := hfield
      _ = Function.const (Vec d) (HilbertBlockVec.ofBlockVec P) x +
            hilbertBlockField Y.potential Y.flux x := hpoint
      _ = (blockVecToHilbertBlockL2Const (U := U) P) x +
            hilbertBlockField Y.potential Y.flux x := by
          rw [← hconst]
      _ = (blockVecToHilbertBlockL2Const (U := U) P) x +
            (toHilbertBlockL2OfComponents Y.potential_memL2 Y.flux_memL2) x := by
          rw [← hcorr]
      _ = (blockVecToHilbertBlockL2Const (U := U) P) x + Y.toHilbertBlockL2 x := by
          simp [Y, CorrectionFieldData.toHilbertBlockL2]
      _ = ((⇑(blockVecToHilbertBlockL2Const (U := U) P) : Vec d → HilbertBlockVec d) +
            (⇑Y.toHilbertBlockL2 : Vec d → HilbertBlockVec d)) x := by
          rfl
      _ = (blockVecToHilbertBlockL2Const (U := U) P + Y.toHilbertBlockL2) x := by
          simpa [Y, CorrectionFieldData.toHilbertBlockL2, Pi.add_apply] using hsum.symm
  calc
    toHilbertBlockL2OfBlockField (R.recoveredField_memBlockL2 system P)
        = blockVecToHilbertBlockL2Const (U := U) P + Y.toHilbertBlockL2 := hconst_add
    _ = blockVecToHilbertBlockL2Const (U := U) P +
          MuCorrectionSpaceRecoveryData.correctionPart R system P := by
          rw [show Y.toHilbertBlockL2 = MuCorrectionSpaceRecoveryData.correctionPart R system P by
            simpa [Y, MuCorrectionSpaceRecoveryData.recoveredCorrectionField] using
              (MuCorrectionSpaceRecoveryData.repr_eq R
                (MuCorrectionSpaceRecoveryData.correctionPart R system P))]
    _ = H.minimizerMap P := by
          change
            H.constantField P + (H.minimizerMap P - H.constantField P) =
              H.minimizerMap P
          rw [add_comm, sub_add_cancel]

theorem blockPairingAverage_repr_recoveredField_eq_zero
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (P : BlockVec d)
    (Y : R.correctionSpace.toSubmodule) :
    blockPairingAverage U a
      { potential := (R.repr Y).potential
        flux := (R.repr Y).flux }
      (R.recoveredField system P) = 0 := by
  let H : MuHilbertRealization U a :=
    system.toMuOperatorRealization.toMuHilbertRealization R.toMuCorrectionSpaceData
  let Z : BlockState d :=
    { potential := (R.repr Y).potential
      flux := (R.repr Y).flux }
  have hZ :
      MemBlockL2 U Z.eval := by
    simpa [Z, CorrectionFieldData.toBlockField, blockField] using!
      (R.repr Y).memBlockL2_toBlockField
  have hrepr :
      toHilbertBlockL2OfBlockField (U := U) hZ = Y := by
    calc
      toHilbertBlockL2OfBlockField (U := U) hZ
          = blockL2ToHilbertBlockL2 (U := U) (R.repr Y).toBlockL2 := by
              symm
              simpa [CorrectionFieldData.toBlockL2, Z, CorrectionFieldData.toBlockField] using!
                (Homogenization.blockL2ToHilbertBlockL2_toBlockL2
                  (U := U)
                  (F := (R.repr Y).toBlockField)
                  (R.repr Y).memBlockL2_toBlockField)
      _ = (R.repr Y).toHilbertBlockL2 := by
            exact (R.repr Y).blockL2ToHilbertBlockL2_toBlockL2
      _ = Y := by
            exact R.repr_eq Y
  calc
    blockPairingAverage U a Z (R.recoveredField system P)
        = H.energyBilin
            (toHilbertBlockL2OfBlockField (U := U) (R.recoveredField_memBlockL2 system P))
            (toHilbertBlockL2OfBlockField (U := U) hZ) := by
              symm
              simpa [H] using!
                system.toMuOperatorRealization.energyBilin_eq_blockPairingAverage_of_blockState
                  (X := Z)
                  (Y := R.recoveredField system P)
                  hZ
                  (R.recoveredField_memBlockL2 system P)
    _ = H.energyBilin (H.minimizerMap P) Y := by
          rw [← R.recoveredField_minimizer_eq system P, hrepr]
    _ = 0 := by
          exact H.minimizerMap_firstVariation P Y

theorem integral_blockPairingIntegrand_repr_recoveredField_eq_zero
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (P : BlockVec d)
    (Y : R.correctionSpace.toSubmodule)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0) :
    ∫ x in U,
        blockPairingIntegrand a
          { potential := (R.repr Y).potential
            flux := (R.repr Y).flux }
          (R.recoveredField system P) x ∂MeasureTheory.volume = 0 := by
  have hzero := R.blockPairingAverage_repr_recoveredField_eq_zero system P Y
  unfold blockPairingAverage volumeAverage at hzero
  exact (mul_eq_zero.mp hzero).resolve_left (inv_ne_zero hvol)

theorem blockPairingAverage_correction_eq_zero
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (P : BlockVec d)
    {f g : Vec d → Vec d}
    (hf : MemVectorL2 U f)
    (hg : MemVectorL2 U g)
    (hpot : IsPotentialZeroTraceOn U f)
    (hsol : IsSolenoidalZeroNormalTraceOn U g) :
    blockPairingAverage U a
      { potential := f
        flux := g }
      (R.recoveredField system P) = 0 := by
  let H : MuHilbertRealization U a :=
    system.toMuOperatorRealization.toMuHilbertRealization R.toMuCorrectionSpaceData
  let Y : R.correctionSpace.toSubmodule :=
    ⟨toHilbertBlockL2OfComponents hf hg,
      R.mem_correctionSpace hf hg hpot hsol⟩
  let Z : BlockState d :=
    { potential := f
      flux := g }
  have hZ :
      MemBlockL2 U Z.eval := by
    simpa [Z, BlockState.eval, blockField] using! memBlockL2_blockField hf hg
  have hY :
      toHilbertBlockL2OfBlockField (U := U) hZ = Y := by
    apply MeasureTheory.Lp.ext
    filter_upwards
        [coeFn_toHilbertBlockL2OfBlockField (U := U) (F := Z.eval) hZ,
         coeFn_toHilbertBlockL2OfComponents (U := U) (f := f) (g := g) hf hg]
      with x hblock hfg
    rw [hblock, hfg]
    simp [Z, BlockState.eval, hilbertifyBlockField, hilbertBlockField, blockField]
  calc
    blockPairingAverage U a Z (R.recoveredField system P)
        = H.energyBilin
            (toHilbertBlockL2OfBlockField (U := U) (R.recoveredField_memBlockL2 system P))
            (toHilbertBlockL2OfBlockField (U := U) hZ) := by
              symm
              simpa [H] using!
                system.toMuOperatorRealization.energyBilin_eq_blockPairingAverage_of_blockState
                  (X := Z)
                  (Y := R.recoveredField system P)
                  hZ
                  (R.recoveredField_memBlockL2 system P)
    _ = H.energyBilin (H.minimizerMap P) Y := by
          rw [← R.recoveredField_minimizer_eq system P, hY]
    _ = 0 := by
          exact H.minimizerMap_firstVariation P Y

theorem integral_blockPairingIntegrand_correction_eq_zero
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (P : BlockVec d)
    {f g : Vec d → Vec d}
    (hf : MemVectorL2 U f)
    (hg : MemVectorL2 U g)
    (hpot : IsPotentialZeroTraceOn U f)
    (hsol : IsSolenoidalZeroNormalTraceOn U g)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0) :
    ∫ x in U,
        blockPairingIntegrand a
          { potential := f
            flux := g }
          (R.recoveredField system P) x ∂MeasureTheory.volume = 0 := by
  have hzero := R.blockPairingAverage_correction_eq_zero system P hf hg hpot hsol
  unfold blockPairingAverage volumeAverage at hzero
  exact (mul_eq_zero.mp hzero).resolve_left (inv_ne_zero hvol)

end MuCorrectionSpaceRecoveryData

end

end Homogenization
