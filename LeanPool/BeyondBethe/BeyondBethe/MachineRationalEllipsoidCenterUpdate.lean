/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.MachineBoundedUnary
public import LeanPool.BeyondBethe.BeyondBethe.MachineRationalVectorSub

/-!
# Polynomial-time center part of the rational ellipsoid update

The input is a canonical ellipsoid-state word followed by a canonical cut
normal.  Every intermediate remains a finite word: the program pulls the cut
back through the transposed basis, normalizes by its `ℓ1` norm, multiplies by
the basis, scales by `alpha`, and subtracts from the stored center.
-/

@[expose] public section

namespace BeyondBethe

open Complexity

/-- Extracts the current ellipsoid-state word from a center-update request. -/
def machineRationalCenterUpdateStateWord
    (word : List Bool) : List Bool := machinePairFirst word

/-- Extracts the cut-vector word from a center-update request. -/
def machineRationalCenterUpdateCutWord
    (word : List Bool) : List Bool := machinePairSecond word

/-- Reads the binary ellipsoid dimension from the center-update state. -/
def machineRationalCenterUpdateDimensionBits
    (word : List Bool) : List Bool :=
  machineRationalEllipsoidDimensionWord
    (machineRationalCenterUpdateStateWord word)

/-- The complete state word is a unary guard for its own dimension. -/
def machineRationalCenterUpdateDimensionUnary
    (word : List Bool) : List Bool :=
  machineBoundedUnary
    (pair (machineRationalCenterUpdateStateWord word)
      (machineRationalCenterUpdateDimensionBits word))

/-- Reads the encoded current center from the center-update state. -/
def machineRationalCenterUpdateCenterWord
    (word : List Bool) : List Bool :=
  machineRationalEllipsoidCenterWord
    (machineRationalCenterUpdateStateWord word)

/-- Reads the encoded current basis matrix from the center-update state. -/
def machineRationalCenterUpdateBasisWord
    (word : List Bool) : List Bool :=
  machineRationalEllipsoidBasisWord
    (machineRationalCenterUpdateStateWord word)

/-- Multiplies the cut vector by the transpose of the current basis to pull it into ellipsoid
coordinates. -/
def machineRationalCenterUpdatePulledBackCode
    (word : List Bool) : List Bool :=
  machineRationalTransposeMulVectorCode
    (pair (machineRationalCenterUpdateDimensionUnary word)
      (pair (machineRationalCenterUpdateBasisWord word)
        (machineRationalCenterUpdateCutWord word)))

/-- Computes the rational normalized direction associated with the pulled-back cut vector. -/
def machineRationalCenterUpdateNormalizedCode
    (word : List Bool) : List Bool :=
  machineRationalNormalizedDirectionCode
    (machineRationalCenterUpdatePulledBackCode word)

/-- Maps the normalized pulled-back direction through the current basis to obtain a displacement
vector. -/
def machineRationalCenterUpdateDisplacementCode
    (word : List Bool) : List Bool :=
  machineRationalMatrixMulVectorCode
    (pair (machineRationalCenterUpdateDimensionUnary word)
      (pair (machineRationalCenterUpdateBasisWord word)
        (machineRationalCenterUpdateNormalizedCode word)))

/-- Scales the displacement vector by the dimension-dependent rational ellipsoid center-shift
factor. -/
def machineRationalCenterUpdateScaledDisplacementCode
    (word : List Bool) : List Bool :=
  machineRationalVectorScaleCode
    (pair
      (machineEllipsoidAlphaRawCode
        (machineRationalCenterUpdateDimensionBits word))
      (machineRationalCenterUpdateDisplacementCode word))

/-- Encodes the updated ellipsoid center by subtracting the scaled displacement from its current
center. -/
def machineRationalEllipsoidCenterUpdateCode
    (word : List Bool) : List Bool :=
  machineRationalVectorSubCode
    (pair (machineRationalCenterUpdateDimensionUnary word)
      (pair (machineRationalCenterUpdateCenterWord word)
        (machineRationalCenterUpdateScaledDisplacementCode word)))

theorem machineRationalCenterUpdateStateWord_mem_FP :
    machineRationalCenterUpdateStateWord ∈ FP := machinePairFirst_mem_FP

theorem machineRationalCenterUpdateCutWord_mem_FP :
    machineRationalCenterUpdateCutWord ∈ FP := machinePairSecond_mem_FP

theorem machineRationalCenterUpdateDimensionBits_mem_FP :
    machineRationalCenterUpdateDimensionBits ∈ FP := by
  simpa only [machineRationalCenterUpdateDimensionBits] using!
    machineCompose_mem_FP machineRationalCenterUpdateStateWord_mem_FP
      machineRationalEllipsoidDimensionWord_mem_FP

theorem machineRationalCenterUpdateDimensionUnary_mem_FP :
    machineRationalCenterUpdateDimensionUnary ∈ FP := by
  have hinput := machinePair_mem_FP
    machineRationalCenterUpdateStateWord_mem_FP
    machineRationalCenterUpdateDimensionBits_mem_FP
  simpa only [machineRationalCenterUpdateDimensionUnary] using!
    machineCompose_mem_FP hinput machineBoundedUnary_mem_FP

theorem machineRationalCenterUpdateCenterWord_mem_FP :
    machineRationalCenterUpdateCenterWord ∈ FP := by
  simpa only [machineRationalCenterUpdateCenterWord] using!
    machineCompose_mem_FP machineRationalCenterUpdateStateWord_mem_FP
      machineRationalEllipsoidCenterWord_mem_FP

theorem machineRationalCenterUpdateBasisWord_mem_FP :
    machineRationalCenterUpdateBasisWord ∈ FP := by
  simpa only [machineRationalCenterUpdateBasisWord] using!
    machineCompose_mem_FP machineRationalCenterUpdateStateWord_mem_FP
      machineRationalEllipsoidBasisWord_mem_FP

theorem machineRationalCenterUpdatePulledBackCode_mem_FP :
    machineRationalCenterUpdatePulledBackCode ∈ FP := by
  have hpayload := machinePair_mem_FP
    machineRationalCenterUpdateBasisWord_mem_FP
    machineRationalCenterUpdateCutWord_mem_FP
  have hinput := machinePair_mem_FP
    machineRationalCenterUpdateDimensionUnary_mem_FP hpayload
  simpa only [machineRationalCenterUpdatePulledBackCode] using!
    machineCompose_mem_FP hinput machineRationalTransposeMulVectorCode_mem_FP

theorem machineRationalCenterUpdateNormalizedCode_mem_FP :
    machineRationalCenterUpdateNormalizedCode ∈ FP := by
  simpa only [machineRationalCenterUpdateNormalizedCode] using!
    machineCompose_mem_FP machineRationalCenterUpdatePulledBackCode_mem_FP
      machineRationalNormalizedDirectionCode_mem_FP

theorem machineRationalCenterUpdateDisplacementCode_mem_FP :
    machineRationalCenterUpdateDisplacementCode ∈ FP := by
  have hpayload := machinePair_mem_FP
    machineRationalCenterUpdateBasisWord_mem_FP
    machineRationalCenterUpdateNormalizedCode_mem_FP
  have hinput := machinePair_mem_FP
    machineRationalCenterUpdateDimensionUnary_mem_FP hpayload
  simpa only [machineRationalCenterUpdateDisplacementCode] using!
    machineCompose_mem_FP hinput machineRationalMatrixMulVectorCode_mem_FP

theorem machineRationalCenterUpdateScaledDisplacementCode_mem_FP :
    machineRationalCenterUpdateScaledDisplacementCode ∈ FP := by
  have halpha := machineCompose_mem_FP
    machineRationalCenterUpdateDimensionBits_mem_FP
    machineEllipsoidAlphaRawCode_mem_FP
  have hinput := machinePair_mem_FP halpha
    machineRationalCenterUpdateDisplacementCode_mem_FP
  simpa only [machineRationalCenterUpdateScaledDisplacementCode] using!
    machineCompose_mem_FP hinput machineRationalVectorScaleCode_mem_FP

theorem machineRationalEllipsoidCenterUpdateCode_mem_FP :
    machineRationalEllipsoidCenterUpdateCode ∈ FP := by
  have hpayload := machinePair_mem_FP
    machineRationalCenterUpdateCenterWord_mem_FP
    machineRationalCenterUpdateScaledDisplacementCode_mem_FP
  have hinput := machinePair_mem_FP
    machineRationalCenterUpdateDimensionUnary_mem_FP hpayload
  simpa only [machineRationalEllipsoidCenterUpdateCode] using!
    machineCompose_mem_FP hinput machineRationalVectorSubCode_mem_FP

/-! ## Exact semantics -/

theorem rationalEllipsoid_dimension_le_state_code_length {d : ℕ}
    (E : RationalEllipsoidState d) :
    d ≤ (rationalEllipsoidStateBinaryCode E).length := by
  have hlist := binaryListCode_listLength_le rationalEntryBinaryCode
    (List.ofFn E.center)
  have hcenter :
      (rationalFiniteVectorCode E.center).length ≤
        (rationalEllipsoidStateBinaryCode E).length := by
    let payload := pair (rationalFiniteVectorCode E.center)
      (rationalSquareMatrixRowsCode E.basis)
    have hfirst := machinePairFirst_length_le payload
    have hsecond : payload.length ≤
        (rationalEllipsoidStateBinaryCode E).length := by
      simpa only [payload, rationalEllipsoidStateBinaryCode,
        machinePairSecond_pair] using! machinePairSecond_length_le
          (rationalEllipsoidStateBinaryCode E)
    simpa only [payload, machinePairFirst_pair] using! hfirst.trans hsecond
  simpa only [rationalFiniteVectorCode, List.length_ofFn] using!
    hlist.trans hcenter

@[simp] theorem machineRationalCenterUpdateDimensionUnary_encode {d : ℕ}
    (E : RationalEllipsoidState d) (a : Fin d → ℚ) :
    machineRationalCenterUpdateDimensionUnary
        (pair (rationalEllipsoidStateBinaryCode E)
          (rationalFiniteVectorCode a)) =
      List.replicate d true := by
  rw [machineRationalCenterUpdateDimensionUnary]
  simp only [machineRationalCenterUpdateStateWord,
    machineRationalCenterUpdateDimensionBits,
    machinePairFirst_pair, machineRationalEllipsoidDimensionWord_encode]
  exact machineBoundedUnary_encode_of_le
    (rationalEllipsoidStateBinaryCode E) d
    (rationalEllipsoid_dimension_le_state_code_length E)

@[simp] theorem machineRationalCenterUpdatePulledBackCode_encode {d : ℕ}
    (E : RationalEllipsoidState d) (a : Fin d → ℚ) :
    machineRationalCenterUpdatePulledBackCode
        (pair (rationalEllipsoidStateBinaryCode E)
          (rationalFiniteVectorCode a)) =
      rationalFiniteVectorCode (rationalPulledBackNormal E a) := by
  rw [machineRationalCenterUpdatePulledBackCode]
  simp only [machineRationalCenterUpdateDimensionUnary_encode,
    machineRationalCenterUpdateBasisWord,
    machineRationalCenterUpdateStateWord, machinePairFirst_pair,
    machineRationalEllipsoidBasisWord_encode,
    machineRationalCenterUpdateCutWord, machinePairSecond_pair]
  change machineRationalTransposeMulVectorCode
      (rationalTransposeMulVectorCanonicalWord E.basis a) = _
  rw [machineRationalTransposeMulVectorCode_encode,
    rationalTransposeMulVector_eq_pulledBack]

@[simp] theorem machineRationalCenterUpdateNormalizedCode_encode {d : ℕ}
    (E : RationalEllipsoidState d) (a : Fin d → ℚ) :
    machineRationalCenterUpdateNormalizedCode
        (pair (rationalEllipsoidStateBinaryCode E)
          (rationalFiniteVectorCode a)) =
      rationalFiniteVectorCode
        (rationalNormalizedDirection (rationalPulledBackNormal E a)) := by
  rw [machineRationalCenterUpdateNormalizedCode,
    machineRationalCenterUpdatePulledBackCode_encode,
    machineRationalNormalizedDirectionCode_encode]

@[simp] theorem machineRationalCenterUpdateDisplacementCode_encode {d : ℕ}
    (E : RationalEllipsoidState d) (a : Fin d → ℚ) :
    machineRationalCenterUpdateDisplacementCode
        (pair (rationalEllipsoidStateBinaryCode E)
          (rationalFiniteVectorCode a)) =
      rationalFiniteVectorCode
        (rationalMatrixMulVector E.basis
          (rationalNormalizedDirection (rationalPulledBackNormal E a))) := by
  rw [machineRationalCenterUpdateDisplacementCode]
  simp only [machineRationalCenterUpdateDimensionUnary_encode,
    machineRationalCenterUpdateBasisWord,
    machineRationalCenterUpdateStateWord, machinePairFirst_pair,
    machineRationalEllipsoidBasisWord_encode,
    machineRationalCenterUpdateNormalizedCode_encode]
  change machineRationalMatrixMulVectorCode
      (rationalMatrixMulVectorCanonicalWord E.basis
        (rationalNormalizedDirection (rationalPulledBackNormal E a))) = _
  rw [machineRationalMatrixMulVectorCode_encode]

@[simp] theorem machineRationalCenterUpdateScaledDisplacementCode_encode
    {d : ℕ} (E : RationalEllipsoidState d) (a : Fin d → ℚ) :
    machineRationalCenterUpdateScaledDisplacementCode
        (pair (rationalEllipsoidStateBinaryCode E)
          (rationalFiniteVectorCode a)) =
      rationalFiniteVectorCode
        (rationalVectorScale (rationalEllipsoidAlpha d)
          (rationalMatrixMulVector E.basis
            (rationalNormalizedDirection
              (rationalPulledBackNormal E a)))) := by
  rw [machineRationalCenterUpdateScaledDisplacementCode]
  simp only [machineRationalCenterUpdateDimensionBits,
    machineRationalCenterUpdateStateWord, machinePairFirst_pair,
    machineRationalEllipsoidDimensionWord_encode,
    machineEllipsoidAlphaRawCode_encode,
    machineRationalCenterUpdateDisplacementCode_encode,
    machineRationalVectorScaleCode_encode, rawEllipsoidAlpha_value]

theorem rationalEllipsoidCentralUpdate_center_eq {d : ℕ}
    (E : RationalEllipsoidState d) (a : Fin d → ℚ) :
    (rationalEllipsoidCentralUpdate E a).center =
      rationalVectorSub E.center
        (rationalVectorScale (rationalEllipsoidAlpha d)
          (rationalMatrixMulVector E.basis
            (rationalNormalizedDirection
              (rationalPulledBackNormal E a)))) := by
  funext i
  simp [rationalEllipsoidCentralUpdate, rationalVectorSub,
    rationalVectorScale, rationalMatrixMulVector,
    rationalNormalizedDirection, cutL1Scale]

@[simp] theorem machineRationalEllipsoidCenterUpdateCode_encode {d : ℕ}
    (E : RationalEllipsoidState d) (a : Fin d → ℚ) :
    machineRationalEllipsoidCenterUpdateCode
        (pair (rationalEllipsoidStateBinaryCode E)
          (rationalFiniteVectorCode a)) =
      rationalFiniteVectorCode (rationalEllipsoidCentralUpdate E a).center := by
  rw [machineRationalEllipsoidCenterUpdateCode]
  simp only [machineRationalCenterUpdateDimensionUnary_encode,
    machineRationalCenterUpdateCenterWord,
    machineRationalCenterUpdateStateWord, machinePairFirst_pair,
    machineRationalEllipsoidCenterWord_encode,
    machineRationalCenterUpdateScaledDisplacementCode_encode]
  change machineRationalVectorSubCode
      (rationalVectorSubCanonicalWord E.center
        (rationalVectorScale (rationalEllipsoidAlpha d)
          (rationalMatrixMulVector E.basis
            (rationalNormalizedDirection
              (rationalPulledBackNormal E a))))) = _
  rw [machineRationalVectorSubCode_encode,
    ← rationalEllipsoidCentralUpdate_center_eq]

end BeyondBethe
