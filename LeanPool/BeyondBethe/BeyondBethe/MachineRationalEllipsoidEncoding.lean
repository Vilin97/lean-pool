/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineEncoding
import LeanPool.BeyondBethe.BeyondBethe.MachineFPBasics
import LeanPool.BeyondBethe.BeyondBethe.RationalFeasibility

/-! # Machine Rational Ellipsoid Encoding -/

namespace BeyondBethe

open Complexity

/-!
# Canonical finite-word encodings for rational ellipsoid feasibility

The optimizer stores a center vector and a square basis matrix.  This file
fixes their ordinary binary representation before any update or oracle
machine is introduced.  Every list is right-nested with `binaryListCode`, and
every rational entry is in the unique reduced representation
`rationalEntryBinaryCode`.
-/

/-- Canonical word for a fixed-length rational vector. -/
def rationalFiniteVectorCode {d : ℕ} (v : Fin d → ℚ) : List Bool :=
  binaryListCode rationalEntryBinaryCode (List.ofFn v)

theorem rationalFiniteVectorCode_injective {d : ℕ} :
    Function.Injective (@rationalFiniteVectorCode d) := by
  intro v w h
  have hlists : List.ofFn v = List.ofFn w :=
    (binaryListCode_injective rationalEntryBinaryCode_injective) h
  exact List.ofFn_injective hlists

/-- Canonical word for a fixed-size rational square matrix, without a second
copy of the dimension. -/
def rationalSquareMatrixRowsCode {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) : List Bool :=
  binaryListCode (binaryListCode rationalEntryBinaryCode)
    (rationalMatrixRows A)

theorem rationalSquareMatrixRowsCode_injective {d : ℕ} :
    Function.Injective (@rationalSquareMatrixRowsCode d) := by
  intro A B h
  apply rationalMatrixRows_injective
  exact (binaryListCode_injective
    (binaryListCode_injective rationalEntryBinaryCode_injective)) h

/-- Dimension followed by center and basis.  Keeping the dimension in the
word makes the representation self-contained for a single uniform machine. -/
def rationalEllipsoidStateBinaryCode {d : ℕ}
    (E : RationalEllipsoidState d) : List Bool :=
  pair d.bits
    (pair (rationalFiniteVectorCode E.center)
      (rationalSquareMatrixRowsCode E.basis))

theorem rationalEllipsoidStateBinaryCode_injective_fixed {d : ℕ} :
    Function.Injective (@rationalEllipsoidStateBinaryCode d) := by
  intro E F h
  obtain ⟨_hd, hpayload⟩ := pair_inj h
  obtain ⟨hcenter, hbasis⟩ := pair_inj hpayload
  cases E with
  | mk Ec Eb =>
      cases F with
      | mk Fc Fb =>
          simp only at hcenter hbasis ⊢
          have hc : Ec = Fc := rationalFiniteVectorCode_injective hcenter
          have hb : Eb = Fb :=
            rationalSquareMatrixRowsCode_injective hbasis
          cases hc
          cases hb
          rfl

/-- A dimension-indexed ellipsoid state, used only to state global
injectivity of the self-contained word representation. -/
abbrev RationalEllipsoidInput := Σ d : ℕ, RationalEllipsoidState d

def rationalEllipsoidInputBinaryCode :
    RationalEllipsoidInput → List Bool
  | ⟨_d, E⟩ => rationalEllipsoidStateBinaryCode E

theorem rationalEllipsoidInputBinaryCode_injective :
    Function.Injective rationalEllipsoidInputBinaryCode := by
  intro x y h
  obtain ⟨d, E⟩ := x
  obtain ⟨e, F⟩ := y
  simp only [rationalEllipsoidInputBinaryCode,
    rationalEllipsoidStateBinaryCode] at h
  obtain ⟨hde, hpayload⟩ := pair_inj h
  have hde' : d = e := natBits_injective hde
  subst e
  have hcode : rationalEllipsoidStateBinaryCode E =
      rationalEllipsoidStateBinaryCode F := by
    simp only [rationalEllipsoidStateBinaryCode]
    exact congrArg (pair d.bits) hpayload
  have hEF : E = F :=
    rationalEllipsoidStateBinaryCode_injective_fixed hcode
  subst F
  rfl

/-- Tag and payload encoding of an oracle response. -/
def rationalCentralOracleResponseBinaryCode {d : ℕ} :
    RationalCentralOracleResponse d → List Bool
  | .accept => pair [false] []
  | .cut a => pair [true] (rationalFiniteVectorCode a)

theorem rationalCentralOracleResponseBinaryCode_injective {d : ℕ} :
    Function.Injective (@rationalCentralOracleResponseBinaryCode d) := by
  intro r s h
  cases r with
  | accept =>
      cases s with
      | accept => rfl
      | cut a =>
          have htag := congrArg machinePairFirst h
          simp [rationalCentralOracleResponseBinaryCode] at htag
  | cut a =>
      cases s with
      | accept =>
          have htag := congrArg machinePairFirst h
          simp [rationalCentralOracleResponseBinaryCode] at htag
      | cut b =>
          have hpayload := congrArg machinePairSecond h
          simp only [rationalCentralOracleResponseBinaryCode,
            machinePairSecond_pair] at hpayload
          exact congrArg RationalCentralOracleResponse.cut
            (rationalFiniteVectorCode_injective hpayload)

/-- Tag and payload encoding of a bounded feasibility result. -/
def rationalFeasibilityResultBinaryCode {d : ℕ} :
    RationalFeasibilityResult d → List Bool
  | .accepted q => pair [false] (rationalFiniteVectorCode q)
  | .exhausted E => pair [true] (rationalEllipsoidStateBinaryCode E)

theorem rationalFeasibilityResultBinaryCode_injective {d : ℕ} :
    Function.Injective (@rationalFeasibilityResultBinaryCode d) := by
  intro r s h
  cases r with
  | accepted q =>
      cases s with
      | accepted z =>
          have hpayload := congrArg machinePairSecond h
          simp only [rationalFeasibilityResultBinaryCode,
            machinePairSecond_pair] at hpayload
          exact congrArg RationalFeasibilityResult.accepted
            (rationalFiniteVectorCode_injective hpayload)
      | exhausted E =>
          have htag := congrArg machinePairFirst h
          simp [rationalFeasibilityResultBinaryCode] at htag
  | exhausted E =>
      cases s with
      | accepted q =>
          have htag := congrArg machinePairFirst h
          simp [rationalFeasibilityResultBinaryCode] at htag
      | exhausted F =>
          have hpayload := congrArg machinePairSecond h
          simp only [rationalFeasibilityResultBinaryCode,
            machinePairSecond_pair] at hpayload
          exact congrArg RationalFeasibilityResult.exhausted
            (rationalEllipsoidStateBinaryCode_injective_fixed hpayload)

/-! ## Polynomial-time field accessors -/

def machineRationalEllipsoidDimensionWord (word : List Bool) : List Bool :=
  machinePairFirst word

def machineRationalEllipsoidPayloadWord (word : List Bool) : List Bool :=
  machinePairSecond word

def machineRationalEllipsoidCenterWord (word : List Bool) : List Bool :=
  machinePairFirst (machineRationalEllipsoidPayloadWord word)

def machineRationalEllipsoidBasisWord (word : List Bool) : List Bool :=
  machinePairSecond (machineRationalEllipsoidPayloadWord word)

theorem machineRationalEllipsoidDimensionWord_mem_FP :
    machineRationalEllipsoidDimensionWord ∈ FP :=
  machinePairFirst_mem_FP

theorem machineRationalEllipsoidPayloadWord_mem_FP :
    machineRationalEllipsoidPayloadWord ∈ FP :=
  machinePairSecond_mem_FP

theorem machineRationalEllipsoidCenterWord_mem_FP :
    machineRationalEllipsoidCenterWord ∈ FP := by
  simpa only [machineRationalEllipsoidCenterWord] using!
    machineCompose_mem_FP machineRationalEllipsoidPayloadWord_mem_FP
      machinePairFirst_mem_FP

theorem machineRationalEllipsoidBasisWord_mem_FP :
    machineRationalEllipsoidBasisWord ∈ FP := by
  simpa only [machineRationalEllipsoidBasisWord] using!
    machineCompose_mem_FP machineRationalEllipsoidPayloadWord_mem_FP
      machinePairSecond_mem_FP

@[simp] theorem machineRationalEllipsoidDimensionWord_encode {d : ℕ}
    (E : RationalEllipsoidState d) :
    machineRationalEllipsoidDimensionWord
        (rationalEllipsoidStateBinaryCode E) = d.bits := by
  simp [machineRationalEllipsoidDimensionWord,
    rationalEllipsoidStateBinaryCode]

@[simp] theorem machineRationalEllipsoidCenterWord_encode {d : ℕ}
    (E : RationalEllipsoidState d) :
    machineRationalEllipsoidCenterWord
        (rationalEllipsoidStateBinaryCode E) =
      rationalFiniteVectorCode E.center := by
  simp [machineRationalEllipsoidCenterWord,
    machineRationalEllipsoidPayloadWord,
    rationalEllipsoidStateBinaryCode]

@[simp] theorem machineRationalEllipsoidBasisWord_encode {d : ℕ}
    (E : RationalEllipsoidState d) :
    machineRationalEllipsoidBasisWord
        (rationalEllipsoidStateBinaryCode E) =
      rationalSquareMatrixRowsCode E.basis := by
  simp [machineRationalEllipsoidBasisWord,
    machineRationalEllipsoidPayloadWord,
    rationalEllipsoidStateBinaryCode]

def machineRationalTaggedResultTag (word : List Bool) : List Bool :=
  machinePairFirst word

def machineRationalTaggedResultPayload (word : List Bool) : List Bool :=
  machinePairSecond word

theorem machineRationalTaggedResultTag_mem_FP :
    machineRationalTaggedResultTag ∈ FP :=
  machinePairFirst_mem_FP

theorem machineRationalTaggedResultPayload_mem_FP :
    machineRationalTaggedResultPayload ∈ FP :=
  machinePairSecond_mem_FP

end BeyondBethe
