/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.MachineBetheFeasibilitySemantics
import LeanPool.BeyondBethe.BeyondBethe.RationalEncodingBounds
import Mathlib.Tactic

/-!
# Ordinary binary bounds for scheduled ellipsoid states

The semantic feasibility proof bounds magnitudes and denominators.  The
finite-word loop needs the corresponding bound on its concrete, nested binary
code.  This file supplies that elementary bridge without changing encodings.
-/

namespace BeyondBethe

open Complexity
open scoped BigOperators

def rationalEntryMachineCodeBound (K P : ℕ) : ℕ :=
  8 + 2 * K + 4 * P

def rationalVectorMachineCodeBound (d K P : ℕ) : ℕ :=
  d * (2 * rationalEntryMachineCodeBound K P + 2)

def rationalMatrixMachineCodeBound (d K P : ℕ) : ℕ :=
  d * (2 * rationalVectorMachineCodeBound d K P + 2)

def rationalEllipsoidMachineCodeBound (d K P : ℕ) : ℕ :=
  2 * (d + 1) +
    2 * (2 * rationalVectorMachineCodeBound d K P +
      2 * rationalMatrixMachineCodeBound d K P + 2) + 2

theorem integerBinaryCode_length_le_of_natAbs_le_two_pow
    {z : ℤ} {K : ℕ} (h : z.natAbs ≤ 2 ^ K) :
    (integerBinaryCode z).length ≤ K + 2 := by
  cases z with
  | ofNat n =>
      have hn : n ≤ 2 ^ K := by simpa using h
      have hs := nat_size_le_succ_of_le_two_pow hn
      have hs' : n.bits.length ≤ K + 1 := by
        simpa only [Nat.size_eq_bits_len] using hs
      simp only [integerBinaryCode, List.length_cons]
      omega
  | negSucc n =>
      have hn : n ≤ 2 ^ K := by
        simp only [Int.natAbs_negSucc] at h
        omega
      have hs := nat_size_le_succ_of_le_two_pow hn
      have hs' : n.bits.length ≤ K + 1 := by
        simpa only [Nat.size_eq_bits_len] using hs
      simp only [integerBinaryCode, List.length_cons]
      omega

theorem rationalEntryBinaryCode_length_le_of_abs_and_den_bounds
    {q : ℚ} {K P : ℕ}
    (habs : abs q ≤ (2 : ℚ) ^ K)
    (hden : q.den ≤ 2 ^ P) :
    (rationalEntryBinaryCode q).length ≤
      rationalEntryMachineCodeBound K P := by
  have hnum := rat_num_natAbs_le_of_abs_and_den_bounds habs hden
  have hnumCode := integerBinaryCode_length_le_of_natAbs_le_two_pow hnum
  have hdenSize := nat_size_le_succ_of_le_two_pow hden
  rw [rationalEntryBinaryCode, pair_length]
  rw [← Nat.size_eq_bits_len] at hdenSize
  simp only [rationalEntryMachineCodeBound]
  omega

theorem rationalFiniteVectorCode_length_le_of_bounds {d K P : ℕ}
    (v : Fin d → ℚ)
    (habs : ∀ i, abs (v i) ≤ (2 : ℚ) ^ K)
    (hden : ∀ i, (v i).den ≤ 2 ^ P) :
    (rationalFiniteVectorCode v).length ≤
      rationalVectorMachineCodeBound d K P := by
  rw [rationalFiniteVectorCode, binaryListCode_length_eq_sum,
    List.map_ofFn, List.sum_ofFn]
  have hsum : (∑ i : Fin d,
      (2 * (rationalEntryBinaryCode (v i)).length + 2)) ≤
      ∑ _i : Fin d, (2 * rationalEntryMachineCodeBound K P + 2) := by
    apply Finset.sum_le_sum
    intro i _
    have hi := rationalEntryBinaryCode_length_le_of_abs_and_den_bounds
      (habs i) (hden i)
    omega
  simpa only [rationalVectorMachineCodeBound, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.mul_comm] using hsum

theorem rationalSquareMatrixRowsCode_length_le_of_bounds {d K P : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ)
    (habs : ∀ i j, abs (A i j) ≤ (2 : ℚ) ^ K)
    (hden : ∀ i j, (A i j).den ≤ 2 ^ P) :
    (rationalSquareMatrixRowsCode A).length ≤
      rationalMatrixMachineCodeBound d K P := by
  rw [rationalSquareMatrixRowsCode, binaryListCode_length_eq_sum,
    rationalMatrixRows, List.map_ofFn, List.sum_ofFn]
  have hsum : (∑ i : Fin d,
      (2 * (binaryListCode rationalEntryBinaryCode
        (List.ofFn (A i))).length + 2)) ≤
      ∑ _i : Fin d, (2 * rationalVectorMachineCodeBound d K P + 2) := by
    apply Finset.sum_le_sum
    intro i _
    have hi := rationalFiniteVectorCode_length_le_of_bounds
      (A i) (habs i) (hden i)
    simp only [rationalFiniteVectorCode] at hi
    omega
  simpa only [rationalMatrixMachineCodeBound, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.mul_comm] using hsum

theorem nat_bits_length_le_add_one (d : ℕ) :
    d.bits.length ≤ d + 1 := by
  cases d with
  | zero => simp
  | succ k =>
      rw [Nat.size_eq_bits_len, Nat.size_le]
      exact Nat.lt_two_pow_self.trans
        (Nat.pow_lt_pow_right (by decide) (by omega))

theorem rationalEllipsoidStateBinaryCode_length_le_of_bounds {d K P : ℕ}
    (E : RationalEllipsoidState d)
    (hcenterAbs : ∀ i, abs (E.center i) ≤ (2 : ℚ) ^ K)
    (hcenterDen : ∀ i, (E.center i).den ≤ 2 ^ P)
    (hbasisAbs : ∀ i j, abs (E.basis i j) ≤ (2 : ℚ) ^ K)
    (hbasisDen : ∀ i j, (E.basis i j).den ≤ 2 ^ P) :
    (rationalEllipsoidStateBinaryCode E).length ≤
      rationalEllipsoidMachineCodeBound d K P := by
  have hc := rationalFiniteVectorCode_length_le_of_bounds
    E.center hcenterAbs hcenterDen
  have hB := rationalSquareMatrixRowsCode_length_le_of_bounds
    E.basis hbasisAbs hbasisDen
  have hd := nat_bits_length_le_add_one d
  rw [rationalEllipsoidStateBinaryCode]
  simp only [pair_length, rationalEllipsoidMachineCodeBound]
  omega

theorem scheduledRoundedEllipsoid_stateCode_length_le
    {d K p : ℕ} (hd : 0 < d) (U : RationalEllipsoidState d)
    (hM : rationalStateAbsBound (scheduledRoundedEllipsoid p U) ≤
      (2 : ℚ) ^ K) :
    (rationalEllipsoidStateBinaryCode
      (scheduledRoundedEllipsoid p U)).length ≤
      rationalEllipsoidMachineCodeBound d K (p + 10 + 4 * d) := by
  apply rationalEllipsoidStateBinaryCode_length_le_of_bounds
  · intro i
    exact (abs_center_entry_lt_rationalStateAbsBound
      (scheduledRoundedEllipsoid p U) i).le.trans hM
  · intro i
    have hden := inflatedDyadicRound_center_den_le (p := p)
      (roundedEllipsoidInflation d) U i
    have hp : p ≤ p + 10 + 4 * d := by omega
    exact hden.trans (Nat.pow_le_pow_right (by decide) hp)
  · intro i j
    exact (abs_basis_entry_lt_rationalStateAbsBound
      (scheduledRoundedEllipsoid p U) i j).le.trans hM
  · intro i j
    exact inflatedDyadicRound_basis_den_le hd U i j

theorem scheduledRoundedEllipsoidCentralUpdate_stateCode_length_le
    {d K p : ℕ} (hd : 0 < d) (E : RationalEllipsoidState d)
    (a : Fin d → ℚ)
    (hM : rationalStateAbsBound
      (scheduledRoundedEllipsoidCentralUpdate p E a) ≤ (2 : ℚ) ^ K) :
    (rationalEllipsoidStateBinaryCode
      (scheduledRoundedEllipsoidCentralUpdate p E a)).length ≤
      rationalEllipsoidMachineCodeBound d K (p + 10 + 4 * d) := by
  exact scheduledRoundedEllipsoid_stateCode_length_le hd
    (rationalEllipsoidCentralUpdate E a) hM

end BeyondBethe
