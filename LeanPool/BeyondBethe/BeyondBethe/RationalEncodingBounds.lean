/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.RoundedEllipsoidIterationBounds
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-! # Rational Encoding Bounds -/

namespace BeyondBethe

open Complexity

/-!
# Upper bounds for the canonical rational encoding

The algorithm uses Complexitylib's parenthesized binary `DataEncode`
serialization.  These lemmas give explicit upper bounds for that exact
encoding, rather than appealing to an informal notion of rational bit size.
-/

theorem bool_dataEncode_size_le_four (b : Bool) :
    (DataEncode.encode b).size ≤ 4 := by
  cases b <;> norm_num [DataEncode.encode, Data.size]

theorem nat_encodedBitLength_le (n : ℕ) :
    encodedBitLength ℕ n ≤ 2 + 4 * n.size := by
  rw [encodedBitLength_eq_dataSize]
  change (Data.l (n.bits.map fun b ↦ DataEncode.encode b)).size ≤ _
  rw [Data.size]
  simp only [List.map_map]
  have hsum :
      ((n.bits.map fun b ↦ (DataEncode.encode b).size).sum) ≤
        4 * n.bits.length := by
    induction n.bits with
    | nil => simp
    | cons b bits ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        have hb := bool_dataEncode_size_le_four b
        omega
  have hadd := Nat.add_le_add_left hsum 2
  simpa only [Function.comp_apply, Nat.size_eq_bits_len] using hadd

theorem integer_encodedBitLength_le (z : ℤ) :
    encodedBitLength ℤ z ≤ 8 + 4 * z.natAbs.size := by
  rw [encodedBitLength_eq_dataSize]
  change (DataEncode.encode (integerPayload z)).size ≤ _
  rw [show DataEncode.encode (integerPayload z) =
      Data.l [DataEncode.encode (integerPayload z).1,
        DataEncode.encode (integerPayload z).2] by
      exact DataEncode_pair _ _]
  simp only [Data.size, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]
  have hb := bool_dataEncode_size_le_four (integerPayload z).1
  have hn := nat_encodedBitLength_le (integerPayload z).2
  rw [encodedBitLength_eq_dataSize] at hn
  have hn' : (DataEncode.encode (integerPayload z).2).size ≤
      2 + 4 * z.natAbs.size := by
    simpa only [integerPayload_snd] using hn
  omega

theorem rational_encodedBitLength_le (q : ℚ) :
    encodedBitLength ℚ q ≤
      12 + 4 * (q.num.natAbs.size + q.den.size) := by
  rw [encodedBitLength_eq_dataSize]
  change (DataEncode.encode (rationalPayload q)).size ≤ _
  rw [show DataEncode.encode (rationalPayload q) =
      Data.l [DataEncode.encode q.num, DataEncode.encode q.den] by
      simpa only [rationalPayload] using DataEncode_pair q.num q.den]
  simp only [Data.size, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]
  have hz := integer_encodedBitLength_le q.num
  have hd := nat_encodedBitLength_le q.den
  rw [encodedBitLength_eq_dataSize] at hz hd
  omega

theorem one_le_rational_encodedBitLength (q : ℚ) :
    1 ≤ encodedBitLength ℚ q := by
  have h := denominator_encodedBitLength_lt_rational q
  omega

theorem nat_size_le_succ_of_le_two_pow {n P : ℕ}
    (h : n ≤ 2 ^ P) : n.size ≤ P + 1 := by
  rw [Nat.size_le]
  calc
    n ≤ 2 ^ P := h
    _ < 2 ^ (P + 1) := by
      rw [pow_succ]
      have hp : 0 < 2 ^ P := by positivity
      omega

theorem rat_abs_eq_numNatAbs_div_den (q : ℚ) :
    abs q = (q.num.natAbs : ℚ) / q.den := by
  rw [Rat.abs_def, Rat.divInt_eq_div]
  norm_num

theorem rat_num_natAbs_le_of_abs_and_den_bounds
    {q : ℚ} {K P : ℕ}
    (habs : abs q ≤ (2 : ℚ) ^ K)
    (hden : q.den ≤ 2 ^ P) :
    q.num.natAbs ≤ 2 ^ (K + P) := by
  have hdenQ : (q.den : ℚ) ≤ (2 : ℚ) ^ P := by exact_mod_cast hden
  have hnumQ : (q.num.natAbs : ℚ) ≤
      (2 : ℚ) ^ K * q.den := by
    rw [rat_abs_eq_numNatAbs_div_den] at habs
    rw [div_le_iff₀ (by positivity : (0 : ℚ) < q.den)] at habs
    simpa only [mul_comm] using habs
  have hboundQ : (q.num.natAbs : ℚ) ≤ (2 : ℚ) ^ (K + P) := by
    calc
      (q.num.natAbs : ℚ) ≤ (2 : ℚ) ^ K * q.den := hnumQ
      _ ≤ (2 : ℚ) ^ K * (2 : ℚ) ^ P :=
        mul_le_mul_of_nonneg_left hdenQ (by positivity)
      _ = (2 : ℚ) ^ (K + P) := by rw [pow_add]
  exact_mod_cast hboundQ

theorem rational_encodedBitLength_le_of_abs_and_den_bounds
    {q : ℚ} {K P : ℕ}
    (habs : abs q ≤ (2 : ℚ) ^ K)
    (hden : q.den ≤ 2 ^ P) :
    encodedBitLength ℚ q ≤ 20 + 4 * K + 8 * P := by
  have hnum := rat_num_natAbs_le_of_abs_and_den_bounds habs hden
  have hnumSize := nat_size_le_succ_of_le_two_pow hnum
  have hdenSize := nat_size_le_succ_of_le_two_pow hden
  have hencode := rational_encodedBitLength_le q
  omega

theorem dyadicFloor_den_le (p : ℕ) (q : ℚ) :
    (dyadicFloor p q).den ≤ 2 ^ p := by
  let z : ℤ := Int.floor (q * (2 : ℚ) ^ p)
  have heq : dyadicFloor p q = Rat.divInt z (2 ^ p : ℤ) := by
    rw [dyadicFloor]
    dsimp only [z]
    rw [show (2 : ℚ) ^ p = ((2 ^ p : ℕ) : ℚ) by norm_num,
      ← Rat.intCast_div_eq_divInt]
    norm_num
  have hdvdZ : (((dyadicFloor p q).den : ℕ) : ℤ) ∣ (2 ^ p : ℤ) := by
    rw [heq]
    exact Rat.den_dvd z (2 ^ p : ℤ)
  have hdvd : (dyadicFloor p q).den ∣ 2 ^ p := by
    exact_mod_cast hdvdZ
  exact Nat.le_of_dvd (by positivity) hdvd

theorem abs_dyadicFloor_le_two_pow_succ {p K : ℕ} {q : ℚ}
    (hq : abs q ≤ (2 : ℚ) ^ K) :
    abs (dyadicFloor p q) ≤ (2 : ℚ) ^ (K + 1) := by
  have hround := abs_dyadicFloor_le p q
  have hmesh := dyadicMesh_le_one p
  have hone : (1 : ℚ) ≤ (2 : ℚ) ^ K := one_le_pow₀ (by norm_num)
  rw [pow_succ]
  linarith

/-- Exact encoding bound for the executable dyadic-floor primitive. -/
theorem dyadicFloor_encodedBitLength_le {p K : ℕ} {q : ℚ}
    (hq : abs q ≤ (2 : ℚ) ^ K) :
    encodedBitLength ℚ (dyadicFloor p q) ≤
      24 + 4 * K + 8 * p := by
  have h := rational_encodedBitLength_le_of_abs_and_den_bounds
    (abs_dyadicFloor_le_two_pow_succ (p := p) hq)
    (dyadicFloor_den_le p q)
  omega

theorem roundedEllipsoidInflationFactor_den_dvd (d : ℕ) :
    (1 + roundedEllipsoidInflation d).den ∣ 1024 * d ^ 4 := by
  let N := 1024 * d ^ 4
  have heq : roundedEllipsoidInflation d = Rat.divInt 1 (N : ℤ) := by
    rw [roundedEllipsoidInflation]
    dsimp only [N]
    rw [← Rat.intCast_div_eq_divInt]
    norm_num
  have hdenZ : (((roundedEllipsoidInflation d).den : ℕ) : ℤ) ∣ (N : ℤ) := by
    rw [heq]
    exact Rat.den_dvd 1 (N : ℤ)
  have hden : (roundedEllipsoidInflation d).den ∣ N := by
    exact_mod_cast hdenZ
  have hadd : (1 + roundedEllipsoidInflation d).den ∣
      (roundedEllipsoidInflation d).den := by
    simpa using Rat.add_den_dvd (1 : ℚ) (roundedEllipsoidInflation d)
  exact hadd.trans hden

theorem roundedEllipsoidInflationFactor_den_le {d : ℕ} (hd : 0 < d) :
    (1 + roundedEllipsoidInflation d).den ≤ 1024 * d ^ 4 :=
  Nat.le_of_dvd (by positivity) (roundedEllipsoidInflationFactor_den_dvd d)

theorem roundedEllipsoidInflationDenominator_le_two_pow (d : ℕ) :
    (1024 * d ^ 4 : ℕ) ≤ 2 ^ (10 + 4 * d) := by
  have hdq := natCast_le_two_pow_self d
  have hd4 : (d : ℚ) ^ 4 ≤ ((2 : ℚ) ^ d) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hdq 4
  have hq : ((1024 * d ^ 4 : ℕ) : ℚ) ≤
      ((2 ^ (10 + 4 * d) : ℕ) : ℚ) := by
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    calc
      (1024 : ℚ) * d ^ 4 ≤ 1024 * ((2 : ℚ) ^ d) ^ 4 :=
        mul_le_mul_of_nonneg_left hd4 (by norm_num)
      _ = (2 : ℚ) ^ (10 + 4 * d) := by
        rw [show (1024 : ℚ) = 2 ^ 10 by norm_num, ← pow_mul, ← pow_add]
        congr 1
        omega
  exact_mod_cast hq

theorem inflatedDyadicRound_center_den_le {d p : ℕ} (η : ℚ)
    (U : RationalEllipsoidState d) (i : Fin d) :
    ((inflatedDyadicRound p η U).center i).den ≤ 2 ^ p := by
  change (dyadicFloor p (U.center i)).den ≤ 2 ^ p
  exact dyadicFloor_den_le p (U.center i)

theorem inflatedDyadicRound_basis_den_le {d p : ℕ} (hd : 0 < d)
    (U : RationalEllipsoidState d) (i j : Fin d) :
    ((inflatedDyadicRound p (roundedEllipsoidInflation d) U).basis i j).den ≤
      2 ^ (p + 10 + 4 * d) := by
  let f : ℚ := 1 + roundedEllipsoidInflation d
  let q : ℚ := dyadicFloor p (U.basis i j)
  have hdiv : (f * q).den ∣ f.den * q.den := Rat.mul_den_dvd f q
  have hprodPos : 0 < f.den * q.den := by positivity
  have hden : (f * q).den ≤ f.den * q.den := Nat.le_of_dvd hprodPos hdiv
  have hf : f.den ≤ 1024 * d ^ 4 := by
    dsimp only [f]
    exact roundedEllipsoidInflationFactor_den_le hd
  have hq : q.den ≤ 2 ^ p := by
    dsimp only [q]
    exact dyadicFloor_den_le p (U.basis i j)
  have hN := roundedEllipsoidInflationDenominator_le_two_pow d
  change (f * q).den ≤ 2 ^ (p + 10 + 4 * d)
  calc
    (f * q).den ≤ f.den * q.den := hden
    _ ≤ (1024 * d ^ 4) * 2 ^ p := Nat.mul_le_mul hf hq
    _ ≤ 2 ^ (10 + 4 * d) * 2 ^ p := Nat.mul_le_mul_right _ hN
    _ = 2 ^ (p + 10 + 4 * d) := by
      rw [← pow_add]
      congr 1
      omega

theorem adaptiveRoundedEllipsoid_center_den_le {d : ℕ}
    (U : RationalEllipsoidState d) (i : Fin d) :
    ((adaptiveRoundedEllipsoid U).center i).den ≤
      2 ^ roundedEllipsoidPrecision U := by
  exact inflatedDyadicRound_center_den_le
    (roundedEllipsoidInflation d) U i

theorem adaptiveRoundedEllipsoid_basis_den_le {d : ℕ} (hd : 0 < d)
    (U : RationalEllipsoidState d) (i j : Fin d) :
    ((adaptiveRoundedEllipsoid U).basis i j).den ≤
      2 ^ (roundedEllipsoidPrecision U + 10 + 4 * d) := by
  exact inflatedDyadicRound_basis_den_le hd U i j

theorem abs_center_entry_lt_rationalCenterAbsBound {d : ℕ}
    (c : Fin d → ℚ) (i : Fin d) :
    abs (c i) < rationalCenterAbsBound c := by
  rw [rationalCenterAbsBound]
  have hi : abs (c i) ≤ ∑ j, abs (c j) :=
    Finset.single_le_sum (fun j _ ↦ abs_nonneg (c j))
      (Finset.mem_univ i)
  linarith

theorem abs_center_entry_lt_rationalStateAbsBound {d : ℕ}
    (E : RationalEllipsoidState d) (i : Fin d) :
    abs (E.center i) < rationalStateAbsBound E := by
  rw [rationalStateAbsBound]
  exact (abs_center_entry_lt_rationalCenterAbsBound E.center i).trans_le
    (le_add_of_nonneg_right (by
      linarith [rationalMatrixAbsBound_one_le E.basis]))

theorem abs_basis_entry_lt_rationalStateAbsBound {d : ℕ}
    (E : RationalEllipsoidState d) (i j : Fin d) :
    abs (E.basis i j) < rationalStateAbsBound E := by
  rw [rationalStateAbsBound]
  exact (abs_entry_lt_rationalMatrixAbsBound E.basis i j).trans_le
    (le_add_of_nonneg_left (by
      linarith [rationalCenterAbsBound_one_le E.center]))

theorem adaptiveRoundedEllipsoid_center_encodedBitLength_le
    {d K P : ℕ} (U : RationalEllipsoidState d)
    (hM : rationalStateAbsBound (adaptiveRoundedEllipsoid U) ≤ (2 : ℚ) ^ K)
    (hp : roundedEllipsoidPrecision U ≤ P) (i : Fin d) :
    encodedBitLength ℚ ((adaptiveRoundedEllipsoid U).center i) ≤
      20 + 4 * K + 8 * P := by
  have habs : abs ((adaptiveRoundedEllipsoid U).center i) ≤ (2 : ℚ) ^ K :=
    (abs_center_entry_lt_rationalStateAbsBound
      (adaptiveRoundedEllipsoid U) i).le.trans hM
  have hden0 := adaptiveRoundedEllipsoid_center_den_le U i
  have hpow : 2 ^ roundedEllipsoidPrecision U ≤ 2 ^ P :=
    Nat.pow_le_pow_right (by decide) hp
  exact rational_encodedBitLength_le_of_abs_and_den_bounds habs
    (hden0.trans hpow)

theorem adaptiveRoundedEllipsoid_basis_encodedBitLength_le
    {d K P : ℕ} (hd : 0 < d) (U : RationalEllipsoidState d)
    (hM : rationalStateAbsBound (adaptiveRoundedEllipsoid U) ≤ (2 : ℚ) ^ K)
    (hp : roundedEllipsoidPrecision U ≤ P) (i j : Fin d) :
    encodedBitLength ℚ ((adaptiveRoundedEllipsoid U).basis i j) ≤
      100 + 4 * K + 8 * P + 32 * d := by
  have habs : abs ((adaptiveRoundedEllipsoid U).basis i j) ≤ (2 : ℚ) ^ K :=
    (abs_basis_entry_lt_rationalStateAbsBound
      (adaptiveRoundedEllipsoid U) i j).le.trans hM
  have hden0 := adaptiveRoundedEllipsoid_basis_den_le hd U i j
  have hexp : roundedEllipsoidPrecision U + 10 + 4 * d ≤
      P + 10 + 4 * d := by omega
  have hpow : 2 ^ (roundedEllipsoidPrecision U + 10 + 4 * d) ≤
      2 ^ (P + 10 + 4 * d) := Nat.pow_le_pow_right (by decide) hexp
  have h := rational_encodedBitLength_le_of_abs_and_den_bounds habs
    (hden0.trans hpow)
  omega

/-- Canonical payload for a fixed-dimensional ellipsoid state. -/
def rationalEllipsoidStatePayload {d : ℕ} (E : RationalEllipsoidState d) :
    List ℚ × List (List ℚ) :=
  (List.ofFn E.center, rationalMatrixRows E.basis)

def rationalEllipsoidStateEncodedBitLength {d : ℕ}
    (E : RationalEllipsoidState d) : ℕ :=
  encodedBitLength (List ℚ × List (List ℚ))
    (rationalEllipsoidStatePayload E)

theorem dataEncode_list_ofFn_size {d : ℕ} {α : Type}
    [DataEncode α] (x : Fin d → α) :
    (DataEncode.encode (List.ofFn x)).size =
      2 + ∑ i, (DataEncode.encode (x i)).size := by
  change (Data.l ((List.ofFn x).map DataEncode.encode)).size = _
  rw [Data.size]
  simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]

theorem rationalMatrixInput_encodedBitLength_eq {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    encodedBitLength RationalMatrixInput ⟨n, A⟩ =
      4 + encodedBitLength ℕ n + 2 * n +
        ∑ i, ∑ j, encodedBitLength ℚ (A i j) := by
  rw [encodedBitLength_eq_dataSize]
  change (DataEncode.encode (rationalMatrixInputPayload ⟨n, A⟩)).size = _
  simp only [rationalMatrixInputPayload, DataEncode_pair, Data.size,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    rationalMatrixRows, encodedBitLength_eq_dataSize]
  rw [dataEncode_list_ofFn_size]
  simp_rw [dataEncode_list_ofFn_size]
  have htwo : (∑ _i : Fin n, (2 : ℕ)) = 2 * n := by
    simp [mul_comm]
  rw [Finset.sum_add_distrib, htwo]
  omega

theorem rationalMatrixEntryBitBound_le_inputLength {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    rationalMatrixEntryBitBound A ≤
      encodedBitLength RationalMatrixInput ⟨n, A⟩ := by
  rw [rationalMatrixInput_encodedBitLength_eq, rationalMatrixEntryBitBound]
  omega

theorem matrixDimensionSq_le_inputLength {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ) :
    n ^ 2 ≤ encodedBitLength RationalMatrixInput ⟨n, A⟩ := by
  have hentries : n ^ 2 ≤
      ∑ i, ∑ j, encodedBitLength ℚ (A i j) := by
    calc
      n ^ 2 = ∑ _i : Fin n, ∑ _j : Fin n, 1 := by simp; ring
      _ ≤ ∑ i, ∑ j, encodedBitLength ℚ (A i j) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact one_le_rational_encodedBitLength (A i j)
  rw [rationalMatrixInput_encodedBitLength_eq]
  omega

theorem rationalEllipsoidStateEncodedBitLength_eq {d : ℕ}
    (E : RationalEllipsoidState d) :
    rationalEllipsoidStateEncodedBitLength E =
      6 + (∑ i, encodedBitLength ℚ (E.center i)) + 2 * d +
        ∑ i, ∑ j, encodedBitLength ℚ (E.basis i j) := by
  rw [rationalEllipsoidStateEncodedBitLength,
    encodedBitLength_eq_dataSize]
  simp only [rationalEllipsoidStatePayload, DataEncode_pair, Data.size,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    rationalMatrixRows, encodedBitLength_eq_dataSize]
  rw [dataEncode_list_ofFn_size, dataEncode_list_ofFn_size]
  simp_rw [dataEncode_list_ofFn_size]
  have htwo : (∑ _i : Fin d, (2 : ℕ)) = 2 * d := by
    simp [mul_comm]
  rw [Finset.sum_add_distrib]
  rw [htwo]
  omega

/-- Total encoding size of one stored rounded state. -/
theorem adaptiveRoundedEllipsoid_state_encodedBitLength_le
    {d K P : ℕ} (hd : 0 < d) (U : RationalEllipsoidState d)
    (hM : rationalStateAbsBound (adaptiveRoundedEllipsoid U) ≤ (2 : ℚ) ^ K)
    (hp : roundedEllipsoidPrecision U ≤ P) :
    rationalEllipsoidStateEncodedBitLength (adaptiveRoundedEllipsoid U) ≤
      6 + d * (20 + 4 * K + 8 * P) + 2 * d +
        d ^ 2 * (100 + 4 * K + 8 * P + 32 * d) := by
  rw [rationalEllipsoidStateEncodedBitLength_eq]
  have hc : (∑ i : Fin d, encodedBitLength ℚ
      ((adaptiveRoundedEllipsoid U).center i)) ≤
      ∑ _i : Fin d, (20 + 4 * K + 8 * P) := by
    apply Finset.sum_le_sum
    intro i _
    exact adaptiveRoundedEllipsoid_center_encodedBitLength_le U hM hp i
  have hB : (∑ i : Fin d, ∑ j : Fin d, encodedBitLength ℚ
      ((adaptiveRoundedEllipsoid U).basis i j)) ≤
      ∑ _i : Fin d, ∑ _j : Fin d,
        (100 + 4 * K + 8 * P + 32 * d) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact adaptiveRoundedEllipsoid_basis_encodedBitLength_le hd U hM hp i j
  have hc' : (∑ i : Fin d, encodedBitLength ℚ
      ((adaptiveRoundedEllipsoid U).center i)) ≤
      d * (20 + 4 * K + 8 * P) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] using hc
  have hB' : (∑ i : Fin d, ∑ j : Fin d, encodedBitLength ℚ
      ((adaptiveRoundedEllipsoid U).basis i j)) ≤
      d * (d * (100 + 4 * K + 8 * P + 32 * d)) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] using hB
  calc
    6 + (∑ i, encodedBitLength ℚ
          ((adaptiveRoundedEllipsoid U).center i)) + 2 * d +
        ∑ i, ∑ j, encodedBitLength ℚ
          ((adaptiveRoundedEllipsoid U).basis i j) ≤
      6 + d * (20 + 4 * K + 8 * P) + 2 * d +
        d * (d * (100 + 4 * K + 8 * P + 32 * d)) := by omega
    _ = 6 + d * (20 + 4 * K + 8 * P) + 2 * d +
        d ^ 2 * (100 + 4 * K + 8 * P + 32 * d) := by ring

end BeyondBethe
