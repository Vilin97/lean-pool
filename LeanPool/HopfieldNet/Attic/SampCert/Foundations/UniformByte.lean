/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.Attic.SampCert.SLang
import LeanPool.HopfieldNet.Attic.SampCert.Util.Util
import LeanPool.HopfieldNet.Attic.SampCert.Foundations.Auto
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Nat.Log
import LeanPool.HopfieldNet.Attic.SampCert.Foundations.Monad


/-!
# ``probUniformByte`` Properties

This file contains lemmas about ``probUniformByte``, a ``SLang`` sampler for the
uniform distribution on bytes.

It also contains the derivation that ``probUniformP2`` is a uniform distribution.
-/


open Classical Nat PMF



namespace SLang




local instance : Finite UInt8 := by
  constructor
  · apply Equiv.ofBijective (fun v => v.toFin)
    apply Function.bijective_iff_has_inverse.mpr
    exists (fun v => UInt8.ofNat v.val)
    simp [Function.RightInverse, Function.LeftInverse]



/--
ProbUniformByte is a proper distribution
-/
def probUniformByte_normalizes : HasSum probUniformByte 1 := by
  rw [Summable.hasSum_iff ENNReal.summable]
  unfold SLang.probUniformByte
  rw [division_def]
  rw [ENNReal.tsum_mul_right]
  simp only [Nat.cast_ofNat]
  apply (ENNReal.toReal_eq_one_iff _).mp
  simp only [ENNReal.toReal_mul]
  rw [ENNReal.tsum_toReal_eq ?G1]
  case G1 => simp
  simp only [ENNReal.toReal_one, tsum_const, nsmul_eq_mul, mul_one]
  rw [@Nat.card_eq_of_equiv_fin UInt8 256 ?G1]
  case G1 =>
    apply Equiv.ofBijective (fun v => v.toFin)
    apply Function.bijective_iff_has_inverse.mpr
    exists (fun v => UInt8.ofNat v.val)
    simp [Function.RightInverse, Function.LeftInverse]
  simp [ENNReal.toReal_inv]

/--
ProbUniformByte as a PMF
-/
def probUniformByte_PMF : PMF UInt8 := ⟨ probUniformByte, probUniformByte_normalizes ⟩

/--
Evaluation of ``probUniformByteUpperBits`` for inside the support
-/
def probUniformByteUpperBits_eval_support {i x : ℕ} (Hx : x < 2 ^ (min 8 i)) :
    probUniformByteUpperBits i x = 2^(8 - i) / UInt8.size := by
  simp [probUniformByteUpperBits]
  rw [Nat.sub_eq_max_sub]
  simp [SLang.probBind, SLang.probPure, probUniformByte]
  cases (Classical.em (i < 8))
  · rw [max_eq_left (by linarith)]
    rw [min_eq_right (by linarith)] at Hx
    conv =>
      enter [1, 1, a]
      rw [Nat.shiftRight_eq_div_pow]
    conv =>
      enter [1, 1, a]
      rw [<- mul_one (256)⁻¹]
      rw [<- mul_zero (256)⁻¹]
      rw [<- mul_ite]
    rw [ENNReal.tsum_mul_left]
    rw [division_def]
    rw [mul_comm]
    congr 1

    -- Restruct sum to type where body is constant
    rw [<- (@tsum_subtype_eq_of_support_subset  _ _ _ _ _ { i_1 : UInt8 |  x = i_1.toNat / 2 ^ (8 - i) } ?G1)]
    case G1 => simp [Function.support]
    generalize HT : { i_1 : UInt8 |  x = i_1.toNat / 2 ^ (8 - i) } = T
    have H (x1 : T) : (@ite _ (x = (x1 : UInt8).toNat / 2 ^ (8 - i)) _ (1 : ENNReal) (0 : ENNReal)) = 1 := by
      apply ite_eq_iff.mpr
      simp
      rcases x1
      rename_i h val property
      subst HT
      simp_all only
      simp_all only [Set.mem_setOf_eq]
    conv =>
      enter [1, 1, a]
      rw [H a]
    clear H

    -- Rewrite to real sum
    -- Simplify me
    suffices ENNReal.toReal (∑' (_ : T), 1) = ENNReal.toReal (2 ^ (8 - i)) by
      refine (ENNReal.toReal_eq_toReal_iff' ?G1 ?G2).mp this
      case G1 =>
        rw [tsum_eq_finsum ?G1]
        case G1 =>
          simp [Function.support]
          apply Set.finite_univ_iff.mpr
          apply Subtype.finite
        simp
        have R := @finsum_induction ENNReal T _ (fun _ => 1) (fun z => z ≠ ⊤) (by simp) (by aesop) (by simp)
        simp at R
        trivial
      case G2 => simp

    -- Rewrite to set cardinality
    rw [ENNReal.tsum_toReal_eq ?G1]
    case G1 => simp
    simp [tsum_const]


    -- Evaluate set cardinality using bijection
    -- Simplify me!
    rw [@Nat.card_eq_of_equiv_fin T (2^(8 - i)) ?G1]
    case G1 =>
      rw [<- HT]
      simp
      apply Equiv.ofBijective
      case f =>
        intro v
        rcases v with ⟨ v', Hv' ⟩
        exact
          ⟨ v'.toNat - x * (2 ^ (8 - i)),
            by
              have W := (Nat.le_div_iff_mul_le (by simp)).mp (Eq.le Hv')
              have W' := (Nat.div_lt_iff_lt_mul (by simp)).mp (Nat.lt_succ_iff.mpr (Eq.le (Eq.symm Hv')))
              have W'' : v'.toNat - x * 2 ^ (8 - i) < x.succ * 2 ^ (8 - i) - x * 2 ^ (8 - i) := by
                exact Nat.sub_lt_sub_right W W'
              suffices  (x.succ * 2 ^ (8 - i) - x * 2 ^ (8 - i)) ≤  2 ^ (8 - i) by
                exact Nat.lt_of_lt_of_le W'' this
              rw [← Nat.sub_mul]
              simp ⟩
      apply Function.bijective_iff_has_inverse.mpr

      -- Set up the bijections
      -- Is there a simpler way to do this?
      exists ?G1
      case G1 =>
        intro f
        rcases f with ⟨ f', Hf' ⟩
        exact
          ⟨ UInt8.ofNatLT (f' + x * 2^(8-i))
            (by
              rw [UInt8.size]
              apply (@LT.lt.trans_le _ _ _ (2^(8-i) + x * 2^(8-i)))
              · exact Nat.add_lt_add_right Hf' (x * 2 ^ (8 - i))
              · conv =>
                  enter [1, 1]
                  rw [<- one_mul (2^(8-i))]
                rw [<- add_mul]
                have Z : (1 + x) ≤ 2^i := by linarith
                have Z' : (1 + x) * (2^(8-i)) ≤ 2^i * (2^(8-i)) := by
                  exact Nat.mul_le_mul_right (2 ^ (8 - i)) Z
                apply le_trans Z'
                apply Eq.le
                rw [<- pow_add]
                have H256 : 256 = 2^8 := by simp
                rw [H256]
                clear H256
                congr 1
                apply add_sub_of_le
                apply le_of_succ_le
                trivial
              ),
            (by
              unfold UInt8.toNat
              unfold UInt8.ofNatLT
              simp
              apply (nat_div_eq_le_lt_iff (by simp)).mpr
              apply And.intro
              · apply Nat.le_add_left (x * 2 ^ (8 - i)) f'
              · linarith )⟩
      dsimp [Function.RightInverse, Function.LeftInverse]
      apply And.intro
      · intro x'
        rcases x' with ⟨ ⟨ x'', H2x'' ⟩, Hx'' ⟩
        --unfold UInt8.toNat
        --simp
        congr
        --unfold UInt8.ofNatLT
        apply Nat.sub_add_cancel
        simp only [reducePow, UInt8.ofBitVec_ofFin, UInt8.ofFin_mk, UInt8.toNat_ofNatLT]
        rw [Hx'']
        rw [UInt8.toNat]
        apply (Nat.le_div_iff_mul_le (by simp)).mp
        simp
      · intro x'
        rcases x' with ⟨ x'', Hx'' ⟩
        --rw [UInt8.toNat]
        simp
    simp
  · rw [max_eq_right (by linarith)]
    rw [min_eq_left (by linarith)] at Hx
    rw [tsum_eq_single (UInt8.ofNatLT x Hx) ?G1]
    case G1 =>
      intro b' Hb'
      simp
      intro Hx'
      exfalso
      apply Hb'
      rcases b' with ⟨ ⟨ b'', Hb'' ⟩ ⟩
      congr
      rw [Hx']
      simp [UInt8.toNat]
    simp


/--
Evaluation of ``probUniformByteUpperBits`` for zero-shifts outside of the support
-/
def probUniformByteUpperBits_eval_zero {i x : ℕ} (Hx : x ≥ 2 ^ (min 8 i)) :
    probUniformByteUpperBits i x = 0 := by
  simp [probUniformByteUpperBits]
  rw [Nat.sub_eq_max_sub]
  simp [SLang.probBind, SLang.probPure, probUniformByte]
  intro v H1
  exfalso
  cases (Classical.em (i < 8))
  · -- i < 8
    rename_i Hi
    rw [max_eq_left (by linarith)] at H1
    rw [min_eq_right (by linarith)] at Hx
    simp_all
    rw [Nat.shiftRight_eq_div_pow] at *
    have H2 := UInt8.toNat_lt v
    apply Nat.mul_le_of_le_div (2 ^ (8 - i)) (2 ^ i) v.toNat at Hx
    rw [<- pow_add] at Hx
    have X : (i + (8 - i)) = 8 := by
      apply add_sub_of_le
      linarith
    rw [X] at Hx
    clear X
    linarith
  · -- i >= 8
    rename_i Hi
    rw [max_eq_right (by linarith)] at H1
    rw [min_eq_left (by linarith)] at Hx
    have H2 := UInt8.toNat_lt v
    simp_all
    linarith


lemma UIint8_cast_lt_size (a : UInt8) : a.toNat < UInt8.size := by
  rcases a with ⟨ ⟨ a', Ha' ⟩ ⟩
  rw [UInt8.toNat]
  simp
  apply Ha'


/--
Evaluation of ``probUniformP2`` for inside the support
-/
def probUniformP2_eval_support {i x : ℕ} (Hx : x < 2 ^ i):
    probUniformP2 i x = (1 / 2 ^ i) := by stop
  revert x
  induction' i using Nat.strong_induction_on with i ih
  rw [probUniformP2]
  split
  · intro x Hx'
    rename_i h
    rw [probUniformByteUpperBits_eval_support]
    · rw [UInt8.size]
      have X : 256 = 2^8 := by simp
      rw [X]
      clear X
      rw [cast_pow]
      apply (ENNReal.div_eq_div_iff _ _ _ _).mpr <;> try simp
      rw [← pow_add]
      congr 1
      rw [add_tsub_cancel_iff_le]
      linarith
    · rw [min_eq_right ?G1]
      case G1 => linarith
      assumption
  · intro x Hx'
    simp [probUniformByte]

    -- Simplify, rewrite to indicator function
    conv =>
      enter [1, 1, a]
      rw [<- ENNReal.tsum_mul_left]
      enter [1, b]
      rw [<- mul_one (probUniformP2 (i - 8) b)]
      rw [<- mul_zero (probUniformP2 (i - 8) b)]
      rw [<- mul_ite]
      rw [<- mul_assoc]

    -- Similar to the Laplace proof: use Euclidean division to rewrite
    -- to product of indicator functions
    rcases @euclidean_division x UInt8.size (by simp) with ⟨ p, q, Hq, Hx ⟩
    have X (a : UInt8) (b : ℕ) D :
        (@ite _ (q + UInt8.size * p = UInt8.size * b + a.toNat) D (1 : ENNReal) 0) =
        (if p = b then (1 : ENNReal) else 0) * (if q = a.toNat then (1 : ENNReal) else 0) := by stop
      split
      · rename_i He
        conv at He =>
          enter [2]
          rw [add_comm]
        have R := (euclidean_division_uniquness _ _ _ _ (by simp) Hq ?G3).mp He
        case G3 => apply UIint8_cast_lt_size
        rcases R with ⟨ R1 , R2 ⟩
        simp_all
      · rename_i He
        suffices (p ≠ b) ∨ (q ≠ a.toNat) by
          rcases this with Ht | Ht
          · rw [ite_eq_right_iff.mpr]
            · simp
            · intro Hk
              exfalso
              apply Ht Hk
          · rw [mul_comm]
            rw [ite_eq_right_iff.mpr]
            · simp
            · intro Hk
              exfalso
              apply Ht Hk
        simp only [ne_eq]
        apply (Decidable.not_and_iff_or_not.mp (p = b) (q = a.toNat))
        intro HK
        apply He
        rw [And.comm] at HK
        have _ := (euclidean_division_uniquness _ _ _ _ (by simp) Hq ?G3).mpr HK
        case G3 => apply UIint8_cast_lt_size
        linarith
    conv =>
      enter [1, 1, a, 1, b]
      rw [Hx]
      rw [X a b]
    clear X

    -- Separate the sums
    conv =>
      enter [1, 1, a, 1, b]
      repeat rw [mul_assoc]
    conv =>
      enter [1, 1, a]
      rw [ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_mul_left]
    conv =>
      enter [1, 2, 1, a, 1, b]
      rw [<- mul_assoc]
      rw [mul_comm]
    conv =>
      enter [1, 2, 1, a]
      rw [ENNReal.tsum_mul_left]
    conv =>
      enter [1, 2]
      rw [ENNReal.tsum_mul_right]
    simp

    -- Simplify the singleton sums
    rw [tsum_eq_single p ?G1]
    case G1 =>
      intro _ HK
      simp
      intro HK'
      exfalso
      exact HK (id (Eq.symm HK'))
    have X : (UInt8.ofNatLT q Hq).toNat = q := by
      rw [UInt8.toNat]
      simp only [UInt8.toBitVec_ofNatLT, BitVec.toNat_ofNatLT]
    rw [tsum_eq_single (UInt8.ofNatLT q Hq) ?G1]
    case G1 =>
      simp
      intro b HK' HK''
      apply HK'
      rcases b with ⟨ ⟨ b' , Hb' ⟩ ⟩
      congr
      rw [HK'']
      rw [UInt8.toNat]
      simp only [reducePow, BitVec.toNat_ofFin]
    rw [X]
    clear X
    simp only [↓reduceIte, one_mul]

    -- Apply the IH
    rw [ih]
    · simp
      rw [<- ENNReal.mul_inv ?G1 ?G2]
      case G1 => simp
      case G2 => simp
      congr 1
      have H256 : (256 : ENNReal) = (256 : ℕ) := by simp
      rw [H256]
      have X : (256 : ℕ) = 2^8 := by simp
      rw [X]
      rw [cast_pow]
      rw [cast_two]
      rw [← pow_add]
      congr 1
      apply add_sub_of_le
      linarith
    · simp
      linarith
    · rw [Hx] at Hx'
      have Hx'' : UInt8.size * p < OfNat.ofNat 2 ^ i := by
        apply Classical.byContradiction
        intro HK
        linarith
      rw [UInt8.size] at Hx''
      have Y : 256 = 2^8 := by simp
      rw [Y] at Hx''
      clear Y
      have W := (Nat.lt_div_iff_mul_lt ?G1 _).mpr Hx''
      case G1 =>
        apply Nat.pow_dvd_pow (OfNat.ofNat 2)
        linarith
      apply (LT.lt.trans_eq W)
      apply Nat.pow_div <;> linarith

/--
Evaluation of ``probUniformP2`` for zero-shifts outside of the support
-/
def probUniformP2_eval_zero {i x : ℕ} (Hx : x ≥ 2 ^ i):
    probUniformP2 i x = 0 := by
  revert x
  induction' i using Nat.strong_induction_on with i ih
  intro x Hk
  rw [probUniformP2]
  split
  · apply probUniformByteUpperBits_eval_zero
    rw [min_eq_right]
    · trivial
    · linarith
  · simp
    intro i1
    right
    intro i2 Hi
    apply ih
    · apply sub_lt
      · linarith
      · simp
    · rw [Hi] at Hk
      simp_all
      suffices 2^ i ≤ UInt8.size * i2 by
        rw [UInt8.size] at this
        rw [← Nat.pow_div (by trivial) ?G1]
        case G1 => simp
        exact Nat.div_le_of_le_mul this
      have H : (i1.toNat < UInt8.size) := by exact UIint8_cast_lt_size i1

      -- Establish this bound by the uniqueness of Euclidean division
      rcases @euclidean_division (2^i) (2^8) (by simp) with ⟨ p, q, Hq, H ⟩
      have Hple : (p ≤ i2) := by linarith
      have Heuc' : q + 2 ^ 8 * p = 0 + 2 ^ 8 * (2 ^ (i - 8)) := by
        rw [<- H]
        rw [zero_add]
        rw [<- pow_add]
        congr 1
        symm
        apply add_sub_of_le
        trivial
      have W := (euclidean_division_uniquness _ _ _ _ (by simp) Hq (by simp)).mp Heuc'
      simp_all

end SLang
