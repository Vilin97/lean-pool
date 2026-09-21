/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Core.RotationTorus
import Mathlib.FieldTheory.PrimeField

/-!
# Split and nonsplit trace classification

This module proves the elementary representation of every normalized trace over an odd
prime field by either the split torus or the concrete norm-one torus in the canonical quadratic
extension.
-/

namespace BGS.Markoff

open scoped Polynomial

section QuadraticExtensionSquares

variable (p : ℕ) [Fact p.Prime]

private theorem quadraticFiniteField_natCard :
    Nat.card (quadraticFiniteField p) = p ^ 2 :=
  GaloisField.card p (n := 2) (by norm_num)

/-- Every base-field scalar becomes a square in the canonical quadratic extension. -/
theorem isSquare_algebraMap_quadraticFiniteField (hpTwo : p ≠ 2) (a : ZMod p) :
    IsSquare (algebraMap (ZMod p) (quadraticFiniteField p) a) := by
  let E := quadraticFiniteField p
  letI : Fintype E := Fintype.ofFinite _
  change IsSquare (algebraMap (ZMod p) E a)
  by_cases ha : a = 0
  · subst a
    exact ⟨0, by simp⟩
  have hpOddCard : Odd p := (Fact.out : p.Prime).odd_of_ne_two hpTwo
  have hcharE : ringChar E ≠ 2 := by
    rw [show ringChar E = p from ringChar.eq (R := E) p]
    exact hpTwo
  have hmap_ne : algebraMap (ZMod p) E a ≠ 0 :=
    (map_ne_zero (algebraMap (ZMod p) E)).2 ha
  rw [FiniteField.isSquare_iff hcharE hmap_ne]
  rw [show Fintype.card E = p ^ 2 by
    rw [Fintype.card_eq_nat_card]
    exact quadraticFiniteField_natCard p]
  have hbasePow : a ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one ha
  have hexponent : p ^ 2 / 2 = (p - 1) * ((p + 1) / 2) := by
    apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
    calc
      2 * (p ^ 2 / 2) = p ^ 2 - 1 :=
        Nat.two_mul_odd_div_two (Nat.odd_iff.mp (Odd.pow hpOddCard))
      _ = (p - 1) * (p + 1) := by
        rw [show p ^ 2 - 1 = (p + 1) * (p - 1) by
          simpa using (sq_tsub_sq p 1)]
        exact mul_comm _ _
      _ = (p - 1) * (2 * ((p + 1) / 2)) := by
        rw [Nat.two_mul_div_two_of_even (Odd.add_one hpOddCard)]
      _ = 2 * ((p - 1) * ((p + 1) / 2)) := by ring
  rw [hexponent, pow_mul, ← map_pow, hbasePow, map_one, one_pow]

end QuadraticExtensionSquares

section TraceClassification

variable (p : ℕ) [Fact p.Prime]

private theorem two_ne_zero_zmod (hpTwo : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro hzero
  have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 hzero
  have hpLe : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
  exact hpTwo (Nat.le_antisymm hpLe (Fact.out : p.Prime).two_le)

private theorem nonparabolic_split_eigenvalue
    (t : ZMod p) (ht : t ^ 2 ≠ 4) (w : (ZMod p)ˣ)
    (htrace : splitTorusTrace w = t) : (w : ZMod p) ^ 2 ≠ 1 := by
  intro hw
  apply ht
  rw [← htrace]
  have hinv : ((w⁻¹ : (ZMod p)ˣ) : ZMod p) = (w : ZMod p) := by
    exact Units.inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hw)
  change ((w : ZMod p) + ((w⁻¹ : (ZMod p)ˣ) : ZMod p)) ^ 2 = 4
  rw [hinv]
  calc
    ((w : ZMod p) + (w : ZMod p)) ^ 2 = 4 * (w : ZMod p) ^ 2 := by ring
    _ = 4 := by rw [hw, mul_one]

private theorem nonparabolic_extension_eigenvalue
    (t : ZMod p) (ht : t ^ 2 ≠ 4) (w : (quadraticFiniteField p)ˣ)
    (htrace : algebraMap (ZMod p) (quadraticFiniteField p) t = splitTorusTrace w) :
    (w : quadraticFiniteField p) ^ 2 ≠ 1 := by
  intro hw
  apply ht
  apply (algebraMap (ZMod p) (quadraticFiniteField p)).injective
  rw [map_pow, map_ofNat, htrace]
  have hinv : ((w⁻¹ : (quadraticFiniteField p)ˣ) : quadraticFiniteField p) =
      (w : quadraticFiniteField p) := by
    exact Units.inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hw)
  change ((w : quadraticFiniteField p) +
      ((w⁻¹ : (quadraticFiniteField p)ˣ) : quadraticFiniteField p)) ^ 2 = 4
  rw [hinv]
  calc
    ((w : quadraticFiniteField p) + (w : quadraticFiniteField p)) ^ 2 =
        4 * (w : quadraticFiniteField p) ^ 2 := by ring
    _ = 4 := by rw [hw, mul_one]

/-- Every nonparabolic normalized trace over an odd prime field is represented by either the
split torus or the concrete norm-one torus in the canonical quadratic extension. -/
theorem exists_split_or_quadraticNormOneTrace
    (hpTwo : p ≠ 2) (t : ZMod p) (ht : t ^ 2 ≠ 4) :
    (∃ w : (ZMod p)ˣ,
      splitTorusTrace w = t ∧ (w : ZMod p) ^ 2 ≠ 1) ∨
    (∃ w : quadraticNormOneTorus p,
      quadraticNormOneTrace p w = t ∧
        (((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p) ^ 2 ≠ 1)) := by
  let d : ZMod p := t ^ 2 - 4
  have hd : d ≠ 0 := sub_ne_zero.mpr ht
  have htwoF : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod p hpTwo
  by_cases hdsquare : IsSquare d
  · obtain ⟨s, hs⟩ := hdsquare
    have hsDisc : s ^ 2 = t ^ 2 - 4 := by
      simpa [d, pow_two] using hs.symm
    let w0 : ZMod p := (t + s) / 2
    let v0 : ZMod p := (t - s) / 2
    have hwv : w0 * v0 = 1 := by
      dsimp [w0, v0]
      field_simp [htwoF]
      linear_combination -hsDisc
    have hw0 : w0 ≠ 0 := by
      intro hw
      rw [hw, zero_mul] at hwv
      exact zero_ne_one hwv
    let w : (ZMod p)ˣ := Units.mk0 w0 hw0
    have hinv : ((w⁻¹ : (ZMod p)ˣ) : ZMod p) = v0 :=
      Units.inv_eq_of_mul_eq_one_right hwv
    have htrace : splitTorusTrace w = t := by
      change w0 + ((w⁻¹ : (ZMod p)ˣ) : ZMod p) = t
      rw [hinv]
      dsimp [w0, v0]
      field_simp [htwoF]
      ring
    exact Or.inl ⟨w, htrace, nonparabolic_split_eigenvalue p t ht w htrace⟩
  · let E := quadraticFiniteField p
    letI : Fintype E := Fintype.ofFinite _
    obtain ⟨s, hs⟩ := isSquare_algebraMap_quadraticFiniteField p hpTwo d
    have hsDiscBase : s ^ 2 = algebraMap (ZMod p) E d := by
      simpa [pow_two] using hs.symm
    have hsFrobeniusSquare : (s ^ p) ^ 2 = s ^ 2 := by
      calc
        (s ^ p) ^ 2 = s ^ (p * 2) := (pow_mul s p 2).symm
        _ = s ^ (2 * p) := by rw [mul_comm]
        _ = (s ^ 2) ^ p := pow_mul s 2 p
        _ = (algebraMap (ZMod p) E d) ^ p := by rw [hsDiscBase]
        _ = algebraMap (ZMod p) E (d ^ p) := by rw [map_pow]
        _ = algebraMap (ZMod p) E d := by rw [ZMod.pow_card]
        _ = s ^ 2 := hsDiscBase.symm
    have hsFrobeniusCases : s ^ p = s ∨ s ^ p = -s := by
      have hfactor : (s ^ p - s) * (s ^ p + s) = 0 := by
        calc
          (s ^ p - s) * (s ^ p + s) = (s ^ p) ^ 2 - s ^ 2 := by ring
          _ = 0 := sub_eq_zero.mpr hsFrobeniusSquare
      rcases mul_eq_zero.mp hfactor with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h)
    have hsFrobenius : s ^ p = -s := by
      rcases hsFrobeniusCases with hfixed | hneg
      · exfalso
        apply hdsquare
        have hmem : s ∈ (⊥ : Subfield E) :=
          (Subfield.mem_bot_iff_pow_eq_self E p).2 hfixed
        obtain ⟨n, hn⟩ := (mem_bot_iff_intCast p E).1 hmem
        have hbaseSquare : d = (n : ZMod p) ^ 2 := by
          apply (algebraMap (ZMod p) E).injective
          calc
            algebraMap (ZMod p) E d = s ^ 2 := hsDiscBase.symm
            _ = (n : E) ^ 2 := by rw [hn]
            _ = algebraMap (ZMod p) E ((n : ZMod p) ^ 2) := by norm_cast
        exact ⟨(n : ZMod p), by simpa [pow_two] using hbaseSquare⟩
      · exact hneg
    let T : E := algebraMap (ZMod p) E t
    have hsDisc : s ^ 2 = T ^ 2 - 4 := by
      simpa only [d, T, map_sub, map_pow, map_ofNat] using hsDiscBase
    have htwoE : (2 : E) ≠ 0 := by
      exact (map_ne_zero (algebraMap (ZMod p) E)).2 htwoF
    let w0 : E := (T + s) / 2
    let v0 : E := (T - s) / 2
    have hwv : w0 * v0 = 1 := by
      dsimp [w0, v0]
      rw [div_mul_div_comm]
      apply (div_eq_iff (mul_ne_zero htwoE htwoE)).2
      linear_combination -hsDisc
    have hw0 : w0 ≠ 0 := by
      intro hw
      rw [hw, zero_mul] at hwv
      exact zero_ne_one hwv
    let w : Eˣ := Units.mk0 w0 hw0
    have hinv : ((w⁻¹ : Eˣ) : E) = v0 :=
      Units.inv_eq_of_mul_eq_one_right hwv
    have htrace : splitTorusTrace w = T := by
      change w0 + ((w⁻¹ : Eˣ) : E) = T
      rw [hinv]
      dsimp [w0, v0]
      rw [← add_div]
      apply (div_eq_iff htwoE).2
      ring
    have hTpow : T ^ p = T := by
      dsimp [T]
      rw [← map_pow, ZMod.pow_card]
    have htwoPow : (2 : E) ^ p = 2 := by
      change (algebraMap (ZMod p) E (2 : ZMod p)) ^ p =
        algebraMap (ZMod p) E (2 : ZMod p)
      rw [← map_pow, ZMod.pow_card]
    have hwpow : w0 ^ p = v0 := by
      dsimp [w0, v0]
      rw [div_pow, add_pow_char, hTpow, hsFrobenius, htwoPow]
      simp [sub_eq_add_neg]
    have hfinrank : Module.finrank (ZMod p) E = 2 :=
      GaloisField.finrank p (n := 2) (by norm_num)
    have hnormFormula := FiniteField.algebraMap_norm_eq_prod_pow
      (ZMod p) E w0
    rw [hfinrank, Nat.card_zmod] at hnormFormula
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, pow_zero, pow_one,
      one_mul] at hnormFormula
    have hnorm : Algebra.norm (ZMod p) w0 = 1 := by
      apply (algebraMap (ZMod p) E).injective
      rw [hnormFormula, hwpow, hwv, map_one]
    have hwMem : w ∈ quadraticNormOneTorus p := by
      rw [quadraticNormOneTorus, MonoidHom.mem_ker]
      apply Units.ext
      simpa [w] using hnorm
    let normOneW : quadraticNormOneTorus p := ⟨w, hwMem⟩
    have hnormOneTrace : quadraticNormOneTrace p normOneW = t := by
      apply (algebraMap (ZMod p) E).injective
      rw [algebraMap_quadraticNormOneTrace]
      exact htrace
    refine Or.inr ⟨normOneW, hnormOneTrace, ?_⟩
    exact nonparabolic_extension_eigenvalue p t ht w (hnormOneTrace ▸
      algebraMap_quadraticNormOneTrace p normOneW)

/-- The two normalized parabolic trace parameters. -/
def normalizedParabolicTraceSet : Finset (ZMod p) :=
  {2, -2}

/-- The concrete low-order trace set used for normalized Markoff rotations over `ZMod p`. -/
noncomputable def concreteLowOrderTraceSet (bound : ℕ) : Finset (ZMod p) :=
  lowOrderTraceSet (normalizedParabolicTraceSet p)
    (splitTorusTrace : (ZMod p)ˣ → ZMod p) (quadraticNormOneTrace p) bound

/-- The concrete trace set has the quadratic cardinality bound needed in the giant-orbit count. -/
theorem concreteLowOrderTraceSet_card_le (bound : ℕ) :
    (concreteLowOrderTraceSet p bound).card ≤ 2 + 2 * bound ^ 2 := by
  calc
    (concreteLowOrderTraceSet p bound).card ≤
        (normalizedParabolicTraceSet p).card + 2 * bound ^ 2 := by
      exact lowOrderTraceSet_card_le_parabolic_add_two_mul_bound_sq
        (normalizedParabolicTraceSet p) (splitTorusTrace : (ZMod p)ˣ → ZMod p)
          (quadraticNormOneTrace p) bound
    _ ≤ 2 + 2 * bound ^ 2 := by
      gcongr
      exact Finset.card_le_two

/-- A normalized trace of small rotation order lies in the concrete union of the parabolic,
split-torus, and quadratic norm-one bounded-order trace sets. -/
theorem mem_concreteLowOrderTraceSet_of_rotationOrder_lt
    (hpTwo : p ≠ 2) (t : ZMod p) (bound : ℕ)
    (hsmall : rotationOrder t < bound) :
    t ∈ concreteLowOrderTraceSet p bound := by
  by_cases ht : t ^ 2 = 4
  · have hfactor : (t - 2) * (t + 2) = 0 := by
      calc
        (t - 2) * (t + 2) = t ^ 2 - 4 := by ring
        _ = 0 := sub_eq_zero.mpr ht
    have htCases : t = 2 ∨ t = -2 := by
      rcases mul_eq_zero.mp hfactor with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h)
    have hparabolic : t ∈ normalizedParabolicTraceSet p := by
      rcases htCases with rfl | rfl <;> simp [normalizedParabolicTraceSet]
    rw [concreteLowOrderTraceSet, lowOrderTraceSet]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hparabolic)
  · rcases exists_split_or_quadraticNormOneTrace p hpTwo t ht with
      ⟨w, htrace, hw⟩ | ⟨w, htrace, hw⟩
    · have hsplit : splitTorusTrace w ∈
          boundedOrderTraceSet (splitTorusTrace : (ZMod p)ˣ → ZMod p) bound :=
        splitTorusTrace_mem_boundedOrderTraceSet_of_rotationOrder_lt w hw bound (by
          simpa [htrace] using hsmall)
      rw [concreteLowOrderTraceSet, lowOrderTraceSet]
      rw [← htrace]
      exact Finset.mem_union_left _ (Finset.mem_union_right _ hsplit)
    · have hnonsplit : quadraticNormOneTrace p w ∈
          boundedOrderTraceSet (quadraticNormOneTrace p) bound :=
        quadraticNormOneTrace_mem_boundedOrderTraceSet_of_rotationOrder_lt p w hw bound (by
          simpa [htrace] using hsmall)
      rw [concreteLowOrderTraceSet, lowOrderTraceSet]
      rw [← htrace]
      exact Finset.mem_union_right _ hnonsplit

end TraceClassification

end BGS.Markoff
