/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández, jayyswan
-/
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Topology.Algebra.IsOpenUnits

/-!
# Padic unit squares form an open subgroup

Port of upstream `Padics/Squares.lean`.  The squares among the `p`-adic units form an open
subgroup of `ℚ_[p]ˣ`: every element close enough to `1` is a square, so the square locus is
a neighbourhood of `1`, and translation by an already-known square exhibits it as a
neighbourhood of every one of its points.

The two lifting lemmas (`PadicInt.isSquare_of_zmod`, `PadicInt.isSquare_of_zmodPow`) are
Hensel-style: a `p`-adic integer unit is a square as soon as its reduction modulo `p`
(odd `p`) resp. modulo `8` (`p = 2`) is one.  They are ported here because the upstream
`Padics/Squares.lean` obtains them from `Padics/Lemmas.lean`.

## Provenance

This file is a derived work.  It is based on `Padics/Squares.lean` and `Padics/Lemmas.lean` of the
HassePrinciple project (<https://github.com/mariainesdff/HassePrinciple>,
Apache-2.0, Copyright (c) 2026 Nirvana Coppola,
María Inés de Frutos-Fernández), a Women in Numbers 7 collaboration.
It has been modified: the statements and proofs were rewritten for Lean 4.33 /
Mathlib without upstream's module system, and the development is extended beyond
what upstream proves.  Upstream declaration names are kept so that the two
developments can be compared side by side.  See the repository NOTICE file.
-/

open Polynomial

/-! ### Reduction criteria for `p`-adic integer squares -/

namespace PadicInt

-- Theorem: an element of `ℤ_[p]` is divisible by `p` iff its reduction modulo `p` vanishes.
lemma p_dvd_iff_toZMod_eq_zero {p : ℕ} [Fact (Nat.Prime p)] {m : ℤ_[p]} :
    (p : ℤ_[p]) ∣ m ↔ m.toZMod = 0 := by
  rw [← Ideal.mem_span_singleton, ← maximalIdeal_eq_span_p, ← RingHom.mem_ker, ker_toZMod]

-- Theorem: an element of `ℤ_[p]` is divisible by `p ^ n` iff its reduction modulo `p ^ n`
-- vanishes.
lemma pow_p_dvd_iff_toZModPow_eq_zero {p : ℕ} [Fact (Nat.Prime p)] {m : ℤ_[p]} {n : ℕ} :
    (p : ℤ_[p]) ^ n ∣ m ↔ m.toZModPow n = 0 := by
  rw [← Ideal.mem_span_singleton, ← RingHom.mem_ker, ker_toZModPow]

-- Theorem: an element in `ℤ_[p]` for odd `p` is a square if its reduction modulo `p` is a
-- square.
lemma isSquare_of_zmod {p : ℕ} [Fact (Nat.Prime p)] (hp : p ≠ 2)
    {m : ℤ_[p]} (hm : ¬ (p : ℤ_[p]) ∣ m) (hmod : IsSquare m.toZMod) : IsSquare m := by
  obtain ⟨r, hr⟩ := hmod
  let a := (r.cast : ℤ_[p])
  let F : ℤ_[p][X] := X ^ 2 - C m
  have hF : ‖(aeval a) F‖ < ‖(aeval a) (derivative F)‖ ^ 2 := by
    have h2 : ‖(2 : ℤ_[p])‖ = 1 := by
      rw [← Nat.cast_two, norm_natCast_eq_one_iff]
      simp [Nat.coprime_two_right, Nat.Prime.odd_of_ne_two Fact.out hp]
    have h1 : ‖(r.cast : ℤ_[p])‖ = 1 := by
      rw [← isUnit_iff, ← IsLocalRing.notMem_maximalIdeal, ← ker_toZMod, RingHom.mem_ker]
      simp only [ZMod.ringHom_map_cast]
      by_contra h0
      simp only [h0, mul_zero, ← p_dvd_iff_toZMod_eq_zero] at hr
      exact hm hr
    simp only [aeval_sub, coe_aeval_eq_eval, eval_pow, eval_X, aeval_C, Algebra.algebraMap_self,
      RingHom.id_apply, derivative_sub, derivative_X_pow_succ, Nat.cast_one, one_add_one_eq_two,
      pow_one, derivative_C, sub_zero, eval_mul, eval_C, norm_mul, a, F, h2, one_mul, h1, one_pow]
    simp [norm_lt_one_iff_dvd, p_dvd_iff_toZMod_eq_zero, hr, pow_two]
  obtain ⟨z, hz0, hz⟩ := hensels_lemma hF
  simp only [aeval_sub, coe_aeval_eq_eval, eval_pow, eval_X, aeval_C, Algebra.algebraMap_self,
    RingHom.id_apply, F, sub_eq_zero] at hz0
  exact ⟨z, by simp [← hz0, pow_two]⟩

-- Theorem: an element in `ℤ_[2]` is a square if its reduction modulo `8` is a square.
lemma isSquare_of_zmodPow {m : ℤ_[2]} (hm : ¬ (2 : ℤ_[2]) ∣ m)
    (hmod : IsSquare (m.toZModPow 3)) : IsSquare m := by
  obtain ⟨r, hr⟩ := hmod
  let a := (r.cast : ℤ_[2])
  let F : ℤ_[2][X] := X ^ 2 - C m
  have hF : ‖(aeval a) F‖ < ‖(aeval a) (derivative F)‖ ^ 2 := by
    have h1 : ‖(r.cast : ℤ_[2])‖ = 1 := by
      rw [← isUnit_iff, ← IsLocalRing.notMem_maximalIdeal, ← ker_toZMod, RingHom.mem_ker]
      simp only [Nat.reducePow, ← p_dvd_iff_toZMod_eq_zero, Nat.cast_ofNat]
      by_contra h0
      have : toZModPow 3 r.cast = r := by simp
      rw [← sub_eq_zero, ← this, ← map_mul, ← map_sub, ← pow_p_dvd_iff_toZModPow_eq_zero,
        Nat.cast_ofNat] at hr
      exact hm ((dvd_iff_dvd_of_dvd_sub (dvd_trans (dvd_pow_self 2 three_ne_zero) hr)).mpr
        (dvd_mul_of_dvd_left h0 r.cast))
    simp only [aeval_sub, coe_aeval_eq_eval, eval_pow, eval_X, aeval_C, Algebra.algebraMap_self,
      RingHom.id_apply, derivative_sub, derivative_X_pow_succ, Nat.cast_one, one_add_one_eq_two,
      pow_one, derivative_C, sub_zero, eval_mul, eval_C, norm_mul, a, F, mul_one, h1,
      ← Nat.cast_two (R := ℤ_[2]), PadicInt.norm_p, ← zpow_neg_one, ← zpow_natCast,
      ← zpow_mul, Nat.reducePow, Int.reduceNeg, neg_mul, one_mul,
      norm_lt_pow_iff_norm_le_pow_sub_one, Nat.cast_ofNat (R := ℤ), Int.reduceSub]
    rw [← Nat.cast_three, norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton,
      pow_p_dvd_iff_toZModPow_eq_zero]
    simp [hr, pow_two]
  obtain ⟨z, hz0, hz⟩ := hensels_lemma hF
  simp only [aeval_sub, coe_aeval_eq_eval, eval_pow, eval_X, aeval_C, Algebra.algebraMap_self,
    RingHom.id_apply, F, sub_eq_zero] at hz0
  exact ⟨z, by simp [← hz0, pow_two]⟩

end PadicInt

/-! ### Near `1` the `p`-adic units are squares -/

namespace Padic

variable (p : ℕ) [Fact (Nat.Prime p)]

-- Theorem: for odd `p`, any `p`-adic number within distance `1` of `1` is a square.
lemma isSquare_of_dist_one_lt_one {p : ℕ} [Fact (Nat.Prime p)] (hp : p ≠ 2) {x : ℚ_[p]}
    (hx : dist x 1 < 1) : IsSquare x := by
  let z : ℤ_[p] := ⟨x - 1, hx.le⟩
  have : ‖x - 1‖ = ‖z‖ := by simp [z]
  rw [dist_eq_norm, ← zpow_zero (p : ℝ), norm_lt_pow_iff_norm_le_pow_sub_one, this, zero_sub,
    ← Nat.cast_one, PadicInt.norm_le_pow_iff_mem_span_pow, pow_one, Ideal.mem_span_singleton] at hx
  have hz1 : IsSquare (z + 1) := by
    have hz0 : PadicInt.toZMod z = 0 := by
      simp [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
        Ideal.mem_span_singleton, hx]
    exact (z + 1).isSquare_of_zmod hp (by simp [dvd_add_right hx, ← PadicInt.norm_lt_one_iff_dvd])
      (by simp [hz0])
  obtain ⟨r, hr⟩ := hz1
  exact ⟨r, by simp [← PadicInt.coe_mul, ← hr]; aesop⟩

-- Theorem: any `2`-adic number within distance `2⁻²` of `1` is a square.
lemma isSquare_of_dist_one_lt_pow {x : ℚ_[2]} (hx : dist x 1 < 2 ^ (-(2 : ℤ))) : IsSquare x := by
  have hx1 : ‖x - 1‖ ≤ 1 := le_trans hx.le (by norm_num)
  let z : ℤ_[2] := ⟨x - 1, hx1⟩
  have : ‖x - 1‖ = ‖z‖ := by simp [z]
  rw [dist_eq_norm, ← Nat.cast_two (R := ℝ), norm_lt_pow_iff_norm_le_pow_sub_one, this] at hx
  simp only [Int.reduceSub, ← Nat.cast_three (R := ℤ), PadicInt.norm_le_pow_iff_mem_span_pow,
    Ideal.mem_span_singleton] at hx
  rw [Nat.cast_two] at hx
  have hz1 : IsSquare (z + 1) := by
    have hz0 : z.toZModPow 3 = 0 := by
      simp [-Nat.reducePow, ← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton, hx]
    refine (z + 1).isSquare_of_zmodPow ?_ (by simp [hz0])
    rw [dvd_add_right (dvd_trans (dvd_pow_self 2 three_ne_zero) hx), ← Nat.cast_two (R := ℤ_[2]),
      ← PadicInt.norm_lt_one_iff_dvd]
    simp
  obtain ⟨r, hr⟩ := hz1
  exact ⟨r, by simp [← PadicInt.coe_mul, ← hr]; aesop⟩

-- Theorem: there is a uniform `p`-adic neighbourhood of `1` consisting of squares.
lemma exists_pow_isSquare_of_dist_one_lt (p : ℕ) [Fact (Nat.Prime p)] :
    ∃ (n : ℕ), ∀ (x : ℚ_[p]), dist x 1 < p ^ (-(n : ℤ)) → IsSquare x := by
  by_cases hp : p = 2
  · subst hp
    exact ⟨2, fun x ↦ isSquare_of_dist_one_lt_pow⟩
  · exact ⟨0, fun x ↦ isSquare_of_dist_one_lt_one hp⟩

open Pointwise Set

-- Theorem: the nonzero `p`-adic squares form an open set.
lemma isOpen_squares_sdiff_zero : IsOpen ({x : ℚ_[p] | IsSquare x} \ {0}) := by
  rw [isOpen_iff_forall_mem_open]
  intro x ⟨hx, hx0⟩
  simp only [mem_ofPred_eq, mem_singleton_iff] at hx hx0
  obtain ⟨n, hn⟩ := exists_pow_isSquare_of_dist_one_lt p
  refine ⟨x • (Metric.ball (1 : ℚ_[p]) (p ^ (-(n : ℤ)))), fun y hy ↦ ?_, by
    simp [smul_ball hx0, Metric.isOpen_ball], mem_smul_set.mpr ⟨1,
      Metric.mem_ball_self (zpow_pos (Nat.cast_pos.mpr (Nat.pos_of_neZero p)) _), by simp⟩⟩
  simp only [← image_smul, mem_image, Metric.mem_ball, mem_sdiff, mem_ofPred_eq,
    mem_singleton_iff] at hy ⊢
  obtain ⟨u, hup, hu⟩ := hy
  simp only [← hu, smul_eq_mul, mul_eq_zero, not_or]
  refine ⟨hx.mul (hn u hup), hx0, ?_⟩
  by_contra h0
  simp only [h0, dist_zero, norm_one, ← zpow_zero (p : ℝ)] at hup
  rw [zpow_lt_zpow_iff_right₀ (Nat.one_lt_cast.mpr (Nat.Prime.one_lt Fact.out))] at hup
  simp [← not_le] at hup

-- Theorem: the `p`-adic unit squares form an open subgroup of `ℚ_[p]ˣ`.
/-- The open subgroup of `p`-adic unit squares inside `ℚ_[p]ˣ`. -/
def unitSquares : OpenSubgroup ℚ_[p]ˣ where
  carrier              := {x : ℚ_[p]ˣ | IsSquare x}
  mul_mem' {x y} hx hy := IsSquare.mul hx hy
  one_mem'             := by simp
  inv_mem' {x} hx      := IsSquare.inv hx
  isOpen'              := by
    have h : (Units.val '' {x : ℚ_[p]ˣ | IsSquare x}) = {x : ℚ_[p] | IsSquare x} \ {0} := by
      ext x
      simp only [mem_image, mem_ofPred_eq, mem_sdiff, mem_singleton_iff]
      refine ⟨fun ⟨u, hu2, hux⟩ ↦ ?_, fun ⟨hxs, hx0⟩ ↦ ?_⟩
      · simp only [← hux, Units.ne_zero, not_false_eq_true, and_true]
        obtain ⟨v, hv⟩ := hu2
        exact ⟨v, by simp [hv]⟩
      · obtain ⟨r, hr⟩ := hxs
        exact ⟨Units.mk0 x hx0, ⟨Units.mk0 r (by aesop), by simp [hr]⟩, by simp⟩
    rw [IsOpenUnits.isOpenEmbedding_unitsVal.isOpen_iff_image_isOpen, h]
    exact isOpen_squares_sdiff_zero p

end Padic
