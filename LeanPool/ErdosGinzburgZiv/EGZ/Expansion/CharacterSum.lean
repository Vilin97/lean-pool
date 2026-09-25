/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.CenteredLift
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Character sums away from a centered slab

Jordan's inequality bounds a nontrivial root of unity away from one in
terms of its centered residue. The finite geometric-series identity then
bounds every partial character sum independently of its length.
-/

@[expose] public section

open scoped BigOperators

namespace EGZ.Expansion

theorem zmodAddEquiv_one {p : ℕ} [NeZero p] (r : ZMod p) :
    (AddChar.zmodAddEquiv r : AddChar (ZMod p) ℂ) 1 =
      Complex.exp (Complex.I * (2 * Real.pi * (r.valMinAbs : ℝ) / p)) := by
  change ((AddChar.zmod p r 1 : Circle) : ℂ) = _
  have hr : (r.valMinAbs : ZMod p) = r := ZMod.coe_valMinAbs r
  rw [← hr]
  have h := AddChar.zmod_intCast p r.valMinAbs (1 : ℤ)
  simp only [Int.cast_one, mul_one] at h
  rw [h, Circle.coe_exp]
  congr 1
  push_cast
  ring

/-- A centered residue controls the distance of its character value from
one. This estimate does not require primality. -/
theorem norm_zmodAddEquiv_one_sub_one_ge {p : ℕ} [NeZero p] (r : ZMod p) :
    4 * |(r.valMinAbs : ℝ)| / p ≤
      ‖(AddChar.zmodAddEquiv r : AddChar (ZMod p) ℂ) 1 - 1‖ := by
  have hp : (0 : ℝ) < p := by exact_mod_cast NeZero.pos p
  have hz : |(r.valMinAbs : ℝ)| ≤ (p : ℝ) / 2 := by
    have hn := r.natAbs_valMinAbs_le
    have hh : 2 * r.valMinAbs.natAbs ≤ p :=
      (Nat.mul_le_mul_left 2 hn).trans (Nat.mul_div_le p 2)
    have hr : (2 : ℝ) * |(r.valMinAbs : ℝ)| ≤ p := by
      simpa only [Nat.cast_natAbs, Int.cast_abs] using
        (show (2 : ℝ) * r.valMinAbs.natAbs ≤ p by exact_mod_cast hh)
    linarith
  let t : ℝ := 2 * Real.pi * (r.valMinAbs : ℝ) / p
  have ht : |t / 2| ≤ Real.pi / 2 := by
    have heq : |t / 2| = Real.pi * |(r.valMinAbs : ℝ)| / p := by
      dsimp [t]
      rw [abs_div, abs_div, abs_mul, abs_mul, abs_of_pos Real.pi_pos,
        abs_of_pos hp]
      norm_num
      ring
    rw [heq]
    apply (div_le_iff₀ hp).2
    nlinarith [mul_le_mul_of_nonneg_left hz Real.pi_pos.le]
  have hs := Real.mul_abs_le_abs_sin ht
  rw [zmodAddEquiv_one]
  have htcast : (2 * (Real.pi : ℂ) * ((r.valMinAbs : ℝ) : ℂ) / (p : ℂ)) = (t : ℂ) := by
    simp [t]
  rw [htcast, Complex.norm_exp_I_mul_ofReal_sub_one]
  change 4 * |(r.valMinAbs : ℝ)| / p ≤ ‖2 * Real.sin (t / 2)‖
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have heq : 2 * (2 / Real.pi * |t / 2|) = 4 * |(r.valMinAbs : ℝ)| / p := by
    dsimp [t]
    rw [abs_div, abs_div, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hp]
    norm_num
    field_simp
    ring
  rw [← heq]
  exact mul_le_mul_of_nonneg_left hs (by norm_num)

theorem character_partial_sum_le {p K : ℕ} [NeZero p] (hK : 0 < K)
    (r : ZMod p) (hr : ¬ HasBoundedRepresentative p K r) (m : ℕ) :
    ‖∑ j ∈ Finset.range m, (AddChar.zmodAddEquiv r : AddChar (ZMod p) ℂ) (j : ZMod p)‖ ≤
      2 * (p : ℝ) / K := by
  let χ : AddChar (ZMod p) ℂ := AddChar.zmodAddEquiv r
  have hp : (0 : ℝ) < p := by exact_mod_cast NeZero.pos p
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hrK : K < r.valMinAbs.natAbs := by
    by_contra! h
    exact hr ⟨r.valMinAbs, h, ZMod.coe_valMinAbs r⟩
  have hrKR : (K : ℝ) < |(r.valMinAbs : ℝ)| := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using
      (show (K : ℝ) < r.valMinAbs.natAbs by exact_mod_cast hrK)
  have hroot : (K : ℝ) / p ≤ ‖χ 1 - 1‖ := by
    have h := norm_zmodAddEquiv_one_sub_one_ge r
    exact (div_le_div_of_nonneg_right (by linarith) hp.le).trans h
  have hχ (j : ℕ) : χ (j : ZMod p) = χ 1 ^ j := by
    simpa using χ.map_nsmul_eq_pow j (1 : ZMod p)
  simp_rw [show (AddChar.zmodAddEquiv r : AddChar (ZMod p) ℂ) = χ from rfl, hχ]
  have hgeom := congrArg norm (geom_sum_mul (χ 1) m)
  rw [norm_mul] at hgeom
  have hnorm : ‖χ 1 ^ m - 1‖ ≤ 2 := by
    calc
      _ ≤ ‖χ 1 ^ m‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by norm_num [norm_pow, χ.norm_apply]
  have hproduct : ‖∑ j ∈ Finset.range m, χ 1 ^ j‖ * ((K : ℝ) / p) ≤ 2 :=
    (mul_le_mul_of_nonneg_left hroot (norm_nonneg _)).trans (hgeom.le.trans hnorm)
  apply (le_div_iff₀ hKR).2
  have h := (div_le_iff₀ hp).mp (show
      ‖∑ j ∈ Finset.range m, χ 1 ^ j‖ * (K : ℝ) / p ≤ 2 by
        simpa only [mul_div_assoc] using hproduct)
  exact h

end EGZ.Expansion
