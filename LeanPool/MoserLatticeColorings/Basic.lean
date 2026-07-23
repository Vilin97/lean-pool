/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Geometric four-colorings of the Moser lattice

This file formalizes the lattice part of Theorem 3.1 of Ákos Dúcz,
*A note on geometric colorings of the Moser lattice*, arXiv:2606.12325.
It derives the exact squared-norm formula, defines both parity colorings from
the paper, and proves that each is proper and geometric on the whole lattice.

The uniqueness assertion in Theorem 3.2 is not formalized here.
-/

namespace LeanPool.MoserLatticeColorings

open SimpleGraph

/-- The Euclidean plane with its standard metric. -/
abbrev R2 := EuclideanSpace ℝ (Fin 2)

/-- Integer coordinates in the basis `1, omega_1, omega_3, omega_1 * omega_3`. -/
structure Coeff where
  /-- Coefficient of `1`. -/
  a : ℤ
  /-- Coefficient of `omega_1`. -/
  b : ℤ
  /-- Coefficient of `omega_3`. -/
  c : ℤ
  /-- Coefficient of `omega_1 * omega_3`. -/
  d : ℤ
deriving DecidableEq

namespace Coeff

/-- Coordinatewise subtraction. -/
def sub (p q : Coeff) : Coeff :=
  ⟨p.a - q.a, p.b - q.b, p.c - q.c, p.d - q.d⟩

/-- Rational coefficient in six times the squared norm. -/
def normRational (p : Coeff) : ℤ :=
  6 * (p.a ^ 2 + p.a * p.b + p.b ^ 2 + p.c ^ 2 + p.c * p.d + p.d ^ 2) +
    10 * p.a * p.c + 5 * p.a * p.d + 5 * p.b * p.c + 10 * p.b * p.d

/-- `sqrt 33` coefficient in six times the squared norm. -/
def normRadical (p : Coeff) : ℤ := p.b * p.c - p.a * p.d

/-- The Euclidean coordinates of
`a + b * ω₁ + c * ω₃ + d * ω₁ * ω₃`, where
`ω₁ = 1 / 2 + i * √3 / 2` and `ω₃ = 5 / 6 + i * √11 / 6`. -/
noncomputable def toR2 (p : Coeff) : R2 :=
  WithLp.toLp 2 ![
    ((12 * p.a + 6 * p.b + 10 * p.c + 5 * p.d : ℤ) : ℝ) / 12 -
      (p.d : ℝ) * Real.sqrt 33 / 12,
    (3 * ((6 * p.b + 5 * p.d : ℤ) : ℝ) +
      ((2 * p.c + p.d : ℤ) : ℝ) * Real.sqrt 33) /
        (12 * Real.sqrt 3)]

@[simp] lemma toR2_zero (p : Coeff) :
    p.toR2 0 =
      ((12 * p.a + 6 * p.b + 10 * p.c + 5 * p.d : ℤ) : ℝ) / 12 -
        (p.d : ℝ) * Real.sqrt 33 / 12 := rfl

@[simp] lemma toR2_one (p : Coeff) :
    p.toR2 1 =
      (3 * ((6 * p.b + 5 * p.d : ℤ) : ℝ) +
        ((2 * p.c + p.d : ℤ) : ℝ) * Real.sqrt 33) /
          (12 * Real.sqrt 3) := rfl

lemma dist_sq (p q : Coeff) :
    dist p.toR2 q.toR2 ^ 2 =
      ((p.sub q).normRational : ℝ) / 6 +
        ((p.sub q).normRadical : ℝ) * Real.sqrt 33 / 6 := by
  rw [PiLp.dist_sq_eq_of_L2]
  simp only [Fin.sum_univ_two, toR2_zero, toR2_one, Real.dist_eq, sq_abs]
  have hs3 : Real.sqrt 3 * Real.sqrt 3 = 3 :=
    Real.mul_self_sqrt (by norm_num)
  have hs33 : Real.sqrt 33 * Real.sqrt 33 = 33 :=
    Real.mul_self_sqrt (by norm_num)
  have hs3ne : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  simp only [Coeff.sub, normRational, normRadical, Int.cast_add, Int.cast_sub,
    Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
  field_simp [hs3ne]
  ring_nf
  rw [show Real.sqrt 3 ^ 2 = 3 by nlinarith,
    show Real.sqrt 33 ^ 2 = 33 by nlinarith]
  ring

/-- Ducz's first parity coloring. -/
def color (p : Coeff) : ZMod 2 × ZMod 2 :=
  (p.a + p.b + p.d, p.a + p.c + p.d)

lemma color_sub_eq_zero_of_eq {p q : Coeff} (h : color p = color q) :
    color (p.sub q) = 0 := by
  have hfst := congrArg Prod.fst h
  have hsnd := congrArg Prod.snd h
  ext
  · simp only [color, Coeff.sub]
    simp at ⊢
    simp only [color] at hfst
    linear_combination hfst
  · simp only [color, Coeff.sub]
    simp at ⊢
    simp only [color] at hsnd
    linear_combination hsnd

lemma color_sub_eq_zero_iff (p q : Coeff) :
    color (p.sub q) = 0 ↔ color p = color q := by
  constructor
  · intro h
    have hfst := congrArg Prod.fst h
    have hsnd := congrArg Prod.snd h
    simp only [color, Coeff.sub] at hfst hsnd
    simp at hfst hsnd
    ext
    · simp only [color] at ⊢
      linear_combination hfst
    · simp only [color] at ⊢
      linear_combination hsnd
  · exact color_sub_eq_zero_of_eq

lemma norm_sum_dvd_eight_of_color_zero {p : Coeff} (h : color p = 0) :
    (8 : ℤ) ∣ p.normRational + p.normRadical := by
  have h₁ : (2 : ℤ) ∣ p.a + p.b + p.d := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
    simpa [color] using congrArg Prod.fst h
  have h₂ : (2 : ℤ) ∣ p.a + p.c + p.d := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
    simpa [color] using congrArg Prod.snd h
  obtain ⟨u, hu⟩ := h₁
  obtain ⟨v, hv⟩ := h₂
  have hb : p.b = 2 * u - p.a - p.d := by omega
  have hc : p.c = 2 * v - p.a - p.d := by omega
  refine ⟨p.a ^ 2 + p.a * p.d - 3 * p.a * u - 2 * p.a * v +
      p.d ^ 2 - 2 * p.d * u - 3 * p.d * v + 3 * u ^ 2 +
      3 * u * v + 3 * v ^ 2, ?_⟩
  simp only [normRational, normRadical]
  rw [hb, hc]
  ring

private def parityReduction : ZMod 4 →+* ZMod 2 :=
  ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)

private lemma color_residue_table (a b c d : ZMod 4) :
    (parityReduction (a + b + d), parityReduction (a + c + d)) = 0 ↔
      6 * (a ^ 2 + a * b + b ^ 2 + c ^ 2 + c * d + d ^ 2) +
        10 * a * c + 5 * a * d + 5 * b * c + 10 * b * d +
          (b * c - a * d) = 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide

lemma color_eq_zero_iff_norm_sum_dvd_four (p : Coeff) :
    color p = 0 ↔ (4 : ℤ) ∣ p.normRational + p.normRadical := by
  change color p = 0 ↔ ((4 : ℕ) : ℤ) ∣ p.normRational + p.normRadical
  rw [(ZMod.intCast_zmod_eq_zero_iff_dvd
    (p.normRational + p.normRadical) 4).symm]
  simpa [color, normRational, normRadical, parityReduction,
    ZMod.castHom_apply] using
      color_residue_table (p.a : ZMod 4) (p.b : ZMod 4)
        (p.c : ZMod 4) (p.d : ZMod 4)

lemma unit_norm_coefficients {p : Coeff}
    (h : ((p.normRational : ℝ) + (p.normRadical : ℝ) * Real.sqrt 33) / 6 = 1) :
    p.normRational = 6 ∧ p.normRadical = 0 := by
  have hirr : Irrational (Real.sqrt 33) := by norm_num
  by_cases hm : p.normRadical = 0
  · constructor
    · have hcast : (p.normRational : ℝ) = 6 := by
        rw [hm] at h
        norm_num at h
        linarith
      exact Int.cast_injective hcast
    · exact hm
  · exfalso
    have hmR : (p.normRadical : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
    have hsqrt : Real.sqrt 33 =
        ((6 - p.normRational : ℤ) : ℝ) / (p.normRadical : ℝ) := by
      apply (eq_div_iff hmR).2
      field_simp at h
      push_cast
      nlinarith
    exact hirr.ne_rational (6 - p.normRational) p.normRadical hsqrt

lemma radical_coordinates_unique {a b c d : ℤ}
    (h : (a : ℝ) + (b : ℝ) * Real.sqrt 33 =
      (c : ℝ) + (d : ℝ) * Real.sqrt 33) :
    a = c ∧ b = d := by
  have hirr : Irrational (Real.sqrt 33) := by norm_num
  by_cases hbd : b = d
  · constructor
    · subst d
      exact_mod_cast (by linarith : (a : ℝ) = c)
    · exact hbd
  · exfalso
    have hden : ((b - d : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr (sub_ne_zero.mpr hbd)
    have hsqrt : Real.sqrt 33 = ((c - a : ℤ) : ℝ) / ((b - d : ℤ) : ℝ) := by
      apply (eq_div_iff hden).2
      push_cast
      linarith
    exact hirr.ne_rational (c - a) (b - d) hsqrt


/-- The four integer coordinates give a faithful presentation of the Moser lattice. -/
theorem toR2_injective : Function.Injective toR2 := by
  intro p q h
  have hx := congrArg (fun x : R2 => x 0) h
  have hy := congrArg (fun x : R2 => x 1) h
  simp only [toR2_zero] at hx
  simp only [toR2_one] at hy
  have hxrad :
      (((12 * p.a + 6 * p.b + 10 * p.c + 5 * p.d) -
          (12 * q.a + 6 * q.b + 10 * q.c + 5 * q.d) : ℤ) : ℝ) +
        ((q.d - p.d : ℤ) : ℝ) * Real.sqrt 33 = 0 := by
    push_cast at hx ⊢
    linear_combination 12 * hx
  have hxc := radical_coordinates_unique
    (a := (12 * p.a + 6 * p.b + 10 * p.c + 5 * p.d) -
      (12 * q.a + 6 * q.b + 10 * q.c + 5 * q.d))
    (b := q.d - p.d) (c := 0) (d := 0) (by simpa using hxrad)
  have hd : p.d = q.d := by omega
  have hyrad :
      ((18 * (p.b - q.b) : ℤ) : ℝ) +
        ((2 * (p.c - q.c) : ℤ) : ℝ) * Real.sqrt 33 = 0 := by
    have hs3ne : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    push_cast at hy ⊢
    field_simp [hs3ne] at hy
    rw [hd] at hy
    linear_combination hy
  have hyc := radical_coordinates_unique
    (a := 18 * (p.b - q.b)) (b := 2 * (p.c - q.c))
    (c := 0) (d := 0) (by simpa using hyrad)
  have hb : p.b = q.b := by omega
  have hc : p.c = q.c := by omega
  have ha : p.a = q.a := by
    rw [hb, hc, hd] at hxc
    omega
  cases p
  cases q
  simp_all

lemma norm_coordinates_eq_of_sqNorm_eq {p q : Coeff}
    (h : ((p.normRational : ℝ) + (p.normRadical : ℝ) * Real.sqrt 33) / 6 =
      ((q.normRational : ℝ) + (q.normRadical : ℝ) * Real.sqrt 33) / 6) :
    p.normRational = q.normRational ∧ p.normRadical = q.normRadical := by
  apply radical_coordinates_unique
  linarith

/-- A coloring is geometric when equality of colors for a pair depends only
on the Euclidean distance between the pair. -/
def IsGeometricColoring {κ : Type*} (f : Coeff → κ) : Prop :=
  ∀ p q r s : Coeff,
    dist p.toR2 q.toR2 = dist r.toR2 s.toR2 →
      (f p = f q ↔ f r = f s)

theorem color_isGeometric : IsGeometricColoring color := by
  intro p q r s hdist
  have hsq : dist p.toR2 q.toR2 ^ 2 = dist r.toR2 s.toR2 ^ 2 :=
    congrArg (fun x : ℝ => x ^ 2) hdist
  rw [dist_sq, dist_sq] at hsq
  have hcoords := norm_coordinates_eq_of_sqNorm_eq (by
    convert hsq using 1
    all_goals ring)
  rw [← color_sub_eq_zero_iff p q, ← color_sub_eq_zero_iff r s,
    color_eq_zero_iff_norm_sum_dvd_four,
    color_eq_zero_iff_norm_sum_dvd_four, hcoords.1, hcoords.2]

/-- Ducz's second parity coloring. -/
def colorTwo (p : Coeff) : ZMod 2 × ZMod 2 :=
  (p.a + p.d, p.b + p.c + p.d)

lemma colorTwo_sub_eq_zero_iff (p q : Coeff) :
    colorTwo (p.sub q) = 0 ↔ colorTwo p = colorTwo q := by
  constructor
  · intro h
    have hfst := congrArg Prod.fst h
    have hsnd := congrArg Prod.snd h
    simp only [colorTwo, Coeff.sub] at hfst hsnd
    simp at hfst hsnd
    ext
    · simp only [colorTwo] at ⊢
      linear_combination hfst
    · simp only [colorTwo] at ⊢
      linear_combination hsnd
  · intro h
    have hfst := congrArg Prod.fst h
    have hsnd := congrArg Prod.snd h
    ext
    · simp only [colorTwo, Coeff.sub]
      simp at ⊢
      simp only [colorTwo] at hfst
      linear_combination hfst
    · simp only [colorTwo, Coeff.sub]
      simp at ⊢
      simp only [colorTwo] at hsnd
      linear_combination hsnd

private lemma colorTwo_residue_table (a b c d : ZMod 4) :
    (parityReduction (a + d), parityReduction (b + c + d)) = 0 ↔
      6 * (a ^ 2 + a * b + b ^ 2 + c ^ 2 + c * d + d ^ 2) +
        10 * a * c + 5 * a * d + 5 * b * c + 10 * b * d -
          (b * c - a * d) = 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide

lemma colorTwo_eq_zero_iff_norm_diff_dvd_four (p : Coeff) :
    colorTwo p = 0 ↔ (4 : ℤ) ∣ p.normRational - p.normRadical := by
  change colorTwo p = 0 ↔ ((4 : ℕ) : ℤ) ∣ p.normRational - p.normRadical
  rw [(ZMod.intCast_zmod_eq_zero_iff_dvd
    (p.normRational - p.normRadical) 4).symm]
  simpa [colorTwo, normRational, normRadical, parityReduction,
    ZMod.castHom_apply] using
      colorTwo_residue_table (p.a : ZMod 4) (p.b : ZMod 4)
        (p.c : ZMod 4) (p.d : ZMod 4)

lemma colorTwo_ne_of_dist_eq_one {p q : Coeff} (h : dist p.toR2 q.toR2 = 1) :
    colorTwo p ≠ colorTwo q := by
  intro heq
  have hcolor : colorTwo (p.sub q) = 0 :=
    (colorTwo_sub_eq_zero_iff p q).2 heq
  have hdiv : (4 : ℤ) ∣
      (p.sub q).normRational - (p.sub q).normRadical :=
    (colorTwo_eq_zero_iff_norm_diff_dvd_four _).1 hcolor
  have hformula := dist_sq p q
  have hunit : ((p.sub q).normRational : ℝ) / 6 +
      ((p.sub q).normRadical : ℝ) * Real.sqrt 33 / 6 = 1 := by
    rw [h] at hformula
    norm_num at hformula
    linarith
  have hcoeff := unit_norm_coefficients (p := p.sub q) (by
    convert hunit using 1
    all_goals ring)
  rw [hcoeff.1, hcoeff.2] at hdiv
  norm_num at hdiv

theorem colorTwo_isGeometric : IsGeometricColoring colorTwo := by
  intro p q r s hdist
  have hsq : dist p.toR2 q.toR2 ^ 2 = dist r.toR2 s.toR2 ^ 2 :=
    congrArg (fun x : ℝ => x ^ 2) hdist
  rw [dist_sq, dist_sq] at hsq
  have hcoords := norm_coordinates_eq_of_sqNorm_eq (by
    convert hsq using 1
    all_goals ring)
  rw [← colorTwo_sub_eq_zero_iff p q, ← colorTwo_sub_eq_zero_iff r s,
    colorTwo_eq_zero_iff_norm_diff_dvd_four,
    colorTwo_eq_zero_iff_norm_diff_dvd_four, hcoords.1, hcoords.2]

lemma color_ne_of_dist_eq_one {p q : Coeff} (h : dist p.toR2 q.toR2 = 1) :
    color p ≠ color q := by
  intro heq
  have hcolor : color (p.sub q) = 0 := color_sub_eq_zero_of_eq heq
  have hdiv := norm_sum_dvd_eight_of_color_zero hcolor
  have hsq : dist p.toR2 q.toR2 ^ 2 = 1 := by rw [h]; norm_num
  have hformula := dist_sq p q
  have hunit : ((p.sub q).normRational : ℝ) / 6 +
      ((p.sub q).normRadical : ℝ) * Real.sqrt 33 / 6 = 1 := by
    linarith
  have hcoeff := unit_norm_coefficients (p := p.sub q) (by
    convert hunit using 1
    all_goals ring)
  rw [hcoeff.1, hcoeff.2] at hdiv
  norm_num at hdiv

/-- Unit-distance graph induced by the entire Moser lattice. -/
def unitDistanceGraph : SimpleGraph Coeff :=
  SimpleGraph.fromRel fun p q => dist p.toR2 q.toR2 = 1

/-- Dúcz's first parity map as a proper four-coloring. -/
noncomputable def coloring : unitDistanceGraph.Coloring (ZMod 2 × ZMod 2) :=
  SimpleGraph.Coloring.mk color fun {p q} h => by
    unfold unitDistanceGraph at h
    rw [SimpleGraph.fromRel_adj] at h
    rcases h.2 with hpq | hqp
    · exact color_ne_of_dist_eq_one hpq
    · exact color_ne_of_dist_eq_one (dist_comm q.toR2 p.toR2 ▸ hqp)

theorem colorable_four : unitDistanceGraph.Colorable 4 := by
  simpa using coloring.colorable

/-- Dúcz's second parity map as a proper four-coloring. -/
noncomputable def coloringTwo : unitDistanceGraph.Coloring (ZMod 2 × ZMod 2) :=
  SimpleGraph.Coloring.mk colorTwo fun {p q} h => by
    unfold unitDistanceGraph at h
    rw [SimpleGraph.fromRel_adj] at h
    rcases h.2 with hpq | hqp
    · exact colorTwo_ne_of_dist_eq_one hpq
    · exact colorTwo_ne_of_dist_eq_one (dist_comm q.toR2 p.toR2 ▸ hqp)

/-- Integer scaling of a coefficient vector. -/
def scale (n : ℤ) (p : Coeff) : Coeff :=
  ⟨n * p.a, n * p.b, n * p.c, n * p.d⟩

/-- The zero coefficient vector. -/
def zero : Coeff := ⟨0, 0, 0, 0⟩

lemma sub_zero (p : Coeff) : p.sub zero = p := by
  cases p
  simp [Coeff.sub, zero]

lemma toR2_zero_coeff : zero.toR2 = 0 := by
  ext i
  fin_cases i <;> simp [zero, toR2]

lemma toR2_scale (n : ℤ) (p : Coeff) :
    (scale n p).toR2 = (n : ℝ) • p.toR2 := by
  ext i
  fin_cases i <;> simp [scale, toR2] <;> ring

lemma toR2_sub (p q : Coeff) :
    (p.sub q).toR2 = p.toR2 - q.toR2 := by
  ext i
  fin_cases i <;> simp [Coeff.sub, toR2] <;> ring

lemma color_scale_three_pow (k : ℕ) (p : Coeff) :
    color (scale ((3 : ℤ) ^ k) p) = color p := by
  have hthree : (3 : ZMod 2) = 1 := by decide
  ext <;> simp [color, scale, hthree]

lemma colorTwo_scale_three_pow (k : ℕ) (p : Coeff) :
    colorTwo (scale ((3 : ℤ) ^ k) p) = colorTwo p := by
  have hthree : (3 : ZMod 2) = 1 := by decide
  ext <;> simp [colorTwo, scale, hthree]

end Coeff

end LeanPool.MoserLatticeColorings
