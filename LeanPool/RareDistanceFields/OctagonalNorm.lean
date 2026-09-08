/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# An integer descent height for octagonal coordinates

See the project entry module for the exact coordinate restrictions and source roles.
The actual embedding is Z[zeta_8] in the complex plane. The integer height
is the field norm of the squared Euclidean norm, not the squared norm itself.
No arbitrary-real coordinate reduction is claimed.
-/

namespace LeanPool.RareDistanceFields.OctagonalNorm

/-- Four integer coefficients in the octagonal basis, grouped as two pairs. -/
abbrev Point := (ℤ × ℤ) × (ℤ × ℤ)

/-- The rational coefficient of the squared norm of the octagonal embedding. -/
def rationalPart (u : Point) : ℤ :=
  u.1.1 ^ 2 + u.1.2 ^ 2 + u.2.1 ^ 2 + u.2.2 ^ 2

/-- The coefficient of sqrt(2) in the squared norm of the octagonal embedding. -/
def irrationalPart (u : Point) : ℤ :=
  u.1.1 * (u.1.2 - u.2.2) + u.2.1 * (u.1.2 + u.2.2)

/-- The quadratic field norm of the squared Euclidean norm, an integer descent height. -/
def height (u : Point) : ℤ := rationalPart u ^ 2 - 2 * irrationalPart u ^ 2

/-- The complex embedding with basis 1, exp(pi*i/4), i, and exp(3*pi*i/4). -/
noncomputable def embed (u : Point) : ℂ :=
  ⟨(u.1.1 : ℝ) + (u.1.2 - u.2.2 : ℤ) * Real.sqrt 2 / 2,
    (u.2.1 : ℝ) + (u.1.2 + u.2.2 : ℤ) * Real.sqrt 2 / 2⟩

/-- The sum of the four integer coefficients modulo two. -/
def parity (u : Point) : ℤ := (u.1.1 + u.1.2 + u.2.1 + u.2.2) % 2

/-- Coefficient multiplication by the octagonal element `pi`. -/
def multiplyPi (u : Point) : Point :=
  ((u.1.1 + u.2.2, u.1.2 - u.1.1), (u.2.1 - u.1.2, u.2.2 - u.2.1))

/-- The translated coefficient descent map for a fixed parity class. -/
def divide (e : ℤ) (u : Point) : Point :=
  (((u.1.1 - u.1.2 - u.2.1 - u.2.2 - e) / 2, (u.1.1 + u.1.2 - u.2.1 - u.2.2 - e) / 2),
    ((u.1.1 + u.1.2 + u.2.1 - u.2.2 - e) / 2, (u.1.1 + u.1.2 + u.2.1 + u.2.2 - e) / 2))

theorem sqrt_two_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem integer_coefficients (a b : ℤ) (h : (a : ℝ) + (b : ℝ) * Real.sqrt 2 = 0) :
    a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · simp only [hb, Int.cast_zero, zero_mul, add_zero] at h
    exact ⟨by exact_mod_cast h, hb⟩
  · have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    exfalso
    apply irrational_sqrt_two.ne_rat (-(a : ℚ) / (b : ℚ))
    push_cast
    apply (eq_div_iff hb').mpr
    nlinarith

theorem integer_coefficients_equal (a b c d : ℤ)
    (h : (a : ℝ) + (b : ℝ) * Real.sqrt 2 = (c : ℝ) + (d : ℝ) * Real.sqrt 2) : a = c ∧ b = d := by
  have hh := integer_coefficients (a - c) (b - d) (by push_cast; linarith)
  omega

theorem height_squares (u : Point) : height u =
    (u.1.1 ^ 2 + u.2.1 ^ 2 - u.1.2 ^ 2 - u.2.2 ^ 2) ^ 2 +
      2 * (u.1.1 * (u.1.2 + u.2.2) - u.2.1 * (u.1.2 - u.2.2)) ^ 2 := by
  simp only [height, rationalPart, irrationalPart]
  ring

theorem height_nonneg (u : Point) : 0 ≤ height u := by
  rw [height_squares]
  positivity

theorem height_product (u : Point) : (height u : ℝ) =
    ((rationalPart u : ℝ) + (irrationalPart u : ℝ) * Real.sqrt 2)*
      ((rationalPart u : ℝ) - (irrationalPart u : ℝ) * Real.sqrt 2) := by
  simp only [height]
  push_cast
  ring_nf
  rw [sqrt_two_sq]

theorem height_eq_zero (u : Point) : height u = 0 ↔ u = 0 := by
  constructor
  · intro h
    have hz : ((rationalPart u : ℝ) + (irrationalPart u : ℝ) * Real.sqrt 2)*
        ((rationalPart u : ℝ) - (irrationalPart u : ℝ) * Real.sqrt 2) = 0 := by
      rw [←height_product, h, Int.cast_zero]
    have ha : rationalPart u = 0 := by
      rcases mul_eq_zero.mp hz with h|h
      · exact (integer_coefficients _ _ h).1
      · exact (integer_coefficients (rationalPart u) (-irrationalPart u)
          (by push_cast; linarith)).1
    dsimp [rationalPart] at ha
    have h1 : u.1.1 = 0 := by nlinarith [sq_nonneg u.1.2, sq_nonneg u.2.1, sq_nonneg u.2.2]
    have h2 : u.1.2 = 0 := by nlinarith [sq_nonneg u.1.1, sq_nonneg u.2.1, sq_nonneg u.2.2]
    have h3 : u.2.1 = 0 := by nlinarith [sq_nonneg u.1.1, sq_nonneg u.1.2, sq_nonneg u.2.2]
    have h4 : u.2.2 = 0 := by nlinarith [sq_nonneg u.1.1, sq_nonneg u.1.2, sq_nonneg u.2.1]
    exact Prod.ext (Prod.ext h1 h2) (Prod.ext h3 h4)
  · rintro rfl
    norm_num [height, rationalPart, irrationalPart]

theorem embed_sub (u v : Point) : embed (u - v) = embed u - embed v := by
  apply Complex.ext <;> simp only [embed, Complex.sub_re, Complex.sub_im, Prod.fst_sub,
    Prod.snd_sub]
  all_goals push_cast; ring

theorem squared_norm (u : Point) : Complex.normSq (embed u) =
    (rationalPart u : ℝ) + (irrationalPart u : ℝ) * Real.sqrt 2 := by
  simp only [embed, Complex.normSq_apply, rationalPart, irrationalPart]
  push_cast
  ring_nf
  rw [sqrt_two_sq]
  ring

theorem embed_injective : Function.Injective embed := by
  intro u v h
  have hh : Complex.normSq (embed (u - v)) = 0 := by rw [embed_sub, h, sub_self]; simp
  rw [squared_norm] at hh
  have hab := integer_coefficients _ _ hh
  apply sub_eq_zero.mp
  apply (height_eq_zero _).mp
  simp [height, hab.1, hab.2]

theorem distance_squared (u v : Point) : dist (embed u) (embed v) ^ 2 =
    (rationalPart (u - v) : ℝ) + (irrationalPart (u - v) : ℝ) * Real.sqrt 2 := by
  rw [Complex.dist_eq, ←Complex.normSq_eq_norm_sq, ←embed_sub, squared_norm]

theorem distance_height (u v w z : Point) (h : dist (embed u) (embed v) = dist (embed w) (embed
    z)) :
    height (u - v) = height (w - z) := by
  have hh := congrArg (fun r : ℝ => r ^ 2) h
  rw [distance_squared, distance_squared] at hh
  have hc := integer_coefficients_equal _ _ _ _ hh
  simp only [height, hc.1, hc.2]

theorem parity_zero_or_one (u : Point) : parity u = 0 ∨ parity u = 1 := by
  dsimp [parity]
  omega

theorem height_mod_two (u : Point) : height u % 2 = parity u := by
  have hs (a : ℤ) : a ^ 2 % 2 = a % 2 := by
    have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
    rcases ha with ha|ha <;> simp [pow_two, Int.mul_emod, ha]
  rw [height, Int.sub_emod, hs, Int.mul_emod]
  norm_num only [zero_mul, sub_zero, Int.emod_emod]
  have h1 := hs u.1.1
  have h2 := hs u.1.2
  have h3 := hs u.2.1
  have h4 := hs u.2.2
  dsimp [rationalPart, parity]
  omega

theorem height_even_iff (u v : Point) : 2∣height (u - v) ↔ parity u = parity v := by
  rw [Int.dvd_iff_emod_eq_zero, height_mod_two]
  dsimp [parity]
  omega

theorem height_multiplyPi (u : Point) : height (multiplyPi u) = 2 * height u := by
  simp only [height, rationalPart, irrationalPart, multiplyPi]
  ring

theorem divide_difference (e : ℤ) (u v : Point) (hu : parity u = e) (hv : parity v = e) :
    multiplyPi (divide e u - divide e v) = u - v := by
  dsimp [parity] at hu hv
  apply Prod.ext <;> apply Prod.ext
  all_goals dsimp [multiplyPi, divide]; omega

theorem divide_height (e : ℤ) (u v : Point) (hu : parity u = e) (hv : parity v = e) :
    height (u - v) = 2 * height (divide e u - divide e v) := by
  rw [←height_multiplyPi, divide_difference e u v hu hv]

/-- The nonzero octagonal element 1 - exp(pi*i/4) used for descent. -/
noncomputable def pi : ℂ := embed ((1, -1), (0, 0))

theorem embed_zero : embed 0 = 0 := by
  apply Complex.ext <;> simp [embed]

theorem pi_ne_zero : pi ≠ 0 := by
  intro h
  have hh : (((1, -1), (0, 0)) : Point) = 0 := embed_injective (h.trans embed_zero.symm)
  norm_num at hh

theorem embed_multiplyPi (u : Point) : embed (multiplyPi u) = pi * embed u := by
  apply Complex.ext
  all_goals simp only [embed, multiplyPi, pi, Complex.mul_re, Complex.mul_im]
  all_goals push_cast; ring_nf; rw [sqrt_two_sq]
  all_goals ring

theorem divide_distance (e : ℤ) (u v : Point) (hu : parity u = e) (hv : parity v = e) :
    dist (embed u) (embed v) = ‖pi‖ * dist (embed (divide e u)) (embed (divide e v)) := by
  rw [Complex.dist_eq, ←embed_sub, ←divide_difference e u v hu hv, embed_multiplyPi,
    Complex.norm_mul, embed_sub, ←Complex.dist_eq]

theorem height_symmetric (u v : Point) : height (u - v) = height (v - u) := by
  simp only [height, rationalPart, irrationalPart, Prod.fst_sub, Prod.snd_sub]
  ring

end LeanPool.RareDistanceFields.OctagonalNorm
