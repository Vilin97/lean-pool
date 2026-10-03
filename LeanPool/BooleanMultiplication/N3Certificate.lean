/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.SmallCases

/-!
# N3Certificate for unrestricted Boolean polynomial multiplication
-/

public section

namespace UnrestrictedBooleanMul.N3Certificate

/-- The two-element coefficient field used by the scalar certificates. -/
abbrev F2 := ZMod 2

theorem mul_self_f2 (x : F2) : x * x = x := by
  rcases f2_eq_zero_or_one x with rfl | rfl <;> simp

theorem pow_two_f2 (x : F2) : x ^ 2 = x := by
  rw [pow_two, mul_self_f2]

theorem two_eq_zero_f2 : (2 : F2) = 0 := by decide
theorem three_eq_one_f2 : (3 : F2) = 1 := by decide
theorem four_eq_zero_f2 : (4 : F2) = 0 := by decide
theorem six_eq_zero_f2 : (6 : F2) = 0 := by decide
theorem eight_eq_zero_f2 : (8 : F2) = 0 := by decide

/-- A bilinear coordinate product from two rational-basis coefficient vectors. -/
@[expose] def ab (a b : Fin 10 -> F2) (i j : Fin 10) : F2 := a i * b j

/-- The product coefficient at the squarefree monomial `{0, 1, 4}`. -/
@[expose] def c3 (a b : Fin 10 -> F2) : F2 :=
  ab a b 1 9 + ab a b 2 9 + ab a b 9 1 + ab a b 9 2

/-- The product coefficient at the squarefree monomial `{0, 4, 5}`. -/
@[expose] def c20 (a b : Fin 10 -> F2) : F2 :=
  ab a b 5 9 + ab a b 6 9 + ab a b 9 5 + ab a b 9 6

/-- The product coefficient at the squarefree monomial `{0, 1}`. -/
@[expose] def c25 (a b : Fin 10 -> F2) : F2 := ab a b 1 2 + ab a b 2 1
/-- The product coefficient at the squarefree monomial `{4, 5}`. -/
@[expose] def c30 (a b : Fin 10 -> F2) : F2 := ab a b 5 6 + ab a b 6 5

/-- Sum of product coefficients at `{0, 4}` and `{1, 3}`. -/
@[expose] def c31 (a b : Fin 10 -> F2) : F2 :=
  ab a b 1 5 + ab a b 1 9 + ab a b 2 4 + ab a b 2 9 +
  ab a b 4 2 + ab a b 4 9 + ab a b 5 1 + ab a b 5 9 +
  ab a b 9 1 + ab a b 9 2 + ab a b 9 4 + ab a b 9 5

/-- Sum of product coefficients at `{0, 5}` and `{1, 4}`. -/
@[expose] def c32 (a b : Fin 10 -> F2) : F2 :=
  ab a b 1 6 + ab a b 1 9 + ab a b 2 5 + ab a b 2 9 +
  ab a b 5 2 + ab a b 5 9 + ab a b 6 1 + ab a b 6 9 +
  ab a b 9 1 + ab a b 9 2 + ab a b 9 5 + ab a b 9 6

/-- Sum of product coefficients at `{1, 5}` and `{2, 4}`. -/
@[expose] def c34 (a b : Fin 10 -> F2) : F2 :=
  ab a b 2 6 + ab a b 2 9 + ab a b 3 5 + ab a b 3 9 +
  ab a b 5 3 + ab a b 5 9 + ab a b 6 2 + ab a b 6 9 +
  ab a b 9 2 + ab a b 9 3 + ab a b 9 5 + ab a b 9 6

/-- The first target-coordinate obstruction, detected at `{0, 4}` and `{0, 5}`. -/
@[expose] def g0 (a b : Fin 10 -> F2) : F2 :=
  ab a b 1 5 + ab a b 1 6 + ab a b 5 1 + ab a b 5 9 +
  ab a b 6 1 + ab a b 6 9 + ab a b 9 5 + ab a b 9 6

/-- The second target-coordinate obstruction, detected at `{0, 5}` and `{1, 5}`. -/
@[expose] def g1 (a b : Fin 10 -> F2) : F2 :=
  ab a b 1 6 + ab a b 1 9 + ab a b 2 6 + ab a b 2 9 +
  ab a b 6 1 + ab a b 6 2 + ab a b 9 1 + ab a b 9 2

/-- Multiplier of `c3` in the scalar certificate for `g0`. -/
def q00 (a b : Fin 10 -> F2) : F2 :=
  ab a b 2 1 + ab a b 1 2 + ab a b 4 2 + ab a b 5 2 +
  ab a b 2 4 + ab a b 9 4 + ab a b 2 5 + ab a b 9 5 +
  ab a b 4 9 + ab a b 5 9

/-- Multiplier of `c25` in the scalar certificate for `g0`. -/
def q01 (a b : Fin 10 -> F2) : F2 :=
  ab a b 5 1 + ab a b 5 2 + ab a b 1 5 + ab a b 2 5

/-- Multiplier of `c31` in the scalar certificate for `g0`. -/
def q02 (a b : Fin 10 -> F2) : F2 :=
  1 + a 2 + a 9 + ab a b 9 1 + b 2 + ab a b 2 2 + b 9 +
  ab a b 1 9 + ab a b 9 9

/-- Multiplier of `c32` in the scalar certificate for `g0`. -/
def q03 (a b : Fin 10 -> F2) : F2 :=
  a 1 + a 9 + b 1 + ab a b 1 1 + ab a b 9 1 + b 9 +
  ab a b 1 9 + ab a b 9 9

/-- Multiplier of `c20` in the scalar certificate for `g1`. -/
def q10 (a b : Fin 10 -> F2) : F2 :=
  1 + a 5 + a 6 + ab a b 6 1 + ab a b 9 1 + ab a b 6 2 +
  ab a b 9 2 + b 5 + ab a b 5 5 + b 6 + ab a b 1 6 +
  ab a b 2 6 + ab a b 6 6 + ab a b 1 9 + ab a b 2 9

/-- Multiplier of `c30` in the scalar certificate for `g1`. -/
def q11 (a b : Fin 10 -> F2) : F2 :=
  ab a b 5 2 + ab a b 6 2 + ab a b 2 5 + ab a b 2 6

/-- Multiplier of `c32` in the scalar certificate for `g1`. -/
def q12 (a b : Fin 10 -> F2) : F2 :=
  a 6 + a 9 + ab a b 9 5 + b 6 + ab a b 6 6 + b 9 +
  ab a b 5 9 + ab a b 9 9

/-- Multiplier of `c34` in the scalar certificate for `g1`. -/
def q13 (a b : Fin 10 -> F2) : F2 :=
  1 + a 5 + a 9 + b 5 + ab a b 5 5 + ab a b 9 5 + b 9 +
  ab a b 5 9 + ab a b 9 9

theorem identity0 (a b : Fin 10 -> F2) :
    g0 a b = q00 a b * c3 a b + q01 a b * c25 a b +
      q02 a b * c31 a b + q03 a b * c32 a b := by
  simp only [g0, q00, q01, q02, q03, c3, c25, c31, c32, ab]
  generalize a 1 = a₁, a 2 = a₂, a 4 = a₄, a 5 = a₅, a 6 = a₆, a 9 = a₉,
    b 1 = b₁, b 2 = b₂, b 4 = b₄, b 5 = b₅, b 6 = b₆, b 9 = b₉
  revert a₁ a₂ a₄ a₅ a₆ a₉ b₁ b₂ b₄ b₅ b₆ b₉
  decide +kernel

theorem identity1 (a b : Fin 10 -> F2) :
    g1 a b = q10 a b * c20 a b + q11 a b * c30 a b +
      q12 a b * c32 a b + q13 a b * c34 a b := by
  simp only [g1, q10, q11, q12, q13, c20, c30, c32, c34, ab]
  generalize a 1 = a₁, a 2 = a₂, a 3 = a₃, a 5 = a₅, a 6 = a₆, a 9 = a₉,
    b 1 = b₁, b 2 = b₂, b 3 = b₃, b 5 = b₅, b 6 = b₆, b 9 = b₉
  revert a₁ a₂ a₃ a₅ a₆ a₉ b₁ b₂ b₃ b₅ b₆ b₉
  decide +kernel

theorem cert0 (a b : Fin 10 -> F2)
    (h3 : c3 a b = 0) (h25 : c25 a b = 0)
    (h31 : c31 a b = 0) (h32 : c32 a b = 0) : g0 a b = 0 := by
  rw [identity0, h3, h25, h31, h32]
  ring

theorem cert1 (a b : Fin 10 -> F2)
    (h20 : c20 a b = 0) (h30 : c30 a b = 0)
    (h32 : c32 a b = 0) (h34 : c34 a b = 0) : g1 a b = 0 := by
  rw [identity1, h20, h30, h32, h34]
  ring

end UnrestrictedBooleanMul.N3Certificate
