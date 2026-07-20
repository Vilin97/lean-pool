/-
Copyright (c) 2026 Ben Cassie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Cassie
-/

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Witness geometry

A direct force-magnitude form of the one-dimensional barrier-asymmetry claim: at equal
distances from the minimum, different quadratic curvatures give different restoring-force
magnitudes.
-/

open Real

/-- Direct force-magnitude form of the one-dimensional barrier-asymmetry claim: at equal
distances from the minimum, different quadratic curvatures produce different
restoring-force magnitudes. -/
theorem barrier_asymmetry_direct
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) (x : ℝ) (hx : 0 < x) :
    |(-2 * a * (-x))| ≠ |(-2 * b * x)| := by
  have hleft_pos : 0 < -2 * a * (-x) := by
    nlinarith [ha, hx]
  have hright_neg : -2 * b * x < 0 := by
    nlinarith [hb, hx]
  rw [abs_of_pos hleft_pos, abs_of_neg hright_neg]
  intro h
  have hab' : a = b := by
    nlinarith
  exact hab hab'
