/-
Copyright (c) 2026 Joseph McKinsey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph McKinsey
-/
import Mathlib.Data.Rat.Defs

/-!
# Floating-Point Configuration

This module defines `FloatCfg`, the precision and exponent-range parameters that
describe a floating-point format, along with the available `RoundingMode`s and a
`Rounding` typeclass selecting the mode in scope.
-/

/-- A floating-point format: a precision `prec` and an exponent range
`[emin, emax]`. -/
structure FloatCfg where
  /-- The precision: the number of representable mantissa steps. -/
  prec : ℕ
  /-- The minimum exponent of the format. -/
  emin : ℤ
  /-- The maximum exponent of the format. -/
  emax : ℤ
  /-- The exponent range is nonempty. -/
  emin_lt_emax : emin < emax
  /-- The precision is positive. -/
  prec_pos : 0 < prec

/-- The supported rounding modes for converting a rational to a float. -/
inductive RoundingMode where
  /-- Round to the nearest representable value (ties to even). -/
  | nearest
  /-- Round toward negative infinity. -/
  | down
  /-- Round toward positive infinity. -/
  | up
  /-- Round toward zero. -/
  | tozero
  /-- Round away from zero (toward infinity in magnitude). -/
  | toinf

/-- A typeclass selecting the `RoundingMode` in scope. -/
class Rounding where
  /-- The rounding mode used by the operations in scope. -/
  mode : RoundingMode
