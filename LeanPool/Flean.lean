/-
Copyright (c) 2026 Joseph McKinsey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph McKinsey
-/

import LeanPool.Flean.Basic

/-!
# Flean: Floating-Point Numbers in Lean

Source: doi:10.1109/IEEESTD.2019.8766229, url:https://github.com/josephmckinsey/flean
Authors: Joseph McKinsey
Status: verified
Main declarations: `Flean.Float`, `toFloat`, `toRat`, `to_float_to_rat`, `roundf_close`
Tags: floating-point, numerical-analysis, ieee-754, rounding
MSC: 65G50, 65G30, 68V20
-/

/-!
## Mathematical overview

This project formalizes a model of floating-point numbers in Lean 4, parameterized
by a configuration `FloatCfg` (precision and exponent range) so it can target
different precisions such as IEEE 754 binary64.

`FloatRep` and `Flean.Float` model normal and subnormal floating-point
representations, with `coeQ` interpreting a representation as a rational number.
`toFloat` and `toRat` convert between rationals and floats, and
`to_float_to_rat` establishes the round-trip correctness on finite nonzero
floats. The rounding development (`roundf`, `roundDown`, and the `IntRounder`
abstraction) culminates in error bounds such as `roundf_close`, which controls
the distance between a rational and its rounded floating-point value.
-/
