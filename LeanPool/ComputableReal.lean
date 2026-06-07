/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import LeanPool.ComputableReal.ComputableRSeq
import LeanPool.ComputableReal.ComputableReal
import LeanPool.ComputableReal.IsComputable
import LeanPool.ComputableReal.IsComputableC
import LeanPool.ComputableReal.SpecialFunctions

/-!
# Computable real numbers

Source: url:https://github.com/Timeroot/computableReal
Authors: Alex Meiburg
Status: verified
Main declarations: `LeanPool.ComputableReal.ComputableℝSeq`, `LeanPool.ComputableReal.Computableℝ`, `LeanPool.ComputableReal.IsComputable`, `LeanPool.ComputableReal.Computableℝ.instField`, `LeanPool.ComputableReal.ComputableℝSeq.Sqrt.sqrtq`
Tags: computable-reals, interval-arithmetic, native-decide, real-numbers

A framework for proving statements about concrete real numbers by computation: a
`ComputableℝSeq` carries converging rational lower/upper bounds, these are quotiented
into a field `Computableℝ`, and an `IsComputable` typeclass lets `native_decide`
discharge inequalities involving `Real.sqrt`, `Real.exp`, `Real.pi`, and more.
-/
