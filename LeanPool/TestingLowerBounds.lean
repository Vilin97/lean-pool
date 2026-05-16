/-
Copyright (c) 2026 Rémy Degenne, Lorenzo Luccioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/

import LeanPool.TestingLowerBounds.ForMathlib.AbsolutelyContinuous
import LeanPool.TestingLowerBounds.ForMathlib.CountableOrCountablyGenerated
import LeanPool.TestingLowerBounds.ForMathlib.EReal
import LeanPool.TestingLowerBounds.ForMathlib.Integrable
import LeanPool.TestingLowerBounds.ForMathlib.KernelFstSnd
import LeanPool.TestingLowerBounds.ForMathlib.MaxMinEqAbs
import LeanPool.TestingLowerBounds.Kernel.Deterministic

/-!
# Lower bounds for hypothesis testing based on information theory

Source: url:https://github.com/RemyDegenne/testing-lower-bounds
Authors: Rémy Degenne, Lorenzo Luccioli
Status: verified
Main declarations: `ProbabilityTheory.Kernel.fst'`, `ProbabilityTheory.Kernel.snd'`
Tags: probability, information-theory, measure-theory
MSC: 62F03, 62B10, 94A17, 60A10
-/
