/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.CoefficientEquation
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.Intertwiner
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.LinearTerm
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.RecursiveCorrection
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.Reduction
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.Series
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.StandardSeries
/-!
# Lubin--Tate formal modules

Public aggregate for the formal-series constructions used by Lubin--Tate
theory: composition, linear terms, intertwiners, coefficient equations,
reduction, the standard Lubin--Tate series, and the coefficientwise recursive
existence-and-uniqueness construction, including the resulting standard
commutative formal group and its coefficient-ring endomorphisms.
-/
