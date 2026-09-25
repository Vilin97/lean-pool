/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.CoefficientEquation
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.Intertwiner
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.LinearTerm
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.RecursiveCorrection
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.Reduction
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.Series
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.StandardSeries
/-!
# Lubin--Tate formal modules

Public aggregate for the formal-series constructions used by Lubin--Tate
theory: composition, linear terms, intertwiners, coefficient equations,
reduction, the standard Lubin--Tate series, and the coefficientwise recursive
existence-and-uniqueness construction, including the resulting standard
commutative formal group and its coefficient-ring endomorphisms.
-/

@[expose] public section
