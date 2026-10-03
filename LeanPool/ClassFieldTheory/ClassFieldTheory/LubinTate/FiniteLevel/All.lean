/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.ChangedLevelCompositum
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.ChangedPrimitiveEvaluation
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.ChangedUniformizer
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.CompletedEvaluation
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.CompletedIterates
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.FiniteParameterFiltration
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.FiniteParameters
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.GaloisParameterFiltration
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.HerbrandFormula
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.HigherUnitLevelEquiv
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.LevelAbelian
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.LevelAutomorphisms
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.LevelFieldTower
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.LevelValuation
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.LocalUpperRamification
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.LowerRamification
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.LowerRamificationFormula
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.NormSubgroup
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.NormUniformizer
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.ParameterCongruence
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveAction
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveDisplacement
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveEisenstein
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveRoot
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveTorsion
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveUniformizer
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FiniteLevel.UpperRamification
/-!
# General finite-level Lubin--Tate theory

Public aggregate for the characteristic-independent standard division
polynomials, primitive torsion fields, analytic formal-module action, explicit
finite Galois parameterization, integral-closure valuation, ramification
filtrations and their Herbrand formula, level-field tower, and the norm of a
primitive uniformizer.  It also exports stability of a standard level under
a principal-unit change of its defining uniformizer.
-/

