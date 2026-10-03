/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldEmbedding
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldEquiv
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldMembership
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldSurjective
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFrobeniusFixed
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitLevelMapFixed
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnits
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitsNorm
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.LevelAlgebra
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.StandardSubgroupNorm
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.UniformizerNorm
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.UnitQuotientCard
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.UnitTransport
/-!
# Reusable Lubin--Tate norm calculations in equal characteristic

Public aggregate for higher-unit norms, containment of the standard subgroup
in the finite-level norm subgroup, and the corresponding finite quotient
calculation.  The exact norm-subgroup equality, which uses finite local
reciprocity, is exported by
`LocalClassFieldTheory.LubinTateApplication`.
-/

