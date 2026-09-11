/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/
module

public import LeanPool.BrauerGroupNew.CentralSimple
public import LeanPool.BrauerGroupNew.Centralizer
public import LeanPool.BrauerGroupNew.CrossProductAlgebra
public import LeanPool.BrauerGroupNew.ExtendScalar
public import LeanPool.BrauerGroupNew.Azumaya.Basic
public import LeanPool.BrauerGroupNew.Azumaya.Mul
public import LeanPool.BrauerGroupNew.Examples.ShortComplex.LeftHomologyMapData
public import LeanPool.BrauerGroupNew.FieldCat
public import LeanPool.BrauerGroupNew.AlgClosedUnion
public import LeanPool.BrauerGroupNew.FiniteField
public import LeanPool.BrauerGroupNew.BrauerGroup
public import LeanPool.BrauerGroupNew.LemmasAboutSimpleRing
public import LeanPool.BrauerGroupNew.MatrixCenterEquiv
public import LeanPool.BrauerGroupNew.MatrixEquivTensor
public import LeanPool.BrauerGroupNew.Morita.ChangeOfRings
public import LeanPool.BrauerGroupNew.Morita.TensorProduct
public import LeanPool.BrauerGroupNew.MoritaEquivalence
public import LeanPool.BrauerGroupNew.SplittingOfCSA
public import LeanPool.BrauerGroupNew.TwoSidedIdeal
public import LeanPool.BrauerGroupNew.Wedderburn
public import LeanPool.BrauerGroupNew.ZeroSevenFourE
public import LeanPool.BrauerGroupNew.RelativeBrauer
public import LeanPool.BrauerGroupNew.SkolemNoether
public import LeanPool.BrauerGroupNew.ToSecond
public import LeanPool.BrauerGroupNew.IsoSecond
public import LeanPool.BrauerGroupNew.AbsoluteIsoH2
public import LeanPool.BrauerGroupNew.DoubleCentralizer
public import LeanPool.BrauerGroupNew.FrobeniusTheorem
public import LeanPool.BrauerGroupNew.BrauerOverR
public import LeanPool.BrauerGroupNew.Mathlib
public import LeanPool.BrauerGroupNew.Subfield

/-!
# Brauer Group Core

Source: url:https://doi.org/10.1017/9781316661277
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
Status: verified
Main declarations: `BrauerGroup.BruaerGroup`, `BrauerGroupHom.Br`, `WedderburnArtin`
Tags: algebra, ring-theory, central-simple-algebras, brauer-groups
MSC: 16K20, 16K50, 16S35
-/

@[expose] public section
