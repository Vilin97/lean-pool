/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/

import LeanPool.BrauerGroupNew.CentralSimple
import LeanPool.BrauerGroupNew.Centralizer
import LeanPool.BrauerGroupNew.CrossProductAlgebra
import LeanPool.BrauerGroupNew.ExtendScalar
import LeanPool.BrauerGroupNew.Azumaya.Basic
import LeanPool.BrauerGroupNew.Azumaya.Mul
import LeanPool.BrauerGroupNew.Examples.ShortComplex.LeftHomologyMapData
import LeanPool.BrauerGroupNew.FieldCat
import LeanPool.BrauerGroupNew.AlgClosedUnion
import LeanPool.BrauerGroupNew.FiniteField
import LeanPool.BrauerGroupNew.BrauerGroup
import LeanPool.BrauerGroupNew.LemmasAboutSimpleRing
import LeanPool.BrauerGroupNew.MatrixCenterEquiv
import LeanPool.BrauerGroupNew.MatrixEquivTensor
import LeanPool.BrauerGroupNew.Morita.ChangeOfRings
import LeanPool.BrauerGroupNew.Morita.TensorProduct
import LeanPool.BrauerGroupNew.MoritaEquivalence
import LeanPool.BrauerGroupNew.SplittingOfCSA
import LeanPool.BrauerGroupNew.TwoSidedIdeal
import LeanPool.BrauerGroupNew.Wedderburn
import LeanPool.BrauerGroupNew.ZeroSevenFourE
import LeanPool.BrauerGroupNew.RelativeBrauer
import LeanPool.BrauerGroupNew.SkolemNoether
import LeanPool.BrauerGroupNew.ToSecond
import LeanPool.BrauerGroupNew.IsoSecond
import LeanPool.BrauerGroupNew.AbsoluteIsoH2
import LeanPool.BrauerGroupNew.DoubleCentralizer
import LeanPool.BrauerGroupNew.FrobeniusTheorem
import LeanPool.BrauerGroupNew.BrauerOverR
import LeanPool.BrauerGroupNew.Mathlib
import LeanPool.BrauerGroupNew.Subfield

/-!
# Brauer Group Core

Source: url:https://doi.org/10.1017/9781107359419
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
Status: verified
Main declarations: `BrauerGroup.BruaerGroup`, `BrauerGroupHom.Br`, `WedderburnArtin`
Tags: algebra, ring-theory, central-simple-algebras, brauer-groups
MSC: 16K20, 16K50, 16S35
-/
