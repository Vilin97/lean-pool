/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia
-/
module

public import LeanPool.WhiteheadTheorem.Auxiliary
public import LeanPool.WhiteheadTheorem.Basic
public import LeanPool.WhiteheadTheorem.Compressible.CWComplex
public import LeanPool.WhiteheadTheorem.Compressible.Defs
public import LeanPool.WhiteheadTheorem.Compressible.Disk
public import LeanPool.WhiteheadTheorem.Compressible.WeakEquiv
public import LeanPool.WhiteheadTheorem.CWComplex.Basic
public import LeanPool.WhiteheadTheorem.CWComplex.IProd.Def
public import LeanPool.WhiteheadTheorem.CWComplex.IProd.Iso
public import LeanPool.WhiteheadTheorem.Defs
public import LeanPool.WhiteheadTheorem.Exponential
public import LeanPool.WhiteheadTheorem.HEP.Cofibration
public import LeanPool.WhiteheadTheorem.HEP.Cube
public import LeanPool.WhiteheadTheorem.HEP.CubeJar
public import LeanPool.WhiteheadTheorem.HEP.Retract
public import LeanPool.WhiteheadTheorem.HomotopyGroup.ChangeBasePt
public import LeanPool.WhiteheadTheorem.HomotopyGroup.InducedMaps
public import LeanPool.WhiteheadTheorem.RelHomotopyGroup.Algebra
public import LeanPool.WhiteheadTheorem.RelHomotopyGroup.Compression
public import LeanPool.WhiteheadTheorem.RelHomotopyGroup.Defs
public import LeanPool.WhiteheadTheorem.RelHomotopyGroup.LongExactSeq
public import LeanPool.WhiteheadTheorem.Shapes.Cube
public import LeanPool.WhiteheadTheorem.Shapes.CubeBoundaryMap
public import LeanPool.WhiteheadTheorem.Shapes.Disk
public import LeanPool.WhiteheadTheorem.Shapes.DiskHomeoCube
public import LeanPool.WhiteheadTheorem.Shapes.Jar
public import LeanPool.WhiteheadTheorem.Shapes.MappingCylinder
public import LeanPool.WhiteheadTheorem.Shapes.Maps
public import LeanPool.WhiteheadTheorem.Shapes.Pushout
public import LeanPool.WhiteheadTheorem.Shapes.UnitInterval
import Mathlib.Tactic.Measurability.Init

/-!
# Whitehead's theorem for CW-complexes

Source: url:https://github.com/jzxia/WhiteheadTheorem
Authors: Jiazhen Xia
Status: verified
Main declarations: `WhiteheadTheorem`
Tags: algebraic-topology, cw-complex, homotopy-groups, weak-homotopy-equivalence
MSC: 55P10, 55Q05, 55U10
-/

@[expose] public section
