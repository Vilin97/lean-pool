/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia
-/

import LeanPool.WhiteheadTheorem.Auxiliary
import LeanPool.WhiteheadTheorem.Basic
import LeanPool.WhiteheadTheorem.Compressible.CWComplex
import LeanPool.WhiteheadTheorem.Compressible.Defs
import LeanPool.WhiteheadTheorem.Compressible.Disk
import LeanPool.WhiteheadTheorem.Compressible.WeakEquiv
import LeanPool.WhiteheadTheorem.CWComplex.Basic
import LeanPool.WhiteheadTheorem.CWComplex.IProd.Def
import LeanPool.WhiteheadTheorem.CWComplex.IProd.Iso
import LeanPool.WhiteheadTheorem.Defs
import LeanPool.WhiteheadTheorem.Exponential
import LeanPool.WhiteheadTheorem.HEP.Cofibration
import LeanPool.WhiteheadTheorem.HEP.Cube
import LeanPool.WhiteheadTheorem.HEP.CubeJar
import LeanPool.WhiteheadTheorem.HEP.Retract
import LeanPool.WhiteheadTheorem.HomotopyGroup.ChangeBasePt
import LeanPool.WhiteheadTheorem.HomotopyGroup.InducedMaps
import LeanPool.WhiteheadTheorem.RelHomotopyGroup.Algebra
import LeanPool.WhiteheadTheorem.RelHomotopyGroup.Compression
import LeanPool.WhiteheadTheorem.RelHomotopyGroup.Defs
import LeanPool.WhiteheadTheorem.RelHomotopyGroup.LongExactSeq
import LeanPool.WhiteheadTheorem.Shapes.Cube
import LeanPool.WhiteheadTheorem.Shapes.CubeBoundaryMap
import LeanPool.WhiteheadTheorem.Shapes.Disk
import LeanPool.WhiteheadTheorem.Shapes.DiskHomeoCube
import LeanPool.WhiteheadTheorem.Shapes.Jar
import LeanPool.WhiteheadTheorem.Shapes.MappingCylinder
import LeanPool.WhiteheadTheorem.Shapes.Maps
import LeanPool.WhiteheadTheorem.Shapes.Pushout
import LeanPool.WhiteheadTheorem.Shapes.UnitInterval

/-!
# Whitehead's theorem for CW-complexes

Source: url:https://github.com/jzxia/WhiteheadTheorem
Authors: Jiazhen Xia
Status: verified
Main declarations: `WhiteheadTheorem`
Tags: algebraic-topology, cw-complex, homotopy-groups, weak-homotopy-equivalence
MSC: 55P10, 55Q05, 55U10
-/
