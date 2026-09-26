/-
Copyright (c) 2026 ukiyois, OpenCode agent sessions. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ukiyois, OpenCode agent sessions
-/

module

public import LeanPool.HardSphereNBC.GraphicMatroid
public import LeanPool.HardSphereNBC.HardSphereClosePair
public import LeanPool.HardSphereNBC.HardSphereCompound
public import LeanPool.HardSphereNBC.HardSphereFork
public import LeanPool.HardSphereNBC.HardSphereForkPackingCoordinates
public import LeanPool.HardSphereNBC.HardSphereGeometry
public import LeanPool.HardSphereNBC.HardSphereMeasure
public import LeanPool.HardSphereNBC.HardSphereNBC
public import LeanPool.HardSphereNBC.HardSphereTree
public import LeanPool.HardSphereNBC.HardSphereTreeDifference
public import LeanPool.HardSphereNBC.HardSphereTreeEdges
public import LeanPool.HardSphereNBC.MayerNBC
public import LeanPool.HardSphereNBC.NBCGraph
public import LeanPool.HardSphereNBC.NBCMatroid
public import LeanPool.HardSphereNBC.NBCVolume
public import LeanPool.HardSphereNBC.Solution


/-!
# Hard-sphere Mayer NBC identity and fork-packing volume bound

Source: url:https://github.com/ukiyois/hs-virial-nbc-identity
Authors: ukiyois, OpenCode agent sessions
Status: verified
Main declarations: `PalomarHS.main_result`, `PalomarHS.nbc_region_real_volume_le_fork_factor`
Tags: mathematical-physics
MSC: 05C15, 82B05
-/

@[expose] public section
