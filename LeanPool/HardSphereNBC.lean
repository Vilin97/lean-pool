/-
Copyright (c) 2026 ukiyois, OpenCode agent sessions. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ukiyois, OpenCode agent sessions
-/

import LeanPool.HardSphereNBC.GraphicMatroid
import LeanPool.HardSphereNBC.HardSphereClosePair
import LeanPool.HardSphereNBC.HardSphereCompound
import LeanPool.HardSphereNBC.HardSphereFork
import LeanPool.HardSphereNBC.HardSphereForkPackingCoordinates
import LeanPool.HardSphereNBC.HardSphereGeometry
import LeanPool.HardSphereNBC.HardSphereMeasure
import LeanPool.HardSphereNBC.HardSphereNBC
import LeanPool.HardSphereNBC.HardSphereTree
import LeanPool.HardSphereNBC.HardSphereTreeDifference
import LeanPool.HardSphereNBC.HardSphereTreeEdges
import LeanPool.HardSphereNBC.MayerNBC
import LeanPool.HardSphereNBC.NBCGraph
import LeanPool.HardSphereNBC.NBCMatroid
import LeanPool.HardSphereNBC.NBCVolume
import LeanPool.HardSphereNBC.Solution

/-!
# Hard-sphere Mayer NBC identity and fork-packing volume bound

Source: url:https://github.com/ukiyois/hs-virial-nbc-identity
Authors: ukiyois, OpenCode agent sessions
Status: verified
Main declarations: `PalomarHS.main_result`, `PalomarHS.nbc_region_real_volume_le_fork_factor`
Tags: mathematical-physics
MSC: 05C15, 82B05
-/
