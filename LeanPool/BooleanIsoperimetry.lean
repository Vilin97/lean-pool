/-
Copyright (c) 2026 Alexey Milovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexey Milovanov
-/

import LeanPool.BooleanIsoperimetry.Cascade
import LeanPool.BooleanIsoperimetry.Compression
import LeanPool.BooleanIsoperimetry.Cube
import LeanPool.BooleanIsoperimetry.Harper
import LeanPool.BooleanIsoperimetry.KruskalKatona
import LeanPool.BooleanIsoperimetry.LayerWindows
import LeanPool.BooleanIsoperimetry.Macaulay
import LeanPool.BooleanIsoperimetry.MacaulayMin
import LeanPool.BooleanIsoperimetry.SetFamilyShadow
import LeanPool.BooleanIsoperimetry.Shadow
import LeanPool.BooleanIsoperimetry.SimplicialCompression

/-!
# Harper's Vertex-Isoperimetric Theorem for the Boolean Cube

Source: doi:10.1016/0012-365X(81)90009-1
Authors: Alexey Milovanov
Status: verified
Main declarations: `BooleanIsoperimetry.harper_theorem`, `BooleanIsoperimetry.harper_vertex_iso`
Tags: combinatorics, isoperimetry, boolean-cube, kruskal-katona
MSC: 05D05
-/
