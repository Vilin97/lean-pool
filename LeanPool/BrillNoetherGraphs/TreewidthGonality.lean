/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


-- Treewidth and gonality: the van Dobben de Bruyn--Gijswijt theorem
-- `treewidth <= gonality` (arXiv:1407.7055) and the Seymour--Thomas
-- bramble/treewidth duality it rests on.
--
-- This application library imports only `Utilities` and external dependencies.
-- Its declarations use the `Utilities.Treewidth` and `Utilities.Gonality`
-- namespaces.

-- Tree decompositions, brambles, and Seymour--Thomas duality.
public import LeanPool.BrillNoetherGraphs.TreewidthGonality.Treewidth.TreeDecomposition
public import LeanPool.BrillNoetherGraphs.TreewidthGonality.Treewidth.Bramble
public import LeanPool.BrillNoetherGraphs.TreewidthGonality.Treewidth.PartialDecomposition
public import LeanPool.BrillNoetherGraphs.TreewidthGonality.Treewidth.TreePath
public import LeanPool.BrillNoetherGraphs.TreewidthGonality.Treewidth.Separation
public import LeanPool.BrillNoetherGraphs.TreewidthGonality.Treewidth.SeymourThomasInduction
public import LeanPool.BrillNoetherGraphs.TreewidthGonality.Treewidth.SeymourThomas

-- The divisor-theoretic half, and the assembled theorem.
public import LeanPool.BrillNoetherGraphs.TreewidthGonality.Gonality.BrambleGonality
public import LeanPool.BrillNoetherGraphs.TreewidthGonality.Gonality.TreewidthGonality

-- A one-file public interface: the library's main theorems restated in full
-- and checked by the kernel against the real declarations.
public import LeanPool.BrillNoetherGraphs.TreewidthGonality.Highlights

/-! # Treewidth Gonality -/

@[expose] public section
