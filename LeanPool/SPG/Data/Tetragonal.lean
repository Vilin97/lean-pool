/-
Copyright (c) 2024 Yizhou Tong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizhou Tong
-/
import LeanPool.SPG.Data.ICENotation
import LeanPool.SPG.Algebra.Group
import LeanPool.SPG.Geometry.SpatialOps

/-!
# Tetragonal example groups

This module constructs the `D2d` point group and its Laue extension for the
chalcopyrite structure from their standard generators.
-/

namespace SPG.Data.Tetragonal

open SPG.Geometry.SpatialOps
open SPG.Algebra

-- Generators for CuFeS2 (Chalcopyrite structure, I-42d, #122)
-- Using 4bar_z, 2_x, and m_xy (standard generators for D2d point group)
-- Assuming non-magnetic for now (time_reversal = false)

/-- Gen1. -/
def gen1 : SPGElement := mkIceElement mat4barZ false
/-- Gen2. -/
def gen2 : SPGElement := mkIceElement mat2X false
/-- Gen3. -/
def gen3 : SPGElement := mkIceElement matMXy false

/-- D2d Gens. -/
def D2dGens : List SPGElement := [gen1, gen2, gen3]
/-- D2d. -/
def D2d : List SPGElement := generateGroup D2dGens

/-- Laue D2d Gens. -/
def LaueD2dGens : List SPGElement := D2dGens ++ [mkIceElement matInv false]
/-- Laue D2d. -/
def LaueD2d : List SPGElement := generateGroup LaueD2dGens

end SPG.Data.Tetragonal
