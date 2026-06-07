/-
Copyright (c) 2024 Yizhou Tong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizhou Tong
-/
import LeanPool.SPG.Data.ICE_Notation
import LeanPool.SPG.Algebra.Group
import LeanPool.SPG.Geometry.SpatialOps

namespace SPG.Data.Tetragonal

open SPG.Geometry.SpatialOps
open SPG.Algebra

-- Generators for CuFeS2 (Chalcopyrite structure, I-42d, #122)
-- Using 4bar_z, 2_x, and m_xy (standard generators for D2d point group)
-- Assuming non-magnetic for now (time_reversal = false)

def gen1 : SPGElement := mk_ice_element mat_4bar_z false
def gen2 : SPGElement := mk_ice_element mat_2_x false
def gen3 : SPGElement := mk_ice_element mat_m_xy false

def D2d_gens : List SPGElement := [gen1, gen2, gen3]
def D2d : List SPGElement := generate_group D2d_gens

def Laue_D2d_gens : List SPGElement := D2d_gens ++ [mk_ice_element mat_inv false]
def Laue_D2d : List SPGElement := generate_group Laue_D2d_gens

end SPG.Data.Tetragonal
