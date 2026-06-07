/-
Copyright (c) 2024 Yizhou Tong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizhou Tong
-/
import LeanPool.SPG.Algebra.Basic
import LeanPool.SPG.Algebra.Group
import LeanPool.SPG.Geometry.SpatialOps
import LeanPool.SPG.Geometry.SpinOps
import LeanPool.SPG.Interface.Notation

namespace SPG.Data.MagneticGroups

open SPG
open SPG.Geometry.SpatialOps
open SPG.Geometry.SpinOps
open SPG.Interface
open SPG.Algebra

-- Define common matrices
def mat_2_xy : Matrix (Fin 3) (Fin 3) ℚ := ![![0, 1, 0], ![1, 0, 0], ![0, 0, -1]]

-- 1. Ferromagnet (FM)
-- A typical ferromagnet breaks Time Reversal (T) symmetry.
-- It may preserve spatial symmetries compatible with the magnetization direction.
-- Example: FM with magnetization along z-axis in a D4h crystal.
-- Preserved symmetries: C4z, C2x (if M is axial?), Inversion?
-- Actually, M is an axial vector.
-- C4z (M along z) -> M along z. OK.
-- C2x (M along z) -> M along -z (rotation of axial vector). Broken!
-- Inversion (M axial) -> M (axial vectors even under I). OK.
-- Time Reversal T -> -M. Broken!
-- So the group is reduced.
-- Generators: C4z, I (No T, No T*Operation)
def gen_FM_C4z : SPGElement := Op[mat_4_z, ^1]
def gen_FM_Inv : SPGElement := Op[mat_inv, ^1]

def Ferromagnet_Group_D4h_z : List SPGElement := generate_group [gen_FM_C4z, gen_FM_Inv]


-- 2. Antiferromagnet (AFM)
-- A typical AFM preserves T combined with a spatial operation (or translation).
-- Since we are doing Point Groups, we consider T combined with a spatial symmetry that swaps sublattices.
-- Example: AFM in D4h.
-- Moments: Up at (0,0), Down at (0.5, 0.5) [Simplified view for point group]
-- Or simply: T is broken, but T * C2x is preserved?
-- Or T * Inversion (PT symmetry) is preserved?
-- Let's define a PT-symmetric AFM (common in many materials).
-- Generators: C4z, P*T (Inversion * TimeReversal), C2x (swaps sublattices? or broken?)
-- Let's take a simple PT-symmetric AFM.
-- Symmetries: C4z (spatial only), I*T (spacetime), C2x (spatial? if it preserves sublattice)
-- Let's assume C2x is broken for simplicity, or C2x*T?
-- Let's define:
-- 1. C4z (Space only)
-- 2. I * T (Combined)
-- 3. C2x (Space only) - wait, C2x usually flips z-axis (if it's C2y? no C2x rotates around x).
-- If C2x rotates around x, z -> -z. Spin z -> -z (axial).
-- If we have AFM, sublattices A(up), B(down).
-- C2x swaps z and -z. So it maps A to itself? No, spatial position changes.
-- Point group approximation ignores translation.
-- Let's focus on the magnetic point group operations.
-- PT-symmetric AFM: { E, C4z, ..., PT, PT*C4z, ... }
def gen_AFM_C4z : SPGElement := Op[mat_4_z, ^1]
def gen_AFM_PT  : SPGElement := Op[mat_inv, ^-1] -- P * T
def gen_AFM_C2x : SPGElement := Op[mat_2_x, ^1] -- Rotation around x

def Antiferromagnet_Group_PT : List SPGElement := generate_group [gen_AFM_C4z, gen_AFM_PT, gen_AFM_C2x]


-- 3. Altermagnet (AM) - D4h (from Demo)
-- Generators: C4z * T, C2xy, I
def gen_AM_C4z_TR : SPGElement := Op[mat_4_z, ^-1]
def gen_AM_C2xy   : SPGElement := Op[mat_2_xy, ^1]
def gen_AM_Inv    : SPGElement := Op[mat_inv, ^1]

def Altermagnet_Group_D4h : List SPGElement := generate_group [gen_AM_C4z_TR, gen_AM_C2xy, gen_AM_Inv]

end SPG.Data.MagneticGroups
