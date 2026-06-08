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

/-!
# Example magnetic point groups

This module builds concrete spin point groups for representative ferromagnetic,
antiferromagnetic, and altermagnetic configurations in a `D4h` setting from
their generating operations.
-/

namespace SPG.Data.MagneticGroups

open SPG
open SPG.Geometry.SpatialOps
open SPG.Geometry.SpinOps
open SPG.Interface
open SPG.Algebra

-- Define common matrices
/-- Mat2 Xy. -/
def mat2Xy : Matrix (Fin 3) (Fin 3) ℚ := ![![0, 1, 0], ![1, 0, 0], ![0, 0, -1]]

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
/-- Gen FMC4z. -/
def genFMC4z : SPGElement := Op[mat4Z, ^1]
/-- Gen FM Inv. -/
def genFMInv : SPGElement := Op[matInv, ^1]

/-- Ferromagnet Group D4h Z. -/
def FerromagnetGroupD4hZ : List SPGElement :=
  generateGroup [genFMC4z, genFMInv]


-- 2. Antiferromagnet (AFM)
-- A typical AFM preserves T combined with a spatial operation (or translation).
-- Since we are doing Point Groups, we consider T combined with a spatial
-- symmetry that swaps sublattices.
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
-- 3. C2x (Space only) - wait, C2x usually flips z-axis
--    (if it's C2y? no C2x rotates around x).
-- If C2x rotates around x, z -> -z. Spin z -> -z (axial).
-- If we have AFM, sublattices A(up), B(down).
-- C2x swaps z and -z. So it maps A to itself? No, spatial position changes.
-- Point group approximation ignores translation.
-- Let's focus on the magnetic point group operations.
-- PT-symmetric AFM: { E, C4z, ..., PT, PT*C4z, ... }
/-- Gen AFMC4z. -/
def genAFMC4z : SPGElement := Op[mat4Z, ^1]
/-- Gen AFMPT. -/
def genAFMPT : SPGElement := Op[matInv, ^-1] -- P * T
/-- Gen AFMC2x. -/
def genAFMC2x : SPGElement := Op[mat2X, ^1] -- Rotation around x

/-- Antiferromagnet Group PT. -/
def AntiferromagnetGroupPT : List SPGElement :=
  generateGroup [genAFMC4z, genAFMPT, genAFMC2x]


-- 3. Altermagnet (AM) - D4h (from Demo)
-- Generators: C4z * T, C2xy, I
/-- Gen AMC4z TR. -/
def genAMC4zTR : SPGElement := Op[mat4Z, ^-1]
/-- Gen AMC2xy. -/
def genAMC2xy : SPGElement := Op[mat2Xy, ^1]
/-- Gen AM Inv. -/
def genAMInv : SPGElement := Op[matInv, ^1]

/-- Altermagnet Group D4h. -/
def AltermagnetGroupD4h : List SPGElement :=
  generateGroup [genAMC4zTR, genAMC2xy, genAMInv]

end SPG.Data.MagneticGroups
