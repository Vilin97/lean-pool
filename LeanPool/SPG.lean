/-
Copyright (c) 2024 Yizhou Tong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yizhou Tong
-/
import LeanPool.SPG.Algebra.Basic
import LeanPool.SPG.Algebra.Actions
import LeanPool.SPG.Algebra.Group
import LeanPool.SPG.Geometry.SpatialOps
import LeanPool.SPG.Geometry.SpinOps
import LeanPool.SPG.Physics.SymmetryBreaking
import LeanPool.SPG.Physics.ResidualGroup
import LeanPool.SPG.Physics.Hamiltonian
import LeanPool.SPG.Data.MagneticGroups
import LeanPool.SPG.Data.ICE_Notation
import LeanPool.SPG.Data.Tetragonal
import LeanPool.SPG.Interface.Notation

/-!
# Spin Point Groups (SPG)

Source: url:https://github.com/tsurumi-yizhou/SPG
Authors: Yizhou Tong
Status: verified
Main declarations: `SPG.Algebra.generate_group`, `SPG.Physics.get_mpg`,
`SPG.Physics.allows_z_polarization`, `SPG.Physics.Hamiltonian.isInvariantHam`,
`SPG.Physics.Hamiltonian.find_invariants`
Tags: spin-point-groups, magnetic-symmetry, altermagnetism, condensed-matter, group-theory
MSC: 20C35
-/
