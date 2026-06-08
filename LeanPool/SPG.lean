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
import LeanPool.SPG.Data.ICENotation
import LeanPool.SPG.Data.Tetragonal
import LeanPool.SPG.Interface.Notation

/-!
# Spin Point Groups

Source: url:https://github.com/tsurumi-yizhou/SPG
Authors: Yizhou Tong
Status: verified
Main declarations: `SPG.Algebra.generateGroup`, `SPG.Physics.getMpg`
Tags: spin-point-groups, magnetic-symmetry, altermagnetism, condensed-matter, group-theory
MSC: 20C35
-/
