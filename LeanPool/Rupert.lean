/-
Copyright (c) 2026 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/
module

public import LeanPool.Rupert.Affine
public import LeanPool.Rupert.Attr
public import LeanPool.Rupert.Basic
public import LeanPool.Rupert.Convex
public import LeanPool.Rupert.Cube
public import LeanPool.Rupert.FinCases
public import LeanPool.Rupert.Icosahedron
public import LeanPool.Rupert.MatrixSimps
public import LeanPool.Rupert.Quaternion
public import LeanPool.Rupert.Equivalences.RupertEquivRupertPrime
public import LeanPool.Rupert.Equivalences.RupertEquivRupertSet
public import LeanPool.Rupert.Equivalences.AffineRupertEquivRupertSet
public import LeanPool.Rupert.Set
public import LeanPool.Rupert.SnubCube
public import LeanPool.Rupert.Square
public import LeanPool.Rupert.Tetrahedron
public import LeanPool.Rupert.TriakisTetrahedron

/-!
# The Rupert Problem for convex polyhedra

Source: url:https://github.com/dwrensha/Rupert.lean
Authors: David Renshaw
Status: verified
Main declarations: `Cube.rupert`, `Tetrahedron.rupert`, `TriakisTetrahedron.rupert`
Tags: convex-geometry, polyhedra, rupert-problem
MSC: 52B10, 52A15
-/

@[expose] public section
