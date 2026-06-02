/-
Copyright (c) 2026 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/

import LeanPool.Rupert.Affine
import LeanPool.Rupert.Attr
import LeanPool.Rupert.Basic
import LeanPool.Rupert.Convex
import LeanPool.Rupert.Cube
import LeanPool.Rupert.FinCases
import LeanPool.Rupert.Icosahedron
import LeanPool.Rupert.MatrixSimps
import LeanPool.Rupert.Quaternion
import LeanPool.Rupert.Equivalences.RupertEquivRupertPrime
import LeanPool.Rupert.Equivalences.RupertEquivRupertSet
import LeanPool.Rupert.Equivalences.AffineRupertEquivRupertSet
import LeanPool.Rupert.Set
import LeanPool.Rupert.SnubCube
import LeanPool.Rupert.Square
import LeanPool.Rupert.Tetrahedron
import LeanPool.Rupert.TriakisTetrahedron

/-!
# The Rupert Problem for convex polyhedra

Source: url:https://github.com/dwrensha/Rupert.lean
Authors: David Renshaw
Status: verified
Main declarations: `Cube.rupert`, `Tetrahedron.rupert`, `TriakisTetrahedron.rupert`
Tags: convex-geometry, polyhedra, rupert-problem
MSC: 52B10, 52A15
-/
