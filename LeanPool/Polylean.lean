/-
Copyright (c) 2026 Siddhartha Gadgil, Anand Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Anand Rao
-/
module

public import LeanPool.Polylean.UnitConjecture
public import LeanPool.Polylean.Complexes
public import LeanPool.Polylean.Complexes.Constructions.UniversalCover
public import LeanPool.Polylean.Complexes.GraphPaths
public import LeanPool.Polylean.Complexes.Structures.Category
public import LeanPool.Polylean.Complexes.Structures.FreeGroupoid
public import LeanPool.Polylean.Complexes.Structures.Groupoid
public import LeanPool.Polylean.Complexes.Structures.Invertegory
public import LeanPool.Polylean.Complexes.Structures.Quiver
public import LeanPool.Polylean.Complexes.Structures.TwoComplex
public import LeanPool.Polylean.ConjInvLength
public import LeanPool.Polylean.ConjInvLength.Length
public import LeanPool.Polylean.ConjInvLength.LengthBound
public import LeanPool.Polylean.ConjInvLength.LengthNode
public import LeanPool.Polylean.ConjInvLength.MemoLength
public import LeanPool.Polylean.ConjInvLength.ProvedBound
public import LeanPool.Polylean.ConjInvLength.WordTree
public import LeanPool.Polylean.Polymath

/-!
# Polylean Unit Conjecture Counterexample

Source: arxiv:2102.11818, doi:10.4007/annals.2021.194.3.9
Authors: Siddhartha Gadgil, Anand Rao
Status: verified
Main declarations: `LeanPool.Polylean.P.torsionFree`, `LeanPool.Polylean.Gardam.GardamTheorem`
Tags: algebra, group-theory, ring-theory, unit-conjecture
MSC: 16S34, 20F65
-/

@[expose] public section
