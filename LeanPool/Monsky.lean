/-
Copyright (c) 2026 Dhyan Aranha and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhyan Aranha, contributors
-/
module

public import LeanPool.Monsky.Appendix
public import LeanPool.Monsky.RainbowTriangles
public import LeanPool.Monsky.TriangleCorollary
public import LeanPool.Monsky.BasicDefinitions
public import LeanPool.Monsky.MainStatement
public import LeanPool.Monsky.Miscellaneous
public import LeanPool.Monsky.MonskyEven
public import LeanPool.Monsky.SegmentCounting
public import LeanPool.Monsky.SegmentTriangle
public import LeanPool.Monsky.SimplexBasic
public import LeanPool.Monsky.Square
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Covering.Besicovitch

/-!
# Monsky's Theorem

Source: doi:10.2307/2317329
Authors: Dhyan Aranha, contributors
Status: verified
Main declarations: `LeanPool.Monsky.monsky_theorem`
Tags: geometry, combinatorics, measure-theory
MSC: 52C20, 05B45
-/

@[expose] public section

/-!
## Mathematical overview

This project formalizes Monsky's theorem: a square can be dissected into `n`
triangles of equal area if and only if `n` is nonzero and even. The proof
constructs a non-Archimedean valuation on the real numbers, uses it to define
Monsky's three-coloring of the unit square, proves that an odd equal-area
triangulation would contain a forbidden rainbow triangle, and constructs the
standard even dissections.
-/
