/-
Copyright (c) 2026 Dhyan Aranha and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhyan Aranha and contributors
-/

import LeanPool.Monsky.Appendix
import LeanPool.Monsky.RainbowTriangles
import LeanPool.Monsky.TriangleCorollary
import LeanPool.Monsky.BasicDefinitions
import LeanPool.Monsky.MainStatement
import LeanPool.Monsky.Miscellaneous
import LeanPool.Monsky.MonskyEven
import LeanPool.Monsky.SegmentCounting
import LeanPool.Monsky.SegmentTriangle
import LeanPool.Monsky.SimplexBasic
import LeanPool.Monsky.Square

/-!
# Monsky's Theorem

Source: doi:10.2307/2316270
Authors: Dhyan Aranha and contributors
Status: verified
Main declarations: `LeanPool.Monsky.monsky_theorem`
Tags: geometry, combinatorics, measure-theory
MSC: 52C20, 05B45
-/

/-!
## Mathematical overview

This project formalizes Monsky's theorem: a square can be dissected into `n`
triangles of equal area if and only if `n` is nonzero and even. The proof
constructs a non-Archimedean valuation on the real numbers, uses it to define
Monsky's three-coloring of the unit square, proves that an odd equal-area
triangulation would contain a forbidden rainbow triangle, and constructs the
standard even dissections.
-/
