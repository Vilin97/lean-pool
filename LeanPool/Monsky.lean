/-
Copyright (c) 2026 Dhyan Aranha and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhyan Aranha and contributors
-/

import LeanPool.Monsky.Appendix
import LeanPool.Monsky.Rainbow_triangles
import LeanPool.Monsky.Triangle_corollary
import LeanPool.Monsky.basic_definitions
import LeanPool.Monsky.main_statement
import LeanPool.Monsky.miscellaneous
import LeanPool.Monsky.monsky_even
import LeanPool.Monsky.segment_counting
import LeanPool.Monsky.segment_triangle
import LeanPool.Monsky.simplex_basic
import LeanPool.Monsky.square

/-!
# Monsky's Theorem

Source: url:https://github.com/dhyan-aranha/Monsky
Authors: Dhyan Aranha and contributors
Thomas Koopman, Dion Leijnse, Thijs Maessen, Maris Ozols, Jonas van der Schaaf,
Lenny Taelman
Status: verified
Main declarations: `LeanPool.Monsky.Monsky`
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
