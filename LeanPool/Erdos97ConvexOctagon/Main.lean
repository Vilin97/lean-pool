/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.Erdos97ConvexOctagon.Classification

/-!
# The convex-octagon case of Erdős problem 97

The headline theorem exported by this entry module is
`Erdos97Octagon.erdos97_convex_octagon`: among eight labelled points in convex
position, some point does not have four other points at a common distance.

The proof reduces a hypothetical counterexample to a normalized balanced
incidence table, classifies its first row up to symmetry, and excludes all
seven canonical masks with a kernel-audited exhaustive search over the
remaining legal rows and checked geometric obstruction witnesses.

This is the eight-point convex case only. It does not prove the general open
problem.
-/
