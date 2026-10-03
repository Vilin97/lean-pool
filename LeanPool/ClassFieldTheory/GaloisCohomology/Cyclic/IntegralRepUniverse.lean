/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


/-!
# Universe boundary for integral representations

Mathlib's `Rep ℤ G` currently requires the coefficient ring and acting group
to inhabit the same universe.  Since `ℤ : Type 0`, every representation-bearing
part of local class field theory uses this single named boundary.  Keeping the
restriction here makes a future universe-polymorphic migration searchable and
prevents individual subtrees from inventing private aliases.
-/

@[expose] public section
/-- The universe-zero group boundary imposed by integral representations. -/
abbrev IntegralRepGroupType := Type 0
