/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

import LeanPool.AsymptoticTrianglePacking.Internal.RegularMost

/-!
# Finite near-regular hypergraph rounding: basic statement

The public statement records the finite near-regular hypergraph rounding interface used by
the nibble method. The underlying finite definitions are kept in the internal library.
-/

namespace LeanPool.AsymptoticTrianglePacking

/-- The finite ceiling-carrying nibble interface for near-regular hypergraphs. -/
abbrev NearRegularNibbleTheorem : Prop :=
  Internal.NibbleTheoremMostCeil

end LeanPool.AsymptoticTrianglePacking
