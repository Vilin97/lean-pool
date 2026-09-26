/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import LeanPool.AsymptoticTrianglePacking.Basic
import LeanPool.AsymptoticTrianglePacking.Internal.NearRegularNibble

/-!
# Nibble rounding infrastructure

This module makes the ceiling-carrying finite nibble interface available to the final assembly.
The full development remains internal so that the public API is limited to stable theorem-level
statements.
-/

public section

namespace LeanPool.AsymptoticTrianglePacking

/-- The finite nibble-rounding theorem in the public interface. -/
theorem nearRegularNibbleTheorem : NearRegularNibbleTheorem :=
  Internal.nibbleTheoremMostCeil_holds

end LeanPool.AsymptoticTrianglePacking
