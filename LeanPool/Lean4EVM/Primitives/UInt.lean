/-
Copyright (c) 2026 mrLSD. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mrLSD
-/
import LeanPool.Lean4EVM.Primitives.UInt.U256

/-!
# Fixed-width unsigned integers

Public entry point for the fixed-width integer family. `Core` contains the shared representation,
executable arithmetic, and generic laws. `U64`, `U128`, and `U256` keep width-specific operations,
conversions, and theorems beside their owning type. The import order is intentionally widening:
`Core → U64 → U128 → U256`, which keeps cross-width conversions acyclic.
-/
