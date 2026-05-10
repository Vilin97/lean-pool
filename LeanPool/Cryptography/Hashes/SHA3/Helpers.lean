/-
Copyright (c) 2026 Gerald Doussot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gerald Doussot, François G. Dorais
-/

/-!
# Helper lemma: `ByteArray.set` preserves size

Reproduced from Batteries (`Batteries.Data.ByteArray.size_set`,
[source](https://github.com/leanprover-community/batteries/blob/ad3ba5ff13913874b80146b54d0a4e5b9b739451/Batteries/Data/ByteArray.lean#L51))
to avoid an extra dependency. The original is Apache-2.0 by François G.
Dorais and is included with attribution above.
-/

/-- `(a.set i v h).size = a.size`: writing through `ByteArray.set` does
not change the array length. -/
@[simp] theorem size_set (a : ByteArray) (i : Nat) (v : UInt8) (h : i < a.size) :
    (a.set i v h).size = a.size :=
  Array.size_set h
