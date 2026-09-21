/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.FreeModShuffle

/-!
# Components of the free module on a biproduct

The free module on a binary biproduct is the biproduct of the two
free modules; that isomorphism is `freeModBiprodIso`, assembled
from the carrier-level distributor `tensorBiprodIso`.
Recorded here are its four components: the distributor followed by
a projection of the module biproduct is the free module on the
corresponding projection of the underlying biproduct, and an
injection of the module biproduct followed by the inverse
distributor is the free module on the corresponding injection.
Since each side is a module map, the identifications are those of
the carriers, and the carrier-level identifications are the
defining equations of `biprod.lift` and `biprod.desc`.

The vanishing of the free module on a zero object completes the
bookkeeping of the empty mixed sum.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- **The free module on a zero object is zero**: the vanishing of
a tensor product, retyped at the carrier of the free module. -/
theorem freeModZeroIso [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] (R : D) [MonObj R]
    {V : D} (h : IsZero V) :
    IsZero (freeMod R V).X :=
  isZero_whiskerLeft R h

end RS
