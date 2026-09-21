/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.Basic

/-!
# Regression checks for flag convex closure

The implementation lives in `EGZ.ConvexFlag.ConvexHull`.  These checks keep
the two downstream consequences used by decomposition visible at the
consistency layer.
-/

namespace EGZ

example (F : ConvexFlag) (S : Set F.Point) :
    F.convexHull (F.convexHull S) = F.convexHull S :=
  ConvexFlag.convexHull_idempotent F S

example {p d : ℕ} [NeZero p] {F : ConvexFlag}
    (R : FpRepresentation p d F) (pieces : F.Node → FpCoord p d → ℕ) :
    F.convexHull (FlagDecompositionRaw.omega R pieces) ⊆
      FlagDecompositionRaw.omega R pieces :=
  FlagDecompositionRaw.omega_convex_closed R pieces

end EGZ
