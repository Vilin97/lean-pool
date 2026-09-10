/-
Copyright (c) 2026 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/

module

public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Finiteness of quotient modules
-/

public
instance Submodule.Quotient.finite {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [Finite M]
    (S : Submodule R M) : Finite (M ⧸ S) := by
  cases nonempty_fintype M; infer_instance
