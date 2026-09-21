/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.KummerAlgebra
import Mathlib.RingTheory.AdjoinRoot
/-!
# Finite freeness of a Kummer algebra

The polynomial `X ^ n - a` is monic for positive `n`. Its quotient algebra is
finite free even when that polynomial is reducible, so no field assumption is
placed on the Kummer algebra.
-/

namespace ClassFieldTheory

universe u

/-- A Kummer algebra is finite free over its base field, including reducible
and degree-one cases. -/
theorem kummerAlgebra_finiteFree
    (K : Type u) [Field K] (n : ℕ+) (a : Kˣ) :
    Module.Finite K (KummerAlgebra K n a) ∧
      Module.Free K (KummerAlgebra K n a) := by
  let p : Polynomial K :=
    Polynomial.X ^ (n : ℕ) - Polynomial.C (a : K)
  have hp : p.Monic :=
    Polynomial.monic_X_pow_sub_C (a : K) (Nat.ne_of_gt n.pos)
  change Module.Finite K (AdjoinRoot p) ∧ Module.Free K (AdjoinRoot p)
  exact ⟨hp.finite_adjoinRoot, hp.free_adjoinRoot⟩

end ClassFieldTheory
