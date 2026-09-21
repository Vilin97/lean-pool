/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Topology.UniformSpace.AbsoluteValue
/-!
# Absolute values above a fixed absolute value

This index type uses only Mathlib's absolute values and algebra map.  Its
elements are precisely the absolute values on `L` extending `v` on `K`.
-/

namespace ClassFieldTheory

universe u v

/-- An absolute value on `L` whose restriction along `K → L` is `v`. -/
abbrev ExtendingAbsoluteValue
    {K : Type u} [Field K] (v : AbsoluteValue K ℝ)
    (L : Type v) [Field L] [Algebra K L] :=
  { w : AbsoluteValue L ℝ // ∀ a : K, w (algebraMap K L a) = v a }

end ClassFieldTheory
