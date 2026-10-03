/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.UniformSpace.AbsoluteValue
/-!
# Extensions of absolute values

A reusable predicate for exact extension along an algebra map.
-/

@[expose] public section
namespace AbsoluteValue
/-- The target absolute value agrees with the base absolute value along the algebra map. -/
def Extends {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ) : Prop :=
  ∀ x : K, w (algebraMap K L x) = v x

end AbsoluteValue
