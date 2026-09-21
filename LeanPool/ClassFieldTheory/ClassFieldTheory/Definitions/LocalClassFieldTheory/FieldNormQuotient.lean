/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.LocalClassFieldTheory.FieldNormSubgroup
import Mathlib.GroupTheory.QuotientGroup.Basic
/-!
# The field-norm quotient
-/

noncomputable section

namespace ClassFieldTheory

universe u v

/-- The norm quotient `Kˣ / N_{L/K}(Lˣ)`. -/
abbrev FieldNormQuotient
    (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] :=
  Kˣ ⧸ fieldNormSubgroup K L

end ClassFieldTheory
