/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.RingTheory.Norm.Basic
/-!
# The field norm on multiplicative groups
-/

noncomputable section

namespace ClassFieldTheory

universe u v

/-- The field norm as a homomorphism on multiplicative groups. -/
def fieldNormHom
    (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] :
    Lˣ →* Kˣ :=
  Units.map (Algebra.norm K)

end ClassFieldTheory
