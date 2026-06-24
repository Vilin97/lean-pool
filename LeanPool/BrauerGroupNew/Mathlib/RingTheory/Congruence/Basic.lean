/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/

import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.RingQuot
import Mathlib.RingTheory.Congruence.Basic

/-!
# LeanPool.BrauerGroupNew.Mathlib.RingTheory.Congruence.Basic

Imported Lean Pool material for `LeanPool.BrauerGroupNew.Mathlib.RingTheory.Congruence.Basic`.
-/

open Function

/-!
# Ring congruence quotient compatibility

This file restores the upstream quotient-map names used by the Brauer group port.
-/

namespace RingCon

variable {α R : Type*}

instance instModuleQuotientOfIsScalarTowerLeanPool [Semiring α] [NonAssocSemiring R]
    [Module α R] [IsScalarTower α R R]
    (c : RingCon R) : Module α c.Quotient where
  zero_smul x := by
    induction x using Quotient.ind
    change ⟦_⟧ = ⟦_⟧
    simp
  add_smul r s x := by
    induction x using Quotient.ind
    change ⟦_⟧ = ⟦_⟧
    simp [add_smul]

variable (α) in
/-- The quotient map as a linear map. -/
def mkL [Semiring α] [NonAssocSemiring R] [Module α R] [IsScalarTower α R R]
    (c : RingCon R) : R →ₗ[α] c.Quotient where
  __ := c.mk'
  map_smul' _ _ := rfl

lemma algebraMap_def [CommSemiring α] [Semiring R] [Algebra α R] (c : RingCon R) :
    algebraMap α c.Quotient = c.mk'.comp (algebraMap α R) := rfl

variable (α) in
/-- The quotient map as an algebra homomorphism. -/
def mkA [CommSemiring α] [Semiring R] [Algebra α R] (c : RingCon R) : R →ₐ[α] c.Quotient :=
  c.mkₐ (α := α)

end RingCon
