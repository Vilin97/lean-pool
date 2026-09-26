/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNorm
/-!
# Ideles in the ordinary idele-class norm quotient

This file supplies the useful composite from ideles to the quotient
of `C_K` by the range of the ordinary norm `C_L → C_K`, used by the
global norm-residue-symbol constructions.
-/

@[expose] public section

open scoped NumberField

noncomputable
section

namespace GlobalClassFieldTheory
namespace Reciprocity

variable
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

local instance normQuotientIdeleClassGroupIsMulCommutative :
    IsMulCommutative (IdeleClassGroup K) :=
  ⟨⟨fun a b => mul_comm a b⟩⟩

/-- The composite from ideles to the canonical class norm quotient
`C_K / N_{L/K} C_L`. -/
def globalNormClassFromIdele :
    IdeleGroup K →*
      IdeleClassGroup K ⧸
        (_root_.ideleClassNorm K L).range :=
  (QuotientGroup.mk'
      (_root_.ideleClassNorm K L).range).comp
    (QuotientGroup.mk'
      (IdeleGroup.principalSubgroup K))

omit [FiniteDimensional K L] in
/-- The map from ideles to the class norm quotient factors through
`C_K`, so it kills every principal idele. -/
@[simp]
theorem globalNormClassFromIdele_principalIdele
    (x : Kˣ) :
    globalNormClassFromIdele K L
        (IdeleGroup.principalIdele K x) = 1 := by
  rw [globalNormClassFromIdele, MonoidHom.comp_apply]
  have hclass :
      QuotientGroup.mk'
          (IdeleGroup.principalSubgroup K)
          (IdeleGroup.principalIdele K x) = 1 :=
    (QuotientGroup.eq_one_iff
      (IdeleGroup.principalIdele K x)).2 ⟨x, rfl⟩
  rw [hclass, map_one]

end Reciprocity
end GlobalClassFieldTheory
