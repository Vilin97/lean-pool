/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormTopology.ArchimedeanNorm
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalNorm
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdealClass
/-!
# The ordinary norm on idele classes

The ordinary idele-class norm preserves the absolute norm and restricts to
the norm-one idele-class subgroups.
-/

open scoped NumberField
open NumberField

noncomputable section

namespace IdeleClassGroup

universe u v

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]

/-- The ordinary idèle-class norm preserves the absolute idèle norm. -/
theorem absoluteNorm_ideleClassNorm
    (c : IdeleClassGroup L) :
    absoluteNorm (_root_.ideleClassNorm K L c) =
      absoluteNorm c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  change
    absoluteNorm
        (_root_.ideleClassNorm K L
          (QuotientGroup.mk'
            (IdeleGroup.principalSubgroup L) a)) =
      absoluteNorm
        (QuotientGroup.mk'
          (IdeleGroup.principalSubgroup L) a)
  rw [_root_.ideleClassNorm_mk,
    absoluteNorm_mk, absoluteNorm_mk,
    IdeleGroup.absoluteNorm_norm]

/-- The ordinary idele-class norm carries norm-one idele classes to
norm-one idele classes. -/
theorem ideleClassNorm_mem_normOneSubgroup
    (c : IdeleClassGroup L)
    (hc : c ∈ normOneSubgroup (K := L)) :
    _root_.ideleClassNorm K L c ∈
      normOneSubgroup (K := K) := by
  change
    absoluteNorm (_root_.ideleClassNorm K L c) = 1
  change absoluteNorm c = 1 at hc
  rw [absoluteNorm_ideleClassNorm]
  exact hc

/-- The ordinary idele-class norm restricted to the norm-one idele-class
groups. -/
noncomputable def normOneNorm :
    normOneSubgroup (K := L) →*
      normOneSubgroup (K := K) :=
  ((_root_.ideleClassNorm K L).comp
      (normOneSubgroup (K := L)).subtype).codRestrict
    (normOneSubgroup (K := K))
    (fun c =>
      ideleClassNorm_mem_normOneSubgroup
        K L c.1 c.2)

/-- Coercing the restricted norm-one map recovers the ordinary idèle-class norm. -/
@[simp]
theorem normOneNorm_apply
    (c : normOneSubgroup (K := L)) :
    (normOneNorm K L c : IdeleClassGroup K) =
      _root_.ideleClassNorm K L c.1 :=
  rfl


end IdeleClassGroup

end
