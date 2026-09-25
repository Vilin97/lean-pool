/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormTopology.ArchimedeanNorm
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalNorm
/-!
# Norms on norm-one idele groups

The ordinary idele norm restricts to a homomorphism between the actual
norm-one idele subgroups.
-/

@[expose] public section

open scoped NumberField
open NumberField

noncomputable
section

namespace IdeleGroup

universe u v

variable
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]

/-- The ordinary idèle norm carries norm-one idèles to norm-one idèles. -/
theorem norm_mem_normOneSubgroup
    (a : IdeleGroup L)
    (ha : a ∈ normOneSubgroup (K := L)) :
    norm K L a ∈ normOneSubgroup (K := K) := by
  change absoluteNorm (norm K L a) = 1
  change absoluteNorm a = 1 at ha
  rw [absoluteNorm_norm]
  exact ha

/-- The ordinary idele norm restricted to the norm-one idele groups. -/
noncomputable def normOneNorm :
    normOneSubgroup (K := L) →*
      normOneSubgroup (K := K) :=
  ((norm K L).comp
      (normOneSubgroup (K := L)).subtype).codRestrict
    (normOneSubgroup (K := K))
    (fun a =>
      norm_mem_normOneSubgroup K L a.1 a.2)

/-- Coercing the restricted norm-one map recovers the ordinary idèle norm. -/
@[simp]
theorem normOneNorm_apply
    (a : normOneSubgroup (K := L)) :
    (normOneNorm K L a : IdeleGroup K) =
      norm K L a.1 :=
  rfl

/- The canonical map between completions at infinite places is an
isometry.  This is the metric form of the `LiesOver` condition. -/

end IdeleGroup

end
