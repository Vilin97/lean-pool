/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.NormalClosure
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerBaseChange
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquiv
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.NormComparison
/-!
# Idèle-class norms from a finite normal closure

The distinguished copy of a finite extension inside its normal closure
is an intermediate field.  Norm transitivity therefore puts every norm
from the normal closure inside the norm subgroup of that copy.  Transport
across the canonical algebra equivalence identifies the latter subgroup
with the norm subgroup of the original extension.
-/

@[expose] public section

open scoped NumberField
open NumberField

noncomputable
section

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- Every idèle-class norm from the finite normal closure of `L / K` is
already an idèle-class norm from `L / K`.  This supplies a genuine
finite Galois norm neighbourhood inside the norm subgroup of an
arbitrary finite extension. -/
theorem finiteNormalClosure_ideleClassNorm_range_le_source :
    (_root_.ideleClassNorm K (finiteNormalClosure K L)).range ≤
      (_root_.ideleClassNorm K L).range := by
  let N := finiteNormalClosure K L
  let : Algebra (finiteNormalClosureOriginalField K L) N :=
    (finiteNormalClosureOriginalField K L).val.toRingHom.toAlgebra
  let : IsScalarTower K (finiteNormalClosureOriginalField K L) N :=
    by infer_instance
  let : FiniteDimensional (finiteNormalClosureOriginalField K L) N :=
    FiniteDimensional.right K (finiteNormalClosureOriginalField K L) N
  let : IsMulCommutative
      (RelativeIdeleGroup K
        (finiteNormalClosureOriginalField K L)) :=
    ⟨⟨fun a b => mul_comm a b⟩⟩
  let : Group
      (RelativeIdeleGroup.ClassGroup K
        (finiteNormalClosureOriginalField K L)) :=
    QuotientGroup.Quotient.group
      (RelativeIdeleGroup.principalSubgroup K
        (finiteNormalClosureOriginalField K L))
  calc
    (_root_.ideleClassNorm K N).range ≤
        (_root_.ideleClassNorm K (finiteNormalClosureOriginalField K L)).range :=
      ordinaryIdeleClassNorm_range_le_of_tower
        (K := K) (M := finiteNormalClosureOriginalField K L) (L := N)
    _ = (RelativeIdeleGroup.classNorm K (finiteNormalClosureOriginalField K L)).range :=
      ordinaryIdeleClassNorm_range_eq_relative
        (K := K) (L := finiteNormalClosureOriginalField K L)
    _ = (RelativeIdeleGroup.classNorm K L).range :=
      (ideleClassNorm_range_algEquiv
        (K := K) (L := L)
        (M := finiteNormalClosureOriginalField K L)
        (finiteNormalClosureOriginalFieldEquiv K L) :
          (RelativeIdeleGroup.classNorm K
            (finiteNormalClosureOriginalField K L)).range =
            (RelativeIdeleGroup.classNorm K L).range)
    _ = (_root_.ideleClassNorm K L).range :=
      (ordinaryIdeleClassNorm_range_eq_relative
        (K := K) (L := L)).symm

end
