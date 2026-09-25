/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.NormTheorems.IsNormAtInfinitePlace
public import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.AbelianConductorExactness
/-!
# Norms at an unramified infinite place

For a finite abelian extension, the determinant norm from the whole
archimedean tensor algebra is surjective when the base place is
unramified in the extension.
-/

@[expose] public section

open scoped NumberField TensorProduct
open NumberField

noncomputable section

namespace ClassFieldTheory

/-- Every nonzero base-field element is an archimedean tensor norm at an
unramified infinite place of a finite abelian extension. -/
theorem isNormAtInfinitePlace_of_unramified
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    (v : InfinitePlace K) (hv : v.IsUnramifiedIn L) (x : Kˣ) :
    IsNormAtInfinitePlace K L v x := by
  have htop : infiniteTensorNormSubgroup (K := K) (L := L) v = ⊤ :=
    (GlobalClassFieldTheory.GlobalClassFields.infiniteTensorNormSubgroup_eq_top_iff_isUnramifiedIn
      (K := K) (L := L) v).2 hv
  let xv : v.Completionˣ := Units.map (algebraMap K v.Completion) x
  have hnorm : xv ∈ infiniteTensorNormSubgroup (K := K) (L := L) v := by
    rw [htop]
    trivial
  obtain ⟨y, hy⟩ := hnorm
  exact ⟨y, congrArg Units.val hy⟩

end ClassFieldTheory
