/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.NormTheorems.IsNormAtInfinitePlace
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormApproximation.InfinitePlaces
/-!
# Norms at a complex infinite place

The positivity condition is vacuous at a complex place. Consequently every
nonzero base-field element is a determinant norm from the whole archimedean
tensor algebra.
-/

@[expose] public section

open scoped NumberField TensorProduct
open NumberField

noncomputable section

namespace ClassFieldTheory

universe u v

/-- The determinant norm from `K_v ⊗_K L` is surjective on the image of
`Kˣ` when `v` is complex. -/
theorem isNormAtInfinitePlace_of_complex
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : InfinitePlace K) (hv : v.IsComplex) (x : Kˣ) :
    IsNormAtInfinitePlace K L v x := by
  let xv : v.Completionˣ := Units.map (algebraMap K v.Completion) x
  have hpos : xv ∈ RayClass.infinitePositiveSubgroup v := by
    intro hr
    exact ((InfinitePlace.not_isReal_iff_isComplex).2 hv hr).elim
  have hnorm : xv ∈ infiniteTensorNormSubgroup (K := K) (L := L) v :=
    infinitePositiveSubgroup_le_infiniteTensorNormSubgroup
      (K := K) (L := L) v hpos
  obtain ⟨y, hy⟩ := hnorm
  exact ⟨y, congrArg Units.val hy⟩

end ClassFieldTheory
