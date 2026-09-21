/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.NormTheorems.IsNormAtInfinitePlace
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.InfinitePlaceTensorNorm
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfinitePlaceArtin
/-!
# The norm criterion at a real place that becomes complex

At such a place the determinant norms from the full archimedean tensor
algebra are exactly the positive real elements.  In particular this does
not incorrectly replace the tensor norm by a separate condition at every
factor of the tensor product.
-/

open scoped NumberField TensorProduct
open NumberField

noncomputable section

namespace ClassFieldTheory

/-- At a real place that becomes complex in a finite Galois extension,
being a norm from the archimedean tensor algebra is equivalent to positivity. -/
theorem isNormAtInfinitePlace_iff_positive_of_real_complex
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : InfinitePlace K) (w : InfinitePlace L)
    (hw : w.comap (algebraMap K L) = v)
    (hv : v.IsReal) (hc : w.IsComplex)
    (x : Kˣ) :
    IsNormAtInfinitePlace K L v x ↔
      0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
        (algebraMap K v.Completion (x : K)) := by
  let xv : v.Completionˣ := Units.map (algebraMap K v.Completion) x
  let : w.1.LiesOver v.1 :=
    ⟨congrArg (fun q : InfinitePlace K => q.1) hw⟩
  constructor
  · rintro ⟨y, hy⟩
    have hnorm : xv ∈ infiniteTensorNormSubgroup (K := K) (L := L) v := by
      refine ⟨y, ?_⟩
      apply Units.ext
      exact hy
    rw [infiniteTensorNormSubgroup_eq_localNormSubgroup
      (K := K) (L := L) v w hw] at hnorm
    obtain ⟨z, hz⟩ := hnorm
    have hpos :=
      GlobalClassFieldTheory.Reciprocity.infinitePlace_normUnits_real_complex_pos
        (K := K) (K' := L) v w hw hv hc z
    rw [hz, InfinitePlace.Completion.ringEquivRealOfIsReal_apply] at hpos
    exact hpos
  · intro hpos
    have hxpos : xv ∈ RayClass.infinitePositiveSubgroup v := by
      intro hv'
      have heq : hv' = hv := Subsingleton.elim _ _
      subst hv'
      change 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
        (algebraMap K v.Completion (x : K))
      exact hpos
    have hnorm : xv ∈ infiniteTensorNormSubgroup (K := K) (L := L) v :=
      infinitePositiveSubgroup_le_infiniteTensorNormSubgroup
        (K := K) (L := L) v hxpos
    obtain ⟨y, hy⟩ := hnorm
    refine ⟨y, ?_⟩
    exact congrArg Units.val hy

end ClassFieldTheory
