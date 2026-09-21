/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.NormTheorems.IsNormAtInfinitePlace
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.InfinitePlaceTensorNorm
import LeanPool.ClassFieldTheory.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfinitePlaceArtin
/-!
# The real-to-complex norm obstruction

At a real place which becomes complex, the determinant norm from the whole
archimedean tensor algebra cannot be negative.  The tensor algebra, rather
than a single chosen completion, is the object in the public statement.
-/

open scoped NumberField TensorProduct
open NumberField

noncomputable section

namespace ClassFieldTheory

/-- Negative one is not a norm from the complete archimedean tensor algebra
if a real place becomes complex in a finite Galois extension. -/
theorem not_isNormAtInfinitePlace_neg_one_of_real_complex
    (K L : Type)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : InfinitePlace K) (w : InfinitePlace L)
    (hw : w.comap (algebraMap K L) = v)
    (hv : v.IsReal) (hc : w.IsComplex) :
    ¬ IsNormAtInfinitePlace K L v (-1 : Kˣ) := by
  intro h
  have hnorm : (-1 : v.Completionˣ) ∈
      infiniteTensorNormSubgroup (K := K) (L := L) v := by
    obtain ⟨y, hy⟩ := h
    refine ⟨y, ?_⟩
    apply Units.ext
    change Algebra.norm v.Completion (y : v.Completion ⊗[K] L) =
      (-1 : v.Completion)
    simpa only [Units.coe_neg_one, map_neg, map_one] using hy
  let : w.1.LiesOver v.1 :=
    ⟨congrArg (fun q : InfinitePlace K => q.1) hw⟩
  rw [infiniteTensorNormSubgroup_eq_localNormSubgroup
    (K := K) (L := L) v w hw] at hnorm
  obtain ⟨z, hz⟩ := hnorm
  have hpos := GlobalClassFieldTheory.Reciprocity.infinitePlace_normUnits_real_complex_pos
    (K := K) (K' := L) v w hw hv hc z
  have hneg : (0 : ℝ) < -1 := by
    rw [hz] at hpos
    simpa only [InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
      Units.coe_neg_one, map_neg, map_one] using hpos
  norm_num at hneg

end ClassFieldTheory
