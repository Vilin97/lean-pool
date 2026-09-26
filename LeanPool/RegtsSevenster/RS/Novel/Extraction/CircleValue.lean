/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Extraction.StdRigid

/-!
# The circle value

Closing the standard copairing against the standard form yields
the superdimension `k − 2ℓ`, which is the value Definition 5 gives
a free circle.
-/

@[expose] public section

noncomputable section

namespace RS

open scoped TensorProduct

/-- **The circle value** (accompanying paper §5.2): the standard form
closes
the standard copairing to the superdimension `k − 2ℓ`. -/
theorem stdForm_comp_stdCopair (k ℓ : ℕ) :
    (SuperVect.Hom.comp (stdForm k ℓ) (stdCopair k ℓ)).evenMap 1 =
      (k : ℂ) - 2 * ℓ := by
  change (LinearMap.coprod (TensorProduct.lift (stdFormEvenBilin k))
      (TensorProduct.lift (stdFormOddBilin ℓ)))
    ((LinearMap.toSpanSingleton ℂ _
      (stdCopairEvenElem k, stdCopairOddElem ℓ)) 1) =
    (k : ℂ) - 2 * ℓ
  rw [LinearMap.toSpanSingleton_apply_one, LinearMap.coprod_apply]
  have he : TensorProduct.lift (stdFormEvenBilin k)
      (stdCopairEvenElem k) = (k : ℂ) := by
    unfold stdCopairEvenElem
    rw [map_sum]
    rw [Finset.sum_congr rfl fun i _ => TensorProduct.lift.tmul
      (f' := stdFormEvenBilin k) (stdE k i) (stdE k i)]
    exact sum_stdFormEven_diag k
  have ho : TensorProduct.lift (stdFormOddBilin ℓ)
      (stdCopairOddElem ℓ) = -(2 * ℓ : ℂ) := by
    unfold stdCopairOddElem
    rw [map_sum]
    rw [Finset.sum_congr rfl fun i _ => TensorProduct.lift.tmul
      (f' := stdFormOddBilin ℓ) (stdF ℓ i) (stdG ℓ i)]
    exact sum_stdFormOdd_diag ℓ
  rw [he, ho]
  ring

end RS
