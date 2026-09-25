/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.Rappel210

/-!
# The free modules of a finite biproduct as retracts

A finite biproduct in the ambient category presents each of its
summands as a retract, and taking free modules preserves both the
retraction identities and the totality of the projectors.  This is
how a mixed sum of copies of the unit and the odd line is fed to an
additivity argument without ever forming a biproduct in the
category of module objects.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

variable {D : Type u}

/-- **The free-module retracts of a finite biproduct are total.** -/
theorem freeModMap_biproduct_total
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] (A : D) [MonObj A] [HasFiniteBiproducts D]
    {ι : Type} [Fintype ι]
    (f : ι → D) :
    ∑ i : ι, (freeModMap A (biproduct.π f i)).hom ≫
        (freeModMap A (biproduct.ι f i)).hom =
      𝟙 (freeMod A (⨁ f)).X := by
  have h : ∀ i : ι, (freeModMap A (biproduct.π f i)).hom ≫
      (freeModMap A (biproduct.ι f i)).hom =
        A ◁ (biproduct.π f i ≫ biproduct.ι f i) := fun i =>
    (MonoidalCategory.whiskerLeft_comp A _ _).symm
  refine Eq.trans (Finset.sum_congr rfl fun i _ => h i) ?_
  refine Eq.trans (whiskerLeft_sum A Finset.univ
    (fun i => biproduct.π f i ≫ biproduct.ι f i)).symm ?_
  rw [biproduct.total]
  exact MonoidalCategory.whiskerLeft_id A (⨁ f)

end RS
