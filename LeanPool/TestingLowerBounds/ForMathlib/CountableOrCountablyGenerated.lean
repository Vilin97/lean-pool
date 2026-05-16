/-
Copyright (c) 2026 Rémy Degenne, Lorenzo Luccioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated

/-!
# Instance form of the product-swap closure for `CountableOrCountablyGenerated`

Mathlib provides `countableOrCountablyGenerated_prod_left_swap` as a lemma. Type-class
resolution does not pick lemmas up automatically, so we re-export the same content as an
instance, which the downstream divergence files rely on.
-/

namespace MeasurableSpace

variable {α β γ : Type*}
variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

instance instCountableOrCountablyGeneratedProdSwap [h : CountableOrCountablyGenerated (α × β) γ] :
    CountableOrCountablyGenerated (β × α) γ :=
  countableOrCountablyGenerated_prod_left_swap

end MeasurableSpace
