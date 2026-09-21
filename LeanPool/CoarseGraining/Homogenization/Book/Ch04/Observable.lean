/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceObservable
import LeanPool.CoarseGraining.Homogenization.Book.Ch04.SourceMeasurability

/-!
# Canonical Chapter 4 source observables

Unprefixed locality and observable names in this file are transparent aliases
for the exact coarse-source, integral-local API. The separate
`RestrictionObservable` API remains in the pointwise-restriction engineering
lane.
-/

namespace Homogenization.Book.Ch04

/-- A canonical local random variable on the exact coarse source carrier. -/
abbrev IsLocalRandomVariable {β : Type*} [MeasurableSpace β] {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (X : Source.Coarse.Carrier d → β) : Prop :=
  IsSourceLocalRandomVariable U hU X

namespace IsLocalRandomVariable

export IsSourceLocalRandomVariable
  (mono const comp_measurable comp_translate vec_of_components vec_component
   mat_of_entries mat_entry add neg sub mul inv abs finset_sum measurable
   nullMeasurable aemeasurable aestronglyMeasurable)

end IsLocalRandomVariable

/-- A canonical bundled observable on the exact coarse source carrier. -/
abbrev Observable (d : ℕ) (U : Set (Vec d)) (β : Type*) [MeasurableSpace β] :=
  SourceObservable d U β

namespace Observable

abbrev apply {d : ℕ} {U : Set (Vec d)} {β : Type*} [MeasurableSpace β]
    (X : Observable d U β) (a : Source.Coarse.Carrier d) : β :=
  SourceObservable.toFun X a

export SourceObservable
  (mono const comp translate translate_apply vecOfComponents vecComponent
   matOfEntries matEntry add neg sub mul inv abs finsetSum nullMeasurable
   aemeasurable aestronglyMeasurable)

end Observable

end Homogenization.Book.Ch04
