/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.AllInternalAgreement

/-!
# Unconditional consequences of Eulerian independence

`EulerianIndependence` is a theorem (`eulerianIndependence`), so
the choice-free value lemma and equivalence invariance of the
mixed partition value hold unconditionally.
-/

namespace RS

/-- The choice-free value lemma, unconditionally: the choice-based
mixed value equals the summand at any concrete transition data. -/
theorem EdgeSubset.mixedValue_eq_summand_open
    {α : Type} {W : Fragment α} (F : EdgeSubset W) {k ℓ : ℕ}
    (h : MixedFunctional k ℓ)
    {κ : F.TransitionSystem} (o : κ.Orientation) :
    F.mixedValue h = F.mixedSummand h o :=
  EdgeSubset.mixedValue_eq_summand eulerianIndependence F h o

end RS
