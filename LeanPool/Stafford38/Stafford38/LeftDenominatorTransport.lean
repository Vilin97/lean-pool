/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.LocalizationCorollaries

namespace Stafford38.LocalizationCorollaries

theorem s38_of_leftUnitClearing
    {R : Type u} {L : Type v} [Ring R] [Ring L]
    {f : R →+* L} (hR : S38 R)
    (hclear : ∀ q : L, q ≠ 0 →
      ∃ a : R, ∃ u : L, IsUnit u ∧ u * q = f a) : S38 L :=
  AlgebraicAnalysis.TwoGeneratorIdentity.of_leftUnitClearing hR hclear


end Stafford38.LocalizationCorollaries
