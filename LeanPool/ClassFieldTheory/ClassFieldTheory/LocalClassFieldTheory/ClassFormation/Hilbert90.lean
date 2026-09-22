/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.SetTheory.Cardinal.Finite
import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.GaloisCohomology
/-!
Provides the public declarations in the
`LocalClassFieldTheory.ClassFormation.Hilbert90` Lean module.
-/

namespace LocalClassFieldTheory

open CyclicCohomology

noncomputable section

/-- The `i = -1` half of the local class-field-axiom theorem on the actual field-unit
representation.  This is Hilbert 90 transported through the cyclic
`H¹ ≃ H⁻¹` comparison. -/
theorem unitsTateHminusOne_card_eq_one
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (g : Gal(L/K)) (hg : ∀ σ : Gal(L/K), σ ∈ Subgroup.zpowers g) :
    Nat.card (tateCohomology (Rep.ofAlgebraAutOnUnits K L) (-1)) = 1 := by
  calc
    Nat.card (tateCohomology (Rep.ofAlgebraAutOnUnits K L) (-1)) =
        Nat.card (groupCohomology.H1 (Rep.ofAlgebraAutOnUnits K L)) :=
      Nat.card_congr
        (unitsH1IsoTateHminusOne K L g hg).symm.toLinearEquiv.toEquiv
    _ = 1 := Nat.card_unique

end
end LocalClassFieldTheory
