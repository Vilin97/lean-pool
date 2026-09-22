/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# Multiplicity after extending an ideal

The `emultiplicity` theorem in mathlib is the generic local factorization
statement.  This file records the `Nat`-valued wrapper used by the
exact-constant genus transport, first for a specified pair of height-one
places and then with the lower place chosen by `under`.
-/

open IsDedekindDomain

namespace BGS.HasseWeil

noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S]
  [IsDedekindDomain R] [IsDedekindDomain S]
  [Algebra R S] [Module.IsTorsionFree R S]

/-- Extending a nonzero ideal multiplies its multiplicity at a height-one
prime by the ramification index of that prime. -/
theorem multiplicity_map_eq_ramificationIdx_mul
    (v : HeightOneSpectrum R) (w : HeightOneSpectrum S)
    [w.asIdeal.LiesOver v.asIdeal]
    (I : Ideal R) (hI : I ≠ ⊥) :
    multiplicity w.asIdeal (I.map (algebraMap R S)) =
      w.asIdeal.ramificationIdx R * multiplicity v.asIdeal I := by
  refine multiplicity_eq_of_emultiplicity_eq_some ?_
  rw [Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul
      hI v.irreducible w.irreducible w.ne_bot,
    Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot,
    Nat.cast_mul,
    (FiniteMultiplicity.of_prime_left v.prime hI).emultiplicity_eq_multiplicity]

variable [Algebra.IsIntegral R S]

/-- The same formula with the lower place chosen canonically by contraction. -/
theorem multiplicity_map_eq_ramificationIdx_mul_under
    (w : HeightOneSpectrum S) (I : Ideal R) (hI : I ≠ ⊥) :
    multiplicity w.asIdeal (I.map (algebraMap R S)) =
      w.asIdeal.ramificationIdx R *
        multiplicity (w.under R).asIdeal I := by
  let : w.asIdeal.LiesOver (w.under R).asIdeal := ⟨rfl⟩
  simpa using
    multiplicity_map_eq_ramificationIdx_mul
      (R := R) (S := S) (w.under R) w I hI

end

end BGS.HasseWeil
