/-
Copyright (c) 2026 Wouter Cames van Batenburg, Samuel Korsky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Cames van Batenburg, Samuel Korsky
-/

import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Order.Filter.AtTopBot.Tendsto

/-!
# Finite fields of prime-power order

This file separates the finite-geometric construction from its numerical
prime-power indexing.  A `FiniteFieldModel` stores the carrier and the exact
field and finiteness structures that are used to compute its cardinality.

For every natural-number prime power `q`, `finiteFieldModelOfPrimePower`
chooses a Galois field of cardinality exactly `q`.  The subtype
`PrimePowerIndex` is ordered by its underlying natural number, so `atTop` on
this type is literally the filter "as `q` tends to infinity through prime
powers".  The cofinality theorem below makes that interpretation explicit.

Lean Pool port of wewantmoore commit d59bd80ea93fabb9faf769e790ab47692645e022.
The port adds a namespace and adapts proofs to the current Mathlib APIs and repository style.
-/

namespace MooreBound

open Filter

namespace DegreeDiameter

/-- A finite field together with the particular structures used on its
carrier.  Keeping the structures explicit makes existential prime-power
instantiation straightforward and avoids any hidden choice of instances. -/
structure FiniteFieldModel where
  /-- The underlying type of the finite field. -/
  carrier : Type
  /-- The field structure on the chosen carrier. -/
  field : Field carrier
  finite : Finite carrier

namespace FiniteFieldModel

/-- The cardinality of an explicitly packaged finite field. -/
noncomputable def card (M : FiniteFieldModel) : ℕ :=
  Nat.card M.carrier

end FiniteFieldModel

/-- The cardinality of every finite field is a prime power.  Together with
`exists_finiteFieldModel_of_isPrimePow` below, this records both directions
of the correspondence used by the prime-power indexing. -/
theorem isPrimePow_natCard_finiteField (K : Type*) [Field K] [Finite K] :
    IsPrimePow (Nat.card K) := by
  let : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card]
  exact FiniteField.isPrimePow_card K

/-- Every natural-number prime power is the cardinality of an explicitly
packaged finite field.  The field is the Mathlib Galois field `GF(p^e)`. -/
theorem exists_finiteFieldModel_of_isPrimePow (q : ℕ) (hq : IsPrimePow q) :
    ∃ M : FiniteFieldModel, M.card = q := by
  rcases (isPrimePow_nat_iff q).mp hq with ⟨p, e, hp, he, rfl⟩
  let : Fact (Nat.Prime p) := ⟨hp⟩
  let M : FiniteFieldModel :=
    { carrier := GaloisField p e
      field := inferInstance
      finite := inferInstance }
  refine ⟨M, ?_⟩
  simpa only [FiniteFieldModel.card, M] using
    (GaloisField.card p e he.ne')

/-- A natural number is a prime power exactly when it occurs as the
cardinality of an explicitly packaged finite field. -/
theorem isPrimePow_iff_exists_finiteFieldModel (q : ℕ) :
    IsPrimePow q ↔ ∃ M : FiniteFieldModel, M.card = q := by
  constructor
  · exact exists_finiteFieldModel_of_isPrimePow q
  · rintro ⟨M, rfl⟩
    simpa only [FiniteFieldModel.card] using
      (@isPrimePow_natCard_finiteField M.carrier M.field M.finite)

/-- Natural numbers that are positive powers of a prime.  Its inherited
order is the order of the underlying cardinalities. -/
abbrev PrimePowerIndex := {q : ℕ // IsPrimePow q}

/-- Prime powers are cofinal in the natural numbers.  Consequently `atTop`
on `PrimePowerIndex` is precisely "tending to infinity through prime
powers". -/
theorem tendsto_primePowerIndex_val :
    Tendsto (fun q : PrimePowerIndex ↦ q.1) atTop atTop := by
  apply Monotone.tendsto_atTop_atTop
  · intro a b hab
    exact hab
  · intro n
    obtain ⟨p, hnp, hp⟩ := Nat.exists_infinite_primes n
    exact ⟨⟨p, hp.isPrimePow⟩, hnp⟩

/-- A chosen finite field model of order `q`, for each prime power `q`. -/
noncomputable def finiteFieldModelOfPrimePower (q : PrimePowerIndex) :
    FiniteFieldModel :=
  Classical.choose (exists_finiteFieldModel_of_isPrimePow q.1 q.2)

@[simp]
theorem finiteFieldModelOfPrimePower_card (q : PrimePowerIndex) :
    (finiteFieldModelOfPrimePower q).card = q.1 :=
  Classical.choose_spec (exists_finiteFieldModel_of_isPrimePow q.1 q.2)

/-- A chosen field of each prime-power cardinality.  The construction is
noncomputable only because a prime/exponent presentation of `q` is chosen. -/
noncomputable abbrev PrimePowerField (q : PrimePowerIndex) : Type :=
  (finiteFieldModelOfPrimePower q).carrier

noncomputable instance primePowerFieldField (q : PrimePowerIndex) :
    Field (PrimePowerField q) :=
  (finiteFieldModelOfPrimePower q).field

noncomputable instance primePowerFieldFinite (q : PrimePowerIndex) :
    Finite (PrimePowerField q) :=
  (finiteFieldModelOfPrimePower q).finite

/-- The chosen field really has the prime-power cardinality indexing it. -/
@[simp]
theorem natCard_primePowerField (q : PrimePowerIndex) :
    Nat.card (PrimePowerField q) = q.1 := by
  simpa only [FiniteFieldModel.card] using
    finiteFieldModelOfPrimePower_card q

/-- The cardinalities of the chosen fields tend to infinity along the
prime-power index. -/
theorem tendsto_natCard_primePowerField :
    Tendsto (fun q : PrimePowerIndex ↦ Nat.card (PrimePowerField q))
      atTop atTop := by
  simpa only [natCard_primePowerField] using tendsto_primePowerIndex_val

end DegreeDiameter

end MooreBound
