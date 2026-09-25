/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionPlaceTower
public import LeanPool.MarkoffModP.BGS.HasseWeil.RationalPlace

/-!
# Restriction of rational places in a function-field tower

Place degree is multiplicative in a tower.  Consequently a degree-one place
of the top field restricts to a degree-one place of every intermediate field,
and its relative residue degree is one.  This file packages that consequence
for the repository's exhaustive finite/infinity place type.
-/

@[expose] public section

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier

variable (K : Type*) [Field K] [DecidableEq K] [DecidableEq (RatFunc K)]
variable (M : Type*) [Field M] [Algebra (RatFunc K) M]
  [FiniteDimensional (RatFunc K) M]
  [Algebra.IsSeparable (RatFunc K) M]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]
  [Algebra M L] [IsScalarTower (RatFunc K) M L]

/-- A degree-one finite place of the top field restricts to a degree-one
finite place of the intermediate field. -/
def rationalFinitePlaceUnder
    (Q : FiniteExtensionRationalFinitePlace K L) :
    FiniteExtensionRationalFinitePlace K M := by
  refine ⟨finitePlaceUnder K M L Q.1, ?_⟩
  have hmul :=
    finiteExtensionPlaceDegree_inl_eq_mul_relativeInertiaDeg K M L Q.1
  rw [Q.2] at hmul
  exact Nat.eq_one_of_dvd_one
    ⟨finitePlaceRelativeInertiaDeg K M L Q.1, hmul⟩

/-- A degree-one place above infinity restricts to a degree-one place above
infinity in the intermediate field. -/
def rationalInfinityPlaceUnder
    (Q : FiniteExtensionRationalInfinityPlace K L) :
    FiniteExtensionRationalInfinityPlace K M := by
  refine ⟨infinityPlaceUnder K M L Q.1, ?_⟩
  have hmul :=
    finiteExtensionPlaceDegree_inr_eq_mul_relativeInertiaDeg K M L Q.1
  rw [Q.2] at hmul
  exact Nat.eq_one_of_dvd_one
    ⟨infinityPlaceRelativeInertiaDeg K M L Q.1, hmul⟩

/-- Restriction of an exhaustive degree-one place through an intermediate
function field. -/
def rationalPlaceUnder :
    FiniteExtensionRationalPlace K L →
      FiniteExtensionRationalPlace K M
  | .inl Q => .inl (rationalFinitePlaceUnder K M L Q)
  | .inr Q => .inr (rationalInfinityPlaceUnder K M L Q)

omit [FiniteDimensional (RatFunc K) M] [Algebra.IsSeparable (RatFunc K) M]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L] in
/-- The relative residue degree of a rational finite place is one. -/
theorem rationalFinitePlace_relativeInertiaDeg_eq_one
    (Q : FiniteExtensionRationalFinitePlace K L) :
    finitePlaceRelativeInertiaDeg K M L Q.1 = 1 := by
  have hmul :=
    finiteExtensionPlaceDegree_inl_eq_mul_relativeInertiaDeg K M L Q.1
  rw [Q.2] at hmul
  exact Nat.eq_one_of_dvd_one
    ⟨finiteExtensionPlaceDegree K M
      (.inl (finitePlaceUnder K M L Q.1)), by
        simpa only [Nat.mul_comm] using hmul⟩

omit [FiniteDimensional (RatFunc K) M] [Algebra.IsSeparable (RatFunc K) M]
  [FiniteDimensional (RatFunc K) L] [Algebra.IsSeparable (RatFunc K) L] in
/-- The relative residue degree of a rational place above infinity is one. -/
theorem rationalInfinityPlace_relativeInertiaDeg_eq_one
    (Q : FiniteExtensionRationalInfinityPlace K L) :
    infinityPlaceRelativeInertiaDeg K M L Q.1 = 1 := by
  have hmul :=
    finiteExtensionPlaceDegree_inr_eq_mul_relativeInertiaDeg K M L Q.1
  rw [Q.2] at hmul
  exact Nat.eq_one_of_dvd_one
    ⟨finiteExtensionPlaceDegree K M
      (.inr (infinityPlaceUnder K M L Q.1)), by
        simpa only [Nat.mul_comm] using hmul⟩

end

end BGS.HasseWeil
