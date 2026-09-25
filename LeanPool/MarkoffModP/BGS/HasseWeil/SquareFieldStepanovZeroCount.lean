/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.OnePointHeight
public import LeanPool.MarkoffModP.BGS.HasseWeil.SquareFieldStepanovAuxiliary
public import Mathlib.Tactic

/-!
# The square-field Stepanov zero count

This module turns a semilinear square-field Stepanov auxiliary into the
sharp zero-count estimate.  The selected points are represented by an
injective finite family of finite exhaustive places, all away from a
degree-one pole place `P`.

Membership of the two section families in their one-point Riemann spaces
makes every section regular at each selected place.  The square-field local
vanishing theorem then gives positive order of the nonzero first restriction
at every selected place.  Its pole budget is `ell + (#K) * m`, so the
degree-one one-point height bound controls the cardinality of the family by
that same number.
-/

@[expose] public section

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open scoped Polynomial

noncomputable section

variable (K S : Type*) [Field K] [Fintype K]
  [Field S] [Fintype S] [DecidableEq S] [Algebra K S]
  [DecidableEq (RatFunc S)]
variable (L : Type*) [Field L] [Algebra (RatFunc S) L]
  [FiniteDimensional (RatFunc S) L]
  [Algebra.IsSeparable (RatFunc S) L]

local instance squareFieldZeroCountConstantAlgebra : Algebra S L :=
  RingHom.toAlgebra ((algebraMap (RatFunc S) L).comp
    (algebraMap S (RatFunc S)))

local instance squareFieldZeroCountConstantTower :
    IsScalarTower S (RatFunc S) L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- A square-field Stepanov auxiliary bounds any injective finite family of
finite places away from its degree-one pole place.

The quadratic Frobenius identity is required only in the residue field of
each selected place.  Thus the theorem records exactly the local geometric
input used by the semilinear vanishing step, without imposing a global
residue-degree assertion. -/
theorem Fintype.card_le_of_squareFieldStepanovAuxiliary
    {alpha beta iota : Type*} [Fintype iota]
    (P : FiniteExtensionPlace S L) (ell m : Nat)
    (f : alpha → L) (df : alpha → Nat)
    (g : beta → L) (dg : beta → Nat)
    (c : alpha × beta →₀ S)
    (hf : onePointSectionFamilySpec S L P ell f df)
    (hg : onePointSectionFamilySpec S L P m g dg)
    (hdegree : finiteExtensionPlaceDegree S L P = 1)
    (place : iota → FiniteExtensionFinitePlace S L)
    (hinjective : Function.Injective place)
    (haway : ∀ i,
      (Sum.inl (place i) : FiniteExtensionPlace S L) ≠ P)
    (hsquare : ∀ (i : iota) (z : (place i).asIdeal.ResidueField),
      z ^ (Fintype.card K) ^ 2 = z)
    (hsecond : onePointStepanovSecondRestrictionMap S L f g
      (Fintype.card K) c = 0)
    (hfirst : squareFieldStepanovFirstRestriction K S L f g c ≠ 0) :
    Fintype.card iota ≤ ell + Fintype.card K * m := by
  have hfRegular (i : iota) (a : alpha) :
      0 ≤ finiteExtensionPrincipalDivisor S L (f a) (.inl (place i)) := by
    rcases (mem_finiteExtensionOnePointRiemannSpace_iff
      S L P ell (f a)).mp (hf.1 a) with hzero | hdescription
    · exact (hf.2.1 a hzero).elim
    · exact hdescription.2.2 (.inl (place i)) (haway i)
  have hgRegular (i : iota) (b : beta) :
      0 ≤ finiteExtensionPrincipalDivisor S L (g b) (.inl (place i)) := by
    rcases (mem_finiteExtensionOnePointRiemannSpace_iff
      S L P m (g b)).mp (hg.1 b) with hzero | hdescription
    · exact (hg.2.1 b hzero).elim
    · exact hdescription.2.2 (.inl (place i)) (haway i)
  have hpositive (i : iota) :
      0 < finiteExtensionPrincipalDivisor S L
        (squareFieldStepanovFirstRestriction K S L f g c)
          (.inl (place i)) := by
    exact (squareFieldStepanovFirstRestriction_eq_zero_or_principalDivisor_pos_at_finitePlace
      K S L (place i) f g c (hfRegular i) (hgRegular i)
        (hsquare i) hsecond).resolve_left hfirst
  have hplaceInjective : Function.Injective
      (fun i => (Sum.inl (place i) : FiniteExtensionPlace S L)) := by
    intro i j hij
    apply hinjective
    exact Sum.inl.inj hij
  have hspace : squareFieldStepanovFirstRestriction K S L f g c ∈
      finiteExtensionOnePointRiemannSpace S L P
        (ell + Fintype.card K * m) :=
    squareFieldStepanovFirstRestriction_mem K S L P f g ell m
      hf.1 hg.1 c
  exact Fintype.card_le_of_onePointRiemannSpace_degree_one
    S L P (ell + Fintype.card K * m)
      (squareFieldStepanovFirstRestriction K S L f g c)
      hfirst hspace hdegree
      (fun i => (Sum.inl (place i) : FiniteExtensionPlace S L))
      hplaceInjective hpositive

end

end BGS.HasseWeil
