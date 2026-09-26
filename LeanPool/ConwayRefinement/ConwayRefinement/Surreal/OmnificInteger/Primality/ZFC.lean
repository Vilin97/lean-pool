/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.ZFC.OmnificInteger
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.ZFC.OmnificCodes
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.ZFC.Reduced
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.OmnificInteger.Primality.IrreducibleOmnificIntegers
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.OmnificInteger.Primality.FiniteClasses

import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Divisibility.PrimalPreimage

/-!
# Factorisation in the class presentation of the omnific integers

The cut-preserving ring equivalence carries factors and divisibility witnesses in both directions.
Consequently the factorisation conclusions hold for the proper-class presentation as well.
-/

universe u

public noncomputable section

namespace ZFSet.Surreal.OmnificInteger

/-- An ordinary omnific class value is an integer cast. -/
def IsOrdinaryInteger (x : OmnificInteger.{u}) : Prop := ∃ z : ℤ, x = z

/-- Ordinary integers agree in the class and library presentations. -/
theorem isOrdinaryInteger_iff (x : OmnificInteger.{u}) :
    x.IsOrdinaryInteger ↔ _root_.Surreal.OmnificInteger.IsOrdinaryInteger (ringEquiv x) := by
  rw [IsOrdinaryInteger, _root_.Surreal.OmnificInteger.isOrdinaryInteger_iff]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, by simp⟩
  · rintro ⟨z, hz⟩
    refine ⟨z, ringEquiv.injective ?_⟩
    rw [map_intCast]
    exact Subtype.ext hz

/-- Every irreducible omnific class value is prime. -/
theorem prime_of_irreducible (x : OmnificInteger.{u}) (hx : Irreducible x) : Prime x :=
  (MulEquiv.prime_iff ringEquiv).1
    (_root_.Surreal.OmnificInteger.prime_of_irreducible (ringEquiv x)
      ((MulEquiv.irreducible_iff ringEquiv).2 hx))

/-- Two finite factorisations into irreducible class values agree up to order and units. -/
theorem factorization_unique {f g : Multiset OmnificInteger.{u}}
    (hf : ∀ x ∈ f, Irreducible x) (hg : ∀ x ∈ g, Irreducible x)
    (hfg : Associated f.prod g.prod) :
    Multiset.Rel Associated f g :=
  prime_factors_unique (fun x hx ↦ prime_of_irreducible x (hf x hx))
    (fun x hx ↦ prime_of_irreducible x (hg x hx)) hfg

/-- Every reduced, nonordinary omnific class value is primal. -/
theorem isPrimal_of_isReduced (x : OmnificInteger.{u}) (hx : ¬x.IsOrdinaryInteger)
    (hred : ZFSet.Surreal.IsReduced (x : ZFSet.Surreal.{u})) : IsPrimal x :=
  (RingEquiv.isPrimal_iff ringEquiv x).1
    (_root_.Surreal.OmnificInteger.isPrimal_of_isReduced (ringEquiv x)
      (fun h ↦ hx ((isOrdinaryInteger_iff x).2 h))
      ((isReduced_iff_toSignedNonpositiveHahn x).1 hred))

/-- A nonzero omnific class value meeting finitely many support classes is primal. -/
theorem isPrimal_of_hasFiniteSupportClasses (x : OmnificInteger.{u}) (_hx : x ≠ 0)
    (hfinite : ZFSet.Surreal.HasFiniteSupportClasses (x : ZFSet.Surreal.{u})) : IsPrimal x := by
  apply (RingEquiv.isPrimal_iff ringEquiv x).1
  apply _root_.Surreal.OmnificInteger.isPrimal_of_supportArchimedeanClasses_finite
  rw [_root_.Surreal.OmnificInteger.supportArchimedeanClasses_toSignedNonpositiveHahn,
    ringEquiv_apply, coe_toOmnificInteger]
  exact (ZFSet.Surreal.hasFiniteSupportClasses_iff_toSurreal _).1 hfinite


end ZFSet.Surreal.OmnificInteger

namespace ZFSet.OmnificCode

/-- Every irreducible omnific set code is prime, with no restriction on factor codes. -/
theorem isPrime_of_isIrreducible (x : OmnificCode.{u}) (hx : x.IsIrreducible) : x.IsPrime :=
  (isPrime_iff x).2 (_root_.Surreal.OmnificInteger.prime_of_irreducible x.value
    ((isIrreducible_iff x).1 hx))

end ZFSet.OmnificCode
