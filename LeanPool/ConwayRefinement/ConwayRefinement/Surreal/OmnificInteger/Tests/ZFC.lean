/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.OmnificInteger.Primality.ZFC
public import LeanPool.ConwayRefinement.ConwayRefinement.Examples.OmnificInteger.ZFCDegreeTwoPrime
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.ZFC.Properness
public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.ZFC.Refinement

/-!
# Certificates for factorisation over the class of omnific codes

The explicit degree-two example supplies an irreducible code with infinite support, so the
irreducible-to-prime implication is not vacuous and does not describe only ordinary integers.
The zero and unit cases check the public factorisation predicates. The remaining certificates
check the exported conclusions for native class values and their normal forms.
-/

universe u

public noncomputable section

namespace Tests.ZFC

open ZFSet

/-- A nonordinary, infinite-support irreducible code exercises the class-wide prime theorem. -/
theorem exists_degreeTwo_prime_code :
    ∃ c : OmnificCode.{u},
      c.value = _root_.Surreal.OmnificInteger.DegreeTwoExample.degreeTwoOz ∧
      c.IsIrreducible ∧ c.IsPrime := by
  obtain ⟨c, hc⟩ := OmnificCode.value_surjective
    _root_.Surreal.OmnificInteger.DegreeTwoExample.degreeTwoOz.{u}
  have hp : Prime c.value := by
    rw [hc]
    exact _root_.Surreal.OmnificInteger.DegreeTwoExample.degreeTwoOz_prime
  have hi := (OmnificCode.isIrreducible_iff c).2 hp.irreducible
  exact ⟨c, hc, hi, OmnificCode.isPrime_of_isIrreducible c hi⟩

example : ¬(0 : OmnificCode.{u}).IsPrime := by
  simp [OmnificCode.isPrime_iff]

example : ¬(1 : OmnificCode.{u}).IsIrreducible := by
  simp [OmnificCode.isIrreducible_iff]

example : (1 : OmnificCode.{u}).IsUnit := by
  simp [OmnificCode.isUnit_iff]

example : OmnificCode.Divides (0 : OmnificCode.{u}) 0 := by
  simp [OmnificCode.divides_iff]

example : ¬OmnificCode.Divides (0 : OmnificCode.{u}) 1 := by
  simp [OmnificCode.divides_iff]

example (z : ZFSet.{u}) (h : IsGameCode z)
    (hz : (GameCode.mk z h).IsOmnificInteger)
    (hi : (⟨GameCode.mk z h, hz⟩ : OmnificCode.{u}).IsIrreducible) :
    (⟨GameCode.mk z h, hz⟩ : OmnificCode.{u}).IsPrime :=
  OmnificCode.isPrime_of_isIrreducible _ hi

example : ∀ s : ZFSet.{u}, omnificGameCodes ≠ Class.ofSet s :=
  omnificGameCodes_ne_ofSet

example (x : ZFSet.Surreal.OmnificInteger.{u}) (hx : Irreducible x) : Prime x :=
  ZFSet.Surreal.OmnificInteger.prime_of_irreducible x hx

example (x : ZFSet.Surreal.OmnificInteger.{u}) (hx : x ≠ 0)
    (hf : ZFSet.Surreal.HasFiniteSupportClasses (x : ZFSet.Surreal.{u})) : IsPrimal x :=
  ZFSet.Surreal.OmnificInteger.isPrimal_of_hasFiniteSupportClasses x hx hf

example (x : ZFSet.Surreal.OmnificInteger.{u})
    (hx : ¬x.IsOrdinaryInteger) (hr : ZFSet.Surreal.IsReduced (x : ZFSet.Surreal.{u})) :
    IsPrimal x :=
  ZFSet.Surreal.OmnificInteger.isPrimal_of_isReduced x hx hr

open ZFSet.Surreal.OmnificInteger.DegreeTwoExample

example :
    ZFSet.Surreal.toHahnSeries (degreeTwoOz.{u} : ZFSet.Surreal.{u}) =
      _root_.Surreal.OmnificInteger.DegreeTwoExample.normalForm :=
  degreeTwoOz_toHahnSeries

example (x : ZFSet.Surreal.OmnificInteger.{u}) :
    ZFSet.Surreal.toHahnSeries (x : ZFSet.Surreal.{u}) =
      _root_.Surreal.OmnificInteger.DegreeTwoExample.normalForm ↔ x = degreeTwoOz :=
  toHahnSeries_eq_normalForm_iff x

example :
    (ZFSet.Surreal.toHahnSeries (degreeTwoOz.{u} : ZFSet.Surreal.{u})).length =
      Ordinal.omega0 ^ (2 : Ordinal) + 1 :=
  degreeTwoOz_length

example : ZFSet.Surreal.IsReduced (degreeTwoOz.{u} : ZFSet.Surreal.{u}) :=
  degreeTwoOz_isReduced

example : Prime degreeTwoOz.{u} := degreeTwoOz_prime

example : ZFSet.Surreal.OmnificInteger.RefinementConjecture.{u} ↔
    ConwayRefinementConjecture.{u} :=
  ZFSet.Surreal.OmnificInteger.refinementConjecture_iff

end Tests.ZFC
