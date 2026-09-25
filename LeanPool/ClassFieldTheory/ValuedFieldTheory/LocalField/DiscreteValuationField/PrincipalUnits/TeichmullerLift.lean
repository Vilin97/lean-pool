/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.ResidueRoots
public import Mathlib.Algebra.CharP.Lemmas

/-! # Teichmuller Lift -/

@[expose] public section
namespace LocalFieldTheory

open ValuationTheory
open ValuationTheory.DiscreteValuationField.ResidueField

/-!
# Teichmuller lifts

Constructs multiplicative Teichmuller representatives, and in equal characteristic the
coefficient-field section of the residue map.
-/

noncomputable section

open scoped BigOperators

universe u v

namespace DiscreteValuationField
namespace CompleteDVF

variable {K : Type u} [Field K]

namespace higherPrincipalUnitGroup

variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)

/-- The Teichmuller representative lift from the finite residue field to the
valuation ring: `0` lifts to `0`, and nonzero residue classes lift through the
root-of-unity splitting of `κˣ`. -/
noncomputable def residueTeichmullerLift [Finite F.residueField] :
    F.residueField → F.valuationSubring :=
  fun y =>
    letI := Classical.decEq F.residueField
    if hy : y = 0 then
      0
    else
      (((higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits F).symm
          (Units.mk0 y hy) :
        higherPrincipalUnitGroup.residueRootsOfUnityGroup F) :
        F.valuationSubringˣ)

/-- Establishes the identity `higherPrincipalUnitGroup.residueTeichmullerLift F 0 = 0`. -/
@[simp] theorem residueTeichmullerLift_zero [Finite F.residueField] :
    higherPrincipalUnitGroup.residueTeichmullerLift F 0 = 0 := by
  simp [higherPrincipalUnitGroup.residueTeichmullerLift]

/-- Establishes the identity `higherPrincipalUnitGroup.residueTeichmullerLift F 1 = 1`. -/
@[simp] theorem residueTeichmullerLift_one [Finite F.residueField] :
    higherPrincipalUnitGroup.residueTeichmullerLift F 1 = 1 := by
  let e :=
    higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits F
  have hone : (1 : F.residueField) ≠ 0 := one_ne_zero
  have hroot :
      e.symm (Units.mk0 (1 : F.residueField) hone) = 1 := by
    apply e.injective
    simp [e]
  have hunit :
      ((e.symm (Units.mk0 (1 : F.residueField) hone) :
          higherPrincipalUnitGroup.residueRootsOfUnityGroup F) :
          F.valuationSubringˣ) = 1 := by
    simp
  simp [higherPrincipalUnitGroup.residueTeichmullerLift, hone]

/-- The Teichmuller lift reduces to the residue class it lifts. -/
theorem residueMap_residueTeichmullerLift [Finite F.residueField]
    (y : F.residueField) :
    F.residueMap (higherPrincipalUnitGroup.residueTeichmullerLift F y) = y := by
  classical
  by_cases hy : y = 0
  · simp [higherPrincipalUnitGroup.residueTeichmullerLift, hy]
  · let e :=
      higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits F
    have hroot :
        higherPrincipalUnitGroup.residueUnitHom F
            (((e.symm (Units.mk0 y hy) :
              higherPrincipalUnitGroup.residueRootsOfUnityGroup F) :
              F.valuationSubringˣ)) =
          Units.mk0 y hy := by
      change e (e.symm (Units.mk0 y hy)) = Units.mk0 y hy
      simp
    have hval :=
      congrArg (fun u : F.residueFieldˣ => (u : F.residueField)) hroot
    simpa [higherPrincipalUnitGroup.residueTeichmullerLift, hy, e,
      higherPrincipalUnitGroup.residueUnitHom] using hval

/-- The Teichmuller lift is multiplicative. -/
theorem residueTeichmullerLift_mul [Finite F.residueField]
    (x y : F.residueField) :
    higherPrincipalUnitGroup.residueTeichmullerLift F (x * y) =
      higherPrincipalUnitGroup.residueTeichmullerLift F x *
        higherPrincipalUnitGroup.residueTeichmullerLift F y := by
  classical
  by_cases hx : x = 0
  · simp [higherPrincipalUnitGroup.residueTeichmullerLift, hx]
  by_cases hy : y = 0
  · simp [higherPrincipalUnitGroup.residueTeichmullerLift, hy]
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  let e :=
    higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits F
  have hroot :
      e.symm (Units.mk0 (x * y) hxy) =
        e.symm (Units.mk0 x hx) * e.symm (Units.mk0 y hy) := by
    apply e.injective
    apply Units.ext
    simp [e]
  have hunit :
      ((e.symm (Units.mk0 (x * y) hxy) :
          higherPrincipalUnitGroup.residueRootsOfUnityGroup F) :
          F.valuationSubringˣ) =
        ((e.symm (Units.mk0 x hx) :
            higherPrincipalUnitGroup.residueRootsOfUnityGroup F) :
            F.valuationSubringˣ) *
          ((e.symm (Units.mk0 y hy) :
            higherPrincipalUnitGroup.residueRootsOfUnityGroup F) :
            F.valuationSubringˣ) := by
    simp
  simp [higherPrincipalUnitGroup.residueTeichmullerLift, hx, hy, hxy]

/-- Every Teichmuller representative is a root of `T^q - T`, where
`q = #κ`. -/
theorem residueTeichmullerLift_pow_card [Finite F.residueField]
    (y : F.residueField) :
    higherPrincipalUnitGroup.residueTeichmullerLift F y ^
        Nat.card F.residueField =
      higherPrincipalUnitGroup.residueTeichmullerLift F y := by
  classical
  let := Fintype.ofFinite F.residueField
  have hcard_pos : 0 < Nat.card F.residueField := by
    simpa [Nat.card_eq_fintype_card] using
      (Fintype.card_pos : 0 < Fintype.card F.residueField)
  by_cases hy : y = 0
  · simp [higherPrincipalUnitGroup.residueTeichmullerLift, hy]
  · let u : higherPrincipalUnitGroup.residueRootsOfUnityGroup F :=
      (higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits F).symm
        (Units.mk0 y hy)
    have hpowUnits :
        (u : F.valuationSubringˣ) ^
            (Nat.card F.residueField - 1) = 1 :=
      u.property
    have hpowRing :
        ((u : F.valuationSubringˣ) : F.valuationSubring) ^
            (Nat.card F.residueField - 1) = 1 := by
      simpa using
        congrArg (fun z : F.valuationSubringˣ => (z : F.valuationSubring))
          hpowUnits
    have hpow :
        ((u : F.valuationSubringˣ) : F.valuationSubring) ^
            Nat.card F.residueField =
          ((u : F.valuationSubringˣ) : F.valuationSubring) := by
      calc
        ((u : F.valuationSubringˣ) : F.valuationSubring) ^
            Nat.card F.residueField =
            ((u : F.valuationSubringˣ) : F.valuationSubring) ^
              ((Nat.card F.residueField - 1) + 1) := by
              rw [Nat.sub_one_add_one_eq_of_pos hcard_pos]
        _ =
            ((u : F.valuationSubringˣ) : F.valuationSubring) ^
              (Nat.card F.residueField - 1) *
            ((u : F.valuationSubringˣ) : F.valuationSubring) := by
              rw [pow_succ]
        _ = ((u : F.valuationSubringˣ) : F.valuationSubring) := by
              rw [hpowRing, one_mul]
    simpa [higherPrincipalUnitGroup.residueTeichmullerLift, hy, u] using hpow

/--
Every residue Teichmüller lift is a root of the polynomial `X^q - X`, where `q` is the
residue-field cardinality.
-/
theorem residueTeichmullerLift_isRoot_X_pow_card_sub_X
    [Finite F.residueField] (y : F.residueField) :
    (Polynomial.X ^ Nat.card F.residueField - Polynomial.X :
        Polynomial F.valuationSubring).IsRoot
      (higherPrincipalUnitGroup.residueTeichmullerLift F y) := by
  rw [Polynomial.IsRoot.def]
  simp [Polynomial.eval_sub,
    higherPrincipalUnitGroup.residueTeichmullerLift_pow_card]

/-- In equal characteristic, `T^q - T` has unit derivative at every
Teichmuller representative. -/
theorem residueTeichmullerRootPolynomial_derivative_eval_isUnit_of_charP
    [Finite F.residueField] (p : ℕ) [Fact p.Prime]
    [CharP F.valuationSubring p] {n : ℕ+}
    (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (y : F.residueField) :
    IsUnit
      (((Polynomial.X ^ Nat.card F.residueField - Polynomial.X :
          Polynomial F.valuationSubring).derivative).eval
        (higherPrincipalUnitGroup.residueTeichmullerLift F y)) := by
  have hp_dvd_card : p ∣ Nat.card F.residueField := by
    rw [hcard]
    exact dvd_pow_self p n.ne_zero
  have hcard_cast :
      ((Nat.card F.residueField : ℕ) : F.valuationSubring) = 0 :=
    (CharP.cast_eq_zero_iff F.valuationSubring p
      (Nat.card F.residueField)).2 hp_dvd_card
  have hderiv :
      ((Polynomial.X ^ Nat.card F.residueField - Polynomial.X :
          Polynomial F.valuationSubring).derivative).eval
        (higherPrincipalUnitGroup.residueTeichmullerLift F y) = -1 := by
    simp [Polynomial.derivative_sub, Polynomial.derivative_X_pow,
      Polynomial.derivative_X, hcard_cast]
  rw [hderiv]
  exact isUnit_neg_one

/-- In equal characteristic, the Teichmuller lift from the finite residue field
to the valuation ring is additive. -/
theorem residueTeichmullerLift_add_of_charP [Finite F.residueField]
    (p : ℕ) [Fact p.Prime] [CharP F.valuationSubring p] {n : ℕ+}
    (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (x y : F.residueField) :
    higherPrincipalUnitGroup.residueTeichmullerLift F (x + y) =
      higherPrincipalUnitGroup.residueTeichmullerLift F x +
        higherPrincipalUnitGroup.residueTeichmullerLift F y := by
  let f : Polynomial F.valuationSubring :=
    Polynomial.X ^ Nat.card F.residueField - Polynomial.X
  let a : F.valuationSubring :=
    higherPrincipalUnitGroup.residueTeichmullerLift F (x + y)
  let b : F.valuationSubring :=
    higherPrincipalUnitGroup.residueTeichmullerLift F x +
      higherPrincipalUnitGroup.residueTeichmullerLift F y
  have ha : f.IsRoot a := by
    simpa [f, a] using
      higherPrincipalUnitGroup.residueTeichmullerLift_isRoot_X_pow_card_sub_X
        (F := F) (x + y)
  have hb : f.IsRoot b := by
    rw [Polynomial.IsRoot.def]
    have hxpow :=
      higherPrincipalUnitGroup.residueTeichmullerLift_pow_card (F := F) x
    have hypow :=
      higherPrincipalUnitGroup.residueTeichmullerLift_pow_card (F := F) y
    have hfresh :
        b ^ (p ^ (n : ℕ)) =
          higherPrincipalUnitGroup.residueTeichmullerLift F x ^
              (p ^ (n : ℕ)) +
            higherPrincipalUnitGroup.residueTeichmullerLift F y ^
              (p ^ (n : ℕ)) := by
      simpa [b] using
        add_pow_char_pow
          (higherPrincipalUnitGroup.residueTeichmullerLift F x)
          (higherPrincipalUnitGroup.residueTeichmullerLift F y)
          p (n : ℕ)
    have hxpow' :
        higherPrincipalUnitGroup.residueTeichmullerLift F x ^
            (p ^ (n : ℕ)) =
          higherPrincipalUnitGroup.residueTeichmullerLift F x := by
      simpa [hcard] using hxpow
    have hypow' :
        higherPrincipalUnitGroup.residueTeichmullerLift F y ^
            (p ^ (n : ℕ)) =
          higherPrincipalUnitGroup.residueTeichmullerLift F y := by
      simpa [hcard] using hypow
    have hbpow : b ^ Nat.card F.residueField = b := by
      rw [hcard, hfresh]
      rw [hxpow', hypow']
    simp [f, b, Polynomial.eval_sub, hbpow]
  have hres : F.residueMap b = F.residueMap a := by
    simp [a, b, map_add,
      higherPrincipalUnitGroup.residueMap_residueTeichmullerLift]
  have hderiv : IsUnit (f.derivative.eval a) := by
    simpa [f, a] using
      higherPrincipalUnitGroup.residueTeichmullerRootPolynomial_derivative_eval_isUnit_of_charP
        (F := F) p hcard (x + y)
  have hba : b = a :=
    F.toHenselianDVF.eq_of_isRoot_of_isRoot_of_residue_eq_of_derivative_isUnit
      (f := f) ha hb hres hderiv
  simpa [a, b] using hba.symm

/-- In equal characteristic, the Teichmuller lift is a ring homomorphic
coefficient-field section of the residue map. -/
noncomputable def residueTeichmullerRingHomOfCharP
    [Finite F.residueField] (p : ℕ) [Fact p.Prime]
    [CharP F.valuationSubring p] {n : ℕ+}
    (hcard : Nat.card F.residueField = p ^ (n : ℕ)) :
    F.residueField →+* F.valuationSubring where
  toFun := higherPrincipalUnitGroup.residueTeichmullerLift F
  map_zero' := by
    exact higherPrincipalUnitGroup.residueTeichmullerLift_zero (F := F)
  map_one' := by
    exact higherPrincipalUnitGroup.residueTeichmullerLift_one (F := F)
  map_mul' := fun x y =>
    higherPrincipalUnitGroup.residueTeichmullerLift_mul (F := F) x y
  map_add' := fun x y =>
    higherPrincipalUnitGroup.residueTeichmullerLift_add_of_charP
      (F := F) p hcard x y

/--
The defining evaluation formula for `residueTeichmullerRingHomOfCharP` is
`higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP (F := F) p hcard x =
higherPrincipalUnitGroup.residueTeichmullerLift F x`.
-/
@[simp] theorem residueTeichmullerRingHomOfCharP_apply
    [Finite F.residueField] (p : ℕ) [Fact p.Prime]
    [CharP F.valuationSubring p] {n : ℕ+}
    (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (x : F.residueField) :
    higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP
        (F := F) p hcard x =
      higherPrincipalUnitGroup.residueTeichmullerLift F x :=
  rfl

/--
Establishes the identity `F.residueMap.comp
(higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP (F := F) p hcard) = RingHom.id
F.residueField`.
-/
theorem residueMap_comp_residueTeichmullerRingHomOfCharP
    [Finite F.residueField] (p : ℕ) [Fact p.Prime]
    [CharP F.valuationSubring p] {n : ℕ+}
    (hcard : Nat.card F.residueField = p ^ (n : ℕ)) :
    F.residueMap.comp
        (higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP
          (F := F) p hcard) =
      RingHom.id F.residueField := by
  ext x
  exact higherPrincipalUnitGroup.residueMap_residueTeichmullerLift
    (F := F) x

/-- The corresponding coefficient-field embedding into the fraction field. -/
noncomputable def residueTeichmullerFieldHomOfCharP
    [Finite F.residueField] (p : ℕ) [Fact p.Prime]
    [CharP F.valuationSubring p] {n : ℕ+}
    (hcard : Nat.card F.residueField = p ^ (n : ℕ)) :
    F.residueField →+* K :=
  F.valuation.valuationSubring.subtype.comp
    (higherPrincipalUnitGroup.residueTeichmullerRingHomOfCharP
      (F := F) p hcard)

/--
The defining evaluation formula for `residueTeichmullerFieldHomOfCharP` is
`higherPrincipalUnitGroup.residueTeichmullerFieldHomOfCharP (F := F) p hcard x =
(higherPrincipalUnitGroup.residueTeichmullerLift F x : K)`.
-/
@[simp] theorem residueTeichmullerFieldHomOfCharP_apply
    [Finite F.residueField] (p : ℕ) [Fact p.Prime]
    [CharP F.valuationSubring p] {n : ℕ+}
    (hcard : Nat.card F.residueField = p ^ (n : ℕ))
    (x : F.residueField) :
    higherPrincipalUnitGroup.residueTeichmullerFieldHomOfCharP
        (F := F) p hcard x =
      (higherPrincipalUnitGroup.residueTeichmullerLift F x : K) :=
  rfl
end higherPrincipalUnitGroup

end CompleteDVF
end DiscreteValuationField

end

end LocalFieldTheory
