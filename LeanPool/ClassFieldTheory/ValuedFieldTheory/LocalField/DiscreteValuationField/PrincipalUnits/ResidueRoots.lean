/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Filtration
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.HenselLemma
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-! # Residue Roots -/

@[expose] public section
namespace LocalFieldTheory

open ValuationTheory
open ValuationTheory.DiscreteValuationField.ResidueField

/-!
# Residue roots of unity

Hensel lifting identifies the finite residue-field unit group with the lifted roots of
unity in the valuation ring.
-/

noncomputable
section

open scoped BigOperators

universe u v

namespace DiscreteValuationField
namespace CompleteDVF

variable {K : Type u} [Field K]

namespace higherPrincipalUnitGroup

variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)

/-- The `(q - 1)`-st roots of unity in the valuation ring, where
`q = #κ`. -/
abbrev residueRootsOfUnityGroup :
    Subgroup F.valuationSubringˣ :=
  rootsOfUnity (Nat.card F.residueField - 1) F.valuationSubring

/-- Every nonzero residue class is a simple root of
`X^(#κ - 1) - 1`. -/
theorem residueRootPolynomial_derivative_eval_ne_zero
    [Finite F.residueField] (y : F.residueFieldˣ) :
    (((Polynomial.X ^ (Nat.card F.residueField - 1) - 1 :
        Polynomial F.residueField).derivative).eval
          (y : F.residueField)) ≠ 0 := by
  classical
  let := Fintype.ofFinite F.residueField
  have hn :
      ((Nat.card F.residueField - 1 : ℕ) : F.residueField) ≠ 0 := by
    have hunitcard :
        (Fintype.card F.residueFieldˣ : F.residueField) ≠ 0 := by
      simpa using
        (FiniteField.card_cast_subgroup_card_ne_zero
          (K := F.residueField) (⊤ : Subgroup F.residueFieldˣ))
    simpa [Nat.card_eq_fintype_card, Fintype.card_units] using hunitcard
  have hy :
      (y : F.residueField) ^ ((Nat.card F.residueField - 1) - 1) ≠ 0 :=
    pow_ne_zero _ y.ne_zero
  have hmul :
      ((Nat.card F.residueField - 1 : ℕ) : F.residueField) *
          (y : F.residueField) ^
            ((Nat.card F.residueField - 1) - 1) ≠ 0 :=
    mul_ne_zero hn hy
  simpa [Polynomial.derivative_sub, Polynomial.derivative_one,
    Polynomial.derivative_X_pow, Polynomial.eval_mul] using hmul

/-- Hensel lift of finite-residue-field roots of unity: every residue-field
unit has a valuation-ring unit representative satisfying `u^(q - 1) = 1`.

This is the substantive splitting input for the multiplicative unit decomposition:
it upgrades the quotient isomorphism `O^*/U^1 ≃ κ^*` from an abstract
first-isomorphism statement to a root-of-unity representative in `O^*`. -/
theorem exists_residueRootsOfUnity_lift
    [Finite F.residueField] (y : F.residueFieldˣ) :
    ∃ u : F.valuationSubringˣ,
      u ∈ higherPrincipalUnitGroup.residueRootsOfUnityGroup F ∧
        higherPrincipalUnitGroup.residueUnitHom F u = y := by
  classical
  let n := Nat.card F.residueField - 1
  let f : Polynomial F.valuationSubring := Polynomial.X ^ n - 1
  have hnpos : 0 < n := by
    let := Fintype.ofFinite F.residueField
    have hunitpos : 0 < Fintype.card F.residueFieldˣ :=
      Fintype.card_pos_iff.mpr ⟨1⟩
    simpa [n, Nat.card_eq_fintype_card, Fintype.card_units] using hunitpos
  have hf : f.Monic := by
    dsimp [f, n]
    simpa using
      (Polynomial.monic_X_pow_sub_C
        (1 : F.valuationSubring) (ne_of_gt hnpos))
  have hroot : (f.map F.residueMap).eval (y : F.residueField) = 0 := by
    let := Fintype.ofFinite F.residueField
    have hpow :
        (y : F.residueField) ^ (Fintype.card F.residueField - 1) = 1 :=
      FiniteField.pow_card_sub_one_eq_one
        (K := F.residueField) (y : F.residueField) y.ne_zero
    simp [f, n, Nat.card_eq_fintype_card, Polynomial.eval_sub, hpow]
  have hsimple :
      ((f.map F.residueMap).derivative).eval
        (y : F.residueField) ≠ 0 := by
    simpa [f, n] using
      (higherPrincipalUnitGroup.residueRootPolynomial_derivative_eval_ne_zero
        (F := F) y)
  rcases
      F.toHenselianDVF.exists_monic_linear_factor_lift_of_reduced_simple_root
        f hf (y : F.residueField) hroot hsimple with
    ⟨a, q, ha_root, ha_residue, _hlinear, _hq, _hfactor⟩
  have hunit : IsUnit a :=
    (F.residue_ne_zero_iff_isUnit a).1
      (by
        change F.toHenselianDVF.residueMap a ≠ 0
        rw [ha_residue]
        exact y.ne_zero)
  rcases hunit with ⟨u, hu⟩
  have ha_pow : a ^ n = 1 := by
    have ha_eval : f.eval a = 0 := Polynomial.IsRoot.def.mp ha_root
    have hsub : a ^ n - 1 = 0 := by
      simpa [f, n, Polynomial.eval_sub] using ha_eval
    exact sub_eq_zero.mp hsub
  refine ⟨u, ?_, ?_⟩
  · rw [mem_rootsOfUnity]
    apply Units.ext
    change
      (((u : F.toHenselianDVF.valuationSubring) : F.valuationSubring) ^
          (Nat.card F.residueField - 1)) =
        (1 : F.valuationSubring)
    simpa [n, hu] using ha_pow
  · apply Units.ext
    rw [higherPrincipalUnitGroup.residueUnitHom_apply]
    rw [hu]
    exact ha_residue

/-- The residue map restricted to the Hensel-lifted `(q - 1)`-roots of unity. -/
def residueRootsOfUnityResidueHom [Finite F.residueField] :
    higherPrincipalUnitGroup.residueRootsOfUnityGroup F →* F.residueFieldˣ :=
  (higherPrincipalUnitGroup.residueUnitHom F).comp
    (higherPrincipalUnitGroup.residueRootsOfUnityGroup F).subtype

/--
The specified map is surjective: `Function.Surjective
(higherPrincipalUnitGroup.residueRootsOfUnityResidueHom F)`.
-/
theorem residueRootsOfUnityResidueHom_surjective
    [Finite F.residueField] :
    Function.Surjective
      (higherPrincipalUnitGroup.residueRootsOfUnityResidueHom F) := by
  intro y
  rcases higherPrincipalUnitGroup.exists_residueRootsOfUnity_lift
      (F := F) y with
    ⟨u, hu, hres⟩
  exact ⟨⟨u, hu⟩, hres⟩

/-- A unit satisfying the Teichmuller equation is a root of
`X^(q - 1) - 1` over the valuation ring. -/
theorem residueRootPolynomial_isRoot_of_mem
    [Finite F.residueField] {u : F.valuationSubringˣ}
    (hu : u ∈ higherPrincipalUnitGroup.residueRootsOfUnityGroup F) :
    (Polynomial.X ^ (Nat.card F.residueField - 1) - 1 :
        Polynomial F.valuationSubring).IsRoot
      (u : F.valuationSubring) := by
  rw [mem_rootsOfUnity] at hu
  have hpow :
      (u : F.valuationSubring) ^ (Nat.card F.residueField - 1) = 1 := by
    have hunit :=
      congrArg (fun z : F.valuationSubringˣ => (z : F.valuationSubring)) hu
    simpa using hunit
  exact Polynomial.IsRoot.def.mpr (by
    simp [Polynomial.eval_sub, hpow])

/-- The derivative of `X^(q - 1) - 1` at a valuation-ring unit is a unit.
This is the simple-root input for uniqueness of Teichmuller representatives. -/
theorem residueRootPolynomial_derivative_eval_isUnit
    [Finite F.residueField] (u : F.valuationSubringˣ) :
    IsUnit
      (((Polynomial.X ^ (Nat.card F.residueField - 1) - 1 :
          Polynomial F.valuationSubring).derivative).eval
        (u : F.valuationSubring)) := by
  let n := Nat.card F.residueField - 1
  let f : Polynomial F.valuationSubring := Polynomial.X ^ n - 1
  have hres :
      F.residueMap (f.derivative.eval (u : F.valuationSubring)) =
        ((f.map F.residueMap).derivative).eval
          (F.residueMap (u : F.valuationSubring)) := by
    calc
      F.residueMap (f.derivative.eval (u : F.valuationSubring)) =
          (f.derivative.map F.residueMap).eval
            (F.residueMap (u : F.valuationSubring)) := by
        exact (Polynomial.eval_map_apply (f := F.residueMap)
          (p := f.derivative) (u : F.valuationSubring)).symm
      _ = ((f.map F.residueMap).derivative).eval
          (F.residueMap (u : F.valuationSubring)) := by
        rw [Polynomial.derivative_map]
  have hsimple :
      ((f.map F.residueMap).derivative).eval
          (F.residueMap (u : F.valuationSubring)) ≠ 0 := by
    simpa [f, n, higherPrincipalUnitGroup.residueUnitHom] using
      higherPrincipalUnitGroup.residueRootPolynomial_derivative_eval_ne_zero
        (F := F) (higherPrincipalUnitGroup.residueUnitHom F u)
  exact
    (F.residue_ne_zero_iff_isUnit
      (f.derivative.eval (u : F.valuationSubring))).1
      (by
        rw [hres]
        exact hsimple)

/--
The specified map is injective: `Function.Injective
(higherPrincipalUnitGroup.residueRootsOfUnityResidueHom F)`.
-/
theorem residueRootsOfUnityResidueHom_injective
    [Finite F.residueField] :
    Function.Injective
      (higherPrincipalUnitGroup.residueRootsOfUnityResidueHom F) := by
  intro x y hxy
  let n := Nat.card F.residueField - 1
  let f : Polynomial F.valuationSubring := Polynomial.X ^ n - 1
  have hxroot :
      f.IsRoot ((x : F.valuationSubringˣ) : F.valuationSubring) := by
    dsimp [f, n]
    exact
      higherPrincipalUnitGroup.residueRootPolynomial_isRoot_of_mem
        (F := F) x.property
  have hyroot :
      f.IsRoot ((y : F.valuationSubringˣ) : F.valuationSubring) := by
    dsimp [f, n]
    exact
      higherPrincipalUnitGroup.residueRootPolynomial_isRoot_of_mem
        (F := F) y.property
  have hres :
      F.residueMap ((y : F.valuationSubringˣ) : F.valuationSubring) =
        F.residueMap ((x : F.valuationSubringˣ) : F.valuationSubring) := by
    have hval :=
      congrArg (fun z : F.residueFieldˣ => (z : F.residueField)) hxy
    simpa [higherPrincipalUnitGroup.residueRootsOfUnityResidueHom,
      higherPrincipalUnitGroup.residueUnitHom] using hval.symm
  have hderiv :
      IsUnit
        (f.derivative.eval
          ((x : F.valuationSubringˣ) : F.valuationSubring)) := by
    dsimp [f, n]
    exact
      higherPrincipalUnitGroup.residueRootPolynomial_derivative_eval_isUnit
        (F := F) (x : F.valuationSubringˣ)
  have hring :
      ((y : F.valuationSubringˣ) : F.valuationSubring) =
        ((x : F.valuationSubringˣ) : F.valuationSubring) :=
    F.toHenselianDVF.eq_of_isRoot_of_isRoot_of_residue_eq_of_derivative_isUnit
      (f := f) hxroot hyroot hres hderiv
  apply Subtype.ext
  apply Units.ext
  exact hring.symm

/--
The specified map is bijective: `Function.Bijective
(higherPrincipalUnitGroup.residueRootsOfUnityResidueHom F)`.
-/
theorem residueRootsOfUnityResidueHom_bijective
    [Finite F.residueField] :
    Function.Bijective
      (higherPrincipalUnitGroup.residueRootsOfUnityResidueHom F) :=
  ⟨higherPrincipalUnitGroup.residueRootsOfUnityResidueHom_injective F,
    higherPrincipalUnitGroup.residueRootsOfUnityResidueHom_surjective F⟩

/-- Hensel's splitting of the residue-unit map on the `(q - 1)`-roots of
unity: the Teichmuller representatives in `O^*` are exactly `κ^*`. -/
noncomputable def residueRootsOfUnityEquivResidueFieldUnits
    [Finite F.residueField] :
    higherPrincipalUnitGroup.residueRootsOfUnityGroup F ≃*
      F.residueFieldˣ :=
  MulEquiv.ofBijective
    (higherPrincipalUnitGroup.residueRootsOfUnityResidueHom F)
    (higherPrincipalUnitGroup.residueRootsOfUnityResidueHom_bijective F)

/--
The defining evaluation formula for `residueRootsOfUnityEquivResidueFieldUnits` is
`higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits F u =
higherPrincipalUnitGroup.residueUnitHom F u`.
-/
@[simp] theorem residueRootsOfUnityEquivResidueFieldUnits_apply
    [Finite F.residueField]
    (u : higherPrincipalUnitGroup.residueRootsOfUnityGroup F) :
    higherPrincipalUnitGroup.residueRootsOfUnityEquivResidueFieldUnits F u =
      higherPrincipalUnitGroup.residueUnitHom F u :=
  rfl
end higherPrincipalUnitGroup

end CompleteDVF
end DiscreteValuationField

end

end LocalFieldTheory
