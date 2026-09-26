/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.ResidueField
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Group.Units.Hom

/-! # Filtration -/

@[expose] public section
namespace LocalFieldTheory

open ValuationTheory
open ValuationTheory.DiscreteValuationField.ResidueField

/-!
# Principal-unit filtration from a valuation ring

For a complete DVF `F`, the concrete principal-unit filtration on the unit group
of the valuation ring is

`U^n = { u | u - 1 ∈ m^n }`.

This file turns that definition into the abstract `AntitoneSubgroupFiltration`
used by ramification and norm arguments.
-/

noncomputable
section

open scoped BigOperators

universe u v

namespace DiscreteValuationField
namespace CompleteDVF

variable {K : Type u} [Field K]

/-- The concrete `n`-th principal-unit subgroup of the valuation ring unit group. -/
def higherPrincipalUnitGroup
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) (n : ℕ) :
    Subgroup F.valuationSubringˣ where
  carrier := {u | (u : F.valuationSubring) - 1 ∈ F.maximalIdeal ^ n}
  one_mem' := by
    simp
  mul_mem' := by
    intro x y hx hy
    have hxy :
        ((x * y : F.valuationSubringˣ) : F.valuationSubring) - 1 =
          (x : F.valuationSubring) * ((y : F.valuationSubring) - 1) +
            ((x : F.valuationSubring) - 1) := by
      simp
      ring
    change ((x * y : F.valuationSubringˣ) : F.valuationSubring) - 1 ∈ F.maximalIdeal ^ n
    rw [hxy]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hy) hx
  inv_mem' := by
    intro x hx
    have hxinv :
        ((x⁻¹ : F.valuationSubringˣ) : F.valuationSubring) - 1 =
            -(((x⁻¹ : F.valuationSubringˣ) : F.valuationSubring) *
              ((x : F.valuationSubring) - 1)) := by
      calc
        ((x⁻¹ : F.valuationSubringˣ) : F.valuationSubring) - 1 =
            ((x⁻¹ : F.valuationSubringˣ) : F.valuationSubring) -
              ((x⁻¹ : F.valuationSubringˣ) : F.valuationSubring) *
                (x : F.valuationSubring) := by
          simp
        _ = -(((x⁻¹ : F.valuationSubringˣ) : F.valuationSubring) *
              ((x : F.valuationSubring) - 1)) := by
          ring
    change ((x⁻¹ : F.valuationSubringˣ) : F.valuationSubring) - 1 ∈ F.maximalIdeal ^ n
    rw [hxinv]
    exact (F.maximalIdeal ^ n).neg_mem
      (Ideal.mul_mem_left (F.maximalIdeal ^ n)
        ((x⁻¹ : F.valuationSubringˣ) : F.valuationSubring) hx)

namespace higherPrincipalUnitGroup

variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)

/--
Characterizes `u ∈ higherPrincipalUnitGroup F n` by the equivalent condition `(u :
F.valuationSubring) - 1 ∈ F.maximalIdeal ^ n`.
-/
@[simp] theorem mem_iff (n : ℕ) (u : F.valuationSubringˣ) :
    u ∈ higherPrincipalUnitGroup F n ↔
      (u : F.valuationSubring) - 1 ∈ F.maximalIdeal ^ n :=
  Iff.rfl

/-- Higher levels are contained in lower levels. -/
theorem antitone {m n : ℕ} (h : m ≤ n) :
    higherPrincipalUnitGroup F n ≤ higherPrincipalUnitGroup F m := by
  intro u hu
  exact (Ideal.pow_le_pow_right h) hu

/-- Prime-binomial containment in an ideal.  If `p ∈ I` and `a ∈ I^n` with
`n ≥ 1`, then `(1 + a)^p - 1` is one level deeper. -/
theorem one_add_pow_prime_sub_one_mem_pow_succ
    {R : Type*} [CommRing R] (I : Ideal R)
    {p n : ℕ} (hp : Nat.Prime p) (hn : 1 ≤ n)
    (hp_mem : (p : R) ∈ I) {a : R} (ha : a ∈ I ^ n) :
    (1 + a) ^ p - 1 ∈ I ^ (n + 1) := by
  rcases exists_add_pow_prime_eq hp (1 : R) a with ⟨r, hr⟩
  have hnp : n + 1 ≤ n * p := by
    exact (Nat.add_le_add_left hn n).trans
      (by simpa [Nat.mul_two] using Nat.mul_le_mul_left n hp.two_le)
  have ha_pow_np : a ^ p ∈ I ^ (n * p) := by
    simpa [pow_mul] using (Ideal.pow_mem_pow ha p)
  have ha_pow_succ : a ^ p ∈ I ^ (n + 1) :=
    Ideal.pow_le_pow_right hnp ha_pow_np
  have ha_p_succ : a * (p : R) ∈ I ^ (n + 1) := by
    simpa [pow_succ] using (Ideal.mul_mem_mul ha hp_mem)
  have hp_a_succ : (p : R) * a ∈ I ^ (n + 1) := by
    simpa [mul_comm] using ha_p_succ
  have hp_a_r_succ : (p : R) * a * r ∈ I ^ (n + 1) :=
    (I ^ (n + 1)).mul_mem_right r hp_a_succ
  have hbinom : (1 + a) ^ p - 1 = a ^ p + (p : R) * a * r := by
    rw [hr]
    ring
  rw [hbinom]
  exact Ideal.add_mem _ ha_pow_succ hp_a_r_succ

/-- If the residue field has ring characteristic `p`, then `p` lies in the
maximal ideal of the valuation ring. -/
theorem natCast_mem_maximalIdeal_of_residue_ringChar_eq
    {p : ℕ} (hchar : ringChar F.residueField = p) :
    (p : F.valuationSubring) ∈ F.maximalIdeal := by
  have : CharP F.residueField p := (ringChar.eq_iff (R := F.residueField)).1 hchar
  rw [← F.residue_eq_zero_iff]
  rw [map_natCast]
  exact CharP.cast_eq_zero F.residueField p

/-- Concrete principal-unit form of the prime-binomial containment:
if `p ∈ m`, then the `p`th power carries `U^n` into `U^(n+1)` for `n ≥ 1`. -/
theorem pow_mem_succ_of_natCast_mem_maximalIdeal
    {p n : ℕ} (hp : Nat.Prime p) (hn : 1 ≤ n)
    (hp_mem : (p : F.valuationSubring) ∈ F.maximalIdeal)
    {u : F.valuationSubringˣ}
    (hu : u ∈ higherPrincipalUnitGroup F n) :
    u ^ p ∈ higherPrincipalUnitGroup F (n + 1) := by
  rw [higherPrincipalUnitGroup.mem_iff] at hu ⊢
  let a : F.valuationSubring := (u : F.valuationSubring) - 1
  have hu_eq : (u : F.valuationSubring) = 1 + a := by
    simp [a]
  have hpow :
      ((u ^ p : F.valuationSubringˣ) : F.valuationSubring) =
        (u : F.valuationSubring) ^ p := by
    simp
  rw [hpow, hu_eq]
  exact
    higherPrincipalUnitGroup.one_add_pow_prime_sub_one_mem_pow_succ
      F.maximalIdeal hp hn hp_mem hu

/-- Residue-characteristic form of `pow_mem_succ_of_natCast_mem_maximalIdeal`:
if the residue field has characteristic `p`, then `p`th powers move principal
units one step deeper. -/
theorem pow_mem_succ_of_residue_ringChar_eq
    {p n : ℕ} (hp : Nat.Prime p) (hn : 1 ≤ n)
    (hchar : ringChar F.residueField = p)
    {u : F.valuationSubringˣ}
    (hu : u ∈ higherPrincipalUnitGroup F n) :
    u ^ p ∈ higherPrincipalUnitGroup F (n + 1) :=
  higherPrincipalUnitGroup.pow_mem_succ_of_natCast_mem_maximalIdeal
    F hp hn
    (higherPrincipalUnitGroup.natCast_mem_maximalIdeal_of_residue_ringChar_eq
      F hchar)
    hu

/-- Establishes the identity `higherPrincipalUnitGroup F 0 = ⊤`. -/
@[simp] theorem zero_eq_top :
    higherPrincipalUnitGroup F 0 = ⊤ := by
  ext u
  simp [higherPrincipalUnitGroup]

/-- The residue of a valuation-ring unit, viewed as a unit of the residue
field. -/
def residueUnitHom :
    F.valuationSubringˣ →* F.residueFieldˣ :=
  Units.map F.residueMap.toMonoidHom

/--
The defining evaluation formula for `residueUnitHom` is `((higherPrincipalUnitGroup.residueUnitHom
F u : F.residueFieldˣ) : F.residueField) = F.residueMap (u : F.valuationSubring)`.
-/
@[simp] theorem residueUnitHom_apply (u : F.valuationSubringˣ) :
    ((higherPrincipalUnitGroup.residueUnitHom F u : F.residueFieldˣ) :
        F.residueField) =
      F.residueMap (u : F.valuationSubring) :=
  rfl

/-- The first concrete principal-unit level consists exactly of units whose
residue is `1`. -/
theorem mem_one_iff_residue_eq_one (u : F.valuationSubringˣ) :
    u ∈ higherPrincipalUnitGroup F 1 ↔
      F.residueMap (u : F.valuationSubring) = 1 := by
  rw [higherPrincipalUnitGroup.mem_iff, pow_one]
  constructor
  · intro hu
    have hres :
        F.residueMap (u : F.valuationSubring) = F.residueMap 1 := by
      exact
        (residue_eq_residue_iff_sub_mem_maximalIdeal
          (R := F.valuationSubring) (u : F.valuationSubring) 1).2 hu
    simpa using hres
  · intro hu
    exact
      (residue_eq_residue_iff_sub_mem_maximalIdeal
        (R := F.valuationSubring) (u : F.valuationSubring) 1).1
        (by simpa using hu)

/--
Characterizes `higherPrincipalUnitGroup.residueUnitHom F u = 1` by the equivalent condition `u ∈
higherPrincipalUnitGroup F 1`.
-/
theorem residueUnitHom_eq_one_iff (u : F.valuationSubringˣ) :
    higherPrincipalUnitGroup.residueUnitHom F u = 1 ↔
      u ∈ higherPrincipalUnitGroup F 1 := by
  constructor
  · intro hu
    apply (higherPrincipalUnitGroup.mem_one_iff_residue_eq_one F u).2
    have hval :=
      congrArg (fun z : F.residueFieldˣ => (z : F.residueField)) hu
    simpa using hval
  · intro hu
    apply Units.ext
    simpa using (higherPrincipalUnitGroup.mem_one_iff_residue_eq_one F u).1 hu

/--
Characterizes `higherPrincipalUnitGroup.residueUnitHom F u =
higherPrincipalUnitGroup.residueUnitHom F v` by the equivalent condition `F.residueMap (u :
F.valuationSubring) = F.residueMap (v : F.valuationSubring)`.
-/
theorem residueUnitHom_eq_iff_residue_eq
    (u v : F.valuationSubringˣ) :
    higherPrincipalUnitGroup.residueUnitHom F u =
        higherPrincipalUnitGroup.residueUnitHom F v ↔
      F.residueMap (u : F.valuationSubring) =
        F.residueMap (v : F.valuationSubring) := by
  constructor
  · intro h
    exact congrArg (fun z : F.residueFieldˣ => (z : F.residueField)) h
  · intro h
    apply Units.ext
    simpa using h
end higherPrincipalUnitGroup

end CompleteDVF
end DiscreteValuationField

end

end LocalFieldTheory
