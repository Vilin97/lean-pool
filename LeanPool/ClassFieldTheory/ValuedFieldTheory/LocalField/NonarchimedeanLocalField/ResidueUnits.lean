/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Category.ModuleCat.Basic
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.AdditiveEquiv
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits
/-!
# Residue units

Constructs the quotient of valuation-ring units by first principal units and
identifies it, multiplicatively and additively, with the residue-field units.
-/
namespace LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- The residue-field unit group attached to a valued field. -/
def ResidueUnits (K : Type u) [Field K] [ValuativeRel K] : Type u :=
  𝓀[K]ˣ

/-- The unit group of the residue field is a commutative group. -/
instance residueUnitsCommGroup
    (K : Type u) [Field K] [ValuativeRel K] :
    CommGroup (ResidueUnits K) := by
  change CommGroup 𝓀[K]ˣ
  infer_instance

/-- Explicit comparison with the concrete unit group of the residue field. -/
def residueUnitsConcreteEquiv
    (K : Type u) [Field K] [ValuativeRel K] :
    ResidueUnits K ≃* 𝓀[K]ˣ := by
  change 𝓀[K]ˣ ≃* 𝓀[K]ˣ
  exact MulEquiv.refl _

/-- The concrete residue-unit comparison preserves the underlying residue
unit. -/
@[simp]
theorem residueUnitsConcreteEquiv_apply
    (K : Type u) [Field K] [ValuativeRel K] (u : ResidueUnits K) :
    residueUnitsConcreteEquiv K u = u :=
  rfl

/-- The unit group of the finite residue field is finite. -/
noncomputable instance residueUnitsFinite
    (K : Type u) [Field K] [ValuativeRel K] [Finite 𝓀[K]] :
    Finite (ResidueUnits K) := by
  exact Finite.of_equiv 𝓀[K]ˣ (residueUnitsConcreteEquiv K).symm.toEquiv

/-- Integer units modulo first principal units. -/
@[implicit_reducible]
def IntegerUnitsModPrincipalUnits
    (K : Type u) [Field K] [ValuativeRel K] : Type u :=
  𝒪[K]ˣ ⧸ principalUnits K 1

/-- Valuation-ring units modulo first principal units form a commutative quotient group. -/
@[implicit_reducible]
instance integerUnitsModPrincipalUnitsCommGroup
    (K : Type u) [Field K] [ValuativeRel K] :
    CommGroup (IntegerUnitsModPrincipalUnits K) := by
  change CommGroup (𝒪[K]ˣ ⧸ principalUnits K 1)
  infer_instance

/-- Explicit access to the concrete quotient model. -/
def integerUnitsModPrincipalUnitsConcreteEquiv
    (K : Type u) [Field K] [ValuativeRel K] :
    IntegerUnitsModPrincipalUnits K ≃*
      (𝒪[K]ˣ ⧸ principalUnits K 1) := by
  change (𝒪[K]ˣ ⧸ principalUnits K 1) ≃*
    (𝒪[K]ˣ ⧸ principalUnits K 1)
  exact MulEquiv.refl _

/-- The canonical class of an integer unit modulo first principal units. -/
@[implicit_reducible]
def integerUnitsModPrincipalUnitsMk
    (K : Type u) [Field K] [ValuativeRel K] :
    𝒪[K]ˣ →* IntegerUnitsModPrincipalUnits K := by
  change 𝒪[K]ˣ →* (𝒪[K]ˣ ⧸ principalUnits K 1)
  exact QuotientGroup.mk' (principalUnits K 1)

/-- The concrete quotient equivalence sends a valuation-ring unit to its class modulo first
principal units. -/
@[simp]
theorem integerUnitsModPrincipalUnitsConcreteEquiv_mk
    (K : Type u) [Field K] [ValuativeRel K] (x : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsConcreteEquiv K
        (integerUnitsModPrincipalUnitsMk K x) =
      QuotientGroup.mk x :=
  rfl

/-- Every class modulo first principal units has a valuation-ring unit representative. -/
theorem integerUnitsModPrincipalUnitsMk_surjective
    (K : Type u) [Field K] [ValuativeRel K] :
    Function.Surjective (integerUnitsModPrincipalUnitsMk K) :=
  QuotientGroup.mk'_surjective (principalUnits K 1)

/-- Eliminate a quotient class through the canonical class map. -/
protected theorem IntegerUnitsModPrincipalUnits.inductionOn
    {K : Type u} [Field K] [ValuativeRel K]
    {motive : IntegerUnitsModPrincipalUnits K → Prop}
    (q : IntegerUnitsModPrincipalUnits K)
    (h : ∀ x : 𝒪[K]ˣ, motive (integerUnitsModPrincipalUnitsMk K x)) :
    motive q := by
  change motive (show 𝒪[K]ˣ ⧸ principalUnits K 1 from q)
  refine QuotientGroup.induction_on q ?_
  intro x
  exact h x

/-- Descend a homomorphism that kills the first principal-unit group. -/
def integerUnitsModPrincipalUnitsLift
    {K : Type u} {M : Type*} [Field K] [ValuativeRel K] [Group M]
    (f : 𝒪[K]ˣ →* M) (h : principalUnits K 1 ≤ f.ker) :
    IntegerUnitsModPrincipalUnits K →* M := by
  change (𝒪[K]ˣ ⧸ principalUnits K 1) →* M
  exact QuotientGroup.lift (principalUnits K 1) f h

/-- A map lifted from units modulo first principal units agrees with the original map on
representatives. -/
@[simp]
theorem integerUnitsModPrincipalUnitsLift_mk
    {K : Type u} {M : Type*} [Field K] [ValuativeRel K] [Group M]
    (f : 𝒪[K]ˣ →* M) (h : principalUnits K 1 ≤ f.ker) (x : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsLift f h
        (integerUnitsModPrincipalUnitsMk K x) = f x :=
  rfl

/-- Reduction of valuation-integer units to residue-field units. -/
def integerUnitsToResidueUnits (K : Type u) [Field K] [ValuativeRel K] :
    𝒪[K]ˣ →* ResidueUnits K :=
  Units.map (IsLocalRing.residue 𝒪[K]).toMonoidHom

/-- Reduction of a valuation-ring unit has underlying residue equal to reduction of its underlying
integer. -/
theorem integerUnitsToResidueUnits_apply (K : Type u) [Field K] [ValuativeRel K]
    (x : 𝒪[K]ˣ) :
    ((residueUnitsConcreteEquiv K (integerUnitsToResidueUnits K x) : 𝓀[K]ˣ) :
        𝓀[K]) =
      IsLocalRing.residue 𝒪[K] (x : 𝒪[K]) :=
  rfl

/-- Kernel criterion for reduction on valuation-integer units. -/
theorem mem_ker_integerUnitsToResidueUnits_iff (K : Type u) [Field K] [ValuativeRel K]
    (x : 𝒪[K]ˣ) :
    x ∈ (integerUnitsToResidueUnits K).ker ↔
      IsLocalRing.residue 𝒪[K] (x : 𝒪[K]) = 1 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have h' := congrArg (residueUnitsConcreteEquiv K) h
    have h'' := congrArg Units.val h'
    simpa only [integerUnitsToResidueUnits_apply, map_one, Units.val_one] using h''
  · intro h
    apply (residueUnitsConcreteEquiv K).injective
    apply Units.ext
    simpa only [integerUnitsToResidueUnits_apply, map_one, Units.val_one] using h

/-- The first principal-unit group is the kernel of reduction to residue-field units. -/
theorem principalUnits_one_eq_ker_integerUnitsToResidueUnits
    (K : Type u) [Field K] [ValuativeRel K] :
    principalUnits K 1 = (integerUnitsToResidueUnits K).ker := by
  ext x
  rw [mem_principalUnits_iff, mem_ker_integerUnitsToResidueUnits_iff]
  rw [pow_one]
  rw [← sub_eq_zero]
  rw [← map_one (IsLocalRing.residue 𝒪[K]), ← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.symm

/-- A valuation-ring unit reduces to one exactly when it is a first principal unit. -/
theorem integerUnitsToResidueUnits_eq_one_iff_mem_principalUnits_one
    (K : Type u) [Field K] [ValuativeRel K] (x : 𝒪[K]ˣ) :
    integerUnitsToResidueUnits K x = 1 ↔ x ∈ principalUnits K 1 := by
  rw [principalUnits_one_eq_ker_integerUnitsToResidueUnits K, MonoidHom.mem_ker]

/-- Two valuation-ring units have the same residue exactly when their quotient is a first principal
unit. -/
theorem integerUnitsToResidueUnits_eq_iff_div_mem_principalUnits_one
    (K : Type u) [Field K] [ValuativeRel K] (x y : 𝒪[K]ˣ) :
    integerUnitsToResidueUnits K x = integerUnitsToResidueUnits K y ↔
      x / y ∈ principalUnits K 1 := by
  constructor
  · intro h
    rw [← integerUnitsToResidueUnits_eq_one_iff_mem_principalUnits_one K]
    simp only [div_eq_mul_inv, (integerUnitsToResidueUnits K).map_mul,
      (integerUnitsToResidueUnits K).map_inv, h, mul_inv_cancel]
  · intro h
    have h1 : integerUnitsToResidueUnits K (x / y) = 1 :=
      (integerUnitsToResidueUnits_eq_one_iff_mem_principalUnits_one K (x / y)).2 h
    have hdiv : integerUnitsToResidueUnits K x / integerUnitsToResidueUnits K y = 1 := by
      simpa only [div_eq_mul_inv, (integerUnitsToResidueUnits K).map_mul,
        (integerUnitsToResidueUnits K).map_inv] using h1
    exact div_eq_one.mp hdiv

/-- Higher principal units reduce to `1` in the residue-field unit group. -/
theorem principalUnits_le_ker_reduction
    (K : Type u) [Field K] [ValuativeRel K] {n : Nat} (hn : 1 ≤ n) :
    principalUnits K n ≤ (integerUnitsToResidueUnits K).ker := by
  rw [← principalUnits_one_eq_ker_integerUnitsToResidueUnits K]
  exact principalUnits_antitone K hn

/-- Every residue-field unit lifts to a valuation-ring unit. -/
theorem integerUnitsToResidueUnits_surjective (K : Type u) [Field K] [ValuativeRel K] :
    Function.Surjective (integerUnitsToResidueUnits K) :=
  IsLocalRing.surjective_units_map_of_local_ringHom _ Ideal.Quotient.mk_surjective
    (inferInstanceAs (IsLocalHom (IsLocalRing.residue 𝒪[K])))

/-- Reduction induces `𝒪[K]ˣ / U¹ ≃ 𝓀[K]ˣ`. -/
def integerUnitsModPrincipalUnitsEquivResidueUnits
    (K : Type u) [Field K] [ValuativeRel K] :
    IntegerUnitsModPrincipalUnits K ≃* ResidueUnits K :=
  (integerUnitsModPrincipalUnitsConcreteEquiv K).trans
    ((QuotientGroup.quotientMulEquivOfEq
      (principalUnits_one_eq_ker_integerUnitsToResidueUnits K)).trans
      (QuotientGroup.quotientKerEquivOfSurjective (integerUnitsToResidueUnits K)
        (integerUnitsToResidueUnits_surjective K)))

/-- The quotient-to-residue-unit equivalence sends a unit class to the reduction of its
representative. -/
@[simp]
theorem integerUnitsModPrincipalUnitsEquivResidueUnits_mk
    (K : Type u) [Field K] [ValuativeRel K] (x : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsEquivResidueUnits K
        (integerUnitsModPrincipalUnitsMk K x) =
      integerUnitsToResidueUnits K x := by
  simp only [integerUnitsModPrincipalUnitsEquivResidueUnits, MulEquiv.trans_apply,
    integerUnitsModPrincipalUnitsConcreteEquiv_mk,
    QuotientGroup.quotientMulEquivOfEq_mk]
  rw [QuotientGroup.quotientKerEquivOfSurjective,
    QuotientGroup.quotientKerEquivOfRightInverse_apply,
    QuotientGroup.kerLift_mk]

/-- The residue-unit quotient equivalence sends a class to `1` exactly for first
principal units. -/
theorem integerUnitsModPrincipalUnitsEquivResidueUnits_mk_eq_one_iff
    (K : Type u) [Field K] [ValuativeRel K] (x : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsEquivResidueUnits K
        (integerUnitsModPrincipalUnitsMk K x) = 1 ↔
      x ∈ principalUnits K 1 := by
  rw [integerUnitsModPrincipalUnitsEquivResidueUnits_mk]
  exact integerUnitsToResidueUnits_eq_one_iff_mem_principalUnits_one K x

/-- Equality of residue classes is the same as quotient by a first principal unit. -/
theorem integerUnitsModPrincipalUnitsEquivResidueUnits_mk_eq_mk_iff
    (K : Type u) [Field K] [ValuativeRel K] (x y : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsEquivResidueUnits K
        (integerUnitsModPrincipalUnitsMk K x) =
      integerUnitsModPrincipalUnitsEquivResidueUnits K
        (integerUnitsModPrincipalUnitsMk K y) ↔
      x / y ∈ principalUnits K 1 := by
  rw [integerUnitsModPrincipalUnitsEquivResidueUnits_mk,
    integerUnitsModPrincipalUnitsEquivResidueUnits_mk]
  exact integerUnitsToResidueUnits_eq_iff_div_mem_principalUnits_one K x y

/-- Additive form of `𝒪[K]ˣ / U¹ ≃ 𝓀[K]ˣ`. -/
def integerUnitsModPrincipalUnitsAddEquivResidueUnits
    (K : Type u) [Field K] [ValuativeRel K] :
    Additive (IntegerUnitsModPrincipalUnits K) ≃+ Additive (ResidueUnits K) :=
  additiveEquivOfMulEquiv (integerUnitsModPrincipalUnitsEquivResidueUnits K)

/-- Equality in `𝒪[K]ˣ / U¹`, expressed by a first-principal-unit quotient. -/
theorem IntegerUnitsModPrincipalUnits_mk_eq_mk_iff
    (K : Type u) [Field K] [ValuativeRel K] (x y : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsMk K x =
        integerUnitsModPrincipalUnitsMk K y ↔
      x / y ∈ principalUnits K 1 :=
  by
    change (QuotientGroup.mk x : 𝒪[K]ˣ ⧸ principalUnits K 1) =
      QuotientGroup.mk y ↔ _
    exact QuotientGroup.eq_iff_div_mem (N := principalUnits K 1)

/-- Triviality criterion in `𝒪[K]ˣ / U¹`. -/
theorem IntegerUnitsModPrincipalUnits_mk_eq_one_iff
    (K : Type u) [Field K] [ValuativeRel K] (x : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsMk K x = 1 ↔
      x ∈ principalUnits K 1 :=
  by
    change (QuotientGroup.mk x : 𝒪[K]ˣ ⧸ principalUnits K 1) = 1 ↔ _
    exact QuotientGroup.eq_one_iff (N := principalUnits K 1) x

/-- Equality in `𝒪[K]ˣ / U¹` is exactly equality after reduction to residue
units. -/
theorem IntegerUnitsModPrincipalUnits_mk_eq_mk_iff_residue
    (K : Type u) [Field K] [ValuativeRel K] (x y : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsMk K x =
        integerUnitsModPrincipalUnitsMk K y ↔
      integerUnitsToResidueUnits K x = integerUnitsToResidueUnits K y := by
  constructor
  · intro h
    exact (integerUnitsToResidueUnits_eq_iff_div_mem_principalUnits_one K x y).2
      ((IntegerUnitsModPrincipalUnits_mk_eq_mk_iff K x y).1 h)
  · intro h
    exact (IntegerUnitsModPrincipalUnits_mk_eq_mk_iff K x y).2
      ((integerUnitsToResidueUnits_eq_iff_div_mem_principalUnits_one K x y).1 h)

/-- The class of an integer unit in `𝒪[K]ˣ / U¹` is trivial exactly when its
residue is `1`. -/
theorem IntegerUnitsModPrincipalUnits_mk_eq_one_iff_residue_eq_one
    (K : Type u) [Field K] [ValuativeRel K] (x : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsMk K x = 1 ↔
      integerUnitsToResidueUnits K x = 1 := by
  constructor
  · intro h
    exact (integerUnitsToResidueUnits_eq_one_iff_mem_principalUnits_one K x).2
      ((IntegerUnitsModPrincipalUnits_mk_eq_one_iff K x).1 h)
  · intro h
    exact (IntegerUnitsModPrincipalUnits_mk_eq_one_iff K x).2
      ((integerUnitsToResidueUnits_eq_one_iff_mem_principalUnits_one K x).1 h)

/-- Additive version of the residue-unit quotient equivalence on quotient representatives. -/
@[simp]
theorem integerUnitsModPrincipalUnitsAddEquivResidueUnits_mk
    (K : Type u) [Field K] [ValuativeRel K] (x : 𝒪[K]ˣ) :
    integerUnitsModPrincipalUnitsAddEquivResidueUnits K
        (Additive.ofMul (integerUnitsModPrincipalUnitsMk K x)) =
      Additive.ofMul (integerUnitsToResidueUnits K x) := by
  exact congrArg Additive.ofMul
    (integerUnitsModPrincipalUnitsEquivResidueUnits_mk K x)

/-- Module form of the residue-unit quotient equivalence. -/
def integerUnitsModPrincipalUnitsIsoResidueUnits
    (K : Type u) [Field K] [ValuativeRel K] :
    CategoryTheory.Iso (ModuleCat.of ℤ (Additive (IntegerUnitsModPrincipalUnits K)))
      (ModuleCat.of ℤ (Additive (ResidueUnits K))) :=
  (integerUnitsModPrincipalUnitsAddEquivResidueUnits K).toIntLinearEquiv.toModuleIso

/-- Cardinality statement transported from the quotient equivalence with residue units. -/
theorem integerUnitsModPrincipalUnits_card_eq_residueUnits_card
    (K : Type u) [Field K] [ValuativeRel K]
    [Finite (IntegerUnitsModPrincipalUnits K)]
    [Finite (ResidueUnits K)] :
    Nat.card (IntegerUnitsModPrincipalUnits K) = Nat.card (ResidueUnits K) :=
  Nat.card_congr (integerUnitsModPrincipalUnitsEquivResidueUnits K).toEquiv

end
end LocalFieldTheory
