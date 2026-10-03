/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.SetTheory.Cardinal.Finite
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields
public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.FieldTheory.Galois.Profinite

/-! # Finite Residue Frobenius -/

@[expose] public section
namespace LocalClassFieldTheory

open ClassFormation

/-!
# Finite local reciprocity: finite residue Frobenius coordinates

The degree map used in local reciprocity comes from the arithmetic Frobenius
on the algebraic closure of the finite residue field.  This file constructs
the finite-level source of that map: for every finite extension of a finite
field, exponentiation of Frobenius identifies its Galois group with the
appropriate cyclic quotient of `ℤ̂`.

No cyclic generator is chosen.  The generator is the actual arithmetic
Frobenius `x ↦ x ^ #k`, and the exponent map is obtained by factoring its
integer powers through `ZMod [L : k]`.
-/

noncomputable
section

universe u v w

variable (k : Type u) (L : Type v)
  [Field k] [Fintype k] [Field L] [Finite L] [Algebra k L]

/-- Integer powers of the arithmetic Frobenius, written additively. -/
def finiteResidueFrobeniusIntegerPowers :
    ℤ →+ Additive (L ≃ₐ[k] L) :=
  zmultiplesHom (Additive (L ≃ₐ[k] L)) (Additive.ofMul
    (FiniteField.frobeniusAlgEquivOfAlgebraic k L))

/-- The order relation which lets integer Frobenius powers factor through
`ZMod [L : k]`. -/
private theorem finiteResidueFrobeniusIntegerPowers_degree_eq_zero :
    finiteResidueFrobeniusIntegerPowers k L (Module.finrank k L) = 0 := by
  apply Additive.ext
  change (FiniteField.frobeniusAlgEquivOfAlgebraic k L) ^
      (Module.finrank k L : ℤ) = 1
  rw [← FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (K := k) (L := L)]
  rw [zpow_natCast, pow_orderOf_eq_one]

/-- The canonical finite-level exponent homomorphism
`Z/[L:k]Z → Gal(L/k)`, sending `1` to arithmetic Frobenius. -/
def finiteResidueFrobeniusExponentHom :
    Multiplicative (ZMod (Module.finrank k L)) →* (L ≃ₐ[k] L) :=
  AddMonoidHom.toMultiplicative
    (ZMod.lift (Module.finrank k L)
      ⟨finiteResidueFrobeniusIntegerPowers k L,
        by exact finiteResidueFrobeniusIntegerPowers_degree_eq_zero k L⟩)

/-- An integer residue exponent maps to the corresponding power of Frobenius. -/
@[simp]
theorem finiteResidueFrobeniusExponentHom_intCast (m : ℤ) :
    finiteResidueFrobeniusExponentHom k L
        (Multiplicative.ofAdd (m : ZMod (Module.finrank k L))) =
      (FiniteField.frobeniusAlgEquivOfAlgebraic k L) ^ m := by
  change
    (ZMod.lift (Module.finrank k L)
      ⟨finiteResidueFrobeniusIntegerPowers k L,
        by exact finiteResidueFrobeniusIntegerPowers_degree_eq_zero k L⟩)
      (m : ZMod (Module.finrank k L)) =
        Additive.ofMul ((FiniteField.frobeniusAlgEquivOfAlgebraic k L) ^ m)
  rw [ZMod.lift_coe]
  rfl

/-- Residue exponent one maps to the arithmetic Frobenius automorphism. -/
@[simp]
theorem finiteResidueFrobeniusExponentHom_one :
    finiteResidueFrobeniusExponentHom k L
        (Multiplicative.ofAdd (1 : ZMod (Module.finrank k L))) =
      FiniteField.frobeniusAlgEquivOfAlgebraic k L := by
  simpa using finiteResidueFrobeniusExponentHom_intCast k L 1

/-- Every finite residue-field automorphism is a power of arithmetic
Frobenius, so the canonical exponent homomorphism is onto. -/
theorem finiteResidueFrobeniusExponentHom_surjective :
    Function.Surjective (finiteResidueFrobeniusExponentHom k L) := by
  intro sigma
  obtain ⟨m, hm⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k L).2 sigma
  refine ⟨Multiplicative.ofAdd
    ((m.1 : ℤ) : ZMod (Module.finrank k L)), ?_⟩
  rw [finiteResidueFrobeniusExponentHom_intCast]
  simpa [zpow_natCast] using hm

/-- The finite-level Frobenius exponent homomorphism is injective. -/
theorem finiteResidueFrobeniusExponentHom_injective :
    Function.Injective (finiteResidueFrobeniusExponentHom k L) := by
  let : NeZero (Module.finrank k L) := ⟨Module.finrank_pos.ne'⟩
  have hcard :
      Nat.card (Multiplicative (ZMod (Module.finrank k L))) =
        Nat.card (L ≃ₐ[k] L) := by
    rw [Nat.card_congr Multiplicative.toAdd,
      Nat.card_zmod, IsGalois.card_aut_eq_finrank]
  exact ((finiteResidueFrobeniusExponentHom_surjective k L).bijective_of_nat_card_le
    hcard.le).1

/-- Canonical finite-level Frobenius coordinates. -/
def finiteResidueFrobeniusExponentEquiv :
    Multiplicative (ZMod (Module.finrank k L)) ≃* (L ≃ₐ[k] L) :=
  MulEquiv.ofBijective (finiteResidueFrobeniusExponentHom k L)
    ⟨finiteResidueFrobeniusExponentHom_injective k L,
      finiteResidueFrobeniusExponentHom_surjective k L⟩

/-- The Frobenius exponent equivalence has the same underlying map as the exponent homomorphism. -/
@[simp]
theorem finiteResidueFrobeniusExponentEquiv_apply (z) :
    finiteResidueFrobeniusExponentEquiv k L z =
      finiteResidueFrobeniusExponentHom k L z :=
  rfl

/-- The Frobenius exponent equivalence sends one to arithmetic Frobenius. -/
theorem finiteResidueFrobeniusExponentEquiv_one :
    finiteResidueFrobeniusExponentEquiv k L
        (Multiplicative.ofAdd (1 : ZMod (Module.finrank k L))) =
      FiniteField.frobeniusAlgEquivOfAlgebraic k L :=
  finiteResidueFrobeniusExponentHom_one k L

/-- A profinite exponent acts on a finite residue extension through reduction
modulo its degree. -/
def finiteResidueFrobeniusFromZHat :
    ZHatMul →ₜ* (L ≃ₐ[k] L) where
  toFun z := finiteResidueFrobeniusExponentHom k L
    (Multiplicative.ofAdd
      (zHatReduction (Module.finrank k L) Module.finrank_pos z.toAdd))
  map_one' := by
    apply (finiteResidueFrobeniusExponentHom k L).map_one
  map_mul' x y := by
    apply (finiteResidueFrobeniusExponentHom k L).map_mul
  continuous_toFun := by
    apply continuous_of_discreteTopology.comp
    exact continuous_ofAdd.comp
      ((zHatReduction (Module.finrank k L) Module.finrank_pos).continuous_toFun.comp
        continuous_toAdd)

/-- The profinite Frobenius map depends on reduction modulo the residue extension degree. -/
@[simp]
theorem finiteResidueFrobeniusFromZHat_apply (z : ZHatMul) :
    finiteResidueFrobeniusFromZHat k L z =
      finiteResidueFrobeniusExponentHom k L
        (Multiplicative.ofAdd
          (zHatReduction (Module.finrank k L) Module.finrank_pos z.toAdd)) :=
  rfl

/-- The distinguished profinite integer `1` acts as arithmetic Frobenius. -/
theorem finiteResidueFrobeniusFromZHat_one :
    finiteResidueFrobeniusFromZHat k L
        (Multiplicative.ofAdd (1 : ZHat)) =
      FiniteField.frobeniusAlgEquivOfAlgebraic k L := by
  rw [finiteResidueFrobeniusFromZHat_apply]
  exact finiteResidueFrobeniusExponentHom_one k L

/-- Every automorphism of a finite residue extension is induced by a
profinite Frobenius exponent. -/
theorem finiteResidueFrobeniusFromZHat_surjective :
    Function.Surjective (finiteResidueFrobeniusFromZHat k L) := by
  intro sigma
  obtain ⟨a, ha⟩ := finiteResidueFrobeniusExponentHom_surjective k L sigma
  obtain ⟨z, hz⟩ := zHatReduction_surjective
    (Module.finrank k L) Module.finrank_pos a.toAdd
  refine ⟨Multiplicative.ofAdd z, ?_⟩
  rw [finiteResidueFrobeniusFromZHat_apply]
  change finiteResidueFrobeniusExponentHom k L
      (Multiplicative.ofAdd
        (zHatReduction (Module.finrank k L) Module.finrank_pos z)) = sigma
  rw [hz]
  exact ha

/-- A profinite exponent acts trivially on a finite residue extension exactly
when it is zero modulo the extension degree. -/
theorem finiteResidueFrobeniusFromZHat_eq_one_iff (z : ZHatMul) :
    finiteResidueFrobeniusFromZHat k L z = 1 ↔
      zHatReduction (Module.finrank k L) Module.finrank_pos z.toAdd = 0 := by
  rw [finiteResidueFrobeniusFromZHat_apply]
  constructor
  · intro h
    have h' :
        Multiplicative.ofAdd
            (zHatReduction (Module.finrank k L) Module.finrank_pos z.toAdd) =
          1 := by
      apply finiteResidueFrobeniusExponentHom_injective k L
      simpa using h
    exact congrArg Multiplicative.toAdd h'
  · intro h
    rw [h]
    exact (finiteResidueFrobeniusExponentHom k L).map_one

section Tower

variable {E : Type v} {F : Type w}
  [Field E] [Finite E] [Field F] [Finite F]
  [Algebra k E] [Algebra k F] [Algebra E F]
  [IsScalarTower k E F] [Normal k E]

/-- Arithmetic Frobenius commutes with restriction in a tower of finite
extensions of a finite field. -/
theorem restrictNormalHom_finiteResidueFrobenius :
    AlgEquiv.restrictNormalHom E
        (FiniteField.frobeniusAlgEquivOfAlgebraic k F) =
      FiniteField.frobeniusAlgEquivOfAlgebraic k E := by
  apply AlgEquiv.ext
  intro x
  apply (algebraMap E F).injective
  calc
    (algebraMap E F)
        (((AlgEquiv.restrictNormalHom E)
          (FiniteField.frobeniusAlgEquivOfAlgebraic k F)) x) =
        FiniteField.frobeniusAlgEquivOfAlgebraic k F
          (algebraMap E F x) :=
      AlgEquiv.restrictNormal_commutes
        (FiniteField.frobeniusAlgEquivOfAlgebraic k F) E x
    _ = (algebraMap E F
        ((FiniteField.frobeniusAlgEquivOfAlgebraic k E) x) : F) := by
      simp only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
      exact (map_pow (algebraMap E F) x (Fintype.card k)).symm

/-- The finite Frobenius exponent coordinates commute with restriction.  The
exponent on the smaller field is obtained by the canonical reduction
`Z/[F:k]Z → Z/[E:k]Z`. -/
theorem restrictNormalHom_finiteResidueFrobeniusExponentHom
    (z : Multiplicative (ZMod (Module.finrank k F))) :
    AlgEquiv.restrictNormalHom E
        (finiteResidueFrobeniusExponentHom k F z) =
      finiteResidueFrobeniusExponentHom k E
        (Multiplicative.ofAdd
          (ZMod.castHom
            (show Module.finrank k E ∣ Module.finrank k F from
              ⟨Module.finrank E F,
                (Module.finrank_mul_finrank k E F).symm⟩)
            (ZMod (Module.finrank k E)) z.toAdd)) := by
  rcases ZMod.intCast_surjective z.toAdd with ⟨m, hm⟩
  have hz : z = Multiplicative.ofAdd
      (m : ZMod (Module.finrank k F)) := by
    apply Multiplicative.ext
    exact hm.symm
  subst z
  apply AlgEquiv.ext
  intro x
  rw [finiteResidueFrobeniusExponentHom_intCast]
  simp only [toAdd_ofAdd]
  have hred :
      ZMod.castHom
          (show Module.finrank k E ∣ Module.finrank k F from
            ⟨Module.finrank E F,
              (Module.finrank_mul_finrank k E F).symm⟩)
          (ZMod (Module.finrank k E))
          (m : ZMod (Module.finrank k F)) =
        (m : ZMod (Module.finrank k E)) := by
    exact map_intCast _ m
  rw [hred, finiteResidueFrobeniusExponentHom_intCast]
  have hfrob := restrictNormalHom_finiteResidueFrobenius
    (k := k) (E := E) (F := F)
  have hpow := congrArg (fun sigma : E ≃ₐ[k] E => sigma ^ m) hfrob
  rw [map_zpow]
  exact DFunLike.congr_fun hpow x

/-- The actions of `ℤ̂` on finite residue extensions commute with restriction
in finite towers. -/
theorem restrictNormalHom_finiteResidueFrobeniusFromZHat (z : ZHatMul) :
    AlgEquiv.restrictNormalHom E
        (finiteResidueFrobeniusFromZHat k F z) =
      finiteResidueFrobeniusFromZHat k E z := by
  rw [finiteResidueFrobeniusFromZHat_apply,
    restrictNormalHom_finiteResidueFrobeniusExponentHom,
    finiteResidueFrobeniusFromZHat_apply]
  congr 2
  apply Multiplicative.ext
  exact zHatReduction_transition
    (m := Module.finrank k E) (n := Module.finrank k F)
    Module.finrank_pos Module.finrank_pos
    (show Module.finrank k E ∣ Module.finrank k F from
      ⟨Module.finrank E F,
        (Module.finrank_mul_finrank k E F).symm⟩)
    z.toAdd

end Tower

end
end LocalClassFieldTheory
