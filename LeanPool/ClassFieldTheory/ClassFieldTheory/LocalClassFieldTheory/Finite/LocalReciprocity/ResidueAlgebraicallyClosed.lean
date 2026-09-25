/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAlgebraicClosureDegree
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Valuation.Integral
public import Mathlib.RingTheory.Valuation.ValuationSubring

/-! # Residue Algebraically Closed -/

@[expose] public section
namespace LocalClassFieldTheory

/-!
# Residues of algebraically closed valued fields

The residue field of a valuation ring in an algebraically closed field is
algebraically closed.  This is the missing source needed to apply the
intrinsic finite-field degree map to the residue of an algebraic closure of a
local field.
-/

noncomputable section

universe u

variable {Omega : Type u} [Field Omega] [IsAlgClosed Omega]

/-- The residue field of a valuation subring of an algebraically closed field
is algebraically closed.  A monic irreducible residue polynomial is lifted
monically to the valuation ring.  A root in the ambient algebraically closed
field is integral, hence lies back in the valuation ring and can be reduced. -/
theorem valuationSubring_residueField_isAlgClosed
    (A : ValuationSubring Omega) :
    IsAlgClosed (IsLocalRing.ResidueField A) := by
  apply IsAlgClosed.of_exists_root
  intro p hpmonic hpirreducible
  have hlifts : p ∈ Polynomial.lifts (IsLocalRing.residue A) := by
    rw [Polynomial.mem_lifts]
    exact (Polynomial.map_surjective
      (IsLocalRing.residue A) IsLocalRing.residue_surjective) p
  obtain ⟨q, hqmap, hqdegree, hqmonic⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic hlifts hpmonic
  have hqmapSubtypeDegree :
      (q.map A.subtype).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective A.subtype_injective q]
    rw [hqdegree]
    exact ne_of_gt (Polynomial.degree_pos_of_irreducible hpirreducible)
  obtain ⟨x, hxroot⟩ :=
    IsAlgClosed.exists_root (q.map A.subtype) hqmapSubtypeDegree
  have hxIntegral : IsIntegral A x := by
    refine ⟨q, hqmonic, ?_⟩
    change Polynomial.eval₂ A.subtype x q = 0
    simpa [Polynomial.eval_map] using hxroot
  have hxA : x ∈ A := by
    let hAIntegers : A.valuation.Integers A :=
      { hom_inj := A.subtype_injective
        map_le_one := fun a =>
          (A.valuation_le_one_iff (a : Omega)).mpr a.property
        exists_of_le_one := fun {r} hr =>
          ⟨⟨r, (A.valuation_le_one_iff r).mp hr⟩, rfl⟩ }
    have hxValuation : A.valuation x ≤ 1 :=
      (hAIntegers.isIntegral_iff_v_le_one).mp hxIntegral
    exact (A.valuation_le_one_iff x).mp hxValuation
  let xA : A := ⟨x, hxA⟩
  have hxrootEval₂ : Polynomial.eval₂ A.subtype x q = 0 := by
    rw [← Polynomial.eval_map]
    exact hxroot
  have hxrootA : q.eval xA = 0 := by
    apply A.subtype_injective
    rw [← Polynomial.eval₂_at_apply A.subtype xA]
    simpa [xA] using hxrootEval₂
  refine ⟨IsLocalRing.residue A xA, ?_⟩
  rw [← hqmap]
  simp [Polynomial.eval_map, hxrootA]

/-! ## Residues under a purely inseparable ambient extension -/

section PurelyInseparableComap

variable {F Omega : Type u} [Field F] [Field Omega] [Algebra F Omega]

/-- The inclusion from the pullback of a valuation ring to the ambient
valuation ring. -/
def valuationSubringComapMap (A : ValuationSubring Omega) :
    A.comap (algebraMap F Omega) →+* A where
  toFun x := ⟨algebraMap F Omega x, x.property⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

/-- Pullback along a field embedding gives a local map of valuation rings. -/
theorem valuationSubringComapMap_isLocalHom (A : ValuationSubring Omega) :
    IsLocalHom (valuationSubringComapMap (F := F) A) := by
  constructor
  intro x hx
  obtain ⟨u, hu⟩ := hx
  have hx0 : (x : F) ≠ 0 := by
    intro hzero
    have hmapZero : valuationSubringComapMap (F := F) A x = 0 := by
      apply Subtype.ext
      simp [valuationSubringComapMap, hzero]
    exact Units.ne_zero u (hu.trans hmapZero)
  let xinv : A.comap (algebraMap F Omega) :=
    ⟨(x : F)⁻¹, by
      change algebraMap F Omega ((x : F)⁻¹) ∈ A
      rw [map_inv₀]
      have hu' : algebraMap F Omega (x : F) = ((u : A) : Omega) := by
        have h := congrArg Subtype.val hu
        exact h.symm
      rw [hu']
      have hinv : (((u : A) : Omega))⁻¹ = (((u⁻¹ : Aˣ) : A) : Omega) := by
        have hprod :
            ((u : A) : Omega) * (((u⁻¹ : Aˣ) : A) : Omega) = 1 := by
          have hprodA : (u : A) * ((u⁻¹ : Aˣ) : A) = 1 := u.val_inv
          exact congrArg A.subtype hprodA
        exact (eq_inv_of_mul_eq_one_right hprod).symm
      rw [hinv]
      exact (u⁻¹ : Aˣ).val.property⟩
  let xu : (A.comap (algebraMap F Omega))ˣ :=
    { val := x
      inv := xinv
      val_inv := by apply Subtype.ext; simp [xinv, hx0]
      inv_val := by apply Subtype.ext; simp [xinv, hx0] }
  exact ⟨xu, rfl⟩

/-- The residue-field embedding induced by pullback of a valuation ring. -/
noncomputable def valuationSubringComapResidueMap
    (A : ValuationSubring Omega) :
    IsLocalRing.ResidueField (A.comap (algebraMap F Omega)) →+*
      IsLocalRing.ResidueField A := by
  letI : IsLocalHom (valuationSubringComapMap (F := F) A) :=
    valuationSubringComapMap_isLocalHom (F := F) A
  exact IsLocalRing.ResidueField.map (valuationSubringComapMap (F := F) A)

/-- States the theorem `valuationSubringComapResidueMap_residue`. -/
@[simp] theorem valuationSubringComapResidueMap_residue
    (A : ValuationSubring Omega)
    (x : A.comap (algebraMap F Omega)) :
    valuationSubringComapResidueMap (F := F) A
        (IsLocalRing.residue (A.comap (algebraMap F Omega)) x) =
      IsLocalRing.residue A (valuationSubringComapMap (F := F) A x) :=
  rfl

/-- A purely inseparable extension remains purely inseparable after passing
to the residue fields of a valuation ring and its pullback.  In positive
characteristic this is the same Frobenius-power argument; in characteristic
zero the ambient purely inseparable extension is already trivial. -/
theorem valuationSubring_comap_residueField_isPurelyInseparable
    [IsPurelyInseparable F Omega] (A : ValuationSubring Omega) :
    letI : Algebra
        (IsLocalRing.ResidueField (A.comap (algebraMap F Omega)))
        (IsLocalRing.ResidueField A) :=
      (valuationSubringComapResidueMap (F := F) A).toAlgebra
    IsPurelyInseparable
      (IsLocalRing.ResidueField (A.comap (algebraMap F Omega)))
      (IsLocalRing.ResidueField A) := by
  let B := A.comap (algebraMap F Omega)
  let barI := valuationSubringComapResidueMap (F := F) A
  let : Algebra (IsLocalRing.ResidueField B)
      (IsLocalRing.ResidueField A) := barI.toAlgebra
  obtain ⟨q, hqF⟩ := ExpChar.exists F
  let : ExpChar F q := hqF
  cases hqF with
  | zero =>
      let : Algebra.IsSeparable F Omega := inferInstance
      rw [isPurelyInseparable_iff_pow_mem
        (IsLocalRing.ResidueField B)
        (ringExpChar (IsLocalRing.ResidueField B))]
      intro y
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
      obtain ⟨z, hz⟩ :=
        IsPurelyInseparable.surjective_algebraMap_of_isSeparable F Omega
          (a : Omega)
      let zB : B := ⟨z, by
        change algebraMap F Omega z ∈ A
        rw [hz]
        exact a.property⟩
      refine ⟨0, IsLocalRing.residue B zB, ?_⟩
      simp only [pow_zero, pow_one]
      change barI (IsLocalRing.residue B zB) = IsLocalRing.residue A a
      dsimp only [barI, B]
      rw [valuationSubringComapResidueMap_residue]
      apply congrArg (IsLocalRing.residue A)
      apply Subtype.ext
      exact hz
  | prime hq =>
      let : CharP Omega q :=
        charP_of_injective_algebraMap (algebraMap F Omega).injective q
      let : CharP A q := A.subtype.charP A.subtype_injective q
      let : CharP (IsLocalRing.ResidueField A) q :=
        CharP.of_ringHom_of_ne_zero (IsLocalRing.residue A) q hq.ne_zero
      let : CharP (IsLocalRing.ResidueField B) q :=
        barI.charP barI.injective q
      let : ExpChar (IsLocalRing.ResidueField B) q := ExpChar.prime hq
      rw [isPurelyInseparable_iff_pow_mem
        (IsLocalRing.ResidueField B) q]
      intro y
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
      obtain ⟨n, z, hz⟩ := IsPurelyInseparable.pow_mem F q (a : Omega)
      let zB : B := ⟨z, by
        change algebraMap F Omega z ∈ A
        rw [hz]
        exact pow_mem a.property _⟩
      refine ⟨n, IsLocalRing.residue B zB, ?_⟩
      change barI (IsLocalRing.residue B zB) =
        (IsLocalRing.residue A a) ^ q ^ n
      dsimp only [barI, B]
      rw [valuationSubringComapResidueMap_residue]
      rw [← map_pow]
      apply congrArg (IsLocalRing.residue A)
      apply Subtype.ext
      exact hz

end PurelyInseparableComap

end
end LocalClassFieldTheory
