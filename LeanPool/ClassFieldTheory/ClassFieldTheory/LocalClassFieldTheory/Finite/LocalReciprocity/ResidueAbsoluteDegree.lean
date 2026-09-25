/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAbsoluteFrobenius
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.IsSepClosed

/-! # Residue Absolute Degree -/

@[expose] public section
namespace LocalClassFieldTheory

open ClassFormation

/-!
# Finite local reciprocity: the absolute residue degree map

For a finite field `k`, arithmetic Frobenius identifies the absolute Galois
group of `k` with the profinite integers.  This file proves the missing
global statement from the compatible finite Frobenius coordinates:

* every positive integer occurs as the degree of an actual finite Galois
  intermediate field of `AlgebraicClosure k`;
* those fields detect every finite coordinate of `ℤ̂`, hence the assembled
  Frobenius map is injective;
* its compact image is all of the absolute Galois group;
* inversion gives the continuous degree map of the finite local reciprocity construction.
-/

noncomputable
section

universe u

open CategoryTheory Opposite
open FiniteGaloisIntermediateField ProfiniteGrp
open Polynomial

variable (k : Type u) [Field k] [Fintype k]

omit [Fintype k] in
/-- The characteristic of a finite field is prime. -/
instance finiteFieldRingCharPrime [Finite k] : Fact (ringChar k).Prime :=
  ⟨CharP.char_is_prime k (ringChar k)⟩

/-- The absolute Galois group of the residue field has a Hausdorff Krull topology. -/
noncomputable instance absoluteGaloisGroupT2 :
    T2Space (Field.absoluteGaloisGroup k) := by
  unfold Field.absoluteGaloisGroup
  exact krullTopology_t2

/-- A chosen embedding of the degree-`n` finite extension of `k` into its
algebraic closure. -/
noncomputable def finiteResidueExtensionEmbedding (n : ℕ) [NeZero n] :
    FiniteField.Extension k (ringChar k) n →ₐ[k] AlgebraicClosure k :=
  IsAlgClosed.lift

/-- The image in `AlgebraicClosure k` of the chosen degree-`n` extension. -/
noncomputable def finiteResidueIntermediateField (n : ℕ) [NeZero n] :
    IntermediateField k (AlgebraicClosure k) :=
  (⊤ : IntermediateField k (FiniteField.Extension k (ringChar k) n)).map
    (finiteResidueExtensionEmbedding k n)

/-- The chosen degree-`n` extension is isomorphic to its image in the
algebraic closure. -/
noncomputable def finiteResidueExtensionEquivIntermediate (n : ℕ) [NeZero n] :
    FiniteField.Extension k (ringChar k) n ≃ₐ[k]
      finiteResidueIntermediateField k n :=
  IntermediateField.topEquiv.symm.trans
    (IntermediateField.equivMap ⊤ (finiteResidueExtensionEmbedding k n))

/-- For every `n > 0`, an actual degree-`n` finite Galois intermediate field
inside `AlgebraicClosure k`. -/
noncomputable def finiteResidueGaloisIntermediateField (n : ℕ) [NeZero n] :
    FiniteGaloisIntermediateField k (AlgebraicClosure k) where
  toIntermediateField := finiteResidueIntermediateField k n
  finiteDimensional := Module.Finite.equiv
    (finiteResidueExtensionEquivIntermediate k n).toLinearEquiv
  isGalois := IsGalois.of_algEquiv
    (finiteResidueExtensionEquivIntermediate k n)

/-- The canonical finite residue subextension of level `n` has degree `n`. -/
@[simp]
theorem finrank_finiteResidueGaloisIntermediateField (n : ℕ) [NeZero n] :
    Module.finrank k (finiteResidueGaloisIntermediateField k n) = n := by
  calc
    Module.finrank k (finiteResidueGaloisIntermediateField k n) =
        Module.finrank k (FiniteField.Extension k (ringChar k) n) :=
      (finiteResidueExtensionEquivIntermediate k n).toLinearEquiv.finrank_eq.symm
    _ = n := FiniteField.finrank_extension k (ringChar k) n

/-- Finite extensions of every degree detect all profinite coordinates, so
the assembled Frobenius map on the algebraic closure is injective. -/
theorem residueAbsoluteFrobenius_algebraicClosure_injective :
    Function.Injective
      (residueAbsoluteFrobenius k (AlgebraicClosure k)) := by
  intro z w hzw
  apply Multiplicative.ext
  apply ZHat.ext
  intro n hn
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let E := finiteResidueGaloisIntermediateField k n
  have hrestriction := congrArg (AlgEquiv.restrictNormalHom E) hzw
  rw [restrictNormalHom_residueAbsoluteFrobenius (z := z) (E := E),
    restrictNormalHom_residueAbsoluteFrobenius (z := w) (E := E)] at hrestriction
  let : Finite E := Module.finite_of_finite k
  change finiteResidueFrobeniusFromZHat k E z =
    finiteResidueFrobeniusFromZHat k E w at hrestriction
  rw [finiteResidueFrobeniusFromZHat_apply,
    finiteResidueFrobeniusFromZHat_apply] at hrestriction
  have hcoordinate := congrArg Multiplicative.toAdd
    (finiteResidueFrobeniusExponentHom_injective k E hrestriction)
  have hdegree : Module.finrank k E = n := by
    exact finrank_finiteResidueGaloisIntermediateField k n
  simp only [toAdd_ofAdd] at hcoordinate
  change zHatReduction (Module.finrank k E) Module.finrank_pos z.toAdd =
    zHatReduction (Module.finrank k E) Module.finrank_pos w.toAdd at hcoordinate
  have hdiv : n ∣ Module.finrank k E := by simp [hdegree]
  have hcast := congrArg (ZMod.castHom hdiv (ZMod n)) hcoordinate
  rw [zHatReduction_transition hn Module.finrank_pos hdiv z.toAdd,
    zHatReduction_transition hn Module.finrank_pos hdiv w.toAdd] at hcast
  exact hcast

/-- In an algebraic closure of a finite field, the fixed points of arithmetic
Frobenius are exactly the elements of the base field. -/
theorem mem_range_algebraMap_iff_frobenius_fixed
    (x : AlgebraicClosure k) :
    x ∈ Set.range (algebraMap k (AlgebraicClosure k)) ↔
      FiniteField.frobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k) x = x := by
  constructor
  · rintro ⟨a, rfl⟩
    simp only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
    rw [← map_pow, FiniteField.pow_card]
  · intro hx
    have hxpow : x ^ Fintype.card k = x := by
      simpa only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic] using hx
    let p : k[X] := X ^ Fintype.card k - X
    have hpne : p ≠ 0 := by
      exact FiniteField.X_pow_card_sub_X_ne_zero k Fintype.one_lt_card
    have hxroot : x ∈ p.rootSet (AlgebraicClosure k) := by
      rw [Polynomial.mem_rootSet_of_ne hpne]
      simp [p, hxpow]
    have hsplits : (p.map (algebraMap k k)).Splits := by
      simpa only [p] using (FiniteField.isSplittingField_sub k k).splits
    have himage := hsplits.image_rootSet
      (Algebra.ofId k (AlgebraicClosure k))
    rw [← himage] at hxroot
    rcases hxroot with ⟨a, _ha, hax⟩
    exact ⟨a, hax⟩

/-- The compact image of the assembled Frobenius map, as a closed subgroup
of the absolute Galois group. -/
noncomputable def residueAbsoluteFrobeniusRange :
    ClosedSubgroup (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) where
  toSubgroup :=
    (residueAbsoluteFrobenius k (AlgebraicClosure k)).toMonoidHom.range
  isClosed' := by
    change IsClosed
      (Set.range (residueAbsoluteFrobenius k (AlgebraicClosure k)))
    exact (isCompact_range
      (residueAbsoluteFrobenius k
        (AlgebraicClosure k)).continuous_toFun).isClosed

/-- The compact Frobenius image fixes no elements beyond the base finite
field. -/
theorem fixedField_residueAbsoluteFrobeniusRange :
    IntermediateField.fixedField
        (residueAbsoluteFrobeniusRange k).toSubgroup = ⊥ := by
  apply le_antisymm
  · intro x hx
    have hfrobenius_mem :
        FiniteField.frobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k) ∈
          residueAbsoluteFrobeniusRange k := by
      change FiniteField.frobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k) ∈
        (residueAbsoluteFrobenius k
          (AlgebraicClosure k)).toMonoidHom.range
      exact ⟨Multiplicative.ofAdd (1 : ZHat),
        residueAbsoluteFrobenius_one k (AlgebraicClosure k)⟩
    rw [IntermediateField.mem_fixedField_iff] at hx
    have hxFrobenius := hx
      (FiniteField.frobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k))
      hfrobenius_mem
    rw [IntermediateField.mem_bot]
    exact (mem_range_algebraMap_iff_frobenius_fixed k x).mpr hxFrobenius
  · exact bot_le

/-- The closed Frobenius image is the whole absolute Galois group. -/
theorem residueAbsoluteFrobeniusRange_eq_top :
    (residueAbsoluteFrobeniusRange k).toSubgroup = ⊤ := by
  have hfixed := InfiniteGalois.fixingSubgroup_fixedField
    (residueAbsoluteFrobeniusRange k)
  rw [fixedField_residueAbsoluteFrobeniusRange,
    IntermediateField.fixingSubgroup_bot] at hfixed
  exact hfixed.symm

/-- The assembled Frobenius map onto the absolute Galois group of a finite
field is surjective. -/
theorem residueAbsoluteFrobenius_algebraicClosure_surjective :
    Function.Surjective
      (residueAbsoluteFrobenius k (AlgebraicClosure k)) := by
  intro sigma
  have hsigma : sigma ∈ (residueAbsoluteFrobeniusRange k).toSubgroup := by
    rw [residueAbsoluteFrobeniusRange_eq_top]
    exact Subgroup.mem_top sigma
  exact hsigma

/-- The Frobenius parameter map is a bijection for the algebraic closure of
a finite field. -/
theorem residueAbsoluteFrobenius_algebraicClosure_bijective :
    Function.Bijective
      (residueAbsoluteFrobenius k (AlgebraicClosure k)) :=
  ⟨residueAbsoluteFrobenius_algebraicClosure_injective k,
    residueAbsoluteFrobenius_algebraicClosure_surjective k⟩

/-- The underlying multiplicative equivalence between profinite integers and
the absolute Galois group of a finite field. -/
noncomputable def residueAbsoluteFrobeniusMulEquiv :
    ZHatMul ≃* Field.absoluteGaloisGroup k :=
  MulEquiv.ofBijective
    (residueAbsoluteFrobenius k (AlgebraicClosure k)).toMonoidHom
    (residueAbsoluteFrobenius_algebraicClosure_bijective k)

/-- Arithmetic Frobenius gives a topological group equivalence
`ℤ̂ ≃ Gal(k_bar/k)`. -/
noncomputable def residueAbsoluteFrobeniusEquiv :
    ZHatMul ≃ₜ* Field.absoluteGaloisGroup k where
  toMulEquiv := residueAbsoluteFrobeniusMulEquiv k
  continuous_toFun :=
    (residueAbsoluteFrobenius k
      (AlgebraicClosure k)).continuous_toFun
  continuous_invFun :=
    Continuous.continuous_symm_of_equiv_compact_to_t2
      (f := (residueAbsoluteFrobeniusMulEquiv k).toEquiv)
      (residueAbsoluteFrobenius k
        (AlgebraicClosure k)).continuous_toFun

/-- **Finite local reciprocity, absolute residue degree.**  The inverse of arithmetic
Frobenius coordinates, as a continuous surjective homomorphism
`Gal(k_bar/k) → ℤ̂`. -/
noncomputable def residueAbsoluteDegree :
    Field.absoluteGaloisGroup k →ₜ* ZHatMul :=
  ContinuousMonoidHom.toContinuousMonoidHom
    (residueAbsoluteFrobeniusEquiv k).symm

/-- The degree map is normalized by sending arithmetic Frobenius to `1`. -/
@[simp]
theorem residueAbsoluteDegree_frobenius :
    residueAbsoluteDegree k
        (FiniteField.frobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k)) =
      Multiplicative.ofAdd (1 : ZHat) := by
  apply (residueAbsoluteFrobeniusEquiv k).injective
  change (residueAbsoluteFrobeniusEquiv k)
      ((residueAbsoluteFrobeniusEquiv k).symm
        (FiniteField.frobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k))) =
    (residueAbsoluteFrobeniusEquiv k)
      (Multiplicative.ofAdd (1 : ZHat))
  exact ((residueAbsoluteFrobeniusEquiv k).apply_symm_apply
    (show Field.absoluteGaloisGroup k from
      FiniteField.frobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k))).trans
    (residueAbsoluteFrobenius_one k (AlgebraicClosure k)).symm

/-- On every finite Galois residue subextension, the absolute degree of an
automorphism is exactly its canonical Frobenius exponent.  This is the
finite-coordinate compatibility needed when the residue degree map is pulled
back to the absolute Galois group of a local field. -/
theorem finiteResidueFrobeniusIntermediate_residueAbsoluteDegree
    (sigma : Field.absoluteGaloisGroup k)
    (E : FiniteGaloisIntermediateField k (AlgebraicClosure k)) :
    finiteResidueFrobeniusIntermediate k (AlgebraicClosure k) E
        (residueAbsoluteDegree k sigma) =
      AlgEquiv.restrictNormalHom E sigma := by
  calc
    finiteResidueFrobeniusIntermediate k (AlgebraicClosure k) E
        (residueAbsoluteDegree k sigma) =
        AlgEquiv.restrictNormalHom E
          (residueAbsoluteFrobenius k (AlgebraicClosure k)
            (residueAbsoluteDegree k sigma)) :=
      (restrictNormalHom_residueAbsoluteFrobenius
        (k := k) (Omega := AlgebraicClosure k)
        (z := residueAbsoluteDegree k sigma) E).symm
    _ = AlgEquiv.restrictNormalHom E sigma := by
      exact congrArg (AlgEquiv.restrictNormalHom E)
        ((residueAbsoluteFrobeniusEquiv k).apply_symm_apply sigma)

/-- Coordinate form of
`finiteResidueFrobeniusIntermediate_residueAbsoluteDegree`: reducing the
absolute degree modulo `[E:k]` and exponentiating arithmetic Frobenius gives
the actual restriction of the automorphism to `E`. -/
theorem finiteResidueFrobeniusExponentHom_degree_coordinate
    (sigma : Field.absoluteGaloisGroup k)
    (E : FiniteGaloisIntermediateField k (AlgebraicClosure k)) :
    letI : Finite E := Module.finite_of_finite k
    finiteResidueFrobeniusExponentHom k E
        (Multiplicative.ofAdd
          (zHatReduction (Module.finrank k E) Module.finrank_pos
            (residueAbsoluteDegree k sigma).toAdd)) =
      AlgEquiv.restrictNormalHom E sigma := by
  let : Finite E := Module.finite_of_finite k
  exact finiteResidueFrobeniusIntermediate_residueAbsoluteDegree k sigma E

/-- Equivalently, the inverse finite Frobenius coordinate of a restriction
is the reduction of the absolute degree modulo the residue extension degree. -/
theorem finiteResidueFrobeniusExponentEquiv_symm_restrict
    (sigma : Field.absoluteGaloisGroup k)
    (E : FiniteGaloisIntermediateField k (AlgebraicClosure k)) :
    letI : Finite E := Module.finite_of_finite k
    (finiteResidueFrobeniusExponentEquiv k E).symm
        (AlgEquiv.restrictNormalHom E sigma) =
      Multiplicative.ofAdd
        (zHatReduction (Module.finrank k E) Module.finrank_pos
          (residueAbsoluteDegree k sigma).toAdd) := by
  let : Finite E := Module.finite_of_finite k
  apply (finiteResidueFrobeniusExponentEquiv k E).injective
  rw [(finiteResidueFrobeniusExponentEquiv k E).apply_symm_apply]
  exact (finiteResidueFrobeniusExponentHom_degree_coordinate k sigma E).symm

end
end LocalClassFieldTheory
