/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Weyl.Transposition
public import LeanPool.Stafford38.Stafford38.Weyl.GradedAlgebra
public import LeanPool.Stafford38.Stafford38.Weyl.SymbolCompatibility


/-!
# Filtration and symbol transport under Weyl transposition

The Weyl transposition reverses products, fixes coordinates, and negates
momenta.  This file proves directly from the checked PBW filtration that it
preserves both differential order and Bernstein degree.  No filtered
`D`-module or characteristic-variety theorem is used here.
-/

@[expose] public section

namespace Stafford38.WeylTranspositionFiltration

open MulOpposite
open Stafford
open Stafford38.Characteristic
open Stafford38.CharacteristicLinearAction
open Stafford38.WeylAssociatedGraded
open Stafford38.WeylFiltration
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylLeadingSymbol
open Stafford38.WeylPBW
open Stafford38.WeylTransposition

noncomputable section


universe u

variable (k : Type u) [Field k]

@[simp]
theorem transpose_zero (n : Nat) :
    transpose k n 0 = 0 := by
  simp [transpose]

@[simp]
theorem transpose_add (n : Nat) (a b : PresentedWeyl k n) :
    transpose k n (a + b) = transpose k n a + transpose k n b := by
  simp [transpose]

@[simp]
theorem transpose_smul (n : Nat) (c : k) (a : PresentedWeyl k n) :
    transpose k n (c • a) = c • transpose k n a := by
  simp [transpose]

@[simp]
theorem transpose_pow (n : Nat) (a : PresentedWeyl k n) (r : Nat) :
    transpose k n (a ^ r) = transpose k n a ^ r := by
  induction r with
  | zero => simp [transpose]
  | succ r ih =>
      rw [pow_succ, transpose_mul, ih]
      calc
        transpose k n a * transpose k n a ^ r =
            transpose k n a ^ r * transpose k n a :=
          ((Commute.refl (transpose k n a)).pow_right r).eq
        _ = transpose k n a ^ (r + 1) := (pow_succ _ _).symm

theorem transpose_previousWeylEmbedding (n : Nat) (a : PresentedWeyl k n) :
    transpose k (n + 1) (previousWeylEmbedding k n a) =
      previousWeylEmbedding k n (transpose k n a) := by
  let lhs : PresentedWeyl k n →ₐ[k] (PresentedWeyl k (n + 1))ᵐᵒᵖ :=
    (transpositionHom k (n + 1)).comp (previousWeylEmbedding k n)
  let rhs : PresentedWeyl k n →ₐ[k] (PresentedWeyl k (n + 1))ᵐᵒᵖ :=
    (AlgHom.op (previousWeylEmbedding k n)).comp (transpositionHom k n)
  have h : lhs = rhs := by
    apply Stafford38.WeylUniversal.freeWeyl_algHom_ext
    intro i
    dsimp [lhs, rhs]
    cases i with
    | inl i =>
        rw [previousWeylEmbedding_generator,
          show freeWeylGenerator (Matrix.J (Fin n) k) (.inl i) =
            coordinate k n i from rfl,
          transpositionHom_coordinate]
        change transpositionHom k (n + 1) (oldGenerator k n (.inl i)) =
          op (previousWeylEmbedding k n (coordinate k n i))
        rw [show oldGenerator k n (.inl i) = coordinate k (n + 1) i.succ from rfl,
          transpositionHom_coordinate]
        have hp := previousWeylEmbedding_generator k n (.inl i)
        change previousWeylEmbedding k n (coordinate k n i) =
          coordinate k (n + 1) i.succ at hp
        exact congrArg op hp.symm
    | inr i =>
        rw [previousWeylEmbedding_generator,
          show freeWeylGenerator (Matrix.J (Fin n) k) (.inr i) =
            momentum k n i from rfl,
          transpositionHom_momentum]
        change transpositionHom k (n + 1) (oldGenerator k n (.inr i)) =
          op (previousWeylEmbedding k n (-momentum k n i))
        rw [show oldGenerator k n (.inr i) = momentum k (n + 1) i.succ from rfl,
          transpositionHom_momentum, map_neg]
        have hp := previousWeylEmbedding_generator k n (.inr i)
        change previousWeylEmbedding k n (momentum k n i) =
          momentum k (n + 1) i.succ at hp
        exact congrArg op (congrArg Neg.neg hp.symm)
  have ha := DFunLike.congr_fun h a
  exact congrArg MulOpposite.unop ha

theorem coordinate_mem_bernsteinPiece {n : Nat} (i : Fin n) :
    coordinate k n i ∈ bernsteinPiece k n 1 := by
  rw [bernsteinPiece, mem_presentedWeightPiece, coordinate,
    presentedNormalFormLinearEquiv_generator]
  intro m hm
  simp only [MvPolynomial.coeff_X, ne_eq, ite_eq_right_iff] at hm
  by_contra hweight
  exact hm (by
    intro h
    subst m
    simp [monomialWeight, bernsteinWeight] at hweight)

theorem momentum_mem_bernsteinPiece {n : Nat} (i : Fin n) :
    momentum k n i ∈ bernsteinPiece k n 1 := by
  rw [bernsteinPiece, mem_presentedWeightPiece, momentum,
    presentedNormalFormLinearEquiv_generator]
  intro m hm
  simp only [MvPolynomial.coeff_X, ne_eq, ite_eq_right_iff] at hm
  by_contra hweight
  exact hm (by
    intro h
    subst m
    simp [monomialWeight, bernsteinWeight] at hweight)

theorem coordinate_mem_orderPiece {n : Nat} (i : Fin n) :
    coordinate k n i ∈ orderPiece k n 0 := by
  rw [orderPiece, mem_presentedWeightPiece, coordinate,
    presentedNormalFormLinearEquiv_generator]
  intro m hm
  simp only [MvPolynomial.coeff_X, ne_eq, ite_eq_right_iff] at hm
  by_contra hweight
  exact hm (by
    intro h
    subst m
    simp [monomialWeight, orderWeight, fibreWeight] at hweight)

theorem momentum_mem_orderPiece {n : Nat} (i : Fin n) :
    momentum k n i ∈ orderPiece k n 1 := by
  rw [orderPiece, mem_presentedWeightPiece, momentum,
    presentedNormalFormLinearEquiv_generator]
  intro m hm
  simp only [MvPolynomial.coeff_X, ne_eq, ite_eq_right_iff] at hm
  by_contra hweight
  exact hm (by
    intro h
    subst m
    simp [monomialWeight, orderWeight, fibreWeight] at hweight)

private theorem one_mem_weightPiece {n : Nat} (w : PhaseVar n → Nat) :
    (1 : PresentedWeyl k n) ∈ presentedWeightPiece k w 0 := by
  rw [mem_presentedWeightPiece, presentedNormalFormLinearEquiv_one]
  intro m hm
  simp only [MvPolynomial.coeff_one, ne_eq, ite_eq_right_iff] at hm
  by_contra hweight
  exact hm (by
    intro h
    subst m
    simp [monomialWeight] at hweight)

theorem coordinate_pow_mem_bernsteinPiece {n : Nat} (i : Fin n) (r : Nat) :
    coordinate k n i ^ r ∈ bernsteinPiece k n r := by
  induction r with
  | zero => simpa [bernsteinPiece] using one_mem_weightPiece k (@bernsteinWeight n)
  | succ r ih =>
      simpa [pow_succ] using mul_mem_bernsteinPiece k ih
        (coordinate_mem_bernsteinPiece k i)

theorem momentum_pow_mem_bernsteinPiece {n : Nat} (i : Fin n) (r : Nat) :
    (-momentum k n i) ^ r ∈ bernsteinPiece k n r := by
  have hm : -momentum k n i ∈ bernsteinPiece k n 1 :=
    (bernsteinPiece k n 1).neg_mem (momentum_mem_bernsteinPiece k i)
  induction r with
  | zero => simpa [bernsteinPiece] using one_mem_weightPiece k (@bernsteinWeight n)
  | succ r ih => simpa [pow_succ] using mul_mem_bernsteinPiece k ih hm

theorem coordinate_pow_mem_orderPiece {n : Nat} (i : Fin n) (r : Nat) :
    coordinate k n i ^ r ∈ orderPiece k n 0 := by
  induction r with
  | zero => simpa [orderPiece] using one_mem_weightPiece k (@orderWeight n)
  | succ r ih =>
      simpa [pow_succ] using mul_mem_orderPiece k ih
        (coordinate_mem_orderPiece k i)

theorem momentum_pow_mem_orderPiece {n : Nat} (i : Fin n) (r : Nat) :
    (-momentum k n i) ^ r ∈ orderPiece k n r := by
  have hm : -momentum k n i ∈ orderPiece k n 1 :=
    (orderPiece k n 1).neg_mem (momentum_mem_orderPiece k i)
  induction r with
  | zero => simpa [orderPiece] using one_mem_weightPiece k (@orderWeight n)
  | succ r ih => simpa [pow_succ] using mul_mem_orderPiece k ih hm

theorem previousWeylEmbedding_mem_bernsteinPiece {n N : Nat}
    {a : PresentedWeyl k n} (ha : a ∈ bernsteinPiece k n N) :
    previousWeylEmbedding k n a ∈ bernsteinPiece k (n + 1) N := by
  simpa [presentedCoefficientOrdered] using
    presentedCoefficientOrdered_mem_bernsteinPiece k n N 0 0 a ha

theorem previousWeylEmbedding_mem_orderPiece {n N : Nat}
    {a : PresentedWeyl k n} (ha : a ∈ orderPiece k n N) :
    previousWeylEmbedding k n a ∈ orderPiece k (n + 1) N := by
  simpa [presentedCoefficientOrdered] using
    presentedCoefficientOrdered_mem_orderPiece k n N 0 0 a ha

theorem transpose_orderedMonomial_mem_bernsteinPiece :
    ∀ (n : Nat) (a p : Fin n → Nat),
      transpose k n (presentedOrderedMonomial k n a p) ∈
        bernsteinPiece k n
          (monomialWeight (@bernsteinWeight n) (phaseExponent a p)) := by
  intro n
  induction n with
  | zero =>
      intro a p
      have he : phaseExponent a p = 0 := by
        ext i
        exact Sum.elim Fin.elim0 Fin.elim0 i
      rw [he]
      simpa [presentedOrderedMonomial, monomialWeight, bernsteinPiece,
        transpose] using one_mem_weightPiece k (@bernsteinWeight 0)
  | succ n ih =>
      intro a p
      let oldA : Fin n → Nat := fun i => a i.succ
      let oldP : Fin n → Nat := fun i => p i.succ
      have hold := previousWeylEmbedding_mem_bernsteinPiece k
        (ih oldA oldP)
      have hx := coordinate_pow_mem_bernsteinPiece k
        (0 : Fin (n + 1)) (a 0)
      have hp := momentum_pow_mem_bernsteinPiece k
        (0 : Fin (n + 1)) (p 0)
      have hmul := mul_mem_bernsteinPiece k
        (mul_mem_bernsteinPiece k hp hx) hold
      rw [presentedOrderedMonomial, transpose_mul, transpose_mul,
        transpose_pow, transpose_pow,
        show presentedMomentum k n = momentum k (n + 1) 0 from rfl,
        show presentedCoordinate k n = coordinate k (n + 1) 0 from rfl,
        transpose_momentum, transpose_coordinate,
        transpose_previousWeylEmbedding]
      rw [monomialWeight_phaseExponent_succ_bernstein]
      simpa [oldA, oldP, mul_assoc, add_assoc, add_comm, add_left_comm] using hmul

theorem transpose_orderedMonomial_mem_orderPiece :
    ∀ (n : Nat) (a p : Fin n → Nat),
      transpose k n (presentedOrderedMonomial k n a p) ∈
        orderPiece k n
          (monomialWeight (@orderWeight n) (phaseExponent a p)) := by
  intro n
  induction n with
  | zero =>
      intro a p
      have he : phaseExponent a p = 0 := by
        ext i
        exact Sum.elim Fin.elim0 Fin.elim0 i
      rw [he]
      simpa [presentedOrderedMonomial, monomialWeight, orderPiece,
        transpose] using one_mem_weightPiece k (@orderWeight 0)
  | succ n ih =>
      intro a p
      let oldA : Fin n → Nat := fun i => a i.succ
      let oldP : Fin n → Nat := fun i => p i.succ
      have hold := previousWeylEmbedding_mem_orderPiece k (ih oldA oldP)
      have hx := coordinate_pow_mem_orderPiece k
        (0 : Fin (n + 1)) (a 0)
      have hp := momentum_pow_mem_orderPiece k
        (0 : Fin (n + 1)) (p 0)
      have hmul := mul_mem_orderPiece k (mul_mem_orderPiece k hp hx) hold
      rw [presentedOrderedMonomial, transpose_mul, transpose_mul,
        transpose_pow, transpose_pow,
        show presentedMomentum k n = momentum k (n + 1) 0 from rfl,
        show presentedCoordinate k n = coordinate k (n + 1) 0 from rfl,
        transpose_momentum, transpose_coordinate,
        transpose_previousWeylEmbedding]
      rw [monomialWeight_phaseExponent_succ_order]
      simpa [oldA, oldP, mul_assoc, add_assoc, add_comm, add_left_comm] using hmul

theorem transpose_mem_bernsteinPiece {n N : Nat} {a : PresentedWeyl k n}
    (ha : a ∈ bernsteinPiece k n N) :
    transpose k n a ∈ bernsteinPiece k n N := by
  rw [bernsteinPiece, presentedWeightPiece_eq_span] at ha
  change transpose k n a ∈ presentedWeightPiece k bernsteinWeight N
  induction ha using Submodule.span_induction with
  | mem b hb =>
      obtain ⟨m, hm, rfl⟩ := hb
      rw [presentedPBWBasis_apply]
      have hmono := transpose_orderedMonomial_mem_bernsteinPiece k n
        (fun i => m (.inl i)) (fun i => m (.inr i))
      exact presentedWeightPiece_mono k bernsteinWeight hm
        (by simpa [bernsteinPiece, phaseExponent_split] using hmono)
  | zero =>
      rw [transpose_zero]
      exact (presentedWeightPiece k bernsteinWeight N).zero_mem
  | add x y hx hy ihx ihy =>
      rw [transpose_add]
      exact (presentedWeightPiece k bernsteinWeight N).add_mem ihx ihy
  | smul c x hx ih =>
      rw [transpose_smul]
      exact (presentedWeightPiece k bernsteinWeight N).smul_mem c ih

theorem transpose_mem_orderPiece {n N : Nat} {a : PresentedWeyl k n}
    (ha : a ∈ orderPiece k n N) :
    transpose k n a ∈ orderPiece k n N := by
  rw [orderPiece, presentedWeightPiece_eq_span] at ha
  change transpose k n a ∈ presentedWeightPiece k orderWeight N
  induction ha using Submodule.span_induction with
  | mem b hb =>
      obtain ⟨m, hm, rfl⟩ := hb
      rw [presentedPBWBasis_apply]
      have hmono := transpose_orderedMonomial_mem_orderPiece k n
        (fun i => m (.inl i)) (fun i => m (.inr i))
      exact presentedWeightPiece_mono k orderWeight hm
        (by simpa [orderPiece, phaseExponent_split] using hmono)
  | zero =>
      rw [transpose_zero]
      exact (presentedWeightPiece k orderWeight N).zero_mem
  | add x y hx hy ihx ihy =>
      rw [transpose_add]
      exact (presentedWeightPiece k orderWeight N).add_mem ihx ihy
  | smul c x hx ih =>
      rw [transpose_smul]
      exact (presentedWeightPiece k orderWeight N).smul_mem c ih

theorem transpose_mem_bernsteinPiece_iff {n N : Nat} (a : PresentedWeyl k n) :
    transpose k n a ∈ bernsteinPiece k n N ↔ a ∈ bernsteinPiece k n N := by
  constructor
  · intro h
    simpa using transpose_mem_bernsteinPiece k h
  · exact transpose_mem_bernsteinPiece k

theorem transpose_mem_orderPiece_iff {n N : Nat} (a : PresentedWeyl k n) :
    transpose k n a ∈ orderPiece k n N ↔ a ∈ orderPiece k n N := by
  constructor
  · intro h
    simpa using transpose_mem_orderPiece k h
  · exact transpose_mem_orderPiece k

/-- The expected phase-space sign substitution: coordinates are fixed and
momentum variables are negated. -/
def symbolTransposition {n : Nat} : SymbolRing k n →ₐ[k] SymbolRing k n :=
  MvPolynomial.aeval (Sum.elim
    (fun i : Fin n => MvPolynomial.X (.inl i))
    (fun i : Fin n => -MvPolynomial.X (.inr i)))

@[simp]
theorem symbolTransposition_coordinate {n : Nat} (i : Fin n) :
    symbolTransposition k (MvPolynomial.X (.inl i)) = MvPolynomial.X (.inl i) := by
  simp [symbolTransposition]

@[simp]
theorem symbolTransposition_momentum {n : Nat} (i : Fin n) :
    symbolTransposition k (MvPolynomial.X (.inr i)) = -MvPolynomial.X (.inr i) := by
  simp [symbolTransposition]

private theorem principal_coordinate_bernstein {n : Nat} (i : Fin n) :
    presentedPrincipalComponent k (@bernsteinWeight n) 1 (coordinate k n i) =
      MvPolynomial.X (.inl i) := by
  rw [presentedPrincipalComponent, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, coordinate,
    presentedNormalFormLinearEquiv_generator]
  have hx : MvPolynomial.X (.inl i : PhaseVar n) =
      MvPolynomial.monomial
        (Finsupp.single (.inl i : PhaseVar n) 1) (1 : k) := by
    simpa using (MvPolynomial.X_pow_eq_monomial
      (R := k) (n := (.inl i : PhaseVar n)) (e := 1))
  rw [hx]
  rw [weightedHomogeneousComponent_monomial]
  simp [monomialWeight, bernsteinWeight]

private theorem principal_momentum_bernstein {n : Nat} (i : Fin n) :
    presentedPrincipalComponent k (@bernsteinWeight n) 1 (momentum k n i) =
      MvPolynomial.X (.inr i) := by
  rw [presentedPrincipalComponent, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, momentum,
    presentedNormalFormLinearEquiv_generator]
  have hx : MvPolynomial.X (.inr i : PhaseVar n) =
      MvPolynomial.monomial
        (Finsupp.single (.inr i : PhaseVar n) 1) (1 : k) := by
    simpa using (MvPolynomial.X_pow_eq_monomial
      (R := k) (n := (.inr i : PhaseVar n)) (e := 1))
  rw [hx]
  rw [weightedHomogeneousComponent_monomial]
  simp [monomialWeight, bernsteinWeight]

private theorem principal_negMomentum_pow_bernstein {n : Nat}
    (i : Fin n) (r : Nat) :
    presentedPrincipalComponent k (@bernsteinWeight n) r
        ((-momentum k n i) ^ r) = (-MvPolynomial.X (.inr i)) ^ r := by
  have hm : -momentum k n i ∈ bernsteinPiece k n 1 :=
    (bernsteinPiece k n 1).neg_mem (momentum_mem_bernsteinPiece k i)
  rw [Stafford38.WeylSymbolCompatibility.pow_principal_bernstein k hm,
    map_neg, principal_momentum_bernstein]

private theorem principal_coordinate_pow_bernstein {n : Nat}
    (i : Fin n) (r : Nat) :
    presentedPrincipalComponent k (@bernsteinWeight n) r
        (coordinate k n i ^ r) = MvPolynomial.X (.inl i) ^ r := by
  rw [Stafford38.WeylSymbolCompatibility.pow_principal_bernstein k
      (coordinate_mem_bernsteinPiece k i),
    principal_coordinate_bernstein]

private theorem principal_previous_bernstein {n N : Nat}
    (a : PresentedWeyl k n) :
    presentedPrincipalComponent k (@bernsteinWeight (n + 1)) N
        (previousWeylEmbedding k n a) =
      MvPolynomial.rename oldIndex
        (presentedPrincipalComponent k (@bernsteinWeight n) N a) := by
  simpa [presentedCoefficientOrdered, extendPhaseExponent] using
    presentedPrincipalComponent_coefficientOrdered_bernstein k n N 0 0 a

theorem symbolTransposition_rename_oldIndex {n : Nat} (f : SymbolRing k n) :
    symbolTransposition k (MvPolynomial.rename oldIndex f) =
      MvPolynomial.rename oldIndex (symbolTransposition k f) := by
  let lhs : SymbolRing k n →ₐ[k] SymbolRing k (n + 1) :=
    (symbolTransposition k).comp (MvPolynomial.rename oldIndex)
  let rhs : SymbolRing k n →ₐ[k] SymbolRing k (n + 1) :=
    (MvPolynomial.rename oldIndex).comp (symbolTransposition k)
  have h : lhs = rhs := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | inl i => simp [lhs, rhs, oldIndex]
    | inr i => simp [lhs, rhs, oldIndex]
  exact DFunLike.congr_fun h f

theorem principal_transpose_orderedMonomial_bernstein :
    ∀ (n : Nat) (a p : Fin n → Nat),
      presentedPrincipalComponent k (@bernsteinWeight n)
          (monomialWeight (@bernsteinWeight n) (phaseExponent a p))
          (transpose k n (presentedOrderedMonomial k n a p)) =
        symbolTransposition k
          (MvPolynomial.monomial (phaseExponent a p) (1 : k)) := by
  intro n
  induction n with
  | zero =>
      intro a p
      have he : phaseExponent a p = 0 := by
        ext i
        exact Sum.elim Fin.elim0 Fin.elim0 i
      rw [he]
      simp [presentedOrderedMonomial, transpose, monomialWeight,
        presentedPrincipalComponent, presentedNormalFormLinearEquiv_one,
         symbolTransposition]
  | succ n ih =>
      intro a p
      let oldA : Fin n → Nat := fun i => a i.succ
      let oldP : Fin n → Nat := fun i => p i.succ
      let oldD := monomialWeight (@bernsteinWeight n) (phaseExponent oldA oldP)
      have hold := previousWeylEmbedding_mem_bernsteinPiece k
        (transpose_orderedMonomial_mem_bernsteinPiece k n oldA oldP)
      have hx := coordinate_pow_mem_bernsteinPiece k
        (0 : Fin (n + 1)) (a 0)
      have hp := momentum_pow_mem_bernsteinPiece k
        (0 : Fin (n + 1)) (p 0)
      have hxo := mul_mem_bernsteinPiece k hx hold
      rw [presentedOrderedMonomial, transpose_mul, transpose_mul,
        transpose_pow, transpose_pow,
        show presentedMomentum k n = momentum k (n + 1) 0 from rfl,
        show presentedCoordinate k n = coordinate k (n + 1) 0 from rfl,
        transpose_momentum, transpose_coordinate,
        transpose_previousWeylEmbedding,
        monomialWeight_phaseExponent_succ_bernstein]
      change presentedPrincipalComponent k (@bernsteinWeight (n + 1))
          (oldD + a 0 + p 0)
          ((-momentum k (n + 1) 0) ^ p 0 *
            (coordinate k (n + 1) 0 ^ a 0 *
              previousWeylEmbedding k n
                (transpose k n (presentedOrderedMonomial k n oldA oldP)))) = _
      rw [show oldD + a 0 + p 0 = p 0 + (a 0 + oldD) by omega,
        presentedPrincipalComponent_mul_bernstein k hp hxo,
        presentedPrincipalComponent_mul_bernstein k hx hold,
        principal_negMomentum_pow_bernstein,
        principal_coordinate_pow_bernstein,
        principal_previous_bernstein, ih oldA oldP]
      rw [Stafford38.WeylSymbolCompatibility.phaseMonomial_succ_decompose]
      simp only [map_mul, map_pow, symbolTransposition_coordinate,
        symbolTransposition_momentum, symbolTransposition_rename_oldIndex]
      ring

theorem principal_transpose_bernstein {n N : Nat} {a : PresentedWeyl k n}
    (ha : a ∈ bernsteinPiece k n N) :
    presentedPrincipalComponent k (@bernsteinWeight n) N (transpose k n a) =
      symbolTransposition k
        (presentedPrincipalComponent k (@bernsteinWeight n) N a) := by
  rw [bernsteinPiece, presentedWeightPiece_eq_span] at ha
  induction ha using Submodule.span_induction with
  | mem b hb =>
      obtain ⟨m, hm, rfl⟩ := hb
      let d := monomialWeight (@bernsteinWeight n) m
      by_cases hd : d = N
      · subst N
        rw [presentedPBWBasis_apply]
        have ht := principal_transpose_orderedMonomial_bernstein k n
          (fun i => m (.inl i)) (fun i => m (.inr i))
        have ht' :
            presentedPrincipalComponent k (@bernsteinWeight n) d
                (transpose k n
                  (presentedOrderedMonomial k n
                    (fun i => m (.inl i)) (fun i => m (.inr i)))) =
              symbolTransposition k (MvPolynomial.monomial m (1 : k)) := by
          simpa [phaseExponent_split] using ht
        have ho :
            presentedPrincipalComponent k (@bernsteinWeight n) d
                (presentedOrderedMonomial k n
                  (fun i => m (.inl i)) (fun i => m (.inr i))) =
              MvPolynomial.monomial m (1 : k) := by
          rw [← presentedPBWBasis_apply,
            presentedPrincipalComponent_basis, ite_eq_left rfl]
        rw [ht', ho]
      · have hdlt : d < N := lt_of_le_of_ne hm hd
        have ht := transpose_orderedMonomial_mem_bernsteinPiece k n
          (fun i => m (.inl i)) (fun i => m (.inr i))
        rw [presentedPBWBasis_apply]
        have ht' : transpose k n
              (presentedOrderedMonomial k n
                (fun i => m (.inl i)) (fun i => m (.inr i))) ∈
            bernsteinPiece k n d := by
          simpa [phaseExponent_split] using ht
        have ho :
            presentedPrincipalComponent k (@bernsteinWeight n) N
                (presentedOrderedMonomial k n
                  (fun i => m (.inl i)) (fun i => m (.inr i))) = 0 := by
          rw [← presentedPBWBasis_apply,
            presentedPrincipalComponent_basis, ite_eq_right hd]
        rw [presentedPrincipalComponent_eq_zero_of_mem_of_lt k
            bernsteinWeight _ ht' hdlt, ho, map_zero]
  | zero => simp
  | add x y hx hy ihx ihy => simp only [transpose_add, map_add, ihx, ihy]
  | smul c x hx ih => simp only [transpose_smul, map_smul, ih]

private theorem principal_coordinate_order {n : Nat} (i : Fin n) :
    presentedPrincipalComponent k (@orderWeight n) 0 (coordinate k n i) =
      MvPolynomial.X (.inl i) := by
  rw [presentedPrincipalComponent, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, coordinate,
    presentedNormalFormLinearEquiv_generator]
  have hx : MvPolynomial.X (.inl i : PhaseVar n) =
      MvPolynomial.monomial
        (Finsupp.single (.inl i : PhaseVar n) 1) (1 : k) := by
    simpa using (MvPolynomial.X_pow_eq_monomial
      (R := k) (n := (.inl i : PhaseVar n)) (e := 1))
  rw [hx, weightedHomogeneousComponent_monomial]
  simp [monomialWeight, orderWeight, fibreWeight]

private theorem principal_momentum_order {n : Nat} (i : Fin n) :
    presentedPrincipalComponent k (@orderWeight n) 1 (momentum k n i) =
      MvPolynomial.X (.inr i) := by
  rw [presentedPrincipalComponent, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, momentum,
    presentedNormalFormLinearEquiv_generator]
  have hx : MvPolynomial.X (.inr i : PhaseVar n) =
      MvPolynomial.monomial
        (Finsupp.single (.inr i : PhaseVar n) 1) (1 : k) := by
    simpa using (MvPolynomial.X_pow_eq_monomial
      (R := k) (n := (.inr i : PhaseVar n)) (e := 1))
  rw [hx, weightedHomogeneousComponent_monomial]
  simp [monomialWeight, orderWeight, fibreWeight]

private theorem principal_one_order {n : Nat} :
    presentedPrincipalComponent k (@orderWeight n) 0
        (1 : PresentedWeyl k n) = 1 := by
  rw [presentedPrincipalComponent, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, presentedNormalFormLinearEquiv_one]
  rw [show (1 : SymbolRing k n) = MvPolynomial.monomial 0 (1 : k) by simp,
    weightedHomogeneousComponent_monomial]
  simp [monomialWeight]

private theorem principal_coordinate_pow_order {n : Nat}
    (i : Fin n) (r : Nat) :
    presentedPrincipalComponent k (@orderWeight n) 0
        (coordinate k n i ^ r) = MvPolynomial.X (.inl i) ^ r := by
  induction r with
  | zero => simpa using principal_one_order k (n := n)
  | succ r ih =>
      rw [pow_succ, pow_succ]
      rw [presentedPrincipalComponent_mul_order k
        (coordinate_pow_mem_orderPiece k i r) (coordinate_mem_orderPiece k i),
        ih, principal_coordinate_order]

private theorem principal_negMomentum_pow_order {n : Nat}
    (i : Fin n) (r : Nat) :
    presentedPrincipalComponent k (@orderWeight n) r
        ((-momentum k n i) ^ r) = (-MvPolynomial.X (.inr i)) ^ r := by
  induction r with
  | zero => simpa using principal_one_order k (n := n)
  | succ r ih =>
      have hm : -momentum k n i ∈ orderPiece k n 1 :=
        (orderPiece k n 1).neg_mem (momentum_mem_orderPiece k i)
      rw [pow_succ, pow_succ]
      rw [presentedPrincipalComponent_mul_order k
        (momentum_pow_mem_orderPiece k i r) hm,
        ih,
        map_neg, principal_momentum_order]

private theorem principal_previous_order {n N : Nat}
    (a : PresentedWeyl k n) :
    presentedPrincipalComponent k (@orderWeight (n + 1)) N
        (previousWeylEmbedding k n a) =
      MvPolynomial.rename oldIndex
        (presentedPrincipalComponent k (@orderWeight n) N a) := by
  simpa [presentedCoefficientOrdered, extendPhaseExponent] using
    presentedPrincipalComponent_coefficientOrdered_order k n N 0 0 a

theorem principal_transpose_orderedMonomial_order :
    ∀ (n : Nat) (a p : Fin n → Nat),
      presentedPrincipalComponent k (@orderWeight n)
          (monomialWeight (@orderWeight n) (phaseExponent a p))
          (transpose k n (presentedOrderedMonomial k n a p)) =
        symbolTransposition k
          (MvPolynomial.monomial (phaseExponent a p) (1 : k)) := by
  intro n
  induction n with
  | zero =>
      intro a p
      have he : phaseExponent a p = 0 := by
        ext i
        exact Sum.elim Fin.elim0 Fin.elim0 i
      rw [he]
      simp [presentedOrderedMonomial, transpose, monomialWeight,
        presentedPrincipalComponent, presentedNormalFormLinearEquiv_one,
         symbolTransposition]
  | succ n ih =>
      intro a p
      let oldA : Fin n → Nat := fun i => a i.succ
      let oldP : Fin n → Nat := fun i => p i.succ
      let oldD := monomialWeight (@orderWeight n) (phaseExponent oldA oldP)
      have hold := previousWeylEmbedding_mem_orderPiece k
        (transpose_orderedMonomial_mem_orderPiece k n oldA oldP)
      have hx := coordinate_pow_mem_orderPiece k
        (0 : Fin (n + 1)) (a 0)
      have hp := momentum_pow_mem_orderPiece k
        (0 : Fin (n + 1)) (p 0)
      have hxo := mul_mem_orderPiece k hx hold
      rw [presentedOrderedMonomial, transpose_mul, transpose_mul,
        transpose_pow, transpose_pow,
        show presentedMomentum k n = momentum k (n + 1) 0 from rfl,
        show presentedCoordinate k n = coordinate k (n + 1) 0 from rfl,
        transpose_momentum, transpose_coordinate,
        transpose_previousWeylEmbedding,
        monomialWeight_phaseExponent_succ_order]
      change presentedPrincipalComponent k (@orderWeight (n + 1))
          (oldD + p 0)
          ((-momentum k (n + 1) 0) ^ p 0 *
            (coordinate k (n + 1) 0 ^ a 0 *
              previousWeylEmbedding k n
                (transpose k n (presentedOrderedMonomial k n oldA oldP)))) = _
      rw [show oldD + p 0 = p 0 + (0 + oldD) by omega,
        presentedPrincipalComponent_mul_order k hp hxo,
        presentedPrincipalComponent_mul_order k hx hold,
        principal_negMomentum_pow_order,
        principal_coordinate_pow_order,
        principal_previous_order, ih oldA oldP]
      rw [Stafford38.WeylSymbolCompatibility.phaseMonomial_succ_decompose]
      simp only [map_mul, map_pow, symbolTransposition_coordinate,
        symbolTransposition_momentum, symbolTransposition_rename_oldIndex]
      ring

theorem principal_transpose_order {n N : Nat} {a : PresentedWeyl k n}
    (ha : a ∈ orderPiece k n N) :
    presentedPrincipalComponent k (@orderWeight n) N (transpose k n a) =
      symbolTransposition k
        (presentedPrincipalComponent k (@orderWeight n) N a) := by
  rw [orderPiece, presentedWeightPiece_eq_span] at ha
  induction ha using Submodule.span_induction with
  | mem b hb =>
      obtain ⟨m, hm, rfl⟩ := hb
      let d := monomialWeight (@orderWeight n) m
      by_cases hd : d = N
      · subst N
        rw [presentedPBWBasis_apply]
        have ht := principal_transpose_orderedMonomial_order k n
          (fun i => m (.inl i)) (fun i => m (.inr i))
        have ht' :
            presentedPrincipalComponent k (@orderWeight n) d
                (transpose k n
                  (presentedOrderedMonomial k n
                    (fun i => m (.inl i)) (fun i => m (.inr i)))) =
              symbolTransposition k (MvPolynomial.monomial m (1 : k)) := by
          simpa [phaseExponent_split] using ht
        have ho :
            presentedPrincipalComponent k (@orderWeight n) d
                (presentedOrderedMonomial k n
                  (fun i => m (.inl i)) (fun i => m (.inr i))) =
              MvPolynomial.monomial m (1 : k) := by
          rw [← presentedPBWBasis_apply,
            presentedPrincipalComponent_basis, ite_eq_left rfl]
        rw [ht', ho]
      · have hdlt : d < N := lt_of_le_of_ne hm hd
        have ht := transpose_orderedMonomial_mem_orderPiece k n
          (fun i => m (.inl i)) (fun i => m (.inr i))
        rw [presentedPBWBasis_apply]
        have ht' : transpose k n
              (presentedOrderedMonomial k n
                (fun i => m (.inl i)) (fun i => m (.inr i))) ∈
            orderPiece k n d := by
          simpa [phaseExponent_split] using ht
        have ho :
            presentedPrincipalComponent k (@orderWeight n) N
                (presentedOrderedMonomial k n
                  (fun i => m (.inl i)) (fun i => m (.inr i))) = 0 := by
          rw [← presentedPBWBasis_apply,
            presentedPrincipalComponent_basis, ite_eq_right hd]
        rw [presentedPrincipalComponent_eq_zero_of_mem_of_lt k
            orderWeight _ ht' hdlt, ho, map_zero]
  | zero => simp
  | add x y hx hy ihx ihy => simp only [transpose_add, map_add, ihx, ihy]
  | smul c x hx ih => simp only [transpose_smul, map_smul, ih]

theorem symbolTransposition_comp_self {n : Nat} :
    (symbolTransposition k).comp (symbolTransposition k) =
      AlgHom.id k (SymbolRing k n) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | inl i => simp
  | inr i => simp

/-- The involutive symbol-algebra automorphism induced by Weyl transposition. -/
def symbolTranspositionEquiv {n : Nat} :
    SymbolRing k n ≃ₐ[k] SymbolRing k n :=
  AlgEquiv.ofAlgHom (symbolTransposition k) (symbolTransposition k)
    (symbolTransposition_comp_self k) (symbolTransposition_comp_self k)

/-- The associated-graded automorphism corresponding to Weyl transposition.
It is conjugate to momentum-sign substitution under the checked symbol
equivalence. -/
def associatedGradedTransposition {n : Nat} (w : PhaseVar n → Nat) :
    PresentedAssociatedGraded k w ≃ₐ[k] PresentedAssociatedGraded k w :=
  (presentedAssociatedGradedAlgEquiv k w).trans
    ((symbolTranspositionEquiv k).trans
      (presentedAssociatedGradedAlgEquiv k w).symm)

theorem associatedGradedTransposition_mk_bernstein {n N : Nat}
    (a : bernsteinPiece k n N) :
    associatedGradedTransposition k bernsteinWeight
        (presentedAssociatedGradedMk k bernsteinWeight a) =
      presentedAssociatedGradedMk k bernsteinWeight
        ⟨transpose k n a, transpose_mem_bernsteinPiece k a.property⟩ := by
  change presentedWeightPiece k bernsteinWeight N at a
  apply (presentedAssociatedGradedAlgEquiv k bernsteinWeight).injective
  simp [associatedGradedTransposition, symbolTranspositionEquiv,
    principal_transpose_bernstein k a.property]

theorem associatedGradedTransposition_mk_order {n N : Nat}
    (a : orderPiece k n N) :
    associatedGradedTransposition k orderWeight
        (presentedAssociatedGradedMk k orderWeight a) =
      presentedAssociatedGradedMk k orderWeight
        ⟨transpose k n a, transpose_mem_orderPiece k a.property⟩ := by
  change presentedWeightPiece k orderWeight N at a
  apply (presentedAssociatedGradedAlgEquiv k orderWeight).injective
  simp [associatedGradedTransposition, symbolTranspositionEquiv,
    principal_transpose_order k a.property]

theorem principal_transpose_coordinate {n : Nat} (i : Fin n) :
    presentedPrincipalComponent k (@bernsteinWeight n) 1
        (transpose k n (coordinate k n i)) =
      symbolTransposition k
        (presentedPrincipalComponent k (@bernsteinWeight n) 1
          (coordinate k n i)) := by
  rw [transpose_coordinate]
  rw [principal_coordinate_bernstein, symbolTransposition_coordinate]

theorem principal_transpose_momentum {n : Nat} (i : Fin n) :
    presentedPrincipalComponent k (@bernsteinWeight n) 1
        (transpose k n (momentum k n i)) =
      symbolTransposition k
        (presentedPrincipalComponent k (@bernsteinWeight n) 1
          (momentum k n i)) := by
  rw [transpose_momentum]
  rw [map_neg, principal_momentum_bernstein, symbolTransposition_momentum]


end
end Stafford38.WeylTranspositionFiltration
