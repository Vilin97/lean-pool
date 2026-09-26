/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Characteristic.OrderReesTwoJet
public import LeanPool.Stafford38.Stafford38.Weyl.PBWFirstContraction


/-!
# The commutator bracket in the order-Rees two-jet

Every commutator in the order-Rees ring loses one unit of differential order,
so it has an explicit factor of the Rees parameter.  This file constructs the
quotient coefficient by coefficient.  After specialization, that quotient is
the negative Poisson bracket, with the sign forced by `[x,p] = -1`.

The quotient is deliberately attached to chosen Rees lifts: modulo `T²`, a
quotient by `T` is only determined modulo `T`.  The final theorem therefore
asserts existence for arbitrary two-jet classes while retaining the explicit
source-level witness used to prove it.
-/

@[expose] public section

namespace Stafford38.CharacteristicOrderReesTwoJetBracket

open Stafford38.Characteristic
open Stafford38.CharacteristicOrderReesTwoJet
open Stafford38.WeylAssociatedGraded
open Stafford38.WeylFilteredCommutator
open Stafford38.WeylFiltration
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylLeadingSymbol
open Stafford38.WeylOrderRees
open Stafford38.WeylPBWFirstContraction

noncomputable section


universe u

variable (k : Type u) [Field k]
variable {n : ℕ}

/-- The quotient of a homogeneous Rees commutator by one Rees parameter. -/
def homogeneousCommutatorQuotient
    (r s : ℕ) (a : orderPiece k n r) (b : orderPiece k n s) :
    OrderReesRing (n := n) k :=
  if _h : 0 < r + s then
    orderReesMonomial k (r + s - 1)
      ⟨Stafford.commutator (a : PresentedWeyl k n) b,
        commutator_mem_orderPiece_pred k a.property b.property⟩
  else 0

/-- Multiplying the homogeneous quotient by `T` recovers the written-order
commutator of the two homogeneous Rees terms. -/
theorem parameter_mul_homogeneousCommutatorQuotient
    (r s : ℕ) (a : orderPiece k n r) (b : orderPiece k n s) :
    orderReesParameter (n := n) k *
        homogeneousCommutatorQuotient k r s a b =
      Stafford.commutator
        (orderReesMonomial k r a) (orderReesMonomial k s b) := by
  by_cases h : 0 < r + s
  · rw [homogeneousCommutatorQuotient, dite_eq_left h,
      orderReesParameter_mul_monomial]
    apply Subtype.ext
    change Polynomial.monomial ((r + s - 1) + 1)
        (Stafford.commutator (a : PresentedWeyl k n) b) =
      Polynomial.monomial r (a : PresentedWeyl k n) *
          Polynomial.monomial s (b : PresentedWeyl k n) -
        Polynomial.monomial s (b : PresentedWeyl k n) *
          Polynomial.monomial r (a : PresentedWeyl k n)
    simp only [Polynomial.monomial_mul_monomial, Stafford.commutator,
      AlgebraicAnalysis.ringCommutator]
    rw [show s + r = r + s by omega]
    rw [Nat.sub_add_cancel (by omega : 1 ≤ r + s)]
    exact Polynomial.monomial_sub (r + s)
  · have hrs : r = 0 ∧ s = 0 := by omega
    rcases hrs with ⟨rfl, rfl⟩
    rw [homogeneousCommutatorQuotient, dite_eq_right (by omega), mul_zero]
    have hab := commutator_eq_zero_of_mem_orderPiece_zero
      k a.property b.property
    apply Subtype.ext
    change (0 : Polynomial (PresentedWeyl k n)) =
      Polynomial.monomial 0 (a : PresentedWeyl k n) *
          Polynomial.monomial 0 (b : PresentedWeyl k n) -
        Polynomial.monomial 0 (b : PresentedWeyl k n) *
          Polynomial.monomial 0 (a : PresentedWeyl k n)
    simp only [Polynomial.monomial_mul_monomial, zero_add,
      ← Polynomial.monomial_sub]
    rw [show (a : PresentedWeyl k n) * b - b * a = 0 by
      simpa [Stafford.commutator, AlgebraicAnalysis.ringCommutator] using hab]
    simp

/-- The homogeneous quotient specializes to the sign-correct negative
Poisson bracket of the two homogeneous principal symbols. -/
theorem specialization_homogeneousCommutatorQuotient
    (r s : ℕ) (a : orderPiece k n r) (b : orderPiece k n s) :
    orderReesSpecialization (n := n) k
        (homogeneousCommutatorQuotient k r s a b) =
      -poissonBracket
        (presentedPrincipalComponent k (@orderWeight n) r a)
        (presentedPrincipalComponent k (@orderWeight n) s b) := by
  by_cases h : 0 < r + s
  · rw [homogeneousCommutatorQuotient, dite_eq_left h,
      orderReesSpecialization_monomial]
    exact principalComponent_commutator_eq_neg_poisson
      k a.property b.property
  · have hrs : r = 0 ∧ s = 0 := by omega
    rcases hrs with ⟨rfl, rfl⟩
    rw [homogeneousCommutatorQuotient, dite_eq_right (by omega), map_zero]
    have hcomm := principalComponent_commutator_eq_neg_poisson
      k a.property b.property
    rw [commutator_eq_zero_of_mem_orderPiece_zero k a.property b.property,
      map_zero] at hcomm
    exact hcomm

/-- Explicit source-level quotient of an arbitrary Rees commutator by `T`.
It is the finite double sum of the homogeneous subprincipal commutators. -/
def orderReesCommutatorQuotient
    (a b : OrderReesRing (n := n) k) : OrderReesRing (n := n) k :=
  ∑ r ∈ (a : Polynomial (PresentedWeyl k n)).support,
    ∑ s ∈ (b : Polynomial (PresentedWeyl k n)).support,
      homogeneousCommutatorQuotient k r s
        ⟨(a : Polynomial (PresentedWeyl k n)).coeff r, a.property r⟩
        ⟨(b : Polynomial (PresentedWeyl k n)).coeff s, b.property s⟩

private theorem orderRees_eq_sum_monomials
    (a : OrderReesRing (n := n) k) :
    a = ∑ r ∈ (a : Polynomial (PresentedWeyl k n)).support,
      orderReesMonomial k r
        ⟨(a : Polynomial (PresentedWeyl k n)).coeff r, a.property r⟩ := by
  apply Subtype.ext
  ext N
  simp [orderReesMonomial, Polynomial.coeff_monomial]

private theorem commutator_finset_sum
    {R S : Type*} (U : Finset R) (V : Finset S)
    (f : R → OrderReesRing (n := n) k)
    (g : S → OrderReesRing (n := n) k) :
    Stafford.commutator (∑ r ∈ U, f r) (∑ s ∈ V, g s) =
      ∑ r ∈ U, ∑ s ∈ V, Stafford.commutator (f r) (g s) := by
  simp only [Stafford.commutator, AlgebraicAnalysis.ringCommutator,
    Finset.sum_mul, Finset.mul_sum,
    Finset.sum_sub_distrib]
  rw [Finset.sum_comm]

/-- The explicit arbitrary witness divides the source commutator by `T`. -/
theorem parameter_mul_orderReesCommutatorQuotient
    (a b : OrderReesRing (n := n) k) :
    orderReesParameter (n := n) k * orderReesCommutatorQuotient k a b =
      Stafford.commutator a b := by
  rw [orderReesCommutatorQuotient, Finset.mul_sum]
  simp_rw [Finset.mul_sum, parameter_mul_homogeneousCommutatorQuotient]
  rw [← commutator_finset_sum]
  rw [← orderRees_eq_sum_monomials k a,
    ← orderRees_eq_sum_monomials k b]

private theorem poissonBracket_finset_sum_left {R : Type*}
    (U : Finset R) (f : R → SymbolRing k n) (g : SymbolRing k n) :
    poissonBracket (∑ r ∈ U, f r) g =
      ∑ r ∈ U, poissonBracket (f r) g := by
  classical
  induction U using Finset.induction_on with
  | empty => simp
  | @insert r U hr ih =>
      rw [Finset.sum_insert hr, Finset.sum_insert hr,
        poissonBracket_add_left, ih]

private theorem poissonBracket_finset_sum_right {S : Type*}
    (V : Finset S) (f : SymbolRing k n) (g : S → SymbolRing k n) :
    poissonBracket f (∑ s ∈ V, g s) =
      ∑ s ∈ V, poissonBracket f (g s) := by
  classical
  induction V using Finset.induction_on with
  | empty => simp
  | @insert s V hs ih =>
      rw [Finset.sum_insert hs, Finset.sum_insert hs,
        poissonBracket_add_right, ih]

private theorem poissonBracket_finset_sum {R S : Type*}
    (U : Finset R) (V : Finset S)
    (f : R → SymbolRing k n) (g : S → SymbolRing k n) :
    poissonBracket (∑ r ∈ U, f r) (∑ s ∈ V, g s) =
      ∑ r ∈ U, ∑ s ∈ V, poissonBracket (f r) (g s) := by
  rw [poissonBracket_finset_sum_left]
  apply Finset.sum_congr rfl
  intro r hr
  exact poissonBracket_finset_sum_right k V (f r) g

private theorem orderReesSpecialization_eq_sum
    (a : OrderReesRing (n := n) k) :
    orderReesSpecialization (n := n) k a =
      ∑ r ∈ (a : Polynomial (PresentedWeyl k n)).support,
        presentedPrincipalComponent k (@orderWeight n) r
          ((a : Polynomial (PresentedWeyl k n)).coeff r) := by
  rfl

/-- The explicit arbitrary quotient specializes to the negative Poisson
bracket of the two Rees specializations. -/
theorem specialization_orderReesCommutatorQuotient
    (a b : OrderReesRing (n := n) k) :
    orderReesSpecialization (n := n) k
        (orderReesCommutatorQuotient k a b) =
      -poissonBracket
        (orderReesSpecialization (n := n) k a)
        (orderReesSpecialization (n := n) k b) := by
  rw [orderReesCommutatorQuotient, map_sum]
  simp_rw [map_sum, specialization_homogeneousCommutatorQuotient]
  change
    (∑ r ∈ (a : Polynomial (PresentedWeyl k n)).support,
      ∑ s ∈ (b : Polynomial (PresentedWeyl k n)).support,
        -poissonBracket
          (presentedPrincipalComponent k (@orderWeight n) r
            ((a : Polynomial (PresentedWeyl k n)).coeff r))
          (presentedPrincipalComponent k (@orderWeight n) s
            ((b : Polynomial (PresentedWeyl k n)).coeff s))) = _
  rw [orderReesSpecialization_eq_sum, orderReesSpecialization_eq_sum]
  simp_rw [Finset.sum_neg_distrib]
  rw [← neg_eq_iff_eq_neg]
  simp only [neg_neg]
  exact (poissonBracket_finset_sum k _ _ _ _).symm

/-- An explicit two-jet witness attached to chosen source lifts. -/
def orderReesTwoJetCommutatorWitness
    (a b : OrderReesRing (n := n) k) : OrderReesTwoJet (n := n) k :=
  orderReesTwoJetQuotient (n := n) k
    (orderReesCommutatorQuotient k a b)

/-- Exact two-jet commutator factorization for chosen Rees lifts. -/
theorem twoJet_commutator_eq_parameter_mul_witness
    (a b : OrderReesRing (n := n) k) :
    Stafford.commutator
        (orderReesTwoJetQuotient (n := n) k a)
        (orderReesTwoJetQuotient (n := n) k b) =
      orderReesTwoJetParameter (n := n) k *
        orderReesTwoJetCommutatorWitness k a b := by
  change orderReesTwoJetQuotient (n := n) k
      (Stafford.commutator a b) =
    orderReesTwoJetQuotient (n := n) k
      (orderReesParameter (n := n) k *
        orderReesCommutatorQuotient k a b)
  exact congrArg (orderReesTwoJetQuotient (n := n) k)
    (parameter_mul_orderReesCommutatorQuotient k a b).symm

/-- The chosen two-jet witness retains the negative-Poisson specialization. -/
theorem twoJet_witness_specialization
    (a b : OrderReesRing (n := n) k) :
    orderReesTwoJetSpecialization (n := n) k
        (orderReesTwoJetCommutatorWitness k a b) =
      -poissonBracket
        (orderReesTwoJetSpecialization (n := n) k
          (orderReesTwoJetQuotient (n := n) k a))
        (orderReesTwoJetSpecialization (n := n) k
          (orderReesTwoJetQuotient (n := n) k b)) := by
  simpa [orderReesTwoJetCommutatorWitness] using
    specialization_orderReesCommutatorQuotient k a b

/-- Every arbitrary two-jet commutator is a parameter multiple, and one may
choose a quotient whose specialization is exactly the negative Poisson bracket
of the specialized inputs. -/
theorem exists_twoJet_commutatorQuotient
    (x y : OrderReesTwoJet (n := n) k) :
    ∃ z : OrderReesTwoJet (n := n) k,
      Stafford.commutator x y =
          orderReesTwoJetParameter (n := n) k * z ∧
        orderReesTwoJetSpecialization (n := n) k z =
          -poissonBracket
            (orderReesTwoJetSpecialization (n := n) k x)
            (orderReesTwoJetSpecialization (n := n) k y) := by
  obtain ⟨a, rfl⟩ := Quotient.mk''_surjective x
  obtain ⟨b, rfl⟩ := Quotient.mk''_surjective y
  exact ⟨orderReesTwoJetCommutatorWitness k a b,
    twoJet_commutator_eq_parameter_mul_witness k a b,
    twoJet_witness_specialization k a b⟩


end

end Stafford38.CharacteristicOrderReesTwoJetBracket
