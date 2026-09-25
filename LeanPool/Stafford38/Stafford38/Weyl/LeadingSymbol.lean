/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Weyl.Filtration
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous


/-!
# Principal components and leading-symbol multiplication

Weighted homogeneous projection of the checked PBW normal form defines the
degree-`N` principal component of a filtered Weyl element. Exact one-pair
normal ordering proves that, for both the Bernstein and differential-order
filtrations, the principal component of a product is the product of the
principal components. No associated graded identification is assumed here.
-/

@[expose] public section

namespace Stafford38.WeylLeadingSymbol

open Stafford38.Characteristic
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylPBW
open Stafford38.WeylFiltration

noncomputable section

universe u

variable (k : Type u) [Field k]

theorem finsupp_weight_eq_monomialWeight {n : ℕ}
    (w : PhaseVar n → ℕ) (m : PhaseVar n →₀ ℕ) :
    Finsupp.weight w m = monomialWeight w m := by
  rfl

/-- The homogeneous component at the declared filtration bound `N`. It is zero
when the element has strictly smaller actual weighted degree. -/
def presentedPrincipalComponent {n : ℕ} (w : PhaseVar n → ℕ) (N : ℕ) :
    PresentedWeyl k n →ₗ[k] SymbolRing k n :=
  (MvPolynomial.weightedHomogeneousComponent w N).comp
    (presentedNormalFormLinearEquiv k n).toLinearMap

theorem coeff_presentedPrincipalComponent {n : ℕ}
    (w : PhaseVar n → ℕ) (N : ℕ) (z : PresentedWeyl k n)
    (m : PhaseVar n →₀ ℕ) :
    (presentedPrincipalComponent k w N z).coeff m =
      if monomialWeight w m = N then
        (presentedNormalFormLinearEquiv k n z).coeff m
      else 0 := by
  rw [presentedPrincipalComponent, LinearMap.comp_apply,
    MvPolynomial.coeff_weightedHomogeneousComponent,
    finsupp_weight_eq_monomialWeight]
  rfl

theorem presentedPrincipalComponent_eq_zero_of_mem_of_lt {n L T : ℕ}
    (w : PhaseVar n → ℕ) (z : PresentedWeyl k n)
    (hz : z ∈ presentedWeightPiece k w L) (hLT : L < T) :
    presentedPrincipalComponent k w T z = 0 := by
  ext m
  rw [coeff_presentedPrincipalComponent]
  by_cases hm : monomialWeight w m = T
  · rw [ite_eq_left hm]
    have hcoeff :
        (presentedNormalFormLinearEquiv k n z).coeff m = 0 := by
      by_contra hne
      have hle := (mem_presentedWeightPiece k w L z).mp hz m hne
      omega
    simp only [hcoeff, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  · simp only [ite_eq_right hm, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]

theorem presentedPrincipalComponent_basis {n : ℕ}
    (w : PhaseVar n → ℕ) (N : ℕ) (m : PhaseVar n →₀ ℕ) :
    presentedPrincipalComponent k w N (presentedPBWBasis k n m) =
      if monomialWeight w m = N then MvPolynomial.monomial m 1 else 0 := by
  classical
  ext q
  rw [coeff_presentedPrincipalComponent,
    presentedNormalFormLinearEquiv_basis]
  by_cases hm : monomialWeight w m = N
  · rw [ite_eq_left hm, MvPolynomial.coeff_monomial]
    by_cases hmq : m = q
    · subst q
      simp [hm]
    · simp [hmq]
  · simp only [ite_eq_right hm, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    by_cases hqm : q = m
    · subst q
      simp [hm]
    · simp [ Ne.symm hqm]

theorem weightedHomogeneousComponent_monomial {n N : ℕ}
    (w : PhaseVar n → ℕ) (m : PhaseVar n →₀ ℕ) (c : k) :
    MvPolynomial.weightedHomogeneousComponent w N
        (MvPolynomial.monomial m c) =
      if monomialWeight w m = N then MvPolynomial.monomial m c else 0 := by
  classical
  ext q
  rw [MvPolynomial.coeff_weightedHomogeneousComponent,
    finsupp_weight_eq_monomialWeight]
  by_cases hm : monomialWeight w m = N
  · rw [ite_eq_left hm, MvPolynomial.coeff_monomial]
    by_cases hmq : m = q
    · subst q
      simp [hm]
    · simp [hmq]
  · simp only [ite_eq_right hm, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    by_cases hqm : q = m
    · subst q
      simp [hm]
    · simp [ Ne.symm hqm]

theorem weightedHomogeneousComponent_rename
    {n r T : ℕ} (wOld : PhaseVar n → ℕ) (wNew : PhaseVar r → ℕ)
    (e : PhaseVar n → PhaseVar r)
    (hweight : ∀ m : PhaseVar n →₀ ℕ,
      monomialWeight wNew (m.mapDomain e) = monomialWeight wOld m)
    (f : SymbolRing k n) :
  MvPolynomial.weightedHomogeneousComponent wNew T
        (MvPolynomial.rename e f) =
      MvPolynomial.rename e
        (MvPolynomial.weightedHomogeneousComponent wOld T f) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial m c =>
    rw [MvPolynomial.rename_monomial,
      weightedHomogeneousComponent_monomial,
      weightedHomogeneousComponent_monomial, hweight]
    by_cases h : monomialWeight wOld m = T
    · simp [h, MvPolynomial.rename_monomial]
    · simp [h]
  | add p q hp hq =>
    simp [map_add, hp, hq]

theorem weightedHomogeneousComponent_monomial_mul {n T : ℕ}
    (w : PhaseVar n → ℕ) (s : PhaseVar n →₀ ℕ)
    (f : SymbolRing k n) :
    MvPolynomial.weightedHomogeneousComponent w
        (T + monomialWeight w s) (MvPolynomial.monomial s 1 * f) =
      MvPolynomial.monomial s 1 *
        MvPolynomial.weightedHomogeneousComponent w T f := by
  classical
  ext q
  rw [MvPolynomial.coeff_weightedHomogeneousComponent,
    MvPolynomial.coeff_monomial_mul',
    MvPolynomial.coeff_monomial_mul']
  by_cases hsq : s ≤ q
  · rw [ite_eq_left hsq, ite_eq_left hsq, one_mul, one_mul,
      MvPolynomial.coeff_weightedHomogeneousComponent]
    have hsplit : s + (q - s) = q := by
      rw [add_comm]
      exact tsub_add_cancel_of_le hsq
    have hweight :
        monomialWeight w q =
          monomialWeight w s + monomialWeight w (q - s) := by
      rw [← hsplit]
      simp [monomialWeight, Finsupp.sum_add_index, add_mul]
    rw [finsupp_weight_eq_monomialWeight,
      finsupp_weight_eq_monomialWeight]
    rw [hweight]
    by_cases hrest : monomialWeight w (q - s) = T
    · simp [hrest, Nat.add_comm]
    · have hne :
          monomialWeight w s + monomialWeight w (q - s) ≠
            T + monomialWeight w s := by
        omega
      simp [hrest, hne]
  · rw [ite_eq_right hsq, ite_eq_right hsq]
    simp

theorem monomialWeight_mapDomain_oldIndex_bernstein (n : ℕ)
    (m : PhaseVar n →₀ ℕ) :
    monomialWeight (@bernsteinWeight (n + 1)) (m.mapDomain oldIndex) =
      monomialWeight (@bernsteinWeight n) m := by
  have h := monomialWeight_extend_bernstein n 0 0 m
  simpa [extendPhaseExponent] using h.symm

theorem monomialWeight_mapDomain_oldIndex_order (n : ℕ)
    (m : PhaseVar n →₀ ℕ) :
    monomialWeight (@orderWeight (n + 1)) (m.mapDomain oldIndex) =
      monomialWeight (@orderWeight n) m := by
  have h := monomialWeight_extend_order n 0 0 m
  simpa [extendPhaseExponent] using h.symm

theorem presentedNormalFormLinearEquiv_previous_ordered_monomial
    (n a p : ℕ) (z : PresentedWeyl k n) :
    presentedNormalFormLinearEquiv k (n + 1)
        (presentedCoefficientOrdered k n a p z) =
      MvPolynomial.monomial (extendPhaseExponent n a p 0) 1 *
        MvPolynomial.rename oldIndex
          (presentedNormalFormLinearEquiv k n z) := by
  rw [presentedNormalFormLinearEquiv_previous_ordered,
    MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.monomial_mul_monomial]
  simp [extendPhaseExponent]

theorem monomialWeight_extend_zero_bernstein (n a p : ℕ) :
    monomialWeight (@bernsteinWeight (n + 1))
        (extendPhaseExponent n a p 0) = a + p := by
  rw [← monomialWeight_extend_bernstein]
  simp [monomialWeight]

theorem monomialWeight_extend_zero_order (n a p : ℕ) :
    monomialWeight (@orderWeight (n + 1))
        (extendPhaseExponent n a p 0) = p := by
  rw [← monomialWeight_extend_order]
  simp [monomialWeight]

theorem presentedPrincipalComponent_coefficientOrdered_bernstein
    (n N a p : ℕ) (z : PresentedWeyl k n) :
    presentedPrincipalComponent k (@bernsteinWeight (n + 1)) (N + a + p)
        (presentedCoefficientOrdered k n a p z) =
      MvPolynomial.monomial (extendPhaseExponent n a p 0) 1 *
        MvPolynomial.rename oldIndex
          (presentedPrincipalComponent k (@bernsteinWeight n) N z) := by
  rw [presentedPrincipalComponent, LinearMap.comp_apply,
    show N + a + p = N + monomialWeight (@bernsteinWeight (n + 1))
        (extendPhaseExponent n a p 0) by
      rw [monomialWeight_extend_zero_bernstein]
      omega]
  change MvPolynomial.weightedHomogeneousComponent
      (@bernsteinWeight (n + 1))
      (N + monomialWeight (@bernsteinWeight (n + 1))
        (extendPhaseExponent n a p 0))
      (presentedNormalFormLinearEquiv k (n + 1)
        (presentedCoefficientOrdered k n a p z)) = _
  rw [presentedNormalFormLinearEquiv_previous_ordered_monomial]
  rw [weightedHomogeneousComponent_monomial_mul,
    weightedHomogeneousComponent_rename
      k (@bernsteinWeight n) (@bernsteinWeight (n + 1)) oldIndex
      (monomialWeight_mapDomain_oldIndex_bernstein n)]
  rfl

theorem presentedPrincipalComponent_coefficientOrdered_order
    (n N a p : ℕ) (z : PresentedWeyl k n) :
    presentedPrincipalComponent k (@orderWeight (n + 1)) (N + p)
        (presentedCoefficientOrdered k n a p z) =
      MvPolynomial.monomial (extendPhaseExponent n a p 0) 1 *
        MvPolynomial.rename oldIndex
          (presentedPrincipalComponent k (@orderWeight n) N z) := by
  rw [presentedPrincipalComponent, LinearMap.comp_apply,
    show N + p = N + monomialWeight (@orderWeight (n + 1))
        (extendPhaseExponent n a p 0) by
      rw [monomialWeight_extend_zero_order]]
  change MvPolynomial.weightedHomogeneousComponent
      (@orderWeight (n + 1))
      (N + monomialWeight (@orderWeight (n + 1))
        (extendPhaseExponent n a p 0))
      (presentedNormalFormLinearEquiv k (n + 1)
        (presentedCoefficientOrdered k n a p z)) = _
  rw [presentedNormalFormLinearEquiv_previous_ordered_monomial]
  rw [weightedHomogeneousComponent_monomial_mul,
    weightedHomogeneousComponent_rename
      k (@orderWeight n) (@orderWeight (n + 1)) oldIndex
      (monomialWeight_mapDomain_oldIndex_order n)]
  rfl

theorem phaseMonomial_succ_product (n : ℕ)
    (a p c q : Fin (n + 1) → ℕ) :
    MvPolynomial.monomial (phaseExponent a p) (1 : k) *
        MvPolynomial.monomial (phaseExponent c q) 1 =
      MvPolynomial.monomial
          (extendPhaseExponent n (a 0 + c 0) (p 0 + q 0) 0) 1 *
        MvPolynomial.rename oldIndex
          (MvPolynomial.monomial
              (phaseExponent (fun i => a i.succ) (fun i => p i.succ)) 1 *
            MvPolynomial.monomial
              (phaseExponent (fun i => c i.succ) (fun i => q i.succ)) 1) := by
  have hexp :
      phaseExponent a p + phaseExponent c q =
        extendPhaseExponent n (a 0 + c 0) (p 0 + q 0) 0 +
          (phaseExponent (fun i => a i.succ) (fun i => p i.succ) +
            phaseExponent (fun i => c i.succ) (fun i => q i.succ)).mapDomain
              oldIndex := by
    rw [phaseExponent_succ_eq_extend, phaseExponent_succ_eq_extend]
    simp? [extendPhaseExponent,  add_assoc, add_comm, add_left_comm]
    rw [Finsupp.mapDomain_add]
  rw [MvPolynomial.monomial_mul_monomial, MvPolynomial.monomial_mul_monomial,
    MvPolynomial.rename_monomial, MvPolynomial.monomial_mul_monomial]
  simp only [one_mul]
  rw [hexp]

theorem presentedOrderedMonomial_mul_principal_bernstein :
    ∀ (n : ℕ) (a p c q : Fin n → ℕ),
      presentedPrincipalComponent k (@bernsteinWeight n)
          (monomialWeight (@bernsteinWeight n) (phaseExponent a p) +
            monomialWeight (@bernsteinWeight n) (phaseExponent c q))
          (presentedOrderedMonomial k n a p *
            presentedOrderedMonomial k n c q) =
        MvPolynomial.monomial (phaseExponent a p) 1 *
          MvPolynomial.monomial (phaseExponent c q) 1 := by
  intro n
  induction n with
  | zero =>
      intro a p c q
      have hap : phaseExponent a p = 0 := by
        ext i
        exact Sum.elim Fin.elim0 Fin.elim0 i
      have hcq : phaseExponent c q = 0 := by
        ext i
        exact Sum.elim Fin.elim0 Fin.elim0 i
      rw [hap, hcq]
      simp [presentedOrderedMonomial, monomialWeight,
        presentedPrincipalComponent, presentedNormalFormLinearEquiv_one]
  | succ n ih =>
      intro a p c q
      let L :=
        monomialWeight (@bernsteinWeight n)
            (phaseExponent (fun i => a i.succ) (fun i => p i.succ)) +
          monomialWeight (@bernsteinWeight n)
            (phaseExponent (fun i => c i.succ) (fun i => q i.succ))
      have htarget :
          monomialWeight (@bernsteinWeight (n + 1)) (phaseExponent a p) +
              monomialWeight (@bernsteinWeight (n + 1)) (phaseExponent c q) =
            L + (a 0 + c 0) + (p 0 + q 0) := by
        rw [monomialWeight_phaseExponent_succ_bernstein,
          monomialWeight_phaseExponent_succ_bernstein]
        simp only [L]
        omega
      rw [htarget]
      change
        presentedPrincipalComponent k (@bernsteinWeight (n + 1))
            (L + (a 0 + c 0) + (p 0 + q 0))
            (presentedCoefficientOrdered k n (a 0) (p 0)
                (presentedOrderedMonomial k n
                  (fun i => a i.succ) (fun i => p i.succ)) *
              presentedCoefficientOrdered k n (c 0) (q 0)
                (presentedOrderedMonomial k n
                  (fun i => c i.succ) (fun i => q i.succ))) = _
      rw [presentedCoefficientOrdered_mul]
      simp only [map_sum]
      rw [Finset.sum_eq_single 0]
      · simp only [Nat.zero_le, ite_true, Nat.choose_zero_right,
          Nat.descFactorial_zero, mul_one, one_nsmul, Nat.sub_zero]
        rw [presentedPrincipalComponent_coefficientOrdered_bernstein]
        have hih := ih
          (fun i => a i.succ) (fun i => p i.succ)
          (fun i => c i.succ) (fun i => q i.succ)
        change presentedPrincipalComponent k (@bernsteinWeight n) L
            (presentedOrderedMonomial k n
                (fun i => a i.succ) (fun i => p i.succ) *
              presentedOrderedMonomial k n
                (fun i => c i.succ) (fun i => q i.succ)) = _ at hih
        rw [hih]
        exact (phaseMonomial_succ_product k n a p c q).symm
      · intro i hi hi0
        have hib : i ≤ p 0 := by
          have := Finset.mem_range.mp hi
          omega
        by_cases hic : i ≤ c 0
        · simp only [ite_eq_left hic]
          have hold :
              presentedOrderedMonomial k n
                    (fun j => a j.succ) (fun j => p j.succ) *
                  presentedOrderedMonomial k n
                    (fun j => c j.succ) (fun j => q j.succ) ∈
                bernsteinPiece k n L := by
            simpa [L] using
              presentedOrderedMonomial_mul_mem_bernsteinPiece k n
                (fun j => a j.succ) (fun j => p j.succ)
                (fun j => c j.succ) (fun j => q j.succ)
          have hterm := presentedCoefficientOrdered_mem_bernsteinPiece k n L
            (a 0 + c 0 - i) (p 0 + q 0 - i)
            (presentedOrderedMonomial k n
                (fun j => a j.succ) (fun j => p j.succ) *
              presentedOrderedMonomial k n
                (fun j => c j.succ) (fun j => q j.succ)) hold
          have hlt :
              L + (a 0 + c 0 - i) + (p 0 + q 0 - i) <
                L + (a 0 + c 0) + (p 0 + q 0) := by
            omega
          have hz := presentedPrincipalComponent_eq_zero_of_mem_of_lt k
            (@bernsteinWeight (n + 1)) _ hterm hlt
          rw [map_nsmul, hz, nsmul_zero]
        · simp [hic]
      · simp

theorem presentedOrderedMonomial_mul_principal_order :
    ∀ (n : ℕ) (a p c q : Fin n → ℕ),
      presentedPrincipalComponent k (@orderWeight n)
          (monomialWeight (@orderWeight n) (phaseExponent a p) +
            monomialWeight (@orderWeight n) (phaseExponent c q))
          (presentedOrderedMonomial k n a p *
            presentedOrderedMonomial k n c q) =
        MvPolynomial.monomial (phaseExponent a p) 1 *
          MvPolynomial.monomial (phaseExponent c q) 1 := by
  intro n
  induction n with
  | zero =>
      intro a p c q
      have hap : phaseExponent a p = 0 := by
        ext i
        exact Sum.elim Fin.elim0 Fin.elim0 i
      have hcq : phaseExponent c q = 0 := by
        ext i
        exact Sum.elim Fin.elim0 Fin.elim0 i
      rw [hap, hcq]
      simp [presentedOrderedMonomial, monomialWeight,
        presentedPrincipalComponent, presentedNormalFormLinearEquiv_one]
  | succ n ih =>
      intro a p c q
      let L :=
        monomialWeight (@orderWeight n)
            (phaseExponent (fun i => a i.succ) (fun i => p i.succ)) +
          monomialWeight (@orderWeight n)
            (phaseExponent (fun i => c i.succ) (fun i => q i.succ))
      have htarget :
          monomialWeight (@orderWeight (n + 1)) (phaseExponent a p) +
              monomialWeight (@orderWeight (n + 1)) (phaseExponent c q) =
            L + (p 0 + q 0) := by
        rw [monomialWeight_phaseExponent_succ_order,
          monomialWeight_phaseExponent_succ_order]
        simp only [L]
        omega
      rw [htarget]
      change
        presentedPrincipalComponent k (@orderWeight (n + 1))
            (L + (p 0 + q 0))
            (presentedCoefficientOrdered k n (a 0) (p 0)
                (presentedOrderedMonomial k n
                  (fun i => a i.succ) (fun i => p i.succ)) *
              presentedCoefficientOrdered k n (c 0) (q 0)
                (presentedOrderedMonomial k n
                  (fun i => c i.succ) (fun i => q i.succ))) = _
      rw [presentedCoefficientOrdered_mul]
      simp only [map_sum]
      rw [Finset.sum_eq_single 0]
      · simp only [Nat.zero_le, ite_true, Nat.choose_zero_right,
          Nat.descFactorial_zero, mul_one, one_nsmul, Nat.sub_zero]
        rw [presentedPrincipalComponent_coefficientOrdered_order]
        have hih := ih
          (fun i => a i.succ) (fun i => p i.succ)
          (fun i => c i.succ) (fun i => q i.succ)
        change presentedPrincipalComponent k (@orderWeight n) L
            (presentedOrderedMonomial k n
                (fun i => a i.succ) (fun i => p i.succ) *
              presentedOrderedMonomial k n
                (fun i => c i.succ) (fun i => q i.succ)) = _ at hih
        rw [hih]
        exact (phaseMonomial_succ_product k n a p c q).symm
      · intro i hi hi0
        have hib : i ≤ p 0 := by
          have := Finset.mem_range.mp hi
          omega
        by_cases hic : i ≤ c 0
        · simp only [ite_eq_left hic]
          have hold :
              presentedOrderedMonomial k n
                    (fun j => a j.succ) (fun j => p j.succ) *
                  presentedOrderedMonomial k n
                    (fun j => c j.succ) (fun j => q j.succ) ∈
                orderPiece k n L := by
            simpa [L] using
              presentedOrderedMonomial_mul_mem_orderPiece k n
                (fun j => a j.succ) (fun j => p j.succ)
                (fun j => c j.succ) (fun j => q j.succ)
          have hterm := presentedCoefficientOrdered_mem_orderPiece k n L
            (a 0 + c 0 - i) (p 0 + q 0 - i)
            (presentedOrderedMonomial k n
                (fun j => a j.succ) (fun j => p j.succ) *
              presentedOrderedMonomial k n
                (fun j => c j.succ) (fun j => q j.succ)) hold
          have hlt :
              L + (p 0 + q 0 - i) < L + (p 0 + q 0) := by
            omega
          have hz := presentedPrincipalComponent_eq_zero_of_mem_of_lt k
            (@orderWeight (n + 1)) _ hterm hlt
          rw [map_nsmul, hz, nsmul_zero]
        · simp [hic]
      · simp

theorem presentedPBWBasis_mul_principal_bernstein {n : ℕ}
    (m r : PhaseVar n →₀ ℕ) :
    presentedPrincipalComponent k (@bernsteinWeight n)
        (monomialWeight (@bernsteinWeight n) m +
          monomialWeight (@bernsteinWeight n) r)
        (presentedPBWBasis k n m * presentedPBWBasis k n r) =
      MvPolynomial.monomial m 1 * MvPolynomial.monomial r 1 := by
  rw [presentedPBWBasis_apply, presentedPBWBasis_apply,
    ← phaseExponent_split m, ← phaseExponent_split r]
  exact presentedOrderedMonomial_mul_principal_bernstein k n
    (fun i => m (.inl i)) (fun i => m (.inr i))
    (fun i => r (.inl i)) (fun i => r (.inr i))

theorem presentedPBWBasis_mul_principal_order {n : ℕ}
    (m r : PhaseVar n →₀ ℕ) :
    presentedPrincipalComponent k (@orderWeight n)
        (monomialWeight (@orderWeight n) m +
          monomialWeight (@orderWeight n) r)
        (presentedPBWBasis k n m * presentedPBWBasis k n r) =
      MvPolynomial.monomial m 1 * MvPolynomial.monomial r 1 := by
  rw [presentedPBWBasis_apply, presentedPBWBasis_apply,
    ← phaseExponent_split m, ← phaseExponent_split r]
  exact presentedOrderedMonomial_mul_principal_order k n
    (fun i => m (.inl i)) (fun i => m (.inr i))
    (fun i => r (.inl i)) (fun i => r (.inr i))

theorem presentedPrincipalComponent_mul_bernstein
    {n N M : ℕ} {x y : PresentedWeyl k n}
    (hx : x ∈ bernsteinPiece k n N) (hy : y ∈ bernsteinPiece k n M) :
    presentedPrincipalComponent k (@bernsteinWeight n) (N + M) (x * y) =
      presentedPrincipalComponent k (@bernsteinWeight n) N x *
        presentedPrincipalComponent k (@bernsteinWeight n) M y := by
  rw [bernsteinPiece, presentedWeightPiece_eq_span] at hx hy
  apply Submodule.span_induction₂
      (p := fun x y _ _ =>
        presentedPrincipalComponent k (@bernsteinWeight n) (N + M) (x * y) =
          presentedPrincipalComponent k (@bernsteinWeight n) N x *
            presentedPrincipalComponent k (@bernsteinWeight n) M y)
      (ha := hx) (hb := hy)
  · intro bx bz hbx hbz
    obtain ⟨m, hm, rfl⟩ := hbx
    obtain ⟨r, hr, rfl⟩ := hbz
    by_cases hmN : monomialWeight (@bernsteinWeight n) m = N
    · by_cases hrM : monomialWeight (@bernsteinWeight n) r = M
      · rw [← hmN, ← hrM,
          presentedPBWBasis_mul_principal_bernstein,
          presentedPrincipalComponent_basis,
          presentedPrincipalComponent_basis]
        simp
      · have hrlt : monomialWeight (@bernsteinWeight n) r < M :=
          lt_of_le_of_ne hr hrM
        have hprod :
            presentedPBWBasis k n m * presentedPBWBasis k n r ∈
              bernsteinPiece k n
                (monomialWeight (@bernsteinWeight n) m +
                  monomialWeight (@bernsteinWeight n) r) := by
          rw [presentedPBWBasis_apply, presentedPBWBasis_apply]
          simpa [phaseExponent_split] using
            presentedOrderedMonomial_mul_mem_bernsteinPiece k n
              (fun i => m (.inl i)) (fun i => m (.inr i))
              (fun i => r (.inl i)) (fun i => r (.inr i))
        have hlt :
            monomialWeight (@bernsteinWeight n) m +
                monomialWeight (@bernsteinWeight n) r < N + M := by
          omega
        rw [presentedPrincipalComponent_eq_zero_of_mem_of_lt k
            (@bernsteinWeight n) _ hprod hlt,
          presentedPrincipalComponent_basis,
          presentedPrincipalComponent_basis]
        simp [hrM]
    · have hmlt : monomialWeight (@bernsteinWeight n) m < N :=
        lt_of_le_of_ne hm hmN
      have hprod :
          presentedPBWBasis k n m * presentedPBWBasis k n r ∈
            bernsteinPiece k n
              (monomialWeight (@bernsteinWeight n) m +
                monomialWeight (@bernsteinWeight n) r) := by
        rw [presentedPBWBasis_apply, presentedPBWBasis_apply]
        simpa [phaseExponent_split] using
          presentedOrderedMonomial_mul_mem_bernsteinPiece k n
            (fun i => m (.inl i)) (fun i => m (.inr i))
            (fun i => r (.inl i)) (fun i => r (.inr i))
      have hlt :
          monomialWeight (@bernsteinWeight n) m +
              monomialWeight (@bernsteinWeight n) r < N + M := by
        omega
      rw [presentedPrincipalComponent_eq_zero_of_mem_of_lt k
          (@bernsteinWeight n) _ hprod hlt,
        presentedPrincipalComponent_basis,
        presentedPrincipalComponent_basis]
      simp [hmN]
  · intro y hy
    simp
  · intro x hx
    simp
  · intro x y z hx hy hz hxy hyz
    simp only [add_mul, map_add, hxy, hyz]
  · intro x y z hx hy hz hxy hxz
    simp only [mul_add, map_add, hxy, hxz]
  · intro c x y hx hy hxy
    simp only [Algebra.smul_mul_assoc, map_smul, hxy]
  · intro c x y hx hy hxy
    simp only [Algebra.mul_smul_comm, map_smul, hxy]

theorem presentedPrincipalComponent_mul_order
    {n N M : ℕ} {x y : PresentedWeyl k n}
    (hx : x ∈ orderPiece k n N) (hy : y ∈ orderPiece k n M) :
    presentedPrincipalComponent k (@orderWeight n) (N + M) (x * y) =
      presentedPrincipalComponent k (@orderWeight n) N x *
        presentedPrincipalComponent k (@orderWeight n) M y := by
  rw [orderPiece, presentedWeightPiece_eq_span] at hx hy
  apply Submodule.span_induction₂
      (p := fun x y _ _ =>
        presentedPrincipalComponent k (@orderWeight n) (N + M) (x * y) =
          presentedPrincipalComponent k (@orderWeight n) N x *
            presentedPrincipalComponent k (@orderWeight n) M y)
      (ha := hx) (hb := hy)
  · intro bx bz hbx hbz
    obtain ⟨m, hm, rfl⟩ := hbx
    obtain ⟨r, hr, rfl⟩ := hbz
    by_cases hmN : monomialWeight (@orderWeight n) m = N
    · by_cases hrM : monomialWeight (@orderWeight n) r = M
      · rw [← hmN, ← hrM,
          presentedPBWBasis_mul_principal_order,
          presentedPrincipalComponent_basis,
          presentedPrincipalComponent_basis]
        simp
      · have hrlt : monomialWeight (@orderWeight n) r < M :=
          lt_of_le_of_ne hr hrM
        have hprod :
            presentedPBWBasis k n m * presentedPBWBasis k n r ∈
              orderPiece k n
                (monomialWeight (@orderWeight n) m +
                  monomialWeight (@orderWeight n) r) := by
          rw [presentedPBWBasis_apply, presentedPBWBasis_apply]
          simpa [phaseExponent_split] using
            presentedOrderedMonomial_mul_mem_orderPiece k n
              (fun i => m (.inl i)) (fun i => m (.inr i))
              (fun i => r (.inl i)) (fun i => r (.inr i))
        have hlt :
            monomialWeight (@orderWeight n) m +
                monomialWeight (@orderWeight n) r < N + M := by
          omega
        rw [presentedPrincipalComponent_eq_zero_of_mem_of_lt k
            (@orderWeight n) _ hprod hlt,
          presentedPrincipalComponent_basis,
          presentedPrincipalComponent_basis]
        simp [hrM]
    · have hmlt : monomialWeight (@orderWeight n) m < N :=
          lt_of_le_of_ne hm hmN
      have hprod :
          presentedPBWBasis k n m * presentedPBWBasis k n r ∈
            orderPiece k n
              (monomialWeight (@orderWeight n) m +
                monomialWeight (@orderWeight n) r) := by
        rw [presentedPBWBasis_apply, presentedPBWBasis_apply]
        simpa [phaseExponent_split] using
          presentedOrderedMonomial_mul_mem_orderPiece k n
            (fun i => m (.inl i)) (fun i => m (.inr i))
            (fun i => r (.inl i)) (fun i => r (.inr i))
      have hlt :
          monomialWeight (@orderWeight n) m +
              monomialWeight (@orderWeight n) r < N + M := by
        omega
      rw [presentedPrincipalComponent_eq_zero_of_mem_of_lt k
          (@orderWeight n) _ hprod hlt,
        presentedPrincipalComponent_basis,
        presentedPrincipalComponent_basis]
      simp [hmN]
  · intro y hy
    simp
  · intro x hx
    simp
  · intro x y z hx hy hz hxy hyz
    simp only [add_mul, map_add, hxy, hyz]
  · intro x y z hx hy hz hxy hxz
    simp only [mul_add, map_add, hxy, hxz]
  · intro c x y hx hy hxy
    simp only [Algebra.smul_mul_assoc, map_smul, hxy]
  · intro c x y hx hy hxy
    simp only [Algebra.mul_smul_comm, map_smul, hxy]


end

end Stafford38.WeylLeadingSymbol
