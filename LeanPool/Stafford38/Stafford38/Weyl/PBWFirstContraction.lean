/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Weyl.FilteredCommutator


/-!
# The first PBW contraction

This file extracts the degree-one contraction term from the recursive ordered
PBW multiplication formula.  It is kept separate from the downstream
commutator argument so that the one-sided normal-ordering calculation is an
independent input.
-/

@[expose] public section

namespace Stafford38.WeylPBWFirstContraction

open Stafford38.Characteristic
open Stafford38.WeylFilteredCommutator
open Stafford38.WeylFiltration
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylLeadingSymbol
open Stafford38.WeylPBW

noncomputable section

universe u

variable (k : Type u) [Field k]

private theorem weightedHomogeneousComponent_monomial_mul_eq_zero_of_lt
    {n T : ℕ} (w : PhaseVar n → ℕ) (s : PhaseVar n →₀ ℕ)
    (f : SymbolRing k n) (hT : T < monomialWeight w s) :
    MvPolynomial.weightedHomogeneousComponent w T
        (MvPolynomial.monomial s 1 * f) = 0 := by
  classical
  ext q
  rw [MvPolynomial.coeff_weightedHomogeneousComponent,
    MvPolynomial.coeff_monomial_mul', AddMonoidAlgebra.coeff_zero]
  by_cases hsq : s ≤ q
  · rw [ite_eq_left hsq, one_mul]
    have hsplit : s + (q - s) = q := by
      rw [add_comm]
      exact tsub_add_cancel_of_le hsq
    have hweight :
        monomialWeight w q =
          monomialWeight w s + monomialWeight w (q - s) := by
      rw [← hsplit]
      simp [monomialWeight, Finsupp.sum_add_index, add_mul]
    have hne : monomialWeight w q ≠ T := by omega
    rw [finsupp_weight_eq_monomialWeight, ite_eq_right hne, Finsupp.zero_apply]
  · rw [ite_eq_right hsq]
    simp

private theorem phaseExponent_old_contraction_exponents
    (n : ℕ) (a p c q : Fin (n + 1) → ℕ) (i : Fin n) :
    (phaseExponent a p -
          Finsupp.single (.inr i.succ : PhaseVar (n + 1)) 1) +
        (phaseExponent c q -
          Finsupp.single (.inl i.succ : PhaseVar (n + 1)) 1) =
      extendPhaseExponent n (a 0 + c 0) (p 0 + q 0) 0 +
        (((phaseExponent (fun j => a j.succ) (fun j => p j.succ) -
              Finsupp.single (.inr i : PhaseVar n) 1) +
            (phaseExponent (fun j => c j.succ) (fun j => q j.succ) -
              Finsupp.single (.inl i : PhaseVar n) 1)).mapDomain oldIndex) := by
  classical
  have hmapCoordinate (s : PhaseVar n →₀ ℕ) (j : Fin n) :
      Finsupp.mapDomain oldIndex s (.inl j.succ) = s (.inl j) := by
    change Finsupp.mapDomain oldIndex s (oldIndex (.inl j)) = _
    rw [Finsupp.mapDomain_apply_of_injective oldIndex_injective]
  have hmapMomentum (s : PhaseVar n →₀ ℕ) (j : Fin n) :
      Finsupp.mapDomain oldIndex s (.inr j.succ) = s (.inr j) := by
    change Finsupp.mapDomain oldIndex s (oldIndex (.inr j)) = _
    rw [Finsupp.mapDomain_apply_of_injective oldIndex_injective]
  have hmapCoordinateZero (s : PhaseVar n →₀ ℕ) :
      Finsupp.mapDomain oldIndex s (.inl (0 : Fin (n + 1))) = 0 := by
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨v, hv⟩
    cases v <;> simp [oldIndex, Fin.succ_ne_zero] at hv
  have hmapMomentumZero (s : PhaseVar n →₀ ℕ) :
      Finsupp.mapDomain oldIndex s (.inr (0 : Fin (n + 1))) = 0 := by
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨v, hv⟩
    cases v <;> simp [oldIndex, Fin.succ_ne_zero] at hv
  ext v
  rcases v with v | v
  · refine Fin.cases ?_ (fun j => ?_) v
    · simp [phaseExponent, extendPhaseExponent, oldIndex,
         Fin.succ_ne_zero, hmapCoordinateZero]
    · have hzero : (0 : Fin (n + 1)) ≠ j.succ :=
        Ne.symm (Fin.succ_ne_zero j)
      simp [phaseExponent, extendPhaseExponent, oldIndex,
        Finsupp.single_apply, Fin.succ_ne_zero,  hmapCoordinate]
  · refine Fin.cases ?_ (fun j => ?_) v
    · simp [phaseExponent, extendPhaseExponent, oldIndex,
         Fin.succ_ne_zero, hmapMomentumZero]
    · have hzero : (0 : Fin (n + 1)) ≠ j.succ :=
        Ne.symm (Fin.succ_ne_zero j)
      simp [phaseExponent, extendPhaseExponent, oldIndex,
        Finsupp.single_apply, Fin.succ_ne_zero,  hmapMomentum]

private theorem firstContraction_old_term
    (n : ℕ) (a p c q : Fin (n + 1) → ℕ) (i : Fin n) :
    MvPolynomial.pderiv (.inr i.succ)
          (MvPolynomial.monomial (phaseExponent a p) (1 : k)) *
        MvPolynomial.pderiv (.inl i.succ)
          (MvPolynomial.monomial (phaseExponent c q) 1) =
      MvPolynomial.monomial
          (extendPhaseExponent n (a 0 + c 0) (p 0 + q 0) 0) 1 *
        MvPolynomial.rename oldIndex
          (MvPolynomial.pderiv (.inr i)
              (MvPolynomial.monomial
                (phaseExponent (fun j => a j.succ) (fun j => p j.succ)) 1) *
            MvPolynomial.pderiv (.inl i)
              (MvPolynomial.monomial
                (phaseExponent (fun j => c j.succ) (fun j => q j.succ)) 1)) := by
  classical
  simp only [MvPolynomial.pderiv_monomial,
    MvPolynomial.monomial_mul_monomial, MvPolynomial.rename_monomial]
  rw [phaseExponent_old_contraction_exponents n a p c q i]
  simp [phaseExponent]

private theorem phaseExponent_newest_contraction_exponents
    (n : ℕ) (a p c q : Fin (n + 1) → ℕ)
    (hp : 0 < p 0) (hc : 0 < c 0) :
    (phaseExponent a p -
          Finsupp.single (.inr (0 : Fin (n + 1))) 1) +
        (phaseExponent c q -
          Finsupp.single (.inl (0 : Fin (n + 1))) 1) =
      extendPhaseExponent n (a 0 + c 0 - 1) (p 0 + q 0 - 1) 0 +
        (phaseExponent (fun j => a j.succ) (fun j => p j.succ) +
          phaseExponent (fun j => c j.succ) (fun j => q j.succ)).mapDomain
            oldIndex := by
  classical
  rw [phaseExponent_succ_eq_extend, phaseExponent_succ_eq_extend]
  ext v
  rcases v with v | v
  · refine Fin.cases ?_ (fun j => ?_) v
    · have hmap (s : PhaseVar n →₀ ℕ) :
          Finsupp.mapDomain oldIndex s (.inl (0 : Fin (n + 1))) = 0 := by
        apply Finsupp.mapDomain_of_notMem_range
        rintro ⟨w, hw⟩
        cases w <;> simp [oldIndex, Fin.succ_ne_zero] at hw
      simp [extendPhaseExponent,  hmap]
      omega
    · have hmap (s : PhaseVar n →₀ ℕ) :
          Finsupp.mapDomain oldIndex s (.inl j.succ) = s (.inl j) := by
        change Finsupp.mapDomain oldIndex s (oldIndex (.inl j)) = _
        rw [Finsupp.mapDomain_apply_of_injective oldIndex_injective]
      have hzero : (0 : Fin (n + 1)) ≠ j.succ :=
        Ne.symm (Fin.succ_ne_zero j)
      simp [extendPhaseExponent, phaseExponent,
        hmap,  Fin.succ_ne_zero]
  · refine Fin.cases ?_ (fun j => ?_) v
    · have hmap (s : PhaseVar n →₀ ℕ) :
          Finsupp.mapDomain oldIndex s (.inr (0 : Fin (n + 1))) = 0 := by
        apply Finsupp.mapDomain_of_notMem_range
        rintro ⟨w, hw⟩
        cases w <;> simp [oldIndex, Fin.succ_ne_zero] at hw
      simp [extendPhaseExponent,  hmap]
      omega
    · have hmap (s : PhaseVar n →₀ ℕ) :
          Finsupp.mapDomain oldIndex s (.inr j.succ) = s (.inr j) := by
        change Finsupp.mapDomain oldIndex s (oldIndex (.inr j)) = _
        rw [Finsupp.mapDomain_apply_of_injective oldIndex_injective]
      have hzero : (0 : Fin (n + 1)) ≠ j.succ :=
        Ne.symm (Fin.succ_ne_zero j)
      simp [extendPhaseExponent, phaseExponent,
        hmap,  Fin.succ_ne_zero]

private theorem firstContraction_newest_term
    (n : ℕ) (a p c q : Fin (n + 1) → ℕ)
    (hp : 0 < p 0) (hc : 0 < c 0) :
    ((p 0).choose 1 * (c 0).descFactorial 1) •
        (MvPolynomial.monomial
            (extendPhaseExponent n (a 0 + c 0 - 1)
              (p 0 + q 0 - 1) 0) (1 : k) *
          MvPolynomial.rename oldIndex
            (MvPolynomial.monomial
                (phaseExponent (fun i => a i.succ) (fun i => p i.succ)) 1 *
              MvPolynomial.monomial
                (phaseExponent (fun i => c i.succ) (fun i => q i.succ)) 1)) =
      MvPolynomial.pderiv (.inr (0 : Fin (n + 1)))
          (MvPolynomial.monomial (phaseExponent a p) 1) *
        MvPolynomial.pderiv (.inl (0 : Fin (n + 1)))
          (MvPolynomial.monomial (phaseExponent c q) 1) := by
  classical
  simp only [MvPolynomial.pderiv_monomial,
    MvPolynomial.monomial_mul_monomial, MvPolynomial.rename_monomial]
  rw [phaseExponent_newest_contraction_exponents n a p c q hp hc]
  simp only [Nat.choose_one_right, Nat.descFactorial, tsub_zero, mul_one, phaseExponent,
    nsmul_eq_mul, Nat.cast_mul, Finsupp.equivFunOnFinite_symm_apply_apply, Sum.elim_inr, one_mul,
    Sum.elim_inl]
  rw [← map_natCast
      (MvPolynomial.C : k →+* SymbolRing k (n + 1)) (p 0),
    ← map_natCast
      (MvPolynomial.C : k →+* SymbolRing k (n + 1)) (c 0),
    ← map_mul, MvPolynomial.C_mul_monomial, mul_one]

/-- Splitting off the newest pair decomposes the first contraction into its
newest-pair term and the renamed first contraction in the older pairs. -/
theorem pbwFirstContraction_phaseExponent_succ
    (n : ℕ) (a p c q : Fin (n + 1) → ℕ) :
    pbwFirstContraction k (phaseExponent a p) (phaseExponent c q) =
      MvPolynomial.pderiv (.inr (0 : Fin (n + 1)))
          (MvPolynomial.monomial (phaseExponent a p) 1) *
        MvPolynomial.pderiv (.inl (0 : Fin (n + 1)))
          (MvPolynomial.monomial (phaseExponent c q) 1) +
      MvPolynomial.monomial
          (extendPhaseExponent n (a 0 + c 0) (p 0 + q 0) 0) 1 *
        MvPolynomial.rename oldIndex
          (pbwFirstContraction k
            (phaseExponent (fun i => a i.succ) (fun i => p i.succ))
            (phaseExponent (fun i => c i.succ) (fun i => q i.succ))) := by
  simp only [pbwFirstContraction, Fin.sum_univ_succ, map_sum, Finset.mul_sum]
  refine congrArg₂ (· + ·) rfl ?_
  apply Finset.sum_congr rfl
  intro i hi
  exact firstContraction_old_term k n a p c q i

/-- For ordered monomials of positive total differential order, the component
one below the top order of their product is exactly the one-contraction term. -/
theorem presentedOrderedMonomial_mul_firstContraction :
    ∀ (n : ℕ) (a p c q : Fin n → ℕ),
      0 < monomialWeight (@orderWeight n) (phaseExponent a p) +
          monomialWeight (@orderWeight n) (phaseExponent c q) →
      presentedPrincipalComponent k (@orderWeight n)
          (monomialWeight (@orderWeight n) (phaseExponent a p) +
            monomialWeight (@orderWeight n) (phaseExponent c q) - 1)
          (presentedOrderedMonomial k n a p *
            presentedOrderedMonomial k n c q) =
        pbwFirstContraction k (phaseExponent a p) (phaseExponent c q) := by
  intro n
  induction n with
  | zero =>
      intro a p c q hpos
      have hap : phaseExponent a p = 0 := by
        ext i
        exact Sum.elim Fin.elim0 Fin.elim0 i
      have hcq : phaseExponent c q = 0 := by
        ext i
        exact Sum.elim Fin.elim0 Fin.elim0 i
      rw [hap, hcq] at hpos
      simp [monomialWeight] at hpos
  | succ n ih =>
      intro a p c q hpos
      let mold :=
        phaseExponent (fun i => a i.succ) (fun i => p i.succ)
      let qold :=
        phaseExponent (fun i => c i.succ) (fun i => q i.succ)
      let z :=
        presentedOrderedMonomial k n (fun i => a i.succ) (fun i => p i.succ) *
          presentedOrderedMonomial k n (fun i => c i.succ) (fun i => q i.succ)
      let L := monomialWeight (@orderWeight n) mold +
        monomialWeight (@orderWeight n) qold
      let t := p 0 + q 0
      have htarget :
          monomialWeight (@orderWeight (n + 1)) (phaseExponent a p) +
              monomialWeight (@orderWeight (n + 1)) (phaseExponent c q) =
            L + t := by
        rw [monomialWeight_phaseExponent_succ_order,
          monomialWeight_phaseExponent_succ_order]
        dsimp [L, t, mold, qold]
        omega
      have htotal : 0 < L + t := by
        rwa [htarget] at hpos
      have hzOrder : z ∈ orderPiece k n L := by
        dsimp [z, L, mold, qold]
        exact presentedOrderedMonomial_mul_mem_orderPiece k n
          (fun i => a i.succ) (fun i => p i.succ)
          (fun i => c i.succ) (fun i => q i.succ)
      have hzeroTerm :
          presentedPrincipalComponent k (@orderWeight (n + 1)) (L + t - 1)
              (presentedCoefficientOrdered k n (a 0 + c 0) t z) =
            MvPolynomial.monomial
                (extendPhaseExponent n (a 0 + c 0) t 0) 1 *
              MvPolynomial.rename oldIndex
                (pbwFirstContraction k mold qold) := by
        by_cases hL : L = 0
        · have ht : 0 < t := by omega
          have hvanish :
              presentedPrincipalComponent k (@orderWeight (n + 1))
                  (L + t - 1)
                  (presentedCoefficientOrdered k n (a 0 + c 0) t z) = 0 := by
            rw [presentedPrincipalComponent, LinearMap.comp_apply]
            change MvPolynomial.weightedHomogeneousComponent
                (@orderWeight (n + 1)) (L + t - 1)
                (presentedNormalFormLinearEquiv k (n + 1)
                  (presentedCoefficientOrdered k n (a 0 + c 0) t z)) = 0
            rw [presentedNormalFormLinearEquiv_previous_ordered_monomial]
            apply weightedHomogeneousComponent_monomial_mul_eq_zero_of_lt k
            rw [monomialWeight_extend_zero_order]
            omega
          have hmold : monomialWeight (@orderWeight n) mold = 0 := by
            dsimp [L] at hL
            omega
          rw [hvanish,
            pbwFirstContraction_eq_zero_of_orderWeight_eq_zero
              k mold qold hmold, map_zero, mul_zero]
        · have hLpos : 0 < L := Nat.pos_of_ne_zero hL
          have hih := ih
            (fun i => a i.succ) (fun i => p i.succ)
            (fun i => c i.succ) (fun i => q i.succ) hLpos
          change presentedPrincipalComponent k (@orderWeight n) (L - 1) z =
              pbwFirstContraction k mold qold at hih
          rw [show L + t - 1 = (L - 1) + t by omega,
            presentedPrincipalComponent_coefficientOrdered_order, hih]
      rw [htarget]
      change presentedPrincipalComponent k (@orderWeight (n + 1)) (L + t - 1)
          (presentedCoefficientOrdered k n (a 0) (p 0)
              (presentedOrderedMonomial k n
                (fun i => a i.succ) (fun i => p i.succ)) *
            presentedCoefficientOrdered k n (c 0) (q 0)
              (presentedOrderedMonomial k n
                (fun i => c i.succ) (fun i => q i.succ))) = _
      rw [presentedCoefficientOrdered_mul]
      simp only [map_sum]
      have hmem0 : 0 ∈ Finset.range (p 0 + 1) := by simp
      rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hmem0]
      simp only [Nat.zero_le, ite_true, Nat.choose_zero_right,
        Nat.descFactorial_zero, mul_one, one_nsmul, Nat.sub_zero]
      change presentedPrincipalComponent k (@orderWeight (n + 1)) (L + t - 1)
            (presentedCoefficientOrdered k n (a 0 + c 0) t z) + _ = _
      rw [hzeroTerm]
      rw [pbwFirstContraction_phaseExponent_succ]
      by_cases hp0 : p 0 = 0
      · have hempty : Finset.range (p 0 + 1) \ {0} = ∅ := by
          ext i
          simp [hp0]
        rw [hempty]
        simp [MvPolynomial.pderiv_monomial, phaseExponent, hp0,
          t, mold, qold]
      · have hp : 0 < p 0 := Nat.pos_of_ne_zero hp0
        by_cases hc0 : c 0 = 0
        · have hrest :
              ∑ i ∈ Finset.range (p 0 + 1) \ {0},
                  presentedPrincipalComponent k (@orderWeight (n + 1))
                    (L + t - 1)
                    (if i ≤ c 0 then
                      ((p 0).choose i * (c 0).descFactorial i) •
                        presentedCoefficientOrdered k n
                          (a 0 + c 0 - i) (p 0 + q 0 - i) z
                    else 0) = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            have hi' := Finset.mem_sdiff.mp hi
            have hi0 : i ≠ 0 := by simpa using hi'.2
            have hnot : ¬ i ≤ c 0 := by omega
            simp [hnot]
          rw [hrest]
          simp [MvPolynomial.pderiv_monomial, phaseExponent, hc0,
            t, mold, qold]
        · have hc : 0 < c 0 := Nat.pos_of_ne_zero hc0
          have honeMem : 1 ∈ Finset.range (p 0 + 1) \ {0} := by
            simp [hp]
          have hone :
              presentedPrincipalComponent k (@orderWeight (n + 1))
                (L + t - 1)
                (((p 0).choose 1 * (c 0).descFactorial 1) •
                  presentedCoefficientOrdered k n
                    (a 0 + c 0 - 1) (p 0 + q 0 - 1) z) =
              MvPolynomial.pderiv (.inr (0 : Fin (n + 1)))
                    (MvPolynomial.monomial (phaseExponent a p) 1) *
                MvPolynomial.pderiv (.inl (0 : Fin (n + 1)))
                    (MvPolynomial.monomial (phaseExponent c q) 1) := by
            simp only [map_nsmul]
            rw [show L + t - 1 = L + (p 0 + q 0 - 1) by omega,
              presentedPrincipalComponent_coefficientOrdered_order]
            have htop := presentedOrderedMonomial_mul_principal_order k n
              (fun i => a i.succ) (fun i => p i.succ)
              (fun i => c i.succ) (fun i => q i.succ)
            change presentedPrincipalComponent k (@orderWeight n) L z =
                MvPolynomial.monomial mold 1 *
                  MvPolynomial.monomial qold 1 at htop
            rw [htop]
            exact firstContraction_newest_term k n a p c q hp hc
          rw [Finset.sum_eq_single 1]
          · simp only [show 1 ≤ c 0 from hc, ite_true]
            rw [hone]
            abel
          · intro i hi hi1
            have hi' := Finset.mem_sdiff.mp hi
            have hirange : i ∈ Finset.range (p 0 + 1) := hi'.1
            have hi0 : i ≠ 0 := by simpa using hi'.2
            have hip : i ≤ p 0 := by
              have := Finset.mem_range.mp hirange
              omega
            by_cases hic : i ≤ c 0
            · simp only [ite_eq_left hic, map_nsmul]
              have hterm := presentedCoefficientOrdered_mem_orderPiece k n L
                (a 0 + c 0 - i) (p 0 + q 0 - i) z hzOrder
              have hlt : L + (p 0 + q 0 - i) < L + t - 1 := by
                dsimp [t]
                omega
              have hvanish :=
                presentedPrincipalComponent_eq_zero_of_mem_of_lt k
                  (@orderWeight (n + 1)) _ hterm hlt
              rw [hvanish, nsmul_zero]
            · simp [hic]
          · exact fun h => (h honeMem).elim

/-- The exact first-contraction coefficient for arbitrary PBW basis vectors.
The positivity hypothesis says that the two monomials have positive combined
differential order, so the component one below the top is unambiguous. -/
theorem presentedPBWBasis_mul_firstContraction {n : ℕ}
    (m q : PhaseVar n →₀ ℕ)
    (hpos : 0 < monomialWeight (@orderWeight n) m +
      monomialWeight (@orderWeight n) q) :
    presentedPrincipalComponent k (@orderWeight n)
        (monomialWeight (@orderWeight n) m +
          monomialWeight (@orderWeight n) q - 1)
        (presentedPBWBasis k n m * presentedPBWBasis k n q) =
      pbwFirstContraction k m q := by
  have hpos' :
      0 < monomialWeight (@orderWeight n)
            (phaseExponent (fun i => m (.inl i)) (fun i => m (.inr i))) +
          monomialWeight (@orderWeight n)
            (phaseExponent (fun i => q (.inl i)) (fun i => q (.inr i))) := by
    simpa only [phaseExponent_split] using hpos
  rw [presentedPBWBasis_apply, presentedPBWBasis_apply,
    ← phaseExponent_split m, ← phaseExponent_split q]
  exact presentedOrderedMonomial_mul_firstContraction k n
    (fun i => m (.inl i)) (fun i => m (.inr i))
    (fun i => q (.inl i)) (fun i => q (.inr i)) hpos'

/-- The unconditional two-element subprincipal commutator formula. -/
theorem principalComponent_commutator_eq_neg_poisson
    {n r s : ℕ} {a b : PresentedWeyl k n}
    (ha : a ∈ orderPiece k n r) (hb : b ∈ orderPiece k n s) :
    presentedPrincipalComponent k (@orderWeight n) (r + s - 1)
        (Stafford.commutator a b) =
      -poissonBracket
        (presentedPrincipalComponent k (@orderWeight n) r a)
        (presentedPrincipalComponent k (@orderWeight n) s b) :=
  principalComponent_commutator_eq_neg_poisson_of_firstContraction k
    (presentedPBWBasis_mul_firstContraction k) ha hb


end

end Stafford38.WeylPBWFirstContraction
