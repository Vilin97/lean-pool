/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Weyl.CommutatorSymbol

/-!
# Coordinate commutators on arbitrary PBW sums

This file extends the ordered-block commutator--symbol formula to arbitrary
presented Weyl elements.  The proof packages both sides as linear maps and
checks equality on the full PBW basis.
-/

namespace Stafford38.WeylCoordinateCommutatorSymbol

open Stafford38.Characteristic
open Stafford38.WeylCommutatorSymbol
open Stafford38.WeylFiltration
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylLeadingSymbol
open Stafford38.WeylPBW

noncomputable section

universe u

variable (k : Type u) [Field k]

/-- Commutation with the newest coordinate, followed by extraction of one
order-homogeneous component, as a linear map. -/
def coordinateCommutatorPrincipalLinear (n T : ℕ) :
    PresentedWeyl k (n + 1) →ₗ[k] SymbolRing k (n + 1) where
  toFun w :=
    presentedPrincipalComponent k (@orderWeight (n + 1)) T
      (Stafford.commutator (presentedCoordinate k n) w)
  map_add' a b := by
    change presentedPrincipalComponent k orderWeight T
        (Stafford.commutator (presentedCoordinate k n) (a + b)) =
      presentedPrincipalComponent k orderWeight T
          (Stafford.commutator (presentedCoordinate k n) a) +
        presentedPrincipalComponent k orderWeight T
          (Stafford.commutator (presentedCoordinate k n) b)
    rw [show Stafford.commutator (presentedCoordinate k n) (a + b) =
        Stafford.commutator (presentedCoordinate k n) a +
          Stafford.commutator (presentedCoordinate k n) b by
      simp only [Stafford.commutator, AlgebraicAnalysis.ringCommutator,
        mul_add, add_mul]
      abel]
    exact LinearMap.map_add _ _ _
  map_smul' c a := by
    change presentedPrincipalComponent k orderWeight T
        (Stafford.commutator (presentedCoordinate k n) (c • a)) =
      c • presentedPrincipalComponent k orderWeight T
        (Stafford.commutator (presentedCoordinate k n) a)
    rw [show Stafford.commutator (presentedCoordinate k n) (c • a) =
        c • Stafford.commutator (presentedCoordinate k n) a by
      simp only [Stafford.commutator, AlgebraicAnalysis.ringCommutator,
        Algebra.mul_smul_comm,
        Algebra.smul_mul_assoc, smul_sub]]
    exact LinearMap.map_smul _ _ _

/-- The negative Poisson derivative of the next order-homogeneous component,
as a linear map. -/
def coordinatePoissonPrincipalLinear (n T : ℕ) :
    PresentedWeyl k (n + 1) →ₗ[k] SymbolRing k (n + 1) :=
  (-((MvPolynomial.pderiv (R := k)
      (Sum.inr (0 : Fin (n + 1)) : PhaseVar (n + 1))).toLinearMap)).comp
    (presentedPrincipalComponent k (@orderWeight (n + 1)) (T + 1))

/-- A PBW basis vector in `n+1` pairs is an ordered newest-pair block whose
coefficient is the corresponding PBW basis vector in `n` pairs. -/
theorem presentedPBWBasis_succ_eq_coefficientOrdered
    (n : ℕ) (m : PhaseVar (n + 1) →₀ ℕ) :
    presentedPBWBasis k (n + 1) m =
      presentedCoefficientOrdered k n
        (m (.inl (0 : Fin (n + 1))))
        (m (.inr (0 : Fin (n + 1))))
        (presentedPBWBasis k n
          (phaseExponent
            (fun i => m (.inl i.succ))
            (fun i => m (.inr i.succ)))) := by
  rw [presentedPBWBasis_apply, presentedOrderedMonomial,
    presentedPBWBasis_apply]
  rfl

theorem extendPhaseExponent_sub_newestMomentum_general
    (n a p : ℕ) (m : PhaseVar n →₀ ℕ) :
    extendPhaseExponent n a p m -
        Finsupp.single (.inr (0 : Fin (n + 1))) 1 =
      extendPhaseExponent n a (p - 1) m := by
  classical
  have hnew : (Finsupp.mapDomain oldIndex m)
      (.inr (0 : Fin (n + 1))) = 0 := by
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨i, hi⟩
    cases i <;> simp [oldIndex, Fin.succ_ne_zero] at hi
  ext i
  rcases i with i | i
  · by_cases hi : i = 0
    · subst i
      simp [extendPhaseExponent, oldIndex,
        add_comm,  add_assoc]
    · simp [extendPhaseExponent, oldIndex, hi,
        add_comm,  add_assoc]
  · by_cases hi : i = 0
    · subst i
      simp [extendPhaseExponent, oldIndex, hnew]
    · have h0i : (0 : Fin (n + 1)) ≠ i := Ne.symm hi
      simp [extendPhaseExponent, oldIndex, hi,
        add_comm,  add_assoc]

theorem extendPhaseExponent_newestMomentum_apply
    (n a p : ℕ) (m : PhaseVar n →₀ ℕ) :
    extendPhaseExponent n a p m (.inr (0 : Fin (n + 1))) = p := by
  have hnew : (Finsupp.mapDomain oldIndex m)
      (.inr (0 : Fin (n + 1))) = 0 := by
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨i, hi⟩
    cases i <;> simp [oldIndex, Fin.succ_ne_zero] at hi
  simp [extendPhaseExponent, oldIndex, hnew]

theorem coordinate_symbol_linear_maps_eq (n T : ℕ) :
    coordinateCommutatorPrincipalLinear k n T =
      coordinatePoissonPrincipalLinear k n T := by
  apply Module.Basis.ext (presentedPBWBasis k (n + 1))
  intro m
  let a := m (.inl (0 : Fin (n + 1)))
  let p := m (.inr (0 : Fin (n + 1)))
  let mold : PhaseVar n →₀ ℕ :=
    phaseExponent
      (fun i => m (.inl i.succ))
      (fun i => m (.inr i.succ))
  rw [presentedPBWBasis_succ_eq_coefficientOrdered k n m]
  change presentedPrincipalComponent k orderWeight T
      (Stafford.commutator (presentedCoordinate k n)
        (presentedCoefficientOrdered k n a p
          (presentedPBWBasis k n mold))) =
    -MvPolynomial.pderiv (.inr (0 : Fin (n + 1)))
      (presentedPrincipalComponent k orderWeight (T + 1)
        (presentedCoefficientOrdered k n a p
          (presentedPBWBasis k n mold)))
  rw [presentedCoordinate_commutator_coefficientOrdered]
  simp only [map_neg, map_smul]
  change -((p : k) •
      MvPolynomial.weightedHomogeneousComponent orderWeight T
        (presentedNormalFormLinearEquiv k (n + 1)
          (presentedCoefficientOrdered k n a (p - 1)
            (presentedPBWBasis k n mold)))) =
    -MvPolynomial.pderiv (.inr (0 : Fin (n + 1)))
      (MvPolynomial.weightedHomogeneousComponent orderWeight (T + 1)
        (presentedNormalFormLinearEquiv k (n + 1)
          (presentedCoefficientOrdered k n a p
            (presentedPBWBasis k n mold))))
  rw [show presentedNormalFormLinearEquiv k (n + 1)
        (presentedCoefficientOrdered k n a (p - 1)
          (presentedPBWBasis k n mold)) =
        MvPolynomial.monomial
          (extendPhaseExponent n a (p - 1) mold) 1 from
      presentedCoefficientOrdered_basis_normal k n a (p - 1) mold,
    weightedHomogeneousComponent_monomial,
    show presentedNormalFormLinearEquiv k (n + 1)
        (presentedCoefficientOrdered k n a p
          (presentedPBWBasis k n mold)) =
        MvPolynomial.monomial (extendPhaseExponent n a p mold) 1 from
      presentedCoefficientOrdered_basis_normal k n a p mold,
    weightedHomogeneousComponent_monomial]
  let q := extendPhaseExponent n a p mold
  let q' := extendPhaseExponent n a (p - 1) mold
  change -((p : k) •
      (if monomialWeight orderWeight q' = T then
        MvPolynomial.monomial q' 1 else 0)) =
    -MvPolynomial.pderiv (.inr (0 : Fin (n + 1)))
      (if monomialWeight orderWeight q = T + 1 then
        MvPolynomial.monomial q 1 else 0)
  by_cases hp : p = 0
  · simp [hp, q, q']
    split <;> simp [MvPolynomial.pderiv_monomial,
      extendPhaseExponent_newestMomentum_apply]
  · have hp0 : 0 < p := Nat.pos_of_ne_zero hp
    have hweight :
        monomialWeight orderWeight q =
          monomialWeight orderWeight q' + 1 := by
      dsimp [q, q']
      rw [← monomialWeight_extend_order, ← monomialWeight_extend_order]
      omega
    by_cases hq : monomialWeight orderWeight q = T + 1
    · have hq' : monomialWeight orderWeight q' = T := by omega
      rw [ite_eq_left hq, ite_eq_left hq', MvPolynomial.pderiv_monomial,
        extendPhaseExponent_newestMomentum_apply,
        extendPhaseExponent_sub_newestMomentum_general]
      rw [MvPolynomial.smul_monomial]
      simp [q']
    · have hq' : monomialWeight orderWeight q' ≠ T := by
        intro h
        apply hq
        omega
      rw [ite_eq_right hq, ite_eq_right hq']
      simp

/-- For every presented Weyl element and every homogeneous order degree, the
symbol of commutation with the newest coordinate is the negative Poisson
bracket with its coordinate symbol.  No filtration-bound hypothesis on `w`
is required. -/
theorem principalComponent_coordinate_commutator_arbitrary
    (n T : ℕ) (w : PresentedWeyl k (n + 1)) :
    presentedPrincipalComponent k (@orderWeight (n + 1)) T
        (Stafford.commutator (presentedCoordinate k n) w) =
      -poissonBracket (MvPolynomial.X (.inl (0 : Fin (n + 1))))
        (presentedPrincipalComponent k (@orderWeight (n + 1)) (T + 1) w) := by
  have h := LinearMap.congr_fun (coordinate_symbol_linear_maps_eq k n T) w
  change _ = -MvPolynomial.pderiv (.inr (0 : Fin (n + 1)))
      (presentedPrincipalComponent k orderWeight (T + 1) w) at h
  rw [poissonBracket_newestCoordinate]
  exact h


end

end Stafford38.WeylCoordinateCommutatorSymbol
