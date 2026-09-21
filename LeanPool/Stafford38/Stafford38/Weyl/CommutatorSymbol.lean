/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Weyl.GradedAlgebra
import LeanPool.Stafford38.Stafford38.Characteristic.Polynomial

/-!
# Coordinate commutators and order symbols

This file proves the newest-coordinate generator case of the filtered
commutator--Poisson correspondence.  It uses the exact PBW block normal form;
no characteristic-ideal, radical, or Gabber statement is assumed.
-/

namespace Stafford38.WeylCommutatorSymbol

open Stafford38.Characteristic
open Stafford38.WeylIteratedEquivalence
open Stafford38.WeylPBW
open Stafford38.WeylFiltration
open Stafford38.WeylLeadingSymbol

noncomputable section

universe u

variable (k : Type u) [Field k]

/-- Commutation with the newest coordinate differentiates the momentum power
in an exact ordered PBW block, with the sign dictated by `[x,p] = -1`. -/
theorem presentedCoordinate_commutator_coefficientOrdered
    (n a p : ℕ) (z : PresentedWeyl k n) :
    Stafford.commutator (presentedCoordinate k n)
        (presentedCoefficientOrdered k n a p z) =
      -((p : k) • presentedCoefficientOrdered k n a (p - 1) z) := by
  let X := presentedCoordinate k n
  let P := presentedMomentum k n
  let Z := previousWeylEmbedding k n z
  have hXZ : X * Z = Z * X :=
    presentedCoordinate_commutes_previous k n z
  have hPX : P * X = X * P + 1 := presentedMomentum_mul_coordinate k n
  have hpowSucc : ∀ r : ℕ,
      X * P ^ (r + 1) - P ^ (r + 1) * X = -((r + 1) • P ^ r) := by
    intro r
    let Xop : (PresentedWeyl k (n + 1))ᵐᵒᵖ := MulOpposite.op X
    let Pop : (PresentedWeyl k (n + 1))ᵐᵒᵖ := MulOpposite.op P
    have hop : Xop * Pop - Pop * Xop = 1 := by
      have hopEq := congrArg MulOpposite.op hPX
      change MulOpposite.op X * MulOpposite.op P -
        MulOpposite.op P * MulOpposite.op X = 1
      rw [show MulOpposite.op X * MulOpposite.op P =
          MulOpposite.op P * MulOpposite.op X + 1 by simpa using hopEq]
      abel
    have ht := AlgebraicAnalysis.OreDivision.OreAmbient.commutator_pow_succ
      Xop Pop hop r
    have hu := congrArg MulOpposite.unop ht
    change P ^ (r + 1) * X - X * P ^ (r + 1) = (r + 1) • P ^ r at hu
    rw [← hu]
    abel
  have hpow : ∀ q : ℕ,
      X * P ^ q - P ^ q * X = -((q : k) • P ^ (q - 1)) := by
    intro q
    cases q with
    | zero => simp
    | succ r =>
        rw [Nat.cast_smul_eq_nsmul k]
        exact hpowSucc r
  rw [presentedCoefficientOrdered]
  change X * (Z * X ^ a * P ^ p) - (Z * X ^ a * P ^ p) * X = _
  let Q := Z * X ^ a
  have hXpow : X * X ^ a = X ^ a * X := (Commute.refl X).pow_right a
  have hQ : Stafford.commutator X Q = 0 := by
    change X * (Z * X ^ a) - (Z * X ^ a) * X = 0
    rw [show X * (Z * X ^ a) = (Z * X ^ a) * X by
      calc
        X * (Z * X ^ a) = (X * Z) * X ^ a := by rw [mul_assoc]
        _ = (Z * X) * X ^ a := by rw [hXZ]
        _ = Z * (X * X ^ a) := by rw [mul_assoc]
        _ = Z * (X ^ a * X) := by rw [hXpow]
        _ = (Z * X ^ a) * X := by rw [mul_assoc]]
    exact sub_self _
  change Stafford.commutator X (Q * P ^ p) = _
  calc
    Stafford.commutator X (Q * P ^ p) =
        Stafford.commutator X Q * P ^ p +
          Q * Stafford.commutator X (P ^ p) := by
            simp only [Stafford.commutator,
              AlgebraicAnalysis.ringCommutator, sub_mul, mul_sub, mul_assoc]
            abel
    _ = Q * (X * P ^ p - P ^ p * X) := by
      have hQ' : X * Q - Q * X = 0 := by exact hQ
      change (X * Q - Q * X) * P ^ p +
          Q * (X * P ^ p - P ^ p * X) = _
      rw [hQ', zero_mul, zero_add]
    _ = Q * -((p : k) • P ^ (p - 1)) := by rw [hpow]
    _ = -((p : k) • (Q * P ^ (p - 1))) := by
      calc
        Q * -((p : k) • P ^ (p - 1)) =
            -(Q * ((p : k) • P ^ (p - 1))) := by
              simpa only using (mul_neg Q ((p : k) • P ^ (p - 1)))
        _ = -((p : k) • (Q * P ^ (p - 1))) :=
          congrArg Neg.neg
            (Algebra.mul_smul_comm (p : k) Q (P ^ (p - 1)))

@[simp]
theorem poissonBracket_newestCoordinate
    (n : ℕ) (f : SymbolRing k (n + 1)) :
    poissonBracket (MvPolynomial.X (.inl (0 : Fin (n + 1)))) f =
      MvPolynomial.pderiv (.inr (0 : Fin (n + 1))) f := by
  simp only [poissonBracket, MvPolynomial.pderiv_X]
  rw [Finset.sum_eq_single (0 : Fin (n + 1))]
  · simp
  · intro i _ hi
    simp [ hi]
  · simp

theorem pderiv_rename_oldIndex_newestMomentum
    (n : ℕ) (f : SymbolRing k n) :
    MvPolynomial.pderiv (.inr (0 : Fin (n + 1)))
        (MvPolynomial.rename oldIndex f) = 0 := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial m c =>
      rw [MvPolynomial.rename_monomial, MvPolynomial.pderiv_monomial]
      have hz : (m.mapDomain oldIndex) (.inr (0 : Fin (n + 1))) = 0 := by
        apply Finsupp.mapDomain_of_notMem_range
        rintro ⟨i, hi⟩
        cases i <;> simp [oldIndex, Fin.succ_ne_zero] at hi
      simp [hz]
  | add f g hf hg => simp [map_add, hf, hg]

theorem extendPhaseExponent_sub_newestMomentum
    (n a p : ℕ) :
    extendPhaseExponent n a p 0 -
        Finsupp.single (.inr (0 : Fin (n + 1))) 1 =
      extendPhaseExponent n a (p - 1) 0 := by
  classical
  ext i
  rcases i with i | i
  · by_cases hi : i = 0
    · subst i
      simp [extendPhaseExponent, oldIndex]
    · simp [extendPhaseExponent, oldIndex, hi]
  · by_cases hi : i = 0
    · subst i
      simp [extendPhaseExponent, oldIndex]
    · simp [extendPhaseExponent, oldIndex, hi]

/-- Generator/ordered-block case of the order-symbol commutator formula.
The exact degree is `N+p-1`; positivity of `p` prevents truncated subtraction.
The sign records the repository convention `[x,p] = -1`. -/
theorem principalComponent_coordinate_commutator_eq_neg_poisson
    (n N a p : ℕ) (z : PresentedWeyl k n) (hp : 0 < p) :
    presentedPrincipalComponent k (@orderWeight (n + 1)) (N + p - 1)
        (Stafford.commutator (presentedCoordinate k n)
          (presentedCoefficientOrdered k n a p z)) =
      -poissonBracket (MvPolynomial.X (.inl (0 : Fin (n + 1))))
        (presentedPrincipalComponent k (@orderWeight (n + 1)) (N + p)
          (presentedCoefficientOrdered k n a p z)) := by
  rw [presentedCoordinate_commutator_coefficientOrdered]
  simp only [map_neg, map_smul]
  rw [show N + p - 1 = N + (p - 1) by omega,
    presentedPrincipalComponent_coefficientOrdered_order,
    presentedPrincipalComponent_coefficientOrdered_order,
    poissonBracket_newestCoordinate,
    MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_monomial,
    pderiv_rename_oldIndex_newestMomentum,
    mul_zero, add_zero,
    extendPhaseExponent_sub_newestMomentum n a p]
  have hexp : (extendPhaseExponent n a p 0)
      (.inr (0 : Fin (n + 1))) = p := by
    simp [extendPhaseExponent, oldIndex]
  rw [hexp]
  congr 1
  rw [← Algebra.smul_mul_assoc, MvPolynomial.smul_monomial]
  simp


end

end Stafford38.WeylCommutatorSymbol
