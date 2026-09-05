/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.MetricCodes.HighestWeights
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Data.Set.PowersetCard

/-!
# Universal root complexes

Orthogonal root kernels and the universal BGG complex used in the all-rank argument.
-/

noncomputable section MetricCodesNoncomputable

section


section

open scoped BigOperators

namespace MetricCodes.Spherical.HigherYoungArbitraryRankOrthogonalRootHighestKernel

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherYoungAmbientRootNilpotence
open MetricCodes.Spherical.HigherYoungAmbientRootRotationDecomposition
open MetricCodes.Spherical.HigherYoungAmbientPositiveRootGeneratorAction
open MetricCodes.Spherical.HigherYoungAmbientPositiveRootUnusedGeneratorAction
open MetricCodes.Spherical.HigherYoungIsotropicCoordinateHomogeneity
open MetricCodes.Spherical.HigherYoungTwoRowLieIrreducibility

/-- Data encoding the orthogonal positive root construction. -/
inductive OrthogonalPositiveRoot (r n : ℕ) where
  | difference (p q : Fin (r + 1)) (_ : p < q)
  | sum (p q : Fin (r + 1)) (_ : p < q)
  | short (p : Fin (r + 1)) (t : Fin n)
      (_ : 2 * (r + 1) ≤ t.val)

/-- The orthogonal positive root derivation used in the spherical-code argument. -/
def orthogonalPositiveRootDerivation {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) :
    OrthogonalPositiveRoot r n →
      Derivation ℂ (MvPolynomial (Fin ((r + 1) * n)) ℂ)
        (MvPolynomial (Fin ((r + 1) * n)) ℂ)
  | .difference p q _ => ambientPositiveRoot h p q
  | .sum p q _ => ambientSumPositiveRoot h p q
  | .short p t _ => ambientShortPositiveRoot h p t

private def isotropicCoordinateCoheight {r n : ℕ}
    (v : Fin ((r + 1) * n)) : ℕ :=
  let t := ((finProdFinEquiv (m := r + 1) (n := n)).symm v).2
  if ht : t.val < 2 * (r + 1) then
    if t.val % 2 = 0 then (ambientPairIndex t ht).val
    else 2 * (r + 1) - (ambientPairIndex t ht).val
  else r + 1

@[simp] theorem isotropicCoordinateCoheight_even {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (a p : Fin (r + 1)) :
    isotropicCoordinateCoheight (r := r) (n := n)
      (variableIndex a (evenCoordinate h p)) = p.val := by
  have hcut : (evenCoordinate h p).val < 2 * (r + 1) := by
    simp only [evenCoordinate, Order.lt_two_iff, zero_le, mul_lt_mul_iff_right₀,
      Order.lt_add_one_iff]
    have := p.isLt
    omega
  simp only [isotropicCoordinateCoheight, variableIndex,
    Equiv.symm_apply_apply, dite_eq_left hcut]
  simp only [evenCoordinate_val, Nat.mul_mod_right, ↓reduceIte, ambientPairIndex_even]

@[simp] theorem isotropicCoordinateCoheight_odd {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (a p : Fin (r + 1)) :
    isotropicCoordinateCoheight (r := r) (n := n)
      (variableIndex a (oddCoordinate h p)) =
      2 * (r + 1) - p.val := by
  have hcut : (oddCoordinate h p).val < 2 * (r + 1) := by
    simp only [oddCoordinate]
    have := p.isLt
    omega
  simp only [isotropicCoordinateCoheight, variableIndex,
    Equiv.symm_apply_apply, dite_eq_left hcut]
  simp only [oddCoordinate_val, Nat.mul_add_mod_self_left, Nat.mod_succ, one_ne_zero, ↓reduceIte,
    ambientPairIndex_odd]

@[simp] theorem isotropicCoordinateCoheight_unused {r n : ℕ}
    (a : Fin (r + 1)) (t : Fin n)
    (ht : 2 * (r + 1) ≤ t.val) :
    isotropicCoordinateCoheight (r := r) (n := n) (variableIndex a t) = r + 1 := by
  simp only [isotropicCoordinateCoheight, variableIndex, Equiv.symm_apply_apply, not_lt_of_ge ht,
    ↓reduceDIte]

theorem isotropicCoordinateCoheight_le {r n : ℕ}
    (v : Fin ((r + 1) * n)) :
    isotropicCoordinateCoheight (r := r) (n := n) v ≤ 2 * (r + 1) := by
  simp only [isotropicCoordinateCoheight]
  split_ifs with ht he
  · have hi := (ambientPairIndex _ ht).isLt
    omega
  · omega
  · omega

/-- The conjugated polynomial derivation used in the spherical-code argument. -/
def conjugatedPolynomialDerivation {σ : Type*}
    (e : MvPolynomial σ ℂ ≃ₐ[ℂ] MvPolynomial σ ℂ)
    (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) :
    Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ) :=
  MvPolynomial.mkDerivation ℂ
    (fun i : σ => e.symm (D (e (MvPolynomial.X i))))

@[simp] theorem conjugatedPolynomialDerivation_X {σ : Type*}
    (e : MvPolynomial σ ℂ ≃ₐ[ℂ] MvPolynomial σ ℂ)
    (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) (i : σ) :
    conjugatedPolynomialDerivation e D (MvPolynomial.X i) =
      e.symm (D (e (MvPolynomial.X i))) := by
  simp only [conjugatedPolynomialDerivation, MvPolynomial.mkDerivation_X]

theorem conjugatedPolynomialDerivation_intertwine {σ : Type*}
    (e : MvPolynomial σ ℂ ≃ₐ[ℂ] MvPolynomial σ ℂ)
    (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (p : MvPolynomial σ ℂ) :
    e (conjugatedPolynomialDerivation e D p) = D (e p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      rw [MvPolynomial.derivation_C, map_zero]
      have hC : e (MvPolynomial.C c) = MvPolynomial.C c := by
        change e (algebraMap ℂ (MvPolynomial σ ℂ) c) =
          algebraMap ℂ (MvPolynomial σ ℂ) c
        exact e.commutes c
      rw [hC, MvPolynomial.derivation_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
      rw [(conjugatedPolynomialDerivation e D).leibniz,
        map_mul, D.leibniz]
      simp only [conjugatedPolynomialDerivation_X, smul_eq_mul, map_add, map_mul,
        AlgEquiv.apply_symm_apply, hp]

/-- The isotropic orthogonal positive root derivation used in the spherical-code argument. -/
def isotropicOrthogonalPositiveRootDerivation {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (α : OrthogonalPositiveRoot r n) :
    Derivation ℂ (MvPolynomial (Fin ((r + 1) * n)) ℂ)
      (MvPolynomial (Fin ((r + 1) * n)) ℂ) :=
  conjugatedPolynomialDerivation (isotropicCoordinateEquiv h)
    (orthogonalPositiveRootDerivation h α)

@[simp] theorem isotropicOrthogonalPositiveRootDerivation_intertwine
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (α : OrthogonalPositiveRoot r n)
    (p : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    isotropicCoordinateEquiv h
      (isotropicOrthogonalPositiveRootDerivation h α p) =
      orthogonalPositiveRootDerivation h α (isotropicCoordinateEquiv h p) :=
  conjugatedPolynomialDerivation_intertwine
    (isotropicCoordinateEquiv h)
    (orthogonalPositiveRootDerivation h α) p

theorem weighted_coefficient_smul_X_lt
    {σ : Type*} (weight : σ → ℕ) (u v : σ) (c : ℂ)
    (huv : weight u < weight v)
    (d : σ →₀ ℕ)
    (hd : ((c • MvPolynomial.X u : MvPolynomial σ ℂ)).coeff d ≠ 0) :
    Finsupp.weight weight d + 1 ≤ weight v := by
  classical
  rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_X] at hd
  split_ifs at hd with heq
  · subst d
    simpa only [Finsupp.weight_single, smul_eq_mul, one_mul, Order.add_one_le_iff] using huv
  · simp only [smul_eq_mul, mul_zero, ne_eq, not_true_eq_false] at hd

theorem isotropicOrthogonalPositiveRootWord_intertwine
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (word : List (OrthogonalPositiveRoot r n))
    (p : MvPolynomial (Fin ((r + 1) * n)) ℂ) :
    isotropicCoordinateEquiv h
      (rootOperatorWord
        (fun α => (isotropicOrthogonalPositiveRootDerivation h α).toLinearMap)
        word p) =
      rootOperatorWord
        (fun α => (orthogonalPositiveRootDerivation h α).toLinearMap)
        word (isotropicCoordinateEquiv h p) := by
  induction word generalizing p with
  | nil => rfl
  | cons α word ih =>
      change isotropicCoordinateEquiv h
        (rootOperatorWord
          (fun β => (isotropicOrthogonalPositiveRootDerivation h β).toLinearMap)
          word (isotropicOrthogonalPositiveRootDerivation h α p)) =
        rootOperatorWord
          (fun β => (orthogonalPositiveRootDerivation h β).toLinearMap)
          word
          (orthogonalPositiveRootDerivation h α
            (isotropicCoordinateEquiv h p))
      rw [ih, isotropicOrthogonalPositiveRootDerivation_intertwine]

end MetricCodes.Spherical.HigherYoungArbitraryRankOrthogonalRootHighestKernel

end

namespace MetricCodes.Spherical.HigherYoungArbitraryRankOrthogonalRootHighestKernel

section

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherYoungAmbientRootNilpotence
open MetricCodes.Spherical.HigherYoungAmbientPositiveRootGeneratorAction
open MetricCodes.Spherical.HigherYoungAmbientPositiveRootUnusedGeneratorAction
open MetricCodes.Spherical.HigherYoungIsotropicCoordinateHomogeneity

theorem conjugatedDifferenceRoot_X_even {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (p q : Fin (r + 1)) (hpq : p < q)
    (a j : Fin (r + 1)) :
    isotropicOrthogonalPositiveRootDerivation h (.difference p q hpq)
      (MvPolynomial.X (variableIndex a (evenCoordinate h j))) =
      if q = j then (2 : ℂ) •
        MvPolynomial.X (variableIndex a (evenCoordinate h p)) else 0 := by
  rw [isotropicOrthogonalPositiveRootDerivation,
    conjugatedPolynomialDerivation_X,
    isotropicCoordinateEquiv_X_even,
    orthogonalPositiveRootDerivation,
    ambientPositiveRoot_isotropicVariable]
  split_ifs with hq
  · rw [map_smul]
    congr 1
    rw [← isotropicCoordinateEquiv_X_even h a p,
      AlgEquiv.symm_apply_apply]
  · simp only [map_zero]

theorem conjugatedDifferenceRoot_X_odd {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (p q : Fin (r + 1)) (hpq : p < q)
    (a j : Fin (r + 1)) :
    isotropicOrthogonalPositiveRootDerivation h (.difference p q hpq)
      (MvPolynomial.X (variableIndex a (oddCoordinate h j))) =
      if p = j then (-2 : ℂ) •
        MvPolynomial.X (variableIndex a (oddCoordinate h q)) else 0 := by
  rw [isotropicOrthogonalPositiveRootDerivation,
    conjugatedPolynomialDerivation_X,
    isotropicCoordinateEquiv_X_odd,
    orthogonalPositiveRootDerivation,
    ambientPositiveRoot_conjugateIsotropicVariable]
  split_ifs with hp
  · rw [map_smul]
    congr 1
    rw [← isotropicCoordinateEquiv_X_odd h a q,
      AlgEquiv.symm_apply_apply]
  · simp only [map_zero]

theorem conjugatedSumRoot_X_even {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (p q : Fin (r + 1)) (hpq : p < q)
    (a j : Fin (r + 1)) :
    isotropicOrthogonalPositiveRootDerivation h (.sum p q hpq)
      (MvPolynomial.X (variableIndex a (evenCoordinate h j))) = 0 := by
  rw [isotropicOrthogonalPositiveRootDerivation,
    conjugatedPolynomialDerivation_X,
    isotropicCoordinateEquiv_X_even,
    orthogonalPositiveRootDerivation,
    ambientSumPositiveRoot_isotropicVariable,
    map_zero]

theorem conjugatedSumRoot_X_odd {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (p q : Fin (r + 1)) (hpq : p < q)
    (a j : Fin (r + 1)) :
    isotropicOrthogonalPositiveRootDerivation h (.sum p q hpq)
      (MvPolynomial.X (variableIndex a (oddCoordinate h j))) =
      (if q = j then (2 : ℂ) •
        MvPolynomial.X (variableIndex a (evenCoordinate h p)) else 0) -
      (if p = j then (2 : ℂ) •
        MvPolynomial.X (variableIndex a (evenCoordinate h q)) else 0) := by
  rw [isotropicOrthogonalPositiveRootDerivation,
    conjugatedPolynomialDerivation_X,
    isotropicCoordinateEquiv_X_odd,
    orthogonalPositiveRootDerivation,
    ambientSumPositiveRoot_conjugateIsotropicVariable,
    map_sub]
  congr 1
  · split_ifs with hq
    · rw [map_smul]
      congr 1
      rw [← isotropicCoordinateEquiv_X_even h a p,
        AlgEquiv.symm_apply_apply]
    · simp only [map_zero]
  · split_ifs with hp
    · rw [map_smul]
      congr 1
      rw [← isotropicCoordinateEquiv_X_even h a q,
        AlgEquiv.symm_apply_apply]
    · simp only [map_zero]

theorem conjugatedDifferenceRoot_X_unused {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (p q : Fin (r + 1)) (hpq : p < q)
    (a : Fin (r + 1)) (t : Fin n)
    (ht : 2 * (r + 1) ≤ t.val) :
    isotropicOrthogonalPositiveRootDerivation h (.difference p q hpq)
      (MvPolynomial.X (variableIndex a t)) = 0 := by
  rw [isotropicOrthogonalPositiveRootDerivation,
    conjugatedPolynomialDerivation_X,
    isotropicCoordinateEquiv_X_unused h a t ht,
    orthogonalPositiveRootDerivation,
    ambientPositiveRoot_X_unused h p q a t ht,
    map_zero]

theorem conjugatedSumRoot_X_unused {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (p q : Fin (r + 1)) (hpq : p < q)
    (a : Fin (r + 1)) (t : Fin n)
    (ht : 2 * (r + 1) ≤ t.val) :
    isotropicOrthogonalPositiveRootDerivation h (.sum p q hpq)
      (MvPolynomial.X (variableIndex a t)) = 0 := by
  rw [isotropicOrthogonalPositiveRootDerivation,
    conjugatedPolynomialDerivation_X,
    isotropicCoordinateEquiv_X_unused h a t ht,
    orthogonalPositiveRootDerivation,
    ambientSumPositiveRoot_X_unused h p q a t ht,
    map_zero]

theorem conjugatedShortRoot_X_even {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (p : Fin (r + 1)) (t : Fin n)
    (ht : 2 * (r + 1) ≤ t.val)
    (a j : Fin (r + 1)) :
    isotropicOrthogonalPositiveRootDerivation h (.short p t ht)
      (MvPolynomial.X (variableIndex a (evenCoordinate h j))) = 0 := by
  rw [isotropicOrthogonalPositiveRootDerivation,
    conjugatedPolynomialDerivation_X,
    isotropicCoordinateEquiv_X_even,
    orthogonalPositiveRootDerivation,
    ambientShortPositiveRoot_isotropicVariable h p a j t ht,
    map_zero]

theorem conjugatedShortRoot_X_odd {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (p : Fin (r + 1)) (t : Fin n)
    (ht : 2 * (r + 1) ≤ t.val)
    (a j : Fin (r + 1)) :
    isotropicOrthogonalPositiveRootDerivation h (.short p t ht)
      (MvPolynomial.X (variableIndex a (oddCoordinate h j))) =
      if p = j then (-2 : ℂ) •
        MvPolynomial.X (variableIndex a t) else 0 := by
  rw [isotropicOrthogonalPositiveRootDerivation,
    conjugatedPolynomialDerivation_X,
    isotropicCoordinateEquiv_X_odd,
    orthogonalPositiveRootDerivation,
    ambientShortPositiveRoot_conjugateIsotropicVariable h p a j t ht]
  split_ifs with hp
  · have hfix : (isotropicCoordinateEquiv h).symm
        (MvPolynomial.X (variableIndex a t)) =
        MvPolynomial.X (variableIndex a t) := by
      calc
        (isotropicCoordinateEquiv h).symm
          (MvPolynomial.X (variableIndex a t)) =
          (isotropicCoordinateEquiv h).symm
            (isotropicCoordinateEquiv h
              (MvPolynomial.X (variableIndex a t))) := by
                congr 1
                exact (isotropicCoordinateEquiv_X_unused h a t ht).symm
        _ = _ := AlgEquiv.symm_apply_apply _ _
    rw [map_smul, hfix]
  · simp only [map_zero]

theorem conjugatedShortRoot_X_unused {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (p : Fin (r + 1)) (t u : Fin n)
    (ht : 2 * (r + 1) ≤ t.val)
    (hu : 2 * (r + 1) ≤ u.val)
    (a : Fin (r + 1)) :
    isotropicOrthogonalPositiveRootDerivation h (.short p t ht)
      (MvPolynomial.X (variableIndex a u)) =
      if t = u then MvPolynomial.X (variableIndex a (evenCoordinate h p))
      else 0 := by
  rw [isotropicOrthogonalPositiveRootDerivation,
    conjugatedPolynomialDerivation_X,
    isotropicCoordinateEquiv_X_unused h a u hu,
    orthogonalPositiveRootDerivation,
    ambientShortPositiveRoot_X_unused h p a t u hu]
  split_ifs with htu
  · rw [← isotropicCoordinateEquiv_X_even h a p,
      AlgEquiv.symm_apply_apply]
  · simp only [map_zero]

theorem isotropicOrthogonalPositiveRoot_strict_even
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (α : OrthogonalPositiveRoot r n)
    (a j : Fin (r + 1)) (d : Fin ((r + 1) * n) →₀ ℕ)
    (hd : (isotropicOrthogonalPositiveRootDerivation h α
      (MvPolynomial.X (variableIndex a (evenCoordinate h j)))).coeff d ≠ 0) :
    Finsupp.weight (isotropicCoordinateCoheight (r := r) (n := n)) d + 1 ≤
      isotropicCoordinateCoheight (r := r) (n := n) (variableIndex a (evenCoordinate h j)) := by
  cases α with
  | difference p q hpq =>
      rw [conjugatedDifferenceRoot_X_even h p q hpq a j] at hd
      split_ifs at hd with hq
      · subst j
        apply weighted_coefficient_smul_X_lt
          (isotropicCoordinateCoheight (r := r) (n := n))
          (variableIndex a (evenCoordinate h p))
          (variableIndex a (evenCoordinate h q)) (2 : ℂ) _ d hd
        simpa only [isotropicCoordinateCoheight_even, Fin.val_fin_lt] using hpq
      · simp only [MvPolynomial.coeff_zero, ne_eq, not_true_eq_false] at hd
  | sum p q hpq =>
      rw [conjugatedSumRoot_X_even h p q hpq a j] at hd
      simp only [MvPolynomial.coeff_zero, ne_eq, not_true_eq_false] at hd
  | short p t ht =>
      rw [conjugatedShortRoot_X_even h p t ht a j] at hd
      simp only [MvPolynomial.coeff_zero, ne_eq, not_true_eq_false] at hd

theorem isotropicOrthogonalPositiveRoot_strict_odd
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (α : OrthogonalPositiveRoot r n)
    (a j : Fin (r + 1)) (d : Fin ((r + 1) * n) →₀ ℕ)
    (hd : (isotropicOrthogonalPositiveRootDerivation h α
      (MvPolynomial.X (variableIndex a (oddCoordinate h j)))).coeff d ≠ 0) :
    Finsupp.weight (isotropicCoordinateCoheight (r := r) (n := n)) d + 1 ≤
      isotropicCoordinateCoheight (r := r) (n := n) (variableIndex a (oddCoordinate h j)) := by
  cases α with
  | difference p q hpq =>
      rw [conjugatedDifferenceRoot_X_odd h p q hpq a j] at hd
      split_ifs at hd with hp
      · subst j
        apply weighted_coefficient_smul_X_lt
          (isotropicCoordinateCoheight (r := r) (n := n))
          (variableIndex a (oddCoordinate h q))
          (variableIndex a (oddCoordinate h p)) (-2 : ℂ) _ d hd
        simp only [isotropicCoordinateCoheight_odd]
        have hp' := p.isLt
        have hq' := q.isLt
        omega
      · simp only [MvPolynomial.coeff_zero, ne_eq, not_true_eq_false] at hd
  | sum p q hpq =>
      rw [conjugatedSumRoot_X_odd h p q hpq a j] at hd
      by_cases hq : q = j
      · subst j
        have hp : p ≠ q := ne_of_lt hpq
        simp only [↓reduceIte, hp, sub_zero, MvPolynomial.coeff_smul, smul_eq_mul, ne_eq,
          mul_eq_zero, OfNat.ofNat_ne_zero, false_or] at hd
        have hd' : ((2 : ℂ) •
            (MvPolynomial.X (variableIndex a (evenCoordinate h p)) :
              MvPolynomial (Fin ((r + 1) * n)) ℂ)).coeff d ≠ 0 := by
          simpa only [MvPolynomial.coeff_smul, smul_eq_mul, ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero,
            false_or] using hd
        apply weighted_coefficient_smul_X_lt
          (isotropicCoordinateCoheight (r := r) (n := n))
          (variableIndex a (evenCoordinate h p))
          (variableIndex a (oddCoordinate h q)) (2 : ℂ) _ d hd'
        simp only [isotropicCoordinateCoheight_even,
          isotropicCoordinateCoheight_odd]
        have hp' := p.isLt
        have hq' := q.isLt
        omega
      · by_cases hp : p = j
        · subst j
          have hd' : ((-2 : ℂ) •
              (MvPolynomial.X (variableIndex a (evenCoordinate h q)) :
                MvPolynomial (Fin ((r + 1) * n)) ℂ)).coeff d ≠ 0 := by
            simpa only [neg_smul, MvPolynomial.coeff_neg, MvPolynomial.coeff_smul, smul_eq_mul,
              ne_eq, neg_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero, false_or, hq, ↓reduceIte,
              zero_sub] using hd
          apply weighted_coefficient_smul_X_lt
            (isotropicCoordinateCoheight (r := r) (n := n))
            (variableIndex a (evenCoordinate h q))
            (variableIndex a (oddCoordinate h p)) (-2 : ℂ) _ d hd'
          simp only [isotropicCoordinateCoheight_even,
            isotropicCoordinateCoheight_odd]
          have hp' := p.isLt
          have hq' := q.isLt
          omega
        · simp only [hq, ↓reduceIte, hp, sub_self, MvPolynomial.coeff_zero, ne_eq,
            not_true_eq_false] at hd
  | short p t ht =>
      rw [conjugatedShortRoot_X_odd h p t ht a j] at hd
      split_ifs at hd with hp
      · subst j
        apply weighted_coefficient_smul_X_lt
          (isotropicCoordinateCoheight (r := r) (n := n))
          (variableIndex a t)
          (variableIndex a (oddCoordinate h p)) (-2 : ℂ) _ d hd
        rw [isotropicCoordinateCoheight_unused a t ht,
          isotropicCoordinateCoheight_odd]
        have hp' := p.isLt
        omega
      · simp only [MvPolynomial.coeff_zero, ne_eq, not_true_eq_false] at hd

theorem isotropicOrthogonalPositiveRoot_strict_unused
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (α : OrthogonalPositiveRoot r n)
    (a : Fin (r + 1)) (t : Fin n)
    (ht : 2 * (r + 1) ≤ t.val)
    (d : Fin ((r + 1) * n) →₀ ℕ)
    (hd : (isotropicOrthogonalPositiveRootDerivation h α
      (MvPolynomial.X (variableIndex a t))).coeff d ≠ 0) :
    Finsupp.weight (isotropicCoordinateCoheight (r := r) (n := n)) d + 1 ≤
      isotropicCoordinateCoheight (r := r) (n := n) (variableIndex a t) := by
  cases α with
  | difference p q hpq =>
      rw [conjugatedDifferenceRoot_X_unused h p q hpq a t ht] at hd
      simp only [MvPolynomial.coeff_zero, ne_eq, not_true_eq_false] at hd
  | sum p q hpq =>
      rw [conjugatedSumRoot_X_unused h p q hpq a t ht] at hd
      simp only [MvPolynomial.coeff_zero, ne_eq, not_true_eq_false] at hd
  | short p u hu =>
      rw [conjugatedShortRoot_X_unused h p u t hu ht a] at hd
      split_ifs at hd with hut
      · have hd' : ((1 : ℂ) •
            (MvPolynomial.X (variableIndex a (evenCoordinate h p)) :
              MvPolynomial (Fin ((r + 1) * n)) ℂ)).coeff d ≠ 0 := by
          simpa only [one_smul, ne_eq] using hd
        apply weighted_coefficient_smul_X_lt
          (isotropicCoordinateCoheight (r := r) (n := n))
          (variableIndex a (evenCoordinate h p))
          (variableIndex a t) (1 : ℂ) _ d hd'
        rw [isotropicCoordinateCoheight_even,
          isotropicCoordinateCoheight_unused a t ht]
        exact p.isLt
      · simp only [MvPolynomial.coeff_zero, ne_eq, not_true_eq_false] at hd

theorem isotropicOrthogonalPositiveRoot_strict
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (α : OrthogonalPositiveRoot r n)
    (v : Fin ((r + 1) * n))
    (d : Fin ((r + 1) * n) →₀ ℕ)
    (hd : (isotropicOrthogonalPositiveRootDerivation h α
      (MvPolynomial.X v)).coeff d ≠ 0) :
    Finsupp.weight (isotropicCoordinateCoheight (r := r) (n := n)) d + 1 ≤
      isotropicCoordinateCoheight (r := r) (n := n) v := by
  obtain ⟨⟨a, t⟩, rfl⟩ :=
    (finProdFinEquiv (m := r + 1) (n := n)).surjective v
  change Finsupp.weight (isotropicCoordinateCoheight (r := r) (n := n)) d + 1 ≤
    isotropicCoordinateCoheight (r := r) (n := n) (variableIndex a t)
  by_cases ht : t.val < 2 * (r + 1)
  · let j := ambientPairIndex t ht
    by_cases he : t.val % 2 = 0
    · have hpair : evenCoordinate h j = t := by
        apply Fin.ext
        change 2 * (t.val / 2) = t.val
        omega
      have hstrict := isotropicOrthogonalPositiveRoot_strict_even
        h α a j d
      rw [hpair] at hstrict
      exact hstrict hd
    · have hpair : oddCoordinate h j = t := by
        apply Fin.ext
        change 2 * (t.val / 2) + 1 = t.val
        have hrem : t.val % 2 = 1 := by omega
        omega
      have hstrict := isotropicOrthogonalPositiveRoot_strict_odd
        h α a j d
      rw [hpair] at hstrict
      exact hstrict hd
  · exact isotropicOrthogonalPositiveRoot_strict_unused
      h α a t (Nat.le_of_not_gt ht) d hd

end

section

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherYoungAmbientRootNilpotence
open MetricCodes.Spherical.HigherYoungIsotropicCoordinateHomogeneity
open MetricCodes.Spherical.HigherYoungTwoRowLieIrreducibility

theorem isotropicOrthogonalPositiveRootWord_eq_zero_of_isHomogeneous
    {r n m : ℕ} (h : 2 * (r + 1) ≤ n)
    {p : MvPolynomial (Fin ((r + 1) * n)) ℂ}
    (hp : p.IsHomogeneous m)
    (word : List (OrthogonalPositiveRoot r n))
    (hlen : m * (2 * (r + 1)) < word.length) :
    rootOperatorWord
      (fun α => (isotropicOrthogonalPositiveRootDerivation h α).toLinearMap)
      word p = 0 := by
  apply triangular_rootOperatorWord_eq_zero_of_isHomogeneous
    (isotropicCoordinateCoheight (r := r) (n := n)) (2 * (r + 1))
    isotropicCoordinateCoheight_le
    (isotropicOrthogonalPositiveRootDerivation h)
    (fun α v d hd => isotropicOrthogonalPositiveRoot_strict h α v d hd)
    hp word hlen

theorem orthogonalPositiveRootWord_eq_zero_of_isHomogeneous
    {r n m : ℕ} (h : 2 * (r + 1) ≤ n)
    {p : MvPolynomial (Fin ((r + 1) * n)) ℂ}
    (hp : p.IsHomogeneous m)
    (word : List (OrthogonalPositiveRoot r n))
    (hlen : m * (2 * (r + 1)) < word.length) :
    rootOperatorWord
      (fun α => (orthogonalPositiveRootDerivation h α).toLinearMap)
      word p = 0 := by
  have hhomogeneous := isotropicCoordinateEquiv_symm_isHomogeneous h p hp
  have hzero := isotropicOrthogonalPositiveRootWord_eq_zero_of_isHomogeneous
    h hhomogeneous word hlen
  have hintertwine := isotropicOrthogonalPositiveRootWord_intertwine
    h word ((isotropicCoordinateEquiv h).symm p)
  rw [hzero, map_zero, AlgEquiv.apply_symm_apply] at hintertwine
  exact hintertwine.symm

end

end MetricCodes.Spherical.HigherYoungArbitraryRankOrthogonalRootHighestKernel

end

namespace MetricCodes

namespace Spherical

section


namespace HigherYoungIsotropicAdjoinRange

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors

theorem adjoin_isotropicVariable_eq_nullSubstitution_range
    {r n : ℕ} (h : 2 * (r + 1) ≤ n) :
    Algebra.adjoin ℂ
      (Set.range (fun ap : Fin (r + 1) × Fin (r + 1) =>
        isotropicVariable h ap.1 ap.2)) =
      (nullSubstitution h).range := by
  rw [Algebra.adjoin_range_eq_range_aeval]
  congr 1
  ext ap
  rcases ap with ⟨a, p⟩
  simp only [isotropicVariable_eq_nullRowLinearForm, MvPolynomial.aeval_eq_bind₁,
    MvPolynomial.bind₁_X_right, nullSubstitution_X]

theorem exists_nullSubstitution_of_mem_adjoin_isotropicVariable
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ)
    (hf : f ∈ Algebra.adjoin ℂ
      (Set.range (fun ap : Fin (r + 1) × Fin (r + 1) =>
        isotropicVariable h ap.1 ap.2))) :
    ∃ q : MvPolynomial (Fin (r + 1) × Fin (r + 1)) ℂ,
      nullSubstitution h q = f := by
  rw [adjoin_isotropicVariable_eq_nullSubstitution_range h,
    AlgHom.mem_range] at hf
  exact hf

end HigherYoungIsotropicAdjoinRange

namespace HigherYoungEvenCoordinateHolomorphicAdjoin

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherYoungAmbientRootNilpotence

theorem isotropicCoordinateEquiv_mem_adjoin_of_even_vars
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (g : MvPolynomial (Fin ((r + 1) * n)) ℂ)
    (heven : ∀ v ∈ g.vars, ∃ (a p : Fin (r + 1)),
      v = variableIndex a (evenCoordinate h p)) :
    isotropicCoordinateEquiv h g ∈ Algebra.adjoin ℂ
      (Set.range (fun ap : Fin (r + 1) × Fin (r + 1) =>
        isotropicVariable h ap.1 ap.2)) := by
  classical
  let s : Set (Fin ((r + 1) * n)) :=
    Set.range (fun ap : Fin (r + 1) × Fin (r + 1) =>
      variableIndex ap.1 (evenCoordinate h ap.2))
  have hg : g ∈ MvPolynomial.supported ℂ s := by
    rw [MvPolynomial.mem_supported]
    intro v hv
    obtain ⟨a, p, hvariable⟩ := heven v hv
    exact ⟨(a, p), hvariable.symm⟩
  have hle : MvPolynomial.supported ℂ s ≤
      (Algebra.adjoin ℂ
        (Set.range (fun ap : Fin (r + 1) × Fin (r + 1) =>
          isotropicVariable h ap.1 ap.2))).comap
        (isotropicCoordinateEquiv h).toAlgHom := by
    rw [MvPolynomial.supported_eq_adjoin_X]
    refine Algebra.adjoin_le ?_
    rintro _ ⟨v, hv, rfl⟩
    change isotropicCoordinateEquiv h (MvPolynomial.X v) ∈
      Algebra.adjoin ℂ
        (Set.range (fun ap : Fin (r + 1) × Fin (r + 1) =>
          isotropicVariable h ap.1 ap.2))
    obtain ⟨⟨a, p⟩, hvariable⟩ := hv
    subst v
    rw [isotropicCoordinateEquiv_X_even]
    apply Algebra.subset_adjoin
    exact ⟨(a, p), rfl⟩
  exact hle hg

end HigherYoungEvenCoordinateHolomorphicAdjoin

end

section


open scoped BigOperators

namespace HigherYoungMaximalCartanNullSubstitutionRange

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherYoungAmbientRootNilpotence
open MetricCodes.Spherical.HigherYoungAmbientCartanIsotropicEigenvalues
open MetricCodes.Spherical.HigherYoungArbitraryRankOrthogonalRootHighestKernel
open MetricCodes.Spherical.HigherYoungIsotropicAdjoinRange
open MetricCodes.Spherical.HigherYoungIsotropicCoordinateHomogeneity
open MetricCodes.Spherical.HigherYoungEvenCoordinateHolomorphicAdjoin

private def isotropicCoordinateDefect {r n : ℕ}
    (v : Fin ((r + 1) * n)) : ℕ :=
  let t := ((finProdFinEquiv (m := r + 1) (n := n)).symm v).2
  if t.val < 2 * (r + 1) then
    if t.val % 2 = 0 then 0 else 2
  else 1

@[simp] theorem isotropicCoordinateDefect_even {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (a p : Fin (r + 1)) :
    isotropicCoordinateDefect (r := r) (n := n)
      (variableIndex a (evenCoordinate h p)) = 0 := by
  have hcut : (evenCoordinate h p).val < 2 * (r + 1) := by
    simp only [evenCoordinate, Order.lt_two_iff, zero_le, mul_lt_mul_iff_right₀,
      Order.lt_add_one_iff]
    have := p.isLt
    omega
  have hp := p.isLt
  simp only [isotropicCoordinateDefect, variableIndex, Equiv.symm_apply_apply, evenCoordinate_val,
    Order.lt_two_iff, zero_le, mul_lt_mul_iff_right₀, Order.lt_add_one_iff, Nat.mul_mod_right,
    ↓reduceIte, ite_eq_left_iff, not_le, one_ne_zero, imp_false, not_lt, ge_iff_le]; omega

@[simp] theorem isotropicCoordinateDefect_odd {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) (a p : Fin (r + 1)) :
    isotropicCoordinateDefect (r := r) (n := n)
      (variableIndex a (oddCoordinate h p)) = 2 := by
  have hcut : (oddCoordinate h p).val < 2 * (r + 1) := by
    simp only [oddCoordinate]
    have := p.isLt
    omega
  have hp := p.isLt
  simp only [isotropicCoordinateDefect, variableIndex, Equiv.symm_apply_apply, oddCoordinate_val,
    Nat.mul_add_mod_self_left, Nat.mod_succ, one_ne_zero, ↓reduceIte, ite_eq_left_iff, not_lt,
    OfNat.one_ne_ofNat, imp_false, not_le, gt_iff_lt]; omega

@[simp] theorem isotropicCoordinateDefect_unused {r n : ℕ}
    (a : Fin (r + 1)) (t : Fin n)
    (ht : 2 * (r + 1) ≤ t.val) :
    isotropicCoordinateDefect (r := r) (n := n) (variableIndex a t) = 1 := by
  simp only [isotropicCoordinateDefect, variableIndex, Equiv.symm_apply_apply, not_lt_of_ge ht,
    ↓reduceIte]

private def naturalDiagonalDerivation {ι : Type*} (w : ι → ℕ) :
    Derivation ℂ (MvPolynomial ι ℂ) (MvPolynomial ι ℂ) :=
  MvPolynomial.mkDerivation ℂ
    (fun i => (w i : ℂ) • MvPolynomial.X i)

@[simp] theorem naturalDiagonalDerivation_X {ι : Type*}
    (w : ι → ℕ) (i : ι) :
    naturalDiagonalDerivation w (MvPolynomial.X i) =
      (w i : ℂ) • MvPolynomial.X i := by
  simp only [naturalDiagonalDerivation, MvPolynomial.mkDerivation_X]

theorem coeff_X_mul_pderiv {ι : Type*} (p : MvPolynomial ι ℂ)
    (i : ι) (d : ι →₀ ℕ) :
    (MvPolynomial.X i * MvPolynomial.pderiv i p).coeff d =
      (d i : ℂ) * p.coeff d := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
      simp only [map_add, mul_add, MvPolynomial.coeff_add, hp, hq]
  | monomial m c =>
      rw [MvPolynomial.X_mul_pderiv_monomial]
      rw [← Nat.cast_smul_eq_nsmul ℂ]
      rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial]
      split_ifs with heq
      · subst d
        simp only [smul_eq_mul]
      · simp only [smul_eq_mul, mul_zero]

theorem naturalDiagonalDerivation_eq_sum {ι : Type*} [Fintype ι]
    (w : ι → ℕ) :
    naturalDiagonalDerivation w =
      ∑ i : ι, (w i : ℂ) •
        ((MvPolynomial.X i : MvPolynomial ι ℂ) •
          (MvPolynomial.pderiv i :
            Derivation ℂ (MvPolynomial ι ℂ) (MvPolynomial ι ℂ))) := by
  classical
  apply MvPolynomial.derivation_ext
  intro j
  rw [naturalDiagonalDerivation_X]
  change _ = (Derivation.coeFnAddMonoidHom
    (∑ i : ι, (w i : ℂ) •
      ((MvPolynomial.X i : MvPolynomial ι ℂ) •
        (MvPolynomial.pderiv i :
          Derivation ℂ (MvPolynomial ι ℂ) (MvPolynomial ι ℂ)))))
      (MvPolynomial.X j)
  rw [map_sum, Finset.sum_apply]
  simp only [Derivation.coeFnAddMonoidHom_apply, Derivation.smul_apply, MvPolynomial.pderiv_X,
    Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, smul_ite, smul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

theorem naturalDiagonalDerivation_apply {ι : Type*} [Fintype ι]
    (w : ι → ℕ) (p : MvPolynomial ι ℂ) :
    naturalDiagonalDerivation w p =
      ∑ i : ι, (w i : ℂ) •
        (MvPolynomial.X i * MvPolynomial.pderiv i p) := by
  rw [naturalDiagonalDerivation_eq_sum]
  change (Derivation.coeFnAddMonoidHom
    (∑ i : ι, (w i : ℂ) •
      ((MvPolynomial.X i : MvPolynomial ι ℂ) •
        (MvPolynomial.pderiv i :
          Derivation ℂ (MvPolynomial ι ℂ) (MvPolynomial ι ℂ))))) p = _
  rw [map_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Derivation.coeFnAddMonoidHom_apply, Derivation.smul_apply, smul_eq_mul]

theorem naturalDiagonalDerivation_coeff {ι : Type*} [Fintype ι]
    (w : ι → ℕ) (p : MvPolynomial ι ℂ) (d : ι →₀ ℕ) :
    (naturalDiagonalDerivation w p).coeff d =
      ((∑ i : ι, w i * d i : ℕ) : ℂ) * p.coeff d := by
  rw [naturalDiagonalDerivation_apply]
  simp_rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul,
    coeff_X_mul_pderiv, smul_eq_mul]
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem conjugatedTotalAmbientCartan_X {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (v : Fin ((r + 1) * n)) :
    conjugatedPolynomialDerivation (isotropicCoordinateEquiv h)
      (totalAmbientCartan h) (MvPolynomial.X v) =
      (2 : ℂ) • MvPolynomial.X v -
        ((2 * isotropicCoordinateDefect (r := r) (n := n) v : ℕ) : ℂ) •
          MvPolynomial.X v := by
  classical
  obtain ⟨⟨a, t⟩, rfl⟩ :=
    (finProdFinEquiv (m := r + 1) (n := n)).surjective v
  change
    conjugatedPolynomialDerivation (isotropicCoordinateEquiv h)
      (totalAmbientCartan h) (MvPolynomial.X (variableIndex a t)) =
      (2 : ℂ) • MvPolynomial.X (variableIndex a t) -
        ((2 * isotropicCoordinateDefect (r := r) (n := n) (variableIndex a t) : ℕ) : ℂ) •
          MvPolynomial.X (variableIndex a t)
  by_cases ht : t.val < 2 * (r + 1)
  · let p := ambientPairIndex t ht
    by_cases he : t.val % 2 = 0
    · have hpair : evenCoordinate h p = t := by
        apply Fin.ext
        change 2 * (t.val / 2) = t.val
        omega
      rw [← hpair, conjugatedPolynomialDerivation_X,
        isotropicCoordinateEquiv_X_even,
        totalAmbientCartan_isotropicVariable,
        isotropicCoordinateDefect_even]
      have hinverse : (isotropicCoordinateEquiv h).symm
          (isotropicVariable h a p) =
          MvPolynomial.X (variableIndex a (evenCoordinate h p)) := by
        apply (isotropicCoordinateEquiv h).symm_apply_eq.mpr
        exact (isotropicCoordinateEquiv_X_even h a p).symm
      simp only [map_smul, hinverse, mul_zero, CharP.cast_eq_zero, zero_smul, sub_zero]
    · have hpair : oddCoordinate h p = t := by
        apply Fin.ext
        change 2 * (t.val / 2) + 1 = t.val
        have hrem : t.val % 2 = 1 := by omega
        omega
      rw [← hpair, conjugatedPolynomialDerivation_X,
        isotropicCoordinateEquiv_X_odd,
        totalAmbientCartan_conjugateIsotropicVariable,
        isotropicCoordinateDefect_odd]
      have hinverse : (isotropicCoordinateEquiv h).symm
          (conjugateIsotropicVariable h a p) =
          MvPolynomial.X (variableIndex a (oddCoordinate h p)) := by
        apply (isotropicCoordinateEquiv h).symm_apply_eq.mpr
        exact (isotropicCoordinateEquiv_X_odd h a p).symm
      simp only [neg_smul, map_neg, map_smul, hinverse, Nat.reduceMul, Nat.cast_ofNat]
      module
  · have htge : 2 * (r + 1) ≤ t.val := Nat.le_of_not_gt ht
    rw [conjugatedPolynomialDerivation_X,
      isotropicCoordinateEquiv_X_unused h a t htge,
      totalAmbientCartan_X_unused h a t htge,
      isotropicCoordinateDefect_unused a t htge]
    simp only [map_zero, mul_one, Nat.cast_ofNat, sub_self]

theorem conjugatedTotalAmbientCartan_eq_euler_sub_defect {r n : ℕ}
    (h : 2 * (r + 1) ≤ n) :
    conjugatedPolynomialDerivation (isotropicCoordinateEquiv h)
      (totalAmbientCartan h) =
      (2 : ℂ) • naturalDiagonalDerivation
        (fun _ : Fin ((r + 1) * n) => 1) -
      naturalDiagonalDerivation
        (fun i => 2 * isotropicCoordinateDefect (r := r) (n := n) i) := by
  apply MvPolynomial.derivation_ext
  intro i
  rw [conjugatedTotalAmbientCartan_X]
  simp only [Nat.cast_mul, Nat.cast_ofNat, Derivation.coe_sub, Derivation.coe_smul, Pi.sub_apply,
    Pi.smul_apply, naturalDiagonalDerivation_X, Nat.cast_one, one_smul]

theorem naturalDiagonalDerivation_one_of_homogeneous
    {ι : Type*} [Finite ι] {d : ℕ}
    (p : MvPolynomial ι ℂ) (hp : p.IsHomogeneous d) :
    naturalDiagonalDerivation (fun _ : ι => 1) p = (d : ℂ) • p := by
  let _ : Fintype ι := Fintype.ofFinite ι
  rw [naturalDiagonalDerivation_apply]
  simp only [Nat.cast_one, one_smul]
  simpa only [Nat.cast_smul_eq_nsmul ℂ, nsmul_eq_mul] using hp.sum_X_mul_pderiv

theorem exists_evenCoordinate_of_defect_eq_zero {r n : ℕ}
    (h : 2 * (r + 1) ≤ n)
    (v : Fin ((r + 1) * n))
    (hv : isotropicCoordinateDefect (r := r) (n := n) v = 0) :
    ∃ a p : Fin (r + 1),
      v = variableIndex a (evenCoordinate h p) := by
  classical
  obtain ⟨⟨a, t⟩, rfl⟩ :=
    (finProdFinEquiv (m := r + 1) (n := n)).surjective v
  change isotropicCoordinateDefect (r := r) (n := n) (variableIndex a t) = 0 at hv
  by_cases ht : t.val < 2 * (r + 1)
  · by_cases he : t.val % 2 = 0
    · refine ⟨a, ambientPairIndex t ht, ?_⟩
      congr 1
      congr 1
      apply Fin.ext
      change t.val = 2 * (t.val / 2)
      omega
    · simp only [isotropicCoordinateDefect, variableIndex, Equiv.symm_apply_apply, ht, ↓reduceIte,
        he, OfNat.ofNat_ne_zero] at hv
  · simp only [isotropicCoordinateDefect, variableIndex, Equiv.symm_apply_apply, ht, ↓reduceIte,
      one_ne_zero] at hv

theorem isotropicCoordinateDefectDerivation_eq_zero_of_maximalCartan
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ) (d : ℕ)
    (hfhom : f.IsHomogeneous d)
    (hcartan : totalAmbientCartan h f = ((2 * d : ℕ) : ℂ) • f) :
    naturalDiagonalDerivation
      (fun i => 2 * isotropicCoordinateDefect (r := r) (n := n) i)
      ((isotropicCoordinateEquiv h).symm f) = 0 := by
  let g := (isotropicCoordinateEquiv h).symm f
  have hg : g.IsHomogeneous d :=
    isotropicCoordinateEquiv_symm_isHomogeneous h f hfhom
  have hconj : conjugatedPolynomialDerivation (isotropicCoordinateEquiv h)
      (totalAmbientCartan h) g = ((2 * d : ℕ) : ℂ) • g := by
    apply (isotropicCoordinateEquiv h).injective
    rw [conjugatedPolynomialDerivation_intertwine]
    simp only [AlgEquiv.apply_symm_apply, hcartan, Nat.cast_mul, Nat.cast_ofNat, map_smul, g]
  rw [conjugatedTotalAmbientCartan_eq_euler_sub_defect] at hconj
  change
    (2 : ℂ) • naturalDiagonalDerivation
      (fun _ : Fin ((r + 1) * n) => 1) g -
      naturalDiagonalDerivation
        (fun i => 2 * isotropicCoordinateDefect (r := r) (n := n) i) g =
      ((2 * d : ℕ) : ℂ) • g at hconj
  rw [naturalDiagonalDerivation_one_of_homogeneous g hg,
    smul_smul] at hconj
  norm_num at hconj ⊢
  simpa only using hconj

theorem isotropicCoordinateDefect_eq_zero_of_mem_vars_of_maximalCartan
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ) (d : ℕ)
    (hfhom : f.IsHomogeneous d)
    (hcartan : totalAmbientCartan h f = ((2 * d : ℕ) : ℂ) • f)
    (v : Fin ((r + 1) * n))
    (hv : v ∈ ((isotropicCoordinateEquiv h).symm f).vars) :
    isotropicCoordinateDefect (r := r) (n := n) v = 0 := by
  classical
  let g := (isotropicCoordinateEquiv h).symm f
  obtain ⟨m, hm, hvm⟩ :=
    (MvPolynomial.mem_vars_iff_mem_support v).mp hv
  have hzero := isotropicCoordinateDefectDerivation_eq_zero_of_maximalCartan
    h f d hfhom hcartan
  have hcoeff := congrArg (MvPolynomial.coeff m) hzero
  rw [naturalDiagonalDerivation_coeff] at hcoeff
  simp only [MvPolynomial.coeff_zero] at hcoeff
  have hmcoeff : g.coeff m ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hm
  have hcast :
      ((∑ i : Fin ((r + 1) * n),
        (2 * isotropicCoordinateDefect (r := r) (n := n) i) * m i : ℕ) : ℂ) = 0 :=
    (mul_eq_zero.mp hcoeff).resolve_right hmcoeff
  have hsum :
      (∑ i : Fin ((r + 1) * n),
        (2 * isotropicCoordinateDefect (r := r) (n := n) i) * m i : ℕ) = 0 := by
    exact_mod_cast hcast
  have hterm : (2 * isotropicCoordinateDefect (r := r) (n := n) v) * m v = 0 :=
    (Finset.sum_eq_zero_iff.mp hsum) v (Finset.mem_univ v)
  have hmv : m v ≠ 0 := Finsupp.mem_support_iff.mp hvm
  have hdef : 2 * isotropicCoordinateDefect (r := r) (n := n) v = 0 :=
    (mul_eq_zero.mp hterm).resolve_right hmv
  omega

theorem maximalTotalAmbientCartan_mem_nullSubstitution_range
    {r n : ℕ} (h : 2 * (r + 1) ≤ n)
    (f : MvPolynomial (Fin ((r + 1) * n)) ℂ) (d : ℕ)
    (hfhom : f.IsHomogeneous d)
    (hcartan : totalAmbientCartan h f = ((2 * d : ℕ) : ℂ) • f) :
    ∃ q : MvPolynomial (Fin (r + 1) × Fin (r + 1)) ℂ,
      nullSubstitution h q = f := by
  let g := (isotropicCoordinateEquiv h).symm f
  have hvars : ∀ v ∈ g.vars, ∃ a p : Fin (r + 1),
      v = variableIndex a (evenCoordinate h p) := by
    intro v hv
    apply exists_evenCoordinate_of_defect_eq_zero h v
    exact isotropicCoordinateDefect_eq_zero_of_mem_vars_of_maximalCartan
      h f d hfhom hcartan v hv
  have hadjoin := isotropicCoordinateEquiv_mem_adjoin_of_even_vars h g hvars
  have hfadjoin : f ∈ Algebra.adjoin ℂ
      (Set.range (fun ap : Fin (r + 1) × Fin (r + 1) =>
        isotropicVariable h ap.1 ap.2)) := by
    simpa [g] using hadjoin
  exact exists_nullSubstitution_of_mem_adjoin_isotropicVariable h f hfadjoin

end HigherYoungMaximalCartanNullSubstitutionRange

end

section


open scoped BigOperators InnerProductSpace

namespace HigherYoungArbitraryRankDominantHighestLinePreservation

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.HigherHarmonicYoung.BideterminantHighestLine
open MetricCodes.Spherical.HigherHarmonicYoung.IsotropicAmbientHighestLine
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankGelfandTsetlinGramRotationCommutation
open MetricCodes.Spherical.HigherYoungAmbientRootRotationDecomposition
open MetricCodes.Spherical.HigherYoungAmbientCartanIsotropicEigenvalues
open MetricCodes.Spherical.HigherYoungArbitraryRankGelfandTsetlinHighestEigenpair
open MetricCodes.Spherical.HigherYoungCyclicHighestSchur
open MetricCodes.Spherical.HigherYoungMaximalCartanNullSubstitutionRange
open MetricCodes.Spherical.HigherYoungTwoRowLieIrreducibility

/-- The young complex pair used in the spherical-code argument. -/
def youngComplexPair {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (p q : HarmonicYoungSpace (n := n) lam) :
    MvPolynomial (Fin ((r + 1) * n)) ℂ :=
  polynomialComplexification (p : PolynomialSpace r n) +
    Complex.I • polynomialComplexification (q : PolynomialSpace r n)

@[simp] theorem polynomialRealPart_youngComplexPair
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (p q : HarmonicYoungSpace (n := n) lam) :
    polynomialRealPart (youngComplexPair lam p q) =
      (p : PolynomialSpace r n) := by
  unfold youngComplexPair
  rw [map_add, polynomialRealPart_complex_smul,
    polynomialRealPart_complexification,
    polynomialRealPart_complexification,
    polynomialImaginaryPart_complexification]
  simp only [Complex.I_re, zero_smul, Complex.I_im, smul_zero, sub_self, add_zero]

@[simp] theorem polynomialImaginaryPart_youngComplexPair
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (p q : HarmonicYoungSpace (n := n) lam) :
    polynomialImaginaryPart (youngComplexPair lam p q) =
      (q : PolynomialSpace r n) := by
  unfold youngComplexPair
  rw [map_add, polynomialImaginaryPart_complex_smul,
    polynomialImaginaryPart_complexification,
    polynomialImaginaryPart_complexification,
    polynomialRealPart_complexification]
  simp only [Complex.I_re, smul_zero, Complex.I_im, one_smul, zero_add]

theorem complexPolynomial_eq_of_real_imaginary
    {r n : ℕ}
    (p q : MvPolynomial (Fin ((r + 1) * n)) ℂ)
    (hreal : polynomialRealPart p = polynomialRealPart q)
    (himag : polynomialImaginaryPart p = polynomialImaginaryPart q) :
    p = q := by
  apply MvPolynomial.ext
  intro d
  apply Complex.ext
  · simpa only [coeff_polynomialRealPart] using congrArg (fun f : PolynomialSpace r n => f.coeff
    d) hreal
  · simpa only [coeff_polynomialImaginaryPart] using congrArg (fun f : PolynomialSpace r n =>
    f.coeff d) himag

theorem youngComplexPair_eq_zero_iff
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (p q : HarmonicYoungSpace (n := n) lam) :
    youngComplexPair lam p q = 0 ↔ p = 0 ∧ q = 0 := by
  constructor
  · intro h
    constructor
    · apply Subtype.ext
      simpa only [ZeroMemClass.coe_zero, ZeroMemClass.coe_eq_zero,
        polynomialRealPart_youngComplexPair, map_zero] using congrArg polynomialRealPart h
    · apply Subtype.ext
      simpa only [ZeroMemClass.coe_zero, ZeroMemClass.coe_eq_zero,
        polynomialImaginaryPart_youngComplexPair, map_zero] using congrArg polynomialImaginaryPart h
  · rintro ⟨rfl, rfl⟩
    simp only [youngComplexPair, ZeroMemClass.coe_zero, map_zero,
      smul_zero, add_zero]

theorem complexAmbientRotation_youngComplexPair
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (a b : Fin n)
    (p q : HarmonicYoungSpace (n := n) lam) :
    complexAmbientRotation (r := r) a b (youngComplexPair lam p q) =
      youngComplexPair lam
        (youngAmbientRotation lam a b p)
        (youngAmbientRotation lam a b q) := by
  unfold youngComplexPair
  rw [map_add, Derivation.map_smul,
    complexAmbientRotation_complexification,
    complexAmbientRotation_complexification]
  rfl

theorem complex_smul_youngComplexPair
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (c : ℂ) (p q : HarmonicYoungSpace (n := n) lam) :
    c • youngComplexPair lam p q =
      youngComplexPair lam
        (c.re • p - c.im • q)
        (c.im • p + c.re • q) := by
  apply complexPolynomial_eq_of_real_imaginary
  · rw [polynomialRealPart_complex_smul,
      polynomialRealPart_youngComplexPair,
      polynomialImaginaryPart_youngComplexPair,
      polynomialRealPart_youngComplexPair]
    rfl
  · rw [polynomialImaginaryPart_complex_smul,
      polynomialRealPart_youngComplexPair,
      polynomialImaginaryPart_youngComplexPair,
      polynomialImaginaryPart_youngComplexPair]
    change c.re • (q : PolynomialSpace r n) +
      c.im • (p : PolynomialSpace r n) = _
    rw [add_comm]
    rfl

@[simp] theorem youngComplexPair_add
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (p q p' q' : HarmonicYoungSpace (n := n) lam) :
    youngComplexPair lam (p + p') (q + q') =
      youngComplexPair lam p q + youngComplexPair lam p' q' := by
  unfold youngComplexPair
  change polynomialComplexification
      ((p : PolynomialSpace r n) + (p' : PolynomialSpace r n)) +
    Complex.I • polynomialComplexification
      ((q : PolynomialSpace r n) + (q' : PolynomialSpace r n)) = _
  rw [map_add, map_add, smul_add]
  module

theorem complexRotationCombination_youngComplexPair
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (a b : Fin k → Fin n) (c : Fin k → ℂ)
    (p q : HarmonicYoungSpace (n := n) lam) :
    (∑ i : Fin k,
      c i • complexAmbientRotation (r := r) (a i) (b i)
        (youngComplexPair lam p q)) =
      youngComplexPair lam
        (∑ i : Fin k,
          ((c i).re • youngAmbientRotation lam (a i) (b i) p -
            (c i).im • youngAmbientRotation lam (a i) (b i) q))
        (∑ i : Fin k,
          ((c i).im • youngAmbientRotation lam (a i) (b i) p +
            (c i).re • youngAmbientRotation lam (a i) (b i) q)) := by
  simp_rw [complexAmbientRotation_youngComplexPair,
    complex_smul_youngComplexPair]
  classical
  induction (Finset.univ : Finset (Fin k)) using Finset.induction_on with
  | empty => simp only [youngComplexPair, AddSubgroupClass.coe_sub, SetLike.val_smul,
               youngAmbientRotation_apply_coe, ambientRotation_apply,
               ambientCoordinateDerivation_apply, polynomialComplexification_apply, map_sub,
               Submodule.coe_add, map_add, smul_add, Finset.sum_empty, Finset.sum_sub_distrib,
               sub_self, ZeroMemClass.coe_zero, map_zero, smul_zero, add_zero]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [youngComplexPair_add]
      exact congrArg (fun z => youngComplexPair lam
        ((c i).re • youngAmbientRotation lam (a i) (b i) p -
          (c i).im • youngAmbientRotation lam (a i) (b i) q)
        ((c i).im • youngAmbientRotation lam (a i) (b i) p +
          (c i).re • youngAmbientRotation lam (a i) (b i) q) + z) ih

theorem rowDerivation_self_youngComplexPair
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (p q : HarmonicYoungSpace (n := n) lam)
    (i : Fin (r + 1)) :
    rowDerivation i i (youngComplexPair lam p q) =
      (lam i : ℂ) • youngComplexPair lam p q := by
  rw [← complexRowEuler_eq_rowDerivation]
  apply complexPolynomial_eq_of_real_imaginary
  · rw [polynomialRealPart_complexRowEuler,
      polynomialRealPart_complex_smul,
      polynomialRealPart_youngComplexPair,
      polynomialImaginaryPart_youngComplexPair]
    simpa only [rowEuler_apply, Complex.natCast_re, Complex.natCast_im, zero_smul, sub_zero] using
      ((mem_harmonicYoungSubmodule lam (p : PolynomialSpace r n)).mp p.property).2.1 i
  · rw [polynomialImaginaryPart_complexRowEuler,
      polynomialImaginaryPart_complex_smul,
      polynomialRealPart_youngComplexPair,
      polynomialImaginaryPart_youngComplexPair]
    simpa only [rowEuler_apply, Complex.natCast_re, Complex.natCast_im, zero_smul, add_zero] using
      ((mem_harmonicYoungSubmodule lam (q : PolynomialSpace r n)).mp q.property).2.1 i

theorem rowDerivation_upper_youngComplexPair
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (p q : HarmonicYoungSpace (n := n) lam)
    (i j : Fin (r + 1)) (hij : i < j) :
    rowDerivation i j (youngComplexPair lam p q) = 0 := by
  rw [← complexPolarization_eq_rowDerivation]
  apply complexPolynomial_eq_of_real_imaginary
  · rw [polynomialRealPart_complexPolarization,
      polynomialRealPart_youngComplexPair]
    simpa only [polarization_apply, map_zero] using
      ((mem_harmonicYoungSubmodule lam (p : PolynomialSpace r n)).mp p.property).2.2.2 i j hij
  · rw [polynomialImaginaryPart_complexPolarization,
      polynomialImaginaryPart_youngComplexPair]
    simpa only [polarization_apply, map_zero] using
      ((mem_harmonicYoungSubmodule lam (q : PolynomialSpace r n)).mp q.property).2.2.2 i j hij

theorem youngComplexPair_dominantHighest
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam) :
    youngComplexPair lam
      (dominantHighestRealVector hn lam hdom)
      (dominantHighestImaginaryVector hn lam hdom) =
      (dominantHighestWeightWitness hn lam hdom).polynomial := by
  apply complexPolynomial_eq_of_real_imaginary
  · exact polynomialRealPart_youngComplexPair lam _ _
  · exact polynomialImaginaryPart_youngComplexPair lam _ _

theorem youngComplexPair_endomorphism_dominantHighest
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (A : HarmonicYoungSpace (n := n) lam →ₗ[ℝ]
      HarmonicYoungSpace (n := n) lam) :
    youngComplexPair lam
      (A (dominantHighestRealVector hn lam hdom))
      (A (dominantHighestImaginaryVector hn lam hdom)) =
      youngEndomorphismHighestPolynomial hn lam hdom A := rfl

theorem youngComplexPair_isHomogeneous
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (p q : HarmonicYoungSpace (n := n) lam) :
    (youngComplexPair lam p q).IsHomogeneous (∑ i, lam i) := by
  unfold youngComplexPair
  apply MvPolynomial.IsHomogeneous.add
  · exact ((mem_harmonicYoungSubmodule lam
      (p : PolynomialSpace r n)).mp p.property).1.map Complex.ofRealHom
  · rw [MvPolynomial.smul_eq_C_mul]
    exact (((mem_harmonicYoungSubmodule lam
      (q : PolynomialSpace r n)).mp q.property).1.map
        Complex.ofRealHom).C_mul Complex.I

theorem youngEndomorphismHighestPolynomial_isHomogeneous
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (A : HarmonicYoungSpace (n := n) lam →ₗ[ℝ]
      HarmonicYoungSpace (n := n) lam) :
    (youngEndomorphismHighestPolynomial hn lam hdom A).IsHomogeneous
      (∑ i, lam i) :=
  youngComplexPair_isHomogeneous lam
    (A (dominantHighestRealVector hn lam hdom))
    (A (dominantHighestImaginaryVector hn lam hdom))

theorem rotationIntertwiner_complexCombination_eigen
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (A : HarmonicYoungSpace (n := n) lam →ₗ[ℝ]
      HarmonicYoungSpace (n := n) lam)
    (hcomm : ∀ a b : Fin n,
      A.comp (youngAmbientRotation lam a b) =
        (youngAmbientRotation lam a b).comp A)
    (a b : Fin k → Fin n) (c : Fin k → ℂ) (z : ℂ)
    (p q : HarmonicYoungSpace (n := n) lam)
    (heigen :
      (∑ i : Fin k,
        c i • complexAmbientRotation (r := r) (a i) (b i)
          (youngComplexPair lam p q)) =
        z • youngComplexPair lam p q) :
    (∑ i : Fin k,
      c i • complexAmbientRotation (r := r) (a i) (b i)
        (youngComplexPair lam (A p) (A q))) =
      z • youngComplexPair lam (A p) (A q) := by
  rw [complexRotationCombination_youngComplexPair,
    complex_smul_youngComplexPair] at heigen ⊢
  have hreal :
      (∑ i : Fin k,
        ((c i).re • youngAmbientRotation lam (a i) (b i) p -
          (c i).im • youngAmbientRotation lam (a i) (b i) q)) =
        z.re • p - z.im • q := by
    apply Subtype.ext
    simpa only [Finset.sum_sub_distrib, AddSubgroupClass.coe_sub, AddSubmonoidClass.coe_finsetSum,
      SetLike.val_smul, youngAmbientRotation_apply_coe, ambientRotation_apply,
      ambientCoordinateDerivation_apply,
      polynomialRealPart_youngComplexPair] using congrArg polynomialRealPart heigen
  have himag :
      (∑ i : Fin k,
        ((c i).im • youngAmbientRotation lam (a i) (b i) p +
          (c i).re • youngAmbientRotation lam (a i) (b i) q)) =
        z.im • p + z.re • q := by
    apply Subtype.ext
    simpa only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_add, SetLike.val_smul,
      youngAmbientRotation_apply_coe, ambientRotation_apply, ambientCoordinateDerivation_apply,
      Finset.sum_sub_distrib,
      polynomialImaginaryPart_youngComplexPair] using congrArg polynomialImaginaryPart heigen
  have hArot (i : Fin k) (v : HarmonicYoungSpace (n := n) lam) :
      A (youngAmbientRotation lam (a i) (b i) v) =
        youngAmbientRotation lam (a i) (b i) (A v) :=
    LinearMap.congr_fun (hcomm (a i) (b i)) v
  have hrealA := congrArg A hreal
  have himagA := congrArg A himag
  simp only [map_sum, map_sub, map_add, map_smul, hArot]
    at hrealA himagA
  exact congrArg₂ (youngComplexPair lam) hrealA himagA

@[simp] theorem complexAmbientRotation_self
    {r n : ℕ} (a : Fin n) :
    complexAmbientRotation (r := r) a a = 0 := by
  simp only [complexAmbientRotation, sub_self]

theorem ambientCartan_eq_twice_I_complexRotation
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (i : Fin (r + 1)) :
    ambientCartan hn i =
      ((2 : ℂ) * Complex.I) •
        complexAmbientRotation (r := r)
          (oddCoordinate hn i) (evenCoordinate hn i) := by
  rw [ambientCartan, ambientPositiveRoot_eq_complexRotations]
  simp only [complexAmbientRotation_self, zero_add]
  rw [← add_smul]
  congr 1
  ring

theorem rotationIntertwiner_complexRotation_eigen
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (A : HarmonicYoungSpace (n := n) lam →ₗ[ℝ]
      HarmonicYoungSpace (n := n) lam)
    (hcomm : ∀ a b : Fin n,
      A.comp (youngAmbientRotation lam a b) =
        (youngAmbientRotation lam a b).comp A)
    (a b : Fin n) (c z : ℂ)
    (p q : HarmonicYoungSpace (n := n) lam)
    (heigen :
      c • complexAmbientRotation (r := r) a b
          (youngComplexPair lam p q) =
        z • youngComplexPair lam p q) :
    c • complexAmbientRotation (r := r) a b
        (youngComplexPair lam (A p) (A q)) =
      z • youngComplexPair lam (A p) (A q) := by
  have h := rotationIntertwiner_complexCombination_eigen
    lam A hcomm (fun _ : Fin 1 => a) (fun _ : Fin 1 => b)
    (fun _ : Fin 1 => c) z p q (by
      simpa only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_const,
        Finset.card_singleton, one_smul] using heigen)
  simpa only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_const,
    Finset.card_singleton, one_smul] using h

theorem rotationIntertwiner_ambientCartan_dominantHighest
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (A : HarmonicYoungSpace (n := n) lam →ₗ[ℝ]
      HarmonicYoungSpace (n := n) lam)
    (hcomm : ∀ a b : Fin n,
      A.comp (youngAmbientRotation lam a b) =
        (youngAmbientRotation lam a b).comp A)
    (i : Fin (r + 1)) :
    ambientCartan hn i (youngEndomorphismHighestPolynomial hn lam hdom A) =
      ((2 * lam i : ℕ) : ℂ) •
        youngEndomorphismHighestPolynomial hn lam hdom A := by
  rw [← youngComplexPair_endomorphism_dominantHighest]
  rw [ambientCartan_eq_twice_I_complexRotation]
  change
    ((2 : ℂ) * Complex.I) •
      complexAmbientRotation (r := r)
        (oddCoordinate hn i) (evenCoordinate hn i)
        (youngComplexPair lam
          (A (dominantHighestRealVector hn lam hdom))
          (A (dominantHighestImaginaryVector hn lam hdom))) = _
  apply rotationIntertwiner_complexRotation_eigen lam A hcomm
    (oddCoordinate hn i) (evenCoordinate hn i)
    ((2 : ℂ) * Complex.I) ((2 * lam i : ℕ) : ℂ)
    (dominantHighestRealVector hn lam hdom)
    (dominantHighestImaginaryVector hn lam hdom)
  rw [youngComplexPair_dominantHighest]
  change
    (((2 : ℂ) * Complex.I) •
      complexAmbientRotation (r := r)
        (oddCoordinate hn i) (evenCoordinate hn i))
        (dominantHighestWeightWitness hn lam hdom).polynomial = _
  rw [← ambientCartan_eq_twice_I_complexRotation]
  exact ambientCartan_dominantHighestWeightWitness hn lam hdom i

theorem rotationIntertwiner_totalAmbientCartan_dominantHighest
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (A : HarmonicYoungSpace (n := n) lam →ₗ[ℝ]
      HarmonicYoungSpace (n := n) lam)
    (hcomm : ∀ a b : Fin n,
      A.comp (youngAmbientRotation lam a b) =
        (youngAmbientRotation lam a b).comp A) :
    totalAmbientCartan hn
        (youngEndomorphismHighestPolynomial hn lam hdom A) =
      ((2 * (∑ i, lam i) : ℕ) : ℂ) •
        youngEndomorphismHighestPolynomial hn lam hdom A := by
  rw [totalAmbientCartan_apply]
  simp_rw [rotationIntertwiner_ambientCartan_dominantHighest
    hn lam hdom A hcomm]
  rw [← Finset.sum_smul]
  congr 1
  simp only [Nat.cast_mul, Nat.cast_ofNat, Finset.mul_sum, Nat.cast_sum]

theorem rotationIntertwiner_dominantHighest_mem_ambientIsotropic_of_maximalCartan_range
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (A : HarmonicYoungSpace (n := n) lam →ₗ[ℝ]
      HarmonicYoungSpace (n := n) lam)
    (hcomm : ∀ a b : Fin n,
      A.comp (youngAmbientRotation lam a b) =
        (youngAmbientRotation lam a b).comp A)
    (hrange : ∀ (f : MvPolynomial (Fin ((r + 1) * n)) ℂ) (d : ℕ),
      f.IsHomogeneous d →
      totalAmbientCartan hn f = ((2 * d : ℕ) : ℂ) • f →
      ∃ q : SourceMatrix (r + 1), nullSubstitution hn q = f) :
    youngEndomorphismHighestPolynomial hn lam hdom A ∈
      ambientIsotropicHighestSubmodule hn lam := by
  apply (mem_ambientIsotropicHighestSubmodule hn lam _).mpr
  refine ⟨hrange _ (∑ i, lam i)
      (youngEndomorphismHighestPolynomial_isHomogeneous hn lam hdom A)
      (rotationIntertwiner_totalAmbientCartan_dominantHighest
        hn lam hdom A hcomm), ?_, ?_, ?_⟩
  · intro i
    exact rowDerivation_self_youngComplexPair lam
      (A (dominantHighestRealVector hn lam hdom))
      (A (dominantHighestImaginaryVector hn lam hdom)) i
  · exact rotationIntertwiner_ambientCartan_dominantHighest
      hn lam hdom A hcomm
  · intro i j hij
    exact rowDerivation_upper_youngComplexPair lam
      (A (dominantHighestRealVector hn lam hdom))
      (A (dominantHighestImaginaryVector hn lam hdom)) i j hij

theorem rotationIntertwiner_dominantHighest_mem_ambientIsotropic
    {r n : ℕ} (hn : 2 * (r + 1) ≤ n)
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam)
    (A : HarmonicYoungSpace (n := n) lam →ₗ[ℝ]
      HarmonicYoungSpace (n := n) lam)
    (hcomm : ∀ a b : Fin n,
      A.comp (youngAmbientRotation lam a b) =
        (youngAmbientRotation lam a b).comp A) :
    youngEndomorphismHighestPolynomial hn lam hdom A ∈
      ambientIsotropicHighestSubmodule hn lam :=
  rotationIntertwiner_dominantHighest_mem_ambientIsotropic_of_maximalCartan_range
    hn lam hdom A hcomm
    (fun f d hfhom hcartan =>
      maximalTotalAmbientCartan_mem_nullSubstitution_range
        hn f d hfhom hcartan)

end HigherYoungArbitraryRankDominantHighestLinePreservation

end

namespace HigherHarmonicYoung

section


open scoped BigOperators InnerProductSpace TensorProduct

namespace ArbitraryRowRaiseTensorGram

open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowDownstreamActualChannels
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowRaiseLowerTensorTrace
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowRaisingSchurTraceGram
open MetricCodes.Spherical.HigherHarmonicYoung.IsotropicAmbientHighestLine
open MetricCodes.Spherical.HigherYoungArbitraryRankGelfandTsetlinHighestEigenpair
open MetricCodes.Spherical.HigherYoungArbitraryRankDominantHighestLinePreservation
open MetricCodes.Spherical.HigherYoungCyclicHighestSchur
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower

@[simp] theorem arbitraryRowRaisingGramScalar_eq_tensorGramScalar
    {r n : ℕ} (high : Fin (r + 1) → ℕ) (row : Fin (r + 1)) :
    arbitraryRowRaisingGramScalar (n := n) high row =
      arbitraryRowRaiseTensorGramScalar (n := n) high row := rfl

theorem youngClebschRaise_arbitrary_inner_of_highestLine_and_cyclic
    {r n : ℕ} (high : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (ha : 0 < high row)
    (hn : 2 * (r + 1) ≤ n)
    (hdomhigh : Antitone high)
    (hdomlow : Antitone (loweredInternalYoungWeight high row))
    (hhighest :
      youngEndomorphismHighestPolynomial hn
          (loweredInternalYoungWeight high row) hdomlow
          ((youngClebschRaise (n := n) high
            (loweredInternalYoungWeight high row)
            (loweredInternalYoungWeight_sum_add_one high row ha)
            row).adjoint.comp
            (youngClebschRaise (n := n) high
              (loweredInternalYoungWeight high row)
              (loweredInternalYoungWeight_sum_add_one high row ha)
              row)) ∈
        ambientIsotropicHighestSubmodule hn
          (loweredInternalYoungWeight high row))
    (hcyclic : dominantHighestRotationWordSpan hn
      (loweredInternalYoungWeight high row) hdomlow = ⊤)
    (p q : HarmonicYoungSpace (n := n)
      (loweredInternalYoungWeight high row)) :
    ⟪youngClebschRaise high (loweredInternalYoungWeight high row)
        (loweredInternalYoungWeight_sum_add_one high row ha) row p,
      youngClebschRaise high (loweredInternalYoungWeight high row)
        (loweredInternalYoungWeight_sum_add_one high row ha) row q⟫_ℝ =
      arbitraryRowRaiseTensorGramScalar (n := n) high row * ⟪p, q⟫_ℝ := by
  obtain ⟨c, hreal, himaginary⟩ :=
    youngEndomorphism_dominantHighest_eigenpair hn
      (loweredInternalYoungWeight high row) hdomlow
      ((youngClebschRaise (n := n) high
        (loweredInternalYoungWeight high row)
        (loweredInternalYoungWeight_sum_add_one high row ha) row).adjoint.comp
        (youngClebschRaise (n := n) high
          (loweredInternalYoungWeight high row)
          (loweredInternalYoungWeight_sum_add_one high row ha) row)) hhighest
  simpa only [arbitraryRowRaisingGramScalar_eq_tensorGramScalar] using
    youngClebschRaise_arbitrary_inner_of_dominantCyclicHighest high row
      ha hn hdomhigh hdomlow c hreal himaginary hcyclic p q

theorem arbitraryRowRaiseTensorGram_pos
    {r n : ℕ} (high : Fin (r + 1) → ℕ)
    (row : Fin (r + 1))
    (hn : 2 * (r + 1) ≤ n)
    (ha : 0 < high row)
    (hdomhigh : Antitone high)
    (hdomlow : Antitone (loweredInternalYoungWeight high row))
    (hstrict : ∀ j : Fin (r + 1),
      j.val = row.val + 1 → high j < high row) :
    0 < arbitraryRowRaiseTensorGramScalar (n := n) high row :=
  arbitraryRowRaiseTensorGramScalar_pos high row hn ha
    hdomhigh hdomlow hstrict

theorem youngClebschRaise_arbitrary_inner_of_cyclic
    {r n : ℕ} (high : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (ha : 0 < high row)
    (hn : 2 * (r + 1) ≤ n)
    (hdomhigh : Antitone high)
    (hdomlow : Antitone (loweredInternalYoungWeight high row))
    (hcyclic : dominantHighestRotationWordSpan hn
      (loweredInternalYoungWeight high row) hdomlow = ⊤)
    (p q : HarmonicYoungSpace (n := n)
      (loweredInternalYoungWeight high row)) :
    ⟪youngClebschRaise high (loweredInternalYoungWeight high row)
        (loweredInternalYoungWeight_sum_add_one high row ha) row p,
      youngClebschRaise high (loweredInternalYoungWeight high row)
        (loweredInternalYoungWeight_sum_add_one high row ha) row q⟫_ℝ =
      arbitraryRowRaiseTensorGramScalar (n := n) high row * ⟪p, q⟫_ℝ := by
  apply youngClebschRaise_arbitrary_inner_of_highestLine_and_cyclic
    high row ha hn hdomhigh hdomlow
  · apply rotationIntertwiner_dominantHighest_mem_ambientIsotropic
      hn (loweredInternalYoungWeight high row) hdomlow
      ((youngClebschRaise (n := n) high
        (loweredInternalYoungWeight high row)
        (loweredInternalYoungWeight_sum_add_one high row ha)
        row).adjoint.comp
        (youngClebschRaise (n := n) high
          (loweredInternalYoungWeight high row)
          (loweredInternalYoungWeight_sum_add_one high row ha)
          row))
    exact youngClebschRaise_gram_rotation_intertwine
      high (loweredInternalYoungWeight high row)
      (loweredInternalYoungWeight_sum_add_one high row ha) row
  · exact hcyclic

end ArbitraryRowRaiseTensorGram

end

namespace UniversalBGGRootComplex

section


open MetricCodes.Spherical.HigherHarmonicYoung

/-- The positive root used in the spherical-code argument. -/
abbrev PositiveRoot (r : ℕ) :=
  {z : Fin (r + 1) × Fin (r + 1) // z.1 < z.2}

/-- The positive root operator used in the spherical-code argument. -/
def positiveRootOperator {r : ℕ} (n : ℕ) (α : PositiveRoot r) :
    PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n :=
  polarization r n α.val.2 α.val.1

@[simp] theorem positiveRootOperator_apply {r n : ℕ}
    (α : PositiveRoot r) (p : PolynomialSpace r n) :
    positiveRootOperator n α p =
      polarization r n α.val.2 α.val.1 p := rfl

end

section


variable {α : Type*} [LinearOrder α]

/-- The exterior root sign used in the spherical-code argument. -/
def exteriorRootSign (s : Finset α) (a : α) : ℤ :=
  (-1 : ℤ) ^ (s.filter fun x => x < a).card

theorem exteriorRoot_predecessorCard_erase_lt (s : Finset α) {a b : α}
    (ha : a ∈ s) (hab : a < b) :
    (s.filter fun x => x < b).card =
      ((s.erase a).filter fun x => x < b).card + 1 := by
  have hamem : a ∈ s.filter fun x => x < b := by
    simp only [Finset.mem_filter, ha, hab, and_self]
  rw [Finset.filter_erase]
  exact (Finset.card_erase_add_one hamem).symm

theorem exteriorRoot_predecessors_erase_not_lt (s : Finset α) {a b : α}
    (hab : ¬ a < b) :
    (s.erase a).filter (fun x => x < b) =
      s.filter (fun x => x < b) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨⟨_, hx⟩, hxb⟩
    exact ⟨hx, hxb⟩
  · rintro ⟨hx, hxb⟩
    refine ⟨⟨?_, hx⟩, hxb⟩
    intro hxa
    exact hab (hxa ▸ hxb)

theorem exteriorRootSign_erase_of_lt (s : Finset α) {a b : α}
    (ha : a ∈ s) (hab : a < b) :
    exteriorRootSign s b = - exteriorRootSign (s.erase a) b := by
  unfold exteriorRootSign
  rw [exteriorRoot_predecessorCard_erase_lt s ha hab, pow_succ]
  ring

theorem exteriorRootSign_erase_of_not_lt (s : Finset α) {a b : α}
    (hab : ¬ a < b) :
    exteriorRootSign (s.erase a) b = exteriorRootSign s b := by
  unfold exteriorRootSign
  rw [exteriorRoot_predecessors_erase_not_lt s hab]

theorem exteriorRootSign_erase_anticommute (s : Finset α) {a b : α}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    exteriorRootSign s a * exteriorRootSign (s.erase a) b =
      -(exteriorRootSign s b * exteriorRootSign (s.erase b) a) := by
  rcases lt_or_gt_of_ne hab with hab | hba
  · rw [exteriorRootSign_erase_of_lt s ha hab]
    rw [exteriorRootSign_erase_of_not_lt s (not_lt_of_gt hab)]
    ring
  · rw [exteriorRootSign_erase_of_lt s hb hba]
    rw [exteriorRootSign_erase_of_not_lt s (not_lt_of_gt hba)]
    ring

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

/-- The root wedge used in the spherical-code argument. -/
abbrev RootWedge (r k : ℕ) :=
  {S : Finset (PositiveRoot r) // S.card = k}

/-- The positive root first used in the spherical-code argument. -/
def positiveRootFirst {r : ℕ} (α : PositiveRoot r) : Fin (r + 1) :=
  α.val.1

/-- The positive root second used in the spherical-code argument. -/
def positiveRootSecond {r : ℕ} (α : PositiveRoot r) : Fin (r + 1) :=
  α.val.2

@[simp] theorem positiveRootFirst_lt_second {r : ℕ}
    (α : PositiveRoot r) : positiveRootFirst α < positiveRootSecond α :=
  α.property

theorem positiveRootFirst_ne_second {r : ℕ} (α : PositiveRoot r) :
    positiveRootFirst α ≠ positiveRootSecond α :=
  ne_of_lt (positiveRootFirst_lt_second α)

/-- The root charge used in the spherical-code argument. -/
def rootCharge {r : ℕ} (α : PositiveRoot r)
    (i : Fin (r + 1)) : ℤ :=
  if i = positiveRootFirst α then 1
  else if i = positiveRootSecond α then -1
  else 0

@[simp] theorem rootCharge_first {r : ℕ} (α : PositiveRoot r) :
    rootCharge α (positiveRootFirst α) = 1 := by
  simp only [rootCharge, ↓reduceIte]

@[simp] theorem rootCharge_second {r : ℕ} (α : PositiveRoot r) :
    rootCharge α (positiveRootSecond α) = -1 := by
  simp only [rootCharge, (positiveRootFirst_ne_second α).symm, ↓reduceIte, Int.reduceNeg]

theorem rootCharge_eq_zero_of_ne {r : ℕ}
    (α : PositiveRoot r) (i : Fin (r + 1))
    (hfirst : i ≠ positiveRootFirst α)
    (hsecond : i ≠ positiveRootSecond α) :
    rootCharge α i = 0 := by
  simp only [rootCharge, hfirst, ↓reduceIte, hsecond]

/-- The root family charge used in the spherical-code argument. -/
def rootFamilyCharge {r : ℕ} (S : Finset (PositiveRoot r))
    (i : Fin (r + 1)) : ℤ :=
  ∑ α ∈ S, rootCharge α i

@[simp] theorem rootFamilyCharge_empty {r : ℕ}
    (i : Fin (r + 1)) :
    rootFamilyCharge (∅ : Finset (PositiveRoot r)) i = 0 := by
  simp only [rootFamilyCharge, Finset.sum_empty]

@[simp] theorem rootFamilyCharge_singleton {r : ℕ}
    (α : PositiveRoot r) (i : Fin (r + 1)) :
    rootFamilyCharge ({α} : Finset (PositiveRoot r)) i =
      rootCharge α i := by
  simp only [rootFamilyCharge, Finset.sum_singleton]

theorem rootFamilyCharge_insert {r : ℕ}
    (S : Finset (PositiveRoot r)) (α : PositiveRoot r)
    (hα : α ∉ S) (i : Fin (r + 1)) :
    rootFamilyCharge (insert α S) i =
      rootCharge α i + rootFamilyCharge S i := by
  simp only [rootFamilyCharge, hα, not_false_eq_true, Finset.sum_insert]

theorem rootFamilyCharge_erase {r : ℕ}
    (S : Finset (PositiveRoot r)) (α : PositiveRoot r)
    (hα : α ∈ S) (i : Fin (r + 1)) :
    rootFamilyCharge (S.erase α) i =
      rootFamilyCharge S i - rootCharge α i := by
  have h := rootFamilyCharge_insert (S.erase α) α
    (by simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true]) i
  rw [Finset.insert_erase hα] at h
  omega

/-- The signed root weight used in the spherical-code argument. -/
def signedRootWeight {r : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (S : Finset (PositiveRoot r))
    (i : Fin (r + 1)) : ℤ :=
  (lam i : ℤ) + rootFamilyCharge S i

theorem signedRootWeight_insert {r : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (S : Finset (PositiveRoot r)) (α : PositiveRoot r)
    (hα : α ∉ S) (i : Fin (r + 1)) :
    signedRootWeight lam (insert α S) i =
      signedRootWeight lam S i + rootCharge α i := by
  rw [signedRootWeight, signedRootWeight,
    rootFamilyCharge_insert S α hα]
  omega

theorem signedRootWeight_erase {r : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (S : Finset (PositiveRoot r)) (α : PositiveRoot r)
    (hα : α ∈ S) (i : Fin (r + 1)) :
    signedRootWeight lam (S.erase α) i =
      signedRootWeight lam S i - rootCharge α i := by
  rw [signedRootWeight, signedRootWeight,
    rootFamilyCharge_erase S α hα]
  omega

/-- The admissible root wedge used in the spherical-code argument. -/
abbrev AdmissibleRootWedge {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (k : ℕ) :=
  {S : RootWedge r k // ∀ i, 0 ≤ signedRootWeight lam S.val i}

/-- The root wedge weight used in the spherical-code argument. -/
def rootWedgeWeight {r k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k)
    (i : Fin (r + 1)) : ℕ :=
  (signedRootWeight lam S.val.val i).toNat

@[simp] theorem rootWedgeWeight_cast {r k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k)
    (i : Fin (r + 1)) :
    (rootWedgeWeight lam S i : ℤ) =
      signedRootWeight lam S.val.val i := by
  simp only [rootWedgeWeight, Int.toNat_of_nonneg (S.property i)]

/-- The root joint harmonic chain used in the spherical-code argument. -/
abbrev RootJointHarmonicChain {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) (k : ℕ) :=
  ∀ S : AdmissibleRootWedge lam k,
    JointHarmonicWeightSpace n (rootWedgeWeight lam S)

/-- The root polynomial chain used in the spherical-code argument. -/
abbrev RootPolynomialChain (r n k : ℕ) :=
  RootWedge r k → PolynomialSpace r n

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.BGGRootComplex

/-- The root vector used in the spherical-code argument. -/
abbrev RootVector (r : ℕ) := PositiveRoot r →₀ ℝ

/-- The root structure constant used in the spherical-code argument. -/
def rootStructureConstant {r : ℕ} (α β γ : PositiveRoot r) : ℝ :=
  (if α.val.1 = β.val.2 ∧ γ.val = (β.val.1, α.val.2) then 1 else 0) -
    (if β.val.1 = α.val.2 ∧ γ.val = (α.val.1, β.val.2) then 1 else 0)

/-- The root bracket used in the spherical-code argument. -/
def rootBracket {r : ℕ} (α β : PositiveRoot r) : RootVector r :=
  ∑ γ : PositiveRoot r,
    rootStructureConstant α β γ • Finsupp.single γ (1 : ℝ)

@[simp] theorem rootBracket_apply {r : ℕ} (α β γ : PositiveRoot r) :
    rootBracket α β γ = rootStructureConstant α β γ := by
  classical
  simp only [rootBracket, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

private def rootAction {r : ℕ} (n : ℕ) :
    RootVector r →ₗ[ℝ]
      (PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n) :=
  Finsupp.linearCombination ℝ (positiveRootOperator n)

@[simp] theorem rootAction_single {r n : ℕ} (α : PositiveRoot r) (c : ℝ) :
    rootAction n (Finsupp.single α c) = c • positiveRootOperator n α := by
  simp only [rootAction, Finsupp.linearCombination_single]

theorem positiveRootOperator_commutator {r n : ℕ}
    (α β : PositiveRoot r) :
    (positiveRootOperator n α).comp (positiveRootOperator n β) -
        (positiveRootOperator n β).comp (positiveRootOperator n α) =
      ∑ γ : PositiveRoot r,
        rootStructureConstant α β γ • positiveRootOperator n γ := by
  classical
  apply LinearMap.ext
  intro p
  have hcomm := polarization_polarization_commutator
    (r := r) (n := n) α.val.2 α.val.1 β.val.2 β.val.1 p
  simp only [LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.sum_apply, LinearMap.smul_apply,
    positiveRootOperator_apply]
  change
    polarization r n α.val.2 α.val.1
        (polarization r n β.val.2 β.val.1 p) -
      polarization r n β.val.2 β.val.1
        (polarization r n α.val.2 α.val.1 p) =
      ∑ γ : PositiveRoot r,
        rootStructureConstant α β γ •
          polarization r n γ.val.2 γ.val.1 p
  rw [hcomm]
  have hcancel : ∀ x y z : PolynomialSpace r n,
      (x + y - z) - x = y - z := by
    intro x y z
    abel
  rw [hcancel]
  unfold rootStructureConstant
  simp_rw [sub_smul, Finset.sum_sub_distrib]
  by_cases hfirst : α.val.1 = β.val.2
  · have hγfirst : β.val.1 < α.val.2 :=
      lt_trans β.property (hfirst ▸ α.property)
    let γfirst : PositiveRoot r := ⟨(β.val.1, α.val.2), hγfirst⟩
    have hfirstsum :
        (∑ γ : PositiveRoot r,
          (if α.val.1 = β.val.2 ∧
              γ.val = (β.val.1, α.val.2)
            then (1 : ℝ) else 0) •
              polarization r n γ.val.2 γ.val.1 p) =
          polarization r n α.val.2 β.val.1 p := by
      simp only [hfirst, true_and]
      have heq : ∀ γ : PositiveRoot r,
          γ.val = (β.val.1, α.val.2) ↔ γ = γfirst := by
        intro γ
        constructor
        · intro h
          apply Subtype.ext
          exact h
        · intro h
          subst γ
          rfl
      simp_rw [heq]
      simp only [polarization_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte, γfirst]
    rw [hfirstsum]
    by_cases hsecond : β.val.1 = α.val.2
    · have hcontra : False := by
        have := α.property
        have := β.property
        omega
      exact hcontra.elim
    · have hsecondsum :
          (∑ γ : PositiveRoot r,
            (if β.val.1 = α.val.2 ∧
                γ.val = (α.val.1, β.val.2)
              then (1 : ℝ) else 0) •
                polarization r n γ.val.2 γ.val.1 p) = 0 := by
          simp only [hsecond, false_and, ↓reduceIte, polarization_apply, zero_smul,
            Finset.sum_const_zero]
      rw [hsecondsum]
      simp only [hfirst, ↓reduceIte, polarization_apply, hsecond, sub_zero]
  · have hfirstsum :
        (∑ γ : PositiveRoot r,
          (if α.val.1 = β.val.2 ∧
              γ.val = (β.val.1, α.val.2)
            then (1 : ℝ) else 0) •
              polarization r n γ.val.2 γ.val.1 p) = 0 := by
        simp only [hfirst, false_and, ↓reduceIte, polarization_apply, zero_smul,
          Finset.sum_const_zero]
    rw [hfirstsum]
    by_cases hsecond : β.val.1 = α.val.2
    · have hγsecond : α.val.1 < β.val.2 :=
        lt_trans α.property (hsecond ▸ β.property)
      let γsecond : PositiveRoot r := ⟨(α.val.1, β.val.2), hγsecond⟩
      have hsecondsum :
          (∑ γ : PositiveRoot r,
            (if β.val.1 = α.val.2 ∧
                γ.val = (α.val.1, β.val.2)
              then (1 : ℝ) else 0) •
                polarization r n γ.val.2 γ.val.1 p) =
            polarization r n β.val.2 α.val.1 p := by
        simp only [hsecond, true_and]
        have heq : ∀ γ : PositiveRoot r,
            γ.val = (α.val.1, β.val.2) ↔ γ = γsecond := by
          intro γ
          constructor
          · intro h
            apply Subtype.ext
            exact h
          · intro h
            subst γ
            rfl
        simp_rw [heq]
        simp only [polarization_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
          Finset.mem_univ, ↓reduceIte, γsecond]
      rw [hsecondsum]
      simp only [hfirst, ↓reduceIte, hsecond, polarization_apply, zero_sub]
    · simp only [hfirst, ↓reduceIte, hsecond, sub_self, false_and, polarization_apply, zero_smul,
        Finset.sum_const_zero]

theorem rootAction_rootBracket {r n : ℕ} (α β : PositiveRoot r) :
    rootAction n (rootBracket α β) =
      (positiveRootOperator n α).comp (positiveRootOperator n β) -
        (positiveRootOperator n β).comp (positiveRootOperator n α) := by
  rw [positiveRootOperator_commutator]
  simp only [rootBracket, Finsupp.smul_single, smul_eq_mul, mul_one, map_sum, rootAction_single]

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

instance positiveRootLinearOrder (r : ℕ) : LinearOrder (PositiveRoot r) :=
  LinearOrder.lift'
    (fun α : PositiveRoot r =>
      (finProdFinEquiv (m := r + 1) (n := r + 1)) α.val)
    (fun _α _β h =>
      Subtype.ext ((finProdFinEquiv (m := r + 1) (n := r + 1)).injective h))

/-- The root wedge insert used in the spherical-code argument. -/
def rootWedgeInsert {r k : ℕ} (T : RootWedge r k)
    (α : PositiveRoot r) (hα : α ∉ T.val) : RootWedge r (k + 1) :=
  ⟨insert α T.val, by simp only [hα, not_false_eq_true, Finset.card_insert_of_notMem, T.property]⟩

@[simp] theorem rootWedgeInsert_val {r k : ℕ} (T : RootWedge r k)
    (α : PositiveRoot r) (hα : α ∉ T.val) :
    (rootWedgeInsert T α hα).val = insert α T.val := rfl

/-- The real exterior root sign used in the spherical-code argument. -/
def realExteriorRootSign {α : Type*} [LinearOrder α]
    (S : Finset α) (a : α) : ℝ :=
  (exteriorRootSign S a : ℝ)

/-- The root action boundary used in the spherical-code argument. -/
def rootActionBoundary (r n k : ℕ) :
    RootPolynomialChain r n (k + 1) →ₗ[ℝ]
      RootPolynomialChain r n k where
  toFun f T :=
    ∑ α : PositiveRoot r,
      if hα : α ∈ T.val then 0
      else realExteriorRootSign (insert α T.val) α •
        positiveRootOperator n α (f (rootWedgeInsert T α hα))
  map_add' f g := by
    funext T
    classical
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro α _
    split_ifs with hα
    · simp only [add_zero]
    · simp only [map_add, smul_add]
  map_smul' c f := by
    funext T
    classical
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro α _
    split_ifs with hα
    · simp only [smul_zero]
    · simp only [map_smul, smul_smul, mul_comm]

@[simp] theorem rootActionBoundary_apply (r n k : ℕ)
    (f : RootPolynomialChain r n (k + 1)) (T : RootWedge r k) :
    rootActionBoundary r n k f T =
      ∑ α : PositiveRoot r,
        if hα : α ∈ T.val then 0
        else realExteriorRootSign (insert α T.val) α •
          positiveRootOperator n α (f (rootWedgeInsert T α hα)) := rfl

theorem realExteriorRootSign_erase_anticommute
    {α : Type*} [LinearOrder α] (S : Finset α) {a b : α}
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    realExteriorRootSign S a * realExteriorRootSign (S.erase a) b =
      -(realExteriorRootSign S b *
          realExteriorRootSign (S.erase b) a) := by
  unfold realExteriorRootSign
  exact_mod_cast exteriorRootSign_erase_anticommute S ha hb hab

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

/-- The lower root weight used in the spherical-code argument. -/
def lowerRootWeight {r : ℕ} (μ : Fin (r + 1) → ℕ)
    (α : PositiveRoot r) (i : Fin (r + 1)) : ℕ :=
  if i = positiveRootFirst α then μ i - 1
  else if i = positiveRootSecond α then μ i + 1
  else μ i

@[simp] theorem lowerRootWeight_first {r : ℕ}
    (μ : Fin (r + 1) → ℕ) (α : PositiveRoot r) :
    lowerRootWeight μ α (positiveRootFirst α) =
      μ (positiveRootFirst α) - 1 := by
  simp only [lowerRootWeight, ↓reduceIte]

@[simp] theorem lowerRootWeight_second {r : ℕ}
    (μ : Fin (r + 1) → ℕ) (α : PositiveRoot r) :
    lowerRootWeight μ α (positiveRootSecond α) =
      μ (positiveRootSecond α) + 1 := by
  simp only [lowerRootWeight, (positiveRootFirst_ne_second α).symm, ↓reduceIte]

theorem lowerRootWeight_other {r : ℕ}
    (μ : Fin (r + 1) → ℕ) (α : PositiveRoot r)
    (i : Fin (r + 1))
    (hfirst : i ≠ positiveRootFirst α)
    (hsecond : i ≠ positiveRootSecond α) :
    lowerRootWeight μ α i = μ i := by
  simp only [lowerRootWeight, hfirst, ↓reduceIte, hsecond]

private def rootTransferBase {r : ℕ} (μ : Fin (r + 1) → ℕ)
    (α : PositiveRoot r) : Fin (r + 1) → ℕ :=
  Function.update μ (positiveRootFirst α)
    (μ (positiveRootFirst α) - 1)

theorem rootTransferSource_eq {r : ℕ}
    (μ : Fin (r + 1) → ℕ) (α : PositiveRoot r)
    (hμ : 0 < μ (positiveRootFirst α)) :
    μ = Function.update (rootTransferBase μ α)
      (positiveRootFirst α)
      (rootTransferBase μ α (positiveRootFirst α) + 1) := by
  funext i
  by_cases hi : i = positiveRootFirst α
  · subst i
    simp only [rootTransferBase, Function.update_self]
    omega
  · simp only [rootTransferBase, Function.update_self, ne_eq, hi, not_false_eq_true,
      Function.update_of_ne]

theorem rootTransferTarget_eq {r : ℕ}
    (μ : Fin (r + 1) → ℕ) (α : PositiveRoot r) :
    lowerRootWeight μ α =
      Function.update (rootTransferBase μ α)
        (positiveRootSecond α)
        (rootTransferBase μ α (positiveRootSecond α) + 1) := by
  funext i
  by_cases hfirst : i = positiveRootFirst α
  · subst i
    have hne := positiveRootFirst_ne_second α
    simp only [lowerRootWeight, ↓reduceIte, rootTransferBase, ne_eq, hne, not_false_eq_true,
      Function.update_of_ne, Function.update_self]
  · by_cases hsecond : i = positiveRootSecond α
    · subst i
      have hne := (positiveRootFirst_ne_second α).symm
      simp only [lowerRootWeight, hne, ↓reduceIte, rootTransferBase, ne_eq, not_false_eq_true,
        Function.update_of_ne, Function.update_self]
    · simp only [lowerRootWeight, hfirst, ↓reduceIte, hsecond, rootTransferBase, ne_eq,
        not_false_eq_true, Function.update_of_ne]

/-- The weighted positive root operator used in the spherical-code argument. -/
def weightedPositiveRootOperator {r : ℕ} (n : ℕ)
    (μ : Fin (r + 1) → ℕ) (α : PositiveRoot r)
    (hμ : 0 < μ (positiveRootFirst α)) :
    JointHarmonicWeightSpace n μ →ₗ[ℝ]
      JointHarmonicWeightSpace n (lowerRootWeight μ α) where
  toFun p := by
    refine ⟨⟨polarization r n (positiveRootSecond α)
      (positiveRootFirst α) (p.val : PolynomialSpace r n), ?_⟩, ?_⟩
    · rw [rootTransferTarget_eq μ α]
      apply polarization_mem_youngMultihomogeneous_transfer
        (rootTransferBase μ α) (positiveRootSecond α)
        (positiveRootFirst α)
        (Ne.symm (positiveRootFirst_ne_second α))
      rw [← rootTransferSource_eq μ α hμ]
      exact p.val.property
    · exact polarization_mem_traceFreeSubmodule
        (positiveRootSecond α) (positiveRootFirst α)
        (p.val : PolynomialSpace r n) p.property
  map_add' p q := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_add (polarization r n
      (positiveRootSecond α) (positiveRootFirst α))
      (p.val : PolynomialSpace r n) (q.val : PolynomialSpace r n)
  map_smul' c p := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_smul (polarization r n
      (positiveRootSecond α) (positiveRootFirst α)) c
      (p.val : PolynomialSpace r n)

/-- The weighted positive root operator star used in the spherical-code argument. -/
def weightedPositiveRootOperatorStar {r : ℕ} (n : ℕ)
    (μ : Fin (r + 1) → ℕ) (α : PositiveRoot r)
    (hμ : 0 < μ (positiveRootFirst α)) :
    JointHarmonicWeightSpace n (lowerRootWeight μ α) →ₗ[ℝ]
      JointHarmonicWeightSpace n μ where
  toFun p := by
    refine ⟨⟨polarization r n (positiveRootFirst α)
      (positiveRootSecond α) (p.val : PolynomialSpace r n), ?_⟩, ?_⟩
    · have hweight :=
        (mem_youngMultihomogeneousSubmodule_iff_rowEuler
          (lowerRootWeight μ α) (p.val : PolynomialSpace r n)).mp
            p.val.property
      apply (mem_youngMultihomogeneousSubmodule_iff_rowEuler μ _).mpr
      intro k
      rw [rowEuler_polarization_commutator, hweight k, map_smul]
      by_cases hfirst : k = positiveRootFirst α
      · subst k
        have hne := positiveRootFirst_ne_second α
        have hcast :
            ((μ (positiveRootFirst α) - 1 : ℕ) : ℝ) + 1 =
              (μ (positiveRootFirst α) : ℝ) := by
          exact_mod_cast Nat.sub_add_cancel hμ
        simp only [ite_true, hne, ite_false,
          lowerRootWeight_first, sub_zero]
        rw [← hcast]
        module
      · by_cases hsecond : k = positiveRootSecond α
        · subst k
          have hne := (positiveRootFirst_ne_second α).symm
          simp only [lowerRootWeight_second, Nat.cast_add, Nat.cast_one, polarization_apply,
            add_smul, one_smul, hne, ↓reduceIte, add_zero, add_sub_cancel_right]
        · simp only [lowerRootWeight_other μ α k hfirst hsecond, polarization_apply, hfirst,
            ↓reduceIte, add_zero, hsecond, sub_zero]
    · exact polarization_mem_traceFreeSubmodule
        (positiveRootFirst α) (positiveRootSecond α)
        (p.val : PolynomialSpace r n) p.property
  map_add' p q := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_add (polarization r n
      (positiveRootFirst α) (positiveRootSecond α))
      (p.val : PolynomialSpace r n) (q.val : PolynomialSpace r n)
  map_smul' c p := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_smul (polarization r n
      (positiveRootFirst α) (positiveRootSecond α)) c
      (p.val : PolynomialSpace r n)

@[simp] theorem weightedPositiveRootOperator_coe
    {r n : ℕ} (μ : Fin (r + 1) → ℕ) (α : PositiveRoot r)
    (hμ : 0 < μ (positiveRootFirst α))
    (p : JointHarmonicWeightSpace n μ) :
    (((weightedPositiveRootOperator n μ α hμ p).val :
      youngMultihomogeneousSubmodule n (lowerRootWeight μ α)) :
        PolynomialSpace r n) =
      positiveRootOperator n α (p.val : PolynomialSpace r n) := rfl

@[simp] theorem weightedPositiveRootOperatorStar_coe
    {r n : ℕ} (μ : Fin (r + 1) → ℕ) (α : PositiveRoot r)
    (hμ : 0 < μ (positiveRootFirst α))
    (q : JointHarmonicWeightSpace n (lowerRootWeight μ α)) :
    (((weightedPositiveRootOperatorStar n μ α hμ q).val :
      youngMultihomogeneousSubmodule n μ) : PolynomialSpace r n) =
      polarization r n (positiveRootFirst α) (positiveRootSecond α)
        (q.val : PolynomialSpace r n) := rfl

theorem lowerRootWeight_cast {r : ℕ}
    (μ : Fin (r + 1) → ℕ) (α : PositiveRoot r)
    (hμ : 0 < μ (positiveRootFirst α))
    (i : Fin (r + 1)) :
    ((lowerRootWeight μ α i : ℕ) : ℤ) =
      (μ i : ℤ) - rootCharge α i := by
  by_cases hfirst : i = positiveRootFirst α
  · subst i
    rw [lowerRootWeight_first, rootCharge_first]
    exact Int.ofNat_sub (show 1 ≤ μ (positiveRootFirst α) by omega)
  · by_cases hsecond : i = positiveRootSecond α
    · subst i
      rw [lowerRootWeight_second, rootCharge_second]
      simp only [Nat.cast_add, Nat.cast_one, Int.reduceNeg, sub_neg_eq_add]
    · rw [lowerRootWeight_other μ α i hfirst hsecond,
        rootCharge_eq_zero_of_ne α i hfirst hsecond]
      simp only [sub_zero]

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

/-- The root admissible insert used in the spherical-code argument. -/
def rootAdmissibleInsert {r k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (T : AdmissibleRootWedge lam k)
    (α : PositiveRoot r) (hα : α ∉ T.val.val)
    (hadm : ∀ i, 0 ≤ signedRootWeight lam (insert α T.val.val) i) :
    AdmissibleRootWedge lam (k + 1) :=
  ⟨rootWedgeInsert T.val α hα, hadm⟩

@[simp] theorem rootAdmissibleInsert_val {r k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (T : AdmissibleRootWedge lam k)
    (α : PositiveRoot r) (hα : α ∉ T.val.val)
    (hadm : ∀ i, 0 ≤ signedRootWeight lam (insert α T.val.val) i) :
    (rootAdmissibleInsert lam T α hα hadm).val.val =
      insert α T.val.val := rfl

theorem rootAdmissibleInsert_weight_charge {r k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (T : AdmissibleRootWedge lam k)
    (α : PositiveRoot r) (hα : α ∉ T.val.val)
    (hadm : ∀ i, 0 ≤ signedRootWeight lam (insert α T.val.val) i)
    (i : Fin (r + 1)) :
    ((rootWedgeWeight lam (rootAdmissibleInsert lam T α hα hadm) i : ℕ) : ℤ) =
      (rootWedgeWeight lam T i : ℤ) + rootCharge α i := by
  rw [rootWedgeWeight_cast, rootWedgeWeight_cast]
  exact signedRootWeight_insert lam T.val.val α hα i

theorem rootAdmissibleInsert_first_pos {r k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (T : AdmissibleRootWedge lam k)
    (α : PositiveRoot r) (hα : α ∉ T.val.val)
    (hadm : ∀ i, 0 ≤ signedRootWeight lam (insert α T.val.val) i) :
    0 < rootWedgeWeight lam
      (rootAdmissibleInsert lam T α hα hadm) (positiveRootFirst α) := by
  have h := rootAdmissibleInsert_weight_charge lam T α hα hadm
    (positiveRootFirst α)
  rw [rootCharge_first] at h
  omega

theorem rootAdmissibleInsert_lowerRootWeight {r k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (T : AdmissibleRootWedge lam k)
    (α : PositiveRoot r) (hα : α ∉ T.val.val)
    (hadm : ∀ i, 0 ≤ signedRootWeight lam (insert α T.val.val) i) :
    lowerRootWeight
        (rootWedgeWeight lam (rootAdmissibleInsert lam T α hα hadm)) α =
      rootWedgeWeight lam T := by
  funext i
  have hlower := lowerRootWeight_cast
    (rootWedgeWeight lam (rootAdmissibleInsert lam T α hα hadm)) α
    (rootAdmissibleInsert_first_pos lam T α hα hadm) i
  have hinsert := rootAdmissibleInsert_weight_charge
    lam T α hα hadm i
  exact_mod_cast (by omega :
    ((lowerRootWeight
        (rootWedgeWeight lam (rootAdmissibleInsert lam T α hα hadm)) α i : ℕ) : ℤ) =
      (rootWedgeWeight lam T i : ℤ))

/-- The joint harmonic weight cast used in the spherical-code argument. -/
def jointHarmonicWeightCast {r : ℕ} (n : ℕ)
    (μ ν : Fin (r + 1) → ℕ) (h : μ = ν) :
    JointHarmonicWeightSpace n μ ≃ₗ[ℝ]
      JointHarmonicWeightSpace n ν := by
  subst ν
  exact LinearEquiv.refl ℝ _

@[simp] theorem jointHarmonicWeightCast_coe {r n : ℕ}
    (μ ν : Fin (r + 1) → ℕ) (h : μ = ν)
    (p : JointHarmonicWeightSpace n μ) :
    (((jointHarmonicWeightCast n μ ν h p).val :
      youngMultihomogeneousSubmodule n ν) : PolynomialSpace r n) =
      (p.val : PolynomialSpace r n) := by
  subst ν
  rfl

/-- The weighted exterior root edge used in the spherical-code argument. -/
def weightedExteriorRootEdge {r k : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (T : AdmissibleRootWedge lam k)
    (α : PositiveRoot r) (hα : α ∉ T.val.val)
    (hadm : ∀ i, 0 ≤ signedRootWeight lam (insert α T.val.val) i) :
    JointHarmonicWeightSpace n
        (rootWedgeWeight lam (rootAdmissibleInsert lam T α hα hadm)) →ₗ[ℝ]
      JointHarmonicWeightSpace n (rootWedgeWeight lam T) :=
  (jointHarmonicWeightCast n
    (lowerRootWeight
      (rootWedgeWeight lam (rootAdmissibleInsert lam T α hα hadm)) α)
    (rootWedgeWeight lam T)
    (rootAdmissibleInsert_lowerRootWeight lam T α hα hadm)).toLinearMap.comp
      (weightedPositiveRootOperator n
        (rootWedgeWeight lam (rootAdmissibleInsert lam T α hα hadm)) α
        (rootAdmissibleInsert_first_pos lam T α hα hadm))

/-- The weighted exterior action differential used in the spherical-code argument. -/
def weightedExteriorActionDifferential {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) (k : ℕ) :
    RootJointHarmonicChain n lam (k + 1) →ₗ[ℝ]
      RootJointHarmonicChain n lam k where
  toFun f T :=
    ∑ α : PositiveRoot r,
      if hα : α ∈ T.val.val then 0
      else if hadm : ∀ i, 0 ≤ signedRootWeight lam
          (insert α T.val.val) i then
        realExteriorRootSign (insert α T.val.val) α •
          weightedExteriorRootEdge n lam T α hα hadm
            (f (rootAdmissibleInsert lam T α hα hadm))
      else 0
  map_add' f g := by
    funext T
    classical
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro α _
    split_ifs with hα hadm
    · simp only [add_zero]
    · simp only [map_add, smul_add]
    · simp only [add_zero]
  map_smul' c f := by
    funext T
    classical
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro α _
    split_ifs with hα hadm
    · simp only [smul_zero]
    · simp only [map_smul, smul_smul, mul_comm]
    · simp only [smul_zero]

@[simp] theorem weightedExteriorActionDifferential_apply {r n k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (f : RootJointHarmonicChain n lam (k + 1))
    (T : AdmissibleRootWedge lam k) :
    weightedExteriorActionDifferential n lam k f T =
      ∑ α : PositiveRoot r,
        if hα : α ∈ T.val.val then 0
        else if hadm : ∀ i, 0 ≤ signedRootWeight lam
            (insert α T.val.val) i then
          realExteriorRootSign (insert α T.val.val) α •
            weightedExteriorRootEdge n lam T α hα hadm
              (f (rootAdmissibleInsert lam T α hα hadm))
        else 0 := rfl

end

end UniversalBGGRootComplex

section


open scoped BigOperators
open ArbitraryRankMixedTraceRegularity

attribute [local instance] MvPolynomial.weightedGradedAlgebra

private def youngGramPrefixIdeal (r n k : ℕ) : Ideal (PolynomialSpace r n) :=
  Ideal.ofList ((gramQuadraticList r n).take k)

private def youngGramPrefixWeightSubmodule {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) (k : ℕ) :
    Submodule ℝ (youngMultihomogeneousSubmodule n lam) :=
  ((youngGramPrefixIdeal r n k).restrictScalars ℝ).comap
    (youngMultihomogeneousSubmodule n lam).subtype

private abbrev YoungGramPrefixWeightQuotient {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) (k : ℕ) :=
  (youngMultihomogeneousSubmodule n lam) ⧸
    youngGramPrefixWeightSubmodule n lam k

@[simp] theorem mem_youngGramPrefixWeightSubmodule
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (k : ℕ)
    (p : youngMultihomogeneousSubmodule n lam) :
    p ∈ youngGramPrefixWeightSubmodule n lam k ↔
      (p : PolynomialSpace r n) ∈ youngGramPrefixIdeal r n k := Iff.rfl

@[simp] theorem youngGramPrefixIdeal_zero (r n : ℕ) :
    youngGramPrefixIdeal r n 0 = ⊥ := by
  simp only [youngGramPrefixIdeal, List.take_zero, Ideal.ofList_nil]

@[simp] theorem youngGramPrefixWeightSubmodule_zero {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    youngGramPrefixWeightSubmodule n lam 0 = ⊥ := by
  ext p
  simp only [mem_youngGramPrefixWeightSubmodule, youngGramPrefixIdeal_zero, Submodule.mem_bot,
    ZeroMemClass.coe_eq_zero]

private def youngVariableRowWeight (r n : ℕ) :
    Fin ((r + 1) * n) → (Fin (r + 1) → ℕ) :=
  fun x => Pi.single
    ((finProdFinEquiv (m := r + 1) (n := n)).symm x).1 1

private def youngGramPairDegree {r : ℕ}
    (i j : Fin (r + 1)) : Fin (r + 1) → ℕ :=
  Pi.single i 1 + Pi.single j 1

@[simp] theorem youngVariableRowWeight_variableIndex {r n : ℕ}
    (i : Fin (r + 1)) (k : Fin n) :
    youngVariableRowWeight r n (variableIndex i k) =
      Pi.single i 1 := by
  simp only [youngVariableRowWeight, variableIndex, Equiv.symm_apply_apply]

theorem youngVariableRowWeight_weight
    {r n : ℕ} (d : Fin ((r + 1) * n) →₀ ℕ) :
    Finsupp.weight (youngVariableRowWeight r n) d =
      fun i : Fin (r + 1) => (rowExponent d i).degree := by
  classical
  ext i
  rw [Finsupp.weight_apply,
    Finsupp.sum_fintype d
      (fun x a => a • youngVariableRowWeight r n x)
      (by intro x; simp only [zero_nsmul]), rowExponent_degree]
  simp only [Finset.sum_apply]
  have h := Equiv.sum_comp
    (finProdFinEquiv (m := r + 1) (n := n))
    (fun x : Fin ((r + 1) * n) =>
      (d x • youngVariableRowWeight r n x) i)
  rw [← h]
  simp only [youngVariableRowWeight, Equiv.symm_apply_apply, Pi.smul_apply, Pi.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Fintype.sum_prod_type, variableIndex]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

theorem youngMultihomogeneousSubmodule_eq_weightedHomogeneousSubmodule
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) :
    youngMultihomogeneousSubmodule n lam =
      MvPolynomial.weightedHomogeneousSubmodule
        ℝ (youngVariableRowWeight r n) lam := by
  ext p
  rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
  constructor
  · intro hp d hd
    rw [youngVariableRowWeight_weight]
    funext i
    exact youngMultihomogeneous_rowExponent_degree
      lam hp hd i
  · intro hp
    change p.support ⊆ youngMultihomogeneousExponents n lam
    intro d hd
    have hcoeff := MvPolynomial.mem_support_iff.mp hd
    have hweight := hp hcoeff
    rw [youngVariableRowWeight_weight] at hweight
    unfold youngMultihomogeneousExponents
    rw [Finset.mem_image]
    refine ⟨fun i => rowExponent d i, ?_,
      flattenRowExponents_rowExponent d⟩
    rw [mem_rowDegreeFamilies]
    intro i
    exact congrFun hweight i

theorem youngWeightedComponent_mem_youngMultihomogeneousSubmodule
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (p : PolynomialSpace r n) :
    MvPolynomial.weightedHomogeneousComponent
        (youngVariableRowWeight r n) lam p ∈
      youngMultihomogeneousSubmodule n lam := by
  rw [youngMultihomogeneousSubmodule_eq_weightedHomogeneousSubmodule]
  exact MvPolynomial.weightedHomogeneousComponent_mem
    (youngVariableRowWeight r n) p lam

theorem rowPairingPolynomial_isWeightedHomogeneous {r n : ℕ}
    (i j : Fin (r + 1)) :
    (rowPairingPolynomial (n := n) i j).IsWeightedHomogeneous
      (youngVariableRowWeight r n) (youngGramPairDegree i j) := by
  unfold rowPairingPolynomial
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro k _
  simpa only [youngGramPairDegree, youngVariableRowWeight_variableIndex] using
    (MvPolynomial.isWeightedHomogeneous_X ℝ (youngVariableRowWeight r n) (variableIndex i k)).mul
      (MvPolynomial.isWeightedHomogeneous_X ℝ (youngVariableRowWeight r n) (variableIndex j k))

theorem rowPairingPolynomial_isHomogeneousElem {r n : ℕ}
    (i j : Fin (r + 1)) :
    SetLike.IsHomogeneousElem
      (MvPolynomial.weightedHomogeneousSubmodule
        ℝ (youngVariableRowWeight r n))
      (rowPairingPolynomial (n := n) i j) :=
  ⟨youngGramPairDegree i j,
    rowPairingPolynomial_isWeightedHomogeneous i j⟩

theorem youngGramPrefixIdeal_isHomogeneous
    (r n k : ℕ) :
    (youngGramPrefixIdeal r n k).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule
        ℝ (youngVariableRowWeight r n)) := by
  classical
  apply Ideal.homogeneous_span
  intro p hp
  change p ∈ (gramQuadraticList r n).take k at hp
  have hp' : p ∈ gramQuadraticList r n := List.mem_of_mem_take hp
  obtain ⟨z, _, rfl⟩ := List.mem_map.mp hp'
  exact rowPairingPolynomial_isHomogeneousElem z.val.1 z.val.2

theorem youngGramPrefixIdeal_weightedHomogeneousComponent_mem
    {r n k : ℕ} {p : PolynomialSpace r n}
    (hp : p ∈ youngGramPrefixIdeal r n k)
    (lam : Fin (r + 1) → ℕ) :
    MvPolynomial.weightedHomogeneousComponent
        (youngVariableRowWeight r n) lam p ∈
      youngGramPrefixIdeal r n k := by
  exact MvPolynomial.weightedHomogeneousComponent_mem_of_mem ℝ
    (youngVariableRowWeight r n)
    (youngGramPrefixIdeal_isHomogeneous r n k) hp lam

theorem finrank_youngGramPrefixWeightQuotient_add_finrank
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (k : ℕ) :
    Module.finrank ℝ (YoungGramPrefixWeightQuotient n lam k) +
        Module.finrank ℝ (youngGramPrefixWeightSubmodule n lam k) =
      ∏ i : Fin (r + 1),
        (n + lam i - 1).choose (lam i) := by
  rw [← finrank_youngMultihomogeneousSubmodule]
  exact Submodule.finrank_quotient_add_finrank _

theorem youngWeightedComponent_gram_mul
    {r n : ℕ} (i j : Fin (r + 1))
    (mu : Fin (r + 1) → ℕ) (p : PolynomialSpace r n) :
    MvPolynomial.weightedHomogeneousComponent
        (youngVariableRowWeight r n)
        (youngGramPairDegree i j + mu)
        (rowPairingPolynomial (n := n) i j * p) =
      rowPairingPolynomial (n := n) i j *
        MvPolynomial.weightedHomogeneousComponent
          (youngVariableRowWeight r n) mu p := by
  classical
  ext d
  rw [MvPolynomial.coeff_weightedHomogeneousComponent,
    MvPolynomial.coeff_mul, MvPolynomial.coeff_mul]
  by_cases hd :
      Finsupp.weight (youngVariableRowWeight r n) d =
        youngGramPairDegree i j + mu
  · rw [ite_eq_left hd]
    apply Finset.sum_congr rfl
    intro ab hab
    by_cases hg :
        MvPolynomial.coeff ab.1
          (rowPairingPolynomial (n := n) i j) = 0
    · simp only [hg, zero_mul]
    · have hga := rowPairingPolynomial_isWeightedHomogeneous i j hg
      have hab' := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
      have hb :
          Finsupp.weight (youngVariableRowWeight r n) ab.2 = mu := by
        apply add_left_cancel
        calc
          youngGramPairDegree i j +
              Finsupp.weight (youngVariableRowWeight r n) ab.2 =
            Finsupp.weight (youngVariableRowWeight r n) (ab.1 + ab.2) := by
              rw [map_add, hga]
          _ = Finsupp.weight (youngVariableRowWeight r n) d := by
            rw [hab']
          _ = youngGramPairDegree i j + mu := hd
      rw [MvPolynomial.coeff_weightedHomogeneousComponent, ite_eq_left hb]
  · rw [ite_eq_right hd]
    symm
    apply Finset.sum_eq_zero
    intro ab hab
    by_cases hg :
        MvPolynomial.coeff ab.1
          (rowPairingPolynomial (n := n) i j) = 0
    · simp only [hg, zero_mul]
    · have hga := rowPairingPolynomial_isWeightedHomogeneous i j hg
      have hab' := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
      have hb :
          Finsupp.weight (youngVariableRowWeight r n) ab.2 ≠ mu := by
        intro h
        apply hd
        calc
          Finsupp.weight (youngVariableRowWeight r n) d =
              Finsupp.weight (youngVariableRowWeight r n)
                (ab.1 + ab.2) := by rw [hab']
          _ = Finsupp.weight (youngVariableRowWeight r n) ab.1 +
                Finsupp.weight (youngVariableRowWeight r n) ab.2 := by
              rw [map_add]
          _ = youngGramPairDegree i j + mu := by rw [hga, h]
      rw [MvPolynomial.coeff_weightedHomogeneousComponent, ite_eq_right hb,
        mul_zero]

private def youngGramPairWeightMultiplication
    {r : ℕ} (n : ℕ) (i j : Fin (r + 1))
    (mu : Fin (r + 1) → ℕ) :
    youngMultihomogeneousSubmodule n mu →ₗ[ℝ]
      youngMultihomogeneousSubmodule n (youngGramPairDegree i j + mu) where
  toFun p := ⟨rowPairingPolynomial (n := n) i j *
    (p : PolynomialSpace r n), by
      rw [youngMultihomogeneousSubmodule_eq_weightedHomogeneousSubmodule,
        MvPolynomial.mem_weightedHomogeneousSubmodule]
      apply (rowPairingPolynomial_isWeightedHomogeneous i j).mul
      rw [← MvPolynomial.mem_weightedHomogeneousSubmodule,
        ← youngMultihomogeneousSubmodule_eq_weightedHomogeneousSubmodule]
      exact p.property⟩
  map_add' p q := by
    apply Subtype.ext
    simp only [Submodule.coe_add, mul_add, AddMemClass.mk_add_mk]
  map_smul' c p := by
    apply Subtype.ext
    simp only [SetLike.val_smul, Algebra.mul_smul_comm, Real.ringHom_apply, SetLike.mk_smul_mk]

theorem youngGramPrefixIdeal_succ
    {r n k : ℕ} (hk : k < (ArbitraryRankMixedTraceRegularity.gramQuadraticList r n).length) :
    youngGramPrefixIdeal r n (k + 1) =
      youngGramPrefixIdeal r n k ⊔
        Ideal.span
          ({(ArbitraryRankMixedTraceRegularity.gramQuadraticList r n)[k]} :
            Set (PolynomialSpace r n)) := by
  unfold youngGramPrefixIdeal
  rw [← List.take_concat_get'
    (ArbitraryRankMixedTraceRegularity.gramQuadraticList r n) k hk,
    Ideal.ofList_append]
  simp only [Ideal.ofList_cons, Ideal.ofList_nil, bot_le, sup_of_le_left]

theorem youngGramPrefixIdeal_le_succ
    {r n k : ℕ}
    (hk : k < (ArbitraryRankMixedTraceRegularity.gramQuadraticList r n).length) :
    youngGramPrefixIdeal r n k ≤ youngGramPrefixIdeal r n (k + 1) := by
  rw [youngGramPrefixIdeal_succ hk]
  exact le_sup_left

theorem youngGramPrefixWeightSubmodule_le_succ
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (hk : k < (ArbitraryRankMixedTraceRegularity.gramQuadraticList r n).length) :
    youngGramPrefixWeightSubmodule n lam k ≤
      youngGramPrefixWeightSubmodule n lam (k + 1) := by
  intro p hp
  exact youngGramPrefixIdeal_le_succ hk hp

private def youngGramPrefixQuotientNext
    {r : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ) (k : ℕ)
    (hk : k < (ArbitraryRankMixedTraceRegularity.gramQuadraticList r n).length) :
    YoungGramPrefixWeightQuotient n lam k →ₗ[ℝ]
      YoungGramPrefixWeightQuotient n lam (k + 1) :=
  (youngGramPrefixWeightSubmodule n lam k).mapQ
    (youngGramPrefixWeightSubmodule n lam (k + 1))
    LinearMap.id (by
      simpa only [Submodule.comap_id] using youngGramPrefixWeightSubmodule_le_succ lam hk)

theorem youngGramPrefixQuotientNext_surjective
    {r : ℕ} (n : ℕ) (lam : Fin (r + 1) → ℕ) (k : ℕ)
    (hk : k < (ArbitraryRankMixedTraceRegularity.gramQuadraticList r n).length) :
    Function.Surjective (youngGramPrefixQuotientNext n lam k hk) := by
  intro q
  obtain ⟨p, rfl⟩ :=
    (youngGramPrefixWeightSubmodule n lam (k + 1)).mkQ_surjective q
  refine ⟨(youngGramPrefixWeightSubmodule n lam k).mkQ p, ?_⟩
  rfl

private def youngGramPairPrefixQuotientMultiplication
    {r : ℕ} (n : ℕ) (i j : Fin (r + 1))
    (mu : Fin (r + 1) → ℕ) (k : ℕ) :
    YoungGramPrefixWeightQuotient n mu k →ₗ[ℝ]
      YoungGramPrefixWeightQuotient n
        (youngGramPairDegree i j + mu) k :=
  (youngGramPrefixWeightSubmodule n mu k).mapQ
    (youngGramPrefixWeightSubmodule n
      (youngGramPairDegree i j + mu) k)
    (youngGramPairWeightMultiplication n i j mu) (by
      intro p hp
      exact (youngGramPrefixIdeal r n k).mul_mem_left
        (rowPairingPolynomial (n := n) i j) hp)

theorem youngGramPairPrefixQuotientMultiplication_injective
    {r : ℕ} (n : ℕ) (i j : Fin (r + 1))
    (mu : Fin (r + 1) → ℕ) (k : ℕ)
    (hreg : ∀ p : PolynomialSpace r n,
      rowPairingPolynomial (n := n) i j * p ∈
        youngGramPrefixIdeal r n k →
      p ∈ youngGramPrefixIdeal r n k) :
    Function.Injective
      (youngGramPairPrefixQuotientMultiplication n i j mu k) := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro p hp
  induction p using Quotient.inductionOn with
  | _ p =>
      have hp' :
          rowPairingPolynomial (n := n) i j *
            (p : PolynomialSpace r n) ∈ youngGramPrefixIdeal r n k := by
        change
          Submodule.Quotient.mk
            (youngGramPairWeightMultiplication n i j mu p) = 0 at hp
        exact (Submodule.Quotient.mk_eq_zero
          (youngGramPrefixWeightSubmodule n
            (youngGramPairDegree i j + mu) k)).mp hp
      exact (Submodule.Quotient.mk_eq_zero
        (youngGramPrefixWeightSubmodule n mu k)).mpr (hreg _ hp')

theorem youngGramPairPrefixQuotient_exact
    {r : ℕ} (n : ℕ) (i j : Fin (r + 1))
    (mu : Fin (r + 1) → ℕ) (k : ℕ)
    (hk : k < (ArbitraryRankMixedTraceRegularity.gramQuadraticList r n).length)
    (hgen : (ArbitraryRankMixedTraceRegularity.gramQuadraticList r n)[k] =
      rowPairingPolynomial (n := n) i j) :
    LinearMap.range
        (youngGramPairPrefixQuotientMultiplication n i j mu k) =
      LinearMap.ker (youngGramPrefixQuotientNext n
        (youngGramPairDegree i j + mu) k hk) := by
  apply le_antisymm
  · rintro q ⟨v, rfl⟩
    induction v using Quotient.inductionOn with
    | _ v =>
        change Submodule.Quotient.mk
          (youngGramPairWeightMultiplication n i j mu v) = 0
        apply (Submodule.Quotient.mk_eq_zero
          (youngGramPrefixWeightSubmodule n
            (youngGramPairDegree i j + mu) (k + 1))).mpr
        have hg : rowPairingPolynomial (n := n) i j ∈
            youngGramPrefixIdeal r n (k + 1) := by
          rw [youngGramPrefixIdeal_succ hk, hgen]
          exact (show
            Ideal.span ({rowPairingPolynomial (n := n) i j} :
                Set (PolynomialSpace r n)) ≤
              youngGramPrefixIdeal r n k ⊔
                Ideal.span ({rowPairingPolynomial (n := n) i j} :
                  Set (PolynomialSpace r n)) from le_sup_right)
            (Ideal.subset_span (by simp only [Set.mem_singleton_iff]))
        exact (youngGramPrefixIdeal r n (k + 1)).mul_mem_right
          (v : PolynomialSpace r n) hg
  · intro q hq
    induction q using Quotient.inductionOn with
    | _ p =>
        have hpnext : (p : PolynomialSpace r n) ∈
            youngGramPrefixIdeal r n (k + 1) := by
          change Submodule.Quotient.mk p = 0 at hq
          exact (Submodule.Quotient.mk_eq_zero
            (youngGramPrefixWeightSubmodule n
              (youngGramPairDegree i j + mu) (k + 1))).mp hq
        rw [youngGramPrefixIdeal_succ hk,
          hgen, sup_comm] at hpnext
        obtain ⟨b, u, hu, hdecomp⟩ :=
          Ideal.mem_span_singleton_sup.mp hpnext
        let v : youngMultihomogeneousSubmodule n mu :=
          ⟨MvPolynomial.weightedHomogeneousComponent
            (youngVariableRowWeight r n) mu b,
            youngWeightedComponent_mem_youngMultihomogeneousSubmodule mu b⟩
        refine ⟨(youngGramPrefixWeightSubmodule n mu k).mkQ v, ?_⟩
        change
          Submodule.Quotient.mk
              (youngGramPairWeightMultiplication n i j mu v) =
            Submodule.Quotient.mk p
        apply (Submodule.Quotient.eq
          (youngGramPrefixWeightSubmodule n
            (youngGramPairDegree i j + mu) k)).mpr
        have hhom :
            (p : PolynomialSpace r n).IsWeightedHomogeneous
              (youngVariableRowWeight r n)
              (youngGramPairDegree i j + mu) := by
          rw [← MvPolynomial.mem_weightedHomogeneousSubmodule,
            ← youngMultihomogeneousSubmodule_eq_weightedHomogeneousSubmodule]
          exact p.property
        have hpdecomp :
            (p : PolynomialSpace r n) =
              rowPairingPolynomial (n := n) i j *
                  MvPolynomial.weightedHomogeneousComponent
                    (youngVariableRowWeight r n) mu b +
                MvPolynomial.weightedHomogeneousComponent
                  (youngVariableRowWeight r n)
                  (youngGramPairDegree i j + mu) u := by
          calc
            (p : PolynomialSpace r n) =
                MvPolynomial.weightedHomogeneousComponent
                  (youngVariableRowWeight r n)
                  (youngGramPairDegree i j + mu)
                  (p : PolynomialSpace r n) :=
              (MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_same
                hhom).symm
            _ = MvPolynomial.weightedHomogeneousComponent
                  (youngVariableRowWeight r n)
                  (youngGramPairDegree i j + mu)
                  (b * rowPairingPolynomial (n := n) i j + u) := by
              rw [hdecomp]
            _ = _ := by
              rw [map_add, mul_comm b,
                youngWeightedComponent_gram_mul]
        change
          rowPairingPolynomial (n := n) i j *
                MvPolynomial.weightedHomogeneousComponent
                  (youngVariableRowWeight r n) mu b -
              (p : PolynomialSpace r n) ∈ youngGramPrefixIdeal r n k
        rw [hpdecomp]
        simpa only [sub_add_cancel_left, neg_mem_iff] using
          (youngGramPrefixIdeal r n k).neg_mem
            (youngGramPrefixIdeal_weightedHomogeneousComponent_mem hu (youngGramPairDegree i j +
              mu))

theorem finrank_youngGramPrefixWeightQuotient_succ_of_fits
    {r : ℕ} (n : ℕ) (i j : Fin (r + 1))
    (mu : Fin (r + 1) → ℕ) (k : ℕ)
    (hk : k < (ArbitraryRankMixedTraceRegularity.gramQuadraticList r n).length)
    (hgen : (ArbitraryRankMixedTraceRegularity.gramQuadraticList r n)[k] =
      rowPairingPolynomial (n := n) i j)
    (hreg : ∀ p : PolynomialSpace r n,
      rowPairingPolynomial (n := n) i j * p ∈
        youngGramPrefixIdeal r n k →
      p ∈ youngGramPrefixIdeal r n k) :
    Module.finrank ℝ
          (YoungGramPrefixWeightQuotient n
            (youngGramPairDegree i j + mu) (k + 1)) +
        Module.finrank ℝ (YoungGramPrefixWeightQuotient n mu k) =
      Module.finrank ℝ
        (YoungGramPrefixWeightQuotient n
          (youngGramPairDegree i j + mu) k) := by
  have h :=
    (youngGramPrefixQuotientNext n
      (youngGramPairDegree i j + mu) k hk).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr
    (youngGramPrefixQuotientNext_surjective n
      (youngGramPairDegree i j + mu) k hk), finrank_top,
    ← youngGramPairPrefixQuotient_exact n i j mu k hk hgen,
    LinearMap.finrank_range_of_inj
      (youngGramPairPrefixQuotientMultiplication_injective
        n i j mu k hreg)] at h
  exact h

theorem youngWeightedComponent_gram_mul_eq_zero_of_overweight
    {r n : ℕ} (i j : Fin (r + 1))
    (lam : Fin (r + 1) → ℕ) (a : Fin (r + 1))
    (hover : lam a < youngGramPairDegree i j a)
    (p : PolynomialSpace r n) :
    MvPolynomial.weightedHomogeneousComponent
        (youngVariableRowWeight r n) lam
        (rowPairingPolynomial (n := n) i j * p) = 0 := by
  classical
  ext d
  rw [MvPolynomial.coeff_weightedHomogeneousComponent,
    MvPolynomial.coeff_zero]
  by_cases hd : Finsupp.weight (youngVariableRowWeight r n) d = lam
  · rw [ite_eq_left hd, MvPolynomial.coeff_mul]
    apply Finset.sum_eq_zero
    intro bc hbc
    by_cases hg :
        MvPolynomial.coeff bc.1
          (rowPairingPolynomial (n := n) i j) = 0
    · simp only [hg, zero_mul]
    · have hga := rowPairingPolynomial_isWeightedHomogeneous i j hg
      have hbc' := Finset.HasAntidiagonal.mem_antidiagonal.mp hbc
      have hdegree :
          lam a = youngGramPairDegree i j a +
            Finsupp.weight (youngVariableRowWeight r n) bc.2 a := by
        calc
          lam a = Finsupp.weight (youngVariableRowWeight r n) d a :=
            congrFun hd.symm a
          _ = Finsupp.weight (youngVariableRowWeight r n)
                (bc.1 + bc.2) a := by rw [hbc']
          _ = youngGramPairDegree i j a +
              Finsupp.weight (youngVariableRowWeight r n) bc.2 a := by
                rw [map_add, hga]
                rfl
      omega
  · simp only [hd, ↓reduceIte]

theorem youngGramPrefixWeightSubmodule_succ_eq_of_overweight
    {r : ℕ} (n : ℕ) (i j : Fin (r + 1))
    (lam : Fin (r + 1) → ℕ) (a : Fin (r + 1)) (k : ℕ)
    (hk : k < (ArbitraryRankMixedTraceRegularity.gramQuadraticList r n).length)
    (hgen : (ArbitraryRankMixedTraceRegularity.gramQuadraticList r n)[k] =
      rowPairingPolynomial (n := n) i j)
    (hover : lam a < youngGramPairDegree i j a) :
    youngGramPrefixWeightSubmodule n lam (k + 1) =
      youngGramPrefixWeightSubmodule n lam k := by
  apply le_antisymm
  · intro p hp
    change (p : PolynomialSpace r n) ∈
      youngGramPrefixIdeal r n (k + 1) at hp
    rw [youngGramPrefixIdeal_succ hk,
      hgen, sup_comm] at hp
    obtain ⟨b, u, hu, hdecomp⟩ :=
      Ideal.mem_span_singleton_sup.mp hp
    have hhom : (p : PolynomialSpace r n).IsWeightedHomogeneous
        (youngVariableRowWeight r n) lam := by
      rw [← MvPolynomial.mem_weightedHomogeneousSubmodule,
        ← youngMultihomogeneousSubmodule_eq_weightedHomogeneousSubmodule]
      exact p.property
    have heq :
        (p : PolynomialSpace r n) =
          MvPolynomial.weightedHomogeneousComponent
            (youngVariableRowWeight r n) lam u := by
      calc
        (p : PolynomialSpace r n) =
            MvPolynomial.weightedHomogeneousComponent
              (youngVariableRowWeight r n) lam
              (p : PolynomialSpace r n) :=
          (MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_same
            hhom).symm
        _ = MvPolynomial.weightedHomogeneousComponent
              (youngVariableRowWeight r n) lam
              (b * rowPairingPolynomial (n := n) i j + u) := by
          rw [hdecomp]
        _ = _ := by
          rw [map_add, mul_comm b,
            youngWeightedComponent_gram_mul_eq_zero_of_overweight
              i j lam a hover, zero_add]
    change (p : PolynomialSpace r n) ∈ youngGramPrefixIdeal r n k
    rw [heq]
    exact youngGramPrefixIdeal_weightedHomogeneousComponent_mem hu lam
  · exact youngGramPrefixWeightSubmodule_le_succ lam hk

theorem finrank_youngGramPrefixWeightQuotient_succ_of_overweight
    {r : ℕ} (n : ℕ) (i j : Fin (r + 1))
    (lam : Fin (r + 1) → ℕ) (a : Fin (r + 1)) (k : ℕ)
    (hk : k < (ArbitraryRankMixedTraceRegularity.gramQuadraticList r n).length)
    (hgen : (ArbitraryRankMixedTraceRegularity.gramQuadraticList r n)[k] =
      rowPairingPolynomial (n := n) i j)
    (hover : lam a < youngGramPairDegree i j a) :
    Module.finrank ℝ (YoungGramPrefixWeightQuotient n lam (k + 1)) =
      Module.finrank ℝ (YoungGramPrefixWeightQuotient n lam k) := by
  change
    Module.finrank ℝ
        ((youngMultihomogeneousSubmodule n lam) ⧸
          youngGramPrefixWeightSubmodule n lam (k + 1)) =
      Module.finrank ℝ
        ((youngMultihomogeneousSubmodule n lam) ⧸
          youngGramPrefixWeightSubmodule n lam k)
  rw [youngGramPrefixWeightSubmodule_succ_eq_of_overweight
    n i j lam a k hk hgen hover]

end

section


open scoped BigOperators
open ArbitraryRankMixedTraceRegularity

/-- The gram pair row degree used in the spherical-code argument. -/
def gramPairRowDegree {r : ℕ}
    (z : UpperGramPair r) (i : Fin (r + 1)) : ℕ :=
  (if z.val.1 = i then 1 else 0) +
    (if z.val.2 = i then 1 else 0)

theorem gramPairRowDegree_eq_youngGramPairDegree {r : ℕ}
    (z : UpperGramPair r) :
    gramPairRowDegree z = youngGramPairDegree z.val.1 z.val.2 := by
  funext i
  simp only [gramPairRowDegree, eq_comm, youngGramPairDegree, Pi.add_apply, Pi.single_apply]

/-- The gram family row degree used in the spherical-code argument. -/
def gramFamilyRowDegree {r : ℕ}
    (s : Finset (UpperGramPair r)) (i : Fin (r + 1)) : ℕ :=
  ∑ z ∈ s, gramPairRowDegree z i

@[simp] theorem gramFamilyRowDegree_insert {r : ℕ}
    (s : Finset (UpperGramPair r)) (z : UpperGramPair r)
    (hz : z ∉ s) (i : Fin (r + 1)) :
    gramFamilyRowDegree (insert z s) i =
      gramPairRowDegree z i + gramFamilyRowDegree s i := by
  simp only [gramFamilyRowDegree, hz, not_false_eq_true, Finset.sum_insert]

/-- The shifted young ambient coefficient used in the spherical-code argument. -/
def shiftedYoungAmbientCoefficient {r : ℕ}
    (n : ℕ) (lam delta : Fin (r + 1) → ℕ) : ℕ :=
  ∏ i : Fin (r + 1),
    if delta i ≤ lam i then
      (n + (lam i - delta i) - 1).choose (lam i - delta i)
    else 0

theorem shiftedYoungAmbientCoefficient_eq_zero_of_not_le
    {r n : ℕ} (lam delta : Fin (r + 1) → ℕ)
    (i : Fin (r + 1)) (hi : lam i < delta i) :
    shiftedYoungAmbientCoefficient n lam delta = 0 := by
  unfold shiftedYoungAmbientCoefficient
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp only [Nat.not_le.mpr hi, ↓reduceIte]

theorem shiftedYoungAmbientCoefficient_add {r n : ℕ}
    (lam delta epsilon : Fin (r + 1) → ℕ)
    (hdelta : ∀ i, delta i ≤ lam i) :
    shiftedYoungAmbientCoefficient n lam
        (fun i => delta i + epsilon i) =
      shiftedYoungAmbientCoefficient n
        (fun i => lam i - delta i) epsilon := by
  unfold shiftedYoungAmbientCoefficient
  apply Finset.prod_congr rfl
  intro i _
  have hd : delta i ≤ lam i := hdelta i
  have hiff : delta i + epsilon i ≤ lam i ↔
      epsilon i ≤ lam i - delta i := by
    omega
  by_cases h : epsilon i ≤ lam i - delta i
  · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
    have hres : lam i - (delta i + epsilon i) =
        (lam i - delta i) - epsilon i := by
      omega
    simpa only using congrArg
      (fun d : ℕ => (n + d - 1).choose d) hres
  · rw [ite_eq_right (mt hiff.mp h), ite_eq_right h]

/-- The gram koszul coefficient used in the spherical-code argument. -/
def gramKoszulCoefficient {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (s : Finset (UpperGramPair r)) : ℤ :=
  ∑ t ∈ s.powerset,
    (-1 : ℤ) ^ t.card *
      (shiftedYoungAmbientCoefficient n lam
        (gramFamilyRowDegree t) : ℤ)

@[simp] theorem gramKoszulCoefficient_empty {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    gramKoszulCoefficient n lam (∅ : Finset (UpperGramPair r)) =
      (∏ i : Fin (r + 1),
        (n + lam i - 1).choose (lam i) : ℕ) := by
  simp only [gramKoszulCoefficient, Finset.powerset_empty, Int.reduceNeg,
    shiftedYoungAmbientCoefficient, gramFamilyRowDegree, Nat.cast_prod, Finset.sum_singleton,
      Finset.card_empty, pow_zero, Finset.sum_empty,
    zero_le, ↓reduceIte, tsub_zero, one_mul]

theorem gramKoszulCoefficient_insert {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (s : Finset (UpperGramPair r)) (z : UpperGramPair r)
    (hz : z ∉ s) :
    gramKoszulCoefficient n lam (insert z s) =
      gramKoszulCoefficient n lam s -
        if ∀ i, gramPairRowDegree z i ≤ lam i then
          gramKoszulCoefficient n
            (fun i => lam i - gramPairRowDegree z i) s
        else 0 := by
  classical
  unfold gramKoszulCoefficient
  rw [Finset.sum_powerset_insert hz]
  by_cases hdeg : ∀ i, gramPairRowDegree z i ≤ lam i
  · rw [ite_eq_left hdeg]
    have hsum :
        (∑ t ∈ s.powerset,
          (-1 : ℤ) ^ (insert z t).card *
            (shiftedYoungAmbientCoefficient n lam
              (gramFamilyRowDegree (insert z t)) : ℤ)) =
          -(∑ t ∈ s.powerset,
            (-1 : ℤ) ^ t.card *
              (shiftedYoungAmbientCoefficient n
                (fun i => lam i - gramPairRowDegree z i)
                (gramFamilyRowDegree t) : ℤ)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro t ht
      have hzt : z ∉ t :=
        Finset.notMem_mono (Finset.mem_powerset.mp ht) hz
      have hdegrees : gramFamilyRowDegree (insert z t) =
          (fun i => gramPairRowDegree z i + gramFamilyRowDegree t i) := by
        funext i
        exact gramFamilyRowDegree_insert t z hzt i
      rw [Finset.card_insert_of_notMem hzt, pow_succ, hdegrees,
        shiftedYoungAmbientCoefficient_add lam _ _ hdeg]
      ring
    rw [hsum]
    ring
  · rw [ite_eq_right hdeg, sub_zero]
    have hsum :
        (∑ t ∈ s.powerset,
          (-1 : ℤ) ^ (insert z t).card *
            (shiftedYoungAmbientCoefficient n lam
              (gramFamilyRowDegree (insert z t)) : ℤ)) = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      obtain ⟨i, hi⟩ := not_forall.mp hdeg
      have hzt : z ∉ t :=
        Finset.notMem_mono (Finset.mem_powerset.mp ht) hz
      have hbad : lam i < gramFamilyRowDegree (insert z t) i := by
        rw [gramFamilyRowDegree_insert t z hzt i]
        exact lt_of_lt_of_le (Nat.lt_of_not_ge hi) (Nat.le_add_right _ _)
      rw [shiftedYoungAmbientCoefficient_eq_zero_of_not_le lam _ i hbad,
        Nat.cast_zero, mul_zero]
    rw [hsum, add_zero]

/-- The full gram koszul coefficient used in the spherical-code argument. -/
def fullGramKoszulCoefficient {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) : ℤ :=
  gramKoszulCoefficient n lam (Finset.univ : Finset (UpperGramPair r))

private def gramPrefixPairFinset (r k : ℕ) : Finset (UpperGramPair r) :=
  ((Finset.univ : Finset (UpperGramPair r)).toList.take k).toFinset

@[simp] theorem gramPrefixPairFinset_zero (r : ℕ) :
    gramPrefixPairFinset r 0 = ∅ := by
  simp only [gramPrefixPairFinset, List.take_zero, List.toFinset_nil]

@[simp] theorem gramPrefixPairFinset_length (r n : ℕ) :
    gramPrefixPairFinset r (gramQuadraticList r n).length =
      (Finset.univ : Finset (UpperGramPair r)) := by
  have hlen : (gramQuadraticList r n).length =
      (Finset.univ : Finset (UpperGramPair r)).toList.length := by
    simp only [gramQuadraticList, List.length_map, Finset.length_toList, Finset.card_univ]
  unfold gramPrefixPairFinset
  rw [hlen, List.take_length, Finset.toList_toFinset]

private def gramPairAt {r : ℕ} (k : Fin (Fintype.card (UpperGramPair r))) :
    UpperGramPair r :=
  ((Finset.univ : Finset (UpperGramPair r)).toList).get
    ⟨k, by simp⟩

theorem gramPrefixPairFinset_succ {r : ℕ}
    (k : Fin (Fintype.card (UpperGramPair r))) :
    gramPrefixPairFinset r (k.val + 1) =
      insert (gramPairAt k) (gramPrefixPairFinset r k.val) := by
  classical
  unfold gramPrefixPairFinset
  rw [List.take_succ_eq_append_getElem (by simp)]
  rw [List.toFinset_append]
  simp only [List.toFinset_cons, List.toFinset_nil, insert_empty_eq, Finset.union_singleton,
    gramPairAt, List.get_eq_getElem]

theorem gramPairAt_not_mem_gramPrefixPairFinset {r : ℕ}
    (k : Fin (Fintype.card (UpperGramPair r))) :
    gramPairAt k ∉ gramPrefixPairFinset r k.val := by
  classical
  intro hmem
  have hlist : gramPairAt k ∈
      (Finset.univ : Finset (UpperGramPair r)).toList.take k.val :=
    List.mem_toFinset.mp hmem
  have hall : gramPairAt k ∈
      (Finset.univ : Finset (UpperGramPair r)).toList := by
    simp only [Finset.mem_toList, Finset.mem_univ]
  have hidx :=
    (List.mem_take_iff_idxOf_lt hall).mp hlist
  have hnodup := Finset.nodup_toList
    (Finset.univ : Finset (UpperGramPair r))
  have heq :
      ((Finset.univ : Finset (UpperGramPair r)).toList).idxOf
        (gramPairAt k) = k.val := by
    unfold gramPairAt
    simpa only [List.get_eq_getElem] using hnodup.idxOf_getElem k.val (by simp)
  omega

theorem gramKoszulCoefficient_prefix_succ {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (k : Fin (Fintype.card (UpperGramPair r))) :
    gramKoszulCoefficient n lam (gramPrefixPairFinset r (k.val + 1)) =
      gramKoszulCoefficient n lam (gramPrefixPairFinset r k.val) -
        if ∀ i, gramPairRowDegree (gramPairAt k) i ≤ lam i then
          gramKoszulCoefficient n
            (fun i => lam i - gramPairRowDegree (gramPairAt k) i)
            (gramPrefixPairFinset r k.val)
        else 0 := by
  rw [gramPrefixPairFinset_succ]
  exact gramKoszulCoefficient_insert lam _ _
    (gramPairAt_not_mem_gramPrefixPairFinset k)

theorem finrank_youngGramPrefixWeightQuotient_zero
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) :
    Module.finrank ℝ (YoungGramPrefixWeightQuotient n lam 0) =
      ∏ i : Fin (r + 1),
        (n + lam i - 1).choose (lam i) := by
  have h :=
    finrank_youngGramPrefixWeightQuotient_add_finrank (n := n) lam 0
  have hz : Module.finrank ℝ
      (youngGramPrefixWeightSubmodule n lam 0) = 0 := by
    simp only [Submodule.finrank_eq_zero, youngGramPrefixWeightSubmodule_zero]
  omega

theorem finrank_youngGramPrefixWeightQuotient_eq_gramKoszulCoefficient_of_recurrence
    {r n : ℕ}
    (hstep : ∀ (lam : Fin (r + 1) → ℕ)
      (k : Fin (Fintype.card (UpperGramPair r))),
      (Module.finrank ℝ
          (YoungGramPrefixWeightQuotient n lam (k.val + 1)) : ℤ) =
        (Module.finrank ℝ
          (YoungGramPrefixWeightQuotient n lam k.val) : ℤ) -
          if ∀ i, gramPairRowDegree (gramPairAt k) i ≤ lam i then
            (Module.finrank ℝ
              (YoungGramPrefixWeightQuotient n
                (fun i => lam i - gramPairRowDegree (gramPairAt k) i)
                k.val) : ℤ)
          else 0)
    (k : ℕ) (hk : k ≤ Fintype.card (UpperGramPair r))
    (lam : Fin (r + 1) → ℕ) :
    (Module.finrank ℝ
        (YoungGramPrefixWeightQuotient n lam k) : ℤ) =
      gramKoszulCoefficient n lam (gramPrefixPairFinset r k) := by
  induction k generalizing lam with
  | zero =>
      simp [finrank_youngGramPrefixWeightQuotient_zero]
  | succ k ih =>
      have hklt : k < Fintype.card (UpperGramPair r) := by omega
      have hkle : k ≤ Fintype.card (UpperGramPair r) := by omega
      let j : Fin (Fintype.card (UpperGramPair r)) := ⟨k, hklt⟩
      calc
        (Module.finrank ℝ
            (YoungGramPrefixWeightQuotient n lam (k + 1)) : ℤ) =
          (Module.finrank ℝ
            (YoungGramPrefixWeightQuotient n lam k) : ℤ) -
            if ∀ i, gramPairRowDegree (gramPairAt j) i ≤ lam i then
              (Module.finrank ℝ
                (YoungGramPrefixWeightQuotient n
                  (fun i => lam i - gramPairRowDegree (gramPairAt j) i)
                  k) : ℤ)
            else 0 := hstep lam j
        _ = gramKoszulCoefficient n lam
            (gramPrefixPairFinset r (k + 1)) := by
          rw [gramKoszulCoefficient_prefix_succ lam j,
            ih hkle lam]
          split_ifs with h
          · rw [ih hkle
              (fun i => lam i - gramPairRowDegree (gramPairAt j) i)]
          · rfl

/-- The weyl shift used in the spherical-code argument. -/
def weylShift {r : ℕ} (lam : Fin (r + 1) → ℕ)
    (σ : Equiv.Perm (Fin (r + 1))) (i : Fin (r + 1)) : ℤ :=
  (lam i : ℤ) - (i.val : ℤ) + ((σ i).val : ℤ)

/-- The signed full gram koszul coefficient used in the spherical-code argument. -/
def signedFullGramKoszulCoefficient {r : ℕ}
    (n : ℕ) (mu : Fin (r + 1) → ℤ) : ℤ :=
  if ∀ i, 0 ≤ mu i then
    fullGramKoszulCoefficient n (fun i => (mu i).toNat)
  else 0

/-- The alternating gram koszul coefficient used in the spherical-code argument. -/
def alternatingGramKoszulCoefficient {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) : ℤ :=
  ∑ σ : Equiv.Perm (Fin (r + 1)),
    (Equiv.Perm.sign σ : ℤ) *
      signedFullGramKoszulCoefficient n (weylShift lam σ)

theorem youngGramPrefixIdeal_length (r n : ℕ) :
    youngGramPrefixIdeal r n (gramQuadraticList r n).length =
      youngGramRadialIdeal r n := by
  simp only [youngGramPrefixIdeal, List.take_length,
    gramQuadraticList_ideal_eq_youngGramRadialIdeal]

theorem youngGramPrefixWeightSubmodule_length {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    youngGramPrefixWeightSubmodule n lam
        (gramQuadraticList r n).length =
      youngGramRadialWeightSubmodule n lam := by
  simp only [youngGramPrefixWeightSubmodule, youngGramPrefixIdeal_length,
    youngGramRadialWeightSubmodule]

theorem gramQuadraticList_length_eq_upperGramPair_card (r n : ℕ) :
    (gramQuadraticList r n).length =
      Fintype.card (UpperGramPair r) := by
  simp only [gramQuadraticList, List.length_map, Finset.length_toList, Finset.card_univ]

theorem gramQuadraticList_getElem_gramPairAt {r n : ℕ}
    (k : Fin (Fintype.card (UpperGramPair r))) :
    (gramQuadraticList r n).get
        ⟨k.val, by simp [gramQuadraticList]⟩ =
      gramPairPolynomial n (gramPairAt k) := by
  simp only [gramQuadraticList, List.get_eq_getElem, List.getElem_map, gramPairAt]

theorem gramPairAt_mul_mem_prefix_of_weaklyRegular
    {r n : ℕ}
    (hregular : RingTheory.Sequence.IsWeaklyRegular
      (PolynomialSpace r n) (gramQuadraticList r n))
    (k : Fin (Fintype.card (UpperGramPair r)))
    (p : PolynomialSpace r n)
    (hp : gramPairPolynomial n (gramPairAt k) * p ∈
      youngGramPrefixIdeal r n k.val) :
    p ∈ youngGramPrefixIdeal r n k.val := by
  have hsat :=
    (gramQuadraticList_weaklyRegular_iff_saturation r n).mp hregular
  let j : Fin (gramQuadraticList r n).length :=
    ⟨k.val, by simp [gramQuadraticList]⟩
  apply hsat j p
  change (gramQuadraticList r n).get j * p ∈
    youngGramPrefixIdeal r n k.val
  rw [show (gramQuadraticList r n).get j =
    gramPairPolynomial n (gramPairAt k) from
      gramQuadraticList_getElem_gramPairAt k]
  exact hp

theorem youngGramPrefixWeightQuotient_signed_recurrence_of_fits_and_overweight
    {r n : ℕ}
    (hfits : ∀ (k : Fin (Fintype.card (UpperGramPair r)))
      (mu : Fin (r + 1) → ℕ),
      Module.finrank ℝ
          (YoungGramPrefixWeightQuotient n
            (youngGramPairDegree (gramPairAt k).val.1
              (gramPairAt k).val.2 + mu) (k.val + 1)) +
        Module.finrank ℝ
          (YoungGramPrefixWeightQuotient n mu k.val) =
        Module.finrank ℝ
          (YoungGramPrefixWeightQuotient n
            (youngGramPairDegree (gramPairAt k).val.1
              (gramPairAt k).val.2 + mu) k.val))
    (hoverweight : ∀ (k : Fin (Fintype.card (UpperGramPair r)))
      (lam : Fin (r + 1) → ℕ)
      (i : Fin (r + 1)),
      lam i < youngGramPairDegree
        (gramPairAt k).val.1 (gramPairAt k).val.2 i →
        Module.finrank ℝ
          (YoungGramPrefixWeightQuotient n lam (k.val + 1)) =
        Module.finrank ℝ
          (YoungGramPrefixWeightQuotient n lam k.val))
    (lam : Fin (r + 1) → ℕ)
    (k : Fin (Fintype.card (UpperGramPair r))) :
    (Module.finrank ℝ
        (YoungGramPrefixWeightQuotient n lam (k.val + 1)) : ℤ) =
      (Module.finrank ℝ
        (YoungGramPrefixWeightQuotient n lam k.val) : ℤ) -
        if ∀ i, gramPairRowDegree (gramPairAt k) i ≤ lam i then
          (Module.finrank ℝ
            (YoungGramPrefixWeightQuotient n
              (fun i => lam i - gramPairRowDegree (gramPairAt k) i)
              k.val) : ℤ)
        else 0 := by
  classical
  by_cases hdeg : ∀ i, gramPairRowDegree (gramPairAt k) i ≤ lam i
  · rw [ite_eq_left hdeg]
    let mu : Fin (r + 1) → ℕ :=
      fun i => lam i - gramPairRowDegree (gramPairAt k) i
    have hweight : youngGramPairDegree
        (gramPairAt k).val.1 (gramPairAt k).val.2 + mu = lam := by
      funext i
      change youngGramPairDegree
        (gramPairAt k).val.1 (gramPairAt k).val.2 i + mu i = lam i
      rw [← congrFun (gramPairRowDegree_eq_youngGramPairDegree
        (gramPairAt k)) i]
      exact Nat.add_sub_of_le (hdeg i)
    have h := hfits k mu
    rw [hweight] at h
    change (Module.finrank ℝ
        (YoungGramPrefixWeightQuotient n lam (k.val + 1)) : ℤ) =
      (Module.finrank ℝ
        (YoungGramPrefixWeightQuotient n lam k.val) : ℤ) -
        (Module.finrank ℝ
          (YoungGramPrefixWeightQuotient n mu k.val) : ℤ)
    omega
  · rw [ite_eq_right hdeg, sub_zero]
    obtain ⟨i, hi⟩ := not_forall.mp hdeg
    have hover := hoverweight k lam i
      (by rw [← congrFun
        (gramPairRowDegree_eq_youngGramPairDegree (gramPairAt k)) i]
          exact Nat.lt_of_not_ge hi)
    exact_mod_cast hover

theorem youngGramPrefixWeightQuotient_signed_recurrence_of_weaklyRegular
    {r n : ℕ}
    (hregular : RingTheory.Sequence.IsWeaklyRegular
      (PolynomialSpace r n) (gramQuadraticList r n))
    (lam : Fin (r + 1) → ℕ)
    (k : Fin (Fintype.card (UpperGramPair r))) :
    (Module.finrank ℝ
        (YoungGramPrefixWeightQuotient n lam (k.val + 1)) : ℤ) =
      (Module.finrank ℝ
        (YoungGramPrefixWeightQuotient n lam k.val) : ℤ) -
        if ∀ i, gramPairRowDegree (gramPairAt k) i ≤ lam i then
          (Module.finrank ℝ
            (YoungGramPrefixWeightQuotient n
              (fun i => lam i - gramPairRowDegree (gramPairAt k) i)
              k.val) : ℤ)
        else 0 := by
  apply youngGramPrefixWeightQuotient_signed_recurrence_of_fits_and_overweight
  · intro j mu
    have hj : j.val < (gramQuadraticList r n).length := by
      simp [gramQuadraticList]
    have hgen : (gramQuadraticList r n)[j.val] =
        rowPairingPolynomial (n := n)
          (gramPairAt j).val.1 (gramPairAt j).val.2 := by
      simpa only [List.get_eq_getElem,
        gramPairPolynomial] using (gramQuadraticList_getElem_gramPairAt (n := n) j)
    apply finrank_youngGramPrefixWeightQuotient_succ_of_fits n
      (gramPairAt j).val.1 (gramPairAt j).val.2 mu j.val hj hgen
    intro p hp
    apply gramPairAt_mul_mem_prefix_of_weaklyRegular hregular j p
    simpa only [gramPairPolynomial] using hp
  · intro j weight i hover
    have hj : j.val < (gramQuadraticList r n).length := by
      simp [gramQuadraticList]
    have hgen : (gramQuadraticList r n)[j.val] =
        rowPairingPolynomial (n := n)
          (gramPairAt j).val.1 (gramPairAt j).val.2 := by
      simpa only [List.get_eq_getElem,
        gramPairPolynomial] using (gramQuadraticList_getElem_gramPairAt (n := n) j)
    exact finrank_youngGramPrefixWeightQuotient_succ_of_overweight n
      (gramPairAt j).val.1 (gramPairAt j).val.2 weight i j.val
      hj hgen hover

theorem finrank_youngGramRadialWeightQuotient_eq_fullGramKoszulCoefficient_of_recurrence
    {r n : ℕ}
    (hstep : ∀ (lam : Fin (r + 1) → ℕ)
      (k : Fin (Fintype.card (UpperGramPair r))),
      (Module.finrank ℝ
          (YoungGramPrefixWeightQuotient n lam (k.val + 1)) : ℤ) =
        (Module.finrank ℝ
          (YoungGramPrefixWeightQuotient n lam k.val) : ℤ) -
          if ∀ i, gramPairRowDegree (gramPairAt k) i ≤ lam i then
            (Module.finrank ℝ
              (YoungGramPrefixWeightQuotient n
                (fun i => lam i - gramPairRowDegree (gramPairAt k) i)
                k.val) : ℤ)
          else 0)
    (lam : Fin (r + 1) → ℕ) :
    (Module.finrank ℝ (YoungGramRadialWeightQuotient n lam) : ℤ) =
      fullGramKoszulCoefficient n lam := by
  let len := (gramQuadraticList r n).length
  have hlen : len = Fintype.card (UpperGramPair r) :=
    gramQuadraticList_length_eq_upperGramPair_card r n
  have hprefix :=
    finrank_youngGramPrefixWeightQuotient_eq_gramKoszulCoefficient_of_recurrence
      hstep len (by omega) lam
  have hsub :
      Module.finrank ℝ (youngGramPrefixWeightSubmodule n lam len) =
        Module.finrank ℝ (youngGramRadialWeightSubmodule n lam) := by
    rw [show youngGramPrefixWeightSubmodule n lam len =
      youngGramRadialWeightSubmodule n lam from
        youngGramPrefixWeightSubmodule_length lam]
  have hprefdim :=
    finrank_youngGramPrefixWeightQuotient_add_finrank
      (n := n) lam len
  have hradialdim :
      Module.finrank ℝ (YoungGramRadialWeightQuotient n lam) +
        Module.finrank ℝ (youngGramRadialWeightSubmodule n lam) =
          Module.finrank ℝ (youngMultihomogeneousSubmodule n lam) :=
    Submodule.finrank_quotient_add_finrank
      (youngGramRadialWeightSubmodule n lam)
  have hdim :
      Module.finrank ℝ (YoungGramRadialWeightQuotient n lam) =
        Module.finrank ℝ
          (YoungGramPrefixWeightQuotient n lam len) := by
    rw [← finrank_youngMultihomogeneousSubmodule] at hprefdim
    omega
  rw [hdim]
  simpa [fullGramKoszulCoefficient, len] using hprefix

theorem finrank_jointHarmonicWeight_eq_fullGramKoszulCoefficient_of_recurrence
    {r n : ℕ}
    (hstep : ∀ (lam : Fin (r + 1) → ℕ)
      (k : Fin (Fintype.card (UpperGramPair r))),
      (Module.finrank ℝ
          (YoungGramPrefixWeightQuotient n lam (k.val + 1)) : ℤ) =
        (Module.finrank ℝ
          (YoungGramPrefixWeightQuotient n lam k.val) : ℤ) -
          if ∀ i, gramPairRowDegree (gramPairAt k) i ≤ lam i then
            (Module.finrank ℝ
              (YoungGramPrefixWeightQuotient n
                (fun i => lam i - gramPairRowDegree (gramPairAt k) i)
                k.val) : ℤ)
          else 0)
    (lam : Fin (r + 1) → ℕ) :
    (Module.finrank ℝ (JointHarmonicWeightSpace n lam) : ℤ) =
      fullGramKoszulCoefficient n lam := by
  rw [finrank_jointHarmonicWeight_eq_finrank_youngGramRadialWeightQuotient]
  exact
    finrank_youngGramRadialWeightQuotient_eq_fullGramKoszulCoefficient_of_recurrence
      hstep lam

theorem finrank_jointHarmonicWeight_eq_fullGramKoszulCoefficient
    {r n : ℕ}
    (hregular : RingTheory.Sequence.IsWeaklyRegular
      (PolynomialSpace r n) (gramQuadraticList r n))
    (lam : Fin (r + 1) → ℕ) :
    (Module.finrank ℝ (JointHarmonicWeightSpace n lam) : ℤ) =
      fullGramKoszulCoefficient n lam := by
  exact finrank_jointHarmonicWeight_eq_fullGramKoszulCoefficient_of_recurrence
    (youngGramPrefixWeightQuotient_signed_recurrence_of_weaklyRegular
      hregular) lam

theorem finrank_jointHarmonicWeight_eq_fullGramKoszulCoefficient_of_stable
    {r n : ℕ} (hn : 2 * r < n)
    (lam : Fin (r + 1) → ℕ) :
    (Module.finrank ℝ (JointHarmonicWeightSpace n lam) : ℤ) =
      fullGramKoszulCoefficient n lam := by
  exact finrank_jointHarmonicWeight_eq_fullGramKoszulCoefficient
    (gramQuadraticList_isWeaklyRegular hn) lam

end

section


open scoped BigOperators
open scoped InnerProductSpace

theorem bgg_range_eq_ker_of_hodgeLaplacian_injective
    {E F G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [FiniteDimensional ℝ G]
    (d : F →ₗ[ℝ] E) (e : G →ₗ[ℝ] F)
    (hchain : d.comp e = 0)
    (hinj : Function.Injective
      (d.adjoint.comp d + e.comp e.adjoint)) :
    LinearMap.range e = LinearMap.ker d := by
  have hle : LinearMap.range e ≤ LinearMap.ker d := by
    rintro x ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    have h := LinearMap.congr_fun hchain y
    simpa only [LinearMap.coe_comp, Function.comp_apply, LinearMap.zero_apply] using h
  have hbottom :
      ((LinearMap.range e)ᗮ ⊓ LinearMap.ker d :
        Submodule ℝ F) = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro x hx
    have hxorth : x ∈ (LinearMap.range e)ᗮ := hx.1
    rw [e.orthogonal_range] at hxorth
    have hezero : e.adjoint x = 0 := LinearMap.mem_ker.mp hxorth
    have hdzero : d x = 0 := LinearMap.mem_ker.mp hx.2
    change x = 0
    apply hinj
    simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply, hdzero, map_zero,
      hezero, add_zero]
  have hdim := Submodule.finrank_add_inf_finrank_orthogonal hle
  have hdimension :
      Module.finrank ℝ (LinearMap.range e) =
        Module.finrank ℝ (LinearMap.ker d) := by
    rw [hbottom] at hdim
    simpa only [finrank_bot, add_zero] using hdim
  exact Submodule.eq_of_le_of_finrank_eq hle hdimension

theorem bgg_range_eq_ker_of_fischerCore_hodgeLaplacian_injective
    {E F G : Type*}
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    [AddCommGroup G] [Module ℝ G]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [FiniteDimensional ℝ G]
    (cE : InnerProductSpace.Core ℝ E)
    (cF : InnerProductSpace.Core ℝ F)
    (cG : InnerProductSpace.Core ℝ G)
    (d : F →ₗ[ℝ] E) (dStar : E →ₗ[ℝ] F)
    (e : G →ₗ[ℝ] F) (eStar : F →ₗ[ℝ] G)
    (hdStar : ∀ x : E, ∀ y : F,
      cF.inner (dStar x) y = cE.inner x (d y))
    (heStar : ∀ x : F, ∀ y : G,
      cG.inner (eStar x) y = cF.inner x (e y))
    (hchain : d.comp e = 0)
    (hinj : Function.Injective (dStar.comp d + e.comp eStar)) :
    LinearMap.range e = LinearMap.ker d := by
  let : InnerProductSpace.Core ℝ E := cE
  let : NormedAddCommGroup E :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  let : InnerProductSpace ℝ E :=
    InnerProductSpace.ofCore
      (inferInstance : PreInnerProductSpace.Core ℝ E)
  let : InnerProductSpace.Core ℝ F := cF
  let : NormedAddCommGroup F :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  let : InnerProductSpace ℝ F :=
    InnerProductSpace.ofCore
      (inferInstance : PreInnerProductSpace.Core ℝ F)
  let : InnerProductSpace.Core ℝ G := cG
  let : NormedAddCommGroup G :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  let : InnerProductSpace ℝ G :=
    InnerProductSpace.ofCore
      (inferInstance : PreInnerProductSpace.Core ℝ G)
  have hd : dStar = d.adjoint := by
    apply (LinearMap.eq_adjoint_iff dStar d).mpr
    intro x y
    change cF.inner (dStar x) y = cE.inner x (d y)
    exact hdStar x y
  have he : eStar = e.adjoint := by
    apply (LinearMap.eq_adjoint_iff eStar e).mpr
    intro x y
    change cG.inner (eStar x) y = cF.inner x (e y)
    exact heStar x y
  apply bgg_range_eq_ker_of_hodgeLaplacian_injective d e hchain
  simpa only [← hd, ← he] using hinj

/-- The signed joint harmonic weight dimension used in the spherical-code argument. -/
def signedJointHarmonicWeightDimension {r : ℕ}
    (n : ℕ) (mu : Fin (r + 1) → ℤ) : ℤ :=
  if _h : ∀ i, 0 ≤ mu i then
    (Module.finrank ℝ
      (JointHarmonicWeightSpace n (fun i => (mu i).toNat)) : ℤ)
  else 0

/-- The alternating joint harmonic weight dimension used in the spherical-code argument. -/
def alternatingJointHarmonicWeightDimension {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) : ℤ :=
  ∑ σ : Equiv.Perm (Fin (r + 1)),
    (Equiv.Perm.sign σ : ℤ) *
      signedJointHarmonicWeightDimension n (weylShift lam σ)

theorem alternatingJointHarmonicWeightDimension_eq_alternatingGramKoszul
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (hgram : ∀ mu : Fin (r + 1) → ℕ,
      (Module.finrank ℝ (JointHarmonicWeightSpace n mu) : ℤ) =
        fullGramKoszulCoefficient n mu) :
    alternatingJointHarmonicWeightDimension n lam =
      alternatingGramKoszulCoefficient n lam := by
  classical
  unfold alternatingJointHarmonicWeightDimension
    alternatingGramKoszulCoefficient
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  unfold signedJointHarmonicWeightDimension signedFullGramKoszulCoefficient
  split_ifs with h
  · exact hgram (fun i => (weylShift lam σ i).toNat)
  · rfl

theorem alternatingJointHarmonicWeightDimension_eq_alternatingGramKoszul_of_stable
    {r n : ℕ} (hn : 2 * r < n) (lam : Fin (r + 1) → ℕ) :
    alternatingJointHarmonicWeightDimension n lam =
      alternatingGramKoszulCoefficient n lam := by
  apply alternatingJointHarmonicWeightDimension_eq_alternatingGramKoszul lam
  intro mu
  exact finrank_jointHarmonicWeight_eq_fullGramKoszulCoefficient_of_stable
    hn mu

end

section


open scoped BigOperators
open scoped InnerProductSpace

@[implicit_reducible]
private def finitePiFischerCore {ι : Type*} [Fintype ι]
    (V : ι → Type*)
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]
    (c : ∀ i, InnerProductSpace.Core ℝ (V i)) :
    InnerProductSpace.Core ℝ (∀ i, V i) where
  inner x y := ∑ i, (c i).inner (x i) (y i)
  conj_inner_symm x y := by
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (c i).conj_inner_symm (x i) (y i)
  re_inner_nonneg x := by
    change 0 ≤ ∑ i, (c i).inner (x i) (x i)
    exact Finset.sum_nonneg fun i _ => by
      simpa only [RCLike.re_to_real] using (c i).re_inner_nonneg (x i)
  add_left x y z := by
    change
      (∑ i, (c i).inner (x i + y i) (z i)) =
        (∑ i, (c i).inner (x i) (z i)) +
          ∑ i, (c i).inner (y i) (z i)
    simp_rw [(c _).add_left]
    exact Finset.sum_add_distrib
  smul_left x y a := by
    change
      (∑ i, (c i).inner (a • x i) (y i)) =
        a * ∑ i, (c i).inner (x i) (y i)
    simp_rw [(c _).smul_left]
    simp only [Real.ringHom_apply, Finset.mul_sum]
  definite x hx := by
    have hsum : (∑ i, (c i).inner (x i) (x i)) = 0 := hx
    funext i
    apply (c i).definite
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => by simpa only [RCLike.re_to_real] using (c j).re_inner_nonneg (x j))).mp
      hsum i (Finset.mem_univ i)

/-- The finite fischer root laplacian used in the spherical-code argument. -/
def finiteFischerRootLaplacian {ι V : Type*}
    [Fintype ι]
    [AddCommGroup V] [Module ℝ V]
    (W : ι → Type*)
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℝ (W i)]
    (A : ∀ i, V →ₗ[ℝ] W i)
    (Astar : ∀ i, W i →ₗ[ℝ] V) : V →ₗ[ℝ] V :=
  ∑ i, (Astar i).comp (A i)

theorem finiteFischerRootLaplacian_energy
    {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℝ V]
    (cV : InnerProductSpace.Core ℝ V)
    (W : ι → Type*)
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℝ (W i)]
    (cW : ∀ i, InnerProductSpace.Core ℝ (W i))
    (A : ∀ i, V →ₗ[ℝ] W i)
    (Astar : ∀ i, W i →ₗ[ℝ] V)
    (hadjoint : ∀ i (x : W i) (y : V),
      cV.inner (Astar i x) y = (cW i).inner x (A i y))
    (x : V) :
    cV.inner x (finiteFischerRootLaplacian W A Astar x) =
      ∑ i, (cW i).inner (A i x) (A i x) := by
  classical
  let : InnerProductSpace.Core ℝ V := cV
  let : NormedAddCommGroup V :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  let : InnerProductSpace ℝ V :=
    InnerProductSpace.ofCore
      (inferInstance : PreInnerProductSpace.Core ℝ V)
  unfold finiteFischerRootLaplacian
  rw [LinearMap.sum_apply]
  change ⟪x, ∑ i, (Astar i).comp (A i) x⟫_ℝ = _
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  change cV.inner x (Astar i (A i x)) = _
  rw [real_inner_comm]
  exact hadjoint i (A i x) x

theorem finiteFischerRootLaplacian_eq_zero_iff
    {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℝ V]
    (cV : InnerProductSpace.Core ℝ V)
    (W : ι → Type*)
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℝ (W i)]
    (cW : ∀ i, InnerProductSpace.Core ℝ (W i))
    (A : ∀ i, V →ₗ[ℝ] W i)
    (Astar : ∀ i, W i →ₗ[ℝ] V)
    (hadjoint : ∀ i (x : W i) (y : V),
      cV.inner (Astar i x) y = (cW i).inner x (A i y))
    (x : V) :
    finiteFischerRootLaplacian W A Astar x = 0 ↔
      ∀ i, A i x = 0 := by
  let : InnerProductSpace.Core ℝ V := cV
  let : NormedAddCommGroup V :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
  let : InnerProductSpace ℝ V :=
    InnerProductSpace.ofCore
      (inferInstance : PreInnerProductSpace.Core ℝ V)
  constructor
  · intro hx
    have hsum : (∑ i, (cW i).inner (A i x) (A i x)) = 0 := by
      rw [← finiteFischerRootLaplacian_energy cV W cW A Astar
        hadjoint x, hx]
      exact @inner_zero_right ℝ V _ _ _ x
    intro i
    apply (cW i).definite
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => by simpa only [RCLike.re_to_real] using (cW j).re_inner_nonneg (A j x))).mp
      hsum i (Finset.mem_univ i)
  · intro h
    simp only [finiteFischerRootLaplacian, LinearMap.coe_sum, LinearMap.coe_comp, Finset.sum_apply,
      Function.comp_apply, h, map_zero, Finset.sum_const_zero]

end

namespace UniversalBGGRootComplex

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

/-- The active positive root used in the spherical-code argument. -/
abbrev ActivePositiveRoot {r : ℕ} (lam : Fin (r + 1) → ℕ) :=
  {α : PositiveRoot r // 0 < lam (positiveRootSecond α)}

/-- The active root base weight used in the spherical-code argument. -/
def activeRootBaseWeight {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (α : ActivePositiveRoot lam) :
    Fin (r + 1) → ℕ :=
  Function.update lam (positiveRootSecond α.val)
    (lam (positiveRootSecond α.val) - 1)

@[simp] theorem activeRootBaseWeight_update_second {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (α : ActivePositiveRoot lam) :
    Function.update (activeRootBaseWeight lam α)
      (positiveRootSecond α.val)
      (activeRootBaseWeight lam α (positiveRootSecond α.val) + 1) = lam := by
  funext i
  by_cases hi : i = positiveRootSecond α.val
  · subst i
    simp only [activeRootBaseWeight, Function.update_self]
    omega
  · simp only [activeRootBaseWeight, Function.update_self, ne_eq, hi, not_false_eq_true,
      Function.update_of_ne]

/-- The active root raised weight used in the spherical-code argument. -/
def activeRootRaisedWeight {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (α : ActivePositiveRoot lam) :
    Fin (r + 1) → ℕ :=
  Function.update (activeRootBaseWeight lam α)
    (positiveRootFirst α.val)
    (activeRootBaseWeight lam α (positiveRootFirst α.val) + 1)

/-- The active positive root raise used in the spherical-code argument. -/
def activePositiveRootRaise {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (α : ActivePositiveRoot lam) :
    JointHarmonicWeightSpace n lam →ₗ[ℝ]
      JointHarmonicWeightSpace n (activeRootRaisedWeight lam α) where
  toFun p := by
    refine ⟨⟨polarization r n (positiveRootFirst α.val)
      (positiveRootSecond α.val) (p.val : PolynomialSpace r n), ?_⟩, ?_⟩
    · exact polarization_mem_youngMultihomogeneous_transfer
        (activeRootBaseWeight lam α)
        (positiveRootFirst α.val) (positiveRootSecond α.val)
        (positiveRootFirst_ne_second α.val)
        (by rw [activeRootBaseWeight_update_second]; exact p.val.property)
    · exact polarization_mem_traceFreeSubmodule
        (positiveRootFirst α.val) (positiveRootSecond α.val)
        (p.val : PolynomialSpace r n) p.property
  map_add' p q := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_add (polarization r n (positiveRootFirst α.val)
      (positiveRootSecond α.val))
      (p.val : PolynomialSpace r n) (q.val : PolynomialSpace r n)
  map_smul' c p := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_smul (polarization r n (positiveRootFirst α.val)
      (positiveRootSecond α.val)) c (p.val : PolynomialSpace r n)

/-- The active positive root lower used in the spherical-code argument. -/
def activePositiveRootLower {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (α : ActivePositiveRoot lam) :
    JointHarmonicWeightSpace n (activeRootRaisedWeight lam α) →ₗ[ℝ]
      JointHarmonicWeightSpace n lam where
  toFun p := by
    refine ⟨⟨polarization r n (positiveRootSecond α.val)
      (positiveRootFirst α.val) (p.val : PolynomialSpace r n), ?_⟩, ?_⟩
    · have hmem := polarization_mem_youngMultihomogeneous_transfer
        (activeRootBaseWeight lam α)
        (positiveRootSecond α.val) (positiveRootFirst α.val)
        (positiveRootFirst_ne_second α.val).symm p.val.property
      exact (congrArg (fun mu : Fin (r + 1) → ℕ =>
        polarization r n (positiveRootSecond α.val)
          (positiveRootFirst α.val) (p.val : PolynomialSpace r n) ∈
            youngMultihomogeneousSubmodule n mu)
              (activeRootBaseWeight_update_second lam α)).mp hmem
    · exact polarization_mem_traceFreeSubmodule
        (positiveRootSecond α.val) (positiveRootFirst α.val)
        (p.val : PolynomialSpace r n) p.property
  map_add' p q := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_add (polarization r n (positiveRootSecond α.val)
      (positiveRootFirst α.val))
      (p.val : PolynomialSpace r n) (q.val : PolynomialSpace r n)
  map_smul' c p := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_smul (polarization r n (positiveRootSecond α.val)
      (positiveRootFirst α.val)) c (p.val : PolynomialSpace r n)

@[simp] theorem activePositiveRootRaise_coe {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (α : ActivePositiveRoot lam)
    (p : JointHarmonicWeightSpace n lam) :
    (((activePositiveRootRaise n lam α p).val :
      youngMultihomogeneousSubmodule n (activeRootRaisedWeight lam α)) :
        PolynomialSpace r n) =
      polarization r n (positiveRootFirst α.val)
        (positiveRootSecond α.val) (p.val : PolynomialSpace r n) := rfl

theorem activePositiveRoot_fischer_adjoint {r n : ℕ}
    (lam : Fin (r + 1) → ℕ) (α : ActivePositiveRoot lam)
    (p : JointHarmonicWeightSpace n (activeRootRaisedWeight lam α))
    (q : JointHarmonicWeightSpace n lam) :
    (jointHarmonicWeightFischerCore n lam).inner
      (activePositiveRootLower n lam α p) q =
        (jointHarmonicWeightFischerCore n
          (activeRootRaisedWeight lam α)).inner
            p (activePositiveRootRaise n lam α q) := by
  rw [jointHarmonicWeightFischerCore_inner,
    jointHarmonicWeightFischerCore_inner]
  exact polynomialInner_polarization_harmonicLift
    (positiveRootSecond α.val) (positiveRootFirst α.val)
    (p.val : PolynomialSpace r n) (q.val : PolynomialSpace r n)

private def positiveRootFischerLaplacian {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) :
    JointHarmonicWeightSpace n lam →ₗ[ℝ]
      JointHarmonicWeightSpace n lam :=
  finiteFischerRootLaplacian
    (ι := ActivePositiveRoot lam)
    (V := JointHarmonicWeightSpace n lam)
    (fun α : ActivePositiveRoot lam =>
      JointHarmonicWeightSpace n (activeRootRaisedWeight lam α))
    (activePositiveRootRaise n lam)
    (activePositiveRootLower n lam)

theorem positiveRootFischerLaplacian_eq_zero_iff {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (p : JointHarmonicWeightSpace n lam) :
    positiveRootFischerLaplacian n lam p = 0 ↔
      ∀ α : ActivePositiveRoot lam,
        activePositiveRootRaise n lam α p = 0 := by
  exact finiteFischerRootLaplacian_eq_zero_iff
    (jointHarmonicWeightFischerCore n lam)
    (fun α : ActivePositiveRoot lam =>
      JointHarmonicWeightSpace n (activeRootRaisedWeight lam α))
    (fun α => jointHarmonicWeightFischerCore n
      (activeRootRaisedWeight lam α))
    (activePositiveRootRaise n lam)
    (activePositiveRootLower n lam)
    (activePositiveRoot_fischer_adjoint lam) p

theorem positiveRootFischerLaplacian_eq_zero_iff_harmonicYoung
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (p : JointHarmonicWeightSpace n lam) :
    positiveRootFischerLaplacian n lam p = 0 ↔
      (p.val : PolynomialSpace r n) ∈ harmonicYoungSubmodule lam := by
  rw [positiveRootFischerLaplacian_eq_zero_iff,
    mem_harmonicYoungSubmodule]
  constructor
  · intro hp
    refine ⟨youngMultihomogeneous_isHomogeneous lam p.val,
      youngMultihomogeneous_rowEuler lam p.val,
      (mem_traceFreeSubmodule _).mp p.property, ?_⟩
    intro i j hij
    by_cases hj : lam j = 0
    · exact youngMultihomogeneous_polarization_eq_zero_of_rowDegree_zero
        lam p.val i j hj
    · have hjpos : 0 < lam j := Nat.pos_of_ne_zero hj
      let α : PositiveRoot r := ⟨(i, j), hij⟩
      let β : ActivePositiveRoot lam := ⟨α, hjpos⟩
      have h := congrArg
        (fun q : JointHarmonicWeightSpace n
          (activeRootRaisedWeight lam β) =>
            (q.val : PolynomialSpace r n)) (hp β)
      exact h
  · rintro ⟨_, _, _, hp⟩ α
    apply Subtype.ext
    apply Subtype.ext
    exact hp (positiveRootFirst α.val) (positiveRootSecond α.val)
      (positiveRootFirst_lt_second α.val)

private def harmonicYoungPositiveRootHodgeKernelEquiv {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) :
    HarmonicYoungSpace (n := n) lam ≃ₗ[ℝ]
      LinearMap.ker (positiveRootFischerLaplacian n lam) where
  toFun p := by
    have hweight := harmonicYoung_mem_youngMultihomogeneousSubmodule lam p
    have htrace : (p : PolynomialSpace r n) ∈ traceFreeSubmodule r n :=
      (mem_traceFreeSubmodule _).mpr
        ((mem_harmonicYoungSubmodule lam
          (p : PolynomialSpace r n)).mp p.property).2.2.1
    let q : JointHarmonicWeightSpace n lam := ⟨⟨p, hweight⟩, htrace⟩
    exact ⟨q, (positiveRootFischerLaplacian_eq_zero_iff_harmonicYoung
      lam q).mpr p.property⟩
  invFun p := ⟨(p.val.val : PolynomialSpace r n),
    (positiveRootFischerLaplacian_eq_zero_iff_harmonicYoung
      lam p.val).mp p.property⟩
  left_inv p := by
    apply Subtype.ext
    rfl
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_add' p q := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl
  map_smul' c p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

/-- The root joint harmonic chain fischer core component. -/
@[implicit_reducible]
def rootJointHarmonicChainFischerCore {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) (k : ℕ) :
    InnerProductSpace.Core ℝ (RootJointHarmonicChain n lam k) :=
  finitePiFischerCore
    (fun S : AdmissibleRootWedge lam k =>
      JointHarmonicWeightSpace n (rootWedgeWeight lam S))
    (fun S => jointHarmonicWeightFischerCore n (rootWedgeWeight lam S))

@[simp] theorem rootJointHarmonicChainFischerCore_inner {r n k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (p q : RootJointHarmonicChain n lam k) :
    (rootJointHarmonicChainFischerCore n lam k).inner p q =
      ∑ S : AdmissibleRootWedge lam k,
        (jointHarmonicWeightFischerCore n
          (rootWedgeWeight lam S)).inner (p S) (q S) := rfl

/-- The empty admissible root wedge used in the spherical-code argument. -/
def emptyAdmissibleRootWedge {r : ℕ}
    (lam : Fin (r + 1) → ℕ) : AdmissibleRootWedge lam 0 :=
  ⟨⟨∅, by simp only [Finset.card_empty]⟩, by
    intro i
    simp only [signedRootWeight, rootFamilyCharge_empty, add_zero, Nat.cast_nonneg]⟩

theorem admissibleRootWedge_zero_eq_empty {r : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam 0) :
    S = emptyAdmissibleRootWedge lam := by
  apply Subtype.ext
  apply Subtype.ext
  exact Finset.card_eq_zero.mp S.val.property

noncomputable instance admissibleRootWedgeZeroUnique {r : ℕ}
    (lam : Fin (r + 1) → ℕ) : Unique (AdmissibleRootWedge lam 0) where
  default := emptyAdmissibleRootWedge lam
  uniq := admissibleRootWedge_zero_eq_empty lam

theorem rootWedgeWeight_degree_zero {r : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam 0) :
    rootWedgeWeight lam S = lam := by
  have hzero : S.val.val = ∅ := Finset.card_eq_zero.mp S.val.property
  funext i
  simp only [rootWedgeWeight, signedRootWeight, hzero, rootFamilyCharge_empty, add_zero,
    Int.toNat_natCast]

/-- The root joint harmonic degree zero equiv used in the spherical-code argument. -/
def rootJointHarmonicDegreeZeroEquiv {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) :
    RootJointHarmonicChain n lam 0 ≃ₗ[ℝ]
      JointHarmonicWeightSpace n lam :=
  (LinearEquiv.piCongrRight fun S : AdmissibleRootWedge lam 0 =>
    jointHarmonicWeightCast n (rootWedgeWeight lam S) lam
      (rootWedgeWeight_degree_zero lam S)).trans
        (LinearEquiv.funUnique
          (AdmissibleRootWedge lam 0) ℝ
          (JointHarmonicWeightSpace n lam))

/-- The root degree zero positive cochain used in the spherical-code argument. -/
def rootDegreeZeroPositiveCochain {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) :
    RootJointHarmonicChain n lam 0 →ₗ[ℝ]
      (∀ α : ActivePositiveRoot lam,
        JointHarmonicWeightSpace n (activeRootRaisedWeight lam α)) :=
  LinearMap.pi fun α =>
    (activePositiveRootRaise n lam α).comp
      (rootJointHarmonicDegreeZeroEquiv n lam).toLinearMap

@[simp] theorem rootDegreeZeroPositiveCochain_apply {r n : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (p : RootJointHarmonicChain n lam 0)
    (α : ActivePositiveRoot lam) :
    rootDegreeZeroPositiveCochain n lam p α =
      activePositiveRootRaise n lam α
        (rootJointHarmonicDegreeZeroEquiv n lam p) := rfl

private def rootDegreeZeroFischerLaplacian {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) :
    RootJointHarmonicChain n lam 0 →ₗ[ℝ]
      RootJointHarmonicChain n lam 0 :=
  (rootJointHarmonicDegreeZeroEquiv n lam).symm.toLinearMap.comp
    ((positiveRootFischerLaplacian n lam).comp
      (rootJointHarmonicDegreeZeroEquiv n lam).toLinearMap)

theorem rootDegreeZeroPositiveCochain_eq_zero_iff_harmonicYoung
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (p : RootJointHarmonicChain n lam 0) :
    rootDegreeZeroPositiveCochain n lam p = 0 ↔
      (((rootJointHarmonicDegreeZeroEquiv n lam p).val :
        youngMultihomogeneousSubmodule n lam) : PolynomialSpace r n) ∈
          harmonicYoungSubmodule lam := by
  rw [← positiveRootFischerLaplacian_eq_zero_iff_harmonicYoung,
    positiveRootFischerLaplacian_eq_zero_iff]
  constructor
  · intro hp α
    have h := congrFun hp α
    simpa only [rootDegreeZeroPositiveCochain_apply, Pi.zero_apply] using h
  · intro hp
    funext α
    exact hp α

theorem rootDegreeZeroFischerLaplacian_eq_zero_iff_harmonicYoung
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (p : RootJointHarmonicChain n lam 0) :
    rootDegreeZeroFischerLaplacian n lam p = 0 ↔
      (((rootJointHarmonicDegreeZeroEquiv n lam p).val :
        youngMultihomogeneousSubmodule n lam) : PolynomialSpace r n) ∈
          harmonicYoungSubmodule lam := by
  change
    (rootJointHarmonicDegreeZeroEquiv n lam).symm
      (positiveRootFischerLaplacian n lam
        (rootJointHarmonicDegreeZeroEquiv n lam p)) = 0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff]
  exact positiveRootFischerLaplacian_eq_zero_iff_harmonicYoung lam _

theorem rootDegreeZeroPositiveCochain_eq_zero_iff_hodge
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (p : RootJointHarmonicChain n lam 0) :
    rootDegreeZeroPositiveCochain n lam p = 0 ↔
      rootDegreeZeroFischerLaplacian n lam p = 0 := by
  rw [rootDegreeZeroPositiveCochain_eq_zero_iff_harmonicYoung,
    rootDegreeZeroFischerLaplacian_eq_zero_iff_harmonicYoung]

private def rootDegreeZeroLaplacianKernelTransport {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) :
    LinearMap.ker (rootDegreeZeroFischerLaplacian n lam) ≃ₗ[ℝ]
      LinearMap.ker (positiveRootFischerLaplacian n lam) where
  toFun p := by
    refine ⟨rootJointHarmonicDegreeZeroEquiv n lam p.val, ?_⟩
    have hp := p.property
    change
      (rootJointHarmonicDegreeZeroEquiv n lam).symm
        (positiveRootFischerLaplacian n lam
          (rootJointHarmonicDegreeZeroEquiv n lam p.val)) = 0 at hp
    exact (LinearEquiv.map_eq_zero_iff _).mp hp
  invFun p := by
    refine ⟨(rootJointHarmonicDegreeZeroEquiv n lam).symm p.val, ?_⟩
    change
      (rootJointHarmonicDegreeZeroEquiv n lam).symm
        (positiveRootFischerLaplacian n lam
          (rootJointHarmonicDegreeZeroEquiv n lam
            ((rootJointHarmonicDegreeZeroEquiv n lam).symm p.val))) = 0
    simp only [LinearEquiv.apply_symm_apply, LinearMap.map_coe_ker, map_zero]
  left_inv p := by
    apply Subtype.ext
    exact (rootJointHarmonicDegreeZeroEquiv n lam).left_inv p.val
  right_inv p := by
    apply Subtype.ext
    exact (rootJointHarmonicDegreeZeroEquiv n lam).right_inv p.val
  map_add' p q := by
    apply Subtype.ext
    exact (rootJointHarmonicDegreeZeroEquiv n lam).map_add p.val q.val
  map_smul' c p := by
    apply Subtype.ext
    exact (rootJointHarmonicDegreeZeroEquiv n lam).map_smul c p.val

private def harmonicYoungRootDegreeZeroHodgeKernelEquiv {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) :
    HarmonicYoungSpace (n := n) lam ≃ₗ[ℝ]
      LinearMap.ker (rootDegreeZeroFischerLaplacian n lam) :=
  (harmonicYoungPositiveRootHodgeKernelEquiv n lam).trans
    (rootDegreeZeroLaplacianKernelTransport n lam).symm

private def rootDegreeZeroCochainHodgeKernelEquiv {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) :
    LinearMap.ker (rootDegreeZeroPositiveCochain n lam) ≃ₗ[ℝ]
      LinearMap.ker (rootDegreeZeroFischerLaplacian n lam) where
  toFun p := ⟨p.val,
    (rootDegreeZeroPositiveCochain_eq_zero_iff_hodge lam p.val).mp
      p.property⟩
  invFun p := ⟨p.val,
    (rootDegreeZeroPositiveCochain_eq_zero_iff_hodge lam p.val).mpr
      p.property⟩
  left_inv p := by
    apply Subtype.ext
    rfl
  right_inv p := by
    apply Subtype.ext
    rfl
  map_add' p q := by
    apply Subtype.ext
    rfl
  map_smul' c p := by
    apply Subtype.ext
    rfl

private def harmonicYoungRootDegreeZeroCochainKernelEquiv {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) :
    HarmonicYoungSpace (n := n) lam ≃ₗ[ℝ]
      LinearMap.ker (rootDegreeZeroPositiveCochain n lam) :=
  (harmonicYoungRootDegreeZeroHodgeKernelEquiv n lam).trans
    (rootDegreeZeroCochainHodgeKernelEquiv n lam).symm

theorem finrank_rootDegreeZeroPositiveCochain_kernel
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) :
    Module.finrank ℝ
        (LinearMap.ker (rootDegreeZeroPositiveCochain n lam)) =
      Module.finrank ℝ (HarmonicYoungSpace (n := n) lam) :=
  (harmonicYoungRootDegreeZeroCochainKernelEquiv n lam).finrank_eq.symm

end

end UniversalBGGRootComplex

section


open scoped BigOperators

theorem finiteChain_eulerCharacteristic_eq_degreeZero_sub_boundary_add_top
    (V : ℕ → Type*)
    [∀ k, AddCommGroup (V k)] [∀ k, Module ℝ (V k)]
    [∀ k, FiniteDimensional ℝ (V k)]
    (d : ∀ k, V (k + 1) →ₗ[ℝ] V k)
    (N : ℕ)
    (hexact : ∀ k, k < N →
      LinearMap.range (d (k + 1)) = LinearMap.ker (d k)) :
    (∑ k ∈ Finset.range (N + 1),
      (-1 : ℤ) ^ k * (Module.finrank ℝ (V k) : ℤ)) =
      (Module.finrank ℝ (V 0) : ℤ) -
        (Module.finrank ℝ (LinearMap.range (d 0)) : ℤ) +
        (-1 : ℤ) ^ N *
          (Module.finrank ℝ (LinearMap.range (d N)) : ℤ) := by
  induction N with
  | zero => simp only [zero_add, Finset.range_one, Int.reduceNeg, Finset.sum_singleton, pow_zero,
              one_mul, Nat.reduceAdd, sub_add_cancel]
  | succ N ih =>
    have ih' := ih (fun k hk => hexact k (Nat.lt_trans hk (Nat.lt_succ_self N)))
    have hdimNat :
        Module.finrank ℝ (LinearMap.range (d (N + 1))) +
          Module.finrank ℝ (LinearMap.range (d N)) =
          Module.finrank ℝ (V (N + 1)) := by
      rw [hexact N (Nat.lt_succ_self N)]
      simpa only [Nat.add_comm] using (d N).finrank_range_add_finrank_ker
    have hdim :
        (Module.finrank ℝ (V (N + 1)) : ℤ) =
          (Module.finrank ℝ (LinearMap.range (d (N + 1))) : ℤ) +
            (Module.finrank ℝ (LinearMap.range (d N)) : ℤ) := by
      exact_mod_cast hdimNat.symm
    rw [Finset.sum_range_succ, ih', hdim, pow_succ]
    ring

namespace OrthogonalDenominator

theorem det_reversed_vandermonde
    {R : Type*} [CommRing R] {r : ℕ}
    (x : Fin (r + 1) → R) :
    Matrix.det (fun i j : Fin (r + 1) => x i ^ (r - j.val)) =
      ∏ i : Fin (r + 1), ∏ j ∈ Finset.Ioi i, (x i - x j) := by
  have hmatrix :
      (fun i j : Fin (r + 1) => x i ^ (r - j.val)) =
        Matrix.projVandermonde (fun _ : Fin (r + 1) => (1 : R)) x := by
    ext i j
    simp only [Matrix.projVandermonde_apply, one_pow, Fin.rev, Nat.reduceSubDiff, one_mul]
  rw [hmatrix, Matrix.det_projVandermonde]
  simp only [one_mul]

theorem det_quadratic_projective_vandermonde
    {R : Type*} [CommRing R] {r : ℕ}
    (x : Fin (r + 1) → R) :
    (Matrix.projVandermonde (fun i => 1 + (x i) ^ 2) x).det =
      Matrix.det (fun i j : Fin (r + 1) => x i ^ (r - j.val)) *
        ∏ i : Fin (r + 1), ∏ j ∈ Finset.Ioi i,
          (1 - x i * x j) := by
  rw [Matrix.det_projVandermonde, det_reversed_vandermonde]
  classical
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  ring

theorem upper_gram_pair_product
    {R : Type*} [CommRing R] {r : ℕ}
    (x : Fin (r + 1) → R) :
    (∏ i : Fin (r + 1), (1 - x i ^ 2)) *
        (∏ i : Fin (r + 1), ∏ j ∈ Finset.Ioi i,
          (1 - x i * x j)) =
      ∏ i : Fin (r + 1), ∏ j ∈ Finset.Ici i,
        (1 - x i * x j) := by
  classical
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hinterval : Finset.Ici i = insert i (Finset.Ioi i) := by
    ext j
    simp only [Finset.mem_Ici, Finset.mem_insert,
      Finset.mem_Ioi]
    omega
  rw [hinterval, Finset.prod_insert]
  · simp only [pow_two]
  · simp only [Finset.mem_Ioi, lt_self_iff_false, not_false_eq_true]

theorem orthogonal_denominator_entry
    {R : Type*} [CommRing R]
    (x : R) (r j : ℕ) (hj : j ≤ r) :
    x ^ (r - j) - x ^ (r + j + 2) =
      (1 - x ^ 2) * x ^ (r - j) *
        ∑ k ∈ Finset.range (j + 1), x ^ (2 * k) := by
  have hgeom := geom_sum_mul (x ^ 2) (j + 1)
  have hsum :
      (∑ k ∈ Finset.range (j + 1), x ^ (2 * k)) *
          (x ^ 2 - 1) = (x ^ 2) ^ (j + 1) - 1 := by
    simpa only [pow_mul] using hgeom
  have hpow : x ^ (r - j) * (x ^ 2) ^ (j + 1) =
      x ^ (r + j + 2) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  calc
    x ^ (r - j) - x ^ (r + j + 2) =
        x ^ (r - j) * (1 - (x ^ 2) ^ (j + 1)) := by
          rw [mul_sub, mul_one, hpow]
    _ = (1 - x ^ 2) * x ^ (r - j) *
        ∑ k ∈ Finset.range (j + 1), x ^ (2 * k) := by
          linear_combination x ^ (r - j) * hsum

theorem chebyshevS_isMonicOfDegree
    (R : Type*) [CommRing R] [Nontrivial R] (j : ℕ) :
    (Polynomial.Chebyshev.S R (j : ℤ)).IsMonicOfDegree j := by
  induction j using Nat.twoStepInduction with
  | zero => simp only [CharP.cast_eq_zero, Polynomial.Chebyshev.S_zero,
              Polynomial.isMonicOfDegree_zero_iff]
  | one => simpa only [Nat.cast_one,
             Polynomial.Chebyshev.S_one] using Polynomial.isMonicOfDegree_X R
  | more n ih0 ih1 =>
      push_cast
      rw [Polynomial.Chebyshev.S_add_two]
      have ih1' :
          (Polynomial.Chebyshev.S R ((n : ℤ) + 1)).IsMonicOfDegree
            (n + 1) := by
        simpa only [Nat.cast_add, Nat.cast_one] using ih1
      have hmul :
          ((Polynomial.X : Polynomial R) *
            Polynomial.Chebyshev.S R ((n : ℤ) + 1)).IsMonicOfDegree
              (n + 2) := by
        simpa only [Nat.add_left_comm,
          Nat.reduceAdd] using (Polynomial.isMonicOfDegree_X R).mul ih1'
      apply hmul.sub
      rw [ih0.natDegree_eq]
      omega

theorem chebyshevS_monic
    (R : Type*) [CommRing R] [Nontrivial R] (j : ℕ) :
    (Polynomial.Chebyshev.S R (j : ℤ)).Monic :=
  (chebyshevS_isMonicOfDegree R j).monic

theorem chebyshevS_natDegree
    (R : Type*) [CommRing R] [Nontrivial R] (j : ℕ) :
    (Polynomial.Chebyshev.S R (j : ℤ)).natDegree = j :=
  (chebyshevS_isMonicOfDegree R j).natDegree_eq

theorem homogenize_shift {R : Type*} [CommSemiring R]
    (p : Polynomial R) (n k : ℕ) (hp : p.natDegree ≤ n) :
    p.homogenize (n + k) =
      p.homogenize n * (MvPolynomial.X 1) ^ k := by
  calc
    p.homogenize (n + k) = (p * 1).homogenize (n + k) := by simp only [mul_one]
    _ = p.homogenize n * (1 : Polynomial R).homogenize k :=
      Polynomial.homogenize_mul p 1 hp (by simp only [Polynomial.natDegree_one, zero_le])
    _ = _ := by simp only [Polynomial.homogenize_one, Fin.isValue]

theorem chebyshevS_homogenize_add_two
    (R : Type*) [CommRing R] [Nontrivial R] (n : ℕ) :
    (Polynomial.Chebyshev.S R ((n + 2 : ℕ) : ℤ)).homogenize (n + 2) =
      MvPolynomial.X 0 *
          (Polynomial.Chebyshev.S R ((n + 1 : ℕ) : ℤ)).homogenize (n + 1) -
        (MvPolynomial.X 1) ^ 2 *
          (Polynomial.Chebyshev.S R (n : ℤ)).homogenize n := by
  have hrec :
      Polynomial.Chebyshev.S R ((n + 2 : ℕ) : ℤ) =
        Polynomial.X * Polynomial.Chebyshev.S R ((n + 1 : ℕ) : ℤ) -
          Polynomial.Chebyshev.S R (n : ℤ) := by
    push_cast
    rw [Polynomial.Chebyshev.S_add_two]
  rw [hrec, Polynomial.homogenize_sub]
  have hmul :
      (Polynomial.X *
        Polynomial.Chebyshev.S R ((n + 1 : ℕ) : ℤ)).homogenize (n + 2) =
          MvPolynomial.X 0 *
            (Polynomial.Chebyshev.S R ((n + 1 : ℕ) : ℤ)).homogenize (n + 1) := by
    convert Polynomial.homogenize_mul (Polynomial.X : Polynomial R)
      (Polynomial.Chebyshev.S R ((n + 1 : ℕ) : ℤ))
      (m := 1) (n := n + 1) (by simp only [Polynomial.natDegree_X, Std.le_refl])
      (by rw [chebyshevS_natDegree]) using 1 <;>
      simp [Nat.add_left_comm]
  rw [hmul]
  have hshift := homogenize_shift
    (Polynomial.Chebyshev.S R (n : ℤ)) n 2
    (by rw [chebyshevS_natDegree])
  rw [hshift]
  ring

theorem even_geometric_sum_add_two
    {R : Type*} [CommRing R] (x : R) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 3), x ^ (2 * k)) =
      (1 + x ^ 2) * (∑ k ∈ Finset.range (n + 2), x ^ (2 * k)) -
        x ^ 2 * (∑ k ∈ Finset.range (n + 1), x ^ (2 * k)) := by
  have hpow : x ^ (2 * (n + 2)) = x ^ 2 * x ^ (2 * (n + 1)) := by
    rw [show 2 * (n + 2) = 2 + 2 * (n + 1) by omega, pow_add]
  rw [show n + 3 = (n + 2) + 1 by omega,
    Finset.sum_range_succ, hpow]
  rw [show n + 2 = (n + 1) + 1 by omega,
    Finset.sum_range_succ]
  ring

theorem chebyshevS_homogenize_eval_one_add_sq
    (R : Type*) [CommRing R] [Nontrivial R]
    (j : ℕ) (x : R) :
    MvPolynomial.eval ![1 + x ^ 2, x]
        ((Polynomial.Chebyshev.S R (j : ℤ)).homogenize j) =
      ∑ k ∈ Finset.range (j + 1), x ^ (2 * k) := by
  induction j using Nat.twoStepInduction with
  | zero => simp only [Nat.succ_eq_add_one, Nat.reduceAdd, CharP.cast_eq_zero,
              Polynomial.Chebyshev.S_zero, Polynomial.homogenize_one, Fin.isValue, pow_zero,
              map_one, zero_add, Finset.range_one, Finset.sum_singleton, mul_zero]
  | one =>
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Nat.cast_one, Polynomial.Chebyshev.S_one,
        ne_eq, one_ne_zero, not_false_eq_true, Polynomial.homogenize_X, Fin.isValue, tsub_self,
        pow_zero, mul_one, MvPolynomial.eval_X, Matrix.cons_val_zero, Finset.sum_range_succ,
        Finset.range_one, Finset.sum_singleton, mul_zero]
  | more n ih0 ih1 =>
      rw [chebyshevS_homogenize_add_two]
      simp only [map_sub, map_mul, map_pow, MvPolynomial.eval_X,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [ih1, ih0]
      simpa only [Nat.add_assoc, Nat.reduceAdd] using (even_geometric_sum_add_two x n).symm

theorem det_homogenized_monic_evaluation
    {R : Type*} [CommRing R] {r : ℕ}
    (p : Fin (r + 1) → Polynomial R)
    (hdegree : ∀ j, (p j).natDegree = j.val)
    (hmonic : ∀ j, (p j).Monic)
    (v w : Fin (r + 1) → R) :
    Matrix.det
        (fun i j : Fin (r + 1) =>
          ∑ k ∈ Finset.range (j.val + 1),
            (p j).coeff k * (v i) ^ k * (w i) ^ (r - k)) =
      (Matrix.projVandermonde v w).det := by
  let C : Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
    Matrix.of fun k j => (p j).coeff k.val
  have hmatrix :
      (fun i j : Fin (r + 1) =>
        ∑ k ∈ Finset.range (j.val + 1),
          (p j).coeff k * (v i) ^ k * (w i) ^ (r - k)) =
        Matrix.projVandermonde v w * C := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.projVandermonde_apply,
      C, Matrix.of_apply]
    simp only [Fin.rev, Nat.add_sub_add_right]
    change
      (∑ k ∈ Finset.range (j.val + 1),
        (p j).coeff k * v i ^ k * w i ^ (r - k)) =
        ∑ k : Fin (r + 1),
          v i ^ (k : ℕ) * w i ^ (r - (k : ℕ)) *
            (p j).coeff (k : ℕ)
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ =>
      v i ^ k * w i ^ (r - k) * (p j).coeff k)]
    have hsubset : Finset.range (j.val + 1) ⊆
        Finset.range (r + 1) :=
      Finset.range_mono j.isLt
    calc
      (∑ k ∈ Finset.range (j.val + 1),
        (p j).coeff k * v i ^ k * w i ^ (r - k)) =
          ∑ k ∈ Finset.range (r + 1),
            (p j).coeff k * v i ^ k * w i ^ (r - k) := by
        apply Finset.sum_subset hsubset
        intro k hk hnot
        have hk' : j.val < k := by
          have hle : j.val + 1 ≤ k :=
            Nat.le_of_not_gt (by simpa only [gt_iff_lt, Order.lt_add_one_iff, not_le,
                                   Finset.mem_range] using hnot)
          omega
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt
          (hdegree j ▸ hk')]
        simp only [zero_mul]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        ring
  rw [hmatrix, Matrix.det_mul]
  have hC : C.det = 1 := by
    exact Matrix.det_matrixOfPolynomials p
      (fun i => by simpa only using hdegree i) hmonic
  rw [hC, mul_one]

theorem homogenize_eval_eq_sum_coeff
    {R : Type*} [CommSemiring R]
    (p : Polynomial R) (j : ℕ) (v w : R) :
    MvPolynomial.eval ![v, w] (p.homogenize j) =
      ∑ k ∈ Finset.range (j + 1),
        p.coeff k * v ^ k * w ^ (j - k) := by
  simp only [Polynomial.homogenize, MvPolynomial.eval_sum,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro k hk
  rw [MvPolynomial.eval_monomial,
    Finsupp.update_eq_add_single (by simp only [Fin.isValue, ne_eq, one_ne_zero, not_false_eq_true,
                                       Finsupp.single_eq_of_ne]),
    Finsupp.prod_add_index', Finsupp.prod_single_index,
    Finsupp.prod_single_index] <;>
    simp [mul_assoc, pow_add]

theorem det_orthogonal_denominator_row_factor
    {R : Type*} [CommRing R] {r : ℕ}
    (x : Fin (r + 1) → R) :
    Matrix.det
        (fun i j : Fin (r + 1) =>
          x i ^ (r - j.val) - x i ^ (r + j.val + 2)) =
      (∏ i : Fin (r + 1), (1 - x i ^ 2)) *
        Matrix.det
          (fun i j : Fin (r + 1) =>
            x i ^ (r - j.val) *
              ∑ k ∈ Finset.range (j.val + 1), x i ^ (2 * k)) := by
  classical
  let A : Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
    fun i j => x i ^ (r - j.val) *
      ∑ k ∈ Finset.range (j.val + 1), x i ^ (2 * k)
  have hmatrix :
      (fun i j : Fin (r + 1) =>
        x i ^ (r - j.val) - x i ^ (r + j.val + 2)) =
        Matrix.of (fun i j => (1 - x i ^ 2) * A i j) := by
    ext i j
    change
      x i ^ (r - j.val) - x i ^ (r + j.val + 2) =
        (1 - x i ^ 2) *
          (x i ^ (r - j.val) *
            ∑ k ∈ Finset.range (j.val + 1), x i ^ (2 * k))
    rw [orthogonal_denominator_entry (x i) r j.val (by omega)]
    ring
  rw [hmatrix, Matrix.det_mul_column]

theorem det_chebyshev_geometric_sum
    {R : Type*} [CommRing R] [Nontrivial R] {r : ℕ}
    (x : Fin (r + 1) → R) :
    Matrix.det (fun i j : Fin (r + 1) =>
      x i ^ (r - j.val) *
        (∑ k ∈ Finset.range (j.val + 1), x i ^ (2 * k))) =
      (Matrix.projVandermonde (fun i => 1 + (x i) ^ 2) x).det := by
  have hdet := det_homogenized_monic_evaluation
    (r := r) (fun j : Fin (r + 1) =>
      Polynomial.Chebyshev.S R (j.val : ℤ))
    (fun j => chebyshevS_natDegree R j.val)
    (fun j => chebyshevS_monic R j.val)
    (fun i => 1 + (x i) ^ 2) x
  rw [← hdet]
  congr 1
  funext i j
  have heval := chebyshevS_homogenize_eval_one_add_sq R j.val (x i)
  rw [← heval, homogenize_eval_eq_sum_coeff, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkj : k ≤ j.val := by
    have hlt : k < j.val + 1 := Finset.mem_range.mp hk
    omega
  have hjr : j.val ≤ r := by
    have hlt := j.isLt
    omega
  calc
    x i ^ (r - j.val) *
        ((Polynomial.Chebyshev.S R (j.val : ℤ)).coeff k *
          (1 + x i ^ 2) ^ k * x i ^ (j.val - k)) =
      (Polynomial.Chebyshev.S R (j.val : ℤ)).coeff k *
        (1 + x i ^ 2) ^ k *
          (x i ^ (r - j.val) * x i ^ (j.val - k)) := by ring
    _ = _ := by
      rw [← pow_add]
      congr 1
      congr 1
      omega

theorem det_orthogonal_denominator
    {R : Type*} [CommRing R] {r : ℕ}
    (x : Fin (r + 1) → R) :
    Matrix.det
        (fun i j : Fin (r + 1) =>
          x i ^ (r - j.val) - x i ^ (r + j.val + 2)) =
      Matrix.det (fun i j : Fin (r + 1) => x i ^ (r - j.val)) *
        ∏ i : Fin (r + 1), ∏ j ∈ Finset.Ici i,
          (1 - x i * x j) := by
  classical
  rcases subsingleton_or_nontrivial R with h | h
  · exact h.elim _ _
  · let := h
    rw [det_orthogonal_denominator_row_factor,
      det_chebyshev_geometric_sum,
      det_quadratic_projective_vandermonde,
      ← upper_gram_pair_product]
    ring

end OrthogonalDenominator

end

namespace UniversalBGGRootComplex

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

theorem positiveRoot_prod_eq {R : Type*} [CommMonoid R] {r : ℕ}
    (f : Fin (r + 1) → Fin (r + 1) → R) :
    (∏ α : PositiveRoot r,
      f (positiveRootFirst α) (positiveRootSecond α)) =
      ∏ i : Fin (r + 1), ∏ j ∈ Finset.Ioi i, f i j := by
  classical
  let e : PositiveRoot r ≃
      (Σ i : Fin (r + 1), {j : Fin (r + 1) // i < j}) :=
    Equiv.subtypeProdEquivSigmaSubtype (fun i j : Fin (r + 1) => i < j)
  calc
    (∏ α : PositiveRoot r,
      f (positiveRootFirst α) (positiveRootSecond α)) =
        ∏ t : (Σ i : Fin (r + 1), {j : Fin (r + 1) // i < j}),
          f t.1 t.2 := by
            exact e.prod_comp (fun t => f t.1 t.2)
    _ = _ := by
      rw [Fintype.prod_sigma]
      apply Finset.prod_congr rfl
      intro i _
      change (∏ y : {j : Fin (r + 1) // i < j}, f i y) = _
      exact (Finset.prod_subtype (Finset.Ioi i)
        (fun j => Finset.mem_Ioi) (f i)).symm

theorem positiveRoot_vandermonde {r : ℕ} :
    (∏ α : PositiveRoot r,
      (MvPolynomial.X (positiveRootSecond α) -
        MvPolynomial.X (positiveRootFirst α) :
          MvPolynomial (Fin (r + 1)) ℤ)) =
      ∑ σ : Equiv.Perm (Fin (r + 1)),
        (Equiv.Perm.sign σ : ℤ) •
          ∏ i : Fin (r + 1),
            MvPolynomial.X i ^ (σ i).val := by
  rw [positiveRoot_prod_eq (fun i j =>
    MvPolynomial.X j - MvPolynomial.X i)]
  rw [← Matrix.det_vandermonde
    (fun i : Fin (r + 1) =>
      (MvPolynomial.X i : MvPolynomial (Fin (r + 1)) ℤ))]
  rw [← Matrix.det_transpose, Matrix.det_apply]
  simp only [Matrix.transpose_apply, Matrix.vandermonde_apply, Units.smul_def, zsmul_eq_mul]

private def shiftedPolynomialWeightFunctional {r : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (F : (Fin (r + 1) → ℤ) → ℤ) :
    MvPolynomial (Fin (r + 1)) ℤ →ₗ[ℤ] ℤ :=
  ((Finsupp.lsum ℤ)
    (fun m : Fin (r + 1) →₀ ℕ =>
      LinearMap.mulLeft ℤ
        (F (fun i => (lam i : ℤ) + (m i : ℤ) - i.val)))).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap

@[simp] theorem shiftedPolynomialWeightFunctional_monomial
    {r : ℕ} (lam : Fin (r + 1) → ℕ)
    (F : (Fin (r + 1) → ℤ) → ℤ)
    (m : Fin (r + 1) →₀ ℕ) (c : ℤ) :
    shiftedPolynomialWeightFunctional lam F
        (MvPolynomial.monomial m c) =
      F (fun i => (lam i : ℤ) + (m i : ℤ) - i.val) * c := by
  change ((Finsupp.lsum ℤ)
    (fun m : Fin (r + 1) →₀ ℕ =>
      LinearMap.mulLeft ℤ
        (F (fun i => (lam i : ℤ) + (m i : ℤ) - i.val))))
      (Finsupp.single m c) = _
  exact Finsupp.lsum_single ℤ _ m c

private def rootSelectedExponent {r : ℕ}
    (S : Finset (PositiveRoot r)) : Fin (r + 1) →₀ ℕ :=
  (∑ α ∈ (Finset.univ \ S),
    Finsupp.single (positiveRootSecond α) 1) +
  ∑ α ∈ S, Finsupp.single (positiveRootFirst α) 1

@[simp] theorem rootSelectedExponent_apply {r : ℕ}
    (S : Finset (PositiveRoot r)) (i : Fin (r + 1)) :
    rootSelectedExponent S i =
      (∑ α ∈ (Finset.univ \ S),
        if positiveRootSecond α = i then 1 else 0) +
        ∑ α ∈ S, if positiveRootFirst α = i then 1 else 0 := by
  simp only [rootSelectedExponent, Finsupp.coe_add, Finsupp.coe_finsetSum, Pi.add_apply,
    Finset.sum_apply, Finsupp.single_apply, Finset.sum_boole, Nat.cast_id]

theorem positiveRootSecond_card {r : ℕ} (i : Fin (r + 1)) :
    (Finset.univ.filter
      (fun α : PositiveRoot r => positiveRootSecond α = i)).card =
        i.val := by
  classical
  let e : {α : PositiveRoot r // positiveRootSecond α = i} ≃
      Fin i.val :=
    { toFun := fun α => ⟨(positiveRootFirst α.val).val,
        by
          have h := positiveRootFirst_lt_second α.val
          rw [α.property] at h
          exact h⟩
      invFun := fun j =>
        ⟨⟨(⟨j.val, by omega⟩, i), by
          change j.val < i.val
          exact j.isLt⟩, rfl⟩
      left_inv := by
        rintro ⟨⟨⟨a, b⟩, hab⟩, hb⟩
        change b = i at hb
        subst b
        rfl
      right_inv := by
        intro j
        apply Fin.ext
        rfl }
  have h := Fintype.card_congr e
  simpa only [Fintype.card_subtype, Fintype.card_fin] using h

theorem rootSelectedExponent_sub_baseline {r : ℕ}
    (S : Finset (PositiveRoot r)) (i : Fin (r + 1)) :
    (rootSelectedExponent S i : ℤ) - i.val =
      rootFamilyCharge S i := by
  classical
  let second : PositiveRoot r → ℕ :=
    fun α => if positiveRootSecond α = i then 1 else 0
  let first : PositiveRoot r → ℕ :=
    fun α => if positiveRootFirst α = i then 1 else 0
  have hsplit :
      (∑ α ∈ (Finset.univ \ S), second α) +
        (∑ α ∈ S, second α) =
          ∑ α : PositiveRoot r, second α := by
    simpa only [add_comm] using (Finset.sum_sdiff (Finset.subset_univ S) (f := second))
  have hsecond : (∑ α : PositiveRoot r, second α) = i.val := by
    simpa [second, Finset.sum_boole] using positiveRootSecond_card i
  have hcharge : rootFamilyCharge S i =
      (∑ α ∈ S, (first α : ℤ)) -
        ∑ α ∈ S, (second α : ℤ) := by
    unfold rootFamilyCharge
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro α _
    by_cases hfirst : positiveRootFirst α = i
    · subst i
      have hne := positiveRootFirst_ne_second α
      simp only [rootCharge, ↓reduceIte, Nat.cast_one, hne.symm, CharP.cast_eq_zero, sub_zero,
        first, second]
    · by_cases hsecond : positiveRootSecond α = i
      · subst i
        have hne := positiveRootFirst_ne_second α
        simp only [rootCharge, hne.symm, ↓reduceIte, Int.reduceNeg, hne, CharP.cast_eq_zero,
          Nat.cast_one, zero_sub, first, second]
      · simp only [rootCharge, Ne.symm hfirst, ↓reduceIte, Ne.symm hsecond, hfirst,
          CharP.cast_eq_zero, hsecond, sub_self, first, second]
  rw [hcharge, rootSelectedExponent_apply]
  change
    ↑((∑ α ∈ Finset.univ \ S, second α) +
      ∑ α ∈ S, first α) - (i.val : ℤ) =
      (∑ α ∈ S, (first α : ℤ)) - ∑ α ∈ S, (second α : ℤ)
  have hnat :
    (∑ α ∈ (Finset.univ \ S), second α) +
      (∑ α ∈ S, first α) +
        (∑ α ∈ S, second α) =
          i.val + (∑ α ∈ S, first α) := by omega
  have hfirstCast : (∑ α ∈ S, (first α : ℤ)) =
      ((∑ α ∈ S, first α : ℕ) : ℤ) := by norm_cast
  have hsecondCast : (∑ α ∈ S, (second α : ℤ)) =
      ((∑ α ∈ S, second α : ℕ) : ℤ) := by norm_cast
  rw [hfirstCast, hsecondCast]
  omega

theorem rootFamily_selectedMonomial {r : ℕ}
    (S : Finset (PositiveRoot r)) :
    (∏ α ∈ Finset.univ \ S,
      (MvPolynomial.X (positiveRootSecond α) :
        MvPolynomial (Fin (r + 1)) ℤ)) *
      (∏ α ∈ S,
        (MvPolynomial.X (positiveRootFirst α) :
          MvPolynomial (Fin (r + 1)) ℤ)) =
      MvPolynomial.monomial (rootSelectedExponent S) 1 := by
  classical
  have hsecond := MvPolynomial.monomial_sum_prod
    (Finset.univ \ S)
    (fun α : PositiveRoot r =>
      Finsupp.single (positiveRootSecond α) 1)
    (fun _ : PositiveRoot r => (1 : ℤ))
  have hfirst := MvPolynomial.monomial_sum_prod
    S (fun α : PositiveRoot r =>
      Finsupp.single (positiveRootFirst α) 1)
    (fun _ : PositiveRoot r => (1 : ℤ))
  simp only [Finset.prod_const_one] at hsecond hfirst
  have hsecond' :
      (∏ α ∈ Finset.univ \ S,
        (MvPolynomial.X (positiveRootSecond α) :
          MvPolynomial (Fin (r + 1)) ℤ)) =
        MvPolynomial.monomial
          (∑ α ∈ Finset.univ \ S,
            Finsupp.single (positiveRootSecond α) 1) 1 := by
    simpa only [MvPolynomial.X] using hsecond.symm
  have hfirst' :
      (∏ α ∈ S,
        (MvPolynomial.X (positiveRootFirst α) :
          MvPolynomial (Fin (r + 1)) ℤ)) =
        MvPolynomial.monomial
          (∑ α ∈ S,
            Finsupp.single (positiveRootFirst α) 1) 1 := by
    simpa only [MvPolynomial.X] using hfirst.symm
  rw [hsecond', hfirst']
  simp [rootSelectedExponent]

private def rootPermutationExponent {r : ℕ}
    (σ : Equiv.Perm (Fin (r + 1))) : Fin (r + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (σ i).val)

@[simp] theorem rootPermutationExponent_apply {r : ℕ}
    (σ : Equiv.Perm (Fin (r + 1))) (i : Fin (r + 1)) :
    rootPermutationExponent σ i = (σ i).val := by
  simp only [rootPermutationExponent, Finsupp.equivFunOnFinite_symm_apply_apply]

theorem rootPermutationMonomial {r : ℕ}
    (σ : Equiv.Perm (Fin (r + 1))) :
    (∏ i : Fin (r + 1),
      (MvPolynomial.X i : MvPolynomial (Fin (r + 1)) ℤ) ^
        (σ i).val) =
      MvPolynomial.monomial (rootPermutationExponent σ) 1 := by
  classical
  rw [MvPolynomial.prod_X_pow]
  have h : Finsupp.indicator (Finset.univ : Finset (Fin (r + 1)))
      (fun i _ => (σ i).val) = rootPermutationExponent σ := by
    ext i
    simp only [Finsupp.indicator_apply, Finset.mem_univ, ↓reduceDIte, rootPermutationExponent_apply]
  rw [h]

theorem signedRootFamily_vandermonde_expansion {r : ℕ} :
    (∏ α : PositiveRoot r,
      (MvPolynomial.X (positiveRootSecond α) -
        MvPolynomial.X (positiveRootFirst α) :
          MvPolynomial (Fin (r + 1)) ℤ)) =
      ∑ S : Finset (PositiveRoot r),
        MvPolynomial.monomial (rootSelectedExponent S)
          ((-1 : ℤ) ^ S.card) := by
  classical
  rw [Finset.prod_sub]
  have hpowerset :
      (Finset.univ : Finset (PositiveRoot r)).powerset =
        (Finset.univ : Finset (Finset (PositiveRoot r))) := by
    ext S
    simp only [Finset.powerset_univ, Finset.mem_univ]
  rw [hpowerset]
  apply Finset.sum_congr rfl
  intro S _
  rw [mul_assoc, rootFamily_selectedMonomial]
  have hpow :
      ((-1 : MvPolynomial (Fin (r + 1)) ℤ) ^ S.card) =
        MvPolynomial.C ((-1 : ℤ) ^ S.card) := by
    simp only [Int.reduceNeg, eq_intCast, Int.cast_pow, Int.cast_neg, Int.cast_one]
  rw [hpow, MvPolynomial.C_mul_monomial]
  simp only [Int.reduceNeg, mul_one]

theorem rootFamilyCharge_alternating_eq_weylShift
    {r : ℕ} (lam : Fin (r + 1) → ℕ)
    (F : (Fin (r + 1) → ℤ) → ℤ) :
    (∑ S : Finset (PositiveRoot r),
      (-1 : ℤ) ^ S.card * F (signedRootWeight lam S)) =
        ∑ σ : Equiv.Perm (Fin (r + 1)),
          (Equiv.Perm.sign σ : ℤ) * F (weylShift lam σ) := by
  classical
  have hfamily : ∀ S : Finset (PositiveRoot r),
      (fun i : Fin (r + 1) =>
        (lam i : ℤ) + (rootSelectedExponent S i : ℤ) - i.val) =
          signedRootWeight lam S := by
    intro S
    funext i
    have h := rootSelectedExponent_sub_baseline S i
    change (lam i : ℤ) + (rootSelectedExponent S i : ℤ) - i.val =
      (lam i : ℤ) + rootFamilyCharge S i
    omega
  have hperm : ∀ σ : Equiv.Perm (Fin (r + 1)),
      (fun i : Fin (r + 1) =>
        (lam i : ℤ) + (rootPermutationExponent σ i : ℤ) - i.val) =
          weylShift lam σ := by
    intro σ
    funext i
    simp only [rootPermutationExponent_apply, weylShift]
    omega
  have hpoly :=
    (signedRootFamily_vandermonde_expansion (r := r)).symm.trans
      (positiveRoot_vandermonde (r := r))
  have h := congrArg (shiftedPolynomialWeightFunctional lam F) hpoly
  simp only [map_sum, map_zsmul] at h
  simp_rw [rootPermutationMonomial,
    shiftedPolynomialWeightFunctional_monomial] at h
  simp_rw [hfamily, hperm] at h
  simpa only [Int.reduceNeg, mul_comm, one_mul, Int.zsmul_eq_mul] using h

theorem finrank_rootJointHarmonicChain {r n k : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    Module.finrank ℝ (RootJointHarmonicChain n lam k) =
      ∑ S : AdmissibleRootWedge lam k,
        Module.finrank ℝ
          (JointHarmonicWeightSpace n (rootWedgeWeight lam S)) := by
  classical
  let : ∀ S : AdmissibleRootWedge lam k,
      Module.Free ℝ
        (JointHarmonicWeightSpace n (rootWedgeWeight lam S)) :=
    fun S => Module.Free.of_basis
      (Module.Basis.ofVectorSpace ℝ
        (JointHarmonicWeightSpace n (rootWedgeWeight lam S)))
  let : ∀ S : AdmissibleRootWedge lam k,
      Module.Finite ℝ
        (JointHarmonicWeightSpace n (rootWedgeWeight lam S)) :=
    fun _ => inferInstance
  exact Module.finrank_pi_fintype ℝ

theorem signedJointHarmonicWeightDimension_signedRootWeight
    {r n k : ℕ} (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam k) :
    signedJointHarmonicWeightDimension n
        (signedRootWeight lam S.val.val) =
      (Module.finrank ℝ
        (JointHarmonicWeightSpace n (rootWedgeWeight lam S)) : ℤ) := by
  unfold signedJointHarmonicWeightDimension
  rw [dite_eq_left S.property]
  rfl

/-- The root exterior euler characteristic used in the spherical-code argument. -/
def rootExteriorEulerCharacteristic {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) : ℤ :=
  ∑ k ∈ Finset.range (Fintype.card (PositiveRoot r) + 1),
    (-1 : ℤ) ^ k *
      (Module.finrank ℝ (RootJointHarmonicChain n lam k) : ℤ)

/-- The root family euler characteristic used in the spherical-code argument. -/
def rootFamilyEulerCharacteristic {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) : ℤ :=
  ∑ S : Finset (PositiveRoot r),
    (-1 : ℤ) ^ S.card *
      signedJointHarmonicWeightDimension n
        (signedRootWeight lam S)

theorem rootFamilyEulerCharacteristic_eq_alternatingJointHarmonicWeightDimension
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) :
    rootFamilyEulerCharacteristic n lam =
      alternatingJointHarmonicWeightDimension n lam := by
  exact rootFamilyCharge_alternating_eq_weylShift lam
    (signedJointHarmonicWeightDimension n)

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

theorem rootStructureConstant_swap {r : ℕ}
    (α β γ : PositiveRoot r) :
    rootStructureConstant β α γ =
      -rootStructureConstant α β γ := by
  unfold rootStructureConstant
  ring

theorem rootAction_apply_X {r n : ℕ}
    (x : RootVector r) (j : Fin (r + 1)) (k : Fin n) :
    rootAction n x (MvPolynomial.X (variableIndex j k)) =
      ∑ α ∈ x.support,
        x α •
          (if α.val.1 = j then
            MvPolynomial.X (variableIndex α.val.2 k) else 0) := by
  classical
  rw [rootAction, Finsupp.linearCombination_apply, Finsupp.sum]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply,
    positiveRootOperator_apply, polarization_X_euler]

theorem rootAction_X_coefficient {r n : ℕ}
    (x : RootVector r) (α : PositiveRoot r) (k : Fin n) :
    MvPolynomial.coeff
      (Finsupp.single (variableIndex α.val.2 k) 1)
      (rootAction n x
        (MvPolynomial.X (variableIndex α.val.1 k))) = x α := by
  classical
  rw [rootAction_apply_X]
  simp_rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul]
  by_cases hα : α ∈ x.support
  · rw [Finset.sum_eq_single α]
    · simp only [↓reduceIte, MvPolynomial.coeff_X, smul_eq_mul, mul_one]
    · intro β hβ hne
      by_cases hsource : β.val.1 = α.val.1
      · have htarget : β.val.2 ≠ α.val.2 := by
          intro htarget'
          apply hne
          apply Subtype.ext
          apply Prod.ext
          · exact hsource
          · exact htarget'
        have hvar : variableIndex β.val.2 k ≠
            variableIndex α.val.2 k := by
          simpa only [ne_eq, variableIndex_eq_iff_harmonicLift, and_true] using htarget
        have hsingle :
            Finsupp.single (variableIndex β.val.2 k) 1 ≠
              Finsupp.single (variableIndex α.val.2 k) 1 := by
          intro h
          exact hvar (Finsupp.single_left_injective (by norm_num : (1 : ℕ) ≠ 0) h)
        simp only [hsource, ↓reduceIte, MvPolynomial.coeff_X, hsingle, smul_eq_mul, mul_zero]
      · simp only [hsource, ↓reduceIte, MvPolynomial.coeff_zero, smul_eq_mul, mul_zero]
    · exact fun h => (h hα).elim
  · have hx : x α = 0 := Finsupp.notMem_support_iff.mp hα
    rw [hx]
    apply Finset.sum_eq_zero
    intro β hβ
    by_cases hsource : β.val.1 = α.val.1
    · have htarget : β.val.2 ≠ α.val.2 := by
        intro htarget'
        have heq : β = α := by
          apply Subtype.ext
          apply Prod.ext
          · exact hsource
          · exact htarget'
        subst β
        exact hα hβ
      have hvar : variableIndex β.val.2 k ≠
          variableIndex α.val.2 k := by
        simpa only [ne_eq, variableIndex_eq_iff_harmonicLift, and_true] using htarget
      have hsingle :
          Finsupp.single (variableIndex β.val.2 k) 1 ≠
            Finsupp.single (variableIndex α.val.2 k) 1 := by
        intro h
        exact hvar (Finsupp.single_left_injective (by norm_num : (1 : ℕ) ≠ 0) h)
      simp only [hsource, ↓reduceIte, MvPolynomial.coeff_X, hsingle, smul_eq_mul, mul_zero]
    · simp only [hsource, ↓reduceIte, MvPolynomial.coeff_zero, smul_eq_mul, mul_zero]

theorem rootAction_injective {r n : ℕ}
    (hn : 0 < n) : Function.Injective (rootAction (r := r) n) := by
  intro x y hxy
  ext α
  let k : Fin n := ⟨0, hn⟩
  have hcoord := LinearMap.congr_fun hxy
    (MvPolynomial.X (variableIndex α.val.1 k))
  have hcoeff := congrArg
    (MvPolynomial.coeff
      (Finsupp.single (variableIndex α.val.2 k) 1)) hcoord
  simpa only [rootAction_X_coefficient] using hcoeff

/-- The root vector bracket used in the spherical-code argument. -/
def rootVectorBracket {r : ℕ} (x y : RootVector r) : RootVector r :=
  Finsupp.linearCombination ℝ
    (fun α : PositiveRoot r =>
      Finsupp.linearCombination ℝ (rootBracket α) y) x

@[simp] theorem rootVectorBracket_zero_left {r : ℕ} (y : RootVector r) :
    rootVectorBracket 0 y = 0 := by
  simp only [rootVectorBracket, map_zero]

@[simp] theorem rootVectorBracket_zero_right {r : ℕ} (x : RootVector r) :
    rootVectorBracket x 0 = 0 := by
  rw [rootVectorBracket]
  change Finsupp.linearCombination ℝ (fun _ : PositiveRoot r => 0) x = 0
  exact Finsupp.linearCombination_zero_apply ℝ x

@[simp] theorem rootVectorBracket_single_single {r : ℕ}
    (α β : PositiveRoot r) (a b : ℝ) :
    rootVectorBracket (Finsupp.single α a) (Finsupp.single β b) =
      (a * b) • rootBracket α β := by
  simp only [rootVectorBracket, Finsupp.linearCombination_single, smul_smul]

theorem rootVectorBracket_add_left {r : ℕ} (x y z : RootVector r) :
    rootVectorBracket (x + y) z =
      rootVectorBracket x z + rootVectorBracket y z := by
  exact map_add (Finsupp.linearCombination ℝ
    (fun α : PositiveRoot r =>
      Finsupp.linearCombination ℝ (rootBracket α) z)) x y

theorem rootVectorBracket_add_right {r : ℕ} (x y z : RootVector r) :
    rootVectorBracket x (y + z) =
      rootVectorBracket x y + rootVectorBracket x z := by
  classical
  unfold rootVectorBracket
  simp_rw [map_add]
  rw [Finsupp.linearCombination_apply,
    Finsupp.linearCombination_apply,
    Finsupp.linearCombination_apply,
    Finsupp.sum, Finsupp.sum, Finsupp.sum]
  simp_rw [smul_add]
  rw [Finset.sum_add_distrib]

theorem rootAction_rootVectorBracket {r n : ℕ}
    (x y : RootVector r) :
    rootAction n (rootVectorBracket x y) =
      (rootAction n x).comp (rootAction n y) -
        (rootAction n y).comp (rootAction n x) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp only [rootVectorBracket_zero_left, map_zero, LinearMap.zero_comp,
              LinearMap.comp_zero, sub_self]
  | add x₁ x₂ hx₁ hx₂ =>
      rw [rootVectorBracket_add_left, map_add, hx₁, hx₂, map_add]
      apply LinearMap.ext
      intro p
      simp only [LinearMap.sub_apply, LinearMap.comp_apply,
        LinearMap.add_apply, map_add]
      abel
  | single α a =>
      induction y using Finsupp.induction_linear with
      | zero => simp only [rootVectorBracket_zero_right, map_zero, rootAction_single,
                  LinearMap.comp_zero, LinearMap.zero_comp, sub_self]
      | add y₁ y₂ hy₁ hy₂ =>
          rw [rootVectorBracket_add_right, map_add, hy₁, hy₂, map_add]
          apply LinearMap.ext
          intro p
          simp only [LinearMap.sub_apply, LinearMap.comp_apply,
            LinearMap.add_apply, map_add]
          abel
      | single β b =>
          rw [rootVectorBracket_single_single, map_smul,
            rootAction_rootBracket, rootAction_single,
            rootAction_single]
          apply LinearMap.ext
          intro p
          simp only [LinearMap.smul_apply, LinearMap.sub_apply,
            LinearMap.comp_apply, map_smul, smul_sub, smul_smul]
          module

theorem rootVectorBracket_jacobi {r : ℕ} (x y z : RootVector r) :
    rootVectorBracket x (rootVectorBracket y z) +
      rootVectorBracket y (rootVectorBracket z x) +
      rootVectorBracket z (rootVectorBracket x y) = 0 := by
  apply rootAction_injective (r := r) (n := 1) (by decide)
  simp only [map_add, map_zero, rootAction_rootVectorBracket]
  apply LinearMap.ext
  intro p
  simp only [LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, map_sub]
  change _ = (0 : PolynomialSpace r 1)
  abel

end

section


open MetricCodes.Spherical.HigherHarmonicYoung

attribute [local instance 100] LieRing.ofAssociativeRing

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

/-- The root bracket boundary coefficient used in the spherical-code argument. -/
def rootBracketBoundaryCoefficient {r k : ℕ}
    (S : RootWedge r (k + 1)) (T : RootWedge r k) : ℝ := by
  classical
  exact ∑ α ∈ S.val, ∑ β ∈ S.val.erase α,
    if α < β then
      ∑ γ : PositiveRoot r,
        if γ ∉ (S.val.erase α).erase β ∧
            T.val = insert γ ((S.val.erase α).erase β) then
          realExteriorRootSign S.val α *
            realExteriorRootSign (S.val.erase α) β *
            realExteriorRootSign T.val γ *
            rootStructureConstant α β γ
        else 0
    else 0

/-- The root wedge singleton used in the spherical-code argument. -/
def rootWedgeSingleton {r : ℕ} (α : PositiveRoot r) : RootWedge r 1 :=
  ⟨{α}, by simp only [Finset.card_singleton]⟩

/-- The root bracket boundary used in the spherical-code argument. -/
def rootBracketBoundary (r n k : ℕ) :
    RootPolynomialChain r n (k + 1) →ₗ[ℝ]
      RootPolynomialChain r n k :=
  LinearMap.pi fun T =>
    ∑ S : RootWedge r (k + 1),
      rootBracketBoundaryCoefficient S T •
        (LinearMap.proj S :
          RootPolynomialChain r n (k + 1) →ₗ[ℝ]
            PolynomialSpace r n)

@[simp] theorem rootBracketBoundary_apply {r n k : ℕ}
    (f : RootPolynomialChain r n (k + 1)) (T : RootWedge r k) :
    rootBracketBoundary r n k f T =
      ∑ S : RootWedge r (k + 1),
        rootBracketBoundaryCoefficient S T • f S := by
  classical
  simp only [rootBracketBoundary, LinearMap.pi_apply, LinearMap.coe_sum, LinearMap.coe_smul,
    LinearMap.coe_proj, Finset.sum_apply, Pi.smul_apply, Function.eval]

@[simp] theorem rootBracketBoundaryCoefficient_degree_zero {r : ℕ}
    (S : RootWedge r 1) (T : RootWedge r 0) :
    rootBracketBoundaryCoefficient S T = 0 := by
  classical
  unfold rootBracketBoundaryCoefficient
  apply Finset.sum_eq_zero
  intro α hα
  have herase : S.val.erase α = ∅ := by
    apply Finset.card_eq_zero.mp
    rw [Finset.card_erase_of_mem hα, S.property]
  simp only [Nat.reduceAdd, herase, Finset.notMem_empty, not_false_eq_true,
    Finset.erase_eq_of_notMem, insert_empty_eq, true_and, Finset.sum_empty]

/-- The root chevalley eilenberg boundary used in the spherical-code argument. -/
def rootChevalleyEilenbergBoundary (r n k : ℕ) :
    RootPolynomialChain r n (k + 1) →ₗ[ℝ]
      RootPolynomialChain r n k :=
  rootActionBoundary r n k + rootBracketBoundary r n k

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

theorem rootStructureConstant_cases_disjoint {r : ℕ}
    (α β γ : PositiveRoot r)
    (hfirst : α.val.1 = β.val.2 ∧
      γ.val = (β.val.1, α.val.2))
    (hsecond : β.val.1 = α.val.2 ∧
      γ.val = (α.val.1, β.val.2)) : False := by
  have hα := α.property
  have hβ := β.property
  omega

theorem rootStructureConstant_ne_zero_iff {r : ℕ}
    (α β γ : PositiveRoot r) :
    rootStructureConstant α β γ ≠ 0 ↔
      (α.val.1 = β.val.2 ∧ γ.val = (β.val.1, α.val.2)) ∨
        (β.val.1 = α.val.2 ∧ γ.val = (α.val.1, β.val.2)) := by
  classical
  let A : Prop := α.val.1 = β.val.2 ∧
    γ.val = (β.val.1, α.val.2)
  let B : Prop := β.val.1 = α.val.2 ∧
    γ.val = (α.val.1, β.val.2)
  have hdisjoint : ¬ (A ∧ B) := by
    rintro ⟨hA, hB⟩
    exact rootStructureConstant_cases_disjoint α β γ hA hB
  change ((if A then (1 : ℝ) else 0) -
    (if B then (1 : ℝ) else 0) ≠ 0) ↔ A ∨ B
  by_cases hA : A <;> by_cases hB : B
  · exact (hdisjoint ⟨hA, hB⟩).elim
  all_goals simp [hA, hB]

theorem rootCharge_eq_add_of_structureConstant_ne_zero {r : ℕ}
    (α β γ : PositiveRoot r)
    (h : rootStructureConstant α β γ ≠ 0)
    (i : Fin (r + 1)) :
    rootCharge γ i = rootCharge α i + rootCharge β i := by
  rcases (rootStructureConstant_ne_zero_iff α β γ).mp h with
    ⟨hjoin, hγ⟩ | ⟨hjoin, hγ⟩
  · have hγfirst : γ.val.1 = β.val.1 := by
      simpa only using congrArg (fun z : Fin (r + 1) × Fin (r + 1) => z.1) hγ
    have hγsecond : γ.val.2 = α.val.2 := by
      simpa only using congrArg (fun z : Fin (r + 1) × Fin (r + 1) => z.2) hγ
    have hα := α.property
    have hβ := β.property
    unfold rootCharge positiveRootFirst positiveRootSecond
    split_ifs <;> omega
  · have hγfirst : γ.val.1 = α.val.1 := by
      simpa only using congrArg (fun z : Fin (r + 1) × Fin (r + 1) => z.1) hγ
    have hγsecond : γ.val.2 = β.val.2 := by
      simpa only using congrArg (fun z : Fin (r + 1) × Fin (r + 1) => z.2) hγ
    have hα := α.property
    have hβ := β.property
    unfold rootCharge positiveRootFirst positiveRootSecond
    split_ifs <;> omega

theorem exists_rootBracketWitness_of_coefficient_ne_zero {r k : ℕ}
    (S : RootWedge r (k + 1)) (T : RootWedge r k)
    (h : rootBracketBoundaryCoefficient S T ≠ 0) :
    ∃ (α β γ : PositiveRoot r),
      α ∈ S.val ∧ β ∈ S.val.erase α ∧ α < β ∧
      γ ∉ (S.val.erase α).erase β ∧
      T.val = insert γ ((S.val.erase α).erase β) ∧
      rootStructureConstant α β γ ≠ 0 := by
  classical
  unfold rootBracketBoundaryCoefficient at h
  obtain ⟨α, hα, hαsum⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨β, hβ, hβsum⟩ := Finset.exists_ne_zero_of_sum_ne_zero hαsum
  by_cases horder : α < β
  · simp only [horder, ↓reduceIte] at hβsum
    obtain ⟨γ, _, hγ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hβsum
    by_cases htarget : γ ∉ (S.val.erase α).erase β ∧
        T.val = insert γ ((S.val.erase α).erase β)
    · simp only [ite_eq_left htarget] at hγ
      have hconstant : rootStructureConstant α β γ ≠ 0 := by
        intro hzero
        simp only [hzero, mul_zero, ne_eq, not_true_eq_false] at hγ
      exact ⟨α, β, γ, hα, hβ, horder,
        htarget.1, htarget.2, hconstant⟩
    · exact (hγ (by rw [ite_eq_right htarget])).elim
  · simp only [horder, ↓reduceIte, ne_eq, not_true_eq_false] at hβsum

theorem signedRootWeight_eq_of_bracketWitness {r : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (S T : Finset (PositiveRoot r))
    (α β γ : PositiveRoot r)
    (hα : α ∈ S) (hβ : β ∈ S.erase α)
    (hγ : γ ∉ (S.erase α).erase β)
    (hT : T = insert γ ((S.erase α).erase β))
    (hconstant : rootStructureConstant α β γ ≠ 0)
    (i : Fin (r + 1)) :
    signedRootWeight lam S i = signedRootWeight lam T i := by
  have hfirst := signedRootWeight_erase lam S α hα i
  have hsecond := signedRootWeight_erase lam (S.erase α) β hβ i
  have htarget :=
    signedRootWeight_insert lam ((S.erase α).erase β) γ hγ i
  rw [← hT] at htarget
  have hcharge :=
    rootCharge_eq_add_of_structureConstant_ne_zero α β γ hconstant i
  omega

theorem signedRootWeight_eq_of_bracketBoundaryCoefficient_ne_zero
    {r k : ℕ} (lam : Fin (r + 1) → ℕ)
    (S : RootWedge r (k + 1)) (T : RootWedge r k)
    (h : rootBracketBoundaryCoefficient S T ≠ 0)
    (i : Fin (r + 1)) :
    signedRootWeight lam S.val i = signedRootWeight lam T.val i := by
  obtain ⟨α, β, γ, hα, hβ, _, hγ, htarget, hconstant⟩ :=
    exists_rootBracketWitness_of_coefficient_ne_zero S T h
  exact signedRootWeight_eq_of_bracketWitness lam S.val T.val
    α β γ hα hβ hγ htarget hconstant i

theorem rootWedgeWeight_eq_of_bracketBoundaryCoefficient_ne_zero
    {r k : ℕ} (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam (k + 1))
    (T : AdmissibleRootWedge lam k)
    (h : rootBracketBoundaryCoefficient S.val T.val ≠ 0) :
    rootWedgeWeight lam S = rootWedgeWeight lam T := by
  funext i
  exact_mod_cast
    (show (rootWedgeWeight lam S i : ℤ) =
      (rootWedgeWeight lam T i : ℤ) by
      rw [rootWedgeWeight_cast, rootWedgeWeight_cast]
      exact signedRootWeight_eq_of_bracketBoundaryCoefficient_ne_zero
        lam S.val T.val h i)

/-- The weighted root bracket edge used in the spherical-code argument. -/
def weightedRootBracketEdge {r k : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam (k + 1))
    (T : AdmissibleRootWedge lam k)
    (h : rootBracketBoundaryCoefficient S.val T.val ≠ 0) :
    JointHarmonicWeightSpace n (rootWedgeWeight lam S) →ₗ[ℝ]
      JointHarmonicWeightSpace n (rootWedgeWeight lam T) :=
  (jointHarmonicWeightCast n (rootWedgeWeight lam S)
    (rootWedgeWeight lam T)
    (rootWedgeWeight_eq_of_bracketBoundaryCoefficient_ne_zero
      lam S T h)).toLinearMap

@[simp] theorem weightedRootBracketEdge_coe {r n k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam (k + 1))
    (T : AdmissibleRootWedge lam k)
    (h : rootBracketBoundaryCoefficient S.val T.val ≠ 0)
    (p : JointHarmonicWeightSpace n (rootWedgeWeight lam S)) :
    (((weightedRootBracketEdge n lam S T h p).val :
      youngMultihomogeneousSubmodule n (rootWedgeWeight lam T)) :
      PolynomialSpace r n) =
      (p.val : PolynomialSpace r n) :=
  jointHarmonicWeightCast_coe
    (rootWedgeWeight lam S) (rootWedgeWeight lam T)
    (rootWedgeWeight_eq_of_bracketBoundaryCoefficient_ne_zero
      lam S T h) p

/-- The weighted root bracket boundary used in the spherical-code argument. -/
def weightedRootBracketBoundary {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) (k : ℕ) :
    RootJointHarmonicChain n lam (k + 1) →ₗ[ℝ]
      RootJointHarmonicChain n lam k := by
  classical
  refine
    { toFun := fun f T =>
        ∑ S : AdmissibleRootWedge lam (k + 1),
          if h : rootBracketBoundaryCoefficient S.val T.val = 0 then 0
          else rootBracketBoundaryCoefficient S.val T.val •
            weightedRootBracketEdge n lam S T h (f S)
      map_add' := ?_
      map_smul' := ?_ }
  · intro f g
    funext T
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro S _
    split_ifs with h
    · simp only [add_zero]
    · simp only [map_add, smul_add]
  · intro c f
    funext T
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro S _
    split_ifs with h
    · simp only [smul_zero]
    · simp only [map_smul, smul_smul, mul_comm]

@[simp] theorem weightedRootBracketBoundary_apply {r n k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (f : RootJointHarmonicChain n lam (k + 1))
    (T : AdmissibleRootWedge lam k) :
    weightedRootBracketBoundary n lam k f T =
      ∑ S : AdmissibleRootWedge lam (k + 1),
        if h : rootBracketBoundaryCoefficient S.val T.val = 0 then 0
        else rootBracketBoundaryCoefficient S.val T.val •
          weightedRootBracketEdge n lam S T h (f S) := by
  unfold weightedRootBracketBoundary DFunLike.coe LinearMap.instFunLike
  with_reducible rfl

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

/-- The weighted chevalley eilenberg differential used in the spherical-code argument. -/
def weightedChevalleyEilenbergDifferential {r : ℕ}
    (n : ℕ) (lam : Fin (r + 1) → ℕ) (k : ℕ) :
    RootJointHarmonicChain n lam (k + 1) →ₗ[ℝ]
      RootJointHarmonicChain n lam k :=
  weightedExteriorActionDifferential n lam k +
    weightedRootBracketBoundary n lam k

end

section


open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung

instance rootJointHarmonicChain_finiteDimensional {r n k : ℕ}
    (lam : Fin (r + 1) → ℕ) :
    FiniteDimensional ℝ (RootJointHarmonicChain n lam k) := by
  classical
  let : ∀ S : AdmissibleRootWedge lam k,
      FiniteDimensional ℝ
        (JointHarmonicWeightSpace n (rootWedgeWeight lam S)) :=
    fun S => jointHarmonicWeightSpace_finiteDimensional n
      (rootWedgeWeight lam S)
  exact Module.Finite.pi

theorem admissibleRootWedge_above_card_isEmpty {r k : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (hk : Fintype.card (PositiveRoot r) < k) :
    IsEmpty (AdmissibleRootWedge lam k) := by
  constructor
  intro S
  have hle : S.val.val.card ≤ Fintype.card (PositiveRoot r) := by
    simpa only [Set.powersetCard.card_eq, Finset.card_univ] using
      (Finset.card_le_card (Finset.subset_univ S.val.val))
  have hcard : S.val.val.card = k := S.val.property
  omega

theorem admissibleRootWedge_one_exists_active {r : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (S : AdmissibleRootWedge lam 1) :
    ∃ α : PositiveRoot r,
      S.val.val = {α} ∧ 0 < lam (positiveRootSecond α) := by
  obtain ⟨α, hα⟩ := Finset.card_eq_one.mp S.val.property
  refine ⟨α, hα, ?_⟩
  have hnonneg := S.property (positiveRootSecond α)
  rw [signedRootWeight, hα, rootFamilyCharge_singleton,
    rootCharge_second] at hnonneg
  omega

theorem rootJointHarmonicChainDifferential_top_eq_zero
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (d : ∀ k,
      RootJointHarmonicChain n lam (k + 1) →ₗ[ℝ]
        RootJointHarmonicChain n lam k) :
    d (Fintype.card (PositiveRoot r)) = 0 := by
  apply LinearMap.ext
  intro p
  have hp : p = 0 := by
    funext S
    exact False.elim
      ((admissibleRootWedge_above_card_isEmpty lam
        (by omega)).false S)
  simp only [hp, map_zero]

@[simp] theorem weightedRootBracketBoundary_degree_zero
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) :
    weightedRootBracketBoundary n lam 0 = 0 := by
  apply LinearMap.ext
  intro p
  funext T
  change weightedRootBracketBoundary n lam 0 p T = 0
  rw [weightedRootBracketBoundary_apply]
  apply Finset.sum_eq_zero
  intro S _
  have hzero : rootBracketBoundaryCoefficient S.val T.val = 0 :=
    rootBracketBoundaryCoefficient_degree_zero S.val T.val
  simp only [Nat.reduceAdd, rootBracketBoundaryCoefficient_degree_zero, ↓reduceDIte]

@[simp] theorem weightedChevalleyEilenbergDifferential_degree_zero
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) :
    weightedChevalleyEilenbergDifferential n lam 0 =
      weightedExteriorActionDifferential n lam 0 := by
  unfold weightedChevalleyEilenbergDifferential
  rw [weightedRootBracketBoundary_degree_zero]
  exact add_zero _

theorem finrank_harmonicYoung_eq_rootExteriorEulerCharacteristic_of_rootExact
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (d : ∀ k,
      RootJointHarmonicChain n lam (k + 1) →ₗ[ℝ]
        RootJointHarmonicChain n lam k)
    (hexact : ∀ k, k < Fintype.card (PositiveRoot r) →
      LinearMap.range (d (k + 1)) = LinearMap.ker (d k))
    (hzero :
      Module.finrank ℝ
          (LinearMap.ker (rootDegreeZeroPositiveCochain n lam)) +
        Module.finrank ℝ (LinearMap.range (d 0)) =
          Module.finrank ℝ (RootJointHarmonicChain n lam 0)) :
    (Module.finrank ℝ (HarmonicYoungSpace (n := n) lam) : ℤ) =
      rootExteriorEulerCharacteristic n lam := by
  classical
  let : ∀ k : ℕ,
      FiniteDimensional ℝ (RootJointHarmonicChain n lam k) :=
    fun k => rootJointHarmonicChain_finiteDimensional lam
  have htop :
      Module.finrank ℝ
        (LinearMap.range (d (Fintype.card (PositiveRoot r)))) = 0 := by
    have hrange :
        LinearMap.range (d (Fintype.card (PositiveRoot r))) = ⊥ := by
      rw [rootJointHarmonicChainDifferential_top_eq_zero lam d]
      exact LinearMap.range_zero
    rw [hrange, finrank_bot]
  have h := finiteChain_eulerCharacteristic_eq_degreeZero_sub_boundary_add_top
    (fun k => RootJointHarmonicChain n lam k)
    d (Fintype.card (PositiveRoot r)) hexact
  rw [htop, Nat.cast_zero, mul_zero, add_zero] at h
  change rootExteriorEulerCharacteristic n lam =
    (Module.finrank ℝ (RootJointHarmonicChain n lam 0) : ℤ) -
      (Module.finrank ℝ (LinearMap.range (d 0)) : ℤ) at h
  have hzero' :
      (Module.finrank ℝ
          (LinearMap.ker (rootDegreeZeroPositiveCochain n lam)) : ℤ) +
        (Module.finrank ℝ (LinearMap.range (d 0)) : ℤ) =
          (Module.finrank ℝ (RootJointHarmonicChain n lam 0) : ℤ) := by
    exact_mod_cast hzero
  have hker := finrank_rootDegreeZeroPositiveCochain_kernel
    (n := n) lam
  omega

end

end UniversalBGGRootComplex

end HigherHarmonicYoung

end Spherical

end MetricCodes

end MetricCodesNoncomputable
