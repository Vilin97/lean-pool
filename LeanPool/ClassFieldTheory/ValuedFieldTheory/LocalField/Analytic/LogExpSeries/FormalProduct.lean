/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.SetTheory.Cardinal.Finite
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCore
/-!
Proves the formal combinatorial identities behind additivity of the logarithm on products of
principal units.
-/

open Filter
open Polynomial
open scoped Topology
open scoped PowerSeries.WithPiTopology
noncomputable section

attribute [local instance] Classical.propDecidable

universe u

open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

variable {K : Type u} [Field K]

/-- Proves the bound `e (0 : Fin 2) ≤ q ∧ e (1 : Fin 2) ≤ q ∧ q ≤ e (0 : Fin 2) + e (1 : Fin 2)`. -/
theorem formalLogOnePlusProductArgument_choiceCounts_q_range
    {q : ℕ} {e : Fin 2 →₀ ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hl : l ∈ Finset.finsuppAntidiag (Finset.range q) e)
    (hbasic : ∀ i ∈ Finset.range q,
      formalLogOnePlusProductArgumentBasicFactor (l i)) :
    e (0 : Fin 2) ≤ q ∧ e (1 : Fin 2) ≤ q ∧
      q ≤ e (0 : Fin 2) + e (1 : Fin 2) := by
  exact
    ⟨formalLogOnePlusProductArgument_choiceCounts_left_coord_le_q
        hl hbasic,
      formalLogOnePlusProductArgument_choiceCounts_right_coord_le_q
        hl hbasic,
      formalLogOnePlusProductArgument_choiceCounts_q_le_coord_sum
        hl hbasic⟩

/-- Proves the bound `e (0 : Fin 2) ≤ q ∧ e (1 : Fin 2) ≤ q ∧ q ≤ e (0 : Fin 2) + e (1 : Fin 2)`. -/
theorem formalLogOnePlusProductArgumentBasicFactorChoices_nonempty_q_range
    {q : ℕ} {e : Fin 2 →₀ ℕ}
    (h :
      (formalLogOnePlusProductArgumentBasicFactorChoices q e).Nonempty) :
    e (0 : Fin 2) ≤ q ∧ e (1 : Fin 2) ≤ q ∧
      q ≤ e (0 : Fin 2) + e (1 : Fin 2) := by
  rcases h with ⟨l, hl⟩
  rw [mem_formalLogOnePlusProductArgumentBasicFactorChoices] at hl
  exact formalLogOnePlusProductArgument_choiceCounts_q_range hl.1 hl.2

/-- Establishes the identity `formalLogOnePlusProductArgumentBasicFactorChoices q e = ∅`. -/
theorem formalLogOnePlusProductArgumentBasicFactorChoices_eq_empty_of_q_lt_left_coord
    {q : ℕ} {e : Fin 2 →₀ ℕ}
    (hleft : q < e (0 : Fin 2)) :
    formalLogOnePlusProductArgumentBasicFactorChoices q e = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.2
  intro l hl
  rw [mem_formalLogOnePlusProductArgumentBasicFactorChoices] at hl
  exact
    (not_le_of_gt hleft)
      (formalLogOnePlusProductArgument_choiceCounts_q_range hl.1 hl.2).1

/-- Establishes the identity `formalLogOnePlusProductArgumentBasicFactorChoices q e = ∅`. -/
theorem formalLogOnePlusProductArgumentBasicFactorChoices_eq_empty_of_q_lt_right_coord
    {q : ℕ} {e : Fin 2 →₀ ℕ}
    (hright : q < e (1 : Fin 2)) :
    formalLogOnePlusProductArgumentBasicFactorChoices q e = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.2
  intro l hl
  rw [mem_formalLogOnePlusProductArgumentBasicFactorChoices] at hl
  exact
    (not_le_of_gt hright)
      (formalLogOnePlusProductArgument_choiceCounts_q_range hl.1 hl.2).2.1

/-- Establishes the identity `formalLogOnePlusProductArgumentBasicFactorChoices q e = ∅`. -/
theorem formalLogOnePlusProductArgumentBasicFactorChoices_eq_empty_of_coord_sum_lt_q
    {q : ℕ} {e : Fin 2 →₀ ℕ}
    (hsum : e (0 : Fin 2) + e (1 : Fin 2) < q) :
    formalLogOnePlusProductArgumentBasicFactorChoices q e = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.2
  intro l hl
  rw [mem_formalLogOnePlusProductArgumentBasicFactorChoices] at hl
  exact
    (not_le_of_gt hsum)
      (formalLogOnePlusProductArgument_choiceCounts_q_range hl.1 hl.2).2.2

/--
Establishes the identity `(∏ i ∈ Finset.range q, MvPowerSeries.coeff (l i)
(formalLogOnePlusProductArgument A)) = 1`.
-/
theorem formalLogOnePlusProductArgument_pow_term_prod_eq_one_of_factors_basic
    (A : Type*) [CommRing A] {q : ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hbasic : ∀ i ∈ Finset.range q,
      l i = Finsupp.single (0 : Fin 2) 1 ∨
        l i = Finsupp.single (1 : Fin 2) 1 ∨
          l i =
            Finsupp.single (0 : Fin 2) 1 +
              Finsupp.single (1 : Fin 2) 1) :
    (∏ i ∈ Finset.range q,
      MvPowerSeries.coeff (l i) (formalLogOnePlusProductArgument A)) = 1 := by
  apply Finset.prod_eq_one
  intro i hi
  rcases hbasic i hi with hleft | hrightOrMixed
  · simp [hleft]
  · rcases hrightOrMixed with hright | hmixed
    · simp [hright]
    · simp [hmixed]

/--
Establishes the identity `(∏ i ∈ Finset.range q, MvPowerSeries.coeff (l i)
(formalLogOnePlusProductArgument A)) = 1`.
-/
theorem formalLogOnePlusProductArgument_pow_term_prod_eq_one_of_basicFactor
    (A : Type*) [CommRing A] {q : ℕ} {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hbasic : ∀ i ∈ Finset.range q,
      formalLogOnePlusProductArgumentBasicFactor (l i)) :
    (∏ i ∈ Finset.range q,
      MvPowerSeries.coeff (l i) (formalLogOnePlusProductArgument A)) = 1 :=
  formalLogOnePlusProductArgument_pow_term_prod_eq_one_of_factors_basic
    A (fun i hi => by
      simpa [formalLogOnePlusProductArgumentBasicFactor] using hbasic i hi)

/--
Establishes the identity `(∏ i ∈ Finset.range q, MvPowerSeries.coeff (l i)
(formalLogOnePlusProductArgument A)) = 1`.
-/
theorem formalLogOnePlusProductArgument_pow_term_prod_eq_one_of_ne_zero
    (A : Type*) [CommRing A] {q : ℕ}
    {l : ℕ →₀ (Fin 2 →₀ ℕ)}
    (hprod :
      (∏ i ∈ Finset.range q,
        MvPowerSeries.coeff (l i) (formalLogOnePlusProductArgument A)) ≠ 0) :
    (∏ i ∈ Finset.range q,
      MvPowerSeries.coeff (l i) (formalLogOnePlusProductArgument A)) = 1 := by
  exact
    formalLogOnePlusProductArgument_pow_term_prod_eq_one_of_factors_basic
      A (fun i hi =>
        formalLogOnePlusProductArgument_pow_term_factor_eq_basic_of_prod_ne_zero
          A hprod hi)

/--
Establishes the identity `MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) = ∑ l ∈
Finset.finsuppAntidiag (Finset.range q) e, if ∀ i ∈ Finset.range q,
formalLogOnePlusProductArgumentBasicFactor (l i) then (1 : A) else 0`.
-/
theorem formalLogOnePlusProductArgument_pow_coeff_eq_sum_basicFactor
    (A : Type*) [CommRing A] (q : ℕ) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) =
      ∑ l ∈ Finset.finsuppAntidiag (Finset.range q) e,
        if ∀ i ∈ Finset.range q,
            formalLogOnePlusProductArgumentBasicFactor (l i)
        then (1 : A) else 0 := by
  classical
  rw [MvPowerSeries.coeff_pow]
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hbasic :
      ∀ i ∈ Finset.range q,
        formalLogOnePlusProductArgumentBasicFactor (l i)
  · rw [formalLogOnePlusProductArgument_pow_term_prod_eq_one_of_basicFactor
      A hbasic]
    rw [ite_eq_left hbasic]
  · have hprodZero :
        (∏ i ∈ Finset.range q,
          MvPowerSeries.coeff (l i) (formalLogOnePlusProductArgument A)) = 0 := by
      by_contra hprodNe
      apply hbasic
      intro i hi
      exact
        formalLogOnePlusProductArgument_coeff_ne_zero_eq_basic A (l i) (by
          intro hzero
          exact hprodNe (Finset.prod_eq_zero hi hzero))
    rw [hprodZero]
    rw [ite_eq_right hbasic]

/--
Establishes the identity `(∑ l ∈ Finset.finsuppAntidiag (Finset.range q) e, if ∀ i ∈ Finset.range
q, formalLogOnePlusProductArgumentBasicFactor (l i) then (1 : A) else 0) =
((formalLogOnePlusProductArgumentBasicFactorChoices q e).card : A)`.
-/
theorem formalLogOnePlusProductArgument_basicFactor_sum_eq_card_choices
    (A : Type*) [CommRing A] (q : ℕ) (e : Fin 2 →₀ ℕ) :
    (∑ l ∈ Finset.finsuppAntidiag (Finset.range q) e,
      if ∀ i ∈ Finset.range q,
          formalLogOnePlusProductArgumentBasicFactor (l i)
      then (1 : A) else 0) =
      ((formalLogOnePlusProductArgumentBasicFactorChoices q e).card : A) := by
  classical
  simp [formalLogOnePlusProductArgumentBasicFactorChoices]

/--
Establishes the identity `MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) =
((formalLogOnePlusProductArgumentBasicFactorChoices q e).card : A)`.
-/
theorem formalLogOnePlusProductArgument_pow_coeff_eq_card_choices
    (A : Type*) [CommRing A] (q : ℕ) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) =
      ((formalLogOnePlusProductArgumentBasicFactorChoices q e).card : A) := by
  rw [formalLogOnePlusProductArgument_pow_coeff_eq_sum_basicFactor,
    formalLogOnePlusProductArgument_basicFactor_sum_eq_card_choices]

/--
Establishes the identity `MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) = 0`.
-/
theorem formalLogOnePlusProductArgument_pow_coeff_eq_zero_of_coord_sum_lt
    (A : Type*) [CommRing A] (q : ℕ) (e : Fin 2 →₀ ℕ)
    (hsum : e (0 : Fin 2) + e (1 : Fin 2) < q) :
    MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) = 0 := by
  rw [formalLogOnePlusProductArgument_pow_coeff_eq_card_choices,
    formalLogOnePlusProductArgumentBasicFactorChoices_eq_empty_of_coord_sum_lt_q
      hsum]
  simp

/--
Establishes the identity `MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) = 0`.
-/
theorem formalLogOnePlusProductArgument_pow_coeff_eq_zero_of_left_coord_lt
    (A : Type*) [CommRing A] (q : ℕ) (e : Fin 2 →₀ ℕ)
    (hleft : q < e (0 : Fin 2)) :
    MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) = 0 := by
  classical
  rw [MvPowerSeries.coeff_pow]
  apply Finset.sum_eq_zero
  intro l hl
  rw [Finset.mem_finsuppAntidiag] at hl
  by_cases hprod :
      ∏ i ∈ Finset.range q,
        MvPowerSeries.coeff (l i) (formalLogOnePlusProductArgument A) = 0
  · exact hprod
  · exfalso
    have hfactor :
        ∀ i ∈ Finset.range q,
          MvPowerSeries.coeff (l i)
            (formalLogOnePlusProductArgument A) ≠ 0 := by
      intro i hi hzero
      exact hprod (Finset.prod_eq_zero hi hzero)
    have hcoord :
        (∑ i ∈ Finset.range q, l i (0 : Fin 2)) = e (0 : Fin 2) := by
      simpa [Finsupp.finsetSum_apply] using
        congrArg (fun m : Fin 2 →₀ ℕ => m (0 : Fin 2)) hl.1
    have hsum_le :
        (∑ i ∈ Finset.range q, l i (0 : Fin 2)) ≤
          ∑ _i ∈ Finset.range q, 1 := by
      exact Finset.sum_le_sum fun i hi =>
        formalLogOnePlusProductArgument_coeff_ne_zero_left_coord_le_one
          A (l i) (hfactor i hi)
    have hcoord_le : e (0 : Fin 2) ≤ q := by
      simpa [hcoord] using hsum_le
    exact (not_lt_of_ge hcoord_le) hleft

/--
Establishes the identity `MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) = 0`.
-/
theorem formalLogOnePlusProductArgument_pow_coeff_eq_zero_of_right_coord_lt
    (A : Type*) [CommRing A] (q : ℕ) (e : Fin 2 →₀ ℕ)
    (hright : q < e (1 : Fin 2)) :
    MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) = 0 := by
  classical
  rw [MvPowerSeries.coeff_pow]
  apply Finset.sum_eq_zero
  intro l hl
  rw [Finset.mem_finsuppAntidiag] at hl
  by_cases hprod :
      ∏ i ∈ Finset.range q,
        MvPowerSeries.coeff (l i) (formalLogOnePlusProductArgument A) = 0
  · exact hprod
  · exfalso
    have hfactor :
        ∀ i ∈ Finset.range q,
          MvPowerSeries.coeff (l i)
            (formalLogOnePlusProductArgument A) ≠ 0 := by
      intro i hi hzero
      exact hprod (Finset.prod_eq_zero hi hzero)
    have hcoord :
        (∑ i ∈ Finset.range q, l i (1 : Fin 2)) = e (1 : Fin 2) := by
      simpa [Finsupp.finsetSum_apply] using
        congrArg (fun m : Fin 2 →₀ ℕ => m (1 : Fin 2)) hl.1
    have hsum_le :
        (∑ i ∈ Finset.range q, l i (1 : Fin 2)) ≤
          ∑ _i ∈ Finset.range q, 1 := by
      exact Finset.sum_le_sum fun i hi =>
        formalLogOnePlusProductArgument_coeff_ne_zero_right_coord_le_one
          A (l i) (hfactor i hi)
    have hcoord_le : e (1 : Fin 2) ≤ q := by
      simpa [hcoord] using hsum_le
    exact (not_lt_of_ge hcoord_le) hright

/--
Establishes the identity `MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) = 0`.
-/
theorem formalLogOnePlusProductArgument_pow_coeff_eq_zero_of_degree_lt
    (A : Type*) [CommRing A] (q : ℕ) (e : Fin 2 →₀ ℕ)
    (hdegree : Finsupp.degree e < q) :
    MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) = 0 := by
  have hnil :
      MvPowerSeries.constantCoeff (formalLogOnePlusProductArgument A) ^ 1 =
        0 := by
    simp [formalLogOnePlusProductArgument_constantCoeff A]
  exact
    MvPowerSeries.coeff_eq_zero_of_constantCoeff_nilpotent
      (f := formalLogOnePlusProductArgument A) (m := 1) hnil
      (d := e) (n := q) (by
        have hs : Finsupp.degree e + 1 ≤ q :=
          Nat.succ_le_of_lt hdegree
        simpa [Nat.add_comm] using hs)

/--
Establishes the identity `PowerSeries.coeff q (PowerSeries.log A) •
MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) = 0`.
-/
theorem formalLogOnePlusProductArgument_logSubst_coeff_term_eq_zero_of_degree_lt
    (A : Type*) [CommRing A] [Algebra ℚ A] (q : ℕ) (e : Fin 2 →₀ ℕ)
    (hdegree : Finsupp.degree e < q) :
    PowerSeries.coeff q (PowerSeries.log A) •
        MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) =
      0 := by
  rw [formalLogOnePlusProductArgument_pow_coeff_eq_zero_of_degree_lt
    A q e hdegree]
  simp

/--
Establishes the identity `PowerSeries.coeff q (PowerSeries.log A) •
MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) = 0`.
-/
theorem formalLogOnePlusProductArgument_logSubst_coeff_term_eq_zero_of_left_coord_lt
    (A : Type*) [CommRing A] [Algebra ℚ A] (q : ℕ) (e : Fin 2 →₀ ℕ)
    (hleft : q < e (0 : Fin 2)) :
    PowerSeries.coeff q (PowerSeries.log A) •
        MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) =
      0 := by
  rw [formalLogOnePlusProductArgument_pow_coeff_eq_zero_of_left_coord_lt
    A q e hleft]
  simp

/--
Establishes the identity `PowerSeries.coeff q (PowerSeries.log A) •
MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) = 0`.
-/
theorem formalLogOnePlusProductArgument_logSubst_coeff_term_eq_zero_of_right_coord_lt
    (A : Type*) [CommRing A] [Algebra ℚ A] (q : ℕ) (e : Fin 2 →₀ ℕ)
    (hright : q < e (1 : Fin 2)) :
    PowerSeries.coeff q (PowerSeries.log A) •
        MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) =
      0 := by
  rw [formalLogOnePlusProductArgument_pow_coeff_eq_zero_of_right_coord_lt
    A q e hright]
  simp

/-- Expands a coefficient of the logarithm substituted at the product
argument as a finite sum bounded by the total degree of the exponent. -/
theorem formalLogOnePlusProductArgument_logSubst_coeff_eq_sum_range_degree_succ
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e
        (PowerSeries.subst (formalLogOnePlusProductArgument A) (PowerSeries.log A)) =
      ∑ q ∈ Finset.range (Finsupp.degree e + 1),
        PowerSeries.coeff q (PowerSeries.log A) •
          MvPowerSeries.coeff e
            ((formalLogOnePlusProductArgument A) ^ q) := by
  rw [PowerSeries.coeff_subst
    (formalLogOnePlusProductArgument_hasSubst A) (PowerSeries.log A) e]
  apply finsum_eq_sum_of_support_subset
  intro q hq
  by_contra hmem
  rw [Finset.mem_coe, Finset.mem_range] at hmem
  have hdegree : Finsupp.degree e < q := Nat.lt_of_succ_le
    (Nat.le_of_not_gt hmem)
  exact hq
    (formalLogOnePlusProductArgument_logSubst_coeff_term_eq_zero_of_degree_lt
      A q e hdegree)

/-- Refines the coefficient expansion to powers at least as large as both
coordinates of the exponent. -/
theorem formalLogOnePlusProductArgument_logSubst_coeff_eq_sum_range_degree_succ_filter_coord_le
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e
        (PowerSeries.subst (formalLogOnePlusProductArgument A) (PowerSeries.log A)) =
      ∑ q ∈
        (Finset.range (Finsupp.degree e + 1)).filter
          (fun q : ℕ => e (0 : Fin 2) ≤ q ∧ e (1 : Fin 2) ≤ q),
        PowerSeries.coeff q (PowerSeries.log A) •
          MvPowerSeries.coeff e
            ((formalLogOnePlusProductArgument A) ^ q) := by
  rw [formalLogOnePlusProductArgument_logSubst_coeff_eq_sum_range_degree_succ]
  exact
    (Finset.sum_subset (Finset.filter_subset _ _) (fun q hq hnot => by
      by_cases hleft : e (0 : Fin 2) ≤ q
      · by_cases hright : e (1 : Fin 2) ≤ q
        · exfalso
          exact hnot (by simpa [hleft, hright] using hq)
        · exact
            formalLogOnePlusProductArgument_logSubst_coeff_term_eq_zero_of_right_coord_lt
              A q e (Nat.lt_of_not_ge hright)
      · exact
          formalLogOnePlusProductArgument_logSubst_coeff_term_eq_zero_of_left_coord_lt
            A q e (Nat.lt_of_not_ge hleft))).symm

/--
Establishes the divisibility statement `(MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) A) ∣
formalLogOnePlusProductArgument A - MvPowerSeries.X (0 : Fin 2)`.
-/
theorem formalLogOnePlusProductArgument_sub_leftVariable_dvd_rightVariable
    (A : Type*) [CommRing A] :
    (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) A) ∣
      formalLogOnePlusProductArgument A -
        MvPowerSeries.X (0 : Fin 2) := by
  let X0 : MvPowerSeries (Fin 2) A := MvPowerSeries.X (0 : Fin 2)
  let X1 : MvPowerSeries (Fin 2) A := MvPowerSeries.X (1 : Fin 2)
  refine ⟨1 + X0, ?_⟩
  change formalLogOnePlusProductArgument A - X0 = X1 * (1 + X0)
  simp [formalLogOnePlusProductArgument]
  ring

/--
Establishes the divisibility statement `(MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) A) ∣
formalLogOnePlusProductArgument A - MvPowerSeries.X (1 : Fin 2)`.
-/
theorem formalLogOnePlusProductArgument_sub_rightVariable_dvd_leftVariable
    (A : Type*) [CommRing A] :
    (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) A) ∣
      formalLogOnePlusProductArgument A -
        MvPowerSeries.X (1 : Fin 2) := by
  let X0 : MvPowerSeries (Fin 2) A := MvPowerSeries.X (0 : Fin 2)
  let X1 : MvPowerSeries (Fin 2) A := MvPowerSeries.X (1 : Fin 2)
  refine ⟨1 + X1, ?_⟩
  change formalLogOnePlusProductArgument A - X1 = X0 * (1 + X1)
  simp [formalLogOnePlusProductArgument]
  ring

/--
Establishes the divisibility statement `(MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) A) ∣
(formalLogOnePlusProductArgument A) ^ d - (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) A)
^ d`.
-/
theorem formalLogOnePlusProductArgument_pow_sub_leftVariable_pow_dvd_rightVariable
    (A : Type*) [CommRing A] (d : ℕ) :
    (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) A) ∣
      (formalLogOnePlusProductArgument A) ^ d -
        (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) A) ^ d := by
  exact
    (formalLogOnePlusProductArgument_sub_leftVariable_dvd_rightVariable A).trans
      (sub_dvd_pow_sub_pow
        (formalLogOnePlusProductArgument A)
        (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) A) d)

/--
Establishes the divisibility statement `(MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) A) ∣
(formalLogOnePlusProductArgument A) ^ d - (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) A)
^ d`.
-/
theorem formalLogOnePlusProductArgument_pow_sub_rightVariable_pow_dvd_leftVariable
    (A : Type*) [CommRing A] (d : ℕ) :
    (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) A) ∣
      (formalLogOnePlusProductArgument A) ^ d -
        (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) A) ^ d := by
  exact
    (formalLogOnePlusProductArgument_sub_rightVariable_dvd_leftVariable A).trans
      (sub_dvd_pow_sub_pow
        (formalLogOnePlusProductArgument A)
        (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) A) d)

/--
Establishes the identity `MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) n)
((formalLogOnePlusProductArgument A) ^ d) = MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) n)
((MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) A) ^ d)`.
-/
theorem formalLogOnePlusProductArgument_pow_coeff_single_left
    (A : Type*) [CommRing A] (d n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) n)
        ((formalLogOnePlusProductArgument A) ^ d) =
      MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) n)
        ((MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) A) ^ d) := by
  have hdiv :=
    formalLogOnePlusProductArgument_pow_sub_leftVariable_pow_dvd_rightVariable
      A d
  have hcoeffSub :
      MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) n)
        ((formalLogOnePlusProductArgument A) ^ d -
          (MvPowerSeries.X (0 : Fin 2) :
            MvPowerSeries (Fin 2) A) ^ d) = 0 := by
    have hvanish :=
      (MvPowerSeries.X_pow_dvd_iff
        (s := (1 : Fin 2)) (n := 1)
        (φ := (formalLogOnePlusProductArgument A) ^ d -
          (MvPowerSeries.X (0 : Fin 2) :
            MvPowerSeries (Fin 2) A) ^ d)).1
        (by simpa using hdiv)
    exact hvanish (Finsupp.single (0 : Fin 2) n) (by
      have h10 : (1 : Fin 2) ≠ (0 : Fin 2) := by decide
      simp [Finsupp.single_eq_of_ne h10])
  rw [map_sub] at hcoeffSub
  exact sub_eq_zero.mp hcoeffSub

/--
Establishes the identity `MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n)
((formalLogOnePlusProductArgument A) ^ d) = MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n)
((MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) A) ^ d)`.
-/
theorem formalLogOnePlusProductArgument_pow_coeff_single_right
    (A : Type*) [CommRing A] (d n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n)
        ((formalLogOnePlusProductArgument A) ^ d) =
      MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n)
        ((MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) A) ^ d) := by
  have hdiv :=
    formalLogOnePlusProductArgument_pow_sub_rightVariable_pow_dvd_leftVariable
      A d
  have hcoeffSub :
      MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n)
        ((formalLogOnePlusProductArgument A) ^ d -
          (MvPowerSeries.X (1 : Fin 2) :
            MvPowerSeries (Fin 2) A) ^ d) = 0 := by
    have hvanish :=
      (MvPowerSeries.X_pow_dvd_iff
        (s := (0 : Fin 2)) (n := 1)
        (φ := (formalLogOnePlusProductArgument A) ^ d -
          (MvPowerSeries.X (1 : Fin 2) :
            MvPowerSeries (Fin 2) A) ^ d)).1
        (by simpa using hdiv)
    exact hvanish (Finsupp.single (1 : Fin 2) n) (by
      have h01 : (0 : Fin 2) ≠ (1 : Fin 2) := by decide
      simp [Finsupp.single_eq_of_ne h01])
  rw [map_sub] at hcoeffSub
  exact sub_eq_zero.mp hcoeffSub

/--
Establishes the identity `MvPowerSeries.coeff e ((MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin
2) A) ^ d) = if e = Finsupp.single (0 : Fin 2) d then 1 else 0`.
-/
theorem formalLogOnePlusLeftVariable_pow_coeff
    (A : Type*) [CommRing A] (e : Fin 2 →₀ ℕ) (d : ℕ) :
    MvPowerSeries.coeff e
        ((MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) A) ^ d) =
      if e = Finsupp.single (0 : Fin 2) d then 1 else 0 := by
  simpa using
    MvPowerSeries.coeff_X_pow (R := A) e (0 : Fin 2) d

/--
Establishes the identity `MvPowerSeries.coeff e ((MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin
2) A) ^ d) = if e = Finsupp.single (1 : Fin 2) d then 1 else 0`.
-/
theorem formalLogOnePlusRightVariable_pow_coeff
    (A : Type*) [CommRing A] (e : Fin 2 →₀ ℕ) (d : ℕ) :
    MvPowerSeries.coeff e
        ((MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) A) ^ d) =
      if e = Finsupp.single (1 : Fin 2) d then 1 else 0 := by
  simpa using
    MvPowerSeries.coeff_X_pow (R := A) e (1 : Fin 2) d

/--
Establishes the identity `MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) n)
(PowerSeries.subst (formalLogOnePlusProductArgument A) (PowerSeries.log A)) = PowerSeries.coeff n
(PowerSeries.log A)`.
-/
theorem formalLogOnePlusProductArgument_logSubst_coeff_single_left
    (A : Type*) [CommRing A] [Algebra ℚ A] (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) n)
        (PowerSeries.subst (formalLogOnePlusProductArgument A) (PowerSeries.log A)) =
      PowerSeries.coeff n (PowerSeries.log A) := by
  rw [PowerSeries.coeff_subst
    (formalLogOnePlusProductArgument_hasSubst A) (PowerSeries.log A)
    (Finsupp.single (0 : Fin 2) n)]
  rw [finsum_eq_single _ n]
  · rw [formalLogOnePlusProductArgument_pow_coeff_single_left]
    simp [formalLogOnePlusLeftVariable_pow_coeff]
  · intro d hd
    rw [formalLogOnePlusProductArgument_pow_coeff_single_left]
    rw [formalLogOnePlusLeftVariable_pow_coeff]
    have hsingle :
        Finsupp.single (0 : Fin 2) n ≠ Finsupp.single (0 : Fin 2) d := by
      intro h
      apply hd
      have hcoord := congrArg (fun e : Fin 2 →₀ ℕ => e (0 : Fin 2)) h
      simpa using hcoord.symm
    simp [hsingle]

/--
Establishes the identity `MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n)
(PowerSeries.subst (formalLogOnePlusProductArgument A) (PowerSeries.log A)) = PowerSeries.coeff n
(PowerSeries.log A)`.
-/
theorem formalLogOnePlusProductArgument_logSubst_coeff_single_right
    (A : Type*) [CommRing A] [Algebra ℚ A] (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n)
        (PowerSeries.subst (formalLogOnePlusProductArgument A) (PowerSeries.log A)) =
      PowerSeries.coeff n (PowerSeries.log A) := by
  rw [PowerSeries.coeff_subst
    (formalLogOnePlusProductArgument_hasSubst A) (PowerSeries.log A)
    (Finsupp.single (1 : Fin 2) n)]
  rw [finsum_eq_single _ n]
  · rw [formalLogOnePlusProductArgument_pow_coeff_single_right]
    simp [formalLogOnePlusRightVariable_pow_coeff]
  · intro d hd
    rw [formalLogOnePlusProductArgument_pow_coeff_single_right]
    rw [formalLogOnePlusRightVariable_pow_coeff]
    have hsingle :
        Finsupp.single (1 : Fin 2) n ≠ Finsupp.single (1 : Fin 2) d := by
      intro h
      apply hd
      have hcoord := congrArg (fun e : Fin 2 →₀ ℕ => e (1 : Fin 2)) h
      simpa using hcoord.symm
    simp [hsingle]

/-- The formal logarithm `log(1 + X)`, viewed as a two-variable series in the
left variable. -/
noncomputable def formalLogOnePlusLeftVariableLogSubst
    (A : Type*) [CommRing A] [Algebra ℚ A] : MvPowerSeries (Fin 2) A :=
  PowerSeries.subst
    (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) A)
    (PowerSeries.log A)

/-- The formal logarithm `log(1 + Y)`, viewed as a two-variable series in the
right variable. -/
noncomputable def formalLogOnePlusRightVariableLogSubst
    (A : Type*) [CommRing A] [Algebra ℚ A] : MvPowerSeries (Fin 2) A :=
  PowerSeries.subst
    (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) A)
    (PowerSeries.log A)

/-- The formal right-hand side `log(1 + X) + log(1 + Y)` of the logarithm
product formula. -/
noncomputable def formalLogOnePlusProductRightSide
    (A : Type*) [CommRing A] [Algebra ℚ A] : MvPowerSeries (Fin 2) A :=
  formalLogOnePlusLeftVariableLogSubst A +
    formalLogOnePlusRightVariableLogSubst A

/--
Establishes the identity `MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) n)
(formalLogOnePlusLeftVariableLogSubst A) = PowerSeries.coeff n (PowerSeries.log A)`.
-/
theorem formalLogOnePlusLeftVariableLogSubst_coeff_single
    (A : Type*) [CommRing A] [Algebra ℚ A] (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) n)
        (formalLogOnePlusLeftVariableLogSubst A) =
      PowerSeries.coeff n (PowerSeries.log A) := by
  simp [formalLogOnePlusLeftVariableLogSubst, PowerSeries.coeff_subst_single]

/--
Establishes the identity `MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n)
(formalLogOnePlusRightVariableLogSubst A) = PowerSeries.coeff n (PowerSeries.log A)`.
-/
theorem formalLogOnePlusRightVariableLogSubst_coeff_single
    (A : Type*) [CommRing A] [Algebra ℚ A] (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n)
        (formalLogOnePlusRightVariableLogSubst A) =
      PowerSeries.coeff n (PowerSeries.log A) := by
  simp [formalLogOnePlusRightVariableLogSubst, PowerSeries.coeff_subst_single]

/--
Establishes the identity `MvPowerSeries.coeff e (formalLogOnePlusLeftVariableLogSubst A) = 0`.
-/
theorem formalLogOnePlusLeftVariableLogSubst_coeff_of_ne_axis
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ)
    (he : ∀ d : ℕ, e ≠ Finsupp.single (0 : Fin 2) d) :
    MvPowerSeries.coeff e (formalLogOnePlusLeftVariableLogSubst A) = 0 := by
  simp [formalLogOnePlusLeftVariableLogSubst, PowerSeries.coeff_subst_single, he]

/--
Establishes the identity `MvPowerSeries.coeff e (formalLogOnePlusRightVariableLogSubst A) = 0`.
-/
theorem formalLogOnePlusRightVariableLogSubst_coeff_of_ne_axis
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ)
    (he : ∀ d : ℕ, e ≠ Finsupp.single (1 : Fin 2) d) :
    MvPowerSeries.coeff e (formalLogOnePlusRightVariableLogSubst A) = 0 := by
  simp [formalLogOnePlusRightVariableLogSubst, PowerSeries.coeff_subst_single, he]

/--
Establishes the identity `MvPowerSeries.coeff e (formalLogOnePlusProductRightSide A) =
MvPowerSeries.coeff e (formalLogOnePlusLeftVariableLogSubst A) + MvPowerSeries.coeff e
(formalLogOnePlusRightVariableLogSubst A)`.
-/
theorem formalLogOnePlusProductRightSide_coeff
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (formalLogOnePlusProductRightSide A) =
      MvPowerSeries.coeff e (formalLogOnePlusLeftVariableLogSubst A) +
        MvPowerSeries.coeff e (formalLogOnePlusRightVariableLogSubst A) := by
  simp [formalLogOnePlusProductRightSide]

/-- The logarithm substituted at the product argument has zero constant
coefficient. -/
theorem formalLogOnePlusProductArgument_logSubst_constantCoeff
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    MvPowerSeries.constantCoeff
        (PowerSeries.subst (formalLogOnePlusProductArgument A) (PowerSeries.log A)) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero
    (formalLogOnePlusProductArgument_constantCoeff A)
    (PowerSeries.log A) PowerSeries.constantCoeff_log

/--
Establishes the identity `MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) n)
(formalLogOnePlusProductRightSide A) = PowerSeries.coeff n (PowerSeries.log A)`.
-/
theorem formalLogOnePlusProductRightSide_coeff_single_left
    (A : Type*) [CommRing A] [Algebra ℚ A] (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) n)
        (formalLogOnePlusProductRightSide A) =
      PowerSeries.coeff n (PowerSeries.log A) := by
  rw [formalLogOnePlusProductRightSide_coeff,
    formalLogOnePlusLeftVariableLogSubst_coeff_single]
  have hright :
      MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) n)
          (formalLogOnePlusRightVariableLogSubst A) = 0 := by
    by_cases hn : n = 0
    · subst n
      simpa [Finsupp.single_zero] using
        formalLogOnePlusRightVariableLogSubst_coeff_single A 0
    · exact
        formalLogOnePlusRightVariableLogSubst_coeff_of_ne_axis A
          (Finsupp.single (0 : Fin 2) n)
          (fun d h => by
            apply hn
            have hcoord :=
              congrArg (fun e : Fin 2 →₀ ℕ => e (0 : Fin 2)) h
            simpa using hcoord)
  simp [hright]

/--
Establishes the identity `MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n)
(formalLogOnePlusProductRightSide A) = PowerSeries.coeff n (PowerSeries.log A)`.
-/
theorem formalLogOnePlusProductRightSide_coeff_single_right
    (A : Type*) [CommRing A] [Algebra ℚ A] (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n)
        (formalLogOnePlusProductRightSide A) =
      PowerSeries.coeff n (PowerSeries.log A) := by
  rw [formalLogOnePlusProductRightSide_coeff,
    formalLogOnePlusRightVariableLogSubst_coeff_single]
  have hleft :
      MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n)
          (formalLogOnePlusLeftVariableLogSubst A) = 0 := by
    by_cases hn : n = 0
    · subst n
      simpa [Finsupp.single_zero] using
        formalLogOnePlusLeftVariableLogSubst_coeff_single A 0
    · exact
        formalLogOnePlusLeftVariableLogSubst_coeff_of_ne_axis A
          (Finsupp.single (1 : Fin 2) n)
          (fun d h => by
            apply hn
            have hcoord :=
              congrArg (fun e : Fin 2 →₀ ℕ => e (1 : Fin 2)) h
            simpa using hcoord)
  abel_nf
  simp [hleft]

/-- Establishes the identity `MvPowerSeries.coeff e (formalLogOnePlusProductRightSide A) = 0`. -/
theorem formalLogOnePlusProductRightSide_coeff_of_ne_axes
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ)
    (heLeft : ∀ d : ℕ, e ≠ Finsupp.single (0 : Fin 2) d)
    (heRight : ∀ d : ℕ, e ≠ Finsupp.single (1 : Fin 2) d) :
    MvPowerSeries.coeff e (formalLogOnePlusProductRightSide A) = 0 := by
  rw [formalLogOnePlusProductRightSide_coeff]
  simp [formalLogOnePlusLeftVariableLogSubst_coeff_of_ne_axis A e heLeft,
    formalLogOnePlusRightVariableLogSubst_coeff_of_ne_axis A e heRight]

/--
Establishes the identity `MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) n)
(PowerSeries.subst (formalLogOnePlusProductArgument A) (PowerSeries.log A)) = MvPowerSeries.coeff
(Finsupp.single (0 : Fin 2) n) (formalLogOnePlusProductRightSide A)`.
-/
theorem formalLogOnePlusProductFormula_coeff_single_left
    (A : Type*) [CommRing A] [Algebra ℚ A] (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) n)
        (PowerSeries.subst (formalLogOnePlusProductArgument A) (PowerSeries.log A)) =
      MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) n)
        (formalLogOnePlusProductRightSide A) := by
  rw [formalLogOnePlusProductArgument_logSubst_coeff_single_left,
    formalLogOnePlusProductRightSide_coeff_single_left]

/--
Establishes the identity `MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n)
(PowerSeries.subst (formalLogOnePlusProductArgument A) (PowerSeries.log A)) = MvPowerSeries.coeff
(Finsupp.single (1 : Fin 2) n) (formalLogOnePlusProductRightSide A)`.
-/
theorem formalLogOnePlusProductFormula_coeff_single_right
    (A : Type*) [CommRing A] [Algebra ℚ A] (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n)
        (PowerSeries.subst (formalLogOnePlusProductArgument A) (PowerSeries.log A)) =
      MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) n)
        (formalLogOnePlusProductRightSide A) := by
  rw [formalLogOnePlusProductArgument_logSubst_coeff_single_right,
    formalLogOnePlusProductRightSide_coeff_single_right]

/-- Establishes the identity `e = Finsupp.single (0 : Fin 2) (e (0 : Fin 2))`. -/
theorem finsupp_fin_two_eq_single_left_of_right_eq_zero
    (e : Fin 2 →₀ ℕ) (he : e (1 : Fin 2) = 0) :
    e = Finsupp.single (0 : Fin 2) (e (0 : Fin 2)) := by
  ext i
  fin_cases i <;> simp [he]

/-- Establishes the identity `e = Finsupp.single (1 : Fin 2) (e (1 : Fin 2))`. -/
theorem finsupp_fin_two_eq_single_right_of_left_eq_zero
    (e : Fin 2 →₀ ℕ) (he : e (0 : Fin 2) = 0) :
    e = Finsupp.single (1 : Fin 2) (e (1 : Fin 2)) := by
  ext i
  fin_cases i <;> simp [he]

/-- Establishes the strict bound `0 < e (0 : Fin 2)`. -/
theorem finsupp_fin_two_left_pos_of_not_right_axis
    (e : Fin 2 →₀ ℕ)
    (he : ∀ d : ℕ, e ≠ Finsupp.single (1 : Fin 2) d) :
    0 < e (0 : Fin 2) := by
  apply Nat.pos_of_ne_zero
  intro hzero
  exact he (e (1 : Fin 2))
    (finsupp_fin_two_eq_single_right_of_left_eq_zero e hzero)

/-- Establishes the strict bound `0 < e (1 : Fin 2)`. -/
theorem finsupp_fin_two_right_pos_of_not_left_axis
    (e : Fin 2 →₀ ℕ)
    (he : ∀ d : ℕ, e ≠ Finsupp.single (0 : Fin 2) d) :
    0 < e (1 : Fin 2) := by
  apply Nat.pos_of_ne_zero
  intro hzero
  exact he (e (0 : Fin 2))
    (finsupp_fin_two_eq_single_left_of_right_eq_zero e hzero)

/-- Establishes the identity `Finsupp.degree e = e (0 : Fin 2) + e (1 : Fin 2)`. -/
theorem finsupp_fin_two_degree_eq (e : Fin 2 →₀ ℕ) :
    Finsupp.degree e = e (0 : Fin 2) + e (1 : Fin 2) := by
  classical
  have huniv :
      (Finset.univ : Finset (Fin 2)) =
        {0, 1} := by
    ext i
    fin_cases i <;> simp
  rw [Finsupp.degree_eq_sum, huniv]
  simp

/-- Establishes the inequality `e ≠ Finsupp.single (0 : Fin 2) d`. -/
theorem finsupp_fin_two_ne_single_left_of_right_pos
    (e : Fin 2 →₀ ℕ) (hpos : 0 < e (1 : Fin 2)) (d : ℕ) :
    e ≠ Finsupp.single (0 : Fin 2) d := by
  intro h
  have hcoord : e (1 : Fin 2) = 0 := by
    simp [h]
  exact (Nat.ne_of_gt hpos) hcoord

/-- Establishes the inequality `e ≠ Finsupp.single (1 : Fin 2) d`. -/
theorem finsupp_fin_two_ne_single_right_of_left_pos
    (e : Fin 2 →₀ ℕ) (hpos : 0 < e (0 : Fin 2)) (d : ℕ) :
    e ≠ Finsupp.single (1 : Fin 2) d := by
  intro h
  have hcoord : e (0 : Fin 2) = 0 := by
    simp [h]
  exact (Nat.ne_of_gt hpos) hcoord

/-- Establishes the identity `MvPowerSeries.coeff e (formalLogOnePlusProductRightSide A) = 0`. -/
theorem formalLogOnePlusProductRightSide_coeff_of_pos_coords
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ)
    (hleft : 0 < e (0 : Fin 2)) (hright : 0 < e (1 : Fin 2)) :
    MvPowerSeries.coeff e (formalLogOnePlusProductRightSide A) = 0 :=
  formalLogOnePlusProductRightSide_coeff_of_ne_axes A e
    (finsupp_fin_two_ne_single_left_of_right_pos e hright)
    (finsupp_fin_two_ne_single_right_of_left_pos e hleft)

/-- On the left coordinate axis, the substituted logarithm and the proposed
right-hand side have the same coefficient. -/
theorem formalLogOnePlusProductFormula_coeff_of_right_coord_zero
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ)
    (he : e (1 : Fin 2) = 0) :
    MvPowerSeries.coeff e
        (PowerSeries.subst (formalLogOnePlusProductArgument A) (PowerSeries.log A)) =
      MvPowerSeries.coeff e (formalLogOnePlusProductRightSide A) := by
  rw [finsupp_fin_two_eq_single_left_of_right_eq_zero e he]
  exact formalLogOnePlusProductFormula_coeff_single_left A (e (0 : Fin 2))

/-- On the right coordinate axis, the substituted logarithm and the proposed
right-hand side have the same coefficient. -/
theorem formalLogOnePlusProductFormula_coeff_of_left_coord_zero
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ)
    (he : e (0 : Fin 2) = 0) :
    MvPowerSeries.coeff e
        (PowerSeries.subst (formalLogOnePlusProductArgument A) (PowerSeries.log A)) =
      MvPowerSeries.coeff e (formalLogOnePlusProductRightSide A) := by
  rw [finsupp_fin_two_eq_single_right_of_left_eq_zero e he]
  exact formalLogOnePlusProductFormula_coeff_single_right A (e (1 : Fin 2))

/-- Difference between the two formal sides of the logarithm product formula.
The remaining proof of the formal identity is exactly the vanishing of this
series on mixed monomials. -/
noncomputable def formalLogOnePlusProductFormulaDefect
    (A : Type*) [CommRing A] [Algebra ℚ A] : MvPowerSeries (Fin 2) A :=
  PowerSeries.subst (formalLogOnePlusProductArgument A) (PowerSeries.log A) -
      formalLogOnePlusProductRightSide A

/--
Establishes the identity `MvPowerSeries.coeff e (formalLogOnePlusProductFormulaDefect A) = 0`.
-/
theorem formalLogOnePlusProductFormulaDefect_coeff_of_right_coord_zero
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ)
    (he : e (1 : Fin 2) = 0) :
    MvPowerSeries.coeff e
        (formalLogOnePlusProductFormulaDefect A) = 0 := by
  simp [formalLogOnePlusProductFormulaDefect,
    formalLogOnePlusProductFormula_coeff_of_right_coord_zero A e he]

/--
Establishes the identity `MvPowerSeries.coeff e (formalLogOnePlusProductFormulaDefect A) = 0`.
-/
theorem formalLogOnePlusProductFormulaDefect_coeff_of_left_coord_zero
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ)
    (he : e (0 : Fin 2) = 0) :
    MvPowerSeries.coeff e
        (formalLogOnePlusProductFormulaDefect A) = 0 := by
  simp [formalLogOnePlusProductFormulaDefect,
    formalLogOnePlusProductFormula_coeff_of_left_coord_zero A e he]

/--
Establishes the identity `MvPowerSeries.coeff e (formalLogOnePlusProductFormulaDefect A) = ∑ q ∈
(Finset.range (Finsupp.degree e + 1)).filter (fun q : ℕ => e (0 : Fin 2) ≤ q ∧ e (1 : Fin 2) ≤ q),
PowerSeries.coeff q (PowerSeries.log A) • MvPowerSeries.coeff e
((formalLogOnePlusProductArgument A) ^ q)`.
-/
theorem formalLogOnePlusProductFormulaDefect_coeff_of_pos_coords_eq_sum_range_degree_succ_filter_coord_le
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ)
    (hleft : 0 < e (0 : Fin 2)) (hright : 0 < e (1 : Fin 2)) :
    MvPowerSeries.coeff e
        (formalLogOnePlusProductFormulaDefect A) =
      ∑ q ∈
        (Finset.range (Finsupp.degree e + 1)).filter
          (fun q : ℕ => e (0 : Fin 2) ≤ q ∧ e (1 : Fin 2) ≤ q),
        PowerSeries.coeff q (PowerSeries.log A) •
          MvPowerSeries.coeff e
            ((formalLogOnePlusProductArgument A) ^ q) := by
  simp [formalLogOnePlusProductFormulaDefect,
    formalLogOnePlusProductRightSide_coeff_of_pos_coords A e hleft hright,
    formalLogOnePlusProductArgument_logSubst_coeff_eq_sum_range_degree_succ_filter_coord_le]

/--
Establishes the identity `MvPowerSeries.coeff e (formalLogOnePlusProductFormulaDefect A) = ∑ q ∈
(Finset.range (e (0 : Fin 2) + e (1 : Fin 2) + 1)).filter (fun q : ℕ => e (0 : Fin 2) ≤ q ∧ e (1 :
Fin 2) ≤ q), PowerSeries.coeff q (PowerSeries.log A) • MvPowerSeries.coeff e
((formalLogOnePlusProductArgument A) ^ q)`.
-/
theorem formalProductDefect_coeff_pos_eq_filtered_sum
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ)
    (hleft : 0 < e (0 : Fin 2)) (hright : 0 < e (1 : Fin 2)) :
    MvPowerSeries.coeff e
        (formalLogOnePlusProductFormulaDefect A) =
      ∑ q ∈
        (Finset.range (e (0 : Fin 2) + e (1 : Fin 2) + 1)).filter
          (fun q : ℕ => e (0 : Fin 2) ≤ q ∧ e (1 : Fin 2) ≤ q),
        PowerSeries.coeff q (PowerSeries.log A) •
          MvPowerSeries.coeff e
            ((formalLogOnePlusProductArgument A) ^ q) := by
  rw [formalLogOnePlusProductFormulaDefect_coeff_of_pos_coords_eq_sum_range_degree_succ_filter_coord_le
    A e hleft hright]
  rw [finsupp_fin_two_degree_eq]

/--
Establishes the identity `MvPowerSeries.coeff e (formalLogOnePlusProductFormulaDefect A) = ∑ q ∈
(Finset.range (e (0 : Fin 2) + e (1 : Fin 2) + 1)).filter (fun q : ℕ => e (0 : Fin 2) ≤ q ∧ e (1 :
Fin 2) ≤ q), PowerSeries.coeff q (PowerSeries.log A) • (∑ l ∈ Finset.finsuppAntidiag
(Finset.range q) e, if ∀ i ∈ Finset.range q, formalLogOnePlusProductArgumentBasicFactor (l i) then
(1 : A) else 0)`.
-/
theorem formalLogOnePlusProductFormulaDefect_coeff_of_pos_coords_eq_sum_basicFactor
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ)
    (hleft : 0 < e (0 : Fin 2)) (hright : 0 < e (1 : Fin 2)) :
    MvPowerSeries.coeff e
        (formalLogOnePlusProductFormulaDefect A) =
      ∑ q ∈
        (Finset.range (e (0 : Fin 2) + e (1 : Fin 2) + 1)).filter
          (fun q : ℕ => e (0 : Fin 2) ≤ q ∧ e (1 : Fin 2) ≤ q),
        PowerSeries.coeff q (PowerSeries.log A) •
          (∑ l ∈ Finset.finsuppAntidiag (Finset.range q) e,
            if ∀ i ∈ Finset.range q,
                formalLogOnePlusProductArgumentBasicFactor (l i)
            then (1 : A) else 0) := by
  rw [formalProductDefect_coeff_pos_eq_filtered_sum
    A e hleft hright]
  apply Finset.sum_congr rfl
  intro q _hq
  rw [formalLogOnePlusProductArgument_pow_coeff_eq_sum_basicFactor]

/--
Establishes the identity `MvPowerSeries.coeff e (formalLogOnePlusProductFormulaDefect A) = ∑ q ∈
(Finset.range (e (0 : Fin 2) + e (1 : Fin 2) + 1)).filter (fun q : ℕ => e (0 : Fin 2) ≤ q ∧ e (1 :
Fin 2) ≤ q), PowerSeries.coeff q (PowerSeries.log A) •
((formalLogOnePlusProductArgumentBasicFactorChoices q e).card : A)`.
-/
theorem formalLogOnePlusProductFormulaDefect_coeff_of_pos_coords_eq_sum_card_choices
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ)
    (hleft : 0 < e (0 : Fin 2)) (hright : 0 < e (1 : Fin 2)) :
    MvPowerSeries.coeff e
        (formalLogOnePlusProductFormulaDefect A) =
      ∑ q ∈
        (Finset.range (e (0 : Fin 2) + e (1 : Fin 2) + 1)).filter
          (fun q : ℕ => e (0 : Fin 2) ≤ q ∧ e (1 : Fin 2) ≤ q),
        PowerSeries.coeff q (PowerSeries.log A) •
          ((formalLogOnePlusProductArgumentBasicFactorChoices q e).card : A) := by
  rw [formalLogOnePlusProductFormulaDefect_coeff_of_pos_coords_eq_sum_basicFactor
    A e hleft hright]
  apply Finset.sum_congr rfl
  intro q _hq
  rw [formalLogOnePlusProductArgument_basicFactor_sum_eq_card_choices]

/--
Establishes the identity `(∑ q ∈ (Finset.range (a + b + 1)).filter (fun q => a ≤ q ∧ b ≤ q), F q)
= ∑ m ∈ (Finset.range (a + 1)).filter (fun m => m ≤ b), F (a + b - m)`.
-/
theorem sum_range_add_filter_coord_le_reindex
    {R : Type*} [AddCommMonoid R] (a b : ℕ) (F : ℕ → R) :
    (∑ q ∈ (Finset.range (a + b + 1)).filter (fun q => a ≤ q ∧ b ≤ q),
      F q) =
      ∑ m ∈ (Finset.range (a + 1)).filter (fun m => m ≤ b),
        F (a + b - m) := by
  refine Finset.sum_bij'
    (fun q _ => a + b - q)
    (fun m _ => a + b - m)
    ?_ ?_ ?_ ?_ ?_
  · intro q hq
    rw [Finset.mem_filter] at hq ⊢
    constructor
    · rw [Finset.mem_range]
      omega
    · omega
  · intro m hm
    rw [Finset.mem_filter] at hm ⊢
    have hmle_a : m ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm.1)
    have hmle_b : m ≤ b := hm.2
    have hleftRewrite : a + b - m = a + (b - m) := by
      exact Nat.add_sub_assoc hmle_b a
    have hrightRewrite : a + b - m = b + (a - m) := by
      rw [Nat.add_comm a b]
      exact Nat.add_sub_assoc hmle_a b
    constructor
    · rw [Finset.mem_range]
      omega
    · constructor
      · rw [hleftRewrite]
        omega
      · rw [hrightRewrite]
        omega
  · intro q hq
    rw [Finset.mem_filter] at hq
    have hqle : q ≤ a + b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq.1)
    exact Nat.sub_sub_self hqle
  · intro m hm
    rw [Finset.mem_filter] at hm
    have hmle_a : m ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm.1)
    have hmle : m ≤ a + b := by omega
    exact Nat.sub_sub_self hmle
  · intro q hq
    rw [Finset.mem_filter] at hq
    have hqle : q ≤ a + b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq.1)
    simp [Nat.sub_sub_self hqle]

/--
Establishes the identity `(∑ m ∈ Finset.range (a + 1), ((-1 : ℚ) ^ m) * (Nat.choose a m : ℚ) *
(Nat.choose (a + b - 1 - m) (a - 1) : ℚ)) = 0`.
-/
theorem formalLogOnePlusProduct_alternating_sum_choose_eq_zero
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (∑ m ∈ Finset.range (a + 1),
      ((-1 : ℚ) ^ m) * (Nat.choose a m : ℚ) *
        (Nat.choose (a + b - 1 - m) (a - 1) : ℚ)) = 0 := by
  let P : ℚ[X] := X + 1
  have hcoeff :
      (∑ m ∈ Finset.range (a + 1),
        ((-1 : ℚ) ^ m) * (Nat.choose a m : ℚ) *
          (Nat.choose (a + b - 1 - m) (a - 1) : ℚ)) =
        Polynomial.coeff
          (∑ m ∈ Finset.range (a + 1),
            C (((-1 : ℚ) ^ m) * (Nat.choose a m : ℚ)) *
              P ^ (a + b - 1 - m)) (a - 1) := by
    have hsumcoeff :
        Polynomial.coeff
          (∑ m ∈ Finset.range (a + 1),
            C (((-1 : ℚ) ^ m) * (Nat.choose a m : ℚ)) *
              P ^ (a + b - 1 - m)) (a - 1) =
          ∑ m ∈ Finset.range (a + 1),
            Polynomial.coeff
              (C (((-1 : ℚ) ^ m) * (Nat.choose a m : ℚ)) *
                P ^ (a + b - 1 - m)) (a - 1) := by
      simp
    rw [hsumcoeff]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Polynomial.coeff_C_mul]
    have hpowcoeff :
        Polynomial.coeff (P ^ (a + b - 1 - m)) (a - 1) =
          (Nat.choose (a + b - 1 - m) (a - 1) : ℚ) := by
      dsimp [P]
      rw [Polynomial.coeff_X_add_one_pow]
    rw [hpowcoeff]
  rw [hcoeff]
  have hpoly :
      (∑ m ∈ Finset.range (a + 1),
        C (((-1 : ℚ) ^ m) * (Nat.choose a m : ℚ)) *
          P ^ (a + b - 1 - m)) =
        X ^ a * P ^ (b - 1) := by
    calc
      (∑ m ∈ Finset.range (a + 1),
        C (((-1 : ℚ) ^ m) * (Nat.choose a m : ℚ)) *
          P ^ (a + b - 1 - m))
          =
        ∑ k ∈ Finset.range (a + 1),
          C (((-1 : ℚ) ^ (a - k)) * (Nat.choose a (a - k) : ℚ)) *
            P ^ (a + b - 1 - (a - k)) := by
            simpa using
              (Finset.sum_range_reflect
                (fun m =>
                  C (((-1 : ℚ) ^ m) * (Nat.choose a m : ℚ)) *
                    P ^ (a + b - 1 - m)) (a + 1)).symm
      _ =
        ∑ k ∈ Finset.range (a + 1),
          C (((-1 : ℚ) ^ (k + a)) * (Nat.choose a k : ℚ)) *
            P ^ (k + (b - 1)) := by
            apply Finset.sum_congr rfl
            intro k hk
            have hk_le : k ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
            have hchoose : Nat.choose a (a - k) = Nat.choose a k :=
              Nat.choose_symm hk_le
            have hpow : ((-1 : ℚ) ^ (a - k)) = (-1 : ℚ) ^ (k + a) := by
              have hadd : k + a = a - k + 2 * k := by omega
              rw [hadd, pow_add, pow_mul]
              simp [pow_two]
            have hexp : a + b - 1 - (a - k) = k + (b - 1) := by omega
            rw [hchoose, hpow, hexp]
      _ =
        (∑ k ∈ Finset.range (a + 1),
          C (((-1 : ℚ) ^ (k + a)) * (Nat.choose a k : ℚ)) *
            P ^ k) * P ^ (b - 1) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro k hk
            rw [pow_add]
            ring
      _ = (P - 1) ^ a * P ^ (b - 1) := by
            rw [sub_pow]
            simp [P, mul_assoc, mul_comm]
      _ = X ^ a * P ^ (b - 1) := by
            simp [P]
  rw [hpoly]
  have hdiv : X ^ a ∣ (X ^ a * P ^ (b - 1) : ℚ[X]) := ⟨P ^ (b - 1), rfl⟩
  exact
    (Polynomial.X_pow_dvd_iff.mp hdiv (a - 1)
      (Nat.sub_lt ha Nat.one_pos))

/--
Establishes the identity `(∑ m ∈ (Finset.range (a + 1)).filter (fun m => m ≤ b), ((-1 : ℚ) ^ m) *
(Nat.choose a m : ℚ) * (Nat.choose (a + b - 1 - m) (a - 1) : ℚ)) = 0`.
-/
theorem formalLogOnePlusProduct_alternating_sum_choose_filter_eq_zero
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (∑ m ∈ (Finset.range (a + 1)).filter (fun m => m ≤ b),
      ((-1 : ℚ) ^ m) * (Nat.choose a m : ℚ) *
        (Nat.choose (a + b - 1 - m) (a - 1) : ℚ)) = 0 := by
  rw [← formalLogOnePlusProduct_alternating_sum_choose_eq_zero a b ha hb]
  exact
    (Finset.sum_subset (Finset.filter_subset _ _) (fun m hm hnot => by
      have hle_a : m ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      have hlt_b : b < m := Nat.lt_of_not_ge (by
        intro hmb
        exact hnot (Finset.mem_filter.mpr ⟨hm, hmb⟩))
      have hchooseZero :
          Nat.choose (a + b - 1 - m) (a - 1) = 0 := by
        apply Nat.choose_eq_zero_of_lt
        omega
      change
        ((-1 : ℚ) ^ m) * (Nat.choose a m : ℚ) *
          (Nat.choose (a + b - 1 - m) (a - 1) : ℚ) = 0
      rw [hchooseZero]
      simp))

/--
After the substitution `q = a + b - m`, the mixed logarithmic coefficient rewrites as the
corresponding alternating binomial term.
-/
theorem formalLogOnePlusProduct_rational_mixed_reindexed_term
    (a b m : ℕ) (ha : 0 < a) (hmle_a : m ≤ a) (hmle_b : m ≤ b) :
    let q := a + b - m
    (a : ℚ) *
        (((-1 : ℚ) ^ (q - 1) / (q : ℚ)) *
          ((Nat.choose q m * Nat.choose (q - m) (q - b) : ℕ) : ℚ)) =
      ((-1 : ℚ) ^ (a + b - 1)) *
        (((-1 : ℚ) ^ m) * (Nat.choose a m : ℚ) *
          (Nat.choose (a + b - 1 - m) (a - 1) : ℚ)) := by
  intro q
  subst q
  have hqpos : 0 < a + b - m := by omega
  have hq_ne : ((a + b - m : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hqpos)
  have hq_sub_b : a + b - m - b = a - m := by omega
  have hq_pred : a + b - m - 1 = a + b - 1 - m := by omega
  have hprodNat :
      Nat.choose (a + b - m) m *
          Nat.choose (a + b - m - m) (a + b - m - b) =
        Nat.choose (a + b - m) a * Nat.choose a m := by
    rw [hq_sub_b]
    exact
      (Nat.choose_mul (n := a + b - m) (k := a) (s := m) hmle_a).symm
  have hsuccNat :
      (a + b - m) * Nat.choose (a + b - m - 1) (a - 1) =
        Nat.choose (a + b - m) a * a := by
    calc
      (a + b - m) * Nat.choose (a + b - m - 1) (a - 1)
          =
        ((a + b - m - 1) + 1) *
          Nat.choose (a + b - m - 1) (a - 1) := by
            rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hqpos)]
      _ =
        Nat.choose ((a + b - m - 1) + 1) ((a - 1) + 1) *
          ((a - 1) + 1) := by
            exact Nat.add_one_mul_choose_eq (a + b - m - 1) (a - 1)
      _ = Nat.choose (a + b - m) a * a := by
            rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hqpos),
              Nat.sub_add_cancel (Nat.succ_le_of_lt ha)]
  have hsuccQ :
      ((a + b - m : ℕ) : ℚ) *
          (Nat.choose (a + b - m - 1) (a - 1) : ℚ) =
        (Nat.choose (a + b - m) a : ℚ) * (a : ℚ) := by
    exact_mod_cast hsuccNat
  have hsuccQ' :
      ((a + b - m : ℕ) : ℚ) *
          (Nat.choose (a + b - 1 - m) (a - 1) : ℚ) =
        (Nat.choose (a + b - m) a : ℚ) * (a : ℚ) := by
    simpa [hq_pred] using hsuccQ
  have hsign :
      (-1 : ℚ) ^ (a + b - m - 1) =
        (-1 : ℚ) ^ (a + b - 1) * (-1 : ℚ) ^ m := by
    calc
      (-1 : ℚ) ^ (a + b - m - 1)
          = (-1 : ℚ) ^ ((a + b - 1) + m) := by
            have hadd : (a + b - 1) + m = a + b - m - 1 + 2 * m := by
              omega
            rw [hadd, pow_add, pow_mul]
            simp [pow_two]
      _ = (-1 : ℚ) ^ (a + b - 1) * (-1 : ℚ) ^ m := by
            rw [pow_add]
  rw [hprodNat, hsign]
  field_simp [hq_ne]
  rw [Nat.cast_mul]
  calc
    (a : ℚ) *
        ((Nat.choose (a + b - m) a : ℚ) * (Nat.choose a m : ℚ))
        =
      ((Nat.choose (a + b - m) a : ℚ) * (a : ℚ)) *
        (Nat.choose a m : ℚ) := by
          ring
    _ =
      (((a + b - m : ℕ) : ℚ) *
          (Nat.choose (a + b - 1 - m) (a - 1) : ℚ)) *
        (Nat.choose a m : ℚ) := by
          rw [← hsuccQ']
    _ =
      ((a + b - m : ℕ) : ℚ) * (Nat.choose a m : ℚ) *
        (Nat.choose (a + b - 1 - m) (a - 1) : ℚ) := by
          ring

/--
Establishes the identity `(∑ q ∈ (Finset.range (a + b + 1)).filter (fun q : ℕ => a ≤ q ∧ b ≤ q),
(((-1 : ℚ) ^ (q - 1) / (q : ℚ)) * ((Nat.choose q (a + b - q) * Nat.choose (q - (a + b - q)) (q -
b) : ℕ) : ℚ))) = 0`.
-/
theorem formalLogOnePlusProduct_rational_mixed_sum_eq_zero
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (∑ q ∈
      (Finset.range (a + b + 1)).filter (fun q : ℕ => a ≤ q ∧ b ≤ q),
      (((-1 : ℚ) ^ (q - 1) / (q : ℚ)) *
        ((Nat.choose q (a + b - q) *
          Nat.choose (q - (a + b - q)) (q - b) : ℕ) : ℚ))) = 0 := by
  let F : ℕ → ℚ := fun q =>
    (((-1 : ℚ) ^ (q - 1) / (q : ℚ)) *
      ((Nat.choose q (a + b - q) *
        Nat.choose (q - (a + b - q)) (q - b) : ℕ) : ℚ))
  change
    (∑ q ∈
      (Finset.range (a + b + 1)).filter (fun q : ℕ => a ≤ q ∧ b ≤ q),
      F q) = 0
  rw [sum_range_add_filter_coord_le_reindex a b F]
  have haQ : (a : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt ha)
  apply (mul_eq_zero.mp ?_).resolve_left haQ
  calc
    (a : ℚ) *
        (∑ m ∈ (Finset.range (a + 1)).filter (fun m => m ≤ b),
          F (a + b - m))
        =
      ∑ m ∈ (Finset.range (a + 1)).filter (fun m => m ≤ b),
        (a : ℚ) * F (a + b - m) := by
          rw [Finset.mul_sum]
    _ =
      ∑ m ∈ (Finset.range (a + 1)).filter (fun m => m ≤ b),
        ((-1 : ℚ) ^ (a + b - 1)) *
          (((-1 : ℚ) ^ m) * (Nat.choose a m : ℚ) *
            (Nat.choose (a + b - 1 - m) (a - 1) : ℚ)) := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [Finset.mem_filter] at hm
          have hmle_a : m ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm.1)
          have hmle_b : m ≤ b := hm.2
          have hmle_sum : m ≤ a + b := by omega
          have hsub : a + b - (a + b - m) = m := Nat.sub_sub_self hmle_sum
          change
            (a : ℚ) *
                (((-1 : ℚ) ^ (a + b - m - 1) /
                    ((a + b - m : ℕ) : ℚ)) *
                  ((Nat.choose (a + b - m) (a + b - (a + b - m)) *
                    Nat.choose
                      (a + b - m - (a + b - (a + b - m)))
                      (a + b - m - b) : ℕ) : ℚ)) =
              ((-1 : ℚ) ^ (a + b - 1)) *
                (((-1 : ℚ) ^ m) * (Nat.choose a m : ℚ) *
                  (Nat.choose (a + b - 1 - m) (a - 1) : ℚ))
          rw [hsub]
          exact formalLogOnePlusProduct_rational_mixed_reindexed_term
            a b m ha hmle_a hmle_b
    _ =
      ((-1 : ℚ) ^ (a + b - 1)) *
        (∑ m ∈ (Finset.range (a + 1)).filter (fun m => m ≤ b),
          ((-1 : ℚ) ^ m) * (Nat.choose a m : ℚ) *
            (Nat.choose (a + b - 1 - m) (a - 1) : ℚ)) := by
          rw [Finset.mul_sum]
    _ = 0 := by
          rw [formalLogOnePlusProduct_alternating_sum_choose_filter_eq_zero
            a b ha hb]
          simp

/--
Establishes the identity `MvPowerSeries.coeff e (formalLogOnePlusProductFormulaDefect A) = 0`.
-/
theorem formalLogOnePlusProductFormulaDefect_coeff_of_pos_coords_eq_zero
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ)
    (hleft : 0 < e (0 : Fin 2)) (hright : 0 < e (1 : Fin 2)) :
    MvPowerSeries.coeff e
        (formalLogOnePlusProductFormulaDefect A) = 0 := by
  rw [formalLogOnePlusProductFormulaDefect_coeff_of_pos_coords_eq_sum_card_choices
    A e hleft hright]
  let S :=
    (Finset.range (e (0 : Fin 2) + e (1 : Fin 2) + 1)).filter
      (fun q : ℕ => e (0 : Fin 2) ≤ q ∧ e (1 : Fin 2) ≤ q)
  let T : ℕ → ℚ := fun q =>
    (((-1 : ℚ) ^ (q - 1) / (q : ℚ)) *
      ((Nat.choose q (e (0 : Fin 2) + e (1 : Fin 2) - q) *
        Nat.choose
          (q - (e (0 : Fin 2) + e (1 : Fin 2) - q))
          (q - e (1 : Fin 2)) : ℕ) : ℚ))
  change
    (∑ q ∈ S,
      PowerSeries.coeff q (PowerSeries.log A) •
        ((formalLogOnePlusProductArgumentBasicFactorChoices q e).card : A)) = 0
  calc
    (∑ q ∈ S,
      PowerSeries.coeff q (PowerSeries.log A) •
        ((formalLogOnePlusProductArgumentBasicFactorChoices q e).card : A))
        = ∑ q ∈ S, algebraMap ℚ A (T q) := by
          apply Finset.sum_congr rfl
          intro q hq
          have hqmem := (Finset.mem_filter.mp hq)
          have hqleft : e (0 : Fin 2) ≤ q := hqmem.2.1
          have hqright : e (1 : Fin 2) ≤ q := hqmem.2.2
          have hqsum : q ≤ e (0 : Fin 2) + e (1 : Fin 2) :=
            Nat.lt_succ_iff.mp (Finset.mem_range.mp hqmem.1)
          rw [formalLogOnePlusProductArgumentBasicFactorChoices_card_eq_choose_mul_choose
            hqleft hqright hqsum]
          have hqpos : 0 < q := lt_of_lt_of_le hleft hqleft
          obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero
            (Nat.ne_of_gt hqpos)
          simp [T, smul_eq_mul, pow_succ]
    _ = algebraMap ℚ A (∑ q ∈ S, T q) := by
          rw [map_sum]
    _ = 0 := by
          rw [formalLogOnePlusProduct_rational_mixed_sum_eq_zero
            (e (0 : Fin 2)) (e (1 : Fin 2)) hleft hright]
          simp

/--
Establishes the identity `MvPowerSeries.coeff e (formalLogOnePlusProductFormulaDefect A) = 0`.
-/
theorem formalLogOnePlusProductFormulaDefect_coeff_eq_zero
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e
        (formalLogOnePlusProductFormulaDefect A) = 0 := by
  by_cases h0 : e (0 : Fin 2) = 0
  · exact formalLogOnePlusProductFormulaDefect_coeff_of_left_coord_zero
      A e h0
  · by_cases h1 : e (1 : Fin 2) = 0
    · exact formalLogOnePlusProductFormulaDefect_coeff_of_right_coord_zero
        A e h1
    · exact formalLogOnePlusProductFormulaDefect_coeff_of_pos_coords_eq_zero
        A e (Nat.pos_of_ne_zero h0) (Nat.pos_of_ne_zero h1)

/-- The formal logarithm product formula
`log ((1 + X) * (1 + Y)) = log (1 + X) + log (1 + Y)`. -/
theorem formalLogOnePlusProductFormula
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    PowerSeries.subst (formalLogOnePlusProductArgument A) (PowerSeries.log A) =
      formalLogOnePlusProductRightSide A := by
  ext e
  have h := formalLogOnePlusProductFormulaDefect_coeff_eq_zero A e
  have hsub :
      MvPowerSeries.coeff e
          (PowerSeries.subst (formalLogOnePlusProductArgument A) (PowerSeries.log A)) -
        MvPowerSeries.coeff e (formalLogOnePlusProductRightSide A) = 0 := by
    simpa [formalLogOnePlusProductFormulaDefect] using h
  exact sub_eq_zero.mp hsub

/-- For finitely many variables, a family is a valid `MvPowerSeries`
evaluation point as soon as every coordinate is topologically nilpotent. -/
theorem mvPowerSeries_hasEval_of_finite_topologicallyNilpotent
    {σ : Type*} {S : Type*} [CommRing S] [TopologicalSpace S] [Finite σ]
    {a : σ → S} (hpow : ∀ s, IsTopologicallyNilpotent (a s)) :
    MvPowerSeries.HasEval a := by
  refine ⟨hpow, ?_⟩
  rw [Filter.cofinite_eq_bot]
  exact Filter.tendsto_bot

/-- Two topologically nilpotent elements give a valid evaluation point for
the two-variable product formula. -/
theorem mvPowerSeries_hasEval_fin_two
    {S : Type*} [CommRing S] [TopologicalSpace S] {x y : S}
    (hx : IsTopologicallyNilpotent x) (hy : IsTopologicallyNilpotent y) :
    MvPowerSeries.HasEval (fun i : Fin 2 => if i = 0 then x else y) := by
  apply mvPowerSeries_hasEval_of_finite_topologicallyNilpotent
  intro i
  fin_cases i <;> simp [hx, hy]

/-- Evaluating the formal logarithm product identity at any convergent
two-variable point preserves the identity.  This is the formal-to-analytic
entry point for the field-unit logarithm theorem. -/
theorem formalLogOnePlusProductFormula_aeval
    (A : Type*) [CommRing A] [Algebra ℚ A]
    [UniformSpace A] [IsUniformAddGroup A]
    [CompleteSpace A] [T2Space A] [IsTopologicalRing A]
    [IsLinearTopology A A]
    {a : Fin 2 → A} (ha : MvPowerSeries.HasEval a) :
    MvPowerSeries.aeval ha
        (PowerSeries.subst (formalLogOnePlusProductArgument A) (PowerSeries.log A)) =
      MvPowerSeries.aeval ha (formalLogOnePlusProductRightSide A) := by
  exact congrArg (fun f => MvPowerSeries.aeval ha f)
    (formalLogOnePlusProductFormula A)

/-- The value of the monomial indexed by a finitely supported exponent at a
chosen evaluation point. -/
noncomputable def mvPowerSeriesMonomialValue
    {σ : Type*} {A : Type*} [CommMonoid A]
    (a : σ → A) (d : σ →₀ ℕ) : A :=
  d.prod fun s e => a s ^ e

/-- For each fixed degree `q`, the polynomial product argument has the expected
finite monomial evaluation at `(x,y)`.  This is the finite-stage bridge used
before turning the substituted formal logarithm into the field-valued product
logarithm. -/
theorem formalLogOnePlusProductArgument_pow_monomialValue_sum_eq
    (A : Type*) [CommRing A] (x y : A) (q : ℕ) :
    (∑ d ∈ (formalLogOnePlusProductArgumentPolynomial A ^ q).support,
      MvPowerSeries.coeff d ((formalLogOnePlusProductArgument A) ^ q) *
        mvPowerSeriesMonomialValue
          (fun i : Fin 2 => if i = 0 then x else y) d) =
      (x + y + x * y) ^ q := by
  classical
  let P : MvPolynomial (Fin 2) A :=
    formalLogOnePlusProductArgumentPolynomial A
  let a : Fin 2 → A := fun i => if i = 0 then x else y
  have hpow :
      ((P ^ q : MvPolynomial (Fin 2) A) : MvPowerSeries (Fin 2) A) =
        (formalLogOnePlusProductArgument A) ^ q := by
    simp [P, formalLogOnePlusProductArgument_eq_coe_polynomial]
  calc
    (∑ d ∈ (formalLogOnePlusProductArgumentPolynomial A ^ q).support,
      MvPowerSeries.coeff d ((formalLogOnePlusProductArgument A) ^ q) *
        mvPowerSeriesMonomialValue
          (fun i : Fin 2 => if i = 0 then x else y) d)
        =
      ∑ d ∈ (P ^ q).support,
        (P ^ q).coeff d * d.prod (fun i e => a i ^ e) := by
          subst P
          subst a
          apply Finset.sum_congr rfl
          intro d hd
          rw [← hpow, MvPolynomial.coeff_coe]
          simp [mvPowerSeriesMonomialValue]
    _ = MvPolynomial.eval a (P ^ q) := by
          rw [MvPolynomial.eval_eq]
          simp [Finsupp.prod]
    _ = (MvPolynomial.eval a P) ^ q := by
          simp
    _ = (x + y + x * y) ^ q := by
          simp [P, a]

/-- For each fixed degree `q`, the monomial family coming from the `q`-th
power of the product argument is finitely supported and sums to
`(x + y + xy)^q`. -/
theorem hasSum_formalLogOnePlusProductArgument_pow_monomialValue_pair
    (A : Type*) [CommRing A] [TopologicalSpace A] (x y : A) (q : ℕ) :
    HasSum
      (fun d : Fin 2 →₀ ℕ =>
        MvPowerSeries.coeff d ((formalLogOnePlusProductArgument A) ^ q) *
          mvPowerSeriesMonomialValue
            (fun i : Fin 2 => if i = 0 then x else y) d)
      ((x + y + x * y) ^ q) := by
  classical
  let P : MvPolynomial (Fin 2) A :=
    formalLogOnePlusProductArgumentPolynomial A
  let term : (Fin 2 →₀ ℕ) → A := fun d =>
    MvPowerSeries.coeff d ((formalLogOnePlusProductArgument A) ^ q) *
      mvPowerSeriesMonomialValue
        (fun i : Fin 2 => if i = 0 then x else y) d
  have hpow :
      ((P ^ q : MvPolynomial (Fin 2) A) : MvPowerSeries (Fin 2) A) =
        (formalLogOnePlusProductArgument A) ^ q := by
    simp [P, formalLogOnePlusProductArgument_eq_coe_polynomial]
  have hzero :
      ∀ d ∉ (formalLogOnePlusProductArgumentPolynomial A ^ q).support,
        term d = 0 := by
    intro d hd
    have hcoeff_poly :
        (formalLogOnePlusProductArgumentPolynomial A ^ q).coeff d = 0 :=
      by
        by_contra hne
        exact hd (MvPolynomial.mem_support_iff.mpr hne)
    have hcoeff_poly_P : (P ^ q).coeff d = 0 := by
      simpa [P] using hcoeff_poly
    have hcoeff :
        MvPowerSeries.coeff d
            ((formalLogOnePlusProductArgument A) ^ q) = 0 := by
      rw [← hpow]
      rw [MvPolynomial.coeff_coe]
      exact hcoeff_poly_P
    simp [term, hcoeff]
  have hfinite : HasSum term
      (∑ d ∈ (formalLogOnePlusProductArgumentPolynomial A ^ q).support,
        term d) :=
    hasSum_sum_of_ne_finset_zero hzero
  have hsum :
      (∑ d ∈ (formalLogOnePlusProductArgumentPolynomial A ^ q).support,
        term d) =
        (x + y + x * y) ^ q := by
    simpa [term] using
      formalLogOnePlusProductArgument_pow_monomialValue_sum_eq A x y q
  simpa [hsum, term] using hfinite

/-- Fixed-degree product-argument monomial evaluation after multiplying by an
outer logarithm coefficient. -/
theorem hasSum_formalLogOnePlusProductArgument_pow_monomialValue_pair_mul_left
    (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalSemiring A]
    (c x y : A) (q : ℕ) :
    HasSum
      (fun d : Fin 2 →₀ ℕ =>
        c * MvPowerSeries.coeff d ((formalLogOnePlusProductArgument A) ^ q) *
          mvPowerSeriesMonomialValue
            (fun i : Fin 2 => if i = 0 then x else y) d)
      (c * (x + y + x * y) ^ q) := by
  refine
    ((hasSum_formalLogOnePlusProductArgument_pow_monomialValue_pair
      A x y q).mul_left c).congr_fun ?_
  intro d
  ring

/-- Field- or ring-valued monomial-sum form of the formal logarithm product
identity.  Unlike `formalLogOnePlusProductFormula_aeval`, this statement only
uses equality of the coefficient functions and `HasSum` uniqueness, so it does
not require the target ring to carry a linear topology. -/
theorem formalLogOnePlusProductFormula_hasSum_monomialValue_eq
    (A : Type*) [CommRing A] [Algebra ℚ A] [TopologicalSpace A] [T2Space A]
    {a : Fin 2 → A} {L R : A}
    (hleft :
      HasSum
        (fun d : Fin 2 →₀ ℕ =>
          MvPowerSeries.coeff d
              (PowerSeries.subst (formalLogOnePlusProductArgument A) (PowerSeries.log A)) *
            mvPowerSeriesMonomialValue a d) L)
    (hright :
      HasSum
        (fun d : Fin 2 →₀ ℕ =>
          MvPowerSeries.coeff d (formalLogOnePlusProductRightSide A) *
            mvPowerSeriesMonomialValue a d) R) :
    L = R := by
  rw [formalLogOnePlusProductFormula A] at hleft
  exact hleft.unique hright

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
