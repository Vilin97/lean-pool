/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.SetTheory.Cardinal.Finite
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectLubinTateBracket
/-!
# The completed theta-intertwining theorem: recursion for the standard Lubin--Tate bracket

The standard bracket constructed from its contracting coefficient equations
agrees with the recursive `T`-adic bracket used in the finite Lubin–Tate bracket construction.
  At the formal
series level the required identity is

`[a](Y) = a₀ Y + [tail(a)](e_T(Y))`.

This file proves the identity from uniqueness of the commuting `q`-additive
series.  It is the bridge from the formal bracket used in the theta identity
to the finite brackets acting on division points.
-/

noncomputable section

open scoped PowerSeries


universe u

namespace LubinTate
namespace EqualCharacteristic

variable {k : Type u} [Field k] [Finite k]

/-- The scalar-linear summand `a₀Y`, in sparse additive coordinates. -/
noncomputable def equalCharacteristicDirectBracketScalarCoefficient
    (a : k⟦X⟧) : ℕ → (AlgebraicClosure k)⟦X⟧
  | 0 => PowerSeries.C
      (algebraMap k (AlgebraicClosure k) (PowerSeries.coeff 0 a))
  | _ + 1 => 0

/-- Coefficients of `[tail(a)] ∘ e_T`. -/
noncomputable def equalCharacteristicDirectBracketTailCompositionCoefficient
    (a : k⟦X⟧) : ℕ → (AlgebraicClosure k)⟦X⟧ :=
  equalCharacteristicLubinTateSubstitutionCoefficient
    (PowerSeries.X : (AlgebraicClosure k)⟦X⟧)
    (equalCharacteristicCompletedDirectBracketCoefficient
      (equalCharacteristicPowerSeriesTail a))

/-- Coefficients of the recursive candidate
`a₀Y + [tail(a)] ∘ e_T`. -/
noncomputable def equalCharacteristicDirectBracketRecursiveCoefficient
    (a : k⟦X⟧) : ℕ → (AlgebraicClosure k)⟦X⟧ :=
  fun j ↦ equalCharacteristicDirectBracketScalarCoefficient a j +
    equalCharacteristicDirectBracketTailCompositionCoefficient a j

private theorem equalCharacteristicDirectBracketScalarSeries_eq
    (a : k⟦X⟧) :
    equalCharacteristicQAdditiveSeries k
        (equalCharacteristicDirectBracketScalarCoefficient a) =
      PowerSeries.C (PowerSeries.C
          (algebraMap k (AlgebraicClosure k) (PowerSeries.coeff 0 a))) *
        PowerSeries.X := by
  apply PowerSeries.ext
  intro n
  by_cases hn : IsEqualCharacteristicAdditiveExponent k n
  · obtain ⟨j, rfl⟩ := hn
    rw [equalCharacteristicQAdditiveSeries_coeff_pow,
      PowerSeries.coeff_C_mul]
    cases j with
    | zero =>
        simp [equalCharacteristicDirectBracketScalarCoefficient]
    | succ j =>
        have hpow : Nat.card k ^ (j + 1) ≠ 1 := by
          intro h
          have := natCard_pow_injective k (h.trans (pow_zero _).symm)
          omega
        rw [equalCharacteristicDirectBracketScalarCoefficient]
        rw [PowerSeries.coeff_X, ite_eq_right hpow]
        simp
  · have hne : n ≠ 1 := by
      intro h
      subst n
      exact hn ⟨0, by simp⟩
    rw [equalCharacteristicQAdditiveSeries_coeff_eq_zero k _ n hn,
      PowerSeries.coeff_C_mul]
    rw [PowerSeries.coeff_X, ite_eq_right hne]
    simp

/-- The recursive candidate is the sum of its scalar term and the genuine
formal substitution `[tail(a)] ∘ e_T`. -/
theorem equalCharacteristicDirectBracketRecursiveSeries_eq
    (a : k⟦X⟧) :
    equalCharacteristicQAdditiveSeries k
        (equalCharacteristicDirectBracketRecursiveCoefficient a) =
      PowerSeries.C (PowerSeries.C
          (algebraMap k (AlgebraicClosure k) (PowerSeries.coeff 0 a))) *
          PowerSeries.X +
        PowerSeries.subst
          (equalCharacteristicCompletedLubinTateSeries (k := k)
            (PowerSeries.X : (AlgebraicClosure k)⟦X⟧))
          (equalCharacteristicCompletedDirectBracket
            (equalCharacteristicPowerSeriesTail a)) := by
  change equalCharacteristicQAdditiveSeries k
      (fun j ↦ equalCharacteristicDirectBracketScalarCoefficient a j +
        equalCharacteristicDirectBracketTailCompositionCoefficient a j) = _
  rw [← equalCharacteristicQAdditiveSeries_add,
    equalCharacteristicDirectBracketScalarSeries_eq]
  congr 1
  rw [equalCharacteristicCompletedDirectBracket,
    equalCharacteristicQAdditiveSeries_subst_completedLubinTateSeries]
  rfl

/-- Coefficient recurrence read from commutation with `e_T`. -/
theorem equalCharacteristicDirectQAdditiveEndomorphism_succ_comparison
    (c : ℕ → (AlgebraicClosure k)⟦X⟧)
    (hcommutes :
      PowerSeries.subst (equalCharacteristicQAdditiveSeries k c)
          (equalCharacteristicCompletedLubinTateSeries (k := k)
            (PowerSeries.X : (AlgebraicClosure k)⟦X⟧)) =
        PowerSeries.subst
          (equalCharacteristicCompletedLubinTateSeries (k := k)
            (PowerSeries.X : (AlgebraicClosure k)⟦X⟧))
          (equalCharacteristicQAdditiveSeries k c))
    (j : ℕ) :
    PowerSeries.X * c (j + 1) -
        PowerSeries.X ^ (Nat.card k ^ (j + 1)) * c (j + 1) =
      c j - c j ^ Nat.card k := by
  rw [equalCharacteristicCompletedLubinTateSeries_subst_qAdditiveSeries,
    equalCharacteristicQAdditiveSeries_subst_completedLubinTateSeries]
    at hcommutes
  have hcoeff := congrArg
    (PowerSeries.coeff (Nat.card k ^ (j + 1))) hcommutes
  rw [equalCharacteristicQAdditiveSeries_coeff_pow,
    equalCharacteristicQAdditiveSeries_coeff_pow,
    equalCharacteristicLubinTatePostcompositionCoefficient,
    equalCharacteristicLubinTateSubstitutionCoefficient] at hcoeff
  linear_combination hcoeff

private theorem equalCharacteristicDirectBracketScalarCoefficient_succ_comparison
    (a : k⟦X⟧) (j : ℕ) :
    PowerSeries.X *
          equalCharacteristicDirectBracketScalarCoefficient a (j + 1) -
        PowerSeries.X ^ (Nat.card k ^ (j + 1)) *
          equalCharacteristicDirectBracketScalarCoefficient a (j + 1) =
      equalCharacteristicDirectBracketScalarCoefficient a j -
        equalCharacteristicDirectBracketScalarCoefficient a j ^ Nat.card k := by
  let : Fintype k := Fintype.ofFinite k
  cases j with
  | zero =>
      simp [equalCharacteristicDirectBracketScalarCoefficient,
        ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
  | succ j => simp [equalCharacteristicDirectBracketScalarCoefficient]

private theorem equalCharacteristicDirectBracketTailCompositionSeries_commutes
    (a : k⟦X⟧) :
    PowerSeries.subst
        (equalCharacteristicQAdditiveSeries k
          (equalCharacteristicDirectBracketTailCompositionCoefficient a))
        (equalCharacteristicCompletedLubinTateSeries (k := k)
          (PowerSeries.X : (AlgebraicClosure k)⟦X⟧)) =
      PowerSeries.subst
        (equalCharacteristicCompletedLubinTateSeries (k := k)
          (PowerSeries.X : (AlgebraicClosure k)⟦X⟧))
        (equalCharacteristicQAdditiveSeries k
          (equalCharacteristicDirectBracketTailCompositionCoefficient a)) := by
  let E := equalCharacteristicCompletedLubinTateSeries (k := k)
    (PowerSeries.X : (AlgebraicClosure k)⟦X⟧)
  let H := equalCharacteristicCompletedDirectBracket
    (equalCharacteristicPowerSeriesTail a)
  have hE : PowerSeries.HasSubst E :=
    equalCharacteristicCompletedLubinTateSeries_hasSubst
      (PowerSeries.X : (AlgebraicClosure k)⟦X⟧)
  have hH : PowerSeries.HasSubst H :=
    equalCharacteristicCompletedDirectBracket_hasSubst
      (equalCharacteristicPowerSeriesTail a)
  have hcomp :
      equalCharacteristicQAdditiveSeries k
          (equalCharacteristicDirectBracketTailCompositionCoefficient a) =
        PowerSeries.subst E H := by
    unfold equalCharacteristicDirectBracketTailCompositionCoefficient
    change equalCharacteristicQAdditiveSeries k
        (equalCharacteristicLubinTateSubstitutionCoefficient
          (PowerSeries.X : (AlgebraicClosure k)⟦X⟧)
          (equalCharacteristicCompletedDirectBracketCoefficient
            (equalCharacteristicPowerSeriesTail a))) =
      PowerSeries.subst E
        (equalCharacteristicQAdditiveSeries k
          (equalCharacteristicCompletedDirectBracketCoefficient
            (equalCharacteristicPowerSeriesTail a)))
    exact (equalCharacteristicQAdditiveSeries_subst_completedLubinTateSeries
      (k := k) (PowerSeries.X : (AlgebraicClosure k)⟦X⟧)
      (equalCharacteristicCompletedDirectBracketCoefficient
        (equalCharacteristicPowerSeriesTail a))).symm
  have hcomm : PowerSeries.subst H E = PowerSeries.subst E H := by
    simpa only [H, E] using
      equalCharacteristicCompletedDirectBracket_commutes
        (equalCharacteristicPowerSeriesTail a)
  rw [hcomp]
  calc
    PowerSeries.subst (PowerSeries.subst E H) E =
        PowerSeries.subst E (PowerSeries.subst H E) :=
      (PowerSeries.subst_comp_subst_apply hH hE E).symm
    _ = PowerSeries.subst E (PowerSeries.subst E H) := by rw [hcomm]

private theorem
    equalCharacteristicDirectBracketTailCompositionCoefficient_succ_comparison
    (a : k⟦X⟧) (j : ℕ) :
    PowerSeries.X *
          equalCharacteristicDirectBracketTailCompositionCoefficient a (j + 1) -
        PowerSeries.X ^ (Nat.card k ^ (j + 1)) *
          equalCharacteristicDirectBracketTailCompositionCoefficient a (j + 1) =
      equalCharacteristicDirectBracketTailCompositionCoefficient a j -
        equalCharacteristicDirectBracketTailCompositionCoefficient a j ^
          Nat.card k :=
  equalCharacteristicDirectQAdditiveEndomorphism_succ_comparison
    (equalCharacteristicDirectBracketTailCompositionCoefficient a)
    (equalCharacteristicDirectBracketTailCompositionSeries_commutes a) j

omit [Finite k] in
private theorem equalCharacteristicDirectBracketRecursiveCoefficient_zero
    (a : k⟦X⟧) :
    equalCharacteristicDirectBracketRecursiveCoefficient a 0 =
      PowerSeries.map (algebraMap k (AlgebraicClosure k)) a := by
  have hsplit := congrArg
    (PowerSeries.map (algebraMap k (AlgebraicClosure k)))
    (equalCharacteristicPowerSeries_eq_X_mul_tail_add_C a)
  simp only [equalCharacteristicDirectBracketRecursiveCoefficient,
    equalCharacteristicDirectBracketScalarCoefficient,
    equalCharacteristicDirectBracketTailCompositionCoefficient,
    equalCharacteristicLubinTateSubstitutionCoefficient,
    equalCharacteristicCompletedDirectBracketCoefficient_zero]
  simpa [map_add, map_mul, mul_comm, add_comm] using hsplit.symm

private theorem
    equalCharacteristicDirectBracketRecursiveCoefficient_succ_comparison
    (a : k⟦X⟧) (j : ℕ) :
    PowerSeries.X *
          equalCharacteristicDirectBracketRecursiveCoefficient a (j + 1) -
        PowerSeries.X ^ (Nat.card k ^ (j + 1)) *
          equalCharacteristicDirectBracketRecursiveCoefficient a (j + 1) =
      equalCharacteristicDirectBracketRecursiveCoefficient a j -
        equalCharacteristicDirectBracketRecursiveCoefficient a j ^ Nat.card k := by
  have hs := equalCharacteristicDirectBracketScalarCoefficient_succ_comparison
    (k := k) a j
  have ht :=
    equalCharacteristicDirectBracketTailCompositionCoefficient_succ_comparison
      (k := k) a j
  change PowerSeries.X *
        (equalCharacteristicDirectBracketScalarCoefficient a (j + 1) +
          equalCharacteristicDirectBracketTailCompositionCoefficient a (j + 1)) -
      PowerSeries.X ^ (Nat.card k ^ (j + 1)) *
        (equalCharacteristicDirectBracketScalarCoefficient a (j + 1) +
          equalCharacteristicDirectBracketTailCompositionCoefficient a (j + 1)) =
    (equalCharacteristicDirectBracketScalarCoefficient a j +
        equalCharacteristicDirectBracketTailCompositionCoefficient a j) -
      (equalCharacteristicDirectBracketScalarCoefficient a j +
        equalCharacteristicDirectBracketTailCompositionCoefficient a j) ^
          Nat.card k
  have hadd :
      (equalCharacteristicDirectBracketScalarCoefficient a j +
          equalCharacteristicDirectBracketTailCompositionCoefficient a j) ^
          Nat.card k =
        equalCharacteristicDirectBracketScalarCoefficient a j ^ Nat.card k +
          equalCharacteristicDirectBracketTailCompositionCoefficient a j ^
            Nat.card k := by
    simpa using add_pow_natCard_pow (k := k)
      (equalCharacteristicDirectBracketScalarCoefficient a j)
      (equalCharacteristicDirectBracketTailCompositionCoefficient a j) 1
  rw [hadd]
  linear_combination hs + ht

/-- Uniqueness of a standard commuting `q`-additive endomorphism from its
linear coefficient. -/
theorem equalCharacteristicCompletedDirectEndomorphismCoefficient_unique
    (c d : ℕ → (AlgebraicClosure k)⟦X⟧)
    (hzero : c 0 = d 0)
    (hc : ∀ j : ℕ,
      PowerSeries.X * c (j + 1) -
          PowerSeries.X ^ (Nat.card k ^ (j + 1)) * c (j + 1) =
        c j - c j ^ Nat.card k)
    (hd : ∀ j : ℕ,
      PowerSeries.X * d (j + 1) -
          PowerSeries.X ^ (Nat.card k ^ (j + 1)) * d (j + 1) =
        d j - d j ^ Nat.card k) :
    c = d := by
  funext j
  induction j with
  | zero => exact hzero
  | succ j ih =>
      have hcj := hc j
      have hdj := hd j
      rw [ih] at hcj
      let delta := c (j + 1) - d (j + 1)
      have hdiff :
          PowerSeries.X * delta -
              PowerSeries.X ^ (Nat.card k ^ (j + 1)) * delta = 0 := by
        dsimp only [delta]
        linear_combination hcj - hdj
      let qj := Nat.card k ^ (j + 1)
      change PowerSeries.X * delta - PowerSeries.X ^ qj * delta = 0 at hdiff
      let gamma : (AlgebraicClosure k)⟦X⟧ :=
        PowerSeries.X ^ (qj - 1)
      have hq : 1 ≤ qj :=
        Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ Nat.card_pos.ne')
      have hXGamma : PowerSeries.X * gamma =
          (PowerSeries.X : (AlgebraicClosure k)⟦X⟧) ^ qj := by
        dsimp only [gamma]
        calc
          PowerSeries.X * PowerSeries.X ^ (qj - 1) =
              PowerSeries.X ^ ((qj - 1) + 1) := by rw [pow_succ']
          _ = _ := by rw [Nat.sub_add_cancel hq]
      have hhom : delta - gamma * delta = 0 := by
        apply PowerSeries.X_mul_injective
        change PowerSeries.X * (delta - gamma * delta) = PowerSeries.X * 0
        rw [mul_sub, ← mul_assoc, hXGamma, mul_zero]
        exact hdiff
      have hgamma : PowerSeries.coeff 0 gamma = 0 := by
        have hcard : 1 < Nat.card k := Finite.one_lt_card
        have hpow : 0 < qj - 1 :=
          Nat.sub_pos_of_lt (Nat.one_lt_pow (Nat.zero_lt_succ j).ne' hcard)
        simp [gamma, hpow.ne]
      have hunique := existsUnique_contractingFrobeniusEquation
        (RingHom.id (AlgebraicClosure k)) gamma 0 hgamma
      have hdelta : delta = 0 := hunique.unique (by simpa using hhom) (by simp)
      exact sub_eq_zero.mp (by simpa only [delta] using hdelta)

/-- Formal recursive identity for the standard bracket. -/
theorem equalCharacteristicCompletedDirectBracket_recursion
    (a : k⟦X⟧) :
    equalCharacteristicCompletedDirectBracket a =
      PowerSeries.C (PowerSeries.C
          (algebraMap k (AlgebraicClosure k) (PowerSeries.coeff 0 a))) *
          PowerSeries.X +
        PowerSeries.subst
          (equalCharacteristicCompletedLubinTateSeries (k := k)
            (PowerSeries.X : (AlgebraicClosure k)⟦X⟧))
          (equalCharacteristicCompletedDirectBracket
            (equalCharacteristicPowerSeriesTail a)) := by
  have hcoeff :
      equalCharacteristicCompletedDirectBracketCoefficient a =
        equalCharacteristicDirectBracketRecursiveCoefficient a :=
    equalCharacteristicCompletedDirectEndomorphismCoefficient_unique
      (equalCharacteristicCompletedDirectBracketCoefficient a)
      (equalCharacteristicDirectBracketRecursiveCoefficient a)
      (equalCharacteristicDirectBracketRecursiveCoefficient_zero a).symm
      (equalCharacteristicCompletedDirectBracketCoefficient_succ_comparison a)
      (equalCharacteristicDirectBracketRecursiveCoefficient_succ_comparison a)
  rw [equalCharacteristicCompletedDirectBracket,
    ← equalCharacteristicDirectBracketRecursiveSeries_eq]
  exact congrArg (equalCharacteristicQAdditiveSeries k) hcoeff

end EqualCharacteristic
end LubinTate
