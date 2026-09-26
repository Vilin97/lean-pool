/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.NumericalNearby
public import Mathlib.Tactic

/-! # Numerical Interior -/

@[expose] public section

namespace BeyondBethe

/-!
# Quantitative interiority of the regularized optimizer

This file proves the analytic part of the finite-precision truncation used by
the algorithm.  The bounds are deliberately elementary: `x log x` terms are
controlled by entropy and by `negMulLog x ≤ 1 - x`.
-/

/-- A convenient range bound for the unregularized Bethe objective when all
matrix entries lie in `[m,1]`. -/
noncomputable def numericalObjectiveRange (n : ℕ) (m : ℝ) : ℝ :=
  n * Real.log (1 / m) + n * Real.log n + n

/-- On a matrix with entries at most one, the Bethe objective is at most the
total row entropy. -/
theorem betheObjective_le_totalRowEntropy
    {n : Type*} [Fintype n] [DecidableEq n]
    {A X : Matrix n n ℝ} (hApos : Matrix.Positive A)
    (hAupper : ∀ i j, A i j ≤ 1) (hX : IsDoublyStochastic X) :
    betheObjective A X ≤ totalRowEntropy X := by
  simp only [betheObjective, betheRowObjective, totalRowEntropy,
    shannonEntropy]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have hlogA : Real.log (A i j) ≤ 0 :=
    Real.log_nonpos (hApos i j).le (hAupper i j)
  have hlinear : X i j * Real.log (A i j) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (hX.nonnegative i j) hlogA
  have hcomp : (1 - X i j) * Real.log (1 - X i j) ≤ 0 :=
    Real.mul_log_nonpos (sub_nonneg.mpr (hX.entry_le_one i j))
      (by linarith [hX.nonnegative i j])
  linarith

/-- A lower bound on the Bethe objective using only a common lower bound on
the entries of the input matrix. -/
theorem betheObjective_lower_of_entry_lower
    {n : Type*} [Fintype n] [DecidableEq n]
    {m : ℝ} (hm : 0 < m) {A X : Matrix n n ℝ}
    (hAlower : ∀ i j, m ≤ A i j) (hX : IsDoublyStochastic X) :
    Fintype.card n * Real.log m - Fintype.card n ≤
      betheObjective A X := by
  simp only [betheObjective, betheRowObjective]
  calc
    Fintype.card n * Real.log m - Fintype.card n =
        ∑ _i : n, (Real.log m - 1) := by
          simp [nsmul_eq_mul]
    _ ≤ ∑ i, ∑ j,
        (X i j * Real.log (A i j) + Real.negMulLog (X i j) +
          (1 - X i j) * Real.log (1 - X i j)) := by
      apply Finset.sum_le_sum
      intro i _
      have hrow : Real.log m - 1 = ∑ j, (X i j * Real.log m - X i j) := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hX.row_sum]
        ring
      rw [hrow]
      apply Finset.sum_le_sum
      intro j _
      have hlog : Real.log m ≤ Real.log (A i j) :=
        Real.log_le_log hm (hAlower i j)
      have hlinear : X i j * Real.log m ≤
          X i j * Real.log (A i j) :=
        mul_le_mul_of_nonneg_left hlog (hX.nonnegative i j)
      have hentropy : 0 ≤ Real.negMulLog (X i j) :=
        Real.negMulLog_nonneg (hX.nonnegative i j) (hX.entry_le_one i j)
      have hcompNonneg : 0 ≤ 1 - X i j :=
        sub_nonneg.mpr (hX.entry_le_one i j)
      have hcomp := Real.negMulLog_le_one_sub_self hcompNonneg
      rw [Real.negMulLog_def] at hcomp
      linarith

/-- The unregularized objective changes by at most
`numericalObjectiveRange` between a feasible point and the Birkhoff
barycenter. -/
theorem betheObjective_sub_uniform_le_range
    {n : ℕ} (hn : 1 < n) {m : ℝ} (hm : 0 < m)
    {A X : Matrix (Fin n) (Fin n) ℝ}
    (hApos : Matrix.Positive A) (hAlower : ∀ i j, m ≤ A i j)
    (hAupper : ∀ i j, A i j ≤ 1) (hX : IsDoublyStochastic X) :
    betheObjective A X - betheObjective A (uniformBirkhoff n) ≤
      numericalObjectiveRange n m := by
  have hn0 : 0 < n := by omega
  letI : Nonempty (Fin n) := ⟨⟨0, hn0⟩⟩
  have hW := uniformBirkhoff_doublyStochastic hn0
  have hupper := (betheObjective_le_totalRowEntropy hApos hAupper hX).trans
    (by simpa using totalRowEntropy_le hX)
  have hlower := betheObjective_lower_of_entry_lower hm hAlower hW
  have hloginv : Real.log (1 / m) = -Real.log m := by
    rw [one_div, Real.log_inv]
  dsimp only [numericalObjectiveRange]
  rw [hloginv]
  simp only [Fintype.card_fin] at hupper hlower
  linarith

/-- The directional entropy derivative from an interior regularized maximizer
toward the Birkhoff barycenter is controlled by the unregularized objective
range. -/
theorem entropy_direction_to_uniform_mul_le_range
    {n : ℕ} (hn : 1 < n) {τ m : ℝ} (hτ : 0 < τ) (hm : 0 < m)
    {A X : Matrix (Fin n) (Fin n) ℝ}
    (hApos : Matrix.Positive A) (hAlower : ∀ i j, m ≤ A i j)
    (hAupper : ∀ i j, A i j ≤ 1)
    (hX : IsDoublyStochastic X)
    (hmax : ∀ Y, IsDoublyStochastic Y →
      regularizedBetheObjective τ A Y ≤ regularizedBetheObjective τ A X) :
    τ * (∑ i, ∑ j, (-1 - Real.log (X i j)) *
        (uniformBirkhoff n i j - X i j)) ≤
      numericalObjectiveRange n m := by
  have hW : IsDoublyStochastic (uniformBirkhoff n) :=
    uniformBirkhoff_doublyStochastic (show 0 < n by omega)
  have hXint := regularizedBetheMaximizer_interior hn hτ hApos hX hmax
  have hDrow : ∀ i, ∑ j, (uniformBirkhoff n i j - X i j) = 0 := by
    intro i
    simp_rw [Finset.sum_sub_distrib, hW.row_sum, hX.row_sum, sub_self]
  have hDcol : ∀ j, ∑ i, (uniformBirkhoff n i j - X i j) = 0 := by
    intro j
    simp_rw [Finset.sum_sub_distrib, hW.col_sum, hX.col_sum, sub_self]
  have hstationary := regularizedBetheMaximizer_tangent_orthogonal
    (D := fun i j ↦ uniformBirkhoff n i j - X i j)
      hX hXint hmax hDrow hDcol
  have hsupport := regularizedBetheObjective_sub_le_gradient
    (A := A) (X := X) (Y := uniformBirkhoff n) (τ := 0)
      (by simpa using hn) (by norm_num) hX hW hXint
  have hbetaLower : -numericalObjectiveRange n m ≤
      betheObjective A (uniformBirkhoff n) - betheObjective A X := by
    have hrange := betheObjective_sub_uniform_le_range hn hm hApos
      hAlower hAupper hX
    linarith
  have hbetheDirectional : -numericalObjectiveRange n m ≤
      ∑ i, ∑ j, regularizedBetheGradient 0 A X i j *
        (uniformBirkhoff n i j - X i j) := by
    rw [regularizedBetheObjective, regularizedBetheObjective] at hsupport
    simp only [zero_mul, add_zero] at hsupport
    exact hbetaLower.trans hsupport
  have hgradient : ∀ i j,
      regularizedBetheGradient τ A X i j =
        regularizedBetheGradient 0 A X i j +
          τ * (-1 - Real.log (X i j)) := by
    intro i j
    simp only [regularizedBetheGradient]
    ring
  have hdecomp :
      (∑ i, ∑ j, regularizedBetheGradient τ A X i j *
          (uniformBirkhoff n i j - X i j)) =
        (∑ i, ∑ j, regularizedBetheGradient 0 A X i j *
          (uniformBirkhoff n i j - X i j)) +
          τ * (∑ i, ∑ j, (-1 - Real.log (X i j)) *
            (uniformBirkhoff n i j - X i j)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hgradient]
    ring
  rw [hdecomp] at hstationary
  linarith

/-- Exact formula for the entropy directional derivative toward the Birkhoff
barycenter. -/
theorem entropy_direction_to_uniform_eq
    {n : ℕ} (hn : 0 < n) {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : IsDoublyStochastic X) :
    (∑ i, ∑ j, (-1 - Real.log (X i j)) *
        (uniformBirkhoff n i j - X i j)) =
      -totalRowEntropy X -
        (1 / n) * (∑ i, ∑ j, Real.log (X i j)) := by
  let W := uniformBirkhoff n
  have hW : IsDoublyStochastic W := uniformBirkhoff_doublyStochastic hn
  have htotalDiff : ∑ i, ∑ j, (X i j - W i j) = 0 := by
    simp_rw [Finset.sum_sub_distrib, hX.row_sum, hW.row_sum, sub_self]
  have hentropy : (∑ i, ∑ j, X i j * Real.log (X i j)) =
      -totalRowEntropy X := by
    rw [totalRowEntropy, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [shannonEntropy, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [Real.negMulLog_def]
    ring
  have hWlog : (∑ i, ∑ j, W i j * Real.log (X i j)) =
      (1 / n) * (∑ i, ∑ j, Real.log (X i j)) := by
    dsimp only [W, uniformBirkhoff]
    simp_rw [← Finset.mul_sum]
  change (∑ i, ∑ j, (-1 - Real.log (X i j)) *
      (W i j - X i j)) = _
  calc
    (∑ i, ∑ j, (-1 - Real.log (X i j)) * (W i j - X i j)) =
        (∑ i, ∑ j, X i j * Real.log (X i j)) -
          (∑ i, ∑ j, W i j * Real.log (X i j)) +
            ∑ i, ∑ j, (X i j - W i j) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = -totalRowEntropy X -
        (1 / n) * (∑ i, ∑ j, Real.log (X i j)) := by
      rw [hentropy, hWlog, htotalDiff, add_zero]

/-- Quantitative form of the interior bound.  Every coordinate, not merely a
chosen minimum, obeys the same estimate. -/
theorem regularizedBetheMaximizer_log_inv_entry_le
    {n : ℕ} (hn : 1 < n) {τ m : ℝ} (hτ : 0 < τ) (hm : 0 < m)
    {A X : Matrix (Fin n) (Fin n) ℝ}
    (hApos : Matrix.Positive A) (hAlower : ∀ i j, m ≤ A i j)
    (hAupper : ∀ i j, A i j ≤ 1)
    (hX : IsDoublyStochastic X)
    (hmax : ∀ Y, IsDoublyStochastic Y →
      regularizedBetheObjective τ A Y ≤ regularizedBetheObjective τ A X)
    (i₀ j₀ : Fin n) :
    Real.log (1 / X i₀ j₀) ≤
      n * numericalObjectiveRange n m / τ + n ^ 2 * Real.log n := by
  have hn0 : 0 < n := by omega
  letI : Nonempty (Fin n) := ⟨⟨0, hn0⟩⟩
  have hXint := regularizedBetheMaximizer_interior hn hτ hApos hX hmax
  have hXpos : ∀ i j, 0 < X i j := fun i j ↦ (hXint i).2 j |>.1
  have hdir := entropy_direction_to_uniform_mul_le_range hn hτ hm
    hApos hAlower hAupper hX hmax
  rw [entropy_direction_to_uniform_eq hn0 hX] at hdir
  have hentropy := totalRowEntropy_le hX
  have hlognonpos : ∀ i j, Real.log (X i j) ≤ 0 := fun i j ↦
    Real.log_nonpos (hX.nonnegative i j) (hX.entry_le_one i j)
  have hchosen : -Real.log (X i₀ j₀) ≤
      -(∑ i, ∑ j, Real.log (X i j)) := by
    have hnonneg : ∀ i j, 0 ≤ -Real.log (X i j) := fun i j ↦
      neg_nonneg.mpr (hlognonpos i j)
    have hsingle : -Real.log (X i₀ j₀) ≤
        ∑ j, -Real.log (X i₀ j) :=
      Finset.single_le_sum (fun j _ ↦ hnonneg i₀ j) (Finset.mem_univ j₀)
    have hrow : ∑ j, -Real.log (X i₀ j) ≤
        ∑ i, ∑ j, -Real.log (X i j) :=
      Finset.single_le_sum
        (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ hnonneg i j)
        (Finset.mem_univ i₀)
    simpa only [Finset.sum_neg_distrib] using hsingle.trans hrow
  have hloginv : Real.log (1 / X i₀ j₀) = -Real.log (X i₀ j₀) := by
    rw [one_div, Real.log_inv]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  rw [hloginv]
  simp only [Fintype.card_fin] at hentropy
  have hscaledChosen := mul_le_mul_of_nonneg_left hchosen
    (by positivity : 0 ≤ (1 / (n : ℝ)))
  have hdirLower :
      -(n : ℝ) * Real.log n + (1 / n) * (-Real.log (X i₀ j₀)) ≤
        -totalRowEntropy X -
          (1 / n) * (∑ i, ∑ j, Real.log (X i j)) := by
    linarith
  have hcore : τ * (-(n : ℝ) * Real.log n +
      (1 / n) * (-Real.log (X i₀ j₀))) ≤
        numericalObjectiveRange n m :=
    (mul_le_mul_of_nonneg_left hdirLower hτ.le).trans hdir
  have hmul := mul_le_mul_of_nonneg_left hcore hnR.le
  have halgebra :
      (n : ℝ) * (τ * (-(n : ℝ) * Real.log n +
        (1 / n) * (-Real.log (X i₀ j₀)))) =
      τ * (-Real.log (X i₀ j₀) -
        (n : ℝ) ^ 2 * Real.log n) := by
    field_simp [hnR.ne']
    ring
  rw [halgebra] at hmul
  have hmul' :
      (-Real.log (X i₀ j₀) - (n : ℝ) ^ 2 * Real.log n) * τ ≤
        (n : ℝ) * numericalObjectiveRange n m := by
    simpa only [mul_comm] using hmul
  have hdiv := (le_div_iff₀ hτ).2 hmul'
  linarith

/-- The complementary coordinates obey the same logarithmic bit bound. -/
theorem regularizedBetheMaximizer_log_inv_one_sub_entry_le
    {n : ℕ} (hn : 1 < n) {τ m : ℝ} (hτ : 0 < τ) (hm : 0 < m)
    {A X : Matrix (Fin n) (Fin n) ℝ}
    (hApos : Matrix.Positive A) (hAlower : ∀ i j, m ≤ A i j)
    (hAupper : ∀ i j, A i j ≤ 1)
    (hX : IsDoublyStochastic X)
    (hmax : ∀ Y, IsDoublyStochastic Y →
      regularizedBetheObjective τ A Y ≤ regularizedBetheObjective τ A X)
    (i₀ j₀ : Fin n) :
    Real.log (1 / (1 - X i₀ j₀)) ≤
      n * numericalObjectiveRange n m / τ + n ^ 2 * Real.log n := by
  obtain ⟨k, hkj⟩ := Fintype.exists_ne_of_one_lt_card
    (by simpa using hn) j₀
  have hXint := regularizedBetheMaximizer_interior hn hτ hApos hX hmax
  have hkpos : 0 < X i₀ k := (hXint i₀).2 k |>.1
  have hcompPos : 0 < 1 - X i₀ j₀ :=
    sub_pos.mpr ((hXint i₀).2 j₀ |>.2)
  have hpair : X i₀ j₀ + X i₀ k ≤ 1 := by
    rw [← hX.row_sum i₀]
    calc
      X i₀ j₀ + X i₀ k =
          ∑ l ∈ ({j₀, k} : Finset (Fin n)), X i₀ l := by
            rw [Finset.sum_pair hkj.symm]
      _ ≤ ∑ l, X i₀ l :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun l _ _ ↦ hX.nonnegative i₀ l)
  have hkcomp : X i₀ k ≤ 1 - X i₀ j₀ := by linarith
  have hinv : 1 / (1 - X i₀ j₀) ≤ 1 / X i₀ k :=
    one_div_le_one_div_of_le hkpos hkcomp
  exact (Real.log_le_log (one_div_pos.mpr hcompPos) hinv).trans
    (regularizedBetheMaximizer_log_inv_entry_le hn hτ hm hApos
      hAlower hAupper hX hmax i₀ k)

end BeyondBethe
