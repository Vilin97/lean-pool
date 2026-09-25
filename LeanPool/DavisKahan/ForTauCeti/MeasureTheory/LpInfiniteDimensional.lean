/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.MeasureTheory.IntervalWeakSecondDeriv
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# `L²` is infinite-dimensional when the measure charges infinitely many disjoint sets

If a measure carries a sequence of pairwise disjoint measurable sets, each of positive finite
measure, then the indicators of those sets form an infinite orthogonal family of nonzero
vectors in `L²`, so `L²` is not finite-dimensional.

The application is the unit-interval model of Davis--Kahan 1970 Section 9: the ambient space
`Lp 𝕜 2 unitIocMeasure` of the free-beam realization is infinite-dimensional, witnessed by the
disjoint intervals `(1/(n+2), 1/(n+1)]`.  That is the input which turns an "the spectrum is
contained in `{0} ∪ (500, ∞)`" statement into an unbounded sequence of eigenvalues: with a
compact resolvent, finitely many eigenvalues would exhaust a finite-dimensional space.

The route through indicators is deliberately elementary — no polynomial or density argument is
needed, and nothing here depends on the measure being on `ℝ` except in the final corollary.

## Main results

* `TauCeti.not_finiteDimensional_lpTwo_of_pairwise_disjoint`: the general criterion.
* `TauCeti.not_finiteDimensional_lpTwo_unitIocMeasure`: `L²(0,1]` is infinite-dimensional.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Spectra influence: **none** -- this module imports only Mathlib and `ForTauCeti`.
-/

@[expose] public section

namespace TauCeti

open MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **An `L²` space with infinitely many disjoint charged sets is infinite-dimensional.**
The indicators of the sets are nonzero — their norms are positive powers of the masses — and
pairwise orthogonal, because the inner product of two indicators is the mass of the
intersection. -/
theorem not_finiteDimensional_lpTwo_of_pairwise_disjoint {α : Type*} [MeasurableSpace α]
    {mu : Measure α} (s : ℕ → Set α) (hmeas : ∀ n, MeasurableSet (s n))
    (hfin : ∀ n, mu (s n) ≠ ∞) (hzero : ∀ n, mu (s n) ≠ 0)
    (hdisj : ∀ i j : ℕ, i ≠ j → Disjoint (s i) (s j)) :
    ¬ FiniteDimensional 𝕜 (Lp 𝕜 2 mu) := by
  intro hfd
  set v : ℕ → Lp 𝕜 2 mu := fun n => indicatorConstLp 2 (hmeas n) (hfin n) (1 : 𝕜) with hv
  have hreal : ∀ n, 0 < mu.real (s n) := by
    intro n
    rw [measureReal_def]
    exact ENNReal.toReal_pos (hzero n) (hfin n)
  have hne : ∀ n, v n ≠ 0 := by
    intro n
    have hnorm : ‖v n‖ = ‖(1 : 𝕜)‖ * mu.real (s n) ^ (1 / (2 : ℝ≥0∞).toReal) :=
      norm_indicatorConstLp (by norm_num) (by norm_num)
    have hpos : 0 < ‖v n‖ := by
      rw [hnorm, norm_one, one_mul]
      exact Real.rpow_pos_of_pos (hreal n) _
    exact norm_pos_iff.mp hpos
  have hortho : Pairwise fun i j => (⟪v i, v j⟫_𝕜 : 𝕜) = 0 := by
    intro i j hij
    have hinter : s i ∩ s j = (∅ : Set α) :=
      Set.disjoint_iff_inter_eq_empty.mp (hdisj i j hij)
    rw [hv]
    rw [MeasureTheory.L2.inner_indicatorConstLp_indicatorConstLp (hmeas i) (hmeas j)
      (hfin i) (hfin j) (1 : 𝕜) (1 : 𝕜), hinter, measureReal_empty, zero_smul]
  have hli : LinearIndependent 𝕜 v :=
    linearIndependent_of_ne_zero_of_inner_eq_zero hne hortho
  have hcard := hli.lt_aleph0_of_finiteDimensional
  rw [Cardinal.mk_nat] at hcard
  exact lt_irrefl _ hcard

/-- The mass a subinterval of `(0,1]` receives from the unit-interval measure. -/
theorem unitIocMeasure_Ioc {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    unitIocMeasure (Set.Ioc a b) = ENNReal.ofReal (b - a) := by
  rw [unitIocMeasure_def, Measure.restrict_apply measurableSet_Ioc, Set.Ioc_inter_Ioc,
    sup_eq_left.mpr ha, inf_eq_left.mpr hb, Real.volume_Ioc]

/-- **`L²(0,1]` is infinite-dimensional.**  The witnesses are the indicators of the disjoint
intervals `(1/(n+2), 1/(n+1)]`, each of mass `1/((n+1)(n+2)) > 0`. -/
theorem not_finiteDimensional_lpTwo_unitIocMeasure :
    ¬ FiniteDimensional 𝕜 (Lp 𝕜 2 unitIocMeasure) := by
  set S : ℕ → Set ℝ := fun n => Set.Ioc (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1)) with hS
  have hlow : ∀ n : ℕ, (0 : ℝ) ≤ 1 / ((n : ℝ) + 2) := by
    intro n
    positivity
  have hhigh : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ 1 := by
    intro n
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hgap : ∀ n : ℕ, 1 / ((n : ℝ) + 2) < 1 / ((n : ℝ) + 1) := by
    intro n
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h2 : (n : ℝ) + 1 < (n : ℝ) + 2 := by linarith
    exact one_div_lt_one_div_of_lt h1 h2
  have hmass : ∀ n : ℕ, unitIocMeasure (S n)
      = ENNReal.ofReal (1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2)) := by
    intro n
    exact unitIocMeasure_Ioc (hlow n) (hhigh n)
  -- A larger index gives an interval strictly to the left of a smaller one.
  have hmono : ∀ i j : ℕ, i < j → 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 2) := by
    intro i j hij
    have h1 : (0 : ℝ) < (i : ℝ) + 2 := by positivity
    have hle : (i : ℝ) + 2 ≤ (j : ℝ) + 1 := by
      have : (i : ℕ) + 1 ≤ j := hij
      have hcast : ((i : ℝ)) + 1 ≤ (j : ℝ) := by exact_mod_cast this
      linarith
    exact one_div_le_one_div_of_le h1 hle
  have hdisjlt : ∀ i j : ℕ, i < j → Disjoint (S i) (S j) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro t hti htj
    have h1 : 1 / ((i : ℝ) + 2) < t := hti.1
    have h2 : t ≤ 1 / ((j : ℝ) + 1) := htj.2
    have h3 := hmono i j hij
    linarith
  refine not_finiteDimensional_lpTwo_of_pairwise_disjoint S (fun _ => measurableSet_Ioc)
    (fun n => ?_) (fun n => ?_) (fun i j hij => ?_)
  · rw [hmass n]
    exact ENNReal.ofReal_ne_top
  · rw [hmass n]
    have : 0 < 1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2) := by
      have := hgap n
      linarith
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact this
  · rcases lt_or_gt_of_ne hij with h | h
    · exact hdisjlt i j h
    · exact (hdisjlt j i h).symm

end

end TauCeti
