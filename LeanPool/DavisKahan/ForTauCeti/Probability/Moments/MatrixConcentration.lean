/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8

Staged for Tau Ceti, roadmap topic T20.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
eigenvalue concentration for a random Hermitian matrix from
per-entry second-moment control (the elementary, no-matrix-Bernstein route:
entrywise Chebyshev + union bound, then entrywise → operator-norm → Weyl).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]); prose symbol `Ŝ` → `Shat`
(matching the Lean variable, clearing the Mathlib unicode-allowlist linter).
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.Matrix.EntrywiseEigenvalue
public import LeanPool.DavisKahan.ForTauCeti.Analysis.Matrix.EntrywiseOpNorm
public import LeanPool.DavisKahan.ForTauCeti.Probability.Moments.Variance


/-! # Eigenvalue concentration of a random Hermitian matrix

For a random real-symmetric `n × n` matrix `Shat(ω)` that is entrywise close in
mean-square to a fixed symmetric `A` (`∫ (Shat_{kl} − A_{kl})² ≤ v` for every
entry), Chebyshev + a union bound over the `n²` entries give that, with
probability `≥ 1 − n² v / η²`, every entry is within `η`; whence (entrywise
eigenvalue perturbation) every eigenvalue of `Shat(ω)` is within `n · η` of
the corresponding eigenvalue of `A`.

This is the elementary route to sample second-moment / empirical-Gram eigenvalue
concentration — no matrix Bernstein/Hoeffding needed (at the cost of the loose
`n`/`n²` constants).

## Main results

* `TauCeti.measure_exists_entry_gt_le` — entrywise concentration (union bound).
* `TauCeti.measure_forall_abs_eigenvalues₀_sub_le_ge` — eigenvalue concentration.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Probability.Moments.MatrixConcentration`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `2356fd0`.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`; declaration names and proofs are unchanged.
* Original authors / copyright: Jon Crall, Claude Opus 4.8; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

public section

open scoped Matrix ENNReal
open MeasureTheory

namespace TauCeti

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

/-- **Entrywise concentration (union bound).**  If each entry of `Shat(ω) − A` has
mean-square `≤ v`, then the probability that *some* entry exceeds `η` in absolute
value is at most `n² v / η²`. -/
theorem measure_exists_entry_gt_le
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Shat : Ω → Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hint : ∀ k l, Integrable (fun ω => (Shat ω k l - A k l) ^ 2) P)
    {v η : ℝ} (hη : 0 < η) (hmoment : ∀ k l, ∫ ω, (Shat ω k l - A k l) ^ 2 ∂P ≤ v) :
    P {ω | ∃ k l, η < |Shat ω k l - A k l|}
      ≤ ENNReal.ofReal ((n : ℝ) ^ 2 * v / η ^ 2) := by
  -- per-entry Chebyshev: P{η < |Shat_{kl} − A_{kl}|} ≤ v / η²
  have hcheb : ∀ k l : Fin n,
      P {ω | η < |Shat ω k l - A k l|} ≤ ENNReal.ofReal (v / η ^ 2) := by
    intro k l
    have hint' : Integrable (fun ω => |Shat ω k l - A k l| ^ 2) P := by
      simpa [sq_abs] using hint k l
    have hmoment' : ∫ ω, |Shat ω k l - A k l| ^ 2 ∂P ≤ v := by
      simpa [sq_abs] using hmoment k l
    exact meas_gt_le_ofReal_integral_sq_div_sq P hint' hη hmoment'
  -- the bad event is the finite union over entries
  have hsub : {ω | ∃ k l, η < |Shat ω k l - A k l|}
      = ⋃ k : Fin n, ⋃ l : Fin n, {ω | η < |Shat ω k l - A k l|} := by
    ext ω; simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [hsub]
  calc P (⋃ k : Fin n, ⋃ l : Fin n, {ω | η < |Shat ω k l - A k l|})
      ≤ ∑ k : Fin n, P (⋃ l : Fin n, {ω | η < |Shat ω k l - A k l|}) :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ k : Fin n, ∑ l : Fin n, P {ω | η < |Shat ω k l - A k l|} :=
        Finset.sum_le_sum fun k _ => measure_iUnion_fintype_le _ _
    _ ≤ ∑ _k : Fin n, ∑ _l : Fin n, ENNReal.ofReal (v / η ^ 2) :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hcheb k l
    _ = ENNReal.ofReal ((n : ℝ) ^ 2 * v / η ^ 2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        simp only [← ENNReal.ofReal_natCast]
        rw [← ENNReal.ofReal_mul (Nat.cast_nonneg n), ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
        congr 1; ring

/-- **The some-entry-far event is measurable.**

It is a finite union over entries of `{η < |Ŝ k l − A k l|}`, each measurable
because the entry is.  Both concentration theorems below opened with this same
seven-line block, differing only in the name they gave the union step. -/
theorem measurableSet_exists_entry_gt {Shat : Ω → Matrix (Fin n) (Fin n) ℝ}
    {A : Matrix (Fin n) (Fin n) ℝ} {η : ℝ}
    (hmeas : ∀ k l, Measurable (fun ω => Shat ω k l)) :
    MeasurableSet {ω | ∃ k l, η < |Shat ω k l - A k l|} := by
  have hunion : {ω | ∃ k l, η < |Shat ω k l - A k l|}
      = ⋃ k : Fin n, ⋃ l : Fin n, {ω | η < |Shat ω k l - A k l|} := by
    ext ω; simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [hunion]
  refine MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun l => ?_
  exact measurableSet_lt measurable_const
    (continuous_abs.measurable.comp ((hmeas k l).sub measurable_const))

/-- **Eigenvalue concentration of a random Hermitian matrix.**  With probability
`≥ 1 − n² v / η²`, every eigenvalue of `Shat(ω)` is within `n · η` of the
corresponding eigenvalue of `A`. -/
theorem measure_forall_abs_eigenvalues₀_sub_le_ge
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Shat : Ω → Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hSherm : ∀ ω, (Shat ω).IsHermitian) (hAherm : A.IsHermitian)
    (hmeas : ∀ k l, Measurable (fun ω => Shat ω k l))
    (hint : ∀ k l, Integrable (fun ω => (Shat ω k l - A k l) ^ 2) P)
    {v η : ℝ} (hη : 0 < η) (hmoment : ∀ k l, ∫ ω, (Shat ω k l - A k l) ^ 2 ∂P ≤ v) :
    P {ω | ∀ k : Fin (Fintype.card (Fin n)),
        |(hSherm ω).eigenvalues₀ k - hAherm.eigenvalues₀ k| ≤ (n : ℝ) * η}
      ≥ 1 - ENNReal.ofReal ((n : ℝ) ^ 2 * v / η ^ 2) := by
  -- the good (all-entries-close) event is contained in the eigenvalue event
  have hcontain :
      {ω | ∀ k l : Fin n, |Shat ω k l - A k l| ≤ η}
        ⊆ {ω | ∀ k : Fin (Fintype.card (Fin n)),
            |(hSherm ω).eigenvalues₀ k - hAherm.eigenvalues₀ k| ≤ (n : ℝ) * η} := by
    intro ω hω k
    exact Matrix.abs_eigenvalues₀_sub_le_of_entry_le hAherm (hSherm ω)
      (fun i j => by simpa only [Real.norm_eq_abs] using hω i j) k
  -- the bad (some-entry-far) event, bounded above
  have hbad : P {ω | ∃ k l, η < |Shat ω k l - A k l|}
      ≤ ENNReal.ofReal ((n : ℝ) ^ 2 * v / η ^ 2) :=
    measure_exists_entry_gt_le P Shat A hint hη hmoment
  -- the good event is the complement of the bad event, and is measurable
  have hbad_meas : MeasurableSet {ω | ∃ k l, η < |Shat ω k l - A k l|} := by
    have : {ω | ∃ k l, η < |Shat ω k l - A k l|}
        = ⋃ k : Fin n, ⋃ l : Fin n, {ω | η < |Shat ω k l - A k l|} := by
      ext ω; simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    rw [this]
    refine MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun l => ?_
    exact measurableSet_lt measurable_const
      (continuous_abs.measurable.comp ((hmeas k l).sub measurable_const))
  have hcompl : {ω | ∀ k l : Fin n, |Shat ω k l - A k l| ≤ η}
      = {ω | ∃ k l, η < |Shat ω k l - A k l|}ᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_exists, not_lt]
  have hgood : 1 - ENNReal.ofReal ((n : ℝ) ^ 2 * v / η ^ 2)
      ≤ P {ω | ∀ k l : Fin n, |Shat ω k l - A k l| ≤ η} := by
    rw [hcompl, prob_compl_eq_one_sub hbad_meas]
    exact tsub_le_tsub_left hbad 1
  exact le_trans hgood (measure_mono hcontain)

/-- **Eigenvalue lower bound for a random Hermitian matrix.**  With probability
`≥ 1 − n² v / η²`, every eigenvalue of `Shat(ω)` is at least the corresponding
eigenvalue of `A` minus `n · η`.  (Take `η := c / (2n)` to keep a top-block
eigenvalue floored at `c` above `c / 2`.) -/
theorem measure_forall_eigenvalues₀_ge_ge
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Shat : Ω → Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hSherm : ∀ ω, (Shat ω).IsHermitian) (hAherm : A.IsHermitian)
    (hmeas : ∀ k l, Measurable (fun ω => Shat ω k l))
    (hint : ∀ k l, Integrable (fun ω => (Shat ω k l - A k l) ^ 2) P)
    {v η : ℝ} (hη : 0 < η) (hmoment : ∀ k l, ∫ ω, (Shat ω k l - A k l) ^ 2 ∂P ≤ v) :
    P {ω | ∀ k : Fin (Fintype.card (Fin n)),
        hAherm.eigenvalues₀ k - (n : ℝ) * η ≤ (hSherm ω).eigenvalues₀ k}
      ≥ 1 - ENNReal.ofReal ((n : ℝ) ^ 2 * v / η ^ 2) := by
  refine le_trans
    (measure_forall_abs_eigenvalues₀_sub_le_ge P Shat A hSherm hAherm hmeas hint hη hmoment)
    (measure_mono ?_)
  intro ω hω k
  have hk := abs_le.mp (hω k)
  linarith [hk.1]

/-- **Operator-norm deviation of a random matrix.**  With probability
`≥ 1 − n² v / η²`, the perturbation `Shat(ω) − A` has Euclidean operator norm at most
`n · η`, in the pointwise form `‖(Shat ω − A) x‖ ≤ n η ‖x‖`.

**No symmetry hypothesis**, deliberately: an operator-norm bound needs none, and dropping it
here is what lets a Davis--Kahan application consume this event after discharging symmetry
elsewhere.  Contrast `measure_forall_abs_eigenvalues₀_sub_le_ge`, which needs both matrices
Hermitian in order to have eigenvalues at all.

**This is a sibling of that theorem, not a corollary of it.**  Eigenvalue closeness does not
bound an operator-norm difference — two matrices can have identical spectra and differ by a
rotation.  Both descend from the same entrywise event `measure_exists_entry_gt_le`, one through
Weyl's inequality and this one through `norm_toEuclideanLin_le_of_entry_le`, so the probability
`1 − n² v / η²` is literally the same number rather than two coincidentally equal bounds.

The route is elementary — Chebyshev plus a union bound — and costs a factor `n` entrywise-to-
operator and `n²` from the union bound.  **The bound is not sharp in the dimension**: a matrix
Bernstein inequality would give `log n` dependence, at the price of matrix Laplace-transform
machinery Mathlib does not have.  Nothing downstream may treat the `n`-dependence as intrinsic. -/
theorem measure_forall_norm_toEuclideanLin_sub_le_ge
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Shat : Ω → Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hmeas : ∀ k l, Measurable (fun ω => Shat ω k l))
    (hint : ∀ k l, Integrable (fun ω => (Shat ω k l - A k l) ^ 2) P)
    {v η : ℝ} (hη : 0 < η) (hmoment : ∀ k l, ∫ ω, (Shat ω k l - A k l) ^ 2 ∂P ≤ v) :
    P {ω | ∀ x : EuclideanSpace ℝ (Fin n),
        ‖Matrix.toEuclideanLin (Shat ω - A) x‖ ≤ (n : ℝ) * η * ‖x‖}
      ≥ 1 - ENNReal.ofReal ((n : ℝ) ^ 2 * v / η ^ 2) := by
  -- the good (all-entries-close) event is contained in the operator-norm event
  have hcontain :
      {ω | ∀ k l : Fin n, |Shat ω k l - A k l| ≤ η}
        ⊆ {ω | ∀ x : EuclideanSpace ℝ (Fin n),
            ‖Matrix.toEuclideanLin (Shat ω - A) x‖ ≤ (n : ℝ) * η * ‖x‖} := by
    intro ω hω x
    exact norm_toEuclideanLin_le_of_entry_le (fun i j => by simpa using hω i j) x
  -- the bad (some-entry-far) event, bounded above by the shared entrywise estimate
  have hbad : P {ω | ∃ k l, η < |Shat ω k l - A k l|}
      ≤ ENNReal.ofReal ((n : ℝ) ^ 2 * v / η ^ 2) :=
    measure_exists_entry_gt_le P Shat A hint hη hmoment
  have hbad_meas : MeasurableSet {ω | ∃ k l, η < |Shat ω k l - A k l|} :=
    measurableSet_exists_entry_gt hmeas
  have hcompl : {ω | ∀ k l : Fin n, |Shat ω k l - A k l| ≤ η}
      = {ω | ∃ k l, η < |Shat ω k l - A k l|}ᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_exists, not_lt]
  have hgood : 1 - ENNReal.ofReal ((n : ℝ) ^ 2 * v / η ^ 2)
      ≤ P {ω | ∀ k l : Fin n, |Shat ω k l - A k l| ≤ η} := by
    rw [hcompl, prob_compl_eq_one_sub hbad_meas]
    exact tsub_le_tsub_left hbad 1
  exact le_trans hgood (measure_mono hcontain)

end TauCeti
