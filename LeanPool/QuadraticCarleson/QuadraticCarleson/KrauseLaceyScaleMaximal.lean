/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyPositiveCorrelation

/-!
# The fixed-scale endpoint in Krause--Lacey Proposition 4.1

This module proves the `L∞ → L∞` endpoint paired with the oscillatory
`L² → L²` estimate in the proof of KL18 Proposition 4.1.  The kernel's
`L¹` mass is bounded directly from the concrete dyadic cutoff.  At a fixed
scale, the localized outputs have disjoint parent supports, so at most one
summand contributes at any point.

Mathlib currently has no Riesz--Thorin or Marcinkiewicz operator
interpolation theorem in its `MemLp` API.  Accordingly this file proves both
actual endpoints but does not introduce the desired intermediate `L^q`
operator estimate as a hypothesis.
-/

open Function MeasureTheory Set
open scoped ENNReal NNReal ComplexConjugate

namespace QuadraticCarleson


/-- The concrete positive-half unit-quadratic kernel has uniformly bounded
`L¹` action on bounded inputs.  This is the trivial endpoint immediately
following the oscillatory estimate (2.4) in KL18. -/
theorem norm_krauseLaceyLocalizedPiece_le
    (j : ℤ) (I : RealInterval) (f : ℝ → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ t, ‖f t‖ ≤ M) (x : ℝ) :
    ‖krauseLaceyLocalizedPiece 1 j I f x‖ ≤
      positiveDyadicAmplitudeBound * M := by
  let R : ℝ := (2 : ℝ) ^ (j - 1)
  let s : Set ℝ := Icc (R / 4) R
  let F : ℝ → ℂ := fun y ↦
    positiveDyadicAmplitude j y * phase (y ^ 2) *
      I.centralThird.indicator f (x - y)
  have hR : 0 < R := by dsimp [R]; positivity
  have hD : 0 ≤ positiveDyadicAmplitudeBound := positiveDyadicAmplitudeBound_nonneg
  have hzero (y : ℝ) (hy : y ∉ s) : F y = 0 := by
    have ha : positiveDyadicAmplitude j y = 0 := by
      by_contra hn
      exact hy (positiveDyadicAmplitude_support_subset j hn)
    simp [F, ha]
  have hid : krauseLaceyLocalizedPiece 1 j I f x = ∫ y in s, F y := by
    unfold krauseLaceyLocalizedPiece
    simp only [one_mul]
    change (∫ y, F y) = _
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
  have hpoint (y : ℝ) (hy : y ∈ s) :
      ‖F y‖ ≤ (positiveDyadicAmplitudeBound / R) * M := by
    have ha := norm_positiveDyadicAmplitude_le j y
    have hi : ‖I.centralThird.indicator f (x - y)‖ ≤ M := by
      by_cases hm : x - y ∈ I.centralThird
      · simpa [Set.indicator_of_mem hm] using hf (x - y)
      · simp [Set.indicator_of_notMem hm, hM]
    calc
      ‖F y‖ = ‖positiveDyadicAmplitude j y‖ *
          ‖I.centralThird.indicator f (x - y)‖ := by
        simp only [F, norm_mul, norm_phase, mul_one]
      _ ≤ (positiveDyadicAmplitudeBound / R) * M :=
        mul_le_mul ha hi (norm_nonneg _) (div_nonneg hD hR.le)
  have hset := norm_setIntegral_le_of_norm_le_const
    (μ := volume)
    (f := F) (s := s) (C := (positiveDyadicAmplitudeBound / R) * M)
    (isCompact_Icc.measure_lt_top) hpoint
  have hvol : volume.real s = 3 * R / 4 := by
    dsimp [s]
    simp only [Measure.real, Real.volume_Icc]
    rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ R - R / 4)]
    ring
  rw [hid]
  calc
    ‖∫ y in s, F y‖ ≤
        (positiveDyadicAmplitudeBound / R) * M * volume.real s := hset
    _ = (positiveDyadicAmplitudeBound * M) * (3 / 4) := by
      rw [hvol]
      field_simp
    _ ≤ positiveDyadicAmplitudeBound * M := by
      have hDM : 0 ≤ positiveDyadicAmplitudeBound * M := mul_nonneg hD hM
      nlinarith

/-- Fixed-scale localized `L∞` endpoint.  The exact scale relation supplies
support in each parent interval, and pairwise-disjoint parents ensure that at
most one localized output is nonzero at a point. -/
theorem norm_krauseLaceyFixedScaleLocalizedSum_le
    (j : ℤ) (S : Finset RealInterval) (f : ℝ → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ t, ‖f t‖ ≤ M)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (j + 2))
    (hdisj : Set.Pairwise (↑S : Set RealInterval)
      (Disjoint on fun I : RealInterval ↦ I.carrier)) (x : ℝ) :
    ‖krauseLaceyFixedScaleLocalizedSum j S f x‖ ≤
      positiveDyadicAmplitudeBound * M := by
  classical
  by_cases hex : ∃ I ∈ S, krauseLaceyLocalizedPiece 1 j I f x ≠ 0
  · rcases hex with ⟨I, hIS, hIx⟩
    have hxI : x ∈ I.carrier :=
      krauseLaceyLocalizedPiece_support_subset 1 j I f (hscale I hIS) hIx
    have hsum : krauseLaceyFixedScaleLocalizedSum j S f x =
        krauseLaceyLocalizedPiece 1 j I f x := by
      unfold krauseLaceyFixedScaleLocalizedSum
      rw [Finset.sum_eq_single I]
      · intro J hJS hJI
        apply krauseLaceyLocalizedPiece_eq_zero_of_notMem 1 j J f (hscale J hJS)
        intro hxJ
        exact Set.disjoint_left.1 (hdisj hIS hJS hJI.symm) hxI hxJ
      · intro hn
        exact (hn hIS).elim
    rw [hsum]
    exact norm_krauseLaceyLocalizedPiece_le j I f hM hf x
  · have hzero : krauseLaceyFixedScaleLocalizedSum j S f x = 0 := by
      unfold krauseLaceyFixedScaleLocalizedSum
      apply Finset.sum_eq_zero
      intro I hIS
      by_contra hn
      exact hex ⟨I, hIS, hn⟩
    rw [hzero, norm_zero]
    exact mul_nonneg positiveDyadicAmplitudeBound_nonneg hM

/-- Finite maximum of fixed-scale localized outputs.  This is useful for
finite approximations, while KL18's actual maximal truncation additionally
requires control of partial sums across scales. -/
noncomputable def krauseLaceyFiniteScaleMaximal
    {n : ℕ} (j : Fin (n + 1) → ℤ) (S : Fin (n + 1) → Finset RealInterval)
    (f : ℝ → ℂ) (x : ℝ) : ℝ :=
  ⨆ i, ‖krauseLaceyFixedScaleLocalizedSum (j i) (S i) f x‖

theorem krauseLaceyFiniteScaleMaximal_le
    {n : ℕ} (j : Fin (n + 1) → ℤ) (S : Fin (n + 1) → Finset RealInterval)
    (f : ℝ → ℂ) {M : ℝ} (hM : 0 ≤ M) (hf : ∀ t, ‖f t‖ ≤ M)
    (hscale : ∀ i I, I ∈ S i → I.length = (2 : ℝ) ^ (j i + 2))
    (hdisj : ∀ i, Set.Pairwise (↑(S i) : Set RealInterval)
      (Disjoint on fun I : RealInterval ↦ I.carrier)) (x : ℝ) :
    krauseLaceyFiniteScaleMaximal j S f x ≤ positiveDyadicAmplitudeBound * M := by
  unfold krauseLaceyFiniteScaleMaximal
  apply ciSup_le
  intro i
  exact norm_krauseLaceyFixedScaleLocalizedSum_le (j i) (S i) f hM hf
    (fun I hI ↦ hscale i I hI) (hdisj i) x

/-- The two rigorously available endpoints for the fixed-scale operator,
packaged in the exact form preceding interpolation in KL18 Proposition 4.1.
The first component is the trivial `L∞` endpoint; the second is the
oscillatory squared-`L²` endpoint from (2.4). -/
theorem krauseLaceyFixedScale_endpoints
    (j : ℤ) (S : Finset RealInterval) {f : ℝ → ℂ} (hf2 : MemLp f 2)
    {M : ℝ} (hM : 0 ≤ M) (hfTop : ∀ t, ‖f t‖ ≤ M)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (j + 2))
    (hdisj : Set.Pairwise (↑S : Set RealInterval)
      (Disjoint on fun I : RealInterval ↦ I.carrier)) :
    (∀ x, ‖krauseLaceyFixedScaleLocalizedSum j S f x‖ ≤
        positiveDyadicAmplitudeBound * M) ∧
      (let R := (2 : ℝ) ^ (j - 1)
       (∫⁻ x, ‖krauseLaceyFixedScaleLocalizedSum j S f x‖ₑ ^ 2) ≤
        ENNReal.ofReal
          (2218647684 * positiveDyadicAmplitudeBound ^ 2 / R) *
            ∫⁻ x, ‖f x‖ₑ ^ 2) := by
  constructor
  · intro x
    exact norm_krauseLaceyFixedScaleLocalizedSum_le j S f hM hfTop hscale hdisj x
  · have hthird : Set.Pairwise (↑S : Set RealInterval)
        (Disjoint on fun I : RealInterval ↦ I.centralThird) := by
      intro I hIS J hJS hIJ
      exact (hdisj hIS hJS hIJ).mono
        I.centralThird_subset_carrier J.centralThird_subset_carrier
    exact krauseLaceyFixedScaleLocalizedSum_sq_lintegral_le_of_disjoint
      j S hf2 hthird

end QuadraticCarleson
