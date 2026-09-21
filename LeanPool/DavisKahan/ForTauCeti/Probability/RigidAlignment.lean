/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5

Staged for Tau Ceti, roadmap topic T04.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track — the probabilistic companion of the rigid-motion
rigidity in `ForTauCeti/Analysis/InnerProductSpace/Gram/Matrix.lean`.

Formalized by Claude Opus 5 (claude-opus-5[1m]).
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Gram.Matrix
public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Alignment error converges in probability when pairwise distances do

A configuration is determined by its pairwise distances only up to a rigid motion, so a
distance-based estimator can be compared with a target only after alignment.  The deterministic
content of that comparison is `TauCeti.exists_delta_alignmentError_le`: one modulus `δ` serves
every pair of configurations whose target has diameter at most `D`.

Because the modulus does not depend on the configurations, it transfers to random ones.  That is
this file's theorem: if the pairwise distances of a sequence of random configurations converge
in probability to those of a random target, then the alignment error converges in probability
to zero.  The target's diameter is random and unbounded, and is handled by tightness — the only
place measurability of the target is used.

No spectral hypothesis appears anywhere in the chain.  This matters: the standard route from
distances to coordinates goes through a spectral embedding and an eigenvalue perturbation bound,
which needs an eigengap that the statement being proved never mentions.
-/

public section

namespace TauCeti

open Filter MeasureTheory
open scoped Topology ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

section

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
variable {κ : Type*} [Finite κ] [Nonempty κ]

/-- The event that the target configuration has diameter exceeding `M`. -/
private def largeDiam (ψ : Ω → κ → G) (M : ℕ) : Set Ω :=
  {ω | ¬ ∀ i j, ‖ψ ω i - ψ ω j‖ ≤ (M : ℝ)}

omit [InnerProductSpace ℝ G] [FiniteDimensional ℝ G] in
/-- A random configuration is tight: its diameter exceeds `M` with probability tending to `0`.
This is the only use of measurability of the target. -/
private theorem tendsto_measure_largeDiam (P : Measure Ω) [IsFiniteMeasure P]
    (ψ : Ω → κ → G) (hψ : ∀ i j, Measurable fun ω => ‖ψ ω i - ψ ω j‖) :
    Tendsto (fun M => P (largeDiam ψ M)) atTop (𝓝 0) := by
  classical
  have hmeas : ∀ M, MeasurableSet (largeDiam ψ M) := by
    intro M
    have hrw : largeDiam ψ M = ⋃ i, ⋃ j, {ω | (M : ℝ) < ‖ψ ω i - ψ ω j‖} := by
      ext ω; simp [largeDiam, not_forall, not_le]
    rw [hrw]
    exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j =>
      measurableSet_lt measurable_const (hψ i j)
  have hanti : Antitone (largeDiam ψ) := by
    intro M M' hMM' ω hω
    simp only [largeDiam, Set.mem_ofPred_eq, not_forall] at hω ⊢
    obtain ⟨i, j, hij⟩ := hω
    refine ⟨i, j, fun hle => hij (le_trans hle ?_)⟩
    exact_mod_cast hMM'
  have hempty : (⋂ M, largeDiam ψ M) = ∅ := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
    intro hω
    let _ : Fintype κ := Fintype.ofFinite κ
    obtain ⟨M, hM⟩ := exists_nat_ge
      (Finset.univ.sup' Finset.univ_nonempty fun p : κ × κ => ‖ψ ω p.1 - ψ ω p.2‖)
    refine (hω M) fun i j => le_trans ?_ hM
    exact Finset.le_sup' (fun p : κ × κ => ‖ψ ω p.1 - ψ ω p.2‖) (Finset.mem_univ (i, j))
  have hlim := tendsto_measure_iInter_atTop (μ := P)
    (fun M => (hmeas M).nullMeasurableSet) hanti ⟨0, measure_ne_top P _⟩
  rw [hempty, measure_empty] at hlim
  exact hlim

/-- **The alignment error converges in probability when the pairwise distances do.**

`φ u` is a sequence of random configurations and `ψ` a random target.  The hypothesis is that,
for every tolerance, the probability that some pairwise distance of `φ u` differs from the
corresponding distance of `ψ` by more than that tolerance tends to zero.  The conclusion is that
the least uniform distance from `φ u` to `ψ` achievable by a rigid motion tends to zero in
probability.

Only `ψ` is required to be measurable, and only to know that its diameter is tight; the
estimates `φ u` need no measurability at all, since the sets whose measure is bounded are
handled by monotonicity and subadditivity of the measure. -/
theorem tendsto_measure_alignmentError_gt (P : Measure Ω) [IsFiniteMeasure P]
    (φ : ℕ → Ω → κ → G) (ψ : Ω → κ → G)
    (hψ : ∀ i j, Measurable fun ω => ‖ψ ω i - ψ ω j‖)
    (hdist : ∀ δ > (0 : ℝ), Tendsto
      (fun u => P {ω | ¬ ∀ i j, |‖φ u ω i - φ u ω j‖ - ‖ψ ω i - ψ ω j‖| ≤ δ}) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun u => P {ω | ε < alignmentError (ψ ω) (φ u ω)}) atTop (𝓝 0) := by
  classical
  rw [ENNReal.tendsto_atTop_zero]
  intro η hη
  -- tightness of the target's diameter
  obtain ⟨M, hM⟩ : ∃ M : ℕ, P (largeDiam ψ M) ≤ η / 2 := by
    have h2 : (0 : ℝ≥0∞) < η / 2 := ENNReal.half_pos hη.ne'
    obtain ⟨M, hM⟩ := (ENNReal.tendsto_atTop_zero.mp
      (tendsto_measure_largeDiam P ψ hψ)) (η / 2) h2
    exact ⟨M, hM M le_rfl⟩
  -- the uniform modulus, which does not depend on the sample
  obtain ⟨δ, hδpos, hδ⟩ := exists_delta_alignmentError_le (F := G) (ι := κ) (M : ℝ) hε
  obtain ⟨N, hN⟩ := (ENNReal.tendsto_atTop_zero.mp (hdist δ hδpos)) (η / 2)
    (ENNReal.half_pos hη.ne')
  refine ⟨N, fun u hu => ?_⟩
  have hsub : {ω | ε < alignmentError (ψ ω) (φ u ω)} ⊆
      largeDiam ψ M ∪ {ω | ¬ ∀ i j, |‖φ u ω i - φ u ω j‖ - ‖ψ ω i - ψ ω j‖| ≤ δ} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, not_or] at hcon
    obtain ⟨h1, h2⟩ := hcon
    simp only [largeDiam, Set.mem_ofPred_eq, not_not] at h1
    simp only [Set.mem_ofPred_eq, not_not] at h2
    exact absurd (hδ (φ u ω) (ψ ω) h1 h2) (not_le.mpr hω)
  calc P {ω | ε < alignmentError (ψ ω) (φ u ω)}
      ≤ P (largeDiam ψ M ∪
          {ω | ¬ ∀ i j, |‖φ u ω i - φ u ω j‖ - ‖ψ ω i - ψ ω j‖| ≤ δ}) := measure_mono hsub
    _ ≤ P (largeDiam ψ M) +
          P {ω | ¬ ∀ i j, |‖φ u ω i - φ u ω j‖ - ‖ψ ω i - ψ ω j‖| ≤ δ} := measure_union_le _ _
    _ ≤ η / 2 + η / 2 := add_le_add hM (hN u hu)
    _ = η := ENNReal.add_halves η

end

end TauCeti
