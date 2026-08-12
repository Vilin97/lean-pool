/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.Convergence.NesterovConvergence
import LeanPool.PLAcceleratedNesterovLean.Core.EmbeddedManifold


/-!
# Internal Assembly for the Main Theorem

This file contains helper statements used by `PLAcceleratedNesterovLean.MainTheorem`.  The public
file intentionally exposes only the clean top-level theorem.
-/

noncomputable section

namespace PLAcceleratedNesterovLean

open scoped Topology NNReal
open Manifold


/-! ## Shared packaging helpers -/

/-- Extend the nearest-point projection on a tubular neighborhood to a total
function.  Outside `U` we choose an arbitrary point of `S`; all theorem
statements only use the metric projection property inside `U`. -/
private theorem exists_total_nearest_projection
    {d : ℕ} {S U : Set (E d)}
    (hTub : IsTubularNeighborhoodOfSubmanifold S U)
    (hS_ne : S.Nonempty) :
    ∃ π : E d → E d,
      (∀ x ∈ U, π x ∈ S ∧ dist x (π x) = Metric.infDist x S) ∧
      (∀ x ∈ S, π x = x) ∧
      (∀ x, π x ∈ S) := by
  classical
  refine ⟨fun x => if hx : x ∈ U then (hTub.uniqueProj x hx).choose else hS_ne.some,
    ?_, ?_, ?_⟩
  · intro x hx
    dsimp only
    rw [dite_eq_left hx]
    exact (hTub.uniqueProj x hx).choose_spec.1
  · intro x hxS
    dsimp only
    have hxU : x ∈ U := hTub.subset hxS
    rw [dite_eq_left hxU]
    have hself : x ∈ S ∧ dist x x = Metric.infDist x S :=
      ⟨hxS, by rw [dist_self]; exact (Metric.infDist_zero_of_mem hxS).symm⟩
    exact ((hTub.uniqueProj x hxU).choose_spec.2 x hself).symm
  · intro x
    dsimp only
    by_cases hx : x ∈ U
    · rw [dite_eq_left hx]
      exact (hTub.uniqueProj x hx).choose_spec.1.1
    · rw [dite_eq_right hx]
      exact hS_ne.some_mem

/-- At every global minimizer, the gradient vanishes. -/
private theorem gradient_eq_zero_on_argmin
    {d : ℕ} {f : E d → ℝ} {S : Set (E d)}
    (hS_argmin : S = argminSet f) :
    ∀ x ∈ S, gradient f x = 0 := by
  intro x hx
  have hmin : ∀ y, f x ≤ f y := by
    have h := hx
    rw [hS_argmin] at h
    exact h
  have hlocmin : IsLocalMin f x := Filter.Eventually.of_forall hmin
  simp only [gradient, hlocmin.fderiv_eq_zero, map_zero]

/-- If the gradient vanishes at a zero-velocity state, one Nesterov step is
stationary. -/
private lemma nesterovStep_at_zero_grad
    {d : ℕ} {f : E d → ℝ} {η ρ : ℝ} {x : E d}
    (hg : gradient f x = 0) :
    nesterovStep f η ρ ⟨x, 0⟩ = ⟨x, 0⟩ := by
  simp only [nesterovStep, NesterovState.lookahead, hg, smul_zero, sub_zero,
    add_zero, sub_self]

/-- A zero-gradient zero-velocity start remains stationary for all Nesterov
iterates. -/
private lemma nesterovSeqGen_at_zero_grad
    {d : ℕ} {f : E d → ℝ} {η ρ : ℝ} {x : E d}
    (hg : gradient f x = 0) :
    ∀ k, nesterovSeqGen f η ρ ⟨x, 0⟩ k = ⟨x, 0⟩ := by
  intro k
  induction k with
  | zero => rfl
  | succ n ih =>
      simp only [nesterovSeqGen, ih]
      exact nesterovStep_at_zero_grad hg

/-- The lookahead is also stationary from a zero-gradient zero-velocity start. -/
private lemma nesterovSeqGen_lookahead_at_zero_grad
    {d : ℕ} {f : E d → ℝ} {η ρ : ℝ} {x : E d}
    (hg : gradient f x = 0) :
    ∀ k, (nesterovSeqGen f η ρ ⟨x, 0⟩ k).lookahead η = x := by
  intro k
  simp only [nesterovSeqGen_at_zero_grad hg k, NesterovState.lookahead, smul_zero,
    add_zero]

/-- With zero step size, zero-velocity starts are stationary for any momentum. -/
private lemma nesterovSeqGen_zero_eta
    {d : ℕ} {f : E d → ℝ} {ρ : ℝ} {x : E d} :
    ∀ k, nesterovSeqGen f 0 ρ ⟨x, 0⟩ k = ⟨x, 0⟩ := by
  intro k
  induction k with
  | zero => rfl
  | succ n ih =>
      simp only [nesterovSeqGen, ih, nesterovStep, NesterovState.lookahead,
        Real.sqrt_zero, zero_smul, smul_zero, add_zero, sub_zero]

/-- In zero ambient dimension, zero-velocity Nesterov starts are stationary. -/
private lemma nesterovSeqGen_zero_dim
    {f : E 0 → ℝ} {η ρ : ℝ} {x : E 0} :
    ∀ k, nesterovSeqGen f η ρ ⟨x, 0⟩ k = ⟨x, 0⟩ := by
  intro k
  induction k with
  | zero => rfl
  | succ n ih =>
      simp only [nesterovSeqGen, ih, nesterovStep, NesterovState.lookahead]
      have hg : gradient f x = 0 := Subsingleton.elim _ _
      simp [hg]

/-- A local non-minimizer near a minimizer forces the PL and Lipschitz constants
to satisfy the compatibility bound `μ ≤ L`. -/
private theorem mu_le_L_of_pl_descent_near
    {d : ℕ} {f : E d → ℝ} {μ : ℝ} {L : ℝ≥0}
    (hL : 0 < (L : ℝ))
    {U : Set (E d)}
    (hPL : PolyakLojasiewicz f μ U)
    (hf_diff : DifferentiableOn ℝ f U)
    (hf_lip : LipschitzOnWith (↑L) (gradient f) U)
    {m : E d} (hm : m ∈ argminSet f)
    {r : ℝ} (hr : 0 < r) (hball : Metric.ball m r ⊆ U)
    {y : E d} (hy : y ∈ Metric.ball m (r / 3)) (hfy : f y ≠ fStar f) :
    μ ≤ ↑L := by
  have hy_dist : dist y m < r / 3 := hy
  have hy_in_ball : y ∈ Metric.ball m r :=
    Metric.ball_subset_ball (by linarith) hy
  have hyU : y ∈ U := hball hy_in_ball
  have hbdd : BddBelow (Set.range f) :=
    ⟨f m, by rintro _ ⟨z, rfl⟩; exact hm z⟩
  have hfstar_le : ∀ z, fStar f ≤ f z := fun z => ciInf_le hbdd z
  have hfy_pos : fStar f < f y := lt_of_le_of_ne (hfstar_le y) (Ne.symm hfy)
  have hgrad_m : gradient f m = 0 :=
    (gradient_eq_zero_on_argmin rfl) m hm
  have hgrad_bound : ‖gradient f y‖ ≤ (L : ℝ) * dist y m := by
    have := hf_lip.dist_le_mul y hyU m (hball (Metric.mem_ball_self hr))
    rwa [hgrad_m, dist_zero_right] at this
  set η := (1 : ℝ) / (L : ℝ) with hη_def
  have hη_pos : 0 < η := by positivity
  have hstep_le : η * ‖gradient f y‖ ≤ dist y m := by
    have h1 : η * ‖gradient f y‖ ≤ η * ((L : ℝ) * dist y m) := by
      exact mul_le_mul_of_nonneg_left hgrad_bound hη_pos.le
    have h2 : η * ((L : ℝ) * dist y m) = dist y m := by
      rw [hη_def]
      field_simp
    linarith
  have hseg : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      y + t • (-(η • gradient f y)) ∈ Metric.ball m r := by
    intro t ht0 ht1
    rw [Metric.mem_ball]
    calc dist (y + t • (-(η • gradient f y))) m
        = ‖y + t • (-(η • gradient f y)) - m‖ := dist_eq_norm _ _
      _ = ‖(y - m) + t • (-(η • gradient f y))‖ := by congr 1; abel
      _ ≤ ‖y - m‖ + ‖t • (-(η • gradient f y))‖ := norm_add_le _ _
      _ ≤ ‖y - m‖ + η * ‖gradient f y‖ := by
          gcongr
          rw [norm_smul, norm_neg, norm_smul, Real.norm_of_nonneg hη_pos.le]
          calc |t| * (η * ‖gradient f y‖)
              ≤ 1 * (η * ‖gradient f y‖) := by
                gcongr
                exact abs_le.mpr ⟨by linarith, ht1⟩
            _ = η * ‖gradient f y‖ := one_mul _
      _ ≤ dist y m + dist y m := by
          have := (dist_eq_norm y m).symm
          linarith [hstep_le]
      _ < r / 3 + r / 3 := by linarith
      _ < r := by linarith
  have hdesc := lsmooth_descent_at f L hL Metric.isOpen_ball
    (hf_diff.mono hball) (hf_lip.mono hball) y hy_in_ball hseg η hη_def
  have hfstar_desc := hfstar_le (y - η • gradient f y)
  have h_upper : ‖gradient f y‖ ^ 2 ≤ 2 * (L : ℝ) * (f y - fStar f) := by
    have h1 : η / 2 * ‖gradient f y‖ ^ 2 ≤ f y - fStar f := by linarith
    have h2 : (L : ℝ) * η = 1 := by
      rw [hη_def]
      field_simp
    calc ‖gradient f y‖ ^ 2
        = (L : ℝ) * η * ‖gradient f y‖ ^ 2 := by rw [h2, one_mul]
      _ = 2 * (L : ℝ) * (η / 2 * ‖gradient f y‖ ^ 2) := by ring
      _ ≤ 2 * (L : ℝ) * (f y - fStar f) := by
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have h_lower : ‖gradient f y‖ ^ 2 ≥ 2 * μ * (f y - fStar f) := hPL.2.2 y hyU
  have hgap_pos : (0 : ℝ) < f y - fStar f := by linarith
  by_contra h_not
  push Not at h_not
  linarith [mul_lt_mul_of_pos_right h_not
    (by linarith : (0 : ℝ) < 2 * (f y - fStar f))]

/-- Turn pointwise local convergence balls around `S` into one open
neighborhood of `S`. -/
private theorem open_neighborhood_from_local_balls
    {d : ℕ} {S U : Set (E d)} {P : E d → Prop}
    (hlocal : ∀ m ∈ S, ∃ α : ℝ, 0 < α ∧
      Metric.ball m α ⊆ U ∧
      ∀ x ∈ Metric.ball m α, P x) :
    ∃ Ū : Set (E d),
      IsOpen Ū ∧ S ⊆ Ū ∧ Ū ⊆ U ∧ ∀ x ∈ Ū, P x := by
  classical
  choose α hα using hlocal
  let α' : E d → ℝ := fun m => if hm : m ∈ S then α m hm else 1
  have hα'_spec : ∀ m (hm : m ∈ S), α' m = α m hm := by
    intro m hm
    simp only [α', dite_eq_left hm]
  refine ⟨⋃ m ∈ S, Metric.ball m (α' m), ?_, ?_, ?_, ?_⟩
  · exact isOpen_biUnion (fun m _ => Metric.isOpen_ball)
  · intro m hm
    have hpos : 0 < α' m := by
      simp_all
    exact Set.mem_biUnion hm (Metric.mem_ball_self hpos)
  · simp_all
  · intro x hx
    obtain ⟨m, hmS, hxm⟩ := Set.mem_iUnion₂.mp hx
    rw [hα'_spec m hmS] at hxm
    exact (hα m hmS).2.2 x hxm

/-- Degenerate zero-smoothness branch for the public theorem.  Since
`1 / L = 0`, the chosen Nesterov dynamics is stationary. -/
private theorem nesterov_pl_accelerated_rate_zero_L
    {d : ℕ}
    (L : ℝ≥0) (hL_zero : (L : ℝ) = 0)
    (μ ρ : ℝ) :
    ∀ (f : E d → ℝ),
    ∀ (n : ℕ),
    ∀ (M : Type*) [TopologicalSpace M] [ChartedSpace (ManifoldModel n) M]
       [Nonempty M]
      (ι : M → E d),
      IsSmoothEmbedding (modelI n) (modelWithCornersSelf ℝ (E d)) 2 ι →
      Set.range ι = argminSet f →
    ∀ (U : Set (E d)),
      IsOpen U →
      Set.range ι ⊆ U →
      ContDiffOn ℝ 2 f U →
      PolyakLojasiewicz f μ U →
      LipschitzOnWith (↑L) (gradient f) U →
    ∃ (Ū : Set (E d)),
      IsOpen Ū ∧ Set.range ι ⊆ Ū ∧ Ū ⊆ U ∧
      ∀ x₀ ∈ Ū,
        ∀ k,
          (nesterovSeqGen f (1 / ↑L) ρ ⟨x₀, 0⟩ k).x ∈ U ∧
          (nesterovSeqGen f (1 / ↑L) ρ ⟨x₀, 0⟩ k).lookahead
            (1 / ↑L) ∈ U ∧
          f ((nesterovSeqGen f (1 / ↑L) ρ ⟨x₀, 0⟩ k).x) - fStar f ≤
            2 * Real.exp (-(↑k / Real.sqrt (↑L / μ))) * (f x₀ - fStar f) := by
  intro f n M _ _ _ ι _hι hrange U hU_open hS_sub _hf_C2 _hPL _hf_lip
  refine ⟨U, hU_open, hS_sub, Set.Subset.rfl, ?_⟩
  intro x₀ hx₀
  have hη : (1 : ℝ) / (L : ℝ) = 0 := by
    simp_all
  have hseq : ∀ k, nesterovSeqGen f (1 / ↑L) ρ ⟨x₀, 0⟩ k = ⟨x₀, 0⟩ := by
    intro k
    rw [hη]
    exact nesterovSeqGen_zero_eta k
  have hS_ne : (Set.range ι).Nonempty := Set.range_nonempty ι
  obtain ⟨m, hmS⟩ := hS_ne
  have hm_argmin : m ∈ argminSet f := by
    simp_all
  have hbdd : BddBelow (Set.range f) :=
    ⟨f m, by rintro _ ⟨z, rfl⟩; exact hm_argmin z⟩
  intro k
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hseq k] using hx₀
  · have hseq0 : nesterovSeqGen f 0 ρ ⟨x₀, 0⟩ k = ⟨x₀, 0⟩ :=
      nesterovSeqGen_zero_eta k
    rw [hη]
    simpa [hseq0, NesterovState.lookahead] using hx₀
  · have hgap_nn : 0 ≤ f x₀ - fStar f :=
      sub_nonneg.mpr (ciInf_le hbdd x₀)
    have hrate :
        2 * Real.exp (-(↑k / Real.sqrt (↑L / μ))) * (f x₀ - fStar f) =
          2 * (f x₀ - fStar f) := by
      simp_all
    calc f ((nesterovSeqGen f (1 / ↑L) ρ ⟨x₀, 0⟩ k).x) - fStar f
        = f x₀ - fStar f := by simp only [hseq k]
      _ ≤ 2 * (f x₀ - fStar f) := by nlinarith
      _ = 2 * Real.exp (-(↑k / Real.sqrt (↑L / μ))) * (f x₀ - fStar f) :=
        hrate.symm

/-- Degenerate zero-dimensional branch for the public theorem. -/
private theorem nesterov_pl_accelerated_rate_zero_dim
    (L : ℝ≥0) (μ ρ : ℝ) :
    ∀ (f : E 0 → ℝ),
    ∀ (n : ℕ),
    ∀ (M : Type*) [TopologicalSpace M] [ChartedSpace (ManifoldModel n) M]
       [Nonempty M]
      (ι : M → E 0),
      IsSmoothEmbedding (modelI n) (modelWithCornersSelf ℝ (E 0)) 2 ι →
      Set.range ι = argminSet f →
    ∀ (U : Set (E 0)),
      IsOpen U →
      Set.range ι ⊆ U →
      ContDiffOn ℝ 2 f U →
      PolyakLojasiewicz f μ U →
      LipschitzOnWith (↑L) (gradient f) U →
    ∃ (Ū : Set (E 0)),
      IsOpen Ū ∧ Set.range ι ⊆ Ū ∧ Ū ⊆ U ∧
      ∀ x₀ ∈ Ū,
        ∀ k,
          (nesterovSeqGen f (1 / ↑L) ρ ⟨x₀, 0⟩ k).x ∈ U ∧
          (nesterovSeqGen f (1 / ↑L) ρ ⟨x₀, 0⟩ k).lookahead
            (1 / ↑L) ∈ U ∧
          f ((nesterovSeqGen f (1 / ↑L) ρ ⟨x₀, 0⟩ k).x) - fStar f ≤
            2 * Real.exp (-(↑k / Real.sqrt (↑L / μ))) * (f x₀ - fStar f) := by
  intro f n M _ _ _ ι _hι hrange U hU_open hS_sub _hf_C2 _hPL _hf_lip
  refine ⟨U, hU_open, hS_sub, Set.Subset.rfl, ?_⟩
  intro x₀ hx₀
  obtain ⟨m, hmS⟩ := Set.range_nonempty ι
  have hx₀_argmin : x₀ ∈ argminSet f := by
    have hx₀_eq_m : x₀ = m := Subsingleton.elim x₀ m
    simp_all
  have hbdd : BddBelow (Set.range f) :=
    ⟨f x₀, by rintro _ ⟨z, rfl⟩; exact hx₀_argmin z⟩
  have hfx₀ : f x₀ = fStar f :=
    le_antisymm (le_ciInf hx₀_argmin) (ciInf_le hbdd x₀)
  intro k
  refine ⟨?_, ?_, ?_⟩
  · simpa only [nesterovSeqGen_zero_dim k] using hx₀
  · simpa [nesterovSeqGen_zero_dim k, NesterovState.lookahead] using hx₀
  · simpa only [nesterovSeqGen_zero_dim k, hfx₀, sub_self, mul_zero]
      using (le_refl (0 : ℝ))

/-- Degenerate zero-smoothness branch for the C³-only theorem.  If the minimizer
set is empty, the empty neighborhood discharges the local statement. -/
private theorem nesterov_pl_accelerated_rate_zero_L_argmin
    {d : ℕ}
    (L : ℝ≥0) (hL_zero : (L : ℝ) = 0)
    (μ ρ : ℝ) :
    ∀ (f : E d → ℝ),
    ∀ (U : Set (E d)),
      IsOpen U →
      argminSet f ⊆ U →
      ContDiffOn ℝ 3 f U →
      PolyakLojasiewicz f μ U →
      LipschitzOnWith (↑L) (gradient f) U →
    ∃ (Ū : Set (E d)),
      IsOpen Ū ∧ argminSet f ⊆ Ū ∧ Ū ⊆ U ∧
      ∀ x₀ ∈ Ū,
        ∀ k,
          (nesterovSeqGen f (1 / ↑L) ρ ⟨x₀, 0⟩ k).x ∈ U ∧
          (nesterovSeqGen f (1 / ↑L) ρ ⟨x₀, 0⟩ k).lookahead
            (1 / ↑L) ∈ U ∧
          f ((nesterovSeqGen f (1 / ↑L) ρ ⟨x₀, 0⟩ k).x) - fStar f ≤
            2 * Real.exp (-(↑k / Real.sqrt (↑L / μ))) * (f x₀ - fStar f) := by
  intro f U hU_open hS_sub _hf_C3 _hPL _hf_lip
  by_cases hS_ne : (argminSet f).Nonempty
  · refine ⟨U, hU_open, hS_sub, Set.Subset.rfl, ?_⟩
    intro x₀ hx₀
    have hη : (1 : ℝ) / (L : ℝ) = 0 := by
      simp_all
    have hseq : ∀ k, nesterovSeqGen f (1 / ↑L) ρ ⟨x₀, 0⟩ k = ⟨x₀, 0⟩ := by
      intro k
      rw [hη]
      exact nesterovSeqGen_zero_eta k
    obtain ⟨m, hm_argmin⟩ := hS_ne
    have hbdd : BddBelow (Set.range f) :=
      ⟨f m, by rintro _ ⟨z, rfl⟩; exact hm_argmin z⟩
    intro k
    refine ⟨?_, ?_, ?_⟩
    · simpa only [hseq k] using hx₀
    · have hseq0 : nesterovSeqGen f 0 ρ ⟨x₀, 0⟩ k = ⟨x₀, 0⟩ :=
        nesterovSeqGen_zero_eta k
      rw [hη]
      simpa [hseq0, NesterovState.lookahead] using hx₀
    · have hgap_nn : 0 ≤ f x₀ - fStar f :=
        sub_nonneg.mpr (ciInf_le hbdd x₀)
      have hrate :
          2 * Real.exp (-(↑k / Real.sqrt (↑L / μ))) * (f x₀ - fStar f) =
            2 * (f x₀ - fStar f) := by
        simp_all
      calc f ((nesterovSeqGen f (1 / ↑L) ρ ⟨x₀, 0⟩ k).x) - fStar f
          = f x₀ - fStar f := by simp only [hseq k]
        _ ≤ 2 * (f x₀ - fStar f) := by nlinarith
        _ = 2 * Real.exp (-(↑k / Real.sqrt (↑L / μ))) * (f x₀ - fStar f) :=
          hrate.symm
  · refine ⟨∅, isOpen_empty, ?_, Set.empty_subset U, ?_⟩
    · intro x hx
      exact False.elim (hS_ne ⟨x, hx⟩)
    · simp_all

/-- Degenerate zero-dimensional branch for the C³-only theorem. -/
private theorem nesterov_pl_accelerated_rate_zero_dim_argmin
    (L : ℝ≥0) (μ ρ : ℝ) :
    ∀ (f : E 0 → ℝ),
    ∀ (U : Set (E 0)),
      IsOpen U →
      argminSet f ⊆ U →
      ContDiffOn ℝ 3 f U →
      PolyakLojasiewicz f μ U →
      LipschitzOnWith (↑L) (gradient f) U →
    ∃ (Ū : Set (E 0)),
      IsOpen Ū ∧ argminSet f ⊆ Ū ∧ Ū ⊆ U ∧
      ∀ x₀ ∈ Ū,
        ∀ k,
          (nesterovSeqGen f (1 / ↑L) ρ ⟨x₀, 0⟩ k).x ∈ U ∧
          (nesterovSeqGen f (1 / ↑L) ρ ⟨x₀, 0⟩ k).lookahead
            (1 / ↑L) ∈ U ∧
          f ((nesterovSeqGen f (1 / ↑L) ρ ⟨x₀, 0⟩ k).x) - fStar f ≤
            2 * Real.exp (-(↑k / Real.sqrt (↑L / μ))) * (f x₀ - fStar f) := by
  intro f U hU_open hS_sub _hf_C3 _hPL _hf_lip
  refine ⟨U, hU_open, hS_sub, Set.Subset.rfl, ?_⟩
  intro x₀ hx₀
  have hx₀_argmin : x₀ ∈ argminSet f := by
    intro z
    simp [Subsingleton.elim x₀ z]
  have hbdd : BddBelow (Set.range f) :=
    ⟨f x₀, by rintro _ ⟨z, rfl⟩; exact hx₀_argmin z⟩
  have hfx₀ : f x₀ = fStar f :=
    le_antisymm (le_ciInf hx₀_argmin) (ciInf_le hbdd x₀)
  intro k
  refine ⟨?_, ?_, ?_⟩
  · simpa only [nesterovSeqGen_zero_dim k] using hx₀
  · simpa [nesterovSeqGen_zero_dim k, NesterovState.lookahead] using hx₀
  · simpa only [nesterovSeqGen_zero_dim k, hfx₀, sub_self, mul_zero]
      using (le_refl (0 : ℝ))

/-! ## Main theorem: state positions, prefactor `2` -/

/-- Explicit-`θ` convergence from a tubular-neighborhood description of the
minimizer set.  Public wrappers construct this tubular neighborhood in different
ways, then delegate here. -/
private theorem nesterov_pl_accelerated_rate_theta_tubular
    {d : ℕ} (hd : 0 < d)
    (L : ℝ≥0) (hL : 0 < (L : ℝ))
    (μ : ℝ) (hμ : 0 < μ)
    (θ : ℝ) (hθ_pos : 0 < θ)
    (hθ_le : θ ≤ Real.sqrt (μ / ↑L) / 8) :
    ∀ (f : E d → ℝ),
    ∀ (S : Set (E d)),
      S = argminSet f →
      S.Nonempty →
    ∀ (U : Set (E d)),
      IsTubularNeighborhoodOfSubmanifold S U →
      ContDiffOn ℝ 2 f U →
      PolyakLojasiewicz f μ U →
      LipschitzOnWith (↑L) (gradient f) U →
    ∃ (Ū : Set (E d)),
      IsOpen Ū ∧ S ⊆ Ū ∧ Ū ⊆ U ∧
      ∀ x₀ ∈ Ū,
        (∀ k,
          (nesterovSeqGen f (1 / ↑L) (rhoOfTheta ↑L μ θ) ⟨x₀, 0⟩ k).x ∈ U ∧
          (nesterovSeqGen f (1 / ↑L) (rhoOfTheta ↑L μ θ) ⟨x₀, 0⟩ k).lookahead
            (1 / ↑L) ∈ U) ∧
        HasAcceleratedRateWithPrefactorTwo f
          (fun k => (nesterovSeqGen f (1 / ↑L) (rhoOfTheta ↑L μ θ) ⟨x₀, 0⟩ k).x)
          ↑L μ x₀ ∧
        HasAcceleratedRate f
          (fun k => (nesterovSeqGen f (1 / ↑L) (rhoOfTheta ↑L μ θ) ⟨x₀, 0⟩ k).x)
          ↑L μ := by
  intro f S hS_argmin hS_ne U hTub_sub hf_C2 hPL hf_lip
  obtain ⟨π, hπ_on_U, hπ_fix, hπ_in_S⟩ :=
    exists_total_nearest_projection hTub_sub hS_ne
  have hgrad_zero : ∀ x ∈ S, gradient f x = 0 :=
    gradient_eq_zero_on_argmin hS_argmin
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hlocal : ∀ mstar ∈ S, ∃ (α : ℝ), 0 < α ∧
      Metric.ball mstar α ⊆ U ∧
      ∀ x₀ ∈ Metric.ball mstar α,
        (∀ k,
          (nesterovSeqGen f (1 / ↑L) (rhoOfTheta ↑L μ θ) ⟨x₀, 0⟩ k).x ∈ U ∧
          (nesterovSeqGen f (1 / ↑L) (rhoOfTheta ↑L μ θ) ⟨x₀, 0⟩ k).lookahead
            (1 / ↑L) ∈ U) ∧
        HasAcceleratedRateWithPrefactorTwo f
          (fun k => (nesterovSeqGen f (1 / ↑L) (rhoOfTheta ↑L μ θ) ⟨x₀, 0⟩ k).x)
          ↑L μ x₀ ∧
        HasAcceleratedRate f
          (fun k => (nesterovSeqGen f (1 / ↑L) (rhoOfTheta ↑L μ θ) ⟨x₀, 0⟩ k).x)
          ↑L μ := by
    intro mstar hmstar
    by_cases hμ_le_L : μ ≤ ↑L
    · have hsqrt_le_one : Real.sqrt (μ / ↑L) ≤ 1 := by
        rw [← Real.sqrt_one]
        apply Real.sqrt_le_sqrt
        rw [div_le_iff₀ hL]
        simpa only [one_mul] using hμ_le_L
      have hθ_le_quarter : θ ≤ 1 / 4 := by
        calc θ ≤ Real.sqrt (μ / ↑L) / 8 := hθ_le
          _ ≤ 1 / 8 := by nlinarith
          _ ≤ 1 / 4 := by norm_num
      have hθ_lt1 : θ < 1 := by linarith
      exact nesterov_convergence_at_base_point_position_theta hd L hL μ hμ hμ_le_L
        θ hθ_pos hθ_lt1 hθ_le hθ_le_quarter f S hS_argmin U hTub_sub hPL hf_C2
        hf_lip π hπ_on_U hπ_fix hπ_in_S hgrad_zero mstar hmstar
    · obtain ⟨r₀, hr₀_pos, hball₀⟩ :=
        Metric.isOpen_iff.mp hTub_sub.isOpen mstar (hTub_sub.subset hmstar)
      have hmstar_argmin : mstar ∈ argminSet f := by
        simp_all
      have hbdd : BddBelow (Set.range f) :=
        ⟨f mstar, by rintro _ ⟨z, rfl⟩; exact hmstar_argmin z⟩
      by_cases hloc_const : ∀ x ∈ Metric.ball mstar (r₀ / 3), f x = fStar f
      · refine ⟨r₀ / 3, by positivity,
          (Metric.ball_subset_ball (by linarith)).trans hball₀, ?_⟩
        intro x₀ hx₀
        have hx₀_U : x₀ ∈ U :=
          hball₀ (Metric.ball_subset_ball (by linarith) hx₀)
        have hfx₀ : f x₀ = fStar f := hloc_const x₀ hx₀
        have hx₀_argmin : x₀ ∈ argminSet f := by
          intro z
          rw [hfx₀]
          exact ciInf_le hbdd z
        have hx₀_S : x₀ ∈ S := by
          simp_all
        have hgrad_x₀ : gradient f x₀ = 0 := hgrad_zero x₀ hx₀_S
        refine ⟨?_, ?_, ?_⟩
        · intro k
          constructor
          · simpa only [nesterovSeqGen_at_zero_grad hgrad_x₀ k] using hx₀_U
          · simpa [nesterovSeqGen_at_zero_grad hgrad_x₀ k, NesterovState.lookahead]
              using hx₀_U
        · intro k
          simpa only [nesterovSeqGen_at_zero_grad hgrad_x₀ k, hfx₀, sub_self,
            mul_zero] using (le_refl (0 : ℝ))
        · refine ⟨1, one_pos, fun k => ?_⟩
          simp only [nesterovSeqGen_at_zero_grad hgrad_x₀ k, hfx₀, sub_self]
          positivity
      · push Not at hloc_const
        obtain ⟨y, hy, hfy⟩ := hloc_const
        have hμ_le_L' : μ ≤ ↑L :=
          mu_le_L_of_pl_descent_near hL hPL
            (hf_C2.differentiableOn (by norm_num : (2 : WithTop ℕ∞) ≠ 0))
            hf_lip hmstar_argmin hr₀_pos hball₀ hy hfy
        exact False.elim (hμ_le_L hμ_le_L')
  exact open_neighborhood_from_local_balls hlocal

/-- Explicit-`θ` form of the main theorem.

Fix a retuning parameter `θ` satisfying
`0 < θ ≤ √(μ/L)/8`.  When the standard compatibility bound `μ ≤ L` holds, the
proof delegates to the local convergence theorem.  In the complementary
`L < μ` case, any local non-minimizer would force `μ ≤ L`, so the theorem is
discharged by the stationary local-constant branch.

For every objective whose minimizer set is an embedded submanifold and
which satisfies the local PL, smoothness, and tubular-neighborhood hypotheses,
there is an open neighborhood of the minimizer manifold such that Nesterov's
state positions stay in the original tubular neighborhood and satisfy

`f(xₖ) - f⋆ ≤ 2 * exp(-k / sqrt (L / μ)) * (f(x₀) - f⋆)`. -/
theorem nesterov_pl_accelerated_rate_theta
    {d : ℕ} (hd : 0 < d)
    (L : ℝ≥0) (hL : 0 < (L : ℝ))
    (μ : ℝ) (hμ : 0 < μ)
    (θ : ℝ) (hθ_pos : 0 < θ)
    (hθ_le : θ ≤ Real.sqrt (μ / ↑L) / 8) :
    ∀ (f : E d → ℝ),
    ∀ (n : ℕ),
    ∀ (M : Type*) [TopologicalSpace M] [ChartedSpace (ManifoldModel n) M]
      [IsManifold (modelI n) 2 M] [Nonempty M]
      (ι : M → E d),
      IsSmoothEmbedding (modelI n) (modelWithCornersSelf ℝ (E d)) 2 ι →
      Set.range ι = argminSet f →
    ∀ (U : Set (E d)),
      IsGeneralTubularNeighborhood (Set.range ι) U →
      ContDiffOn ℝ 2 f U →
      PolyakLojasiewicz f μ U →
      LipschitzOnWith (↑L) (gradient f) U →
    ∃ (Ū : Set (E d)),
      IsOpen Ū ∧ Set.range ι ⊆ Ū ∧ Ū ⊆ U ∧
      ∀ x₀ ∈ Ū,
        (∀ k,
          (nesterovSeqGen f (1 / ↑L) (rhoOfTheta ↑L μ θ) ⟨x₀, 0⟩ k).x ∈ U ∧
          (nesterovSeqGen f (1 / ↑L) (rhoOfTheta ↑L μ θ) ⟨x₀, 0⟩ k).lookahead
            (1 / ↑L) ∈ U) ∧
        HasAcceleratedRateWithPrefactorTwo f
          (fun k => (nesterovSeqGen f (1 / ↑L) (rhoOfTheta ↑L μ θ) ⟨x₀, 0⟩ k).x)
          ↑L μ x₀ ∧
        HasAcceleratedRate f
          (fun k => (nesterovSeqGen f (1 / ↑L) (rhoOfTheta ↑L μ θ) ⟨x₀, 0⟩ k).x)
          ↑L μ := by
  intro f n M _ _ _ _ ι hι hrange U hGenTub hf_C2 hPL hf_lip
  have hTub_sub := general_tubular_of_smooth_embedding M ι hι U hGenTub
  set S := Set.range ι with hS_def
  have hS_argmin : S = argminSet f := hrange
  exact nesterov_pl_accelerated_rate_theta_tubular hd L hL μ hμ θ hθ_pos hθ_le
    f S hS_argmin (Set.range_nonempty ι) U hTub_sub hf_C2 hPL hf_lip

/-- **Main theorem (public form).**

There exists a momentum parameter `ρ`, depending only on `L` and `μ`, such that
for every objective whose minimizer set is an embedded submanifold and
which satisfies the local PL and smoothness hypotheses on an open neighborhood
of the minimizer manifold, there is a smaller open neighborhood such that
Nesterov's state positions stay in the original neighborhood and satisfy the
explicit prefactor-two estimate

`f(xₖ) - f⋆ ≤ 2 * exp(-k / sqrt (L / μ)) * (f(x₀) - f⋆)`.

This internal form exposes the embedded-manifold witness directly; the public
theorem in `PLAcceleratedNesterovLean.MainTheorem` re-exports exactly these report-level
assumptions from a clean file. -/
theorem nesterov_pl_accelerated_rate_embedded
    {d : ℕ}
    (L : ℝ≥0)
    (μ : ℝ) :
    ∃ ρ : ℝ,
    ∀ (f : E d → ℝ),
    ∀ (n : ℕ),
    ∀ (M : Type*) [TopologicalSpace M] [ChartedSpace (ManifoldModel n) M]
      [IsManifold (modelI n) 2 M] [Nonempty M]
      (ι : M → E d),
      IsSmoothEmbedding (modelI n) (modelWithCornersSelf ℝ (E d)) 2 ι →
      Set.range ι = argminSet f →
    ∀ (U : Set (E d)),
      IsOpen U →
      Set.range ι ⊆ U →
      ContDiffOn ℝ 2 f U →
      PolyakLojasiewicz f μ U →
      LipschitzOnWith (↑L) (gradient f) U →
    ∃ (Ū : Set (E d)),
      IsOpen Ū ∧ Set.range ι ⊆ Ū ∧ Ū ⊆ U ∧
      ∀ x₀ ∈ Ū,
        ∀ k,
          (nesterovSeqGen f (1 / ↑L) ρ ⟨x₀, 0⟩ k).x ∈ U ∧
          (nesterovSeqGen f (1 / ↑L) ρ ⟨x₀, 0⟩ k).lookahead
            (1 / ↑L) ∈ U ∧
          f ((nesterovSeqGen f (1 / ↑L) ρ ⟨x₀, 0⟩ k).x) - fStar f ≤
            2 * Real.exp (-(↑k / Real.sqrt (↑L / μ))) * (f x₀ - fStar f) := by
  let θ : ℝ := Real.sqrt (μ / ↑L) / 16
  refine ⟨rhoOfTheta ↑L μ θ, ?_⟩
  intro f n M _ _ _ _ ι hι hrange U hU_open hS_sub hf_C2 hPL hf_lip
  by_cases hd : 0 < d
  · have hμ : 0 < μ := hPL.1
    by_cases hL : 0 < (L : ℝ)
    · have hθ_pos : 0 < θ := by
        dsimp only [θ]
        exact div_pos (Real.sqrt_pos_of_pos (div_pos hμ hL)) (by norm_num)
      have hθ_le : θ ≤ Real.sqrt (μ / ↑L) / 8 := by
        dsimp only [θ]
        nlinarith [Real.sqrt_nonneg (μ / ↑L)]
      obtain ⟨U_tub, _hU_tub_open, _hS_sub_tub, hU_tub_sub, hGenTub⟩ :=
        exists_general_tubular_subneighborhood M ι hι U hU_open hS_sub
      have hf_C2_tub : ContDiffOn ℝ 2 f U_tub := hf_C2.mono hU_tub_sub
      have hPL_tub : PolyakLojasiewicz f μ U_tub :=
        ⟨hPL.1, hPL.2.1.mono hU_tub_sub, fun x hx => hPL.2.2 x (hU_tub_sub hx)⟩
      have hf_lip_tub : LipschitzOnWith (↑L) (gradient f) U_tub :=
        hf_lip.mono hU_tub_sub
      obtain ⟨Ū, hŪ_open, hS_sub_Ū, hŪ_sub_tub, hconv⟩ :=
        nesterov_pl_accelerated_rate_theta hd L hL μ hμ θ hθ_pos hθ_le
          f n M ι hι hrange U_tub hGenTub hf_C2_tub hPL_tub hf_lip_tub
      refine ⟨Ū, hŪ_open, hS_sub_Ū, hŪ_sub_tub.trans hU_tub_sub, ?_⟩
      intro x₀ hx₀
      obtain ⟨hinv, hrate_two, _hrate⟩ := hconv x₀ hx₀
      intro k
      exact ⟨hU_tub_sub (hinv k).1, hU_tub_sub (hinv k).2, hrate_two k⟩
    · have hL_zero : (L : ℝ) = 0 :=
        le_antisymm (not_lt.mp hL) (NNReal.coe_nonneg L)
      exact nesterov_pl_accelerated_rate_zero_L L hL_zero μ (rhoOfTheta ↑L μ θ)
        f n M ι hι hrange U hU_open hS_sub hf_C2 hPL hf_lip
  · have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
    subst d
    exact nesterov_pl_accelerated_rate_zero_dim L μ (rhoOfTheta ↑L μ θ)
      f n M ι hι hrange U hU_open hS_sub hf_C2 hPL hf_lip

/-- **C³-only internal main theorem.**

This variant assumes `f` is `C³` on an open neighborhood of its global minimizer
set.  The C³+PL Morse-Bott machinery constructs the tubular sub-neighborhood
internally from the first-order theorem hypotheses. -/
theorem nesterov_pl_accelerated_rate_c3_internal
    {d : ℕ}
    (L : ℝ≥0)
    (μ : ℝ) :
    ∃ ρ : ℝ,
    ∀ (f : E d → ℝ),
    ∀ (U : Set (E d)),
     IsOpen U →
     argminSet f ⊆ U →
     ContDiffOn ℝ 3 f U →
     PolyakLojasiewicz f μ U →
     LipschitzOnWith (↑L) (gradient f) U →
    ∃ (Ū : Set (E d)),
     IsOpen Ū ∧ argminSet f ⊆ Ū ∧ Ū ⊆ U ∧
     ∀ x₀ ∈ Ū,
       ∀ k,
         (nesterovSeqGen f (1 / ↑L) ρ ⟨x₀, 0⟩ k).x ∈ U ∧
         (nesterovSeqGen f (1 / ↑L) ρ ⟨x₀, 0⟩ k).lookahead
           (1 / ↑L) ∈ U ∧
         f ((nesterovSeqGen f (1 / ↑L) ρ ⟨x₀, 0⟩ k).x) - fStar f ≤
           2 * Real.exp (-(↑k / Real.sqrt (↑L / μ))) * (f x₀ - fStar f) := by
  let θ : ℝ := Real.sqrt (μ / ↑L) / 16
  refine ⟨rhoOfTheta ↑L μ θ, ?_⟩
  intro f U hU_open hS_sub hf_C3 hPL hf_lip
  by_cases hS_ne : (argminSet f).Nonempty
  · by_cases hd : 0 < d
    · have hμ : 0 < μ := hPL.1
      by_cases hL : 0 < (L : ℝ)
      · have hθ_pos : 0 < θ := by
          dsimp only [θ]
          exact div_pos (Real.sqrt_pos_of_pos (div_pos hμ hL)) (by norm_num)
        have hθ_le : θ ≤ Real.sqrt (μ / ↑L) / 8 := by
          dsimp only [θ]
          nlinarith [Real.sqrt_nonneg (μ / ↑L)]
        obtain ⟨U_tub, _hU_tub_open, _hS_sub_tub, hU_tub_sub, _hGenTub, hTub_sub⟩ :=
          exists_tubular_subneighborhood_of_c3_pl hd hU_open hS_sub hPL hf_C3
        have hf_C2_tub : ContDiffOn ℝ 2 f U_tub :=
          (hf_C3.of_le (by norm_num)).mono hU_tub_sub
        have hPL_tub : PolyakLojasiewicz f μ U_tub :=
          ⟨hPL.1, hPL.2.1.mono hU_tub_sub, fun x hx => hPL.2.2 x (hU_tub_sub hx)⟩
        have hf_lip_tub : LipschitzOnWith (↑L) (gradient f) U_tub :=
          hf_lip.mono hU_tub_sub
        obtain ⟨Ū, hŪ_open, hS_sub_Ū, hŪ_sub_tub, hconv⟩ :=
          nesterov_pl_accelerated_rate_theta_tubular hd L hL μ hμ θ hθ_pos hθ_le
            f (argminSet f) rfl hS_ne U_tub hTub_sub hf_C2_tub hPL_tub hf_lip_tub
        refine ⟨Ū, hŪ_open, hS_sub_Ū, hŪ_sub_tub.trans hU_tub_sub, ?_⟩
        intro x₀ hx₀
        obtain ⟨hinv, hrate_two, _hrate⟩ := hconv x₀ hx₀
        intro k
        exact ⟨hU_tub_sub (hinv k).1, hU_tub_sub (hinv k).2, hrate_two k⟩
      · have hL_zero : (L : ℝ) = 0 :=
          le_antisymm (not_lt.mp hL) (NNReal.coe_nonneg L)
        exact nesterov_pl_accelerated_rate_zero_L_argmin L hL_zero μ
          (rhoOfTheta ↑L μ θ) f U hU_open hS_sub hf_C3 hPL hf_lip
    · have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
      subst d
      exact nesterov_pl_accelerated_rate_zero_dim_argmin L μ (rhoOfTheta ↑L μ θ)
        f U hU_open hS_sub hf_C3 hPL hf_lip
  · refine ⟨∅, isOpen_empty, ?_, Set.empty_subset U, ?_⟩
    · intro x hx
      exact False.elim (hS_ne ⟨x, hx⟩)
    · simp_all

end PLAcceleratedNesterovLean
