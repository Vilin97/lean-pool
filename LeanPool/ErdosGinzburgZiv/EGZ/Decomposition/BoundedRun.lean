/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationBounds
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.GapProgress
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.RefinementProgress

/-!
# Actual finite refinement runs

A prime is fixed for a prescribed finite radius horizon before the run is
built. Unfinished states advance by concrete normalized operations; finished
states and stages beyond the horizon keep their state. No infinite sequence
of progress certificates is assumed.
-/

@[expose] public section

open scoped BigOperators

namespace EGZ.FlagDecomposition.Iteration

open DecompositionParameters

variable {p d : ℕ} [NeZero p] [Fact p.Prime] {f : FpCoord p d → ℕ}
    {g : ℕ → ℕ} (P : NormalizedOperationParameters d g) {ε : ℝ}

/-- One actual progress step, together with the uniform radius estimate. -/
structure NextProgress (s : State p d f) (ε δ : ℝ) (g H : ℕ → ℕ) where
  /-- State produced by the next certified refinement step. -/
  target : State p d f
  /-- Certificate of progress from the current state to the target. -/
  progress : Progress s target ε δ g
  radius_le : target.radius ≤ H s.radius

theorem exists_nextProgress (hd : 1 ≤ d) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (hg : Monotone g) {i : ℕ} (s : BoundedState (f := f) P ε i)
    (hprime : P.primeThreshold s.radius < p)
    (hnot : ¬ s.toState.Finished ε (stageScale d ε i) g) :
    Nonempty (NextProgress s.toState ε (stageScale d ε i) g P.radiusGrowth) := by
  have hδ : 0 ≤ stageScale d ε i := (stageScale_pos d hε i).le
  have hsmall := stageScale_small hd hε hεhalf i
  obtain ⟨E, hE⟩ := s.toState.exists_valid_event ε (stageScale d ε i) g hnot
  cases E with
  | gap =>
    obtain ⟨D⟩ := P.gap s.radius p hprime f s.decomposition s.bounded
      (ε * stageScale d ε i ^ 2) (by positivity) hsmall.2
    have hgap : (gapState s.toState D).GapCondition (stageScale d ε i) :=
      gapState_gapCondition s.toState D (i := i + 1) (by omega) hε.le
        (by simpa using s.card_bound) (s.mass_bounds hd hε hεhalf).1
        (initialScale_scale_bound hd hε hεhalf (i + 1))
    exact ⟨⟨gapState s.toState D,
      gapProgress s.toState D hε.le hδ hE hgap g, D.radius_le⟩⟩
  | face anchor Γ =>
    have hΓ : Γ ≠ ⊤ := by
      intro hΓ
      apply hE.2
      rw [hΓ]
      exact s.decomposition.isRealizedFace_top anchor
    obtain ⟨D⟩ := P.face s.radius p hprime f s.decomposition anchor Γ hΓ
      (s.reduced anchor) s.bounded
    exact ⟨⟨faceState s.toState D,
      faceProgress s.toState D hE hε.le hδ, D.radius_le⟩⟩
  | complete anchor =>
    obtain ⟨D⟩ := P.complete s.radius p hprime f s.decomposition anchor
      (stageScale d ε i) hδ hsmall.1 s.bounded
    exact ⟨⟨completeState s.toState D,
      completeProgress s.toState D hE hε.le hg, D.radius_le⟩⟩

/-- Choose a certified next refinement step within the prescribed radius bound. -/
noncomputable def nextProgress (hd : 1 ≤ d) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (hg : Monotone g) {i : ℕ} (s : BoundedState (f := f) P ε i)
    (hprime : P.primeThreshold s.radius < p)
    (hnot : ¬ s.toState.Finished ε (stageScale d ε i) g) :
    NextProgress s.toState ε (stageScale d ε i) g P.radiusGrowth :=
  Classical.choice (exists_nextProgress P hd hε hεhalf hg s hprime hnot)

/-- A transition either makes certified progress or keeps the old state.
Before the horizon it must progress whenever the state is unfinished. -/
structure BoundedTransition {i : ℕ} (s : BoundedState (f := f) P ε i) (N : ℕ) where
  /-- Bounded state at the next iteration index. -/
  target : BoundedState (f := f) P ε (i + 1)
  radius_le : target.radius ≤ P.radiusGrowth s.radius
  progress_or_eq : Nonempty (Progress s.toState target.toState ε (stageScale d ε i) g) ∨
    target.toState = s.toState
  forced_progress : i < N → ¬ s.toState.Finished ε (stageScale d ε i) g →
    Nonempty (Progress s.toState target.toState ε (stageScale d ε i) g)
  after_horizon : N ≤ i → target.toState = s.toState

/-- Advance the bounded iteration, retaining a finished state when appropriate. -/
noncomputable def boundedTransition (hd : 1 ≤ d) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (hg : Monotone g) (N : ℕ) (hprime : P.primeHorizon 1 N < p)
    {i : ℕ} (s : BoundedState (f := f) P ε i) : BoundedTransition P s N := by
  classical
  by_cases hi : i < N
  · by_cases hfinished : s.toState.Finished ε (stageScale d ε i) g
    · exact {
        target := s.keep hε
        radius_le := P.radiusGrowth_ge s.radius
        progress_or_eq := Or.inr rfl
        forced_progress := fun _ hn ↦ (hn hfinished).elim
        after_horizon := fun _ ↦ rfl }
    · have hpstate : P.primeThreshold s.radius < p :=
        P.primeThreshold_lt_of_le_horizon hprime
          (s.radius_bound.trans (P.radiusHorizon_monotone 1 hi.le))
      let D := nextProgress P hd hε hεhalf hg s hpstate hfinished
      exact {
        target := s.advance hε D.progress D.radius_le
        radius_le := D.radius_le
        progress_or_eq := Or.inl ⟨D.progress⟩
        forced_progress := fun _ _ ↦ ⟨D.progress⟩
        after_horizon := fun hNi ↦ (Nat.not_lt_of_ge hNi hi).elim }
  · exact {
      target := s.keep hε
      radius_le := P.radiusGrowth_ge s.radius
      progress_or_eq := Or.inr rfl
      forced_progress := fun hi' _ ↦ (hi hi').elim
      after_horizon := fun _ ↦ rfl }

/-- The actual recursively chosen bounded run, kept constant after the
prescribed horizon. -/
noncomputable def boundedRun (hd : 1 ≤ d) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (hg : Monotone g) (hf : f ≠ 0) (N : ℕ) (hprime : P.primeHorizon 1 N < p) :
    (i : ℕ) → BoundedState (f := f) P ε i :=
  Nat.rec (BoundedState.initial (P := P) (ε := ε) hf)
    (fun _ s ↦ (boundedTransition P hd hε hεhalf hg N hprime s).target)

namespace boundedRun

variable (hd : 1 ≤ d) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (hg : Monotone g) (hf : f ≠ 0) (N : ℕ) (hprime : P.primeHorizon 1 N < p)

/-- Underlying unbounded state at a given index of the bounded run. -/
noncomputable abbrev state (i : ℕ) : State p d f :=
  (boundedRun P hd hε hεhalf hg hf N hprime i).toState

@[simp]
theorem initial_retainedMass :
    (state P hd hε hεhalf hg hf N hprime 0).decomposition.retainedMass = natMass f :=
  FlagDecomposition.initial_retainedMass f hf

theorem card_bound (i : ℕ) :
    Fintype.card (state P hd hε hεhalf hg hf N hprime i).decomposition.flag.Node ≤ 2 ^ i :=
  (boundedRun P hd hε hεhalf hg hf N hprime i).card_bound

theorem radius_bound (i : ℕ) :
    (state P hd hε hεhalf hg hf N hprime i).radius ≤ P.radiusHorizon 1 i :=
  (boundedRun P hd hε hεhalf hg hf N hprime i).radius_bound

theorem radius_le_horizon (i : ℕ) (hi : i ≤ N) :
    (state P hd hε hεhalf hg hf N hprime i).radius ≤ P.radiusHorizon 1 N :=
  (radius_bound P hd hε hεhalf hg hf N hprime i).trans (P.radiusHorizon_monotone 1 hi)

theorem radius_step (i : ℕ) :
    (state P hd hε hεhalf hg hf N hprime (i + 1)).radius ≤
      P.radiusGrowth (state P hd hε hεhalf hg hf N hprime i).radius :=
  (boundedTransition P hd hε hεhalf hg N hprime
    (boundedRun P hd hε hεhalf hg hf N hprime i)).radius_le

theorem progress_or_eq (i : ℕ) :
    Nonempty (Progress (state P hd hε hεhalf hg hf N hprime i)
      (state P hd hε hεhalf hg hf N hprime (i + 1)) ε (stageScale d ε i) g) ∨
    state P hd hε hεhalf hg hf N hprime (i + 1) =
      state P hd hε hεhalf hg hf N hprime i :=
  (boundedTransition P hd hε hεhalf hg N hprime
    (boundedRun P hd hε hεhalf hg hf N hprime i)).progress_or_eq

theorem progress (i : ℕ) (hi : i < N)
    (hnot : ¬ (state P hd hε hεhalf hg hf N hprime i).Finished ε (stageScale d ε i) g) :
    Nonempty (Progress (state P hd hε hεhalf hg hf N hprime i)
      (state P hd hε hεhalf hg hf N hprime (i + 1)) ε (stageScale d ε i) g) :=
  (boundedTransition P hd hε hεhalf hg N hprime
    (boundedRun P hd hε hεhalf hg hf N hprime i)).forced_progress hi hnot

theorem state_succ_eq_of_ge (i : ℕ) (hi : N ≤ i) :
    state P hd hε hεhalf hg hf N hprime (i + 1) =
      state P hd hε hεhalf hg hf N hprime i :=
  (boundedTransition P hd hε hεhalf hg N hprime
    (boundedRun P hd hε hεhalf hg hf N hprime i)).after_horizon hi

theorem state_eq_horizon (i : ℕ) (hi : N ≤ i) :
    state P hd hε hεhalf hg hf N hprime i = state P hd hε hεhalf hg hf N hprime N := by
  induction i, hi using Nat.le_induction with
  | base => rfl
  | succ i hi ih => exact (state_succ_eq_of_ge P hd hε hεhalf hg hf N hprime i hi).trans ih

theorem radius_mono_step (i : ℕ) :
    (state P hd hε hεhalf hg hf N hprime i).radius ≤
      (state P hd hε hεhalf hg hf N hprime (i + 1)).radius := by
  rcases progress_or_eq P hd hε hεhalf hg hf N hprime i with hprogress | heq
  · obtain ⟨D⟩ := hprogress
    exact D.radius_le
  · rw [heq]

theorem radius_monotone : Monotone (fun i ↦ (state P hd hε hεhalf hg hf N hprime i).radius) :=
  monotone_nat_of_le_succ (radius_mono_step P hd hε hεhalf hg hf N hprime)

theorem mass_mono_step (i : ℕ) :
    (state P hd hε hεhalf hg hf N hprime (i + 1)).decomposition.retainedMass ≤
      (state P hd hε hεhalf hg hf N hprime i).decomposition.retainedMass := by
  rcases progress_or_eq P hd hε hεhalf hg hf N hprime i with hprogress | heq
  · obtain ⟨D⟩ := hprogress
    exact D.mass_le
  · rw [heq]

theorem mass_antitone :
    Antitone (fun i ↦ (state P hd hε hεhalf hg hf N hprime i).decomposition.retainedMass) :=
  antitone_nat_of_succ_le (mass_mono_step P hd hε hεhalf hg hf N hprime)

theorem card_step (i : ℕ) :
    Fintype.card (state P hd hε hεhalf hg hf N hprime (i + 1)).decomposition.flag.Node ≤
      2 * Fintype.card (state P hd hε hεhalf hg hf N hprime i).decomposition.flag.Node := by
  rcases progress_or_eq P hd hε hεhalf hg hf N hprime i with hprogress | heq
  · obtain ⟨D⟩ := hprogress
    exact D.card_le
  · rw [heq]
    exact Nat.le_mul_of_pos_left _ (by omega)

theorem mass_step (i : ℕ) :
    ((state P hd hε hεhalf hg hf N hprime i).decomposition.retainedMass : ℝ) -
      (state P hd hε hεhalf hg hf N hprime (i + 1)).decomposition.retainedMass ≤
        lossBudget d ε (initialScale d ε) (i + 1) * natMass f := by
  have hcoef := lossBudget_nonneg d hε.le (initialScale_pos d hε).le (i + 1)
  rcases progress_or_eq P hd hε hεhalf hg hf N hprime i with hprogress | heq
  · obtain ⟨D⟩ := hprogress
    have hmass : ((state P hd hε hεhalf hg hf N hprime i).decomposition.retainedMass : ℝ) ≤
        natMass f := by
      exact_mod_cast (boundedRun P hd hε hεhalf hg hf N hprime i).mass_le_input
    have hloss := D.mass_loss_le
    change ((state P hd hε hεhalf hg hf N hprime i).decomposition.retainedMass : ℝ) -
      (state P hd hε hεhalf hg hf N hprime (i + 1)).decomposition.retainedMass ≤
        lossBudget d ε (initialScale d ε) (i + 1) *
          (state P hd hε hεhalf hg hf N hprime i).decomposition.retainedMass at hloss
    exact hloss.trans (mul_le_mul_of_nonneg_left hmass hcoef)
  · rw [heq, sub_self]
    exact mul_nonneg hcoef (Nat.cast_nonneg _)

theorem retainedMass_bounds (i : ℕ) :
    (natMass f : ℝ) / 2 ≤ (state P hd hε hεhalf hg hf N hprime i).decomposition.retainedMass ∧
      (1 - ε) * (natMass f : ℝ) ≤
        (state P hd hε hεhalf hg hf N hprime i).decomposition.retainedMass :=
  (boundedRun P hd hε hεhalf hg hf N hprime i).mass_bounds hd hε hεhalf

/-- The geometric tail bound holds for every interval of the extended
finite run, including intervals crossing its constant tail. -/
theorem mass_loss_tail (s n : ℕ) :
    ((state P hd hε hεhalf hg hf N hprime s).decomposition.retainedMass : ℝ) -
      (state P hd hε hεhalf hg hf N hprime (n + s)).decomposition.retainedMass ≤
        ε ^ 2 / 8 * (2 : ℝ)⁻¹ ^ s * natMass f :=
  DecompositionParameters.mass_loss_le hd hε hεhalf
    (fun i ↦ (state P hd hε hεhalf hg hf N hprime i).decomposition.retainedMass)
    (Nat.cast_nonneg _) (mass_step P hd hε hεhalf hg hf N hprime) s n

theorem mass_loss_tail_relative (s n : ℕ) :
    ((state P hd hε hεhalf hg hf N hprime s).decomposition.retainedMass : ℝ) -
      (state P hd hε hεhalf hg hf N hprime (n + s)).decomposition.retainedMass ≤
        ε ^ 2 / 4 * (state P hd hε hεhalf hg hf N hprime s).decomposition.retainedMass := by
  have htail := mass_loss_tail P hd hε hεhalf hg hf N hprime s n
  have hpow : (2 : ℝ)⁻¹ ^ s ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have htail' := htail.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ ε ^ 2 / 8)) (Nat.cast_nonneg (natMass f)))
  have hmass := (retainedMass_bounds P hd hε hεhalf hg hf N hprime s).1
  nlinarith [mul_le_mul_of_nonneg_left hmass (sq_nonneg ε)]

/-- The actual finite run either reaches a finished bounded state by its
horizon, or provides a family of progress certificates at every earlier
stage. Its state sequence is defined and constant beyond the horizon. -/
theorem finished_or_progress :
    (∃ i, i ≤ N ∧ (state P hd hε hεhalf hg hf N hprime i).Finished ε (stageScale d ε i) g) ∨
      Nonempty ((i : ℕ) → i < N →
        Progress (state P hd hε hεhalf hg hf N hprime i)
          (state P hd hε hεhalf hg hf N hprime (i + 1)) ε (stageScale d ε i) g) := by
  classical
  by_cases hfinished : ∃ i, i ≤ N ∧
      (state P hd hε hεhalf hg hf N hprime i).Finished ε (stageScale d ε i) g
  · exact Or.inl hfinished
  · right
    refine ⟨fun i hi ↦ Classical.choice
      (progress P hd hε hεhalf hg hf N hprime i hi ?_)⟩
    intro h
    exact hfinished ⟨i, hi.le, h⟩

end boundedRun
end EGZ.FlagDecomposition.Iteration
