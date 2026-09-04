/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/

import LeanPool.Wallace.ConcreteLocalSetup
import LeanPool.Wallace.BlockLimit
import LeanPool.Wallace.GlobalAssembly
import LeanPool.Wallace.FusionSchedule
import LeanPool.Wallace.FusionStage
import LeanPool.Wallace.FusionLimit
import LeanPool.Wallace.InitialCharacter
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.SDiff

/-!
# A local character-fusion core

This file packages the analytic part of the countable fusion separately from the finite stage
constructor.  A `FusionRun` records exactly the output of successive applications of bounded
deletion and `exists_character_fusion_stage`: characters, protected finite sets, and retained
new sets.  From these *proved finite-stage certificates* we construct the pointwise limit
character and derive:

* extension/detection of the distinguished element;
* estimates on every retained block;
* local ultrafilter admissibility.

The second half of the file carries out the scheduling induction for the concrete Wallace data.
-/

open Filter Set Topology

namespace Wallace
namespace LocalFusion

noncomputable section

universe u

open FiniteCombinatorics

/-! ## The bounded-deletion input to one stage -/

/-- A scheduled bounded-deletion and finite-fusion stage. -/
theorem exists_character_after_deletion
    {G : Type} [AddCommGroup G] [DecidableEq G]
    (l : ℕ) (A X : Finset G)
    (hA : A.card ≤ FusionSchedule.protectedBound l)
    (hXcard : X.card ≤ FusionSchedule.blockSize l)
    (hX : BoundedIndependent (FusionSchedule.stageIndependenceBound l) X)
    (old : G →+ UnitAddCircle) :
    ∃ (Y : Finset G) (next : G →+ UnitAddCircle),
      Y ⊆ X ∧ (X \ Y).card ≤ A.card ∧
      (∀ a ∈ A, ‖next a - old a‖ < FusionSchedule.stageError l) ∧
      (∀ y ∈ Y, ‖next y‖ < FusionSchedule.stageError l) := by
  classical
  obtain ⟨Y, hYX, hcard, hfree⟩ := FusionSchedule.exists_stage_deletion A X hA hX
  have hYcard : Y.card ≤ FusionSchedule.blockSize l := by
    exact (Finset.card_le_card hYX).trans hXcard
  have htuple := FusionSchedule.card_union_le_tupleLengthBound hA hYcard
  obtain ⟨next, hold, hzero⟩ := exists_character_fusion_stage
    (FusionSchedule.one_le_kroneckerBound l) hfree old
    (FusionSchedule.kroneckerBound_spec l (A ∪ Y).card htuple)
  exact ⟨Y, next, hYX, hcard, hold, hzero⟩

/-! ## Certified countable runs and their pointwise limits -/

/-- Data produced by the local fusion induction.  Every field is a checkable mathematical
certificate: there is no assertion that an arbitrary run exists.  The finite scheduling
induction and the uniform Kronecker theorem populate these fields directly. -/
structure FusionRun (G : Type u) [AddCommGroup G] where
  /-- The character after stage `l`. -/
  character : ℕ → G →+ UnitAddCircle
  /-- The finite set protected while passing from stage `l` to `l+1`. -/
  guardSet : ℕ → Finset G
  /-- New points retained after bounded deletion at stage `l`. -/
  retained : ℕ → Finset G
  /-- Every element is protected at all sufficiently late stages. -/
  eventually_protected : ∀ g : G, ∀ᶠ l in atTop, g ∈ guardSet l
  /-- Consecutive characters are close on protected points. -/
  protected_step : ∀ l g, g ∈ guardSet l →
    dist (character l g) (character (l + 1) g) ≤ FusionSchedule.stageError l
  /-- A retained point is nearly annihilated when it is introduced. -/
  retained_at_stage : ∀ l g, g ∈ retained l →
    ‖character (l + 1) g‖ ≤ FusionSchedule.stageError l
  /-- Once introduced, retained points are protected forever. -/
  retained_protected : ∀ l g, g ∈ retained l →
    ∀ k, l + 1 ≤ k → g ∈ guardSet k

namespace FusionRun

variable {G : Type u} [AddCommGroup G]

/-- A pointwise tail of a certified fusion has the geometric step estimate. -/
theorem tail_step_le (R : FusionRun G) (g : G) :
    ∃ L : ℕ, ∀ n : ℕ,
      dist (R.character (L + n) g) (R.character (L + n + 1) g) ≤
        FusionSchedule.stageError (L + n) := by
  obtain ⟨L, hL⟩ := eventually_atTop.1 (R.eventually_protected g)
  refine ⟨L, fun n ↦ ?_⟩
  have hmem : g ∈ R.guardSet (L + n) := hL _ (Nat.le_add_right L n)
  simpa only [Nat.add_assoc] using R.protected_step (L + n) g hmem

/-- Every coordinate of a certified fusion is Cauchy. -/
theorem cauchySeq (R : FusionRun G) (g : G) :
    CauchySeq (fun l ↦ R.character l g) := by
  obtain ⟨L, hstep⟩ := R.tail_step_le g
  rw [← cauchySeq_shift L]
  have hcauchy : CauchySeq (fun n ↦ R.character (L + n) g) :=
    cauchySeq_of_dist_le_of_summable
      (fun n ↦ FusionSchedule.stageError (L + n)) hstep
      (FusionSchedule.summable_stageError_add L)
  simpa only [Nat.add_comm] using hcauchy

/-- The local character obtained as the pointwise limit of a certified run. -/
def limitCharacter (R : FusionRun G) : G →+ UnitAddCircle :=
  pointwiseLimitCharacter R.character R.cauchySeq

theorem tendsto_limitCharacter (R : FusionRun G) (g : G) :
    Tendsto (fun l ↦ R.character l g) atTop (nhds (R.limitCharacter g)) :=
  tendsto_pointwiseLimitCharacter R.character R.cauchySeq g

/-- The final value of a retained point is bounded by twice the stage error: one stage error
when the point is introduced, plus the subsequent geometric tail. -/
theorem norm_limitCharacter_le_of_mem_retained (R : FusionRun G)
    (l : ℕ) {g : G} (hg : g ∈ R.retained l) :
    ‖R.limitCharacter g‖ ≤ 2 * FusionSchedule.stageError l := by
  have htail : ∀ n : ℕ,
      dist (R.character (l + 1 + n) g) (R.character (l + 1 + n + 1) g) ≤
        FusionSchedule.stageError (l + 1 + n) := by
    intro n
    apply R.protected_step
    apply R.retained_protected l g hg
    omega
  have hconv : Tendsto (fun n ↦ R.character (l + 1 + n) g) atTop
      (nhds (R.limitCharacter g)) := by
    have hshift :=
      (R.tendsto_limitCharacter g).comp (tendsto_add_atTop_nat (l + 1))
    change Tendsto (fun n ↦ R.character (n + (l + 1)) g) atTop
      (nhds (R.limitCharacter g)) at hshift
    simpa only [Nat.add_comm] using hshift
  have hdist : dist (R.character (l + 1) g) (R.limitCharacter g) ≤
      2 * FusionSchedule.stageError (l + 1) := by
    have := dist_le_tsum_of_dist_le_of_tendsto₀
      (fun n ↦ FusionSchedule.stageError (l + 1 + n)) htail
      (FusionSchedule.summable_stageError_add (l + 1)) hconv
    simpa only [FusionSchedule.tsum_stageError_add] using this
  calc
    ‖R.limitCharacter g‖ ≤
        ‖R.character (l + 1) g‖ +
          dist (R.character (l + 1) g) (R.limitCharacter g) := by
      simpa [dist_eq_norm, norm_sub_rev] using
        norm_add_le (R.character (l + 1) g)
          (R.limitCharacter g - R.character (l + 1) g)
    _ ≤ FusionSchedule.stageError l +
          2 * FusionSchedule.stageError (l + 1) :=
      add_le_add (R.retained_at_stage l g hg) hdist
    _ = 2 * FusionSchedule.stageError l := by
      have herr : FusionSchedule.stageError (l + 1) =
          FusionSchedule.stageError l / 2 := by
        simpa using FusionSchedule.stageError_add l 1
      rw [herr]
      ring

/-! ## Initial detection -/

/-- If a distinguished point is protected at every stage and has prescribed initial value, its
limit remains close to that value. -/
theorem dist_limitCharacter_le_initial (R : FusionRun G) (x : G)
    (hprotect : ∀ l, x ∈ R.guardSet l) :
    dist (R.character 0 x) (R.limitCharacter x) ≤
      ∑' l, FusionSchedule.stageError l := by
  have h := dist_le_tsum_of_dist_le_of_tendsto
    FusionSchedule.stageError (fun l ↦ R.protected_step l x (hprotect l))
    FusionSchedule.summable_stageError (R.tendsto_limitCharacter x) 0
  simpa only [zero_add] using h

/-- Starting at the half-period and protecting `x` throughout makes the limiting character
nonzero. -/
theorem limitCharacter_ne_zero_of_initial_half (R : FusionRun G) {x : G}
    (hhalf : R.character 0 x = ((1 / 2 : ℝ) : UnitAddCircle))
    (hprotect : ∀ l, x ∈ R.guardSet l) :
    R.limitCharacter x ≠ 0 := by
  intro hzero
  have hdist := R.dist_limitCharacter_le_initial x hprotect
  rw [hhalf, hzero, dist_zero_right, AddCircle.norm_half_period_eq,
    FusionSchedule.tsum_stageError] at hdist
  norm_num at hdist

/-! ## Retained blocks imply local ultrafilter admissibility -/

/-- Abstract block data associated with one relevant code in the local closure. -/
structure CodeBlocks (R : FusionRun G) where
  /-- The ultrafilter used for this code. -/
  p : Ultrafilter ℕ
  /-- The finite block at each stage label. -/
  block : ℕ → Finset ℕ
  /-- The stages assigned to this code. -/
  labels : Set ℕ
  /-- The positions deleted from each block. -/
  deletions : ℕ → Finset ℕ
  /-- The local group difference represented by each position. -/
  difference : ℕ → G
  retained_mem : (⋃ l ∈ labels, ↑(block l \ deletions l)) ∈ p
  retained_in_stage : ∀ l n, l ∈ labels → n ∈ block l \ deletions l →
    difference n ∈ R.retained l

/-- On every retained index, the norm of the limiting character is controlled by twice the
stage error of the unique block containing that index. -/
theorem norm_limit_difference_le_on_retained (R : FusionRun G) (B : CodeBlocks R)
    {n : ℕ} (hn : n ∈ ⋃ l ∈ B.labels, ↑(B.block l \ B.deletions l)) :
    ∃ l ∈ B.labels, n ∈ B.block l \ B.deletions l ∧
      ‖R.limitCharacter (B.difference n)‖ ≤
        2 * FusionSchedule.stageError l := by
  simp only [Set.mem_iUnion] at hn
  obtain ⟨l, hl⟩ := hn
  obtain ⟨hlab, hnblock⟩ := hl
  refine ⟨l, hlab, hnblock, ?_⟩
  exact R.norm_limitCharacter_le_of_mem_retained
    l (B.retained_in_stage l n hlab hnblock)

/-- Concrete block-position version of `tendsto_limit_difference_zero`.  Here freeness of the
ultrafilter and the partition theorem for `blockPositions` supply the required divergence of
block labels automatically. -/
theorem tendsto_limit_difference_zero_of_blockPositions (R : FusionRun G)
    (B : CodeBlocks R) (N : ℕ → ℕ) (hN : ∀ l, 0 < N l)
    (hp : (B.p : Filter ℕ) ≤ cofinite)
    (hblock : ∀ l, B.block l = TriangularPreprocess.blockPositions N hN l) :
    Tendsto (fun n ↦ R.limitCharacter (B.difference n)) B.p (nhds 0) := by
  apply tendsto_zero_of_norm_le_stageError_on_mem N hN hp B.retained_mem
  intro n hn
  obtain ⟨l, _hlab, hnblock, hnorm⟩ :=
    R.norm_limit_difference_le_on_retained B hn
  have hnposition : n ∈ TriangularPreprocess.blockPositions N hN l := by
    simpa only [← hblock l] using (Finset.mem_sdiff.mp hnblock).1
  have hlabel : TriangularPreprocess.blockOf N hN n = l :=
    (TriangularPreprocess.mem_blockPositions_iff N hN).mp hnposition
  simpa only [hlabel] using hnorm

/-- Additivity turns convergence of the differences into the required local admissibility
equation. -/
theorem tendsto_limit_prepared (R : FusionRun G) (B : CodeBlocks R)
    (prepared : ℕ → G) (basis : G)
    (hdifference : ∀ n, B.difference n = prepared n - basis)
    (hzero : Tendsto (fun n ↦ R.limitCharacter (B.difference n)) B.p (nhds 0)) :
    Tendsto (fun n ↦ R.limitCharacter (prepared n)) B.p
      (nhds (R.limitCharacter basis)) := by
  have heq : ∀ n, R.limitCharacter (prepared n) =
      R.limitCharacter (B.difference n) + R.limitCharacter basis := by
    intro n
    have hgroup : prepared n = B.difference n + basis := by
      rw [hdifference]
      abel
    rw [hgroup, map_add]
  have hadd : Tendsto
      (fun n ↦ R.limitCharacter (B.difference n) + R.limitCharacter basis) B.p
      (nhds (R.limitCharacter basis)) := by
    simpa using hzero.add_const (R.limitCharacter basis)
  exact hadd.congr' (Eventually.of_forall fun n ↦ (heq n).symm)

end FusionRun

/-! ## A generic concrete scheduling recursion -/

/-- The finite state before stage `l`: its character and the union of every set retained at
earlier stages.  The cardinality invariant is the exact invariant used by `protectedBound`. -/
structure FusionState (G : Type) [AddCommGroup G] (l : ℕ) where
  /-- The character constructed before stage `l`. -/
  character : G →+ UnitAddCircle
  /-- The union of all finite sets retained before stage `l`. -/
  pastRetained : Finset G
  pastRetained_card_le : pastRetained.card ≤ FusionSchedule.accumulatedSize l

/-- The stage guard contains the distinguished point, an initial segment of a surjective
enumeration, and every point retained before the stage. -/
def stageGuard {G : Type} [AddCommGroup G] [DecidableEq G]
    (enumeration : ℕ → G) (x : G) (l : ℕ) (S : FusionState G l) : Finset G :=
  S.pastRetained ∪ {x} ∪ (Finset.range (l + 1)).image enumeration

theorem stageGuard_card_le {G : Type} [AddCommGroup G] [DecidableEq G]
    (enumeration : ℕ → G) (x : G) (l : ℕ) (S : FusionState G l) :
    (stageGuard enumeration x l S).card ≤ FusionSchedule.protectedBound l := by
  calc
    (stageGuard enumeration x l S).card ≤
        (S.pastRetained ∪ {x}).card +
          ((Finset.range (l + 1)).image enumeration).card :=
      Finset.card_union_le _ _
    _ ≤ (S.pastRetained.card + 1) + (l + 1) := by
      apply Nat.add_le_add
      · exact (Finset.card_union_le S.pastRetained {x}).trans_eq (by simp)
      · exact (Finset.card_image_le.trans_eq (Finset.card_range (l + 1)))
    _ = S.pastRetained.card + l + 2 := by omega
    _ ≤ FusionSchedule.accumulatedSize l + l + 2 := by
      exact Nat.add_le_add_right
        (Nat.add_le_add_right S.pastRetained_card_le l) 2
    _ ≤ FusionSchedule.protectedBound l :=
      FusionSchedule.accumulatedSize_add_le_protectedBound l

/-- All data selected at one fusion stage. -/
structure FusionStep {G : Type} [AddCommGroup G] [DecidableEq G]
    (fresh : ℕ → Finset G) (enumeration : ℕ → G) (x : G)
    (l : ℕ) (S : FusionState G l) where
  /-- The subset of the fresh block retained at this stage. -/
  retained : Finset G
  /-- The character produced by this stage. -/
  next : G →+ UnitAddCircle
  retained_subset : retained ⊆ fresh l
  deleted_card_le : (fresh l \ retained).card ≤ (stageGuard enumeration x l S).card
  protected_closeness : ∀ g ∈ stageGuard enumeration x l S,
    dist (S.character g) (next g) ≤ FusionSchedule.stageError l
  retained_small : ∀ g ∈ retained, ‖next g‖ ≤ FusionSchedule.stageError l

/-- The finite deletion/fusion theorem supplies the next state at every stage. -/
theorem fusionStep_nonempty
    {G : Type} [AddCommGroup G] [DecidableEq G]
    (fresh : ℕ → Finset G) (enumeration : ℕ → G) (x : G)
    (hfresh_card : ∀ l, (fresh l).card ≤ FusionSchedule.blockSize l)
    (hfresh_independent : ∀ l,
      BoundedIndependent (FusionSchedule.stageIndependenceBound l) (fresh l))
    (l : ℕ) (S : FusionState G l) :
    Nonempty (FusionStep fresh enumeration x l S) := by
  classical
  obtain ⟨Y, next, hsubset, hdeleted, hprotected, hsmall⟩ :=
    exists_character_after_deletion l (stageGuard enumeration x l S) (fresh l)
      (stageGuard_card_le enumeration x l S) (hfresh_card l)
      (hfresh_independent l) S.character
  exact ⟨⟨Y, next, hsubset, hdeleted,
    fun g hg ↦ by
      simpa [dist_eq_norm, norm_sub_rev] using le_of_lt (hprotected g hg),
    fun g hg ↦ le_of_lt (hsmall g hg)⟩⟩

/-- A stage choice, fixed once and reused by both the state recursion and its certificate. -/
def chosenFusionStep
    {G : Type} [AddCommGroup G] [DecidableEq G]
    (fresh : ℕ → Finset G) (enumeration : ℕ → G) (x : G)
    (hfresh_card : ∀ l, (fresh l).card ≤ FusionSchedule.blockSize l)
    (hfresh_independent : ∀ l,
      BoundedIndependent (FusionSchedule.stageIndependenceBound l) (fresh l))
    (l : ℕ) (S : FusionState G l) : FusionStep fresh enumeration x l S :=
  Classical.choice
    (fusionStep_nonempty fresh enumeration x hfresh_card hfresh_independent l S)

/-- Update the state using the single chosen stage certificate. -/
def nextFusionState
    {G : Type} [AddCommGroup G] [DecidableEq G]
    (fresh : ℕ → Finset G) (enumeration : ℕ → G) (x : G)
    (hfresh_card : ∀ l, (fresh l).card ≤ FusionSchedule.blockSize l)
    (hfresh_independent : ∀ l,
      BoundedIndependent (FusionSchedule.stageIndependenceBound l) (fresh l))
    (l : ℕ) (S : FusionState G l) : FusionState G (l + 1) where
  character :=
    (chosenFusionStep fresh enumeration x hfresh_card hfresh_independent l S).next
  pastRetained := S.pastRetained ∪
    (chosenFusionStep fresh enumeration x hfresh_card hfresh_independent l S).retained
  pastRetained_card_le := by
    calc
      (S.pastRetained ∪
          (chosenFusionStep fresh enumeration x hfresh_card hfresh_independent l S).retained).card
          ≤ S.pastRetained.card +
            (chosenFusionStep fresh enumeration x hfresh_card hfresh_independent
              l S).retained.card :=
        Finset.card_union_le _ _
      _ ≤ FusionSchedule.accumulatedSize l + FusionSchedule.blockSize l := by
        apply Nat.add_le_add S.pastRetained_card_le
        exact (Finset.card_le_card
          (chosenFusionStep fresh enumeration x hfresh_card
            hfresh_independent l S).retained_subset).trans
            (hfresh_card l)
      _ = FusionSchedule.accumulatedSize (l + 1) :=
        (FusionSchedule.accumulatedSize_succ l).symm

/-- The dependent natural-number recursion starting from `initial`. -/
def fusionStates
    {G : Type} [AddCommGroup G] [DecidableEq G]
    (fresh : ℕ → Finset G) (enumeration : ℕ → G) (x : G)
    (hfresh_card : ∀ l, (fresh l).card ≤ FusionSchedule.blockSize l)
    (hfresh_independent : ∀ l,
      BoundedIndependent (FusionSchedule.stageIndependenceBound l) (fresh l))
    (initial : G →+ UnitAddCircle) : (l : ℕ) → FusionState G l
  | 0 => ⟨initial, ∅, by simp⟩
  | l + 1 => nextFusionState fresh enumeration x hfresh_card hfresh_independent l
      (fusionStates fresh enumeration x hfresh_card hfresh_independent initial l)

@[simp] theorem fusionStates_zero
    {G : Type} [AddCommGroup G] [DecidableEq G]
    (fresh : ℕ → Finset G) (enumeration : ℕ → G) (x : G)
    (hfresh_card : ∀ l, (fresh l).card ≤ FusionSchedule.blockSize l)
    (hfresh_independent : ∀ l,
      BoundedIndependent (FusionSchedule.stageIndependenceBound l) (fresh l))
    (initial : G →+ UnitAddCircle) :
    (fusionStates fresh enumeration x hfresh_card hfresh_independent initial 0).character =
      initial := rfl

/- The rest of the construction uses shorter local names. -/
section ScheduledConstruction

variable {G : Type} [AddCommGroup G] [DecidableEq G]
variable (fresh : ℕ → Finset G) (enumeration : ℕ → G) (x : G)
variable (hfresh_card : ∀ l, (fresh l).card ≤ FusionSchedule.blockSize l)
variable (hfresh_independent : ∀ l,
  BoundedIndependent (FusionSchedule.stageIndependenceBound l) (fresh l))
variable (initial : G →+ UnitAddCircle)

private abbrev states (l : ℕ) : FusionState G l :=
  fusionStates fresh enumeration x hfresh_card hfresh_independent initial l

private abbrev step (l : ℕ) : FusionStep fresh enumeration x l (states fresh enumeration x
    hfresh_card hfresh_independent initial l) :=
  chosenFusionStep fresh enumeration x hfresh_card hfresh_independent l
    (states fresh enumeration x hfresh_card hfresh_independent initial l)

theorem fusionStates_pastRetained_subset_succ (l : ℕ) :
    (states fresh enumeration x hfresh_card hfresh_independent initial l).pastRetained ⊆
      (states fresh enumeration x hfresh_card hfresh_independent initial (l + 1)).pastRetained := by
  intro g hg
  change g ∈ (nextFusionState fresh enumeration x hfresh_card hfresh_independent l
    (states fresh enumeration x hfresh_card hfresh_independent initial l)).pastRetained
  exact Finset.mem_union_left _ hg

theorem fusionStates_pastRetained_mono : Monotone fun l ↦
    (states fresh enumeration x hfresh_card hfresh_independent initial l).pastRetained :=
  monotone_nat_of_le_succ
    (fusionStates_pastRetained_subset_succ fresh enumeration x hfresh_card
      hfresh_independent initial)

/-- The fully scheduled run associated with a chosen initial character. -/
def scheduledRun (henumeration : Function.Surjective enumeration) : FusionRun G where
  character := fun l ↦
    (states fresh enumeration x hfresh_card hfresh_independent initial l).character
  guardSet := fun l ↦ stageGuard enumeration x l
    (states fresh enumeration x hfresh_card hfresh_independent initial l)
  retained := fun l ↦ (step fresh enumeration x hfresh_card hfresh_independent initial l).retained
  eventually_protected := by
    intro g
    obtain ⟨n, rfl⟩ := henumeration g
    rw [eventually_atTop]
    refine ⟨n, fun l hl ↦ ?_⟩
    exact Finset.mem_union_right _
      (Finset.mem_image.mpr
        ⟨n, Finset.mem_range.mpr (Nat.lt_succ_of_le hl), rfl⟩)
  protected_step := by
    intro l g hg
    change dist
      ((states fresh enumeration x hfresh_card hfresh_independent initial l).character g)
      ((step fresh enumeration x hfresh_card hfresh_independent initial l).next g) ≤ _
    exact
      (step fresh enumeration x hfresh_card hfresh_independent initial l).protected_closeness g hg
  retained_at_stage := by
    intro l g hg
    change ‖(step fresh enumeration x hfresh_card hfresh_independent initial l).next g‖ ≤ _
    exact (step fresh enumeration x hfresh_card hfresh_independent initial l).retained_small g hg
  retained_protected := by
    intro l g hg k hlk
    have hgNext :
        g ∈ (states fresh enumeration x hfresh_card hfresh_independent
          initial (l + 1)).pastRetained := by
      change g ∈
        (states fresh enumeration x hfresh_card hfresh_independent initial l).pastRetained ∪
          (step fresh enumeration x hfresh_card hfresh_independent initial l).retained
      exact Finset.mem_union_right _ hg
    have hgPast : g ∈
        (states fresh enumeration x hfresh_card hfresh_independent initial k).pastRetained :=
      fusionStates_pastRetained_mono fresh enumeration x hfresh_card
        hfresh_independent initial hlk hgNext
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hgPast)

/-- Public certificate exported by the scheduling recursion. -/
structure ScheduledRunCertificate where
  /-- The certified infinite fusion run. -/
  run : FusionRun G
  initial_half : run.character 0 x = ((1 / 2 : ℝ) : UnitAddCircle)
  distinguished_protected : ∀ l, x ∈ run.guardSet l
  retained_subset : ∀ l, run.retained l ⊆ fresh l
  deleted_card_le : ∀ l,
    (fresh l \ run.retained l).card ≤ (run.guardSet l).card
  guard_card_le : ∀ l,
    (run.guardSet l).card ≤ FusionSchedule.protectedBound l

/-- Starting with the exact half-turn character and applying the dependent recursion produces a
complete certified run; no run is assumed as input. -/
theorem exists_scheduledRunCertificate_of_initial_half
    (hfresh_card : ∀ l, (fresh l).card ≤ FusionSchedule.blockSize l)
    (hfresh_independent : ∀ l,
      BoundedIndependent (FusionSchedule.stageIndependenceBound l) (fresh l))
    (hinitial : initial x = ((1 / 2 : ℝ) : UnitAddCircle))
    (henumeration : Function.Surjective enumeration) :
    Nonempty (ScheduledRunCertificate fresh x) := by
  classical
  -- The parameter `initial` is replaced below by the character chosen from `hx`; this theorem
  -- is stated in its more useful existential form just after the section.
  exact ⟨{
    run := scheduledRun fresh enumeration x hfresh_card hfresh_independent initial henumeration
    initial_half := by
      simpa only [scheduledRun, fusionStates_zero] using hinitial
    distinguished_protected := by
      intro l
      exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self x))
    retained_subset := by
      intro l
      exact (step fresh enumeration x hfresh_card hfresh_independent initial l).retained_subset
    deleted_card_le := by
      intro l
      exact (step fresh enumeration x hfresh_card hfresh_independent initial l).deleted_card_le
    guard_card_le := by
      intro l
      exact stageGuard_card_le enumeration x l
        (states fresh enumeration x hfresh_card hfresh_independent initial l) }⟩

end ScheduledConstruction

/-- Fully existential form of the generic scheduling recursion. -/
theorem exists_scheduledRunCertificate
    {G : Type} [AddCommGroup G] [IsAddTorsionFree G] [DecidableEq G]
    (fresh : ℕ → Finset G) (enumeration : ℕ → G) (x : G)
    (hx : x ≠ 0)
    (hfresh_card : ∀ l, (fresh l).card ≤ FusionSchedule.blockSize l)
    (hfresh_independent : ∀ l,
      BoundedIndependent (FusionSchedule.stageIndependenceBound l) (fresh l))
    (henumeration : Function.Surjective enumeration) :
    Nonempty (ScheduledRunCertificate fresh x) := by
  obtain ⟨initial, hinitial⟩ := exists_character_apply_eq_half hx
  exact exists_scheduledRunCertificate_of_initial_half
    (fresh := fresh) (enumeration := enumeration) (x := x)
    (initial := initial) hfresh_card hfresh_independent hinitial henumeration

/-! ## Interface from concrete runs to the global assembly -/

open TriangularPreprocess ConcreteData ConcreteClosure ConcreteLocalSetup

/-- The block certificate for one code in the countable closure.  In addition to the analytic
`CodeBlocks` data it identifies the abstract fields with the concrete prepared sequence,
ultrafilter, and block partition. -/
structure ConcreteCodeBlocks
    (N : ℕ → ℕ) (hN : ∀ l, 0 < N l) (M : ℕ → ℕ)
    (x : ContinuumFreeGroup)
    (R : FusionRun (closure N hN M x →₀ ℤ))
    (a : RelevantCode N hN M x) where
  /-- The underlying abstract retained-block data. -/
  blocks : R.CodeBlocks
  p_eq : blocks.p = ultrafilter N hN a.1
  block_eq : ∀ l, blocks.block l = blockPositions N hN l
  difference_eq : ∀ n,
    blocks.difference n = localDifference N hN M x a n

namespace ConcreteCodeBlocks

/-- A concrete retained-block certificate gives precisely the local admissibility equation for
its relevant code. -/
theorem tendsto_prepared
    {N : ℕ → ℕ} {hN : ∀ l, 0 < N l} {M : ℕ → ℕ}
    {x : ContinuumFreeGroup}
    {R : FusionRun (closure N hN M x →₀ ℤ)}
    {a : RelevantCode N hN M x}
    (C : ConcreteCodeBlocks N hN M x R a) :
    Tendsto
      (fun n ↦ R.limitCharacter
        (Finsupp.subtypeDomain (closure N hN M x) (prepared N hN M a.1 n)))
      (ultrafilter N hN a.1)
      (nhds (R.limitCharacter (Finsupp.single ⟨codeIndex a.1, a.2⟩ 1))) := by
  have hp : (C.blocks.p : Filter ℕ) ≤ cofinite := by
    rw [C.p_eq]
    exact ultrafilter_free N hN a.1
  have hzero := R.tendsto_limit_difference_zero_of_blockPositions
    C.blocks N hN hp C.block_eq
  have hdifference : ∀ n, C.blocks.difference n =
      Finsupp.subtypeDomain (closure N hN M x) (prepared N hN M a.1 n) -
        Finsupp.single ⟨codeIndex a.1, a.2⟩ 1 := by
    intro n
    rw [C.difference_eq]
    simp only [localDifference]
    ext i
    change prepared N hN M a.1 n i.val - codeBasisVector a.1 i.val =
      prepared N hN M a.1 n i.val -
        Finsupp.single ⟨codeIndex a.1, a.2⟩ 1 i
    by_cases hi : i.val = codeIndex a.1
    · have hisub : i = ⟨codeIndex a.1, a.2⟩ := Subtype.ext hi
      subst i
      simp [codeBasisVector]
    · have hisub : i ≠ ⟨codeIndex a.1, a.2⟩ := by
        intro heq
        exact hi (congrArg Subtype.val heq)
      simp [codeBasisVector, hi, hisub]
  have hprepared := R.tendsto_limit_prepared C.blocks
    (fun n ↦ Finsupp.subtypeDomain (closure N hN M x) (prepared N hN M a.1 n))
    (Finsupp.single ⟨codeIndex a.1, a.2⟩ 1) hdifference hzero
  simpa only [C.p_eq] using hprepared

end ConcreteCodeBlocks

/-- Complete local output for one distinguished nonzero vector.  This is a deliberately small
interface: a concrete scheduling recursion supplies the run and one block certificate for each
relevant code; all limiting arguments are discharged above. -/
structure LocalRunCertificate
    (N : ℕ → ℕ) (hN : ∀ l, 0 < N l) (M : ℕ → ℕ)
    (x : {x : ContinuumFreeGroup // x ≠ 0}) where
  /-- The fusion run on the countable local group generated by `x`. -/
  run : FusionRun (closure N hN M x.1 →₀ ℤ)
  self_ne_zero :
    run.limitCharacter
      (Finsupp.subtypeDomain (closure N hN M x.1) x.1) ≠ 0
  /-- A retained-block certificate for every locally relevant code. -/
  codeBlocks : ∀ a : RelevantCode N hN M x.1,
    ConcreteCodeBlocks N hN M x.1 run a

/-- The concrete run certificate satisfies the exact local interface consumed by the
transfinite-extension and global-assembly modules. -/
theorem LocalRunCertificate.locallyAdmissible
    {N : ℕ → ℕ} {hN : ∀ l, 0 < N l} {M : ℕ → ℕ}
    {x : {x : ContinuumFreeGroup // x ≠ 0}}
    (C : LocalRunCertificate N hN M x) :
    TransfiniteExtension.LocallyAdmissible
      (transfiniteData N hN M) (closure N hN M x.1) C.run.limitCharacter := by
  intro a ha
  exact (C.codeBlocks ⟨a, ha⟩).tendsto_prepared

/-- It is enough to construct a certified concrete fusion run for every nonzero vector. -/
theorem hasLocalSeparatingCharacters_of_certificates
    (N : ℕ → ℕ) (hN : ∀ l, 0 < N l) (M : ℕ → ℕ)
    (H : ∀ x : {x : ContinuumFreeGroup // x ≠ 0},
      Nonempty (LocalRunCertificate N hN M x)) :
    GlobalAssembly.HasLocalSeparatingCharacters N hN M := by
  intro x
  let C : LocalRunCertificate N hN M x := Classical.choice (H x)
  exact ⟨C.run.limitCharacter, C.self_ne_zero, C.locallyAdmissible⟩

end

end LocalFusion
end Wallace
