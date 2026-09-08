/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/

import Mathlib.Analysis.SpecificLimits.Basic
import LeanPool.Wallace.FiniteCombinatorics
import LeanPool.Wallace.UniformKronecker

/-!
# A concrete schedule for the Wallace fusion

This file fixes, once and for all, the numerical parameters used by the character-fusion
construction.  At stage `l`, `accumulatedSize l` is the total size allotted to all earlier
blocks, `protectedBound l` bounds the finite set whose character values must be protected, and
`blockSize l` is the size of the new block.  The identity

`blockSize l = (l + 2) * protectedBound l`

makes the discarded proportion tend to zero.  The errors form a geometric series of total mass
`1 / 32`, leaving a large margin around an initial character value of `1 / 2`.
-/

open Filter Topology

namespace Wallace
namespace FusionSchedule

noncomputable section

open FiniteCombinatorics

/-- Total number of positions allotted to blocks strictly before stage `l`. -/
def accumulatedSize : ℕ → ℕ
  | 0 => 0
  | l + 1 =>
      accumulatedSize l + (l + 2) * (accumulatedSize l + 2 * l + 2)

/-- Cardinality bound for the protected set at stage `l`. -/
def protectedBound (l : ℕ) : ℕ :=
  accumulatedSize l + 2 * l + 2

/-- Size of the fresh finite block at stage `l`. -/
def blockSize (l : ℕ) : ℕ :=
  (l + 2) * protectedBound l

@[simp]
theorem accumulatedSize_succ (l : ℕ) :
    accumulatedSize (l + 1) = accumulatedSize l + blockSize l := by
  rfl

theorem protectedBound_pos (l : ℕ) : 0 < protectedBound l := by
  simp only [protectedBound]
  omega

theorem accumulatedSize_add_le_protectedBound (l : ℕ) :
    accumulatedSize l + l + 2 ≤ protectedBound l := by
  simp only [protectedBound]
  omega

theorem protectedBound_ne_zero (l : ℕ) : protectedBound l ≠ 0 :=
  Nat.ne_of_gt (protectedBound_pos l)

theorem blockSize_pos (l : ℕ) : 0 < blockSize l := by
  simp only [blockSize]
  exact Nat.mul_pos (by omega) (protectedBound_pos l)

/-- The exact discarded-proportion identity behind the density-one argument. -/
theorem protectedBound_div_blockSize (l : ℕ) :
    (protectedBound l : ℝ) / (blockSize l : ℝ) =
      1 / ((l : ℝ) + 2) := by
  rw [blockSize, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  field_simp [protectedBound_ne_zero l]

/-- The proportion of a block which bounded deletion may discard tends to zero. -/
theorem tendsto_protectedBound_div_blockSize :
    Tendsto (fun l : ℕ ↦ (protectedBound l : ℝ) / (blockSize l : ℝ))
      atTop (nhds 0) := by
  have hshift := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
    (tendsto_add_atTop_nat 1)
  have hmain : Tendsto (fun l : ℕ ↦ 1 / ((l : ℝ) + 2)) atTop (nhds 0) := by
    convert hshift using 1
    ext l
    simp only [Function.comp_def, Nat.cast_add, Nat.cast_one]
    ring
  exact hmain.congr' (Eventually.of_forall fun l ↦ (protectedBound_div_blockSize l).symm)

/-- Stage error.  In elementary notation this is `2^(-(l+6))`. -/
def stageError (l : ℕ) : ℝ :=
  (1 / 32 : ℝ) / 2 / 2 ^ l

theorem stageError_pos (l : ℕ) : 0 < stageError l := by
  simp only [stageError]
  positivity

/-- Exact geometric-tail identity, convenient for the completeness estimate. -/
theorem stageError_add (L n : ℕ) :
    stageError (L + n) = stageError L / 2 ^ n := by
  simp only [stageError, pow_add]
  ring

/-- The tail beginning at stage `L` has total mass exactly `2 * stageError L`. -/
theorem hasSum_stageError_add (L : ℕ) :
    HasSum (fun n : ℕ ↦ stageError (L + n)) (2 * stageError L) := by
  convert hasSum_geometric_two' (2 * stageError L) using 1
  ext n
  rw [stageError_add]
  ring

theorem summable_stageError_add (L : ℕ) :
    Summable (fun n : ℕ ↦ stageError (L + n)) :=
  (hasSum_stageError_add L).summable

theorem tsum_stageError_add (L : ℕ) :
    ∑' n : ℕ, stageError (L + n) = 2 * stageError L :=
  (hasSum_stageError_add L).tsum_eq

theorem summable_stageError : Summable stageError := by
  change Summable (fun n : ℕ ↦ (1 / 32 : ℝ) / 2 / 2 ^ n)
  exact summable_geometric_two' (1 / 32 : ℝ)

theorem tendsto_stageError : Tendsto stageError atTop (nhds 0) :=
  summable_stageError.tendsto_atTop_zero

/-- The total perturbation budget of the entire fusion is `1/32`. -/
theorem tsum_stageError : ∑' l : ℕ, stageError l = (1 / 32 : ℝ) := by
  change (∑' n : ℕ, (1 / 32 : ℝ) / 2 / 2 ^ n) = 1 / 32
  exact tsum_geometric_two' (1 / 32 : ℝ)

/-- Independence threshold used before the bounded-deletion step. -/
def independenceBound (l Q : ℕ) : ℕ :=
  deletionIndependenceBound (protectedBound l) Q

/-! ## Uniform Kronecker and deletion bounds -/

/-- Maximum tuple length which can occur at stage `l`. -/
def tupleLengthBound (l : ℕ) : ℕ :=
  protectedBound l + blockSize l

/-- One uniform Kronecker bound for a fixed tuple length.  All groups in the Wallace
construction live in universe zero, so fixing that universe here makes the numerical schedule
literally a single sequence of natural numbers. -/
noncomputable def rawKroneckerBound (l m : ℕ) : ℕ :=
  Classical.choose (exists_uniformKroneckerBound.{0} m (stageError_pos l))

theorem rawKroneckerBound_spec (l m : ℕ) :
    IsUniformKroneckerBound.{0} m (stageError l) (rawKroneckerBound l m) :=
  Classical.choose_spec (exists_uniformKroneckerBound.{0} m (stageError_pos l))

/-- A single relation-height bound which works for every *positive* tuple length possible at
stage `l`.  This is the paper's maximum over `1 ≤ m ≤ R_l + N_l`; the maximum with `1` is used
by the finite disjointness argument.  The empty-tuple case is handled separately below and does
not enter the numerical schedule. -/
noncomputable def kroneckerBound (l : ℕ) : ℕ :=
  max 1 ((Finset.Icc 1 (tupleLengthBound l)).sup (rawKroneckerBound l))

theorem one_le_kroneckerBound (l : ℕ) : 1 ≤ kroneckerBound l := by
  exact Nat.le_max_left _ _

theorem rawKroneckerBound_le (l m : ℕ) (hm0 : 0 < m)
    (hm : m ≤ tupleLengthBound l) :
    rawKroneckerBound l m ≤ kroneckerBound l := by
  apply le_trans _ (Nat.le_max_right 1 _)
  apply Finset.le_sup
  exact Finset.mem_Icc.mpr ⟨hm0, hm⟩

/-- The uniform Kronecker assertion is vacuous for an empty tuple, so no value `q(0, ε_l)` is
needed in the paper's maximum. -/
theorem kroneckerBound_spec_zero (l : ℕ) :
    IsUniformKroneckerBound.{0} 0 (stageError l) (kroneckerBound l) := by
  intro G _inst z t _ht
  exact ⟨0, fun i ↦ Fin.elim0 i⟩

/-- The scheduled height bound is valid for every tuple that can occur at this stage. -/
theorem kroneckerBound_spec (l m : ℕ) (hm : m ≤ tupleLengthBound l) :
    IsUniformKroneckerBound.{0} m (stageError l) (kroneckerBound l) :=
  by
    rcases m with _ | m
    · exact kroneckerBound_spec_zero l
    · exact IsUniformKroneckerBound.mono (rawKroneckerBound_spec l (m + 1))
        (rawKroneckerBound_le l (m + 1) (Nat.succ_pos m) hm)

/-- The independence threshold `M_l` used in the preprocessing of stage `l`. -/
noncomputable def stageIndependenceBound (l : ℕ) : ℕ :=
  independenceBound l (kroneckerBound l)

theorem card_union_le_tupleLengthBound {G : Type*} [DecidableEq G]
    {l : ℕ} {A Y : Finset G}
    (hA : A.card ≤ protectedBound l) (hY : Y.card ≤ blockSize l) :
    (A ∪ Y).card ≤ tupleLengthBound l := by
  calc
    (A ∪ Y).card ≤ A.card + Y.card := Finset.card_union_le A Y
    _ ≤ protectedBound l + blockSize l := Nat.add_le_add hA hY
    _ = tupleLengthBound l := rfl

/-- The bounded-deletion lemma specialized to the numerical schedule. -/
theorem exists_stage_deletion {G : Type*} [AddCommGroup G] [DecidableEq G]
    {l : ℕ} (A X : Finset G) (hA : A.card ≤ protectedBound l)
    (hX : BoundedIndependent (stageIndependenceBound l) X) :
    ∃ Y : Finset G, Y ⊆ X ∧ (X \ Y).card ≤ A.card ∧
      MixedRelationFree (kroneckerBound l) A Y := by
  classical
  simpa only [stageIndependenceBound, independenceBound] using
    bounded_deletion (protectedBound l) (kroneckerBound l) A X hA hX

end

end FusionSchedule
end Wallace
