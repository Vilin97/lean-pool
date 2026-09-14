/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import LeanPool.Schoenflies.QuantitativeForwardStages

/-!
# The recursive quantitative stage construction

This module iterates the two-sided quantitative successor. Window centres are
read from a recurrent sequence and all three quantitative parameters use a dyadic scale.
-/

open Filter Metric Set

namespace Schoenflies

variable {γ : Type*} {S₀ : CellStructure γ} {C : Set Plane}

/-- The external choices needed by the quantitative recursion.  `centreBase` will be wrapped
by `recur`, so every one of its values occurs at arbitrarily late stages. -/
structure QuantitativeSchedule (C : Set Plane) where
  centreBase : ℕ → Plane
  centreBase_mem : ∀ n, centreBase n ∈ inside C
  anchors : ℕ → List Plane

namespace QuantitativeSchedule

variable (q : QuantitativeSchedule C)

/-- The recurrent centre used at stage `n`. -/
def centre (n : ℕ) : Plane := recur q.centreBase n

theorem centre_mem (n : ℕ) : q.centre n ∈ inside C := q.centreBase_mem _

end QuantitativeSchedule

/-- The dyadic window and source-mesh scale at successor `n`. -/
noncomputable def dyadicScale (n : ℕ) : ℝ := ((2 : ℝ) ^ n)⁻¹ / 2

theorem dyadicScale_pos (n : ℕ) : 0 < dyadicScale n := by
  rw [dyadicScale]
  positivity

theorem tendsto_dyadicScale : Tendsto dyadicScale atTop (nhds 0) := by
  change Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹ / 2) atTop (nhds 0)
  simpa only [zero_div] using tendsto_two_pow_neg.div_const (2 : ℝ)

/-- The target bound leaves an inessential factor four for the initial-stage estimate. -/
noncomputable def dyadicTargetBound (n : ℕ) : ℝ := 4 * dyadicScale n

theorem dyadicTargetBound_pos (n : ℕ) : 0 < dyadicTargetBound n :=
  mul_pos (by norm_num) (dyadicScale_pos n)

theorem tendsto_dyadicTargetBound :
    Tendsto dyadicTargetBound atTop (nhds 0) := by
  change Tendsto (fun n => 4 * dyadicScale n) atTop (nhds 0)
  simpa only [mul_zero] using tendsto_const_nhds.mul tendsto_dyadicScale

/-- A target-star bound indexed by the actual stages.  The initial pair receives one coarse
bound; every successor uses the estimate established when it was constructed. -/
noncomputable def quantitativeTargetEps : ℕ → ℝ
  | 0 => 4
  | n + 1 => dyadicTargetBound n

theorem tendsto_quantitativeTargetEps :
    Tendsto quantitativeTargetEps atTop (nhds 0) := by
  apply (tendsto_add_atTop_iff_nat (f := quantitativeTargetEps) 1).mp
  simpa only [quantitativeTargetEps] using tendsto_dyadicTargetBound

variable [Infinite γ]
  (P₀ : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1))
  (hC : IsSeparating C) (hcycle : S₀.OuterEdgesFormCycle)
  (q : QuantitativeSchedule C)

/-- Choose a quantitative successor at stage `n`. -/
noncomputable def scheduledQuantitativeSuccessor
    (n : ℕ)
    (P : GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1)) :
    QuantitativeSuccessor P (q.anchors n) (q.centre n)
      (dyadicScale n) (dyadicScale n) (dyadicTargetBound n) :=
  Classical.choice (P.exists_quantitativeSuccessor hC hcycle (q.anchors n)
    (q.centre_mem n) (dyadicScale_pos n) (dyadicScale_pos n)
      (dyadicTargetBound_pos n))

/-- The recursively chosen generated pairs. -/
noncomputable def quantitativeStage : ℕ →
    GeneratedPair S₀ C (C ∪ inside C) modelCurve (Plane.closedSquare 0 1) :=
  fun n => Nat.rec P₀
    (fun k P => (scheduledQuantitativeSuccessor hC hcycle q k P).pair) n

@[simp] theorem quantitativeStage_zero :
    quantitativeStage P₀ hC hcycle q 0 = P₀ := rfl

@[simp] theorem quantitativeStage_succ (n : ℕ) :
    quantitativeStage P₀ hC hcycle q (n + 1) =
      (scheduledQuantitativeSuccessor hC hcycle q n
        (quantitativeStage P₀ hC hcycle q n)).pair := by
  rfl

/-- The composite parent map selected at successor `n`. -/
noncomputable def quantitativeParent (n : ℕ) : γ → γ :=
  (scheduledQuantitativeSuccessor hC hcycle q n
    (quantitativeStage P₀ hC hcycle q n)).parent

/-- Consecutive recursively chosen stages satisfy the common transition interface. -/
theorem quantitativeTransition (n : ℕ) :
    StageTransition
      (quantitativeStage P₀ hC hcycle q (n + 1))
      (quantitativeStage P₀ hC hcycle q n)
      (quantitativeParent P₀ hC hcycle q n) := by
  rw [quantitativeStage_succ]
  exact (scheduledQuantitativeSuccessor hC hcycle q n
    (quantitativeStage P₀ hC hcycle q n)).transition

/-- Every noninitial target star satisfies the scheduled dyadic bound. -/
theorem quantitativeStage_diam_targetStar_lt (n : ℕ) {σ : γ}
    (hσ : σ ∈ (quantitativeStage P₀ hC hcycle q (n + 1)).str.cells) :
    diam ((quantitativeStage P₀ hC hcycle q (n + 1)).tgt.star σ) <
      dyadicTargetBound n := by
  rw [quantitativeStage_succ] at hσ ⊢
  exact (scheduledQuantitativeSuccessor hC hcycle q n
    (quantitativeStage P₀ hC hcycle q n)).diam_targetStar_lt hσ

/-- Every target star satisfies the stage-indexed uniform bound, including stage zero. -/
theorem quantitativeStage_diam_targetStar_le (n : ℕ) {σ : γ}
    (hσ : σ ∈ (quantitativeStage P₀ hC hcycle q n).str.cells) :
    diam ((quantitativeStage P₀ hC hcycle q n).tgt.star σ) ≤
      quantitativeTargetEps n := by
  cases n with
  | zero =>
      have hstar : P₀.tgt.star σ ⊆ Plane.closedSquare 0 1 :=
        (P₀.tgt_isCellDecomposition.star_subset_closure_domain
          P₀.str_combInvariants).trans
            (Plane.isClosed_closedSquare 0 1).closure_subset
      have hsquare : Plane.closedSquare 0 1 ⊆ ball (0 : Plane) 2 := by
        simpa only [show (2 : ℝ) / 2 = 1 by norm_num] using
          (Plane.closedSquare_subset_ball (c := (0 : Plane)) (ρ := 2) (by norm_num))
      change diam (P₀.tgt.star σ) ≤ 4
      calc
        diam (P₀.tgt.star σ) ≤ 2 * (2 : ℝ) :=
          Metric.diam_le_of_subset_closedBall (by norm_num)
            (hstar.trans (hsquare.trans ball_subset_closedBall))
        _ = 4 := by norm_num
  | succ n =>
      exact (quantitativeStage_diam_targetStar_lt P₀ hC hcycle q n hσ).le

/-- At every point caught by the stage-`n` window, the successor source star satisfies the
scheduled dyadic bound. -/
theorem quantitativeStage_diam_sourceStar_le (n : ℕ) {x : Plane}
    (hx : x ∈ openWindow C (dyadicScale n) (q.centre n)) :
    diam ((quantitativeStage P₀ hC hcycle q (n + 1)).src.star
      ((quantitativeStage P₀ hC hcycle q (n + 1)).src.carrier x)) ≤
        2 * dyadicScale n := by
  rw [quantitativeStage_succ]
  exact (scheduledQuantitativeSuccessor hC hcycle q n
    (quantitativeStage P₀ hC hcycle q n)).diam_sourceStar_le
      hC (q.centre_mem n) (dyadicScale_pos n) (dyadicScale_pos n) hx

/-- Source stars at a fixed point shrink monotonically through all later recursive stages. -/
theorem quantitativeStage_sourceStar_subset_of_le {n m : ℕ} (hnm : n ≤ m)
    {x : Plane} (hx : x ∈ C ∪ inside C) :
    (quantitativeStage P₀ hC hcycle q m).src.star
        ((quantitativeStage P₀ hC hcycle q m).src.carrier x) ⊆
      (quantitativeStage P₀ hC hcycle q n).src.star
        ((quantitativeStage P₀ hC hcycle q n).src.carrier x) := by
  induction m, hnm using Nat.le_induction with
  | base => exact subset_rfl
  | @succ m hnm ih =>
      exact ((quantitativeTransition P₀ hC hcycle q m).refines_src.star_carrier_subset
        (quantitativeStage P₀ hC hcycle q (m + 1)).str_combInvariants
        (quantitativeStage P₀ hC hcycle q m).src_isCellDecomposition
        (quantitativeStage P₀ hC hcycle q (m + 1)).src_isCellDecomposition hx).trans ih

/-- Metric density of the base centre sequence inside the Jordan domain. -/
def QuantitativeSchedule.CentresDense (q : QuantitativeSchedule C) : Prop :=
  ∀ x ∈ inside C, ∀ δ : ℝ, 0 < δ →
    ∃ k, Plane.supDist (q.centreBase k) x < δ

/-- A canonical schedule obtained by taking a dense sequence in the open Jordan domain.
The auxiliary anchor list may be empty: each target-mesh constructor adds whatever fresh
boundary anchors it needs. -/
noncomputable def denseQuantitativeSchedule (hC : IsSeparating C) :
    QuantitativeSchedule C := by
  let _ : Nonempty (inside C) := hC.isConnected_inside.nonempty.to_subtype
  exact
    { centreBase := fun n => (TopologicalSpace.denseSeq (inside C) n : Plane)
      centreBase_mem := fun n => (TopologicalSpace.denseSeq (inside C) n).property
      anchors := fun _ => [] }

theorem denseQuantitativeSchedule_centresDense (hC : IsSeparating C) :
    (denseQuantitativeSchedule hC).CentresDense := by
  let _ : Nonempty (inside C) := hC.isConnected_inside.nonempty.to_subtype
  intro x hx δ hδ
  obtain ⟨k, hk⟩ :=
    (TopologicalSpace.denseRange_denseSeq (inside C)).exists_dist_lt
      (⟨x, hx⟩ : inside C) hδ
  refine ⟨k, lt_of_le_of_lt (Plane.supDist_eq_dist_le _ _) ?_⟩
  rw [dist_comm] at hk
  simpa only [denseQuantitativeSchedule, Subtype.dist_eq] using hk

/-- The recurrent dense windows and dyadic mesh bounds force pointwise convergence of the
source-star diameters. -/
theorem tendsto_quantitativeStage_diam_sourceStar
    (hdense : q.CentresDense) {x : Plane} (hx : x ∈ inside C) :
    Tendsto (fun n => diam ((quantitativeStage P₀ hC hcycle q n).src.star
      ((quantitativeStage P₀ hC hcycle q n).src.carrier x))) atTop (nhds 0) := by
  apply Metric.tendsto_atTop.2
  intro η hη
  have hxC : x ∉ C := fun hxC => inside_subset_compl hx hxC
  have hr : 0 < supRadius C x :=
    supRadius_pos hC.isJordanCurve.isCompact hC.isJordanCurve.nonempty hxC
  obtain ⟨k, hk⟩ := hdense x hx (supRadius C x / 8) (by positivity)
  have hthreshold : 0 < min (supRadius C x / 8) (η / 2) := by positivity
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 tendsto_dyadicScale
    _ hthreshold
  obtain ⟨n, hnN₀, hncentre⟩ := exists_le_recur_eq q.centreBase k N₀
  have hnscaleDist := hN₀ n hnN₀
  have hnscale : dyadicScale n < min (supRadius C x / 8) (η / 2) := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (dyadicScale_pos n)] at hnscaleDist
    exact hnscaleDist
  have hnwindow : x ∈ openWindow C (dyadicScale n) (q.centre n) := by
    apply mem_openWindow_of_supDist_lt hC.isJordanCurve.isCompact
      hC.isJordanCurve.nonempty
    · rw [QuantitativeSchedule.centre, hncentre]
      exact hk
    · exact hnscale.trans_le (min_le_left _ _)
  have hnstar := quantitativeStage_diam_sourceStar_le P₀ hC hcycle q n hnwindow
  refine ⟨n + 1, fun m hm => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg diam_nonneg]
  exact lt_of_le_of_lt
    (Metric.diam_mono
      (quantitativeStage_sourceStar_subset_of_le P₀ hC hcycle q hm (Or.inr hx))
      ((quantitativeStage P₀ hC hcycle q (n + 1)).src_isCellDecomposition.isBounded_star
        (quantitativeStage P₀ hC hcycle q (n + 1)).str_combInvariants
        (isBounded_union_inside hC)))
    (lt_of_le_of_lt hnstar (by
      have := hnscale.trans_le (min_le_right _ _)
      linarith))

/-- The complete quantitative recursion, in the exact interface consumed by the limit-map
construction. -/
noncomputable def quantitativeStageSequence
    (hbase : S₀.CombInvariants) (hdense : q.CentresDense) :
    StageSequence γ S₀ C where
  stage := quantitativeStage P₀ hC hcycle q
  par := quantitativeParent P₀ hC hcycle q
  transition := quantitativeTransition P₀ hC hcycle q
  eps := quantitativeTargetEps
  diam_tgtStar_le := quantitativeStage_diam_targetStar_le P₀ hC hcycle q
  tendsto_eps := tendsto_quantitativeTargetEps
  tendsto_diam_srcStar := by
    intro x hx
    exact tendsto_quantitativeStage_diam_sourceStar P₀ hC hcycle q hdense hx
  base := hbase
  isSeparating := hC

/-- The recursion with its canonical dense schedule.  No convergence hypothesis remains in
this interface. -/
noncomputable def denseQuantitativeStageSequence (hbase : S₀.CombInvariants) :
    StageSequence γ S₀ C :=
  quantitativeStageSequence P₀ hC hcycle (denseQuantitativeSchedule hC) hbase
    (denseQuantitativeSchedule_centresDense hC)

end Schoenflies
