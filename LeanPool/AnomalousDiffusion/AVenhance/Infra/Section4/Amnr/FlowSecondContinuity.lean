/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SecondVariationContinuity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SpatialC2
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.JointSpatialDerivativeAll

/-! Joint continuity of the actual second flow derivative, with a fixed start.
This is the regularity needed to admit the primitive material flow jet. -/

@[expose] public section

noncomputable section
open Homogenization Set Filter
open scoped Topology
namespace AVenhance.Infra.Section4
open AVenhance.Infra.Flow

/-- Evaluation of the actual second spatial flow derivative. -/
def amnrFlowSecondEval (X : ℝ → Vec 2 → ℝ → Vec 2) (s : ℝ)
    (h k : Vec 2) (z : ℝ × Vec 2) : Vec 2 :=
  fderiv ℝ (fun y => fderiv ℝ (fun w => X z.1 w s) y) z.2 h k

/-- The characterized second variation is the actual second flow derivative
throughout every forward time interval. -/
theorem amnrFlowSecondEval_continuousOn_forward
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (h k : Vec 2) (s T : ℝ) (hsT : s ≤ T) :
    ContinuousOn (amnrFlowSecondEval X s h k) (Icc s T ×ˢ univ) := by
  have hc := flow_secondVariation_jointContinuous_of_le hb hX h k s T hsT
  apply hc.congr
  intro z hz
  obtain ⟨_, _, B, hB, hD⟩ := exists_flow_spatialFDeriv_hasFDerivAt_of_le hb hX
    z.2 s z.1 hz.1.1
  change fderiv ℝ (fun y => fderiv ℝ (fun w => X z.1 w s) y) z.2 h k = _
  rw [hD.fderiv]
  exact hB h k

/-- Reversing target and start times does not change a spatial derivative. -/
theorem amnrFlowSecondEval_reverse
    (X : ℝ → Vec 2 → ℝ → Vec 2) (s : ℝ) (h k : Vec 2) (z : ℝ × Vec 2) :
    amnrFlowSecondEval X s h k z =
      amnrFlowSecondEval (regularityReverseTimeFlow X) (-s) h k (-z.1, z.2) := by
  simp only [amnrFlowSecondEval, regularityReverseTimeFlow, neg_neg]

/-- Joint continuity on backward intervals follows from the same proved
forward variation theorem applied to the reversed characterized flow. -/
theorem amnrFlowSecondEval_continuousOn_backward
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (h k : Vec 2) (S s : ℝ) (hSs : S ≤ s) :
    ContinuousOn (amnrFlowSecondEval X s h k) (Icc S s ×ˢ univ) := by
  have hbr := smoothPeriodicField_regularityReverseTime hb
  have hXr := isFlow_regularityReverseTime hX
  have hc := amnrFlowSecondEval_continuousOn_forward hbr hXr h k (-s) (-S) (by linarith)
  have he : Continuous (fun z : ℝ × Vec 2 => (-z.1, z.2)) := by fun_prop
  have hh := hc.comp he.continuousOn (show MapsTo (fun z : ℝ × Vec 2 => (-z.1, z.2))
      (Icc S s ×ˢ univ) (Icc (-s) (-S) ×ˢ univ) from by
    intro z hz
    exact ⟨⟨by linarith [hz.1.2], by linarith [hz.1.1]⟩, mem_univ _⟩)
  apply hh.congr
  intro z _
  exact amnrFlowSecondEval_reverse X s h k z

/-- The actual second spatial flow derivative is jointly continuous on all
target times, including the diagonal at the fixed start time. -/
theorem amnrFlowSecondEval_continuous
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (s : ℝ) (h k : Vec 2) : Continuous (amnrFlowSecondEval X s h k) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  let S := min s z.1 - 1
  let T := max s z.1 + 1
  have hSs : S ≤ s := by dsimp [S]; linarith [min_le_left s z.1]
  have hsT : s ≤ T := by dsimp [T]; linarith [le_max_left s z.1]
  have hc := (amnrFlowSecondEval_continuousOn_backward hb hX h k S s hSs).union_of_isClosed
    (amnrFlowSecondEval_continuousOn_forward hb hX h k s T hsT)
    (isClosed_Icc.prod isClosed_univ) (isClosed_Icc.prod isClosed_univ)
  have hcover : Icc S T ×ˢ (univ : Set (Vec 2)) ⊆
      (Icc S s ×ˢ univ) ∪ (Icc s T ×ˢ univ) := by
    intro y hy
    by_cases ht : y.1 ≤ s
    · exact Or.inl ⟨⟨hy.1.1, ht⟩, mem_univ _⟩
    · exact Or.inr ⟨⟨le_of_not_ge ht, hy.1.2⟩, mem_univ _⟩
  have hzS : S < z.1 := by dsimp [S]; linarith [min_le_right s z.1]
  have hzT : z.1 < T := by dsimp [T]; linarith [le_max_right s z.1]
  exact (hc.mono hcover).continuousAt (prod_mem_nhds (Icc_mem_nhds hzS hzT) univ_mem)

end AVenhance.Infra.Section4
