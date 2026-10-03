/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SecondVariationContinuity

/-! Joint forward-time continuity of the second spatial derivative. -/

@[expose] public section

open Homogenization
open Set
open scoped ContDiff Topology

namespace AVenhance.Infra.Flow

/-- The second spatial derivative, as a nested continuous linear map. -/
noncomputable def flowSecondSpatialDerivative
    (X : ℝ → Vec 2 → ℝ → Vec 2) (t : ℝ) (x : Vec 2) (s : ℝ) :
    Vec 2 →L[ℝ] Vec 2 →L[ℝ] Vec 2 :=
  fderiv ℝ (fun y => fderiv ℝ (fun z => X t z s) y) x

/-- On forward compact target-time intervals, the second spatial derivative
varies jointly continuously with target time and initial point. -/
theorem flowSecondSpatialDerivative_jointContinuousOn_of_le
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (s T : ℝ) (hst : s ≤ T) :
    ContinuousOn
      (fun p : ℝ × Vec 2 => flowSecondSpatialDerivative X p.1 p.2 s)
      (Icc s T ×ˢ univ) := by
  apply continuousOn_clm_apply.mpr
  intro h
  apply continuousOn_clm_apply.mpr
  intro k
  have hvariation := flow_secondVariation_jointContinuous_of_le
    hb hX h k s T hst
  apply hvariation.congr
  intro p hp
  obtain ⟨V, hV, B, hB, hD⟩ :=
    exists_flow_spatialFDeriv_hasFDerivAt_of_le hb hX p.2 s p.1 hp.1.1
  have hB' : flowSecondSpatialDerivative X p.1 p.2 s = B := by
    simpa [flowSecondSpatialDerivative] using hD.fderiv
  change flowSecondSpatialDerivative X p.1 p.2 s h k = _
  rw [hB']
  exact hB h k

/-- For fixed start time, the second spatial derivative is jointly continuous
in target time and initial point across both time orientations. -/
theorem flowSecondSpatialDerivative_jointContinuous
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    (s : ℝ) :
    Continuous (fun p : ℝ × Vec 2 =>
      flowSecondSpatialDerivative X p.1 p.2 s) := by
  apply continuous_iff_continuousAt.mpr
  intro p₀
  rcases p₀ with ⟨t₀, x₀⟩
  let a : ℝ := min t₀ s - 1
  let d : ℝ := max t₀ s + 1
  have has : a ≤ s := by dsimp [a]; linarith [min_le_right t₀ s]
  have hsd : s ≤ d := by dsimp [d]; linarith [le_max_right t₀ s]
  have hat : a < t₀ := by dsimp [a]; linarith [min_le_left t₀ s]
  have htd : t₀ < d := by dsimp [d]; linarith [le_max_left t₀ s]
  let K : ℝ × Vec 2 → Vec 2 →L[ℝ] Vec 2 →L[ℝ] Vec 2 :=
    fun p => flowSecondSpatialDerivative X p.1 p.2 s
  have hforward : ContinuousOn K (Icc s d ×ˢ (univ : Set (Vec 2))) := by
    change ContinuousOn
      (fun p : ℝ × Vec 2 => flowSecondSpatialDerivative X p.1 p.2 s)
      (Icc s d ×ˢ (univ : Set (Vec 2)))
    exact flowSecondSpatialDerivative_jointContinuousOn_of_le hb hX s d hsd
  let br := regularityReverseTimeField b
  let Xr := regularityReverseTimeFlow X
  have hbr : SmoothPeriodicField br := smoothPeriodicField_regularityReverseTime hb
  have hXr : AVenhance.IsFlow br Xr := isFlow_regularityReverseTime hX
  let Kback : ℝ × Vec 2 → Vec 2 →L[ℝ] Vec 2 →L[ℝ] Vec 2 := fun p =>
    flowSecondSpatialDerivative Xr (-p.1) p.2 (-s)
  have hbackR : ContinuousOn Kback (Icc a s ×ˢ (univ : Set (Vec 2))) := by
    have hrev : ContinuousOn
        (fun p : ℝ × Vec 2 => flowSecondSpatialDerivative Xr p.1 p.2 (-s))
        (Icc (-s) (-a) ×ˢ (univ : Set (Vec 2))) :=
      flowSecondSpatialDerivative_jointContinuousOn_of_le hbr hXr
        (-s) (-a) (by linarith)
    have hmap : Continuous (fun p : ℝ × Vec 2 => (-p.1, p.2)) := by fun_prop
    have hmaps : MapsTo (fun p : ℝ × Vec 2 => (-p.1, p.2))
        (Icc a s ×ˢ (univ : Set (Vec 2)))
        (Icc (-s) (-a) ×ˢ (univ : Set (Vec 2))) := by
      intro p hp
      exact ⟨⟨by linarith [hp.1.2], by linarith [hp.1.1]⟩, hp.2⟩
    change ContinuousOn
      (fun p : ℝ × Vec 2 =>
        flowSecondSpatialDerivative Xr (-p.1) p.2 (-s))
      (Icc a s ×ˢ (univ : Set (Vec 2)))
    exact hrev.comp' hmap.continuousOn hmaps
  have hbackEq (p : ℝ × Vec 2) :
      K p = Kback p := by
    dsimp [K, Kback, flowSecondSpatialDerivative, Xr, regularityReverseTimeFlow]
    simp
  have hback : ContinuousOn K (Icc a s ×ˢ (univ : Set (Vec 2))) := by
    apply hbackR.congr
    intro p hp
    exact hbackEq p
  have hunion :
      (Icc a s ×ˢ (univ : Set (Vec 2))) ∪
      (Icc s d ×ˢ (univ : Set (Vec 2))) =
      Icc a d ×ˢ (univ : Set (Vec 2)) := by
    rw [← Set.union_prod, Icc_union_Icc_eq_Icc has hsd]
  have hglobal : ContinuousOn K (Icc a d ×ˢ (univ : Set (Vec 2))) := by
    rw [← hunion]
    exact hback.union_of_isClosed hforward
      (isClosed_Icc.prod isClosed_univ) (isClosed_Icc.prod isClosed_univ)
  have hopen : IsOpen (Ioo a d ×ˢ (univ : Set (Vec 2))) :=
    isOpen_Ioo.prod isOpen_univ
  have hmem : (t₀, x₀) ∈ Ioo a d ×ˢ (univ : Set (Vec 2)) :=
    ⟨⟨hat, htd⟩, mem_univ _⟩
  have hnhds : Icc a d ×ˢ (univ : Set (Vec 2)) ∈ 𝓝 (t₀, x₀) :=
    Filter.mem_of_superset (hopen.mem_nhds hmem) fun p hp =>
      ⟨Ioo_subset_Icc_self hp.1, hp.2⟩
  exact hglobal.continuousAt hnhds

end AVenhance.Infra.Flow
