/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Path.ClosedSetDetection
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.StoppingLtTop

/-!
# Closed-set detection after a stopping time

This file relativizes closed-set detection to the random compact interval between a stopping
time and a fixed deterministic horizon.  The lower endpoint is truncated at the horizon, so it
is a bounded finite stopping time.  Continuity reduces detection on that interval to its two
endpoints and the fixed enumeration of nonnegative rational times strictly between them.

Public declarations:

* `ContinuousPath.hitsSetBetween`;
* `ContinuousPath.measurableSet_hitsSetBetween`.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace MarkovProcess

noncomputable section

namespace ContinuousPath

variable {alpha : Type*} [PseudoMetricSpace alpha]

/-- The event that a path meets `F` between the stopping time `T` and the fixed horizon `t`. -/
def hitsSetBetween (T : ContinuousPath alpha → ℝ≥0∞) (t : NNReal) (F : Set alpha) :
    Set (ContinuousPath alpha) :=
  {omega | ∃ s : NNReal, T omega ≤ s ∧ s ≤ t ∧ omega s ∈ F}

private def restrictIcc (u t : NNReal) (omega : ContinuousPath alpha) :
    C(Set.Icc u t, alpha) where
  toFun s := omega s
  continuous_toFun := omega.continuous.comp continuous_subtype_val

variable [SecondCountableTopology alpha] [MeasurableSpace alpha] [BorelSpace alpha]

/-- Meeting a closed set between a stopping time and a fixed horizon is measurable in the raw
canonical filtration at that horizon. -/
theorem measurableSet_hitsSetBetween
    (T : ContinuousPath alpha → ℝ≥0∞)
    (hT : IsStoppingTime (canonicalFiltration (alpha := alpha)) T)
    (t : NNReal) (F : Set alpha) (hF : IsClosed F) :
    MeasurableSet[canonicalFiltration (alpha := alpha) t] (hitsSetBetween T t F) := by
  by_cases hFnonempty : F.Nonempty
  swap
  · have hFempty : F = ∅ := not_nonempty_iff_eq_empty.mp hFnonempty
    have hevent : hitsSetBetween T t F = ∅ := by
      rw [hFempty]
      ext omega
      simp only [hitsSetBetween, Set.mem_ofPred_eq, Set.notMem_empty, and_false,
        exists_const]
    rw [hevent]
    exact @MeasurableSet.empty _ (canonicalFiltration (alpha := alpha) t)
  let u : ContinuousPath alpha → NNReal := StoppingTime.truncTime T t
  have huStop : IsStoppingTime (canonicalFiltration (alpha := alpha))
      (fun omega ↦ ((u omega : NNReal) : ℝ≥0∞)) :=
    StoppingTime.isStoppingTime_truncTime hT t
  have hut : ∀ omega, u omega ≤ t := by
    intro omega
    apply WithTop.coe_le_coe.mp
    exact (le_of_eq (StoppingTime.coe_truncTime T t omega)).trans (min_le_right _ _)
  have huSpace : huStop.measurableSpace ≤ canonicalFiltration (alpha := alpha) t :=
    huStop.measurableSpace_le_of_le_const fun omega ↦ WithTop.coe_le_coe.mpr (hut omega)
  have huMeas : Measurable[canonicalFiltration (alpha := alpha) t]
      (fun omega ↦ ((u omega : NNReal) : ℝ≥0∞)) :=
    huStop.measurable.mono huSpace le_rfl
  have hEvalU : Measurable[canonicalFiltration (alpha := alpha) t]
      (fun omega : ContinuousPath alpha ↦ omega (u omega)) :=
    (measurable_eval_stoppingTime u huStop).mono huSpace le_rfl
  have hDistU : Measurable[canonicalFiltration (alpha := alpha) t]
      (fun omega : ContinuousPath alpha ↦ Metric.infDist (omega (u omega)) F) := by
    let : MeasurableSpace (ContinuousPath alpha) := canonicalFiltration (alpha := alpha) t
    exact hEvalU.infDist
  have hEvalT : Measurable[canonicalFiltration (alpha := alpha) t]
      (fun omega : ContinuousPath alpha ↦ omega t) :=
    measurable_coordinateProcess_canonicalFiltration t
  have hDistT : Measurable[canonicalFiltration (alpha := alpha) t]
      (fun omega : ContinuousPath alpha ↦ Metric.infDist (omega t) F) := by
    let : MeasurableSpace (ContinuousPath alpha) := canonicalFiltration (alpha := alpha) t
    exact hEvalT.infDist
  let A : ℕ → Set (ContinuousPath alpha) := fun n ↦
    {omega | Metric.infDist (omega (u omega)) F < closedSetDetectionThreshold n}
  let B : ℕ → Set (ContinuousPath alpha) := fun n ↦
    {omega | Metric.infDist (omega t) F < closedSetDetectionThreshold n}
  let C : ℕ → ℕ → Set (ContinuousPath alpha) := fun n k ↦
    if hkt : DenseTime.castOrderEmbedding (DenseTime.enumeration k) < t then
      {omega | u omega < DenseTime.castOrderEmbedding (DenseTime.enumeration k)} ∩
        {omega | Metric.infDist
            (omega (DenseTime.castOrderEmbedding (DenseTime.enumeration k))) F <
          closedSetDetectionThreshold n}
    else ∅
  have hA : ∀ n, MeasurableSet[canonicalFiltration (alpha := alpha) t] (A n) := by
    intro n
    exact hDistU
      (measurableSet_Iio : MeasurableSet (Set.Iio (closedSetDetectionThreshold n)))
  have hB : ∀ n, MeasurableSet[canonicalFiltration (alpha := alpha) t] (B n) := by
    intro n
    exact hDistT
      (measurableSet_Iio : MeasurableSet (Set.Iio (closedSetDetectionThreshold n)))
  have hC : ∀ n k, MeasurableSet[canonicalFiltration (alpha := alpha) t] (C n k) := by
    intro n k
    dsimp only [C]
    split_ifs with hkt
    · have hConst : Measurable[canonicalFiltration (alpha := alpha) t]
          (fun _ : ContinuousPath alpha ↦
            ((DenseTime.castOrderEmbedding (DenseTime.enumeration k) : NNReal) : ℝ≥0∞)) :=
        measurable_const
      refine (show MeasurableSet[canonicalFiltration (alpha := alpha) t]
          {omega | u omega < DenseTime.castOrderEmbedding (DenseTime.enumeration k)} by
        simpa only [ENNReal.coe_lt_coe] using
          measurableSet_lt huMeas hConst).inter ?_
      have hEvalQ : Measurable[canonicalFiltration (alpha := alpha) t]
          (fun omega : ContinuousPath alpha ↦
            omega (DenseTime.castOrderEmbedding (DenseTime.enumeration k))) :=
        (measurable_coordinateProcess_canonicalFiltration
          (DenseTime.castOrderEmbedding (DenseTime.enumeration k))).mono
            (canonicalFiltration.mono hkt.le) le_rfl
      let : MeasurableSpace (ContinuousPath alpha) := canonicalFiltration (alpha := alpha) t
      exact hEvalQ.infDist
        (measurableSet_Iio : MeasurableSet (Set.Iio (closedSetDetectionThreshold n)))
    · exact @MeasurableSet.empty _ (canonicalFiltration (alpha := alpha) t)
  have hevent : hitsSetBetween T t F =
      {omega | T omega ≤ (t : ℝ≥0∞)} ∩ ⋂ n : ℕ, (A n ∪ B n ∪ ⋃ k : ℕ, C n k) := by
    ext omega
    simp only [hitsSetBetween, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_union, Set.mem_iUnion]
    constructor
    · rintro ⟨s, hTs, hst, hsF⟩
      have hTt : T omega ≤ (t : ℝ≥0∞) := hTs.trans (by exact_mod_cast hst)
      refine ⟨hTt, ?_⟩
      have hTne : T omega ≠ ⊤ := ne_top_of_le_ne_top (WithTop.coe_ne_top) hTt
      lift T omega to NNReal using hTne with a ha
      have has : a ≤ s := WithTop.coe_le_coe.mp hTs
      have huEq : u omega = a := by
        change (min (T omega) (t : ℝ≥0∞)).untopD 0 = a
        rw [← ha]
        have hmin : min (a : ℝ≥0∞) (t : ℝ≥0∞) = (a : ℝ≥0∞) :=
          min_eq_left (WithTop.coe_le_coe.mpr (has.trans hst))
        rw [hmin]
        rfl
      have hdetect :=
        (detectsClosedSetOnIcc_iff a t (has.trans hst) F hF (restrictIcc a t omega)).2
          ⟨⟨s, has, hst⟩, hsF⟩
      intro n
      rcases hdetect.2 n with hu | ht | ⟨k, huk, hkt, hk⟩
      · refine Or.inl (Or.inl ?_)
        change Metric.infDist (omega (u omega)) F < closedSetDetectionThreshold n
        rw [huEq]
        exact hu
      · exact Or.inl (Or.inr (by simpa only [B] using! ht))
      · refine Or.inr ⟨k, ?_⟩
        simp only [C, dif_pos hkt, Set.mem_inter_iff, Set.mem_ofPred_eq]
        exact ⟨huEq.symm ▸ huk, hk⟩
    · rintro ⟨hTt, hdetect⟩
      have hTne : T omega ≠ ⊤ := ne_top_of_le_ne_top (WithTop.coe_ne_top) hTt
      lift T omega to NNReal using hTne with a ha
      have hat : a ≤ t := WithTop.coe_le_coe.mp hTt
      have huEq : u omega = a := by
        change (min (T omega) (t : ℝ≥0∞)).untopD 0 = a
        rw [← ha]
        have hmin : min (a : ℝ≥0∞) (t : ℝ≥0∞) = (a : ℝ≥0∞) :=
          min_eq_left (WithTop.coe_le_coe.mpr hat)
        rw [hmin]
        rfl
      have hdetector :
          DetectsClosedSetOnIcc a t hat F (restrictIcc a t omega) := by
        refine ⟨hFnonempty, fun n ↦ ?_⟩
        rcases hdetect n with (hu | ht) | ⟨k, hk⟩
        · refine Or.inl ?_
          change Metric.infDist (omega a) F < closedSetDetectionThreshold n
          rw [← huEq]
          exact hu
        · exact Or.inr (Or.inl (by simpa only [B] using! ht))
        · dsimp only [C] at hk
          split_ifs at hk with hkt
          · refine Or.inr (Or.inr ⟨k, ?_, hkt, hk.2⟩)
            rw [← huEq]
            exact hk.1
          · exact (Set.notMem_empty omega hk).elim
      obtain ⟨s, hsF⟩ :=
        (detectsClosedSetOnIcc_iff a t hat F hF (restrictIcc a t omega)).1 hdetector
      refine ⟨s, WithTop.coe_le_coe.mpr s.property.1, s.property.2, hsF⟩
  rw [hevent]
  exact (hT t).inter <| MeasurableSet.iInter fun n ↦
    ((hA n).union (hB n)).union (MeasurableSet.iUnion (hC n))

end ContinuousPath

end

end MarkovProcess
