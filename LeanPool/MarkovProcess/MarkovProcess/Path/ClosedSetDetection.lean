/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Path.Basic
import LeanPool.MarkovProcess.MarkovProcess.Time.CountableDenseTime
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! # Detecting closed sets from countably many path coordinates -/

open MeasureTheory Set

namespace MarkovProcess

noncomputable section

namespace ContinuousPath

variable {alpha : Type*} [PseudoMetricSpace alpha]

/-- The positive thresholds used to detect zero distance to a closed set. -/
private def detectionThreshold (n : ℕ) : ℝ := 1 / (n + 1 : ℝ)

private theorem detectionThreshold_pos (n : ℕ) : 0 < detectionThreshold n := by
  exact one_div_pos.mpr (Nat.cast_add_one_pos n)

/-- A countable test for whether a path on `[0, t]` meets `F`.  The endpoint `t` is included
separately, while all earlier samples use the fixed enumeration of nonnegative rational times. -/
def DetectsClosedSetOnIic (t : NNReal) (F : Set alpha) (f : C(Set.Iic t, alpha)) : Prop :=
  F.Nonempty ∧ ∀ n : ℕ,
    Metric.infDist (f ⟨t, Set.mem_Iic.mpr le_rfl⟩) F < detectionThreshold n ∨
      ∃ k : ℕ, ∃ hk : DenseTime.castOrderEmbedding (DenseTime.enumeration k) < t,
        Metric.infDist
            (f ⟨DenseTime.castOrderEmbedding (DenseTime.enumeration k),
              Set.mem_Iic.mpr hk.le⟩) F <
          detectionThreshold n

private theorem exists_denseTime_sample_of_lt
    (t : NNReal) (f : C(Set.Iic t, alpha)) (F : Set alpha)
    {s : Set.Iic t} (hs : (s : NNReal) < t) {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hzero : Metric.infDist (f s) F = 0) :
    ∃ k : ℕ, ∃ hk : DenseTime.castOrderEmbedding (DenseTime.enumeration k) < t,
      Metric.infDist
          (f ⟨DenseTime.castOrderEmbedding (DenseTime.enumeration k),
            Set.mem_Iic.mpr hk.le⟩) F < epsilon := by
  let g : Set.Iic t → ℝ := fun u ↦ Metric.infDist (f u) F
  have hg : Continuous g :=
    (Metric.continuous_infDist_pt (s := F)).comp f.continuous
  let O : Set (Set.Iic t) := g ⁻¹' Set.Iio epsilon
  have hOopen : IsOpen O := isOpen_Iio.preimage hg
  have hsO : s ∈ O := by
    change Metric.infDist (f s) F < epsilon
    rw [hzero]
    exact hepsilon
  obtain ⟨V, hVopen, hV⟩ := isOpen_induced_iff.mp hOopen
  have hsV : (s : NNReal) ∈ V := by
    have : s ∈ Subtype.val ⁻¹' V := by
      rw [hV]
      exact hsO
    exact this
  have hWopen : IsOpen (V ∩ Set.Iio t) := hVopen.inter isOpen_Iio
  have hWnonempty : (V ∩ Set.Iio t).Nonempty := ⟨s, hsV, hs⟩
  obtain ⟨a, b, hab, hsub⟩ := hWopen.exists_Ioo_subset hWnonempty
  obtain ⟨q, haq, hqb⟩ := DenseTime.exists_cast_btwn hab
  let k : ℕ := DenseTime.enumeration.symm q
  have hkq : DenseTime.enumeration k = q := DenseTime.enumeration.apply_symm_apply q
  have hqW : DenseTime.castOrderEmbedding q ∈ V ∩ Set.Iio t := hsub ⟨haq, hqb⟩
  have hkW : DenseTime.castOrderEmbedding (DenseTime.enumeration k) ∈
      V ∩ Set.Iio t := by
    rw [hkq]
    exact hqW
  refine ⟨k, ?_, ?_⟩
  · exact hkW.2
  · have hqO :
        (⟨DenseTime.castOrderEmbedding (DenseTime.enumeration k),
          Set.mem_Iic.mpr hkW.2.le⟩ : Set.Iic t) ∈ O := by
      rw [← hV]
      exact hkW.1
    exact hqO

/-- A continuous path on a compact initial interval meets a closed set exactly when the endpoint
and the fixed countable dense-time samples detect arbitrarily small distance to that set. -/
theorem detectsClosedSetOnIic_iff
    (t : NNReal) (F : Set alpha) (hF : IsClosed F) (f : C(Set.Iic t, alpha)) :
    DetectsClosedSetOnIic t F f ↔ ∃ s : Set.Iic t, f s ∈ F := by
  constructor
  · rintro ⟨hFnonempty, hdetect⟩
    by_contra hmeet
    have hnotmem : ∀ s : Set.Iic t, f s ∉ F := by
      intro s hs
      exact hmeet ⟨s, hs⟩
    let g : Set.Iic t → ℝ := fun s ↦ Metric.infDist (f s) F
    have hg : Continuous g :=
      (Metric.continuous_infDist_pt (s := F)).comp f.continuous
    have hIic : IsCompact (Set.Iic t : Set NNReal) := by
      have heq : Set.Iic t = Set.Icc 0 t := by
        ext u
        simp only [Set.mem_Iic, Set.mem_Icc, zero_le, true_and]
      rw [heq]
      exact isCompact_Icc
    let : CompactSpace (Set.Iic t) := isCompact_iff_compactSpace.mp hIic
    have hcompact : IsCompact (Set.univ : Set (Set.Iic t)) := isCompact_univ
    have huniv : (Set.univ : Set (Set.Iic t)).Nonempty :=
      ⟨⟨0, (zero_le : (0 : NNReal) ≤ t)⟩, Set.mem_univ _⟩
    obtain ⟨s, -, hsmin⟩ := hcompact.exists_isMinOn huniv hg.continuousOn
    have hgs : 0 < g s := (hF.notMem_iff_infDist_pos hFnonempty).mp (hnotmem s)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hgs
    have hn' : detectionThreshold n < g s := hn
    rcases hdetect n with hendpoint | ⟨k, hkt, hk⟩
    · have hmin := hsmin
          (Set.mem_univ (⟨t, Set.mem_Iic.mpr le_rfl⟩ : Set.Iic t))
      exact (not_lt_of_ge hmin) (hendpoint.trans hn')
    · let q : Set.Iic t :=
        ⟨DenseTime.castOrderEmbedding (DenseTime.enumeration k), hkt.le⟩
      have hmin := hsmin (Set.mem_univ q)
      exact (not_lt_of_ge hmin) (hk.trans hn')
  · rintro ⟨s, hsF⟩
    have hFnonempty : F.Nonempty := ⟨f s, hsF⟩
    refine ⟨hFnonempty, fun n ↦ ?_⟩
    have hzero : Metric.infDist (f s) F = 0 := Metric.infDist_zero_of_mem hsF
    by_cases hst : (s : NNReal) = t
    · left
      have hs : s = (⟨t, Set.mem_Iic.mpr le_rfl⟩ : Set.Iic t) := Subtype.ext hst
      rw [← hs, hzero]
      exact detectionThreshold_pos n
    · right
      exact exists_denseTime_sample_of_lt t f F
        (lt_of_le_of_ne s.property hst) (detectionThreshold_pos n) hzero

/-- The positive thresholds used to detect zero distance to a closed set. -/
def closedSetDetectionThreshold (n : ℕ) : ℝ := 1 / (n + 1 : ℝ)

private theorem closedSetDetectionThreshold_pos (n : ℕ) :
    0 < closedSetDetectionThreshold n := by
  exact one_div_pos.mpr (Nat.cast_add_one_pos n)

/-- A countable test for whether a continuous map on `[u, t]` meets `F`. -/
def DetectsClosedSetOnIcc (u t : NNReal) (hut : u ≤ t) (F : Set alpha)
    (f : C(Set.Icc u t, alpha)) : Prop :=
  F.Nonempty ∧ ∀ n : ℕ,
    Metric.infDist (f ⟨u, le_rfl, hut⟩) F < closedSetDetectionThreshold n ∨
      Metric.infDist (f ⟨t, hut, le_rfl⟩) F < closedSetDetectionThreshold n ∨
        ∃ k : ℕ,
          ∃ huk : u < DenseTime.castOrderEmbedding (DenseTime.enumeration k),
          ∃ hkt : DenseTime.castOrderEmbedding (DenseTime.enumeration k) < t,
            Metric.infDist
                (f ⟨DenseTime.castOrderEmbedding (DenseTime.enumeration k), huk.le, hkt.le⟩) F <
              closedSetDetectionThreshold n

private theorem exists_denseTime_sample_between
    (u t : NNReal) (f : C(Set.Icc u t, alpha)) (F : Set alpha)
    {s : Set.Icc u t} (hus : u < s) (hst : (s : NNReal) < t)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hzero : Metric.infDist (f s) F = 0) :
    ∃ k : ℕ,
      ∃ huk : u < DenseTime.castOrderEmbedding (DenseTime.enumeration k),
      ∃ hkt : DenseTime.castOrderEmbedding (DenseTime.enumeration k) < t,
        Metric.infDist
            (f ⟨DenseTime.castOrderEmbedding (DenseTime.enumeration k), huk.le, hkt.le⟩) F <
          epsilon := by
  let g : Set.Icc u t → ℝ := fun v ↦ Metric.infDist (f v) F
  have hg : Continuous g := (Metric.continuous_infDist_pt (s := F)).comp f.continuous
  let O : Set (Set.Icc u t) := g ⁻¹' Set.Iio epsilon
  have hOopen : IsOpen O := isOpen_Iio.preimage hg
  have hsO : s ∈ O := by
    change Metric.infDist (f s) F < epsilon
    rw [hzero]
    exact hepsilon
  obtain ⟨W, hWopen, hW⟩ := isOpen_induced_iff.mp hOopen
  have hsW : (s : NNReal) ∈ W := by
    have hsPreimage : s ∈ Subtype.val ⁻¹' W := by
      rw [hW]
      exact hsO
    exact hsPreimage
  have hOpen : IsOpen (W ∩ Set.Ioo u t) := hWopen.inter isOpen_Ioo
  have hNonempty : (W ∩ Set.Ioo u t).Nonempty := ⟨s, hsW, hus, hst⟩
  obtain ⟨a, b, hab, hsub⟩ := hOpen.exists_Ioo_subset hNonempty
  obtain ⟨q, haq, hqb⟩ := DenseTime.exists_cast_btwn hab
  let k : ℕ := DenseTime.enumeration.symm q
  have hkq : DenseTime.enumeration k = q := DenseTime.enumeration.apply_symm_apply q
  have hqW : DenseTime.castOrderEmbedding q ∈ W ∩ Set.Ioo u t := hsub ⟨haq, hqb⟩
  refine ⟨k, ?_, ?_, ?_⟩
  · simpa only [hkq] using hqW.2.1
  · simpa only [hkq] using hqW.2.2
  · have hqO :
        (⟨DenseTime.castOrderEmbedding (DenseTime.enumeration k),
          (by simpa only [hkq] using hqW.2.1.le),
          (by simpa only [hkq] using hqW.2.2.le)⟩ : Set.Icc u t) ∈ O := by
      rw [← hW]
      simpa only [hkq] using! hqW.1
    exact hqO

/-- A continuous map on a nonempty compact interval meets a closed set exactly when the
endpoint and fixed dense-time samples detect arbitrarily small distance to that set. -/
theorem detectsClosedSetOnIcc_iff
    (u t : NNReal) (hut : u ≤ t) (F : Set alpha) (hF : IsClosed F)
    (f : C(Set.Icc u t, alpha)) :
    DetectsClosedSetOnIcc u t hut F f ↔ ∃ s : Set.Icc u t, f s ∈ F := by
  constructor
  · rintro ⟨hFnonempty, hdetect⟩
    by_contra hmeet
    have hnotmem : ∀ s : Set.Icc u t, f s ∉ F := by
      intro s hs
      exact hmeet ⟨s, hs⟩
    let g : Set.Icc u t → ℝ := fun s ↦ Metric.infDist (f s) F
    have hg : Continuous g := (Metric.continuous_infDist_pt (s := F)).comp f.continuous
    let : CompactSpace (Set.Icc u t) := isCompact_iff_compactSpace.mp isCompact_Icc
    have hcompact : IsCompact (Set.univ : Set (Set.Icc u t)) := isCompact_univ
    have huniv : (Set.univ : Set (Set.Icc u t)).Nonempty :=
      ⟨⟨u, le_rfl, hut⟩, Set.mem_univ _⟩
    obtain ⟨s, -, hsmin⟩ := hcompact.exists_isMinOn huniv hg.continuousOn
    have hgs : 0 < g s := (hF.notMem_iff_infDist_pos hFnonempty).mp (hnotmem s)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hgs
    have hn' : closedSetDetectionThreshold n < g s := hn
    rcases hdetect n with hu | ht | ⟨k, huk, hkt, hk⟩
    · have hmin := hsmin (Set.mem_univ (⟨u, le_rfl, hut⟩ : Set.Icc u t))
      exact (not_lt_of_ge hmin) (hu.trans hn')
    · have hmin := hsmin (Set.mem_univ (⟨t, hut, le_rfl⟩ : Set.Icc u t))
      exact (not_lt_of_ge hmin) (ht.trans hn')
    · let q : Set.Icc u t :=
        ⟨DenseTime.castOrderEmbedding (DenseTime.enumeration k), huk.le, hkt.le⟩
      have hmin := hsmin (Set.mem_univ q)
      exact (not_lt_of_ge hmin) (hk.trans hn')
  · rintro ⟨s, hsF⟩
    have hFnonempty : F.Nonempty := ⟨f s, hsF⟩
    refine ⟨hFnonempty, fun n ↦ ?_⟩
    have hzero : Metric.infDist (f s) F = 0 := Metric.infDist_zero_of_mem hsF
    by_cases hsu : (s : NNReal) = u
    · left
      have hs : s = (⟨u, le_rfl, hut⟩ : Set.Icc u t) := Subtype.ext hsu
      rw [← hs, hzero]
      exact closedSetDetectionThreshold_pos n
    by_cases hst : (s : NNReal) = t
    · right
      left
      have hs : s = (⟨t, hut, le_rfl⟩ : Set.Icc u t) := Subtype.ext hst
      rw [← hs, hzero]
      exact closedSetDetectionThreshold_pos n
    · right
      right
      exact exists_denseTime_sample_between u t f F
        (lt_of_le_of_ne s.property.1 (Ne.symm hsu))
        (lt_of_le_of_ne s.property.2 hst) (closedSetDetectionThreshold_pos n) hzero

/-- Restrict an ordinary continuous path to a compact initial time interval. -/
def restrictIic (t : NNReal) (omega : ContinuousPath alpha) : C(Set.Iic t, alpha) where
  toFun s := omega s
  continuous_toFun := omega.continuous.comp continuous_subtype_val

/-- The event that a continuous path meets `F` at or before time `t`. -/
def hitsSetBy (t : NNReal) (F : Set alpha) : Set (ContinuousPath alpha) :=
  {omega | ∃ s : Set.Iic t, omega s ∈ F}

variable [MeasurableSpace alpha] [BorelSpace alpha]

private theorem measurable_infDist_coordinate (t : NNReal) (F : Set alpha)
    {s : NNReal} (hs : s ≤ t) :
    Measurable[canonicalFiltration (alpha := alpha) t]
      (fun omega : ContinuousPath alpha ↦ Metric.infDist (omega s) F) := by
  have hcoordinate : Measurable[canonicalFiltration (alpha := alpha) t]
      (coordinateProcess (alpha := alpha) s) := by
    apply Measurable.of_comap_le
    exact le_iSup_of_le (⟨s, Set.mem_Iic.mpr hs⟩ : Set.Iic t) le_rfl
  have hcoordinate' : Measurable[canonicalFiltration (alpha := alpha) t, borel alpha]
      (coordinateProcess (alpha := alpha) s) :=
    hcoordinate.mono le_rfl (le_of_eq BorelSpace.measurable_eq.symm)
  exact (Metric.continuous_infDist_pt (s := F)).borel_measurable.comp hcoordinate'

/-- Hitting a closed set by a fixed time is measurable in the raw canonical filtration. -/
theorem measurableSet_hitsSetBy (t : NNReal) (F : Set alpha) (hF : IsClosed F) :
    MeasurableSet[canonicalFiltration (alpha := alpha) t] (hitsSetBy t F) := by
  by_cases hFnonempty : F.Nonempty
  swap
  · have hFempty : F = ∅ := not_nonempty_iff_eq_empty.mp hFnonempty
    have hevent : hitsSetBy t F = ∅ := by
      rw [hFempty]
      ext omega
      simp only [hitsSetBy, Set.mem_ofPred_eq, Set.notMem_empty, exists_const]
    rw [hevent]
    exact @MeasurableSet.empty _ (canonicalFiltration (alpha := alpha) t)
  let A : ℕ → Set (ContinuousPath alpha) := fun n ↦
    {omega | Metric.infDist (omega t) F < detectionThreshold n}
  let B : ℕ → ℕ → Set (ContinuousPath alpha) := fun n k ↦
    if h : DenseTime.castOrderEmbedding (DenseTime.enumeration k) < t then
      {omega | Metric.infDist
        (omega (DenseTime.castOrderEmbedding (DenseTime.enumeration k))) F <
          detectionThreshold n}
    else ∅
  have hA : ∀ n, MeasurableSet[canonicalFiltration (alpha := alpha) t] (A n) := by
    intro n
    exact (measurable_infDist_coordinate t F le_rfl)
      (measurableSet_Iio : MeasurableSet (Set.Iio (detectionThreshold n)))
  have hB : ∀ n k, MeasurableSet[canonicalFiltration (alpha := alpha) t] (B n k) := by
    intro n k
    dsimp only [B]
    split_ifs with hkt
    · exact (measurable_infDist_coordinate t F hkt.le)
        (measurableSet_Iio : MeasurableSet (Set.Iio (detectionThreshold n)))
    · exact @MeasurableSet.empty _ (canonicalFiltration (alpha := alpha) t)
  have hevent : hitsSetBy t F = ⋂ n : ℕ, (A n ∪ ⋃ k : ℕ, B n k) := by
    ext omega
    rw [Set.mem_iInter]
    change (∃ s : Set.Iic t, (restrictIic t omega) s ∈ F) ↔ _
    rw [← detectsClosedSetOnIic_iff t F hF (restrictIic t omega)]
    simp only [DetectsClosedSetOnIic, hFnonempty, true_and, Set.mem_union,
      Set.mem_iUnion, Set.mem_ofPred_eq, A, B, restrictIic]
    constructor
    · intro hdetect n
      rcases hdetect n with hendpoint | ⟨k, hkt, hk⟩
      · exact Or.inl hendpoint
      · exact Or.inr ⟨k, by rw [dif_pos hkt]; exact hk⟩
    · intro h n
      rcases h n with hendpoint | ⟨k, hk⟩
      · exact Or.inl hendpoint
      · by_cases hkt : DenseTime.castOrderEmbedding (DenseTime.enumeration k) < t
        · exact Or.inr ⟨k, hkt, by simpa only [dif_pos hkt] using! hk⟩
        · simp only [dif_neg hkt, Set.notMem_empty] at hk
  rw [hevent]
  exact MeasurableSet.iInter fun n ↦ (hA n).union (MeasurableSet.iUnion (hB n))

end ContinuousPath

end
end MarkovProcess
