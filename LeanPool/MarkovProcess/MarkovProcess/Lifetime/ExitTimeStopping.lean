/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Path.ClosedSetDetection
import LeanPool.MarkovProcess.MarkovProcess.Lifetime.ExitTime
import LeanPool.MarkovProcess.MarkovProcess.Lifetime.Filtration

/-! # Exit times as stopping times -/

noncomputable section PortComputability

open MeasureTheory Set
open scoped ENNReal

namespace MarkovProcess.LifetimePath

section

variable {alpha : Type*} [PseudoMetricSpace alpha]

private theorem exists_time_between_lifetime (omega : LifetimePath alpha) (t : NNReal)
    (ht : (t : ENNReal) < omega.lifetime) :
    ∃ r : NNReal, t < r ∧ (r : ENNReal) < omega.lifetime := by
  cases hlifetime : omega.lifetime with
  | top =>
      refine ⟨t + 1, lt_add_one t, ?_⟩
      exact ENNReal.coe_lt_top
  | coe u =>
      have htu : t < u := by
        rw [hlifetime, ENNReal.coe_lt_coe] at ht
        exact ht
      obtain ⟨r, htr, hru⟩ := exists_between htu
      exact ⟨r, htr, ENNReal.coe_lt_coe.mpr hru⟩

private theorem exists_right_interval_in_open (omega : LifetimePath alpha) (U : Set alpha)
    (hU : IsOpen U) (t : NNReal) (ht : (t : ENNReal) < omega.lifetime)
    (htU : omega.livePath ⟨t, ht⟩ ∈ U) :
    ∃ r : NNReal, t < r ∧ (r : ENNReal) < omega.lifetime ∧
      ∀ s : NNReal, t < s → s < r → coordinate s omega ∈ Cemetery.alive '' U := by
  let O : Set {s : NNReal // (s : ENNReal) < omega.lifetime} := omega.livePath ⁻¹' U
  have hOopen : IsOpen O := hU.preimage omega.continuous_livePath
  have htO : (⟨t, ht⟩ : {s : NNReal // (s : ENNReal) < omega.lifetime}) ∈ O := htU
  obtain ⟨V, hVopen, hV⟩ := isOpen_induced_iff.mp hOopen
  have htV : t ∈ V := by
    have : (⟨t, ht⟩ : {s : NNReal // (s : ENNReal) < omega.lifetime}) ∈
        Subtype.val ⁻¹' V := by
      rw [hV]
      exact htO
    exact this
  obtain ⟨b, htb, hblife⟩ := exists_time_between_lifetime omega t ht
  let W : Set NNReal := V ∩ Set.Iio b
  have hWopen : IsOpen W := hVopen.inter isOpen_Iio
  have htW : t ∈ W := ⟨htV, htb⟩
  have hWnhds : W ∈ nhdsWithin t (Set.Ioi t) :=
    mem_nhdsWithin_of_mem_nhds (hWopen.mem_nhds htW)
  obtain ⟨r, htr, hrW⟩ := (mem_nhdsGT_iff_exists_Ioo_subset.mp hWnhds)
  have hrb : r ≤ b := by
    by_contra hbr
    obtain ⟨s, hbs, hsr⟩ := exists_between (lt_of_not_ge hbr)
    have hsW := hrW ⟨htb.trans hbs, hsr⟩
    exact (not_lt_of_ge hbs.le) hsW.2
  have hrlife : (r : ENNReal) < omega.lifetime :=
    (ENNReal.coe_le_coe.mpr hrb).trans_lt hblife
  refine ⟨r, htr, hrlife, ?_⟩
  intro s hts hsr
  have hsW := hrW ⟨hts, hsr⟩
  have hslife : (s : ENNReal) < omega.lifetime :=
    (ENNReal.coe_lt_coe.mpr hsr).trans hrlife
  rw [coordinate_of_lt omega s hslife]
  refine ⟨omega.livePath ⟨s, hslife⟩, ?_, rfl⟩
  have hsO : (⟨s, hslife⟩ : {u : NNReal // (u : ENNReal) < omega.lifetime}) ∈ O := by
    rw [← hV]
    exact hsW.1
  exact hsO

private theorem exitTime_le_iff (U : Set alpha) (hU : IsOpen U)
    (omega : LifetimePath alpha) (t : NNReal) :
    exitTime U omega ≤ (t : ENNReal) ↔
      omega.lifetime ≤ (t : ENNReal) ∨
        ∃ s : Set.Iic t, coordinate s omega ∈ Cemetery.alive '' Uᶜ := by
  constructor
  · intro hexit
    by_cases hlifetime : omega.lifetime ≤ (t : ENNReal)
    · exact Or.inl hlifetime
    · right
      have ht : (t : ENNReal) < omega.lifetime := lt_of_not_ge hlifetime
      by_contra hhit
      have hgood : ∀ s : Set.Iic t, coordinate s omega ∈ Cemetery.alive '' U := by
        intro s
        have hslife : (s : ENNReal) < omega.lifetime :=
          (ENNReal.coe_le_coe.mpr s.property).trans_lt ht
        rw [coordinate_of_lt omega s hslife]
        let x := omega.livePath ⟨s, hslife⟩
        have hxU : x ∈ U := by
          by_contra hxU
          exact hhit ⟨s, x, hxU, (coordinate_of_lt omega s hslife).symm⟩
        refine ⟨x, hxU, ?_⟩
        dsimp only [x]
      obtain ⟨x, hxU, htx⟩ := hgood ⟨t, Set.mem_Iic.mpr le_rfl⟩
      rw [coordinate_of_lt omega t ht] at htx
      have hx : omega.livePath ⟨t, ht⟩ = x := (Sum.inl.inj htx).symm
      have htU : omega.livePath ⟨t, ht⟩ ∈ U := hx ▸ hxU
      obtain ⟨r, htr, -, hright⟩ := exists_right_interval_in_open omega U hU t ht htU
      have hrle : (r : ENNReal) ≤ exitTime U omega := by
        apply le_sInf
        rintro z ⟨s, rfl, hsbad⟩
        apply ENNReal.coe_le_coe.mpr
        by_contra hsr
        have hsr' : s < r := lt_of_not_ge hsr
        by_cases hst : s ≤ t
        · exact hsbad (hgood ⟨s, Set.mem_Iic.mpr hst⟩)
        · exact hsbad (hright s (lt_of_not_ge hst) hsr')
      exact (not_lt_of_ge hexit) ((ENNReal.coe_lt_coe.mpr htr).trans_le hrle)
  · rintro (hlifetime | ⟨s, x, hxnotU, hsx⟩)
    · exact (exitTime_le_lifetime U omega).trans hlifetime
    · refine (exitTime_le_of_coordinate_notMem U omega s ?_).trans
          (ENNReal.coe_le_coe.mpr s.property)
      rintro ⟨y, hyU, hy⟩
      have hxy : x = y := Sum.inl.inj (hsx.trans hy.symm)
      exact hxnotU (hxy ▸ hyU)

private def detectionThreshold (n : ℕ) : ℝ := 1 / (n + 1 : ℝ)

private def liveInfDist (F : Set alpha) : Cemetery alpha → ℝ :=
  Sum.elim (fun x ↦ Metric.infDist x F) (fun _ ↦ 1)

private def DetectsLiveClosedSetBy (t : NNReal) (F : Set alpha)
    (omega : LifetimePath alpha) : Prop :=
  F.Nonempty ∧ ∀ n : ℕ,
    liveInfDist F (coordinate t omega) < detectionThreshold n ∨
      ∃ k : ℕ, DenseTime.castOrderEmbedding (DenseTime.enumeration k) < t ∧
        liveInfDist F
            (coordinate (DenseTime.castOrderEmbedding (DenseTime.enumeration k)) omega) <
          detectionThreshold n

private theorem detectsLiveClosedSetBy_iff (t : NNReal) (F : Set alpha)
    (hF : IsClosed F) (omega : LifetimePath alpha)
    (ht : (t : ENNReal) < omega.lifetime) :
    DetectsLiveClosedSetBy t F omega ↔
      ∃ s : Set.Iic t, coordinate s omega ∈ Cemetery.alive '' F := by
  have hhit : (∃ s : Set.Iic t, coordinate s omega ∈ Cemetery.alive '' F) ↔
      ∃ s : Set.Iic t, (restrictBefore omega t ht) s ∈ F := by
    constructor
    · rintro ⟨s, x, hxF, hsx⟩
      have hslife : (s : ENNReal) < omega.lifetime :=
        (ENNReal.coe_le_coe.mpr s.property).trans_lt ht
      rw [coordinate_of_lt omega s hslife] at hsx
      have hx : omega.livePath ⟨s, hslife⟩ = x := (Sum.inl.inj hsx).symm
      refine ⟨s, ?_⟩
      rw [restrictBefore_apply]
      exact hx ▸ hxF
    · rintro ⟨s, hsF⟩
      have hslife : (s : ENNReal) < omega.lifetime :=
        (ENNReal.coe_le_coe.mpr s.property).trans_lt ht
      refine ⟨s, omega.livePath ⟨s, hslife⟩, ?_, ?_⟩
      · rw [restrictBefore_apply] at hsF
        exact hsF
      · exact (coordinate_of_lt omega s hslife).symm
  have hrestrict := ContinuousPath.detectsClosedSetOnIic_iff
    t F hF (restrictBefore omega t ht)
  rw [hhit, ← hrestrict]
  constructor
  · rintro ⟨hFnonempty, hdetect⟩
    refine ⟨hFnonempty, fun n ↦ ?_⟩
    rcases hdetect n with hendpoint | ⟨k, hkt, hk⟩
    · left
      simpa only [ContinuousPath.restrictIic, restrictBefore_apply,
        liveInfDist, detectionThreshold,
        coordinate_of_lt omega t ht] using! hendpoint
    · right
      refine ⟨k, hkt, ?_⟩
      have hklife :
          (DenseTime.castOrderEmbedding (DenseTime.enumeration k) : ENNReal) <
            omega.lifetime :=
        (ENNReal.coe_lt_coe.mpr hkt).trans ht
      simpa only [ContinuousPath.restrictIic, restrictBefore_apply,
        liveInfDist, detectionThreshold,
        coordinate_of_lt omega _ hklife] using! hk
  · rintro ⟨hFnonempty, hdetect⟩
    refine ⟨hFnonempty, fun n ↦ ?_⟩
    rcases hdetect n with hendpoint | ⟨k, hkt, hk⟩
    · left
      simpa only [ContinuousPath.restrictIic, restrictBefore_apply,
        liveInfDist, detectionThreshold,
        coordinate_of_lt omega t ht] using! hendpoint
    · right
      refine ⟨k, hkt, ?_⟩
      have hklife :
          (DenseTime.castOrderEmbedding (DenseTime.enumeration k) : ENNReal) <
            omega.lifetime :=
        (ENNReal.coe_lt_coe.mpr hkt).trans ht
      simpa only [ContinuousPath.restrictIic, restrictBefore_apply,
        liveInfDist, detectionThreshold,
        coordinate_of_lt omega _ hklife] using! hk

section Measurable

variable [MeasurableSpace alpha] [BorelSpace alpha]

private theorem measurable_liveInfDist (F : Set alpha) : Measurable (liveInfDist F) := by
  apply measurable_fun_sum
  · exact (Metric.continuous_infDist_pt (s := F)).borel_measurable.mono
      (le_of_eq BorelSpace.measurable_eq.symm) le_rfl
  · exact measurable_const

private theorem measurable_liveInfDist_coordinate (t : NNReal) (F : Set alpha)
    {s : NNReal} (hs : s ≤ t) :
    Measurable[canonicalFiltration (alpha := alpha) t]
      (fun omega : LifetimePath alpha ↦ liveInfDist F (coordinate s omega)) := by
  have hcoordinate : Measurable[canonicalFiltration (alpha := alpha) t]
      (coordinate (α := alpha) s) := by
    apply Measurable.of_comap_le
    exact le_iSup_of_le (⟨s, Set.mem_Iic.mpr hs⟩ : Set.Iic t) le_rfl
  exact (measurable_liveInfDist F).comp hcoordinate

private theorem measurableSet_detectsLiveClosedSetBy (t : NNReal) (F : Set alpha) :
    MeasurableSet[canonicalFiltration (alpha := alpha) t]
      {omega | DetectsLiveClosedSetBy t F omega} := by
  by_cases hFnonempty : F.Nonempty
  swap
  · have hevent : {omega | DetectsLiveClosedSetBy t F omega} = ∅ := by
      ext omega
      change DetectsLiveClosedSetBy t F omega ↔ False
      simp only [DetectsLiveClosedSetBy, hFnonempty, false_and]
    rw [hevent]
    exact @MeasurableSet.empty _ (canonicalFiltration (alpha := alpha) t)
  have hmeas (n : ℕ) : MeasurableSet[canonicalFiltration (alpha := alpha) t]
      ({omega | liveInfDist F (coordinate t omega) < detectionThreshold n} ∪
        ⋃ k : ℕ, if h : DenseTime.castOrderEmbedding (DenseTime.enumeration k) < t then
          {omega | liveInfDist F
            (coordinate (DenseTime.castOrderEmbedding (DenseTime.enumeration k)) omega) <
              detectionThreshold n}
        else ∅) := by
    apply MeasurableSet.union
    · exact (measurable_liveInfDist_coordinate t F le_rfl) measurableSet_Iio
    · apply MeasurableSet.iUnion
      intro k
      split_ifs with hkt
      · exact (measurable_liveInfDist_coordinate t F hkt.le) measurableSet_Iio
      · exact @MeasurableSet.empty _ (canonicalFiltration (alpha := alpha) t)
  have hevent : {omega | DetectsLiveClosedSetBy t F omega} =
      ⋂ n : ℕ,
        ({omega | liveInfDist F (coordinate t omega) < detectionThreshold n} ∪
          ⋃ k : ℕ, if h : DenseTime.castOrderEmbedding (DenseTime.enumeration k) < t then
            {omega | liveInfDist F
              (coordinate (DenseTime.castOrderEmbedding (DenseTime.enumeration k)) omega) <
                detectionThreshold n}
          else ∅) := by
    ext omega
    simp only [DetectsLiveClosedSetBy, hFnonempty, true_and, Set.mem_ofPred_eq,
      Set.mem_iInter, Set.mem_union, Set.mem_iUnion]
    constructor
    · intro h n
      rcases h n with hendpoint | ⟨k, hkt, hk⟩
      · exact Or.inl hendpoint
      · exact Or.inr ⟨k, by rw [dite_eq_left hkt]; exact hk⟩
    · intro h n
      rcases h n with hendpoint | ⟨k, hk⟩
      · exact Or.inl hendpoint
      · by_cases hkt : DenseTime.castOrderEmbedding (DenseTime.enumeration k) < t
        · exact Or.inr ⟨k, hkt, by simpa only [dite_eq_left hkt] using! hk⟩
        · simp only [dite_eq_right hkt, Set.notMem_empty] at hk
  rw [hevent]
  exact MeasurableSet.iInter hmeas

/-- The exit time from an open set is a stopping time for the raw canonical filtration. -/
theorem isStoppingTime_exitTime (U : Set alpha) (hU : IsOpen U) :
    IsStoppingTime (canonicalFiltration (alpha := alpha)) (exitTime U) := by
  intro t
  let death : Set (LifetimePath alpha) :=
    {omega | omega.lifetime ≤ (t : ENNReal)}
  let spatial : Set (LifetimePath alpha) :=
    {omega | (t : ENNReal) < omega.lifetime ∧ DetectsLiveClosedSetBy t Uᶜ omega}
  have hdeath : MeasurableSet[canonicalFiltration (alpha := alpha) t] death :=
    isStoppingTime_lifetime t
  have hpast : MeasurableSet[canonicalFiltration (alpha := alpha) t]
      {omega : LifetimePath alpha | (t : ENNReal) < omega.lifetime} := by
    have hcompl : {omega : LifetimePath alpha | (t : ENNReal) < omega.lifetime} = deathᶜ := by
      ext omega
      simp only [death, Set.mem_ofPred_eq, Set.mem_compl_iff]
      exact lt_iff_not_ge
    rw [hcompl]
    exact hdeath.compl
  have hspatial : MeasurableSet[canonicalFiltration (alpha := alpha) t] spatial := by
    exact hpast.inter (measurableSet_detectsLiveClosedSetBy t Uᶜ)
  have hevent : {omega : LifetimePath alpha | exitTime U omega ≤ (t : ENNReal)} =
      death ∪ spatial := by
    ext omega
    change (exitTime U omega ≤ (t : ENNReal)) ↔ _
    rw [Set.mem_union]
    rw [exitTime_le_iff U hU]
    by_cases hlifetime : omega.lifetime ≤ (t : ENNReal)
    · simp only [death, spatial, Set.mem_ofPred_eq, hlifetime, true_or,
        not_lt_of_ge hlifetime, false_and, or_false]
    · have ht : (t : ENNReal) < omega.lifetime := lt_of_not_ge hlifetime
      have hdetect := detectsLiveClosedSetBy_iff t Uᶜ hU.isClosed_compl omega ht
      simp only [death, spatial, Set.mem_ofPred_eq, hlifetime, false_or, ht, true_and]
      exact hdetect.symm
  change MeasurableSet[canonicalFiltration (alpha := alpha) t]
    {omega : LifetimePath alpha | exitTime U omega ≤ (t : ENNReal)}
  rw [hevent]
  exact hdeath.union hspatial

end Measurable

end
end MarkovProcess.LifetimePath

end PortComputability
