/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.Concentration

/-! # Concentration AEMeasurable -/

namespace Homogenization
namespace Book
namespace Ch04

/-!
# A.e.-measurable concentration bridges

The public independent-sum concentration theorems are stated for measurable
summands.  Chapter 4 local-test observables are naturally only
a.e.-measurable under a law carrier.  This file provides the small bridge used
by completed-local partition arguments: replace each summand by its measurable
representative, use a.e. congruence to preserve independence, and transfer the
tail conclusion back.
-/

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem measureReal_mono_ae [IsFiniteMeasure μ] {s t : Set Ω}
    (hst : s ≤ᵐ[μ] t) :
    μ.real s ≤ μ.real t :=
  ENNReal.toReal_mono (by finiteness) (measure_mono_ae hst)

theorem isBigOWith_of_ae_le [IsFiniteMeasure μ] {Ψ : ℝ → ℝ}
    {X Y : Ω → ℝ} {A : ℝ}
    (hX : IsBigOWith μ Ψ X A) (hYX : ∀ᵐ ω ∂μ, Y ω ≤ X ω) :
    IsBigOWith μ Ψ Y A := by
  intro t ht
  refine (measureReal_mono_ae (μ := μ) ?_).trans (hX ht)
  filter_upwards [hYX] with ω hω htail
  exact lt_of_lt_of_le htail hω

theorem isBigO_congr_ae {Ψ : ℝ → ℝ} {X Y : Ω → ℝ} {A : ℝ}
    (hXY : X =ᵐ[μ] Y) :
    IsBigO μ Ψ X A ↔ IsBigO μ Ψ Y A := by
  constructor
  · intro hX t ht
    have hset :
        absTailEvent X (A * t) =ᵐ[μ] absTailEvent Y (A * t) := by
      filter_upwards [hXY] with ω hω
      apply propext
      change A * t < |X ω| ↔ A * t < |Y ω|
      rw [hω]
    have hmeasure :
        μ.real (absTailEvent Y (A * t)) =
          μ.real (absTailEvent X (A * t)) := by
      exact congrArg ENNReal.toReal (MeasureTheory.measure_congr hset.symm)
    change μ.real (absTailEvent Y (A * t)) ≤ (Ψ t)⁻¹
    rw [hmeasure]
    simpa [IndependentSums.absTailEvent] using hX ht
  · intro hY t ht
    have hset :
        absTailEvent Y (A * t) =ᵐ[μ] absTailEvent X (A * t) := by
      filter_upwards [hXY] with ω hω
      apply propext
      change A * t < |Y ω| ↔ A * t < |X ω|
      rw [hω]
    have hmeasure :
        μ.real (absTailEvent X (A * t)) =
          μ.real (absTailEvent Y (A * t)) := by
      exact congrArg ENNReal.toReal (MeasureTheory.measure_congr hset.symm)
    change μ.real (absTailEvent X (A * t)) ≤ (Ψ t)⁻¹
    rw [hmeasure]
    simpa [IndependentSums.absTailEvent] using hY ht

theorem isBigO_gammaSigma_iff_of_map_eq_map
    {σ A : ℝ} {X Y : Ω → ℝ}
    (hX_meas : Measurable X) (hY_meas : Measurable Y)
    (hmap : Measure.map X μ = Measure.map Y μ) :
    IsBigO μ (gammaSigma σ) X A ↔ IsBigO μ (gammaSigma σ) Y A := by
  rw [isBigO_gammaSigma_iff, isBigO_gammaSigma_iff]
  constructor
  · intro hX t ht
    let s : Set ℝ := {x | A * t < |x|}
    have hs : MeasurableSet s := by
      dsimp [s]
      exact measurableSet_lt measurable_const continuous_abs.measurable
    have hmass := congrArg (fun ν : Measure ℝ => ν s) hmap
    have hmass_real := congrArg ENNReal.toReal hmass
    have hXY :
        μ.real (absTailEvent X (A * t)) =
          μ.real (absTailEvent Y (A * t)) := by
      simpa [s, absTailEvent, Measure.map_apply hX_meas hs,
        Measure.map_apply hY_meas hs] using! hmass_real
    rw [← hXY]
    exact hX ht
  · intro hY t ht
    let s : Set ℝ := {x | A * t < |x|}
    have hs : MeasurableSet s := by
      dsimp [s]
      exact measurableSet_lt measurable_const continuous_abs.measurable
    have hmass := congrArg (fun ν : Measure ℝ => ν s) hmap
    have hmass_real := congrArg ENNReal.toReal hmass
    have hYX :
        μ.real (absTailEvent Y (A * t)) =
          μ.real (absTailEvent X (A * t)) := by
      simpa [s, absTailEvent, Measure.map_apply hX_meas hs,
        Measure.map_apply hY_meas hs] using! hmass_real.symm
    rw [← hYX]
    exact hY ht

theorem isBigO_gammaSigma_iff_of_map_eq_map_aemeasurable
    {σ A : ℝ} {X Y : Ω → ℝ}
    (hX_aemeas : AEMeasurable X μ) (hY_aemeas : AEMeasurable Y μ)
    (hmap : Measure.map X μ = Measure.map Y μ) :
    IsBigO μ (gammaSigma σ) X A ↔ IsBigO μ (gammaSigma σ) Y A := by
  let Xm : Ω → ℝ := hX_aemeas.mk X
  let Ym : Ω → ℝ := hY_aemeas.mk Y
  have hXXm : X =ᵐ[μ] Xm := hX_aemeas.ae_eq_mk
  have hYYm : Y =ᵐ[μ] Ym := hY_aemeas.ae_eq_mk
  have hmap_mk : Measure.map Xm μ = Measure.map Ym μ := by
    calc
      Measure.map Xm μ = Measure.map X μ := (Measure.map_congr hXXm).symm
      _ = Measure.map Y μ := hmap
      _ = Measure.map Ym μ := Measure.map_congr hYYm
  have hmk :=
    isBigO_gammaSigma_iff_of_map_eq_map
      (μ := μ) (σ := σ) (A := A)
      hX_aemeas.measurable_mk hY_aemeas.measurable_mk hmap_mk
  exact
    (isBigO_congr_ae (μ := μ) (Ψ := gammaSigma σ) (A := A) hXXm).trans
      (hmk.trans
        (isBigO_congr_ae (μ := μ) (Ψ := gammaSigma σ) (A := A) hYYm).symm)

theorem isBigOWith_gammaSigma_iff_of_map_eq_map
    {σ A : ℝ} {X Y : Ω → ℝ}
    (hX_meas : Measurable X) (hY_meas : Measurable Y)
    (hmap : Measure.map X μ = Measure.map Y μ) :
    IsBigOWith μ (gammaSigma σ) X A ↔
      IsBigOWith μ (gammaSigma σ) Y A := by
  rw [isBigOWith_gammaSigma_iff, isBigOWith_gammaSigma_iff]
  constructor
  · intro hX t ht
    let s : Set ℝ := {x | A * t < x}
    have hs : MeasurableSet s := by
      dsimp [s]
      exact measurableSet_lt measurable_const measurable_id
    have hmass := congrArg (fun ν : Measure ℝ => ν s) hmap
    have hmass_real := congrArg ENNReal.toReal hmass
    have hXY :
        μ.real (upperTailEvent X (A * t)) =
          μ.real (upperTailEvent Y (A * t)) := by
      simpa [s, upperTailEvent, Measure.map_apply hX_meas hs,
        Measure.map_apply hY_meas hs] using! hmass_real
    rw [← hXY]
    exact hX ht
  · intro hY t ht
    let s : Set ℝ := {x | A * t < x}
    have hs : MeasurableSet s := by
      dsimp [s]
      exact measurableSet_lt measurable_const measurable_id
    have hmass := congrArg (fun ν : Measure ℝ => ν s) hmap
    have hmass_real := congrArg ENNReal.toReal hmass
    have hYX :
        μ.real (upperTailEvent Y (A * t)) =
          μ.real (upperTailEvent X (A * t)) := by
      simpa [s, upperTailEvent, Measure.map_apply hX_meas hs,
        Measure.map_apply hY_meas hs] using! hmass_real.symm
    rw [← hYX]
    exact hY ht

theorem isBigOWith_gammaSigma_iff_of_map_eq_map_aemeasurable
    {σ A : ℝ} {X Y : Ω → ℝ}
    [IsFiniteMeasure μ]
    (hX_aemeas : AEMeasurable X μ) (hY_aemeas : AEMeasurable Y μ)
    (hmap : Measure.map X μ = Measure.map Y μ) :
    IsBigOWith μ (gammaSigma σ) X A ↔
      IsBigOWith μ (gammaSigma σ) Y A := by
  let Xm : Ω → ℝ := hX_aemeas.mk X
  let Ym : Ω → ℝ := hY_aemeas.mk Y
  have hXXm : X =ᵐ[μ] Xm := hX_aemeas.ae_eq_mk
  have hYYm : Y =ᵐ[μ] Ym := hY_aemeas.ae_eq_mk
  have hmap_mk : Measure.map Xm μ = Measure.map Ym μ := by
    calc
      Measure.map Xm μ = Measure.map X μ := (Measure.map_congr hXXm).symm
      _ = Measure.map Y μ := hmap
      _ = Measure.map Ym μ := Measure.map_congr hYYm
  have hmk :=
    isBigOWith_gammaSigma_iff_of_map_eq_map
      (μ := μ) (σ := σ) (A := A)
      hX_aemeas.measurable_mk hY_aemeas.measurable_mk hmap_mk
  constructor
  · intro hX
    refine Ch04.isBigOWith_of_ae_le (μ := μ) (Ψ := gammaSigma σ)
      (X := Ym) (Y := Y) ?_ ?_
    · exact (hmk.1
        (Ch04.isBigOWith_of_ae_le (μ := μ) (Ψ := gammaSigma σ)
          (X := X) (Y := Xm) hX (hXXm.mono fun _ h => by rw [← h])))
    · exact hYYm.mono fun _ h => by rw [h]
  · intro hY
    refine Ch04.isBigOWith_of_ae_le (μ := μ) (Ψ := gammaSigma σ)
      (X := Xm) (Y := X) ?_ ?_
    · exact (hmk.2
        (Ch04.isBigOWith_of_ae_le (μ := μ) (Ψ := gammaSigma σ)
          (X := Y) (Y := Ym) hY (hYYm.mono fun _ h => by rw [← h])))
    · exact hXXm.mono fun _ h => by rw [h]

theorem isBigO_finset_sum_of_isBigO_gammaSigma_aemeasurable
    (s : Finset ι) {X : ι → Ω → ℝ} {a : ι → ℝ} {σ : ℝ}
    [IsFiniteMeasure μ]
    (hσ : 0 < σ)
    (hs : s.Nonempty)
    (ha : ∀ i ∈ s, 0 < a i)
    (hX : ∀ i ∈ s, IsBigO μ (gammaSigma σ) (X i) (a i))
    (hXm : ∀ i, AEMeasurable (X i) μ) :
    IsBigO μ (gammaSigma σ) (fun ω => Finset.sum s (fun i => X i ω))
      (gammaTriangleConst σ * Finset.sum s a) := by
  classical
  let Y : ι → Ω → ℝ := fun i => (hXm i).mk (X i)
  have hXY : ∀ i, X i =ᵐ[μ] Y i := fun i => (hXm i).ae_eq_mk
  have hY : ∀ i ∈ s, IsBigO μ (gammaSigma σ) (Y i) (a i) := by
    intro i hi
    exact (isBigO_congr_ae (μ := μ) (Ψ := gammaSigma σ)
      (A := a i) (hXY i)).1 (hX i hi)
  have hYm : ∀ i ∈ s, Measurable (Y i) := by
    intro i _hi
    exact (hXm i).measurable_mk
  have hsumY :=
    isBigO_finset_sum_of_isBigO_gammaSigma
      (μ := μ) s hσ hs ha hY hYm
  have hsumXY :
      (fun ω => Finset.sum s (fun i => X i ω)) =ᵐ[μ]
        fun ω => Finset.sum s (fun i => Y i ω) := by
    have hAll : ∀ᵐ ω ∂μ, ∀ i ∈ s, X i ω = Y i ω := by
      rw [Filter.eventually_all_finset]
      intro i _hi
      exact hXY i
    filter_upwards [hAll] with ω hω
    exact Finset.sum_congr rfl fun i hi => hω i hi
  exact (isBigO_congr_ae (μ := μ) (Ψ := gammaSigma σ)
    (A := gammaTriangleConst σ * Finset.sum s a) hsumXY).2 hsumY

theorem isBigO_finsetAverage_of_isBigO_gammaSigma_aemeasurable
    (s : Finset ι) {X : ι → Ω → ℝ} {a : ι → ℝ} {σ : ℝ}
    [IsFiniteMeasure μ]
    (hσ : 0 < σ)
    (hs : s.Nonempty)
    (ha : ∀ i ∈ s, 0 < a i)
    (hX : ∀ i ∈ s, IsBigO μ (gammaSigma σ) (X i) (a i))
    (hXm : ∀ i, AEMeasurable (X i) μ) :
    IsBigO μ (gammaSigma σ)
      (fun ω => ((s.card : ℝ)⁻¹) * Finset.sum s (fun i => X i ω))
      (gammaTriangleConst σ * (((s.card : ℝ)⁻¹) * Finset.sum s a)) := by
  classical
  let Y : ι → Ω → ℝ := fun i => (hXm i).mk (X i)
  have hXY : ∀ i, X i =ᵐ[μ] Y i := fun i => (hXm i).ae_eq_mk
  have hY : ∀ i ∈ s, IsBigO μ (gammaSigma σ) (Y i) (a i) := by
    intro i hi
    exact (isBigO_congr_ae (μ := μ) (Ψ := gammaSigma σ)
      (A := a i) (hXY i)).1 (hX i hi)
  have hYm : ∀ i ∈ s, Measurable (Y i) := by
    intro i _hi
    exact (hXm i).measurable_mk
  have havgY :=
    isBigO_finsetAverage_of_isBigO_gammaSigma
      (μ := μ) s hσ hs ha hY hYm
  have havgXY :
      (fun ω => ((s.card : ℝ)⁻¹) * Finset.sum s (fun i => X i ω)) =ᵐ[μ]
        fun ω => ((s.card : ℝ)⁻¹) * Finset.sum s (fun i => Y i ω) := by
    have hAll : ∀ᵐ ω ∂μ, ∀ i ∈ s, X i ω = Y i ω := by
      rw [Filter.eventually_all_finset]
      intro i _hi
      exact hXY i
    filter_upwards [hAll] with ω hω
    congr 1
    exact Finset.sum_congr rfl fun i hi => hω i hi
  exact (isBigO_congr_ae (μ := μ) (Ψ := gammaSigma σ)
    (A := gammaTriangleConst σ * (((s.card : ℝ)⁻¹) * Finset.sum s a))
    havgXY).2 havgY

theorem isBigO_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero_aemeasurable
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {s : Finset ι} {σ K : ℝ}
    (h_indep : ProbabilityTheory.iIndepFun X μ)
    (h_aemeas : ∀ i, AEMeasurable (X i) μ)
    (hs : s.Nonempty)
    (hσ₀ : 0 < σ) (hσ₂ : σ ≤ 2)
    (hK : 0 < K)
    (hX : ∀ i ∈ s, IsBigO μ (gammaSigma σ) (X i) K)
    (h_mean : ∀ i ∈ s, ∫ ω, X i ω ∂μ = 0) :
    IsBigO μ (gammaSigma σ) (fun ω => ∑ i ∈ s, X i ω)
      (gammaSigmaIndependentSumConst σ * Real.sqrt (s.card : ℝ) * K) := by
  classical
  let Y : ι → Ω → ℝ := fun i => (h_aemeas i).mk (X i)
  have hXY : ∀ i, X i =ᵐ[μ] Y i := fun i => (h_aemeas i).ae_eq_mk
  have hY_indep : ProbabilityTheory.iIndepFun Y μ := h_indep.congr hXY
  have hY_meas : ∀ i, Measurable (Y i) := fun i => (h_aemeas i).measurable_mk
  have hY_tail :
      ∀ i ∈ s, IsBigO μ (gammaSigma σ) (Y i) K := by
    intro i hi
    exact (isBigO_congr_ae (μ := μ) (Ψ := gammaSigma σ)
      (A := K) (hXY i)).1 (hX i hi)
  have hY_mean : ∀ i ∈ s, ∫ ω, Y i ω ∂μ = 0 := by
    intro i hi
    calc
      ∫ ω, Y i ω ∂μ = ∫ ω, X i ω ∂μ := integral_congr_ae (hXY i).symm
      _ = 0 := h_mean i hi
  have hsumY :=
    isBigO_gammaSigma_finset_sum_of_iIndepFun_of_isBigO_of_integral_eq_zero
      (μ := μ) (X := Y) (s := s) (σ := σ) (K := K)
      hY_indep hY_meas hs hσ₀ hσ₂ hK hY_tail hY_mean
  have hsumXY :
      (fun ω => ∑ i ∈ s, X i ω) =ᵐ[μ] fun ω => ∑ i ∈ s, Y i ω := by
    have hAll : ∀ᵐ ω ∂μ, ∀ i ∈ s, X i ω = Y i ω := by
      rw [Filter.eventually_all_finset]
      intro i _hi
      exact hXY i
    filter_upwards [hAll] with ω hω
    exact Finset.sum_congr rfl fun i hi => hω i hi
  exact (isBigO_congr_ae (μ := μ) (Ψ := gammaSigma σ)
      (A := gammaSigmaIndependentSumConst σ * Real.sqrt (s.card : ℝ) * K)
    hsumXY).2 hsumY

theorem isBigO_gammaSigma_const_of_abs_le
    [IsFiniteMeasure μ] {σ A c : ℝ}
    (hA : 0 ≤ A) (hc : |c| ≤ A) :
    IsBigO μ (gammaSigma σ) (fun _ω : Ω => c) A := by
  rw [isBigO_gammaSigma_iff]
  intro t ht
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  have hAt : A ≤ A * t := by
    calc
      A = A * 1 := by ring
      _ ≤ A * t := mul_le_mul_of_nonneg_left ht hA
  have htail_empty :
      absTailEvent (fun _ω : Ω => c) (A * t) = ∅ := by
    ext ω
    simp [absTailEvent, not_lt_of_ge (hc.trans hAt)]
  rw [htail_empty]
  simpa using (Real.exp_pos (-(t ^ σ))).le

theorem isBigO_gammaSigma_sub_const_of_abs_const_le_aemeasurable
    [IsFiniteMeasure μ] {σ K M c : ℝ} {X : Ω → ℝ}
    (hσ : 0 < σ) (hK : 0 < K) (hM : 0 < M)
    (hX : IsBigO μ (gammaSigma σ) X K)
    (hXm : AEMeasurable X μ) (hc : |c| ≤ M) :
    IsBigO μ (gammaSigma σ) (fun ω => X ω - c)
      (gammaTriangleConst σ * (K + M)) := by
  classical
  let Y : Bool → Ω → ℝ := fun b =>
    if b then fun _ω => -c else X
  let a : Bool → ℝ := fun b => if b then M else K
  have hY :
      ∀ b ∈ (Finset.univ : Finset Bool),
        IsBigO μ (gammaSigma σ) (Y b) (a b) := by
    intro b _hb
    cases b
    · simpa [Y, a] using hX
    · have hconst :
          IsBigO μ (gammaSigma σ) (fun _ω : Ω => -c) M := by
        refine isBigO_gammaSigma_const_of_abs_le (μ := μ)
          (σ := σ) hM.le ?_
        simpa [abs_neg] using hc
      simpa [Y, a] using hconst
  have hYaemeas : ∀ b, AEMeasurable (Y b) μ := by
    intro b
    cases b
    · simpa [Y] using hXm
    · simp [Y]
  have ha : ∀ b ∈ (Finset.univ : Finset Bool), 0 < a b := by
    intro b _hb
    cases b <;> simp [a, hK, hM]
  have hsum :=
    isBigO_finset_sum_of_isBigO_gammaSigma_aemeasurable
      (μ := μ) (s := (Finset.univ : Finset Bool)) (X := Y) (a := a)
      (σ := σ) hσ (Finset.univ_nonempty) ha hY hYaemeas
  have hsum_fun :
      (fun ω => ∑ b ∈ (Finset.univ : Finset Bool), Y b ω) =
        fun ω => X ω - c := by
    funext ω
    simp [Y, sub_eq_add_neg]
    ring
  have hsum_scale :
      (∑ b ∈ (Finset.univ : Finset Bool), a b) = K + M := by
    simp [a, add_comm]
  convert hsum using 1
  · exact hsum_fun.symm
  · rw [hsum_scale]

end

end Ch04
end Book
end Homogenization
