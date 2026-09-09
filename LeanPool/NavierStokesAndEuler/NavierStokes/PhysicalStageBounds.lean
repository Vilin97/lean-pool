/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalMeanJetBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.TailGaugePotential
public import LeanPool.NavierStokesAndEuler.NavierStokes.CutStageEstimates

/-!
# Raw physical stage estimates from native wave and mean data

The data below describe the actual copy families and coherent native mean
fields. Physical derivative estimates are consequences of their native
classes, support and chart identities. No `RawStageBounds` is an input.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.PhysicalStageBounds

open Set Function Filter ProblemStatement
open scoped Topology ContDiff BigOperators

private theorem nat_le_infty (m : ℕ) : (m : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl m

/-- Small physical q automatically restricts time to the interval on which
the existing physical-copy estimates are uniform. -/
theorem abs_time_le_one {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {w : SpaceTime} (hw : w ∈ PhysicalWaveSum.preterminal)
    (hq : PhysicalWaveSum.physicalQ h w ≤ 1) : |w.1| ≤ 1 := by
  have ha : 0 < 2 * h := by positivity
  have ha1 : 2 * h < 1 := by linarith
  have he := SimilarityCoordinates.coordinateQ_spec ha ha1
    (p := (1 - w.1, w.2 2)) (sub_pos.mpr hw)
  have hn : 0 ≤ (w.2 2) ^ 2 *
      SimilarityCoordinates.coordinateQ (2 * h) (1 - w.1, w.2 2) ^ (2 * h) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg he.1.le _)
  change SimilarityCoordinates.coordinateQ (2 * h) (1 - w.1, w.2 2) ≤ 1 at hq
  have heq : SimilarityCoordinates.coordinateQ (2 * h) (1 - w.1, w.2 2) -
      (w.2 2) ^ 2 * SimilarityCoordinates.coordinateQ (2 * h) (1 - w.1, w.2 2) ^ (2 * h) =
      1 - w.1 := he.2
  change w.1 < 1 at hw
  apply abs_le.mpr
  constructor <;> linarith

section Waves

variable (h : ℝ) (D : Type) [NormedAddCommGroup D] [NormedSpace ℝ D]
  (I K J : Type*)

/-- A native source and its actual physical copy representation. All
regularity is confined to the valid native patches. The number of
harmonics and the cover gap may vary between stages. -/
structure WaveData where
  /-- Lower radius of `WaveData`, of type `ℝ`. -/
  lowerRadius : ℝ
  /-- Upper radius of `WaveData`, of type `ℝ`. -/
  upperRadius : ℝ
  /-- Native width of `WaveData`, of type `ℝ`. -/
  nativeWidth : ℝ
  /-- Slow bound of `WaveData`, of type `ℝ`. -/
  slowBound : ℝ
  /-- Frequency bound of `WaveData`, of type `ℝ`. -/
  frequencyBound : ℝ
  /-- Alpha of `WaveData`, of type `ℝ`. -/
  alpha : ℝ
  /-- Shift of `WaveData`, of type `ℝ`. -/
  shift : ℝ
  /-- Harmonics of `WaveData`, of type `ℕ`. -/
  harmonics : ℕ
  /-- Gap bound of `WaveData`, of type `ℕ`. -/
  gapBound : ℕ
  lower_pos : 0 < lowerRadius
  width_nonneg : 0 ≤ nativeWidth
  slow_nonneg : 0 ≤ slowBound
  frequency_one_le : 1 ≤ frequencyBound
  /-- Strip of `WaveData`, of type `WeightedClasses.StripData D`. -/
  strip : WeightedClasses.StripData D
  /-- Weight of `WaveData`, of type `I → ℕ → D → ℝ`. -/
  weight : I → ℕ → D → ℝ
  /-- Source of `WaveData`, of type `I → ℕ → D → ℂ`. -/
  source : I → ℕ → D → ℂ
  source_bounds : LocalPhysicalCopyBounds.LocalSourceBounds strip h alpha weight source
  /-- Copies of `WaveData`, of type `J → PhysicalCopyBounds.CopyFamily harmonics K`. -/
  copies : J → PhysicalCopyBounds.CopyFamily harmonics K
  /-- Cells of `WaveData`, of type `∀ i, PhysicalCopyBounds.SupportCells (copies i)`. -/
  cells : ∀ i, PhysicalCopyBounds.SupportCells (copies i)
  /-- Chart supplied by `WaveData`. -/
  chart : ∀ i, LocalPhysicalCopyBounds.CommonChart (copies i) (cells i)
    lowerRadius upperRadius h nativeWidth shift source
  chart_maps : ∀ i k L, MapsTo ((chart i).map k L) ((chart i).domain k L) strip.domain
  /-- Carrier supplied by `WaveData`. -/
  carrier : ∀ i, PhysicalCopyBounds.CarrierBounds (copies i) (cells i)
    lowerRadius upperRadius h nativeWidth
  support : ∀ i, LocalPhysicalCopyBounds.SupportData (copies i)
    lowerRadius upperRadius h nativeWidth slowBound gapBound
  smooth : ∀ i, LocalPhysicalCopyBounds.SmoothData (copies i) lowerRadius h nativeWidth
  frequencies : ∀ i k L, |((copies i).carrier k L).angular| ≤ frequencyBound ∧
    |((copies i).carrier k L).axial| ≤ frequencyBound ∧
    |((copies i).carrier k L).radial| ≤ frequencyBound

variable {h D I K J}

/-- Scalar, given by `(W.copies i).sum W.lowerRadius h W.nativeWidth`. -/
noncomputable def WaveData.scalar (W : WaveData h D I K J) (i : J) : SpaceTime → ℂ :=
  (W.copies i).sum W.lowerRadius h W.nativeWidth

theorem WaveData.scalar_smooth (W : WaveData h D I K J)
    (hh : 0 < h) (hh1 : h < 1 / 2) (i : J) :
    ContDiffOn ℝ ∞ (W.scalar i) PhysicalWaveSum.preterminal :=
  (W.support i).sum_smooth (W.smooth i) (W.cells i) W.lower_pos hh hh1

/-- The physical exponent and loss are obtained from the native weighted
source and actual chart map, not from a physical-bound hypothesis. -/
theorem WaveData.scalar_bound (W : WaveData h D I K J)
    (hh : 0 < h) (hh1 : h < 1 / 2) (i : J) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ PhysicalWaveSum.preterminal,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (W.scalar i) w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^
          (h * W.alpha - PhysicalClassBounds.physicalLoss h W.shift m) := by
  obtain ⟨C, hC, hb⟩ := LocalPhysicalCopyBounds.physical_sum_jet_bound_of_weighted
    W.source_bounds (W.chart i) (W.chart_maps i) (W.carrier i) (W.support i) (W.smooth i)
    hh hh1 W.lower_pos W.slow_nonneg W.width_nonneg W.frequency_one_le (W.frequencies i) m
  exact ⟨C, hC, fun w hw hq => hb w hw (abs_time_le_one hh hh1 hw hq)⟩

/-- Vector, given by `PhysicalCopyBounds.vectorSum W.copies W.lowerRadius h W.nativeWidth`. -/
noncomputable def WaveData.vector (W : WaveData h D I K (Fin 3)) : VelocityField :=
  PhysicalCopyBounds.vectorSum W.copies W.lowerRadius h W.nativeWidth

theorem WaveData.vector_smooth (W : WaveData h D I K (Fin 3))
    (hh : 0 < h) (hh1 : h < 1 / 2) :
    ContDiffOn ℝ ∞ W.vector PhysicalWaveSum.preterminal :=
  LocalPhysicalCopyBounds.vectorSum_smooth W.support W.smooth W.cells W.lower_pos hh hh1

theorem WaveData.vector_bound (W : WaveData h D I K (Fin 3))
    (hh : 0 < h) (hh1 : h < 1 / 2) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ PhysicalWaveSum.preterminal,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m W.vector w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^
          (h * W.alpha - PhysicalClassBounds.physicalLoss h W.shift m) := by
  obtain ⟨C, hC, hb⟩ := LocalPhysicalCopyBounds.physical_vector_sum_jet_bound_of_weighted
    W.source_bounds W.cells W.chart W.chart_maps W.carrier W.support W.smooth
    hh hh1 W.lower_pos W.slow_nonneg W.width_nonneg W.frequency_one_le W.frequencies m
  exact ⟨C, hC, fun w hw hq => hb w hw (abs_time_le_one hh hh1 hw hq)⟩

/-- Pressure, defined pointwise by `(W.scalar () w).re`. -/
noncomputable def WaveData.pressure (W : WaveData h D I K Unit) : PressureField :=
  fun w => (W.scalar () w).re

theorem WaveData.pressure_smooth (W : WaveData h D I K Unit)
    (hh : 0 < h) (hh1 : h < 1 / 2) :
    ContDiffOn ℝ ∞ W.pressure PhysicalWaveSum.preterminal :=
  Complex.reCLM.contDiff.comp_contDiffOn (W.scalar_smooth hh hh1 ())

theorem WaveData.pressure_bound (W : WaveData h D I K Unit)
    (hh : 0 < h) (hh1 : h < 1 / 2) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ PhysicalWaveSum.preterminal,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m W.pressure w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^
          (h * W.alpha - PhysicalClassBounds.physicalLoss h W.shift m) := by
  obtain ⟨C, hC, hb⟩ := W.scalar_bound hh hh1 () m
  refine ⟨‖Complex.reCLM‖ * C, mul_nonneg (norm_nonneg _) hC, ?_⟩
  intro w hw hq
  have hs := ((W.scalar_smooth hh hh1 ()).contDiffAt
    (PhysicalWaveSum.preterminal_open.mem_nhds hw)).of_le (nat_le_infty m)
  have hc := PhysicalWaveSum.norm_jet_linear_comp_at hs Complex.reCLM
  exact hc.trans ((mul_le_mul_of_nonneg_left (hb w hw hq) (norm_nonneg _)).trans_eq (by ring))

end Waves

/-- Actual coherent mean fields with native local-band classes. The
construction keeps a single physical field represented by all valid bands. -/
structure MeanData (h degree : ℝ) where
  /-- First band of `MeanData`, of type `ℕ`. -/
  firstBand : ℕ
  /-- Gap bound of `MeanData`, of type `ℕ`. -/
  gapBound : ℕ
  /-- Region of `MeanData`, of type `Set PhysicalGraphBounds.Plane`. -/
  region : Set PhysicalGraphBounds.Plane
  /-- Lower radius of `MeanData`, of type `ℝ`. -/
  lowerRadius : ℝ
  /-- Upper radius of `MeanData`, of type `ℝ`. -/
  upperRadius : ℝ
  /-- Alpha of `MeanData`, of type `ℝ`. -/
  alpha : ℝ
  /-- Slow of `MeanData`, of type `ℕ → ℝ`. -/
  slow : ℕ → ℝ
  /-- Family of `MeanData`, of type `PhysicalMeanJetBounds.CoherentFamily h degree firstBand
  gapBound region ℝ`. -/
  family : PhysicalMeanJetBounds.CoherentFamily h degree firstBand gapBound region ℝ
  band_four : 4 ≤ firstBand
  lower_pos : 0 < lowerRadius
  radii_lt : lowerRadius < upperRadius
  region_open : IsOpen region
  region_covers : PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 4) 4 ⊆ region
  smooth : ∀ n ≥ firstBand, ContDiffOn ℝ ∞ (family.native n) (PhysicalMeanDomain.slowDomain region)
  support : PhysicalMeanJetBounds.NativeSupport h lowerRadius upperRadius firstBand region
      family.native
  slow_nonneg : ∀ n ≥ firstBand, 0 ≤ slow n
  slow_growth : ∃ C : ℝ, 1 ≤ C ∧ ∃ p : ℕ, ∀ n ≥ firstBand, slow n ≤ C * ChartScales.S n ^ p
  native_class : PhysicalMeanDomain.LocalBandJets region (ChartScales.epsilon h) slow alpha
      family.native

theorem MeanData.nativeJets {h degree : ℝ} (M : MeanData h degree) :
    PhysicalMeanJetBounds.NativeJets M.firstBand M.region (h * M.alpha) M.family.native := by
  obtain ⟨C, hC, p, hp⟩ := M.slow_growth
  exact PhysicalMeanJetBounds.NativeJets.of_localBandJets M.native_class
    (fun _ _ => rfl) M.slow_nonneg hC hp

theorem MeanData.field_smooth {h degree qbig : ℝ} (M : MeanData h degree)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hq : qbig ≤ ChartScales.Q M.firstBand) :
    ContDiffOn ℝ ∞ M.family.field (CutStageEstimates.physicalSublevel h qbig) := by
  apply (M.family.field_smooth hh hh1 M.lower_pos M.radii_lt M.region_open
    M.region_covers M.smooth M.support).mono
  intro w hw
  exact ⟨hw.1, hw.2.trans_le hq⟩

theorem MeanData.angular_smooth {h degree qbig : ℝ} (M : MeanData h degree)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hq : qbig ≤ ChartScales.Q M.firstBand) :
    ContDiffOn ℝ ∞ M.family.angularField (CutStageEstimates.physicalSublevel h qbig) := by
  apply (M.family.angularField_smooth hh hh1 M.lower_pos M.radii_lt M.region_open
    M.region_covers M.smooth M.support).mono
  intro w hw
  exact ⟨hw.1, hw.2.trans_le hq⟩

theorem MeanData.field_bound {h degree qbig : ℝ} (M : MeanData h degree)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hq : qbig ≤ ChartScales.Q M.firstBand) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m M.family.field w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^ (h * M.alpha - PhysicalMeanJetBounds.loss degree m) :=
            by
  obtain ⟨C, hC, hb⟩ := M.family.field_jet_bound hh hh1 M.lower_pos M.radii_lt M.band_four
    M.region_open M.region_covers M.smooth M.support M.nativeJets m
  exact ⟨C, hC, fun w hw hq1 => hb w hw.1 (abs_time_le_one hh hh1 hw.1 hq1) (hw.2.le.trans hq)⟩

theorem MeanData.angular_bound {h degree qbig : ℝ} (M : MeanData h degree)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hq : qbig ≤ ChartScales.Q M.firstBand) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m M.family.angularField w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^ (h * M.alpha - PhysicalMeanJetBounds.loss degree m) :=
            by
  obtain ⟨C, hC, hb⟩ := M.family.angularField_jet_bound hh hh1 M.lower_pos M.radii_lt M.band_four
    M.region_open M.region_covers M.smooth M.support M.nativeJets m
  exact ⟨C, hC, fun w hw hq1 => hb w hw.1 (abs_time_le_one hh hh1 hw.1 hq1) (hw.2.le.trans hq)⟩

section GainComparison

private theorem norm_bound_mono_loss {E : Type*} [NormedAddCommGroup E] {v : E}
    {C q g l₁ l₂ : ℝ} (hC : 0 ≤ C) (hq : 0 < q) (hq1 : q ≤ 1)
    (hl : l₁ ≤ l₂) (hv : ‖v‖ ≤ C * q ^ (g - l₁)) :
    ‖v‖ ≤ C * q ^ (g - l₂) :=
  hv.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hq hq1 (sub_le_sub_left hl g)) hC)

variable {h g delta : ℝ} {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {I K : Type*}

theorem WaveData.vector_bound_with_gain (W : WaveData h D I K (Fin 3))
    (hh : 0 < h) (hh1 : h < 1 / 2) (hg : g ≤ h * W.alpha + W.shift + delta) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ PhysicalWaveSum.preterminal,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m W.vector w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^
        (g - (PhysicalGraphBounds.waveLoss h m + delta)) := by
  obtain ⟨C, hC, hb⟩ := W.vector_bound hh hh1 m
  refine ⟨C, hC, fun w hw hq => (hb w hw hq).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.rpow_le_rpow_of_exponent_ge (PhysicalWaveSum.physicalQ_pos hh hh1 hw) hq
  unfold PhysicalClassBounds.physicalLoss
  linarith

theorem WaveData.pressure_bound_with_gain (W : WaveData h D I K Unit)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hg : g ≤ h * W.alpha + W.shift + delta) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ PhysicalWaveSum.preterminal,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m W.pressure w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^
        (g - (PhysicalGraphBounds.waveLoss h m + delta)) := by
  obtain ⟨C, hC, hb⟩ := W.pressure_bound hh hh1 m
  refine ⟨C, hC, fun w hw hq => (hb w hw hq).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.rpow_le_rpow_of_exponent_ge (PhysicalWaveSum.physicalQ_pos hh hh1 hw) hq
  unfold PhysicalClassBounds.physicalLoss
  linarith

theorem MeanData.field_bound_with_gain {degree qbig : ℝ} (M : MeanData h degree)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hq : qbig ≤ ChartScales.Q M.firstBand)
    (hg : g ≤ h * M.alpha + delta) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m M.family.field w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^
        (g - (PhysicalMeanJetBounds.loss degree m + delta)) := by
  obtain ⟨C, hC, hb⟩ := M.field_bound hh hh1 hq m
  refine ⟨C, hC, fun w hw hq1 => (hb w hw hq1).trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge (PhysicalWaveSum.physicalQ_pos hh hh1 hw.1) hq1
      (by linarith)) hC

theorem MeanData.angular_bound_with_gain {degree qbig : ℝ} (M : MeanData h degree)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hq : qbig ≤ ChartScales.Q M.firstBand)
    (hg : g ≤ h * M.alpha + delta) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m M.family.angularField w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^
        (g - (PhysicalMeanJetBounds.loss degree m + delta)) := by
  obtain ⟨C, hC, hb⟩ := M.angular_bound hh hh1 hq m
  refine ⟨C, hC, fun w hw hq1 => (hb w hw hq1).trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge (PhysicalWaveSum.physicalQ_pos hh hh1 hw.1) hq1
      (by linarith)) hC

end GainComparison

section Assembly

variable {h : ℝ} {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {I K : Type*}

/-- Potential increment, defined pointwise by `W.vector w + M.family.angularField w`. -/
noncomputable def potentialIncrement (W : WaveData h D I K (Fin 3))
    (M : MeanData h (CoordinateAlgebra.A h - 1 / 2)) : VelocityField :=
  fun w => W.vector w + M.family.angularField w

/-- Pressure increment, defined pointwise by `W.pressure w + M.family.field w`. -/
noncomputable def pressureIncrement (W : WaveData h D I K Unit)
    (M : MeanData h (2 * CoordinateAlgebra.A h)) : PressureField :=
  fun w => W.pressure w + M.family.field w

/-- These losses depend only on fixed physical parameters and jet order.
The five offsets are fixed once for the whole stage sequence. -/
noncomputable def potentialLoss (h waveOffset meanOffset : ℝ) (m : ℕ) : ℝ :=
  max (PhysicalGraphBounds.waveLoss h m + waveOffset)
    (PhysicalMeanJetBounds.loss (CoordinateAlgebra.A h - 1 / 2) m + meanOffset)

/-- Direct loss, given by `PhysicalMeanJetBounds.loss (CoordinateAlgebra.A h) m + meanOffset`. -/
noncomputable def directLoss (h meanOffset : ℝ) (m : ℕ) : ℝ :=
  PhysicalMeanJetBounds.loss (CoordinateAlgebra.A h) m + meanOffset

/-- Pressure loss, given by `max (PhysicalGraphBounds.waveLoss h m + waveOffset)
(PhysicalMeanJetBounds.loss (2 * CoordinateAlgebra.A h) m + meanOffset)`. -/
noncomputable def pressureLoss (h waveOffset meanOffset : ℝ) (m : ℕ) : ℝ :=
  max (PhysicalGraphBounds.waveLoss h m + waveOffset)
    (PhysicalMeanJetBounds.loss (2 * CoordinateAlgebra.A h) m + meanOffset)

private theorem norm_add_jet_le {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {f g : E → V} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => f y + g y) x‖ ≤
      ‖iteratedFDeriv ℝ m f x‖ + ‖iteratedFDeriv ℝ m g x‖ := by
  rw [fun_iteratedFDeriv_add_apply (hf.of_le (nat_le_infty m)) (hg.of_le (nat_le_infty m))]
  exact norm_add_le _ _

theorem potentialIncrement_smooth {qbig : ℝ} (W : WaveData h D I K (Fin 3))
    (M : MeanData h (CoordinateAlgebra.A h - 1 / 2)) (hh : 0 < h) (hh1 : h < 1 / 2)
    (hq : qbig ≤ ChartScales.Q M.firstBand) :
    ContDiffOn ℝ ∞ (potentialIncrement W M) (CutStageEstimates.physicalSublevel h qbig) :=
  ((W.vector_smooth hh hh1).mono inter_subset_left).add (M.angular_smooth hh hh1 hq)

theorem pressureIncrement_smooth {qbig : ℝ} (W : WaveData h D I K Unit)
    (M : MeanData h (2 * CoordinateAlgebra.A h)) (hh : 0 < h) (hh1 : h < 1 / 2)
    (hq : qbig ≤ ChartScales.Q M.firstBand) :
    ContDiffOn ℝ ∞ (pressureIncrement W M) (CutStageEstimates.physicalSublevel h qbig) :=
  ((W.pressure_smooth hh hh1).mono inter_subset_left).add (M.field_smooth hh hh1 hq)

theorem potentialIncrement_bound {qbig g waveOffset meanOffset : ℝ}
    (W : WaveData h D I K (Fin 3)) (M : MeanData h (CoordinateAlgebra.A h - 1 / 2))
    (hh : 0 < h) (hh1 : h < 1 / 2) (hq : qbig ≤ ChartScales.Q M.firstBand)
    (hwave : g ≤ h * W.alpha + W.shift + waveOffset)
    (hmean : g ≤ h * M.alpha + meanOffset) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (potentialIncrement W M) w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^ (g - potentialLoss h waveOffset meanOffset m) := by
  obtain ⟨C₁, hC₁, h₁⟩ := W.vector_bound_with_gain hh hh1 hwave m
  obtain ⟨C₂, hC₂, h₂⟩ := M.angular_bound_with_gain hh hh1 hq hmean m
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, fun w hw hq1 => ?_⟩
  have hpos := PhysicalWaveSum.physicalQ_pos hh hh1 hw.1
  have ha := norm_bound_mono_loss (l₂ := potentialLoss h waveOffset meanOffset m)
    hC₁ hpos hq1 (le_max_left _ _) (h₁ w hw.1 hq1)
  have hb := norm_bound_mono_loss (l₂ := potentialLoss h waveOffset meanOffset m)
    hC₂ hpos hq1 (le_max_right _ _) (h₂ w hw hq1)
  have hsa := (W.vector_smooth hh hh1).contDiffAt (PhysicalWaveSum.preterminal_open.mem_nhds hw.1)
  have hsb := (M.angular_smooth hh hh1 hq).contDiffAt
    ((CutStageEstimates.physicalSublevel_open hh hh1 qbig).mem_nhds hw)
  exact (norm_add_jet_le hsa hsb m).trans ((add_le_add ha hb).trans_eq (by ring))

theorem pressureIncrement_bound {qbig g waveOffset meanOffset : ℝ}
    (W : WaveData h D I K Unit) (M : MeanData h (2 * CoordinateAlgebra.A h))
    (hh : 0 < h) (hh1 : h < 1 / 2) (hq : qbig ≤ ChartScales.Q M.firstBand)
    (hwave : g ≤ h * W.alpha + W.shift + waveOffset)
    (hmean : g ≤ h * M.alpha + meanOffset) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (pressureIncrement W M) w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^ (g - pressureLoss h waveOffset meanOffset m) := by
  obtain ⟨C₁, hC₁, h₁⟩ := W.pressure_bound_with_gain hh hh1 hwave m
  obtain ⟨C₂, hC₂, h₂⟩ := M.field_bound_with_gain hh hh1 hq hmean m
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, fun w hw hq1 => ?_⟩
  have hpos := PhysicalWaveSum.physicalQ_pos hh hh1 hw.1
  have ha := norm_bound_mono_loss (l₂ := pressureLoss h waveOffset meanOffset m)
    hC₁ hpos hq1 (le_max_left _ _) (h₁ w hw.1 hq1)
  have hb := norm_bound_mono_loss (l₂ := pressureLoss h waveOffset meanOffset m)
    hC₂ hpos hq1 (le_max_right _ _) (h₂ w hw hq1)
  have hsa := (W.pressure_smooth hh hh1).contDiffAt (PhysicalWaveSum.preterminal_open.mem_nhds hw.1)
  have hsb := (M.field_smooth hh hh1 hq).contDiffAt
    ((CutStageEstimates.physicalSublevel_open hh hh1 qbig).mem_nhds hw)
  exact (norm_add_jet_le hsa hsb m).trans ((add_le_add ha hb).trans_eq (by ring))

end Assembly

section InitializedStages

variable {X V : Type*} [Add V]

/-- The zeroth increment is the base plus finite initialization. Positive
indices keep the supplied correction increments exactly. -/
noncomputable def addBaseAtZero (base : X → V) (increments : ℕ → X → V) (j : ℕ) (x : X) : V :=
  if j = 0 then base x + increments 0 x else increments j x

@[simp] theorem addBaseAtZero_zero (base : X → V) (increments : ℕ → X → V) :
    addBaseAtZero base increments 0 = fun x => base x + increments 0 x := by
  funext x
  simp [addBaseAtZero]

theorem addBaseAtZero_pos (base : X → V) (increments : ℕ → X → V) {j : ℕ} (hj : 1 ≤ j) :
    addBaseAtZero base increments j = increments j := by
  funext x
  simp only [addBaseAtZero, ite_eq_right (by omega : j ≠ 0)]

end InitializedStages

section Sequences

variable {h qbig : ℝ} {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {I K : Type*}

/-- Potential stages, given by `addBaseAtZero base (fun j => potentialIncrement (W j) (M j))`. -/
noncomputable def potentialStages (base : VelocityField)
    (W : ℕ → WaveData h D I K (Fin 3))
    (M : ℕ → MeanData h (CoordinateAlgebra.A h - 1 / 2)) : ℕ → VelocityField :=
  addBaseAtZero base (fun j => potentialIncrement (W j) (M j))

/-- Direct stages, defined pointwise by `(M j).family.angularField`. -/
noncomputable def directStages (M : ℕ → MeanData h (CoordinateAlgebra.A h)) : ℕ → VelocityField :=
  fun j => (M j).family.angularField

/-- Pressure stages, given by `addBaseAtZero base (fun j => pressureIncrement (W j) (M j))`. -/
noncomputable def pressureStages (base : PressureField)
    (W : ℕ → WaveData h D I K Unit)
    (M : ℕ → MeanData h (2 * CoordinateAlgebra.A h)) : ℕ → PressureField :=
  addBaseAtZero base (fun j => pressureIncrement (W j) (M j))

theorem potentialStages_zero (base : VelocityField)
    (W : ℕ → WaveData h D I K (Fin 3)) (M : ℕ → MeanData h (CoordinateAlgebra.A h - 1 / 2)) :
    potentialStages base W M 0 = fun w => base w + ((W 0).vector w + (M 0).family.angularField w) :=
  addBaseAtZero_zero _ _

theorem pressureStages_zero (base : PressureField)
    (W : ℕ → WaveData h D I K Unit) (M : ℕ → MeanData h (2 * CoordinateAlgebra.A h)) :
    pressureStages base W M 0 = fun w => base w + ((W 0).pressure w + (M 0).family.field w) :=
  addBaseAtZero_zero _ _

theorem potentialStages_smooth (base : VelocityField)
    (W : ℕ → WaveData h D I K (Fin 3)) (M : ℕ → MeanData h (CoordinateAlgebra.A h - 1 / 2))
    (hh : 0 < h) (hh1 : h < 1 / 2)
    (hbase : ContDiffOn ℝ ∞ base (CutStageEstimates.physicalSublevel h qbig))
    (hq : ∀ j, qbig ≤ ChartScales.Q (M j).firstBand) :
    ∀ j, ContDiffOn ℝ ∞ (potentialStages base W M j) (CutStageEstimates.physicalSublevel h qbig) :=
        by
  intro j
  have hs := potentialIncrement_smooth (W j) (M j) hh hh1 (hq j)
  by_cases hj : j = 0
  · subst j
    exact hbase.add hs
  · rw [potentialStages, addBaseAtZero_pos _ _ (by omega : 1 ≤ j)]
    exact hs

theorem pressureStages_smooth (base : PressureField)
    (W : ℕ → WaveData h D I K Unit) (M : ℕ → MeanData h (2 * CoordinateAlgebra.A h))
    (hh : 0 < h) (hh1 : h < 1 / 2)
    (hbase : ContDiffOn ℝ ∞ base (CutStageEstimates.physicalSublevel h qbig))
    (hq : ∀ j, qbig ≤ ChartScales.Q (M j).firstBand) :
    ∀ j, ContDiffOn ℝ ∞ (pressureStages base W M j) (CutStageEstimates.physicalSublevel h qbig) :=
        by
  intro j
  have hs := pressureIncrement_smooth (W j) (M j) hh hh1 (hq j)
  by_cases hj : j = 0
  · subst j
    exact hbase.add hs
  · rw [pressureStages, addBaseAtZero_pos _ _ (by omega : 1 ≤ j)]
    exact hs

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem directStages_smooth (M : ℕ → MeanData h (CoordinateAlgebra.A h))
    (hh : 0 < h) (hh1 : h < 1 / 2) (hq : ∀ j, qbig ≤ ChartScales.Q (M j).firstBand) :
    ∀ j, ContDiffOn ℝ ∞ (directStages M j) (CutStageEstimates.physicalSublevel h qbig) :=
  fun j => (M j).angular_smooth hh hh1 (hq j)

private theorem exists_raw_constants {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : ℕ → SpaceTime → V} {g L : ℕ → ℝ}
    (hb : ∀ j, 1 ≤ j → ∀ m, ∃ C : ℝ, 0 ≤ C ∧
      ∀ w ∈ CutStageEstimates.physicalSublevel h qbig, PhysicalWaveSum.physicalQ h w ≤ 1 →
        ‖iteratedFDeriv ℝ m (F j) w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^ (g j - L m)) :
    ∃ C : ℕ → ℕ → ℝ, (∀ j m, 0 ≤ C j m) ∧
      CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) F g L C (fun _ _ => 0)
        (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig) := by
  have he : ∀ j m, ∃ C : ℝ, 0 ≤ C ∧ (1 ≤ j →
      ∀ w ∈ CutStageEstimates.physicalSublevel h qbig, PhysicalWaveSum.physicalQ h w ≤ 1 →
        ‖iteratedFDeriv ℝ m (F j) w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^ (g j - L m)) := by
    intro j m
    by_cases hj : 1 ≤ j
    · obtain ⟨C, hC, hc⟩ := hb j hj m
      exact ⟨C, hC, fun _ => hc⟩
    · exact ⟨0, le_rfl, fun hj' => False.elim (hj hj')⟩
  choose C hC hb using he
  refine ⟨C, hC, fun j hj m w hw hq => ?_⟩
  simpa only [Real.rpow_zero, mul_one] using hb j m hj w hw.2 hq

/-- All potential-stage raw estimates are derived from the actual wave
copies and azimuthal stream representations. -/
theorem potentialStages_raw (base : VelocityField)
    (W : ℕ → WaveData h D I K (Fin 3)) (M : ℕ → MeanData h (CoordinateAlgebra.A h - 1 / 2))
    (hh : 0 < h) (hh1 : h < 1 / 2) (hq : ∀ j, qbig ≤ ChartScales.Q (M j).firstBand)
    (g : ℕ → ℝ) (waveOffset meanOffset : ℝ)
    (hwave : ∀ j, 1 ≤ j → g j ≤ h * (W j).alpha + (W j).shift + waveOffset)
    (hmean : ∀ j, 1 ≤ j → g j ≤ h * (M j).alpha + meanOffset) :
    ∃ C : ℕ → ℕ → ℝ, (∀ j m, 0 ≤ C j m) ∧
      CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) (potentialStages base W M) g
        (potentialLoss h waveOffset meanOffset) C (fun _ _ => 0)
        (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig) := by
  apply exists_raw_constants
  intro j hj m
  simpa only [potentialStages, addBaseAtZero_pos _ _ hj] using
    potentialIncrement_bound (W j) (M j) hh hh1 (hq j) (hwave j hj) (hmean j hj) m

theorem pressureStages_raw (base : PressureField)
    (W : ℕ → WaveData h D I K Unit) (M : ℕ → MeanData h (2 * CoordinateAlgebra.A h))
    (hh : 0 < h) (hh1 : h < 1 / 2) (hq : ∀ j, qbig ≤ ChartScales.Q (M j).firstBand)
    (g : ℕ → ℝ) (waveOffset meanOffset : ℝ)
    (hwave : ∀ j, 1 ≤ j → g j ≤ h * (W j).alpha + (W j).shift + waveOffset)
    (hmean : ∀ j, 1 ≤ j → g j ≤ h * (M j).alpha + meanOffset) :
    ∃ C : ℕ → ℕ → ℝ, (∀ j m, 0 ≤ C j m) ∧
      CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) (pressureStages base W M) g
        (pressureLoss h waveOffset meanOffset) C (fun _ _ => 0)
        (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig) := by
  apply exists_raw_constants
  intro j hj m
  simpa only [pressureStages, addBaseAtZero_pos _ _ hj] using
    pressureIncrement_bound (W j) (M j) hh hh1 (hq j) (hwave j hj) (hmean j hj) m

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem directStages_raw (M : ℕ → MeanData h (CoordinateAlgebra.A h))
    (hh : 0 < h) (hh1 : h < 1 / 2) (hq : ∀ j, qbig ≤ ChartScales.Q (M j).firstBand)
    (g : ℕ → ℝ) (meanOffset : ℝ)
    (hmean : ∀ j, 1 ≤ j → g j ≤ h * (M j).alpha + meanOffset) :
    ∃ C : ℕ → ℕ → ℝ, (∀ j m, 0 ≤ C j m) ∧
      CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) (directStages M) g
        (directLoss h meanOffset) C (fun _ _ => 0)
        (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig) := by
  apply exists_raw_constants
  intro j hj m
  exact (M j).angular_bound_with_gain hh hh1 (hq j) (hmean j hj) m

end Sequences

section JointInputs

variable {h qbig : ℝ}
  {DA DP : Type} [NormedAddCommGroup DA] [NormedSpace ℝ DA]
  [NormedAddCommGroup DP] [NormedSpace ℝ DP] {IA KA IP KP : Type*}

/-- The six raw-stage inputs needed by the mixed diagonal construction,
derived together for one gain sequence. The losses contain only the fixed
five offsets and the derivative order. Initialization remains in stage zero.
No finite-residual estimate or choice of the gain sequence is hidden here. -/
theorem derived_stage_inputs (baseA : VelocityField) (baseP : PressureField)
    (WA : ℕ → WaveData h DA IA KA (Fin 3))
    (MA : ℕ → MeanData h (CoordinateAlgebra.A h - 1 / 2))
    (MB : ℕ → MeanData h (CoordinateAlgebra.A h))
    (WP : ℕ → WaveData h DP IP KP Unit)
    (MP : ℕ → MeanData h (2 * CoordinateAlgebra.A h))
    (hh : 0 < h) (hh1 : h < 1 / 2)
    (hbaseA : ContDiffOn ℝ ∞ baseA (CutStageEstimates.physicalSublevel h qbig))
    (hbaseP : ContDiffOn ℝ ∞ baseP (CutStageEstimates.physicalSublevel h qbig))
    (hqA : ∀ j, qbig ≤ ChartScales.Q (MA j).firstBand)
    (hqB : ∀ j, qbig ≤ ChartScales.Q (MB j).firstBand)
    (hqP : ∀ j, qbig ≤ ChartScales.Q (MP j).firstBand)
    (g : ℕ → ℝ) (deltaWA deltaMA deltaB deltaWP deltaMP : ℝ)
    (hWA : ∀ j, 1 ≤ j → g j ≤ h * (WA j).alpha + (WA j).shift + deltaWA)
    (hMA : ∀ j, 1 ≤ j → g j ≤ h * (MA j).alpha + deltaMA)
    (hMB : ∀ j, 1 ≤ j → g j ≤ h * (MB j).alpha + deltaB)
    (hWP : ∀ j, 1 ≤ j → g j ≤ h * (WP j).alpha + (WP j).shift + deltaWP)
    (hMP : ∀ j, 1 ≤ j → g j ≤ h * (MP j).alpha + deltaMP) :
    ∃ CA CB CP : ℕ → ℕ → ℝ,
      (∀ j, ContDiffOn ℝ ∞ (potentialStages baseA WA MA j)
        (CutStageEstimates.physicalSublevel h qbig)) ∧
      (∀ j, ContDiffOn ℝ ∞ (directStages MB j)
        (CutStageEstimates.physicalSublevel h qbig)) ∧
      (∀ j, ContDiffOn ℝ ∞ (pressureStages baseP WP MP j)
        (CutStageEstimates.physicalSublevel h qbig)) ∧
      CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h)
        (potentialStages baseA WA MA) g (potentialLoss h deltaWA deltaMA) CA (fun _ _ => 0)
        (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig) ∧
      CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h)
        (directStages MB) g (directLoss h deltaB) CB (fun _ _ => 0)
        (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig) ∧
      CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h)
        (pressureStages baseP WP MP) g (pressureLoss h deltaWP deltaMP) CP (fun _ _ => 0)
        (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig) := by
  obtain ⟨CA, _, hA⟩ := potentialStages_raw baseA WA MA hh hh1 hqA g deltaWA deltaMA hWA hMA
  obtain ⟨CB, _, hB⟩ := directStages_raw MB hh hh1 hqB g deltaB hMB
  obtain ⟨CP, _, hP⟩ := pressureStages_raw baseP WP MP hh hh1 hqP g deltaWP deltaMP hWP hMP
  exact ⟨CA, CB, CP, potentialStages_smooth baseA WA MA hh hh1 hbaseA hqA,
    directStages_smooth MB hh hh1 hqB,
    pressureStages_smooth baseP WP MP hh hh1 hbaseP hqP, hA, hB, hP⟩

end JointInputs

section RepresentationTransfer

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Actual field equality on the valid open physical domain identifies all
ambient derivatives. No regularity of either totalization outside the domain
is required. -/
theorem jets_eq_of_eqOn_open {f g : E → V} {U : Set E} (hU : IsOpen U)
    (he : EqOn f g U) {x : E} (hx : x ∈ U) (m : ℕ) :
    iteratedFDeriv ℝ m f x = iteratedFDeriv ℝ m g x := by
  have hg : f =ᶠ[𝓝 x] g := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact he hy
  exact (SolenoidalDiagonal.iteratedFDeriv_eventuallyEq hg m).self_of_nhds

/-- Transfer the proved raw estimates to a separately defined family by its
literal representation on the valid physical neighborhood. -/
theorem rawStageBounds_congr_on {F G : ℕ → E → V} {U S : Set E}
    {q : E → ℝ} {g L : ℕ → ℝ} {C p : ℕ → ℕ → ℝ}
    (hU : IsOpen U) (hSU : S ⊆ U) (he : ∀ j, EqOn (F j) (G j) U)
    (hb : CutStageEstimates.RawStageBounds q G g L C p S) :
    CutStageEstimates.RawStageBounds q F g L C p S := by
  intro j hj m x hx hq
  rw [jets_eq_of_eqOn_open hU (he j) (hSU hx) m]
  exact hb j hj m x hx hq

theorem stage_smooth_congr_on {F G : ℕ → E → V} {U : Set E}
    (he : ∀ j, EqOn (F j) (G j) U) (hs : ∀ j, ContDiffOn ℝ ∞ (G j) U) :
    ∀ j, ContDiffOn ℝ ∞ (F j) U := fun j => (hs j).congr (he j)

end RepresentationTransfer

section ActualBase

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {d : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness d)

theorem actual_potential_base_smooth (upper : ℝ) (bandFloor : ℕ) (qbig : ℝ) :
    ContDiffOn ℝ ∞ (TailGaugePotential.finalPotential H v upper bandFloor)
      (CutStageEstimates.physicalSublevel F.data.h qbig) :=
  (TailGaugePotential.finalPotential_smooth H v upper bandFloor).mono (fun _ hw => ⟨hw.1, mem_univ
      _⟩)

theorem actual_pressure_base_smooth (upper : ℝ) (bandFloor : ℕ) (qbig : ℝ) :
    ContDiffOn ℝ ∞ (FinalSlowBase.pressure H v upper bandFloor)
      (CutStageEstimates.physicalSublevel F.data.h qbig) :=
  (FinalSlowBase.pressure_smooth H v upper bandFloor).mono (fun _ hw => ⟨hw.1, mem_univ _⟩)

end ActualBase

end NavierStokes.PhysicalStageBounds
