/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.InitializedPhysicalBackground
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualIterationLedger
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualMeanPhysicalData
public import LeanPool.NavierStokesAndEuler.NavierStokes.MixedCandidateAssembly
import LeanPool.NavierStokesAndEuler.NavierStokes.LocalMeanPhysicalBounds

/-!
# Physical stage estimates from the actual native mean region

Mean families are supplied on the original normalized region `(1/2,2)`.
Only native smoothness, support, and class estimates are input. The
physical stage bounds and the initialized velocity estimate are derived.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ActualPhysicalStageBounds

open Set Function Filter ProblemStatement DiagonalResidual
open scoped Topology ContDiff BigOperators

/-- Region, given by `PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 2) 2`. -/
noncomputable def region (h : ℝ) : Set PhysicalGraphBounds.Plane :=
  PhysicalMeanDomain.normalizedSlowDomain (2 * h) (1 / 2) 2

theorem region_open {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2) : IsOpen (region h) :=
  PhysicalMeanDomain.normalizedSlowDomain_open (by linarith) (by linarith) _ _

/-- Native facts about an already constructed coherent mean family.
This record neither constructs a new physical field nor assumes physical
derivative bounds. -/
structure MeanInput (h degree : ℝ) where
  /-- First band of `MeanInput`, of type `ℕ`. -/
  firstBand : ℕ
  /-- Gap bound of `MeanInput`, of type `ℕ`. -/
  gapBound : ℕ
  /-- Lower radius of `MeanInput`, of type `ℝ`. -/
  lowerRadius : ℝ
  /-- Upper radius of `MeanInput`, of type `ℝ`. -/
  upperRadius : ℝ
  /-- Alpha of `MeanInput`, of type `ℝ`. -/
  alpha : ℝ
  /-- Family of `MeanInput`, of type `PhysicalMeanJetBounds.CoherentFamily h degree firstBand
  gapBound (region h) ℝ`. -/
  family : PhysicalMeanJetBounds.CoherentFamily h degree firstBand gapBound (region h) ℝ
  band_four : 4 ≤ firstBand
  lower_pos : 0 < lowerRadius
  radii_lt : lowerRadius < upperRadius
  smooth : ∀ n ≥ firstBand, ContDiffOn ℝ ∞ (family.native n)
    (PhysicalMeanDomain.slowDomain (region h))
  support : PhysicalMeanJetBounds.NativeSupport h lowerRadius upperRadius firstBand (region h)
      family.native
  jets : PhysicalMeanJetBounds.NativeJets firstBand (region h) (h * alpha) family.native

/-- Package the existing moving-field and native-class theorems without
changing the supplied coherent physical field. -/
noncomputable def MeanInput.ofMoving {h degree a b α : ℝ} {N Δ : ℕ}
    (R : LocalSignedRequest.SlowRegion (2 * h)) (hR : R.carrier = region h)
    (M : PhysicalMeanJetBounds.CoherentFamily h degree N Δ (region h) ℝ)
    (hN : 4 ≤ N) (ha : 0 < a) (hab : a < b)
    (hm : GaugeMomentBalances.MovingField R a b M.native)
    (hj : PhysicalMeanJetBounds.NativeJets N R.carrier (h * α) M.native) : MeanInput h degree where
  firstBand := N
  gapBound := Δ
  lowerRadius := a
  upperRadius := b
  alpha := α
  family := M
  band_four := hN
  lower_pos := ha
  radii_lt := hab
  smooth n _ := by simpa only [hR] using hm.smooth n
  support n _ := by
    have hs := hm.supported n
    simp only [hR] at hs
    exact hs
  jets := by simpa only [hR] using hj

theorem MeanInput.field_smooth {h degree qbig : ℝ} (M : MeanInput h degree)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hq : qbig ≤ ChartScales.Q M.firstBand) :
    ContDiffOn ℝ ∞ M.family.field (CutStageEstimates.physicalSublevel h qbig) :=
  LocalMeanPhysicalBounds.field_sublevel_smooth M.family hh hh1 M.lower_pos M.radii_lt
    (region_open hh hh1) (fun _ hx => hx) M.smooth M.support hq

theorem MeanInput.angular_smooth {h degree qbig : ℝ} (M : MeanInput h degree)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hq : qbig ≤ ChartScales.Q M.firstBand) :
    ContDiffOn ℝ ∞ M.family.angularField (CutStageEstimates.physicalSublevel h qbig) :=
  LocalMeanPhysicalBounds.angularField_sublevel_smooth M.family hh hh1 M.lower_pos M.radii_lt
    (region_open hh hh1) (fun _ hx => hx) M.smooth M.support hq

theorem MeanInput.field_bound {h degree qbig : ℝ} (M : MeanInput h degree)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hq : qbig ≤ ChartScales.Q M.firstBand) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m M.family.field w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^ (h * M.alpha - PhysicalMeanJetBounds.loss degree m) :=
  LocalMeanPhysicalBounds.field_sublevel_bound M.family hh hh1 M.lower_pos M.radii_lt M.band_four
    (region_open hh hh1) (fun _ hx => hx) M.smooth M.support M.jets hq m

theorem MeanInput.angular_bound {h degree qbig : ℝ} (M : MeanInput h degree)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hq : qbig ≤ ChartScales.Q M.firstBand) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m M.family.angularField w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^ (h * M.alpha - PhysicalMeanJetBounds.loss degree m) :=
  LocalMeanPhysicalBounds.angularField_sublevel_bound M.family hh hh1 M.lower_pos M.radii_lt
      M.band_four
    (region_open hh hh1) (fun _ hx => hx) M.smooth M.support M.jets hq m

theorem MeanInput.field_bound_with_gain {h degree qbig g delta : ℝ} (M : MeanInput h degree)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hq : qbig ≤ ChartScales.Q M.firstBand)
    (hg : g ≤ h * M.alpha + delta) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m M.family.field w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^ (g - (PhysicalMeanJetBounds.loss degree m + delta)) :=
            by
  obtain ⟨C, hC, hb⟩ := M.field_bound hh hh1 hq m
  refine ⟨C, hC, fun w hw hqw => (hb w hw hqw).trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge (PhysicalWaveSum.physicalQ_pos hh hh1 hw.1) hqw
      (by linarith)) hC

theorem MeanInput.angular_bound_with_gain {h degree qbig g delta : ℝ} (M : MeanInput h degree)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hq : qbig ≤ ChartScales.Q M.firstBand)
    (hg : g ≤ h * M.alpha + delta) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m M.family.angularField w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^ (g - (PhysicalMeanJetBounds.loss degree m + delta)) :=
            by
  obtain ⟨C, hC, hb⟩ := M.angular_bound hh hh1 hq m
  refine ⟨C, hC, fun w hw hqw => (hb w hw hqw).trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge (PhysicalWaveSum.physicalQ_pos hh hh1 hw.1) hqw
      (by linarith)) hC

section JetAlgebra

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {h qbig : ℝ} {f g : SpaceTime → V} {m : ℕ} {r s : ℝ}

theorem weaken_bound (hh : 0 < h) (hh1 : h < 1 / 2) (hsr : s ≤ r)
    (hb : ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m f w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m f w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^ s := by
  obtain ⟨C, hC, hb⟩ := hb
  exact ⟨C, hC, fun w hw hqw => (hb w hw hqw).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge
      (PhysicalWaveSum.physicalQ_pos hh hh1 hw.1) hqw hsr) hC)⟩

theorem add_bounds (hh : 0 < h) (hh1 : h < 1 / 2)
    (hf : ContDiffOn ℝ ∞ f (CutStageEstimates.physicalSublevel h qbig))
    (hg : ContDiffOn ℝ ∞ g (CutStageEstimates.physicalSublevel h qbig))
    (hfb : ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m f w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^ r)
    (hgb : ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m g w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (fun z => f z + g z) w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^ r := by
  obtain ⟨A, hA, hfa⟩ := hfb
  obtain ⟨B, hB, hgb⟩ := hgb
  refine ⟨A + B, add_nonneg hA hB, fun w hw hqw => ?_⟩
  exact (ResidualStability.norm_jet_add_le
    (CutStageEstimates.physicalSublevel_open hh hh1 qbig) hf hg hw m).trans
    ((add_le_add (hfa w hw hqw) (hgb w hw hqw)).trans_eq (by ring))

end JetAlgebra

section Increments

variable {h : ℝ}
  {DP DS : Type} [NormedAddCommGroup DP] [NormedSpace ℝ DP]
  [NormedAddCommGroup DS] [NormedSpace ℝ DS] {IP KP IS KS : Type*}

/-- The four actual potential contributions of one cycle. -/
noncomputable def potentialIncrement
    (WP : PhysicalStageBounds.WaveData h DP IP KP (Fin 3))
    (WS : PhysicalStageBounds.WaveData h DS IS KS (Fin 3))
    (MT MR : MeanInput h (CoordinateAlgebra.A h - 1 / 2)) : VelocityField :=
  fun w => WP.vector w + WS.vector w + MT.family.angularField w + MR.family.angularField w

/-- Pressure increment, defined pointwise by `WP.pressure w + WS.pressure w + MP.family.field
w`. -/
noncomputable def pressureIncrement
    (WP : PhysicalStageBounds.WaveData h DP IP KP Unit)
    (WS : PhysicalStageBounds.WaveData h DS IS KS Unit)
    (MP : MeanInput h (2 * CoordinateAlgebra.A h)) : PressureField :=
  fun w => WP.pressure w + WS.pressure w + MP.family.field w

theorem potentialIncrement_smooth
    (WP : PhysicalStageBounds.WaveData h DP IP KP (Fin 3))
    (WS : PhysicalStageBounds.WaveData h DS IS KS (Fin 3))
    (MT MR : MeanInput h (CoordinateAlgebra.A h - 1 / 2))
    (hh : 0 < h) (hh1 : h < 1 / 2) {qbig : ℝ}
    (hqT : qbig ≤ ChartScales.Q MT.firstBand) (hqR : qbig ≤ ChartScales.Q MR.firstBand) :
    ContDiffOn ℝ ∞ (potentialIncrement WP WS MT MR) (CutStageEstimates.physicalSublevel h qbig) :=
  ((((WP.vector_smooth hh hh1).mono inter_subset_left).add
    ((WS.vector_smooth hh hh1).mono inter_subset_left)).add
      (MT.angular_smooth hh hh1 hqT)).add (MR.angular_smooth hh hh1 hqR)

theorem pressureIncrement_smooth
    (WP : PhysicalStageBounds.WaveData h DP IP KP Unit)
    (WS : PhysicalStageBounds.WaveData h DS IS KS Unit)
    (MP : MeanInput h (2 * CoordinateAlgebra.A h))
    (hh : 0 < h) (hh1 : h < 1 / 2) {qbig : ℝ} (hq : qbig ≤ ChartScales.Q MP.firstBand) :
    ContDiffOn ℝ ∞ (pressureIncrement WP WS MP) (CutStageEstimates.physicalSublevel h qbig) :=
  (((WP.pressure_smooth hh hh1).mono inter_subset_left).add
    ((WS.pressure_smooth hh hh1).mono inter_subset_left)).add (MP.field_smooth hh hh1 hq)

theorem potentialIncrement_bound
    (WP : PhysicalStageBounds.WaveData h DP IP KP (Fin 3))
    (WS : PhysicalStageBounds.WaveData h DS IS KS (Fin 3))
    (MT MR : MeanInput h (CoordinateAlgebra.A h - 1 / 2))
    (hh : 0 < h) (hh1 : h < 1 / 2) {qbig g dw dm : ℝ}
    (hqT : qbig ≤ ChartScales.Q MT.firstBand) (hqR : qbig ≤ ChartScales.Q MR.firstBand)
    (hWP : g ≤ h * WP.alpha + WP.shift + dw) (hWS : g ≤ h * WS.alpha + WS.shift + dw)
    (hMT : g ≤ h * MT.alpha + dm) (hMR : g ≤ h * MR.alpha + dm) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (potentialIncrement WP WS MT MR) w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^ (g - PhysicalStageBounds.potentialLoss h dw dm m) := by
  have hp0 := WP.vector_bound_with_gain hh hh1 hWP m
  have hs0 := WS.vector_bound_with_gain hh hh1 hWS m
  have hp := weaken_bound (qbig := qbig) (s := g - PhysicalStageBounds.potentialLoss h dw dm m) hh
      hh1
    (sub_le_sub_left (le_max_left _ _) g) (by
      obtain ⟨C, hC, hb⟩ := hp0
      exact ⟨C, hC, fun w hw hqw => hb w hw.1 hqw⟩)
  have hs := weaken_bound (qbig := qbig) (s := g - PhysicalStageBounds.potentialLoss h dw dm m) hh
      hh1
    (sub_le_sub_left (le_max_left _ _) g) (by
      obtain ⟨C, hC, hb⟩ := hs0
      exact ⟨C, hC, fun w hw hqw => hb w hw.1 hqw⟩)
  have ht := weaken_bound (s := g - PhysicalStageBounds.potentialLoss h dw dm m)
    hh hh1 (sub_le_sub_left (le_max_right _ _) g)
    (MT.angular_bound_with_gain hh hh1 hqT hMT m)
  have hr := weaken_bound (s := g - PhysicalStageBounds.potentialLoss h dw dm m)
    hh hh1 (sub_le_sub_left (le_max_right _ _) g)
    (MR.angular_bound_with_gain hh hh1 hqR hMR m)
  have sp : ContDiffOn ℝ ∞ WP.vector (CutStageEstimates.physicalSublevel h qbig) :=
    (WP.vector_smooth hh hh1).mono inter_subset_left
  have ss : ContDiffOn ℝ ∞ WS.vector (CutStageEstimates.physicalSublevel h qbig) :=
    (WS.vector_smooth hh hh1).mono inter_subset_left
  have st := MT.angular_smooth hh hh1 hqT
  exact add_bounds hh hh1 ((sp.add ss).add st) (MR.angular_smooth hh hh1 hqR)
    (add_bounds hh hh1 (sp.add ss) st (add_bounds hh hh1 sp ss hp hs) ht) hr

theorem pressureIncrement_bound
    (WP : PhysicalStageBounds.WaveData h DP IP KP Unit)
    (WS : PhysicalStageBounds.WaveData h DS IS KS Unit)
    (MP : MeanInput h (2 * CoordinateAlgebra.A h))
    (hh : 0 < h) (hh1 : h < 1 / 2) {qbig g dw dm : ℝ}
    (hq : qbig ≤ ChartScales.Q MP.firstBand)
    (hWP : g ≤ h * WP.alpha + WP.shift + dw) (hWS : g ≤ h * WS.alpha + WS.shift + dw)
    (hMP : g ≤ h * MP.alpha + dm) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (pressureIncrement WP WS MP) w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^ (g - PhysicalStageBounds.pressureLoss h dw dm m) := by
  have hp0 := WP.pressure_bound_with_gain hh hh1 hWP m
  have hs0 := WS.pressure_bound_with_gain hh hh1 hWS m
  have hp := weaken_bound (qbig := qbig) (s := g - PhysicalStageBounds.pressureLoss h dw dm m) hh
      hh1
    (sub_le_sub_left (le_max_left _ _) g) (by
      obtain ⟨C, hC, hb⟩ := hp0
      exact ⟨C, hC, fun w hw hqw => hb w hw.1 hqw⟩)
  have hs := weaken_bound (qbig := qbig) (s := g - PhysicalStageBounds.pressureLoss h dw dm m) hh
      hh1
    (sub_le_sub_left (le_max_left _ _) g) (by
      obtain ⟨C, hC, hb⟩ := hs0
      exact ⟨C, hC, fun w hw hqw => hb w hw.1 hqw⟩)
  have hm := weaken_bound (s := g - PhysicalStageBounds.pressureLoss h dw dm m)
    hh hh1 (sub_le_sub_left (le_max_right _ _) g)
    (MP.field_bound_with_gain hh hh1 hq hMP m)
  have sp : ContDiffOn ℝ ∞ WP.pressure (CutStageEstimates.physicalSublevel h qbig) :=
    (WP.pressure_smooth hh hh1).mono inter_subset_left
  have ss : ContDiffOn ℝ ∞ WS.pressure (CutStageEstimates.physicalSublevel h qbig) :=
    (WS.pressure_smooth hh hh1).mono inter_subset_left
  exact add_bounds hh hh1 (sp.add ss) (MP.field_smooth hh hh1 hq)
    (add_bounds hh hh1 sp ss hp hs) hm

end Increments

/-! ## Positive correction stages and the exact ledger gain -/

/-- Cycle inputs data, collecting `particularPotential`, `signedPotential`,
`particularPressure`, `signedPressure`, `temporal`, `rank` and their compatibility
conditions. -/
structure CycleInputs (h : ℝ) (DP : Type) [NormedAddCommGroup DP] [NormedSpace ℝ DP]
    (IP KP : Type*) (DS : Type) [NormedAddCommGroup DS] [NormedSpace ℝ DS] (IS KS : Type*) where
  /-- Particular potential of `CycleInputs`, of type `ℕ → PhysicalStageBounds.WaveData h DP IP
  KP (Fin 3)`. -/
  particularPotential : ℕ → PhysicalStageBounds.WaveData h DP IP KP (Fin 3)
  /-- Signed potential of `CycleInputs`, of type `ℕ → PhysicalStageBounds.WaveData h DS IS KS
  (Fin 3)`. -/
  signedPotential : ℕ → PhysicalStageBounds.WaveData h DS IS KS (Fin 3)
  /-- Particular pressure of `CycleInputs`, of type `ℕ → PhysicalStageBounds.WaveData h DP IP KP
  Unit`. -/
  particularPressure : ℕ → PhysicalStageBounds.WaveData h DP IP KP Unit
  /-- Signed pressure of `CycleInputs`, of type `ℕ → PhysicalStageBounds.WaveData h DS IS KS
  Unit`. -/
  signedPressure : ℕ → PhysicalStageBounds.WaveData h DS IS KS Unit
  /-- Temporal of `CycleInputs`, of type `ℕ → MeanInput h (CoordinateAlgebra.A h - 1 / 2)`. -/
  temporal : ℕ → MeanInput h (CoordinateAlgebra.A h - 1 / 2)
  /-- Rank of `CycleInputs`, of type `ℕ → MeanInput h (CoordinateAlgebra.A h - 1 / 2)`. -/
  rank : ℕ → MeanInput h (CoordinateAlgebra.A h - 1 / 2)
  /-- Angular of `CycleInputs`, of type `ℕ → MeanInput h (CoordinateAlgebra.A h)`. -/
  angular : ℕ → MeanInput h (CoordinateAlgebra.A h)
  /-- Pressure field of `CycleInputs`, of type `ℕ → MeanInput h (2 * CoordinateAlgebra.A h)`. -/
  pressure : ℕ → MeanInput h (2 * CoordinateAlgebra.A h)

namespace CycleInputs

variable {h : ℝ}
  {DP DS : Type} [NormedAddCommGroup DP] [NormedSpace ℝ DP]
  [NormedAddCommGroup DS] [NormedSpace ℝ DS] {IP KP IS KS : Type*}
  (D : CycleInputs h DP IP KP DS IS KS)

/-- Potential, given by `potentialIncrement (D.particularPotential k) (D.signedPotential k)
(D.temporal k) (D.rank k)`. -/
noncomputable def potential (k : ℕ) : VelocityField :=
  potentialIncrement (D.particularPotential k) (D.signedPotential k) (D.temporal k) (D.rank k)

/-- Direct, given by `(D.angular k).family.angularField`. -/
noncomputable def direct (k : ℕ) : VelocityField := (D.angular k).family.angularField

/-- Pressure field, given by `pressureIncrement (D.particularPressure k) (D.signedPressure k)
(D.pressure k)`. -/
noncomputable def pressureField (k : ℕ) : PressureField :=
  pressureIncrement (D.particularPressure k) (D.signedPressure k) (D.pressure k)

/-- Cycle `k` contributes physical stage `k+1`. These are native exponent
and chart-degree comparisons, not physical estimates. -/
structure Metadata (κ : ℝ) : Prop where
  particularPotential : ∀ k, ActualIterationLedger.waveNative κ (k + 1) ≤ (D.particularPotential
      k).alpha
  particularPotentialShift : ∀ k, -h ≤ (D.particularPotential k).shift
  signedPotential : ∀ k, ActualIterationLedger.waveNative κ (k + 1) ≤ (D.signedPotential k).alpha
  signedPotentialShift : ∀ k, -h ≤ (D.signedPotential k).shift
  temporal : ∀ k, ActualIterationLedger.meanNative κ (k + 1) ≤ (D.temporal k).alpha
  rank : ∀ k, ActualIterationLedger.meanNative κ (k + 1) ≤ (D.rank k).alpha
  angular : ∀ k, ActualIterationLedger.meanNative κ (k + 1) ≤ (D.angular k).alpha
  particularPressure : ∀ k, ActualIterationLedger.wavePressureNative κ (k + 1) ≤
      (D.particularPressure k).alpha
  particularPressureShift : ∀ k, -(2 * CoordinateAlgebra.A h) ≤ (D.particularPressure k).shift
  signedPressure : ∀ k, ActualIterationLedger.wavePressureNative κ (k + 1) ≤ (D.signedPressure
      k).alpha
  signedPressureShift : ∀ k, -(2 * CoordinateAlgebra.A h) ≤ (D.signedPressure k).shift
  pressure : ∀ k, ActualIterationLedger.meanNative κ (k + 1) ≤ (D.pressure k).alpha

/-- Valid scale data, collecting `temporal`, `rank`, `angular`, `pressure`. -/
structure ValidScale (qbig : ℝ) : Prop where
  temporal : ∀ k, qbig ≤ ChartScales.Q (D.temporal k).firstBand
  rank : ∀ k, qbig ≤ ChartScales.Q (D.rank k).firstBand
  angular : ∀ k, qbig ≤ ChartScales.Q (D.angular k).firstBand
  pressure : ∀ k, qbig ≤ ChartScales.Q (D.pressure k).firstBand

end CycleInputs

private theorem potential_gain {h κ α s : ℝ} (hh : 0 ≤ h) (hκ : κ ≤ 1 / 100000)
    (k : ℕ) (hα : ActualIterationLedger.waveNative κ (k + 1) ≤ α) (hs : -h ≤ s) :
    ActualIterationLedger.gain h (k + 1) ≤ h * α + s + h := by
  have hg := ActualIterationLedger.gain_le_wave hh hκ (Nat.succ_pos k)
  have ha := mul_le_mul_of_nonneg_left hα hh
  linarith

private theorem pressure_gain {h κ α s : ℝ} (hh : 0 ≤ h) (hκ : κ ≤ 1 / 100000)
    (k : ℕ) (hα : ActualIterationLedger.wavePressureNative κ (k + 1) ≤ α)
    (hs : -(2 * CoordinateAlgebra.A h) ≤ s) :
    ActualIterationLedger.gain h (k + 1) ≤ h * α + s + 2 * CoordinateAlgebra.A h := by
  have hg := ActualIterationLedger.gain_le_wavePressure hh hκ (Nat.succ_pos k)
  have ha := mul_le_mul_of_nonneg_left hα hh
  linarith

private theorem mean_gain {h κ α : ℝ} (hh : 0 ≤ h) (hκ : κ ≤ 1 / 100000)
    (k : ℕ) (hα : ActualIterationLedger.meanNative κ (k + 1) ≤ α) :
    ActualIterationLedger.gain h (k + 1) ≤ h * α + 0 := by
  simpa using (ActualIterationLedger.gain_le_mean hh hκ (Nat.succ_pos k)).trans
    (mul_le_mul_of_nonneg_left hα hh)

namespace CycleInputs

variable {h κ qbig : ℝ}
  {DP DS : Type} [NormedAddCommGroup DP] [NormedSpace ℝ DP]
  [NormedAddCommGroup DS] [NormedSpace ℝ DS] {IP KP IS KS : Type*}
  (D : CycleInputs h DP IP KP DS IS KS)

theorem potential_bound (H : D.Metadata κ) (Q : D.ValidScale qbig)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hκ : κ ≤ 1 / 100000) (k m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (D.potential k) w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^
        (ActualIterationLedger.gain h (k + 1) - PhysicalStageBounds.potentialLoss h h 0 m) :=
  potentialIncrement_bound (D.particularPotential k) (D.signedPotential k) (D.temporal k) (D.rank k)
    hh hh1 (Q.temporal k) (Q.rank k)
    (potential_gain hh.le hκ k (H.particularPotential k) (H.particularPotentialShift k))
    (potential_gain hh.le hκ k (H.signedPotential k) (H.signedPotentialShift k))
    (mean_gain hh.le hκ k (H.temporal k)) (mean_gain hh.le hκ k (H.rank k)) m

theorem direct_bound (H : D.Metadata κ) (Q : D.ValidScale qbig)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hκ : κ ≤ 1 / 100000) (k m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (D.direct k) w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^
        (ActualIterationLedger.gain h (k + 1) - PhysicalStageBounds.directLoss h 0 m) :=
  (D.angular k).angular_bound_with_gain hh hh1 (Q.angular k) (mean_gain hh.le hκ k (H.angular k)) m

theorem pressure_bound (H : D.Metadata κ) (Q : D.ValidScale qbig)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hκ : κ ≤ 1 / 100000) (k m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (D.pressureField k) w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^
        (ActualIterationLedger.gain h (k + 1) - PhysicalStageBounds.pressureLoss h (2 *
            CoordinateAlgebra.A h) 0 m) :=
  pressureIncrement_bound (D.particularPressure k) (D.signedPressure k) (D.pressure k)
    hh hh1 (Q.pressure k)
    (pressure_gain hh.le hκ k (H.particularPressure k) (H.particularPressureShift k))
    (pressure_gain hh.le hκ k (H.signedPressure k) (H.signedPressureShift k))
    (mean_gain hh.le hκ k (H.pressure k)) m

theorem potential_smooth (Q : D.ValidScale qbig) (hh : 0 < h) (hh1 : h < 1 / 2) (k : ℕ) :
    ContDiffOn ℝ ∞ (D.potential k) (CutStageEstimates.physicalSublevel h qbig) :=
  potentialIncrement_smooth _ _ _ _ hh hh1 (Q.temporal k) (Q.rank k)

theorem direct_smooth (Q : D.ValidScale qbig) (hh : 0 < h) (hh1 : h < 1 / 2) (k : ℕ) :
    ContDiffOn ℝ ∞ (D.direct k) (CutStageEstimates.physicalSublevel h qbig) :=
  (D.angular k).angular_smooth hh hh1 (Q.angular k)

theorem pressure_smooth (Q : D.ValidScale qbig) (hh : 0 < h) (hh1 : h < 1 / 2) (k : ℕ) :
    ContDiffOn ℝ ∞ (D.pressureField k) (CutStageEstimates.physicalSublevel h qbig) :=
  pressureIncrement_smooth _ _ _ hh hh1 (Q.pressure k)

end CycleInputs

section RawTransfer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {h qbig : ℝ} {f g : SpaceTime → V} {m : ℕ} {r : ℝ}

theorem bound_congr (hh : 0 < h) (hh1 : h < 1 / 2)
    (he : EqOn f g (CutStageEstimates.physicalSublevel h qbig))
    (hb : ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m f w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m g w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^ r := by
  obtain ⟨C, hC, hb⟩ := hb
  refine ⟨C, hC, fun w hw hqw => ?_⟩
  rw [← ResidualStability.iteratedFDeriv_eqOn
    (CutStageEstimates.physicalSublevel_open hh hh1 qbig) he m hw]
  exact hb w hw hqw

theorem raw_of_positive_bounds {F : ℕ → SpaceTime → V} {gain L : ℕ → ℝ}
    (hb : ∀ k m, ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (F (k + 1)) w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^ (gain (k + 1) - L
          m)) :
    ∃ C : ℕ → ℕ → ℝ, (∀ j m, 0 ≤ C j m) ∧
      CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) F gain L C (fun _ _ => 0)
        (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig) := by
  classical
  choose C hC hb using hb
  refine ⟨fun j m => if j = 0 then 0 else C (j - 1) m, ?_, ?_⟩
  · intro j m
    dsimp only
    split_ifs
    · exact le_rfl
    · exact hC _ _
  · intro j hj m w hw hqw
    cases j with
    | zero => omega
    | succ k => simpa only [Nat.succ_ne_zero, ite_false, Nat.succ_sub_one,
        Real.rpow_zero, mul_one] using hb k m w hw.2 hqw

end RawTransfer

namespace CycleInputs

variable {h κ qbig : ℝ}
  {DP DS : Type} [NormedAddCommGroup DP] [NormedSpace ℝ DP]
  [NormedAddCommGroup DS] [NormedSpace ℝ DS] {IP KP IS KS : Type*}
  (D : CycleInputs h DP IP KP DS IS KS)

/-- Literal sequence identities transfer the derived estimates to the
actual potential/direct/pressure stages. Index zero is deliberately absent. -/
theorem represented_raw_bounds (H : D.Metadata κ) (Q : D.ValidScale qbig)
    (hh : 0 < h) (hh1 : h < 1 / 2) (hκ : κ ≤ 1 / 100000)
    (A B : ℕ → VelocityField) (P : ℕ → PressureField)
    (hA : ∀ k, EqOn (D.potential k) (A (k + 1)) (CutStageEstimates.physicalSublevel h qbig))
    (hB : ∀ k, EqOn (D.direct k) (B (k + 1)) (CutStageEstimates.physicalSublevel h qbig))
    (hP : ∀ k, EqOn (D.pressureField k) (P (k + 1)) (CutStageEstimates.physicalSublevel h qbig)) :
    ∃ CA CB CP : ℕ → ℕ → ℝ,
      (∀ j m, 0 ≤ CA j m ∧ 0 ≤ CB j m ∧ 0 ≤ CP j m) ∧
      CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) A (ActualIterationLedger.gain
          h)
        (PhysicalStageBounds.potentialLoss h h 0) CA (fun _ _ => 0)
        (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig) ∧
      CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) B (ActualIterationLedger.gain
          h)
        (PhysicalStageBounds.directLoss h 0) CB (fun _ _ => 0)
        (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig) ∧
      CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) P (ActualIterationLedger.gain
          h)
        (PhysicalStageBounds.pressureLoss h (2 * CoordinateAlgebra.A h) 0) CP (fun _ _ => 0)
        (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig) := by
  obtain ⟨CA, hCA, ha⟩ := raw_of_positive_bounds
    (fun k m => bound_congr hh hh1 (hA k) (D.potential_bound H Q hh hh1 hκ k m))
  obtain ⟨CB, hCB, hb⟩ := raw_of_positive_bounds
    (fun k m => bound_congr hh hh1 (hB k) (D.direct_bound H Q hh hh1 hκ k m))
  obtain ⟨CP, hCP, hp⟩ := raw_of_positive_bounds
    (fun k m => bound_congr hh hh1 (hP k) (D.pressure_bound H Q hh hh1 hκ k m))
  exact ⟨CA, CB, CP, fun j m => ⟨hCA j m, hCB j m, hCP j m⟩, ha, hb, hp⟩

end CycleInputs

/-! ## Initialization on the true native mean domain -/

open InitializedPhysicalBackground (seedPotentialLoss seedDirectLoss initialLoss)

section InitialIncrement

variable {h : ℝ} {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {I K : Type*}

/-- Initial increment, defined pointwise by `W.vector w + MT.family.angularField w +
MR.family.angularField w`. -/
noncomputable def initialIncrement (W : PhysicalStageBounds.WaveData h D I K (Fin 3))
    (MT MR : MeanInput h (CoordinateAlgebra.A h - 1 / 2)) : VelocityField :=
  fun w => W.vector w + MT.family.angularField w + MR.family.angularField w

theorem initialIncrement_smooth (W : PhysicalStageBounds.WaveData h D I K (Fin 3))
    (MT MR : MeanInput h (CoordinateAlgebra.A h - 1 / 2))
    (hh : 0 < h) (hh1 : h < 1 / 2) {qbig : ℝ}
    (hqT : qbig ≤ ChartScales.Q MT.firstBand) (hqR : qbig ≤ ChartScales.Q MR.firstBand) :
    ContDiffOn ℝ ∞ (initialIncrement W MT MR) (CutStageEstimates.physicalSublevel h qbig) :=
  (((W.vector_smooth hh hh1).mono inter_subset_left).add
    (MT.angular_smooth hh hh1 hqT)).add (MR.angular_smooth hh hh1 hqR)

theorem initialIncrement_bound (W : PhysicalStageBounds.WaveData h D I K (Fin 3))
    (MT MR : MeanInput h (CoordinateAlgebra.A h - 1 / 2))
    (hh : 0 < h) (hh1 : h < 1 / 2) {qbig : ℝ}
    (hqT : qbig ≤ ChartScales.Q MT.firstBand) (hqR : qbig ≤ ChartScales.Q MR.firstBand) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (initialIncrement W MT MR) w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^
          (-seedPotentialLoss h W.alpha W.shift (min MT.alpha MR.alpha) m) := by
  have htGain : 0 ≤ h * MT.alpha + -(h * min MT.alpha MR.alpha) := by
    have := mul_le_mul_of_nonneg_left (min_le_left MT.alpha MR.alpha) hh.le
    linarith
  have hrGain : 0 ≤ h * MR.alpha + -(h * min MT.alpha MR.alpha) := by
    have := mul_le_mul_of_nonneg_left (min_le_right MT.alpha MR.alpha) hh.le
    linarith
  have hp0 := W.vector_bound_with_gain (g := 0) (delta := -(h * W.alpha + W.shift))
    hh hh1 (by linarith) m
  have ht0 := MT.angular_bound_with_gain hh hh1 hqT htGain m
  have hr0 := MR.angular_bound_with_gain hh hh1 hqR hrGain m
  simp only [zero_sub] at hp0 ht0 hr0
  have hp := weaken_bound (qbig := qbig)
    (s := -seedPotentialLoss h W.alpha W.shift (min MT.alpha MR.alpha) m) hh hh1
    (neg_le_neg (le_max_left _ _)) (by
      obtain ⟨C, hC, hb⟩ := hp0
      exact ⟨C, hC, fun w hw hqw => hb w hw.1 hqw⟩)
  have ht := weaken_bound (s := -seedPotentialLoss h W.alpha W.shift (min MT.alpha MR.alpha) m)
    hh hh1 (neg_le_neg (le_max_right _ _)) ht0
  have hr := weaken_bound (s := -seedPotentialLoss h W.alpha W.shift (min MT.alpha MR.alpha) m)
    hh hh1 (neg_le_neg (le_max_right _ _)) hr0
  have sp : ContDiffOn ℝ ∞ W.vector (CutStageEstimates.physicalSublevel h qbig) :=
    (W.vector_smooth hh hh1).mono inter_subset_left
  have st := MT.angular_smooth hh hh1 hqT
  exact add_bounds hh hh1 (sp.add st) (MR.angular_smooth hh hh1 hqR)
    (add_bounds hh hh1 sp st hp ht) hr

theorem initialIncrement_rate (W : PhysicalStageBounds.WaveData h D I K (Fin 3))
    (MT MR : MeanInput h (CoordinateAlgebra.A h - 1 / 2))
    (hh : 0 < h) (hh1 : h < 1 / 2) {qbig : ℝ} (hqbig : 0 < qbig)
    (hqT : qbig ≤ ChartScales.Q MT.firstBand) (hqR : qbig ≤ ChartScales.Q MR.firstBand) (m : ℕ) :
    JetRate ActualBaseVelocityBounds.endpoint (PhysicalWaveSum.physicalQ h)
      (initialIncrement W MT MR) m
      (-seedPotentialLoss h W.alpha W.shift (min MT.alpha MR.alpha) m) := by
  obtain ⟨C, hC, hb⟩ := initialIncrement_bound W MT MR hh hh1 hqT hqR m
  refine ⟨C, hC, ?_⟩
  filter_upwards [InitializedPhysicalBackground.endpoint_sublevel hh hh1 hqbig,
    ActualBaseVelocityBounds.endpoint_q_small hh hh1] with w hw hqw
  exact hb w hw hqw.2

/-- The finite pressure inserted at initialization, apart from the actual
base pressure. Both terms retain their original native class exponents. -/
noncomputable def initialPressureIncrement (W : PhysicalStageBounds.WaveData h D I K Unit)
    (M : MeanInput h (2 * CoordinateAlgebra.A h)) : PressureField :=
  fun w => W.pressure w + M.family.field w

/-- Initial pressure loss, given by `PhysicalStageBounds.pressureLoss h (-(h * waveAlpha +
waveShift)) (-(h * meanAlpha)) m`. -/
noncomputable def initialPressureLoss (h waveAlpha waveShift meanAlpha : ℝ) (m : ℕ) : ℝ :=
  PhysicalStageBounds.pressureLoss h (-(h * waveAlpha + waveShift)) (-(h * meanAlpha)) m

theorem initialPressureIncrement_smooth (W : PhysicalStageBounds.WaveData h D I K Unit)
    (M : MeanInput h (2 * CoordinateAlgebra.A h))
    (hh : 0 < h) (hh1 : h < 1 / 2) {qbig : ℝ} (hq : qbig ≤ ChartScales.Q M.firstBand) :
    ContDiffOn ℝ ∞ (initialPressureIncrement W M) (CutStageEstimates.physicalSublevel h qbig) :=
  ((W.pressure_smooth hh hh1).mono inter_subset_left).add (M.field_smooth hh hh1 hq)

theorem initialPressureIncrement_bound (W : PhysicalStageBounds.WaveData h D I K Unit)
    (M : MeanInput h (2 * CoordinateAlgebra.A h))
    (hh : 0 < h) (hh1 : h < 1 / 2) {qbig : ℝ} (hq : qbig ≤ ChartScales.Q M.firstBand) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (initialPressureIncrement W M) w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^ (-initialPressureLoss h W.alpha W.shift M.alpha m) := by
  have hw0 := W.pressure_bound_with_gain (g := 0) (delta := -(h * W.alpha + W.shift))
    hh hh1 (by linarith) m
  have hm0 := M.field_bound_with_gain (g := 0) (delta := -(h * M.alpha))
    hh hh1 hq (by linarith) m
  simp only [zero_sub] at hw0 hm0
  have hw := weaken_bound (qbig := qbig)
    (s := -initialPressureLoss h W.alpha W.shift M.alpha m) hh hh1
    (neg_le_neg (le_max_left _ _)) (by
      obtain ⟨C, hC, hb⟩ := hw0
      exact ⟨C, hC, fun w hw hqw => hb w hw.1 hqw⟩)
  have hm := weaken_bound (s := -initialPressureLoss h W.alpha W.shift M.alpha m)
    hh hh1 (neg_le_neg (le_max_right _ _)) hm0
  have sw : ContDiffOn ℝ ∞ W.pressure (CutStageEstimates.physicalSublevel h qbig) :=
    (W.pressure_smooth hh hh1).mono inter_subset_left
  exact add_bounds hh hh1 sw (M.field_smooth hh hh1 hq) hw hm

theorem initialPressureIncrement_rate (W : PhysicalStageBounds.WaveData h D I K Unit)
    (M : MeanInput h (2 * CoordinateAlgebra.A h))
    (hh : 0 < h) (hh1 : h < 1 / 2) {qbig : ℝ} (hqbig : 0 < qbig)
    (hq : qbig ≤ ChartScales.Q M.firstBand) (m : ℕ) :
    JetRate ActualBaseVelocityBounds.endpoint (PhysicalWaveSum.physicalQ h)
      (initialPressureIncrement W M) m (-initialPressureLoss h W.alpha W.shift M.alpha m) := by
  obtain ⟨C, hC, hb⟩ := initialPressureIncrement_bound W M hh hh1 hq m
  refine ⟨C, hC, ?_⟩
  filter_upwards [InitializedPhysicalBackground.endpoint_sublevel hh hh1 hqbig,
    ActualBaseVelocityBounds.endpoint_q_small hh hh1] with w hw hqw
  exact hb w hw hqw.2

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem initialDirect_rate (MB : MeanInput h (CoordinateAlgebra.A h))
    (hh : 0 < h) (hh1 : h < 1 / 2) {qbig : ℝ} (hqbig : 0 < qbig)
    (hq : qbig ≤ ChartScales.Q MB.firstBand) (m : ℕ) :
    JetRate ActualBaseVelocityBounds.endpoint (PhysicalWaveSum.physicalQ h)
      MB.family.angularField m (-seedDirectLoss h MB.alpha m) := by
  obtain ⟨C, hC, hb⟩ := MB.angular_bound_with_gain (g := 0) (delta := -(h * MB.alpha))
    hh hh1 hq (by linarith) m
  refine ⟨C, hC, ?_⟩
  filter_upwards [InitializedPhysicalBackground.endpoint_sublevel hh hh1 hqbig,
    ActualBaseVelocityBounds.endpoint_q_small hh hh1] with w hw hqw
  simpa only [seedDirectLoss, PhysicalStageBounds.directLoss, zero_sub] using hb w hw hqw.2

end InitialIncrement

section ActualInitialBase

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld)
  {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {I K : Type*}

/-- Initial potential, defined pointwise by `TailGaugePotential.finalPotential H v upper B w +
initialIncrement WA MT MR w`. -/
noncomputable def initialPotential (upper : ℝ) (B : ℕ)
    (WA : PhysicalStageBounds.WaveData F.data.h D I K (Fin 3))
    (MT MR : MeanInput F.data.h (CoordinateAlgebra.A F.data.h - 1 / 2)) : VelocityField :=
  fun w => TailGaugePotential.finalPotential H v upper B w + initialIncrement WA MT MR w

/-- Initial velocity, defined pointwise by `SpatialCurl.spatialCurl (initialPotential H v upper
B WA MT MR) w + MB.family.angularField w`. -/
noncomputable def initialVelocity (upper : ℝ) (B : ℕ)
    (WA : PhysicalStageBounds.WaveData F.data.h D I K (Fin 3))
    (MT MR : MeanInput F.data.h (CoordinateAlgebra.A F.data.h - 1 / 2))
    (MB : MeanInput F.data.h (CoordinateAlgebra.A F.data.h)) : VelocityField :=
  fun w => SpatialCurl.spatialCurl (initialPotential H v upper B WA MT MR) w +
      MB.family.angularField w

theorem initialPotential_smooth (upper : ℝ) (B : ℕ)
    (WA : PhysicalStageBounds.WaveData F.data.h D I K (Fin 3))
    (MT MR : MeanInput F.data.h (CoordinateAlgebra.A F.data.h - 1 / 2))
    {qbig : ℝ} (hqT : qbig ≤ ChartScales.Q MT.firstBand) (hqR : qbig ≤ ChartScales.Q MR.firstBand) :
    ContDiffOn ℝ ∞ (initialPotential H v upper B WA MT MR)
      (CutStageEstimates.physicalSublevel F.data.h qbig) :=
  ((TailGaugePotential.finalPotential_smooth H v upper B).mono
    (fun _ hw => ⟨hw.1, mem_univ _⟩)).add
      (initialIncrement_smooth WA MT MR F.data.h_pos F.data.h_lt_half hqT hqR)

theorem initialVelocity_decomposition (upper : ℝ) (B : ℕ)
    (WA : PhysicalStageBounds.WaveData F.data.h D I K (Fin 3))
    (MT MR : MeanInput F.data.h (CoordinateAlgebra.A F.data.h - 1 / 2))
    (MB : MeanInput F.data.h (CoordinateAlgebra.A F.data.h))
    {qbig : ℝ} (hqT : qbig ≤ ChartScales.Q MT.firstBand) (hqR : qbig ≤ ChartScales.Q MR.firstBand) :
    EqOn (initialVelocity H v upper B WA MT MR MB)
      (fun w => FinalSlowBase.velocity H v upper B w +
        SpatialCurl.spatialCurl (initialIncrement WA MT MR) w + MB.family.angularField w)
      (CutStageEstimates.physicalSublevel F.data.h qbig) := by
  have hbase : ContDiffOn ℝ ∞ (TailGaugePotential.finalPotential H v upper B)
      (CutStageEstimates.physicalSublevel F.data.h qbig) :=
    (TailGaugePotential.finalPotential_smooth H v upper B).mono
      (fun _ hw => ⟨hw.1, mem_univ _⟩)
  have hinc := initialIncrement_smooth WA MT MR F.data.h_pos F.data.h_lt_half hqT hqR
  intro w hw
  unfold initialVelocity initialPotential
  rw [InitializedPhysicalBackground.spatialCurl_add_on
    (CutStageEstimates.physicalSublevel_open F.data.h_pos F.data.h_lt_half qbig) hbase hinc hw]
  dsimp only
  rw [TailGaugePotential.finalPotential_sameCurl H v upper B hw.1]

/-- The true-domain initialization has the same fixed loss as the prior
physical-background calculation, using the minimum of the two stream classes. -/
theorem initialVelocity_rate (upper : ℝ) (B : ℕ)
    (WA : PhysicalStageBounds.WaveData F.data.h D I K (Fin 3))
    (MT MR : MeanInput F.data.h (CoordinateAlgebra.A F.data.h - 1 / 2))
    (MB : MeanInput F.data.h (CoordinateAlgebra.A F.data.h)) (m : ℕ) :
    JetRate ActualBaseVelocityBounds.endpoint (PhysicalWaveSum.physicalQ F.data.h)
      (initialVelocity H v upper B WA MT MR MB) m
      (-initialLoss F.data.h WA.alpha WA.shift (min MT.alpha MR.alpha) MB.alpha m) := by
  let qbig := min (ChartScales.Q MT.firstBand) (min (ChartScales.Q MR.firstBand) (ChartScales.Q
      MB.firstBand))
  have hqbig : 0 < qbig := lt_min (ChartScales.Q_pos _) (lt_min (ChartScales.Q_pos _)
      (ChartScales.Q_pos _))
  have hqT : qbig ≤ ChartScales.Q MT.firstBand := min_le_left _ _
  have hqR : qbig ≤ ChartScales.Q MR.firstBand := (min_le_right _ _).trans (min_le_left _ _)
  have hqB : qbig ≤ ChartScales.Q MB.firstBand := (min_le_right _ _).trans (min_le_right _ _)
  let U := CutStageEstimates.physicalSublevel F.data.h qbig
  have hU : IsOpen U := CutStageEstimates.physicalSublevel_open F.data.h_pos F.data.h_lt_half qbig
  have hlU : ∀ᶠ w in ActualBaseVelocityBounds.endpoint, w ∈ U :=
    InitializedPhysicalBackground.endpoint_sublevel F.data.h_pos F.data.h_lt_half hqbig
  have hq := ActualBaseVelocityBounds.endpoint_q_small F.data.h_pos F.data.h_lt_half
  have hsBase : ContDiffOn ℝ ∞ (FinalSlowBase.velocity H v upper B) U :=
    (FinalSlowBase.velocity_smooth H v upper B).mono (fun _ hw => ⟨hw.1, mem_univ _⟩)
  have hsInc : ContDiffOn ℝ ∞ (initialIncrement WA MT MR) U :=
    initialIncrement_smooth WA MT MR F.data.h_pos F.data.h_lt_half hqT hqR
  have hsDirect : ContDiffOn ℝ ∞ MB.family.angularField U :=
    MB.angular_smooth F.data.h_pos F.data.h_lt_half hqB
  have hsCurl := InitializedPhysicalBackground.spatialCurl_smoothOn hU hsInc
  have hbase : JetRate ActualBaseVelocityBounds.endpoint (PhysicalWaveSum.physicalQ F.data.h)
      (FinalSlowBase.velocity H v upper B) m
      (-initialLoss F.data.h WA.alpha WA.shift (min MT.alpha MR.alpha) MB.alpha m) :=
    (ActualBaseVelocityBounds.velocity_rate H v upper B m).weaken hq (neg_le_neg (le_max_left _ _))
  have hinc : JetRate ActualBaseVelocityBounds.endpoint (PhysicalWaveSum.physicalQ F.data.h)
      (SpatialCurl.spatialCurl (initialIncrement WA MT MR)) m
      (-initialLoss F.data.h WA.alpha WA.shift (min MT.alpha MR.alpha) MB.alpha m) := by
    apply ((initialIncrement_rate WA MT MR F.data.h_pos F.data.h_lt_half hqbig hqT hqR
      (m + 1)).spatialCurl hU hlU hsInc).weaken hq
    exact neg_le_neg ((le_max_left _ _).trans (le_max_right _ _))
  have hdirect : JetRate ActualBaseVelocityBounds.endpoint (PhysicalWaveSum.physicalQ F.data.h)
      MB.family.angularField m
      (-initialLoss F.data.h WA.alpha WA.shift (min MT.alpha MR.alpha) MB.alpha m) := by
    apply (initialDirect_rate MB F.data.h_pos F.data.h_lt_half hqbig hqB m).weaken hq
    exact neg_le_neg ((le_max_right _ _).trans (le_max_right _ _))
  exact ((hbase.add hinc hU hlU hsBase hsCurl).add hdirect hU hlU
    (hsBase.add hsCurl) hsDirect).congr_on hU hlU
      (initialVelocity_decomposition H v upper B WA MT MR MB hqT hqR).symm

theorem represented_initial_rate (upper : ℝ) (B : ℕ)
    (WA : PhysicalStageBounds.WaveData F.data.h D I K (Fin 3))
    (MT MR : MeanInput F.data.h (CoordinateAlgebra.A F.data.h - 1 / 2))
    (MB : MeanInput F.data.h (CoordinateAlgebra.A F.data.h))
    {A Bdirect : ℕ → VelocityField} {U : Set SpaceTime}
    (hU : IsOpen U) (hlU : ∀ᶠ w in ActualBaseVelocityBounds.endpoint, w ∈ U)
    (hA : EqOn (A 0) (initialPotential H v upper B WA MT MR) U)
    (hB : EqOn (Bdirect 0) MB.family.angularField U) (m : ℕ) :
    JetRate ActualBaseVelocityBounds.endpoint (PhysicalWaveSum.physicalQ F.data.h)
      (MixedDiagonalResidual.uncutVelocity A Bdirect 0) m
      (-initialLoss F.data.h WA.alpha WA.shift (min MT.alpha MR.alpha) MB.alpha m) := by
  apply (initialVelocity_rate H v upper B WA MT MR MB m).congr_on hU hlU
  intro w hw
  have he : A 0 =ᶠ[𝓝 w] initialPotential H v upper B WA MT MR := by
    filter_upwards [hU.mem_nhds hw] with y hy
    exact hA hy
  rw [MixedFiniteBackground.uncutVelocity_zero]
  change SpatialCurl.spatialCurl (initialPotential H v upper B WA MT MR) w +
    MB.family.angularField w = SpatialCurl.spatialCurl (A 0) w + Bdirect 0 w
  rw [SolenoidalDiagonal.spatialCurl_eq_of_eventuallyEq he, hB hw]

/-- The finite-background consumer now uses only native wave/mean data
on the true domain, plus exact initial and positive-stage identities. -/
theorem background_from_representations
    {DP DS : Type} [NormedAddCommGroup DP] [NormedSpace ℝ DP]
    [NormedAddCommGroup DS] [NormedSpace ℝ DS] {IP KP IS KS : Type*}
    (Cyc : CycleInputs F.data.h DP IP KP DS IS KS) {κ qbig : ℝ}
    (HM : Cyc.Metadata κ) (HQ : Cyc.ValidScale qbig) (hκ : κ ≤ 1 / 100000)
    (hqbig : 0 < qbig) (upper : ℝ) (bandFloor : ℕ)
    (WA : PhysicalStageBounds.WaveData F.data.h D I K (Fin 3))
    (MT MR : MeanInput F.data.h (CoordinateAlgebra.A F.data.h - 1 / 2))
    (MB : MeanInput F.data.h (CoordinateAlgebra.A F.data.h))
    (hqT : qbig ≤ ChartScales.Q MT.firstBand) (hqR : qbig ≤ ChartScales.Q MR.firstBand)
    (hqB : qbig ≤ ChartScales.Q MB.firstBand)
    (A B : ℕ → VelocityField)
    (hA0 : EqOn (A 0) (initialPotential H v upper bandFloor WA MT MR)
      (CutStageEstimates.physicalSublevel F.data.h qbig))
    (hB0 : EqOn (B 0) MB.family.angularField (CutStageEstimates.physicalSublevel F.data.h qbig))
    (hA : ∀ k, EqOn (Cyc.potential k) (A (k + 1)) (CutStageEstimates.physicalSublevel F.data.h
        qbig))
    (hB : ∀ k, EqOn (Cyc.direct k) (B (k + 1)) (CutStageEstimates.physicalSublevel F.data.h qbig))
    (J m : ℕ) :
    JetRate ActualBaseVelocityBounds.endpoint (PhysicalWaveSum.physicalQ F.data.h)
      (MixedDiagonalResidual.uncutVelocity A B J) m
      (-MixedFiniteBackground.initialBackgroundLoss
        (initialLoss F.data.h WA.alpha WA.shift (min MT.alpha MR.alpha) MB.alpha)
        (PhysicalStageBounds.potentialLoss F.data.h F.data.h 0)
        (PhysicalStageBounds.directLoss F.data.h 0) m) := by
  have hU := CutStageEstimates.physicalSublevel_open F.data.h_pos F.data.h_lt_half qbig
  have hlU := InitializedPhysicalBackground.endpoint_sublevel F.data.h_pos F.data.h_lt_half hqbig
  have hsa : ∀ j, ContDiffOn ℝ ∞ (A j) (CutStageEstimates.physicalSublevel F.data.h qbig) := by
    intro j
    cases j with
    | zero =>
      exact (initialPotential_smooth H v upper bandFloor WA MT MR hqT hqR).congr
        (fun _ hw => hA0 hw)
    | succ k =>
      exact (Cyc.potential_smooth HQ F.data.h_pos F.data.h_lt_half k).congr
        (fun _ hw => (hA k hw).symm)
  have hsb : ∀ j, ContDiffOn ℝ ∞ (B j) (CutStageEstimates.physicalSublevel F.data.h qbig) := by
    intro j
    cases j with
    | zero =>
      exact (MB.angular_smooth F.data.h_pos F.data.h_lt_half hqB).congr (fun _ hw => hB0 hw)
    | succ k =>
      exact (Cyc.direct_smooth HQ F.data.h_pos F.data.h_lt_half k).congr
        (fun _ hw => (hB k hw).symm)
  obtain ⟨CA, _, hrawA⟩ := raw_of_positive_bounds (fun k m =>
    bound_congr F.data.h_pos F.data.h_lt_half (hA k)
      (Cyc.potential_bound HM HQ F.data.h_pos F.data.h_lt_half hκ k m))
  obtain ⟨CB, _, hrawB⟩ := raw_of_positive_bounds (fun k m =>
    bound_congr F.data.h_pos F.data.h_lt_half (hB k)
      (Cyc.direct_bound HM HQ F.data.h_pos F.data.h_lt_half hκ k m))
  exact MixedFiniteBackground.mixed_background_from_initial hU hlU
    (ActualBaseVelocityBounds.endpoint_past.and hlU)
    (ActualBaseVelocityBounds.endpoint_q_small F.data.h_pos F.data.h_lt_half)
    hsa hsb hrawA hrawB (fun j _ => ActualIterationLedger.gain_nonneg F.data.h_pos.le j)
    (represented_initial_rate H v upper bandFloor WA MT MR MB hU hlU hA0 hB0) J m

end ActualInitialBase

/-! ## Literal candidate sequence interface -/

universe u

section CandidateSequences

variable {F : OutgoingProfile.Profile} {W : NominalProfile.Witness F}
  (H : NominalConeAssembly.Certificate W) {ld : ModulatedProfileAssembly.LoopData W}
  (v : ModulatedProfileAssembly.Witness ld)
  {DP DS : Type} [NormedAddCommGroup DP] [NormedSpace ℝ DP]
  [NormedAddCommGroup DS] [NormedSpace ℝ DS] {IP KP IS KS : Type*}

/-- Quantitative bounds for the actual MCA/MAS indexing convention.
The remaining representations concern the literal component fields. -/
theorem candidate_raw_bounds
    (Cyc : CycleInputs F.data.h DP IP KP DS IS KS) {κ qbig : ℝ}
    (HM : Cyc.Metadata κ) (HQ : Cyc.ValidScale qbig) (hκ : κ ≤ 1 / 100000)
    (upper : ℝ) (bandFloor : ℕ)
    (initial : MixedAxisPreservation.PotentialStage.{u} F.data.h
      (MixedAxisPreservation.localDomain F.data.h qbig))
    (stages : ℕ → MixedAxisPreservation.PotentialStage.{u} F.data.h
      (MixedAxisPreservation.localDomain F.data.h qbig))
    (angular : ℕ → DirectAngularDiagonal.AngularData (LocalAngularDiagonal.localSlowDomain F.data.h
        qbig))
    (pInitial : PressureField) (pStages : ℕ → PressureField)
    (hA : ∀ k, EqOn (Cyc.potential k) (stages k).field (CutStageEstimates.physicalSublevel F.data.h
        qbig))
    (hB : ∀ k, EqOn (Cyc.direct k) (LocalAngularDiagonal.rawSeries angular (k + 1))
      (CutStageEstimates.physicalSublevel F.data.h qbig))
    (hP : ∀ k, EqOn (Cyc.pressureField k) (pStages k) (CutStageEstimates.physicalSublevel F.data.h
        qbig)) :
    ∃ CA CB CP : ℕ → ℕ → ℝ,
      (∀ j m, 0 ≤ CA j m ∧ 0 ≤ CB j m ∧ 0 ≤ CP j m) ∧
      CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ F.data.h)
        (MixedCandidateAssembly.potentialStages H v upper bandFloor initial stages)
        (ActualIterationLedger.gain F.data.h) (PhysicalStageBounds.potentialLoss F.data.h F.data.h
            0)
        CA (fun _ _ => 0) (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel
            F.data.h qbig) ∧
      CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ F.data.h)
        (LocalAngularDiagonal.rawSeries angular) (ActualIterationLedger.gain F.data.h)
        (PhysicalStageBounds.directLoss F.data.h 0) CB (fun _ _ => 0)
        (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel F.data.h qbig) ∧
      CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ F.data.h)
        (MixedCandidateAssembly.pressureStages H v upper bandFloor pInitial pStages)
        (ActualIterationLedger.gain F.data.h)
        (PhysicalStageBounds.pressureLoss F.data.h (2 * CoordinateAlgebra.A F.data.h) 0)
        CP (fun _ _ => 0) (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel
            F.data.h qbig) := by
  apply Cyc.represented_raw_bounds HM HQ F.data.h_pos F.data.h_lt_half hκ
  · intro k
    simpa only [MixedCandidateAssembly.potentialStages,
        MixedAxisPreservation.initializedSeries_succ] using hA k
  · exact hB
  · intro k
    simpa only [MixedCandidateAssembly.pressureStages_succ] using hP k

end CandidateSequences

/-! ## Adapters for the constructed native mean families -/

section ConstructedMeans

open CorrectionInitialization.ActualPrimary ActualMeanPhysicalData
open CorrectionStep CorrectionState

/-- The constructed initialization families, with their proved native
classes and common band choice. No native estimate is left as an input. -/
noncomputable def actualInitialTemporalInput (B N0 N : ℕ) (hN : 4 ≤ N) :
    MeanInput h (CoordinateAlgebra.A h - 1 / 2) :=
  MeanInput.ofMoving standardRegion rfl (initialTemporalFamily B N0 N) hN
    (PrimaryTargetBounds.leftRadius_pos nominal) (PrimaryTargetBounds.radii_ordered nominal)
    (initialTemporal_moving B N0) (initialTemporal_nativeJets B N0 N (by omega))

/-- Actual initial rank input, constructed using `MeanInput.ofMoving`. -/
noncomputable def actualInitialRankInput (B N0 N : ℕ) (hN : 4 ≤ N) :
    MeanInput h (CoordinateAlgebra.A h - 1 / 2) :=
  MeanInput.ofMoving standardRegion rfl (initialRankFamily B N0 N) hN
    (PrimaryTargetBounds.leftRadius_pos nominal) (PrimaryTargetBounds.radii_ordered nominal)
    (initialRank_moving B N0) (initialRank_nativeJets B N0 N (by omega))

/-- Actual initial angular input, constructed using `MeanInput.ofMoving`. -/
noncomputable def actualInitialAngularInput (B N0 N : ℕ) (hN : 4 ≤ N) :
    MeanInput h (CoordinateAlgebra.A h) :=
  MeanInput.ofMoving standardRegion rfl (initialAngularFamily B N0 N) hN
    (PrimaryTargetBounds.leftRadius_pos nominal) (PrimaryTargetBounds.radii_ordered nominal)
    (initial_mean_moving B N0).angular (initialAngular_nativeJets B N0 N (by omega))

/-- Actual initial pressure input, constructed using `MeanInput.ofMoving`. -/
noncomputable def actualInitialPressureInput (B N0 N : ℕ) (hN : 4 ≤ N) :
    MeanInput h (2 * CoordinateAlgebra.A h) :=
  MeanInput.ofMoving standardRegion rfl (initialPressureFamily B N0 N) hN
    (PrimaryTargetBounds.leftRadius_pos nominal) (PrimaryTargetBounds.radii_ordered nominal)
    (initial_pressure_moving B N0) (initialPressure_nativeJets B N0 N (by omega))

@[simp] theorem actualInitialTemporalInput_family (B N0 N : ℕ) (hN : 4 ≤ N) :
    (actualInitialTemporalInput B N0 N hN).family = initialTemporalFamily B N0 N := rfl

@[simp] theorem actualInitialRankInput_family (B N0 N : ℕ) (hN : 4 ≤ N) :
    (actualInitialRankInput B N0 N hN).family = initialRankFamily B N0 N := rfl

@[simp] theorem actualInitialAngularInput_family (B N0 N : ℕ) (hN : 4 ≤ N) :
    (actualInitialAngularInput B N0 N hN).family = initialAngularFamily B N0 N := rfl

@[simp] theorem actualInitialPressureInput_family (B N0 N : ℕ) (hN : 4 ≤ N) :
    (actualInitialPressureInput B N0 N hN).family = initialPressureFamily B N0 N := rfl

/-- The actual initialized velocity, with its actual initial temporal,
rank, and direct angular families. Only the primary wave representation
is supplied by the separate physical-copy construction. -/
theorem actualInitialVelocity_rate
    {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {I K : Type*}
    (B N0 N : ℕ) (hN : 4 ≤ N) (WA : PhysicalStageBounds.WaveData h D I K (Fin 3)) (m : ℕ) :
    JetRate ActualBaseVelocityBounds.endpoint (PhysicalWaveSum.physicalQ h)
      (initialVelocity certificate modulation upper B WA
        (actualInitialTemporalInput B N0 N hN) (actualInitialRankInput B N0 N hN)
        (actualInitialAngularInput B N0 N hN)) m
      (-initialLoss h WA.alpha WA.shift (1 - ChartScales.kappa) (9 / 10) m) := by
  simpa only [actualInitialTemporalInput, actualInitialRankInput, actualInitialAngularInput,
    MeanInput.ofMoving, min_self] using
    initialVelocity_rate certificate modulation upper B WA
      (actualInitialTemporalInput B N0 N hN) (actualInitialRankInput B N0 N hN)
      (actualInitialAngularInput B N0 N hN) m

variable {B N0 N : ℕ} {p : ℕ → CycleParameters (ActualInitialization.Index B N0)}

/-- These four cycle adapters retain the literal families of the actual
iterate. Their quantitative hypotheses are native source, debt, or mean
classes; physical derivative bounds are conclusions of the earlier API. -/
noncomputable def actualCycleTemporalInput (H : InitialCycleInput B N0 N p)
    (j : ℕ) (hN : 4 ≤ N) {α : ℝ}
    (HC : WeightedClasses.MeanClass ActualInitialMean.strip α
      (((p j).afterSigned
        (CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0)
            j).coefficients
        (commonContext B) (CycleState.iterate p (commonContext B)
            (ActualInitialization.initialCycleState B N0) j).state).axialResidual
        (commonContext B))) : MeanInput h (CoordinateAlgebra.A h - 1 / 2) :=
  MeanInput.ofMoving standardRegion rfl ((initialCycleData H).temporalFamily j) hN
    initialGeometry.inner_pos initialGeometry.inner_lt_outer
    ((initialCycleData H).temporal_moving j) (cycleTemporal_nativeJets H j (by omega) HC)

/-- Actual cycle rank input, constructed using `MeanInput.ofMoving`. -/
noncomputable def actualCycleRankInput (H : InitialCycleInput B N0 N p)
    (j : ℕ) (hN : 4 ≤ N) {α : ℝ}
    (HC : WeightedClasses.UnweightedClass ActualInitialMean.slowStrip α
      (CorrectionState.debt (commonContext B)
        ((p j).afterTemporal
          (CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0)
              j).coefficients
          (commonContext B) (CycleState.iterate p (commonContext B)
              (ActualInitialization.initialCycleState B N0) j).state))) :
    MeanInput h (CoordinateAlgebra.A h - 1 / 2) :=
  MeanInput.ofMoving standardRegion rfl ((initialCycleData H).rankFamily j) hN
    initialGeometry.inner_pos initialGeometry.inner_lt_outer
    ((initialCycleData H).rank_moving j) (cycleRank_nativeJets H j (by omega) HC)

/-- Actual cycle angular input, constructed using `MeanInput.ofMoving`. -/
noncomputable def actualCycleAngularInput (H : InitialCycleInput B N0 N p)
    (j : ℕ) (hN : 4 ≤ N) {α : ℝ}
    (HT : MeanIncrementBounds.IncrementBounds ActualInitialMean.strip α
      ((p j).temporalIncrement
        (CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0)
            j).coefficients
        (commonContext B) (CycleState.iterate p (commonContext B)
            (ActualInitialization.initialCycleState B N0) j).state))
    (HR : MeanIncrementBounds.IncrementBounds ActualInitialMean.strip α
      ((p j).rankIncrement
        (CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0)
            j).coefficients
        (commonContext B) (CycleState.iterate p (commonContext B)
            (ActualInitialization.initialCycleState B N0) j).state)) :
    MeanInput h (CoordinateAlgebra.A h) :=
  MeanInput.ofMoving standardRegion rfl ((initialCycleData H).angularIncrementFamily j) hN
    initialGeometry.inner_pos initialGeometry.inner_lt_outer
    ((initialCycleData H).angularIncrement_moving j) (angularIncrement_nativeJets H j (by
        omega) HT HR)

/-- Actual cycle pressure input as an element of `MeanInput h (2 * CoordinateAlgebra.A h)`. -/
noncomputable def actualCyclePressureInput (H : InitialCycleInput B N0 N p)
    (j : ℕ) (hN : 4 ≤ N) {α : ℝ}
    (HC : WeightedClasses.MeanClass ActualInitialMean.strip α
      ((CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0)
          (j + 1)).state.pressure -
        (CycleState.iterate p (commonContext B) (ActualInitialization.initialCycleState B N0)
            j).state.pressure)) :
    MeanInput h (2 * CoordinateAlgebra.A h) := by
  have hs : (VariableGaugeMean.reconstructState initialGeometry.gauge (commonContext B)
      (ActualInitialization.initialCycleState B N0).state).pressure =
      (ActualInitialization.initialCycleState B N0).state.pressure := by
    rw [initialGeometry_gauge]
    rfl
  exact MeanInput.ofMoving standardRegion rfl ((initialCycleData H).pressureIncrementFamily j) hN
    initialGeometry.inner_pos initialGeometry.inner_lt_outer
    ((initialCycleData H).pressureIncrement_moving hs j) (pressureIncrement_nativeJets H j (by
        omega) HC)

end ConstructedMeans

end NavierStokes.ActualPhysicalStageBounds
