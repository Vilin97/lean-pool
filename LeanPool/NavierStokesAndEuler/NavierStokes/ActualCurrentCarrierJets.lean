/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualPhaseJetBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.LocalPhysicalCopyBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualParticularStageControls

/-!
# Uniform phase jets for the actual current-chart copies

The functions below are literal reindexings of the selected common phase.
Positive jets have a fixed `Q^(-2h)` loss, uniformly before the label and
band are selected. No bound on the unbounded phase value is asserted.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ActualCurrentCarrierJets

open Set Function Filter CorrectionInitialization
open scoped Topology ContDiff

/-- Label: an abbreviation for `ActualPrimaryBounds.SignedLabel B N0`. -/
abbrev Label (B N0 : ℕ) := ActualPrimaryBounds.SignedLabel B N0
/-- Native: an abbreviation for `ActualParticularBackground.Native`. -/
abbrev Native := ActualParticularBackground.Native
/-- Full point: an abbreviation for `ActualPrimary.FullPoint`. -/
abbrev FullPoint := ActualPrimary.FullPoint

variable {B N0 : ℕ}

/-- The actual common phase in the current free-angle native coordinates. -/
noncomputable def phase (l : Label B N0) (n : ℕ) (z : Native) : ℝ :=
  (ActualPrimary.chartCoefficients l.1 l.2).phase n
    (ActualParticularBackground.nativeToFull z)

/-- The same phase with the actual base carrier already included. -/
noncomputable def weightedPhase (l : Label B N0) (n : ℕ) (z : Native) : ℝ :=
  ActualPhaseJetBounds.weightedPhase l n (ActualParticularBackground.nativeToFull z)

theorem weightedPhase_eq (l : Label B N0) (n : ℕ) :
    weightedPhase l n = fun z => (ChartScales.carrier ActualPrimary.h n : ℝ) * phase l n z := rfl

/-- The oscillatory factor used by the actual harmonic copy is exactly
the character of the carrier-weighted current phase. -/
theorem harmonic_carrier_eq (l : Label B N0) (n : ℕ) (j : ℤ) :
    HarmonicCalculus.carrier ((j : ℝ) * (ChartScales.carrier ActualPrimary.h n : ℝ))
      (phase l n) = PhysicalGraphBounds.character (j : ℝ) ∘ weightedPhase l n := by
  funext z
  simp only [HarmonicCalculus.carrier, HarmonicCalculus.phaseFactor,
    PhysicalGraphBounds.character, PhysicalGraphBounds.phaseFactor, Function.comp_apply,
    weightedPhase_eq, Complex.ofReal_mul]
  congr 1
  ring

theorem actualCarrier_phase
    (b : Label B N0 → CorrectionState.HarmonicBlock CorrectionStep.CyclePoint)
    (hb : ∀ l, CorrectionStep.SameCarrier (b l) (ActualParticularBackground.primaryBlock l))
    (j : ℤ) (l : Label B N0) (n : ℕ) :
    (ActualParticularBackground.carrier b j l).phase n = phase l n :=
  congrFun (ActualParticularBackground.carrier_phase b hb j l) n

theorem actualCarrier_character
    (b : Label B N0 → CorrectionState.HarmonicBlock CorrectionStep.CyclePoint)
    (hb : ∀ l, CorrectionStep.SameCarrier (b l) (ActualParticularBackground.primaryBlock l))
    (j : ℤ) (l : Label B N0) (n : ℕ) :
    HarmonicCalculus.carrier ((ActualParticularBackground.carrier b j l).frequency n)
      ((ActualParticularBackground.carrier b j l).phase n) =
        PhysicalGraphBounds.character (j : ℝ) ∘ weightedPhase l n := by
  rw [actualCarrier_phase b hb j l n, ActualParticularBackground.carrier_frequency b hb j l]
  exact harmonic_carrier_eq l n j

theorem paddedCell_eq_phaseCell (n : ℕ) (i : ActualPhaseJetBounds.CopyIndex B N0) :
    ParticularPaddedBackground.paddedCell n i = ActualPhaseJetBounds.phaseCell n i := rfl

theorem mem_cells_iff (n : ℕ) (i : ActualPhaseJetBounds.CopyIndex B N0) (z : Native) :
    z ∈ ParticularPaddedBackground.cells n i ↔
      ActualParticularBackground.nativeToFull z ∈ ActualPhaseJetBounds.phaseCell n i := Iff.rfl

private theorem smoothNear_congr {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : E → F} {x : E} (hf : LocalPhysicalCopyBounds.SmoothNear f x)
    (he : g =ᶠ[𝓝 x] f) : LocalPhysicalCopyBounds.SmoothNear g x := by
  obtain ⟨U, hU, hx, hf⟩ := hf
  obtain ⟨V, hVe, hV, hxV⟩ := mem_nhds_iff.mp he
  exact ⟨U ∩ V, hU.inter hV, ⟨hx,hxV⟩,
    (hf.mono inter_subset_left).congr (fun y hy => hVe hy.2)⟩

/-- The one open neighborhood is obtained from the actual analytic phase
cell, then intersected with the genuine periodic-copy germ neighborhood. -/
theorem full_weightedPhase_smoothNear {n : ℕ} {i : ActualPhaseJetBounds.CopyIndex B N0}
    {x : FullPoint} (hx : x ∈ ActualPhaseJetBounds.phaseCell n i) :
    LocalPhysicalCopyBounds.SmoothNear (ActualPhaseJetBounds.weightedPhase i.1 n) x := by
  let g : FullPoint → PhaseCalculus.Slow × ℝ := fun y =>
    ((ActualPrimaryBounds.fullCopy i.1 n i.2 y).1,
      (ActualPrimaryBounds.fullCopy i.1 n i.2 y).2.2)
  have hg : ContDiff ℝ ∞ g := by
    have he : g = fun y => ActualPrimaryBounds.slotLinear i.1 n y +
        ActualPrimaryBounds.slotOfNative (ActualPrimaryBounds.copyPoint i.1 n i.2 0) :=
      funext (ActualPrimaryBounds.slotCopy_affine i.1 n i.2)
    rw [he]
    exact (ActualPrimaryBounds.slotLinear i.1 n).contDiff.add contDiff_const
  let U := g ⁻¹' ActualPhaseJetBounds.jetDomain.carrier i.1
  have hU : IsOpen U := (ActualPhaseJetBounds.jetDomain.isOpen i.1).preimage hg.continuous
  have hxU : x ∈ U := ActualPhaseJetBounds.phaseCell_maps hx
  have hr : ContDiffOn ℝ ∞ (fun y => ActualPhaseJetBounds.nativeRemainder i.1 (g y)) U :=
    (ActualPhaseJetBounds.nativeRemainder_polynomial.smooth i.1).comp
      hg.contDiffOn (fun _ hy => hy)
  have hl : ContDiffOn ℝ ∞ (ActualPhaseJetBounds.localPhase n i) U := by
    have hs := (((ActualPhaseJetBounds.phaseLinear i.1 n).contDiff.add
      (contDiff_const (c := ActualPhaseJetBounds.phaseOffset n i))).contDiffOn).add hr
    exact hs.congr (fun y _ => ActualPhaseJetBounds.localPhase_decomposition n i y)
  have hm : LocalPhysicalCopyBounds.SmoothNear
      (fun y => (ChartScales.carrier ActualPrimary.h (BaseChartJets.cellBand i.1.2) : ℝ) *
        ActualPhaseJetBounds.localPhase n i y) x :=
    ⟨U, hU, hxU, contDiffOn_const.mul hl⟩
  exact smoothNear_congr hm (ActualPhaseJetBounds.weightedPhase_germ hx)

theorem weightedPhase_smoothNear {n : ℕ} {i : ActualPhaseJetBounds.CopyIndex B N0}
    {z : Native} (hz : z ∈ ParticularPaddedBackground.cells n i) :
    LocalPhysicalCopyBounds.SmoothNear (weightedPhase i.1 n) z := by
  obtain ⟨U, hU, hx, hf⟩ := full_weightedPhase_smoothNear ((mem_cells_iff n i z).mp hz)
  exact ⟨ActualParticularBackground.nativeToFull ⁻¹' U,
    hU.preimage ActualParticularBackground.nativeToFull.continuous, hx,
    hf.comp ActualParticularBackground.nativeToFull.toContinuousLinearEquiv.contDiff.contDiffOn
      (fun _ hy => hy)⟩

theorem phase_smoothNear {n : ℕ} {i : ActualPhaseJetBounds.CopyIndex B N0}
    {z : Native} (hz : z ∈ ParticularPaddedBackground.cells n i) :
    LocalPhysicalCopyBounds.SmoothNear (phase i.1 n) z := by
  obtain ⟨U, hU, hx, hf⟩ := weightedPhase_smoothNear hz
  have hk : (ChartScales.carrier ActualPrimary.h n : ℝ) ≠ 0 :=
    (ActualPrimary.chartCoefficients_frequency_pos i.1.1 i.1.2 n).ne'
  refine ⟨U, hU, hx, (hf.div_const (ChartScales.carrier ActualPrimary.h n : ℝ)).congr ?_⟩
  intro y _
  rw [weightedPhase_eq]
  field_simp [hk]

/-- Constants are chosen before the active label, band, copy, point, and
positive derivative order. Reindexing is an isometry and adds no loss. -/
theorem weightedPhase_positive_jets (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ p : ℕ, ∀ n (i : ActualPhaseJetBounds.CopyIndex B N0) z,
      z ∈ ParticularPaddedBackground.cells n i → ∀ r, 1 ≤ r → r ≤ m →
      ‖iteratedFDeriv ℝ r (weightedPhase i.1 n) z‖ ≤
        C * ChartScales.S n ^ p * ChartScales.Q n ^ (-(2 * ActualPrimary.h)) := by
  obtain ⟨C,hC,p,hb⟩ := ActualPhaseJetBounds.weightedPhase_positive_jets (B := B) (N0 := N0) m
  refine ⟨C,hC,p,?_⟩
  intro n i z hz r hr hrm
  change ‖iteratedFDeriv ℝ r (fun y => ActualPhaseJetBounds.weightedPhase i.1 n
    (ActualParticularBackground.nativeToFull y)) z‖ ≤ _
  rw [StateReindex.norm_iteratedFDeriv_pull]
  exact hb n i _ ((mem_cells_iff n i z).mp hz) r hr hrm

theorem phase_positive_jets (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ p : ℕ, ∀ n (i : ActualPhaseJetBounds.CopyIndex B N0) z,
      z ∈ ParticularPaddedBackground.cells n i → ∀ r, 1 ≤ r → r ≤ m →
      ‖iteratedFDeriv ℝ r (phase i.1 n) z‖ ≤
        C * ChartScales.S n ^ p * ChartScales.Q n ^ (-(2 * ActualPrimary.h)) := by
  obtain ⟨C,hC,p,hb⟩ := ActualPhaseJetBounds.phase_positive_jets (B := B) (N0 := N0) m
  refine ⟨C,hC,p,?_⟩
  intro n i z hz r hr hrm
  change ‖iteratedFDeriv ℝ r (fun y => (ActualPrimary.chartCoefficients i.1.1 i.1.2).phase n
    (ActualParticularBackground.nativeToFull y)) z‖ ≤ _
  rw [StateReindex.norm_iteratedFDeriv_pull]
  exact hb n i _ ((mem_cells_iff n i z).mp hz) r hr hrm

/-- The displayed physical loss is exactly two inverse powers of epsilon. -/
theorem weightedPhase_positive_jets_epsilon (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ p : ℕ, ∀ n (i : ActualPhaseJetBounds.CopyIndex B N0) z,
      z ∈ ParticularPaddedBackground.cells n i → ∀ r, 1 ≤ r → r ≤ m →
      ‖iteratedFDeriv ℝ r (weightedPhase i.1 n) z‖ ≤
        C * ChartScales.S n ^ p * (ChartScales.epsilon ActualPrimary.h n)⁻¹ ^ 2 := by
  obtain ⟨C,hC,p,hb⟩ := weightedPhase_positive_jets (B := B) (N0 := N0) m
  refine ⟨C,hC,p,?_⟩
  intro n i z hz r hr hrm
  rw [ActualPhaseJetBounds.inverse_epsilon_sq]
  exact hb n i z hz r hr hrm

theorem weightedPhase_smoothNear_controlPatch (l : Label B N0) (n : ℕ)
    (k : TorusInverse.Frequency) {z : Native}
    (hz : z ∈ ActualParticularStageControls.controlPatch l n k) :
    LocalPhysicalCopyBounds.SmoothNear (weightedPhase l n) z :=
  weightedPhase_smoothNear (n := n) (i := (l,k)) (z := z)
    (ActualParticularStageControls.controlPatch_subset_padded l n k hz)

theorem phase_smoothNear_controlPatch (l : Label B N0) (n : ℕ)
    (k : TorusInverse.Frequency) {z : Native}
    (hz : z ∈ ActualParticularStageControls.controlPatch l n k) :
    LocalPhysicalCopyBounds.SmoothNear (phase l n) z :=
  phase_smoothNear (n := n) (i := (l,k)) (z := z)
    (ActualParticularStageControls.controlPatch_subset_padded l n k hz)

/-- The quantitative statement on the actual retained current-copy cells.
The cell hypothesis already supplies activeness; no native-band interior
or separate phase-jet assumption is added. -/
theorem weightedPhase_positive_jets_controlPatch (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ p : ℕ, ∀ (l : Label B N0) n k z,
      z ∈ ActualParticularStageControls.controlPatch l n k → ∀ r, 1 ≤ r → r ≤ m →
      ‖iteratedFDeriv ℝ r (weightedPhase l n) z‖ ≤
        C * ChartScales.S n ^ p * ChartScales.Q n ^ (-(2 * ActualPrimary.h)) := by
  obtain ⟨C,hC,p,hb⟩ := weightedPhase_positive_jets (B := B) (N0 := N0) m
  exact ⟨C,hC,p,fun l n k z hz r hr hrm =>
    hb n (l,k) z (ActualParticularStageControls.controlPatch_subset_padded l n k hz) r hr hrm⟩

theorem phase_positive_jets_controlPatch (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ p : ℕ, ∀ (l : Label B N0) n k z,
      z ∈ ActualParticularStageControls.controlPatch l n k → ∀ r, 1 ≤ r → r ≤ m →
      ‖iteratedFDeriv ℝ r (phase l n) z‖ ≤
        C * ChartScales.S n ^ p * ChartScales.Q n ^ (-(2 * ActualPrimary.h)) := by
  obtain ⟨C,hC,p,hb⟩ := phase_positive_jets (B := B) (N0 := N0) m
  exact ⟨C,hC,p,fun l n k z hz r hr hrm =>
    hb n (l,k) z (ActualParticularStageControls.controlPatch_subset_padded l n k hz) r hr hrm⟩

end NavierStokes.ActualCurrentCarrierJets
