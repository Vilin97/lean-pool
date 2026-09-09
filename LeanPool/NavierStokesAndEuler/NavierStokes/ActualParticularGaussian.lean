/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualParticularStageControls
import LeanPool.NavierStokesAndEuler.NavierStokes.UniformBlockBounds

/-!
# The weighted Gaussian error of the actual particular update

The native estimates are those of the selected actual Volterra solves, already
transferred back to the original label and band in `raw_jets`.  Gaussian decay
is applied at that original band.  The square-root moving-edge weight is kept
through the entire estimate, including the uncovered source term.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ActualParticularGaussian

open Set Function Filter WeightedClasses
open CorrectionState CorrectionStep CommonCoverSolve TorusInverse
open ActualParticularStageControls CorrectionInitialization
open scoped ContDiff Topology


variable {B N0 : ℕ}

/-- Native strip, given by `CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip
slowStrip)`. -/
noncomputable def nativeStrip : StripData Native :=
  CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip slowStrip)

/-- Band scales, bundling `power`, `epsilon_eq`, `boundConstant`, `constant_one_le` and the
required compatibility proofs. -/
noncomputable def bandScales : GaussianTailFlat.BandScaleControl nativeStrip where
  power := ActualPrimary.h
  epsilon_eq := fun _ => rfl
  boundConstant := 1
  constant_one_le := le_rfl
  degree := 1
  slow_le := fun n => by
    change max 1 (ChartScales.S n) ≤ 1 * (1 + ChartScales.S n) ^ 1
    simp only [pow_one, one_mul]
    have hS : 0 ≤ ChartScales.S n := by unfold ChartScales.S; positivity
    exact max_le (by linarith) (by linarith)

theorem fast_bound : BandBound nativeStrip 0 (directions (B := B)).fastScale :=
  (CommonBaseContext.context_operator_bounds ActualPrimary.certificate ActualPrimary.modulation
    ActualPrimary.upper B ActualPrimary.standardRegion
    (CommonWindow.index_le_native ActualPrimary.h)).fastCoefficient

/-! The clock bounds are imposed only on active pairs. -/

/-- Clock upper, given by `ActualSignedGeometry.powerBound (CoordinateAlgebra.A ActualPrimary.h
+ 1 / 2)`. -/
noncomputable def clockUpper : ℝ :=
  ActualSignedGeometry.powerBound (CoordinateAlgebra.A ActualPrimary.h + 1 / 2)

theorem clockUpper_pos : 0 < clockUpper :=
  zero_lt_one.trans_le (ActualSignedGeometry.powerBound_one _)

theorem clock_bounds {l : Label B N0} {n : ℕ} (ha : Active l n) :
    1 / clockUpper ≤ ActualCarrierTransportBase.clock (supportLabel l) n ∧
      ActualCarrierTransportBase.clock (supportLabel l) n ≤ clockUpper := by
  have hd := CommonWindow.distance ha.2
  exact ⟨ActualSignedGeometry.dyadic_ratioPower_lower hd.1 hd.2 _,
    ActualSignedGeometry.dyadic_ratioPower_le hd.1 hd.2 _⟩

/-- Transported length, given by `ActualCarrierTransportBase.referenceLength (supportLabel l) /
ActualCarrierTransportBase.clock (supportLabel l) n`. -/
noncomputable def transportedLength (l : Label B N0) (n : ℕ) : ℝ :=
  ActualCarrierTransportBase.referenceLength (supportLabel l) /
    ActualCarrierTransportBase.clock (supportLabel l) n

theorem transportedLength_pos (l : Label B N0) (n : ℕ) : 0 < transportedLength l n :=
  div_pos (ActualCarrierTransportBase.referenceLength_pos (supportLabel l))
    (ActualCarrierTransportBase.clock_pos (supportLabel l) n)

/-- Length lower, given by `ActualInitialExcluded.gaussianLengthLower / clockUpper`. -/
noncomputable def lengthLower : ℝ := ActualInitialExcluded.gaussianLengthLower / clockUpper

theorem lengthLower_pos : 0 < lengthLower :=
  div_pos ActualInitialExcluded.gaussianLengthLower_pos clockUpper_pos

theorem transportedLength_lower {l : Label B N0} {n : ℕ} (ha : Active l n) :
    lengthLower * ChartScales.S n ≤ transportedLength l n := by
  have href : ActualInitialExcluded.gaussianLengthLower * ChartScales.S n ≤
      ActualCarrierTransportBase.referenceLength (supportLabel l) := by
    simpa only [ActualCarrierTransportBase.referenceLength, supportLabel,
      ActualPrimary.length_sign] using ActualInitialExcluded.gaussianLength_near l n ha
  calc
    _ = (ActualInitialExcluded.gaussianLengthLower * ChartScales.S n) / clockUpper := by
      unfold lengthLower; ring
    _ ≤ ActualCarrierTransportBase.referenceLength (supportLabel l) / clockUpper :=
      div_le_div_of_nonneg_right href clockUpper_pos.le
    _ ≤ transportedLength l n :=
      div_le_div_of_nonneg_left
        (ActualCarrierTransportBase.referenceLength_pos (supportLabel l)).le
        (ActualCarrierTransportBase.clock_pos (supportLabel l) n) (clock_bounds ha).2

/-- The auxiliary length agrees with the actual transported slot wherever
the analytic patch is used.  It only totalizes the Gaussian bookkeeping on
inactive label-band pairs. -/
noncomputable def gaussianLength (l : Label B N0) (n : ℕ) : ℝ :=
  max (transportedLength l n) (lengthLower * ChartScales.S n)

theorem gaussianLength_pos (l : Label B N0) (n : ℕ) : 0 < gaussianLength l n :=
  (transportedLength_pos l n).trans_le (le_max_left _ _)

theorem gaussianLength_lower (l : Label B N0) (n : ℕ) :
    lengthLower * ChartScales.S n ≤ gaussianLength l n := le_max_right _ _

theorem gaussianLength_eq {l : Label B N0} {n : ℕ} (ha : Active l n) :
    gaussianLength l n = transportedLength l n := max_eq_left (transportedLength_lower ha)

/-- Theta, given by `((ActualCarrierTransportBase.geometry (supportLabel l) n).coordinates k
z.2).2 / transportedLength l n`. -/
noncomputable def theta (l : Label B N0) (n : ℕ) (k : Frequency) (z : Native) : ℝ :=
  ((ActualCarrierTransportBase.geometry (supportLabel l) n).coordinates k z.2).2 /
    transportedLength l n

/-- Gaussian rate, given by `ActualGaussianCoverage.gaussianRate (ActualPrimary.choice B
N0).prepared.M⁻¹ (ActualPrimary.choice B N0).prepared.u / clockUpper`. -/
noncomputable def gaussianRate (B N0 : ℕ) : ℝ :=
  ActualGaussianCoverage.gaussianRate (ActualPrimary.choice B N0).prepared.M⁻¹
    (ActualPrimary.choice B N0).prepared.u / clockUpper

theorem gaussianRate_pos (B N0 : ℕ) : 0 < gaussianRate B N0 :=
  div_pos (ActualGaussianCoverage.prepared_gaussian_rate_pos ActualPrimary.certificate
    ActualPrimary.modulation (ActualPrimary.choice B N0).prepared) clockUpper_pos

/-! Exact envelope and cutoff readouts on the actual analytic patch. -/

theorem envelope_gaussian (l : Label B N0) (n : ℕ) (k : Frequency) {z : Native}
    (hz : z ∈ controlPatch l n k) :
    nativeEnvelope l n z ≤ Real.exp (-gaussianRate B N0 * (theta l n k z - 1 / 2) ^ 2 *
      gaussianLength l n) := by
  let e : ℕ → ActivePair B N0 := fun _ => ⟨(l,n),hz.1⟩
  have hp : z ∈ selectedPatch e () 0 k := by
    rw [← selected_controlPatch e () 0 k]
    exact hz
  have hw : nativeEnvelope l n z = selectedPulseEnvelope e () 0
      ((selectedGeometry e () 0).coordinates k z.2).2 :=
    (selected_envelope_eq e 0 (z.1.1,z.2)).symm.trans (selectedWeight_eq e () 0 k hp)
  rw [hw, gaussianLength_eq hz.1]
  have hl : ∀ u q, (ActualPrimary.choice B N0).prepared.M⁻¹ ≤
      (selectedConstruction e).lam (u,q) := by
    intro u q
    exact ActualGaussianCoverage.prepared_lambda_lower ActualPrimary.certificate
      ActualPrimary.modulation (ActualPrimary.choice B N0).prepared
      ActualPrimary.slots.radius_pos l.1 l.2
  have hb := ActualGaussianCoverage.envelope_uniform_bound
    (selectedConstruction e) (selectedClock e)
    (inv_pos.mpr (zero_lt_one.trans_le (ActualPrimary.choice B N0).prepared.one_le_M))
    (ActualPrimary.choice B N0).prepared.u_pos hl (selected_u e) () 0
    (show ((selectedGeometry e () 0).coordinates k z.2).2 ∈
      Icc 0 (ScaledActualParticularControl.length (selectedConstruction e) (selectedClock e) () 0)
      from ⟨hz.2.1.2.2.1.le, hz.2.1.2.2.2.le⟩)
  have hr : ActualGaussianCoverage.gaussianRate (ActualPrimary.choice B N0).prepared.M⁻¹
      (ActualPrimary.choice B N0).prepared.u * (selectedClock e).lower = gaussianRate B N0 := by
    change _ * (1 / clockUpper) = _ / clockUpper
    ring
  have ht : ActualGaussianCoverage.theta (selectedConstruction e) (selectedClock e) () 0
      ((selectedGeometry e () 0).coordinates k z.2).2 = theta l n k z := by
    rw [ActualGaussianCoverage.theta_eq]
    rfl
  have hlen : ScaledActualParticularControl.length (selectedConstruction e) (selectedClock e) () 0 =
      transportedLength l n := rfl
  simp only [hr, ht, hlen] at hb
  exact hb

theorem cutoff_central (x : CycleState (Label B N0)) (l : Label B N0) (j : ℤ)
    (n : ℕ) (k : Frequency) {z : Native} (hz : z ∈ controlPatch l n k)
    (hm : |theta l n k z - 1 / 2| < 1 / 5) :
    (data x l j).cutoff n k =ᶠ[𝓝 z] fun _ => 1 := by
  rw [data_scalar_eq x l j]
  have hrect : (ActualCarrierTransportBase.geometry (supportLabel l) n).coordinates k z.2 ∈
      WaveEnvelopeTransport.rectangle ActualPrimary.slots.radius (transportedLength l n) :=
    ⟨hz.2.2,hz.2.1.2.2.1.le,hz.2.1.2.2.2.le⟩
  exact (ActualGaussianCoverage.nativeCutoff_central_germ ActualPrimary.slots.radius_pos
    (ActualCarrierTransportBase.referenceLength_pos (supportLabel l))
    (ActualCarrierTransportBase.clock_pos (supportLabel l) n) hrect hm).comp_tendsto
      (((ActualCarrierTransportBase.geometry (supportLabel l) n).coordinates_contDiff
          k).continuous.comp
        continuous_snd).continuousAt

/-! The uncovered source is zero; it is not estimated without its edge weight. -/

theorem outside_alternative (x : CycleState (Label B N0)) (hs : InputSupport x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (l : Label B N0) (j : ℤ) (n : ℕ) (k : Frequency) {z : Native}
    (hz : z ∈ nativeStrip.domain) (hk : z ∈ (carrierCells l).carrier n k)
    (hn : z ∉ controlPatch l n k) :
    (((data x l j).cutoff n k =ᶠ[𝓝 z] fun _ => 0) ∧
      ((data x l j).source n =ᶠ[𝓝 z] fun _ => 0)) ∨
    (((data x l j).amplitude n k =ᶠ[𝓝 z] fun _ => 0) ∧
      ((data x l j).source n =ᶠ[𝓝 z] fun _ => 0)) := by
  have hnot : (z.1.1,z.2) ∉ ActualCarrierTransportBase.canonicalSourceRegion (supportLabel l) n :=
    fun hreg => hn (sourceRegion_mem_controlPatch hN l n k hz hk hreg)
  have hf := currentSource_zero_germ x hs hN l j n (native_parameter_domain hz) hnot
  rcases data_control_alternative x hs hN l j n k hz hk with hc | hcut | ⟨ha,_,hf'⟩
  · exact (hn hc).elim
  · exact Or.inl ⟨hcut,hf⟩
  · exact Or.inr ⟨ha,hf'⟩

theorem source_complement (x : CycleState (Label B N0)) (hs : InputSupport x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0) (j : ℤ) (β : ℝ) :
    LocalizedGaussianBounds.UniformComplementJets nativeStrip
      (fun _ _ z => Real.sqrt (nativeStrip.zeta z)) β
      (fun l => (carrierCells l).carrier) (fun l => (data x l j).source) := by
  apply LocalizedGaussianBounds.UniformComplementJets.of_zero_germs
  intro l n z hz hn
  apply currentSource_zero_germ x hs hN l j n (native_parameter_domain hz)
  intro hreg
  obtain ⟨k,hk⟩ := mem_iUnion.mp hreg.2
  exact hn k (ActualGaussianCoverage.sourceCell_subset_outer ActualPrimary.slots.radius_pos
    (ActualCarrierTransportBase.referenceLength_pos (supportLabel l))
    (ActualCarrierTransportBase.clock_pos (supportLabel l) n) hk)

/-- Every power gain for the literal particular Gaussian error, with
constants chosen before the original spatial label and band.  The hypotheses
concern the incoming source and its actual support, never the solved error. -/
theorem globalGaussian_all_gains (x : CycleState (Label B N0))
    (hfrequency : ∀ l n, (x.coefficients.blocks l).frequency n = ChartScales.carrier
        ActualPrimary.h n)
    (hs : InputSupport x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    {α : ℝ} (j : ℤ) (hj : j ≠ 0)
    (H : LabelSumBounds.UniformWaveClass nativeStrip nativeEnvelope α (currentSource x j))
    (β : ℝ) :
    LabelSumBounds.UniformClass nativeStrip (fun _ _ z => Real.sqrt (nativeStrip.zeta z)) β
      (fun l => (data x l j).globalGaussian (directions (B := B))) := by
  apply ActualGaussianCoverage.uniform_globalGaussian_weighted_from_supported_native
    (fun l => data x l j) carrierCells (data_cutoff_support x · j)
    (directions (B := B)) controlPatch
    (fun l n z _ => envelope_nonneg l n (z.1.1,z.2))
    (cutoff_jets x j) fast_bound (raw_jets x hfrequency j hj H).1
    (uniform_to_local H controlPatch) bandScales theta gaussianLength gaussianLength_pos
    lengthLower lengthLower_pos gaussianLength_lower (gaussianRate_pos B N0)
    (fun l n k z _ hz => envelope_gaussian l n k hz)
    (fun l n k z _ hz hm => Or.inl (cutoff_central x l j n k hz hm))
    (fun l n k z hz hk hn => outside_alternative x hs hN l j n k hz hk hn)
    β (source_complement x hs hN j β)

/-- The literal finite harmonic Gaussian block inherits the same weighted
all-power estimate.  Its finite modal sum changes the constant, not its
uniformity in the original spatial label and band. -/
theorem gaussianBlock_all_gains (x : CycleState (Label B N0))
    (hfrequency : ∀ l n, (x.coefficients.blocks l).frequency n = ChartScales.carrier
        ActualPrimary.h n)
    (hs : InputSupport x) (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    {α : ℝ} (N : ℕ)
    (H : ∀ j ∈ ParticularWaveAssembly.modes N,
      LabelSumBounds.UniformWaveClass nativeStrip nativeEnvelope α (currentSource x j))
    (β : ℝ) (i : Fin 3) (m : ℤ) :
    LabelSumBounds.UniformClass associatedStrip (fun _ _ z => Real.sqrt (associatedStrip.zeta z)) β
      (fun l n z => ((parameters x l).gaussianBlock (assembly x l).context (assembly x l).state
        (assembly x l).carrierBlock (assembly x l).gaussianInput (assembly x l).aliasInput
            N).velocity
        n i m z) := by
  have hh := UniformBlockBounds.native_assembledBlock_original_uniform
    (s := associatedStrip)
    (w := fun (_ : Label B N0) (_ : ℕ) z => Real.sqrt (nativeStrip.zeta z))
    (α := β) (γ := β) N
    (fun l => (assembly x l).carrierBlock.frequency)
    (fun l => (assembly x l).carrierBlock.phase)
    (fun l => (assembly x l).carrierBlock.angularFrequency)
    (v := fun l j => (data x l j).globalGaussian (directions (B := B)))
    (p := fun _ _ _ _ => (0 : ℂ))
    (fun _ _ _ _ => Real.sqrt_nonneg _)
    (fun j hj => globalGaussian_all_gains x hfrequency hs hN j
      ((ParticularWaveAssembly.mem_modes N j).mp hj).1 (H j hj) β)
    (fun _ _ => LabelSumBounds.UniformClass.zero (fun _ _ _ _ => Real.sqrt_nonneg _))
  exact hh.1 i m

end NavierStokes.ActualParticularGaussian
