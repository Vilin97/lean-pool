/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualMeanPhysicalData
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCycleParameters
public import LeanPool.NavierStokesAndEuler.NavierStokes.CorrectionAnalyticStep
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualWaveRegularityData
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedCoherence
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualParticularCoherence
import LeanPool.NavierStokesAndEuler.NavierStokes.MeanStageRegularity

/-!
# Coherence of the actual correction recurrence

The incoming chart comparisons retain every radial, free auxiliary and
angular variable.  The actual initialized state and labeled coefficients
start the induction together.  The two literal wave constructions supply
the transport used by the mean, pressure, and alias operations.
-/

section

/-!
# Full-fiber coherence of the actual signed Gaussian error

The differentiated native cutoff is transported before the copy sum is
taken.  The source complement is retained, and the same copy index is
used throughout.  The final field is the actual conjugate-pair Gaussian
block, with its full angular variable.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.ActualSignedGaussianCoherence

open Set Function Filter HarmonicCalculus LinearWaveBounds
open CorrectionState CorrectionStep GaugeStateCoherence
open CorrectionInitialization CorrectionInitialization.ActualPrimary
open scoped Topology ContDiff

section EquivariantCutoff

variable {D E I : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The invertible chart transports the actual directional derivative,
including the totalized derivative at a nonsmooth point. -/
theorem fast_cutoff_equiv (e : D ≃L[ℝ] E)
    (d : GraphDirections D) (dr : GraphDirections E)
    (a : PeriodizedWaveBounds.CopyData D I) (b : PeriodizedWaveBounds.CopyData E I)
    (n m : ℕ) (rate : ℝ) (i : I) (x : D)
    (hcutoff : a.cutoff n i = fun y => b.cutoff m i (e y))
    (hfast : e (d.fastField n x) = rate • dr.fastField m (e x)) :
    d.Dfast (fun j => a.cutoff j i) n x =
      rate * dr.Dfast (fun j => b.cutoff j i) m (e x) := by
  have he := PhysicalResidualNaturality.along_pull e 1 rate
    (d.fastField n) (dr.fastField m) (b.cutoff m i) x hfast
  simp only [one_mul, smul_eq_mul] at he
  simpa only [GraphDirections.Dfast, hcutoff] using he

/-- Exact transport of the computed Gaussian error.  Only copies with a
nonzero differentiated reference cutoff require an amplitude comparison. -/
theorem globalGaussian_equiv (e : D ≃L[ℝ] E)
    (d : GraphDirections D) (dr : GraphDirections E)
    (a : PeriodizedWaveBounds.CopyData D I) (b : PeriodizedWaveBounds.CopyData E I)
    (n m : ℕ) (rate c : ℝ) (x : D)
    (hcutoff : ∀ i, a.cutoff n i = fun y => b.cutoff m i (e y))
    (hfast : e (d.fastField n x) = rate • dr.fastField m (e x))
    (hamplitude : ∀ i, dr.Dfast (fun j => b.cutoff j i) m (e x) ≠ 0 →
      a.amplitude n i x = c • b.amplitude m i (e x))
    (hsource : a.source n x = (rate * c) • b.source m (e x)) :
    a.globalGaussian d n x = (rate * c) • b.globalGaussian dr m (e x) := by
  have htail (i : I) : a.localTail d n i x =
      (rate * c) • b.localTail dr m i (e x) := by
    unfold PeriodizedWaveBounds.CopyData.localTail
    rw [fast_cutoff_equiv e d dr a b n m rate i x (hcutoff i) hfast]
    by_cases hz : dr.Dfast (fun j => b.cutoff j i) m (e x) = 0
    · simp only [hz, mul_zero, zero_smul, smul_zero]
    · rw [hamplitude i hz, smul_smul, smul_smul]
      congr 1
      ring
  have hsum : a.globalTail d n x = (rate * c) • b.globalTail dr m (e x) := by
    change (∑' i, a.localTail d n i x) = (rate * c) • ∑' i, b.localTail dr m i (e x)
    calc
      _ = ∑' i, (rate * c) • b.localTail dr m i (e x) := tsum_congr htail
      _ = _ := tsum_const_smul'' (rate * c)
  have hcut : a.cutoffSum n x = b.cutoffSum m (e x) :=
    tsum_congr (fun i => congrFun (hcutoff i) x)
  rw [PeriodizedWaveBounds.CopyData.globalGaussian, hsum, hcut, hsource]
  simp only [PeriodizedWaveBounds.CopyData.globalGaussian, smul_add, smul_smul]
  congr 1
  congr 1
  ring

end EquivariantCutoff

/-- Exchanging the two bands inverts the physical Gaussian weight. -/
theorem gaussianWeight_swap (exponent : ℝ) (n m : ℕ) :
    (bandVelocityScale exponent n m * bandVelocityScale exponent n m * bandScale n m)⁻¹ =
      bandVelocityScale exponent m n * bandVelocityScale exponent m n * bandScale m n := by
  have hr : ChartScales.Q m / ChartScales.Q n = (ChartScales.Q n / ChartScales.Q m)⁻¹ :=
    (inv_div _ _).symm
  unfold bandVelocityScale bandScale
  simp only [hr, Real.inv_rpow (div_nonneg (ChartScales.Q_pos n).le (ChartScales.Q_pos m).le),
    mul_inv_rev]
  ring

section ActualFourierField

variable {B N0 : ℕ}

/-- Expansion of the literal Gaussian block at an arbitrary angle.  The
coefficient is the actual periodized error on the zero-angle section. -/
theorem gaussianBlock_formula
    (l : ActualSignedStageControls.SignedLabel B N0)
    (s : WeightedClasses.StripData LocalSignedRequest.Point)
    (request : ℕ → LocalSignedRequest.Point × ℝ → SignedWaveUpdate.Vec2)
    (n : ℕ) (x : LocalSignedRequest.Point) (theta : ℝ) (i : Fin 3) :
    ((ActualSignedStageControls.parameters l).gaussianBlock s request).oscillation n (x,theta) i =
      (((ActualSignedStageControls.parameters l).copyData s request).globalGaussian
        (ActualSignedStageControls.directions B) n (x,0) i *
        HarmonicFields.character 1
          ((chartCoefficients l.2 l.1).frequency n * (chartCoefficients l.2 l.1).phase n (x,0) +
            (((ActualSignedStageControls.parameters l).angularFrequency n : ℤ) : ℝ) * theta)).re :=
                by
  exact SignedWaveUpdate.coefficientBlock_velocity _ _ _ _ _ n (x,theta) i

private theorem gaussianBlock_field_transport
    (l : ActualSignedStageControls.SignedLabel B N0)
    (s : WeightedClasses.StripData LocalSignedRequest.Point)
    (request : ℕ → LocalSignedRequest.Point × ℝ → SignedWaveUpdate.Vec2)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (x : LocalSignedRequest.Point) (theta a : ℝ) (i : Fin 3)
    (hg : ((ActualSignedStageControls.parameters l).copyData s request).globalGaussian
        (ActualSignedStageControls.directions B) n (x, 0) =
      a • ((ActualSignedStageControls.parameters l).copyData s request).globalGaussian
        (ActualSignedStageControls.directions B) m (bandChartEquiv h n m k x, 0)) :
    ((ActualSignedStageControls.parameters l).gaussianBlock s request).oscillation n (x,theta) i =
      a * ((ActualSignedStageControls.parameters l).gaussianBlock s request).oscillation
        m (bandChartEquiv h n m k x,theta) i := by
  rw [gaussianBlock_formula, gaussianBlock_formula, hg]
  have hp := ActualInitialCoherence.block_phase_band l n m k hi x
  change (chartCoefficients l.2 l.1).frequency n * (chartCoefficients l.2 l.1).phase n (x,0) =
    (chartCoefficients l.2 l.1).frequency m *
      (chartCoefficients l.2 l.1).phase m (bandChartEquiv h n m k x,0) at hp
  rw [hp]
  rw [show (ActualSignedStageControls.parameters l).angularFrequency n =
    (ActualSignedStageControls.parameters l).angularFrequency m from rfl]
  simp only [Pi.smul_apply, Complex.real_smul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

end ActualFourierField

section ActualTransport

open ActualSignedCoherence

variable {B N0 : ℕ}

/-- The signed request is the only coefficient input to this comparison.
The same literal native copy and cutoff occur on both sides. -/
theorem gaussian_transport_of_request (l : SignedLabel B N0) (u : State Point)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (x : ActualSignedCoherence.FullPoint)
    (hR : request B u n x = coefficientWeight n m ^ 2 • request B u m (chart n m k x)) :
    (copies l u).globalGaussian (ActualSignedStageControls.directions B) n x =
      (bandVelocityScale h n m * bandVelocityScale h n m * bandScale n m) •
        (copies l u).globalGaussian (ActualSignedStageControls.directions B) m (chart n m k x) := by
  have he := globalGaussian_equiv (chart n m k)
    (ActualSignedStageControls.directions B) (ActualSignedStageControls.directions B)
    (copies l u) (copies l u) n m (clockWeight n m) (bandVelocityScale h n m) x
    (fun copy => funext (fun y => cutoff_transport l n m k hi copy y))
    (chart_fast n m k hi x)
    (fun copy _ => raw_amplitude_of_request l u n m k hi copy x hR)
    (by change (0 : ComplexVector) = _ • 0; simp only [smul_zero])
  have hw : clockWeight n m * bandVelocityScale h n m =
      bandVelocityScale h n m * bandVelocityScale h n m * bandScale n m := by
    rw [clockWeight_eq]
    ring
  simpa only [hw] using he

/-- Full-fiber covariance derived from the actual incoming state and
primitive identities. No covariance of a signed output is assumed. -/
theorem gaussian_transport (l : SignedLabel B N0) (u : State Point)
    (H : MeanStateRegularity.PrimitiveData ActualInitialization.geometry.region
      ActualInitialization.geometry.patch.a ActualInitialization.geometry.patch.b (commonContext B)
          u)
    (hfixed : (VariableGaugeMean.reconstructState ActualInitialization.geometry.gauge
      (commonContext B) u).pressure = u.pressure)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (HS : PhysicalResidualNaturality.StateOn
      (PhysicalMeanDomain.slowDomain (ActualInitialCoherence.overlap n m))
      (bandChartEquiv h n m k) (bandVelocityScale h n m) (bandScale n m) u u n m)
    (x : ActualSignedCoherence.FullPoint) (hx : x.1.2.1 ∈ ActualInitialCoherence.overlap n m) :
    (copies l u).globalGaussian (ActualSignedStageControls.directions B) n x =
      (bandVelocityScale h n m * bandVelocityScale h n m * bandScale n m) •
        (copies l u).globalGaussian (ActualSignedStageControls.directions B) m (chart n m k x) :=
  gaussian_transport_of_request l u n m k hi x
    (fullRequest_transport u H hfixed n m k hi HS x hx)

/-- Reverse transport of the actual complex Gaussian coefficient on the
image of the same overlap, with the reciprocal physical weight. -/
theorem gaussian_transport_symm (l : SignedLabel B N0) (u : State Point)
    (H : MeanStateRegularity.PrimitiveData ActualInitialization.geometry.region
      ActualInitialization.geometry.patch.a ActualInitialization.geometry.patch.b (commonContext B)
          u)
    (hfixed : (VariableGaugeMean.reconstructState ActualInitialization.geometry.gauge
      (commonContext B) u).pressure = u.pressure)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (HS : PhysicalResidualNaturality.StateOn
      (PhysicalMeanDomain.slowDomain (ActualInitialCoherence.overlap n m))
      (bandChartEquiv h n m k) (bandVelocityScale h n m) (bandScale n m) u u n m)
    (x : ActualSignedCoherence.FullPoint)
    (hx : ((chart n m k).symm x).1.2.1 ∈ ActualInitialCoherence.overlap n m) :
    (copies l u).globalGaussian (ActualSignedStageControls.directions B) m x =
      (bandVelocityScale h m n * bandVelocityScale h m n * bandScale m n) •
        (copies l u).globalGaussian (ActualSignedStageControls.directions B) n ((chart n m k).symm
            x) := by
  have he := gaussian_transport l u H hfixed n m k hi HS ((chart n m k).symm x) hx
  have hw : bandVelocityScale h n m * bandVelocityScale h n m * bandScale n m ≠ 0 :=
    mul_ne_zero (mul_ne_zero (velocity_pos n m).ne' (velocity_pos n m).ne')
      (bandScale_pos n m).ne'
  have he' := congrArg (fun z : ComplexVector =>
    (bandVelocityScale h n m * bandVelocityScale h n m * bandScale n m)⁻¹ • z) he
  have he'' := he'.symm
  simp only [ContinuousLinearEquiv.apply_symm_apply, smul_smul,
    inv_mul_cancel₀ hw, one_smul] at he''
  simpa only [gaussianWeight_swap] using he''

/-- The Gaussian component of `WaveOn`, for the actual signed Fourier
block, on all radial and free auxiliary fibers and at every angle. -/
theorem gaussianBlock_transport (l : SignedLabel B N0) (u : State Point)
    (H : MeanStateRegularity.PrimitiveData ActualInitialization.geometry.region
      ActualInitialization.geometry.patch.a ActualInitialization.geometry.patch.b (commonContext B)
          u)
    (hfixed : (VariableGaugeMean.reconstructState ActualInitialization.geometry.gauge
      (commonContext B) u).pressure = u.pressure)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (HS : PhysicalResidualNaturality.StateOn
      (PhysicalMeanDomain.slowDomain (ActualInitialCoherence.overlap n m))
      (bandChartEquiv h n m k) (bandVelocityScale h n m) (bandScale n m) u u n m)
    (x : Point) (hx : x ∈ PhysicalMeanDomain.slowDomain (ActualInitialCoherence.overlap n m))
    (theta : ℝ) (i : Fin 3) :
    ((ActualSignedStageControls.parameters l).gaussianBlock ActualInitialization.geometry.strip
      (request B u)).oscillation n (x,theta) i =
      (bandVelocityScale h n m * bandVelocityScale h n m * bandScale n m) *
        ((ActualSignedStageControls.parameters l).gaussianBlock ActualInitialization.geometry.strip
          (request B u)).oscillation m (bandChartEquiv h n m k x,theta) i := by
  apply gaussianBlock_field_transport l ActualInitialization.geometry.strip (request B u)
    n m k hi x theta _ i
  exact gaussian_transport l u H hfixed n m k hi HS (x,0) hx

/-- The same field comparison in the reverse common-chart direction.
Its domain is the exact image of the forward overlap. -/
theorem gaussianBlock_transport_symm (l : SignedLabel B N0) (u : State Point)
    (H : MeanStateRegularity.PrimitiveData ActualInitialization.geometry.region
      ActualInitialization.geometry.patch.a ActualInitialization.geometry.patch.b (commonContext B)
          u)
    (hfixed : (VariableGaugeMean.reconstructState ActualInitialization.geometry.gauge
      (commonContext B) u).pressure = u.pressure)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (HS : PhysicalResidualNaturality.StateOn
      (PhysicalMeanDomain.slowDomain (ActualInitialCoherence.overlap n m))
      (bandChartEquiv h n m k) (bandVelocityScale h n m) (bandScale n m) u u n m)
    (x : Point)
    (hx : (bandChartEquiv h n m k).symm x ∈
      PhysicalMeanDomain.slowDomain (ActualInitialCoherence.overlap n m))
    (theta : ℝ) (i : Fin 3) :
    ((ActualSignedStageControls.parameters l).gaussianBlock ActualInitialization.geometry.strip
      (request B u)).oscillation m (x,theta) i =
      (bandVelocityScale h m n * bandVelocityScale h m n * bandScale m n) *
        ((ActualSignedStageControls.parameters l).gaussianBlock ActualInitialization.geometry.strip
          (request B u)).oscillation n ((bandChartEquiv h n m k).symm x,theta) i := by
  have he := gaussianBlock_transport l u H hfixed n m k hi HS
    ((bandChartEquiv h n m k).symm x) hx theta i
  have hw : bandVelocityScale h n m * bandVelocityScale h n m * bandScale n m ≠ 0 :=
    mul_ne_zero (mul_ne_zero (velocity_pos n m).ne' (velocity_pos n m).ne')
      (bandScale_pos n m).ne'
  have he' := congrArg (fun z : ℝ =>
    (bandVelocityScale h n m * bandVelocityScale h n m * bandScale n m)⁻¹ * z) he
  have he'' := he'.symm
  simp only [ContinuousLinearEquiv.apply_symm_apply, ← mul_assoc,
    inv_mul_cancel₀ hw, one_mul] at he''
  simpa only [gaussianWeight_swap] using he''

end ActualTransport

end NavierStokes.ActualSignedGaussianCoherence

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.ActualCycleCoherence

open Set Function Filter CorrectionState CorrectionStep
open PhysicalResidualNaturality GaugeStateCoherence
open CorrectionInitialization CorrectionInitialization.ActualPrimary
open scoped ContDiff Topology BigOperators

/-- Point: an abbreviation for `ActualInitialization.Point`. -/
abbrev Point := ActualInitialization.Point
/-- Index: an abbreviation for `ActualInitialization.Index`. -/
abbrev Index := ActualInitialization.Index
/-- Geometry: an abbreviation for `ActualMeanPhysicalData.initialGeometry`. -/
abbrev geometry := ActualMeanPhysicalData.initialGeometry
/-- Overlap: an abbreviation for `ActualInitialCoherence.overlap`. -/
abbrev overlap := ActualInitialCoherence.overlap

/-- Every comparison is on the intersection of the two actual normalized
slow charts; the radial and torus fibers are unrestricted. -/
def StateCoherent (u : State Point) : Prop :=
  ∀ n m k, CommonWindow.index h n + k = CommonWindow.index h m →
    StateOn (PhysicalMeanDomain.slowDomain (overlap n m))
      (bandChartEquiv h n m k) (bandVelocityScale h n m) (bandScale n m) u u n m

/-- Individual input fields are compared, including the Gaussian and
nonzero harmonic alias inputs used by the next particular solve. -/
def BlocksCoherent {ι : Type} (v : CycleCoefficients ι) : Prop :=
  ∀ l n m k, CommonWindow.index h n + k = CommonWindow.index h m →
    BlockFieldsOn (PhysicalMeanDomain.slowDomain (overlap n m))
      (bandChartEquiv h n m k) (bandVelocityScale h n m) (bandScale n m)
      (v.blocks l) (v.blocks l) (v.gaussian l) (v.aliasCoefficients l)
      (v.gaussian l) (v.aliasCoefficients l) n m

/-- Axis coherent, given by `∀ n m k, CommonWindow.index h n + k = CommonWindow.index h m →
CycleStateCoherence.AxisBand geometry (overlap n m) n m k a`. -/
def AxisCoherent (a : AxisymmetricAlias) : Prop :=
  ∀ n m k, CommonWindow.index h n + k = CommonWindow.index h m →
    CycleStateCoherence.AxisBand geometry (overlap n m) n m k a

/-- The geometric induction invariant, separate from all quantitative
residual estimates.  The label set is the initializer's fixed choice. -/
structure Coherent {B N0 : ℕ} (x : CycleState (Index B N0)) : Prop where
  state : StateCoherent x.state
  blocks : BlocksCoherent x.coefficients
  axis : AxisCoherent x.axisymmetricAlias
  labels : x.coefficients.labels = activeLabels standardRegion B N0

theorem realizes (B N0 : ℕ) :
    CycleStateCoherence.Realizes geometry (ActualCycleParameters.fixedParameters B N0)
      (commonContext B) :=
  ActualMeanPhysicalData.initial_realizes B _ _

theorem context (B n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m) :
    CycleStateCoherence.ContextBand geometry (overlap n m) n m k (commonContext B) :=
  ActualInitialCoherence.context_band B
    (fun s hs => standardRegion.time_pos s hs.1) n m k hi

theorem initial_state (B N0 : ℕ) : StateCoherent (ActualInitialization.initialState B N0) :=
  ActualInitialization.initial_on_overlap B N0

theorem initial_blocks (B N0 : ℕ) : BlocksCoherent (ActualInitialization.coefficients B N0) := by
  intro l n m k hi
  exact ActualInitialCoherence.blockFields_band l
    (PhysicalMeanDomain.slowDomain (overlap n m)) n m k hi

theorem initial_axis (B N0 : ℕ) : AxisCoherent (ActualInitialization.initialAlias B N0) := by
  intro n m k hi x hx i
  have H := (ActualInitialization.initial_on_overlap B N0 n m k hi).aliasError x hx 0 i
  rw [(ActualInitialization.initialState_error_components B N0).2.2] at H
  exact H

theorem initial (B N0 : ℕ) : Coherent (ActualInitialization.initialCycleState B N0) :=
  ⟨initial_state B N0, initial_blocks B N0, initial_axis B N0, rfl⟩

theorem BlocksCoherent.reindex {ι κ : Type} (e : κ ≃ ι) {v : CycleCoefficients ι}
    (H : BlocksCoherent v) : BlocksCoherent (ActualCycleParameters.reindexCoefficients e v) := by
  intro l n m k hi
  exact H (e l) n m k hi

theorem Coherent.particular_state {B N0 : ℕ} {x : CycleState (Index B N0)} (H : Coherent x) :
    StateCoherent (ActualCycleParameters.particularState x).state := H.state

theorem Coherent.particular_blocks {B N0 : ℕ} {x : CycleState (Index B N0)} (H : Coherent x) :
    BlocksCoherent (ActualCycleParameters.particularState x).coefficients :=
  H.blocks.reindex (ActualCycleParameters.swap B N0).symm

theorem StateCoherent.atlas {u : State Point} (H : StateCoherent u) (N : ℕ) :
    (ActualMeanPhysicalData.initialAtlas N).StateOverlap standardRegion.carrier u :=
  fun n _ m _ k hi => H n m k hi

theorem Coherent.reference_state {B N0 : ℕ} {x : CycleState (Index B N0)} (H : Coherent x)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m) :
    ActualReferenceRebase.StateComparison (ActualCycleParameters.particularState x)
      (overlap n m) n m k := H.state n m k hi

theorem Coherent.reference_block {B N0 : ℕ} {x : CycleState (Index B N0)} (H : Coherent x)
    (l : ActualParticularStageControls.Label B N0) (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m) :
    ActualReferenceRebase.BlockComparison (ActualCycleParameters.particularState x) l
      (overlap n m) n m k :=
  H.blocks ((ActualCycleParameters.swap B N0).symm l) n m k hi

/-! ## Omitted labels vanish by their primitive support and zero modes -/

theorem field_zero_of_support {U K : Set Point}
    (a : HarmonicFields.Coefficients Point)
    (hs : HarmonicSourceSupport.NonzeroSupportedOn U K (HarmonicResidual.realCoefficients a))
    (hzero : a 0 = 0) (frequency : ℝ) (phase : Point → ℝ) (angular : ℤ)
    {x : Point} (hx : x ∈ U) (hn : x ∉ K) (theta : ℝ) :
    (HarmonicFields.field a frequency phase angular (x, theta)).re = 0 := by
  have hc (j : ℤ) : HarmonicResidual.realCoefficients a j x = 0 := by
    by_cases hj : j = 0
    · subst j
      simp [HarmonicResidual.realCoefficients_apply, hzero]
    · exact hs j hj x hx hn
  have he : HarmonicFields.field (HarmonicResidual.realCoefficients a)
      frequency phase angular (x, theta) = 0 := by
    rw [HarmonicFields.field_expansion]
    apply Finset.sum_eq_zero
    intro j hj
    rw [hc, zero_mul, zero_mul]
  rw [HarmonicResidual.field_realCoefficients] at he
  exact Complex.ofReal_eq_zero.mp he

theorem wave_fields_zero_of_support {U : Set Point} {K : ℕ → Set Point}
    (b g : HarmonicBlock Point)
    (hs : HarmonicSourceSupport.InputSupportOn U K b g.velocity 0)
    (hv : HarmonicWaveInteraction.ZeroMode b)
    (hp : ∀ n, b.pressure n 0 = 0)
    (hg : HarmonicWaveInteraction.ZeroMode g)
    (n : ℕ) {x : Point} (hx : x ∈ U) (hn : x ∉ K n) (theta : ℝ) :
    b.oscillation n (x, theta) = 0 ∧ b.oscillatoryPressure n (x, theta) = 0 ∧
      g.oscillation n (x, theta) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · funext i
    exact field_zero_of_support (b.velocity n i) (hs.velocity n i) (hv n i)
      (b.frequency n) (b.phase n) (b.angularFrequency n) hx hn theta
  · exact field_zero_of_support (b.pressure n) (hs.pressure n) (hp n)
      (b.frequency n) (b.phase n) (b.angularFrequency n) hx hn theta
  · funext i
    exact field_zero_of_support (g.velocity n i) (hs.gaussian n i) (hg n i)
      (g.frequency n) (g.phase n) (g.angularFrequency n) hx hn theta

theorem label_waves_of_support {ι : Type}
    (labels : ℕ → Finset ι) (b g : ι → HarmonicBlock Point) (S : ι → ℕ → Set Point)
    (hs : ∀ l, HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain
      (S l) (b l) (g l).velocity 0)
    (hv : ∀ l, HarmonicWaveInteraction.ZeroMode (b l))
    (hp : ∀ l n, (b l).pressure n 0 = 0)
    (hg : ∀ l, HarmonicWaveInteraction.ZeroMode (g l))
    (hcover : ∀ l n x, x ∈ ActualInitialization.geometry.domain → x ∈ S l n → l ∈ labels n)
    (n m k : ℕ)
    (HW : ∀ l, CycleStateCoherence.WaveOn (PhysicalMeanDomain.slowDomain (overlap n m))
      (bandChartEquiv h n m k) (bandVelocityScale h n m) (bandScale n m)
      (b l).oscillation (b l).oscillatoryPressure (g l).oscillation
      (b l).oscillation (b l).oscillatoryPressure (g l).oscillation n m) :
    CycleStateCoherence.LabelWavesOn (PhysicalMeanDomain.slowDomain (overlap n m))
      (bandChartEquiv h n m k) (bandVelocityScale h n m) (bandScale n m)
      labels b g n m := by
  refine ⟨HW, ?_, ?_⟩
  · intro l hl x hx theta
    have hxU : x ∈ ActualInitialization.geometry.domain := hx.1
    exact wave_fields_zero_of_support (b l) (g l) (hs l) (hv l) (hp l) (hg l) n hxU
      (fun h => hl (hcover l n x hxU h)) theta
  · intro l hl x hx theta
    have hxU : bandChartEquiv h n m k x ∈ ActualInitialization.geometry.domain := hx.2
    exact wave_fields_zero_of_support (b l) (g l) (hs l) (hv l) (hp l) (hg l) m hxU
      (fun h => hl (hcover l m _ hxU h)) theta

/-! ## The actual source on every fast-variable fiber -/

/-- Particular source, constructed using `ParticularWaveAssembly.residualSource`. -/
noncomputable def particularSource {B N0 : ℕ} (x : CycleState (Index B N0))
    (l : ActualParticularStageControls.Label B N0) (j : ℤ) (n : ℕ) :
    PhysicalParticularWave.Parameter × PressureStream.Plane → HarmonicCalculus.ComplexVector :=
  ParticularWaveAssembly.residualSource (commonContext B) x.state
    (x.coefficients.blocks (l.2,l.1)) (x.coefficients.gaussian (l.2,l.1))
    (x.coefficients.aliasCoefficients (l.2,l.1)) j n ∘ cycleAssoc.symm

theorem particularSource_eq {B N0 : ℕ} (x : CycleState (Index B N0))
    (l : ActualParticularStageControls.Label B N0) (j : ℤ) (n : ℕ) :
    particularSource x l j n = ParticularWaveAssembly.residualSource
      (ActualParticularStageControls.assembly (ActualCycleParameters.particularState x) l).context
      (ActualParticularStageControls.assembly (ActualCycleParameters.particularState x) l).state
      (ActualParticularStageControls.assembly (ActualCycleParameters.particularState x)
          l).carrierBlock
      (ActualParticularStageControls.assembly (ActualCycleParameters.particularState x)
          l).gaussianInput
      (ActualParticularStageControls.assembly (ActualCycleParameters.particularState x)
          l).aliasInput j n := by
  funext z
  exact (ActualReferenceRebase.assembly_source (ActualCycleParameters.particularState x) l j n
      z).symm

theorem core_ordered {B N0 : ℕ} (l : Index B N0) (n : ℕ) {z : Point}
    (hz : z ∈ ActualInitialization.geometry.domain)
    (hc : z ∈ ActualCoreSupport.refinedCarrier l n) :
    ActualWaveRegularityData.Ordered l n := by
  have hT := standardRegion.time_pos z.2.1 hz
  have hq := ((ActualCoreSupport.mem_refinedCarrier_iff l n hT).mp hc).2.2
  change SimilarityHomogeneity.chartQ h (nativeSlow l.1 (toAbsolute n z)) ∈ _ at hq
  rw [nativeSlow_toAbsolute_eq_slowChange] at hq
  exact ActualWaveRegularityData.ordered_of_native_band l n
    (p := BaseContextAssembly.slowCoordinates z) hT hz.2 hq

theorem core_radius_pos {B N0 : ℕ} (l : Index B N0) (n : ℕ) {z : Point}
    (hz : z ∈ ActualInitialization.geometry.domain)
    (hc : z ∈ ActualCoreSupport.refinedCarrier l n) : 0 < z.1 := by
  have hT := standardRegion.time_pos z.2.1 hz
  have hr := ((ActualCoreSupport.mem_refinedCarrier_iff l n hT).mp hc).2.1.1
  have hlen := VariableGaugeMean.qLength_pos standardRegion.coord_pos standardRegion.coord_lt_one hT
  have hratio := (PrimaryTargetBounds.leftRadius_pos nominal).trans_le hr
  exact (div_pos_iff_of_pos_right hlen).mp hratio

/-- All three fields of the actual signed insertion transform on the
same overlap.  The Gaussian term is the differentiated-cutoff error. -/
theorem signed_wave_on {B N0 : ℕ} (l : Index B N0) (u : State Point)
    (H : MeanStateRegularity.PrimitiveData ActualInitialization.geometry.region
      ActualInitialization.geometry.patch.a ActualInitialization.geometry.patch.b (commonContext B)
          u)
    (hfixed : (VariableGaugeMean.reconstructState ActualInitialization.geometry.gauge
      (commonContext B) u).pressure = u.pressure)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (HS : StateOn (PhysicalMeanDomain.slowDomain (overlap n m))
      (bandChartEquiv h n m k) (bandVelocityScale h n m) (bandScale n m) u u n m) :
    CycleStateCoherence.WaveOn (PhysicalMeanDomain.slowDomain (overlap n m))
      (bandChartEquiv h n m k) (bandVelocityScale h n m) (bandScale n m)
      ((ActualSignedStageControls.parameters l).exactBlock ActualInitialization.geometry.strip
        (ActualSignedCoherence.request B u)).oscillation
      ((ActualSignedStageControls.parameters l).exactBlock ActualInitialization.geometry.strip
        (ActualSignedCoherence.request B u)).oscillatoryPressure
      ((ActualSignedStageControls.parameters l).gaussianBlock ActualInitialization.geometry.strip
        (ActualSignedCoherence.request B u)).oscillation
      ((ActualSignedStageControls.parameters l).exactBlock ActualInitialization.geometry.strip
        (ActualSignedCoherence.request B u)).oscillation
      ((ActualSignedStageControls.parameters l).exactBlock ActualInitialization.geometry.strip
        (ActualSignedCoherence.request B u)).oscillatoryPressure
      ((ActualSignedStageControls.parameters l).gaussianBlock ActualInitialization.geometry.strip
        (ActualSignedCoherence.request B u)).oscillation n m :=
  ⟨ActualSignedCoherence.exactBlock_velocity_transport l u H hfixed n m k hi HS,
    ActualSignedCoherence.exactBlock_pressure_transport l u H hfixed n m k hi HS,
    ActualSignedGaussianCoherence.gaussianBlock_transport l u H hfixed n m k hi HS⟩

/-- Particular point, given by `ParticularWaveAssembly.angleShuffle (cycleAssoc z, 0)`. -/
noncomputable def particularPoint (z : Point) : PhysicalParticularWave.WaveSpace :=
  ParticularWaveAssembly.angleShuffle (cycleAssoc z, 0)

theorem particularPoint_chart (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m) (z : Point) :
    ActualParticularCoherence.bandMap n m (particularPoint z) =
      particularPoint (bandChartEquiv h n m k z) := by
  rw [ActualParticularCoherence.bandMap_apply n m k hi]
  have he := congrArg cycleAssoc
    (ActualReferenceRebase.associatedChart_stateChart n m k (cycleAssoc z))
  simp only [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.symm_apply_apply] at he
  exact congrArg (fun y : PhysicalResidualNaturality.Associated =>
    ParticularWaveAssembly.angleShuffle (y,0)) he

theorem particular_pressure_weight (n m : ℕ) :
    PhysicalParticularWave.pressureWeight h (ChartScales.Q n) (ChartScales.Q m) =
      bandVelocityScale h n m * bandVelocityScale h n m := by
  rw [← ActualSignedCoherence.velocityWeight_eq, PhysicalParticularWave.velocityWeight,
    PhysicalParticularWave.ratioPower_mul (ChartScales.Q_pos n) (ChartScales.Q_pos m)]
  unfold PhysicalParticularWave.pressureWeight
  congr 1
  ring

theorem literal_particular_velocity {B N0 : ℕ} (x : CycleState (Index B N0))
    (l : Index B N0) (n : ℕ) (z : Point) (theta : ℝ) (i : Fin 3) :
    ((ActualCycleParameters.parameters x).particularBlock x.coefficients (commonContext B)
      x.state l).oscillation n (z,theta) i =
      ∑ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand,
        ((ActualParticularCoherence.corrected (ActualCycleParameters.particularState x)
          (l.2,l.1) j).amplitude n (particularPoint z) i * HarmonicFields.character j
          ((x.coefficients.blocks l).frequency n * (x.coefficients.blocks l).phase n z +
            ((x.coefficients.blocks l).angularFrequency n : ℝ) * theta)).re := by
  simp only [CycleParameters.particularBlock, StateReindex.block_oscillation,
    StateReindex.oscillation, StateReindex.cylinder, ParticularParameters.updateBlock,
    ParticularWaveAssembly.assembledBlock_value]
  rfl

theorem literal_particular_pressure {B N0 : ℕ} (x : CycleState (Index B N0))
    (l : Index B N0) (n : ℕ) (z : Point) (theta : ℝ) :
    ((ActualCycleParameters.parameters x).particularBlock x.coefficients (commonContext B)
      x.state l).oscillatoryPressure n (z,theta) =
      ∑ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand,
        ((ActualParticularCoherence.corrected (ActualCycleParameters.particularState x)
          (l.2,l.1) j).pressure n (particularPoint z) * HarmonicFields.character j
          ((x.coefficients.blocks l).frequency n * (x.coefficients.blocks l).phase n z +
            ((x.coefficients.blocks l).angularFrequency n : ℝ) * theta)).re := by
  simp only [CycleParameters.particularBlock, StateReindex.block_pressure,
    StateReindex.cylinder, ParticularParameters.updateBlock,
    ParticularWaveAssembly.assembledBlock_pressure_value]
  rfl

theorem literal_particular_gaussian {B N0 : ℕ} (x : CycleState (Index B N0))
    (l : Index B N0) (n : ℕ) (z : Point) (theta : ℝ) (i : Fin 3) :
    ((ActualCycleParameters.parameters x).particularGaussianBlock x.coefficients (commonContext B)
      x.state l).oscillation n (z,theta) i =
      ∑ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand,
        ((ActualParticularCoherence.copyData (ActualCycleParameters.particularState x)
          (l.2,l.1) j).globalGaussian (ActualParticularStageControls.directions (B := B))
            n (particularPoint z) i * HarmonicFields.character j
          ((x.coefficients.blocks l).frequency n * (x.coefficients.blocks l).phase n z +
            ((x.coefficients.blocks l).angularFrequency n : ℝ) * theta)).re := by
  simp only [CycleParameters.particularGaussianBlock, StateReindex.block_oscillation,
    StateReindex.oscillation, StateReindex.cylinder, ParticularParameters.gaussianBlock,
    ParticularWaveAssembly.assembledBlock_value]
  rfl

/-! ## Algebraic propagation after the two actual wave laws are derived -/

section Step

variable {B N0 : ℕ} {σ : ℝ} {x : CycleState (Index B N0)}
  {S : Index B N0 → ℕ → Set Point}
  (H : CycleAnalyticInvariant ActualInitialization.geometry (commonContext B)
    ActualInitialization.tangentBlock ActualInitialization.envelope S σ x)
  (W : CorrectionAnalyticStep.WaveData ActualInitialization.geometry
    (ActualCycleParameters.fixedParameters B N0) x.coefficients (commonContext B) x.state
    ActualInitialization.envelope S σ ChartScales.kappa)

include H in
theorem source_support (hS : ∀ l n, IsClosed (S l n))
    (l : ActualParticularStageControls.Label B N0) (j : ℤ) (n : ℕ)
    {p : PhysicalParticularWave.Parameter} (hp : p.2 ∈ standardRegion.carrier)
    {Y : PressureStream.Plane} (hne : particularSource x l j n (p, Y) ≠ 0) :
    cycleAssoc.symm (p,Y) ∈ S (l.2,l.1) n := by
  by_contra hn
  exact hne (HarmonicSourceSupport.residualSource_zero_germ_on (commonContext B) x.state
    (x.coefficients.blocks (l.2,l.1)) (x.coefficients.gaussian (l.2,l.1))
    (x.coefficients.aliasCoefficients (l.2,l.1)) ActualInitialization.geometry.domain_open
    (hS (l.2,l.1)) (H.inputSupport (l.2,l.1)) j n hp hn).self_of_nhds

include H in
theorem source_positive_smooth (l : Index B N0) (j : ℤ) (n : ℕ) :
    ContDiffOn ℝ ∞ (ParticularWaveAssembly.residualSource (commonContext B) x.state
      (x.coefficients.blocks l) (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l) j
          n)
      (LocalRankDefect.positiveDomain standardRegion.carrier) := by
  let U := LocalRankDefect.positiveDomain standardRegion.carrier
  have hu : U ⊆ ActualInitialization.geometry.domain := fun _ hz => hz.2
  have hf : (HarmonicResidual.contextFrame (commonContext B) n).Regular U :=
    HarmonicResidual.contextFrame_regular (commonContext B) n contDiffOn_fst
      (fun z hz => hz.1.ne') H.primitives.operators.regular.radialProfile
  have hb (i : Fin 3) : ContDiffOn ℝ ∞
      (fun z => HarmonicResidual.contextBase (commonContext B) n z i) U := by
    fin_cases i
    · exact Complex.ofRealCLM.contDiff.comp_contDiffOn (H.primitives.base.smooth.radial n)
    · exact Complex.ofRealCLM.contDiff.comp_contDiffOn (H.primitives.base.smooth.angular n)
    · exact Complex.ofRealCLM.contDiff.comp_contDiffOn (H.primitives.base.smooth.axial n)
  have hm (i : Fin 3) : ContDiffOn ℝ ∞
      (fun z => HarmonicResidual.stateMean x.state n z i) U := by
    fin_cases i
    · exact Complex.ofRealCLM.contDiff.comp_contDiffOn ((H.primitives.mean.radial.smooth n).mono hu)
    · exact Complex.ofRealCLM.contDiff.comp_contDiffOn ((H.primitives.mean.angular.smooth n).mono
        hu)
    · exact Complex.ofRealCLM.contDiff.comp_contDiffOn ((H.primitives.mean.axial.smooth n).mono hu)
  have hp : ContDiffOn ℝ ∞ ((x.coefficients.blocks l).phase n) U := by
    rw [← (H.carrier l).phase]
    exact (ActualPrimaryCoherence.chart_phase_smooth l.2 l.1 n).comp
      (HarmonicWaveInteraction.inclusion (D := Point)).contDiff.contDiffOn
      (fun z hz => ⟨hz.1, standardRegion.time_pos z.2.1 hz.2⟩)
  have hd : (HarmonicResidual.ofBlock (x.coefficients.blocks l)
      (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l) n).Regular U :=
    ⟨hp, fun i => (show HarmonicResidual.SmoothCoefficients U
      ((x.coefficients.blocks l).velocity n i) from fun k => (H.coefficientSmooth l n i k).mono
          hu).realCoefficients,
      (show HarmonicResidual.SmoothCoefficients U
      ((x.coefficients.blocks l).pressure n) from fun k => (H.pressureCoefficientSmooth l n k).mono
          hu).realCoefficients⟩
  have hg (i : Fin 3) : HarmonicResidual.SmoothCoefficients U
      (x.coefficients.gaussian l n i) := fun k => (H.gaussianCoefficientSmooth l n i k).mono hu
  have ha (i : Fin 3) : HarmonicResidual.SmoothCoefficients U
      (x.coefficients.aliasCoefficients l n i) := by
    rw [H.aliasCoefficients l]
    exact HarmonicResidual.smoothCoefficients_zero U
  exact contDiffOn_pi.mpr (fun i => HarmonicResidual.LabelData.waveResidualCoefficients_smooth
    (LocalRankDefect.positiveDomain_open standardRegion.isOpen) hf _ _ hb hm _ hd hg ha i j)

include H in
theorem source_smooth (hS : ∀ l n, IsClosed (S l n))
    (hpos : ∀ l n z, z ∈ ActualInitialization.geometry.domain → z ∈ S l n → 0 < z.1)
    (l : Index B N0) (j : ℤ) (n : ℕ) :
    ContDiffOn ℝ ∞ (ParticularWaveAssembly.residualSource (commonContext B) x.state
      (x.coefficients.blocks l) (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l) j
          n)
      ActualInitialization.geometry.domain := by
  apply ActualInitialization.geometry.domain_open.contDiffOn_iff.mpr
  intro z hz
  by_cases hr : 0 < z.1
  · exact (source_positive_smooth H l j n).contDiffAt
      ((LocalRankDefect.positiveDomain_open standardRegion.isOpen).mem_nhds ⟨hr,hz⟩)
  · apply contDiffAt_const.congr_of_eventuallyEq
    exact HarmonicSourceSupport.residualSource_zero_germ_on (commonContext B) x.state
      (x.coefficients.blocks l) (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l)
      ActualInitialization.geometry.domain_open (hS l) (H.inputSupport l) j n hz
      (fun hc => hr (hpos l n z hz hc))

include H in
theorem particularSource_smooth (hS : ∀ l n, IsClosed (S l n))
    (hpos : ∀ l n z, z ∈ ActualInitialization.geometry.domain → z ∈ S l n → 0 < z.1)
    (l : ActualParticularStageControls.Label B N0) (j : ℤ) (n : ℕ) :
    ContDiffOn ℝ ∞ (particularSource x l j n)
      {z | z.1.2 ∈ standardRegion.carrier} :=
  (source_smooth H hS hpos (l.2,l.1) j n).comp cycleAssoc.symm.contDiff.contDiffOn
    (fun _ hz => hz)

include H in
theorem source_fiber_continuous (hS : ∀ l n, IsClosed (S l n))
    (hpos : ∀ l n z, z ∈ ActualInitialization.geometry.domain → z ∈ S l n → 0 < z.1)
    (l : ActualParticularStageControls.Label B N0) (j : ℤ) (n : ℕ)
    (p : PhysicalParticularWave.Parameter) (hp : p.2 ∈ standardRegion.carrier) :
    Continuous (fun Y => particularSource x l j n (p,Y)) := by
  have hm : MapsTo (fun Y : PressureStream.Plane => (p,Y)) univ
      {z | z.1.2 ∈ standardRegion.carrier} := fun _ _ => hp
  exact continuousOn_univ.mp ((particularSource_smooth H hS hpos l j n).continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn hm)

include H in
theorem source_ordered (hS : ∀ l n, IsClosed (S l n))
    (hcore : ∀ l n, S l n ⊆ ActualCoreSupport.refinedCarrier l n)
    (l : ActualParticularStageControls.Label B N0) (j : ℤ) (n : ℕ)
    (p : PhysicalParticularWave.Parameter) (hp : p.2 ∈ standardRegion.carrier)
    (hne : ∃ Y, particularSource x l j n (p, Y) ≠ 0) :
    CommonWindow.index h n ≤ ChartScales.nativeIndex h (BaseChartJets.cellBand l.2) := by
  obtain ⟨Y,hY⟩ := hne
  exact core_ordered (l.2,l.1) n hp (hcore _ _ (source_support H hS l j n hp hY))

include H in
theorem particular_source_inputs (hS : ∀ l n, IsClosed (S l n))
    (hcore : ∀ l n, S l n ⊆ ActualCoreSupport.refinedCarrier l n)
    (l : ActualParticularStageControls.Label B N0) :
    ActualParticularCoherence.SourceInputs (ActualCycleParameters.particularState x) l := by
  have hpos (a : Index B N0) (n : ℕ) (z : Point)
      (hz : z ∈ ActualInitialization.geometry.domain) (hs : z ∈ S a n) : 0 < z.1 :=
    core_radius_pos a n hz (hcore a n hs)
  have he (j : ℤ) (n : ℕ) :
      ActualParticularCoherence.source (ActualCycleParameters.particularState x) l j n =
        particularSource x l j n := (particularSource_eq x l j n).symm
  constructor
  · intro j n p hp
    simpa only [he] using source_fiber_continuous H hS hpos l j n p hp
  · intro j n p hp Y hn
    rw [he] at hn
    exact hcore (l.2,l.1) n (source_support H hS l j n hp hn)
  · intro j n p hp Y hn
    rw [he] at hn
    exact source_ordered H hS hcore l j n p hp ⟨Y,hn⟩

include H W in
theorem covariance_moving :
    (∀ i j, GaugeMomentBalances.MovingField standardRegion geometry.inner geometry.outer
      (SignedMeanGain.covarianceIncrement x.state.oscillation
        ((ActualCycleParameters.fixedParameters B N0).particularVelocity x.coefficients
          (commonContext B) x.state) i j)) ∧
    (∀ i j, GaugeMomentBalances.MovingField standardRegion geometry.inner geometry.outer
      (SignedMeanGain.covarianceIncrement
        ((ActualCycleParameters.fixedParameters B N0).afterParticular x.coefficients
          (commonContext B) x.state).oscillation
        ((ActualCycleParameters.fixedParameters B N0).signedVelocity x.coefficients
          (commonContext B) x.state) i j)) :=
  W.covariance_moving H.oscillationSmooth H.oscillationPeriodic

include H in
theorem rank_geometry :
    LocalRankDefect.RankGeometry (ActualCycleParameters.fixedParameters B N0).gauge
      (ActualCycleParameters.fixedParameters B N0).rank standardRegion.carrier
        (commonContext B) x.state :=
  CorrectionInitialization.ActualPrimary.rank_geometry standardRegion B x.state
    (MeanStageRegularity.debt_smooth H.primitives ActualInitialization.geometry.patch.a_pos
      ActualInitialization.geometry.patch.a_lt_b)

include H W in
theorem stage_primitives :
    CycleStateCoherence.StagePrimitives geometry (ActualCycleParameters.fixedParameters B N0)
      x.coefficients (commonContext B) x.state standardRegion :=
  CycleStateCoherence.stage_primitives (realizes B N0) H.primitives
    (covariance_moving H W).1 (covariance_moving H W).2 (rank_geometry H)

include H W in
theorem afterParticular_primitive :
    MeanStateRegularity.PrimitiveData ActualInitialization.geometry.region
      ActualInitialization.geometry.patch.a ActualInitialization.geometry.patch.b
      (commonContext B) ((ActualCycleParameters.fixedParameters B N0).afterParticular
        x.coefficients (commonContext B) x.state) :=
  (stage_primitives H W).particular

theorem afterParticular_pressure :
    (VariableGaugeMean.reconstructState ActualInitialization.geometry.gauge (commonContext B)
      ((ActualCycleParameters.fixedParameters B N0).afterParticular x.coefficients
        (commonContext B) x.state)).pressure =
      ((ActualCycleParameters.fixedParameters B N0).afterParticular x.coefficients
        (commonContext B) x.state).pressure := rfl

include H W in
theorem signed_cycle_wave_on (l : Index B N0) (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (HS : StateOn (PhysicalMeanDomain.slowDomain (overlap n m))
      (bandChartEquiv h n m k) (bandVelocityScale h n m) (bandScale n m)
      ((ActualCycleParameters.fixedParameters B N0).afterParticular x.coefficients (commonContext
          B) x.state)
      ((ActualCycleParameters.fixedParameters B N0).afterParticular x.coefficients (commonContext
          B) x.state) n m) :
    CycleStateCoherence.WaveOn (PhysicalMeanDomain.slowDomain (overlap n m))
      (bandChartEquiv h n m k) (bandVelocityScale h n m) (bandScale n m)
      ((ActualCycleParameters.fixedParameters B N0).signedBlock x.coefficients (commonContext B)
          x.state l).oscillation
      ((ActualCycleParameters.fixedParameters B N0).signedBlock x.coefficients (commonContext B)
          x.state l).oscillatoryPressure
      ((ActualCycleParameters.fixedParameters B N0).signedGaussianBlock x.coefficients
          (commonContext B) x.state l).oscillation
      ((ActualCycleParameters.fixedParameters B N0).signedBlock x.coefficients (commonContext B)
          x.state l).oscillation
      ((ActualCycleParameters.fixedParameters B N0).signedBlock x.coefficients (commonContext B)
          x.state l).oscillatoryPressure
      ((ActualCycleParameters.fixedParameters B N0).signedGaussianBlock x.coefficients
          (commonContext B) x.state l).oscillation n m :=
  signed_wave_on l _ (afterParticular_primitive H W) (afterParticular_pressure (x := x)) n m k hi HS

theorem particular_pressure_zero
    (p : CycleParameters (Index B N0)) (v : CycleCoefficients (Index B N0))
    (c : Context Point) (u : State Point) (l : Index B N0) (n : ℕ) :
    (p.particularBlock v c u l).pressure n 0 = 0 := by
  funext z
  exact congrFun ((ParticularWaveAssembly.assembledBlock_zero _ _ _ _ _ _).2 n) (cycleAssoc z)

variable
  (C : Coherent x)
  (hcover : ∀ l n z, z ∈ ActualInitialization.geometry.domain → z ∈ S l n →
    l ∈ x.coefficients.labels n)

include H C in
theorem particular_wave_on (hS : ∀ l n, IsClosed (S l n))
    (hcore : ∀ l n, S l n ⊆ ActualCoreSupport.refinedCarrier l n)
    (l : Index B N0) (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m) :
    CycleStateCoherence.WaveOn (PhysicalMeanDomain.slowDomain (overlap n m))
      (bandChartEquiv h n m k) (bandVelocityScale h n m) (bandScale n m)
      ((ActualCycleParameters.fixedParameters B N0).particularBlock x.coefficients (commonContext
          B) x.state l).oscillation
      ((ActualCycleParameters.fixedParameters B N0).particularBlock x.coefficients (commonContext
          B) x.state l).oscillatoryPressure
      ((ActualCycleParameters.fixedParameters B N0).particularGaussianBlock x.coefficients
          (commonContext B) x.state l).oscillation
      ((ActualCycleParameters.fixedParameters B N0).particularBlock x.coefficients (commonContext
          B) x.state l).oscillation
      ((ActualCycleParameters.fixedParameters B N0).particularBlock x.coefficients (commonContext
          B) x.state l).oscillatoryPressure
      ((ActualCycleParameters.fixedParameters B N0).particularGaussianBlock x.coefficients
          (commonContext B) x.state l).oscillation n m := by
  let xp := ActualCycleParameters.particularState x
  let lp : ActualParticularStageControls.Label B N0 := (l.2,l.1)
  have I := particular_source_inputs H hS hcore lp
  have hf (a : ℕ) : (xp.coefficients.blocks lp).frequency a = ChartScales.carrier h a :=
    ActualCycleParameters.current_frequency x l (H.carrier l) a
  have hs := C.reference_state n m k hi
  have hb := C.reference_block lp n m k hi
  have ht : ∀ s ∈ overlap n m, 0 < s.1 := fun s hs => standardRegion.time_pos s hs.1
  have hmap : MapsTo (bandSlowEquiv h n m) (overlap n m) standardRegion.carrier :=
    fun _ hz => hz.2
  have hphi (z : Point) (hz : z.2.1 ∈ overlap n m) :
      (x.coefficients.blocks l).frequency n * (x.coefficients.blocks l).phase n z =
        (x.coefficients.blocks l).frequency m *
          (x.coefficients.blocks l).phase m (bandChartEquiv h n m k z) :=
    (C.blocks l n m k hi).phase hz
  have ha (j : ℤ) (hj : j ≠ 0) (z : Point) (hz : z.2.1 ∈ overlap n m) :
      (ActualParticularCoherence.corrected xp lp j).amplitude n (particularPoint z) =
        bandVelocityScale h n m • (ActualParticularCoherence.corrected xp lp j).amplitude m
          (particularPoint (bandChartEquiv h n m k z)) := by
    simpa only [ActualSignedCoherence.velocityWeight_eq, particularPoint_chart n m k hi] using
      ActualParticularCoherence.corrected_amplitude_on xp lp I hf
        (ActualInitialCoherence.overlap_open n m) ht n m k hi hmap hs hb j hj
        (particularPoint z) hz
  have hr (j : ℤ) (hj : j ≠ 0) (z : Point) (hz : z.2.1 ∈ overlap n m) :=
    ActualParticularCoherence.raw_outputs xp lp I hf (ActualInitialCoherence.overlap_open n m)
      ht n m k hi hs hb j hj (particularPoint z) hz
      (by rw [ActualParticularCoherence.parameterChange_slow]; exact hmap hz)
  have hp (j : ℤ) (hj : j ≠ 0) (z : Point) (hz : z.2.1 ∈ overlap n m) :
      (ActualParticularCoherence.corrected xp lp j).pressure n (particularPoint z) =
        (bandVelocityScale h n m * bandVelocityScale h n m) •
          (ActualParticularCoherence.corrected xp lp j).pressure m
            (particularPoint (bandChartEquiv h n m k z)) := by
    have he := (hr j hj z hz).2.1
    simp only [particular_pressure_weight, particularPoint_chart n m k hi] at he
    exact he
  have hg (j : ℤ) (hj : j ≠ 0) (z : Point) (hz : z.2.1 ∈ overlap n m) :
      (ActualParticularCoherence.copyData xp lp j).globalGaussian
          (ActualParticularStageControls.directions (B := B)) n (particularPoint z) =
        (bandVelocityScale h n m * bandVelocityScale h n m * bandScale n m) •
          (ActualParticularCoherence.copyData xp lp j).globalGaussian
            (ActualParticularStageControls.directions (B := B)) m
              (particularPoint (bandChartEquiv h n m k z)) := by
    simpa only [← ActualReferenceRebase.state_sourceWeight, particularPoint_chart n m k hi] using
      (hr j hj z hz).2.2
  rw [← ActualCycleParameters.invariant_parameters_eq_fixed H]
  constructor
  · intro z hz theta i
    rw [literal_particular_velocity, literal_particular_velocity, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [ha j ((ParticularWaveAssembly.mem_modes _ _).mp hj).1 z hz,
      hphi z hz, (C.blocks l n m k hi).angular]
    simp only [Pi.smul_apply, Complex.real_smul, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  · intro z hz theta
    rw [literal_particular_pressure, literal_particular_pressure, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hp j ((ParticularWaveAssembly.mem_modes _ _).mp hj).1 z hz,
      hphi z hz, (C.blocks l n m k hi).angular]
    simp only [Complex.real_smul, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  · intro z hz theta i
    rw [literal_particular_gaussian, literal_particular_gaussian, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hg j ((ParticularWaveAssembly.mem_modes _ _).mp hj).1 z hz,
      hphi z hz, (C.blocks l n m k hi).angular]
    simp only [Pi.smul_apply, Complex.real_smul, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring

include W hcover in
theorem particular_label_waves (n m k : ℕ)
    (HP : ∀ l, CycleStateCoherence.WaveOn (PhysicalMeanDomain.slowDomain (overlap n m))
      (bandChartEquiv h n m k) (bandVelocityScale h n m) (bandScale n m)
      ((ActualCycleParameters.fixedParameters B N0).particularBlock x.coefficients
        (commonContext B) x.state l).oscillation
      ((ActualCycleParameters.fixedParameters B N0).particularBlock x.coefficients
        (commonContext B) x.state l).oscillatoryPressure
      ((ActualCycleParameters.fixedParameters B N0).particularGaussianBlock x.coefficients
        (commonContext B) x.state l).oscillation
      ((ActualCycleParameters.fixedParameters B N0).particularBlock x.coefficients
        (commonContext B) x.state l).oscillation
      ((ActualCycleParameters.fixedParameters B N0).particularBlock x.coefficients
        (commonContext B) x.state l).oscillatoryPressure
      ((ActualCycleParameters.fixedParameters B N0).particularGaussianBlock x.coefficients
        (commonContext B) x.state l).oscillation n m) :
    CycleStateCoherence.LabelWavesOn (PhysicalMeanDomain.slowDomain (overlap n m))
      (bandChartEquiv h n m k) (bandVelocityScale h n m) (bandScale n m) x.coefficients.labels
      ((ActualCycleParameters.fixedParameters B N0).particularBlock x.coefficients (commonContext
          B) x.state)
      ((ActualCycleParameters.fixedParameters B N0).particularGaussianBlock x.coefficients
          (commonContext B) x.state)
      n m := by
  apply label_waves_of_support _ _ _ S W.particularSupport
    ((ActualCycleParameters.fixedParameters B N0).particularBlock_zero x.coefficients
        (commonContext B) x.state)
    (particular_pressure_zero _ _ _ _)
    ((ActualCycleParameters.fixedParameters B N0).particularGaussianBlock_zero x.coefficients
        (commonContext B) x.state)
    hcover n m k HP

include W hcover in
theorem signed_label_waves (n m k : ℕ)
    (HS : ∀ l, CycleStateCoherence.WaveOn (PhysicalMeanDomain.slowDomain (overlap n m))
      (bandChartEquiv h n m k) (bandVelocityScale h n m) (bandScale n m)
      ((ActualCycleParameters.fixedParameters B N0).signedBlock x.coefficients
        (commonContext B) x.state l).oscillation
      ((ActualCycleParameters.fixedParameters B N0).signedBlock x.coefficients
        (commonContext B) x.state l).oscillatoryPressure
      ((ActualCycleParameters.fixedParameters B N0).signedGaussianBlock x.coefficients
        (commonContext B) x.state l).oscillation
      ((ActualCycleParameters.fixedParameters B N0).signedBlock x.coefficients
        (commonContext B) x.state l).oscillation
      ((ActualCycleParameters.fixedParameters B N0).signedBlock x.coefficients
        (commonContext B) x.state l).oscillatoryPressure
      ((ActualCycleParameters.fixedParameters B N0).signedGaussianBlock x.coefficients
        (commonContext B) x.state l).oscillation n m) :
    CycleStateCoherence.LabelWavesOn (PhysicalMeanDomain.slowDomain (overlap n m))
      (bandChartEquiv h n m k) (bandVelocityScale h n m) (bandScale n m) x.coefficients.labels
      ((ActualCycleParameters.fixedParameters B N0).signedBlock x.coefficients (commonContext B)
          x.state)
      ((ActualCycleParameters.fixedParameters B N0).signedGaussianBlock x.coefficients
          (commonContext B) x.state)
      n m := by
  apply label_waves_of_support _ _ _ S W.signedSupport
    (fun l => ((ActualCycleParameters.fixedParameters B N0).signed l).exactBlock_zero _ _)
    (fun l => ((ActualCycleParameters.fixedParameters B N0).signed l).exactBlock_pressure_zero _ _)
    ((ActualCycleParameters.fixedParameters B N0).signedGaussianBlock_zero x.coefficients
        (commonContext B) x.state)
    hcover n m k HS

include H W C in
theorem transport_of_waves (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (HW : CycleStateCoherence.CycleWavesOn geometry (ActualCycleParameters.fixedParameters B N0)
      x.coefficients (commonContext B) x.state (overlap n m) n m k) :
    CycleStateCoherence.CycleTransport geometry (ActualCycleParameters.fixedParameters B N0)
      x.coefficients (commonContext B) x.state (overlap n m) n m k :=
  CycleStateCoherence.cycle_transport (realizes B N0) (ActualInitialCoherence.overlap_open n m)
    inter_subset_left n m k hi (fun _ hz => hz.2) (context B n m k hi) (C.state n m k hi)
    H.primitives (covariance_moving H W).1 (covariance_moving H W).2 (rank_geometry H) HW

include H W C in
theorem afterParticular_coherent
    (HP : ∀ n m k, CommonWindow.index h n + k = CommonWindow.index h m →
      CycleStateCoherence.LabelWavesOn (PhysicalMeanDomain.slowDomain (overlap n m))
        (bandChartEquiv h n m k) (bandVelocityScale h n m) (bandScale n m) x.coefficients.labels
        ((ActualCycleParameters.fixedParameters B N0).particularBlock x.coefficients (commonContext
            B) x.state)
        ((ActualCycleParameters.fixedParameters B N0).particularGaussianBlock x.coefficients
            (commonContext B) x.state)
        n m) :
    StateCoherent ((ActualCycleParameters.fixedParameters B N0).afterParticular
      x.coefficients (commonContext B) x.state) := by
  intro n m k hi
  exact CycleStateCoherence.wave_stage_band (realizes B N0)
    (ActualInitialCoherence.overlap_open n m) inter_subset_left n m k hi
    (fun _ hz => hz.2) (context B n m k hi) H.primitives (C.state n m k hi)
    (covariance_moving H W).1 (HP n m k hi).sum

include H W C hcover in
/-- The two literal wave insertions have the required transport law.
Every source and coefficient comparison is derived from the incoming
state, its support, and the actual solver primitives. -/
theorem waves (hS : ∀ l n, IsClosed (S l n))
    (hcore : ∀ l n, S l n ⊆ ActualCoreSupport.refinedCarrier l n)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m) :
    CycleStateCoherence.CycleWavesOn geometry (ActualCycleParameters.fixedParameters B N0)
      x.coefficients (commonContext B) x.state (overlap n m) n m k := by
  have HP (a b d : ℕ) (hd : CommonWindow.index h a + d = CommonWindow.index h b) :=
    particular_label_waves W hcover a b d
      (fun l => particular_wave_on H C hS hcore l a b d hd)
  have HU := afterParticular_coherent H W C HP
  exact ⟨HP n m k hi, signed_label_waves W hcover n m k
    (fun l => signed_cycle_wave_on H W l n m k hi (HU n m k hi))⟩

include H W C in
theorem step_of_waves
    (HW : ∀ n m k, CommonWindow.index h n + k = CommonWindow.index h m →
      CycleStateCoherence.CycleWavesOn geometry (ActualCycleParameters.fixedParameters B N0)
        x.coefficients (commonContext B) x.state (overlap n m) n m k) :
    Coherent (x.step (ActualCycleParameters.fixedParameters B N0) (commonContext B)) := by
  refine ⟨?_, ?_, ?_, C.labels⟩
  · intro n m k hi
    exact (transport_of_waves H W C n m k hi (HW n m k hi)).next
  · intro l n m k hi
    exact CycleStateCoherence.block_fields_next (HW n m k hi) W.carrier l (C.blocks l n m k hi)
  · intro n m k hi
    exact (transport_of_waves H W C n m k hi (HW n m k hi)).axis (C.axis n m k hi)

include H W C hcover in
/-- Simultaneous propagation of the actual state, stored blocks,
Gaussian/alias data, and the initializer's finite label choice. -/
theorem step (hS : ∀ l n, IsClosed (S l n))
    (hcore : ∀ l n, S l n ⊆ ActualCoreSupport.refinedCarrier l n) :
    Coherent (x.step (ActualCycleParameters.fixedParameters B N0) (commonContext B)) :=
  step_of_waves H W C (waves H W C hcover hS hcore)

include H W in
theorem next_primitive :
    MeanStateRegularity.PrimitiveData standardRegion geometry.inner geometry.outer
      (commonContext B) (x.step (ActualCycleParameters.fixedParameters B N0) (commonContext
          B)).state :=
  ((ActualCycleParameters.fixedParameters B N0).next_primitive x.coefficients (commonContext B)
    x.state standardRegion (realizes B N0).inner_pos (realizes B N0).exponent_pos
    (realizes B N0).length H.primitives (covariance_moving H W).1 (covariance_moving H W).2
    (rank_geometry H)).1

include H W C in
theorem temporal_potential_overlap (N : ℕ)
    (HW : ∀ n m k, CommonWindow.index h n + k = CommonWindow.index h m →
      CycleStateCoherence.CycleWavesOn geometry (ActualCycleParameters.fixedParameters B N0)
        x.coefficients (commonContext B) x.state (overlap n m) n m k) :
    (ActualMeanPhysicalData.initialAtlas N).OverlapLaw standardRegion.carrier
      (CoordinateAlgebra.A h - 1 / 2)
      (VariableGaugeMean.temporalPotential (ActualCycleParameters.fixedParameters B N0).gauge
        (ActualCycleParameters.fixedParameters B N0).timeExponent
        (ActualCycleParameters.fixedParameters B N0).commonIndex (commonContext B)
        ((ActualCycleParameters.fixedParameters B N0).afterSigned x.coefficients (commonContext B)
            x.state)) := by
  have HS : (ActualMeanPhysicalData.initialAtlas N).StateOverlap standardRegion.carrier
      ((ActualCycleParameters.fixedParameters B N0).afterSigned x.coefficients (commonContext B)
          x.state) :=
    fun n _ m _ k hi => (transport_of_waves H W C n m k hi (HW n m k hi)).signed
  exact (ActualMeanPhysicalData.initialAtlas N).temporal_overlap standardRegion
    (ActualCycleParameters.fixedParameters B N0).gauge (commonContext B) _
    (ActualMeanPhysicalData.initial_context_overlap B N) HS
    (ActualMeanPhysicalData.initial_gauge_overlap N) (stage_primitives H W).signed
    (realizes B N0).inner_pos (realizes B N0).exponent_pos (realizes B N0).length rfl

include H W C in
theorem rank_potential_overlap (N : ℕ)
    (HW : ∀ n m k, CommonWindow.index h n + k = CommonWindow.index h m →
      CycleStateCoherence.CycleWavesOn geometry (ActualCycleParameters.fixedParameters B N0)
        x.coefficients (commonContext B) x.state (overlap n m) n m k) :
    (ActualMeanPhysicalData.initialAtlas N).OverlapLaw standardRegion.carrier
      (CoordinateAlgebra.A h - 1 / 2)
      (VariableGaugeMean.rankPotential (ActualCycleParameters.fixedParameters B N0).gauge
        (ActualCycleParameters.fixedParameters B N0).rank (commonContext B)
        ((ActualCycleParameters.fixedParameters B N0).afterTemporal x.coefficients (commonContext
            B) x.state)) := by
  have HS : (ActualMeanPhysicalData.initialAtlas N).StateOverlap standardRegion.carrier
      ((ActualCycleParameters.fixedParameters B N0).afterTemporal x.coefficients (commonContext B)
          x.state) :=
    fun n _ m _ k hi => (transport_of_waves H W C n m k hi (HW n m k hi)).temporal
  exact (ActualMeanPhysicalData.initialAtlas N).rank_overlap standardRegion
    (ActualCycleParameters.fixedParameters B N0).gauge (ActualCycleParameters.fixedParameters B
        N0).rank
    (commonContext B) _ (ActualMeanPhysicalData.initial_context_overlap B N) HS
    (ActualMeanPhysicalData.initial_gauge_overlap N) (ActualMeanPhysicalData.initial_rank_overlap N)
    (stage_primitives H W).temporal (stage_primitives H W).rankGeometry

end Step

/-! ## The fixed actual recurrence and the mean atlas input -/

/-- State, constructed using `CycleState.iterate`. -/
noncomputable def state (B N0 : ℕ) : ℕ → CycleState (Index B N0) :=
  CycleState.iterate (fun _ => ActualCycleParameters.fixedParameters B N0)
    (commonContext B) (ActualInitialization.initialCycleState B N0)

theorem state_zero (B N0 : ℕ) : state B N0 0 = ActualInitialization.initialCycleState B N0 := rfl

theorem state_succ (B N0 j : ℕ) : state B N0 (j + 1) =
    (state B N0 j).step (ActualCycleParameters.fixedParameters B N0) (commonContext B) := rfl

theorem state_labels (B N0 j : ℕ) :
    (state B N0 j).coefficients.labels = activeLabels standardRegion B N0 :=
  CycleStateCoherence.iterate_labels _ _ _ j

theorem state_aliasCoefficients (B N0 j : ℕ) :
    (state B N0 j).coefficients.aliasCoefficients = 0 :=
  CycleStateCoherence.iterate_aliasCoefficients _ _ _ j

/-- Collection of the already proved actual transport laws into precisely
the input used by the physical mean atlas.  Its covariance fields are
derived from the same stage data as the analytic induction. -/
theorem mean_input_of_transport (B N0 N : ℕ) (sigma : ℕ → ℝ)
    (S : Index B N0 → ℕ → Set Point)
    (H : ∀ j, CycleAnalyticInvariant ActualInitialization.geometry (commonContext B)
      ActualInitialization.tangentBlock ActualInitialization.envelope S (sigma j) (state B N0 j))
    (W : ∀ j, CorrectionAnalyticStep.WaveData ActualInitialization.geometry
      (ActualCycleParameters.fixedParameters B N0) (state B N0 j).coefficients
      (commonContext B) (state B N0 j).state ActualInitialization.envelope S (sigma j)
          ChartScales.kappa)
    (HW : ∀ j n m k, CommonWindow.index h n + k = CommonWindow.index h m →
      CycleStateCoherence.CycleWavesOn geometry (ActualCycleParameters.fixedParameters B N0)
        (state B N0 j).coefficients (commonContext B) (state B N0 j).state (overlap n m) n m k) :
    ActualMeanPhysicalData.InitialCycleInput B N0 N (fun _ => ActualCycleParameters.fixedParameters
        B N0) where
  realizes := fun _ => realizes B N0
  covariance_particular := fun j => (covariance_moving (H j) (W j)).1
  covariance_signed := fun j => (covariance_moving (H j) (W j)).2
  waves := fun n _ m _ k hi j => HW j n m k hi

section Iteration

variable (B N0 : ℕ) (sigma : ℕ → ℝ) (S : Index B N0 → ℕ → Set Point)
    (H : ∀ j, CycleAnalyticInvariant ActualInitialization.geometry (commonContext B)
      ActualInitialization.tangentBlock ActualInitialization.envelope S (sigma j) (state B N0 j))
    (W : ∀ j, CorrectionAnalyticStep.WaveData ActualInitialization.geometry
      (ActualCycleParameters.fixedParameters B N0) (state B N0 j).coefficients
      (commonContext B) (state B N0 j).state ActualInitialization.envelope S (sigma j)
          ChartScales.kappa)
    (hS : ∀ l n, IsClosed (S l n))
    (hcore : ∀ l n, S l n ⊆ ActualCoreSupport.refinedCarrier l n)
    (hcover : ∀ l n z, z ∈ ActualInitialization.geometry.domain → z ∈ S l n →
      l ∈ activeLabels standardRegion B N0 n)

include H W hS hcore hcover in
/-- The geometric induction uses the same fixed recurrence and supplied
analytic stage data; no sequence of coherent states is assumed. -/
theorem iterate_coherent (j : ℕ) : Coherent (state B N0 j) := by
  induction j with
  | zero => exact initial B N0
  | succ j ih =>
    exact step (H j) (W j) ih
      (fun l n z hz hs => by
        change l ∈ (state B N0 j).coefficients.labels n
        rw [state_labels]
        exact hcover l n z hz hs) hS hcore

include H W hS hcore hcover in
theorem iterate_waves (j n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m) :
    CycleStateCoherence.CycleWavesOn geometry (ActualCycleParameters.fixedParameters B N0)
      (state B N0 j).coefficients (commonContext B) (state B N0 j).state (overlap n m) n m k :=
  waves (H j) (W j) (iterate_coherent B N0 sigma S H W hS hcore hcover j)
    (fun l n z hz hs => by
      rw [state_labels]
      exact hcover l n z hz hs) hS hcore n m k hi

include H W hS hcore hcover in
/-- The actual mean-atlas input is derived from the same analytic
recurrence; its wave and covariance transports are conclusions. -/
theorem mean_input (N : ℕ) :
    ActualMeanPhysicalData.InitialCycleInput B N0 N (fun _ => ActualCycleParameters.fixedParameters
        B N0) :=
  mean_input_of_transport B N0 N sigma S H W
    (iterate_waves B N0 sigma S H W hS hcore hcover)

end Iteration

end NavierStokes.ActualCycleCoherence
