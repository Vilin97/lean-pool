/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualSignedCoherence

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
