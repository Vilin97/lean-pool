/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualStageEstimates
public import LeanPool.NavierStokesAndEuler.NavierStokes.InitialPhysicalData
import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCurrentParticularBounds
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCurrentParticularPhysical
public import LeanPool.NavierStokesAndEuler.NavierStokes.ValidDyadicBandCover
import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCurrentWaveSupport
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCycleCoherence
public import LeanPool.NavierStokesAndEuler.NavierStokes.GermCandidateAssembly
public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalStageSupport
import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCyclePreservation
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualParticularCoherence

/-!
# Stage estimates with the current-band particular fields

The signed waves and mean increments retain their actual native inputs.
The particular contribution is an independently constructed physical field,
with no physical copy-family representation imposed on it.
-/

section

/-!
# The actual particular waves on valid physical charts

The physical representative uses only the literal current-band solve.
Its compatibility is obtained from the corresponding current-source
transport laws.  No value of a reference solve on an excluded face is
used to define the physical representative.
-/

section

/-!
# Coherence of the actual current-band particular potential

The common copy coefficient is retained, including its cutoffs.  Its vector
potential is transported before taking the physical curl.  The derivative
identity uses an invertible linear chart and does not require an additional
smoothness assumption on the phase.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.ActualParticularPotentialCoherence

open Set Function Filter HarmonicCalculus PhysicalParticularWave
open CorrectionInitialization CorrectionInitialization.ActualPrimary
open scoped Topology ContDiff

section ExactCalculus

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The phase scale cancels the inverse carrier in the literal potential.
An invertible chart also handles the convention for a nonexistent derivative. -/
theorem vectorPotential_equiv (e : E ≃L[ℝ] F) {s b K L : ℝ}
    (hs : s ≠ 0) (hb : b ≠ 0) (hK : K ≠ 0) (hKL : K * b = L)
    (r : E → ℝ) (R : F → ℝ) (Sr St Sz : E → E) (Vr Vt Vz : F → F)
    (hr : ∀ x, R (e x) = s * r x)
    (hDr : ∀ x, e (Sr x) = s • Vr (e x))
    (hDt : ∀ x, e (St x) = Vt (e x))
    (hDz : ∀ x, e (Sz x) = s • Vz (e x)) (c : ℝ)
    (Φ : F → ℝ) (a : F → ComplexVector) (x : E) :
    CurlClassBounds.vectorPotential K r Sr St Sz
      (fun y => b * Φ (e y)) (fun y => c • a (e y)) x =
      (c / s) • CurlClassBounds.vectorPotential L R Vr Vt Vz Φ a (e x) := by
  have hN := ActualPrimaryCoherence.phaseNormal_equiv e hs r R Sr St Sz Vr Vt Vz
    hr hDr hDt hDz b Φ x
  have hphase : carrier K (fun y => b * Φ (e y)) x = carrier L Φ (e x) :=
    PhysicalCurlCovariance.carrier_eq_of_products (by rw [← mul_assoc, hKL])
  have hscale : CurlClassBounds.inverseCarrier K * ((c / (b * s) : ℝ) : ℂ) =
      ((c / s : ℝ) : ℂ) * CurlClassBounds.inverseCarrier L := by
    rw [← hKL]
    unfold CurlClassBounds.inverseCarrier
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hK, Complex.ofReal_ne_zero.mpr hb,
      Complex.ofReal_ne_zero.mpr hs]
  ext i
  simp only [CurlClassBounds.vectorPotential, vectorMode, mode, CurlClassBounds.coefficient,
    hN, PhysicalCurlCovariance.normalCoefficient_scale _ _ (mul_ne_zero hb hs) c,
    hphase, Pi.smul_apply, Complex.real_smul, smul_eq_mul]
  rw [← mul_assoc (CurlClassBounds.inverseCarrier K), hscale]
  ring

end ExactCalculus

/-- The physical potential has the scale exponent `h`, one half below the
velocity exponent. -/
theorem potential_weight {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr) (h : ℝ) :
    velocityWeight h Q Qr / ratioPower Q Qr (1 / 2) = ratioPower Q Qr h := by
  rw [velocityWeight, ratioPower_div hQ hQr]
  congr 1
  unfold CoordinateAlgebra.A
  ring

theorem pressure_weight {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr) (h : ℝ) :
    pressureWeight h Q Qr = (velocityWeight h Q Qr) ^ 2 := by
  rw [pow_two, velocityWeight, ratioPower_mul hQ hQr]
  unfold pressureWeight
  congr 1
  ring

variable {B N0 : ℕ}

/-- Label: an abbreviation for `ActualParticularStageControls.Label`. -/
abbrev Label := ActualParticularStageControls.Label

/-- The potential of the actual current common coefficient. -/
noncomputable def potential (x : CorrectionStep.CycleState (Label B N0))
    (l : Label B N0) (j : ℤ) (n : ℕ) : WaveSpace → ComplexVector :=
  (ActualReferenceRebase.actualCoefficients x l j).curlPotential
    (CorrectionStep.ParticularParameters.nativeStrip ActualParticularStageControls.associatedStrip)
    (ActualParticularStageControls.directions (B := B)) n

/-- The complete harmonic pressure, with the actual current common pressure
coefficient and the same carrier. -/
noncomputable def pressureMode (x : CorrectionStep.CycleState (Label B N0))
    (l : Label B N0) (j : ℤ) (n : ℕ) : WaveSpace → ℂ :=
  mode ((ActualReferenceRebase.actualCoefficients x l j).frequency n)
    ((ActualReferenceRebase.actualCoefficients x l j).phase n)
    ((ActualReferenceRebase.actualCoefficients x l j).pressure n)

theorem potential_eq_copyData (x : CorrectionStep.CycleState (Label B N0))
    (l : Label B N0) (j : ℤ) (n : ℕ) :
    potential x l j n = (ActualParticularCoherence.copyData x l j).common.curlPotential
      (CorrectionStep.ParticularParameters.nativeStrip
          ActualParticularStageControls.associatedStrip)
      (ActualParticularStageControls.directions (B := B)) n := rfl

theorem pressureMode_eq_copyData (x : CorrectionStep.CycleState (Label B N0))
    (l : Label B N0) (j : ℤ) (n : ℕ) :
    pressureMode x l j n = mode ((ActualParticularCoherence.copyData x l j).background.frequency n)
      ((ActualParticularCoherence.copyData x l j).background.phase n)
      ((ActualParticularCoherence.copyData x l j).common.pressure n) := rfl

theorem potential_eq (x : CorrectionStep.CycleState (Label B N0))
    (l : Label B N0) (j : ℤ) (n : ℕ) :
    potential x l j n = CurlClassBounds.vectorPotential
      ((j : ℝ) * (x.coefficients.blocks l).frequency n) (fun y : WaveSpace => y.1.1.1)
      ((ActualParticularStageControls.directions (B := B)).radialField n)
      (fun _ => (ActualParticularStageControls.directions (B := B)).angular)
      ((ActualParticularStageControls.directions (B := B)).axialField
        (CorrectionStep.ParticularParameters.nativeStrip
            ActualParticularStageControls.associatedStrip) n)
      ((ActualReferenceRebase.actualCoefficients x l j).phase n)
      ((ActualReferenceRebase.actualCoefficients x l j).amplitude n) := rfl

theorem pressureMode_eq (x : CorrectionStep.CycleState (Label B N0))
    (l : Label B N0) (j : ℤ) (n : ℕ) :
    pressureMode x l j n = mode ((j : ℝ) * (x.coefficients.blocks l).frequency n)
      ((ActualReferenceRebase.actualCoefficients x l j).phase n)
      ((ActualReferenceRebase.actualCoefficients x l j).pressure n) := rfl

/-- Only the phase needs a germ: the undifferentiated raw amplitude is
evaluated at the point. -/
theorem potential_band_of_germ (x : CorrectionStep.CycleState (Label B N0))
    (l : Label B N0) (j : ℤ) (n m : ℕ)
    (hKn : (j : ℝ) * (x.coefficients.blocks l).frequency n ≠ 0)
    (hKm : (j : ℝ) * (x.coefficients.blocks l).frequency m ≠ 0) (z : WaveSpace)
    (ha : (ActualReferenceRebase.actualCoefficients x l j).amplitude n z =
      velocityWeight h (ChartScales.Q n) (ChartScales.Q m) •
        (ActualReferenceRebase.actualCoefficients x l j).amplitude m
          (ActualParticularCoherence.bandMap n m z))
    (hp : (ActualReferenceRebase.actualCoefficients x l j).phase n =ᶠ[𝓝 z]
      fun y => (((j : ℝ) * (x.coefficients.blocks l).frequency m) /
        ((j : ℝ) * (x.coefficients.blocks l).frequency n)) *
          (ActualReferenceRebase.actualCoefficients x l j).phase m
            (ActualParticularCoherence.bandMap n m y)) :
    potential x l j n z = ratioPower (ChartScales.Q n) (ChartScales.Q m) h •
      potential x l j m (ActualParticularCoherence.bandMap n m z) := by
  let d := ActualParticularStageControls.directions (B := B)
  let s := CorrectionStep.ParticularParameters.nativeStrip
      ActualParticularStageControls.associatedStrip
  rw [potential_eq, potential_eq]
  rw [PhysicalCurlCovariance.vectorPotential_congr
    ((j : ℝ) * (x.coefficients.blocks l).frequency n) (fun y : WaveSpace => y.1.1.1)
    (d.radialField n) (fun _ => d.angular) (d.axialField s n)
    (b := fun y => velocityWeight h (ChartScales.Q n) (ChartScales.Q m) •
      (ActualReferenceRebase.actualCoefficients x l j).amplitude m
        (ActualParticularCoherence.bandMap n m y)) hp ha]
  have he := vectorPotential_equiv (ActualParticularCoherence.bandMap n m)
    (L := (j : ℝ) * (x.coefficients.blocks l).frequency m)
    (ratioPower_pos (ChartScales.Q_pos n) (ChartScales.Q_pos m) _).ne'
    (div_ne_zero hKm hKn) hKn (by field_simp [hKn, (mul_ne_zero_iff.mp hKn).2])
    (fun y => y.1.1.1) (fun y => y.1.1.1)
    (d.radialField n) (fun _ => d.angular) (d.axialField s n)
    (d.radialField m) (fun _ => d.angular) (d.axialField s m)
    (ActualParticularCoherence.bandMap_radius n m)
    (ActualParticularCoherence.bandMap_radial B n m)
    (ActualParticularCoherence.bandMap_angular B n m)
    (ActualParticularCoherence.bandMap_axial B n m)
    (velocityWeight h (ChartScales.Q n) (ChartScales.Q m))
    ((ActualReferenceRebase.actualCoefficients x l j).phase m)
    ((ActualReferenceRebase.actualCoefficients x l j).amplitude m) z
  simpa only [potential_weight (ChartScales.Q_pos n) (ChartScales.Q_pos m)] using he

/-- The pressure carrier is transported exactly together with its scalar
coefficient. -/
theorem pressureMode_band_of_values (x : CorrectionStep.CycleState (Label B N0))
    (l : Label B N0) (j : ℤ) (n m : ℕ)
    (hKn : (j : ℝ) * (x.coefficients.blocks l).frequency n ≠ 0) (z : WaveSpace)
    (ha : (ActualReferenceRebase.actualCoefficients x l j).pressure n z =
      pressureWeight h (ChartScales.Q n) (ChartScales.Q m) •
        (ActualReferenceRebase.actualCoefficients x l j).pressure m
          (ActualParticularCoherence.bandMap n m z))
    (hp : (ActualReferenceRebase.actualCoefficients x l j).phase n z =
      (((j : ℝ) * (x.coefficients.blocks l).frequency m) /
        ((j : ℝ) * (x.coefficients.blocks l).frequency n)) *
          (ActualReferenceRebase.actualCoefficients x l j).phase m
            (ActualParticularCoherence.bandMap n m z)) :
    pressureMode x l j n z = pressureWeight h (ChartScales.Q n) (ChartScales.Q m) •
      pressureMode x l j m (ActualParticularCoherence.bandMap n m z) := by
  have hc : carrier ((j : ℝ) * (x.coefficients.blocks l).frequency n)
      ((ActualReferenceRebase.actualCoefficients x l j).phase n) z =
      carrier ((j : ℝ) * (x.coefficients.blocks l).frequency m)
        ((ActualReferenceRebase.actualCoefficients x l j).phase m)
        (ActualParticularCoherence.bandMap n m z) :=
    PhysicalCurlCovariance.carrier_eq_of_products (by
      rw [hp, ← mul_assoc, mul_div_cancel₀ _ hKn])
  rw [pressureMode_eq, pressureMode_eq]
  simp only [mode, ha, hc, Complex.real_smul, mul_assoc]

/-- Current-copy potential covariance is a consequence of actual source
continuity, support/order, and incoming state/block coherence. -/
theorem potential_band (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    (I : ActualParticularCoherence.SourceInputs x l)
    (hfrequency : ∀ n, (x.coefficients.blocks l).frequency n = ChartScales.carrier h n)
    {V : Set TorusInverse.Plane} (hV : IsOpen V) (htime : ∀ s ∈ V, 0 < s.1)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (hmap : MapsTo (GaugeStateCoherence.bandSlowEquiv h n m) V standardRegion.carrier)
    (HS : ActualReferenceRebase.StateComparison x V n m k)
    (HB : ActualReferenceRebase.BlockComparison x l V n m k)
    (j : ℤ) (hj : j ≠ 0) (z : WaveSpace) (hz : z ∈ ActualParticularCoherence.waveDomain V) :
    potential x l j n z = ratioPower (ChartScales.Q n) (ChartScales.Q m) h •
      potential x l j m (ActualParticularCoherence.bandMap n m z) := by
  have hf (a : ℕ) : (x.coefficients.blocks l).frequency a ≠ 0 := by
    rw [hfrequency]
    exact (Scaling.carrier_frequency_pos (ChartScales.epsilon_pos h a)).ne'
  apply potential_band_of_germ x l j n m
    (mul_ne_zero (by exact_mod_cast hj) (hf n))
    (mul_ne_zero (by exact_mod_cast hj) (hf m)) z
  · exact (ActualParticularCoherence.raw_outputs x l I hfrequency hV htime n m k hi HS HB
      j hj z hz (by rw [ActualParticularCoherence.parameterChange_slow]; exact hmap hz)).1
  · filter_upwards [(ActualParticularCoherence.waveDomain_open hV).mem_nhds hz] with y hy
    exact ActualParticularCoherence.phase_band x l n m k hi HB j hj (hf n) (hf m) y hy

/-- The full current harmonic pressure has the square velocity scale. -/
theorem pressureMode_band (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    (I : ActualParticularCoherence.SourceInputs x l)
    (hfrequency : ∀ n, (x.coefficients.blocks l).frequency n = ChartScales.carrier h n)
    {V : Set TorusInverse.Plane} (hV : IsOpen V) (htime : ∀ s ∈ V, 0 < s.1)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (hmap : MapsTo (GaugeStateCoherence.bandSlowEquiv h n m) V standardRegion.carrier)
    (HS : ActualReferenceRebase.StateComparison x V n m k)
    (HB : ActualReferenceRebase.BlockComparison x l V n m k)
    (j : ℤ) (hj : j ≠ 0) (z : WaveSpace) (hz : z ∈ ActualParticularCoherence.waveDomain V) :
    pressureMode x l j n z = pressureWeight h (ChartScales.Q n) (ChartScales.Q m) •
      pressureMode x l j m (ActualParticularCoherence.bandMap n m z) := by
  have hf (a : ℕ) : (x.coefficients.blocks l).frequency a ≠ 0 := by
    rw [hfrequency]
    exact (Scaling.carrier_frequency_pos (ChartScales.epsilon_pos h a)).ne'
  apply pressureMode_band_of_values x l j n m (mul_ne_zero (by exact_mod_cast hj) (hf n)) z
  · exact (ActualParticularCoherence.raw_outputs x l I hfrequency hV htime n m k hi HS HB
      j hj z hz (by rw [ActualParticularCoherence.parameterChange_slow]; exact hmap hz)).2.1
  · exact ActualParticularCoherence.phase_band x l n m k hi HB j hj (hf n) (hf m) z hz

theorem pressureMode_band_sq (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    (I : ActualParticularCoherence.SourceInputs x l)
    (hfrequency : ∀ n, (x.coefficients.blocks l).frequency n = ChartScales.carrier h n)
    {V : Set TorusInverse.Plane} (hV : IsOpen V) (htime : ∀ s ∈ V, 0 < s.1)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (hmap : MapsTo (GaugeStateCoherence.bandSlowEquiv h n m) V standardRegion.carrier)
    (HS : ActualReferenceRebase.StateComparison x V n m k)
    (HB : ActualReferenceRebase.BlockComparison x l V n m k)
    (j : ℤ) (hj : j ≠ 0) (z : WaveSpace) (hz : z ∈ ActualParticularCoherence.waveDomain V) :
    pressureMode x l j n z = (velocityWeight h (ChartScales.Q n) (ChartScales.Q m)) ^ 2 •
      pressureMode x l j m (ActualParticularCoherence.bandMap n m z) := by
  simpa only [pressure_weight (ChartScales.Q_pos n) (ChartScales.Q_pos m)] using
    pressureMode_band x l I hfrequency hV htime n m k hi hmap HS HB j hj z hz

/-- Equality holds as an ambient germ at every point of the open slow
overlap, including all free radial, angular, and fast coordinates. -/
theorem potential_band_germ (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    (I : ActualParticularCoherence.SourceInputs x l)
    (hfrequency : ∀ n, (x.coefficients.blocks l).frequency n = ChartScales.carrier h n)
    {V : Set TorusInverse.Plane} (hV : IsOpen V) (htime : ∀ s ∈ V, 0 < s.1)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (hmap : MapsTo (GaugeStateCoherence.bandSlowEquiv h n m) V standardRegion.carrier)
    (HS : ActualReferenceRebase.StateComparison x V n m k)
    (HB : ActualReferenceRebase.BlockComparison x l V n m k)
    (j : ℤ) (hj : j ≠ 0) (z : WaveSpace) (hz : z ∈ ActualParticularCoherence.waveDomain V) :
    potential x l j n =ᶠ[𝓝 z] fun y => ratioPower (ChartScales.Q n) (ChartScales.Q m) h •
      potential x l j m (ActualParticularCoherence.bandMap n m y) := by
  filter_upwards [(ActualParticularCoherence.waveDomain_open hV).mem_nhds hz] with y hy
  exact potential_band x l I hfrequency hV htime n m k hi hmap HS HB j hj y hy

theorem pressureMode_band_germ (x : CorrectionStep.CycleState (Label B N0)) (l : Label B N0)
    (I : ActualParticularCoherence.SourceInputs x l)
    (hfrequency : ∀ n, (x.coefficients.blocks l).frequency n = ChartScales.carrier h n)
    {V : Set TorusInverse.Plane} (hV : IsOpen V) (htime : ∀ s ∈ V, 0 < s.1)
    (n m k : ℕ) (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (hmap : MapsTo (GaugeStateCoherence.bandSlowEquiv h n m) V standardRegion.carrier)
    (HS : ActualReferenceRebase.StateComparison x V n m k)
    (HB : ActualReferenceRebase.BlockComparison x l V n m k)
    (j : ℤ) (hj : j ≠ 0) (z : WaveSpace) (hz : z ∈ ActualParticularCoherence.waveDomain V) :
    pressureMode x l j n =ᶠ[𝓝 z]
      fun y => pressureWeight h (ChartScales.Q n) (ChartScales.Q m) •
        pressureMode x l j m (ActualParticularCoherence.bandMap n m y) := by
  filter_upwards [(ActualParticularCoherence.waveDomain_open hV).mem_nhds hz] with y hy
  exact pressureMode_band x l I hfrequency hV htime n m k hi hmap HS HB j hj y hy

end NavierStokes.ActualParticularPotentialCoherence

end
end

end

section

/-!
# Removing the native scales from the current particular modes

The native potential and pressure transformation laws imply equality of
their actual physical modes. The angle and Cartesian rotation are the same
at both bands, so the native scale cancels before applying either map.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.CurrentParticularPhysicalCoherence

open ProblemStatement CorrectionState CorrectionStep
open ActualCurrentParticularPhysical

variable {B N0 : ℕ}

/-- Cancel a positive native scale before applying a physical coordinate
map. No regularity or linearity of that later map is required. -/
theorem unscale_of_ratioPower {E : Type*} [MulAction ℝ E]
    {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr) (a : ℝ)
    {v vr : E} (hv : v = PhysicalParticularWave.ratioPower Q Qr a • vr) :
    Q ^ (-a) • v = Qr ^ (-a) • vr := by
  rw [hv, smul_smul, mul_comm (Q ^ (-a)),
    PhysicalParticularWave.ratioPower_cancel hQ hQr]

/-- The actual current-band vector potential becomes independent of the
band once its native transformation law is supplied. -/
theorem localPotentialMode_eq_of_native
    (x : CycleState (Label B N0)) (l : Label B N0) (j : ℤ) (n m : ℕ)
    (w : SpaceTime)
    (hpot : nativePotential x l j n (nativePoint n w) =
      PhysicalParticularWave.ratioPower (ChartScales.Q n) (ChartScales.Q m)
        CorrectionInitialization.ActualPrimary.h •
          nativePotential x l j m (nativePoint m w)) :
    localPotentialMode x l j n w = localPotentialMode x l j m w := by
  have hv := unscale_of_ratioPower (ChartScales.Q_pos n) (ChartScales.Q_pos m)
    CorrectionInitialization.ActualPrimary.h hpot
  change PhysicalCurlCovariance.realVector
      (CartesianCopySource.rotationMap (PhysicalGraphBounds.radialProjection w)
        ((ChartScales.Q n) ^ (-CorrectionInitialization.ActualPrimary.h) •
          nativePotential x l j n (nativePoint n w))) =
    PhysicalCurlCovariance.realVector
      (CartesianCopySource.rotationMap (PhysicalGraphBounds.radialProjection w)
        ((ChartScales.Q m) ^ (-CorrectionInitialization.ActualPrimary.h) •
          nativePotential x l j m (nativePoint m w)))
  rw [hv]

/-- The pressure weight cancels the physical factor with exponent `-2A`.
The real part is taken only after cancelling the complex native modes. -/
theorem localPressureMode_eq_of_native
    (x : CycleState (Label B N0)) (l : Label B N0) (j : ℤ) (n m : ℕ)
    (w : SpaceTime)
    (hp : nativePressure x l j n (nativePoint n w) =
      PhysicalParticularWave.pressureWeight CorrectionInitialization.ActualPrimary.h
        (ChartScales.Q n) (ChartScales.Q m) •
          nativePressure x l j m (nativePoint m w)) :
    localPressureMode x l j n w = localPressureMode x l j m w := by
  have hv := unscale_of_ratioPower (ChartScales.Q_pos n) (ChartScales.Q_pos m)
    (2 * CoordinateAlgebra.A CorrectionInitialization.ActualPrimary.h) hp
  change (ChartScales.Q n) ^ (-2 * CoordinateAlgebra.A CorrectionInitialization.ActualPrimary.h) *
      (nativePressure x l j n (nativePoint n w)).re =
    (ChartScales.Q m) ^ (-2 * CoordinateAlgebra.A CorrectionInitialization.ActualPrimary.h) *
      (nativePressure x l j m (nativePoint m w)).re
  simpa only [Complex.smul_re, smul_eq_mul, neg_mul] using congrArg Complex.re hv

end NavierStokes.CurrentParticularPhysicalCoherence

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.ActualValidBandWaves

open Set Filter Function ProblemStatement
open CorrectionInitialization CorrectionInitialization.ActualPrimary
open scoped Topology ContDiff BigOperators

variable {B N0 : ℕ}

/-- The actual finite current-band potential, in the initializer's label order. -/
noncomputable def localPotential
    (x : CorrectionStep.CycleState (ActualInitialization.Index B N0)) (n : ℕ) : VelocityField :=
  ActualCurrentParticularPhysical.localPotential (ActualCycleParameters.particularState x) n

/-- Local pressure, given by `ActualCurrentParticularPhysical.localPressure
(ActualCycleParameters.particularState x) n`. -/
noncomputable def localPressure
    (x : CorrectionStep.CycleState (ActualInitialization.Index B N0)) (n : ℕ) : PressureField :=
  ActualCurrentParticularPhysical.localPressure (ActualCycleParameters.particularState x) n

/-- One representative of the actual current-band potential formulas. -/
noncomputable def potential
    (x : CorrectionStep.CycleState (ActualInitialization.Index B N0)) (N : ℕ) : VelocityField :=
  ValidDyadicBandCover.field h N (localPotential x)

/-- Pressure, given by `ValidDyadicBandCover.field h N (localPressure x)`. -/
noncomputable def pressure
    (x : CorrectionStep.CycleState (ActualInitialization.Index B N0)) (N : ℕ) : PressureField :=
  ValidDyadicBandCover.field h N (localPressure x)

/-- Glued potential: an abbreviation for `@potential`. -/
noncomputable abbrev gluedPotential := @potential
/-- Glued pressure: an abbreviation for `@pressure`. -/
noncomputable abbrev gluedPressure := @pressure

/-- The same physical polar angle is used in both bands.  The comparison
therefore retains the complete fast fiber instead of choosing new angles. -/
theorem nativePoint_bandMap (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (w : SpaceTime) (hr : 0 < PolarCharts.radius (PhysicalGraphBounds.radialProjection w)) :
    ActualParticularCoherence.bandMap n m (ActualCurrentParticularPhysical.nativePoint n w) =
      ActualCurrentParticularPhysical.nativePoint m w := by
  have hp : 0 < (ActualCurrentParticularPhysical.cylinderPoint w).2 0 := by
    simpa only [ActualCurrentParticularPhysical.cylinderPoint, AxisymmetricResidual.pack_zero]
        using hr
  unfold ActualCurrentParticularPhysical.nativePoint PhysicalParticularWave.nativeMap
  rw [ActualParticularCoherence.bandMap_apply n m k hi,
    ← PhysicalParticularWave.waveEquiv_cylinderChange]
  congr 1
  simpa only [hi] using PhysicalParticularWave.cylinderChange_graph
    (ChartScales.Q_pos n) (ChartScales.Q_pos m) h (CommonWindow.index h n) k hp

theorem nativePoint_parameterChange (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (w : SpaceTime) (hr : 0 < PolarCharts.radius (PhysicalGraphBounds.radialProjection w)) :
    PhysicalParticularWave.parameterChange h (ChartScales.Q n) (ChartScales.Q m)
      (ActualCurrentParticularPhysical.nativePoint n w).1.1 =
      (ActualCurrentParticularPhysical.nativePoint m w).1.1 := by
  have he := nativePoint_bandMap n m k hi w hr
  rw [ActualParticularCoherence.bandMap_apply n m k hi] at he
  exact congrArg (fun z : PhysicalParticularWave.WaveSpace => z.1.1) he

theorem nativePoint_slowChange (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    (w : SpaceTime) (hr : 0 < PolarCharts.radius (PhysicalGraphBounds.radialProjection w)) :
    GaugeStateCoherence.bandSlowEquiv h n m
      (ActualCurrentParticularPhysical.nativePoint n w).1.1.2 =
      (ActualCurrentParticularPhysical.nativePoint m w).1.1.2 := by
  have hs : (PhysicalParticularWave.parameterChange h (ChartScales.Q n) (ChartScales.Q m)
      (ActualCurrentParticularPhysical.nativePoint n w).1.1).2 =
      GaugeStateCoherence.bandSlowEquiv h n m
        (ActualCurrentParticularPhysical.nativePoint n w).1.1.2 :=
    congrArg (fun z : CorrectionStep.CyclePoint => z.2.1)
      (ActualReferenceRebase.associatedChart_stateChart n m 0
        ((ActualCurrentParticularPhysical.nativePoint n w).1.1, 0))
  exact hs.symm.trans (congrArg Prod.snd (nativePoint_parameterChange n m k hi w hr))

theorem nativePoint_overlap (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    {w : SpaceTime} (hn : w ∈ ValidDyadicBandCover.band h n)
    (hm : w ∈ ValidDyadicBandCover.band h m)
    (hr : 0 < PolarCharts.radius (PhysicalGraphBounds.radialProjection w)) :
    (ActualCurrentParticularPhysical.nativePoint n w).1.1.2 ∈
      ActualInitialCoherence.overlap n m := by
  refine ⟨ActualCurrentWaveSupport.nativePoint_parameterDomain n hn, ?_⟩
  change GaugeStateCoherence.bandSlowEquiv h n m
      (ActualCurrentParticularPhysical.nativePoint n w).1.1.2 ∈ standardRegion.carrier
  rw [nativePoint_slowChange n m k hi w hr]
  exact ActualCurrentWaveSupport.nativePoint_parameterDomain m hm

private theorem sum_eq_of_agree_and_zero {ι E : Type*} [AddCommMonoid E]
    (s t : Finset ι) (f g : ι → E) (he : ∀ i, f i = g i)
    (hf : ∀ i, i ∉ s → f i = 0) (hg : ∀ i, i ∉ t → g i = 0) :
    ∑ i ∈ s, f i = ∑ i ∈ t, g i := by
  classical
  calc
    ∑ i ∈ s, f i = ∑ i ∈ s ∪ t, f i :=
      Finset.sum_subset Finset.subset_union_left (fun i _ hi => hf i hi)
    _ = ∑ i ∈ s ∪ t, g i := Finset.sum_congr rfl (fun i _ => he i)
    _ = ∑ i ∈ t, g i :=
      (Finset.sum_subset Finset.subset_union_right (fun i _ hi => hg i hi)).symm

section Incoming

variable {σ : ℝ} {x : CorrectionStep.CycleState (ActualInitialization.Index B N0)}
    {S : ActualInitialization.Index B N0 → ℕ → Set LocalSignedRequest.Point}
    (H : CorrectionStep.CycleAnalyticInvariant ActualInitialization.geometry (commonContext B)
      ActualInitialization.tangentBlock ActualInitialization.envelope S σ x)
    (C : ActualCycleCoherence.Coherent x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (hS : ∀ l n, IsClosed (S l n))
    (hcore : ∀ l n, S l n ⊆ ActualCoreSupport.refinedCarrier l n)

include H

theorem current_frequency (l : ActualParticularStageControls.Label B N0) (n : ℕ) :
    ((ActualCycleParameters.particularState x).coefficients.blocks l).frequency n =
      ChartScales.carrier h n :=
  ActualCycleParameters.current_frequency x (l.2, l.1) (H.carrier (l.2, l.1)) n

include hcore in
theorem refined_support (l : ActualParticularStageControls.Label B N0) :
    HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain
      (ActualCoreSupport.refinedCarrier (l.2, l.1))
      ((ActualCycleParameters.particularState x).coefficients.blocks l)
      ((ActualCycleParameters.particularState x).coefficients.gaussian l)
      ((ActualCycleParameters.particularState x).coefficients.aliasCoefficients l) :=
  ActualCycleAssembly.inputSupport_mono (H.inputSupport (l.2, l.1)) (hcore (l.2, l.1))

theorem nativePotential_eq_actual (l : ActualParticularStageControls.Label B N0)
    (j : ℤ) (n : ℕ) :
    ActualCurrentParticularPhysical.nativePotential (ActualCycleParameters.particularState x) l j n
        =
      ActualParticularPotentialCoherence.potential (ActualCycleParameters.particularState x) l j n
          := by
  rw [ActualParticularPotentialCoherence.potential_eq_copyData]
  unfold ActualCurrentParticularPhysical.nativePotential
  rw [ActualCurrentParticularPhysical.copyData_eq_actual _ _ _ (current_frequency H l)]

theorem nativePressure_eq_actual (l : ActualParticularStageControls.Label B N0)
    (j : ℤ) (n : ℕ) :
    ActualCurrentParticularPhysical.nativePressure (ActualCycleParameters.particularState x) l j n =
      ActualParticularPotentialCoherence.pressureMode (ActualCycleParameters.particularState x) l j
          n := by
  rw [ActualParticularPotentialCoherence.pressureMode_eq_copyData]
  unfold ActualCurrentParticularPhysical.nativePressure
  rw [ActualCurrentParticularPhysical.copyData_eq_actual _ _ _ (current_frequency H l)]

include C hN hcore in
theorem modes_zero_of_inactive (l : ActualParticularStageControls.Label B N0)
    (j : ℤ) (n : ℕ) {w : SpaceTime} (hw : w ∈ ValidDyadicBandCover.band h n)
    (hl : l ∉ (ActualCycleParameters.particularState x).coefficients.labels n) :
    ActualCurrentParticularPhysical.localPotentialMode (ActualCycleParameters.particularState x) l
        j n w = 0 ∧
      ActualCurrentParticularPhysical.localPressureMode (ActualCycleParameters.particularState x) l
          j n w = 0 := by
  apply ActualCurrentWaveSupport.current_modes_zero_off_carrier hN
    (ActualCycleParameters.particularState x) l (refined_support H hcore l) j n hw
  intro hc
  have ha := ActualCyclePreservation.core_active (l.2, l.1) n
    (ActualCurrentWaveSupport.nativePoint_parameterDomain n hw) hc
  have hb : (l.2, l.1) ∈ x.coefficients.labels n := by rwa [C.labels]
  exact hl ((ActualCycleParameters.particularState_mem x n (l.2, l.1)).mpr hb)

include C hS hcore in
theorem modes_eq_ordered (l : ActualParticularStageControls.Label B N0)
    (j : ℤ) (hj : j ≠ 0) (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    {w : SpaceTime} (hn : w ∈ ValidDyadicBandCover.band h n)
    (hm : w ∈ ValidDyadicBandCover.band h m)
    (hr : 0 < PolarCharts.radius (PhysicalGraphBounds.radialProjection w)) :
    ActualCurrentParticularPhysical.localPotentialMode (ActualCycleParameters.particularState x) l
        j n w =
        ActualCurrentParticularPhysical.localPotentialMode (ActualCycleParameters.particularState
            x) l j m w ∧
      ActualCurrentParticularPhysical.localPressureMode (ActualCycleParameters.particularState x) l
          j n w =
        ActualCurrentParticularPhysical.localPressureMode (ActualCycleParameters.particularState x)
            l j m w := by
  have hs := ActualCycleCoherence.particular_source_inputs H hS hcore l
  have ht : ∀ s ∈ ActualInitialCoherence.overlap n m, 0 < s.1 :=
    fun s hs => standardRegion.time_pos s hs.1
  have hmap : MapsTo (GaugeStateCoherence.bandSlowEquiv h n m)
      (ActualInitialCoherence.overlap n m) standardRegion.carrier := fun _ hs => hs.2
  have hz := nativePoint_overlap n m k hi hn hm hr
  have ha := ActualParticularPotentialCoherence.potential_band
    (ActualCycleParameters.particularState x) l hs (current_frequency H l)
    (ActualInitialCoherence.overlap_open n m) ht n m k hi hmap
    (C.reference_state n m k hi) (C.reference_block l n m k hi)
    j hj (ActualCurrentParticularPhysical.nativePoint n w) hz
  have hp := ActualParticularPotentialCoherence.pressureMode_band
    (ActualCycleParameters.particularState x) l hs (current_frequency H l)
    (ActualInitialCoherence.overlap_open n m) ht n m k hi hmap
    (C.reference_state n m k hi) (C.reference_block l n m k hi)
    j hj (ActualCurrentParticularPhysical.nativePoint n w) hz
  rw [nativePoint_bandMap n m k hi w hr, ← nativePotential_eq_actual H l j n,
    ← nativePotential_eq_actual H l j m] at ha
  rw [nativePoint_bandMap n m k hi w hr, ← nativePressure_eq_actual H l j n,
    ← nativePressure_eq_actual H l j m] at hp
  exact ⟨CurrentParticularPhysicalCoherence.localPotentialMode_eq_of_native _ l j n m w ha,
    CurrentParticularPhysicalCoherence.localPressureMode_eq_of_native _ l j n m w hp⟩

include C hN hS hcore in
theorem local_fields_eq_ordered (n m k : ℕ)
    (hi : CommonWindow.index h n + k = CommonWindow.index h m)
    {w : SpaceTime} (hn : w ∈ ValidDyadicBandCover.band h n)
    (hm : w ∈ ValidDyadicBandCover.band h m)
    (hr : 0 < PolarCharts.radius (PhysicalGraphBounds.radialProjection w)) :
    localPotential x n w = localPotential x m w ∧ localPressure x n w = localPressure x m w := by
  have he := fun (l : ActualParticularStageControls.Label B N0) (j : ℤ)
    (hj : j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand) =>
      modes_eq_ordered H C hS hcore l j
        ((ParticularWaveAssembly.mem_modes x.coefficients.residualBand j).mp hj).1 n m k hi hn hm hr
  have hzn := fun l hl j => modes_zero_of_inactive H C hN hcore l j n hn hl
  have hzm := fun l hl j => modes_zero_of_inactive H C hN hcore l j m hm hl
  constructor
  · apply sum_eq_of_agree_and_zero
    · intro l
      exact Finset.sum_congr rfl (fun j hj => (he l j hj).1)
    · intro l hl
      exact Finset.sum_eq_zero (fun j _ => (hzn l hl j).1)
    · intro l hl
      exact Finset.sum_eq_zero (fun j _ => (hzm l hl j).1)
  · apply sum_eq_of_agree_and_zero
    · intro l
      exact Finset.sum_congr rfl (fun j hj => (he l j hj).2)
    · intro l hl
      exact Finset.sum_eq_zero (fun j _ => (hzn l hl j).2)
    · intro l hl
      exact Finset.sum_eq_zero (fun j _ => (hzm l hl j).2)

include C hN hS hcore in
theorem local_fields_eq (n m : ℕ) {w : SpaceTime}
    (hn : w ∈ ValidDyadicBandCover.band h n) (hm : w ∈ ValidDyadicBandCover.band h m) :
    localPotential x n w = localPotential x m w ∧ localPressure x n w = localPressure x m w := by
  by_cases hr : 0 < PolarCharts.radius (PhysicalGraphBounds.radialProjection w)
  · rcases le_total (CommonWindow.index h n) (CommonWindow.index h m) with hle | hle
    · exact local_fields_eq_ordered H C hN hS hcore n m
        (CommonWindow.index h m - CommonWindow.index h n) (Nat.add_sub_of_le hle) hn hm hr
    · have hh := local_fields_eq_ordered H C hN hS hcore m n
        (CommonWindow.index h n - CommonWindow.index h m) (Nat.add_sub_of_le hle) hm hn hr
      exact ⟨hh.1.symm, hh.2.symm⟩
  · have haxis : PhysicalGraphBounds.radialProjection w = 0 := by
      apply norm_eq_zero.mp
      exact le_antisymm ((PolarCharts.norm_le_radius _).trans (le_of_not_gt hr)) (norm_nonneg _)
    have hzn := ActualCurrentWaveSupport.current_local_axis_germs hN
      (ActualCycleParameters.particularState x) (refined_support H hcore) n hn haxis
    have hzm := ActualCurrentWaveSupport.current_local_axis_germs hN
      (ActualCycleParameters.particularState x) (refined_support H hcore) m hm haxis
    exact ⟨hzn.1.eq_of_nhds.trans hzm.1.eq_of_nhds.symm,
      hzn.2.eq_of_nhds.trans hzm.2.eq_of_nhds.symm⟩

include C hN hS hcore in
theorem compatible (N : ℕ) :
    ValidDyadicBandCover.Compatible h N (localPotential x) ∧
      ValidDyadicBandCover.Compatible h N (localPressure x) := by
  constructor
  · intro n m w hw
    exact (local_fields_eq H C hN hS hcore n.val m.val hw.1 hw.2).1
  · intro n m w hw
    exact (local_fields_eq H C hN hS hcore n.val m.val hw.1 hw.2).2

include C hN hS hcore in
theorem potential_germ (N n : ℕ) (hn : N ≤ n) {w : SpaceTime}
    (hw : w ∈ ValidDyadicBandCover.band h n) :
    potential x N =ᶠ[𝓝 w] localPotential x n :=
  ValidDyadicBandCover.field_germ outgoing.data.h_pos outgoing.data.h_lt_half
    (compatible H C hN hS hcore N).1 hn hw

include C hN hS hcore in
theorem pressure_germ (N n : ℕ) (hn : N ≤ n) {w : SpaceTime}
    (hw : w ∈ ValidDyadicBandCover.band h n) :
    pressure x N =ᶠ[𝓝 w] localPressure x n :=
  ValidDyadicBandCover.field_germ outgoing.data.h_pos outgoing.data.h_lt_half
    (compatible H C hN hS hcore N).2 hn hw

include C hN hS hcore in
theorem fields_eq (N n : ℕ) (hn : N ≤ n) {w : SpaceTime}
    (hw : w ∈ ValidDyadicBandCover.band h n) :
    potential x N w = localPotential x n w ∧ pressure x N w = localPressure x n w :=
  ⟨(potential_germ H C hN hS hcore N n hn hw).eq_of_nhds,
    (pressure_germ H C hN hS hcore N n hn hw).eq_of_nhds⟩

include C hN hS hcore in
theorem potential_curl_germ (N n : ℕ) (hn : N ≤ n) {w : SpaceTime}
    (hw : w ∈ ValidDyadicBandCover.band h n) :
    SpatialCurl.spatialCurl (potential x N) =ᶠ[𝓝 w] SpatialCurl.spatialCurl (localPotential x n) :=
  SolenoidalDiagonal.spatialCurl_eventuallyEq (potential_germ H C hN hS hcore N n hn hw)

include C hN hS hcore in
theorem jets_eq (N n : ℕ) (hn : N ≤ n) {w : SpaceTime}
    (hw : w ∈ ValidDyadicBandCover.band h n) (m : ℕ) :
    iteratedFDeriv ℝ m (potential x N) w = iteratedFDeriv ℝ m (localPotential x n) w ∧
      iteratedFDeriv ℝ m (pressure x N) w = iteratedFDeriv ℝ m (localPressure x n) w := by
  have hc := compatible H C hN hS hcore N
  exact ⟨ValidDyadicBandCover.field_jet_eq outgoing.data.h_pos outgoing.data.h_lt_half hc.1 hn hw m,
    ValidDyadicBandCover.field_jet_eq outgoing.data.h_pos outgoing.data.h_lt_half hc.2 hn hw m⟩

include C hN hS hcore in
theorem active_zero_germs {N : ℕ} {qbig : ℝ} (hqbig : qbig ≤ ChartScales.Q N)
    {w : SpaceTime} (hw : w ∈ CutStageEstimates.physicalSublevel h qbig)
    (hX : (SlowBorelBase.cartesianChart h w).2.1 ∉
      Icc (NominalConeAssembly.activeLeft nominal) (NominalConeAssembly.activeRight nominal)) :
    (potential x N =ᶠ[𝓝 w] fun _ => 0) ∧ (pressure x N =ᶠ[𝓝 w] fun _ => 0) := by
  have hc := compatible H C hN hS hcore N
  exact ActualCurrentWaveSupport.current_field_active_germs hN
    (ActualCycleParameters.particularState x) (refined_support H hcore) hc.1 hc.2 hqbig hw hX

include C hN hS hcore in
theorem shrinking_support {N : ℕ} {qbig : ℝ} (hqbig : qbig ≤ ChartScales.Q N) :
    MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant
        qbig (potential x N) ∧
      MixedDiagonalExtensions.SublevelShrinkingSupport h PhysicalStageSupport.actualOuterConstant
        qbig (pressure x N) := by
  have hc := compatible H C hN hS hcore N
  exact ActualCurrentWaveSupport.current_field_support hN
    (ActualCycleParameters.particularState x) (refined_support H hcore) hc.1 hc.2 hqbig

include C hN hS hcore in
theorem axis_zero {N : ℕ} {qbig : ℝ} (hqbig : qbig ≤ ChartScales.Q N) :
    GermCandidateAssembly.AxisZeroOn (MixedAxisPreservation.localDomain h qbig) (potential x N) :=
  ActualCurrentWaveSupport.current_field_axisZeroOn hN
    (ActualCycleParameters.particularState x) (refined_support H hcore)
    (compatible H C hN hS hcore N).1 hqbig

include hcore in
theorem refined_invariant : ActualParticularCycleData.Invariant σ x :=
  { H with inputSupport := fun l => ActualCycleAssembly.inputSupport_mono (H.inputSupport l) (hcore
      l) }

include hN hcore in
theorem local_fields_smooth (n : ℕ) :
    ContDiffOn ℝ ∞ (localPotential x n) (ValidDyadicBandCover.band h n) ∧
      ContDiffOn ℝ ∞ (localPressure x n) (ValidDyadicBandCover.band h n) := by
  have hs (w : SpaceTime) (hw : w ∈ ValidDyadicBandCover.band h n) :
      ContDiffAt ℝ ∞ (localPotential x n) w ∧ ContDiffAt ℝ ∞ (localPressure x n) w := by
    by_cases haxis : PhysicalGraphBounds.radialProjection w = 0
    · have hz := ActualCurrentWaveSupport.current_local_axis_germs hN
        (ActualCycleParameters.particularState x) (refined_support H hcore) n hw haxis
      exact ⟨contDiffAt_const.congr_of_eventuallyEq hz.1, contDiffAt_const.congr_of_eventuallyEq
          hz.2⟩
    · exact ActualCurrentParticularPhysical.localFields_contDiffAt_of_invariant
        (refined_invariant H hcore) hN n (norm_pos_iff.mpr haxis)
        (PhysicalWaveSum.chooseChart ‖PhysicalGraphBounds.radialProjection w‖
          (PhysicalGraphBounds.radialProjection w))
        (ActualCurrentParticularPhysical.chosenChart_valid haxis)
        ⟨ActualCurrentWaveSupport.nativePoint_parameterDomain n hw, Set.mem_univ _⟩
  exact ⟨fun w hw => (hs w hw).1.contDiffWithinAt, fun w hw => (hs w hw).2.contDiffWithinAt⟩

include C hN hS hcore in
theorem fields_smooth {N : ℕ} {qbig : ℝ} (hqbig : qbig ≤ ChartScales.Q N) :
    ContDiffOn ℝ ∞ (potential x N) (CutStageEstimates.physicalSublevel h qbig) ∧
      ContDiffOn ℝ ∞ (pressure x N) (CutStageEstimates.physicalSublevel h qbig) := by
  have hc := compatible H C hN hS hcore N
  exact ⟨ValidDyadicBandCover.field_smooth outgoing.data.h_pos outgoing.data.h_lt_half hc.1 hqbig
      (fun n _ => (local_fields_smooth H hN hcore n).1),
    ValidDyadicBandCover.field_smooth outgoing.data.h_pos outgoing.data.h_lt_half hc.2 hqbig
      (fun n _ => (local_fields_smooth H hN hcore n).2)⟩

end Incoming

end NavierStokes.ActualValidBandWaves

end
end

end

section

/-!
# Physical jet bounds for the actual current particular label sum

The closed label windows bound the number of contributing spatial labels.
The two column choices are retained by the signed-label map and are already
included in the 2250-color palette.  The finite harmonic sum remains explicit.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.CurrentParticularLabelBounds

open Set Function Filter ProblemStatement
open CorrectionState CorrectionStep CorrectionInitialization.ActualPrimary
open scoped Topology ContDiff BigOperators

/-- Label: an abbreviation for `ActualCurrentParticularPhysical.Label B N0`. -/
abbrev Label (B N0 : ℕ) := ActualCurrentParticularPhysical.Label B N0

variable {B N0 : ℕ}

/-- Signed label, given by `ActualPrimaryCovariance.signedLabelOf (l.2, l.1)`. -/
noncomputable def signedLabel (l : Label B N0) : SlotColoring.Label :=
  ActualPrimaryCovariance.signedLabelOf (l.2, l.1)

theorem signedLabel_injective : Injective (signedLabel (B := B) (N0 := N0)) := by
  intro l k he
  have hk := ActualPrimaryCovariance.signedLabelOf_injective he
  exact Prod.ext (congrArg Prod.snd hk) (congrArg Prod.fst hk)

theorem signedLabel_level (l : Label B N0) : 1 ≤ (signedLabel l).1 :=
  l.2.val.property.1

/-- Window position, given by `![AnnularEndpoint.radius w, w.2 2, 1 - w.1]`. -/
noncomputable def windowPosition (w : SpaceTime) : SlotColoring.Position :=
  ![AnnularEndpoint.radius w, w.2 2, 1 - w.1]

/-- Window, given by `(SquaredPartition.logCoordinate (PhysicalWaveSum.physicalQ h w),
windowPosition w)`. -/
noncomputable def window (w : SpaceTime) : LabelSumBounds.WindowPoint :=
  (SquaredPartition.logCoordinate (PhysicalWaveSum.physicalQ h w), windowPosition w)

theorem windowPosition_continuous : Continuous windowPosition := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact AnnularEndpoint.radius_continuous
  · exact (EuclideanSpace.proj 2).continuous.comp continuous_snd
  · exact continuous_const.sub continuous_fst

theorem window_continuousAt {w : SpaceTime} (ht : w ∈ PhysicalWaveSum.preterminal) :
    ContinuousAt window w := by
  have hq := PhysicalWaveSum.physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half ht
  have hc := (PhysicalWaveSum.physicalQ_smoothAt outgoing.data.h_pos
    outgoing.data.h_lt_half ht).continuousAt
  exact (((Real.continuousAt_log hq.ne').comp hc).neg.div_const _).prodMk
    windowPosition_continuous.continuousAt

/-- Chart point, constructed using `ActualCarrierTransport.associatedPoint`. -/
noncomputable def chartPoint (n : ℕ) (w : SpaceTime) : LocalSignedRequest.Point :=
  ActualCarrierTransport.associatedPoint
    (ActualCurrentParticularPhysical.nativePoint n w).1.1
    (ActualCurrentParticularPhysical.nativePoint n w).2

theorem chartPoint_time_pos (n : ℕ) {w : SpaceTime}
    (hw : w ∈ ValidDyadicBandCover.band h n) : 0 < (chartPoint n w).2.1.1 :=
  (ActualCurrentWaveSupport.nativePoint_parameterDomain n hw).1

theorem chartPoint_scale (n : ℕ) {w : SpaceTime} (ht : w ∈ PhysicalWaveSum.preterminal) :
    physicalScale n (chartPoint n w) = PhysicalWaveSum.physicalQ h w := by
  change ChartScales.Q n * SimilarityCoordinates.coordinateQ (2 * h)
    (ActualCurrentParticularPhysical.nativePoint n w).1.1.2 = _
  rw [ActualCurrentWaveSupport.nativePoint_coordinateQ n ht]
  field_simp [(ChartScales.Q_pos n).ne']

theorem chartPoint_position (n : ℕ) (w : SpaceTime) :
    physicalPosition n (chartPoint n w) = windowPosition w := by
  have hs := ActualCurrentWaveSupport.nativePoint_slow n w
  have hr := ActualCurrentWaveSupport.nativePoint_radius n w
  have hQ := (ChartScales.Q_pos n).ne'
  have hp (a : ℝ) : ChartScales.Q n ^ a * ChartScales.Q n ^ (-a) = 1 := by
    rw [← Real.rpow_add (ChartScales.Q_pos n)]
    simp
  funext i
  fin_cases i
  · change Real.sqrt (ChartScales.Q n) *
      (ActualCurrentParticularPhysical.nativePoint n w).1.1.1 = AnnularEndpoint.radius w
    rw [hr, Real.sqrt_eq_rpow, ← mul_assoc, hp, one_mul]
  · change ChartScales.Q n ^ CoordinateAlgebra.D h *
      (ActualCurrentParticularPhysical.nativePoint n w).1.1.2.2 = w.2 2
    rw [hs, ← mul_assoc, hp, one_mul]
  · change ChartScales.Q n *
      (ActualCurrentParticularPhysical.nativePoint n w).1.1.2.1 = 1 - w.1
    rw [hs, mul_div_cancel₀ _ hQ]

/-- The genuine one-mesh native support is contained in the two-mesh
physical box. The column sign does not change the physical box. -/
theorem nativeMask_physicalBox (L : CorrectionInitialization.ActualPrimary.Label B N0)
    (j : Fin 2) {p : PhaseCalculus.Slow}
    (hp : p ∈ tsupport (PrimaryRepresentatives.nativeMask (BaseChartJets.cellBand L)
      (PrimaryGeometryAssembly.label nominal L).2)) :
    position L p ∈ SlotColoring.physicalBox (CoordinateAlgebra.D h) (signedLabel (j, L)) := by
  have hb := PrimaryRepresentatives.nativeMask_tsupport_subset L.val.property.1
    (PrimaryGeometryAssembly.label nominal L).2 hp
  intro i
  have hscale : 0 < ChartScales.Q (BaseChartJets.cellBand L) ^
      SlotColoring.axisExponent (CoordinateAlgebra.D h) i :=
    Real.rpow_pos_of_pos (ChartScales.Q_pos _) _
  have hspacing := SquaredPartition.nativeSpacing_pos L.val.property.1
  have he : position L p i =
      ChartScales.Q (BaseChartJets.cellBand L) ^ SlotColoring.axisExponent (CoordinateAlgebra.D h)
          i *
        PrimaryRepresentatives.position p i := by
    fin_cases i <;> simp [position, PrimaryRepresentatives.position,
      SlotColoring.axisExponent, Real.sqrt_eq_rpow]
  change |position L p i - SlotColoring.width (CoordinateAlgebra.D h) i
      (BaseChartJets.cellBand L) * (((PrimaryGeometryAssembly.label nominal L).2 i : ℤ) : ℝ)| ≤
    2 * SlotColoring.width (CoordinateAlgebra.D h) i (BaseChartJets.cellBand L)
  rw [he]
  simp only [PrimaryRepresentatives.width_eq_scaled_spacing]
  rw [show ChartScales.Q (BaseChartJets.cellBand L) ^ SlotColoring.axisExponent
      (CoordinateAlgebra.D h) i *
      PrimaryRepresentatives.position p i -
      (ChartScales.Q (BaseChartJets.cellBand L) ^ SlotColoring.axisExponent (CoordinateAlgebra.D h)
          i *
        SquaredPartition.nativeSpacing (BaseChartJets.cellBand L)) *
          (((PrimaryGeometryAssembly.label nominal L).2 i : ℤ) : ℝ) =
      ChartScales.Q (BaseChartJets.cellBand L) ^ SlotColoring.axisExponent (CoordinateAlgebra.D h)
          i *
        (PrimaryRepresentatives.position p i - SquaredPartition.nativeSpacing
            (BaseChartJets.cellBand L) *
          (((PrimaryGeometryAssembly.label nominal L).2 i : ℤ) : ℝ)) by ring]
  rw [abs_mul, abs_of_pos hscale]
  have hi := mul_le_mul_of_nonneg_left (hb i) hscale.le
  rw [one_mul] at hi
  refine hi.trans ?_
  have hn := mul_nonneg hscale.le hspacing.le
  have he := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 2 by norm_num) hn
  simp only [one_mul] at he
  exact he

/-- Full refined support, including the native dyadic factor and the slow
mask, puts a physical point in its actual signed label's closed window. -/
theorem refinedCarrier_window (l : Label B N0) (n : ℕ) {w : SpaceTime}
    (hw : w ∈ ValidDyadicBandCover.band h n)
    (hs : chartPoint n w ∈ ActualCoreSupport.refinedCarrier (l.2, l.1) n) :
    window w ∈ LabelSumBounds.closedWindow (CoordinateAlgebra.D h) (signedLabel l) := by
  have hT := chartPoint_time_pos n hw
  obtain ⟨hb, _, hq⟩ := (ActualCoreSupport.mem_refinedCarrier_iff (l.2, l.1) n hT).mp hs
  obtain ⟨k, hk⟩ := hb
  have hslow : ActualPrimaryCovariance.nativePoint n (chartPoint n w) l.2 ∈
      tsupport (PrimaryRepresentatives.nativeMask (BaseChartJets.cellBand l.2)
        (PrimaryGeometryAssembly.label nominal l.2).2) := hk.1
  have hbox := nativeMask_physicalBox l.2 l.1 hslow
  rw [ActualPrimaryCovariance.nativePoint_position, chartPoint_position] at hbox
  have he := ActualPrimaryCovariance.nativePoint_scale n hT l.2
  change ChartScales.Q (BaseChartJets.cellBand l.2) *
    ActualCoreSupport.nativeQ (l.2, l.1) n (chartPoint n w) =
      physicalScale n (chartPoint n w) at he
  rw [chartPoint_scale n hw.1] at he
  have hleft : ChartScales.Q (BaseChartJets.cellBand l.2) / 2 ≤ PhysicalWaveSum.physicalQ h w := by
    have hb := mul_le_mul_of_nonneg_left hq.1 (ChartScales.Q_pos (BaseChartJets.cellBand l.2)).le
    linarith
  have hright : PhysicalWaveSum.physicalQ h w ≤ 2 * ChartScales.Q (BaseChartJets.cellBand l.2) := by
    have hb := mul_le_mul_of_nonneg_left hq.2 (ChartScales.Q_pos (BaseChartJets.cellBand l.2)).le
    linarith
  have hlog := PhysicalWaveSum.logCoordinate_in_band
    (PhysicalWaveSum.physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half hw.1) hleft hright
  refine ⟨?_, hbox⟩
  change SquaredPartition.logCoordinate (PhysicalWaveSum.physicalQ h w) ∈
    Icc ((BaseChartJets.cellBand l.2 : ℝ) - 2) ((BaseChartJets.cellBand l.2 : ℝ) + 2)
  constructor <;> linarith [hlog.1, hlog.2]

theorem current_modes_window
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (x : CycleState (Label B N0)) (l : Label B N0)
    (hs : HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain
      (ActualCoreSupport.refinedCarrier (l.2, l.1)) (x.coefficients.blocks l)
      (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l))
    (j : ℤ) (n : ℕ) {w : SpaceTime} (hw : w ∈ ValidDyadicBandCover.band h n) :
    (ActualCurrentParticularPhysical.localPotentialMode x l j n w ≠ 0 →
      window w ∈ LabelSumBounds.closedWindow (CoordinateAlgebra.D h) (signedLabel l)) ∧
    (ActualCurrentParticularPhysical.localPressureMode x l j n w ≠ 0 →
      window w ∈ LabelSumBounds.closedWindow (CoordinateAlgebra.D h) (signedLabel l)) := by
  have hm := ActualCurrentWaveSupport.current_modes_support hN x l hs j n hw
  exact ⟨fun hv => refinedCarrier_window l n hw (hm.1 hv),
    fun hv => refinedCarrier_window l n hw (hm.2 hv)⟩

/-! ## Finite harmonic sums with uniform spatial multiplicity -/

section Summation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The spatial factor is 2250, independently of the number of labels.
Different harmonics may retain different constants. All jet hypotheses
are pointwise at `w`; the open band is used only for support and germs. -/
theorem finite_modes_jet_bound (n : ℕ) {w : SpaceTime}
    (hw : w ∈ ValidDyadicBandCover.band h n)
    (F : Finset (Label B N0)) (J : Finset ℤ) (f : Label B N0 → ℤ → SpaceTime → E)
    (m : ℕ)
    (hf : ∀ l ∈ F, ∀ j ∈ J, ContDiffAt ℝ m (f l j) w)
    (hs : ∀ l ∈ F, ∀ j ∈ J, ∀ y ∈ ValidDyadicBandCover.band h n, f l j y ≠ 0 →
      window y ∈ LabelSumBounds.closedWindow (CoordinateAlgebra.D h) (signedLabel l))
    (C : ℤ → ℝ) (hC : ∀ j ∈ J, 0 ≤ C j)
    (hb : ∀ l ∈ F, ∀ j ∈ J,
      window w ∈ LabelSumBounds.closedWindow (CoordinateAlgebra.D h) (signedLabel l) →
      ‖iteratedFDeriv ℝ m (f l j) w‖ ≤ C j) :
    ‖iteratedFDeriv ℝ m (fun y => ∑ l ∈ F, ∑ j ∈ J, f l j y) w‖ ≤
      2250 * ∑ j ∈ J, C j := by
  classical
  have hj (j : ℤ) (hj : j ∈ J) :
      ‖iteratedFDeriv ℝ m (fun y => ∑ l ∈ F, f l j y) w‖ ≤ 2250 * C j :=
    LabelSumBounds.finite_sum_jet_bound
      (ValidDyadicBandCover.band_open outgoing.data.h_pos outgoing.data.h_lt_half n) hw
      F signedLabel signedLabel_injective.injOn (fun l _ => signedLabel_level l)
      (CoordinateAlgebra.D h) window (window_continuousAt hw.1) (fun l => f l j) m
      (fun l hl => hf l hl j hj) (fun l hl => hs l hl j hj) (hC j hj)
      (fun l hl => hb l hl j hj)
  have hsm (j : ℤ) (hj : j ∈ J) : ContDiffAt ℝ m (fun y => ∑ l ∈ F, f l j y) w :=
    ContDiffAt.sum (fun l hl => hf l hl j hj)
  have he : (fun y => ∑ l ∈ F, ∑ j ∈ J, f l j y) =
      (fun y => ∑ j ∈ J, ∑ l ∈ F, f l j y) := by
    funext y
    exact Finset.sum_comm
  rw [he, PhysicalWaveSum.iteratedFDeriv_finset_sum_at J hsm]
  calc
    _ ≤ ∑ j ∈ J, ‖iteratedFDeriv ℝ m (fun y => ∑ l ∈ F, f l j y) w‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ J, 2250 * C j := Finset.sum_le_sum hj
    _ = 2250 * ∑ j ∈ J, C j := by rw [Finset.mul_sum]

end Summation

theorem modes_card (N : ℕ) : (ParticularWaveAssembly.modes N).card = 2 * N := by
  classical
  unfold ParticularWaveAssembly.modes
  rw [Finset.card_erase_of_mem (by simp), Int.card_Icc]
  omega

section ActualSums

variable (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (x : CycleState (Label B N0))
    (hs : ∀ l, HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain
      (ActualCoreSupport.refinedCarrier (l.2, l.1)) (x.coefficients.blocks l)
      (x.coefficients.gaussian l) (x.coefficients.aliasCoefficients l))
    (n m : ℕ) {w : SpaceTime} (hw : w ∈ ValidDyadicBandCover.band h n)

include hN hs hw

theorem localPotential_jet_bound (C : ℤ → ℝ)
    (hC : ∀ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand, 0 ≤ C j)
    (hf : ∀ l ∈ x.coefficients.labels n,
      ∀ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand,
      ContDiffAt ℝ m (ActualCurrentParticularPhysical.localPotentialMode x l j n) w)
    (hb : ∀ l ∈ x.coefficients.labels n,
      ∀ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand,
      window w ∈ LabelSumBounds.closedWindow (CoordinateAlgebra.D h) (signedLabel l) →
      ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPotentialMode x l j n) w‖ ≤ C j) :
    ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPotential x n) w‖ ≤
      2250 * ∑ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand, C j :=
  finite_modes_jet_bound n hw (x.coefficients.labels n)
    (ParticularWaveAssembly.modes x.coefficients.residualBand)
    (fun l j => ActualCurrentParticularPhysical.localPotentialMode x l j n) m hf
    (fun l _ j _ _y hy => (current_modes_window hN x l (hs l) j n hy).1) C hC hb

theorem localPressure_jet_bound (C : ℤ → ℝ)
    (hC : ∀ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand, 0 ≤ C j)
    (hf : ∀ l ∈ x.coefficients.labels n,
      ∀ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand,
      ContDiffAt ℝ m (ActualCurrentParticularPhysical.localPressureMode x l j n) w)
    (hb : ∀ l ∈ x.coefficients.labels n,
      ∀ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand,
      window w ∈ LabelSumBounds.closedWindow (CoordinateAlgebra.D h) (signedLabel l) →
      ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPressureMode x l j n) w‖ ≤ C j) :
    ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPressure x n) w‖ ≤
      2250 * ∑ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand, C j :=
  finite_modes_jet_bound n hw (x.coefficients.labels n)
    (ParticularWaveAssembly.modes x.coefficients.residualBand)
    (fun l j => ActualCurrentParticularPhysical.localPressureMode x l j n) m hf
    (fun l _ j _ _y hy => (current_modes_window hN x l (hs l) j n hy).2) C hC hb

theorem localPotential_jet_bound_uniform {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ l ∈ x.coefficients.labels n,
      ∀ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand,
      ContDiffAt ℝ m (ActualCurrentParticularPhysical.localPotentialMode x l j n) w)
    (hb : ∀ l ∈ x.coefficients.labels n,
      ∀ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand,
      window w ∈ LabelSumBounds.closedWindow (CoordinateAlgebra.D h) (signedLabel l) →
      ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPotentialMode x l j n) w‖ ≤ C) :
    ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPotential x n) w‖ ≤
      2250 * (2 * x.coefficients.residualBand : ℕ) * C := by
  have hh := localPotential_jet_bound hN x hs n m hw (fun _ => C) (fun _ _ => hC) hf hb
  simpa only [Finset.sum_const, nsmul_eq_mul, modes_card, mul_assoc] using hh

theorem localPressure_jet_bound_uniform {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ l ∈ x.coefficients.labels n,
      ∀ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand,
      ContDiffAt ℝ m (ActualCurrentParticularPhysical.localPressureMode x l j n) w)
    (hb : ∀ l ∈ x.coefficients.labels n,
      ∀ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand,
      window w ∈ LabelSumBounds.closedWindow (CoordinateAlgebra.D h) (signedLabel l) →
      ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPressureMode x l j n) w‖ ≤ C) :
    ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPressure x n) w‖ ≤
      2250 * (2 * x.coefficients.residualBand : ℕ) * C := by
  have hh := localPressure_jet_bound hN x hs n m hw (fun _ => C) (fun _ _ => hC) hf hb
  simpa only [Finset.sum_const, nsmul_eq_mul, modes_card, mul_assoc] using hh

end ActualSums

/-! ## The incoming actual invariant supplies all mode regularity -/

section Invariant

variable {σ : ℝ} {x : CycleState (ActualInitialization.Index B N0)}
    (H : ActualParticularCycleData.Invariant σ x)
    (hN : ActualCarrierGeometry.geometricThreshold ≤ N0)

include H hN

/-- Per-mode physical smoothness on the whole open valid band, including
the axis. The invariant supplies source regularity and the actual raw
boundary values; at the axis the retained support gives a zero germ. -/
theorem current_modes_contDiffAt (l : Label B N0) (j : ℤ) (hj : j ≠ 0) (n : ℕ)
    {w : SpaceTime} (hw : w ∈ ValidDyadicBandCover.band h n) :
    ContDiffAt ℝ ∞ (ActualCurrentParticularPhysical.localPotentialMode
      (ActualCycleParameters.particularState x) l j n) w ∧
    ContDiffAt ℝ ∞ (ActualCurrentParticularPhysical.localPressureMode
      (ActualCycleParameters.particularState x) l j n) w := by
  by_cases ha : PhysicalGraphBounds.radialProjection w = 0
  · have hs : HarmonicSourceSupport.InputSupportOn ActualInitialization.geometry.domain
        (ActualCoreSupport.refinedCarrier (l.2, l.1))
        ((ActualCycleParameters.particularState x).coefficients.blocks l)
        ((ActualCycleParameters.particularState x).coefficients.gaussian l)
        ((ActualCycleParameters.particularState x).coefficients.aliasCoefficients l) :=
      H.inputSupport (l.2, l.1)
    have hh := ActualCurrentWaveSupport.current_mode_annulus hN
      (ActualCycleParameters.particularState x) l hs j 0
    exact ⟨contDiffAt_const.congr_of_eventuallyEq
      (hh.1.axis_zero_germ outgoing.data.h_pos outgoing.data.h_lt_half
        (PrimaryTargetBounds.leftRadius_pos nominal) (Nat.zero_le n) hw ha),
      contDiffAt_const.congr_of_eventuallyEq
      (hh.2.axis_zero_germ outgoing.data.h_pos outgoing.data.h_lt_half
        (PrimaryTargetBounds.leftRadius_pos nominal) (Nat.zero_le n) hw ha)⟩
  · have hpos : 0 < ‖PhysicalGraphBounds.radialProjection w‖ := norm_pos_iff.mpr ha
    have hc := ActualCurrentParticularPhysical.chosenChart_valid ha
    have hm : ActualCurrentParticularPhysical.nativePoint n w ∈
        ActualCurrentParticularPhysical.nativeDomain :=
      ⟨ActualCurrentWaveSupport.nativePoint_parameterDomain n hw, mem_univ _⟩
    exact ActualCurrentParticularPhysical.localModes_contDiffAt_of_invariant H hN
      (l.2, l.1) j hj n hpos
      (PhysicalWaveSum.chooseChart ‖PhysicalGraphBounds.radialProjection w‖
        (PhysicalGraphBounds.radialProjection w)) hc hm

theorem current_modes_contDiffOn (l : Label B N0) (j : ℤ) (hj : j ≠ 0) (n : ℕ) :
    ContDiffOn ℝ ∞ (ActualCurrentParticularPhysical.localPotentialMode
      (ActualCycleParameters.particularState x) l j n) (ValidDyadicBandCover.band h n) ∧
    ContDiffOn ℝ ∞ (ActualCurrentParticularPhysical.localPressureMode
      (ActualCycleParameters.particularState x) l j n) (ValidDyadicBandCover.band h n) := by
  constructor
  · intro w hw
    exact (current_modes_contDiffAt H hN l j hj n hw).1.contDiffWithinAt
  · intro w hw
    exact (current_modes_contDiffAt H hN l j hj n hw).2.contDiffWithinAt

omit H hN in
private theorem nat_le_infty (m : ℕ) : (m : WithTop ℕ∞) ≤ ∞ :=
  ENat.natCast_le_of_coe_top_le_withTop le_rfl m

theorem localPotential_jet_bound_of_invariant (n m : ℕ) {w : SpaceTime}
    (hw : w ∈ ValidDyadicBandCover.band h n) (C : ℤ → ℝ)
    (hC : ∀ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand, 0 ≤ C j)
    (hb : ∀ l ∈ (ActualCycleParameters.particularState x).coefficients.labels n,
      ∀ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand,
      window w ∈ LabelSumBounds.closedWindow (CoordinateAlgebra.D h) (signedLabel l) →
      ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPotentialMode
        (ActualCycleParameters.particularState x) l j n) w‖ ≤ C j) :
    ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPotential
      (ActualCycleParameters.particularState x) n) w‖ ≤
      2250 * ∑ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand, C j :=
  localPotential_jet_bound hN (ActualCycleParameters.particularState x)
    (fun l => H.inputSupport (l.2, l.1)) n m hw C hC
    (fun l _ j hj => (current_modes_contDiffAt H hN l j
      ((ParticularWaveAssembly.mem_modes _ _).mp hj).1 n hw).1.of_le (nat_le_infty m)) hb

theorem localPressure_jet_bound_of_invariant (n m : ℕ) {w : SpaceTime}
    (hw : w ∈ ValidDyadicBandCover.band h n) (C : ℤ → ℝ)
    (hC : ∀ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand, 0 ≤ C j)
    (hb : ∀ l ∈ (ActualCycleParameters.particularState x).coefficients.labels n,
      ∀ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand,
      window w ∈ LabelSumBounds.closedWindow (CoordinateAlgebra.D h) (signedLabel l) →
      ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPressureMode
        (ActualCycleParameters.particularState x) l j n) w‖ ≤ C j) :
    ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPressure
      (ActualCycleParameters.particularState x) n) w‖ ≤
      2250 * ∑ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand, C j :=
  localPressure_jet_bound hN (ActualCycleParameters.particularState x)
    (fun l => H.inputSupport (l.2, l.1)) n m hw C hC
    (fun l _ j hj => (current_modes_contDiffAt H hN l j
      ((ParticularWaveAssembly.mem_modes _ _).mp hj).1 n hw).2.of_le (nat_le_infty m)) hb

theorem localPotential_jet_bound_uniform_of_invariant (n m : ℕ) {w : SpaceTime}
    (hw : w ∈ ValidDyadicBandCover.band h n) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ l ∈ (ActualCycleParameters.particularState x).coefficients.labels n,
      ∀ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand,
      window w ∈ LabelSumBounds.closedWindow (CoordinateAlgebra.D h) (signedLabel l) →
      ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPotentialMode
        (ActualCycleParameters.particularState x) l j n) w‖ ≤ C) :
    ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPotential
      (ActualCycleParameters.particularState x) n) w‖ ≤
      2250 * (2 * x.coefficients.residualBand : ℕ) * C := by
  have hh := localPotential_jet_bound_of_invariant H hN n m hw (fun _ => C) (fun _ _ => hC) hb
  simpa only [Finset.sum_const, nsmul_eq_mul, modes_card, mul_assoc] using hh

theorem localPressure_jet_bound_uniform_of_invariant (n m : ℕ) {w : SpaceTime}
    (hw : w ∈ ValidDyadicBandCover.band h n) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ l ∈ (ActualCycleParameters.particularState x).coefficients.labels n,
      ∀ j ∈ ParticularWaveAssembly.modes x.coefficients.residualBand,
      window w ∈ LabelSumBounds.closedWindow (CoordinateAlgebra.D h) (signedLabel l) →
      ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPressureMode
        (ActualCycleParameters.particularState x) l j n) w‖ ≤ C) :
    ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPressure
      (ActualCycleParameters.particularState x) n) w‖ ≤
      2250 * (2 * x.coefficients.residualBand : ℕ) * C := by
  have hh := localPressure_jet_bound_of_invariant H hN n m hw (fun _ => C) (fun _ _ => hC) hb
  simpa only [Finset.sum_const, nsmul_eq_mul, modes_card, mul_assoc] using hh

end Invariant

end NavierStokes.CurrentParticularLabelBounds

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.GluedStageEstimates

open Set Function Filter ProblemStatement CorrectionState CorrectionStep
open CorrectionInitialization CorrectionInitialization.ActualPrimary
open ActualPhysicalStageBounds
open scoped ContDiff Topology BigOperators

/-- Bound type used in glued stage estimates. -/
abbrev Bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (qbig : ℝ) (f : SpaceTime → E) (m : ℕ) (r : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ CutStageEstimates.physicalSublevel h qbig,
    PhysicalWaveSum.physicalQ h w ≤ 1 →
    ‖iteratedFDeriv ℝ m f w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^ r

/-- These are the original native signed-wave data, without an unrelated
particular copy-family field. -/
structure SignedInputs (D : Type) [NormedAddCommGroup D] [NormedSpace ℝ D]
    (I K : Type*) where
  /-- Potential of `SignedInputs`, of type `ℕ → PhysicalStageBounds.WaveData h D (Fin 3 × I) K
  (Fin 3)`. -/
  potential : ℕ → PhysicalStageBounds.WaveData h D (Fin 3 × I) K (Fin 3)
  /-- Pressure field of `SignedInputs`, of type `ℕ → PhysicalStageBounds.WaveData h D I K Unit`. -/
  pressure : ℕ → PhysicalStageBounds.WaveData h D I K Unit
  potential_exponent : ∀ j, 1 / 2 + ActualIterationLedger.sigma j - ChartScales.kappa ≤
    (potential j).alpha
  pressure_exponent : ∀ j, 1 + ActualIterationLedger.sigma j - ChartScales.kappa ≤
    (pressure j).alpha
  potential_shift : ∀ j, (potential j).shift = -h
  pressure_shift : ∀ j, (pressure j).shift = -(2 * CoordinateAlgebra.A h)

section FixedRun

variable {B N0 N : ℕ} {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  {I K : Type*}
  (R : ActualStageEstimates.RunData B N0)
  (M : ActualMeanPhysicalData.InitialCycleInput B N0 N
    (fun _ => ActualCycleParameters.fixedParameters B N0))
  (hN : 4 ≤ N) (W : SignedInputs D I K)

/-- Signed mean potential as an element of `VelocityField`. -/
noncomputable def signedMeanPotential (j : ℕ) : VelocityField := fun w =>
  (W.potential j).vector w +
    (ActualStageEstimates.temporalInput R M hN j).family.angularField w +
    (ActualStageEstimates.rankInput R M hN j).family.angularField w

/-- Signed mean pressure, defined pointwise by `(W.pressure j).pressure w +
(ActualStageEstimates.pressureInput R M hN j).family.field w`. -/
noncomputable def signedMeanPressure (j : ℕ) : PressureField := fun w =>
  (W.pressure j).pressure w +
    (ActualStageEstimates.pressureInput R M hN j).family.field w

/-- Direct, given by `(ActualStageEstimates.angularInput R M hN j).family.angularField`. -/
noncomputable def direct (j : ℕ) : VelocityField :=
  (ActualStageEstimates.angularInput R M hN j).family.angularField

theorem signedMeanPotential_smooth {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) (j : ℕ) :
    ContDiffOn ℝ ∞ (signedMeanPotential R M hN W j)
      (CutStageEstimates.physicalSublevel h qbig) :=
  (((W.potential j).vector_smooth outgoing.data.h_pos outgoing.data.h_lt_half).mono
    inter_subset_left).add
      ((ActualStageEstimates.temporalInput R M hN j).angular_smooth
        outgoing.data.h_pos outgoing.data.h_lt_half hq) |>.add
      ((ActualStageEstimates.rankInput R M hN j).angular_smooth
        outgoing.data.h_pos outgoing.data.h_lt_half hq)

theorem signedMeanPressure_smooth {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) (j : ℕ) :
    ContDiffOn ℝ ∞ (signedMeanPressure R M hN W j)
      (CutStageEstimates.physicalSublevel h qbig) :=
  (((W.pressure j).pressure_smooth outgoing.data.h_pos outgoing.data.h_lt_half).mono
    inter_subset_left).add
      ((ActualStageEstimates.pressureInput R M hN j).field_smooth
        outgoing.data.h_pos outgoing.data.h_lt_half hq)

theorem direct_smooth {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) (j : ℕ) :
    ContDiffOn ℝ ∞ (direct R M hN j) (CutStageEstimates.physicalSublevel h qbig) :=
  (ActualStageEstimates.angularInput R M hN j).angular_smooth
    outgoing.data.h_pos outgoing.data.h_lt_half hq

private theorem potential_gain (j : ℕ) :
    ActualIterationLedger.gain h (j + 1) ≤
      h * (W.potential j).alpha + (W.potential j).shift + h := by
  have hg := ActualIterationLedger.gain_le_wave outgoing.data.h_pos.le
    ActualCyclePreservation.kappa_small (Nat.succ_pos j)
  rw [← ActualStageEstimates.nativePotential_eq_ledger j] at hg
  have ha := mul_le_mul_of_nonneg_left (W.potential_exponent j) outgoing.data.h_pos.le
  rw [W.potential_shift]
  linarith

private theorem pressure_gain (j : ℕ) :
    ActualIterationLedger.gain h (j + 1) ≤
      h * (W.pressure j).alpha + (W.pressure j).shift + 2 * CoordinateAlgebra.A h := by
  have hg := ActualIterationLedger.gain_le_wavePressure outgoing.data.h_pos.le
    ActualCyclePreservation.kappa_small (Nat.succ_pos j)
  rw [← ActualStageEstimates.nativePressure_eq_ledger j] at hg
  have ha := mul_le_mul_of_nonneg_left (W.pressure_exponent j) outgoing.data.h_pos.le
  rw [W.pressure_shift]
  linarith

private theorem mean_gain (j : ℕ) :
    ActualIterationLedger.gain h (j + 1) ≤
      h * (1 + ActualIterationLedger.sigma j - 2 * ChartScales.kappa) + 0 := by
  simpa only [← ActualStageEstimates.nativeMean_eq_ledger, add_zero] using
    ActualIterationLedger.gain_le_mean outgoing.data.h_pos.le
      ActualCyclePreservation.kappa_small (Nat.succ_pos j)

theorem signedMeanPotential_bound {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) (j m : ℕ) :
    Bound qbig (signedMeanPotential R M hN W j) m
      (ActualIterationLedger.gain h (j + 1) - PhysicalStageBounds.potentialLoss h h 0 m) := by
  have hs0 := (W.potential j).vector_bound_with_gain
    outgoing.data.h_pos outgoing.data.h_lt_half (potential_gain W j) m
  have hs := weaken_bound (qbig := qbig)
    (s := ActualIterationLedger.gain h (j + 1) - PhysicalStageBounds.potentialLoss h h 0 m)
    outgoing.data.h_pos outgoing.data.h_lt_half
    (sub_le_sub_left (le_max_left _ _) _) (by
      obtain ⟨C, hC, hb⟩ := hs0
      exact ⟨C, hC, fun w hw hqw => hb w hw.1 hqw⟩)
  have ht := weaken_bound
    (s := ActualIterationLedger.gain h (j + 1) - PhysicalStageBounds.potentialLoss h h 0 m)
    outgoing.data.h_pos outgoing.data.h_lt_half (sub_le_sub_left (le_max_right _ _) _)
    ((ActualStageEstimates.temporalInput R M hN j).angular_bound_with_gain
      outgoing.data.h_pos outgoing.data.h_lt_half hq (mean_gain j) m)
  have hr := weaken_bound
    (s := ActualIterationLedger.gain h (j + 1) - PhysicalStageBounds.potentialLoss h h 0 m)
    outgoing.data.h_pos outgoing.data.h_lt_half (sub_le_sub_left (le_max_right _ _) _)
    ((ActualStageEstimates.rankInput R M hN j).angular_bound_with_gain
      outgoing.data.h_pos outgoing.data.h_lt_half hq (mean_gain j) m)
  have ss : ContDiffOn ℝ ∞ (W.potential j).vector
      (CutStageEstimates.physicalSublevel h qbig) :=
    ((W.potential j).vector_smooth outgoing.data.h_pos outgoing.data.h_lt_half).mono
      inter_subset_left
  have st := (ActualStageEstimates.temporalInput R M hN j).angular_smooth
    outgoing.data.h_pos outgoing.data.h_lt_half hq
  exact add_bounds outgoing.data.h_pos outgoing.data.h_lt_half (ss.add st)
    ((ActualStageEstimates.rankInput R M hN j).angular_smooth
      outgoing.data.h_pos outgoing.data.h_lt_half hq)
    (add_bounds outgoing.data.h_pos outgoing.data.h_lt_half ss st hs ht) hr

theorem signedMeanPressure_bound {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) (j m : ℕ) :
    Bound qbig (signedMeanPressure R M hN W j) m
      (ActualIterationLedger.gain h (j + 1) -
        PhysicalStageBounds.pressureLoss h (2 * CoordinateAlgebra.A h) 0 m) := by
  have hs0 := (W.pressure j).pressure_bound_with_gain
    outgoing.data.h_pos outgoing.data.h_lt_half (pressure_gain W j) m
  have hs := weaken_bound (qbig := qbig)
    (s := ActualIterationLedger.gain h (j + 1) -
      PhysicalStageBounds.pressureLoss h (2 * CoordinateAlgebra.A h) 0 m)
    outgoing.data.h_pos outgoing.data.h_lt_half
    (sub_le_sub_left (le_max_left _ _) _) (by
      obtain ⟨C, hC, hb⟩ := hs0
      exact ⟨C, hC, fun w hw hqw => hb w hw.1 hqw⟩)
  have hm := weaken_bound
    (s := ActualIterationLedger.gain h (j + 1) -
      PhysicalStageBounds.pressureLoss h (2 * CoordinateAlgebra.A h) 0 m)
    outgoing.data.h_pos outgoing.data.h_lt_half (sub_le_sub_left (le_max_right _ _) _)
    ((ActualStageEstimates.pressureInput R M hN j).field_bound_with_gain
      outgoing.data.h_pos outgoing.data.h_lt_half hq (mean_gain j) m)
  exact add_bounds outgoing.data.h_pos outgoing.data.h_lt_half
    (((W.pressure j).pressure_smooth outgoing.data.h_pos outgoing.data.h_lt_half).mono
      inter_subset_left)
    ((ActualStageEstimates.pressureInput R M hN j).field_smooth
      outgoing.data.h_pos outgoing.data.h_lt_half hq) hs hm

theorem direct_bound {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) (j m : ℕ) :
    Bound qbig (direct R M hN j) m
      (ActualIterationLedger.gain h (j + 1) - PhysicalStageBounds.directLoss h 0 m) :=
  (ActualStageEstimates.angularInput R M hN j).angular_bound_with_gain
    outgoing.data.h_pos outgoing.data.h_lt_half hq (mean_gain j) m

end FixedRun

/-! ## A physical particular contribution and the same mixed sequence -/

/-- Potential loss, given by `max (L m) (PhysicalStageBounds.potentialLoss h h 0 m)`. -/
noncomputable def potentialLoss (L : ℕ → ℝ) (m : ℕ) : ℝ :=
  max (L m) (PhysicalStageBounds.potentialLoss h h 0 m)

/-- Pressure loss, given by `max (L m) (PhysicalStageBounds.pressureLoss h (2 *
CoordinateAlgebra.A h) 0 m)`. -/
noncomputable def pressureLoss (L : ℕ → ℝ) (m : ℕ) : ℝ :=
  max (L m) (PhysicalStageBounds.pressureLoss h (2 * CoordinateAlgebra.A h) 0 m)

/-- Background loss, constructed using `MixedFiniteBackground.initialBackgroundLoss`. -/
noncomputable def backgroundLoss (L : ℕ → ℝ) (waveAlpha waveShift : ℝ) : ℕ → ℝ :=
  MixedFiniteBackground.initialBackgroundLoss
    (InitializedPhysicalBackground.initialLoss h waveAlpha waveShift
      (1 - ChartScales.kappa) (9 / 10))
    (potentialLoss L) (PhysicalStageBounds.directLoss h 0)

section MixedSequence

variable {B N0 N : ℕ} {D DA0 DP0 : Type}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup DA0] [NormedSpace ℝ DA0]
  [NormedAddCommGroup DP0] [NormedSpace ℝ DP0]
  {I K IA0 KA0 IP0 KP0 : Type*}
  (R : ActualStageEstimates.RunData B N0)
  (M : ActualMeanPhysicalData.InitialCycleInput B N0 N
    (fun _ => ActualCycleParameters.fixedParameters B N0))
  (hN : 4 ≤ N) (W : SignedInputs D I K)
  (particularA : ℕ → VelocityField) (particularP : ℕ → PressureField)

/-- The four literal contributions use the same order as the physical
sequence construction. -/
noncomputable def potential (j : ℕ) : VelocityField := fun w =>
  particularA j w + (W.potential j).vector w +
    (ActualStageEstimates.temporalInput R M hN j).family.angularField w +
    (ActualStageEstimates.rankInput R M hN j).family.angularField w

/-- Pressure, defined pointwise by `particularP j w + (W.pressure j).pressure w +
(ActualStageEstimates.pressureInput R M hN j).family.field w`. -/
noncomputable def pressure (j : ℕ) : PressureField := fun w =>
  particularP j w + (W.pressure j).pressure w +
    (ActualStageEstimates.pressureInput R M hN j).family.field w

theorem potential_eq (j : ℕ) :
    potential R M hN W particularA j =
      fun w => particularA j w + signedMeanPotential R M hN W j w := by
  funext w
  simp only [potential, signedMeanPotential, add_assoc]

theorem pressure_eq (j : ℕ) :
    pressure R M hN W particularP j =
      fun w => particularP j w + signedMeanPressure R M hN W j w := by
  funext w
  simp only [pressure, signedMeanPressure, add_assoc]

variable {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N)

include hq in
theorem potential_smooth
    (hs : ∀ j, ContDiffOn ℝ ∞ (particularA j) (CutStageEstimates.physicalSublevel h qbig))
    (j : ℕ) :
    ContDiffOn ℝ ∞ (potential R M hN W particularA j)
      (CutStageEstimates.physicalSublevel h qbig) := by
  rw [potential_eq]
  exact (hs j).add (signedMeanPotential_smooth R M hN W hq j)

include hq in
theorem pressure_smooth
    (hs : ∀ j, ContDiffOn ℝ ∞ (particularP j) (CutStageEstimates.physicalSublevel h qbig))
    (j : ℕ) :
    ContDiffOn ℝ ∞ (pressure R M hN W particularP j)
      (CutStageEstimates.physicalSublevel h qbig) := by
  rw [pressure_eq]
  exact (hs j).add (signedMeanPressure_smooth R M hN W hq j)

include hq in
theorem potential_bound {L : ℕ → ℝ}
    (hs : ∀ j, ContDiffOn ℝ ∞ (particularA j) (CutStageEstimates.physicalSublevel h qbig))
    (hb : ∀ j m, Bound qbig (particularA j) m (ActualIterationLedger.gain h (j + 1) - L m))
    (j m : ℕ) :
    Bound qbig (potential R M hN W particularA j) m
      (ActualIterationLedger.gain h (j + 1) - potentialLoss L m) := by
  rw [potential_eq]
  apply add_bounds outgoing.data.h_pos outgoing.data.h_lt_half (hs j)
    (signedMeanPotential_smooth R M hN W hq j)
  · exact weaken_bound outgoing.data.h_pos outgoing.data.h_lt_half
      (sub_le_sub_left (le_max_left _ _) _) (hb j m)
  · exact weaken_bound outgoing.data.h_pos outgoing.data.h_lt_half
      (sub_le_sub_left (le_max_right _ _) _) (signedMeanPotential_bound R M hN W hq j m)

include hq in
theorem pressure_bound {L : ℕ → ℝ}
    (hs : ∀ j, ContDiffOn ℝ ∞ (particularP j) (CutStageEstimates.physicalSublevel h qbig))
    (hb : ∀ j m, Bound qbig (particularP j) m (ActualIterationLedger.gain h (j + 1) - L m))
    (j m : ℕ) :
    Bound qbig (pressure R M hN W particularP j) m
      (ActualIterationLedger.gain h (j + 1) - pressureLoss L m) := by
  rw [pressure_eq]
  apply add_bounds outgoing.data.h_pos outgoing.data.h_lt_half (hs j)
    (signedMeanPressure_smooth R M hN W hq j)
  · exact weaken_bound outgoing.data.h_pos outgoing.data.h_lt_half
      (sub_le_sub_left (le_max_left _ _) _) (hb j m)
  · exact weaken_bound outgoing.data.h_pos outgoing.data.h_lt_half
      (sub_le_sub_left (le_max_right _ _) _) (signedMeanPressure_bound R M hN W hq j m)

variable
  (WA : PhysicalStageBounds.WaveData h DA0 IA0 KA0 (Fin 3))
  (WP : PhysicalStageBounds.WaveData h DP0 IP0 KP0 Unit)
  (A Bdirect : ℕ → VelocityField) (P : ℕ → PressureField)

/-- Six field identities on the common open sublevel.  Their only content
is identification of the actual sequence and its physical components. -/
structure Representations : Prop where
  potential_zero : EqOn (A 0)
    (initialPotential certificate modulation upper B WA
      (actualInitialTemporalInput B N0 N hN) (actualInitialRankInput B N0 N hN))
    (CutStageEstimates.physicalSublevel h qbig)
  direct_zero : EqOn (Bdirect 0) (ActualMeanPhysicalData.initialAngularFamily B N0 N).angularField
    (CutStageEstimates.physicalSublevel h qbig)
  pressure_zero : EqOn (P 0)
    (fun w => FinalSlowBase.pressure certificate modulation upper B w +
      initialPressureIncrement WP (actualInitialPressureInput B N0 N hN) w)
    (CutStageEstimates.physicalSublevel h qbig)
  potential_succ : ∀ j, EqOn (potential R M hN W particularA j) (A (j + 1))
    (CutStageEstimates.physicalSublevel h qbig)
  direct_succ : ∀ j, EqOn (direct R M hN j) (Bdirect (j + 1))
    (CutStageEstimates.physicalSublevel h qbig)
  pressure_succ : ∀ j, EqOn (pressure R M hN W particularP j) (P (j + 1))
    (CutStageEstimates.physicalSublevel h qbig)

variable {A Bdirect P}
  (e : Representations R M hN W particularA particularP WA WP A Bdirect P (qbig := qbig))

include e hq

theorem Representations.potential_smooth
    (hs : ∀ j, ContDiffOn ℝ ∞ (particularA j) (CutStageEstimates.physicalSublevel h qbig))
    (j : ℕ) : ContDiffOn ℝ ∞ (A j) (CutStageEstimates.physicalSublevel h qbig) := by
  cases j with
  | zero =>
    exact (initialPotential_smooth certificate modulation upper B WA
      (actualInitialTemporalInput B N0 N hN) (actualInitialRankInput B N0 N hN) hq hq).congr
      (fun _ hw => e.potential_zero hw)
  | succ j =>
    exact (GluedStageEstimates.potential_smooth R M hN W particularA hq hs j).congr
      (fun _ hw => (e.potential_succ j hw).symm)

theorem Representations.direct_smooth (j : ℕ) :
    ContDiffOn ℝ ∞ (Bdirect j) (CutStageEstimates.physicalSublevel h qbig) := by
  cases j with
  | zero =>
    exact ((actualInitialAngularInput B N0 N hN).angular_smooth
      outgoing.data.h_pos outgoing.data.h_lt_half hq).congr (fun _ hw => e.direct_zero hw)
  | succ j =>
    exact (GluedStageEstimates.direct_smooth R M hN hq j).congr
      (fun _ hw => (e.direct_succ j hw).symm)

theorem Representations.pressure_smooth
    (hs : ∀ j, ContDiffOn ℝ ∞ (particularP j) (CutStageEstimates.physicalSublevel h qbig))
    (j : ℕ) : ContDiffOn ℝ ∞ (P j) (CutStageEstimates.physicalSublevel h qbig) := by
  cases j with
  | zero =>
    have hb : ContDiffOn ℝ ∞ (FinalSlowBase.pressure certificate modulation upper B)
        (CutStageEstimates.physicalSublevel h qbig) :=
      (FinalSlowBase.pressure_smooth certificate modulation upper B).mono
        (fun _ hw => ⟨hw.1, mem_univ _⟩)
    exact (hb.add (initialPressureIncrement_smooth WP (actualInitialPressureInput B N0 N hN)
      outgoing.data.h_pos outgoing.data.h_lt_half hq)).congr (fun _ hw => e.pressure_zero hw)
  | succ j =>
    exact (GluedStageEstimates.pressure_smooth R M hN W particularP hq hs j).congr
      (fun _ hw => (e.pressure_succ j hw).symm)

/-- The algebraic consumer of the separate current-particular estimates.
The fixed-run native inputs derive all signed and mean estimates here. -/
theorem represented_raw_bounds {LA LP : ℕ → ℝ}
    (hsA : ∀ j, ContDiffOn ℝ ∞ (particularA j) (CutStageEstimates.physicalSublevel h qbig))
    (hsP : ∀ j, ContDiffOn ℝ ∞ (particularP j) (CutStageEstimates.physicalSublevel h qbig))
    (hbA : ∀ j m, Bound qbig (particularA j) m (ActualIterationLedger.gain h (j + 1) - LA m))
    (hbP : ∀ j m, Bound qbig (particularP j) m (ActualIterationLedger.gain h (j + 1) - LP m)) :
    ∃ CA CB CP : ℕ → ℕ → ℝ,
      (∀ j m, 0 ≤ CA j m ∧ 0 ≤ CB j m ∧ 0 ≤ CP j m) ∧
      CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) A (ActualIterationLedger.gain
          h)
        (potentialLoss LA) CA (fun _ _ => 0)
        (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig) ∧
      CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) Bdirect
          (ActualIterationLedger.gain h)
        (PhysicalStageBounds.directLoss h 0) CB (fun _ _ => 0)
        (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig) ∧
      CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) P (ActualIterationLedger.gain
          h)
        (pressureLoss LP) CP (fun _ _ => 0)
        (PhysicalWaveSum.preterminal ∩ CutStageEstimates.physicalSublevel h qbig) := by
  obtain ⟨CA, hCA, ha⟩ := raw_of_positive_bounds (fun j m =>
    bound_congr outgoing.data.h_pos outgoing.data.h_lt_half (e.potential_succ j)
      (potential_bound R M hN W particularA hq hsA hbA j m))
  obtain ⟨CB, hCB, hb⟩ := raw_of_positive_bounds (fun j m =>
    bound_congr outgoing.data.h_pos outgoing.data.h_lt_half (e.direct_succ j)
      (direct_bound R M hN hq j m))
  obtain ⟨CP, hCP, hp⟩ := raw_of_positive_bounds (fun j m =>
    bound_congr outgoing.data.h_pos outgoing.data.h_lt_half (e.pressure_succ j)
      (pressure_bound R M hN W particularP hq hsP hbP j m))
  exact ⟨CA, CB, CP, fun j m => ⟨hCA j m, hCB j m, hCP j m⟩, ha, hb, hp⟩

/-- The residual floor is fixed to the next band.  Only exact physical
realizations of finite prefixes enter the residual part of the proof. -/
noncomputable def stageEstimatesOfComponentBounds {LA LP : ℕ → ℝ}
    (hsA : ∀ j, ContDiffOn ℝ ∞ (particularA j) (CutStageEstimates.physicalSublevel h qbig))
    (hsP : ∀ j, ContDiffOn ℝ ∞ (particularP j) (CutStageEstimates.physicalSublevel h qbig))
    (hbA : ∀ j m, Bound qbig (particularA j) m (ActualIterationLedger.gain h (j + 1) - LA m))
    (hbP : ∀ j m, Bound qbig (particularP j) m (ActualIterationLedger.gain h (j + 1) - LP m))
    (hqbig : 0 < qbig) (hGeom : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (d : ∀ J, ActualCycleResidualBounds.PhysicalData B (N + 1)
      (ActualCyclePreservation.state B N0 J).state
      (MixedDiagonalResidual.uncutVelocity A Bdirect J)
      (DiagonalJetBounds.uncutPrefix P (J + 1))) :
    MixedCandidateAssembly.StageEstimates h qbig A Bdirect P := by
  let hr := represented_raw_bounds R M hN W particularA particularP hq WA WP e hsA hsP hbA hbP
  let CA := hr.choose
  let CB := hr.choose_spec.choose
  let CP := hr.choose_spec.choose_spec.choose
  have hc := hr.choose_spec.choose_spec.choose_spec
  have hsa := e.potential_smooth R M hN W particularA particularP hq WA WP hsA
  have hsb := e.direct_smooth R M hN W particularA particularP hq WA WP
  have hsp := e.pressure_smooth R M hN W particularA particularP hq WA WP hsP
  refine {
    potential_smooth := hsa
    direct_smooth := hsb
    pressure_smooth := hsp
    gain := ActualIterationLedger.gain h
    gain_zero := ActualIterationLedger.gain_nonneg outgoing.data.h_pos.le 0
    gain_pos := fun _ hj => ActualIterationLedger.gain_pos outgoing.data.h_pos hj
    gain_mono := ActualIterationLedger.gain_monotone outgoing.data.h_pos.le
    gain_top := ActualIterationLedger.gain_tendsto_atTop outgoing.data.h_pos
    potentialLoss := potentialLoss LA
    directLoss := PhysicalStageBounds.directLoss h 0
    pressureLoss := pressureLoss LP
    potentialConstant := CA
    directConstant := CB
    pressureConstant := CP
    potentialLog := fun _ _ => 0
    directLog := fun _ _ => 0
    pressureLog := fun _ _ => 0
    potential_bound := hc.2.1
    direct_bound := hc.2.2.1
    pressure_bound := hc.2.2.2
    backgroundLoss := backgroundLoss LA WA.alpha WA.shift
    residualLoss := ActualCycleResidualBounds.fixedLoss
    finite_background := ?_
    finite_residual := ?_ }
  · have hU := CutStageEstimates.physicalSublevel_open outgoing.data.h_pos outgoing.data.h_lt_half
      qbig
    have hlU := InitializedPhysicalBackground.endpoint_sublevel
      outgoing.data.h_pos outgoing.data.h_lt_half hqbig
    apply MixedFiniteBackground.mixed_background_from_initial hU hlU
      (ActualBaseVelocityBounds.endpoint_past.and hlU)
      (ActualBaseVelocityBounds.endpoint_q_small outgoing.data.h_pos outgoing.data.h_lt_half)
      hsa hsb hc.2.1 hc.2.2.1 (fun j _ => ActualIterationLedger.gain_nonneg outgoing.data.h_pos.le
          j)
    intro m
    simpa only [actualInitialTemporalInput, actualInitialRankInput,
      actualInitialAngularInput, MeanInput.ofMoving, min_self] using
      represented_initial_rate certificate modulation upper B WA
        (actualInitialTemporalInput B N0 N hN) (actualInitialRankInput B N0 N hN)
        (actualInitialAngularInput B N0 N hN) hU hlU e.potential_zero e.direct_zero m
  · exact ActualCycleResidualBounds.finite_residual_rates hGeom (by omega)
      (fun _ => ActualCycleParameters.fixedParameters B N0)
      (fun J => MixedDiagonalResidual.uncutVelocity A Bdirect J)
      (fun J => DiagonalJetBounds.uncutPrefix P (J + 1))
      (fun J => ActualCyclePreservation.broad_invariant (R.invariant J)) d

end MixedSequence

/-! ## The literal fields and native source data of the fixed run -/

/-- Current potential, given by `ActualValidBandWaves.gluedPotential
(ActualCyclePreservation.state B N0 j) N`. -/
noncomputable def currentPotential (B N0 N : ℕ) (j : ℕ) : VelocityField :=
  ActualValidBandWaves.gluedPotential (ActualCyclePreservation.state B N0 j) N

/-- Current pressure, given by `ActualValidBandWaves.gluedPressure
(ActualCyclePreservation.state B N0 j) N`. -/
noncomputable def currentPressure (B N0 N : ℕ) (j : ℕ) : PressureField :=
  ActualValidBandWaves.gluedPressure (ActualCyclePreservation.state B N0 j) N

/-- Transfer a uniform estimate on comparable current bands to their
actual glued representative.  The bound has no factor counting charts. -/
theorem glued_bound_of_local {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ} {f : ℕ → SpaceTime → E} {qbig r : ℝ} (m : ℕ)
    (hf : ValidDyadicBandCover.Compatible h N f) (hq : qbig ≤ ChartScales.Q N)
    (hb : ∃ C : ℝ, 0 ≤ C ∧ ∀ n, N ≤ n → ∀ w ∈ ValidDyadicBandCover.band h n,
      PhysicalWaveSum.physicalQ h w ≤ ChartScales.Q n → PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (f n) w‖ ≤ C * PhysicalWaveSum.physicalQ h w ^ r) :
    Bound qbig (ValidDyadicBandCover.field h N f) m r := by
  obtain ⟨C, hC, hb⟩ := hb
  refine ⟨C, hC, fun w hw hqw => ?_⟩
  exact ValidDyadicBandCover.field_jet_bound_at outgoing.data.h_pos outgoing.data.h_lt_half
    hf hw.1 (hw.2.le.trans hq) m
    (fun n hn hband hcomp => hb n hn w hband hcomp hqw)

private theorem choose_mode_constants {P : ℤ → ℝ → Prop}
    (hP : ∀ k, k ≠ 0 → ∃ C : ℝ, 0 ≤ C ∧ P k C) :
    ∃ C : ℤ → ℝ, (∀ k, 0 ≤ C k) ∧ ∀ k, k ≠ 0 → P k (C k) := by
  classical
  have hs (k : ℤ) : ∃ C : ℝ, 0 ≤ C ∧ (k ≠ 0 → P k C) := by
    by_cases hk : k = 0
    · exact ⟨0, le_rfl, fun hn => (hn hk).elim⟩
    · obtain ⟨C, hC, hc⟩ := hP k hk
      exact ⟨C, hC, fun _ => hc⟩
  choose C hC hc using hs
  exact ⟨C, hC, hc⟩

section HarmonicSums

variable {B N0 : ℕ} {σ : ℝ} {x : CycleState (ActualInitialization.Index B N0)}
  (H : ActualParticularCycleData.Invariant σ x)
  (hGeom : ActualCarrierGeometry.geometricThreshold ≤ N0)

include H hGeom

/-- The actual finite harmonic sum keeps the geometric factor 2250.
The harmonic constants are summed before the band and point are chosen. -/
theorem localPotential_bound_of_modes (m : ℕ) {r : ℝ}
    (hb : ∀ k : ℤ, k ≠ 0 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (l : ActualParticularStageControls.Label B N0) (n : ℕ), 4 ≤ n →
      ∀ w ∈ ValidDyadicBandCover.band h n, PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPotentialMode
        (ActualCycleParameters.particularState x) l k n) w‖ ≤
          C * PhysicalWaveSum.physicalQ h w ^ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n → ∀ w ∈ ValidDyadicBandCover.band h n,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (ActualValidBandWaves.localPotential x n) w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^ r := by
  classical
  obtain ⟨C, hC, hc⟩ := choose_mode_constants hb
  refine ⟨2250 * ∑ k ∈ ParticularWaveAssembly.modes x.coefficients.residualBand, C k,
    mul_nonneg (by norm_num) (Finset.sum_nonneg (fun k _ => hC k)), ?_⟩
  intro n hn w hw hq
  have hq0 := (PhysicalWaveSum.physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half hw.1).le
  have he := CurrentParticularLabelBounds.localPotential_jet_bound_of_invariant H hGeom n m hw
    (fun k => C k * PhysicalWaveSum.physicalQ h w ^ r)
    (fun k _ => mul_nonneg (hC k) (Real.rpow_nonneg hq0 r))
    (fun l _ k hk _ => hc k ((ParticularWaveAssembly.mem_modes _ _).mp hk).1 l n hn w hw hq)
  exact he.trans_eq (by rw [← Finset.sum_mul, mul_assoc])

theorem localPressure_bound_of_modes (m : ℕ) {r : ℝ}
    (hb : ∀ k : ℤ, k ≠ 0 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (l : ActualParticularStageControls.Label B N0) (n : ℕ), 4 ≤ n →
      ∀ w ∈ ValidDyadicBandCover.band h n, PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (ActualCurrentParticularPhysical.localPressureMode
        (ActualCycleParameters.particularState x) l k n) w‖ ≤
          C * PhysicalWaveSum.physicalQ h w ^ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 4 ≤ n → ∀ w ∈ ValidDyadicBandCover.band h n,
      PhysicalWaveSum.physicalQ h w ≤ 1 →
      ‖iteratedFDeriv ℝ m (ActualValidBandWaves.localPressure x n) w‖ ≤
        C * PhysicalWaveSum.physicalQ h w ^ r := by
  classical
  obtain ⟨C, hC, hc⟩ := choose_mode_constants hb
  refine ⟨2250 * ∑ k ∈ ParticularWaveAssembly.modes x.coefficients.residualBand, C k,
    mul_nonneg (by norm_num) (Finset.sum_nonneg (fun k _ => hC k)), ?_⟩
  intro n hn w hw hq
  have hq0 := (PhysicalWaveSum.physicalQ_pos outgoing.data.h_pos outgoing.data.h_lt_half hw.1).le
  have he := CurrentParticularLabelBounds.localPressure_jet_bound_of_invariant H hGeom n m hw
    (fun k => C k * PhysicalWaveSum.physicalQ h w ^ r)
    (fun k _ => mul_nonneg (hC k) (Real.rpow_nonneg hq0 r))
    (fun l _ k hk _ => hc k ((ParticularWaveAssembly.mem_modes _ _).mp hk).1 l n hn w hw hq)
  exact he.trans_eq (by rw [← Finset.sum_mul, mul_assoc])

end HarmonicSums

section ActualRun

variable {B N0 N : ℕ} (R : ActualStageEstimates.RunData B N0)

include R

theorem current_preservesCarriers (j : ℕ) :
    ActualParticularStageControls.PreservesCarriers
      (ActualCycleParameters.particularState (ActualCyclePreservation.state B N0 j)) :=
  ActualParticularCycleData.preservesCarriers (R.invariant j)

theorem current_inputSupport (j : ℕ) :
    ActualParticularStageControls.InputSupport
      (ActualCycleParameters.particularState (ActualCyclePreservation.state B N0 j)) :=
  ActualParticularCycleData.native_inputSupport (R.invariant j)

/-- The source class is derived from the stored residual invariant and
the actual label/coordinate reindexing. -/
theorem current_source_class (j : ℕ) (k : ℤ) (hk : k ≠ 0) :
    LabelSumBounds.UniformWaveClass
      (CommonCoverClass.sourceStrip (ActualParticularControl.angleStrip
          ActualParticularStageControls.slowStrip))
      ActualParticularStageControls.nativeEnvelope (1 / 2 + ActualIterationLedger.sigma j)
      (ActualParticularStageControls.currentSource
        (ActualCycleParameters.particularState (ActualCyclePreservation.state B N0 j)) k) :=
  ActualParticularCycleData.native_source_class (R.invariant j) k hk

theorem current_compatible
    (C : ∀ j, ActualCycleCoherence.Coherent (ActualCyclePreservation.state B N0 j))
    (hGeom : ActualCarrierGeometry.geometricThreshold ≤ N0) (j N : ℕ) :
    ValidDyadicBandCover.Compatible h N
        (ActualValidBandWaves.localPotential (ActualCyclePreservation.state B N0 j)) ∧
      ValidDyadicBandCover.Compatible h N
        (ActualValidBandWaves.localPressure (ActualCyclePreservation.state B N0 j)) :=
  ActualValidBandWaves.compatible (R.invariant j) (C j) hGeom
    ActualCoreSupport.refinedCarrier_closed (fun _ _ => subset_rfl) N

theorem current_fields_smooth
    (C : ∀ j, ActualCycleCoherence.Coherent (ActualCyclePreservation.state B N0 j))
    (hGeom : ActualCarrierGeometry.geometricThreshold ≤ N0)
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) (j : ℕ) :
    ContDiffOn ℝ ∞ (currentPotential B N0 N j) (CutStageEstimates.physicalSublevel h qbig) ∧
      ContDiffOn ℝ ∞ (currentPressure B N0 N j) (CutStageEstimates.physicalSublevel h qbig) :=
  ActualValidBandWaves.fields_smooth (R.invariant j) (C j) hGeom
    ActualCoreSupport.refinedCarrier_closed (fun _ _ => subset_rfl) hq

omit R in
theorem current_label_mem (j n : ℕ) (l : ActualParticularStageControls.Label B N0) :
    l ∈ (ActualCycleParameters.particularState
      (ActualCyclePreservation.state B N0 j)).coefficients.labels n ↔
      (l.2, l.1) ∈ activeLabels standardRegion B N0 n := by
  have hlabels : (ActualCyclePreservation.state B N0 j).coefficients.labels =
      activeLabels standardRegion B N0 := ActualCycleCoherence.state_labels B N0 j
  simpa only [ActualCycleParameters.swap_apply, hlabels] using
    ActualCycleParameters.particularState_mem (ActualCyclePreservation.state B N0 j) n (l.2, l.1)

omit R in
theorem gain_le_current_exponent (j : ℕ) :
    ActualIterationLedger.gain h (j + 1) ≤ h * ((1 / 2 + ActualIterationLedger.sigma j) + 1 / 2) :=
        by
  have hg := ActualIterationLedger.gain_le_wave outgoing.data.h_pos.le
    ActualCyclePreservation.kappa_small (Nat.succ_pos j)
  rw [← ActualStageEstimates.nativePotential_eq_ledger j] at hg
  apply hg.trans
  apply mul_le_mul_of_nonneg_left _ outgoing.data.h_pos.le
  have hk : 0 ≤ ChartScales.kappa := by norm_num [ChartScales.kappa]
  linarith

omit R in
/-- The current-phase loss fits inside the original physical wave loss.
The inequality uses the fixed condition `h < 1/2`. -/
theorem current_loss_le_wave (degree : ℝ) (m : ℕ) :
    degree + (2 * h) * (m : ℝ) + PhysicalGraphBounds.graphLoss m + 1 ≤
      PhysicalGraphBounds.waveLoss h m + degree := by
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hh : 0 ≤ 2 - 3 * h := by linarith [outgoing.data.h_lt_half]
  have hb := mul_nonneg hh hm
  unfold PhysicalGraphBounds.waveLoss
  linarith

omit R in
theorem current_potential_loss_le (m : ℕ) :
    h + (2 * h) * (m : ℝ) + PhysicalGraphBounds.graphLoss m + 1 ≤
      PhysicalStageBounds.potentialLoss h h 0 m :=
  (current_loss_le_wave h m).trans (le_max_left _ _)

omit R in
theorem current_pressure_loss_le (m : ℕ) :
    2 * CoordinateAlgebra.A h + (2 * h) * (m : ℝ) + PhysicalGraphBounds.graphLoss m + 1 ≤
      PhysicalStageBounds.pressureLoss h (2 * CoordinateAlgebra.A h) 0 m :=
  (current_loss_le_wave (2 * CoordinateAlgebra.A h) m).trans (le_max_left _ _)

theorem current_potential_bound
    (C : ∀ j, ActualCycleCoherence.Coherent (ActualCyclePreservation.state B N0 j))
    (hGeom : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (hN : 4 ≤ N) {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) (j m : ℕ) :
    Bound qbig (currentPotential B N0 N j) m
      (ActualIterationLedger.gain h (j + 1) - PhysicalStageBounds.potentialLoss h h 0 m) := by
  obtain ⟨K, hK, hb⟩ := localPotential_bound_of_modes (R.invariant j) hGeom m
    (fun k hk => ActualCurrentParticularBounds.current_potential_mode_bound
      (R.invariant j) hGeom k hk m)
  have hg : Bound qbig (currentPotential B N0 N j) m
      (h * ((1 / 2 + ActualIterationLedger.sigma j) + 1 / 2) -
        ActualCurrentParticularBounds.currentLoss h (2 * h) m) :=
    glued_bound_of_local m (current_compatible R C hGeom j N).1 hq
      ⟨K, hK, fun n hn w hw _ hqw => hb n (hN.trans hn) w hw hqw⟩
  apply weaken_bound outgoing.data.h_pos outgoing.data.h_lt_half _ hg
  have hgain := gain_le_current_exponent j
  have hloss := current_potential_loss_le m
  unfold ActualCurrentParticularBounds.currentLoss
  linarith

theorem current_pressure_bound
    (C : ∀ j, ActualCycleCoherence.Coherent (ActualCyclePreservation.state B N0 j))
    (hGeom : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (hN : 4 ≤ N) {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) (j m : ℕ) :
    Bound qbig (currentPressure B N0 N j) m
      (ActualIterationLedger.gain h (j + 1) -
        PhysicalStageBounds.pressureLoss h (2 * CoordinateAlgebra.A h) 0 m) := by
  obtain ⟨K, hK, hb⟩ := localPressure_bound_of_modes (R.invariant j) hGeom m
    (fun k hk => ActualCurrentParticularBounds.current_pressure_mode_bound
      (R.invariant j) hGeom k hk m)
  have hg : Bound qbig (currentPressure B N0 N j) m
      (h * ((1 / 2 + ActualIterationLedger.sigma j) + 1 / 2) -
        ActualCurrentParticularBounds.currentLoss (2 * CoordinateAlgebra.A h) (2 * h) m) :=
    glued_bound_of_local m (current_compatible R C hGeom j N).2 hq
      ⟨K, hK, fun n hn w hw _ hqw => hb n (hN.trans hn) w hw hqw⟩
  apply weaken_bound outgoing.data.h_pos outgoing.data.h_lt_half _ hg
  have hgain := gain_le_current_exponent j
  have hloss := current_pressure_loss_le m
  unfold ActualCurrentParticularBounds.currentLoss
  linarith

variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {I K : Type*}
  (M : ActualMeanPhysicalData.InitialCycleInput B N0 N
    (fun _ => ActualCycleParameters.fixedParameters B N0))
  (hN : 4 ≤ N) (W : SignedInputs D I K)

/-- The representation record specialized to the exact glued particular
fields and the constructed initial primary wave data. -/
abbrev ActualRepresentations (qbig : ℝ)
    (A Bdirect : ℕ → VelocityField) (P : ℕ → PressureField) : Prop :=
  Representations R M hN W (currentPotential B N0 N) (currentPressure B N0 N)
    (InitialPhysicalData.potentialWaveData B N0) (InitialPhysicalData.pressureWaveData B N0)
    A Bdirect P (qbig := qbig)

/-- The actual glued current-band rates, native signed/mean data, and
exact finite-prefix realizations supply the complete mixed-stage record.
No physical derivative estimate is a premise of this constructor. -/
noncomputable def actualStageEstimates
    (C : ∀ j, ActualCycleCoherence.Coherent (ActualCyclePreservation.state B N0 j))
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) (hqbig : 0 < qbig)
    (hGeom : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (A Bdirect : ℕ → VelocityField) (P : ℕ → PressureField)
    (e : ActualRepresentations R M hN W qbig A Bdirect P)
    (d : ∀ J, ActualCycleResidualBounds.PhysicalData B (N + 1)
      (ActualCyclePreservation.state B N0 J).state
      (MixedDiagonalResidual.uncutVelocity A Bdirect J)
      (DiagonalJetBounds.uncutPrefix P (J + 1))) :
    MixedCandidateAssembly.StageEstimates h qbig A Bdirect P := by
  let E := stageEstimatesOfComponentBounds R M hN W
    (currentPotential B N0 N) (currentPressure B N0 N) hq
    (InitialPhysicalData.potentialWaveData B N0) (InitialPhysicalData.pressureWaveData B N0) e
    (fun j => (current_fields_smooth R C hGeom hq j).1)
    (fun j => (current_fields_smooth R C hGeom hq j).2)
    (current_potential_bound R C hGeom hN hq)
    (current_pressure_bound R C hGeom hN hq) hqbig hGeom d
  have hA : E.potentialLoss = PhysicalStageBounds.potentialLoss h h 0 := by
    funext m
    exact max_self _
  have hP : E.pressureLoss = PhysicalStageBounds.pressureLoss h (2 * CoordinateAlgebra.A h) 0 := by
    funext m
    exact max_self _
  have hBg : E.backgroundLoss = ActualStageEstimates.backgroundLoss 1 (-h) := by
    change backgroundLoss (PhysicalStageBounds.potentialLoss h h 0) 1 (-h) = _
    funext m
    simp only [backgroundLoss, ActualStageEstimates.backgroundLoss,
      MixedFiniteBackground.initialBackgroundLoss, potentialLoss, max_self]
  refine { E with
    potentialLoss := PhysicalStageBounds.potentialLoss h h 0
    pressureLoss := PhysicalStageBounds.pressureLoss h (2 * CoordinateAlgebra.A h) 0
    backgroundLoss := ActualStageEstimates.backgroundLoss 1 (-h)
    potential_bound := ?_
    pressure_bound := ?_
    finite_background := ?_ }
  · rw [← hA]
    exact E.potential_bound
  · rw [← hP]
    exact E.pressure_bound
  · rw [← hBg]
    exact E.finite_background

theorem actualStageEstimates_ledger
    (C : ∀ j, ActualCycleCoherence.Coherent (ActualCyclePreservation.state B N0 j))
    {qbig : ℝ} (hq : qbig ≤ ChartScales.Q N) (hqbig : 0 < qbig)
    (hGeom : ActualCarrierGeometry.geometricThreshold ≤ N0)
    (A Bdirect : ℕ → VelocityField) (P : ℕ → PressureField)
    (e : ActualRepresentations R M hN W qbig A Bdirect P)
    (d : ∀ J, ActualCycleResidualBounds.PhysicalData B (N + 1)
      (ActualCyclePreservation.state B N0 J).state
      (MixedDiagonalResidual.uncutVelocity A Bdirect J)
      (DiagonalJetBounds.uncutPrefix P (J + 1))) :
    let E := actualStageEstimates R M hN W C hq hqbig hGeom A Bdirect P e d
    E.gain = ActualIterationLedger.gain h ∧
      E.potentialLoss = PhysicalStageBounds.potentialLoss h h 0 ∧
      E.directLoss = PhysicalStageBounds.directLoss h 0 ∧
      E.pressureLoss = PhysicalStageBounds.pressureLoss h (2 * CoordinateAlgebra.A h) 0 ∧
      E.backgroundLoss = ActualStageEstimates.backgroundLoss 1 (-h) ∧
      E.residualLoss = ActualCycleResidualBounds.fixedLoss :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end ActualRun

end NavierStokes.GluedStageEstimates
