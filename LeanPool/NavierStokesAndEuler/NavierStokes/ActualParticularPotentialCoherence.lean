/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualParticularCoherence

@[expose] public section

/-!
# Coherence of the actual current-band particular potential

The common copy coefficient is retained, including its cutoffs.  Its vector
potential is transported before taking the physical curl.  The derivative
identity uses an invertible linear chart and does not require an additional
smoothness assumption on the phase.
-/

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
