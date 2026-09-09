/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.CorrectionStep
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualInitialMeanEquation

@[expose] public section

/-!
# The actual angular mean equation along the correction cycle

The analytic input is on the primitive harmonic coefficients and the
actual stream reconstructions.  Incompressibility and the angular mean
identity are conclusions for the literal stored states.
-/

noncomputable section

namespace NavierStokes.CycleMeanEquation

open Set Function Filter MeasureTheory
open CorrectionState CorrectionStep MeanIncrementBounds
open HarmonicCalculus HarmonicFields HarmonicMeanInteraction HarmonicWaveInteraction
open scoped Topology ContDiff BigOperators


variable {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Local regularity of the actual finite harmonic coefficients. -/
structure BlockData (V : Set D) (b : HarmonicBlock D) : Prop where
  phase : ∀ n, ContDiffOn ℝ ∞ (b.phase n) V
  velocity : ∀ n i, HarmonicResidual.SmoothCoefficients V (b.velocity n i)
  pressure : ∀ n, HarmonicResidual.SmoothCoefficients V (b.pressure n)

theorem BlockData.oscillation {V : Set D} {b : HarmonicBlock D} (H : BlockData V b)
    (n : ℕ) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun x => b.oscillation n x i) (LiftedMeanResidual.cylinder V) :=
  Complex.reCLM.contDiff.comp_contDiffOn
    (HarmonicResidual.field_smoothOn (H.velocity n i) (H.phase n) _ _)

theorem BlockData.oscillatoryPressure {V : Set D} {b : HarmonicBlock D} (H : BlockData V b)
    (n : ℕ) : ContDiffOn ℝ ∞ (b.oscillatoryPressure n) (LiftedMeanResidual.cylinder V) :=
  Complex.reCLM.contDiff.comp_contDiffOn
    (HarmonicResidual.field_smoothOn (H.pressure n) (H.phase n) _ _)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem block_oscillation_periodic (V : Set D) (b : HarmonicBlock D) (n : ℕ) (i : Fin 3) :
    LiftedMeanResidual.PeriodicOn V (fun x => b.oscillation n x i) := by
  intro x _ θ
  exact congrArg Complex.re (field_angular_periodic (b.velocity n i) (b.frequency n)
    (b.phase n) (b.angularFrequency n) x θ)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem block_pressure_periodic (V : Set D) (b : HarmonicBlock D) (n : ℕ) :
    LiftedMeanResidual.PeriodicOn V (b.oscillatoryPressure n) := by
  intro x _ θ
  exact congrArg Complex.re (field_angular_periodic (b.pressure n) (b.frequency n)
    (b.phase n) (b.angularFrequency n) x θ)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem block_pressure_continuous (b : HarmonicBlock D) (n : ℕ) (x : D) :
    Continuous (fun θ => b.oscillatoryPressure n (x, θ)) :=
  Complex.continuous_re.comp (field_angular_continuous (b.pressure n) (b.frequency n)
    (b.phase n) (b.angularFrequency n) x)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem block_pressure_mean_zero (b : HarmonicBlock D)
    (hz : ∀ n, b.pressure n 0 = 0) (hk : ∀ n, b.angularFrequency n ≠ 0)
    (n : ℕ) (x : D) : angularAverage b.oscillatoryPressure n x = 0 := by
  change HarmonicResidual.realAngularMean (fun θ =>
    (field (b.pressure n) (b.frequency n) (b.phase n) (b.angularFrequency n) (x, θ)).re) = 0
  rw [HarmonicResidual.realAngularMean_field _ _ _ (hk n), hz]
  rfl

/-- The real and complex cylindrical divergence operators agree on
the actual real-valued components, including their Fréchet derivatives. -/
theorem ofReal_realDivergence (R : D × ℝ → ℝ) (Vr Vθ Vz : D × ℝ → D × ℝ)
    {v : D × ℝ → Fin 3 → ℝ} {x : D × ℝ}
    (hv : ∀ i, DifferentiableAt ℝ (fun y => v y i) x) :
    (LiftedMeanResidual.realDivergence R Vr Vθ Vz v x : ℂ) =
      cylindricalDivergence R Vr Vθ Vz (fun y i => (v y i : ℂ)) x := by
  have hd (V : D × ℝ → D × ℝ) (i : Fin 3) :
      along V (fun y => (v y i : ℂ)) x = ((along V (fun y => v y i) x : ℝ) : ℂ) := by
    exact LinearWaveResidual.along_map Complex.ofRealCLM V (hv i)
  simp only [LiftedMeanResidual.realDivergence, cylindricalDivergence, hd, Complex.ofReal_add,
    Complex.ofReal_div, Complex.real_smul]
  push_cast
  ring

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
/-- A zero velocity harmonic also removes its derivative contribution. -/
theorem singleMode_zero {b : HarmonicBlock D} (hz : ZeroMode b) (n : ℕ) :
    singleMode b 0 n = 0 := by
  have he := amplitude_zero hz n
  ext x i
  simp only [singleMode, HarmonicResidual.vectorField, field, evaluate_single]
  change amplitude b 0 n x.1 i * _ = 0
  rw [he]
  simp

/-- Per-mode solenoidality implies divergence zero for the actual
finite harmonic field. The zero harmonic is controlled explicitly. -/
theorem block_divergence_zero {s : WeightedClasses.StripData D} {c : Context D}
    {b : HarmonicBlock D} (H : BlockData s.domain b) (hz : ZeroMode b)
    (hk : ∀ n, b.angularFrequency n ≠ 0) (hs : ModeSolenoidal s c b)
    (n : ℕ) {x : D × ℝ} (hx : x ∈ LiftedMeanResidual.cylinder s.domain) :
    LiftedMeanResidual.realDivergence (LiftedMeanResidual.liftScalar c.operators.radius)
      (LiftedMeanResidual.radialDirection c n) LiftedMeanResidual.angularDirection
      (LiftedMeanResidual.axialDirection c n) (b.oscillation n) x = 0 := by
  let g := HarmonicResidual.contextFrame c n
  have hreg (i : Fin 3) : HarmonicResidual.SmoothCoefficients s.domain (blockAmplitude b n i) :=
    (H.velocity n i).realCoefficients
  have hsingle (j : ℤ) (θ : ℝ) :
      cylindricalDivergence (fun y => g.radius y.1) (HarmonicResidual.liftDirection g.radial)
        HarmonicResidual.angularDirection (HarmonicResidual.liftDirection g.axial)
        (singleMode b j n) (x.1, θ) = 0 := by
    by_cases hj : j = 0
    · subst j
      rw [singleMode_zero hz n]
      simp [cylindricalDivergence, along]
    · exact hs j hj n (x.1, θ) hx.1
  have hc (j : ℤ) : divergenceCoefficients g (b.frequency n) (b.phase n)
      (b.angularFrequency n) (blockAmplitude b n) j x.1 = 0 := by
    have hfield : ∀ θ, field
        (AddMonoidAlgebra.single j (divergenceCoefficients g (b.frequency n) (b.phase n)
          (b.angularFrequency n) (blockAmplitude b n) j))
        (b.frequency n) (b.phase n) (b.angularFrequency n) (x.1, θ) =
        field 0 (b.frequency n) (b.phase n) (b.angularFrequency n) (x.1, θ) := by
      intro θ
      rw [← divergenceCoefficients_single, field_divergenceCoefficients s.isOpen_domain g
        (b.frequency n) (H.phase n) (b.angularFrequency n)
        (fun i => AddMonoidAlgebra.single j (blockAmplitude b n i j))
        (fun i => smoothCoefficients_single (hreg i j) j) (show (x.1, θ) ∈
          HarmonicResidual.liftDomain s.domain from ⟨hx.1, mem_univ θ⟩),
        HarmonicResidual.field_zero]
      exact hsingle j θ
    have he := coefficient_eq_of_field_eq_at _ 0 (b.frequency n) (b.phase n) (hk n) j x.1 hfield
    simpa only [AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_zero, Finsupp.single_eq_same,
      Finsupp.zero_apply, Pi.zero_apply] using he
  have hfield : HarmonicResidual.vectorField (blockAmplitude b n)
      (b.frequency n) (b.phase n) (b.angularFrequency n) =
      fun y i => (b.oscillation n y i : ℂ) := by
    ext y i
    exact HarmonicResidual.field_realCoefficients _ _ _ _ _
  have hdiv := field_divergenceCoefficients s.isOpen_domain g (b.frequency n) (H.phase n)
    (b.angularFrequency n) (blockAmplitude b n) hreg hx
  rw [hfield, WaveStateRegularity.field_eq_zero_of_coefficients _ _ _ _ _ hc] at hdiv
  apply Complex.ofReal_eq_zero.mp
  rw [ofReal_realDivergence _ _ _ _ (fun i =>
    ((H.oscillation n i).contDiffAt ((LiftedMeanResidual.cylinder_open s.isOpen_domain).mem_nhds
      hx)).differentiableAt
      (by simp))]
  exact hdiv.symm

theorem realDivergence_sum {ι : Type} (J : Finset ι)
    (R : D × ℝ → ℝ) (Vr Vθ Vz : D × ℝ → D × ℝ)
    (v : ι → D × ℝ → Fin 3 → ℝ) {x : D × ℝ}
    (hv : ∀ j ∈ J, ∀ i, DifferentiableAt ℝ (fun y => v j y i) x) :
    LiftedMeanResidual.realDivergence R Vr Vθ Vz (fun y i => ∑ j ∈ J, v j y i) x =
      ∑ j ∈ J, LiftedMeanResidual.realDivergence R Vr Vθ Vz (v j) x := by
  simp only [LiftedMeanResidual.realDivergence,
    ParticularWaveAssembly.along_finset_sum J Vr _ (fun j hj => hv j hj 0),
    ParticularWaveAssembly.along_finset_sum J Vθ _ (fun j hj => hv j hj 1),
    ParticularWaveAssembly.along_finset_sum J Vz _ (fun j hj => hv j hj 2),
    Finset.sum_div, Finset.sum_add_distrib]

theorem fieldSum_divergence_zero {ι : Type} {s : WeightedClasses.StripData D} {c : Context D}
    (labels : ℕ → Finset ι) (b : ι → HarmonicBlock D)
    (H : ∀ l, BlockData s.domain (b l)) (hz : ∀ l, ZeroMode (b l))
    (hk : ∀ l n, (b l).angularFrequency n ≠ 0) (hs : ∀ l, ModeSolenoidal s c (b l))
    (n : ℕ) {x : D × ℝ} (hx : x ∈ LiftedMeanResidual.cylinder s.domain) :
    LiftedMeanResidual.realDivergence (LiftedMeanResidual.liftScalar c.operators.radius)
      (LiftedMeanResidual.radialDirection c n) LiftedMeanResidual.angularDirection
      (LiftedMeanResidual.axialDirection c n)
      (LabelSumBounds.fieldSum labels (fun l => (b l).oscillation) n) x = 0 := by
  change LiftedMeanResidual.realDivergence _ _ _ _ (fun y i => ∑ l ∈ labels n,
    (b l).oscillation n y i) x = 0
  rw [realDivergence_sum _ _ _ _ _ _ (fun l _ i =>
    (((H l).oscillation n i).contDiffAt
      ((LiftedMeanResidual.cylinder_open s.isOpen_domain).mem_nhds hx)).differentiableAt (by simp))]
  exact Finset.sum_eq_zero (fun l _ => block_divergence_zero (H l) (hz l) (hk l) (hs l) n hx)

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem pressureSum_mean_zero {ι : Type} (labels : ℕ → Finset ι) (b : ι → HarmonicBlock D)
    (hz : ∀ l n, (b l).pressure n 0 = 0) (hk : ∀ l n, (b l).angularFrequency n ≠ 0)
    (n : ℕ) (x : D) :
    angularAverage (fun n y => ∑ l ∈ labels n, (b l).oscillatoryPressure n y) n x = 0 := by
  change HarmonicResidual.realAngularMean (fun θ =>
    ∑ l ∈ labels n, (b l).oscillatoryPressure n (x, θ)) = 0
  rw [HarmonicResidual.realAngularMean_sum (labels n) _
    (fun l _ => block_pressure_continuous (b l) n x)]
  exact Finset.sum_eq_zero (fun l _ => block_pressure_mean_zero (b l) (hz l) (hk l) n x)

abbrev Point := CyclePoint
abbrev Plane := PressureStream.Plane

/-- Inputs on the existing state, the two actual waves, and the primitive
stream construction. No outgoing divergence or mean equation is a field. -/
structure StepData {ι : Type} {coord : ℝ} (U : LocalSignedRequest.SlowRegion coord)
    (p : CycleParameters ι) (v : CycleCoefficients ι) (c : Context Point) (u : State Point) : Prop
      where
  inner_pos : 0 < p.gauge.radial.inner
  exponent_pos : 0 < p.gauge.radial.exponent
  length : ∀ n, p.gauge.length n = VariableGaugeMean.qLength coord
  domain : p.strip.domain ⊆ LocalRankDefect.positiveDomain U.carrier
  primitive : MeanStateRegularity.PrimitiveData U p.gauge.radial.inner p.gauge.radial.outer c u
  particular_covariance : ∀ i j, GaugeMomentBalances.MovingField U
    p.gauge.radial.inner p.gauge.radial.outer
    (SignedMeanGain.covarianceIncrement u.oscillation (p.particularVelocity v c u) i j)
  signed_covariance : ∀ i j, GaugeMomentBalances.MovingField U
    p.gauge.radial.inner p.gauge.radial.outer
    (SignedMeanGain.covarianceIncrement (p.afterParticular v c u).oscillation
      (p.signedVelocity v c u) i j)
  rank : LocalRankDefect.RankGeometry p.gauge p.rank U.carrier c u
  operators : ∃ slowTime : Plane × Plane, ∃ temporal : Plane,
    c.operators = graphOperators p.gauge.radial c.operators.epsilon c.operators.fastCoefficient
      p.axial slowTime temporal
  particular_regular : ∀ l, BlockData p.strip.domain (p.particularBlock v c u l)
  signed_regular : ∀ l, BlockData p.strip.domain (p.signedBlock v c u l)
  particular_solenoidal : ∀ l, ModeSolenoidal p.strip c (p.particularBlock v c u l)
  signed_solenoidal : ∀ l, ModeSolenoidal p.strip c (p.signedBlock v c u l)
  angular : ∀ l n, (v.blocks l).angularFrequency n ≠ 0
  signed_carrier : ∀ l, SameCarrier (v.blocks l) (p.signedBlock v c u l)

theorem particular_pressure_zero {ι : Type} (p : CycleParameters ι) (v : CycleCoefficients ι)
    (c : Context Point) (u : State Point) (l : ι) (n : ℕ) :
    (p.particularBlock v c u l).pressure n 0 = 0 := by
  ext x
  exact congrFun ((ParticularWaveAssembly.assembledBlock_zero _ _ _ _ _ _).2 n) (cycleAssoc x)

theorem signed_pressure_zero {ι : Type} (p : CycleParameters ι) (v : CycleCoefficients ι)
    (c : Context Point) (u : State Point) (l : ι) (n : ℕ) :
    (p.signedBlock v c u l).pressure n 0 = 0 :=
  (p.signed l).exactBlock_pressure_zero p.strip (p.signedRequest v c u) n

theorem gaugeWaveStage_divergence (g : VariableGaugeMean.GaugeData Plane)
    (c : Context Point) (u : State Point) (w : Oscillation Point) (q : OscillatoryScalar Point)
    (e : ExcludedErrors Point) (n : ℕ) (x : Point × ℝ)
    (hu : ∀ i, DifferentiableAt ℝ (fun y => u.totalVelocity c n y i) x)
    (hw : ∀ i, DifferentiableAt ℝ (fun y => w n y i) x) :
    fullDivergence c (gaugeWaveStage g c u w q e) n x = fullDivergence c u n x +
      LiftedMeanResidual.realDivergence (LiftedMeanResidual.liftScalar c.operators.radius)
        (LiftedMeanResidual.radialDirection c n) LiftedMeanResidual.angularDirection
        (LiftedMeanResidual.axialDirection c n) (w n) x := by
  have hz : meanLift (zeroTriple : Triple Point) = 0 := by
    ext n y i
    fin_cases i <;> rfl
  have hi (i : Fin 3) : DifferentiableAt ℝ
      (fun y => meanLift (zeroTriple : Triple Point) n y i + w n y i) x := by
    simpa only [hz, Pi.zero_apply, zero_add] using hw i
  have he := fullDivergence_actual_update c u zeroTriple 0 w q e n x hu hi
  change fullDivergence c (u.addIncrement zeroTriple 0 w q e) n x = _
  simp only [hz, Pi.zero_apply, zero_add] at he
  exact he

theorem next_errors_total {ι : Type} (p : CycleParameters ι) (v : CycleCoefficients ι)
    (c : Context Point) (u : State Point) :
    (p.next v c u).errors.total = u.errors.total + p.particularGaussian v c u +
      p.signedGaussian v c u + (fun n x => p.nextAxisymmetricAlias v c u 0 n x.1) := by
  unfold ExcludedErrors.total
  rw [p.next_base_error, p.next_gaussian_error, p.next_alias_lift]
  ext n x i
  simp only [Pi.add_apply]
  ring

namespace StepData

variable {ι : Type} {coord : ℝ} {U : LocalSignedRequest.SlowRegion coord}
    {p : CycleParameters ι} {v : CycleCoefficients ι} {c : Context Point} {u : State Point}
    (H : StepData U p v c u)

include H

theorem particular_angular (l : ι) (n : ℕ) :
    (p.particularBlock v c u l).angularFrequency n ≠ 0 := H.angular l n

theorem signed_angular (l : ι) (n : ℕ) :
    (p.signedBlock v c u l).angularFrequency n ≠ 0 := by
  rw [(H.signed_carrier l).angular]
  exact H.angular l n

theorem particular_smooth (n : ℕ) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun x => p.particularVelocity v c u n x i)
      (LiftedMeanResidual.cylinder p.strip.domain) :=
  ContDiffOn.sum (fun l _ => (H.particular_regular l).oscillation n i)

theorem signed_smooth (n : ℕ) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun x => p.signedVelocity v c u n x i)
      (LiftedMeanResidual.cylinder p.strip.domain) :=
  ContDiffOn.sum (fun l _ => (H.signed_regular l).oscillation n i)

theorem particular_divergence (n : ℕ) {x : Point × ℝ}
    (hx : x ∈ LiftedMeanResidual.cylinder p.strip.domain) :
    LiftedMeanResidual.realDivergence (LiftedMeanResidual.liftScalar c.operators.radius)
      (LiftedMeanResidual.radialDirection c n) LiftedMeanResidual.angularDirection
      (LiftedMeanResidual.axialDirection c n) (p.particularVelocity v c u n) x = 0 :=
  fieldSum_divergence_zero v.labels (p.particularBlock v c u) H.particular_regular
    (p.particularBlock_zero v c u) H.particular_angular H.particular_solenoidal n hx

theorem signed_divergence (n : ℕ) {x : Point × ℝ}
    (hx : x ∈ LiftedMeanResidual.cylinder p.strip.domain) :
    LiftedMeanResidual.realDivergence (LiftedMeanResidual.liftScalar c.operators.radius)
      (LiftedMeanResidual.radialDirection c n) LiftedMeanResidual.angularDirection
      (LiftedMeanResidual.axialDirection c n) (p.signedVelocity v c u n) x = 0 :=
  fieldSum_divergence_zero v.labels (p.signedBlock v c u) H.signed_regular
    (fun l => (p.signed l).exactBlock_zero p.strip (p.signedRequest v c u))
    H.signed_angular H.signed_solenoidal n hx

theorem next_oscillation_smooth
    (hu : ∀ n i, ContDiffOn ℝ ∞ (fun x => u.oscillation n x i)
      (LiftedMeanResidual.cylinder p.strip.domain)) (n : ℕ) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun x => (p.next v c u).oscillation n x i)
      (LiftedMeanResidual.cylinder p.strip.domain) := by
  rw [p.next_oscillation]
  exact ((hu n i).add (H.particular_smooth n i)).add (H.signed_smooth n i)

theorem next_pressure_smooth
    (hu : ∀ n, ContDiffOn ℝ ∞ (u.oscillatoryPressure n)
      (LiftedMeanResidual.cylinder p.strip.domain)) (n : ℕ) :
    ContDiffOn ℝ ∞ ((p.next v c u).oscillatoryPressure n)
      (LiftedMeanResidual.cylinder p.strip.domain) := by
  rw [p.next_oscillatoryPressure]
  exact ((hu n).add (ContDiffOn.sum fun l _ => (H.particular_regular l).oscillatoryPressure n)).add
    (ContDiffOn.sum fun l _ => (H.signed_regular l).oscillatoryPressure n)

omit H in
theorem next_oscillation_periodic
    (hu : ∀ n i, LiftedMeanResidual.PeriodicOn p.strip.domain (fun x => u.oscillation n x i))
    (n : ℕ) (i : Fin 3) :
    LiftedMeanResidual.PeriodicOn p.strip.domain (fun x => (p.next v c u).oscillation n x i) := by
  rw [p.next_oscillation]
  intro x hx θ
  change u.oscillation n (x, θ + _) i + (∑ l ∈ v.labels n,
    (p.particularBlock v c u l).oscillation n (x, θ + _) i) + (∑ l ∈ v.labels n,
    (p.signedBlock v c u l).oscillation n (x, θ + _) i) = _
  have hux := hu n i x hx θ
  change u.oscillation n (x, θ + LiftedMeanResidual.period) i = u.oscillation n (x, θ) i at hux
  rw [hux]
  congr 1
  · congr 1
    exact Finset.sum_congr rfl (fun l _ => block_oscillation_periodic _ _ n i x hx θ)
  · exact Finset.sum_congr rfl (fun l _ => block_oscillation_periodic _ _ n i x hx θ)

omit H in
theorem next_pressure_periodic
    (hu : ∀ n, LiftedMeanResidual.PeriodicOn p.strip.domain (u.oscillatoryPressure n)) (n : ℕ) :
    LiftedMeanResidual.PeriodicOn p.strip.domain ((p.next v c u).oscillatoryPressure n) := by
  rw [p.next_oscillatoryPressure]
  intro x hx θ
  change u.oscillatoryPressure n (x, θ + _) + (∑ l ∈ v.labels n,
    (p.particularBlock v c u l).oscillatoryPressure n (x, θ + _)) + (∑ l ∈ v.labels n,
    (p.signedBlock v c u l).oscillatoryPressure n (x, θ + _)) = _
  rw [hu n x hx θ]
  congr 1
  · congr 1
    exact Finset.sum_congr rfl (fun l _ => block_pressure_periodic _ _ n x hx θ)
  · exact Finset.sum_congr rfl (fun l _ => block_pressure_periodic _ _ n x hx θ)

theorem next_oscillation_mean_zero
    (hu : ∀ n i, ContDiffOn ℝ ∞ (fun x => u.oscillation n x i)
      (LiftedMeanResidual.cylinder p.strip.domain))
    (hz : ∀ n x, x ∈ p.strip.domain → ∀ i,
      angularAverage (fun k y => u.oscillation k y i) n x = 0)
    (n : ℕ) {x : Point} (hx : x ∈ p.strip.domain) (i : Fin 3) :
    angularAverage (fun k y => (p.next v c u).oscillation k y i) n x = 0 := by
  have huc := LiftedMeanResidual.continuous_slice p.strip.isOpen_domain (hu n i).continuousOn hx
  have hpc : Continuous (fun θ => p.particularVelocity v c u n (x, θ) i) :=
    LabelSumBounds.fieldSum_angularContinuous v.labels
    (fun l => (p.particularBlock v c u l).oscillation) (fun _ =>
      CorrectionStep.block_angularContinuous _) n x i
  have hsc : Continuous (fun θ => p.signedVelocity v c u n (x, θ) i) :=
    LabelSumBounds.fieldSum_angularContinuous v.labels
    (fun l => (p.signedBlock v c u l).oscillation) (fun _ => CorrectionStep.block_angularContinuous
      _) n x i
  have hpz : angularMeanVector (p.particularVelocity v c u) n x i = 0 :=
    congrFun (congrFun (congrFun (fieldSum_angularMean_zero v.labels
    (p.particularBlock v c u) (p.particularBlock_zero v c u) H.particular_angular) n) x) i
  have hsz : angularMeanVector (p.signedVelocity v c u) n x i = 0 :=
    congrFun (congrFun (congrFun (fieldSum_angularMean_zero v.labels
    (p.signedBlock v c u) (fun l => (p.signed l).exactBlock_zero _ _) H.signed_angular) n) x) i
  rw [p.next_oscillation]
  change HarmonicResidual.realAngularMean (fun θ =>
    (u.oscillation n (x, θ) i + p.particularVelocity v c u n (x, θ) i) +
      p.signedVelocity v c u n (x, θ) i) = 0
  rw [HarmonicResidual.realAngularMean_add (huc.fun_add hpc) hsc,
    HarmonicResidual.realAngularMean_add huc hpc]
  change angularAverage (fun k y => u.oscillation k y i) n x +
    angularMeanVector (p.particularVelocity v c u) n x i +
    angularMeanVector (p.signedVelocity v c u) n x i = 0
  rw [hz n x hx i, hpz, hsz]
  norm_num

theorem next_pressure_mean_zero
    (hu : ∀ n, ContDiffOn ℝ ∞ (u.oscillatoryPressure n)
      (LiftedMeanResidual.cylinder p.strip.domain))
    (hz : ∀ n x, x ∈ p.strip.domain → angularAverage u.oscillatoryPressure n x = 0)
    (n : ℕ) {x : Point} (hx : x ∈ p.strip.domain) :
    angularAverage (p.next v c u).oscillatoryPressure n x = 0 := by
  have huc := LiftedMeanResidual.continuous_slice p.strip.isOpen_domain (hu n).continuousOn hx
  have hpc : Continuous (fun θ => p.particularPressure v c u n (x, θ)) :=
    continuous_finsetSum (v.labels n) (fun l _ =>
    block_pressure_continuous (p.particularBlock v c u l) n x)
  have hsc : Continuous (fun θ => p.signedPressure v c u n (x, θ)) :=
    continuous_finsetSum (v.labels n) (fun l _ =>
    block_pressure_continuous (p.signedBlock v c u l) n x)
  rw [p.next_oscillatoryPressure]
  change HarmonicResidual.realAngularMean (fun θ =>
    (u.oscillatoryPressure n (x, θ) + p.particularPressure v c u n (x, θ)) +
      p.signedPressure v c u n (x, θ)) = 0
  rw [HarmonicResidual.realAngularMean_add (huc.fun_add hpc) hsc,
    HarmonicResidual.realAngularMean_add huc hpc]
  change angularAverage u.oscillatoryPressure n x +
    angularAverage (p.particularPressure v c u) n x +
    angularAverage (p.signedPressure v c u) n x = 0
  have hpz : angularAverage (p.particularPressure v c u) n x = 0 :=
    pressureSum_mean_zero v.labels (p.particularBlock v c u)
      (particular_pressure_zero p v c u) H.particular_angular n x
  have hsz : angularAverage (p.signedPressure v c u) n x = 0 :=
    pressureSum_mean_zero v.labels (p.signedBlock v c u)
      (signed_pressure_zero p v c u) H.signed_angular n x
  rw [hz n x hx, hpz, hsz]
  norm_num

omit H in
theorem next_excluded_continuous
    (hu : ∀ n x, x ∈ p.strip.domain → ∀ i,
      Continuous (fun θ => u.errors.total n (x, θ) i))
    (n : ℕ) {x : Point} (hx : x ∈ p.strip.domain) (i : Fin 3) :
    Continuous (fun θ => (p.next v c u).errors.total n (x, θ) i) := by
  rw [next_errors_total]
  have hs := p.gaussianIncrement_angularContinuous v c u
  change Continuous (fun θ => ((u.errors.total n (x, θ) i + p.particularGaussian v c u n (x, θ) i) +
    p.signedGaussian v c u n (x, θ) i) + p.nextAxisymmetricAlias v c u 0 n x i)
  exact (((hu n x hx i).add (hs.1 n x i)).add (hs.2 n x i)).add continuous_const

end StepData

theorem meanHypotheses_angularData {V : Set Point} {c : Context Point} {u : State Point}
    (H : LiftedMeanResidual.MeanHypotheses V c u) : ActualInitialMeanEquation.AngularData V u :=
  ⟨H.oscillation_smooth, H.oscillatoryPressure_smooth, H.oscillation_periodic,
    H.oscillatoryPressure_periodic, H.oscillation_mean_zero, H.oscillatoryPressure_mean_zero,
    H.base_error_continuous, H.excluded_continuous⟩

namespace StepData

variable {ι : Type} {coord : ℝ} {U : LocalSignedRequest.SlowRegion coord}
    {p : CycleParameters ι} {v : CycleCoefficients ι} {c : Context Point} {u : State Point}
    (H : StepData U p v c u)

include H

theorem next_angularData (HA : ActualInitialMeanEquation.AngularData p.strip.domain u) :
    ActualInitialMeanEquation.AngularData p.strip.domain (p.next v c u) := by
  refine ⟨H.next_oscillation_smooth HA.velocity_smooth,
    H.next_pressure_smooth HA.pressure_smooth,
    next_oscillation_periodic HA.velocity_periodic,
    next_pressure_periodic HA.pressure_periodic,
    fun n x hx i => H.next_oscillation_mean_zero HA.velocity_smooth HA.velocity_mean_zero n hx i,
    fun n x hx => H.next_pressure_mean_zero HA.pressure_smooth HA.pressure_mean_zero n hx,
    ?_, fun n x hx i => next_excluded_continuous HA.excluded_continuous n hx i⟩
  intro n x hx i
  rw [p.next_base_error]
  exact HA.base_error_continuous n x hx i

/-- Each wave contributes zero actual divergence; both subsequent mean
increments are the genuine divergence-free stream reconstructions. -/
theorem next_fullDivergence
    (hu : ∀ n i, ContDiffOn ℝ ∞ (fun x => u.oscillation n x i)
      (LiftedMeanResidual.cylinder p.strip.domain))
    (n : ℕ) {x : Point × ℝ} (hx : x ∈ LiftedMeanResidual.cylinder p.strip.domain) :
    fullDivergence c (p.next v c u) n x = fullDivergence c u n x := by
  obtain ⟨slowTime, temporal, hop⟩ := H.operators
  have HP₁ : MeanStateRegularity.PrimitiveData U p.gauge.radial.inner p.gauge.radial.outer
      c (p.afterParticular v c u) :=
    H.primitive.waveStage p.gauge (p.particularVelocity v c u) (p.particularPressure v c u)
      (p.particularGaussian v c u) H.particular_covariance
  have HP₂ : MeanStateRegularity.PrimitiveData U p.gauge.radial.inner p.gauge.radial.outer
      c (p.afterSigned v c u) :=
    HP₁.waveStage p.gauge (p.signedVelocity v c u) (p.signedPressure v c u)
      (p.signedGaussian v c u) H.signed_covariance
  have hs₁ (k : ℕ) (i : Fin 3) : ContDiffOn ℝ ∞
      (fun y => (p.afterParticular v c u).oscillation k y i)
      (LiftedMeanResidual.cylinder p.strip.domain) :=
    (hu k i).add (H.particular_smooth k i)
  have hs₂ (k : ℕ) (i : Fin 3) : ContDiffOn ℝ ∞
      (fun y => (p.afterSigned v c u).oscillation k y i)
      (LiftedMeanResidual.cylinder p.strip.domain) :=
    (hs₁ k i).add (H.signed_smooth k i)
  have HPt : MeanStateRegularity.PrimitiveData U p.gauge.radial.inner p.gauge.radial.outer
      c (p.afterTemporal v c u) :=
    MeanStageRegularity.temporalStage_primitive HP₂ H.inner_pos H.exponent_pos H.length rfl
      p.timeExponent p.commonIndex p.axial
  have hst (k : ℕ) (i : Fin 3) : ContDiffOn ℝ ∞
      (fun y => (p.afterTemporal v c u).oscillation k y i)
      (LiftedMeanResidual.cylinder p.strip.domain) := by
    simpa only [CycleParameters.afterTemporal, VariableGaugeMean.temporalStageState,
      VariableGaugeMean.reconstructState, State.addIncrement, Pi.add_apply, Pi.zero_apply, add_zero]
      using hs₂ k i
  have hgt := MeanStageRegularity.rankGeometry_for_state HPt H.inner_pos
    p.gauge.radial.inner_lt_outer H.rank
  have hnhds := (LiftedMeanResidual.cylinder_open p.strip.isOpen_domain).mem_nhds hx
  have du₀ (i : Fin 3) : DifferentiableAt ℝ (fun y => u.totalVelocity c n y i) x :=
    ((ActualInitialMeanEquation.totalVelocity_smooth_of_primitive H.primitive H.domain hu n
      i).contDiffAt
      hnhds).differentiableAt (by simp)
  have du₁ (i : Fin 3) : DifferentiableAt ℝ
      (fun y => (p.afterParticular v c u).totalVelocity c n y i) x :=
    ((ActualInitialMeanEquation.totalVelocity_smooth_of_primitive HP₁ H.domain hs₁ n i).contDiffAt
      hnhds).differentiableAt (by simp)
  have du₂ (i : Fin 3) : DifferentiableAt ℝ
      (fun y => (p.afterSigned v c u).totalVelocity c n y i) x :=
    ((ActualInitialMeanEquation.totalVelocity_smooth_of_primitive HP₂ H.domain hs₂ n i).contDiffAt
      hnhds).differentiableAt (by simp)
  have dut (i : Fin 3) : DifferentiableAt ℝ
      (fun y => (p.afterTemporal v c u).totalVelocity c n y i) x :=
    ((ActualInitialMeanEquation.totalVelocity_smooth_of_primitive HPt H.domain hst n i).contDiffAt
      hnhds).differentiableAt (by simp)
  have hw₁ := gaugeWaveStage_divergence p.gauge c u (p.particularVelocity v c u)
    (p.particularPressure v c u) ⟨0, p.particularGaussian v c u, 0⟩ n x du₀
    (fun i => ((H.particular_smooth n i).contDiffAt hnhds).differentiableAt (by simp))
  rw [H.particular_divergence n hx, add_zero] at hw₁
  have hw₂ := gaugeWaveStage_divergence p.gauge c (p.afterParticular v c u) (p.signedVelocity v c u)
    (p.signedPressure v c u) ⟨0, p.signedGaussian v c u, 0⟩ n x du₁
    (fun i => ((H.signed_smooth n i).contDiffAt hnhds).differentiableAt (by simp))
  rw [H.signed_divergence n hx, add_zero] at hw₂
  have ht := ActualInitialMeanEquation.temporalStage_fullDivergence_local HP₂ H.inner_pos
    H.exponent_pos H.length rfl p.timeExponent p.commonIndex p.axial slowTime temporal hop
    n (H.domain hx.1).2 (H.domain hx.1).1.ne' x.2 du₂
  have hr := ActualInitialMeanEquation.rankStage_fullDivergence_local hgt H.length
    p.axial slowTime temporal hop n (H.domain hx.1).2 (H.domain hx.1).1.ne' x.2 dut
  exact hr.trans (ht.trans (hw₂.trans hw₁))

/-- The complete primitive mean-PDE hypotheses are preserved by the
actual four updates, including pressure reconstruction and error refresh. -/
theorem next_meanHypotheses (HM : LiftedMeanResidual.MeanHypotheses p.strip.domain c u) :
    LiftedMeanResidual.MeanHypotheses p.strip.domain c (p.next v c u) := by
  have HP := p.next_primitive v c u U H.inner_pos H.exponent_pos H.length H.primitive
    H.particular_covariance H.signed_covariance H.rank
  apply ActualInitialMeanEquation.meanHypotheses_of_primitive HP.1 H.inner_pos H.exponent_pos
    H.length (p.next_reconstructed v c u) p.strip.isOpen_domain H.domain
    (H.next_angularData (meanHypotheses_angularData HM)) HM.base_divergence
  intro n x hx
  exact (H.next_fullDivergence HM.oscillation_smooth n hx).trans (HM.total_divergence n x hx)

theorem next_angularMean_fullGoodResidual
    (HM : LiftedMeanResidual.MeanHypotheses p.strip.domain c u)
    (n : ℕ) {x : Point} (hx : x ∈ p.strip.domain) (i : Fin 3) :
    angularMeanVector (fullGoodResidual c (p.next v c u)) n x i =
      (p.next v c u).meanGoodResidual c n x i :=
  LiftedMeanResidual.angularMean_fullGoodResidual (H.next_meanHypotheses HM) n hx i

end StepData

/-- A fixed local domain is used throughout the actual stored iteration.
The step inputs are on its constructed waves and streams, not mean identities. -/
theorem iterate_meanHypotheses {ι : Type} {coord : ℝ}
    (U : LocalSignedRequest.SlowRegion coord) (p : ℕ → CycleParameters ι)
    (c : Context Point) (seed : CycleState ι) (V : Set Point)
    (hV : ∀ j, (p j).strip.domain = V)
    (H₀ : LiftedMeanResidual.MeanHypotheses V c seed.state)
    (H : ∀ j, StepData U (p j) (CycleState.iterate p c seed j).coefficients c
      (CycleState.iterate p c seed j).state) (j : ℕ) :
    LiftedMeanResidual.MeanHypotheses V c (CycleState.iterate p c seed j).state := by
  induction j with
  | zero => exact H₀
  | succ j ih =>
    have hi : LiftedMeanResidual.MeanHypotheses (p j).strip.domain c
        (CycleState.iterate p c seed j).state := by simpa only [hV j] using ih
    have hn := (H j).next_meanHypotheses hi
    change LiftedMeanResidual.MeanHypotheses V c
      ((p j).next (CycleState.iterate p c seed j).coefficients c (CycleState.iterate p c seed
        j).state)
    simpa only [hV j] using hn

theorem iterate_divergence_zero {ι : Type} {coord : ℝ}
    (U : LocalSignedRequest.SlowRegion coord) (p : ℕ → CycleParameters ι)
    (c : Context Point) (seed : CycleState ι) (V : Set Point)
    (hV : ∀ j, (p j).strip.domain = V)
    (H₀ : LiftedMeanResidual.MeanHypotheses V c seed.state)
    (H : ∀ j, StepData U (p j) (CycleState.iterate p c seed j).coefficients c
      (CycleState.iterate p c seed j).state)
    (j n : ℕ) {x : Point × ℝ} (hx : x ∈ LiftedMeanResidual.cylinder V) :
    fullDivergence c (CycleState.iterate p c seed j).state n x = 0 :=
  (iterate_meanHypotheses U p c seed V hV H₀ H j).total_divergence n x hx

theorem iterate_angularMean_fullGoodResidual {ι : Type} {coord : ℝ}
    (U : LocalSignedRequest.SlowRegion coord) (p : ℕ → CycleParameters ι)
    (c : Context Point) (seed : CycleState ι) (V : Set Point)
    (hV : ∀ j, (p j).strip.domain = V)
    (H₀ : LiftedMeanResidual.MeanHypotheses V c seed.state)
    (H : ∀ j, StepData U (p j) (CycleState.iterate p c seed j).coefficients c
      (CycleState.iterate p c seed j).state)
    (j n : ℕ) {x : Point} (hx : x ∈ V) (i : Fin 3) :
    angularMeanVector (fullGoodResidual c (CycleState.iterate p c seed j).state) n x i =
      (CycleState.iterate p c seed j).state.meanGoodResidual c n x i :=
  LiftedMeanResidual.angularMean_fullGoodResidual (iterate_meanHypotheses U p c seed V hV H₀ H j) n
    hx i

/-- Specialization to the literal initializer: its mean-PDE hypotheses
come from the proved initialization theorem, not an additional premise. -/
theorem iterate_meanHypotheses_of_initialized {ι : Type} {coord : ℝ}
    (U : LocalSignedRequest.SlowRegion coord) (B N0 : ℕ)
    (p : ℕ → CycleParameters ι) (seed : CycleState ι)
    (hseed : seed.state = ActualInitialCoherence.initialized B N0)
    (hV : ∀ j, (p j).strip.domain = ActualInitialMeanEquation.strip.domain)
    (H : ∀ j, StepData U (p j)
      (CycleState.iterate p (CorrectionInitialization.ActualPrimary.commonContext B) seed
        j).coefficients
      (CorrectionInitialization.ActualPrimary.commonContext B)
      (CycleState.iterate p (CorrectionInitialization.ActualPrimary.commonContext B) seed j).state)
    (j : ℕ) :
    LiftedMeanResidual.MeanHypotheses ActualInitialMeanEquation.strip.domain
      (CorrectionInitialization.ActualPrimary.commonContext B)
      (CycleState.iterate p (CorrectionInitialization.ActualPrimary.commonContext B) seed j).state
        := by
  apply iterate_meanHypotheses U p (CorrectionInitialization.ActualPrimary.commonContext B)
    seed ActualInitialMeanEquation.strip.domain hV ?_ H j
  rw [hseed]
  exact ActualInitialMeanEquation.initialized_meanHypotheses B N0

theorem iterate_angularMean_fullGoodResidual_of_initialized {ι : Type} {coord : ℝ}
    (U : LocalSignedRequest.SlowRegion coord) (B N0 : ℕ)
    (p : ℕ → CycleParameters ι) (seed : CycleState ι)
    (hseed : seed.state = ActualInitialCoherence.initialized B N0)
    (hV : ∀ j, (p j).strip.domain = ActualInitialMeanEquation.strip.domain)
    (H : ∀ j, StepData U (p j)
      (CycleState.iterate p (CorrectionInitialization.ActualPrimary.commonContext B) seed
        j).coefficients
      (CorrectionInitialization.ActualPrimary.commonContext B)
      (CycleState.iterate p (CorrectionInitialization.ActualPrimary.commonContext B) seed j).state)
    (j n : ℕ) {x : Point} (hx : x ∈ ActualInitialMeanEquation.strip.domain) (i : Fin 3) :
    angularMeanVector (fullGoodResidual (CorrectionInitialization.ActualPrimary.commonContext B)
      (CycleState.iterate p (CorrectionInitialization.ActualPrimary.commonContext B) seed j).state)
        n x i =
      (CycleState.iterate p (CorrectionInitialization.ActualPrimary.commonContext B) seed
        j).state.meanGoodResidual
        (CorrectionInitialization.ActualPrimary.commonContext B) n x i :=
  LiftedMeanResidual.angularMean_fullGoodResidual
    (iterate_meanHypotheses_of_initialized U B N0 p seed hseed hV H j) n hx i

end NavierStokes.CycleMeanEquation
