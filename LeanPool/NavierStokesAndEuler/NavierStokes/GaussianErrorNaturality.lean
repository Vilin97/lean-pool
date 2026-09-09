/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.CorrectionStep

@[expose] public section

/-!
# Naturality of the actual Gaussian cutoff error

The error is the sum of differentiated-cutoff terms and the uncovered
source. Both terms are transported from their primitive data before the
copy sum is taken.
-/

noncomputable section

namespace NavierStokes.GaussianErrorNaturality

open Set Filter Function HarmonicCalculus LinearWaveBounds
open scoped Topology ContDiff

section CopyTransport

variable {D E I : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fast_cutoff_transport (Γ : D →L[ℝ] E)
    (d : GraphDirections D) (dr : GraphDirections E)
    (a : PeriodizedWaveBounds.CopyData D I) (b : PeriodizedWaveBounds.CopyData E I)
    (n nr : ℕ) (rate : ℝ) (i : I) (x : D)
    (hcutoff : a.cutoff n i = fun y => b.cutoff nr i (Γ y))
    (hfast : Γ (d.fastField n x) = rate • dr.fastField nr (Γ x))
    (hdiff : DifferentiableAt ℝ (b.cutoff nr i) (Γ x)) :
    d.Dfast (fun m => a.cutoff m i) n x =
      rate * dr.Dfast (fun m => b.cutoff m i) nr (Γ x) := by
  have hc := hdiff.hasFDerivAt.comp x Γ.hasFDerivAt
  simp only [Function.comp_def] at hc
  simp only [GraphDirections.Dfast, along, hcutoff, hc.fderiv,
    ContinuousLinearMap.comp_apply, hfast, map_smul, smul_eq_mul]

theorem cutoffSum_transport (Γ : D →L[ℝ] E)
    (a : PeriodizedWaveBounds.CopyData D I) (b : PeriodizedWaveBounds.CopyData E I)
    (n nr : ℕ) (x : D)
    (hcutoff : ∀ i, a.cutoff n i x = b.cutoff nr i (Γ x)) :
    a.cutoffSum n x = b.cutoffSum nr (Γ x) := by
  exact tsum_congr hcutoff

theorem localTail_transport (Γ : D →L[ℝ] E)
    (d : GraphDirections D) (dr : GraphDirections E)
    (a : PeriodizedWaveBounds.CopyData D I) (b : PeriodizedWaveBounds.CopyData E I)
    (n nr : ℕ) (rate c : ℝ) (i : I) (x : D)
    (hcutoff : a.cutoff n i = fun y => b.cutoff nr i (Γ y))
    (hfast : Γ (d.fastField n x) = rate • dr.fastField nr (Γ x))
    (hdiff : DifferentiableAt ℝ (b.cutoff nr i) (Γ x))
    (hamplitude : dr.Dfast (fun m => b.cutoff m i) nr (Γ x) ≠ 0 →
      a.amplitude n i x = c • b.amplitude nr i (Γ x)) :
    a.localTail d n i x = (rate * c) • b.localTail dr nr i (Γ x) := by
  unfold PeriodizedWaveBounds.CopyData.localTail
  rw [fast_cutoff_transport Γ d dr a b n nr rate i x hcutoff hfast hdiff]
  by_cases hz : dr.Dfast (fun m => b.cutoff m i) nr (Γ x) = 0
  · simp [hz]
  · rw [hamplitude hz, smul_smul, smul_smul]
    congr 1
    ring

/-- Only copies with a nonzero differentiated reference cutoff need an
amplitude comparison. No exterior continuation of a Volterra solve is assumed. -/
theorem globalTail_transport (Γ : D →L[ℝ] E)
    (d : GraphDirections D) (dr : GraphDirections E)
    (a : PeriodizedWaveBounds.CopyData D I) (b : PeriodizedWaveBounds.CopyData E I)
    (n nr : ℕ) (rate c : ℝ) (x : D)
    (hcutoff : ∀ i, a.cutoff n i = fun y => b.cutoff nr i (Γ y))
    (hfast : Γ (d.fastField n x) = rate • dr.fastField nr (Γ x))
    (hdiff : ∀ i, DifferentiableAt ℝ (b.cutoff nr i) (Γ x))
    (hamplitude : ∀ i, dr.Dfast (fun m => b.cutoff m i) nr (Γ x) ≠ 0 →
      a.amplitude n i x = c • b.amplitude nr i (Γ x)) :
    a.globalTail d n x = (rate * c) • b.globalTail dr nr (Γ x) := by
  change (∑' i, a.localTail d n i x) = (rate * c) • ∑' i, b.localTail dr nr i (Γ x)
  calc
    _ = ∑' i, (rate * c) • b.localTail dr nr i (Γ x) := tsum_congr fun i =>
      localTail_transport Γ d dr a b n nr rate c i x (hcutoff i) hfast (hdiff i) (hamplitude i)
    _ = _ := tsum_const_smul'' (rate * c)

/-- Full transport of the actual Gaussian error, including the source
on the part of the domain uncovered by native cutoffs. -/
theorem globalGaussian_transport (Γ : D →L[ℝ] E)
    (d : GraphDirections D) (dr : GraphDirections E)
    (a : PeriodizedWaveBounds.CopyData D I) (b : PeriodizedWaveBounds.CopyData E I)
    (n nr : ℕ) (rate c : ℝ) (x : D)
    (hcutoff : ∀ i, a.cutoff n i = fun y => b.cutoff nr i (Γ y))
    (hfast : Γ (d.fastField n x) = rate • dr.fastField nr (Γ x))
    (hdiff : ∀ i, DifferentiableAt ℝ (b.cutoff nr i) (Γ x))
    (hamplitude : ∀ i, dr.Dfast (fun m => b.cutoff m i) nr (Γ x) ≠ 0 →
      a.amplitude n i x = c • b.amplitude nr i (Γ x))
    (hsource : a.source n x = (rate * c) • b.source nr (Γ x)) :
    a.globalGaussian d n x = (rate * c) • b.globalGaussian dr nr (Γ x) := by
  rw [PeriodizedWaveBounds.CopyData.globalGaussian,
    globalTail_transport Γ d dr a b n nr rate c x hcutoff hfast hdiff hamplitude,
    cutoffSum_transport Γ a b n nr x (fun i => congrFun (hcutoff i) x), hsource]
  simp only [PeriodizedWaveBounds.CopyData.globalGaussian, smul_add, smul_smul]
  congr 1
  congr 1
  ring

end CopyTransport

section ReferenceData

open CommonCoverSolve TorusInverse ParticularWaveAssembly ParticularWaveBounds
open CorrectionState

abbrev Parameter := PhysicalParticularWave.Parameter
abbrev WaveSpace := PhysicalParticularWave.WaveSpace
abbrev Cylinder := PhysicalParticularWave.Cylinder

/-- The full native change of variables, conjugate to the actual
cylindrical change of band and common cover. -/
noncomputable def waveChange (h Q Qr : ℝ) (gap : ℕ) : WaveSpace →L[ℝ] WaveSpace :=
  PhysicalParticularWave.waveEquiv.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((PhysicalParticularWave.cylinderChange h Q Qr gap).comp
      PhysicalParticularWave.waveEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem waveChange_apply (h Q Qr : ℝ) (gap : ℕ) (x : WaveSpace) :
    waveChange h Q Qr gap x =
      ((PhysicalParticularWave.parameterChange h Q Qr x.1.1, x.1.2), coverPower gap x.2) := rfl

theorem waveChange_waveEquiv (h Q Qr : ℝ) (gap : ℕ) (x : Cylinder) :
    waveChange h Q Qr gap (PhysicalParticularWave.waveEquiv x) =
      PhysicalParticularWave.waveEquiv (PhysicalParticularWave.cylinderChange h Q Qr gap x) := rfl

/-- The actual untransported reference data, evaluated at its own band. -/
noncomputable def referenceParameters (D : AssemblyData Parameter) :
    CorrectionStep.ParticularParameters Parameter where
  tangent j _ := D.reference.tangent j
  geometry _ := D.reference.geometry
  length _ := D.reference.length
  length_pos _ := D.reference.length_pos
  cutoff _ := D.reference.cutoff
  background := D.background
  directions := D.directions

noncomputable def nativeData (D : AssemblyData Parameter) (h : ℝ) (gap : ℕ → ℕ) (j : ℤ) :
    PeriodizedWaveBounds.CopyData WaveSpace Frequency :=
  (CorrectionStep.ParticularParameters.fromReference D h gap).copyData
    D.context D.state D.carrierBlock D.gaussianInput D.aliasInput j

noncomputable def referenceData (D : AssemblyData Parameter) (j : ℤ) :
    PeriodizedWaveBounds.CopyData WaveSpace Frequency :=
  (referenceParameters D).copyData D.context D.state D.carrierBlock D.gaussianInput D.aliasInput j

theorem copyData_amplitude (p : CorrectionStep.ParticularParameters Parameter)
    (C : Context (Parameter × Plane)) (u : State (Parameter × Plane))
    (b : HarmonicBlock (Parameter × Plane))
    (G A : HarmonicResidual.BlockCoefficients (Parameter × Plane))
    (j : ℤ) (n : ℕ) (copy : Frequency) (x : WaveSpace) :
    (p.copyData C u b G A j).amplitude n copy x =
      complexCopyVelocity (p.tangent j n) (residualSource C u b G A j n)
        (p.geometry n) (p.length_pos n).le copy (x.1.1, x.2) :=
  complexCopyVelocity_angle (p.tangent j n) (residualSource C u b G A j n)
    (p.geometry n) (p.length_pos n).le copy x.1.1 x.1.2 x.2

theorem native_cutoff_transport (D : AssemblyData Parameter) (h : ℝ) (gap : ℕ → ℕ)
    (j : ℤ) (n : ℕ) (copy : Frequency) :
    (nativeData D h gap j).cutoff n copy = fun x =>
      (referenceData D j).cutoff D.reference.band copy
        (waveChange h (ChartScales.Q n) (ChartScales.Q D.reference.band) (gap n) x) := by
  funext x
  change D.reference.cutoff
      (CopySolveCompatibility.nativeTimeMap 0
        (PhysicalParticularWave.clockWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band))
        ((CopySolveCompatibility.transportGeometry D.reference.geometry (gap n) 0
          (PhysicalParticularWave.clockWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band))
            _).coordinates copy x.2)) =
    D.reference.cutoff (D.reference.geometry.coordinates copy (coverPower (gap n) x.2))
  erw [ScaledTangentTransport.coordinates_transport]

theorem reference_cutoff_differentiable (D : AssemblyData Parameter) (j : ℤ)
    (hcutoff : ContDiff ℝ ∞ D.reference.cutoff) (copy : Frequency) (x : WaveSpace) :
    DifferentiableAt ℝ ((referenceData D j).cutoff D.reference.band copy) x := by
  change DifferentiableAt ℝ (fun y : WaveSpace =>
    D.reference.cutoff (D.reference.geometry.coordinates copy y.2)) x
  exact ((hcutoff.comp (D.reference.geometry.coordinates_contDiff copy)).comp
    contDiff_snd).contDiffAt.differentiableAt (by simp)

/-- A nonzero actual directional derivative is supported in any closed
set supporting the original cutoff. -/
theorem along_ne_zero_mem_closed {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {K : Set E} (hK : IsClosed K) (hf : support f ⊆ K)
    (V : E → E) {x : E} (hx : along V f x ≠ 0) : x ∈ K := by
  have hd : x ∈ support (fderiv ℝ f) := by
    intro hz
    apply hx
    simp only [along, hz, _root_.zero_apply]
  exact (closure_minimal hf hK) (support_fderiv_subset ℝ hd)

theorem reference_derivative_mem_slot (D : AssemblyData Parameter) (j : ℤ)
    {U : Set Parameter} (R : PhysicalParticularWave.ReferenceODE D j U)
    (copy : Frequency) {x : WaveSpace}
    (hx : D.directions.Dfast (fun m => (referenceData D j).cutoff m copy) D.reference.band x ≠ 0) :
    (D.reference.geometry.coordinates copy x.2).2 ∈ Icc 0 D.reference.length := by
  let K : Set WaveSpace := {y | (D.reference.geometry.coordinates copy y.2).2 ∈ Icc 0
    D.reference.length}
  have hK : IsClosed K := isClosed_Icc.preimage
    (((D.reference.geometry.coordinates_contDiff copy).continuous.comp continuous_snd).snd)
  apply along_ne_zero_mem_closed hK (V := D.directions.fastField D.reference.band) _ hx
  intro y hy
  exact (R.cutoff hy).2

theorem current_slot_of_reference_derivative (D : AssemblyData Parameter) (h : ℝ)
    (gap : ℕ → ℕ) (j : ℤ) (n : ℕ) {U : Set Parameter}
    (R : PhysicalParticularWave.ReferenceODE D j U) (copy : Frequency) (x : WaveSpace)
    (hx : D.directions.Dfast (fun m => (referenceData D j).cutoff m copy) D.reference.band
      (waveChange h (ChartScales.Q n) (ChartScales.Q D.reference.band) (gap n) x) ≠ 0) :
    (((CorrectionStep.ParticularParameters.fromReference D h gap).geometry n).coordinates copy
      x.2).2 ∈
      Icc 0 ((CorrectionStep.ParticularParameters.fromReference D h gap).length n) := by
  let rate := PhysicalParticularWave.clockWeight h (ChartScales.Q n) (ChartScales.Q
    D.reference.band)
  have hrate : 0 < rate := PhysicalParticularWave.ratioPower_pos
    (ChartScales.Q_pos n) (ChartScales.Q_pos D.reference.band) _
  have hs := reference_derivative_mem_slot D j R copy hx
  change (D.reference.geometry.coordinates copy (coverPower (gap n) x.2)).2 ∈
    Icc 0 D.reference.length at hs
  apply (ScaledTangentTransport.current_slot_iff D.reference.geometry (gap n) 0 rate hrate
    copy x.2 0 (D.reference.length / rate)).mpr
  have hlen : rate * (D.reference.length / rate) = D.reference.length := by field_simp
  simpa only [zero_add, mul_zero, hlen] using hs

theorem interval_congr {E : Type} (F : (a b : ℝ) → a ≤ b → E)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (ha : a = c) (hb : b = d) :
    F a b hab = F c d hcd := by
  subst c
  subst d
  rfl

theorem complexCopyVelocity_zeroEntry
    (t : TangentData Parameter ProblemStatement.Space) (f : Parameter × Plane → ComplexVector)
    (parameter : Parameter → Parameter) (g : Geometry) (gap : ℕ)
    (L rate amplitude normalScale : ℝ) (hL : 0 < L) (hrate : 0 < rate) (hnormal : normalScale ≠ 0)
    {U : Set Parameter} (hA : ContinuousOn t.linearData.coefficient (U ×ˢ univ))
    (hB : ContinuousOn t.linearData.forcingMap (U ×ˢ univ))
    (hf : ContinuousOn f (U ×ˢ univ)) (q : Parameter) (hq : parameter q ∈ U)
    (copy : Frequency) (Y : Plane)
    (hslot : ((CopySolveCompatibility.transportGeometry g gap 0 rate hrate.ne').coordinates copy
      Y).2 ∈
      Icc 0 (L / rate)) :
    complexCopyVelocity (ScaledTangentTransport.transportTangent t parameter gap 0 rate amplitude
      normalScale)
      (ScaledTangentTransport.transportSource f parameter gap rate amplitude)
      (CopySolveCompatibility.transportGeometry g gap 0 rate hrate.ne') (div_pos hL hrate).le copy
        (q, Y) =
        amplitude • complexCopyVelocity t f g hL.le copy (parameter q, coverPower gap Y) := by
  have he := ScaledTangentTransport.complexCopyVelocity_transport t f parameter g (div_pos hL
    hrate).le
    gap 0 rate amplitude normalScale hrate hnormal hA hB hf q hq copy Y hslot
  refine he.trans (congrArg (fun z : ComplexVector => amplitude • z) ?_)
  apply interval_congr (fun a b hab => complexCopyVelocity t f g (a := a) (b := b) hab
    copy (parameter q, coverPower gap Y)) _ _ (by ring)
  field_simp ; simp

end ReferenceData

section ActualReference

open CommonCoverSolve TorusInverse ParticularWaveAssembly ParticularWaveBounds
open CorrectionState PhysicalParticularWave

theorem native_source_transport (D : AssemblyData Parameter) (h : ℝ) (gap : ℕ → ℕ)
    (j : ℤ) (n i : ℕ)
    (H : PhysicalResidualNaturality.BandCoherence D h (ChartScales.Q_pos n)
      (ChartScales.Q_pos D.reference.band) i (gap n) n)
    (hn : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput n)
    (hr : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput
      D.reference.band)
    (x : WaveSpace) :
    (nativeData D h gap j).source n x =
      (clockWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band) *
        velocityWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band)) •
      (referenceData D j).source D.reference.band
        (waveChange h (ChartScales.Q n) (ChartScales.Q D.reference.band) (gap n) x) := by
  exact congrFun (H.source_eq hn hr j) (x.1.1, x.2)

theorem native_amplitude_transport (D : AssemblyData Parameter) (h : ℝ) (gap : ℕ → ℕ)
    (j : ℤ) (n i : ℕ)
    (H : PhysicalResidualNaturality.BandCoherence D h (ChartScales.Q_pos n)
      (ChartScales.Q_pos D.reference.band) i (gap n) n)
    (hn : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput n)
    (hr : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput
      D.reference.band)
    {U : Set Parameter} (R : ReferenceODE D j U)
    (hK : (j : ℝ) * D.carrierBlock.frequency n ≠ 0) (hKr : referenceFrequency D j ≠ 0)
    (copy : Frequency) (x : WaveSpace)
    (hx : parameterChange h (ChartScales.Q n) (ChartScales.Q D.reference.band) x.1.1 ∈ U)
    (hslot : (((CorrectionStep.ParticularParameters.fromReference D h gap).geometry n).coordinates
      copy x.2).2 ∈
      Icc 0 ((CorrectionStep.ParticularParameters.fromReference D h gap).length n)) :
    (nativeData D h gap j).amplitude n copy x =
      velocityWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band) •
        (referenceData D j).amplitude D.reference.band copy
          (waveChange h (ChartScales.Q n) (ChartScales.Q D.reference.band) (gap n) x) := by
  unfold nativeData referenceData
  rw [copyData_amplitude, copyData_amplitude, H.source_eq hn hr j]
  exact complexCopyVelocity_zeroEntry (D.reference.tangent j) (referenceSource D j)
    (parameterChange h (ChartScales.Q n) (ChartScales.Q D.reference.band)) D.reference.geometry
      (gap n)
    D.reference.length (clockWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band))
    (velocityWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band))
    (normalWeight (ChartScales.Q n) (ChartScales.Q D.reference.band)
      ((j : ℝ) * D.carrierBlock.frequency n) (referenceFrequency D j))
    D.reference.length_pos (ratioPower_pos (ChartScales.Q_pos n) (ChartScales.Q_pos
      D.reference.band) _)
    (normalWeight_ne (ChartScales.Q_pos n) (ChartScales.Q_pos D.reference.band) hK hKr)
    R.coefficient R.forcing R.source x.1.1 hx copy x.2 hslot

/-- The fast transport hypothesis follows from the actual slot-direction
identities stored by the primitive copy geometry. -/
theorem fast_transport_of_slotDirections (D : AssemblyData Parameter) (h : ℝ) (gap : ℕ → ℕ) (n : ℕ)
    (hn : D.directions.fastScale n • D.directions.fast =
      ((0 : Parameter × ℝ), slotDirection ((CorrectionStep.ParticularParameters.fromReference D h
        gap).geometry n)))
    (hr : D.directions.fastScale D.reference.band • D.directions.fast =
      ((0 : Parameter × ℝ), slotDirection D.reference.geometry)) :
    waveChange h (ChartScales.Q n) (ChartScales.Q D.reference.band) (gap n)
      (D.directions.fastScale n • D.directions.fast) =
      clockWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band) •
        (D.directions.fastScale D.reference.band • D.directions.fast) := by
  rw [hn, hr]
  have he := ScaledTangentTransport.slotDirection_transport D.reference.geometry (gap n) 0
    (clockWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band))
    (ratioPower_pos (ChartScales.Q_pos n) (ChartScales.Q_pos D.reference.band)
      (CoordinateAlgebra.A h + 1 / 2)).ne'
  have hh := congrArg (fun Y : Plane => ((0 : Parameter × ℝ), Y)) he
  simp [waveChange_apply, parameterChange] at hh ⊢
  exact hh

/-- The actual transported reference solve has the derived Gaussian
source weight on the full native cylinder, including uncovered points. -/
theorem fromReference_globalGaussian (D : AssemblyData Parameter) (h : ℝ) (gap : ℕ → ℕ)
    (j : ℤ) (n i : ℕ)
    (H : PhysicalResidualNaturality.BandCoherence D h (ChartScales.Q_pos n)
      (ChartScales.Q_pos D.reference.band) i (gap n) n)
    (hn : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput n)
    (hr : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput
      D.reference.band)
    {U : Set Parameter} (R : ReferenceODE D j U) (hcutoff : ContDiff ℝ ∞ D.reference.cutoff)
    (hK : (j : ℝ) * D.carrierBlock.frequency n ≠ 0) (hKr : referenceFrequency D j ≠ 0)
    (hfast : waveChange h (ChartScales.Q n) (ChartScales.Q D.reference.band) (gap n)
      (D.directions.fastScale n • D.directions.fast) =
      clockWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band) •
        (D.directions.fastScale D.reference.band • D.directions.fast))
    (x : WaveSpace)
    (hx : parameterChange h (ChartScales.Q n) (ChartScales.Q D.reference.band) x.1.1 ∈ U) :
    (nativeData D h gap j).globalGaussian D.directions n x =
      sourceWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band) •
        (referenceData D j).globalGaussian D.directions D.reference.band
          (waveChange h (ChartScales.Q n) (ChartScales.Q D.reference.band) (gap n) x) := by
  rw [← clock_mul_velocity (ChartScales.Q_pos n) (ChartScales.Q_pos D.reference.band)]
  apply globalGaussian_transport _ D.directions D.directions _ _ n D.reference.band _ _ x
    (native_cutoff_transport D h gap j n) hfast
  · exact fun copy => reference_cutoff_differentiable D j hcutoff copy _
  · intro copy hcopy
    exact native_amplitude_transport D h gap j n i H hn hr R hK hKr copy x hx
      (current_slot_of_reference_derivative D h gap j n R copy x hcopy)
  · exact native_source_transport D h gap j n i H hn hr x

theorem fromReference_globalGaussian_cylinder (D : AssemblyData Parameter) (h : ℝ) (gap : ℕ → ℕ)
    (j : ℤ) (n i : ℕ)
    (H : PhysicalResidualNaturality.BandCoherence D h (ChartScales.Q_pos n)
      (ChartScales.Q_pos D.reference.band) i (gap n) n)
    (hn : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput n)
    (hr : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput
      D.reference.band)
    {U : Set Parameter} (R : ReferenceODE D j U) (hcutoff : ContDiff ℝ ∞ D.reference.cutoff)
    (hK : (j : ℝ) * D.carrierBlock.frequency n ≠ 0) (hKr : referenceFrequency D j ≠ 0)
    (hfast : waveChange h (ChartScales.Q n) (ChartScales.Q D.reference.band) (gap n)
      (D.directions.fastScale n • D.directions.fast) =
      clockWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band) •
        (D.directions.fastScale D.reference.band • D.directions.fast))
    (x : Cylinder)
    (hx : parameterChange h (ChartScales.Q n) (ChartScales.Q D.reference.band)
      (PhysicalParticularWave.waveEquiv x).1.1 ∈ U) :
    (nativeData D h gap j).globalGaussian D.directions n (PhysicalParticularWave.waveEquiv x) =
      (velocityWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band) ^ 2 *
        ratioPower (ChartScales.Q n) (ChartScales.Q D.reference.band) (1 / 2)) •
      (referenceData D j).globalGaussian D.directions D.reference.band
        (PhysicalParticularWave.waveEquiv
          (cylinderChange h (ChartScales.Q n) (ChartScales.Q D.reference.band) (gap n) x)) := by
  rw [pow_two, PhysicalResidualNaturality.weight_source (ChartScales.Q_pos n)
    (ChartScales.Q_pos D.reference.band)]
  simpa only [waveChange_waveEquiv] using
    fromReference_globalGaussian D h gap j n i H hn hr R hcutoff hK hKr hfast
      (PhysicalParticularWave.waveEquiv x) hx

end ActualReference

section HarmonicAssembly

open CommonCoverSolve TorusInverse ParticularWaveAssembly ParticularWaveBounds
open CorrectionState PhysicalParticularWave
open scoped BigOperators

/-- A single actual Gaussian Fourier contribution transports with its
full angular carrier. The reference phase relation is primitive block
coherence; the Gaussian coefficient relation is proved from the solve. -/
theorem fromReference_gaussian_character (D : AssemblyData Parameter) (h : ℝ) (gap : ℕ → ℕ)
    (j : ℤ) (n i : ℕ)
    (H : PhysicalResidualNaturality.BandCoherence D h (ChartScales.Q_pos n)
      (ChartScales.Q_pos D.reference.band) i (gap n) n)
    (hn : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput n)
    (hr : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput
      D.reference.band)
    {U : Set Parameter} (R : ReferenceODE D j U) (hcutoff : ContDiff ℝ ∞ D.reference.cutoff)
    (hK : (j : ℝ) * D.carrierBlock.frequency n ≠ 0) (hKr : referenceFrequency D j ≠ 0)
    (hfast : waveChange h (ChartScales.Q n) (ChartScales.Q D.reference.band) (gap n)
      (D.directions.fastScale n • D.directions.fast) =
      clockWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band) •
        (D.directions.fastScale D.reference.band • D.directions.fast))
    (x : Parameter × Plane) (hxpos : 0 < x.1.1)
    (hx : parameterChange h (ChartScales.Q n) (ChartScales.Q D.reference.band) x.1 ∈ U)
    (θ : ℝ) (k : Fin 3) :
    ((nativeData D h gap j).globalGaussian D.directions n (angleShuffle (x, 0)) k *
      HarmonicFields.character j (D.carrierBlock.frequency n * D.carrierBlock.phase n x +
        (D.carrierBlock.angularFrequency n : ℝ) * θ)).re =
      sourceWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band) *
      ((referenceData D j).globalGaussian D.directions D.reference.band
        (angleShuffle (PhysicalResidualNaturality.associatedChart h (ChartScales.Q_pos n)
          (ChartScales.Q_pos D.reference.band) (gap n) x, 0)) k *
        HarmonicFields.character j (D.carrierBlock.frequency D.reference.band *
          D.carrierBlock.phase D.reference.band
            (PhysicalResidualNaturality.associatedChart h (ChartScales.Q_pos n)
              (ChartScales.Q_pos D.reference.band) (gap n) x) +
          (D.carrierBlock.angularFrequency D.reference.band : ℝ) * θ)).re := by
  have hg := fromReference_globalGaussian D h gap j n i H hn hr R hcutoff hK hKr hfast
    (angleShuffle (x, 0)) hx
  have hp := H.block.phase (x := x) hxpos
  dsimp only at hp
  rw [hg, hp, H.block.angular]
  simp only [Pi.smul_apply, smul_mul_assoc, Complex.smul_re, smul_eq_mul]
  rfl

/-- Naturality of the actual finite Gaussian harmonic block, with all
angular variables retained. No equality of Gaussian outputs is assumed. -/
theorem fromReference_gaussianBlock (D : AssemblyData Parameter) (h : ℝ) (gap : ℕ → ℕ)
    (N n i : ℕ)
    (H : PhysicalResidualNaturality.BandCoherence D h (ChartScales.Q_pos n)
      (ChartScales.Q_pos D.reference.band) i (gap n) n)
    (hn : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput n)
    (hr : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput
      D.reference.band)
    {U : Set Parameter} (R : ∀ j ∈ modes N, ReferenceODE D j U)
    (hcutoff : ContDiff ℝ ∞ D.reference.cutoff) (hfrequency : ∀ m, D.carrierBlock.frequency m ≠ 0)
    (hfast : waveChange h (ChartScales.Q n) (ChartScales.Q D.reference.band) (gap n)
      (D.directions.fastScale n • D.directions.fast) =
      clockWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band) •
        (D.directions.fastScale D.reference.band • D.directions.fast))
    (x : Parameter × Plane) (hxpos : 0 < x.1.1)
    (hx : parameterChange h (ChartScales.Q n) (ChartScales.Q D.reference.band) x.1 ∈ U)
    (θ : ℝ) (k : Fin 3) :
    ((CorrectionStep.ParticularParameters.fromReference D h gap).gaussianBlock
      D.context D.state D.carrierBlock D.gaussianInput D.aliasInput N).oscillation n (x, θ) k =
      sourceWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band) *
      ((referenceParameters D).gaussianBlock D.context D.state D.carrierBlock D.gaussianInput
        D.aliasInput N).oscillation
        D.reference.band
        (PhysicalResidualNaturality.associatedChart h (ChartScales.Q_pos n)
          (ChartScales.Q_pos D.reference.band) (gap n) x, θ) k := by
  unfold CorrectionStep.ParticularParameters.gaussianBlock
  rw [assembledBlock_value, assembledBlock_value, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast ((mem_modes N j).mp hj).1
  exact fromReference_gaussian_character D h gap j n i H hn hr (R j hj) hcutoff
    (mul_ne_zero hj0 (hfrequency n)) (mul_ne_zero hj0 (hfrequency D.reference.band))
    hfast x hxpos hx θ k

/-- The same finite-block statement on the original full cylindrical
coordinates, with the source weight explicitly written as `c^2 * l`. -/
theorem fromReference_gaussianBlock_cylinder (D : AssemblyData Parameter) (h : ℝ) (gap : ℕ → ℕ)
    (N n i : ℕ)
    (H : PhysicalResidualNaturality.BandCoherence D h (ChartScales.Q_pos n)
      (ChartScales.Q_pos D.reference.band) i (gap n) n)
    (hn : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput n)
    (hr : PhysicalResidualNaturality.PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput
      D.reference.band)
    {U : Set Parameter} (R : ∀ j ∈ modes N, ReferenceODE D j U)
    (hcutoff : ContDiff ℝ ∞ D.reference.cutoff) (hfrequency : ∀ m, D.carrierBlock.frequency m ≠ 0)
    (hfast : waveChange h (ChartScales.Q n) (ChartScales.Q D.reference.band) (gap n)
      (D.directions.fastScale n • D.directions.fast) =
      clockWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band) •
        (D.directions.fastScale D.reference.band • D.directions.fast))
    (x : Cylinder) (hxpos : 0 < x.1.1)
    (hx : parameterChange h (ChartScales.Q n) (ChartScales.Q D.reference.band)
      (PhysicalParticularWave.waveEquiv x).1.1 ∈ U) (k : Fin 3) :
    ((CorrectionStep.ParticularParameters.fromReference D h gap).gaussianBlock
      D.context D.state D.carrierBlock D.gaussianInput D.aliasInput N).oscillation n
        (angleShuffle.symm (PhysicalParticularWave.waveEquiv x)) k =
      (velocityWeight h (ChartScales.Q n) (ChartScales.Q D.reference.band) ^ 2 *
        ratioPower (ChartScales.Q n) (ChartScales.Q D.reference.band) (1 / 2)) *
      ((referenceParameters D).gaussianBlock D.context D.state D.carrierBlock D.gaussianInput
        D.aliasInput N).oscillation
        D.reference.band
        (angleShuffle.symm (PhysicalParticularWave.waveEquiv
          (cylinderChange h (ChartScales.Q n) (ChartScales.Q D.reference.band) (gap n) x))) k := by
  rw [pow_two, PhysicalResidualNaturality.weight_source (ChartScales.Q_pos n)
    (ChartScales.Q_pos D.reference.band)]
  exact fromReference_gaussianBlock D h gap N n i H hn hr R hcutoff hfrequency hfast
    ((PhysicalParticularWave.waveEquiv x).1.1, (PhysicalParticularWave.waveEquiv x).2)
    hxpos hx (PhysicalParticularWave.waveEquiv x).1.2 k

end HarmonicAssembly

end NavierStokes.GaussianErrorNaturality
