/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.CoordinateGradient
public import LeanPool.PoincareGeometry.AlmostSchur.EnergyChartDerivative
public import LeanPool.PoincareGeometry.AlmostSchur.EnergyPairingReconstruction
public import LeanPool.PoincareGeometry.AlmostSchur.CoordinateEllipticity

/-! # Single-chart variational identity for the actual completed solution

Compact coordinate tests are lifted by zero, the actual gradient is identified
with the inverse Gram matrix, and the core energy formula passes to the Hilbert
completion by continuity. There is no assumed coordinate-PDE bridge.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Set MeasureTheory
open scoped Manifold ContDiff Topology BigOperators

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M] [LindelofSpace M]
  [T2Space M] [CompactSpace M]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance energyLocalVariationalMetricZero : IsContMDiffRiemannianBundle I (↑(0 : ℕ)) E
    (TangentSpace I : M → Type _) :=
  IsContMDiffRiemannianBundle.of_le (n := 1) (by norm_num)
local instance energyLocalVariationalContinuousMetric :
    IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
  continuousRiemannianBundle_of_contMDiff (I := I)
local instance energyLocalVariationalFiniteVolume :
    IsFiniteMeasure (riemannianVolume (I := I) (M := M)) :=
  ⟨(riemannianVolume_finite_positive (I := I)).2⟩

/-- The density-weighted coordinate flux of a lifted test, extended by zero. -/
def chartTestFluxCoeff (b : OrthonormalBasis ι ℝ E) (c : M) (φ : E → ℝ) (i : ι) : E → ℝ :=
  (extChartAt I c).target.indicator (fun z =>
    matrixDensity (coordinateMetric (I := I) b.toBasis c z) *
      inner ℝ (b i) (coordinateVectorField (I := I) c (gradient (I := I) (chartTestLift (I := I) c φ)) z))

/-- Actual inverse-Gram coefficients give the lifted-test flux on the chart. -/
theorem chartTestFluxCoeff_eq_sum (b : OrthonormalBasis ι ℝ E) (c : M) (φ : E → ℝ)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ (extChartAt I c).target) {z : E}
    (hz : z ∈ (extChartAt I c).target) (i : ι) :
    chartTestFluxCoeff (I := I) b c φ i z = ∑ j,
      coordinateEllipticMatrix (I := I) b.toBasis c z i j * fderiv ℝ φ z (b j) := by
  rw [chartTestFluxCoeff, indicator_of_mem hz,
    coordinateGradient_component_eq_sum b c _ (contMDiff_chartTestLift c φ hφ hc hs) hz i,
    fderiv_chartTestLift_comp_symm c φ hz, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [coordinateEllipticMatrix_apply]
  ring

/-- Flux vanishes off the coordinate test support, including off the chart. -/
theorem chartTestFluxCoeff_eq_zero_off_support (b : OrthonormalBasis ι ℝ E) (c : M)
    (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ (extChartAt I c).target) {z : E} (hz : z ∉ tsupport φ) (i : ι) :
    chartTestFluxCoeff (I := I) b c φ i z = 0 := by
  by_cases hzt : z ∈ (extChartAt I c).target
  · rw [chartTestFluxCoeff_eq_sum b c φ hφ hc hs hzt i, fderiv_of_notMem_tsupport (𝕜 := ℝ) hz]
    simp
  · exact indicator_of_notMem hzt _

/-- The flux coefficients have compact support contained in the test support. -/
theorem tsupport_chartTestFluxCoeff_subset (b : OrthonormalBasis ι ℝ E) (c : M)
    (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ (extChartAt I c).target) (i : ι) :
    tsupport (chartTestFluxCoeff (I := I) b c φ i) ⊆ tsupport φ := by
  apply closure_minimal _ (isClosed_tsupport φ)
  intro z hz
  by_contra hn
  exact hz (chartTestFluxCoeff_eq_zero_off_support b c φ hφ hc hs hn i)

/-- Each flux coefficient is continuous, with no differentiability of the gradient needed. -/
theorem continuous_chartTestFluxCoeff (b : OrthonormalBasis ι ℝ E) (c : M)
    (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ (extChartAt I c).target) (i : ι) :
    Continuous (chartTestFluxCoeff (I := I) b c φ i) := by
  have hv := continuousOn_coordinateVectorField_gradient c (contMDiff_chartTestLift c φ hφ hc hs)
  have hco := (continuousOn_coordinateDensity b.toBasis c).mul
    ((continuousOn_const (c := b i)).inner hv)
  apply ContinuousOn.continuous_of_tsupport_subset (s := (extChartAt I c).target) _
    (isOpen_extChartAt_target c) ((tsupport_chartTestFluxCoeff_subset b c φ hφ hc hs i).trans hs)
  apply hco.congr
  intro z hz
  exact indicator_of_mem hz _

/-- The compactly supported coefficient is an actual L² test coefficient. -/
theorem memLp_chartTestFluxCoeff (b : OrthonormalBasis ι ℝ E) (c : M)
    (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ (extChartAt I c).target) (i : ι) :
    MemLp (chartTestFluxCoeff (I := I) b c φ i) 2 (volume : Measure E) :=
  (continuous_chartTestFluxCoeff b c φ hφ hc hs i).memLp_of_hasCompactSupport
    (hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_chartTestFluxCoeff_subset b c φ hφ hc hs i))

/-- Compact support and local C¹ regularity justify all classical coordinate pairings. -/
theorem integrable_chartDerivative_mul_chartTestFluxCoeff (b : OrthonormalBasis ι ℝ E)
    (c : M) (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ (extChartAt I c).target) (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f) (i : ι) :
    Integrable (fun z => fderiv ℝ (f ∘ (extChartAt I c).symm) z (b i) *
      chartTestFluxCoeff (I := I) b c φ i z) (volume : Measure E) := by
  have hd := ((contDiffOn_chart_comp c f hf.contMDiffOn).continuousOn_fderiv_of_isOpen
    (isOpen_extChartAt_target c) (by norm_num)).clm_apply (continuousOn_const (c := b i))
  have ht := tsupport_chartTestFluxCoeff_subset b c φ hφ hc hs i
  have hco := (hd.mul (continuous_chartTestFluxCoeff b c φ hφ hc hs i).continuousOn).continuous_of_tsupport_subset
    (isOpen_extChartAt_target c) (tsupport_mul_subset_right.trans (ht.trans hs))
  have hcs : HasCompactSupport (chartTestFluxCoeff (I := I) b c φ i) :=
    hc.of_isClosed_subset (isClosed_tsupport _) ht
  exact hco.integrable_of_hasCompactSupport hcs.mul_left

/-- A lifted test has zero actual gradient away from the chart source. -/
theorem gradient_chartTestLift_eq_zero_off_source (c : M) (φ : E → ℝ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ (extChartAt I c).target)
    {x : M} (hx : x ∉ (extChartAt I c).source) :
    gradient (I := I) (chartTestLift (I := I) c φ) x = 0 := by
  have hn : x ∉ tsupport (chartTestLift (I := I) c φ) :=
    fun h => hx (tsupport_chartTestLift_subset_source c φ hc hs h)
  have he : chartTestLift (I := I) c φ =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) :=
    notMem_tsupport_iff_eventuallyEq.mp hn
  have hd := he.mfderiv_eq (I := I) (I' := 𝓘(ℝ, ℝ))
  apply (gradient_eq_zero_iff _ _).2
  simp only [mfderiv_const] at hd
  ext v
  change (NormedSpace.fromTangentSpace (chartTestLift (I := I) c φ x))
    ((mfderiv I 𝓘(ℝ, ℝ) (chartTestLift (I := I) c φ) x) v) = 0
  rw [hd]
  exact map_zero _

/-- Single-chart classical energy identity, before extending the first argument. -/
theorem dirichletForm_chartTestLift_eq_sum (b : OrthonormalBasis ι ℝ E)
    (c : M) (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ (extChartAt I c).target) (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f) :
    dirichletForm (I := I) f (chartTestLift (I := I) c φ) =
      ∑ i, ∫ z, fderiv ℝ (f ∘ (extChartAt I c).symm) z (b i) *
        chartTestFluxCoeff (I := I) b c φ i z := by
  let χ := extChartAt I c
  let F := chartTestLift (I := I) c φ
  have hν : (riemannianVolume (I := I)).restrict χ.source =
      chartMetricMeasure (I := I) volume b.toBasis c := by
    rw [riemannianVolume_eq b.toBasis, metricDensityMeasure_restrict,
      chartMetricMeasure_restrict_source, b.addHaar_eq_volume]
  have hzero (x : M) (hx : x ∉ χ.source) :
      inner ℝ (gradient (I := I) f x) (gradient (I := I) F x) = 0 := by
    rw [gradient_chartTestLift_eq_zero_off_source c φ hc hs hx, inner_zero_right]
  unfold dirichletForm
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  change (∫ x, _ ∂(riemannianVolume (I := I)).restrict χ.source) = _
  rw [hν, integral_chartMetricMeasure_density]
  have hpoint (z : E) (hz : z ∈ χ.target) :
      matrixDensity (coordinateMetric (I := I) b.toBasis c z) *
        inner ℝ (gradient (I := I) f (χ.symm z)) (gradient (I := I) F (χ.symm z)) =
      ∑ i, fderiv ℝ (f ∘ χ.symm) z (b i) * chartTestFluxCoeff (I := I) b c φ i z := by
    have hx : χ.symm z ∈ (chartAt H c).source := by
      simpa only [χ, extChartAt_source] using χ.map_target hz
    have hdf := fderiv_chart_coordinateVectorField f (gradient (I := I) F) c (χ.symm z)
      hx (hf.mdifferentiableAt (by norm_num))
    change fderiv ℝ (f ∘ χ.symm) (χ (χ.symm z))
      (coordinateVectorField (I := I) c (gradient (I := I) F) (χ (χ.symm z))) = _ at hdf
    rw [χ.right_inv hz, ← inner_gradient] at hdf
    rw [← hdf, ← b.sum_repr (coordinateVectorField (I := I) c (gradient (I := I) F) z)]
    simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [chartTestFluxCoeff, indicator_of_mem hz]
    simp only [OrthonormalBasis.repr_apply_apply]
    ring
  rw [setIntegral_congr_fun (isOpen_extChartAt_target c).measurableSet hpoint,
    integral_finsetSum _ (fun i _ =>
      (integrable_chartDerivative_mul_chartTestFluxCoeff b c φ hφ hc hs f hf i).integrableOn)]
  apply Finset.sum_congr rfl
  intro i _
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  rw [chartTestFluxCoeff_eq_zero_off_support b c φ hφ hc hs (fun hh => hz (hs hh)) i, mul_zero]

variable [PreconnectedSpace M]

/-- The actual completed energy pairing is a single-chart pairing with the test flux. -/
theorem energyCompletion_inner_chartTestLift (b : OrthonormalBasis ι ℝ E)
    (c : M) {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target)
    (u : EnergyCompletion (I := I) (M := M))
    (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (hφK : tsupport φ ⊆ K) :
    inner ℝ u (energyToCompletion (meanCorrectedEnergyTest (chartTestLift (I := I) c φ)
      (contMDiff_chartTestLift c φ hφ hc (hφK.trans hKt)))) =
      ∑ i, ∫ z in K, energyChartDerivative c hK hKt (b i) u z *
        chartTestFluxCoeff (I := I) b c φ i z := by
  let F := chartTestLift (I := I) c φ
  let hF := contMDiff_chartTestLift c φ hφ hc (hφK.trans hKt)
  let Q (i : ι) : Lp ℝ 2 ((volume : Measure E).restrict K) :=
    ((memLp_chartTestFluxCoeff b c φ hφ hc (hφK.trans hKt) i).mono_measure
      Measure.restrict_le_self).toLp (chartTestFluxCoeff (I := I) b c φ i)
  have hQ (i : ι) : (Q i : E → ℝ) =ᵐ[(volume : Measure E).restrict K]
      chartTestFluxCoeff (I := I) b c φ i :=
    ((memLp_chartTestFluxCoeff b c φ hφ hc (hφK.trans hKt) i).mono_measure
      Measure.restrict_le_self).coeFn_toLp
  have hpair (v : EnergyCompletion (I := I) (M := M)) (i : ι) :
      inner ℝ (energyChartDerivative c hK hKt (b i) v) (Q i) =
      ∫ z in K, energyChartDerivative c hK hKt (b i) v z * chartTestFluxCoeff (I := I) b c φ i z := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hQ i] with z hz
    simp only [RCLike.inner_apply, conj_trivial, hz, mul_comm]
  have hclosed : inner ℝ u (energyToCompletion (meanCorrectedEnergyTest F hF)) =
      ∑ i, inner ℝ (energyChartDerivative c hK hKt (b i) u) (Q i) := by
    refine (denseRange_energyToCompletion (I := I) (M := M)).induction_on
      (p := fun v => inner ℝ v (energyToCompletion (meanCorrectedEnergyTest F hF)) =
        ∑ i, inner ℝ (energyChartDerivative c hK hKt (b i) v) (Q i)) u ?_ ?_
    · exact isClosed_eq (continuous_id.inner continuous_const)
        (continuous_finsetSum _ fun i _ => (energyChartDerivative c hK hKt (b i)).continuous.inner continuous_const)
    · intro f
      rw [energyCompletion_inner]
      have hm : dirichletForm (I := I) f.val (meanCorrectedEnergyTest F hF).val =
          dirichletForm (I := I) f.val F := by
        simp only [dirichletForm, gradient_meanCorrectedEnergyTest]
      rw [hm, dirichletForm_chartTestLift_eq_sum b c φ hφ hc (hφK.trans hKt) f.val f.property.1]
      apply Finset.sum_congr rfl
      intro i _
      rw [hpair]
      have hzero (z : E) (hz : z ∉ K) :
          fderiv ℝ (f.val ∘ (extChartAt I c).symm) z (b i) * chartTestFluxCoeff (I := I) b c φ i z = 0 := by
        rw [chartTestFluxCoeff_eq_zero_off_support b c φ hφ hc (hφK.trans hKt)
          (fun h => hz (hφK h)) i, mul_zero]
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
        energyChartDerivative_energyToCompletion]
      apply integral_congr_ae
      filter_upwards [energyChartDerivativeLinear_ae_eq c hK hKt (b i) f] with z hz
      rw [hz]
  simpa only [hpair] using hclosed

/-- The completed pairing has the actual density-times-inverse-Gram coefficient. -/
theorem energyCompletion_inner_coordinateEllipticMatrix (b : OrthonormalBasis ι ℝ E)
    (c : M) {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target)
    (u : EnergyCompletion (I := I) (M := M))
    (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (hφK : tsupport φ ⊆ K) :
    inner ℝ u (energyToCompletion (meanCorrectedEnergyTest (chartTestLift (I := I) c φ)
      (contMDiff_chartTestLift c φ hφ hc (hφK.trans hKt)))) =
      ∫ z in K, ∑ i, ∑ j, coordinateEllipticMatrix (I := I) b.toBasis c z i j *
        energyChartDerivative c hK hKt (b i) u z * fderiv ℝ φ z (b j) := by
  rw [energyCompletion_inner_chartTestLift b c hK hKt u φ hφ hc hφK]
  have hint (i : ι) : Integrable (fun z => energyChartDerivative c hK hKt (b i) u z *
      chartTestFluxCoeff (I := I) b c φ i z) ((volume : Measure E).restrict K) :=
    (Lp.memLp _).integrable_mul ((memLp_chartTestFluxCoeff b c φ hφ hc (hφK.trans hKt) i).mono_measure
      Measure.restrict_le_self)
  rw [← integral_finsetSum _ (fun i _ => hint i)]
  apply setIntegral_congr_fun hK.measurableSet
  intro z hz
  apply Finset.sum_congr rfl
  intro i _
  rw [chartTestFluxCoeff_eq_sum b c φ hφ hc (hφK.trans hKt) (hKt hz) i, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Forcing against a lifted coordinate test is exactly the actual density integral. -/
theorem integral_mul_chartTestLift (b : OrthonormalBasis ι ℝ E) (c : M)
    {K : Set E} (hKt : K ⊆ (extChartAt I c).target)
    (h : M → ℝ) (φ : E → ℝ) (hφK : tsupport φ ⊆ K) :
    (∫ x, h x * chartTestLift (I := I) c φ x ∂riemannianVolume (I := I)) =
      ∫ z in K, matrixDensity (coordinateMetric (I := I) b.toBasis c z) *
        h ((extChartAt I c).symm z) * φ z := by
  let χ := extChartAt I c
  have hν : (riemannianVolume (I := I)).restrict χ.source =
      chartMetricMeasure (I := I) volume b.toBasis c := by
    rw [riemannianVolume_eq b.toBasis, metricDensityMeasure_restrict,
      chartMetricMeasure_restrict_source, b.addHaar_eq_volume]
  have hzero (x : M) (hx : x ∉ χ.source) : h x * chartTestLift (I := I) c φ x = 0 := by
    rw [chartTestLift, indicator_of_notMem hx, mul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  change (∫ x, _ ∂(riemannianVolume (I := I)).restrict χ.source) = _
  rw [hν, integral_chartMetricMeasure_density]
  have heq : (∫ z in χ.target, matrixDensity (coordinateMetric (I := I) b.toBasis c z) *
      (h (χ.symm z) * chartTestLift (I := I) c φ (χ.symm z))) =
      ∫ z in χ.target, matrixDensity (coordinateMetric (I := I) b.toBasis c z) * h (χ.symm z) * φ z := by
    apply setIntegral_congr_fun (isOpen_extChartAt_target c).measurableSet
    intro z hz
    dsimp only [χ]
    rw [chartTestLift_comp_symm c φ hz]
    ring
  rw [heq]
  have hzK (z : E) (hz : z ∉ K) :
      matrixDensity (coordinateMetric (I := I) b.toBasis c z) * h (χ.symm z) * φ z = 0 := by
    rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hφK h)), mul_zero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun z hz => hzK z (fun h => hz (hKt h))),
    setIntegral_eq_integral_of_forall_compl_eq_zero hzK]

/-- The actual weak-Poisson solution satisfies the single-chart divergence-form
variational equation with the proved density-weighted inverse metric. -/
theorem weakPoissonSolution_coordinate_variational (b : OrthonormalBasis ι ℝ E)
    (c : M) {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target)
    (h : Lp ℝ 2 (riemannianVolume (I := I) (M := M)))
    (hh : (∫ x, h x ∂riemannianVolume (I := I)) = 0)
    (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (hφK : tsupport φ ⊆ K) :
    (∫ z in K, ∑ i, ∑ j, coordinateEllipticMatrix (I := I) b.toBasis c z i j *
      energyChartDerivative c hK hKt (b i) (weakPoissonSolution h) z * fderiv ℝ φ z (b j)) =
      -(∫ z in K, matrixDensity (coordinateMetric (I := I) b.toBasis c z) *
        h ((extChartAt I c).symm z) * φ z) := by
  rw [← energyCompletion_inner_coordinateEllipticMatrix b c hK hKt (weakPoissonSolution h) φ hφ hc hφK,
    weakPoissonSolution_meanCorrected_test h hh,
    integral_mul_chartTestLift b c hKt (fun x => h x) φ hφK]

end AlmostSchur
