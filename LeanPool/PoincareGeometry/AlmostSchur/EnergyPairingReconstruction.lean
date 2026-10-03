/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.EnergyPairingCoefficients
public import LeanPool.PoincareGeometry.AlmostSchur.EnergyChartDerivative

/-! # Finite-chart reconstruction of the actual energy pairing

The second argument is only C¹. Continuous compactly supported coefficients,
not derivatives of its gradient, pair with the first argument's coordinate
derivatives. This formula is suitable for extension along the dense energy core.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Set MeasureTheory
open scoped Manifold ContDiff Topology BigOperators
open RellichKondrachov.Geometry.Manifold.Sobolev FiniteChartData

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

local instance : IsContMDiffRiemannianBundle I (↑(0 : ℕ)) E
    (TangentSpace I : M → Type _) :=
  IsContMDiffRiemannianBundle.of_le (n := 1) (by norm_num)
local instance : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
  continuousRiemannianBundle_of_contMDiff (I := I)

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] [LindelofSpace M] in
/-- The derivative-coefficient products are globally integrable in coordinates. -/
theorem integrable_chartDerivative_mul_energyPairingCoeff
    (d : FiniteChartData (H := H) (M := M) I) (i : d.ι)
    {f g : M → ℝ} (hf : CMDiff 1 f) (hg : CMDiff 1 g) (v : E) :
    Integrable (fun z => fderiv ℝ (f ∘ (extChartAt I (d.center i)).symm) z v *
      energyPairingCoeff d i g v z) volume := by
  have hd := ((contDiffOn_chart_comp (d.center i) f hf.contMDiffOn).continuousOn_fderiv_of_isOpen
    (isOpen_extChartAt_target (d.center i)) (by norm_num)).clm_apply (continuousOn_const (c := v))
  have hc := (hd.mul (continuous_energyPairingCoeff d i hg v).continuousOn).continuous_of_tsupport_subset
    (isOpen_extChartAt_target (d.center i))
    (tsupport_mul_subset_right.trans ((tsupport_energyPairingCoeff_subset d i g v).trans
      (rhoSupportImage_subset_target (d := d) i)))
  exact hc.integrable_of_hasCompactSupport (hasCompactSupport_energyPairingCoeff d i g v).mul_left

/-- A single partition term of the intrinsic energy is exactly the sum of
directional coordinate derivative pairings with the actual-density coefficients. -/
theorem integral_cutoff_inner_gradients_eq_sum
    (d : FiniteChartData (H := H) (M := M) I) (i : d.ι)
    {f g : M → ℝ} (hf : CMDiff 1 f) (hg : CMDiff 1 g) :
    (∫ x, d.ρ i x * inner ℝ (gradient (I := I) f x) (gradient (I := I) g x)
      ∂riemannianVolume (I := I)) =
    ∑ j, ∫ z, fderiv ℝ (f ∘ (extChartAt I (d.center i)).symm) z
      ((stdOrthonormalBasis ℝ E) j) *
      energyPairingCoeff d i g ((stdOrthonormalBasis ℝ E) j) z := by
  classical
  let c := d.center i
  let χ := extChartAt I c
  let b := stdOrthonormalBasis ℝ E
  have hν : (riemannianVolume (I := I)).restrict χ.source =
      chartMetricMeasure (I := I) volume b.toBasis c := by
    rw [riemannianVolume_eq b.toBasis, metricDensityMeasure_restrict,
      chartMetricMeasure_restrict_source, b.addHaar_eq_volume]
  have hzero (x : M) (hx : x ∉ χ.source) :
      d.ρ i x * inner ℝ (gradient (I := I) f x) (gradient (I := I) g x) = 0 := by
    have hρ : d.ρ i x = 0 := by
      by_contra hn
      exact hx (by simpa only [χ, extChartAt_source] using d.subordinate i (subset_closure hn))
    rw [hρ, zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  change (∫ x, _ ∂(riemannianVolume (I := I)).restrict χ.source) = _
  rw [hν, integral_chartMetricMeasure_density]
  have hpoint (z : E) (hz : z ∈ χ.target) :
      matrixDensity (coordinateMetric (I := I) b.toBasis c z) *
        (d.ρ i (χ.symm z) * inner ℝ (gradient (I := I) f (χ.symm z))
          (gradient (I := I) g (χ.symm z))) =
      ∑ j, fderiv ℝ (f ∘ χ.symm) z (b j) * energyPairingCoeff d i g (b j) z := by
    have hx : χ.symm z ∈ (chartAt H c).source := by
      simpa only [χ, extChartAt_source] using χ.map_target hz
    have hdf := fderiv_chart_coordinateVectorField f (gradient (I := I) g) c (χ.symm z)
      hx (hf.mdifferentiableAt (by norm_num))
    change fderiv ℝ (f ∘ χ.symm) (χ (χ.symm z))
      (coordinateVectorField (I := I) c (gradient (I := I) g) (χ (χ.symm z))) = _ at hdf
    rw [χ.right_inv hz, ← inner_gradient] at hdf
    rw [← hdf, ← b.sum_repr (coordinateVectorField (I := I) c (gradient (I := I) g) z)]
    simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hr : localize (d := d) (fun _ => (1 : ℝ)) i z = d.ρ i (χ.symm z) := by
      change χ.target.indicator (fun y => d.ρ i (χ.symm y) * 1) z = _
      rw [indicator_of_mem hz, mul_one]
    simp only [energyPairingCoeff, hr, OrthonormalBasis.repr_apply_apply]
    ring
  rw [setIntegral_congr_fun (isOpen_extChartAt_target c).measurableSet hpoint,
    integral_finsetSum _ (fun j _ =>
      (integrable_chartDerivative_mul_energyPairingCoeff d i hf hg (b j)).integrableOn)]
  apply Finset.sum_congr rfl
  intro j _
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  have hz' : z ∉ tsupport (energyPairingCoeff d i g (b j)) := fun hh => hz
    ((rhoSupportImage_subset_target (d := d) i) (tsupport_energyPairingCoeff_subset d i g (b j) hh))
  rw [image_eq_zero_of_notMem_tsupport hz', mul_zero]

/-- Finite partition reconstruction of the intrinsic Dirichlet pairing. -/
theorem dirichletForm_eq_sum_coordinatePairings
    (d : FiniteChartData (H := H) (M := M) I)
    {f g : M → ℝ} (hf : CMDiff 1 f) (hg : CMDiff 1 g) :
    dirichletForm (I := I) f g =
      ∑ i : d.ι, ∑ j, ∫ z,
        fderiv ℝ (f ∘ (extChartAt I (d.center i)).symm) z ((stdOrthonormalBasis ℝ E) j) *
          energyPairingCoeff d i g ((stdOrthonormalBasis ℝ E) j) z := by
  have hi (i : d.ι) : Integrable
      (fun x => d.ρ i x * inner ℝ (gradient (I := I) f x) (gradient (I := I) g x))
      (riemannianVolume (I := I)) := by
    have hc := (d.ρ i).contMDiff.continuous.mul
      (Continuous.inner_bundle (F := E) (E := TangentSpace I)
        (contMDiff_gradient (I := I) 0 hf).continuous (contMDiff_gradient (I := I) 0 hg).continuous)
    let : IsFiniteMeasure (riemannianVolume (I := I) (M := M)) :=
      ⟨(riemannianVolume_finite_positive (I := I)).2⟩
    exact hc.integrable_of_hasCompactSupport isClosed_closure.isCompact
  calc
    dirichletForm (I := I) f g = ∑ i : d.ι, ∫ x,
        d.ρ i x * inner ℝ (gradient (I := I) f x) (gradient (I := I) g x)
          ∂riemannianVolume (I := I) := by
      rw [← integral_finsetSum _ (fun i _ => hi i)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [← Finset.sum_mul]
        have hs : ∑ i : d.ι, d.ρ i x = 1 := by
          simpa only [finsum_eq_sum_of_fintype] using d.ρ.sum_eq_one (mem_univ x)
        rw [hs, one_mul]
    _ = _ := Finset.sum_congr rfl fun i _ => integral_cutoff_inner_gradients_eq_sum d i hf hg

/-- The coefficient as a restricted L² class. The compact set may be enlarged
to leave the cutoff support strictly in its interior. -/
def energyPairingCoeffL2 (d : FiniteChartData (H := H) (M := M) I)
    (i : d.ι) {g : M → ℝ} (hg : CMDiff 1 g) (v : E) (K : Set E) :
    Lp ℝ 2 ((volume : Measure E).restrict K) :=
  ((memLp_energyPairingCoeff d i hg v).mono_measure Measure.restrict_le_self).toLp _

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] [LindelofSpace M] in
theorem energyPairingCoeffL2_ae_eq (d : FiniteChartData (H := H) (M := M) I)
    (i : d.ι) {g : M → ℝ} (hg : CMDiff 1 g) (v : E) (K : Set E) :
    (energyPairingCoeffL2 d i hg v K : E → ℝ) =ᵐ[(volume : Measure E).restrict K]
      energyPairingCoeff d i g v :=
  ((memLp_energyPairingCoeff d i hg v).mono_measure Measure.restrict_le_self).coeFn_toLp

/-- The actual energy pairing on the C¹ core is a finite sum of L² inner
products on any compact chart neighborhoods containing the cutoff supports. -/
theorem dirichletForm_eq_sum_energyChartDerivativeLinear
    (d : FiniteChartData (H := H) (M := M) I)
    (K : d.ι → Set E) (hK : ∀ i, IsCompact (K i))
    (hKt : ∀ i, K i ⊆ (extChartAt I (d.center i)).target)
    (hcover : ∀ i, rhoSupportImage (d := d) i ⊆ K i)
    (f g : EnergySpace (I := I) (M := M)) :
    dirichletForm (I := I) f.val g.val = ∑ i : d.ι, ∑ j,
      inner ℝ (energyChartDerivativeLinear (d.center i) (hK i) (hKt i)
        ((stdOrthonormalBasis ℝ E) j) f)
        (energyPairingCoeffL2 d i g.property.1 ((stdOrthonormalBasis ℝ E) j) (K i)) := by
  rw [dirichletForm_eq_sum_coordinatePairings d f.property.1 g.property.1]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [L2.inner_def]
  calc
    _ = ∫ z in K i,
        fderiv ℝ (f.val ∘ (extChartAt I (d.center i)).symm) z ((stdOrthonormalBasis ℝ E) j) *
        energyPairingCoeff d i g.val ((stdOrthonormalBasis ℝ E) j) z := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      have hz' : z ∉ tsupport (energyPairingCoeff d i g.val ((stdOrthonormalBasis ℝ E) j)) :=
        fun hh => hz (hcover i (tsupport_energyPairingCoeff_subset d i g.val _ hh))
      rw [image_eq_zero_of_notMem_tsupport hz', mul_zero]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [energyChartDerivativeLinear_ae_eq (d.center i) (hK i) (hKt i)
        ((stdOrthonormalBasis ℝ E) j) f,
        energyPairingCoeffL2_ae_eq d i g.property.1 ((stdOrthonormalBasis ℝ E) j) (K i)]
        with z hz hq
      simp only [hz, hq, RCLike.inner_apply, conj_trivial, mul_comm]

variable [PreconnectedSpace M]

/-- Completed energy is reconstructed by completed local derivatives paired
against the continuous coefficients of any C¹ core function. No density of
C² functions in the energy norm is used. -/
theorem energyCompletion_inner_eq_sum_chartPairings
    (d : FiniteChartData (H := H) (M := M) I)
    (K : d.ι → Set E) (hK : ∀ i, IsCompact (K i))
    (hKt : ∀ i, K i ⊆ (extChartAt I (d.center i)).target)
    (hcover : ∀ i, rhoSupportImage (d := d) i ⊆ K i)
    (u : EnergyCompletion (I := I) (M := M)) (g : EnergySpace (I := I) (M := M)) :
    inner ℝ u (energyToCompletion g) = ∑ i : d.ι, ∑ j,
      inner ℝ (energyChartDerivative (d.center i) (hK i) (hKt i)
        ((stdOrthonormalBasis ℝ E) j) u)
        (energyPairingCoeffL2 d i g.property.1 ((stdOrthonormalBasis ℝ E) j) (K i)) := by
  refine (denseRange_energyToCompletion (I := I) (M := M)).induction_on u ?_ ?_
  · apply isClosed_eq
    · exact continuous_id.inner continuous_const
    · exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
        (energyChartDerivative (d.center i) (hK i) (hKt i) ((stdOrthonormalBasis ℝ E) j)).continuous.inner
          continuous_const
  · intro f
    rw [energyCompletion_inner]
    simpa only [energyChartDerivative_energyToCompletion] using
      dirichletForm_eq_sum_energyChartDerivativeLinear d K hK hKt hcover f g

end AlmostSchur
