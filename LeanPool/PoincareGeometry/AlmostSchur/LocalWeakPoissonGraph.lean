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

public import LeanPool.PoincareGeometry.AlmostSchur.CoordinateWeakPoisson
public import LeanPool.PoincareGeometry.AlmostSchur.CoordinateCoefficientRegularity
public import LeanPool.PoincareGeometry.AlmostSchur.TestGraphVariational

/-! # Actual local weak Poisson data on the supported test-graph closure

The flux in test direction `j` is `∑ i, A i j * D i`. Flux and negative
forcing are extended by zero only as L² classes. No continuity, Lipschitz
regularity, or weak derivative of these zero extensions is asserted.
-/

@[expose] public noncomputable section
open Bundle Set MeasureTheory Filter
open scoped Manifold ContDiff Topology BigOperators
namespace AlmostSchur
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace LocalWeakPoissonData
variable {b : OrthonormalBasis ι ℝ E} {K : Set E}
  {A : E → Matrix ι ι ℝ} {U F : E → ℝ} {D : ι → E → ℝ}

omit [DecidableEq ι] in
/-- The local flux is square integrable; coefficient bounds are needed only on K. -/
theorem memLp_flux (d : LocalWeakPoissonData b K A U F D)
    (hA : ∀ i j, AEStronglyMeasurable (fun z => A z i j) ((volume : Measure E).restrict K))
    (C : ℝ) (hC : ∀ᵐ z ∂(volume : Measure E).restrict K, ∀ i j, ‖A z i j‖ ≤ C)
    (j : ι) : MemLp (fun z => ∑ i, A z i j * D i z) 2 ((volume : Measure E).restrict K) := by
  apply memLp_finsetSum
  intro i _
  apply (d.derivative_memLp i).of_le_mul (c := C)
    ((hA i j).mul (d.derivative_memLp i).aestronglyMeasurable)
  filter_upwards [hC] with z hz
  simpa only [Pi.mul_apply, norm_mul] using
    mul_le_mul_of_nonneg_right (hz i j) (norm_nonneg (D i z))

/-- The actual flux extended by zero as a global L² class. -/
def globalFlux (d : LocalWeakPoissonData b K A U F D) (hK : MeasurableSet K)
    (hA : ∀ i j, AEStronglyMeasurable (fun z => A z i j) ((volume : Measure E).restrict K))
    (C : ℝ) (hC : ∀ᵐ z ∂(volume : Measure E).restrict K, ∀ i j, ‖A z i j‖ ≤ C)
    (j : ι) : Lp ℝ 2 (volume : Measure E) :=
  Lp.extendByZeroₗᵢ hK ((d.memLp_flux hA C hC j).toLp _)

/-- The RHS includes the negative sign in the actual Poisson variational identity. -/
def globalForcing (d : LocalWeakPoissonData b K A U F D) (hK : MeasurableSet K) :
    Lp ℝ 2 (volume : Measure E) :=
  -(Lp.extendByZeroₗᵢ hK (d.forcing_memLp.toLp F))

omit [DecidableEq ι] in
/-- Global flux representatives are exactly the indicator extensions. -/
theorem globalFlux_ae_eq (d : LocalWeakPoissonData b K A U F D) (hK : MeasurableSet K)
    (hA : ∀ i j, AEStronglyMeasurable (fun z => A z i j) ((volume : Measure E).restrict K))
    (C : ℝ) (hC : ∀ᵐ z ∂(volume : Measure E).restrict K, ∀ i j, ‖A z i j‖ ≤ C)
    (j : ι) : d.globalFlux hK hA C hC j =ᵐ[volume] K.indicator (fun z => ∑ i, A z i j * D i z) := by
  have hp := (ae_restrict_iff' hK).mp (d.memLp_flux hA C hC j).coeFn_toLp
  filter_upwards [Lp.extendByZeroₗᵢ_ae_eq hK ((d.memLp_flux hA C hC j).toLp _), hp] with z hz hp
  exact hz.trans (by by_cases hk : z ∈ K <;> simp [hk, hp])

omit [DecidableEq ι] in
/-- Global RHS representatives are the negative indicator extension of local forcing. -/
theorem globalForcing_ae_eq (d : LocalWeakPoissonData b K A U F D) (hK : MeasurableSet K) :
    d.globalForcing hK =ᵐ[volume] (fun z => -(K.indicator F z)) := by
  have hp := (ae_restrict_iff' hK).mp d.forcing_memLp.coeFn_toLp
  filter_upwards [Lp.coeFn_neg (Lp.extendByZeroₗᵢ hK (d.forcing_memLp.toLp F)),
    Lp.extendByZeroₗᵢ_ae_eq hK (d.forcing_memLp.toLp F), hp] with z hn hz hp
  exact hn.trans (by rw [Pi.neg_apply, hz]; by_cases hk : z ∈ K <;> simp [hk, hp])

omit [DecidableEq ι] in
/-- The actual local PDE holds on the closure of supported C¹ test graphs.
The support set can be any subset of the fixed coordinate set K. -/
theorem variational_on_graph_closure (d : LocalWeakPoissonData b K A U F D)
    (hK : MeasurableSet K)
    (hA : ∀ i j, AEStronglyMeasurable (fun z => A z i j) ((volume : Measure E).restrict K))
    (C : ℝ) (hC : ∀ᵐ z ∂(volume : Measure E).restrict K, ∀ i j, ‖A z i j‖ ≤ C)
    {S : Set E} (hS : S ⊆ K)
    {p : Lp ℝ 2 (volume : Measure E) × (ι → Lp ℝ 2 (volume : Measure E))}
    (hp : p ∈ closure (c1SupportedTestGraph (fun i => b i) S)) :
    (∑ j, inner ℝ (d.globalFlux hK hA C hC j) (p.2 j)) =
      inner ℝ (d.globalForcing hK) p.1 := by
  apply variational_eq_on_closure_c1SupportedTestGraph (fun i => b i) S
    (d.globalFlux hK hA C hC) (d.globalForcing hK) ?_ hp
  intro q hq
  obtain ⟨φ, hφ, hcφ, hsφ, hqφ, hqdφ⟩ := hq
  have hl (j : ι) : inner ℝ (d.globalFlux hK hA C hC j) (q.2 j) =
      ∫ z in K, (∑ i, A z i j * D i z) * fderiv ℝ φ z (b j) := by
    rw [L2.inner_def]
    calc
      _ = ∫ z, K.indicator (fun z => (∑ i, A z i j * D i z) * fderiv ℝ φ z (b j)) z := by
        apply integral_congr_ae
        filter_upwards [d.globalFlux_ae_eq hK hA C hC j, hqdφ j] with z hz hd
        simp only [RCLike.inner_apply, conj_trivial, hz, hd]
        by_cases hk : z ∈ K <;> simp [hk, mul_comm]
      _ = _ := integral_indicator hK
  have hr : inner ℝ (d.globalForcing hK) q.1 = -(∫ z in K, F z * φ z) := by
    rw [L2.inner_def, ← integral_indicator hK, ← integral_neg]
    apply integral_congr_ae
    filter_upwards [d.globalForcing_ae_eq hK, hqφ] with z hz hφz
    simp only [RCLike.inner_apply, conj_trivial, hz, hφz]
    by_cases hk : z ∈ K <;> simp [hk, mul_comm]
  simp_rw [hl]
  rw [hr, ← integral_finsetSum]
  · have he : (fun z => ∑ j, (∑ i, A z i j * D i z) * fderiv ℝ φ z (b j)) =
        (fun z => ∑ i, ∑ j, A z i j * D i z * fderiv ℝ φ z (b j)) := by
      funext z
      simp_rw [Finset.sum_mul]
      exact Finset.sum_comm
    rw [he]
    exact d.variational φ hφ hcφ (hsφ.trans hS)
  · intro j _
    exact (d.memLp_flux hA C hC j).integrable_mul
      ((((hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const).memLp_of_hasCompactSupport
        (hcφ.fderiv_apply ℝ (b j)) : MemLp _ 2 (volume : Measure E)).restrict K)

end LocalWeakPoissonData

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M] [LindelofSpace M]
  [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local instance localWeakPoissonGraphContinuousMetric :
    IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
  continuousRiemannianBundle_of_contMDiff (I := I)

/-- The constructed manifold solution supplies actual global L² flux and
negative forcing, whose variational identity holds on every test-graph closure
supported inside the fixed compact coordinate neighborhood. -/
theorem weakPoissonSolution_coordinate_graph_variational
    (b : OrthonormalBasis ι ℝ E) (c : M)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target)
    (h : Lp ℝ 2 (riemannianVolume (I := I) (M := M)))
    (hh : (∫ x, h x ∂riemannianVolume (I := I)) = 0) :
    ∃ G : ι → Lp ℝ 2 (volume : Measure E),
    ∃ g : Lp ℝ 2 (volume : Measure E),
      (∀ j, G j =ᵐ[volume] K.indicator (fun z => ∑ i,
        coordinateEllipticMatrix (I := I) b.toBasis c z i j *
          energyChartDerivative c hK hKt (b i) (weakPoissonSolution h) z)) ∧
      (g =ᵐ[volume] (fun z => -(K.indicator (fun z =>
        matrixDensity (coordinateMetric (I := I) b.toBasis c z) *
          h ((extChartAt I c).symm z)) z))) ∧
      ∀ (S : Set E), S ⊆ K →
      ∀ (p : Lp ℝ 2 (volume : Measure E) × (ι → Lp ℝ 2 (volume : Measure E))),
        p ∈ closure (c1SupportedTestGraph (fun i => b i) S) →
          (∑ j, inner ℝ (G j) (p.2 j)) = inner ℝ g p.1 := by
  let d := weakPoissonSolution_local_data b c hK hKt h hh
  have hA (i j : ι) : AEStronglyMeasurable
      (fun z => coordinateEllipticMatrix (I := I) b.toBasis c z i j)
      ((volume : Measure E).restrict K) := by
    have hc := (continuousOn_coordinateEllipticMatrix (I := I) b.toBasis c).mono hKt
    exact ((continuous_apply j).comp_continuousOn
      ((continuous_apply i).comp_continuousOn hc)).aestronglyMeasurable hK.measurableSet
  obtain ⟨C, _, hC⟩ := exists_coordinateEllipticMatrix_entry_bound (I := I) b.toBasis c hK hKt
  have hb : ∀ᵐ z ∂(volume : Measure E).restrict K, ∀ i j,
      ‖coordinateEllipticMatrix (I := I) b.toBasis c z i j‖ ≤ C := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
    exact hC z hz
  refine ⟨d.globalFlux hK.measurableSet hA C hb, d.globalForcing hK.measurableSet,
    ?_, ?_, ?_⟩
  · exact d.globalFlux_ae_eq hK.measurableSet hA C hb
  · exact d.globalForcing_ae_eq hK.measurableSet
  · intro S hS p hp
    exact d.variational_on_graph_closure hK.measurableSet hA C hb hS hp

end AlmostSchur
