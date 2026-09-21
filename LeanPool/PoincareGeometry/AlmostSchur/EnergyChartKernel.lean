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

public import LeanPool.PoincareGeometry.AlmostSchur.EnergyChartDerivative
public import LeanPool.PoincareGeometry.AlmostSchur.L2TestUniqueness

/-! # Local derivatives of elements with zero L² realization

The completed integration-by-parts identity and uniqueness of distributions
show that a zero realized function has zero coordinate derivative in the
interior of every compact chart set. Boundary values are not asserted.
-/

@[expose] public noncomputable section
open Bundle Set MeasureTheory
open scoped Manifold ContDiff Topology

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
  [T2Space M] [CompactSpace M] [PreconnectedSpace M]

/-- Zero realized L² function implies vanishing coordinate derivative test pairings. -/
theorem energyChartDerivative_test_eq_zero_of_realization_eq_zero
    (c : M) {K : Set E} (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt I c).target) (v : E)
    (u : EnergyCompletion (I := I) (M := M)) (hu : energyCompletionToL2 u = 0)
    (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hφK : tsupport φ ⊆ K) :
    ∫ z in K, φ z * energyChartDerivative c hK hKt v u z = 0 := by
  have h := setIntegral_energyChartDerivative c hK hKt v u φ
    (hφ.of_le (by simp)) hcφ hφK
  have hz : (energyCompletionToL2 u : M → ℝ) =ᵐ[riemannianVolume (I := I)] 0 := by
    rw [hu]
    exact Lp.coeFn_zero ℝ 2 _
  have hc := ae_eq_comp_chart_symm hz c hK hKt
  have hl : (∫ z in K, energyCompletionToL2 u ((extChartAt I c).symm z) *
      fderiv ℝ φ z v) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hc] with z hzz
    simp only [Function.comp_apply, Pi.zero_apply] at hzz
    change energyCompletionToL2 u ((extChartAt I c).symm z) * fderiv ℝ φ z v = 0
    rw [hzz, zero_mul]
  rw [hl] at h
  simpa only [mul_comm, neg_eq_zero] using h.symm

/-- Local AE vanishing is asserted only in the compact set's interior. -/
theorem energyChartDerivative_ae_eq_zero_of_realization_eq_zero
    (c : M) {K : Set E} (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt I c).target) (v : E)
    (u : EnergyCompletion (I := I) (M := M)) (hu : energyCompletionToL2 u = 0) :
    ∀ᵐ z ∂(volume : Measure E).restrict K,
      z ∈ interior K → energyChartDerivative c hK hKt v u z = 0 := by
  letI : IsFiniteMeasure ((volume : Measure E).restrict K) :=
    ⟨by simpa using hK.measure_lt_top (μ := (volume : Measure E))⟩
  apply lp_ae_eq_zero_on_of_smooth_tests _ isOpen_interior
  intro φ hφ hcφ hs
  exact energyChartDerivative_test_eq_zero_of_realization_eq_zero c hK hKt v u hu
    φ hφ hcφ (hs.trans interior_subset)

end AlmostSchur
