/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.WeakPoissonH2Jet
public import LeanPool.PoincareGeometry.AlmostSchur.ScalarCommutatorForcing
public import LeanPool.PoincareGeometry.AlmostSchur.MetricHigherRegularity

/-! # A differentiated equation for the actual weak Poisson solution

The order-two jet is constructed, and its principal differentiated equation
has scalar L² forcing. This does not assert an order-three jet.
-/
@[expose] public noncomputable section
open Set Bundle MeasureTheory Filter
open scoped Manifold ContDiff Topology BigOperators
namespace AlmostSchur
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M] [LindelofSpace M]
  [T2Space M] [CompactSpace M] [PreconnectedSpace M]

theorem exists_weakPoisson_differentiated_local_equation
    [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
    [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]
    (b : OrthonormalBasis ι ℝ E) (c : M) {K S : Set E}
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target) (hconv : Convex ℝ K)
    (hS : IsCompact S) (hSK : S ⊆ interior K)
    (f : Lp ℝ 2 (riemannianVolume (I := I) (M := M)))
    (hf : (∫ x, f x ∂riemannianVolume (I := I)) = 0)
    (hF : ContDiffOn ℝ ∞ (fun z => matrixDensity (coordinateMetric (I := I) b.toBasis c z) *
      f ((extChartAt I c).symm z)) (extChartAt I c).target) :
    ∃ J : LocalL2DerivativeJet (fun i => b i) S 2,
      (J.value [] =ᵐ[volume.restrict S] (fun z =>
        energyCompletionToL2 (weakPoissonSolution f) ((extChartAt I c).symm z))) ∧
      (∀ i, J.value [i] =ᵐ[volume.restrict S] (fun z =>
        energyChartDerivative c hK hKt (b i) (weakPoissonSolution f) z)) ∧
      ∀ k : ι, ∃ G : E → ℝ, MemLp G 2 (volume.restrict S) ∧
        ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ S →
          (∑ j, ∫ z in S, (∑ i, coordinateEllipticMatrix (I := I) b.toBasis c z i j *
            J.value [k, i] z) * fderiv ℝ φ z (b j)) = -(∫ z in S, G z * φ z) := by
  obtain ⟨J, C, hC, hJ0, hJ1, hJ2, hweak⟩ :=
    exists_weakPoisson_local_L2_jet_two b c hK hKt hconv hS hSK f hf
  let A := coordinateEllipticMatrix (I := I) b.toBasis c
  let F := fun z => matrixDensity (coordinateMetric (I := I) b.toBasis c z) *
    f ((extChartAt I c).symm z)
  have hSS : S ⊆ K := hSK.trans interior_subset
  have hSt := hSS.trans hKt
  have hA (i j : ι) : ContDiffOn ℝ ∞ (fun z => A z i j) (extChartAt I c).target :=
    (contDiff_apply_apply ℝ ℝ i j).comp_contDiffOn
      (contDiffOn_coordinateEllipticMatrix_of_order (I := I) ∞ b.toBasis c)
  have hpde : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ S →
      (∑ j, ∫ z in S, (∑ i, A z i j * J.value [i] z) * fderiv ℝ φ z (b j)) =
        -(∫ z in S, F z * φ z) := by
    intro φ hφ hc hs
    have hm (i j : ι) := memLp_mul_coefficient_on_compact hS
      ((hA i j).continuousOn.mono hSt) ((Lp.memLp (J.value [i])).restrict S)
    have ht (j : ι) : MemLp (fun z => fderiv ℝ φ z (b j)) 2 (volume.restrict S) :=
      ((contDiff_smooth_test_derivative hφ (b j)).continuous.memLp_of_hasCompactSupport
        (hc.fderiv_apply ℝ (b j)) : MemLp _ 2 volume).restrict S
    rw [← integral_finsetSum (f := fun j z =>
      (∑ i, A z i j * J.value [i] z) * fderiv ℝ φ z (b j))
      Finset.univ (fun j _ =>
      (memLp_finsetSum Finset.univ (fun i _ => hm i j)).integrable_mul (ht j))]
    have hid (z : E) : (∑ j, (∑ i, A z i j * J.value [i] z) * fderiv ℝ φ z (b j)) =
        ∑ i, ∑ j, A z i j * J.value [i] z * fderiv ℝ φ z (b j) := by
      simp_rw [Finset.sum_mul]
      exact Finset.sum_comm
    simp_rw [hid]
    have he := (weakPoissonSolution_local_data b c hK hKt f hf).variational
      φ (hφ.of_le (by decide)) hc (hs.trans hSS)
    have hz (z : E) (hz : z ∉ S) : φ z = 0 ∧ fderiv ℝ φ z = 0 :=
      ⟨image_eq_zero_of_notMem_tsupport (fun hh => hz (hs hh)),
       fderiv_of_notMem_tsupport ℝ (fun hh => hz (hs hh))⟩
    have hl : (∫ z in K, ∑ i, ∑ j, A z i j *
        energyChartDerivative c hK hKt (b i) (weakPoissonSolution f) z * fderiv ℝ φ z (b j)) =
        ∫ z in S, ∑ i, ∑ j, A z i j * J.value [i] z * fderiv ℝ φ z (b j) := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := K)
        (fun z hzK => by simp [(hz z (fun hh => hzK (hSS hh))).2])]
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := S)
        (fun z hzS => by simp [(hz z hzS).2])]
      apply integral_congr_ae
      filter_upwards [ae_all_iff.mpr hJ1] with z hj
      simp_rw [hj]
    have hr : (∫ z in K, F z * φ z) = ∫ z in S, F z * φ z := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := K)
        (fun z hzK => by simp [(hz z (fun hh => hzK (hSS hh))).1]),
        setIntegral_eq_integral_of_forall_compl_eq_zero (s := S)
        (fun z hzS => by simp [(hz z hzS).1])]
    change (∫ z in K, ∑ i, ∑ j, A z i j *
      energyChartDerivative c hK hKt (b i) (weakPoissonSolution f) z * fderiv ℝ φ z (b j)) =
      -(∫ z in K, F z * φ z) at he
    rwa [hl, hr] at he
  refine ⟨J, hJ0, hJ1, fun k => ?_⟩
  obtain ⟨G, hg, hrep, he⟩ := J.exists_scalar_forcing_differentiated_equation []
    (by simp) hS (isOpen_extChartAt_target c) hSt k A F hA hF hpde
  exact ⟨G, hg, he⟩

end AlmostSchur
