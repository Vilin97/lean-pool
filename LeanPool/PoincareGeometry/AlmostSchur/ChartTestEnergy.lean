/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.EnergyLocalVariational

/-! # Energy of lifted compact coordinate tests

This bridge supplies the actual quadratic coordinate energy before any
completion of the Euclidean test space is chosen.
-/

@[expose] public noncomputable section
open Bundle Set MeasureTheory
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

theorem dirichletForm_chartTestLift_self (b : OrthonormalBasis ι ℝ E) (c : M)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target)
    (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hφK : tsupport φ ⊆ K) :
    dirichletForm (I := I) (chartTestLift (I := I) c φ) (chartTestLift (I := I) c φ) =
      ∫ z in K, ∑ i, ∑ j, coordinateEllipticMatrix (I := I) b.toBasis c z i j *
        fderiv ℝ φ z (b i) * fderiv ℝ φ z (b j) := by
  have hs := hφK.trans hKt
  have hf := contMDiff_chartTestLift (I := I) c φ hφ hc hs
  rw [dirichletForm_chartTestLift_eq_sum b c φ hφ hc hs _ hf]
  have hint (i : ι) := integrable_chartDerivative_mul_chartTestFluxCoeff b c φ hφ hc hs
    (chartTestLift (I := I) c φ) hf i
  rw [← integral_finsetSum _ (fun i _ => hint i)]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) (fun z hz => ?_)]
  · apply setIntegral_congr_fun hK.measurableSet
    intro z hz
    apply Finset.sum_congr rfl
    intro i _
    rw [fderiv_chartTestLift_comp_symm c φ (hKt hz),
      chartTestFluxCoeff_eq_sum b c φ hφ hc hs (hKt hz) i, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · apply Finset.sum_eq_zero
    intro i _
    rw [chartTestFluxCoeff_eq_zero_off_support b c φ hφ hc hs (fun hx => hz (hφK hx)) i,
      mul_zero]

local instance chartTestEnergy_continuousRiemannian : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
  continuousRiemannianBundle_of_contMDiff (I := I)

/-- A fixed compact chart subset gives one energy bound for all supported C¹ tests. -/
theorem exists_dirichletForm_chartTestLift_bound (b : OrthonormalBasis ι ℝ E) (c : M)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (φ : E → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ K →
      dirichletForm (I := I) (chartTestLift (I := I) c φ) (chartTestLift (I := I) c φ) ≤
        B * ∫ z in K, ∑ i, (fderiv ℝ φ z (b i)) ^ 2 := by
  obtain ⟨B, hB0, hB⟩ := exists_coordinateEllipticMatrix_upper_bound (I := I) b.toBasis c hK hKt
  refine ⟨B, hB0, fun φ hφ hc hs => ?_⟩
  rw [dirichletForm_chartTestLift_self b c hK hKt φ hφ hc hs, ← integral_const_mul]
  have hd (i : ι) : Continuous (fun z => fderiv ℝ φ z (b i)) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hA (i j : ι) : ContinuousOn
      (fun z => coordinateEllipticMatrix (I := I) b.toBasis c z i j) K :=
    (continuousOn_pi.mp (continuousOn_pi.mp
      ((continuousOn_coordinateEllipticMatrix (I := I) b.toBasis c).mono hKt) i) j)
  apply setIntegral_mono_on
    ((continuousOn_finsetSum _ (fun i _ => continuousOn_finsetSum _ (fun j _ =>
      ((hA i j).mul (hd i).continuousOn).mul (hd j).continuousOn))).integrableOn_compact hK)
    ((continuous_const.mul (continuous_finsetSum _ (fun i _ => (hd i).pow 2))).continuousOn.integrableOn_compact hK)
    hK.measurableSet
  intro z hz
  simpa [EuclideanSpace.real_norm_sq_eq, Pi.mul_apply, Pi.pow_apply] using
    hB z hz (WithLp.toLp 2 (fun i => fderiv ℝ φ z (b i)))

variable [PreconnectedSpace M]

/-- Mean correction and inclusion into the completion preserve the test's energy norm. -/
theorem norm_completed_meanCorrectedEnergyTest (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f) :
    ‖energyToCompletion (meanCorrectedEnergyTest f hf)‖ =
      Real.sqrt (dirichletForm (I := I) f f) := by
  rw [energyToCompletion.norm_map, energySpace_norm]
  congr 1
  unfold dirichletForm
  simp only [gradient_meanCorrectedEnergyTest]

/-- Uniform continuity estimate into the energy completion; no Euclidean completion
or density theorem is assumed here. -/
theorem exists_completed_chartTestLift_bound (b : OrthonormalBasis ι ℝ E) (c : M)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : E → ℝ) (hφ : ContDiff ℝ 1 φ)
      (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ K),
      ‖energyToCompletion (meanCorrectedEnergyTest (chartTestLift (I := I) c φ)
        (contMDiff_chartTestLift c φ hφ hc (hs.trans hKt)))‖ ≤
        C * Real.sqrt (∫ z in K, ∑ i, (fderiv ℝ φ z (b i)) ^ 2) := by
  obtain ⟨B, hB0, hB⟩ := exists_dirichletForm_chartTestLift_bound b c hK hKt
  refine ⟨Real.sqrt B, Real.sqrt_nonneg _, fun φ hφ hc hs => ?_⟩
  rw [norm_completed_meanCorrectedEnergyTest]
  calc
    _ ≤ Real.sqrt (B * ∫ z in K, ∑ i, (fderiv ℝ φ z (b i)) ^ 2) :=
      Real.sqrt_le_sqrt (hB φ hφ hc hs)
    _ = _ := Real.sqrt_mul hB0 _

end AlmostSchur
