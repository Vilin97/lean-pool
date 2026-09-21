/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.EnergyMean

/-! # Global Green identity on the energy completion

The proved classical Green identity extends in its first argument by density
and continuity. Consequently the realized variational solution solves the
transposed Laplace equation on C² tests. This is not a smoothness assertion.
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

local notation "TM" => (TangentSpace I : M → Type _)

local instance : IsContinuousRiemannianBundle E TM :=
  continuousRiemannianBundle_of_contMDiff (I := I)
local instance : IsFiniteMeasure (riemannianVolume (I := I) (M := M)) :=
  ⟨(riemannianVolume_finite_positive (I := I)).2⟩

/-- Subtracting the mean of the second test leaves the energy pairing unchanged. -/
theorem dirichletForm_meanCorrectedEnergyTest (g f : M → ℝ) (hf : CMDiff 1 f) :
    dirichletForm (I := I) g (meanCorrectedEnergyTest f hf).val =
      dirichletForm (I := I) g f := by
  simp only [dirichletForm, gradient_meanCorrectedEnergyTest]

/-- The actual C² Laplacian is square integrable on the closed manifold. -/
theorem memLp_laplacian (cov : CovariantDerivative I E TM)
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    (f : M → ℝ) (hf : CMDiff 2 f) :
    MemLp (laplacian cov f) 2 (riemannianVolume (I := I)) :=
  (continuous_laplacian cov hm ht f hf).memLp_of_hasCompactSupport
    isClosed_closure.isCompact

/-- The global Green formula extends to every element of the energy completion. -/
theorem integral_energyCompletionToL2_mul_laplacian
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov)
    (ht : cov.torsion = 0) (u : EnergyCompletion (I := I) (M := M))
    (f : M → ℝ) (hf : CMDiff 2 f) :
    (∫ x, energyCompletionToL2 u x * laplacian cov f x ∂riemannianVolume (I := I)) =
      -inner ℝ u (energyToCompletion (meanCorrectedEnergyTest f (hf.of_le (by norm_num)))) := by
  let hf1 : CMDiff 1 f := hf.of_le (by norm_num)
  let F := energyToCompletion (meanCorrectedEnergyTest f hf1)
  let hl := memLp_laplacian cov hm ht f hf
  let L := hl.toLp (laplacian cov f)
  have hpair (w : EnergyCompletion (I := I) (M := M)) :
      inner ℝ (energyCompletionToL2 w) L =
        ∫ x, energyCompletionToL2 w x * laplacian cov f x ∂riemannianVolume (I := I) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hl.coeFn_toLp] with x hx
    change L x = laplacian cov f x at hx
    simp only [RCLike.inner_apply, conj_trivial, hx, mul_comm]
  have hidentity : inner ℝ (energyCompletionToL2 u) L = -inner ℝ u F := by
    refine (denseRange_energyToCompletion (I := I) (M := M)).induction_on
      (p := fun w => inner ℝ (energyCompletionToL2 w) L = -inner ℝ w F) u ?_ ?_
    · exact isClosed_eq (energyCompletionToL2.continuous.inner continuous_const)
        (continuous_id.inner continuous_const).neg
    · intro g
      rw [hpair]
      have hi : (∫ x, energyCompletionToL2 (energyToCompletion g) x * laplacian cov f x
          ∂riemannianVolume (I := I)) =
          ∫ x, g.val x * laplacian cov f x ∂riemannianVolume (I := I) := by
        apply integral_congr_ae
        filter_upwards [energyCompletionToL2_core_ae_eq g] with x hx
        rw [hx]
      rw [hi, integral_mul_laplacian cov hm ht g.val f g.property.1 hf]
      dsimp only [F]
      rw [energyCompletion_inner, dirichletForm_meanCorrectedEnergyTest]
  rw [hpair] at hidentity
  exact hidentity

/-- The actual L² realization solves the transposed Laplace equation on all C² tests. -/
theorem weakPoissonSolution_laplacian_test
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov)
    (ht : cov.torsion = 0) (h : Lp ℝ 2 (riemannianVolume (I := I) (M := M)))
    (hh : (∫ x, h x ∂riemannianVolume (I := I)) = 0)
    (f : M → ℝ) (hf : CMDiff 2 f) :
    (∫ x, energyCompletionToL2 (weakPoissonSolution h) x * laplacian cov f x
      ∂riemannianVolume (I := I)) = ∫ x, h x * f x ∂riemannianVolume (I := I) := by
  rw [integral_energyCompletionToL2_mul_laplacian cov hm ht _ f hf,
    weakPoissonSolution_meanCorrected_test h hh f (hf.of_le (by norm_num)), neg_neg]

/-- The realized solution has the L² estimate obtained by applying Poincaré twice. -/
theorem norm_weakPoissonSolution_L2_le
    (h : Lp ℝ 2 (riemannianVolume (I := I) (M := M))) :
    ‖energyCompletionToL2 (weakPoissonSolution h)‖ ≤
      energyL2Constant (I := I) (M := M) ^ 2 * ‖h‖ := by
  calc
    _ ≤ ‖energyCompletionToL2 (I := I) (M := M)‖ * ‖weakPoissonSolution h‖ :=
      energyCompletionToL2.le_opNorm _
    _ ≤ energyL2Constant (I := I) (M := M) * ‖weakPoissonSolution h‖ :=
      mul_le_mul_of_nonneg_right norm_energyCompletionToL2_le (norm_nonneg _)
    _ ≤ energyL2Constant (I := I) (M := M) *
        (‖h‖ * energyL2Constant (I := I) (M := M)) :=
      mul_le_mul_of_nonneg_left (norm_weakPoissonSolution_le h) energyL2Constant_pos.le
    _ = _ := by ring

/-- Genuine mean-zero L² existence for the transposed Poisson equation.
No classical regularity or uniqueness among arbitrary L² distributions is asserted. -/
theorem exists_weakPoisson_L2
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov)
    (ht : cov.torsion = 0) (h : Lp ℝ 2 (riemannianVolume (I := I) (M := M)))
    (hh : (∫ x, h x ∂riemannianVolume (I := I)) = 0) :
    ∃ u : Lp ℝ 2 (riemannianVolume (I := I) (M := M)),
      (∫ x, u x ∂riemannianVolume (I := I)) = 0 ∧
      ‖u‖ ≤ energyL2Constant (I := I) (M := M) ^ 2 * ‖h‖ ∧
      ∀ f : M → ℝ, CMDiff 2 f →
        (∫ x, u x * laplacian cov f x ∂riemannianVolume (I := I)) =
          ∫ x, h x * f x ∂riemannianVolume (I := I) :=
  ⟨energyCompletionToL2 (weakPoissonSolution h), integral_weakPoissonSolution h,
    norm_weakPoissonSolution_L2_le h, fun f hf =>
      weakPoissonSolution_laplacian_test cov hm ht h hh f hf⟩

end AlmostSchur
