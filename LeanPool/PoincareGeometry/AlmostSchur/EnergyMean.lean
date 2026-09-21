/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.WeakPoisson

/-! # Mean-zero realization and mean-corrected variational tests

The integral constraint passes to completed elements by continuity and density.
Arbitrary C¹ test functions can be mean-corrected in the energy core; for
mean-zero L² forcing, the forcing integral is unchanged. No injectivity or
distributional interpretation of the completed realization is assumed.
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

local instance energyMeanContinuousMetric :
    IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
  continuousRiemannianBundle_of_contMDiff (I := I)
local instance energyMeanFiniteVolume :
    IsFiniteMeasure (riemannianVolume (I := I) (M := M)) :=
  ⟨(riemannianVolume_finite_positive (I := I)).2⟩

/-- Integration of the completed L² realization is continuous. -/
theorem continuous_integral_energyCompletionToL2 :
    Continuous (fun u : EnergyCompletion (I := I) (M := M) =>
      ∫ x, energyCompletionToL2 u x ∂riemannianVolume (I := I)) := by
  let oneL2 := (memLp_const (μ := riemannianVolume (I := I) (M := M))
    (p := 2) (1 : ℝ)).toLp (fun _ : M => (1 : ℝ))
  have heq (u : EnergyCompletion (I := I) (M := M)) :
      inner ℝ oneL2 (energyCompletionToL2 u) =
        ∫ x, energyCompletionToL2 u x ∂riemannianVolume (I := I) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(memLp_const (μ := riemannianVolume (I := I) (M := M))
      (p := 2) (1 : ℝ)).coeFn_toLp] with x hx
    change oneL2 x = 1 at hx
    simp [hx]
  have hc : Continuous (fun u : EnergyCompletion (I := I) (M := M) =>
      inner ℝ oneL2 (energyCompletionToL2 u)) :=
    ((innerSL ℝ oneL2).comp (energyCompletionToL2 (I := I) (M := M))).continuous
  simpa only [heq] using hc

/-- Every completed element has a mean-zero actual L² realization. -/
theorem integral_energyCompletionToL2 (u : EnergyCompletion (I := I) (M := M)) :
    (∫ x, energyCompletionToL2 u x ∂riemannianVolume (I := I)) = 0 := by
  refine (denseRange_energyToCompletion (I := I) (M := M)).induction_on
    (p := fun v => (∫ x, energyCompletionToL2 v x ∂riemannianVolume (I := I)) = 0) u
    (isClosed_eq continuous_integral_energyCompletionToL2 continuous_const) ?_
  intro f
  rw [energyCompletionToL2_core]
  exact integral_energyToL2Linear f

/-- The actual integral average; the measure itself is not a probability measure. -/
def riemannianMean (f : M → ℝ) : ℝ :=
  (∫ x, f x ∂riemannianVolume (I := I)) /
    (riemannianVolume (I := I) (M := M) univ).toReal

omit [PreconnectedSpace M] in
/-- Subtracting the average produces an actual mean-zero function. -/
theorem integral_sub_riemannianMean (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f) :
    (∫ x, (f x - riemannianMean (I := I) f) ∂riemannianVolume (I := I)) = 0 := by
  have hv : (riemannianVolume (I := I) (M := M) univ).toReal ≠ 0 :=
    (ENNReal.toReal_pos (riemannianVolume_finite_positive (I := I)).1.ne'
      (riemannianVolume_finite_positive (I := I)).2.ne).ne'
  rw [integral_sub (hf.continuous.integrable_of_hasCompactSupport isClosed_closure.isCompact)
    (integrable_const _), integral_const]
  simp only [riemannianMean, smul_eq_mul, Measure.real]
  field_simp
  ring

/-- An arbitrary C¹ function, with its mean removed, is a valid energy-core test. -/
def meanCorrectedEnergyTest (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f) :
    EnergySpace (I := I) (M := M) :=
  ⟨fun x => f x - riemannianMean (I := I) f,
    hf.sub contMDiff_const, integral_sub_riemannianMean f hf⟩

omit [PreconnectedSpace M] in
/-- Mean correction leaves the actual intrinsic gradient unchanged. -/
theorem gradient_meanCorrectedEnergyTest (f : M → ℝ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f) (x : M) :
    gradient (I := I) (meanCorrectedEnergyTest f hf).val x = gradient (I := I) f x := by
  change gradient (I := I) (fun y => f y - riemannianMean (I := I) f) x = _
  rw [gradient_sub_of_contMDiff _ _ hf contMDiff_const]
  simp [gradient, mvfderiv_const]

/-- Mean correction does not change the forcing pairing for mean-zero L² forcing. -/
theorem integral_forcing_meanCorrectedEnergyTest
    (h : Lp ℝ 2 (riemannianVolume (I := I) (M := M)))
    (hh : (∫ x, h x ∂riemannianVolume (I := I)) = 0)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f) :
    (∫ x, h x * (meanCorrectedEnergyTest f hf).val x ∂riemannianVolume (I := I)) =
      ∫ x, h x * f x ∂riemannianVolume (I := I) := by
  have hprod : Integrable (fun x => h x * f x) (riemannianVolume (I := I)) :=
    (Lp.memLp h).integrable_mul (memLp_c1_riemannianVolume hf)
  have hint : Integrable (fun x => h x) (riemannianVolume (I := I)) :=
    MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2) (Lp.memLp h)
  change (∫ x, h x * (f x - riemannianMean (I := I) f) ∂riemannianVolume (I := I)) = _
  simp_rw [mul_sub]
  rw [integral_sub hprod (hint.mul_const _), integral_mul_const, hh, zero_mul, sub_zero]

/-- The completed solution satisfies the uncorrected forcing integral on every
C¹ test, interpreted on the left through its mean-corrected energy-core class. -/
theorem weakPoissonSolution_meanCorrected_test
    (h : Lp ℝ 2 (riemannianVolume (I := I) (M := M)))
    (hh : (∫ x, h x ∂riemannianVolume (I := I)) = 0)
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f) :
    inner ℝ (weakPoissonSolution h) (energyToCompletion (meanCorrectedEnergyTest f hf)) =
      -(∫ x, h x * f x ∂riemannianVolume (I := I)) := by
  rw [weakPoissonSolution_core_identity, integral_forcing_meanCorrectedEnergyTest h hh f hf]

/-- In particular the realized variational solution has zero integral. -/
theorem integral_weakPoissonSolution (h : Lp ℝ 2 (riemannianVolume (I := I) (M := M))) :
    (∫ x, energyCompletionToL2 (weakPoissonSolution h) x ∂riemannianVolume (I := I)) = 0 :=
  integral_energyCompletionToL2 _

end AlmostSchur
