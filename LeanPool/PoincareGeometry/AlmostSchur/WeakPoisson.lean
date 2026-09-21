/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.EnergyL2Completion
public import Mathlib.MeasureTheory.Function.L2Space

/-! # Completed variational forcing

The actual bounded L² realization defines forcing on the genuine energy
Hilbert space. We also expose map-parameterized helpers. No injectivity of
the L² realization or distributional or classical regularity is asserted.
The minus sign matches the convention `Δ = div grad`.
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

/-- Negative L² pairing pulled back along a bounded realization map. -/
def weakPoissonForcingOfMap
    (J : EnergyCompletion (I := I) (M := M) →L[ℝ] Lp ℝ 2 (riemannianVolume (I := I) (M := M)))
    (h : Lp ℝ 2 (riemannianVolume (I := I) (M := M))) :
    EnergyCompletion (I := I) (M := M) →L[ℝ] ℝ :=
  -(innerSL ℝ h).comp J

/-- The forcing bound is the L² Cauchy–Schwarz estimate. -/
theorem norm_weakPoissonForcingOfMap_le
    (J : EnergyCompletion (I := I) (M := M) →L[ℝ] Lp ℝ 2 (riemannianVolume (I := I) (M := M)))
    (h : Lp ℝ 2 (riemannianVolume (I := I) (M := M))) :
    ‖weakPoissonForcingOfMap J h‖ ≤ ‖h‖ * ‖J‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro v
  change ‖-inner ℝ h (J v)‖ ≤ _
  rw [norm_neg]
  exact (norm_inner_le_norm h (J v)).trans
    (by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (J.le_opNorm v) (norm_nonneg h))

/-- Riesz gives a unique solution of the completed variational equation. -/
theorem existsUnique_weakPoissonOfMap
    (J : EnergyCompletion (I := I) (M := M) →L[ℝ] Lp ℝ 2 (riemannianVolume (I := I) (M := M)))
    (h : Lp ℝ 2 (riemannianVolume (I := I) (M := M))) :
    ∃! u : EnergyCompletion (I := I) (M := M), ∀ v,
      inner ℝ u v = -inner ℝ h (J v) :=
  existsUnique_energyRiesz (weakPoissonForcingOfMap J h)

/-- The solution's energy norm is bounded by the forcing and realization norms. -/
theorem norm_weakPoissonOfMap_le
    (J : EnergyCompletion (I := I) (M := M) →L[ℝ] Lp ℝ 2 (riemannianVolume (I := I) (M := M)))
    (h : Lp ℝ 2 (riemannianVolume (I := I) (M := M))) :
    ‖energyRiesz (weakPoissonForcingOfMap J h)‖ ≤ ‖h‖ * ‖J‖ := by
  rw [norm_energyRiesz]
  exact norm_weakPoissonForcingOfMap_le J h

/-- For a realization agreeing with core functions, the variational identity
on core tests is the actual negative forcing integral. -/
theorem weakPoissonOfMap_core_identity
    (J : EnergyCompletion (I := I) (M := M) →L[ℝ] Lp ℝ 2 (riemannianVolume (I := I) (M := M)))
    (hJ : ∀ f : EnergySpace (I := I) (M := M),
      (J (energyToCompletion f) : M → ℝ) =ᵐ[riemannianVolume (I := I)] f.val)
    (h : Lp ℝ 2 (riemannianVolume (I := I) (M := M)))
    (f : EnergySpace (I := I) (M := M)) :
    inner ℝ (energyRiesz (weakPoissonForcingOfMap J h)) (energyToCompletion f) =
      -(∫ x, h x * f.val x ∂riemannianVolume (I := I)) := by
  rw [energyRiesz_inner]
  change -inner ℝ h (J (energyToCompletion f)) = _
  rw [L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [hJ f] with x hx
  simp [hx, mul_comm]

/-- Actual L² forcing on the mean-zero Hilbert energy completion. -/
def weakPoissonForcing (h : Lp ℝ 2 (riemannianVolume (I := I) (M := M))) :
    EnergyCompletion (I := I) (M := M) →L[ℝ] ℝ :=
  weakPoissonForcingOfMap energyCompletionToL2 h

/-- The actual forcing functional has the proved Poincaré/Cauchy–Schwarz bound. -/
theorem norm_weakPoissonForcing_le (h : Lp ℝ 2 (riemannianVolume (I := I) (M := M))) :
    ‖weakPoissonForcing h‖ ≤ ‖h‖ * energyL2Constant (I := I) (M := M) :=
  (norm_weakPoissonForcingOfMap_le energyCompletionToL2 h).trans
    (mul_le_mul_of_nonneg_left norm_energyCompletionToL2_le (norm_nonneg h))

/-- The actual completed variational solution, with no PDE-regularity assertion. -/
def weakPoissonSolution (h : Lp ℝ 2 (riemannianVolume (I := I) (M := M))) :
    EnergyCompletion (I := I) (M := M) := energyRiesz (weakPoissonForcing h)

/-- The chosen solution satisfies the actual completed variational identity. -/
theorem weakPoissonSolution_inner (h : Lp ℝ 2 (riemannianVolume (I := I) (M := M)))
    (v : EnergyCompletion (I := I) (M := M)) :
    inner ℝ (weakPoissonSolution h) v = -inner ℝ h (energyCompletionToL2 v) :=
  energyRiesz_inner (weakPoissonForcing h) v

/-- Existence and uniqueness in the actual energy completion, not assumed solvability. -/
theorem existsUnique_weakPoisson (h : Lp ℝ 2 (riemannianVolume (I := I) (M := M))) :
    ∃! u : EnergyCompletion (I := I) (M := M), ∀ v,
      inner ℝ u v = -inner ℝ h (energyCompletionToL2 v) :=
  existsUnique_weakPoissonOfMap energyCompletionToL2 h

/-- Core tests recover the actual negative integral against the forcing. -/
theorem weakPoissonSolution_core_identity
    (h : Lp ℝ 2 (riemannianVolume (I := I) (M := M)))
    (f : EnergySpace (I := I) (M := M)) :
    inner ℝ (weakPoissonSolution h) (energyToCompletion f) =
      -(∫ x, h x * f.val x ∂riemannianVolume (I := I)) :=
  weakPoissonOfMap_core_identity energyCompletionToL2 energyCompletionToL2_core_ae_eq h f

/-- Quantitative energy-norm bound for the completed variational solution. -/
theorem norm_weakPoissonSolution_le (h : Lp ℝ 2 (riemannianVolume (I := I) (M := M))) :
    ‖weakPoissonSolution h‖ ≤ ‖h‖ * energyL2Constant (I := I) (M := M) := by
  unfold weakPoissonSolution
  rw [norm_energyRiesz]
  exact norm_weakPoissonForcing_le h

end AlmostSchur
