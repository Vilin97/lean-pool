/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
module

public import LeanPool.Malliavin.Malliavin.BrownianChaosTotality

/-!
# The canonical positive Brownian chaos embedding

The completed simplex integrals form an orthogonal family of linear isometries.  Assembling them
gives a single canonical isometry from the external Hilbert sum of positive simplex kernels into
random `L²`; its range is exactly the closed supremum of the positive canonical Brownian chaoses.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace

noncomputable
section

namespace Malliavin.BrownianIteratedConstruction

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

omit [CompleteSpace W] [BorelSpace W] in
/-- The canonical Brownian simplex integral at one positive order, bundled as a linear
isometry. -/
noncomputable def brownianSimplexIntegralLI
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) (n : ℕ) :
    IteratedIntegralConstruction.SimplexKernel (n + 1) →ₗᵢ[ℝ] RandomL2 P where
  toLinearMap := (simplexIntegral hB (n + 1)).toLinearMap
  norm_map' f := by
    have hinner := inner_simplexIntegral hB hsm (orderedBoxDense_succ n) f f
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hinner
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hinner

omit [CompleteSpace W] [BorelSpace W] in
@[simp]
theorem brownianSimplexIntegralLI_apply
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (n : ℕ) (f : IteratedIntegralConstruction.SimplexKernel (n + 1)) :
    brownianSimplexIntegralLI hB hsm n f = simplexIntegral hB (n + 1) f :=
  rfl

omit [CompleteSpace W] [BorelSpace W] in
/-- Positive-order canonical Brownian simplex integrals form an orthogonal family. -/
theorem brownianSimplexIntegralLI_orthogonalFamily
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) :
    OrthogonalFamily ℝ
      (fun n : ℕ => IteratedIntegralConstruction.SimplexKernel (n + 1))
      (brownianSimplexIntegralLI hB hsm) := by
  intro m n hmn f g
  exact inner_simplexIntegral_of_ne hB hsm
    (fun h => hmn (Nat.succ.inj h))
    (orderedBoxDense_succ m) (orderedBoxDense_succ n) f g

omit [CompleteSpace W] [BorelSpace W] in
/-- The canonical isometric embedding of the external sum of all positive simplex orders. -/
noncomputable def brownianPositiveTowerLI
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) :
    IteratedIntegralConstruction.PositiveKernelSum →ₗᵢ[ℝ] RandomL2 P :=
  (brownianSimplexIntegralLI_orthogonalFamily hB hsm).linearIsometry

omit [CompleteSpace W] [BorelSpace W] in
@[simp]
theorem brownianPositiveTowerLI_single
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (n : ℕ) (f : IteratedIntegralConstruction.SimplexKernel (n + 1)) :
    brownianPositiveTowerLI hB hsm (lp.single 2 n f) =
      simplexIntegral hB (n + 1) f := by
  exact (brownianSimplexIntegralLI_orthogonalFamily hB hsm
    ).linearIsometry_apply_single f

omit [CompleteSpace W] [BorelSpace W] in
/-- The global positive-tower value is the convergent sum of its canonical orderwise simplex
integrals. -/
theorem hasSum_brownianPositiveTowerLI
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    (f : IteratedIntegralConstruction.PositiveKernelSum) :
    HasSum (fun n => simplexIntegral hB (n + 1) (f n))
      (brownianPositiveTowerLI hB hsm f) := by
  exact (brownianSimplexIntegralLI_orthogonalFamily hB hsm
    ).hasSum_linearIsometry f

omit [CompleteSpace W] [BorelSpace W] in
/-- The completed canonical chaos of positive order `n + 1` is precisely the closed range of
the corresponding simplex isometry. -/
theorem brownianHomogeneousChaos_succ_eq_range_simplexIntegralLI
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) (n : ℕ) :
    (brownianHomogeneousChaos hB (n + 1) : Submodule ℝ (RandomL2 P)) =
      LinearMap.range (brownianSimplexIntegralLI hB hsm n).toLinearMap := by
  apply le_antisymm
  · unfold brownianHomogeneousChaos brownianMultipleIntegralRange
    apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨f, rfl⟩
      exact ⟨restrictToSimplex (n + 1) f, rfl⟩
    · exact (brownianSimplexIntegralLI hB hsm n).isometry.isClosedEmbedding.isClosed_range
  · rintro _ ⟨f, rfl⟩
    change simplexIntegral hB (n + 1) f ∈ brownianHomogeneousChaos hB (n + 1)
    refine (orderedBoxDense_succ n).induction_on f
      ((brownianHomogeneousChaos hB (n + 1)).isClosed.preimage
        (simplexIntegral hB (n + 1)).continuous) ?_
    intro c
    rw [simplexIntegral_orderedBoxToSimplexKernel hB hsm (orderedBoxDense_succ n)]
    unfold orderedBoxToRandom
    rw [Finsupp.linearCombination_apply]
    apply Submodule.sum_mem
    intro a _ha
    apply Submodule.smul_mem
    rw [← positiveIntegralCLM_box hB hsm (orderedBoxDense_succ n) a]
    exact integralCLM_mem_brownianHomogeneousChaos hB (n + 1)
      (boxKernel a.u a.v)

omit [CompleteSpace W] [BorelSpace W] in
/-- The range of the global positive tower is the closed supremum of the positive canonical
Brownian chaoses. -/
theorem range_brownianPositiveTowerLI
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t)) :
    LinearMap.range (brownianPositiveTowerLI hB hsm).toLinearMap =
      (⨆ n : ℕ,
        (brownianHomogeneousChaos hB (n + 1) : Submodule ℝ (RandomL2 P))
      ).topologicalClosure := by
  rw [brownianPositiveTowerLI,
    (brownianSimplexIntegralLI_orthogonalFamily hB hsm).range_linearIsometry]
  congr 1
  exact iSup_congr fun n =>
    (brownianHomogeneousChaos_succ_eq_range_simplexIntegralLI hB hsm n).symm

omit [CompleteSpace W] [BorelSpace W] in
/-- Every value of the global canonical positive tower is a natural Itô terminal value. -/
theorem brownianPositiveTowerLI_mem_naturalItoRange
    (hB : IsPreBrownianReal B P) (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm)
    (f : IteratedIntegralConstruction.PositiveKernelSum) :
    brownianPositiveTowerLI hB hsm f ∈ naturalItoRange hB hsm hnat := by
  apply Submodule.topologicalClosure_minimal
    (⨆ n : ℕ,
      (brownianHomogeneousChaos hB (n + 1) : Submodule ℝ (RandomL2 P)))
  · exact iSup_le fun n =>
      brownianHomogeneousChaos_le_naturalItoRange hB hsm hnat (n + 1)
        (Nat.zero_lt_succ n)
  · exact isClosed_naturalItoRange hB hsm hnat
  · rw [← range_brownianPositiveTowerLI hB hsm]
    exact LinearMap.mem_range_self (brownianPositiveTowerLI hB hsm).toLinearMap f

end Malliavin.BrownianIteratedConstruction

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
