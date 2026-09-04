/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.AugmentedTwoPointKernel
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.Probability.Kernel.Composition.Lemmas

/-!
# Coordinatewise two-point mixtures

This file lifts the one-dimensional measurable two-point decomposition to a
finite independent product.  It is the product-measure interface used in the
proof of Theorem 2.1 before conditioning on all latent pairs.
-/

open MeasureTheory ProbabilityTheory Set

namespace Feige

noncomputable section

/-- Given all latent coordinates, the observations are conditionally
independent with the augmented two-point conditional marginals. -/
noncomputable def augmentedConditionalProduct {n : ℕ}
    (p : Fin n → AugmentedTwoPointParams) : Measure (Fin n → ℝ) :=
  Measure.pi (fun i ↦ augmentedTwoPointKernel (p i))

instance {n : ℕ} (p : Fin n → AugmentedTwoPointParams) :
    IsProbabilityMeasure (augmentedConditionalProduct p) := by
  unfold augmentedConditionalProduct
  infer_instance

/-- The independent product of the complete latent coordinate laws. -/
noncomputable def augmentedLatentProduct {n : ℕ}
    (μ : Fin n → Measure ℝ) (M : Fin n → ℝ) :
    Measure (Fin n → AugmentedTwoPointParams) :=
  Measure.pi (fun i ↦ augmentedLatentMeasure (μ i) (M i))

/-- Each coordinate of every conditional product is a mean-one law. -/
theorem augmentedConditionalProduct_coordinate_mean {n : ℕ}
    (p : Fin n → AugmentedTwoPointParams) (i : Fin n) :
    (∫ x : ℝ, x ∂augmentedTwoPointKernel (p i)) = 1 :=
  augmentedTwoPointKernel_mean (p i)

/-- Each coordinate of every conditional product is supported on at most two
points (one point on the atom branch). -/
theorem augmentedConditionalProduct_coordinate_support {n : ℕ}
    (p : Fin n → AugmentedTwoPointParams) (i : Fin n) :
    augmentedTwoPointKernel (p i)
        (match p i with
          | Sum.inl _ => ({1} : Set ℝ)ᶜ
          | Sum.inr q => ({q.1.1, q.1.2} : Set ℝ)ᶜ) = 0 :=
  augmentedTwoPointKernel_support (p i)

/-- Replacing every marginal by its full two-point kernel mixture leaves the
finite independent product law unchanged. -/
theorem pi_fullKernelMixture_eq
    {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℝ)
    [hprob : ∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, Integrable (fun x : ℝ ↦ x) (μ i))
    (hmean : ∀ i, (∫ x : ℝ, x ∂μ i) = 1)
    (hM : ∀ i, 0 < belowMoment (μ i)) :
    Measure.pi (fun i ↦ fullKernelMixture (μ i) (belowMoment (μ i))) =
      Measure.pi μ := by
  congr 1
  funext i
  exact fullKernelMixture_eq (hμ i) (hmean i) (hM i)

/-- The corresponding identity for probabilities of measurable events in the
coordinate product space. -/
theorem pi_fullKernelMixture_apply
    {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, Integrable (fun x : ℝ ↦ x) (μ i))
    (hmean : ∀ i, (∫ x : ℝ, x ∂μ i) = 1)
    (hM : ∀ i, 0 < belowMoment (μ i))
    (A : Set (ι → ℝ)) :
    Measure.pi (fun i ↦ fullKernelMixture (μ i) (belowMoment (μ i))) A =
      Measure.pi μ A := by
  rw [pi_fullKernelMixture_eq μ hμ hmean hM]

/-- Any nonnegative product-space integral may likewise be computed after
replacing the marginals by their full two-point mixtures.  This is the
Tonelli-ready form of the coordinatewise decomposition. -/
theorem lintegral_pi_fullKernelMixture
    {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, Integrable (fun x : ℝ ↦ x) (μ i))
    (hmean : ∀ i, (∫ x : ℝ, x ∂μ i) = 1)
    (hM : ∀ i, 0 < belowMoment (μ i))
    (f : (ι → ℝ) → ENNReal) :
    (∫⁻ x, f x
        ∂Measure.pi (fun i ↦
          fullKernelMixture (μ i) (belowMoment (μ i)))) =
      ∫⁻ x, f x ∂Measure.pi μ := by
  rw [pi_fullKernelMixture_eq μ hμ hmean hM]

/-- In particular, every measurable rejection event has exactly the same
probability before and after the coordinatewise latent two-point
decomposition. -/
theorem probability_pi_fullKernelMixture
    {ι : Type*} [Fintype ι]
    (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, Integrable (fun x : ℝ ↦ x) (μ i))
    (hmean : ∀ i, (∫ x : ℝ, x ∂μ i) = 1)
    (hM : ∀ i, 0 < belowMoment (μ i))
    {A : Set (ι → ℝ)} (hA : MeasurableSet A) :
    (∫⁻ x, A.indicator (fun _ ↦ (1 : ENNReal)) x
        ∂Measure.pi (fun i ↦
          fullKernelMixture (μ i) (belowMoment (μ i)))) =
      Measure.pi μ A := by
  rw [lintegral_pi_fullKernelMixture μ hμ hmean hM]
  exact lintegral_indicator_one hA

/-- Binary Fubini exchange: independently binding two latent laws against
their coordinate kernels is the same as binding their product against the
parallel product kernel.  This is the recursion step needed for a finite
product. -/
theorem parallelComp_comp_prod_measure
    {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ]
    (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel γ δ) [IsSFiniteKernel η]
    (μ : Measure α) (ν : Measure γ) [SFinite μ] [SFinite ν] :
    (κ ∥ₖ η) ∘ₘ (μ.prod ν) = (κ ∘ₘ μ).prod (η ∘ₘ ν) := by
  symm
  calc
    (κ ∘ₘ μ).prod (η ∘ₘ ν) =
      (κ ∥ₖ Kernel.id) ∘ₘ (μ.prod (η ∘ₘ ν)) := by
        rw [← Measure.prod_comp_left]
    _ = (κ ∥ₖ Kernel.id) ∘ₘ
        ((Kernel.id ∥ₖ η) ∘ₘ (μ.prod ν)) := by
          rw [← Measure.prod_comp_right]
    _ = ((κ ∥ₖ Kernel.id) ∘ₖ (Kernel.id ∥ₖ η)) ∘ₘ
        (μ.prod ν) := by rw [Measure.comp_assoc]
    _ = (κ ∥ₖ η) ∘ₘ (μ.prod ν) := by
      rw [Kernel.parallelComp_id_right_comp_parallelComp, Kernel.comp_id]

theorem augmentedTwoPointKernel_parallelComp_latent
    (μ₁ μ₂ : Measure ℝ) (M₁ M₂ : ℝ)
    [SFinite (augmentedLatentMeasure μ₁ M₁)]
    [SFinite (augmentedLatentMeasure μ₂ M₂)] :
    (augmentedTwoPointKernel ∥ₖ augmentedTwoPointKernel) ∘ₘ
        ((augmentedLatentMeasure μ₁ M₁).prod
          (augmentedLatentMeasure μ₂ M₂)) =
      (fullKernelMixture μ₁ M₁).prod (fullKernelMixture μ₂ M₂) := by
  rw [← augmentedTwoPointKernel_comp_latent μ₁ M₁,
    ← augmentedTwoPointKernel_comp_latent μ₂ M₂]
  exact parallelComp_comp_prod_measure _ _ _ _

/-- The two-coordinate original product law is a mixture of conditionally
independent augmented two-point laws. -/
theorem prod_eq_augmentedTwoPoint_mixture
    (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂]
    (hμ₁ : Integrable (fun x : ℝ ↦ x) μ₁)
    (hμ₂ : Integrable (fun x : ℝ ↦ x) μ₂)
    (hmean₁ : (∫ x : ℝ, x ∂μ₁) = 1)
    (hmean₂ : (∫ x : ℝ, x ∂μ₂) = 1)
    (hM₁ : 0 < belowMoment μ₁) (hM₂ : 0 < belowMoment μ₂) :
    (augmentedTwoPointKernel ∥ₖ augmentedTwoPointKernel) ∘ₘ
        ((augmentedLatentMeasure μ₁ (belowMoment μ₁)).prod
          (augmentedLatentMeasure μ₂ (belowMoment μ₂))) =
      μ₁.prod μ₂ := by
  let hlat₁ : IsProbabilityMeasure
      (augmentedLatentMeasure μ₁ (belowMoment μ₁)) :=
    augmentedLatentMeasure_isProbability hμ₁ hmean₁ hM₁
  let hlat₂ : IsProbabilityMeasure
      (augmentedLatentMeasure μ₂ (belowMoment μ₂)) :=
    augmentedLatentMeasure_isProbability hμ₂ hmean₂ hM₂
  rw [augmentedTwoPointKernel_parallelComp_latent,
    fullKernelMixture_eq hμ₁ hmean₁ hM₁,
    fullKernelMixture_eq hμ₂ hmean₂ hM₂]

section RecursiveFiniteKernel

/-- Measurable head/tail splitting of a homogeneous `Fin (n+1)` vector. -/
noncomputable def finHeadTailEquiv (α : Type*) [MeasurableSpace α] (n : ℕ) :
    (Fin (n + 1) → α) ≃ᵐ α × (Fin n → α) :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0

/-- A genuinely measurable finite parallel product of the augmented
coordinate kernels.  This avoids the unavailable `Kernel.pi`: the successor
case splits head and tail, uses `parallelComp`, and maps the output pair back
to a `Fin (n+1)` vector. -/
noncomputable def recursiveAugmentedKernel :
    (n : ℕ) → Kernel (Fin n → AugmentedTwoPointParams) (Fin n → ℝ)
  | 0 => Kernel.const _ (Measure.dirac (fun i => Fin.elim0 i))
  | n + 1 =>
      (((augmentedTwoPointKernel ∥ₖ recursiveAugmentedKernel n).comap
          (finHeadTailEquiv AugmentedTwoPointParams n)
          (finHeadTailEquiv AugmentedTwoPointParams n).measurable).map
        (finHeadTailEquiv ℝ n).symm)

instance recursiveAugmentedKernel_markov (n : ℕ) :
    IsMarkovKernel (recursiveAugmentedKernel n) := by
  induction n with
  | zero =>
      unfold recursiveAugmentedKernel
      infer_instance
  | succ n ih =>
      let : IsMarkovKernel (recursiveAugmentedKernel n) := ih
      unfold recursiveAugmentedKernel
      exact Kernel.IsMarkovKernel.map _
        (finHeadTailEquiv ℝ n).symm.measurable

/-- Binding is invariant under simultaneous measurable-equivalence changes
of latent and observation coordinates. -/
theorem bind_congr_measurableEquiv
    {α α' β β' : Type*} [MeasurableSpace α] [MeasurableSpace α']
    [MeasurableSpace β] [MeasurableSpace β']
    (κ : Kernel α β) (μ : Measure α)
    (eα : α' ≃ᵐ α) (eβ : β' ≃ᵐ β) :
    ((κ.comap eα eα.measurable).map eβ.symm) ∘ₘ
        (μ.map eα.symm) =
      (κ ∘ₘ μ).map eβ.symm := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _),
    Measure.map_apply eβ.symm.measurable hs,
    Measure.bind_apply (hs.preimage eβ.symm.measurable) κ.aemeasurable]
  rw [lintegral_map' (by
      exact (Kernel.measurable_coe _ hs).aemeasurable)
    eα.symm.measurable.aemeasurable]
  apply lintegral_congr
  intro a
  rw [Kernel.map_apply' _ eβ.symm.measurable _ hs,
    Kernel.comap_apply]
  simp

/-- Recursive latent product aligned definitionally with
`recursiveAugmentedKernel`. -/
noncomputable def recursiveAugmentedLatent :
    (n : ℕ) → (Fin n → Measure AugmentedTwoPointParams) →
      Measure (Fin n → AugmentedTwoPointParams)
  | 0 => fun _ => Measure.dirac (fun i => Fin.elim0 i)
  | Nat.succ n => fun latent =>
      ((latent 0).prod
        (recursiveAugmentedLatent n (fun i => latent (Fin.succ i)))).map
          (finHeadTailEquiv AugmentedTwoPointParams n).symm

/-- The analogous head/tail recursive product of observation marginals. -/
noncomputable def recursiveRealProduct :
    (n : ℕ) → (Fin n → Measure ℝ) → Measure (Fin n → ℝ)
  | 0 => fun _ => Measure.dirac (fun i => Fin.elim0 i)
  | Nat.succ n => fun μ =>
      ((μ 0).prod (recursiveRealProduct n (fun i => μ (Fin.succ i)))).map
        (finHeadTailEquiv ℝ n).symm

instance recursiveAugmentedLatent_sfinite
    (n : ℕ) (latent : Fin n → Measure AugmentedTwoPointParams)
    [∀ i, SFinite (latent i)] :
    SFinite (recursiveAugmentedLatent n latent) := by
  induction n with
  | zero =>
      unfold recursiveAugmentedLatent
      infer_instance
  | succ n ih =>
      let : ∀ i : Fin n, SFinite (latent (Fin.succ i)) :=
        fun i => inferInstance
      have htail : SFinite
          (recursiveAugmentedLatent n (fun i => latent (Fin.succ i))) :=
        ih (fun i => latent (Fin.succ i))
      let := htail
      unfold recursiveAugmentedLatent
      infer_instance

/-- Finite recursive product-of-binds theorem.  This is the full induction:
the binary Fubini step handles head/tail and the measurable-equivalence
conjugation returns to `Fin (n+1)` coordinates. -/
theorem recursiveAugmentedKernel_comp_latent
    (n : ℕ) (latent : Fin n → Measure AugmentedTwoPointParams)
    [∀ i, SFinite (latent i)] :
    recursiveAugmentedKernel n ∘ₘ
        recursiveAugmentedLatent n latent =
      recursiveRealProduct n
        (fun i => augmentedTwoPointKernel ∘ₘ latent i) := by
  induction n with
  | zero =>
      unfold recursiveAugmentedKernel recursiveAugmentedLatent
        recursiveRealProduct
      simp
  | succ n ih =>
      let : ∀ i : Fin n, SFinite (latent (Fin.succ i)) :=
        fun i => inferInstance
      let : IsMarkovKernel (recursiveAugmentedKernel n) :=
        recursiveAugmentedKernel_markov n
      unfold recursiveAugmentedKernel recursiveAugmentedLatent
        recursiveRealProduct
      rw [bind_congr_measurableEquiv]
      rw [parallelComp_comp_prod_measure]
      rw [ih (fun i => latent (Fin.succ i))]

/-- Zero-dimensional recursive product. -/
theorem recursiveRealProduct_zero (μ : Fin 0 → Measure ℝ) :
    recursiveRealProduct 0 μ =
      Measure.dirac (fun i : Fin 0 => Fin.elim0 i) := rfl

/-- The head/tail recursive product is the standard finite `Measure.pi`. -/
theorem recursiveRealProduct_eq_pi
    (n : ℕ) (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] :
    recursiveRealProduct n μ = Measure.pi μ := by
  induction n with
  | zero =>
      rw [recursiveRealProduct_zero, Measure.pi_of_empty]
      exact congrArg Measure.dirac (Subsingleton.elim _ _)
  | succ n ih =>
      let : ∀ i : Fin n, IsProbabilityMeasure (μ (Fin.succ i)) :=
        fun i => inferInstance
      change
        ((μ 0).prod
          (recursiveRealProduct n (fun i => μ (Fin.succ i)))).map
            (finHeadTailEquiv ℝ n).symm = Measure.pi μ
      rw [ih (fun i => μ (Fin.succ i))]
      have hmp := MeasureTheory.measurePreserving_piFinSuccAbove
        (fun i : Fin (n + 1) => μ i) 0
      exact hmp.symm.map_eq

/-- Complete finite mixture theorem: the original independent product law is
the mixture of the recursively constructed conditionally independent
augmented two-point kernel over the recursively constructed latent product. -/
theorem pi_eq_recursiveAugmented_mixture
    (n : ℕ) (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, Integrable (fun x : ℝ ↦ x) (μ i))
    (hmean : ∀ i, (∫ x : ℝ, x ∂μ i) = 1)
    (hM : ∀ i, 0 < belowMoment (μ i)) :
    recursiveAugmentedKernel n ∘ₘ
        recursiveAugmentedLatent n
          (fun i => augmentedLatentMeasure (μ i) (belowMoment (μ i))) =
      Measure.pi μ := by
  let hlatent : ∀ i, IsProbabilityMeasure
      (augmentedLatentMeasure (μ i) (belowMoment (μ i))) :=
    fun i => augmentedLatentMeasure_isProbability
      (hμ i) (hmean i) (hM i)
  rw [recursiveAugmentedKernel_comp_latent]
  have hcoord :
      (fun i => augmentedTwoPointKernel ∘ₘ
          augmentedLatentMeasure (μ i) (belowMoment (μ i))) = μ := by
    funext i
    rw [augmentedTwoPointKernel_comp_latent,
      fullKernelMixture_eq (hμ i) (hmean i) (hM i)]
  rw [hcoord, recursiveRealProduct_eq_pi]

end RecursiveFiniteKernel

end

end Feige
