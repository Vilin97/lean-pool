/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Kernel.OnePointKilled
import LeanPool.MarkovProcess.MarkovProcess.Killed.GluingTransfer

/-!
# Comparing two local resolvents through the part-process identity

Two positive `C₀`-contractive resolvents on nested locally compact state spaces are compared here
through the process of the larger one.  The data are an open embedding `iota : X₀ → X₁`, the
regularity data (`PositiveC0ContractiveResolvent.OnePointRegular`) which the continuous-path
process of the compactification of `X₁` is formed from, and the part-process identity: the
resolvent of the process of `X₁` killed at the exit from the image of `X₀` is the resolvent
supplied on `X₀`.

The conclusion (`PositiveC0ContractiveResolvent.kernelResolvent_le_of_partProcess`) is that the
kernel resolvent of the smaller space is dominated by the kernel resolvent of the larger one: a
path leaves the smaller domain no later, so it accumulates less.  The identity is supplied for
nonnegative continuous observables vanishing at infinity, which is the form an analytic
construction produces, and is upgraded to all nonnegative measurable observables through the
potential measures.

The regularity data are an explicit hypothesis: positivity, contractivity and the resolvent
identity do not by themselves give the compactified semigroup a continuous-path process.
-/

noncomputable section PortComputability

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty

section

namespace MarkovProcess.PositiveC0ContractiveResolvent

open MarkovProcess.SubMarkovKernelSemigroup

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

/-- Regularity data for the compactified process of a positive `C₀`-contractive resolvent: a
positive `1`-Lipschitz exhaustion function with compact positive superlevel sets, together with
the Kolmogorov regularity of the compactified kernel semigroup in the metric which that function
determines.  The continuous-path process of the compactified semigroup is formed from exactly
these data. -/
structure OnePointRegular (R : PositiveC0ContractiveResolvent X) where
  /-- The exhaustion function on the live space. -/
  rho : X → ℝ
  /-- The exhaustion function is continuous. -/
  continuous_rho : Continuous rho
  /-- The exhaustion function is positive. -/
  rho_pos : ∀ x, 0 < rho x
  /-- The exhaustion function is `1`-Lipschitz. -/
  lipschitz_rho : LipschitzWith 1 rho
  /-- The positive superlevel sets of the exhaustion function are compact. -/
  isCompact_superlevel : ∀ epsilon > 0, IsCompact {x | epsilon ≤ rho x}
  /-- The compactified kernel semigroup is Kolmogorov regular in the exhaustion metric. -/
  kolmogorovRegular :
    letI := OnePoint.exhaustionMetricSpace rho continuous_rho rho_pos lipschitz_rho
      isCompact_superlevel
    letI : CompleteSpace (OnePoint X) :=
      completeSpace_of_isComplete_univ isCompact_univ.isComplete
    R.onePointKernelSemigroup.KolmogorovRegular R.isConservative_onePointKernelSemigroup

namespace OnePointRegular

variable {R : PositiveC0ContractiveResolvent X}

/-- The metric on the compactification determined by the exhaustion function. -/
@[implicit_reducible]
noncomputable def metricSpace (h : R.OnePointRegular) : MetricSpace (OnePoint X) :=
  OnePoint.exhaustionMetricSpace h.rho h.continuous_rho h.rho_pos h.lipschitz_rho
    h.isCompact_superlevel

/-- Typeclass-search cache: lets `letI := h.metricSpace` discharge an ambient
`CompactSpace (OnePoint X)` obligation without re-deriving compactness at each call site (the
exhaustion metric's topology coincides with the canonical one-point topology, which is always
compact). -/
private instance instCompactSpaceMetricSpace (h : R.OnePointRegular) :
    @CompactSpace (OnePoint X)
        h.metricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
  unfold OnePointRegular.metricSpace
  rw [OnePoint.exhaustionMetricSpace_toTopologicalSpace]
  infer_instance

/-- Typeclass-search cache, in the same spirit as `instCompactSpaceMetricSpace`: lets
`letI := h.metricSpace` discharge an ambient `BorelSpace (OnePoint X)` obligation. -/
private instance instBorelSpaceMetricSpace (h : R.OnePointRegular) :
    @BorelSpace (OnePoint X) h.metricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      OnePoint.instMeasurableSpace := by
  unfold OnePointRegular.metricSpace
  rw [OnePoint.exhaustionMetricSpace_toTopologicalSpace]
  exact OnePoint.instBorelSpace

/-- Typeclass-search cache, in the same spirit as `instCompactSpaceMetricSpace`: lets
`letI := h.metricSpace` discharge an ambient `SecondCountableTopology (OnePoint X)`
obligation. -/
private instance instSecondCountableTopologyMetricSpace (h : R.OnePointRegular) :
    @SecondCountableTopology (OnePoint X)
      h.metricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
  unfold OnePointRegular.metricSpace
  rw [OnePoint.exhaustionMetricSpace_toTopologicalSpace]
  exact OnePoint.instSecondCountableTopology

/-- The compactification is complete in the exhaustion metric. -/
theorem completeSpace (h : R.OnePointRegular) :
    letI := h.metricSpace
    CompleteSpace (OnePoint X) :=
  letI := h.metricSpace
  completeSpace_of_isComplete_univ isCompact_univ.isComplete

/-- **The killed resolvent of the compactified process is the kernel resolvent.**  Killing the
process of the compactification at the exit from the live space returns the sub-Markov semigroup
originally represented by the resolvent. -/
theorem killedResolvent_live_eq_kernelResolvent (h : R.OnePointRegular) (lam : ℝ)
    {f : X → ℝ≥0∞} (hf : Measurable f) (x : X) :
    letI := h.metricSpace
    letI := h.completeSpace
    IsConservative.killedResolvent R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup
        (Set.range ((↑) : X → OnePoint X)) OnePoint.isOpen_range_coe lam
        (onePointLiveExtension f) (x : OnePoint X) =
      R.kernelSemigroup.kernelResolvent lam f x :=
  R.killedResolvent_onePointLive_eq_kernelResolvent h.rho h.continuous_rho h.rho_pos
    h.lipschitz_rho h.isCompact_superlevel h.kolmogorovRegular lam hf x

end OnePointRegular

/-- For a nonnegative observable vanishing at infinity, the kernel resolvent of the represented
semigroup is the analytic resolvent originally supplied. -/
theorem kernelResolvent_ofReal_eq_operator (R : PositiveC0ContractiveResolvent X)
    (mu : Semigroup.PositiveShift) (f : C₀(X, ℝ)) (hf0 : ∀ y, 0 ≤ f y) (x : X) :
    R.kernelSemigroup.kernelResolvent (mu : ℝ) (fun y ↦ ENNReal.ofReal (f y)) x =
      ENNReal.ofReal (R.toContractiveResolvent.operator mu f x) := by
  rw [R.isFellerKernelSemigroup_kernelSemigroup.kernelResolvent_ofReal_eq_resolvent mu f hf0 x,
    R.resolvent_c0Semigroup_kernelSemigroup]

section Embedding

variable {X₀ X₁ : Type*}

/-- The embedding of a smaller live space into the compactification of a larger one. -/
def compactifiedEmbedding (iota : X₀ → X₁) (y : X₀) : OnePoint X₁ := ((iota y : X₁) : OnePoint X₁)

/-- The embedding of a smaller live space into the compactification, unfolded. -/
@[simp] theorem compactifiedEmbedding_apply (iota : X₀ → X₁) (y : X₀) :
    compactifiedEmbedding iota y = ((iota y : X₁) : OnePoint X₁) := rfl

/-- The embedding of a smaller live space into the compactification of a larger one is
injective. -/
theorem injective_compactifiedEmbedding {iota : X₀ → X₁} (hiota : Function.Injective iota) :
    Function.Injective (compactifiedEmbedding iota) :=
  OnePoint.coe_injective.comp hiota

/-- The image of the smaller live space is contained in the live part of the compactification. -/
theorem range_compactifiedEmbedding_subset (iota : X₀ → X₁) :
    Set.range (compactifiedEmbedding iota) ⊆ Set.range ((↑) : X₁ → OnePoint X₁) := by
  rintro _ ⟨y, rfl⟩
  exact ⟨iota y, rfl⟩

/-- An observable of the smaller space, extended by zero off its image in the compactification,
is dominated by the observable of the larger space extended by zero at infinity. -/
theorem extend_compactifiedEmbedding_le (iota : X₀ → X₁) (hiota : Function.Injective iota)
    (g : X₁ → ℝ≥0∞) :
    Function.extend (compactifiedEmbedding iota) (fun z ↦ g (iota z)) 0 ≤
      onePointLiveExtension g := by
  intro w
  by_cases hw : w ∈ Set.range (compactifiedEmbedding iota)
  · obtain ⟨z, rfl⟩ := hw
    rw [(injective_compactifiedEmbedding hiota).extend_apply]
    exact le_of_eq rfl
  · rw [Function.extend_apply' _ _ _ fun hmem ↦ hw hmem]
    exact zero_le

end Embedding

section EmbeddingTopology

variable {X₀ X₁ : Type*} [TopologicalSpace X₀] [TopologicalSpace X₁]

/-- The embedding of a smaller live space into the compactification of a larger one is an open
embedding. -/
theorem isOpenEmbedding_compactifiedEmbedding {iota : X₀ → X₁} (hiota : IsOpenEmbedding iota) :
    IsOpenEmbedding (compactifiedEmbedding iota) :=
  OnePoint.isOpenEmbedding_coe.comp hiota

/-- The image of a smaller live space in the compactification of a larger one is open. -/
theorem isOpen_range_compactifiedEmbedding {iota : X₀ → X₁} (hiota : IsOpenEmbedding iota) :
    IsOpen (Set.range (compactifiedEmbedding iota)) :=
  (isOpenEmbedding_compactifiedEmbedding hiota).isOpen_range

end EmbeddingTopology

section Comparison

variable {X₀ X₁ : Type*}
  [MetricSpace X₀] [LocallyCompactSpace X₀] [SecondCountableTopology X₀]
  [MeasurableSpace X₀] [BorelSpace X₀]
  [MetricSpace X₁] [LocallyCompactSpace X₁] [SecondCountableTopology X₁]
  [MeasurableSpace X₁] [BorelSpace X₁]

/-- **The part-process identity.**  The resolvent of the compactified process of `R₁`, killed at
the exit from the image of the smaller live space, is the analytic resolvent supplied on that
space, tested on nonnegative observables vanishing at infinity and extended by zero off the
image. -/
def IsPartProcess (R₀ : PositiveC0ContractiveResolvent X₀)
    (R₁ : PositiveC0ContractiveResolvent X₁) (h₁ : R₁.OnePointRegular)
    {iota : X₀ → X₁} (hiota : IsOpenEmbedding iota) : Prop :=
  ∀ (mu : Semigroup.PositiveShift) (f : C₀(X₀, ℝ)), (∀ z, 0 ≤ f z) → ∀ y : X₀,
    letI := h₁.metricSpace
    letI := h₁.completeSpace
    IsConservative.killedResolvent R₁.onePointKernelSemigroup
        R₁.isConservative_onePointKernelSemigroup
        (Set.range (compactifiedEmbedding iota))
        (isOpen_range_compactifiedEmbedding hiota) (mu : ℝ)
        (Function.extend (compactifiedEmbedding iota) (fun z ↦ ENNReal.ofReal (f z)) 0)
        (compactifiedEmbedding iota y) =
      ENNReal.ofReal (R₀.toContractiveResolvent.operator mu f y)

/-- **Domination of the local kernel resolvents.**  If the resolvent of the compactified process
of `R₁` killed at the exit from the image of `X₀` is the resolvent `R₀`, then the kernel resolvent
of `R₀` is dominated by the kernel resolvent of `R₁`: leaving the smaller domain kills the path
earlier, so it accumulates less. -/
theorem kernelResolvent_le_of_partProcess (R₀ : PositiveC0ContractiveResolvent X₀)
    (R₁ : PositiveC0ContractiveResolvent X₁) (h₁ : R₁.OnePointRegular)
    {iota : X₀ → X₁} (hiota : IsOpenEmbedding iota)
    (hcompat : IsPartProcess R₀ R₁ h₁ hiota)
    {lam : ℝ} (hlam : 0 < lam) {g : X₁ → ℝ≥0∞} (hg : Measurable g) (y : X₀) :
    R₀.kernelSemigroup.kernelResolvent lam (fun z ↦ g (iota z)) y ≤
      R₁.kernelSemigroup.kernelResolvent lam g (iota y) := by
  let := h₁.metricSpace
  let := h₁.completeSpace
  have hj : IsOpenEmbedding (compactifiedEmbedding iota) :=
    isOpenEmbedding_compactifiedEmbedding hiota
  have hjm : MeasurableEmbedding (compactifiedEmbedding iota) := hj.measurableEmbedding
  have hjopen : IsOpen (Set.range (compactifiedEmbedding iota)) :=
    isOpen_range_compactifiedEmbedding hiota
  have hgi : Measurable fun z : X₀ ↦ g (iota z) := hg.comp hiota.continuous.measurable
  have := IsConservative.isFiniteMeasure_killedPotential R₁.onePointKernelSemigroup
    R₁.isConservative_onePointKernelSemigroup (Set.range (compactifiedEmbedding iota))
    hjopen hlam (compactifiedEmbedding iota y)
  have := R₀.kernelSemigroup.isFiniteMeasure_resolventPotential hlam y
  have hc0 : ∀ f : C₀(X₀, ℝ), (∀ z, 0 ≤ f z) →
      ∫⁻ w, Function.extend (compactifiedEmbedding iota)
          (fun z ↦ ENNReal.ofReal (f z)) 0 w
        ∂IsConservative.killedPotential R₁.onePointKernelSemigroup
          R₁.isConservative_onePointKernelSemigroup (Set.range (compactifiedEmbedding iota))
          hjopen lam (compactifiedEmbedding iota y) =
      ∫⁻ z, ENNReal.ofReal (f z) ∂R₀.kernelSemigroup.resolventPotential lam y := by
    intro f hf0
    have hfmeas : Measurable fun z : X₀ ↦ ENNReal.ofReal (f z) :=
      ENNReal.measurable_ofReal.comp f.continuous.measurable
    have hextmeas : Measurable (Function.extend (compactifiedEmbedding iota)
        (fun z ↦ ENNReal.ofReal (f z)) (0 : OnePoint X₁ → ℝ≥0∞)) :=
      hjm.measurable_extend hfmeas measurable_const
    rw [IsConservative.lintegral_killedPotential R₁.onePointKernelSemigroup
        R₁.isConservative_onePointKernelSemigroup (Set.range (compactifiedEmbedding iota))
        hjopen lam hextmeas (compactifiedEmbedding iota y),
      R₀.kernelSemigroup.lintegral_resolventPotential lam hfmeas y,
      hcompat ⟨lam, hlam⟩ f hf0 y,
      ← R₀.kernelResolvent_ofReal_eq_operator ⟨lam, hlam⟩ f hf0 y]
  have hgextmeas : Measurable (Function.extend (compactifiedEmbedding iota)
      (fun z ↦ g (iota z)) (0 : OnePoint X₁ → ℝ≥0∞)) :=
    hjm.measurable_extend hgi measurable_const
  have hstep : IsConservative.killedResolvent R₁.onePointKernelSemigroup
      R₁.isConservative_onePointKernelSemigroup (Set.range (compactifiedEmbedding iota))
      hjopen lam
      (Function.extend (compactifiedEmbedding iota) (fun z ↦ g (iota z)) 0)
      (compactifiedEmbedding iota y) =
        R₀.kernelSemigroup.kernelResolvent lam (fun z ↦ g (iota z)) y := by
    have h := lintegral_extend_eq_of_forall_zeroAtInfty hjm
      (IsConservative.killedPotential R₁.onePointKernelSemigroup
        R₁.isConservative_onePointKernelSemigroup (Set.range (compactifiedEmbedding iota))
        hjopen lam (compactifiedEmbedding iota y))
      (R₀.kernelSemigroup.resolventPotential lam y) hc0 hgi
    rwa [IsConservative.lintegral_killedPotential R₁.onePointKernelSemigroup
        R₁.isConservative_onePointKernelSemigroup (Set.range (compactifiedEmbedding iota))
        hjopen lam hgextmeas (compactifiedEmbedding iota y),
      R₀.kernelSemigroup.lintegral_resolventPotential lam hgi y] at h
  rw [← hstep, ← h₁.killedResolvent_live_eq_kernelResolvent lam hg (iota y)]
  exact IsConservative.killedResolvent_mono R₁.onePointKernelSemigroup
    R₁.isConservative_onePointKernelSemigroup (Set.range (compactifiedEmbedding iota))
    hjopen OnePoint.isOpen_range_coe (range_compactifiedEmbedding_subset iota) lam
    (extend_compactifiedEmbedding_le iota hiota.injective g) (compactifiedEmbedding iota y)

end Comparison

end MarkovProcess.PositiveC0ContractiveResolvent

end

end PortComputability
