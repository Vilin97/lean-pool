/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Feller.Semigroup
import LeanPool.MarkovProcess.MarkovProcess.Kernel.PositiveC0Resolvent
import LeanPool.MarkovProcess.MarkovProcess.Kernel.Resolvent
import LeanPool.MarkovProcess.MarkovProcess.Semigroup.Resolvent
import LeanPool.MarkovProcess.MarkovProcess.Semigroup.ResolventGeneration

/-!
# The resolvent of a Feller kernel semigroup

The resolvent of the `C₀` semigroup of a Feller kernel semigroup `P`, evaluated at a point, is
the Laplace transform of the transition integrals,

  `R_μ f (x) = ∫₀^∞ e^{-μ t} (∫ f d(P t x)) dt`   (`IsFellerKernelSemigroup.resolvent_apply_apply`),

and the generator domain of the `C₀` semigroup is the range of this resolvent
(`IsFellerKernelSemigroup.mem_generatorDomain_iff_exists_resolvent`), the kernel-side reading of
`Semigroup/Resolvent.lean`.  The shared bounded evaluation functional `c0EvalCLM` commutes with
Bochner integrals in `C₀(α, ℝ)`.  For the Feller kernel
semigroup represented by a positive contractive resolvent `R` (`Kernel/PositiveC0Resolvent.lean`),
the resolvent of its `C₀` semigroup is `R` itself
(`PositiveC0ContractiveResolvent.resolvent_c0Semigroup_kernelSemigroup`).

Conversely, the kernel semigroup represented by that resolvent is the original one
(`IsFellerKernelSemigroup.kernelSemigroup_positiveC0ContractiveResolvent`).

Main results: `IsFellerKernelSemigroup.resolvent_apply_apply`,
`IsFellerKernelSemigroup.positiveC0ContractiveResolvent`,
`IsFellerKernelSemigroup.kernelResolvent_ofReal_eq_resolvent`,
`IsFellerKernelSemigroup.mem_generatorDomain_iff_exists_resolvent`,
`PositiveC0ContractiveResolvent.resolvent_c0Semigroup_kernelSemigroup`.

The bridge to `SubMarkovKernelSemigroup.kernelResolvent` is pointwise on nonnegative observables;
no kernel-valued resolvent is constructed.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped NNReal ZeroAtInfty

namespace MarkovProcess

namespace SubMarkovKernelSemigroup

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  [LocallyCompactSpace α] [T2Space α]
variable {P : SubMarkovKernelSemigroup α} (hP : P.IsFellerKernelSemigroup)

/-- **The resolvent of the `C₀` semigroup, evaluated at a point**: the Laplace transform of the
transition integrals. -/
theorem IsFellerKernelSemigroup.resolvent_apply_apply (μ : Semigroup.PositiveShift)
    (f : C₀(α, ℝ)) (x : α) :
    hP.c0Semigroup.resolvent μ f x =
      ∫ t in Ioi (0 : ℝ), Real.exp (-(μ : ℝ) * t) * kernelIntegral (P (Real.toNNReal t)) f x := by
  rw [← c0EvalCLM_apply x (hP.c0Semigroup.resolvent μ f),
    Semigroup.StronglyContinuousContractionSemigroup.resolvent_apply,
    ← ContinuousLinearMap.integral_comp_comm _
      (hP.c0Semigroup.integrableOn_laplaceIntegrand μ.2 f)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
  simp only [Semigroup.StronglyContinuousContractionSemigroup.laplaceIntegrand_apply, map_smul,
    c0EvalCLM_apply, smul_eq_mul, IsFellerKernelSemigroup.c0Semigroup_apply_apply]

/-- The resolvent of a Feller kernel semigroup, packaged as a positive contractive resolvent on
`C₀`. Positivity follows directly from the nonnegative Laplace-transform integrand. -/
noncomputable def IsFellerKernelSemigroup.positiveC0ContractiveResolvent :
    PositiveC0ContractiveResolvent α where
  toContractiveResolvent := hP.c0Semigroup.toContractiveResolvent
  isPositive := fun μ f hf x ↦ by
    rw [Semigroup.StronglyContinuousContractionSemigroup.toContractiveResolvent_operator,
      hP.resolvent_apply_apply]
    exact integral_nonneg fun t ↦ mul_nonneg (Real.exp_pos _).le (integral_nonneg hf)

/-- Generating a semigroup from the positive resolvent of a Feller semigroup recovers its
original `C₀` semigroup. -/
theorem IsFellerKernelSemigroup.generatedSemigroup_positiveC0ContractiveResolvent :
    hP.positiveC0ContractiveResolvent.toContractiveResolvent.generatedSemigroup =
      hP.c0Semigroup :=
  hP.c0Semigroup.generatedSemigroup_toContractiveResolvent

/-- The real kernel resolvent of a `C₀` observable is the pointwise resolvent of the associated
`C₀` semigroup. -/
theorem IsFellerKernelSemigroup.kernelResolventReal_eq_resolvent
    (hP : P.IsFellerKernelSemigroup) (μ : Semigroup.PositiveShift)
    (f : C₀(α, ℝ)) (x : α) :
    P.kernelResolventReal (μ : ℝ) (fun y ↦ f y) x =
      hP.c0Semigroup.resolvent μ f x := by
  exact (hP.resolvent_apply_apply μ f x).symm

/-- The extended-real kernel resolvent of a nonnegative `C₀` observable agrees with the
pointwise `C₀`-semigroup resolvent after applying `ENNReal.ofReal`. -/
theorem IsFellerKernelSemigroup.kernelResolvent_ofReal_eq_resolvent
    (hP : P.IsFellerKernelSemigroup) (μ : Semigroup.PositiveShift)
    (f : C₀(α, ℝ)) (hf0 : ∀ y, 0 ≤ f y) (x : α) :
    P.kernelResolvent (μ : ℝ) (fun y ↦ ENNReal.ofReal (f y)) x =
      ENNReal.ofReal (hP.c0Semigroup.resolvent μ f x) := by
  have houter : IntegrableOn (fun t : ℝ ↦
      Real.exp (-(μ : ℝ) * t) * kernelIntegral (P (Real.toNNReal t)) f x) (Ioi 0) := by
    have hint := (c0EvalCLM x).integrable_comp
      (hP.c0Semigroup.integrableOn_laplaceIntegrand μ.2 f)
    simpa only [Function.comp_apply,
      Semigroup.StronglyContinuousContractionSemigroup.laplaceIntegrand_apply,
      map_smul, c0EvalCLM_apply, smul_eq_mul,
      IsFellerKernelSemigroup.c0Semigroup_apply_apply] using! hint
  rw [hP.resolvent_apply_apply μ f x,
    ofReal_integral_eq_lintegral_ofReal houter
      (Eventually.of_forall fun t ↦ mul_nonneg (Real.exp_pos _).le
        (integral_nonneg fun y ↦ hf0 y))]
  unfold SubMarkovKernelSemigroup.kernelResolvent
  apply lintegral_congr
  intro t
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1
  let : IsFiniteKernel (P (Real.toNNReal t)) :=
    (P.isSubMarkovKernel (Real.toNNReal t)).isFiniteKernel
  have hfint : Integrable (fun y ↦ f y) (P (Real.toNNReal t) x) :=
    f.toBCF.integrable (P (Real.toNNReal t) x)
  exact (ofReal_integral_eq_lintegral_ofReal hfint (Eventually.of_forall hf0)).symm

/-- **The kernel semigroup represented by the resolvent of a Feller kernel semigroup is that
semigroup.**  Both transition laws are finite Borel measures with the same integral on every
compactly supported continuous observable. -/
theorem IsFellerKernelSemigroup.kernelSemigroup_positiveC0ContractiveResolvent
    [SecondCountableTopology α] (hP : P.IsFellerKernelSemigroup) :
    hP.positiveC0ContractiveResolvent.kernelSemigroup = P := by
  refine SubMarkovKernelSemigroup.ext fun t ↦ ?_
  refine Kernel.ext fun x ↦ ?_
  have : IsFiniteMeasure (P t x) :=
    ⟨lt_of_le_of_lt (P.measure_univ_le_one t x) ENNReal.one_lt_top⟩
  have : IsFiniteMeasure (hP.positiveC0ContractiveResolvent.kernelSemigroup t x) :=
    ⟨lt_of_le_of_lt
      (hP.positiveC0ContractiveResolvent.kernelSemigroup.measure_univ_le_one t x)
      ENNReal.one_lt_top⟩
  refine Measure.ext_of_integral_eq_on_compactlySupported fun f ↦ ?_
  set g : C₀(α, ℝ) := PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f with hg
  have hgf : ∀ y, g y = f y := fun y ↦
    PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap_apply f y
  have hleft : ∫ y, f y ∂hP.positiveC0ContractiveResolvent.kernelSemigroup t x =
      ∫ y, g y ∂hP.positiveC0ContractiveResolvent.kernelSemigroup t x := by
    simp only [hgf]
  have hright : ∫ y, f y ∂P t x = ∫ y, g y ∂P t x := by
    simp only [hgf]
  rw [hleft, hright, hP.positiveC0ContractiveResolvent.integral_kernelSemigroup t g x,
    hP.generatedSemigroup_positiveC0ContractiveResolvent, hP.c0Semigroup_apply_apply t g x]
  rfl

/-- **The generator domain of the `C₀` semigroup is the range of its resolvent**, at every
positive shift. -/
theorem IsFellerKernelSemigroup.mem_generatorDomain_iff_exists_resolvent
    (μ : Semigroup.PositiveShift) (f : C₀(α, ℝ)) :
    f ∈ hP.c0Semigroup.generatorDomain ↔ ∃ g, hP.c0Semigroup.resolvent μ g = f := by
  rw [← SetLike.mem_coe, hP.c0Semigroup.generatorDomain_eq_range_resolvent μ]
  exact Set.mem_range

end SubMarkovKernelSemigroup

namespace PositiveC0ContractiveResolvent

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  (R : PositiveC0ContractiveResolvent X)

/-- **The resolvent of the represented process is the given resolvent.** -/
theorem resolvent_c0Semigroup_kernelSemigroup (μ : Semigroup.PositiveShift) :
    R.isFellerKernelSemigroup_kernelSemigroup.c0Semigroup.resolvent μ =
      R.toContractiveResolvent.operator μ := by
  rw [R.c0Semigroup_kernelSemigroup, Semigroup.ContractiveResolvent.resolvent_generatedSemigroup]

end PositiveC0ContractiveResolvent

end MarkovProcess
