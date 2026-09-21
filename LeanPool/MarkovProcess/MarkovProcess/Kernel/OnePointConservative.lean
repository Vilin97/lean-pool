/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Kernel.ConservativeResolvent
import LeanPool.MarkovProcess.MarkovProcess.Kernel.OnePointKilled
import LeanPool.MarkovProcess.MarkovProcess.Killed.GluingLocal

/-!
# A conservative resolvent keeps the compactified process in the live space

The Laplace transform of the finite exit time from the live part of the compactification is one
minus the shift times the kernel resolvent of the constant observable one
(`Kernel/OnePointKilled.lean`).  When that product is one, the transform vanishes, so the exit
time is almost surely infinite: the compactified process started at a live point almost surely
never reaches the added point
(`PositiveC0ContractiveResolvent.OnePointRegular.ae_exitTime_eq_top`).  No kernel into the
continuous paths of the live space is produced here; the statement is about the law of the
compactified process.

The regularity data of the compactification are an explicit hypothesis, as everywhere the
continuous-path process is formed.
-/

noncomputable section PortComputability

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty

section

namespace MarkovProcess.PositiveC0ContractiveResolvent

open MarkovProcess.SubMarkovKernelSemigroup

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] {R : PositiveC0ContractiveResolvent X}

/-- **A conservative resolvent leaves no escape.**  If at one positive shift the shift times the
kernel resolvent of the constant observable one is one at a live starting point, then the
compactified process started there almost surely never leaves the live space. -/
theorem OnePointRegular.ae_exitTime_eq_top (h : R.OnePointRegular) {lam : ℝ} (hlam : 0 < lam)
    (x : X) (hone : ENNReal.ofReal lam *
      R.kernelSemigroup.kernelResolvent lam (fun _ : X ↦ 1) x = 1) :
    letI := h.metricSpace
    letI := h.completeSpace
    ∀ᵐ omega ∂IsConservative.continuousProcess R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup (x : OnePoint X),
      ContinuousPath.exitTime (Set.range ((↑) : X → OnePoint X)) omega = ⊤ := by
  let := h.metricSpace
  let := h.completeSpace
  have hlaplace := R.lintegral_exp_neg_onePoint_exitTime h.rho h.continuous_rho h.rho_pos
    h.lipschitz_rho h.isCompact_superlevel h.kolmogorovRegular lam hlam x
  rw [hone, tsub_self] at hlaplace
  have hmeasTime : Measurable
      (ContinuousPath.exitTime (Set.range ((↑) : X → OnePoint X)) :
        ContinuousPath (OnePoint X) → ℝ≥0∞) :=
    ContinuousPath.measurable_exitTime _ OnePoint.isOpen_range_coe
  have hmeasSet : MeasurableSet
      {omega : ContinuousPath (OnePoint X) |
        ContinuousPath.exitTime (Set.range ((↑) : X → OnePoint X)) omega < ⊤} :=
    measurableSet_lt hmeasTime measurable_const
  have hmeas : Measurable
      (({omega : ContinuousPath (OnePoint X) |
          ContinuousPath.exitTime (Set.range ((↑) : X → OnePoint X)) omega < ⊤}).indicator
        (fun omega ↦ ENNReal.ofReal (Real.exp (-lam *
          (ContinuousPath.exitTime (Set.range ((↑) : X → OnePoint X)) omega).toReal)))) :=
    Measurable.indicator
      (ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
        ((measurable_const.mul hmeasTime.ennreal_toReal))))
      hmeasSet
  have hzero := (lintegral_eq_zero_iff hmeas).mp hlaplace
  filter_upwards [hzero] with omega homega
  by_contra hlt
  have hfinite : omega ∈ {omega : ContinuousPath (OnePoint X) |
      ContinuousPath.exitTime (Set.range ((↑) : X → OnePoint X)) omega < ⊤} :=
    lt_top_iff_ne_top.mpr hlt
  rw [Set.indicator_of_mem hfinite] at homega
  exact absurd homega (by
    simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero, not_le]
    exact Real.exp_pos _)

end MarkovProcess.PositiveC0ContractiveResolvent

end

end PortComputability
