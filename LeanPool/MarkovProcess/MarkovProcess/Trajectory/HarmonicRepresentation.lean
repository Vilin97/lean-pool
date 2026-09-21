/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.DynkinStopping
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.ExpectedExitTime

/-!
# Harmonic and Poisson representations, and the localized Dynkin formula

Consequences of Dynkin's formula at the exit time of an open set `U` truncated at a horizon `K`
(`Trajectory/DynkinStopping.lean`), for the continuous-path process `Q` of a conservative Feller
semigroup and `f` in the generator domain of its `C₀` semigroup, with generator `L f`:

* `integral_eval_exitTimeTrunc_eq_of_generator_eq_zero` (**harmonic representation**): if
  `L f = 0` on `U`, then `E_x f(ω_{τ ∧ K}) = f x`;
* `integral_eval_exitTimeTrunc_add_eq_of_generator_eq_neg` (**Poisson representation**): if
  `L f = -g` on `U`, then `E_x f(ω_{τ ∧ K}) + E_x ∫_0^{τ ∧ K} g(ω_s) ds = f x`;
* `stopped_exitTimeTrunc_mem_closure`: from a starting point in `U`, the position at `τ ∧ K` lies
  in the closure of `U`, so a continuous function that agrees with `f` on the closure of `U`
  has the same stopped expectation; this gives the **localized Dynkin formula**
  `integral_eval_exitTimeTrunc_sub_eq_of_eqOn_closure`, which is how test functions outside `C₀`
  (agreeing with a domain element near the closure of a bounded set) enter moment identities.

The integrand of Dynkin's formula is only ever evaluated strictly before the exit time, where the
path is inside `U`; this is the observation behind all three statements.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess

namespace ContinuousPath

variable {alpha : Type*} [PseudoMetricSpace alpha]

/-- Strictly before the truncated exit time the path is inside `U`. -/
theorem mem_of_lt_exitTimeTrunc (U : Set alpha) (K : NNReal) (omega : ContinuousPath alpha)
    {s : NNReal} (hs : s < exitTimeTrunc U K omega) : omega s ∈ U := by
  apply mem_of_lt_exitTime U omega s
  have h : ((s : NNReal) : ℝ≥0∞) < ((exitTimeTrunc U K omega : NNReal) : ℝ≥0∞) :=
    ENNReal.coe_lt_coe.mpr hs
  rw [coe_exitTimeTrunc_ennreal] at h
  exact lt_of_lt_of_le h (min_le_left _ _)

/-- From a starting point in the open set `U`, the position at the truncated exit time lies in the
closure of `U`: inside `U` if the horizon comes first, on the frontier if the exit comes first. -/
theorem stopped_exitTimeTrunc_mem_closure (U : Set alpha) (hU : IsOpen U) (K : NNReal)
    (omega : ContinuousPath alpha) (h0 : omega 0 ∈ U) :
    omega (exitTimeTrunc U K omega) ∈ closure U := by
  rcases lt_or_ge (K : ℝ≥0∞) (exitTime U omega) with hK | hexit
  · have hT : exitTimeTrunc U K omega = K := by
      apply WithTop.coe_injective
      rw [coe_exitTimeTrunc, exitTimeTop_apply]
      exact min_eq_right hK.le
    rw [hT]
    exact subset_closure (mem_of_lt_exitTime U omega K hK)
  · have hfin : exitTime U omega ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hexit
    have hT : exitTimeTrunc U K omega = (exitTime U omega).toNNReal := by
      apply ENNReal.coe_injective
      rw [coe_exitTimeTrunc_ennreal, min_eq_left hexit, ENNReal.coe_toNNReal hfin]
    rw [hT]
    exact (hU.frontier_eq ▸ coordinate_exitTime_mem_frontier U hU omega h0 hfin).1

/-- The time integral of a function of the path up to the truncated exit time only sees the values
of the function on `U`: two functions agreeing on `U` give the same integral. -/
theorem integral_exitTimeTrunc_congr (U : Set alpha) (K : NNReal)
    {g₁ g₂ : alpha → ℝ} (hg : Set.EqOn g₁ g₂ U) (omega : ContinuousPath alpha) :
    ∫ s in (0 : ℝ)..(exitTimeTrunc U K omega : ℝ), g₁ (omega (Real.toNNReal s)) =
      ∫ s in (0 : ℝ)..(exitTimeTrunc U K omega : ℝ),
        g₂ (omega (Real.toNNReal s)) := by
  rw [intervalIntegral.integral_of_le NNReal.zero_le_coe,
    intervalIntegral.integral_of_le NNReal.zero_le_coe,
    ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  refine setIntegral_congr_fun measurableSet_Ioo fun s hs ↦ ?_
  refine hg (mem_of_lt_exitTimeTrunc U K omega ?_)
  rw [← NNReal.coe_lt_coe, Real.coe_toNNReal s hs.1.le]
  exact hs.2

end ContinuousPath

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

variable {P : SubMarkovKernelSemigroup alpha} (hP : P.IsConservative)

omit [LocallyCompactSpace alpha] in
/-- Under the process started at `x`, the path starts at `x` almost surely. -/
theorem IsConservative.ae_eval_zero_eq (hK : P.KolmogorovRegular hP) (x : alpha) :
    ∀ᵐ omega ∂(IsConservative.continuousProcess P hP x), omega 0 = x := by
  have hmeas : Measurable (fun omega : ContinuousPath alpha ↦ omega 0) :=
    ContinuousPath.measurable_coordinateProcess (alpha := alpha) 0
  have hmap : (IsConservative.continuousProcess P hP x).map (fun omega ↦ omega 0) =
      Measure.dirac x := by
    rw [← Kernel.map_apply _ hmeas, IsConservative.continuousProcess_map_eval_zero P hP hK,
      Kernel.id_apply]
  rw [ae_iff]
  have hset : {omega : ContinuousPath alpha | ¬ omega 0 = x} =
      (fun omega : ContinuousPath alpha ↦ omega 0) ⁻¹' ({x}ᶜ : Set alpha) := by
    ext omega
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
  rw [hset, ← Measure.map_apply hmeas (measurableSet_singleton x).compl, hmap,
    Measure.dirac_apply' _ (measurableSet_singleton x).compl,
    Set.indicator_of_notMem (by simp only [Set.mem_compl_iff, Set.mem_singleton_iff,
      not_true_eq_false, not_false_eq_true])]

/-- **Harmonic representation.**  If `L f = 0` on the open set `U`, the value of `f` at a starting
point is the expectation of `f` at the exit time truncated at any horizon. -/
theorem IsFellerKernelSemigroup.integral_eval_exitTimeTrunc_eq_of_generator_eq_zero
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (f : hFeller.c0Semigroup.generatorDomain) (U : Set alpha) (hU : IsOpen U)
    (hLf : ∀ y ∈ U, (hFeller.c0Semigroup.generator f) y = 0) (K : NNReal) (x : alpha) :
    ∫ omega, (f : C₀(alpha, ℝ)) (omega (ContinuousPath.exitTimeTrunc U K omega))
        ∂(IsConservative.continuousProcess P hP x) = (f : C₀(alpha, ℝ)) x := by
  have hdynkin := hFeller.integral_eval_stoppingTime_sub_eq_integral_integral_generator hP hK f
    (ContinuousPath.exitTimeTrunc U K) (ContinuousPath.isStoppingTime_exitTimeTrunc U hU K)
    (ContinuousPath.exitTimeTrunc_le U K) x
  have hzero : ∀ omega : ContinuousPath alpha,
      ∫ s in (0 : ℝ)..(ContinuousPath.exitTimeTrunc U K omega : ℝ),
        (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s)) = 0 := by
    intro omega
    rw [ContinuousPath.integral_exitTimeTrunc_congr U K (g₂ := fun _ ↦ 0) (fun y hy ↦ hLf y hy)
        omega,
      intervalIntegral.integral_zero]
  simp only [hzero, integral_zero] at hdynkin
  exact sub_eq_zero.mp hdynkin

/-- **Poisson representation.**  If `L f = -g` on the open set `U`, then
`f x = E_x f(ω_{τ ∧ K}) + E_x ∫_0^{τ ∧ K} g(ω_s) ds` for every horizon `K`. -/
theorem IsFellerKernelSemigroup.integral_eval_exitTimeTrunc_add_eq_of_generator_eq_neg
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (f : hFeller.c0Semigroup.generatorDomain) (U : Set alpha) (hU : IsOpen U)
    {g : alpha → ℝ} (hLf : ∀ y ∈ U, (hFeller.c0Semigroup.generator f) y = -g y) (K : NNReal)
    (x : alpha) :
    ∫ omega, (f : C₀(alpha, ℝ)) (omega (ContinuousPath.exitTimeTrunc U K omega))
        ∂(IsConservative.continuousProcess P hP x) +
      ∫ omega, (∫ s in (0 : ℝ)..(ContinuousPath.exitTimeTrunc U K omega : ℝ),
          g (omega (Real.toNNReal s))) ∂(IsConservative.continuousProcess P hP x) =
      (f : C₀(alpha, ℝ)) x := by
  have hdynkin := hFeller.integral_eval_stoppingTime_sub_eq_integral_integral_generator hP hK f
    (ContinuousPath.exitTimeTrunc U K) (ContinuousPath.isStoppingTime_exitTimeTrunc U hU K)
    (ContinuousPath.exitTimeTrunc_le U K) x
  have hneg : ∀ omega : ContinuousPath alpha,
      ∫ s in (0 : ℝ)..(ContinuousPath.exitTimeTrunc U K omega : ℝ),
        (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s)) =
      -∫ s in (0 : ℝ)..(ContinuousPath.exitTimeTrunc U K omega : ℝ),
        g (omega (Real.toNNReal s)) := by
    intro omega
    rw [ContinuousPath.integral_exitTimeTrunc_congr U K (g₂ := fun y ↦ -g y) (fun y hy ↦ hLf y
        hy) omega,
      intervalIntegral.integral_neg]
  simp only [hneg, integral_neg] at hdynkin
  linarith only [hdynkin]

/-- **Localized Dynkin formula.**  For a starting point in the open set `U` and a function `φ`
that agrees with the domain element `f` on the closure of `U`, Dynkin's formula at the truncated
exit time holds for `φ` with the generator of `f`: the stopped path sits in the closure of `U`,
where `φ` and `f` agree, and the generator is only ever evaluated inside `U`. -/
theorem IsFellerKernelSemigroup.integral_eval_exitTimeTrunc_sub_eq_of_eqOn_closure
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (f : hFeller.c0Semigroup.generatorDomain) (U : Set alpha) (hU : IsOpen U)
    {φ : alpha → ℝ} (hφ : Set.EqOn φ (f : C₀(alpha, ℝ)) (closure U)) (K : NNReal) {x : alpha}
    (hx : x ∈ U) :
    ∫ omega, φ (omega (ContinuousPath.exitTimeTrunc U K omega))
        ∂(IsConservative.continuousProcess P hP x) - φ x =
      ∫ omega, (∫ s in (0 : ℝ)..(ContinuousPath.exitTimeTrunc U K omega : ℝ),
          (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s)))
        ∂(IsConservative.continuousProcess P hP x) := by
  have hdynkin := hFeller.integral_eval_stoppingTime_sub_eq_integral_integral_generator hP hK f
    (ContinuousPath.exitTimeTrunc U K) (ContinuousPath.isStoppingTime_exitTimeTrunc U hU K)
    (ContinuousPath.exitTimeTrunc_le U K) x
  have hstopped : ∫ omega, φ (omega (ContinuousPath.exitTimeTrunc U K omega))
        ∂(IsConservative.continuousProcess P hP x) =
      ∫ omega, (f : C₀(alpha, ℝ)) (omega (ContinuousPath.exitTimeTrunc U K omega))
        ∂(IsConservative.continuousProcess P hP x) := by
    refine integral_congr_ae ?_
    filter_upwards [IsConservative.ae_eval_zero_eq hP hK x] with omega h0
    exact hφ (ContinuousPath.stopped_exitTimeTrunc_mem_closure U hU K omega (h0 ▸ hx))
  rw [hstopped, hφ (subset_closure hx)]
  exact hdynkin

end SubMarkovKernelSemigroup

end MarkovProcess
