/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Path.ExitTime
import LeanPool.MarkovProcess.MarkovProcess.Path.OptionalStopping
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.DiscountedDynkin

/-!
# Dynkin's formula at a bounded stopping time, and the expected exit time

The Dynkin process of `f` in the generator domain is a martingale for the canonical filtration
under the continuous-path process `Q = continuousProcess P hP` (`martingale_dynkinProcess`), it is
bounded on bounded time intervals, and it is continuous in time along every path.  Optional
stopping (`MarkovProcess.integral_stoppedValue_eq_of_locallyBounded`) therefore applies at every
finite stopping time `T` bounded by a deterministic horizon, and gives **Dynkin's formula at a
bounded stopping time**:

  `E_x f(omega (T omega)) - f x = E_x ∫₀^{T omega} (L f)(omega s) ds`

(`integral_eval_stoppingTime_sub_eq_integral_integral_generator`, with the equivalent compact form
`integral_dynkinProcess_stoppingTime`).

The classical consequence is the **expected exit time bound**: if `L f ≤ -1` on an open set `U`
and `f` is bounded below by `m`, then the exit time from `U`, truncated at any horizon `K`, has
expectation at most `f x - m` from every starting point `x`
(`integral_exitTimeTrunc_le`).  The proof uses that strictly before the exit time the path is
still inside `U`, so the integrand of Dynkin's formula is at most `-1` there.

The truncation at `K` is what keeps the stopping time finite; the bound is uniform in `K`, and
`Trajectory/ExpectedExitTime.lean` removes the truncation by monotone convergence
(`lintegral_exitTime_le`, `ae_exitTime_lt_top`).

The progressive-measurability and optional-stopping statements below are the zero-discount
specializations of the corresponding results in `Trajectory/DiscountedDynkin.lean`.
-/

noncomputable section PortComputability

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess.SubMarkovKernelSemigroup

section

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [LocallyCompactSpace alpha]

variable {P : SubMarkovKernelSemigroup alpha}

section ProgressiveMeasurability

variable [SecondCountableTopology alpha]

omit [LocallyCompactSpace alpha] in
/-- The Dynkin process is progressively measurable: it is adapted and continuous in time. -/
theorem IsFellerKernelSemigroup.progMeasurable_dynkinProcess (hFeller : P.IsFellerKernelSemigroup)
    (f : hFeller.c0Semigroup.generatorDomain) :
    IsStronglyProgressive (ContinuousPath.canonicalFiltration (alpha := alpha))
      (hFeller.dynkinProcess f) := by
  simpa only [hFeller.discountedDynkinProcess_zero f] using!
    hFeller.progMeasurable_discountedDynkinProcess f 0

omit [LocallyCompactSpace alpha] in
/-- The Dynkin process evaluated at a finite stopping time is Borel measurable. -/
theorem IsFellerKernelSemigroup.measurable_dynkinProcess_stoppingTime
    (hFeller : P.IsFellerKernelSemigroup) (f : hFeller.c0Semigroup.generatorDomain)
    (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal))) :
    Measurable fun omega ↦ hFeller.dynkinProcess f (T omega) omega := by
  simpa only [hFeller.discountedDynkinProcess_zero f] using
    hFeller.measurable_discountedDynkinProcess_stoppingTime f 0 T hT

end ProgressiveMeasurability

section Stopping

variable [CompleteSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (hP : P.IsConservative)

/-- **Dynkin's formula at a bounded finite stopping time, in compact form**: the expectation of
the Dynkin process at a finite stopping time bounded by a deterministic horizon is the initial
value `f x`.  This is optional stopping applied to the Dynkin martingale. -/
theorem IsFellerKernelSemigroup.integral_dynkinProcess_stoppingTime
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (f : hFeller.c0Semigroup.generatorDomain) (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal)))
    {K : NNReal} (hTK : ∀ omega, T omega ≤ K) (x : alpha) :
    ∫ omega, hFeller.dynkinProcess f (T omega) omega
        ∂(IsConservative.continuousProcess P hP x) =
      (f : C₀(alpha, ℝ)) x := by
  simpa only [hFeller.discountedDynkinProcess_zero f] using
    hFeller.integral_discountedDynkinProcess_stoppingTime hP hK f 0 T hT hTK x

omit [LocallyCompactSpace alpha] in
/-- The position at a finite stopping time is integrable: it is Borel measurable and bounded by
the `C₀` norm of `f`. -/
theorem IsFellerKernelSemigroup.integrable_eval_stoppingTime
    (hFeller : P.IsFellerKernelSemigroup) (f : hFeller.c0Semigroup.generatorDomain)
    (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal))) (x : alpha) :
    Integrable (fun omega : ContinuousPath alpha ↦ (f : C₀(alpha, ℝ)) (omega (T omega)))
      (IsConservative.continuousProcess P hP x) := by
  refine Integrable.of_bound
    (((f : C₀(alpha, ℝ)).continuous.measurable.comp
      (ContinuousPath.measurable_eval_stoppingTime_borel T hT)).aestronglyMeasurable)
    ‖(f : C₀(alpha, ℝ))‖ (Eventually.of_forall fun omega ↦ ?_)
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact BoundedContinuousFunction.norm_coe_le_norm (f : C₀(alpha, ℝ)).toBCF _

omit [LocallyCompactSpace alpha] in
/-- The Dynkin correction term at a finite stopping time bounded by `K` is integrable: it is
Borel measurable, being the difference of the position at the stopping time and the Dynkin
process there, and bounded by `K ‖L f‖`. -/
theorem IsFellerKernelSemigroup.integrable_integral_generator_stoppingTime
    (hFeller : P.IsFellerKernelSemigroup) (f : hFeller.c0Semigroup.generatorDomain)
    (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal)))
    {K : NNReal} (hTK : ∀ omega, T omega ≤ K) (x : alpha) :
    Integrable (fun omega : ContinuousPath alpha ↦ ∫ s in (0 : ℝ)..(T omega : ℝ),
        (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s)))
      (IsConservative.continuousProcess P hP x) := by
  have hdiff : (fun omega : ContinuousPath alpha ↦ ∫ s in (0 : ℝ)..(T omega : ℝ),
        (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s))) =
      fun omega : ContinuousPath alpha ↦
        (f : C₀(alpha, ℝ)) (omega (T omega)) - hFeller.dynkinProcess f (T omega) omega := by
    funext omega
    rw [hFeller.dynkinProcess_apply]
    ring
  have hmeas : Measurable (fun omega : ContinuousPath alpha ↦ ∫ s in (0 : ℝ)..(T omega : ℝ),
      (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s))) := by
    rw [hdiff]
    exact ((f : C₀(alpha, ℝ)).continuous.measurable.comp
      (ContinuousPath.measurable_eval_stoppingTime_borel T hT)).sub
      (hFeller.measurable_dynkinProcess_stoppingTime f T hT)
  refine Integrable.of_bound hmeas.aestronglyMeasurable
    ((K : ℝ) * ‖hFeller.c0Semigroup.generator f‖) (Eventually.of_forall fun omega ↦ ?_)
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := ((T omega : NNReal) : ℝ)) (C := ‖hFeller.c0Semigroup.generator f‖)
    (f := fun s : ℝ ↦ (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s)))
    (fun s _ ↦ by
      rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
      exact BoundedContinuousFunction.norm_coe_le_norm
        (hFeller.c0Semigroup.generator f).toBCF _)
  rw [sub_zero, abs_of_nonneg (T omega).coe_nonneg, mul_comm] at hb
  refine hb.trans (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr (hTK omega))
    (norm_nonneg (hFeller.c0Semigroup.generator f)))

/-- **Dynkin's formula at a bounded finite stopping time.**  For `f` in the generator domain and
a finite stopping time `T` bounded by a deterministic horizon `K`,

  `E_x f(omega (T omega)) - f x = E_x ∫₀^{T omega} (L f)(omega s) ds`. -/
theorem IsFellerKernelSemigroup.integral_eval_stoppingTime_sub_eq_integral_integral_generator
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (f : hFeller.c0Semigroup.generatorDomain) (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal)))
    {K : NNReal} (hTK : ∀ omega, T omega ≤ K) (x : alpha) :
    ∫ omega, (f : C₀(alpha, ℝ)) (omega (T omega))
          ∂(IsConservative.continuousProcess P hP x) - (f : C₀(alpha, ℝ)) x =
      ∫ omega, (∫ s in (0 : ℝ)..(T omega : ℝ),
          (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s)))
        ∂(IsConservative.continuousProcess P hP x) := by
  have hstop := hFeller.integral_dynkinProcess_stoppingTime hP hK f T hT hTK x
  have hsplit : ∫ omega, hFeller.dynkinProcess f (T omega) omega
        ∂(IsConservative.continuousProcess P hP x) =
      (∫ omega, (f : C₀(alpha, ℝ)) (omega (T omega))
          ∂(IsConservative.continuousProcess P hP x)) -
        ∫ omega, (∫ s in (0 : ℝ)..(T omega : ℝ),
            (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s)))
          ∂(IsConservative.continuousProcess P hP x) := by
    simp only [IsFellerKernelSemigroup.dynkinProcess_apply]
    exact integral_sub (hFeller.integrable_eval_stoppingTime hP f T hT x)
      (hFeller.integrable_integral_generator_stoppingTime hP f T hT hTK x)
  linarith only [hstop, hsplit]

end Stopping

section ExitTime

variable [CompleteSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (hP : P.IsConservative)

omit [MeasurableSpace alpha] [BorelSpace alpha] [LocallyCompactSpace alpha] [CompleteSpace alpha]
  [SecondCountableTopology alpha] [Nonempty alpha] in
/-- Strictly before the truncated exit time, the path is still inside the open set `U`. -/
private theorem mem_of_lt_exitTimeTrunc (U : Set alpha) (K : NNReal)
    (omega : ContinuousPath alpha) (t : NNReal) (ht : t < ContinuousPath.exitTimeTrunc U K omega) :
    omega t ∈ U := by
  have hlt : ((t : NNReal) : ℝ≥0∞) <
      ((ContinuousPath.exitTimeTrunc U K omega : NNReal) : ℝ≥0∞) := ENNReal.coe_lt_coe.mpr ht
  have hle : ((ContinuousPath.exitTimeTrunc U K omega : NNReal) : ℝ≥0∞) ≤
      ContinuousPath.exitTime U omega := by
    have h : ((ContinuousPath.exitTimeTrunc U K omega : NNReal) : WithTop NNReal) ≤
        ContinuousPath.exitTimeTop U omega := by
      rw [ContinuousPath.coe_exitTimeTrunc]
      exact min_le_left _ _
    exact h
  exact ContinuousPath.mem_of_lt_exitTime U omega t (hlt.trans_le hle)

omit [LocallyCompactSpace alpha] in
/-- The truncated exit time is integrable: it is Borel measurable and bounded by its horizon. -/
private theorem integrable_exitTimeTrunc (U : Set alpha) (hU : IsOpen U) (K : NNReal)
    (x : alpha) :
    Integrable (fun omega : ContinuousPath alpha ↦
        ((ContinuousPath.exitTimeTrunc U K omega : NNReal) : ℝ))
      (IsConservative.continuousProcess P hP x) := by
  have hmeas : Measurable (ContinuousPath.exitTimeTrunc U K : ContinuousPath alpha → NNReal) :=
    ContinuousPath.measurable_of_isStoppingTime _
      (ContinuousPath.isStoppingTime_exitTimeTrunc U hU K)
  refine Integrable.of_bound (NNReal.continuous_coe.measurable.comp hmeas).aestronglyMeasurable
    (K : ℝ) (Eventually.of_forall fun omega ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (ContinuousPath.exitTimeTrunc U K omega).coe_nonneg]
  exact NNReal.coe_le_coe.mpr (ContinuousPath.exitTimeTrunc_le U K omega)

omit [CompleteSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha] in
omit [LocallyCompactSpace alpha] in
/-- Along a path, the Dynkin integrand is at most `-1` almost everywhere on `[0, T]`, where `T`
is the truncated exit time: strictly before `T` the path is inside `U`, and the endpoint is a
null set. -/
private theorem integral_generator_exitTimeTrunc_le (hFeller : P.IsFellerKernelSemigroup)
    (f : hFeller.c0Semigroup.generatorDomain) (U : Set alpha)
    (hLf : ∀ y ∈ U, (hFeller.c0Semigroup.generator f) y ≤ -1) (K : NNReal)
    (omega : ContinuousPath alpha) :
    (∫ s in (0 : ℝ)..((ContinuousPath.exitTimeTrunc U K omega : NNReal) : ℝ),
        (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s))) ≤
      -((ContinuousPath.exitTimeTrunc U K omega : NNReal) : ℝ) := by
  have hb0 : (0 : ℝ) ≤ ((ContinuousPath.exitTimeTrunc U K omega : NNReal) : ℝ) :=
    (ContinuousPath.exitTimeTrunc U K omega).coe_nonneg
  have hcont : Continuous fun s : ℝ ↦
      (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s)) :=
    (hFeller.c0Semigroup.generator f).continuous.comp
      (omega.continuous.comp continuous_real_toNNReal)
  have hsingleton : ∀ᵐ s : ℝ ∂(volume : Measure ℝ),
      s ≠ ((ContinuousPath.exitTimeTrunc U K omega : NNReal) : ℝ) := by
    rw [ae_iff]
    simpa only [Ne, not_not, Set.ofPred_eq_eq_singleton] using
      measure_singleton ((ContinuousPath.exitTimeTrunc U K omega : NNReal) : ℝ)
  have hae : ∀ᵐ s : ℝ ∂(volume.restrict
      (Set.Icc (0 : ℝ) ((ContinuousPath.exitTimeTrunc U K omega : NNReal) : ℝ))),
      (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s)) ≤ -1 := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hsingleton] with s hs hsmem
    refine hLf _ (mem_of_lt_exitTimeTrunc U K omega (Real.toNNReal s) ?_)
    exact (Real.toNNReal_lt_iff_lt_coe hsmem.1).mpr (lt_of_le_of_ne hsmem.2 hs)
  have hmono := intervalIntegral.integral_mono_ae_restrict hb0
    (hcont.intervalIntegrable _ _) (intervalIntegrable_const (c := (-1 : ℝ))) hae
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hmono
  linarith only [hmono]

/-- **The expected exit time bound.**  If `f` lies in the generator domain, `L f ≤ -1` on the
open set `U`, and `m` is a lower bound for `f`, then the exit time from `U` truncated at any
horizon `K` has expectation at most `f x - m` under the process started at `x`.  The bound does
not depend on the horizon `K`. -/
theorem IsFellerKernelSemigroup.integral_exitTimeTrunc_le
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (f : hFeller.c0Semigroup.generatorDomain) (U : Set alpha) (hU : IsOpen U)
    (hLf : ∀ y ∈ U, (hFeller.c0Semigroup.generator f) y ≤ -1)
    {m : ℝ} (hm : ∀ y, m ≤ (f : C₀(alpha, ℝ)) y) (K : NNReal) (x : alpha) :
    ∫ omega, ((ContinuousPath.exitTimeTrunc U K omega : NNReal) : ℝ)
        ∂(IsConservative.continuousProcess P hP x) ≤ (f : C₀(alpha, ℝ)) x - m := by
  have hT := ContinuousPath.isStoppingTime_exitTimeTrunc U hU K
  have hTK := ContinuousPath.exitTimeTrunc_le U K
  have hdynkin := hFeller.integral_eval_stoppingTime_sub_eq_integral_integral_generator hP hK f
    (ContinuousPath.exitTimeTrunc U K) hT hTK x
  have hlow : m ≤ ∫ omega, (f : C₀(alpha, ℝ)) (omega (ContinuousPath.exitTimeTrunc U K omega))
      ∂(IsConservative.continuousProcess P hP x) := by
    have hconst : ∫ _omega : ContinuousPath alpha, m
        ∂(IsConservative.continuousProcess P hP x) = m := by
      rw [integral_const, probReal_univ, smul_eq_mul, one_mul]
    rw [← hconst]
    exact integral_mono (integrable_const m)
      (hFeller.integrable_eval_stoppingTime hP f _ hT x) fun omega ↦ hm _
  have hupper : (∫ omega, (∫ s in (0 : ℝ)..((ContinuousPath.exitTimeTrunc U K omega : NNReal) : ℝ),
        (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s)))
      ∂(IsConservative.continuousProcess P hP x)) ≤
      ∫ omega, -((ContinuousPath.exitTimeTrunc U K omega : NNReal) : ℝ)
        ∂(IsConservative.continuousProcess P hP x) :=
    integral_mono (hFeller.integrable_integral_generator_stoppingTime hP f _ hT hTK x)
      (integrable_exitTimeTrunc hP U hU K x).neg
      fun omega ↦ integral_generator_exitTimeTrunc_le hFeller f U hLf K omega
  rw [integral_neg] at hupper
  linarith only [hdynkin, hlow, hupper]

end ExitTime

end

end MarkovProcess.SubMarkovKernelSemigroup

end PortComputability
