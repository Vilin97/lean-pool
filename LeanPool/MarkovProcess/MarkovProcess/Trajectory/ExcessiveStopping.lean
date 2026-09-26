/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Feller.Resolvent
public import LeanPool.MarkovProcess.MarkovProcess.Path.OptionalStopping
public import LeanPool.MarkovProcess.MarkovProcess.Trajectory.DynkinMartingale
public import LeanPool.MarkovProcess.MarkovProcess.Trajectory.ExpectedExitTime


/-!
# Excessive functions and stopping

This file turns the semigroup definition of an exponentially excessive `C₀` function into a
supermartingale along the canonical continuous process.  Continuous-time optional stopping then
gives the corresponding inequality at bounded stopping times and, by Fatou's lemma, at the finite
exit time from an open set.

The exit inequality is the lower-bound half paired with
`IsFellerKernelSemigroup.lintegral_pathResolvent_eq_killedResolvent_add`.  No model-specific
assumptions enter here.

Main results: `IsFellerKernelSemigroup.resolvent_isLambdaExcessive`,
`IsLambdaExcessive.supermartingale_discountedValueProcess`,
`IsLambdaExcessive.integral_discountedValueProcess_stoppingTime_le`, and
`IsLambdaExcessive.lintegral_discountedValue_exitTime_le`.

No converse characterization of excessive functions is asserted.
-/

@[expose] public section

noncomputable section PortComputability

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess.SubMarkovKernelSemigroup

section

section Supermedian

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]

variable {P : SubMarkovKernelSemigroup alpha}

/-- A nonnegative `C₀` function is `lam`-supermedian when its discounted semigroup orbit lies
below the function.  In the Feller setting used below, continuity of `C₀` orbits supplies the
zero-time limit in the usual definition of `lam`-excessiveness; see
`IsFellerKernelSemigroup.tendsto_exp_neg_mul_c0Semigroup_zero`. -/
def IsLambdaExcessive (P : SubMarkovKernelSemigroup alpha) (lam : ℝ) (v : C₀(alpha, ℝ)) : Prop :=
  (∀ x, 0 ≤ v x) ∧ ∀ (t : NNReal) (x : alpha),
    Real.exp (-lam * (t : ℝ)) * ∫ y, v y ∂(P t x) ≤ v x

/-- A semigroup comparison `S(t)v ≤ exp(lam t)v` gives `lam`-excessiveness. -/
theorem isLambdaExcessive_of_c0Semigroup_apply_le_exp_mul
    (lam : ℝ) (v : C₀(alpha, ℝ))
    (hv : ∀ x, 0 ≤ v x)
    (hcomp : ∀ (t : NNReal) (x : alpha),
      kernelIntegral (P t) v x ≤ Real.exp (lam * (t : ℝ)) * v x) :
    P.IsLambdaExcessive lam v := by
  refine ⟨hv, fun t x ↦ ?_⟩
  calc
    Real.exp (-lam * (t : ℝ)) * kernelIntegral (P t) v x
        ≤ Real.exp (-lam * (t : ℝ)) * (Real.exp (lam * (t : ℝ)) * v x) :=
      mul_le_mul_of_nonneg_left (hcomp t x) (Real.exp_pos _).le
    _ = v x := by rw [← mul_assoc, ← Real.exp_add]; ring_nf; simp only [Real.exp_zero, one_mul]

end Supermedian

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [Nonempty alpha] [LocallyCompactSpace alpha]

variable {P : SubMarkovKernelSemigroup alpha}

omit [CompleteSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha] in
omit [LocallyCompactSpace alpha] in
/-- For a Feller semigroup, every exponentially discounted `C₀` orbit converges in `C₀` norm to
its initial function at time zero.  Thus `IsLambdaExcessive` includes the usual excessive
zero-time condition automatically. -/
theorem IsFellerKernelSemigroup.tendsto_exp_neg_mul_c0Semigroup_zero
    (hFeller : P.IsFellerKernelSemigroup) (lam : ℝ) (v : C₀(alpha, ℝ)) :
    Tendsto (fun t : NNReal ↦ Real.exp (-lam * (t : ℝ)) • hFeller.c0Semigroup t v)
      (𝓝 0) (𝓝 v) := by
  have hcontinuous : Continuous fun t : NNReal ↦
      Real.exp (-lam * (t : ℝ)) • hFeller.c0Semigroup t v :=
    (Real.continuous_exp.comp (continuous_const.mul NNReal.continuous_coe)).smul
      (hFeller.c0Semigroup.continuous v)
  have hzero : Tendsto
      (fun t : NNReal ↦ Real.exp (-lam * (t : ℝ)) • hFeller.c0Semigroup t v)
      (𝓝 0) (𝓝 (Real.exp (-lam * ((0 : NNReal) : ℝ)) • hFeller.c0Semigroup 0 v)) :=
    hcontinuous.continuousAt
  simpa only [NNReal.coe_zero, mul_zero, neg_zero, Real.exp_zero, one_smul,
    Semigroup.StronglyContinuousContractionSemigroup.zero_apply] using hzero

omit [CompleteSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha] in
omit [LocallyCompactSpace alpha] in
/-- The resolvent of a nonnegative `C₀` function at a positive shift is excessive at that shift. -/
theorem IsFellerKernelSemigroup.resolvent_isLambdaExcessive
    (hFeller : P.IsFellerKernelSemigroup) (lam : ℝ) (hlam : 0 < lam)
    (f : C₀(alpha, ℝ)) (hf : ∀ x, 0 ≤ f x) :
    P.IsLambdaExcessive lam
      (hFeller.c0Semigroup.resolvent (⟨lam, hlam⟩ : Semigroup.PositiveShift) f) := by
  let mu : Semigroup.PositiveShift := ⟨lam, hlam⟩
  let S := hFeller.c0Semigroup
  let v : C₀(alpha, ℝ) := S.resolvent mu f
  have hv : ∀ x, 0 ≤ v x := by
    intro x
    dsimp only [v, S]
    rw [hFeller.resolvent_apply_apply]
    exact integral_nonneg fun t ↦ mul_nonneg (Real.exp_pos _).le (integral_nonneg hf)
  change P.IsLambdaExcessive lam v
  refine ⟨hv, fun t x ↦ ?_⟩
  change Real.exp (-lam * (t : ℝ)) * S t v x ≤ v x
  let vdom : S.generatorDomain := ⟨v, by
    dsimp only [v]
    exact S.resolvent_mem_generatorDomain mu f⟩
  have hgen : S.generator vdom - lam • (vdom : C₀(alpha, ℝ)) = -f := by
    have hgenerator : S.generator vdom = lam • v - f := by
      dsimp only [vdom, v]
      exact S.generator_resolvent mu f
    rw [hgenerator]
    change (lam • v - f) - lam • v = -f
    module
  have hidentity : Real.exp (-lam * (t : ℝ)) * S t v x - v x =
      ∫ s in (0 : ℝ)..t,
        Real.exp (-lam * s) * S (Real.toNNReal s) (-f) x := by
    calc
      Real.exp (-lam * (t : ℝ)) * S t v x - v x =
          c0EvalCLM x (Real.exp (-lam * (t : ℝ)) • S t (vdom : C₀(alpha, ℝ)) - vdom) := by
        rw [map_sub, map_smul, c0EvalCLM_apply, c0EvalCLM_apply, smul_eq_mul]
      _ = c0EvalCLM x (∫ s in (0 : ℝ)..t, Real.exp (-lam * s) •
            S (Real.toNNReal s) (S.generator vdom - lam • (vdom : C₀(alpha, ℝ)))) := by
        rw [S.exp_smul_operator_sub_eq_integral vdom lam t]
      _ = c0EvalCLM x (∫ s in (0 : ℝ)..t,
            Real.exp (-lam * s) • S (Real.toNNReal s) (-f)) := by rw [hgen]
      _ = ∫ s in (0 : ℝ)..t,
            c0EvalCLM x (Real.exp (-lam * s) • S (Real.toNNReal s) (-f)) := by
        rw [← (c0EvalCLM x).intervalIntegral_comp_comm]
        exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
          (S.continuous_operator_toNNReal (-f))).intervalIntegrable _ _
      _ = ∫ s in (0 : ℝ)..t,
            Real.exp (-lam * s) * S (Real.toNNReal s) (-f) x := by
        refine intervalIntegral.integral_congr fun s _ ↦ ?_
        rw [map_smul, c0EvalCLM_apply, smul_eq_mul]
  have hnonneg : 0 ≤ ∫ s in (0 : ℝ)..t,
      Real.exp (-lam * s) * S (Real.toNNReal s) f x := by
    refine intervalIntegral.integral_nonneg t.coe_nonneg fun s _ ↦
      mul_nonneg (Real.exp_pos _).le ?_
    change 0 ≤ P.c0Operator hFeller.mapsC0 (Real.toNNReal s) f x
    exact P.c0Operator_apply_nonneg hFeller.mapsC0 _ hf x
  have hneg : (∫ s in (0 : ℝ)..t,
      Real.exp (-lam * s) * S (Real.toNNReal s) (-f) x) =
      -(∫ s in (0 : ℝ)..t, Real.exp (-lam * s) * S (Real.toNNReal s) f x) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun s _ ↦ ?_
    rw [map_neg]
    change Real.exp (-lam * s) * (-S (Real.toNNReal s) f x) =
      -(Real.exp (-lam * s) * S (Real.toNNReal s) f x)
    ring
  apply sub_nonpos.mp
  rw [hidentity, hneg]
  exact neg_nonpos.mpr hnonneg

/-- The exponentially discounted value of `v` along a continuous path. -/
def discountedValueProcess (lam : ℝ) (v : C₀(alpha, ℝ))
    (t : NNReal) (omega : ContinuousPath alpha) : ℝ :=
  Real.exp (-lam * (t : ℝ)) * v (omega t)

omit [CompleteSpace alpha] [Nonempty alpha] [LocallyCompactSpace alpha] in
/-- The discounted value process is adapted to the canonical filtration. -/
theorem adapted_discountedValueProcess (lam : ℝ) (v : C₀(alpha, ℝ)) :
    StronglyAdapted (ContinuousPath.canonicalFiltration (alpha := alpha))
      (discountedValueProcess lam v) := by
  intro t
  exact ((v.continuous.comp_stronglyMeasurable
    (ContinuousPath.measurable_coordinateProcess_canonicalFiltration
      (alpha := alpha) t).stronglyMeasurable).const_mul _)

omit [CompleteSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [Nonempty alpha] [LocallyCompactSpace alpha] in
/-- The discounted value process is uniformly bounded in the path at each time. -/
theorem norm_discountedValueProcess_le (lam : ℝ) (v : C₀(alpha, ℝ))
    (t : NNReal) (omega : ContinuousPath alpha) :
    ‖discountedValueProcess lam v t omega‖ ≤ Real.exp (-lam * (t : ℝ)) * ‖v‖ := by
  rw [discountedValueProcess, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (norm_c0_apply_le v (omega t)) (Real.exp_pos _).le

omit [CompleteSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [Nonempty alpha] [LocallyCompactSpace alpha] in
/-- The discounted value process has continuous sample paths. -/
theorem continuous_discountedValueProcess (lam : ℝ) (v : C₀(alpha, ℝ))
    (omega : ContinuousPath alpha) :
    Continuous fun t : NNReal ↦ discountedValueProcess lam v t omega :=
  (Real.continuous_exp.comp (continuous_const.mul NNReal.continuous_coe)).mul
    (v.continuous.comp omega.continuous)

/-- **Excessive functions give supermartingales.** -/
theorem IsLambdaExcessive.supermartingale_discountedValueProcess
    (hP : P.IsConservative) (hFeller : P.IsFellerKernelSemigroup)
    (hK : P.KolmogorovRegular hP) {lam : ℝ} {v : C₀(alpha, ℝ)}
    (hv : P.IsLambdaExcessive lam v) (x : alpha) :
    Supermartingale (discountedValueProcess lam v)
      (ContinuousPath.canonicalFiltration (alpha := alpha))
      (IsConservative.continuousProcess P hP x) := by
  refine ⟨adapted_discountedValueProcess lam v, ?_, ?_⟩
  · intro s t hst
    let c : ℝ := Real.exp (-lam * (s : ℝ))
    let F : ContinuousPath alpha → ℝ := fun eta ↦
      Real.exp (-lam * ((t - s : NNReal) : ℝ)) * v (eta (t - s))
    have hdecomp : discountedValueProcess lam v t =
        fun omega ↦ c * F (ContinuousPath.shift s omega) := by
      funext omega
      dsimp only [discountedValueProcess, c, F]
      rw [ContinuousPath.shift_apply, add_tsub_cancel_of_le hst]
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      rw [NNReal.coe_sub hst]
      ring
    have hmeasF : StronglyMeasurable F :=
      (v.continuous.comp_stronglyMeasurable
        (ContinuousPath.measurable_coordinateProcess (t - s)).stronglyMeasurable).const_mul _
    have hboundF : ∀ eta : ContinuousPath alpha, ‖F eta‖ ≤
        Real.exp (-lam * ((t - s : NNReal) : ℝ)) * ‖v‖ := fun eta ↦ by
      exact norm_discountedValueProcess_le lam v (t - s) eta
    have hcond := hFeller.continuousProcess_condExp_shift P hP hK x s F hmeasF _ hboundF
    rw [hdecomp]
    refine (condExp_smul c (fun omega ↦ F (ContinuousPath.shift s omega)) _).trans_le ?_
    refine (EventuallyEq.const_smul hcond c).trans_le (Eventually.of_forall fun omega ↦ ?_)
    change c * (∫ eta, F eta ∂IsConservative.continuousProcess P hP (omega s)) ≤
      discountedValueProcess lam v s omega
    have hinner : ∫ eta, F eta ∂IsConservative.continuousProcess P hP (omega s) ≤
        v (omega s) := by
      dsimp only [F]
      rw [MeasureTheory.integral_const_mul,
        hFeller.integral_eval_continuousProcess P hP hK]
      exact hv.2 (t - s) (omega s)
    dsimp only [c, discountedValueProcess]
    exact mul_le_mul_of_nonneg_left hinner (Real.exp_pos _).le
  · intro t
    exact Integrable.of_bound
      ((adapted_discountedValueProcess lam v t).mono
        ((ContinuousPath.canonicalFiltration (alpha := alpha)).le t)).aestronglyMeasurable
      (Real.exp (-lam * (t : ℝ)) * ‖v‖)
      (Eventually.of_forall (norm_discountedValueProcess_le lam v t))

/-- **Optional stopping for an excessive function.**  At every bounded finite stopping time, the
expected discounted terminal value is at most its initial value. -/
theorem IsLambdaExcessive.integral_discountedValueProcess_stoppingTime_le
    (hP : P.IsConservative) (hFeller : P.IsFellerKernelSemigroup)
    (hK : P.KolmogorovRegular hP) {lam : ℝ} {v : C₀(alpha, ℝ)}
    (hv : P.IsLambdaExcessive lam v) (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal)))
    {K : NNReal} (hTK : ∀ omega, T omega ≤ K) (x : alpha) :
    ∫ omega, Real.exp (-lam * (T omega : ℝ)) * v (omega (T omega))
        ∂(IsConservative.continuousProcess P hP x) ≤ v x := by
  have hlocal : ∀ u : NNReal, ∃ C : ℝ, ∀ t ≤ u, ∀ omega : ContinuousPath alpha,
      ‖discountedValueProcess lam v t omega‖ ≤ C := by
    intro u
    refine ⟨Real.exp (|lam| * (u : ℝ)) * ‖v‖, fun t htu omega ↦ ?_⟩
    refine (norm_discountedValueProcess_le lam v t omega).trans ?_
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr <| calc
      -lam * (t : ℝ) ≤ |lam| * (t : ℝ) :=
        mul_le_mul_of_nonneg_right (neg_le_abs lam) t.coe_nonneg
      _ ≤ |lam| * (u : ℝ) :=
        mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr htu) (abs_nonneg lam)) (norm_nonneg v)
  have hstop := MarkovProcess.integral_stoppedValue_le_of_locallyBounded
    (hv.supermartingale_discountedValueProcess hP hFeller hK x) hlocal
    (fun omega u ↦ (continuous_discountedValueProcess lam v omega).continuousWithinAt)
    hT hTK
  have hzero :
      ∫ omega, v (omega 0) ∂(IsConservative.continuousProcess P hP x) = v x := by
    rw [← hFeller.c0Semigroup_apply_eq_integral P hP hK]
    simp only [Semigroup.StronglyContinuousContractionSemigroup.zero_apply]
  simpa only [discountedValueProcess, NNReal.coe_zero, mul_zero, neg_zero, Real.exp_zero,
    one_mul, hzero] using hstop

omit [CompleteSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [Nonempty alpha] [LocallyCompactSpace alpha] in
private theorem exitTimeTrunc_eq_untopD_of_le (U : Set alpha) (omega : ContinuousPath alpha)
    {K : NNReal} (hfinite : ContinuousPath.exitTime U omega ≠ ⊤)
    (hle : (ContinuousPath.exitTime U omega).toNNReal ≤ K) :
    ContinuousPath.exitTimeTrunc U K omega =
      (ContinuousPath.exitTime U omega).untopD 0 := by
  have hexit : ContinuousPath.exitTime U omega ≤ (K : ℝ≥0∞) := by
    rw [← ENNReal.coe_toNNReal hfinite]
    exact ENNReal.coe_le_coe.mpr hle
  apply ENNReal.coe_injective
  rw [ContinuousPath.coe_exitTimeTrunc_ennreal, min_eq_left hexit]
  exact (ENNReal.coe_toNNReal hfinite).symm

/-- **Exit inequality for an excessive function.**  The discounted value at the finite exit time
from an open set has `ℝ≥0∞` expectation at most the initial value.  Together with
`IsFellerKernelSemigroup.lintegral_pathResolvent_eq_killedResolvent_add`, this is the lower-bound
half of the resolvent comparison. -/
theorem IsLambdaExcessive.lintegral_discountedValue_exitTime_le
    (hP : P.IsConservative) (hFeller : P.IsFellerKernelSemigroup)
    (hK : P.KolmogorovRegular hP) {lam : ℝ} {v : C₀(alpha, ℝ)}
    (hv : P.IsLambdaExcessive lam v) (U : Set alpha) (hU : IsOpen U) (x : alpha) :
    ∫⁻ omega, ({omega | ContinuousPath.exitTime U omega < ⊤} : Set _).indicator
        (fun omega ↦
          ENNReal.ofReal (Real.exp (-lam * (ContinuousPath.exitTime U omega).toReal)) *
            ENNReal.ofReal (v (omega ((ContinuousPath.exitTime U omega).untopD 0)))) omega
        ∂(IsConservative.continuousProcess P hP x) ≤ ENNReal.ofReal (v x) := by
  let Q : Measure (ContinuousPath alpha) := IsConservative.continuousProcess P hP x
  let T : ℕ → ContinuousPath alpha → NNReal := fun n omega ↦
    ContinuousPath.exitTimeTrunc U n omega
  let g : ℕ → ContinuousPath alpha → ℝ≥0∞ := fun n omega ↦
    ENNReal.ofReal (Real.exp (-lam * (T n omega : ℝ))) *
      ENNReal.ofReal (v (omega (T n omega)))
  have hTstop : ∀ n, IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T n omega : WithTop NNReal)) := fun n ↦
    ContinuousPath.isStoppingTime_exitTimeTrunc U hU n
  have hTle : ∀ n omega, T n omega ≤ n := fun n omega ↦
    ContinuousPath.exitTimeTrunc_le U n omega
  have hrealMeas : ∀ n, Measurable fun omega ↦
      Real.exp (-lam * (T n omega : ℝ)) * v (omega (T n omega)) := by
    intro n
    have htime : Measurable fun omega : ContinuousPath alpha ↦ (T n omega : ℝ) :=
      measurable_coe_nnreal_real.comp
        (ContinuousPath.measurable_of_isStoppingTime _ (hTstop n))
    exact (Real.continuous_exp.measurable.comp (measurable_const.mul htime)).mul
      (v.continuous.measurable.comp
        (ContinuousPath.measurable_eval_stoppingTime_borel _ (hTstop n)))
  have hgMeas : ∀ n, Measurable (g n) := fun n ↦
    (ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp (measurable_const.mul
        (measurable_coe_nnreal_real.comp
          (ContinuousPath.measurable_of_isStoppingTime _ (hTstop n)))))).mul
      (ENNReal.measurable_ofReal.comp (v.continuous.measurable.comp
        (ContinuousPath.measurable_eval_stoppingTime_borel _ (hTstop n))))
  have hnonneg : ∀ n omega,
      0 ≤ Real.exp (-lam * (T n omega : ℝ)) * v (omega (T n omega)) := fun n omega ↦
    mul_nonneg (Real.exp_pos _).le (hv.1 _)
  have hint : ∀ n, Integrable (fun omega ↦
      Real.exp (-lam * (T n omega : ℝ)) * v (omega (T n omega))) Q := by
    intro n
    refine Integrable.of_bound (hrealMeas n).aestronglyMeasurable
      (Real.exp (|lam| * (n : ℝ)) * ‖v‖)
      (Eventually.of_forall fun omega ↦ ?_)
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-lam * (T n omega : ℝ)) * ‖v (omega (T n omega))‖
          ≤ Real.exp (-lam * (T n omega : ℝ)) * ‖v‖ :=
        mul_le_mul_of_nonneg_left (norm_c0_apply_le v _) (Real.exp_pos _).le
      _ ≤ Real.exp (|lam| * (n : ℝ)) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr <| calc
          -lam * (T n omega : ℝ) ≤ |lam| * (T n omega : ℝ) :=
            mul_le_mul_of_nonneg_right (neg_le_abs lam) NNReal.zero_le_coe
          _ ≤ |lam| * (n : ℝ) :=
            mul_le_mul_of_nonneg_left
              (by exact_mod_cast hTle n omega) (abs_nonneg lam)) (norm_nonneg v)
  have hbound : ∀ n, ∫⁻ omega, g n omega ∂Q ≤ ENNReal.ofReal (v x) := by
    intro n
    have hreal : ∫⁻ omega, ENNReal.ofReal
        (Real.exp (-lam * (T n omega : ℝ)) * v (omega (T n omega))) ∂Q ≤
        ENNReal.ofReal (v x) := by
      rw [← ofReal_integral_eq_lintegral_ofReal (hint n)
        (Eventually.of_forall (hnonneg n))]
      exact ENNReal.ofReal_le_ofReal
        (hv.integral_discountedValueProcess_stoppingTime_le hP hFeller hK
          (T n) (hTstop n) (hTle n) x)
    simpa only [g, ENNReal.ofReal_mul (Real.exp_pos _).le] using hreal
  have htarget : ∀ omega : ContinuousPath alpha,
      ({omega | ContinuousPath.exitTime U omega < ⊤} : Set _).indicator
          (fun omega ↦
            ENNReal.ofReal (Real.exp (-lam * (ContinuousPath.exitTime U omega).toReal)) *
              ENNReal.ofReal (v (omega
                ((ContinuousPath.exitTime U omega).untopD 0)))) omega ≤
        liminf (fun n ↦ g n omega) atTop := by
    intro omega
    by_cases hfinite : ContinuousPath.exitTime U omega < ⊤
    · simp only [Set.indicator_of_mem (show omega ∈
          {omega | ContinuousPath.exitTime U omega < ⊤} from hfinite)]
      have hne : ContinuousPath.exitTime U omega ≠ ⊤ := ne_top_of_lt hfinite
      obtain ⟨N, hN⟩ := exists_nat_ge (ContinuousPath.exitTime U omega).toNNReal
      have hevent : ∀ᶠ n : ℕ in atTop,
          g n omega = ENNReal.ofReal
              (Real.exp (-lam * (ContinuousPath.exitTime U omega).toReal)) *
            ENNReal.ofReal (v (omega
              ((ContinuousPath.exitTime U omega).untopD 0))) := by
        filter_upwards [eventually_ge_atTop N] with n hn
        have htime : T n omega = (ContinuousPath.exitTime U omega).untopD 0 :=
          exitTimeTrunc_eq_untopD_of_le U omega hne (hN.trans (by exact_mod_cast hn))
        dsimp only [g]
        rw [htime]
        rw [show (((ContinuousPath.exitTime U omega).untopD (0 : NNReal) : NNReal) : ℝ) =
          (ContinuousPath.exitTime U omega).toReal by
            rw [← ENNReal.coe_toNNReal hne]
            rfl]
      have htend : Tendsto (fun n ↦ g n omega) atTop
          (𝓝 (ENNReal.ofReal
              (Real.exp (-lam * (ContinuousPath.exitTime U omega).toReal)) *
            ENNReal.ofReal (v (omega
              ((ContinuousPath.exitTime U omega).untopD 0))))) :=
        tendsto_const_nhds.congr' (hevent.mono fun _ hn ↦ hn.symm)
      exact le_of_eq htend.liminf_eq.symm
    · simp only [Set.indicator_of_notMem (show omega ∉
          {omega | ContinuousPath.exitTime U omega < ⊤} from hfinite)]
      exact zero_le
  calc
    ∫⁻ omega, ({omega | ContinuousPath.exitTime U omega < ⊤} : Set _).indicator
          (fun omega ↦
            ENNReal.ofReal (Real.exp (-lam * (ContinuousPath.exitTime U omega).toReal)) *
              ENNReal.ofReal (v (omega
                ((ContinuousPath.exitTime U omega).untopD 0)))) omega ∂Q
        ≤ ∫⁻ omega, liminf (fun n ↦ g n omega) atTop ∂Q := lintegral_mono htarget
    _ ≤ liminf (fun n ↦ ∫⁻ omega, g n omega ∂Q) atTop := lintegral_liminf_le hgMeas
    _ ≤ ENNReal.ofReal (v x) :=
      liminf_le_of_frequently_le' (Frequently.of_forall hbound)

/-- The finite-exit inequality with the nonnegative factors combined inside `ENNReal.ofReal`. -/
theorem IsLambdaExcessive.lintegral_ofReal_discountedValue_exitTime_le
    (hP : P.IsConservative) (hFeller : P.IsFellerKernelSemigroup)
    (hK : P.KolmogorovRegular hP) {lam : ℝ} {v : C₀(alpha, ℝ)}
    (hv : P.IsLambdaExcessive lam v) (U : Set alpha) (hU : IsOpen U) (x : alpha) :
    ∫⁻ omega, ({omega | ContinuousPath.exitTime U omega < ⊤} : Set _).indicator
        (fun omega ↦ ENNReal.ofReal
          (Real.exp (-lam * (ContinuousPath.exitTime U omega).toReal) *
            v (omega ((ContinuousPath.exitTime U omega).untopD 0)))) omega
        ∂(IsConservative.continuousProcess P hP x) ≤ ENNReal.ofReal (v x) := by
  simpa only [ENNReal.ofReal_mul (Real.exp_pos _).le] using
    hv.lintegral_discountedValue_exitTime_le hP hFeller hK U hU x

end

end MarkovProcess.SubMarkovKernelSemigroup

end PortComputability
