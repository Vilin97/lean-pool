/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.ClampedCoordinate
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.Dynkin
import Mathlib.Probability.Martingale.Basic

/-!
# The Dynkin martingale

For the continuous-path process `Q = continuousProcess P hP` of a conservative Feller semigroup
`P` and a function `f` in the generator domain of the `C₀` semigroup of `P`, with generator
`L f`, the **Dynkin process**

  `M t omega = f (omega t) - ∫₀ᵗ (L f) (omega s) ds`

is a martingale for the canonical filtration under `Q x`, for every starting point `x`
(`IsFellerKernelSemigroup.martingale_dynkinProcess`).

The route is the deterministic-time Dynkin identity
(`integral_eval_sub_eq_integral_integral_generator`), which says exactly that
`E_y M u = f y` for every time `u` and starting point `y` (`integral_dynkinProcess`), together
with the additive decomposition

  `M t omega = M s omega - f (omega s) + M (t - s) (shift s omega)`   (`s ≤ t`)

(`dynkinProcess_eq_add_shift`) and the simple Markov property in conditional-expectation form
(`continuousProcess_condExp_shift`): conditionally on the canonical filtration at time `s`, the
expectation of the last term is `f (omega s)`, which cancels the middle term.

The auxiliary facts proved on the way are of independent use: the Dynkin process is bounded by
`‖f‖ + t ‖L f‖` on `[0, t]` (`norm_dynkinProcess_le`), it is adapted to the canonical filtration
(`adapted_dynkinProcess`), and it is continuous in time along every path
(`continuous_dynkinProcess`).  Adaptedness of the time-integral term comes from progressive
measurability of the coordinate process together with measurability of Bochner integrals in a
parameter.

The exponentially discounted extension is developed in `Trajectory/DiscountedDynkin.lean`;
its zero-discount process is identified with this one by `discountedDynkinProcess_zero`.
-/

noncomputable section PortComputability

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess.SubMarkovKernelSemigroup

section

section C0Bound

variable {alpha : Type*} [TopologicalSpace alpha]

/-- The `C₀` norm bounds the values of a `C₀` function. -/
theorem norm_c0_apply_le (g : C₀(alpha, ℝ)) (y : alpha) : ‖g y‖ ≤ ‖g‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact BoundedContinuousFunction.norm_coe_le_norm g.toBCF y

end C0Bound

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [LocallyCompactSpace alpha]

variable {P : SubMarkovKernelSemigroup alpha}

section Definition

/-- The **Dynkin process** of a function `f` in the generator domain: the position functional
`f (omega t)` corrected by the time integral `∫₀ᵗ (L f) (omega s) ds` of the generator along the
path.  Under the continuous-path process of `P` this is a martingale
(`martingale_dynkinProcess`). -/
def IsFellerKernelSemigroup.dynkinProcess (hFeller : P.IsFellerKernelSemigroup)
    (f : hFeller.c0Semigroup.generatorDomain) (t : NNReal) (omega : ContinuousPath alpha) : ℝ :=
  (f : C₀(alpha, ℝ)) (omega t) -
    ∫ s in (0 : ℝ)..t, (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s))

omit [LocallyCompactSpace alpha] in
/-- The Dynkin process, written out. -/
theorem IsFellerKernelSemigroup.dynkinProcess_apply (hFeller : P.IsFellerKernelSemigroup)
    (f : hFeller.c0Semigroup.generatorDomain) (t : NNReal) (omega : ContinuousPath alpha) :
    hFeller.dynkinProcess f t omega =
      (f : C₀(alpha, ℝ)) (omega t) -
        ∫ s in (0 : ℝ)..t, (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s)) :=
  rfl

omit [LocallyCompactSpace alpha] in
/-- The integrand of the Dynkin correction term is continuous in the time variable. -/
private theorem continuous_generator_path (hFeller : P.IsFellerKernelSemigroup)
    (f : hFeller.c0Semigroup.generatorDomain) (omega : ContinuousPath alpha) :
    Continuous fun s : ℝ ↦ (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s)) :=
  (hFeller.c0Semigroup.generator f).continuous.comp
    (omega.continuous.comp continuous_real_toNNReal)

omit [LocallyCompactSpace alpha] in
/-- **The Dynkin process is bounded on bounded time intervals**: at time `t` it is bounded by
`‖f‖ + t ‖L f‖`, uniformly in the path. -/
theorem IsFellerKernelSemigroup.norm_dynkinProcess_le (hFeller : P.IsFellerKernelSemigroup)
    (f : hFeller.c0Semigroup.generatorDomain) (t : NNReal) (omega : ContinuousPath alpha) :
    ‖hFeller.dynkinProcess f t omega‖ ≤
      ‖(f : C₀(alpha, ℝ))‖ + (t : ℝ) * ‖hFeller.c0Semigroup.generator f‖ := by
  have hint : ‖∫ s in (0 : ℝ)..t,
      (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s))‖ ≤
        (t : ℝ) * ‖hFeller.c0Semigroup.generator f‖ := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := (t : ℝ)) (C := ‖hFeller.c0Semigroup.generator f‖)
      (f := fun s : ℝ ↦ (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s)))
      (fun s _ ↦ norm_c0_apply_le _ _)
    rwa [sub_zero, abs_of_nonneg t.coe_nonneg, mul_comm] at h
  rw [hFeller.dynkinProcess_apply]
  exact (norm_sub_le _ _).trans (add_le_add (norm_c0_apply_le _ _) hint)

omit [LocallyCompactSpace alpha] in
/-- The Dynkin process is continuous in time along every path: the position term is continuous
because paths and `f` are, and the correction term is continuous because it is the integral of a
continuous integrand over `[0, t]`. -/
theorem IsFellerKernelSemigroup.continuous_dynkinProcess (hFeller : P.IsFellerKernelSemigroup)
    (f : hFeller.c0Semigroup.generatorDomain) (omega : ContinuousPath alpha) :
    Continuous fun t : NNReal ↦ hFeller.dynkinProcess f t omega := by
  have hcont := continuous_generator_path hFeller f omega
  have hinteg : Continuous fun u : ℝ ↦
      ∫ s in (0 : ℝ)..u, (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s)) := by
    rw [continuous_iff_continuousAt]
    intro u
    exact ((hcont.integral_hasStrictDerivAt 0 u).hasDerivAt).continuousAt
  exact ((f : C₀(alpha, ℝ)).continuous.comp omega.continuous).sub
    (hinteg.comp NNReal.continuous_coe)

end Definition

section Adapted

variable [SecondCountableTopology alpha]

omit [LocallyCompactSpace alpha] in
/-- The coordinate at a time clamped to `[0, t]`, read jointly in the time and the path, is
strongly measurable for the product of the Borel structure of the time variable with the
canonical filtration at time `t`.  This is progressive measurability of the coordinate process,
transported along the clamping map. -/
private theorem stronglyMeasurable_generator_min (hFeller : P.IsFellerKernelSemigroup)
    (f : hFeller.c0Semigroup.generatorDomain) (t : NNReal) :
    StronglyMeasurable[(borel ℝ).prod (ContinuousPath.canonicalFiltration (alpha := alpha) t)]
      (fun p : ℝ × ContinuousPath alpha ↦
        (hFeller.c0Semigroup.generator f) (p.2 (min (Real.toNNReal p.1) t))) := by
  exact (hFeller.c0Semigroup.generator f).continuous.comp_stronglyMeasurable
    (ContinuousPath.measurable_clampedCoordinate (alpha := alpha) t).stronglyMeasurable

/-- Measurability of a Bochner integral in a parameter, with the parameter sigma-algebra given by
a variable so that it can be instantiated at a filtration. -/
theorem stronglyMeasurable_integral_prod {Omega : Type*} {mOmega : MeasurableSpace Omega}
    (mu : Measure ℝ) [SFinite mu] {phi : ℝ × Omega → ℝ}
    (hphi : StronglyMeasurable[(borel ℝ).prod mOmega] phi) :
    StronglyMeasurable[mOmega] fun omega : Omega ↦ ∫ s, phi (s, omega) ∂mu :=
  hphi.integral_prod_left'

omit [LocallyCompactSpace alpha] in
/-- The Dynkin correction term at time `t` is strongly measurable for the canonical filtration at
time `t`: it is a Bochner integral over `[0, t]` of a jointly measurable integrand. -/
theorem IsFellerKernelSemigroup.stronglyMeasurable_integral_generator
    (hFeller : P.IsFellerKernelSemigroup) (f : hFeller.c0Semigroup.generatorDomain) (t : NNReal) :
    StronglyMeasurable[ContinuousPath.canonicalFiltration (alpha := alpha) t]
      (fun omega : ContinuousPath alpha ↦
        ∫ s in (0 : ℝ)..t, (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s))) := by
  have hprod := stronglyMeasurable_integral_prod (volume.restrict (Set.Ioc (0 : ℝ) t))
    (stronglyMeasurable_generator_min hFeller f t)
  have hfun : (fun omega : ContinuousPath alpha ↦
      ∫ s in (0 : ℝ)..t, (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s))) =
      fun omega : ContinuousPath alpha ↦
        ∫ s, (hFeller.c0Semigroup.generator f) (omega (min (Real.toNNReal s) t))
          ∂(volume.restrict (Set.Ioc (0 : ℝ) t)) := by
    funext omega
    rw [intervalIntegral.integral_of_le t.coe_nonneg]
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs ↦ ?_
    rw [min_eq_left (Real.toNNReal_le_iff_le_coe.mpr hs.2)]
  rw [hfun]
  exact hprod

omit [LocallyCompactSpace alpha] in
/-- The Dynkin process at time `t` is strongly measurable for the canonical filtration at time
`t`. -/
theorem IsFellerKernelSemigroup.stronglyMeasurable_dynkinProcess_canonicalFiltration
    (hFeller : P.IsFellerKernelSemigroup) (f : hFeller.c0Semigroup.generatorDomain) (t : NNReal) :
    StronglyMeasurable[ContinuousPath.canonicalFiltration (alpha := alpha) t]
      (hFeller.dynkinProcess f t) :=
  ((f : C₀(alpha, ℝ)).continuous.comp_stronglyMeasurable
      (ContinuousPath.measurable_coordinateProcess_canonicalFiltration
        (alpha := alpha) t).stronglyMeasurable).sub
    (hFeller.stronglyMeasurable_integral_generator f t)

omit [LocallyCompactSpace alpha] in
/-- The Dynkin process at time `t` is Borel measurable on path space. -/
theorem IsFellerKernelSemigroup.stronglyMeasurable_dynkinProcess
    (hFeller : P.IsFellerKernelSemigroup) (f : hFeller.c0Semigroup.generatorDomain) (t : NNReal) :
    StronglyMeasurable (hFeller.dynkinProcess f t) :=
  (hFeller.stronglyMeasurable_dynkinProcess_canonicalFiltration f t).mono
    ((ContinuousPath.canonicalFiltration (alpha := alpha)).le t)

omit [LocallyCompactSpace alpha] in
/-- **The Dynkin process is adapted** to the canonical filtration. -/
theorem IsFellerKernelSemigroup.adapted_dynkinProcess (hFeller : P.IsFellerKernelSemigroup)
    (f : hFeller.c0Semigroup.generatorDomain) :
    StronglyAdapted (ContinuousPath.canonicalFiltration (alpha := alpha))
      (hFeller.dynkinProcess f) :=
  fun t ↦ hFeller.stronglyMeasurable_dynkinProcess_canonicalFiltration f t

end Adapted

section Decomposition

omit [LocallyCompactSpace alpha] in
/-- **Additive decomposition of the Dynkin process at an intermediate time.**  For `s ≤ t` the
Dynkin process at time `t` is the Dynkin process at time `s`, corrected by the position at time
`s`, plus the Dynkin process at time `t - s` of the path shifted by `s`. -/
theorem IsFellerKernelSemigroup.dynkinProcess_eq_add_shift (hFeller : P.IsFellerKernelSemigroup)
    (f : hFeller.c0Semigroup.generatorDomain) (s t : NNReal) (hst : s ≤ t)
    (omega : ContinuousPath alpha) :
    hFeller.dynkinProcess f t omega =
      hFeller.dynkinProcess f s omega - (f : C₀(alpha, ℝ)) (omega s) +
        hFeller.dynkinProcess f (t - s) (ContinuousPath.shift s omega) := by
  have hcont := continuous_generator_path hFeller f omega
  have hshift : (∫ u in (0 : ℝ)..((t - s : NNReal) : ℝ),
        (hFeller.c0Semigroup.generator f) (omega (s + Real.toNNReal u))) =
      ∫ v in (s : ℝ)..(t : ℝ),
        (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal v)) := by
    have hcongr : (∫ u in (0 : ℝ)..((t - s : NNReal) : ℝ),
          (hFeller.c0Semigroup.generator f) (omega (s + Real.toNNReal u))) =
        ∫ u in (0 : ℝ)..((t - s : NNReal) : ℝ),
          (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal (u + s))) := by
      refine intervalIntegral.integral_congr fun u hu ↦ ?_
      have hu0 : (0 : ℝ) ≤ u := by
        rw [Set.uIcc_of_le (t - s : NNReal).coe_nonneg] at hu
        exact hu.1
      have hcoe : Real.toNNReal (u + s) = s + Real.toNNReal u := by
        apply NNReal.coe_injective
        rw [NNReal.coe_add, Real.coe_toNNReal u hu0,
          Real.coe_toNNReal _ (add_nonneg hu0 s.coe_nonneg)]
        ring
      rw [hcoe]
    rw [hcongr,
      intervalIntegral.integral_comp_add_right
        (fun v : ℝ ↦ (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal v))) (s : ℝ),
      zero_add]
    congr 1
    rw [NNReal.coe_sub hst]
    ring
  have hsplit : (∫ v in (0 : ℝ)..(s : ℝ),
        (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal v))) +
      (∫ v in (s : ℝ)..(t : ℝ),
        (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal v))) =
      ∫ v in (0 : ℝ)..(t : ℝ),
        (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal v)) :=
    intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)
  simp only [IsFellerKernelSemigroup.dynkinProcess_apply, ContinuousPath.shift_apply,
    add_tsub_cancel_of_le hst]
  rw [hshift]
  linarith only [hsplit]

end Decomposition

section Process

variable [CompleteSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
variable (hP : P.IsConservative)

section Expectation

omit [LocallyCompactSpace alpha] in
/-- Integrability of the Dynkin process under the continuous-path process: it is Borel measurable
and bounded, and the law of the process is a probability measure. -/
theorem IsFellerKernelSemigroup.integrable_dynkinProcess (hFeller : P.IsFellerKernelSemigroup)
    (f : hFeller.c0Semigroup.generatorDomain) (t : NNReal) (y : alpha) :
    Integrable (hFeller.dynkinProcess f t) (IsConservative.continuousProcess P hP y) :=
  Integrable.of_bound (hFeller.stronglyMeasurable_dynkinProcess f t).aestronglyMeasurable _
    (Eventually.of_forall (hFeller.norm_dynkinProcess_le f t))

/-- **The expectation of the Dynkin process is the initial value**: `E_y M u = f y` for every
time `u`.  This is Dynkin's formula at a deterministic time, rearranged. -/
theorem IsFellerKernelSemigroup.integral_dynkinProcess (hFeller : P.IsFellerKernelSemigroup)
    (hK : P.KolmogorovRegular hP) (f : hFeller.c0Semigroup.generatorDomain) (u : NNReal)
    (y : alpha) :
    ∫ omega, hFeller.dynkinProcess f u omega ∂(IsConservative.continuousProcess P hP y) =
      (f : C₀(alpha, ℝ)) y := by
  have hpos : Integrable (fun omega : ContinuousPath alpha ↦ (f : C₀(alpha, ℝ)) (omega u))
      (IsConservative.continuousProcess P hP y) :=
    Integrable.of_bound
      (StronglyMeasurable.aestronglyMeasurable
        ((f : C₀(alpha, ℝ)).continuous.comp_stronglyMeasurable
          (ContinuousPath.measurable_coordinateProcess (alpha := alpha) u).stronglyMeasurable))
      ‖(f : C₀(alpha, ℝ))‖ (Eventually.of_forall fun omega ↦ norm_c0_apply_le _ _)
  have hcorr : Integrable (fun omega : ContinuousPath alpha ↦
      ∫ s in (0 : ℝ)..u, (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s)))
      (IsConservative.continuousProcess P hP y) := by
    refine Integrable.of_bound
      ((hFeller.stronglyMeasurable_integral_generator f u).mono
        ((ContinuousPath.canonicalFiltration (alpha := alpha)).le u)).aestronglyMeasurable
      ((u : ℝ) * ‖hFeller.c0Semigroup.generator f‖) (Eventually.of_forall fun omega ↦ ?_)
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := (u : ℝ)) (C := ‖hFeller.c0Semigroup.generator f‖)
      (f := fun s : ℝ ↦ (hFeller.c0Semigroup.generator f) (omega (Real.toNNReal s)))
      (fun s _ ↦ norm_c0_apply_le _ _)
    rwa [sub_zero, abs_of_nonneg u.coe_nonneg, mul_comm] at h
  have hdynkin := hFeller.integral_eval_sub_eq_integral_integral_generator P hP hK f u y
  simp only [IsFellerKernelSemigroup.dynkinProcess_apply]
  rw [integral_sub hpos hcorr]
  linarith only [hdynkin]

end Expectation

section Martingale

/-- **The Dynkin martingale.**  For a conservative, Kolmogorov-regular Feller semigroup `P` and
`f` in the generator domain of its `C₀` semigroup, the Dynkin process

  `M t omega = f (omega t) - ∫₀ᵗ (L f) (omega s) ds`

is a martingale for the canonical filtration under the continuous-path process of `P` started at
any point `x`. -/
theorem IsFellerKernelSemigroup.martingale_dynkinProcess (hFeller : P.IsFellerKernelSemigroup)
    (hK : P.KolmogorovRegular hP) (f : hFeller.c0Semigroup.generatorDomain) (x : alpha) :
    Martingale (hFeller.dynkinProcess f)
      (ContinuousPath.canonicalFiltration (alpha := alpha))
      (IsConservative.continuousProcess P hP x) := by
  refine ⟨hFeller.adapted_dynkinProcess f, fun s t hst ↦ ?_⟩
  have hdecomp : hFeller.dynkinProcess f t =
      (fun omega : ContinuousPath alpha ↦
          hFeller.dynkinProcess f s omega - (f : C₀(alpha, ℝ)) (omega s)) +
        fun omega : ContinuousPath alpha ↦
          hFeller.dynkinProcess f (t - s) (ContinuousPath.shift s omega) := by
    funext omega
    exact hFeller.dynkinProcess_eq_add_shift f s t hst omega
  have hmeasA : StronglyMeasurable[ContinuousPath.canonicalFiltration (alpha := alpha) s]
      (fun omega : ContinuousPath alpha ↦
        hFeller.dynkinProcess f s omega - (f : C₀(alpha, ℝ)) (omega s)) :=
    (hFeller.stronglyMeasurable_dynkinProcess_canonicalFiltration f s).sub
      ((f : C₀(alpha, ℝ)).continuous.comp_stronglyMeasurable
        (ContinuousPath.measurable_coordinateProcess_canonicalFiltration
          (alpha := alpha) s).stronglyMeasurable)
  have hintA : Integrable (fun omega : ContinuousPath alpha ↦
      hFeller.dynkinProcess f s omega - (f : C₀(alpha, ℝ)) (omega s))
      (IsConservative.continuousProcess P hP x) := by
    refine Integrable.of_bound
      (hmeasA.mono
        ((ContinuousPath.canonicalFiltration (alpha := alpha)).le s)).aestronglyMeasurable
      (‖(f : C₀(alpha, ℝ))‖ + (s : ℝ) * ‖hFeller.c0Semigroup.generator f‖ +
        ‖(f : C₀(alpha, ℝ))‖) (Eventually.of_forall fun omega ↦ ?_)
    exact (norm_sub_le _ _).trans
      (add_le_add (hFeller.norm_dynkinProcess_le f s omega) (norm_c0_apply_le _ _))
  have hmeasF : StronglyMeasurable (hFeller.dynkinProcess f (t - s)) :=
    hFeller.stronglyMeasurable_dynkinProcess f (t - s)
  have hintB : Integrable (fun omega : ContinuousPath alpha ↦
      hFeller.dynkinProcess f (t - s) (ContinuousPath.shift s omega))
      (IsConservative.continuousProcess P hP x) :=
    Integrable.of_bound
      (hmeasF.comp_measurable
        (ContinuousPath.measurable_shift_fixed (alpha := alpha) s)).aestronglyMeasurable
      _ (Eventually.of_forall fun omega ↦
        hFeller.norm_dynkinProcess_le f (t - s) (ContinuousPath.shift s omega))
  have hcondA := condExp_of_stronglyMeasurable
    ((ContinuousPath.canonicalFiltration (alpha := alpha)).le s) hmeasA hintA
  have hcondB := hFeller.continuousProcess_condExp_shift P hP hK x s
    (hFeller.dynkinProcess f (t - s)) hmeasF
    (‖(f : C₀(alpha, ℝ))‖ + ((t - s : NNReal) : ℝ) * ‖hFeller.c0Semigroup.generator f‖)
    (hFeller.norm_dynkinProcess_le f (t - s))
  have hcondB' : (IsConservative.continuousProcess P hP x)[fun omega ↦
      hFeller.dynkinProcess f (t - s) (ContinuousPath.shift s omega)|
        ContinuousPath.canonicalFiltration (alpha := alpha) s] =ᵐ[
      IsConservative.continuousProcess P hP x]
      fun omega : ContinuousPath alpha ↦ (f : C₀(alpha, ℝ)) (omega s) := by
    refine hcondB.trans (Eventually.of_forall fun omega ↦ ?_)
    exact hFeller.integral_dynkinProcess hP hK f (t - s) (omega s)
  rw [hdecomp]
  refine (condExp_add hintA hintB _).trans ?_
  rw [hcondA]
  refine (EventuallyEq.add (EventuallyEq.refl _ _) hcondB').trans
    (Eventually.of_forall fun omega ↦ ?_)
  change hFeller.dynkinProcess f s omega - (f : C₀(alpha, ℝ)) (omega s) +
    (f : C₀(alpha, ℝ)) (omega s) = hFeller.dynkinProcess f s omega
  ring

end Martingale

end Process

end

end MarkovProcess.SubMarkovKernelSemigroup

end PortComputability
