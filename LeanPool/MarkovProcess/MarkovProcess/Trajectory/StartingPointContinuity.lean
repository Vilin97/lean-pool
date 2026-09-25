/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Feller.FiniteSetCompactTestContinuity
public import LeanPool.MarkovProcess.MarkovProcess.Kernel.WeakConvergence
public import LeanPool.MarkovProcess.MarkovProcess.Main
public import LeanPool.MarkovProcess.MarkovProcess.Parameterized.ContinuousProcessProperties
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.MeasureTheory.Measure.Tight


/-!
# Measurable and continuous dependence on the starting point

Two regularity statements for the continuous-path process of a conservative sub-Markov kernel
semigroup, both in the starting point.

*Measurability.*  For a strongly measurable functional `F` of the path, the expectation
`x ↦ ∫ F d(continuousProcess P hP x)` is strongly measurable, hence measurable into a Borel
target: `IsConservative.stronglyMeasurable_integral_continuousProcess` and
`IsConservative.measurable_integral_continuousProcess`.  The same holds for the two functionals
that the strong Markov property produces, the shifted path and the state at a finite stopping
time: `IsConservative.measurable_integral_shift_stoppingTime_continuousProcess` and
`IsConservative.measurable_integral_eval_stoppingTime_continuousProcess`.

*Continuity.*  For a Feller semigroup the finite-dimensional laws depend weakly continuously on
the starting point: `IsFellerKernelSemigroup.continuous_integral_boundedContinuous_finiteSetKernel`
upgrades compact-test continuity to all bounded continuous test functions.  The
upgrade is a tightness argument: a finite-dimensional law on a Polish coordinate space is tight,
so a compactly supported continuous cutoff `g` with `1_K ≤ g ≤ 1` captures all but `epsilon` of the
mass at the reference starting point, the truncated integral `∫ f * g` is continuous by the
compact-test theorem, and the discarded part is bounded by `‖f‖ * (1 - ∫ g)`, itself continuous
and small.  On the process this reads as continuity of cylinder expectations,
`IsFellerKernelSemigroup.continuous_integral_finsetEvaluation_continuousProcess`, with the
one-time case `IsFellerKernelSemigroup.continuous_integral_eval_continuousProcess`.

Nothing here asserts weak continuity of the full path law `x ↦ continuousProcess P hP x` on path
space; that needs tightness on path space itself, which is not proved here.  No statement covers
a stopping time that can be infinite.
-/

@[expose] public section

noncomputable section PortComputability

open Filter MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction CompactlySupported NNReal

namespace MarkovProcess


namespace SubMarkovKernelSemigroup

section BoundedContinuousTest

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [SecondCountableTopology alpha] [LocallyCompactSpace alpha]

/-- **Weak continuity of the finite-dimensional laws in the starting point.**  For a conservative
Feller semigroup on a locally compact Polish state space, the integral of a *bounded continuous*
test function against the finite-set kernel `finiteSetKernel P I` is a continuous function of the
starting point.

The compact-test version
`IsFellerKernelSemigroup.continuous_integral_compactlySupported_finiteSetKernel` only sees
compactly supported tests; conservativity supplies the missing total mass one, and tightness of
the finite-dimensional law at the reference point turns vague continuity into weak continuity. -/
theorem IsFellerKernelSemigroup.continuous_integral_boundedContinuous_finiteSetKernel
    {P : SubMarkovKernelSemigroup alpha} (hFeller : P.IsFellerKernelSemigroup)
    (hP : P.IsConservative) (I : Finset NNReal) (f : (I → alpha) →ᵇ ℝ) :
    Continuous fun x ↦ ∫ path, f path ∂finiteSetKernel P I x := by
  let : IsMarkovKernel (finiteSetKernel P I) := hP.isMarkovKernel_finiteSetKernel P I
  have hcompact : ∀ g : C_c(I → alpha, ℝ),
      Continuous fun x ↦ ∫ path, g path ∂finiteSetKernel P I x :=
    fun g ↦ hFeller.continuous_integral_compactlySupported_finiteSetKernel hP I g
  refine continuous_iff_continuousAt.mpr fun x0 ↦ Metric.tendsto_nhds.mpr fun eps heps ↦ ?_
  have hnorm : (0 : ℝ) ≤ ‖f‖ := norm_nonneg f
  have hdpos : 0 < eps / (3 * (‖f‖ + 1)) := by positivity
  obtain ⟨g, hg01, hgint⟩ :=
    exists_compactlySupported_one_sub_lt_integral (finiteSetKernel P I x0) hdpos
  have hsmall : ‖f‖ * (eps / (3 * (‖f‖ + 1))) ≤ eps / 3 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 3)]
    have hexpand : eps * (3 * (‖f‖ + 1)) - ‖f‖ * eps * 3 = 3 * eps := by ring
    linarith only [hexpand, heps]
  have htrunc : ∀ᶠ x in nhds x0,
      |(∫ path, (f • g) path ∂finiteSetKernel P I x)
        - ∫ path, (f • g) path ∂finiteSetKernel P I x0| < eps / 3 := by
    have h := Metric.tendsto_nhds.mp ((hcompact (f • g)).continuousAt (x := x0)) (eps / 3)
      (by positivity)
    simpa only [Real.dist_eq] using h
  have hmass : ∀ᶠ x in nhds x0,
      1 - (∫ path, g path ∂finiteSetKernel P I x) < eps / (3 * (‖f‖ + 1)) :=
    Tendsto.eventually_lt_const (by simp only [Pi.sub_apply]; linarith only [hgint])
      ((continuous_const.sub (hcompact g)).continuousAt (x := x0))
  filter_upwards [htrunc, hmass] with x hxtrunc hxmass
  rw [Real.dist_eq]
  have hkey := abs_integral_sub_integral_smul_le (finiteSetKernel P I x) f g hg01
  have hkey0 := abs_integral_sub_integral_smul_le (finiteSetKernel P I x0) f g hg01
  have hbound : ‖f‖ * (1 - ∫ path, g path ∂finiteSetKernel P I x)
      ≤ ‖f‖ * (eps / (3 * (‖f‖ + 1))) :=
    mul_le_mul_of_nonneg_left hxmass.le hnorm
  have hbound0 : ‖f‖ * (1 - ∫ path, g path ∂finiteSetKernel P I x0)
      ≤ ‖f‖ * (eps / (3 * (‖f‖ + 1))) :=
    mul_le_mul_of_nonneg_left (by linarith only [hgint]) hnorm
  have htri := abs_sub_le (∫ path, f path ∂finiteSetKernel P I x)
    (∫ path, (f • g) path ∂finiteSetKernel P I x) (∫ path, f path ∂finiteSetKernel P I x0)
  have htri0 := abs_sub_le (∫ path, (f • g) path ∂finiteSetKernel P I x)
    (∫ path, (f • g) path ∂finiteSetKernel P I x0) (∫ path, f path ∂finiteSetKernel P I x0)
  have hcomm := abs_sub_comm (∫ path, (f • g) path ∂finiteSetKernel P I x0)
    (∫ path, f path ∂finiteSetKernel P I x0)
  linarith only [hkey, hkey0, hxtrunc, hbound, hbound0, hsmall, htri, htri0, hcomm]

end BoundedContinuousTest

section Process

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

section Measurability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Expectations of the process are strongly measurable in the starting point.**  For a
strongly measurable functional `F` on continuous paths, `x ↦ ∫ F d(continuousProcess P hP x)` is
strongly measurable; this is the kernel integral of a strongly measurable function, so no
regularity hypothesis on `P` beyond conservativity is needed. -/
theorem IsConservative.stronglyMeasurable_integral_continuousProcess
    (F : ContinuousPath alpha → E) (hF : StronglyMeasurable F) :
    StronglyMeasurable fun x ↦ ∫ eta, F eta ∂(continuousProcess P hP x) :=
  hF.integral_kernel (κ := continuousProcess P hP)

variable [MeasurableSpace E] [BorelSpace E]

/-- **Expectations of the process are measurable in the starting point.**  Borel-target form of
`stronglyMeasurable_integral_continuousProcess`: the map `x ↦ ∫ F d(continuousProcess P hP x)` is
measurable for every strongly measurable functional `F` on continuous paths. -/
theorem IsConservative.measurable_integral_continuousProcess
    (F : ContinuousPath alpha → E) (hF : StronglyMeasurable F) :
    Measurable fun x ↦ ∫ eta, F eta ∂(continuousProcess P hP x) :=
  (IsConservative.stronglyMeasurable_integral_continuousProcess P hP F hF).measurable

/-- Expectations of a functional of the path shifted at a finite stopping time are measurable in
the starting point.  This is the measurability that makes the right-hand side of the strong
Markov property a legitimate integrand. -/
theorem IsConservative.measurable_integral_shift_stoppingTime_continuousProcess
    (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal)))
    (F : ContinuousPath alpha → E) (hF : StronglyMeasurable F) :
    Measurable fun x ↦ ∫ omega, F (ContinuousPath.shift (T omega) omega)
      ∂(continuousProcess P hP x) :=
  IsConservative.measurable_integral_continuousProcess P hP _
    (hF.comp_measurable (ContinuousPath.measurable_shift_stoppingTime T hT))

/-- Expectations of a functional of the state at a finite stopping time are measurable in the
starting point. -/
theorem IsConservative.measurable_integral_eval_stoppingTime_continuousProcess
    (T : ContinuousPath alpha → NNReal)
    (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
      (fun omega ↦ (T omega : WithTop NNReal)))
    (G : alpha → E) (hG : StronglyMeasurable G) :
    Measurable fun x ↦ ∫ omega, G (omega (T omega)) ∂(continuousProcess P hP x) :=
  IsConservative.measurable_integral_continuousProcess P hP _
    (hG.comp_measurable (ContinuousPath.measurable_eval_stoppingTime_borel T hT))

end Measurability

section Continuity

variable [LocallyCompactSpace alpha]

/-- **Continuity of cylinder expectations in the starting point.**  For a conservative Feller
semigroup with a continuous modification, the expectation of a bounded continuous function of the
coordinates at a finite set `I` of times is a continuous function of the starting point.  This is
the process form of `continuous_integral_boundedContinuous_finiteSetKernel`, transported through
the finite-dimensional distributions of `continuousProcess P hP`. -/
theorem IsFellerKernelSemigroup.continuous_integral_finsetEvaluation_continuousProcess
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP) (I : Finset NNReal)
    (f : (I → alpha) →ᵇ ℝ) :
    Continuous fun x ↦ ∫ omega, f (ContinuousPath.finsetEvaluation I omega)
      ∂(continuousProcess P hP x) := by
  refine (hFeller.continuous_integral_boundedContinuous_finiteSetKernel hP I f).congr fun x ↦ ?_
  have hmap : ((continuousProcess P hP) x).map (ContinuousPath.finsetEvaluation I) =
      finiteSetKernel P I x := by
    rw [← Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I),
      hFeller.continuousProcess_map_finiteEvaluation P hP hK I]
  rw [← hmap, integral_map (ContinuousPath.measurable_finsetEvaluation I).aemeasurable
    f.continuous.aestronglyMeasurable]

/-- Continuity of a one-time expectation in the starting point: for a bounded continuous `g` on
the state space and a nonnegative time `t`, the expectation of `g (omega t)` under the process is
continuous in the starting point. -/
theorem IsFellerKernelSemigroup.continuous_integral_eval_continuousProcess
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP) (t : NNReal)
    (g : alpha →ᵇ ℝ) :
    Continuous fun x ↦ ∫ omega, g (omega t) ∂(continuousProcess P hP x) := by
  have hmem : t ∈ ({t} : Finset NNReal) := Finset.mem_singleton_self t
  have h := hFeller.continuous_integral_finsetEvaluation_continuousProcess P hP hK {t}
    (g.compContinuous ⟨fun path ↦ path ⟨t, hmem⟩, continuous_apply _⟩)
  exact h.congr fun x ↦ rfl

end Continuity

end Process

end SubMarkovKernelSemigroup

end MarkovProcess

end PortComputability
