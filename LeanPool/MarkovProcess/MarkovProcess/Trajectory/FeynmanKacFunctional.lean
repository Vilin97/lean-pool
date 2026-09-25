/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Analysis.ExpPrimitive
public import LeanPool.MarkovProcess.MarkovProcess.Kernel.Operator
public import LeanPool.MarkovProcess.MarkovProcess.Trajectory.DynkinMartingale


/-!
# Feynman--Kac functionals and semigroups

For the continuous-path process of a conservative Feller semigroup, this file constructs the
Feynman--Kac operators associated with a bounded nonnegative measurable potential.  It proves
measurability and bounds for the accumulated potential and operators, the identity at time zero,
and the Feynman--Kac semigroup law.

Main results: `feynmanKacAdditiveFunctional`,
`stronglyMeasurable_feynmanKacAdditiveFunctional`,
`continuous_feynmanKacAdditiveFunctional`, `feynmanKacAdditiveFunctional_add`,
`IsConservative.feynmanKac`, `IsConservative.feynmanKac_zero`,
`IsConservative.measurable_feynmanKac`, `IsConservative.feynmanKac_nonneg`,
`IsConservative.feynmanKac_le`, `IsConservative.feynmanKac_add_apply`,
`IsConservative.feynmanKac_smul_apply`, and `IsFellerKernelSemigroup.feynmanKac_add`.

The resolvent and perturbation identities are developed in `Trajectory/FeynmanKacResolvent.lean`.
-/

@[expose] public section

noncomputable section PortComputability

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MarkovProcess.SubMarkovKernelSemigroup

section

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]

/-- The accumulated potential along a continuous path up to time `t`. -/
def feynmanKacAdditiveFunctional (q : alpha → ℝ) (t : NNReal)
    (omega : ContinuousPath alpha) : ℝ :=
  ∫ s in (0 : ℝ)..t, q (omega (Real.toNNReal s))

omit [MeasurableSpace alpha] [BorelSpace alpha] in
/-- The accumulated potential is unfolded as its path integral. -/
theorem feynmanKacAdditiveFunctional_apply (q : alpha → ℝ) (t : NNReal)
    (omega : ContinuousPath alpha) :
    feynmanKacAdditiveFunctional q t omega =
      ∫ s in (0 : ℝ)..t, q (omega (Real.toNNReal s)) :=
  rfl

variable [SecondCountableTopology alpha]

/-- The accumulated potential at a deterministic time is strongly measurable for the canonical
filtration at that time. -/
theorem stronglyMeasurable_feynmanKacAdditiveFunctional_canonicalFiltration {q : alpha → ℝ}
    (hq : Measurable q) (t : NNReal) :
    StronglyMeasurable[ContinuousPath.canonicalFiltration (alpha := alpha) t]
      (feynmanKacAdditiveFunctional q t) := by
  have hclamp := ContinuousPath.measurable_clampedCoordinate (alpha := alpha) t
  have hprod : StronglyMeasurable[ContinuousPath.canonicalFiltration (alpha := alpha) t]
      (fun omega : ContinuousPath alpha ↦
      ∫ s, q (omega (min (Real.toNNReal s) t))
        ∂(volume.restrict (Ioc (0 : ℝ) t))) :=
    stronglyMeasurable_integral_prod (volume.restrict (Ioc (0 : ℝ) t))
      ((hq.comp hclamp).stronglyMeasurable)
  have hfun : feynmanKacAdditiveFunctional q t = fun omega : ContinuousPath alpha ↦
      ∫ s, q (omega (min (Real.toNNReal s) t))
        ∂(volume.restrict (Ioc (0 : ℝ) t)) := by
    funext omega
    rw [feynmanKacAdditiveFunctional_apply, intervalIntegral.integral_of_le t.coe_nonneg]
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs ↦ ?_
    rw [min_eq_left (Real.toNNReal_le_iff_le_coe.mpr hs.2)]
  rw [hfun]
  exact hprod

/-- The accumulated potential at a deterministic time is strongly measurable on path space. -/
theorem stronglyMeasurable_feynmanKacAdditiveFunctional {q : alpha → ℝ}
    (hq : Measurable q) (t : NNReal) :
    StronglyMeasurable (feynmanKacAdditiveFunctional q t) :=
  (stronglyMeasurable_feynmanKacAdditiveFunctional_canonicalFiltration hq t).mono
    ((ContinuousPath.canonicalFiltration (alpha := alpha)).le t)

/-- The accumulated potential is jointly strongly measurable in time and path. -/
theorem stronglyMeasurable_feynmanKacAdditiveFunctional_joint {q : alpha → ℝ}
    (hq : Measurable q) :
    StronglyMeasurable fun p : NNReal × ContinuousPath alpha ↦
      feynmanKacAdditiveFunctional q p.1 p.2 := by
  let phi : (NNReal × ContinuousPath alpha) × ℝ → ℝ := fun p ↦
    if 0 < p.2 ∧ p.2 ≤ (p.1.1 : ℝ)
    then q (p.1.2 (Real.toNNReal p.2)) else 0
  have hset : MeasurableSet {p : (NNReal × ContinuousPath alpha) × ℝ |
      0 < p.2 ∧ p.2 ≤ (p.1.1 : ℝ)} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd
        (NNReal.continuous_coe.measurable.comp (measurable_fst.comp measurable_fst)))
  have heval : Measurable fun p : (NNReal × ContinuousPath alpha) × ℝ ↦
      q (p.1.2 (Real.toNNReal p.2)) := by
    have hpath : Measurable fun p : (NNReal × ContinuousPath alpha) × ℝ ↦
        p.1.2 (Real.toNNReal p.2) :=
      (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
        ((measurable_real_toNNReal.comp measurable_snd).prodMk
          (measurable_snd.comp measurable_fst))
    exact hq.comp hpath
  have hphi : StronglyMeasurable phi := by
    exact (heval.ite hset measurable_const).stronglyMeasurable
  have hint : StronglyMeasurable fun p : NNReal × ContinuousPath alpha ↦
      ∫ s, phi (p, s) := hphi.integral_prod_right'
  have heq : (fun p : NNReal × ContinuousPath alpha ↦
      feynmanKacAdditiveFunctional q p.1 p.2) = fun p ↦ ∫ s, phi (p, s) := by
    funext p
    rw [feynmanKacAdditiveFunctional_apply,
      intervalIntegral.integral_of_le p.1.coe_nonneg]
    change (∫ s in Ioc (0 : ℝ) (p.1 : ℝ), q (p.2 (Real.toNNReal s))) =
      ∫ s, phi (p, s)
    rw [← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    exact Eventually.of_forall fun s ↦ by
      by_cases hs : s ∈ Ioc (0 : ℝ) (p.1 : ℝ)
      · have hs' : 0 < s ∧ s ≤ (p.1 : ℝ) := hs
        simp only [indicator_of_mem hs, phi, ite_eq_left hs']
      · have hs' : ¬(0 < s ∧ s ≤ (p.1 : ℝ)) := hs
        simp only [indicator_of_notMem hs, phi, ite_eq_right hs']
  rw [heq]
  exact hint

omit [SecondCountableTopology alpha] in
/-- A bounded measurable potential is interval integrable along every continuous path. -/
private theorem intervalIntegrable_potential_path {q : alpha → ℝ} (hq : Measurable q)
    {C : ℝ} (hq0 : ∀ y, 0 ≤ q y) (hqC : ∀ y, q y ≤ C)
    (omega : ContinuousPath alpha) (a b : ℝ) :
    IntervalIntegrable (fun s : ℝ ↦ q (omega (Real.toNNReal s))) volume a b := by
  rw [intervalIntegrable_iff]
  refine IntegrableOn.of_bound (by simpa only [uIoc] using
      (measure_Ioc_lt_top : volume (Ioc (min a b) (max a b)) < ∞))
    (((hq.comp (omega.continuous.measurable.comp measurable_real_toNNReal)).stronglyMeasurable
      ).aestronglyMeasurable.restrict) C ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with s _
  rw [Real.norm_eq_abs, abs_of_nonneg (hq0 _)]
  exact hqC _

omit [SecondCountableTopology alpha] in
/-- Along every path, the accumulated potential is continuous in its time argument. -/
theorem continuous_feynmanKacAdditiveFunctional {q : alpha → ℝ} (hq : Measurable q)
    {C : ℝ} (hq0 : ∀ y, 0 ≤ q y) (hqC : ∀ y, q y ≤ C)
    (omega : ContinuousPath alpha) :
    Continuous fun t : NNReal ↦ feynmanKacAdditiveFunctional q t omega := by
  have hcont : Continuous fun t : ℝ ↦
      ∫ s in (0 : ℝ)..t, q (omega (Real.toNNReal s)) :=
    intervalIntegral.continuous_primitive
      (fun a b ↦ intervalIntegrable_potential_path hq hq0 hqC omega a b) 0
  exact hcont.comp NNReal.continuous_coe

omit [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] in
/-- The accumulated potential is nonnegative. -/
theorem feynmanKacAdditiveFunctional_nonneg {q : alpha → ℝ} (hq0 : ∀ y, 0 ≤ q y)
    (t : NNReal) (omega : ContinuousPath alpha) :
    0 ≤ feynmanKacAdditiveFunctional q t omega := by
  rw [feynmanKacAdditiveFunctional_apply]
  exact intervalIntegral.integral_nonneg t.coe_nonneg fun s _ ↦ hq0 _

omit [SecondCountableTopology alpha] in
/-- The accumulated potential is at most the uniform potential bound times elapsed time. -/
theorem feynmanKacAdditiveFunctional_le {q : alpha → ℝ} {C : ℝ}
    (hq : Measurable q) (hq0 : ∀ y, 0 ≤ q y) (hqC : ∀ y, q y ≤ C)
    (t : NNReal) (omega : ContinuousPath alpha) :
    feynmanKacAdditiveFunctional q t omega ≤ C * t := by
  rw [feynmanKacAdditiveFunctional_apply]
  calc
    (∫ s in (0 : ℝ)..t, q (omega (Real.toNNReal s))) ≤ ∫ _s in (0 : ℝ)..t, C := by
      apply intervalIntegral.integral_mono_on t.coe_nonneg
        (intervalIntegrable_potential_path hq hq0 hqC omega 0 t)
        continuousOn_const.intervalIntegrable
      intro s _
      exact hqC _
    _ = C * t := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      ring

omit [SecondCountableTopology alpha] in
/-- Accumulated potentials add under deterministic path shifts. -/
theorem feynmanKacAdditiveFunctional_add {q : alpha → ℝ} (hq : Measurable q)
    {C : ℝ} (hq0 : ∀ y, 0 ≤ q y) (hqC : ∀ y, q y ≤ C)
    (s t : NNReal) (omega : ContinuousPath alpha) :
    feynmanKacAdditiveFunctional q (s + t) omega =
      feynmanKacAdditiveFunctional q s omega +
        feynmanKacAdditiveFunctional q t (ContinuousPath.shift s omega) := by
  let g : ℝ → ℝ := fun u ↦ q (omega (Real.toNNReal u))
  have hshift : (∫ u in (0 : ℝ)..(t : ℝ), q (omega (s + Real.toNNReal u))) =
      ∫ v in (s : ℝ)..((s + t : NNReal) : ℝ), g v := by
    have hcongr : (∫ u in (0 : ℝ)..(t : ℝ), q (omega (s + Real.toNNReal u))) =
        ∫ u in (0 : ℝ)..(t : ℝ), g (u + s) := by
      refine intervalIntegral.integral_congr fun u hu ↦ ?_
      have hu0 : 0 ≤ u := by
        rw [uIcc_of_le t.coe_nonneg] at hu
        exact hu.1
      have hcoe : Real.toNNReal (u + s) = s + Real.toNNReal u := by
        apply NNReal.coe_injective
        rw [NNReal.coe_add, Real.coe_toNNReal u hu0,
          Real.coe_toNNReal _ (add_nonneg hu0 s.coe_nonneg)]
        ring
      simp only [g]
      rw [hcoe]
    rw [hcongr, intervalIntegral.integral_comp_add_right g (s : ℝ), zero_add]
    congr 1
    simp only [NNReal.coe_add, add_comm]
  have hsplit : (∫ v in (0 : ℝ)..(s : ℝ), g v) +
      (∫ v in (s : ℝ)..((s + t : NNReal) : ℝ), g v) =
        ∫ v in (0 : ℝ)..((s + t : NNReal) : ℝ), g v :=
    intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_potential_path hq hq0 hqC omega 0 s)
      (intervalIntegrable_potential_path hq hq0 hqC omega s (s + t))
  simp only [feynmanKacAdditiveFunctional_apply, ContinuousPath.shift_apply]
  change (∫ v in (0 : ℝ)..((s + t : NNReal) : ℝ), g v) =
    (∫ v in (0 : ℝ)..(s : ℝ), g v) +
      ∫ u in (0 : ℝ)..(t : ℝ), q (omega (s + Real.toNNReal u))
  rw [hshift]
  exact hsplit.symm

omit [SecondCountableTopology alpha] in
/-- The accumulated potential is monotone in time for a nonnegative potential. -/
theorem feynmanKacAdditiveFunctional_mono {q : alpha → ℝ} (hq : Measurable q)
    {C : ℝ} (hq0 : ∀ y, 0 ≤ q y) (hqC : ∀ y, q y ≤ C)
    {s t : NNReal} (hst : s ≤ t) (omega : ContinuousPath alpha) :
    feynmanKacAdditiveFunctional q s omega ≤ feynmanKacAdditiveFunctional q t omega := by
  rw [← add_tsub_cancel_of_le hst,
    feynmanKacAdditiveFunctional_add hq hq0 hqC]
  exact le_add_of_nonneg_right
    (feynmanKacAdditiveFunctional_nonneg hq0 (t - s) (ContinuousPath.shift s omega))

omit [SecondCountableTopology alpha] in
/-- The increment of the accumulated potential is the accumulated potential of the shifted
path. -/
theorem feynmanKacAdditiveFunctional_sub {q : alpha → ℝ} (hq : Measurable q)
    {C : ℝ} (hq0 : ∀ y, 0 ≤ q y) (hqC : ∀ y, q y ≤ C)
    {s t : NNReal} (hst : s ≤ t) (omega : ContinuousPath alpha) :
    feynmanKacAdditiveFunctional q t omega - feynmanKacAdditiveFunctional q s omega =
      feynmanKacAdditiveFunctional q (t - s) (ContinuousPath.shift s omega) := by
  have hadd := feynmanKacAdditiveFunctional_add hq hq0 hqC s (t - s) omega
  rw [add_tsub_cancel_of_le hst] at hadd
  linarith only [hadd]

omit [SecondCountableTopology alpha] in
/-- Pathwise exponential-integral identity for the accumulated potential. -/
theorem one_sub_exp_neg_feynmanKacAdditiveFunctional {q : alpha → ℝ}
    (hq : Measurable q) {C : ℝ} (hq0 : ∀ y, 0 ≤ q y)
    (hqC : ∀ y, q y ≤ C) (t : NNReal) (omega : ContinuousPath alpha) :
    1 - Real.exp (-feynmanKacAdditiveFunctional q t omega) =
      ∫ s in (0 : ℝ)..t, q (omega (Real.toNNReal s)) *
        Real.exp (-(feynmanKacAdditiveFunctional q t omega -
          feynmanKacAdditiveFunctional q (Real.toNNReal s) omega)) := by
  let a : ℝ → ℝ := fun s ↦ q (omega (Real.toNNReal s))
  have ha : IntegrableOn a (Icc (0 : ℝ) (t : ℝ)) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg).mp
      (intervalIntegrable_potential_path hq hq0 hqC omega 0 t)
  have hprimitive := intervalIntegral.integral_mul_exp_primitive
    (right_mem_Icc.mpr t.coe_nonneg) ha
    (fun s _ ↦ hq0 _) (fun s _ ↦ hqC _)
  have hscaled := congrArg (fun z : ℝ ↦ Real.exp
      (-feynmanKacAdditiveFunctional q t omega) * z) hprimitive
  change Real.exp (-feynmanKacAdditiveFunctional q t omega) *
      (∫ s in (0 : ℝ)..t, a s * Real.exp (∫ r in (0 : ℝ)..s, a r)) =
    Real.exp (-feynmanKacAdditiveFunctional q t omega) *
      (Real.exp (∫ r in (0 : ℝ)..t, a r) - 1) at hscaled
  rw [← intervalIntegral.integral_const_mul] at hscaled
  simp only [a, ← feynmanKacAdditiveFunctional_apply] at hscaled
  calc
    1 - Real.exp (-feynmanKacAdditiveFunctional q t omega) =
        Real.exp (-feynmanKacAdditiveFunctional q t omega) *
          (Real.exp (feynmanKacAdditiveFunctional q t omega) - 1) := by
            rw [mul_sub, ← Real.exp_add]
            simp only [neg_add_cancel, Real.exp_zero, mul_one]
    _ = ∫ s in (0 : ℝ)..t, Real.exp (-feynmanKacAdditiveFunctional q t omega) *
          (q (omega (Real.toNNReal s)) *
            Real.exp (∫ r in (0 : ℝ)..s, q (omega (Real.toNNReal r)))) := hscaled.symm
    _ = ∫ s in (0 : ℝ)..t, q (omega (Real.toNNReal s)) *
          Real.exp (-(feynmanKacAdditiveFunctional q t omega -
            feynmanKacAdditiveFunctional q (Real.toNNReal s) omega)) := by
            refine intervalIntegral.integral_congr fun s hs ↦ ?_
            have hs0 : 0 ≤ s := by
              rw [uIcc_of_le t.coe_nonneg] at hs
              exact hs.1
            have hAs : feynmanKacAdditiveFunctional q (Real.toNNReal s) omega =
                ∫ r in (0 : ℝ)..s, q (omega (Real.toNNReal r)) := by
              rw [feynmanKacAdditiveFunctional_apply, Real.coe_toNNReal s hs0]
            rw [hAs]
            rw [neg_sub, Real.exp_sub, Real.exp_neg]
            field_simp [Real.exp_ne_zero]

variable [CompleteSpace alpha] [Nonempty alpha] [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

/-- The real-valued Feynman--Kac operator associated with a potential. -/
def IsConservative.feynmanKac (q : alpha → ℝ) (t : NNReal) (f : alpha → ℝ)
    (x : alpha) : ℝ :=
  ∫ omega, Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t)
    ∂(IsConservative.continuousProcess P hP x)

omit [LocallyCompactSpace alpha] in
/-- The Feynman--Kac operator is unfolded as a path expectation. -/
theorem IsConservative.feynmanKac_apply (q : alpha → ℝ) (t : NNReal)
    (f : alpha → ℝ) (x : alpha) :
    IsConservative.feynmanKac P hP q t f x =
      ∫ omega, Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t)
        ∂(IsConservative.continuousProcess P hP x) :=
  rfl

omit [LocallyCompactSpace alpha] in
/-- At time zero the Feynman--Kac operator is the identity on measurable observables. -/
theorem IsConservative.feynmanKac_zero (hK : P.KolmogorovRegular hP)
    (q : alpha → ℝ) {f : alpha → ℝ} (hf : Measurable f) :
    IsConservative.feynmanKac P hP q 0 f = f := by
  funext x
  simp only [IsConservative.feynmanKac_apply, feynmanKacAdditiveFunctional,
    NNReal.coe_zero, intervalIntegral.integral_same, neg_zero, Real.exp_zero, one_mul]
  have heval := ContinuousPath.measurable_coordinateProcess (alpha := alpha) 0
  calc
    (∫ omega, f (omega 0) ∂(IsConservative.continuousProcess P hP x)) =
        ∫ y, f y ∂Measure.map (fun omega : ContinuousPath alpha ↦ omega 0)
          (IsConservative.continuousProcess P hP x) :=
      (integral_map heval.aemeasurable hf.stronglyMeasurable.aestronglyMeasurable).symm
    _ = ∫ y, f y ∂(Kernel.id x) := by
      change ∫ y, f y ∂Measure.map (ContinuousPath.coordinateProcess (alpha := alpha) 0)
        (IsConservative.continuousProcess P hP x) = _
      rw [← Kernel.map_apply _ heval]
      have hmap : (IsConservative.continuousProcess P hP).map
          (ContinuousPath.coordinateProcess (alpha := alpha) 0) = Kernel.id := by
        simpa only [ContinuousPath.coordinateProcess] using!
          IsConservative.continuousProcess_map_eval_zero P hP hK
      rw [hmap]
    _ = f x := by
      rw [Kernel.id_apply]
      exact integral_dirac' f x hf.stronglyMeasurable

omit [LocallyCompactSpace alpha] in
/-- The Feynman--Kac operator of a bounded measurable function is measurable in the starting
point. -/
theorem IsConservative.measurable_feynmanKac {q : alpha → ℝ} (hq : Measurable q)
    (t : NNReal) {f : alpha → ℝ} (hf : Measurable f) :
    Measurable (IsConservative.feynmanKac P hP q t f) := by
  have hpath : StronglyMeasurable (fun omega : ContinuousPath alpha ↦
      Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t)) :=
    (((stronglyMeasurable_feynmanKacAdditiveFunctional hq t).measurable.neg.exp).mul
      (hf.comp (ContinuousPath.measurable_coordinateProcess (alpha := alpha) t))).stronglyMeasurable
  exact hpath.integral_kernel.measurable

omit [LocallyCompactSpace alpha] in
/-- The Feynman--Kac operator preserves nonnegativity. -/
theorem IsConservative.feynmanKac_nonneg {q : alpha → ℝ} {t : NNReal}
    {f : alpha → ℝ} (hf0 : ∀ y, 0 ≤ f y) (x : alpha) :
    0 ≤ IsConservative.feynmanKac P hP q t f x := by
  exact integral_nonneg fun omega ↦ mul_nonneg (Real.exp_pos _).le (hf0 _)

omit [LocallyCompactSpace alpha] in
/-- A nonnegative Feynman--Kac operator is bounded by the uniform bound of its observable. -/
theorem IsConservative.feynmanKac_le {q : alpha → ℝ} (hq0 : ∀ y, 0 ≤ q y)
    {t : NNReal} {f : alpha → ℝ} (hf0 : ∀ y, 0 ≤ f y) {D : ℝ}
    (hfD : ∀ y, f y ≤ D) (x : alpha) :
    IsConservative.feynmanKac P hP q t f x ≤ D := by
  calc
    IsConservative.feynmanKac P hP q t f x ≤ ∫ _omega, D
        ∂(IsConservative.continuousProcess P hP x) := by
      apply integral_mono_of_nonneg
      · exact Eventually.of_forall fun omega ↦ mul_nonneg (Real.exp_pos _).le (hf0 _)
      · exact integrable_const D
      · exact Eventually.of_forall fun omega ↦ by
          calc
            Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t) ≤
                1 * f (omega t) := by
              exact mul_le_mul_of_nonneg_right
                ((Real.exp_le_one_iff).mpr
                  (neg_nonpos.mpr (feynmanKacAdditiveFunctional_nonneg hq0 t omega)))
                (hf0 _)
            _ ≤ D := by simpa only [one_mul] using hfD _
    _ = D := by simp only [integral_const, probReal_univ, one_smul]

omit [LocallyCompactSpace alpha] in
/-- The Feynman--Kac operator sends the constant one to a function bounded above by one. -/
theorem IsConservative.feynmanKac_one_le_one {q : alpha → ℝ} (hq0 : ∀ y, 0 ≤ q y)
    (t : NNReal) (x : alpha) :
    IsConservative.feynmanKac P hP q t (fun _ ↦ 1) x ≤ 1 :=
  IsConservative.feynmanKac_le P hP hq0 (fun _ ↦ zero_le_one) (fun _ ↦ le_rfl) x

/-- The nonnegative-extended-real Feynman--Kac operator. -/
def IsConservative.feynmanKacENNReal (q : alpha → ℝ) (t : NNReal)
    (f : alpha → ℝ≥0∞) (x : alpha) : ℝ≥0∞ :=
  ∫⁻ omega, ENNReal.ofReal (Real.exp (-feynmanKacAdditiveFunctional q t omega)) *
    f (omega t) ∂(IsConservative.continuousProcess P hP x)

omit [LocallyCompactSpace alpha] in
/-- The extended-real Feynman--Kac operator is unfolded as a path integral. -/
theorem IsConservative.feynmanKacENNReal_apply (q : alpha → ℝ) (t : NNReal)
    (f : alpha → ℝ≥0∞) (x : alpha) :
    IsConservative.feynmanKacENNReal P hP q t f x =
      ∫⁻ omega, ENNReal.ofReal (Real.exp (-feynmanKacAdditiveFunctional q t omega)) *
        f (omega t) ∂(IsConservative.continuousProcess P hP x) :=
  rfl

omit [LocallyCompactSpace alpha] in
/-- The extended-real Feynman--Kac operator is jointly measurable in time and starting point. -/
theorem IsConservative.measurable_feynmanKacENNReal_joint {q : alpha → ℝ}
    (hq : Measurable q) {f : alpha → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun p : NNReal × alpha ↦
      IsConservative.feynmanKacENNReal P hP q p.1 f p.2 := by
  let Q : Kernel alpha (ContinuousPath alpha) := IsConservative.continuousProcess P hP
  let Q' : Kernel (NNReal × alpha) (ContinuousPath alpha) := Kernel.comap Q Prod.snd measurable_snd
  have hA : Measurable fun p : (NNReal × alpha) × ContinuousPath alpha ↦
      feynmanKacAdditiveFunctional q p.1.1 p.2 :=
    (stronglyMeasurable_feynmanKacAdditiveFunctional_joint hq).measurable.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have heval : Measurable fun p : (NNReal × alpha) × ContinuousPath alpha ↦
      p.2 p.1.1 :=
    (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hint : Measurable fun p : (NNReal × alpha) × ContinuousPath alpha ↦
      ENNReal.ofReal (Real.exp (-feynmanKacAdditiveFunctional q p.1.1 p.2)) * f (p.2 p.1.1) :=
    (hA.neg.exp.ennreal_ofReal).mul (hf.comp heval)
  have hlin := hint.lintegral_kernel_prod_right' (κ := Q')
  simpa only [Q', Kernel.comap_apply, IsConservative.feynmanKacENNReal_apply] using hlin

omit [LocallyCompactSpace alpha] in
/-- The extended-real Feynman--Kac operator is measurable in the starting point. -/
theorem IsConservative.measurable_feynmanKacENNReal {q : alpha → ℝ} (hq : Measurable q)
    (t : NNReal) {f : alpha → ℝ≥0∞} (hf : Measurable f) :
    Measurable (IsConservative.feynmanKacENNReal P hP q t f) :=
  (IsConservative.measurable_feynmanKacENNReal_joint P hP hq hf).comp
    (measurable_const.prodMk measurable_id)

omit [LocallyCompactSpace alpha] in
/-- For nonnegative bounded real observables, the two versions of the Feynman--Kac operator agree
after applying `ENNReal.ofReal`. -/
theorem IsConservative.ofReal_feynmanKac_eq_feynmanKacENNReal {q : alpha → ℝ}
    (hq : Measurable q) (hq0 : ∀ y, 0 ≤ q y) (t : NNReal) {f : alpha → ℝ} (hf : Measurable f)
    (hf0 : ∀ y, 0 ≤ f y) {D : ℝ} (hfD : ∀ y, f y ≤ D) (x : alpha) :
    ENNReal.ofReal (IsConservative.feynmanKac P hP q t f x) =
      IsConservative.feynmanKacENNReal P hP q t (fun y ↦ ENNReal.ofReal (f y)) x := by
  let g : ContinuousPath alpha → ℝ := fun omega ↦
    Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t)
  have hg : Integrable g (IsConservative.continuousProcess P hP x) := by
    refine Integrable.of_bound ?_ D (Eventually.of_forall fun omega ↦ ?_)
    · exact ((((stronglyMeasurable_feynmanKacAdditiveFunctional hq t).measurable.neg.exp).mul
        (hf.comp (ContinuousPath.measurable_coordinateProcess
          (alpha := alpha) t))).stronglyMeasurable
          ).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hf0 _))]
      exact (mul_le_mul_of_nonneg_right
        ((Real.exp_le_one_iff).mpr
          (neg_nonpos.mpr (feynmanKacAdditiveFunctional_nonneg hq0 t omega))) (hf0 _)).trans
        (by simpa only [one_mul] using hfD _)
  rw [IsConservative.feynmanKac_apply, IsConservative.feynmanKacENNReal_apply,
    ofReal_integral_eq_lintegral_ofReal hg
      (Eventually.of_forall fun omega ↦ mul_nonneg (Real.exp_pos _).le (hf0 _))]
  refine lintegral_congr fun omega ↦ ?_
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le]

omit [LocallyCompactSpace alpha] in
/-- The path integrand defining a Feynman--Kac operator is integrable for a bounded observable
and a nonnegative potential. -/
theorem IsConservative.integrable_feynmanKac_integrand {q : alpha → ℝ}
    (hq : Measurable q) (hq0 : ∀ y, 0 ≤ q y) (t : NNReal) {f : alpha → ℝ}
    (hf : Measurable f) {D : ℝ} (hfD : ∀ y, |f y| ≤ D) (x : alpha) :
    Integrable (fun omega : ContinuousPath alpha ↦
      Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t))
      (IsConservative.continuousProcess P hP x) := by
  exact Integrable.of_bound
    (((((stronglyMeasurable_feynmanKacAdditiveFunctional hq t).measurable.neg.exp).mul
      (hf.comp (ContinuousPath.measurable_coordinateProcess (alpha := alpha) t))
      ).stronglyMeasurable).aestronglyMeasurable) D (Eventually.of_forall fun omega ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc
        Real.exp (-feynmanKacAdditiveFunctional q t omega) * |f (omega t)| ≤
            1 * |f (omega t)| := mul_le_mul_of_nonneg_right
              ((Real.exp_le_one_iff).mpr
                (neg_nonpos.mpr (feynmanKacAdditiveFunctional_nonneg hq0 t omega)))
              (abs_nonneg _)
        _ ≤ D := by simpa only [one_mul] using hfD _)

omit [LocallyCompactSpace alpha] in
/-- Feynman--Kac operators are additive on bounded measurable real observables. -/
theorem IsConservative.feynmanKac_add_apply {q : alpha → ℝ} (hq : Measurable q)
    (hq0 : ∀ y, 0 ≤ q y) (t : NNReal) {f g : alpha → ℝ}
    (hf : Measurable f) (hg : Measurable g) {D E : ℝ}
    (hfD : ∀ y, |f y| ≤ D) (hgE : ∀ y, |g y| ≤ E) :
    IsConservative.feynmanKac P hP q t (f + g) =
      IsConservative.feynmanKac P hP q t f + IsConservative.feynmanKac P hP q t g := by
  funext x
  change (∫ omega, Real.exp (-feynmanKacAdditiveFunctional q t omega) *
      (f + g) (omega t) ∂(IsConservative.continuousProcess P hP x)) =
    (∫ omega, Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t)
      ∂(IsConservative.continuousProcess P hP x)) +
    ∫ omega, Real.exp (-feynmanKacAdditiveFunctional q t omega) * g (omega t)
      ∂(IsConservative.continuousProcess P hP x)
  rw [← integral_add
      (IsConservative.integrable_feynmanKac_integrand P hP hq hq0 t hf hfD x)
      (IsConservative.integrable_feynmanKac_integrand P hP hq hq0 t hg hgE x)]
  apply integral_congr_ae
  exact Eventually.of_forall fun omega ↦ by
    simp only [Pi.add_apply]
    ring

omit [LocallyCompactSpace alpha] in
/-- Feynman--Kac operators are real homogeneous. -/
theorem IsConservative.feynmanKac_smul_apply (q : alpha → ℝ) (t : NNReal) (a : ℝ)
    (f : alpha → ℝ) :
    IsConservative.feynmanKac P hP q t (a • f) =
      a • IsConservative.feynmanKac P hP q t f := by
  funext x
  change (∫ omega, Real.exp (-feynmanKacAdditiveFunctional q t omega) *
      (a • f) (omega t) ∂(IsConservative.continuousProcess P hP x)) =
    a • (∫ omega, Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t)
      ∂(IsConservative.continuousProcess P hP x))
  rw [← integral_smul]
  apply integral_congr_ae
  exact Eventually.of_forall fun omega ↦ by
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

omit [LocallyCompactSpace alpha] in
/-- A Feynman--Kac operator contracts the uniform bound of a bounded observable when
the potential is nonnegative. -/
theorem IsConservative.norm_feynmanKac_le {q : alpha → ℝ} (hq0 : ∀ y, 0 ≤ q y)
    (t : NNReal) {f : alpha → ℝ} {D : ℝ} (hfD : ∀ y, |f y| ≤ D) (x : alpha) :
    |IsConservative.feynmanKac P hP q t f x| ≤ D := by
  rw [← Real.norm_eq_abs]
  calc
    ‖IsConservative.feynmanKac P hP q t f x‖ ≤ ∫ _omega, D
        ∂(IsConservative.continuousProcess P hP x) := by
      rw [IsConservative.feynmanKac_apply]
      apply norm_integral_le_of_norm_le (integrable_const D)
      exact Eventually.of_forall fun omega ↦ by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        exact (mul_le_mul_of_nonneg_right
          ((Real.exp_le_one_iff).mpr
            (neg_nonpos.mpr (feynmanKacAdditiveFunctional_nonneg hq0 t omega)))
          (abs_nonneg _)).trans (by simpa only [one_mul] using hfD _)
    _ = D := by simp only [integral_const, probReal_univ, one_smul]

omit [LocallyCompactSpace alpha] in
/-- A Feynman--Kac operator applied to a bounded measurable observable is jointly measurable in
time and starting point. -/
theorem IsConservative.measurable_feynmanKac_joint {q : alpha → ℝ}
    (hq : Measurable q) : ∀ {f : alpha → ℝ}, Measurable f →
    Measurable fun p : NNReal × alpha ↦
      IsConservative.feynmanKac P hP q p.1 f p.2 := by
  intro f hf
  let Q : Kernel alpha (ContinuousPath alpha) := IsConservative.continuousProcess P hP
  let Q' : Kernel (NNReal × alpha) (ContinuousPath alpha) :=
    Kernel.comap Q Prod.snd measurable_snd
  have hA : Measurable fun p : (NNReal × alpha) × ContinuousPath alpha ↦
      feynmanKacAdditiveFunctional q p.1.1 p.2 :=
    (stronglyMeasurable_feynmanKacAdditiveFunctional_joint hq).measurable.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have heval : Measurable fun p : (NNReal × alpha) × ContinuousPath alpha ↦
      p.2 p.1.1 :=
    (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hint : StronglyMeasurable fun p : (NNReal × alpha) × ContinuousPath alpha ↦
      Real.exp (-feynmanKacAdditiveFunctional q p.1.1 p.2) * f (p.2 p.1.1) :=
    ((hA.neg.exp).mul (hf.comp heval)).stronglyMeasurable
  have hInt := hint.integral_kernel_prod_right' (κ := Q')
  simpa only [Q', Kernel.comap_apply, IsConservative.feynmanKac_apply] using hInt.measurable


/-- The Feynman--Kac operators satisfy the semigroup law. -/
theorem IsFellerKernelSemigroup.feynmanKac_add (hFeller : P.IsFellerKernelSemigroup)
    (hK : P.KolmogorovRegular hP) {q : alpha → ℝ} (hq : Measurable q)
    {C : ℝ} (hq0 : ∀ y, 0 ≤ q y) (hqC : ∀ y, q y ≤ C)
    (s t : NNReal) {f : alpha → ℝ} (hf : Measurable f) {D : ℝ}
    (hfD : ∀ y, ‖f y‖ ≤ D) (x : alpha) :
    IsConservative.feynmanKac P hP q (s + t) f x =
      IsConservative.feynmanKac P hP q s
        (IsConservative.feynmanKac P hP q t f) x := by
  let W : ContinuousPath alpha → ℝ := fun omega ↦
    Real.exp (-feynmanKacAdditiveFunctional q s omega)
  let F : ContinuousPath alpha → ℝ := fun eta ↦
    Real.exp (-feynmanKacAdditiveFunctional q t eta) * f (eta t)
  let mu : Measure (ContinuousPath alpha) := IsConservative.continuousProcess P hP x
  have hW : StronglyMeasurable[ContinuousPath.canonicalFiltration (alpha := alpha) s] W := by
    have hA : Measurable[ContinuousPath.canonicalFiltration (alpha := alpha) s]
        (fun omega ↦ -feynmanKacAdditiveFunctional q s omega) :=
      (stronglyMeasurable_feynmanKacAdditiveFunctional_canonicalFiltration hq s).measurable.neg
    exact hA.exp.stronglyMeasurable
  have hF : StronglyMeasurable F := by
    have hweight : StronglyMeasurable fun eta : ContinuousPath alpha ↦
        Real.exp (-feynmanKacAdditiveFunctional q t eta) :=
      (stronglyMeasurable_feynmanKacAdditiveFunctional hq t).measurable.neg.exp.stronglyMeasurable
    exact hweight.mul ((hf.comp
      (ContinuousPath.measurable_coordinateProcess (alpha := alpha) t)).stronglyMeasurable)
  have hFbound : ∀ eta : ContinuousPath alpha, ‖F eta‖ ≤ D := by
    intro eta
    dsimp only [F]
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-feynmanKacAdditiveFunctional q t eta) * ‖f (eta t)‖ ≤ 1 * ‖f (eta t)‖ :=
        mul_le_mul_of_nonneg_right
          ((Real.exp_le_one_iff).mpr
            (neg_nonpos.mpr (feynmanKacAdditiveFunctional_nonneg hq0 t eta))) (norm_nonneg _)
      _ ≤ D := by simpa only [one_mul] using hfD _
  have hWFbound : ∀ omega : ContinuousPath alpha,
      ‖W omega * F (ContinuousPath.shift s omega)‖ ≤ D := by
    intro omega
    rw [norm_mul]
    calc
      ‖W omega‖ * ‖F (ContinuousPath.shift s omega)‖ ≤ 1 * ‖F (ContinuousPath.shift s omega)‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        dsimp only [W]
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact (Real.exp_le_one_iff).mpr
          (neg_nonpos.mpr (feynmanKacAdditiveFunctional_nonneg hq0 s omega))
      _ ≤ D := by simpa only [one_mul] using hFbound _
  have hIntFshift : Integrable (fun omega ↦ F (ContinuousPath.shift s omega)) mu :=
    Integrable.of_bound
      (hF.comp_measurable
        (ContinuousPath.measurable_shift_fixed (alpha := alpha) s)).aestronglyMeasurable
      D (Eventually.of_forall fun omega ↦ hFbound _)
  have hIntWF : Integrable (fun omega ↦ W omega * F (ContinuousPath.shift s omega)) mu :=
    Integrable.of_bound
      ((hW.mono ((ContinuousPath.canonicalFiltration (alpha := alpha)).le s)).mul
        (hF.comp_measurable
          (ContinuousPath.measurable_shift_fixed (alpha := alpha) s))).aestronglyMeasurable
      D (Eventually.of_forall hWFbound)
  have hcond := hFeller.continuousProcess_condExp_shift P hP hK x s F hF D hFbound
  have hpull := condExp_mul_of_stronglyMeasurable_left (μ := mu) hW hIntWF hIntFshift
  have htotal : (fun omega ↦
      Real.exp (-feynmanKacAdditiveFunctional q (s + t) omega) * f (omega (s + t))) =
      fun omega ↦ W omega * F (ContinuousPath.shift s omega) := by
    funext omega
    dsimp only [W, F]
    rw [ContinuousPath.shift_apply, feynmanKacAdditiveFunctional_add hq hq0 hqC]
    rw [neg_add, Real.exp_add]
    ring
  rw [IsConservative.feynmanKac_apply, htotal]
  calc
    (∫ omega, W omega * F (ContinuousPath.shift s omega) ∂mu) =
        ∫ omega, mu[fun eta ↦ W eta * F (ContinuousPath.shift s eta)|
          ContinuousPath.canonicalFiltration (alpha := alpha) s] omega ∂mu := by
            rw [integral_condExp ((ContinuousPath.canonicalFiltration (alpha := alpha)).le s)]
    _ = ∫ omega, W omega *
          (∫ eta, F eta ∂IsConservative.continuousProcess P hP (omega s)) ∂mu := by
            refine integral_congr_ae (hpull.trans ?_)
            exact EventuallyEq.mul (EventuallyEq.refl _ _) hcond
    _ = IsConservative.feynmanKac P hP q s
          (IsConservative.feynmanKac P hP q t f) x := by
            rfl

end

end MarkovProcess.SubMarkovKernelSemigroup

end PortComputability
