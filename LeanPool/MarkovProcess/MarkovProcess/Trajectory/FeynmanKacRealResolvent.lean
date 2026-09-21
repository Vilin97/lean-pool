/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Kernel.ResolventUniqueness
import LeanPool.MarkovProcess.MarkovProcess.Semigroup.Resolvent
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.FeynmanKacResolvent
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Real Feynman--Kac resolvents

This file defines the real Feynman--Kac resolvent on bounded measurable observables.  It proves
its uniform bound, linearity, the resolvent identity, and the bounded-potential perturbation
identity.

Main results: `IsConservative.feynmanKacResolventReal`,
`IsFellerKernelSemigroup.feynmanKacResolventReal_resolvent_identity`, and
`IsFellerKernelSemigroup.feynmanKacResolventReal_perturbation`.

Together with `perturbed_eq_of_resolventFamilies`, these identities characterize the
Feynman--Kac resolvent among bounded measurable resolvent families solving the same perturbation
equation at all sufficiently large shifts.  No model-specific realization is assumed.
-/

noncomputable section PortComputability

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MarkovProcess.SubMarkovKernelSemigroup

section

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [CompleteSpace alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

/-- The real Feynman--Kac resolvent on bounded measurable observables. -/
def IsConservative.feynmanKacResolventReal (q : alpha → ℝ) (lam : ℝ)
    (f : alpha → ℝ) (x : alpha) : ℝ :=
  ∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) *
    IsConservative.feynmanKac P hP q (Real.toNNReal t) f x

omit [LocallyCompactSpace alpha] in
private theorem IsConservative.integrableOn_feynmanKacResolventReal_integrand
    {q : alpha → ℝ} (hq : Measurable q) (hq0 : ∀ y, 0 ≤ q y) {lam : ℝ} (hlam : 0 < lam)
    {f : alpha → ℝ} (hf : Measurable f) {D : ℝ} (hfD : ∀ y, |f y| ≤ D) (x : alpha) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-lam * t) *
      IsConservative.feynmanKac P hP q (Real.toNNReal t) f x) (Ioi 0) := by
  apply Integrable.mono' ((exp_neg_integrableOn_Ioi 0 hlam).mul_const D)
  · exact (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.mul
      ((IsConservative.measurable_feynmanKac_joint P hP hq hf).comp
        (measurable_real_toNNReal.prodMk measurable_const))).stronglyMeasurable
      ).aestronglyMeasurable.restrict
  · exact Eventually.of_forall fun t ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left
        (IsConservative.norm_feynmanKac_le P hP hq0 (Real.toNNReal t) hfD x)
        (Real.exp_pos _).le

omit [LocallyCompactSpace alpha] in
/-- The real Feynman--Kac resolvent of a bounded measurable observable is measurable in the
starting point. -/
theorem IsConservative.measurable_feynmanKacResolventReal {q : alpha → ℝ}
    (hq : Measurable q) (lam : ℝ) {f : alpha → ℝ} (hf : Measurable f) :
    Measurable (IsConservative.feynmanKacResolventReal P hP q lam f) := by
  have hjoint : StronglyMeasurable fun p : ℝ × alpha ↦
      Real.exp (-lam * p.1) *
        IsConservative.feynmanKac P hP q (Real.toNNReal p.1) f p.2 :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.comp
      measurable_fst).mul
      ((IsConservative.measurable_feynmanKac_joint P hP hq hf).comp
        ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
      ) |>.stronglyMeasurable
  exact (hjoint.integral_prod_left' (μ := volume.restrict (Ioi 0))).measurable

omit [LocallyCompactSpace alpha] in
/-- The real Feynman--Kac resolvent is additive on bounded measurable observables. -/
theorem IsConservative.feynmanKacResolventReal_add {q : alpha → ℝ}
    (hq : Measurable q) (hq0 : ∀ y, 0 ≤ q y) {lam : ℝ} (hlam : 0 < lam)
    {f g : alpha → ℝ} (hf : Measurable f) (hg : Measurable g) {D E : ℝ}
    (hfD : ∀ y, |f y| ≤ D) (hgE : ∀ y, |g y| ≤ E) :
    IsConservative.feynmanKacResolventReal P hP q lam (f + g) =
      IsConservative.feynmanKacResolventReal P hP q lam f +
        IsConservative.feynmanKacResolventReal P hP q lam g := by
  funext x
  unfold IsConservative.feynmanKacResolventReal
  change (∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) *
      IsConservative.feynmanKac P hP q (Real.toNNReal t) (f + g) x) =
    (∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) *
      IsConservative.feynmanKac P hP q (Real.toNNReal t) f x) +
    ∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) *
      IsConservative.feynmanKac P hP q (Real.toNNReal t) g x
  rw [← integral_add
    (IsConservative.integrableOn_feynmanKacResolventReal_integrand
      P hP hq hq0 hlam hf hfD x)
    (IsConservative.integrableOn_feynmanKacResolventReal_integrand
      P hP hq hq0 hlam hg hgE x)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _ht
  dsimp only
  rw [congrFun (IsConservative.feynmanKac_add_apply P hP hq hq0
    (Real.toNNReal t) hf hg hfD hgE) x]
  simp only [Pi.add_apply]
  ring

omit [LocallyCompactSpace alpha] in
/-- The real Feynman--Kac resolvent is real homogeneous. -/
theorem IsConservative.feynmanKacResolventReal_smul (q : alpha → ℝ) (lam a : ℝ)
    (f : alpha → ℝ) :
    IsConservative.feynmanKacResolventReal P hP q lam (a • f) =
      a • IsConservative.feynmanKacResolventReal P hP q lam f := by
  funext x
  unfold IsConservative.feynmanKacResolventReal
  change (∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) *
      IsConservative.feynmanKac P hP q (Real.toNNReal t) (a • f) x) =
    a • (∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) *
      IsConservative.feynmanKac P hP q (Real.toNNReal t) f x)
  rw [← integral_smul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _ht
  dsimp only
  rw [congrFun (IsConservative.feynmanKac_smul_apply P hP q
    (Real.toNNReal t) a f) x]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

omit [LocallyCompactSpace alpha] in
/-- The uniform bound for the real Feynman--Kac resolvent at a positive shift. -/
theorem IsConservative.norm_feynmanKacResolventReal_le {q : alpha → ℝ}
    (hq0 : ∀ y, 0 ≤ q y) {lam : ℝ} (hlam : 0 < lam)
    {f : alpha → ℝ} {D : ℝ} (hfD : ∀ y, |f y| ≤ D)
    (x : alpha) : |IsConservative.feynmanKacResolventReal P hP q lam f x| ≤ D / lam := by
  rw [← Real.norm_eq_abs]
  unfold IsConservative.feynmanKacResolventReal
  calc
    ‖∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) *
        IsConservative.feynmanKac P hP q (Real.toNNReal t) f x‖ ≤
        ∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) * D := by
      apply norm_integral_le_of_norm_le
        ((exp_neg_integrableOn_Ioi 0 hlam).mul_const D)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left
        (IsConservative.norm_feynmanKac_le P hP hq0 (Real.toNNReal t) hfD x)
        (Real.exp_pos _).le
    _ = D / lam := by
      rw [integral_mul_const,
        Semigroup.StronglyContinuousContractionSemigroup.integral_exp_neg_mul_Ioi_zero hlam]
      field_simp

omit [LocallyCompactSpace alpha] in
/-- For a bounded nonnegative real observable, applying `ENNReal.ofReal` to the real
Feynman--Kac resolvent gives the extended-real Feynman--Kac resolvent. -/
theorem IsConservative.ofReal_feynmanKacResolventReal_eq_feynmanKacResolvent
    {q : alpha → ℝ} (hq : Measurable q) (hq0 : ∀ y, 0 ≤ q y)
    {lam : ℝ} (hlam : 0 < lam) {f : alpha → ℝ} (hf : Measurable f)
    (hf0 : ∀ y, 0 ≤ f y) {D : ℝ} (hfD : ∀ y, |f y| ≤ D) (x : alpha) :
    ENNReal.ofReal (IsConservative.feynmanKacResolventReal P hP q lam f x) =
      IsConservative.feynmanKacResolvent P hP q lam
        (fun y ↦ ENNReal.ofReal (f y)) x := by
  have hint := IsConservative.integrableOn_feynmanKacResolventReal_integrand
    P hP hq hq0 hlam hf hfD x
  rw [IsConservative.feynmanKacResolventReal,
    ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun t ↦ mul_nonneg (Real.exp_pos _).le
        (IsConservative.feynmanKac_nonneg P hP hf0 x))]
  unfold IsConservative.feynmanKacResolvent
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t _ht
  dsimp only
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le,
    IsConservative.ofReal_feynmanKac_eq_feynmanKacENNReal P hP hq hq0
      (Real.toNNReal t) hf hf0 (fun y ↦ (le_abs_self (f y)).trans (hfD y)) x]

/-- With zero potential, the real Feynman--Kac resolvent is the real kernel resolvent. -/
theorem IsFellerKernelSemigroup.feynmanKacResolventReal_zero_eq_kernelResolventReal
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (lam : ℝ) {f : alpha → ℝ} (hf : Measurable f) :
    IsConservative.feynmanKacResolventReal P hP (fun _ ↦ 0) lam f =
      P.kernelResolventReal lam f := by
  funext x
  unfold IsConservative.feynmanKacResolventReal SubMarkovKernelSemigroup.kernelResolventReal
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _ht
  have heval := hFeller.integral_eval_continuousProcess_of_measurable
    P hP hK (Real.toNNReal t) x hf
  simp only [IsConservative.feynmanKac_apply, feynmanKacAdditiveFunctional,
    intervalIntegral.integral_zero, neg_zero, Real.exp_zero, one_mul]
  rw [heval]
  rfl

/-- The real kernel resolvent of a bounded measurable observable is measurable. -/
theorem IsFellerKernelSemigroup.measurable_kernelResolventReal
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (lam : ℝ) {f : alpha → ℝ} (hf : Measurable f) :
    Measurable (P.kernelResolventReal lam f) := by
  rw [← hFeller.feynmanKacResolventReal_zero_eq_kernelResolventReal P hP hK lam hf]
  exact IsConservative.measurable_feynmanKacResolventReal P hP measurable_const lam hf

private theorem IsFellerKernelSemigroup.feynmanKac_comp_feynmanKacResolventReal
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    {q : alpha → ℝ} (hq : Measurable q) {C : ℝ}
    (hq0 : ∀ y, 0 ≤ q y) (hqC : ∀ y, q y ≤ C) {mu : ℝ} (hmu : 0 < mu)
    (s : NNReal) {f : alpha → ℝ} (hf : Measurable f) {D : ℝ}
    (hfD : ∀ y, |f y| ≤ D) (x : alpha) :
    IsConservative.feynmanKac P hP q s
        (IsConservative.feynmanKacResolventReal P hP q mu f) x =
      ∫ t in Ioi (0 : ℝ), Real.exp (-mu * t) *
        IsConservative.feynmanKac P hP q (s + Real.toNNReal t) f x := by
  let Qx : Measure (ContinuousPath alpha) := IsConservative.continuousProcess P hP x
  let H : ContinuousPath alpha × ℝ → ℝ := fun p ↦
    Real.exp (-feynmanKacAdditiveFunctional q s p.1) * Real.exp (-mu * p.2) *
      IsConservative.feynmanKac P hP q (Real.toNNReal p.2) f (p.1 s)
  have hHmeas : StronglyMeasurable H := by
    have hstart : Measurable fun p : ContinuousPath alpha × ℝ ↦ p.1 s :=
      (ContinuousPath.measurable_coordinateProcess (alpha := alpha) s).comp measurable_fst
    have htime : Measurable fun p : ContinuousPath alpha × ℝ ↦ Real.toNNReal p.2 :=
      measurable_real_toNNReal.comp measurable_snd
    have hW : Measurable fun p : ContinuousPath alpha × ℝ ↦
        Real.exp (-feynmanKacAdditiveFunctional q s p.1) :=
      (stronglyMeasurable_feynmanKacAdditiveFunctional hq s).measurable.neg.exp.comp
        measurable_fst
    have hE : Measurable fun p : ContinuousPath alpha × ℝ ↦ Real.exp (-mu * p.2) :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.comp
        measurable_snd
    have hFK : Measurable fun p : ContinuousPath alpha × ℝ ↦
        IsConservative.feynmanKac P hP q (Real.toNNReal p.2) f (p.1 s) :=
      (IsConservative.measurable_feynmanKac_joint P hP hq hf).comp
        (htime.prodMk hstart)
    exact ((hW.mul hE).mul hFK).stronglyMeasurable
  have htimeInt : IntegrableOn (fun t : ℝ ↦ Real.exp (-mu * t) * D) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hmu).mul_const D
  have hdom : Integrable (fun p : ContinuousPath alpha × ℝ ↦
      (1 : ℝ) * (Real.exp (-mu * p.2) * D))
      (Qx.prod (volume.restrict (Ioi 0))) :=
    (integrable_const (μ := Qx) (1 : ℝ)).mul_prod htimeInt
  have hHint : Integrable H (Qx.prod (volume.restrict (Ioi 0))) := by
    apply Integrable.mono' hdom hHmeas.aestronglyMeasurable
    exact Eventually.of_forall fun p ↦ by
      dsimp only [H]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
        abs_of_pos (Real.exp_pos _), one_mul]
      calc
        Real.exp (-feynmanKacAdditiveFunctional q s p.1) *
            Real.exp (-mu * p.2) *
              |IsConservative.feynmanKac P hP q (Real.toNNReal p.2) f (p.1 s)| ≤
            1 * Real.exp (-mu * p.2) * D := by
          calc
            Real.exp (-feynmanKacAdditiveFunctional q s p.1) *
                Real.exp (-mu * p.2) *
                  |IsConservative.feynmanKac P hP q
                    (Real.toNNReal p.2) f (p.1 s)| ≤
                (1 * Real.exp (-mu * p.2)) *
                  |IsConservative.feynmanKac P hP q
                    (Real.toNNReal p.2) f (p.1 s)| := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right
                  ((Real.exp_le_one_iff).mpr
                    (neg_nonpos.mpr (feynmanKacAdditiveFunctional_nonneg hq0 s p.1)))
                  (Real.exp_pos _).le) (abs_nonneg _)
            _ ≤ (1 * Real.exp (-mu * p.2)) * D :=
              mul_le_mul_of_nonneg_left
                (IsConservative.norm_feynmanKac_le P hP hq0
                  (Real.toNNReal p.2) hfD (p.1 s))
                (mul_nonneg zero_le_one (Real.exp_pos _).le)
        _ = Real.exp (-mu * p.2) * D := by ring
  rw [IsConservative.feynmanKac_apply]
  unfold IsConservative.feynmanKacResolventReal
  change (∫ omega, Real.exp (-feynmanKacAdditiveFunctional q s omega) *
      (∫ t in Ioi (0 : ℝ), Real.exp (-mu * t) *
        IsConservative.feynmanKac P hP q (Real.toNNReal t) f (omega s)) ∂Qx) = _
  calc
    (∫ omega, Real.exp (-feynmanKacAdditiveFunctional q s omega) *
        (∫ t in Ioi (0 : ℝ), Real.exp (-mu * t) *
          IsConservative.feynmanKac P hP q (Real.toNNReal t) f (omega s)) ∂Qx) =
        ∫ omega, (∫ t in Ioi (0 : ℝ), H (omega, t)) ∂Qx := by
      apply integral_congr_ae
      exact Eventually.of_forall fun omega ↦ by
        dsimp only
        rw [← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t _ht
        dsimp only [H]
        ring
    _ = ∫ t in Ioi (0 : ℝ), ∫ omega, H (omega, t) ∂Qx :=
      integral_integral_swap hHint
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _ht
      dsimp only [H]
      calc
        (∫ omega, Real.exp (-feynmanKacAdditiveFunctional q s omega) *
            Real.exp (-mu * t) *
              IsConservative.feynmanKac P hP q (Real.toNNReal t) f (omega s) ∂Qx) =
            ∫ omega, Real.exp (-mu * t) *
              (Real.exp (-feynmanKacAdditiveFunctional q s omega) *
                IsConservative.feynmanKac P hP q (Real.toNNReal t) f (omega s)) ∂Qx := by
          apply integral_congr_ae
          exact Eventually.of_forall fun omega ↦ by ring
        _ = Real.exp (-mu * t) *
            ∫ omega, Real.exp (-feynmanKacAdditiveFunctional q s omega) *
              IsConservative.feynmanKac P hP q (Real.toNNReal t) f (omega s) ∂Qx := by
          rw [integral_const_mul]
        _ = Real.exp (-mu * t) *
            IsConservative.feynmanKac P hP q (s + Real.toNNReal t) f x := by
          rw [← IsConservative.feynmanKac_apply]
          rw [← hFeller.feynmanKac_add P hP hK hq hq0 hqC s
            (Real.toNNReal t) hf hfD x]

private theorem exp_sub_mul_integral_exp_mul_exp_sub (lam mu u : ℝ) (hu : 0 ≤ u) :
    (lam - mu) * (∫ s in Ioo (0 : ℝ) u,
      Real.exp (-lam * s) * Real.exp (-mu * (u - s))) =
      Real.exp (-mu * u) - Real.exp (-lam * u) := by
  let phi : ℝ → ℝ := fun s ↦
    Real.exp (-lam * s) * Real.exp (-mu * (u - s))
  have hderiv (s : ℝ) : HasDerivAt phi ((mu - lam) * phi s) s := by
    dsimp only [phi]
    have hd := (((hasDerivAt_const s (-lam)).mul (hasDerivAt_id s)).exp.mul
      ((hasDerivAt_const s (-mu)).mul
        ((hasDerivAt_const s u).sub (hasDerivAt_id s))).exp)
    convert hd using 1
    all_goals first
      | rfl
      | (simp only [Pi.mul_apply, Pi.sub_apply, id_eq]; ring)
  have hint : IntervalIntegrable (fun s ↦ (mu - lam) * phi s) volume 0 u :=
    (continuous_const.mul
      (continuous_iff_continuousAt.mpr fun s ↦ (hderiv s).continuousAt)).intervalIntegrable 0 u
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _hs ↦ hderiv s) hint
  rw [intervalIntegral.integral_of_le hu, integral_Ioc_eq_integral_Ioo,
    MeasureTheory.integral_const_mul] at hFTC
  dsimp only [phi] at hFTC ⊢
  simp only [sub_self, mul_zero, Real.exp_zero, mul_one, sub_zero, one_mul] at hFTC
  linarith only [hFTC]

/-- The real Feynman--Kac resolvents satisfy the resolvent identity on bounded measurable
observables. -/
theorem IsFellerKernelSemigroup.feynmanKacResolventReal_resolvent_identity
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    {q : alpha → ℝ} (hq : Measurable q) {C : ℝ}
    (hq0 : ∀ y, 0 ≤ q y) (hqC : ∀ y, q y ≤ C)
    {mu lam : ℝ} (hmu : 0 < mu) (hlam : 0 < lam) {f : alpha → ℝ}
    (hf : Measurable f) {D : ℝ} (hfD : ∀ y, |f y| ≤ D) :
    IsConservative.feynmanKacResolventReal P hP q mu f =
      IsConservative.feynmanKacResolventReal P hP q lam f +
        (lam - mu) • IsConservative.feynmanKacResolventReal P hP q lam
          (IsConservative.feynmanKacResolventReal P hP q mu f) := by
  funext x
  let H : ℝ × ℝ → ℝ := fun p ↦
    Real.exp (-lam * p.1) * Real.exp (-mu * p.2) *
      IsConservative.feynmanKac P hP q
        (Real.toNNReal p.1 + Real.toNNReal p.2) f x
  let K : ℝ → ℝ := fun u ↦ ∫ s in Ioo (0 : ℝ) u, H (s, u - s)
  have hHmeas : Measurable H := by
    exact (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.comp
      measurable_fst).mul
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.comp
        measurable_snd)).mul
      ((IsConservative.measurable_feynmanKac_joint P hP hq hf).comp
        (((measurable_real_toNNReal.comp measurable_fst).add
          (measurable_real_toNNReal.comp measurable_snd)).prodMk measurable_const))
  have hQ : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
    measurableSet_Ioi.prod measurableSet_Ioi
  have hHquad : Integrable H
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have hbase := (exp_neg_integrableOn_Ioi 0 hlam).mul_prod
      ((exp_neg_integrableOn_Ioi 0 hmu).mul_const D)
    apply Integrable.mono' hbase hHmeas.aestronglyMeasurable
    exact Eventually.of_forall fun p ↦ by
      dsimp only [H]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
        abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left
        (IsConservative.norm_feynmanKac_le P hP hq0
          (Real.toNNReal p.1 + Real.toNNReal p.2) hfD x)
        (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) |>.trans_eq (by ring)
  have hHind : Integrable ((Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)).indicator H)
      (volume.prod volume) := by
    apply (integrable_indicator_iff hQ).2
    change Integrable H ((volume.prod volume).restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)))
    rw [← Measure.prod_restrict]
    exact hHquad
  have htriangle := intervalIntegral.integral_timeTriangle_sub hHmeas hHind
  have hmuInt := IsConservative.integrableOn_feynmanKacResolventReal_integrand
    P hP hq hq0 hmu hf hfD x
  have hlamInt := IsConservative.integrableOn_feynmanKacResolventReal_integrand
    P hP hq hq0 hlam hf hfD x
  have hpoint (u : ℝ) (hu : u ∈ Ioi (0 : ℝ)) :
      Real.exp (-mu * u) * IsConservative.feynmanKac P hP q (Real.toNNReal u) f x =
        Real.exp (-lam * u) * IsConservative.feynmanKac P hP q (Real.toNNReal u) f x +
          (lam - mu) * K u := by
    have hK : K u = (∫ s in Ioo (0 : ℝ) u,
        Real.exp (-lam * s) * Real.exp (-mu * (u - s))) *
          IsConservative.feynmanKac P hP q (Real.toNNReal u) f x := by
      dsimp only [K]
      rw [← MeasureTheory.integral_mul_const]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro s hs
      dsimp only [H]
      have hs0 : 0 ≤ s := hs.1.le
      have hus0 : 0 ≤ u - s := sub_nonneg.mpr hs.2.le
      have htime : Real.toNNReal s + Real.toNNReal (u - s) = Real.toNNReal u := by
        apply NNReal.coe_injective
        rw [NNReal.coe_add, Real.coe_toNNReal s hs0, Real.coe_toNNReal (u - s) hus0,
          Real.coe_toNNReal u hu.le]
        ring
      rw [htime]
    rw [hK]
    have hexp := exp_sub_mul_integral_exp_mul_exp_sub lam mu u hu.le
    calc
      Real.exp (-mu * u) * IsConservative.feynmanKac P hP q (Real.toNNReal u) f x =
          (Real.exp (-lam * u) +
            (lam - mu) * (∫ s in Ioo (0 : ℝ) u,
              Real.exp (-lam * s) * Real.exp (-mu * (u - s)))) *
            IsConservative.feynmanKac P hP q (Real.toNNReal u) f x := by
        rw [hexp]
        ring
      _ = _ := by ring
  have hsecond : IntegrableOn (fun u ↦ (lam - mu) * K u) (Ioi (0 : ℝ)) := by
    apply (hmuInt.sub hlamInt).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    change Real.exp (-mu * u) * IsConservative.feynmanKac P hP q (Real.toNNReal u) f x -
      Real.exp (-lam * u) * IsConservative.feynmanKac P hP q (Real.toNNReal u) f x =
        (lam - mu) * K u
    linarith only [hpoint u hu]
  have hcomp : IsConservative.feynmanKacResolventReal P hP q lam
      (IsConservative.feynmanKacResolventReal P hP q mu f) x =
      ∫ s in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), H (s, t) := by
    change (∫ s in Ioi (0 : ℝ), Real.exp (-lam * s) *
      IsConservative.feynmanKac P hP q (Real.toNNReal s)
        (IsConservative.feynmanKacResolventReal P hP q mu f) x) = _
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s _hs
    dsimp only
    rw [hFeller.feynmanKac_comp_feynmanKacResolventReal
      P hP hK hq hq0 hqC hmu (Real.toNNReal s) hf hfD x]
    rw [← MeasureTheory.integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _ht
    dsimp only [H]
    ring
  have htriangle' : (∫ u in Ioi (0 : ℝ), K u) =
      ∫ s in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), H (s, t) := by
    simpa only [K] using htriangle
  change (∫ u in Ioi (0 : ℝ), Real.exp (-mu * u) *
      IsConservative.feynmanKac P hP q (Real.toNNReal u) f x) =
    (∫ u in Ioi (0 : ℝ), Real.exp (-lam * u) *
      IsConservative.feynmanKac P hP q (Real.toNNReal u) f x) +
      (lam - mu) * IsConservative.feynmanKacResolventReal P hP q lam
        (IsConservative.feynmanKacResolventReal P hP q mu f) x
  rw [hcomp, ← htriangle', ← MeasureTheory.integral_const_mul,
    ← integral_add hlamInt hsecond]
  apply setIntegral_congr_fun measurableSet_Ioi
  exact hpoint

/-- The real kernel resolvents satisfy the resolvent identity on bounded measurable
observables. -/
theorem IsFellerKernelSemigroup.kernelResolventReal_resolvent_identity
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    {mu lam : ℝ} (hmu : 0 < mu) (hlam : 0 < lam) {f : alpha → ℝ}
    (hf : Measurable f) {D : ℝ} (hfD : ∀ y, |f y| ≤ D) :
    P.kernelResolventReal mu f = P.kernelResolventReal lam f +
      (lam - mu) • P.kernelResolventReal lam (P.kernelResolventReal mu f) := by
  have hmuEq := hFeller.feynmanKacResolventReal_zero_eq_kernelResolventReal
    P hP hK mu hf
  have hlamEq := hFeller.feynmanKacResolventReal_zero_eq_kernelResolventReal
    P hP hK lam hf
  have hRmeas := hFeller.measurable_kernelResolventReal P hP hK mu hf
  have hcompEq := hFeller.feynmanKacResolventReal_zero_eq_kernelResolventReal
    P hP hK lam hRmeas
  calc
    P.kernelResolventReal mu f =
        IsConservative.feynmanKacResolventReal P hP (fun _ ↦ 0) mu f := hmuEq.symm
    _ = IsConservative.feynmanKacResolventReal P hP (fun _ ↦ 0) lam f +
        (lam - mu) • IsConservative.feynmanKacResolventReal P hP (fun _ ↦ 0) lam
          (IsConservative.feynmanKacResolventReal P hP (fun _ ↦ 0) mu f) :=
      hFeller.feynmanKacResolventReal_resolvent_identity P hP hK measurable_const
        (fun _ ↦ le_rfl) (fun _ ↦ le_rfl) hmu hlam hf hfD
    _ = P.kernelResolventReal lam f +
        (lam - mu) • P.kernelResolventReal lam (P.kernelResolventReal mu f) := by
      rw [hlamEq, hmuEq, hcompEq]

omit [LocallyCompactSpace alpha] in
private theorem IsConservative.kernelIntegral_mul_feynmanKacResolventReal
    {q : alpha → ℝ} (hq : Measurable q)
    {C : ℝ} (hq0 : ∀ y, 0 ≤ q y) (hqC : ∀ y, q y ≤ C)
    {lam : ℝ} (hlam : 0 < lam) (s : NNReal) {f : alpha → ℝ}
    (hf : Measurable f) {D : ℝ} (hfD : ∀ y, |f y| ≤ D) (x : alpha) :
    kernelIntegral (P s)
        (fun y ↦ q y * IsConservative.feynmanKacResolventReal P hP q lam f y) x =
      ∫ u in Ioi (0 : ℝ), Real.exp (-lam * u) *
        kernelIntegral (P s)
          (fun y ↦ q y * IsConservative.feynmanKac P hP q (Real.toNNReal u) f y) x := by
  let H : alpha × ℝ → ℝ := fun p ↦
    q p.1 * Real.exp (-lam * p.2) *
      IsConservative.feynmanKac P hP q (Real.toNNReal p.2) f p.1
  have hHmeas : StronglyMeasurable H := by
    exact (((hq.comp measurable_fst).mul
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.comp
        measurable_snd)).mul
      ((IsConservative.measurable_feynmanKac_joint P hP hq hf).comp
        ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)
      )).stronglyMeasurable
  let : IsFiniteKernel (P s) := (P.isSubMarkovKernel s).isFiniteKernel
  have hC0 : 0 ≤ C := (hq0 x).trans (hqC x)
  have hD0 : 0 ≤ D := (abs_nonneg (f x)).trans (hfD x)
  have hbase : Integrable (fun p : alpha × ℝ ↦
      C * (Real.exp (-lam * p.2) * D))
      ((P s x).prod (volume.restrict (Ioi 0))) :=
    (integrable_const (C : ℝ)).mul_prod ((exp_neg_integrableOn_Ioi 0 hlam).mul_const D)
  have hHint : Integrable H ((P s x).prod (volume.restrict (Ioi 0))) := by
    apply Integrable.mono' hbase hHmeas.aestronglyMeasurable
    exact Eventually.of_forall fun p ↦ by
      dsimp only [H]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hq0 p.1),
        abs_of_pos (Real.exp_pos _)]
      calc
        q p.1 * Real.exp (-lam * p.2) *
            |IsConservative.feynmanKac P hP q (Real.toNNReal p.2) f p.1| ≤
            C * Real.exp (-lam * p.2) * D := by
          exact mul_le_mul
            (mul_le_mul (hqC p.1) le_rfl (Real.exp_pos _).le hC0)
            (IsConservative.norm_feynmanKac_le P hP hq0
              (Real.toNNReal p.2) hfD p.1) (abs_nonneg _)
            (mul_nonneg hC0 (Real.exp_pos _).le)
        _ = C * (Real.exp (-lam * p.2) * D) := by ring
  unfold IsConservative.feynmanKacResolventReal
  change (∫ y, q y * (∫ u in Ioi (0 : ℝ), Real.exp (-lam * u) *
      IsConservative.feynmanKac P hP q (Real.toNNReal u) f y) ∂(P s x)) = _
  calc
    (∫ y, q y * (∫ u in Ioi (0 : ℝ), Real.exp (-lam * u) *
        IsConservative.feynmanKac P hP q (Real.toNNReal u) f y) ∂(P s x)) =
        ∫ y, (∫ u in Ioi (0 : ℝ), H (y, u)) ∂(P s x) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun y ↦ by
        dsimp only
        rw [← MeasureTheory.integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u _hu
        dsimp only [H]
        ring
    _ = ∫ u in Ioi (0 : ℝ), ∫ y, H (y, u) ∂(P s x) :=
      integral_integral_swap hHint
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u _hu
      dsimp only [H]
      calc
        (∫ y, q y * Real.exp (-lam * u) *
            IsConservative.feynmanKac P hP q (Real.toNNReal u) f y ∂(P s x)) =
            ∫ y, Real.exp (-lam * u) *
              (q y * IsConservative.feynmanKac P hP q (Real.toNNReal u) f y)
              ∂(P s x) := by
          apply integral_congr_ae
          exact Eventually.of_forall fun y ↦ by ring
        _ = Real.exp (-lam * u) *
            ∫ y, q y * IsConservative.feynmanKac P hP q (Real.toNNReal u) f y
              ∂(P s x) := MeasureTheory.integral_const_mul _ _

/-- The real Feynman--Kac resolvent satisfies the bounded-potential perturbation equation against
the real kernel resolvent.  This supplies the Feynman--Kac fixed-point input to
`perturbed_eq_of_resolventFamilies`. -/
theorem IsFellerKernelSemigroup.feynmanKacResolventReal_perturbation
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    {q : alpha → ℝ} (hq : Measurable q) {C : ℝ}
    (hq0 : ∀ y, 0 ≤ q y) (hqC : ∀ y, q y ≤ C)
    {lam : ℝ} (hlam : 0 < lam) {f : alpha → ℝ} (hf : Measurable f)
    {D : ℝ} (hfD : ∀ y, |f y| ≤ D) :
    IsConservative.feynmanKacResolventReal P hP q lam f =
      P.kernelResolventReal lam f - P.kernelResolventReal lam
        (fun y ↦ q y * IsConservative.feynmanKacResolventReal P hP q lam f y) := by
  funext x
  let H : ℝ × ℝ → ℝ := fun p ↦
    Real.exp (-lam * (p.1 + p.2)) *
      kernelIntegral (P (Real.toNNReal p.1))
        (fun y ↦ q y * IsConservative.feynmanKac P hP q (Real.toNNReal p.2) f y) x
  have hHmeas : Measurable H := by
    have hintegrand : Measurable fun p : (ℝ × ℝ) × alpha ↦
        q p.2 * IsConservative.feynmanKac P hP q (Real.toNNReal p.1.2) f p.2 :=
      (hq.comp measurable_snd).mul
        ((IsConservative.measurable_feynmanKac_joint P hP hq hf).comp
          (((measurable_real_toNNReal.comp measurable_snd).comp measurable_fst).prodMk
            measurable_snd))
    let K : Kernel (ℝ × ℝ) alpha :=
      { toFun := fun p ↦ P (Real.toNNReal p.1) x
        measurable' := P.measurable_toMeasure.comp
          ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_const) }
    let : IsFiniteKernel K :=
      { exists_univ_le := ⟨1, ENNReal.one_lt_top, fun p ↦ P.measure_univ_le_one _ _⟩ }
    have hkernel : Measurable fun p : ℝ × ℝ ↦
        kernelIntegral (P (Real.toNNReal p.1))
          (fun y ↦ q y * IsConservative.feynmanKac P hP q (Real.toNNReal p.2) f y) x := by
      have hlin := hintegrand.stronglyMeasurable.integral_kernel_prod_right' (κ := K)
      simpa only [K, kernelIntegral] using! hlin.measurable
    exact ((Real.continuous_exp.comp
      (continuous_const.mul (continuous_fst.add continuous_snd))).measurable.mul hkernel)
  have hC0 : 0 ≤ C := (hq0 x).trans (hqC x)
  have hD0 : 0 ≤ D := (abs_nonneg (f x)).trans (hfD x)
  have hinnerBound (s u : ℝ) :
      |kernelIntegral (P (Real.toNNReal s))
        (fun y ↦ q y * IsConservative.feynmanKac P hP q (Real.toNNReal u) f y) x| ≤
          C * D := by
    rw [← Real.norm_eq_abs]
    let : IsFiniteKernel (P (Real.toNNReal s)) :=
      (P.isSubMarkovKernel (Real.toNNReal s)).isFiniteKernel
    calc
      ‖kernelIntegral (P (Real.toNNReal s))
          (fun y ↦ q y * IsConservative.feynmanKac P hP q (Real.toNNReal u) f y) x‖ ≤
          ∫ _y, C * D ∂(P (Real.toNNReal s) x) := by
        apply norm_integral_le_of_norm_le (integrable_const (C * D))
        exact Eventually.of_forall fun y ↦ by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hq0 y)]
          exact mul_le_mul (hqC y)
            (IsConservative.norm_feynmanKac_le P hP hq0 (Real.toNNReal u) hfD y)
            (abs_nonneg _) hC0
      _ ≤ C * D := by
        rw [integral_const, smul_eq_mul]
        apply mul_le_of_le_one_left (mul_nonneg hC0 hD0)
        rw [measureReal_def, ← ENNReal.toReal_one]
        apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.one_ne_top).2
        exact (P.isSubMarkovKernel (Real.toNNReal s)).measure_le_one x Set.univ
  have hQ : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
    measurableSet_Ioi.prod measurableSet_Ioi
  have hHquad : Integrable H
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have hbase := (exp_neg_integrableOn_Ioi 0 hlam).mul_prod
      ((exp_neg_integrableOn_Ioi 0 hlam).mul_const (C * D))
    apply Integrable.mono' hbase hHmeas.stronglyMeasurable.aestronglyMeasurable
    exact Eventually.of_forall fun p ↦ by
      dsimp only [H]
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc
        Real.exp (-lam * (p.1 + p.2)) *
            |kernelIntegral (P (Real.toNNReal p.1))
              (fun y ↦ q y * IsConservative.feynmanKac P hP q
                (Real.toNNReal p.2) f y) x| ≤
            Real.exp (-lam * (p.1 + p.2)) * (C * D) :=
          mul_le_mul_of_nonneg_left (hinnerBound p.1 p.2) (Real.exp_pos _).le
        _ = Real.exp (-lam * p.1) * (Real.exp (-lam * p.2) * (C * D)) := by
          rw [show -lam * (p.1 + p.2) = -lam * p.1 + -lam * p.2 by ring,
            Real.exp_add]
          ring
  have hHind : Integrable ((Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)).indicator H)
      (volume.prod volume) := by
    apply (integrable_indicator_iff hQ).2
    change Integrable H ((volume.prod volume).restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)))
    rw [← Measure.prod_restrict]
    exact hHquad
  have htriangle := intervalIntegral.integral_timeTriangle_sub hHmeas hHind
  have hFKInt := IsConservative.integrableOn_feynmanKacResolventReal_integrand
    P hP hq hq0 hlam hf hfD x
  have hKernelInt : IntegrableOn (fun t : ℝ ↦ Real.exp (-lam * t) *
      kernelIntegral (P (Real.toNNReal t)) f x) (Ioi 0) := by
    have hzero := IsConservative.integrableOn_feynmanKacResolventReal_integrand
      P hP measurable_const (fun _ ↦ le_rfl) hlam hf hfD x
    apply hzero.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _ht
    have heval := hFeller.integral_eval_continuousProcess_of_measurable
      P hP hK (Real.toNNReal t) x hf
    simp only [IsConservative.feynmanKac_apply, feynmanKacAdditiveFunctional,
      intervalIntegral.integral_zero, neg_zero, Real.exp_zero, one_mul]
    rw [heval]
    rfl
  have htime (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      Real.exp (-lam * t) *
        (kernelIntegral (P (Real.toNNReal t)) f x -
          IsConservative.feynmanKac P hP q (Real.toNNReal t) f x) =
        ∫ s in Ioo (0 : ℝ) t, H (s, t - s) := by
    have hfinite := hFeller.integral_sub_feynmanKac_eq_integral_of_norm_le
      P hP hK hq hq0 hqC hf hfD (Real.toNNReal t) x
    rw [intervalIntegral.integral_of_le (Real.toNNReal t).coe_nonneg,
      integral_Ioc_eq_integral_Ioo, Real.coe_toNNReal t ht.le] at hfinite
    change kernelIntegral (P (Real.toNNReal t)) f x -
      IsConservative.feynmanKac P hP q (Real.toNNReal t) f x = _ at hfinite
    calc
      Real.exp (-lam * t) *
          (kernelIntegral (P (Real.toNNReal t)) f x -
            IsConservative.feynmanKac P hP q (Real.toNNReal t) f x) =
          Real.exp (-lam * t) *
            ∫ s in Ioo (0 : ℝ) t, kernelIntegral (P (Real.toNNReal s))
              (fun y ↦ q y * IsConservative.feynmanKac P hP q
                (Real.toNNReal t - Real.toNNReal s) f y) x := by
        rw [hfinite]
        congr 2
      _ = ∫ s in Ioo (0 : ℝ) t, Real.exp (-lam * t) *
            kernelIntegral (P (Real.toNNReal s))
              (fun y ↦ q y * IsConservative.feynmanKac P hP q
                (Real.toNNReal t - Real.toNNReal s) f y) x := by
        rw [MeasureTheory.integral_const_mul]
      _ = ∫ s in Ioo (0 : ℝ) t, H (s, t - s) := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro s hs
        have hs0 : 0 ≤ s := hs.1.le
        have hsub0 : 0 ≤ t - s := sub_nonneg.mpr hs.2.le
        have hsub : Real.toNNReal t - Real.toNNReal s = Real.toNNReal (t - s) := by
          apply NNReal.coe_injective
          rw [NNReal.coe_sub (Real.toNNReal_le_toNNReal hs.2.le),
            Real.coe_toNNReal t ht.le, Real.coe_toNNReal s hs0,
            Real.coe_toNNReal (t - s) hsub0]
        dsimp only [H]
        rw [hsub]
        congr 2
        ring
  have hcorr : P.kernelResolventReal lam
      (fun y ↦ q y * IsConservative.feynmanKacResolventReal P hP q lam f y) x =
      ∫ s in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), H (s, u) := by
    unfold SubMarkovKernelSemigroup.kernelResolventReal
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    dsimp only
    rw [hP.kernelIntegral_mul_feynmanKacResolventReal
      P hq hq0 hqC hlam (Real.toNNReal s) hf hfD x]
    rw [← MeasureTheory.integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _hu
    dsimp only [H]
    rw [show -lam * (s + u) = -lam * s + -lam * u by ring, Real.exp_add]
    ring
  have hdiff : P.kernelResolventReal lam f x -
      IsConservative.feynmanKacResolventReal P hP q lam f x =
      P.kernelResolventReal lam
        (fun y ↦ q y * IsConservative.feynmanKacResolventReal P hP q lam f y) x := by
    unfold SubMarkovKernelSemigroup.kernelResolventReal
    unfold IsConservative.feynmanKacResolventReal
    rw [← integral_sub hKernelInt hFKInt]
    calc
      (∫ t in Ioi (0 : ℝ),
          Real.exp (-lam * t) * kernelIntegral (P (Real.toNNReal t)) f x -
            Real.exp (-lam * t) *
              IsConservative.feynmanKac P hP q (Real.toNNReal t) f x) =
          ∫ t in Ioi (0 : ℝ), ∫ s in Ioo (0 : ℝ) t, H (s, t - s) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp only
        rw [← mul_sub]
        exact htime t ht
      _ = ∫ s in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), H (s, u) := htriangle
      _ = _ := hcorr.symm
  simp only [Pi.sub_apply]
  linarith only [hdiff]

end


end MarkovProcess.SubMarkovKernelSemigroup

end PortComputability
