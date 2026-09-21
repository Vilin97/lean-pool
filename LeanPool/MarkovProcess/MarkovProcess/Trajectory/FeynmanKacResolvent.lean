/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import LeanPool.MarkovProcess.MarkovProcess.Kernel.Resolvent
import LeanPool.MarkovProcess.MarkovProcess.Killed.Resolvent
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.FeynmanKacFunctional
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.ResolventExitDecomposition

/-!
# Feynman--Kac resolvents

This file Laplace-transforms the nonnegative extended-real Feynman--Kac operators and proves their
path-occupation formula, comparison with killed resolvents, and perturbation identities against
the unperturbed kernel resolvent.

Main results: `IsConservative.feynmanKacResolvent`,
`IsConservative.feynmanKacResolvent_eq_lintegral_path`,
`IsConservative.killedResolvent_le_feynmanKacResolvent`,
`IsFellerKernelSemigroup.integral_sub_feynmanKac_eq_integral_of_norm_le`,
`IsFellerKernelSemigroup.kernelResolvent_eq_feynmanKacResolvent_add`, and
`IsFellerKernelSemigroup.feynmanKacResolvent_eq_kernelResolvent_sub`.

No uniqueness statement for the associated resolvent equation is asserted.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MarkovProcess.SubMarkovKernelSemigroup

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [CompleteSpace alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

/-- The Feynman--Kac resolvent, obtained by Laplace-transforming the extended-real operators. -/
def IsConservative.feynmanKacResolvent (q : alpha → ℝ) (lam : ℝ)
    (f : alpha → ℝ≥0∞) (x : alpha) : ℝ≥0∞ :=
  ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) *
    IsConservative.feynmanKacENNReal P hP q (Real.toNNReal t) f x

omit [LocallyCompactSpace alpha] in
/-- The Feynman--Kac resolvent is measurable in the starting point. -/
theorem IsConservative.measurable_feynmanKacResolvent {q : alpha → ℝ}
    (hq : Measurable q) (lam : ℝ) {f : alpha → ℝ≥0∞} (hf : Measurable f) :
    Measurable (IsConservative.feynmanKacResolvent P hP q lam f) := by
  have hjoint : Measurable fun p : ℝ × alpha ↦
      ENNReal.ofReal (Real.exp (-lam * p.1)) *
        IsConservative.feynmanKacENNReal P hP q (Real.toNNReal p.1) f p.2 := by
    exact (ENNReal.measurable_ofReal.comp
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.comp
        measurable_fst)).mul
      ((IsConservative.measurable_feynmanKacENNReal_joint P hP hq hf).comp
        ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd))
  exact hjoint.lintegral_prod_left' (μ := volume.restrict (Ioi 0))

omit [LocallyCompactSpace alpha] in
/-- The Feynman--Kac resolvent is the expected discounted weighted path occupation. -/
theorem IsConservative.feynmanKacResolvent_eq_lintegral_path {q : alpha → ℝ}
    (hq : Measurable q) (lam : ℝ) {f : alpha → ℝ≥0∞} (hf : Measurable f) (x : alpha) :
    IsConservative.feynmanKacResolvent P hP q lam f x =
      ∫⁻ omega, (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) *
        (ENNReal.ofReal (Real.exp
          (-feynmanKacAdditiveFunctional q (Real.toNNReal t) omega)) *
          f (omega (Real.toNNReal t))))
        ∂(IsConservative.continuousProcess P hP x) := by
  have hA : Measurable fun p : ℝ × ContinuousPath alpha ↦
      feynmanKacAdditiveFunctional q (Real.toNNReal p.1) p.2 :=
    (stronglyMeasurable_feynmanKacAdditiveFunctional_joint hq).measurable.comp
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have heval : Measurable fun p : ℝ × ContinuousPath alpha ↦
      p.2 (Real.toNNReal p.1) :=
    (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hjoint : Measurable fun p : ℝ × ContinuousPath alpha ↦
      ENNReal.ofReal (Real.exp (-lam * p.1)) *
        (ENNReal.ofReal (Real.exp
          (-feynmanKacAdditiveFunctional q (Real.toNNReal p.1) p.2)) *
          f (p.2 (Real.toNNReal p.1))) :=
    (ENNReal.measurable_ofReal.comp
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.comp
        measurable_fst)).mul
      ((hA.neg.exp.ennreal_ofReal).mul (hf.comp heval))
  unfold IsConservative.feynmanKacResolvent IsConservative.feynmanKacENNReal
  calc
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) *
        ∫⁻ omega, ENNReal.ofReal (Real.exp
          (-feynmanKacAdditiveFunctional q (Real.toNNReal t) omega)) *
          f (omega (Real.toNNReal t))
          ∂(IsConservative.continuousProcess P hP x)) =
        ∫⁻ t in Ioi (0 : ℝ), ∫⁻ omega,
          ENNReal.ofReal (Real.exp (-lam * t)) *
            (ENNReal.ofReal (Real.exp
              (-feynmanKacAdditiveFunctional q (Real.toNNReal t) omega)) *
              f (omega (Real.toNNReal t)))
            ∂(IsConservative.continuousProcess P hP x) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro t _ht
      exact (lintegral_const_mul' _ _ (by finiteness)).symm
    _ = _ := lintegral_lintegral_swap hjoint.aemeasurable

/-- The kernel resolvent is the killed resolvent for the whole state space. -/
theorem IsFellerKernelSemigroup.kernelResolvent_eq_killedResolvent_univ
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (lam : ℝ) {f : alpha → ℝ≥0∞} (hf : Measurable f) (x : alpha) :
    P.kernelResolvent lam f x =
      IsConservative.killedResolvent P hP Set.univ isOpen_univ lam f x := by
  have hzero : P.kernelResolvent lam f x =
      IsConservative.feynmanKacResolvent P hP (fun _ ↦ 0) lam f x := by
    unfold SubMarkovKernelSemigroup.kernelResolvent IsConservative.feynmanKacResolvent
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t _ht
    unfold IsConservative.feynmanKacENNReal
    simp only [feynmanKacAdditiveFunctional, intervalIntegral.integral_zero,
      neg_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul]
    have heval := ContinuousPath.measurable_coordinateProcess
      (alpha := alpha) (Real.toNNReal t)
    have hin :
      (∫⁻ y, f y ∂(P (Real.toNNReal t) x)) =
        ∫⁻ omega, f (omega (Real.toNNReal t))
          ∂(IsConservative.continuousProcess P hP x) := by
      calc
        (∫⁻ y, f y ∂(P (Real.toNNReal t) x)) =
            ∫⁻ y, f y ∂((IsConservative.continuousProcess P hP).map
              (ContinuousPath.coordinateProcess (alpha := alpha) (Real.toNNReal t))) x := by
          have hmap : (IsConservative.continuousProcess P hP).map
              (ContinuousPath.coordinateProcess (alpha := alpha) (Real.toNNReal t)) =
                P (Real.toNNReal t) := by
            simpa only [ContinuousPath.coordinateProcess] using!
              hFeller.continuousProcess_map_eval_nnreal P hP hK (Real.toNNReal t)
          rw [hmap]
        _ = ∫⁻ omega, f (omega (Real.toNNReal t))
            ∂(IsConservative.continuousProcess P hP x) := by
          rw [Kernel.map_apply _ heval]
          exact lintegral_map hf heval
    exact congrArg (fun z ↦ ENNReal.ofReal (Real.exp (-lam * t)) * z) hin
  calc
    P.kernelResolvent lam f x =
        IsConservative.feynmanKacResolvent P hP (fun _ ↦ 0) lam f x := hzero
    _ = ∫⁻ omega, ContinuousPath.pathResolvent lam f omega
          ∂(IsConservative.continuousProcess P hP x) := by
      simpa only [ContinuousPath.pathResolvent, feynmanKacAdditiveFunctional,
        intervalIntegral.integral_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one,
        one_mul] using
        IsConservative.feynmanKacResolvent_eq_lintegral_path P hP
          (q := fun _ ↦ 0) measurable_const lam hf x
    _ = IsConservative.killedResolvent P hP Set.univ isOpen_univ lam f x :=
      IsConservative.lintegral_pathResolvent_eq_killedResolvent_univ P hP lam hf x

omit [LocallyCompactSpace alpha] in
/-- The Feynman--Kac resolvent dominates the resolvent of the process killed on leaving an open
set when the potential vanishes there.  No sign condition on the potential is needed away from
the open set. -/
theorem IsConservative.killedResolvent_le_feynmanKacResolvent
    {q : alpha → ℝ} (hq : Measurable q)
    {U : Set alpha} (hU : IsOpen U) (hqU : ∀ y ∈ U, q y = 0)
    (lam : ℝ) {f : alpha → ℝ≥0∞} (hf : Measurable f) (x : alpha) :
    IsConservative.killedResolvent P hP U hU lam f x ≤
      IsConservative.feynmanKacResolvent P hP q lam f x := by
  rw [IsConservative.killedResolvent_eq_lintegral P hP U hU lam hf x,
    IsConservative.feynmanKacResolvent_eq_lintegral_path P hP hq lam hf x]
  apply lintegral_mono
  intro omega
  apply setLIntegral_mono' measurableSet_Ioi
  intro t ht
  have ht0 : 0 < t := ht
  let u : NNReal := Real.toNNReal t
  by_cases hsurv : (u : ℝ≥0∞) < ContinuousPath.exitTime U omega
  · have hA0 : feynmanKacAdditiveFunctional q u omega = 0 := by
      rw [feynmanKacAdditiveFunctional_apply]
      calc
        (∫ s in (0 : ℝ)..u, q (omega (Real.toNNReal s))) = ∫ _s in (0 : ℝ)..u, 0 := by
          apply intervalIntegral.integral_congr
          intro s hs
          have hsu : Real.toNNReal s ≤ u := by
            apply Real.toNNReal_le_iff_le_coe.mpr
            rw [uIcc_of_le u.coe_nonneg] at hs
            exact hs.2
          exact hqU _ (ContinuousPath.mem_of_lt_exitTime U omega (Real.toNNReal s)
            ((ENNReal.coe_le_coe.mpr hsu).trans_lt hsurv))
        _ = 0 := intervalIntegral.integral_zero
    have hsurv' : t ∈ {r : ℝ | ((Real.toNNReal r : NNReal) : ℝ≥0∞) <
        ContinuousPath.exitTime U omega} := by simpa only [u] using! hsurv
    rw [indicator_of_mem hsurv', show feynmanKacAdditiveFunctional q (Real.toNNReal t) omega = 0
      by simpa only [u] using hA0, neg_zero, Real.exp_zero, ENNReal.ofReal_one,
      one_mul]
  · have hsurv' : t ∉ {r : ℝ | ((Real.toNNReal r : NNReal) : ℝ≥0∞) <
        ContinuousPath.exitTime U omega} := by simpa only [u] using! hsurv
    simp only [indicator_of_notMem hsurv', mul_zero, zero_le]

/-- Finite-time perturbation formula for the Feynman--Kac operators on bounded real
observables. -/
theorem IsFellerKernelSemigroup.integral_sub_feynmanKac_eq_integral_of_norm_le
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    {q : alpha → ℝ} (hq : Measurable q) {C : ℝ}
    (hq0 : ∀ y, 0 ≤ q y) (hqC : ∀ y, q y ≤ C)
    {f : alpha → ℝ} (hf : Measurable f)
    {D : ℝ} (hfD : ∀ y, |f y| ≤ D) (t : NNReal) (x : alpha) :
    (∫ y, f y ∂(P t x)) - IsConservative.feynmanKac P hP q t f x =
      ∫ s in (0 : ℝ)..t, ∫ y, q y *
        IsConservative.feynmanKac P hP q (t - Real.toNNReal s) f y
        ∂(P (Real.toNNReal s) x) := by
  have hC : 0 ≤ C := (hq0 x).trans (hqC x)
  let mu : Measure (ContinuousPath alpha) := IsConservative.continuousProcess P hP x
  let H : ℝ × ContinuousPath alpha → ℝ := fun p ↦
    q (p.2 (Real.toNNReal p.1)) *
      Real.exp (-(feynmanKacAdditiveFunctional q t p.2 -
        feynmanKacAdditiveFunctional q (Real.toNNReal p.1) p.2)) * f (p.2 t)
  have hevalJoint : Measurable fun p : ℝ × ContinuousPath alpha ↦
      p.2 (Real.toNNReal p.1) :=
    (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hAs : Measurable fun p : ℝ × ContinuousPath alpha ↦
      feynmanKacAdditiveFunctional q (Real.toNNReal p.1) p.2 :=
    (stronglyMeasurable_feynmanKacAdditiveFunctional_joint hq).measurable.comp
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hAt : Measurable fun p : ℝ × ContinuousPath alpha ↦
      feynmanKacAdditiveFunctional q t p.2 :=
    (stronglyMeasurable_feynmanKacAdditiveFunctional hq t).measurable.comp measurable_snd
  have hH : StronglyMeasurable H := by
    exact (((hq.comp hevalJoint).mul ((hAt.sub hAs).neg.exp)).mul
      ((hf.comp (ContinuousPath.measurable_coordinateProcess (alpha := alpha) t)).comp
        measurable_snd)).stronglyMeasurable
  have hD0 : 0 ≤ D := (abs_nonneg (f x)).trans (hfD x)
  have hHbound (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (t : ℝ))
      (omega : ContinuousPath alpha) : ‖H (s, omega)‖ ≤ C * D := by
    have hsNN : Real.toNNReal s ≤ t := Real.toNNReal_le_iff_le_coe.mpr hs.2
    have hAdiff : 0 ≤ feynmanKacAdditiveFunctional q t omega -
        feynmanKacAdditiveFunctional q (Real.toNNReal s) omega :=
      sub_nonneg.mpr (feynmanKacAdditiveFunctional_mono hq hq0 hqC hsNN omega)
    dsimp only [H]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hq0 _),
      abs_of_pos (Real.exp_pos _)]
    calc
      q (omega (Real.toNNReal s)) * Real.exp (-_) * |f (omega t)| ≤
          C * 1 * D := by
        exact mul_le_mul
          (mul_le_mul (hqC _)
            ((Real.exp_le_one_iff).mpr (neg_nonpos.mpr hAdiff))
            (Real.exp_pos _).le hC) (hfD _) (abs_nonneg _) (mul_nonneg hC zero_le_one)
      _ = C * D := by ring
  have hProdInt : Integrable (Function.uncurry fun (s : ℝ)
      (omega : ContinuousPath alpha) ↦ H (s, omega))
      ((volume.restrict (Ioc (0 : ℝ) t)).prod mu) := by
    refine Integrable.of_bound hH.aestronglyMeasurable (C * D) ?_
    change ∀ᵐ p : ℝ × ContinuousPath alpha
      ∂((volume.restrict (Ioc (0 : ℝ) t)).prod mu), ‖H p‖ ≤ C * D
    rw [Measure.ae_prod_iff_ae_ae (measurableSet_le hH.norm.measurable measurable_const)]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact Eventually.of_forall fun omega ↦ hHbound s ⟨hs.1.le, hs.2⟩ omega
  have hInner (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (t : ℝ)) :
      ∫ omega, H (s, omega) ∂mu =
        ∫ y, q y * IsConservative.feynmanKac P hP q
          (t - Real.toNNReal s) f y ∂(P (Real.toNNReal s) x) := by
    let u : NNReal := Real.toNNReal s
    let r : NNReal := t - u
    let W : ContinuousPath alpha → ℝ := fun omega ↦ q (omega u)
    let F : ContinuousPath alpha → ℝ := fun eta ↦
      Real.exp (-feynmanKacAdditiveFunctional q r eta) * f (eta r)
    have hu : u ≤ t := Real.toNNReal_le_iff_le_coe.mpr hs.2
    have hW : StronglyMeasurable[ContinuousPath.canonicalFiltration (alpha := alpha) u] W :=
      (hq.comp (ContinuousPath.measurable_coordinateProcess_canonicalFiltration
        (alpha := alpha) u)).stronglyMeasurable
    have hF : StronglyMeasurable F := by
      exact (((stronglyMeasurable_feynmanKacAdditiveFunctional hq r).measurable.neg.exp).mul
        (hf.comp (ContinuousPath.measurable_coordinateProcess
          (alpha := alpha) r))).stronglyMeasurable
    have hFbound : ∀ eta : ContinuousPath alpha, ‖F eta‖ ≤ D := by
      intro eta
      dsimp only [F]
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact (mul_le_mul_of_nonneg_right
        ((Real.exp_le_one_iff).mpr
          (neg_nonpos.mpr (feynmanKacAdditiveFunctional_nonneg hq0 r eta))) (abs_nonneg _)).trans
        (by simpa only [one_mul] using hfD _)
    have hIntFshift : Integrable (fun omega ↦ F (ContinuousPath.shift u omega)) mu :=
      Integrable.of_bound
        (((hF.comp_measurable (ContinuousPath.measurable_shift_fixed (alpha := alpha) u))
          ).aestronglyMeasurable) D (Eventually.of_forall fun omega ↦ hFbound _)
    have hIntWF : Integrable (fun omega ↦ W omega * F (ContinuousPath.shift u omega)) mu := by
      refine Integrable.of_bound
        ((((hW.mono ((ContinuousPath.canonicalFiltration (alpha := alpha)).le u)).mul
          (hF.comp_measurable (ContinuousPath.measurable_shift_fixed (alpha := alpha) u)))
          ).aestronglyMeasurable) (C * D) ?_
      exact Eventually.of_forall fun omega ↦ by
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hq0 _)]
        exact mul_le_mul (hqC _) (hFbound _) (norm_nonneg _) hC
    have hcond := hFeller.continuousProcess_condExp_shift P hP hK x u F hF D hFbound
    have hpull := condExp_mul_of_stronglyMeasurable_left (μ := mu) hW hIntWF hIntFshift
    have hfactor : (fun omega ↦ H (s, omega)) =
        fun omega ↦ W omega * F (ContinuousPath.shift u omega) := by
      funext omega
      dsimp only [H, W, F, u, r]
      rw [ContinuousPath.shift_apply, add_tsub_cancel_of_le hu,
        feynmanKacAdditiveFunctional_sub hq hq0 hqC hu]
      ring
    rw [hfactor]
    calc
      (∫ omega, W omega * F (ContinuousPath.shift u omega) ∂mu) =
          ∫ omega, mu[fun eta ↦ W eta * F (ContinuousPath.shift u eta)|
            ContinuousPath.canonicalFiltration (alpha := alpha) u] omega ∂mu := by
              rw [integral_condExp ((ContinuousPath.canonicalFiltration (alpha := alpha)).le u)]
      _ = ∫ omega, W omega *
            (∫ eta, F eta ∂IsConservative.continuousProcess P hP (omega u)) ∂mu := by
              refine integral_congr_ae (hpull.trans ?_)
              exact EventuallyEq.mul (EventuallyEq.refl _ _) hcond
      _ = ∫ omega, q (omega u) * IsConservative.feynmanKac P hP q r f (omega u) ∂mu := by
            rfl
      _ = ∫ y, q y * IsConservative.feynmanKac P hP q r f y ∂(P u x) := by
            simpa only [mu] using!
              (hFeller.integral_eval_continuousProcess_of_measurable P hP hK u x
                (hq.mul (IsConservative.measurable_feynmanKac P hP hq r hf)))
      _ = ∫ y, q y * IsConservative.feynmanKac P hP q
            (t - Real.toNNReal s) f y ∂(P (Real.toNNReal s) x) := by rfl
  have hPath : (∫ omega, f (omega t) ∂mu) -
      IsConservative.feynmanKac P hP q t f x =
        ∫ omega, (∫ s in (0 : ℝ)..t, H (s, omega)) ∂mu := by
    have hPlain : Integrable (fun omega : ContinuousPath alpha ↦ f (omega t)) mu :=
      Integrable.of_bound
        (((hf.comp (ContinuousPath.measurable_coordinateProcess
          (alpha := alpha) t)).stronglyMeasurable
          ).aestronglyMeasurable) D (Eventually.of_forall fun omega ↦ by
            rw [Real.norm_eq_abs]
            exact hfD _)
    have hWeighted : Integrable (fun omega : ContinuousPath alpha ↦
        Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t)) mu :=
      have hmeasWeighted : StronglyMeasurable fun omega : ContinuousPath alpha ↦
          Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t) := by
        have hmeas : Measurable fun omega : ContinuousPath alpha ↦
            Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t) :=
          ((stronglyMeasurable_feynmanKacAdditiveFunctional hq t).measurable.neg.exp).mul
            (hf.comp (ContinuousPath.measurable_coordinateProcess (alpha := alpha) t))
        exact hmeas.stronglyMeasurable
      Integrable.of_bound hmeasWeighted.aestronglyMeasurable D (Eventually.of_forall fun omega ↦ by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
          exact (mul_le_mul_of_nonneg_right
            ((Real.exp_le_one_iff).mpr
              (neg_nonpos.mpr (feynmanKacAdditiveFunctional_nonneg hq0 t omega)))
              (abs_nonneg _)).trans
            (by simpa only [one_mul] using hfD _))
    change (∫ omega, f (omega t) ∂mu) -
      (∫ omega, Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t) ∂mu) = _
    rw [← integral_sub hPlain hWeighted]
    refine integral_congr_ae (Eventually.of_forall fun omega ↦ ?_)
    change f (omega t) - Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t) =
      ∫ s in (0 : ℝ)..t, H (s, omega)
    have halg : f (omega t) - Real.exp (-feynmanKacAdditiveFunctional q t omega) * f (omega t) =
        (1 - Real.exp (-feynmanKacAdditiveFunctional q t omega)) * f (omega t) := by ring
    rw [halg, one_sub_exp_neg_feynmanKacAdditiveFunctional hq hq0 hqC,
      ← intervalIntegral.integral_mul_const]
  have hEval := hFeller.integral_eval_continuousProcess_of_measurable P hP hK t x hf
  calc
    (∫ y, f y ∂(P t x)) - IsConservative.feynmanKac P hP q t f x =
        (∫ omega, f (omega t) ∂mu) - IsConservative.feynmanKac P hP q t f x := by
          rw [hEval]
    _ = ∫ omega, (∫ s in (0 : ℝ)..t, H (s, omega)) ∂mu := hPath
    _ =
        ∫ s in (0 : ℝ)..t, ∫ omega, H (s, omega) ∂mu := by
          calc
            (∫ omega, (∫ s in (0 : ℝ)..t, H (s, omega)) ∂mu) =
                ∫ omega, (∫ s in Ioc (0 : ℝ) t, H (s, omega)) ∂mu := by
                  refine integral_congr_ae (Eventually.of_forall fun omega ↦ ?_)
                  exact intervalIntegral.integral_of_le t.coe_nonneg
            _ = ∫ s in Ioc (0 : ℝ) t, ∫ omega, H (s, omega) ∂mu :=
              (integral_integral_swap hProdInt).symm
            _ = ∫ s in (0 : ℝ)..t, ∫ omega, H (s, omega) ∂mu :=
              (intervalIntegral.integral_of_le t.coe_nonneg).symm
    _ = ∫ s in (0 : ℝ)..t, ∫ y, q y *
          IsConservative.feynmanKac P hP q (t - Real.toNNReal s) f y
          ∂(P (Real.toNNReal s) x) := by
            refine intervalIntegral.integral_congr fun s hs ↦ ?_
            rw [uIcc_of_le t.coe_nonneg] at hs
            exact hInner s hs

/-- Finite-time perturbation formula for a bounded nonnegative observable. -/
theorem IsFellerKernelSemigroup.integral_sub_feynmanKac_eq_integral
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    {q : alpha → ℝ} (hq : Measurable q) {C : ℝ}
    (hq0 : ∀ y, 0 ≤ q y) (hqC : ∀ y, q y ≤ C)
    {f : alpha → ℝ} (hf : Measurable f) (hf0 : ∀ y, 0 ≤ f y)
    {D : ℝ} (hfD : ∀ y, f y ≤ D) (t : NNReal) (x : alpha) :
    (∫ y, f y ∂(P t x)) - IsConservative.feynmanKac P hP q t f x =
      ∫ s in (0 : ℝ)..t, ∫ y, q y *
        IsConservative.feynmanKac P hP q (t - Real.toNNReal s) f y
        ∂(P (Real.toNNReal s) x) := by
  apply hFeller.integral_sub_feynmanKac_eq_integral_of_norm_le P hP hK hq hq0 hqC hf
    (fun y ↦ by rw [abs_of_nonneg (hf0 y)]; exact hfD y)

/-- Extended-real finite-time perturbation formula for bounded nonnegative observables. -/
theorem IsFellerKernelSemigroup.lintegral_eq_feynmanKacENNReal_add_lintegral
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    {q : alpha → ℝ} (hq : Measurable q) {C : ℝ}
    (hq0 : ∀ y, 0 ≤ q y) (hqC : ∀ y, q y ≤ C)
    {f : alpha → ℝ≥0∞} (hf : Measurable f) {D : NNReal}
    (hfD : ∀ y, f y ≤ (D : ℝ≥0∞)) (t : NNReal) (x : alpha) :
    (∫⁻ y, f y ∂(P t x)) =
      IsConservative.feynmanKacENNReal P hP q t f x +
        ∫⁻ s in Ioc (0 : ℝ) t, ∫⁻ y, ENNReal.ofReal (q y) *
          IsConservative.feynmanKacENNReal P hP q (t - Real.toNNReal s) f y
          ∂(P (Real.toNNReal s) x) := by
  have hC : 0 ≤ C := (hq0 x).trans (hqC x)
  let g : alpha → ℝ := fun y ↦ (f y).toReal
  let kR : ℝ → ℝ := fun s ↦ ∫ y, q y *
    IsConservative.feynmanKac P hP q (t - Real.toNNReal s) g y
    ∂(P (Real.toNNReal s) x)
  let kE : ℝ → ℝ≥0∞ := fun s ↦ ∫⁻ y, ENNReal.ofReal (q y) *
    IsConservative.feynmanKacENNReal P hP q (t - Real.toNNReal s) f y
    ∂(P (Real.toNNReal s) x)
  have hftop (y : alpha) : f y ≠ ∞ :=
    ne_of_lt ((hfD y).trans_lt ENNReal.coe_lt_top)
  have hg : Measurable g := hf.ennreal_toReal
  have hg0 (y : alpha) : 0 ≤ g y := ENNReal.toReal_nonneg
  have hgD (y : alpha) : g y ≤ D := by
    exact (ENNReal.toReal_le_toReal (hftop y) ENNReal.coe_ne_top).mpr (hfD y)
  have hgf : (fun y ↦ ENNReal.ofReal (g y)) = f := by
    funext y
    exact ENNReal.ofReal_toReal (hftop y)
  have hreal := hFeller.integral_sub_feynmanKac_eq_integral P hP hK hq hq0 hqC
    hg hg0 hgD t x
  have hrealAdd : (∫ y, g y ∂(P t x)) =
      IsConservative.feynmanKac P hP q t g x + ∫ s in (0 : ℝ)..t, kR s := by
    exact (sub_eq_iff_eq_add').mp hreal
  have hkR0 (s : ℝ) : 0 ≤ kR s := by
    dsimp only [kR]
    exact integral_nonneg fun y ↦ mul_nonneg (hq0 y)
      (IsConservative.feynmanKac_nonneg P hP hg0 y)
  have hkpoint (s : ℝ) : ENNReal.ofReal (kR s) = kE s := by
    let u : NNReal := Real.toNNReal s
    let r : NNReal := t - u
    let hMarkovU : IsMarkovKernel (P u) := hP.isMarkovKernel u
    have hterm : Integrable (fun y ↦ q y * IsConservative.feynmanKac P hP q r g y)
        (P u x) := by
      refine Integrable.of_bound
        ((hq.mul (IsConservative.measurable_feynmanKac P hP hq r hg)).stronglyMeasurable
          ).aestronglyMeasurable (C * D) ?_
      exact Eventually.of_forall fun y ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg (hq0 y) (IsConservative.feynmanKac_nonneg P hP hg0 y))]
        exact mul_le_mul (hqC y)
          (IsConservative.feynmanKac_le P hP hq0 hg0 hgD y)
          (IsConservative.feynmanKac_nonneg P hP hg0 y) hC
    change ENNReal.ofReal
      (∫ y, q y * IsConservative.feynmanKac P hP q r g y ∂(P u x)) =
        ∫⁻ y, ENNReal.ofReal (q y) *
          IsConservative.feynmanKacENNReal P hP q r f y ∂(P u x)
    rw [ofReal_integral_eq_lintegral_ofReal hterm
        (Eventually.of_forall fun y ↦ mul_nonneg (hq0 y)
          (IsConservative.feynmanKac_nonneg P hP hg0 y))]
    apply lintegral_congr
    intro y
    rw [ENNReal.ofReal_mul (hq0 y),
      IsConservative.ofReal_feynmanKac_eq_feynmanKacENNReal P hP hq hq0 r hg hg0 hgD y,
      hgf]
  have hkEmeas : Measurable kE := by
    let hFiniteJoint : IsFiniteKernel P.jointKernel := ⟨⟨1, ENNReal.one_lt_top, fun p ↦ by
        rw [jointKernel_apply]
        exact P.measure_univ_le_one p.1 p.2⟩⟩
    let K : Kernel ℝ alpha := Kernel.comap P.jointKernel
      (fun s ↦ (Real.toNNReal s, x)) (measurable_real_toNNReal.prodMk measurable_const)
    have hint : Measurable fun p : ℝ × alpha ↦ ENNReal.ofReal (q p.2) *
        IsConservative.feynmanKacENNReal P hP q
          (t - Real.toNNReal p.1) f p.2 := by
      exact (hq.ennreal_ofReal.comp measurable_snd).mul
        ((IsConservative.measurable_feynmanKacENNReal_joint P hP hq hf).comp
          ((measurable_const.sub (measurable_real_toNNReal.comp measurable_fst)).prodMk
            measurable_snd))
    have hlin := hint.lintegral_kernel_prod_right' (κ := K)
    simpa only [kE, K, Kernel.comap_apply, jointKernel_apply] using hlin
  have hkR_eq_toReal : kR = fun s ↦ (kE s).toReal := by
    funext s
    rw [← hkpoint s, ENNReal.toReal_ofReal (hkR0 s)]
  have hkRmeas : Measurable kR := by
    rw [hkR_eq_toReal]
    exact hkEmeas.ennreal_toReal
  have hkRle (s : ℝ) : kR s ≤ C * D := by
    let u : NNReal := Real.toNNReal s
    let r : NNReal := t - u
    let hMarkovU : IsMarkovKernel (P u) := hP.isMarkovKernel u
    dsimp only [kR]
    calc
      (∫ y, q y * IsConservative.feynmanKac P hP q r g y ∂(P u x)) ≤
          ∫ _y, C * D ∂(P u x) := by
        apply integral_mono_of_nonneg
        · exact Eventually.of_forall fun y ↦ mul_nonneg (hq0 y)
            (IsConservative.feynmanKac_nonneg P hP hg0 y)
        · exact integrable_const (C * D)
        · exact Eventually.of_forall fun y ↦ mul_le_mul (hqC y)
            (IsConservative.feynmanKac_le P hP hq0 hg0 hgD y)
            (IsConservative.feynmanKac_nonneg P hP hg0 y) hC
      _ = C * D := by simp only [integral_const, probReal_univ, one_smul]
  have hkRInt : IntervalIntegrable kR volume (0 : ℝ) t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg]
    refine IntegrableOn.of_bound (by simpa only [uIoc] using
        (measure_Ioc_lt_top : volume (Ioc (0 : ℝ) t) < ∞))
      hkRmeas.stronglyMeasurable.aestronglyMeasurable.restrict (C * D) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s _hs
    rw [Real.norm_eq_abs, abs_of_nonneg (hkR0 s)]
    exact hkRle s
  have hplainInt : Integrable g (P t x) := by
    let hMarkovT : IsMarkovKernel (P t) := hP.isMarkovKernel t
    refine Integrable.of_bound hg.stronglyMeasurable.aestronglyMeasurable D ?_
    exact Eventually.of_forall fun y ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 y)]
      exact hgD y
  have hplain : ENNReal.ofReal (∫ y, g y ∂(P t x)) = ∫⁻ y, f y ∂(P t x) := by
    rw [ofReal_integral_eq_lintegral_ofReal hplainInt (Eventually.of_forall hg0), hgf]
  have hfk : ENNReal.ofReal (IsConservative.feynmanKac P hP q t g x) =
      IsConservative.feynmanKacENNReal P hP q t f x := by
    rw [IsConservative.ofReal_feynmanKac_eq_feynmanKacENNReal P hP hq hq0 t hg hg0 hgD x,
      hgf]
  have hcorr : ENNReal.ofReal (∫ s in (0 : ℝ)..t, kR s) =
      ∫⁻ s in Ioc (0 : ℝ) t, kE s := by
    rw [intervalIntegral.integral_of_le t.coe_nonneg,
      ofReal_integral_eq_lintegral_ofReal
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg).mp hkRInt)
        (Eventually.of_forall hkR0)]
    exact lintegral_congr hkpoint
  have hof := congrArg ENNReal.ofReal hrealAdd
  rw [ENNReal.ofReal_add
    (IsConservative.feynmanKac_nonneg P hP hg0 x) (intervalIntegral.integral_nonneg
      t.coe_nonneg fun s _hs ↦ hkR0 s), hplain, hfk, hcorr] at hof
  exact hof

/-- Resolvent perturbation formula in its subtraction-free extended-real form. -/
theorem IsFellerKernelSemigroup.kernelResolvent_eq_feynmanKacResolvent_add
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    {q : alpha → ℝ} (hq : Measurable q) {C : ℝ}
    (hq0 : ∀ y, 0 ≤ q y) (hqC : ∀ y, q y ≤ C)
    {f : alpha → ℝ≥0∞} (hf : Measurable f) {D : NNReal}
    (hfD : ∀ y, f y ≤ (D : ℝ≥0∞)) (lam : ℝ) (x : alpha) :
    P.kernelResolvent lam f x =
      IsConservative.feynmanKacResolvent P hP q lam f x +
        P.kernelResolvent lam (fun y ↦ ENNReal.ofReal (q y) *
          IsConservative.feynmanKacResolvent P hP q lam f y) x := by
  have hC : 0 ≤ C := (hq0 x).trans (hqC x)
  let W : ℝ → ℝ≥0∞ := fun t ↦ ENNReal.ofReal (Real.exp (-lam * t))
  let B : ℝ × ℝ → ℝ≥0∞ := fun p ↦ ∫⁻ y, ENNReal.ofReal (q y) *
    IsConservative.feynmanKacENNReal P hP q (Real.toNNReal p.2) f y
    ∂(P (Real.toNNReal p.1) x)
  let H : ℝ × ℝ → ℝ≥0∞ := fun p ↦ W (p.1 + p.2) * B p
  let hFiniteJoint : IsFiniteKernel P.jointKernel := ⟨⟨1, ENNReal.one_lt_top, fun p ↦ by
    rw [jointKernel_apply]
    exact P.measure_univ_le_one p.1 p.2⟩⟩
  let K : Kernel (ℝ × ℝ) alpha := Kernel.comap P.jointKernel
    (fun p ↦ (Real.toNNReal p.1, x))
    ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_const)
  have hB : Measurable B := by
    have hint : Measurable fun p : (ℝ × ℝ) × alpha ↦ ENNReal.ofReal (q p.2) *
        IsConservative.feynmanKacENNReal P hP q (Real.toNNReal p.1.2) f p.2 := by
      exact (hq.ennreal_ofReal.comp measurable_snd).mul
        ((IsConservative.measurable_feynmanKacENNReal_joint P hP hq hf).comp
          ((measurable_real_toNNReal.comp (measurable_snd.comp measurable_fst)).prodMk
            measurable_snd))
    have hlin := hint.lintegral_kernel_prod_right' (κ := K)
    simpa only [B, K, Kernel.comap_apply, jointKernel_apply] using hlin
  have hW : Measurable W := by
    exact ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable
  have hH : Measurable H := (hW.comp measurable_add).mul hB
  have hsets (t : ℝ) : Ioc (0 : ℝ) t =ᶠ[ae volume] Ioo (0 : ℝ) t := by
    filter_upwards [volume.ae_ne t] with s hst
    apply propext
    constructor
    · intro hs
      exact ⟨hs.1, hs.2.lt_of_ne hst⟩
    · exact fun hs ↦ ⟨hs.1, hs.2.le⟩
  have htriangle :
      (∫⁻ t in Ioi (0 : ℝ), W t *
        ∫⁻ s in Ioc (0 : ℝ) t, ∫⁻ y, ENNReal.ofReal (q y) *
          IsConservative.feynmanKacENNReal P hP q
            (Real.toNNReal t - Real.toNNReal s) f y
          ∂(P (Real.toNNReal s) x)) =
        ∫⁻ s in Ioi (0 : ℝ), ∫⁻ u in Ioi (0 : ℝ), H (s, u) := by
    calc
      (∫⁻ t in Ioi (0 : ℝ), W t *
          ∫⁻ s in Ioc (0 : ℝ) t, ∫⁻ y, ENNReal.ofReal (q y) *
            IsConservative.feynmanKacENNReal P hP q
              (Real.toNNReal t - Real.toNNReal s) f y
            ∂(P (Real.toNNReal s) x)) =
          ∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioo (0 : ℝ) t, H (s, t - s) := by
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro t ht
        change W t *
          (∫⁻ s in Ioc (0 : ℝ) t, ∫⁻ y, ENNReal.ofReal (q y) *
            IsConservative.feynmanKacENNReal P hP q
              (Real.toNNReal t - Real.toNNReal s) f y
            ∂(P (Real.toNNReal s) x)) = ∫⁻ s in Ioo (0 : ℝ) t, H (s, t - s)
        rw [← lintegral_const_mul' (μ := volume.restrict (Ioc (0 : ℝ) t))
          (W t) _ (by dsimp only [W]; finiteness), Measure.restrict_congr_set (hsets t)]
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
        have htime : Real.toNNReal t - Real.toNNReal s = Real.toNNReal (t - s) := by
          apply NNReal.coe_injective
          rw [NNReal.coe_sub (Real.toNNReal_le_toNNReal hs.2.le),
            Real.coe_toNNReal t ht.le, Real.coe_toNNReal s hs.1.le,
            Real.coe_toNNReal (t - s) (sub_nonneg.mpr hs.2.le)]
        dsimp only [H, B]
        rw [← htime]
        congr 2
        ring
      _ = _ := intervalIntegral.lintegral_timeTriangle_sub hH
  have hWadd (s u : ℝ) : W (s + u) = W s * W u := by
    dsimp only [W]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  have hquadrant : (∫⁻ s in Ioi (0 : ℝ), ∫⁻ u in Ioi (0 : ℝ), H (s, u)) =
      P.kernelResolvent lam (fun y ↦ ENNReal.ofReal (q y) *
        IsConservative.feynmanKacResolvent P hP q lam f y) x := by
    unfold SubMarkovKernelSemigroup.kernelResolvent
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro s _hs
    let hMarkovS : IsMarkovKernel (P (Real.toNNReal s)) :=
      hP.isMarkovKernel (Real.toNNReal s)
    have hG : Measurable fun p : ℝ × alpha ↦ W p.1 *
        (ENNReal.ofReal (q p.2) *
          IsConservative.feynmanKacENNReal P hP q (Real.toNNReal p.1) f p.2) := by
      exact (hW.comp measurable_fst).mul
        ((hq.ennreal_ofReal.comp measurable_snd).mul
          ((IsConservative.measurable_feynmanKacENNReal_joint P hP hq hf).comp
            ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)))
    calc
      (∫⁻ u in Ioi (0 : ℝ), H (s, u)) =
          W s * ∫⁻ u in Ioi (0 : ℝ), ∫⁻ y, W u *
            (ENNReal.ofReal (q y) *
              IsConservative.feynmanKacENNReal P hP q (Real.toNNReal u) f y)
            ∂(P (Real.toNNReal s) x) := by
        rw [← lintegral_const_mul' (μ := volume.restrict (Ioi (0 : ℝ)))
          (W s) _ (by dsimp only [W]; finiteness)]
        apply lintegral_congr
        intro u
        dsimp only [H, B]
        rw [hWadd]
        rw [lintegral_const_mul' (W u) _ (by dsimp only [W]; finiteness)]
        simp only [mul_assoc]
      _ = W s * ∫⁻ y, (∫⁻ u in Ioi (0 : ℝ), W u *
              (ENNReal.ofReal (q y) *
                IsConservative.feynmanKacENNReal P hP q (Real.toNNReal u) f y))
            ∂(P (Real.toNNReal s) x) := by
        congr 1
        exact lintegral_lintegral_swap (μ := volume.restrict (Ioi (0 : ℝ)))
          (ν := P (Real.toNNReal s) x) hG.aemeasurable
      _ = W s * ∫⁻ y, ENNReal.ofReal (q y) *
            IsConservative.feynmanKacResolvent P hP q lam f y
            ∂(P (Real.toNNReal s) x) := by
        congr 1
        apply lintegral_congr
        intro y
        unfold IsConservative.feynmanKacResolvent
        rw [← lintegral_const_mul' (μ := volume.restrict (Ioi (0 : ℝ)))
          (ENNReal.ofReal (q y)) _ (by finiteness)]
        apply lintegral_congr
        intro u
        ring
  unfold SubMarkovKernelSemigroup.kernelResolvent IsConservative.feynmanKacResolvent
  have hFKmeas : Measurable fun t : ℝ ↦ W t *
      IsConservative.feynmanKacENNReal P hP q (Real.toNNReal t) f x :=
    hW.mul ((IsConservative.measurable_feynmanKacENNReal_joint P hP hq hf).comp
      (measurable_real_toNNReal.prodMk measurable_const))
  calc
    (∫⁻ t in Ioi (0 : ℝ), W t * ∫⁻ y, f y ∂(P (Real.toNNReal t) x)) =
        ∫⁻ t in Ioi (0 : ℝ), W t *
          (IsConservative.feynmanKacENNReal P hP q (Real.toNNReal t) f x +
            ∫⁻ s in Ioc (0 : ℝ) (Real.toNNReal t), ∫⁻ y, ENNReal.ofReal (q y) *
              IsConservative.feynmanKacENNReal P hP q
                (Real.toNNReal t - Real.toNNReal s) f y
              ∂(P (Real.toNNReal s) x)) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have hslice := hFeller.lintegral_eq_feynmanKacENNReal_add_lintegral P hP hK hq
        hq0 hqC hf hfD (Real.toNNReal t) x
      exact congrArg (fun z ↦ W t * z) (by
        simpa only [Real.coe_toNNReal t ht.le] using hslice)
    _ = (∫⁻ t in Ioi (0 : ℝ), W t *
          IsConservative.feynmanKacENNReal P hP q (Real.toNNReal t) f x) +
        ∫⁻ t in Ioi (0 : ℝ), W t *
          ∫⁻ s in Ioc (0 : ℝ) t, ∫⁻ y, ENNReal.ofReal (q y) *
            IsConservative.feynmanKacENNReal P hP q
              (Real.toNNReal t - Real.toNNReal s) f y
            ∂(P (Real.toNNReal s) x) := by
      rw [← lintegral_add_left (μ := volume.restrict (Ioi (0 : ℝ))) hFKmeas]
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [mul_add, Real.coe_toNNReal t ht.le]
    _ = _ := by
      rw [htriangle, hquadrant]
      simp only [W, SubMarkovKernelSemigroup.kernelResolvent,
        IsConservative.feynmanKacResolvent]

omit [MetricSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [CompleteSpace alpha] [Nonempty alpha] [LocallyCompactSpace alpha] in
/-- The kernel resolvent of a bounded observable is finite at a positive shift. -/
theorem IsConservative.kernelResolvent_lt_top (hP : P.IsConservative) (lam : ℝ) (hlam : 0 < lam)
    {f : alpha → ℝ≥0∞} {D : NNReal} (hfD : ∀ y, f y ≤ (D : ℝ≥0∞)) (x : alpha) :
    P.kernelResolvent lam f x < ∞ := by
  have hinner (t : ℝ) : (∫⁻ y, f y ∂(P (Real.toNNReal t) x)) ≤ (D : ℝ≥0∞) := by
    let hMarkovT : IsMarkovKernel (P (Real.toNNReal t)) :=
      hP.isMarkovKernel (Real.toNNReal t)
    calc
      (∫⁻ y, f y ∂(P (Real.toNNReal t) x)) ≤ ∫⁻ _y, (D : ℝ≥0∞)
          ∂(P (Real.toNNReal t) x) := lintegral_mono hfD
      _ = D := by simp only [lintegral_const, measure_univ, mul_one]
  have hweightInt : IntegrableOn (fun t : ℝ ↦ Real.exp (-lam * t) * (D : ℝ))
      (Ioi (0 : ℝ)) := by
    exact (integrableOn_exp_mul_Ioi (show -lam < 0 by linarith only [hlam]) 0).mul_const D
  unfold SubMarkovKernelSemigroup.kernelResolvent
  calc
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) *
        ∫⁻ y, f y ∂(P (Real.toNNReal t) x)) ≤
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t) * (D : ℝ)) := by
      apply setLIntegral_mono'
      · exact measurableSet_Ioi
      · intro t _ht
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le,
          show ENNReal.ofReal (D : ℝ) = (D : ℝ≥0∞) by simp only [ENNReal.ofReal_coe_nnreal]]
        exact mul_le_mul_of_nonneg_left (hinner t) bot_le
    _ = ENNReal.ofReal (∫ t in Ioi (0 : ℝ), Real.exp (-lam * t) * (D : ℝ)) := by
      exact (ofReal_integral_eq_lintegral_ofReal hweightInt
        (Eventually.of_forall fun t ↦ mul_nonneg (Real.exp_pos _).le D.coe_nonneg)).symm
    _ < ∞ := ENNReal.ofReal_lt_top

/-- The Feynman--Kac resolvent is the kernel resolvent minus its potential correction. -/
theorem IsFellerKernelSemigroup.feynmanKacResolvent_eq_kernelResolvent_sub
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    {q : alpha → ℝ} (hq : Measurable q) {C : ℝ}
    (hq0 : ∀ y, 0 ≤ q y) (hqC : ∀ y, q y ≤ C)
    {f : alpha → ℝ≥0∞} (hf : Measurable f) {D : NNReal}
    (hfD : ∀ y, f y ≤ (D : ℝ≥0∞)) (lam : ℝ) (hlam : 0 < lam) (x : alpha) :
    IsConservative.feynmanKacResolvent P hP q lam f x =
      P.kernelResolvent lam f x -
        P.kernelResolvent lam (fun y ↦ ENNReal.ofReal (q y) *
          IsConservative.feynmanKacResolvent P hP q lam f y) x := by
  have hadd := hFeller.kernelResolvent_eq_feynmanKacResolvent_add P hP hK hq hq0 hqC
    hf hfD lam x
  exact ENNReal.eq_sub_of_add_eq'
    (IsConservative.kernelResolvent_lt_top P hP lam hlam hfD x).ne hadd.symm



end

end MarkovProcess.SubMarkovKernelSemigroup
