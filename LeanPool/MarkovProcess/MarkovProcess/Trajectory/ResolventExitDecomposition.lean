/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.ExitTimeLaplace
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.StoppingLtTop

/-!
# Resolvent decomposition at an exit time

This file splits the whole-space path resolvent at the first exit time from an open set.  The
occupation before exit is the killed resolvent; on finite exit, the remaining occupation is the
discounted whole-space resolvent restarted from the exit location.  The restart step uses the
strong Markov property on `{exitTime U < ⊤}` and is valid for arbitrary nonnegative extended
measurable observables.

Main definitions and results: `ContinuousPath.pathResolvent`,
`ContinuousPath.measurable_pathResolvent`,
`IsConservative.lintegral_pathResolvent_eq_killedResolvent_univ`, and
`IsFellerKernelSemigroup.lintegral_pathResolvent_eq_killedResolvent_add`.

No integrability or almost-sure finiteness of the exit time is asserted.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MarkovProcess

namespace ContinuousPath

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

/-- The discounted occupation of a nonnegative extended observable along one continuous path. -/
def pathResolvent (lam : ℝ) (f : alpha → ℝ≥0∞)
    (omega : ContinuousPath alpha) : ℝ≥0∞ :=
  ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) *
    f (omega (Real.toNNReal t))

omit [CompleteSpace alpha] [Nonempty alpha] [LocallyCompactSpace alpha] in
/-- The path resolvent is measurable when its observable is measurable. -/
theorem measurable_pathResolvent (lam : ℝ) {f : alpha → ℝ≥0∞}
    (hf : Measurable f) : Measurable (pathResolvent lam f) := by
  have heval : Measurable fun p : ℝ × ContinuousPath alpha ↦ p.2 (Real.toNNReal p.1) :=
    (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hjoint : Measurable (fun p : ℝ × ContinuousPath alpha ↦
      ENNReal.ofReal (Real.exp (-lam * p.1)) * f (p.2 (Real.toNNReal p.1))) := by
    exact (ENNReal.measurable_ofReal.comp
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.comp
        measurable_fst)).mul (hf.comp heval)
  exact hjoint.lintegral_prod_left' (μ := volume.restrict (Set.Ioi 0))

end

end ContinuousPath

namespace SubMarkovKernelSemigroup

noncomputable section

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

omit [LocallyCompactSpace alpha] in
/-- Expected discounted path occupation is the killed resolvent for the whole state space. -/
theorem IsConservative.lintegral_pathResolvent_eq_killedResolvent_univ
    (lam : ℝ) {f : alpha → ℝ≥0∞} (hf : Measurable f) (x : alpha) :
    ∫⁻ omega, ContinuousPath.pathResolvent lam f omega
        ∂(IsConservative.continuousProcess P hP x) =
      IsConservative.killedResolvent P hP Set.univ isOpen_univ lam f x := by
  rw [IsConservative.killedResolvent_eq_lintegral P hP Set.univ isOpen_univ lam hf x]
  refine lintegral_congr fun omega ↦ setLIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
  rw [(ContinuousPath.exitTime_eq_top_iff Set.univ omega).mpr fun _ ↦ Set.mem_univ _]
  have ht : t ∈ {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ⊤} := ENNReal.coe_lt_top
  rw [Set.indicator_of_mem ht]

/-- Translation of a nonnegative Lebesgue integral on a right half-line. -/
private theorem lintegral_comp_add_right_Ioi (h : ℝ → ℝ≥0∞) (A : ℝ) :
    ∫⁻ s in Set.Ioi (0 : ℝ), h (s + A) = ∫⁻ t in Set.Ioi A, h t := by
  have hcv := (MeasureTheory.measurePreserving_add_right volume A).setLIntegral_comp_emb
    (measurableEmbedding_addRight A) h (Set.Ioi (0 : ℝ))
  simpa only [zero_add, Set.image_add_const_Ioi] using hcv

/-- A nonnegative integral on the positive half-line splits at a nonnegative time. -/
private theorem lintegral_Ioi_zero_eq_Ioo_add_Ioi (h : ℝ → ℝ≥0∞) (A : ℝ) (hA : 0 ≤ A) :
    ∫⁻ t in Set.Ioi (0 : ℝ), h t =
      (∫⁻ t in Set.Ioo (0 : ℝ) A, h t) + ∫⁻ t in Set.Ioi A, h t := by
  rcases hA.eq_or_lt with rfl | hA
  · simp only [lt_self_iff_false, not_false_eq_true, Ioo_eq_empty, Measure.restrict_empty,
      lintegral_zero_measure, zero_add]
  · rw [show volume.restrict (Set.Ioi A) = volume.restrict (Set.Ici A) from
      Measure.restrict_congr_set Ioi_ae_eq_Ici]
    rw [← lintegral_union measurableSet_Ici
      ((Iio_disjoint_Ici le_rfl).mono Set.Ioo_subset_Iio_self le_rfl)]
    rw [Set.Ioo_union_Ici_eq_Ioi hA]

omit [CompleteSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [Nonempty alpha] [LocallyCompactSpace alpha] in
/-- Pathwise splitting of discounted occupation into the part before exit and the shifted tail. -/
private theorem pathResolvent_eq_preExit_add_restart
    (U : Set alpha) (lam : ℝ) (f : alpha → ℝ≥0∞)
    (omega : ContinuousPath alpha) :
    ContinuousPath.pathResolvent lam f omega =
      (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) *
        {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) <
          ContinuousPath.exitTime U omega}.indicator
          (fun t ↦ f (omega (Real.toNNReal t))) t) +
      ({omega | ContinuousPath.exitTime U omega < ⊤} : Set _).indicator
        (fun omega ↦ ENNReal.ofReal
            (Real.exp (-lam * (ContinuousPath.exitTime U omega).toReal)) *
          ContinuousPath.pathResolvent lam f
            (ContinuousPath.shift ((ContinuousPath.exitTime U omega).untopD 0) omega)) omega := by
  let tau := ContinuousPath.exitTime U omega
  let H : ℝ → ℝ≥0∞ := fun t ↦
    ENNReal.ofReal (Real.exp (-lam * t)) * f (omega (Real.toNNReal t))
  let T : Set ℝ := {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < tau}
  have hfun : (fun t ↦ ENNReal.ofReal (Real.exp (-lam * t)) *
        T.indicator (fun t ↦ f (omega (Real.toNNReal t))) t) = T.indicator H := by
    funext t
    by_cases ht : t ∈ T
    · simp only [neg_mul, Set.indicator_of_mem ht, H]
    · simp only [neg_mul, Set.indicator_of_notMem ht, mul_zero, H]
  by_cases htau : tau = ⊤
  · have hnot : omega ∉ {omega | ContinuousPath.exitTime U omega < ⊤} := by
      change ¬tau < ⊤
      rw [htau]
      exact lt_irrefl _
    rw [Set.indicator_of_notMem hnot, add_zero]
    change (∫⁻ t in Set.Ioi (0 : ℝ), H t) = _
    rw [hfun, setLIntegral_indicator]
    · have hT : T ∩ Set.Ioi (0 : ℝ) = Set.Ioi 0 := by
        change {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < tau} ∩ Set.Ioi 0 = _
        rw [htau]
        exact ContinuousPath.survivalSet_top
      rw [hT]
    · exact measurableSet_lt
        (measurable_coe_nnreal_ennreal.comp measurable_real_toNNReal) measurable_const
  · lift tau to NNReal using htau with a ha
    have htau' : tau ≠ ⊤ := by rw [← ha]; exact WithTop.coe_ne_top
    have haReal : tau.toReal = (a : ℝ) := by rw [← ha]; simp only [ENNReal.coe_toReal]
    have hmem : omega ∈ {omega | ContinuousPath.exitTime U omega < ⊤} := by
      change tau < ⊤
      rw [← ha]
      exact WithTop.coe_lt_top a
    rw [Set.indicator_of_mem hmem]
    change (∫⁻ t in Set.Ioi (0 : ℝ), H t) = _
    have hpre : (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) *
          T.indicator (fun t ↦ f (omega (Real.toNNReal t))) t) =
        ∫⁻ t in Set.Ioo (0 : ℝ) (a : ℝ), H t := by
      rw [hfun, setLIntegral_indicator]
      · rw [ContinuousPath.survivalSet_ne_top tau htau', haReal]
      · exact measurableSet_lt
          (measurable_coe_nnreal_ennreal.comp measurable_real_toNNReal) measurable_const
    rw [lintegral_Ioi_zero_eq_Ioo_add_Ioi H (a : ℝ) a.coe_nonneg]
    congr 1
    · exact hpre.symm
    · rw [← lintegral_comp_add_right_Ioi H (a : ℝ)]
      have hexit : ContinuousPath.exitTime U omega = (a : ℝ≥0∞) := ha.symm
      rw [hexit]
      simp only [ENNReal.coe_toReal]
      change (∫⁻ s in Set.Ioi (0 : ℝ), H (s + (a : ℝ))) =
        ENNReal.ofReal (Real.exp (-lam * (a : ℝ))) *
          (∫⁻ s in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * s)) *
            f (ContinuousPath.shift a omega (Real.toNNReal s)))
      have hweight_ne_top : ENNReal.ofReal (Real.exp (-lam * (a : ℝ))) ≠ ⊤ :=
        ENNReal.ofReal_ne_top
      rw [← lintegral_const_mul'
        (ENNReal.ofReal (Real.exp (-lam * (a : ℝ)))) _
        hweight_ne_top]
      refine setLIntegral_congr_fun measurableSet_Ioi fun s hs ↦ ?_
      have hs0 : 0 ≤ s := (Set.mem_Ioi.mp hs).le
      simp only [H, ContinuousPath.shift_apply]
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      have hexp : -lam * (s + (a : ℝ)) = -lam * (a : ℝ) + -lam * s := by ring
      rw [hexp]
      congr 1
      rw [Real.toNNReal_add hs0 a.coe_nonneg, Real.toNNReal_of_nonneg a.coe_nonneg]
      apply congrArg (fun u : NNReal ↦ f (omega u))
      exact add_comm (Real.toNNReal s) a

/-- **Strong-Markov resolvent decomposition at an exit time.**  The expected discounted path
occupation is the killed resolvent plus, on finite exit, the discounted occupation restarted from
the exit location.  At discount `lam = 0` this is the corresponding Green-function decomposition. -/
theorem IsFellerKernelSemigroup.lintegral_pathResolvent_eq_killedResolvent_add
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (U : Set alpha) (hU : IsOpen U) (lam : ℝ)
    {f : alpha → ℝ≥0∞} (hf : Measurable f) (x : alpha) :
    ∫⁻ omega, ContinuousPath.pathResolvent lam f omega
        ∂(IsConservative.continuousProcess P hP x) =
      IsConservative.killedResolvent P hP U hU lam f x +
        ∫⁻ omega, ({omega | ContinuousPath.exitTime U omega < ⊤} : Set _).indicator
          (fun omega ↦ ENNReal.ofReal
              (Real.exp (-lam * (ContinuousPath.exitTime U omega).toReal)) *
            (∫⁻ eta, ContinuousPath.pathResolvent lam f eta
              ∂(IsConservative.continuousProcess P hP
                (omega ((ContinuousPath.exitTime U omega).untopD 0))))) omega
          ∂(IsConservative.continuousProcess P hP x) := by
  let Q : Kernel alpha (ContinuousPath alpha) := IsConservative.continuousProcess P hP
  let tau : ContinuousPath alpha → ℝ≥0∞ := ContinuousPath.exitTime U
  let S : Set (ContinuousPath alpha) := {omega | tau omega < ⊤}
  let W : ContinuousPath alpha → ℝ≥0∞ := fun omega ↦
    ENNReal.ofReal (Real.exp (-lam * (tau omega).toReal))
  let F : ContinuousPath alpha → ℝ≥0∞ := ContinuousPath.pathResolvent lam f
  have htau := ContinuousPath.isStoppingTime_exitTime U hU
  have hS : MeasurableSet[htau.measurableSpace] S := by
    exact StoppingTime.measurableSet_stoppingTime_lt_top htau
  have hW : Measurable[htau.measurableSpace] W := by
    exact ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp
        (measurable_const.mul (ENNReal.measurable_toReal.comp htau.measurable)))
  have hF : Measurable F := ContinuousPath.measurable_pathResolvent lam hf
  have hPre : Measurable (fun omega : ContinuousPath alpha ↦
      ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) *
        {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < tau omega}.indicator
          (fun t ↦ f (omega (Real.toNNReal t))) t) := by
    have heval : Measurable fun p : ℝ × ContinuousPath alpha ↦
        p.2 (Real.toNNReal p.1) :=
      (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
        ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
    have hset : MeasurableSet {p : ℝ × ContinuousPath alpha |
        ((Real.toNNReal p.1 : NNReal) : ℝ≥0∞) < tau p.2} :=
      measurableSet_lt
        (measurable_coe_nnreal_ennreal.comp
          (measurable_real_toNNReal.comp measurable_fst))
        ((ContinuousPath.measurable_exitTime U hU).comp measurable_snd)
    have hjoint : Measurable (fun p : ℝ × ContinuousPath alpha ↦
        ENNReal.ofReal (Real.exp (-lam * p.1)) *
          {p : ℝ × ContinuousPath alpha |
            ((Real.toNNReal p.1 : NNReal) : ℝ≥0∞) < tau p.2}.indicator
            (fun p ↦ f (p.2 (Real.toNNReal p.1))) p) := by
      exact (ENNReal.measurable_ofReal.comp
        ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.comp
          measurable_fst)).mul ((hf.comp heval).indicator hset)
    exact hjoint.lintegral_prod_left' (μ := volume.restrict (Set.Ioi 0))
  have hRestart :
      ∫⁻ omega, W omega * S.indicator
          (fun omega ↦ F (ContinuousPath.shift ((tau omega).untopD 0) omega)) omega ∂Q x =
        ∫⁻ omega, W omega * S.indicator
          (fun omega ↦ ∫⁻ eta, F eta ∂Q (omega ((tau omega).untopD 0))) omega ∂Q x := by
    apply StoppingTime.lintegral_mul_indicator_of_restrict_map
      (mu := Q x)
      (kappa := Kernel.comap Q (fun omega ↦ omega ((tau omega).untopD 0))
        (ContinuousPath.measurable_eval_untopD_stoppingTime tau htau))
      (Y := fun omega ↦ ContinuousPath.shift ((tau omega).untopD 0) omega)
      (m := htau.measurableSpace) (S := S) (F := F) (W := W)
    · exact ContinuousPath.measurable_shift_untopD_stoppingTime tau htau
    · exact htau.measurableSpace_le
    · exact hS
    · intro A hA
      exact hFeller.continuousProcess_restrict_map_shift_stoppingTime_lt_top
        P hP hK x tau htau A hA
    · exact hF
    · exact hW
  have hRestart' :
      ∫⁻ omega, S.indicator
          (fun omega ↦ W omega * F
            (ContinuousPath.shift ((tau omega).untopD 0) omega)) omega ∂Q x =
        ∫⁻ omega, S.indicator
          (fun omega ↦ W omega * ∫⁻ eta, F eta ∂Q
            (omega ((tau omega).untopD 0))) omega ∂Q x := by
    rw [show S.indicator (fun omega ↦ W omega * F
          (ContinuousPath.shift ((tau omega).untopD 0) omega)) =
        fun omega ↦ W omega * S.indicator
          (fun omega ↦ F (ContinuousPath.shift ((tau omega).untopD 0) omega)) omega by
      funext omega
      by_cases hs : omega ∈ S
      · simp only [hs, Set.indicator_of_mem]
      · simp only [hs, not_false_eq_true, Set.indicator_of_notMem, mul_zero]]
    rw [show S.indicator (fun omega ↦ W omega * ∫⁻ eta, F eta ∂Q
          (omega ((tau omega).untopD 0))) =
        fun omega ↦ W omega * S.indicator
          (fun omega ↦ ∫⁻ eta, F eta ∂Q (omega ((tau omega).untopD 0))) omega by
      funext omega
      by_cases hs : omega ∈ S
      · simp only [hs, Set.indicator_of_mem]
      · simp only [hs, not_false_eq_true, Set.indicator_of_notMem, mul_zero]]
    exact hRestart
  change (∫⁻ omega, F omega ∂Q x) = _
  have hSplit : ∀ omega, F omega =
      (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) *
        {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < tau omega}.indicator
          (fun t ↦ f (omega (Real.toNNReal t))) t) +
      S.indicator (fun omega ↦ W omega * F
        (ContinuousPath.shift ((tau omega).untopD 0) omega)) omega := by
    intro omega
    exact pathResolvent_eq_preExit_add_restart U lam f omega
  rw [lintegral_congr hSplit, lintegral_add_left hPre]
  rw [← IsConservative.killedResolvent_eq_lintegral P hP U hU lam hf x]
  change IsConservative.killedResolvent P hP U hU lam f x +
      ∫⁻ omega, S.indicator
        (fun omega ↦ W omega * F
          (ContinuousPath.shift ((tau omega).untopD 0) omega)) omega ∂Q x = _
  rw [hRestart']

end

end SubMarkovKernelSemigroup

end MarkovProcess
