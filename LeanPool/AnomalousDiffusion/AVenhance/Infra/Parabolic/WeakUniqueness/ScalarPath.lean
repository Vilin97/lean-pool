/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.WeakUniqueness.Distribution
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.ODE.Linear.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Recovering an integral path from the scalar weak time equation

Separated tests against a fixed spatial Fourier mode give a scalar distributional equation.
Subtracting the forcing primitive turns it into zero pairing against all compactly supported
interior tests, where the distribution separation lemma applies.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace AVenhance.Infra.Parabolic.WeakUniqueness

/-- A smooth compactly supported interior function has a smooth terminal primitive. -/
noncomputable def ScalarPath.terminalPrimitive (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in t..(1 : ℝ), g s

theorem ScalarPath.terminalPrimitive_hasDerivAt {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) (t : ℝ) :
    HasDerivAt (ScalarPath.terminalPrimitive g) (-g t) t := by
  exact intervalIntegral.integral_hasDerivAt_left
    (hg.continuous.intervalIntegrable t 1)
    (hg.continuous.stronglyMeasurableAtFilter volume (𝓝 t))
    hg.continuous.continuousAt

theorem ScalarPath.terminalPrimitive_deriv {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) :
    deriv (ScalarPath.terminalPrimitive g) = fun t => -g t := by
  funext t
  exact (ScalarPath.terminalPrimitive_hasDerivAt hg t).deriv

theorem ScalarPath.terminalPrimitive_contDiff {g : ℝ → ℝ}
    (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (ScalarPath.terminalPrimitive g) := by
  apply (contDiff_infty_iff_deriv).2
  refine ⟨fun t => (ScalarPath.terminalPrimitive_hasDerivAt hg t).differentiableAt, ?_⟩
  rw [ScalarPath.terminalPrimitive_deriv hg]
  exact hg.neg

theorem ScalarPath.terminalPrimitive_zero_of_ge_one {g : ℝ → ℝ}
    (hgSupport : tsupport g ⊆ Set.Ioo (0 : ℝ) 1)
    (t : ℝ) (ht : 1 ≤ t) : ScalarPath.terminalPrimitive g t = 0 := by
  by_cases h : t = 1
  · subst t
    simp [ScalarPath.terminalPrimitive]
  · have h1t : 1 < t := lt_of_le_of_ne ht (Ne.symm h)
    rw [ScalarPath.terminalPrimitive, intervalIntegral.integral_symm]
    have hz : ∀ᵐ s ∂volume, s ∈ Set.uIoc (1 : ℝ) t → g s = 0 := by
      filter_upwards with s hs
      by_contra hgs
      have hts : s ∈ tsupport g := subset_closure hgs
      have hsIoo := hgSupport hts
      have hsIoc : s ∈ Set.Ioc (1 : ℝ) t := by
        simpa [uIoc_of_le ht] using hs
      have hsLeft : 1 < s := hsIoc.1
      rcases hsIoo with ⟨_, hsUpper⟩
      linarith
    rw [intervalIntegral.integral_congr_ae hz]
    simp

/-- Clamp real time to the closed unit interval for a weak scalar path. -/
def ScalarPath.clampUnitTime (t : ℝ) : ℝ := max 0 (min 1 t)

theorem ScalarPath.clampUnitTime_continuous : Continuous ScalarPath.clampUnitTime := by
  exact continuous_const.max (continuous_const.min continuous_id)

theorem ScalarPath.clampUnitTime_mem (t : ℝ) : ScalarPath.clampUnitTime t ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · dsimp [ScalarPath.clampUnitTime]
    exact le_max_left _ _
  · dsimp [ScalarPath.clampUnitTime]
    exact max_le (by norm_num) (min_le_left _ _)

theorem ScalarPath.clampUnitTime_eq {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ScalarPath.clampUnitTime t = t := by
  simp [ScalarPath.clampUnitTime, max_eq_right ht.1, min_eq_right ht.2]

/-- A scalar weak time equation with integrable forcing has the corresponding absolutely
continuous integral path. -/
theorem scalar_weak_tests_imply_integral_path {u q : ℝ → ℝ} {u₀ : ℝ}
    (hu : ContinuousOn u (Set.Icc (0 : ℝ) 1))
    (hq : IntervalIntegrable q volume 0 1)
    (hweak : ∀ η : ℝ → ℝ, ContDiff ℝ ∞ η →
      (∀ t, 1 ≤ t → η t = 0) →
      ∫ t in (0 : ℝ)..1, (-(u t) * deriv η t + q t * η t) = u₀ * η 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, u t = u₀ - ∫ s in (0 : ℝ)..t, q s := by
  let P : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, q s
  have hPcont : ContinuousOn P (Set.uIcc (0 : ℝ) 1) :=
    AVenhance.Infra.ODE.continuousOn_intervalPrimitive hq
  have hPac : AbsolutelyContinuousOnInterval P 0 1 :=
    AVenhance.Infra.ODE.IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_vector
      hq left_mem_uIcc
  have hPderiv := AVenhance.Infra.ODE.ae_hasDerivAt_intervalPrimitive hq
  let F : ℝ → ℝ := fun t => u (ScalarPath.clampUnitTime t) - u₀ + P (ScalarPath.clampUnitTime t)
  have hclampRange (t : ℝ) : ScalarPath.clampUnitTime t ∈ Set.uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ScalarPath.clampUnitTime_mem t
  have hclampRangeIcc (t : ℝ) : ScalarPath.clampUnitTime t ∈ Set.Icc (0 : ℝ) 1 :=
    ScalarPath.clampUnitTime_mem t
  have huExtOn : ContinuousOn (fun t => u (ScalarPath.clampUnitTime t)) Set.univ := by
    refine hu.comp (ScalarPath.clampUnitTime_continuous.continuousOn) ?_
    intro t ht
    exact hclampRangeIcc t
  have hPExtOn : ContinuousOn (fun t => P (ScalarPath.clampUnitTime t)) Set.univ := by
    refine hPcont.comp (ScalarPath.clampUnitTime_continuous.continuousOn) ?_
    intro t ht
    exact hclampRange t
  have hF : Continuous F := by
    apply continuousOn_univ.mp
    exact huExtOn.sub continuousOn_const |>.add hPExtOn
  have hzero : ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      tsupport g ⊆ Set.Ioo (0 : ℝ) 1 →
      ∫ t in (0 : ℝ)..1, F t * g t = 0 := by
    intro g hg hcompact hgsupport
    let η : ℝ → ℝ := ScalarPath.terminalPrimitive g
    have hηsmooth : ContDiff ℝ ∞ η := ScalarPath.terminalPrimitive_contDiff hg
    have hηterminal : ∀ t, 1 ≤ t → η t = 0 :=
      ScalarPath.terminalPrimitive_zero_of_ge_one hgsupport
    have hweakη := hweak η hηsmooth hηterminal
    have hη₁ : η 1 = 0 := hηterminal 1 le_rfl
    have hηac : AbsolutelyContinuousOnInterval η 0 1 := by
      have hηone : ContDiff ℝ 1 η := hηsmooth.of_le (by simp)
      exact hηone.contDiffOn.absolutelyContinuousOnInterval
    have hηderiv : deriv η = fun t => -g t := by
      dsimp [η]
      exact ScalarPath.terminalPrimitive_deriv hg
    have hPqη : ∫ t in (0 : ℝ)..1, deriv P t * η t =
        ∫ t in (0 : ℝ)..1, q t * η t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hPderiv] with t ht
      intro ht'
      have htcc : t ∈ Set.uIcc (0 : ℝ) 1 := uIoc_subset_uIcc ht'
      exact congrArg (fun a : ℝ => a * η t) (ht htcc).deriv
    have hIBP := hPac.integral_mul_deriv_eq_deriv_mul hηac
    have hP₀ : P 0 = 0 := by simp [P]
    have hPηderiv : ∫ t in (0 : ℝ)..1, P t * deriv η t =
        -∫ t in (0 : ℝ)..1, q t * η t := by
      rw [hIBP, hPqη]
      simp [P, hη₁]
    have hηderivInt : ∫ t in (0 : ℝ)..1, deriv η t = η 1 - η 0 :=
      hηac.integral_deriv_eq_sub
    have hηdcont : Continuous (deriv η) := by
      rw [hηderiv]
      exact hg.continuous.neg
    have hqηInt : IntervalIntegrable (fun t => q t * η t) volume 0 1 :=
      hq.mul_continuousOn hηsmooth.continuous.continuousOn
    have huηdInt : IntervalIntegrable (fun t => u t * deriv η t) volume 0 1 :=
      (hu.mul hηdcont.continuousOn).intervalIntegrable_of_Icc (by norm_num)
    have hAInt : IntervalIntegrable
        (fun t => -(u t * deriv η t) + q t * η t) volume 0 1 := by
      exact huηdInt.neg.add hqηInt
    have hBInt : IntervalIntegrable (fun t => u₀ * deriv η t) volume 0 1 := by
      exact (hηdcont.intervalIntegrable 0 1).const_mul u₀
    have hPηInt : IntervalIntegrable (fun t => P t * deriv η t) volume 0 1 :=
      (hPcont.mul hηdcont.continuousOn).intervalIntegrable
    have hCInt : IntervalIntegrable
        (fun t => -(P t * deriv η t) - q t * η t) volume 0 1 := by
      exact hPηInt.neg.add hqηInt.neg
    have hTargetEq (t : ℝ) :
        -(u t - u₀ + P t) * deriv η t =
          (-(u t * deriv η t) + q t * η t) + u₀ * deriv η t +
            (-(P t * deriv η t) - q t * η t) := by ring
    have hTarget :
        ∫ t in (0 : ℝ)..1, -(u t - u₀ + P t) * deriv η t =
          (∫ t in (0 : ℝ)..1, (-(u t * deriv η t) + q t * η t)) +
            u₀ * (∫ t in (0 : ℝ)..1, deriv η t) +
            (∫ t in (0 : ℝ)..1, (-(P t * deriv η t) - q t * η t)) := by
      calc
        _ = ∫ t in (0 : ℝ)..1,
              ((-(u t * deriv η t) + q t * η t) + u₀ * deriv η t) +
                (-(P t * deriv η t) - q t * η t) := by
              apply intervalIntegral.integral_congr_ae
              filter_upwards with t ht
              exact hTargetEq t
        _ = (∫ t in (0 : ℝ)..1, (-(u t * deriv η t) + q t * η t)) +
              u₀ * (∫ t in (0 : ℝ)..1, deriv η t) +
              (∫ t in (0 : ℝ)..1, (-(P t * deriv η t) - q t * η t)) := by
              calc
                _ = ((∫ t in (0 : ℝ)..1, (-(u t * deriv η t) + q t * η t)) +
                    (∫ t in (0 : ℝ)..1, u₀ * deriv η t)) +
                    (∫ t in (0 : ℝ)..1, (-(P t * deriv η t) - q t * η t)) := by
                      rw [intervalIntegral.integral_add (hAInt.add hBInt) hCInt,
                        intervalIntegral.integral_add hAInt hBInt]
                _ = _ := by simp only [intervalIntegral.integral_const_mul]
    have hAweak : ∫ t in (0 : ℝ)..1,
        (-(u t * deriv η t) + q t * η t) = u₀ * η 0 := by
      calc
        _ = ∫ t in (0 : ℝ)..1, (-u t * deriv η t + q t * η t) := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards with t ht
          ring
        _ = u₀ * η 0 := hweakη
    have hCzero : ∫ t in (0 : ℝ)..1, (-(P t * deriv η t) - q t * η t) = 0 := by
      have hPnegInt : IntervalIntegrable (fun t => -(P t * deriv η t)) volume 0 1 :=
        hPηInt.neg
      calc
        _ = -(∫ t in (0 : ℝ)..1, P t * deriv η t) -
            ∫ t in (0 : ℝ)..1, q t * η t := by
              rw [intervalIntegral.integral_sub hPnegInt hqηInt,
                intervalIntegral.integral_neg]
        _ = 0 := by rw [hPηderiv]; ring
    have hFfactor : ∀ t ∈ Set.Icc (0 : ℝ) 1, F t = u t - u₀ + P t := by
      intro t ht
      simp [F, ScalarPath.clampUnitTime_eq ht]
    have hFtimes : (fun t => F t * g t) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)]
        fun t => (u t - u₀ + P t) * g t := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [hFfactor t ⟨le_of_lt ht.1, ht.2⟩]
    have hTargetZero : ∫ t in (0 : ℝ)..1,
        (u t - u₀ + P t) * g t = 0 := by
      have hderivEq : (fun t => -(u t - u₀ + P t) * deriv η t) =
          fun t => (u t - u₀ + P t) * g t := by
        funext t
        rw [hηderiv]
        ring
      rw [← hderivEq]
      rw [hTarget, hAweak, hηderivInt, hη₁, hCzero]
      ring
    calc
      ∫ t in (0 : ℝ)..1, F t * g t =
          ∫ t in (0 : ℝ)..1, (u t - u₀ + P t) * g t := by
            apply intervalIntegral.integral_congr_ae_restrict
            simpa [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hFtimes
      _ = 0 := hTargetZero
  have hFzero := continuous_eq_zero_of_smooth_interior_tests hF hzero
  intro t ht
  have h := hFzero t ht
  have hclamp := ScalarPath.clampUnitTime_eq ht
  dsimp [F] at h
  rw [hclamp] at h
  change u t - u₀ + P t = 0 at h
  dsimp [P] at h ⊢
  linarith

end AVenhance.Infra.Parabolic.WeakUniqueness

end
