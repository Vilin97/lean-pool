/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Uniformization.SpecialPeriods4
import all LeanPool.HopfProblem.Uniformization.CuspUniformization1
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods2
import all LeanPool.HopfProblem.Threefold.SpecialPeriods4
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods4

/-!
# Hopf problem: threefold · special periods 5

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

private theorem SpecialPeriods.TauCusp.exists_global_normalized_lift_of_meromorphic_cusp (F : ℍ → ℂ)
    (hF : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) F)
    (h₃ :
      ∀ a : ℍ,
        F a = 0 → ∃ k : ℕ, analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (a : ℂ) = (3 * k : ℕ))
    (h₂ :
      ∀ a : ℍ,
        F a = 1728 →
          ∃ k : ℕ,
            analyticOrderAt (fun z => F (UpperHalfPlane.ofComplex z) - 1728) (a : ℂ) =
              (2 * k : ℕ))
    (w : ℝ) (hw : 0 < w) (Fc : ℂ → ℂ) (hFc : MeromorphicAt Fc 0)
    (horder : meromorphicOrderAt Fc 0 = (-1 : ℤ)) {c : ℂ}
    (hc : Filter.Tendsto (fun t => t * Fc t) (𝓝[≠] 0) (𝓝 c)) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hsource :
      ∀ z : ℍ,
        ‖Function.Periodic.qParam w (z : ℂ)‖ < r₀ →
          F z = Fc (Function.Periodic.qParam w (z : ℂ))) :
    ∃ τ : ℍ → ℍ,
      ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω τ ∧
        (∀ z : ℍ, SpecialPeriods.modularJ (τ z) = F z) ∧
          ∃ r > 0,
            r < r₀ ∧
              r < 1 ∧
                ∃ h : ℂ → ℂ,
                  AnalyticOnNhd ℂ h (Metric.ball 0 r) ∧
                    h 0 = CuspUniformization.logarithm (1 / c) ∧
                      ∀ z : ℍ,
                        ‖Function.Periodic.qParam w (z : ℂ)‖ < r →
                          (τ z : ℂ) = correctedLogarithmWidth w h (z : ℂ) := by
  obtain ⟨a, ha, ha0, hac, rF, hrF, hfactor⟩ := simplePole_factorization_of_tendsto hFc horder hc
  obtain ⟨r, hr, hrr, hr1, h, hh, hh0, _, hlift⟩ :=
    exists_simplePole_logarithmic_lift_width w hw ha ha0 (R := 1) (r₀ := Min.min r₀ rF)
      zero_lt_one (lt_min hr₀ hrF)
  have hrr₀ : r < r₀ := lt_of_lt_of_le hrr (min_le_left r₀ rF)
  have hrrF : r < rF := lt_of_lt_of_le hrr (min_le_right r₀ rF)
  have hlocalJ (s : ℂ) (hs : ‖Function.Periodic.qParam w s‖ < r) :
    SpecialPeriods.modularJ (UpperHalfPlane.ofComplex (correctedLogarithmWidth w h s)) =
      F (UpperHalfPlane.ofComplex s) := by
    have hspos : 0 < s.im := upperHalfPlane_of_qParam_norm_lt_one w hw (hs.trans hr1)
    have hqt : Function.Periodic.qParam w s ∈ Metric.ball (0 : ℂ) rF := by
      simpa only [Metric.mem_ball, dist_zero_right] using hs.trans hrrF
    have hfactorq :=
      hfactor (Function.Periodic.qParam w s) hqt (Function.Periodic.qParam_ne_zero (h := w) s)
    have hsourceq : F (UpperHalfPlane.ofComplex s) = Fc (Function.Periodic.qParam w s) := by
      have he :=
        hsource (UpperHalfPlane.ofComplex s)
          (by simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hspos] using hs.trans hrr₀)
      simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hspos] using he
    exact (hlift s hs).2.2.2.trans (hfactorq.symm.trans hsourceq.symm)
  obtain ⟨z₀, hz₀⟩ := exists_upperHalfPlane_qParam_small_mo1973_17412 w hw r hr hr1
  have hJgerm :
    (fun s =>
        SpecialPeriods.modularJ
          (UpperHalfPlane.ofComplex (correctedLogarithmWidth w h s))) =ᶠ[𝓝 (z₀ : ℂ)]
      F ∘ UpperHalfPlane.ofComplex := by
    filter_upwards [(isOpen_qParam_norm_lt_mo1973_17413 w r).mem_nhds hz₀] with s hs
    exact hlocalJ s hs
  obtain ⟨τ, hτ, hJ, hgerm⟩ :=
    SpecialPeriods.ModularGermLift.exists_holomorphic_modularJ_lift_upperHalfPlane_extending F hF
      h₃ h₂ z₀ (correctedLogarithmWidth w h) (correctedLogarithmWidth_analyticAt w hh hz₀)
      (hlift z₀ hz₀).2.1 hJgerm
  have hformula := native_eqOn_correctedLogarithmWidth_of_eventuallyEq w hw hr hr1 hh hτ hz₀ hgerm
  refine ⟨τ, hτ, hJ, r, hr, hrr₀, hr1, h, hh, ?_, ?_⟩
  · simpa only [hac] using hh0
  · intro z hz
    have hzEq :
      (τ (UpperHalfPlane.ofComplex (z : ℂ)) : ℂ) = correctedLogarithmWidth w h (z : ℂ) :=
      hformula hz
    simpa only [UpperHalfPlane.ofComplex_apply] using hzEq

public
theorem SpecialPeriods.TauCusp.exists_simplePole_normalized_limit_mo1973_17415
    {Fc : ℂ → ℂ} (hFc : MeromorphicAt Fc 0) (horder : meromorphicOrderAt Fc 0 = (-1 : ℤ)) :
    ∃ c : ℂ, c ≠ 0 ∧ Filter.Tendsto (fun t => t * Fc t) (𝓝[≠] 0) (𝓝 c) := by
  obtain ⟨a, ha, ha0, r, hr, hball⟩ := simplePole_factorization hFc horder
  refine ⟨a 0, ha0, ?_⟩
  have heq : (fun t => t * Fc t) =ᶠ[𝓝[≠] (0 : ℂ)] a := by
    have hnear : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t ∈ Metric.ball 0 r :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hr)
    filter_upwards [hnear, self_mem_nhdsWithin] with t ht hne
    have ht0 : t ≠ 0 := hne
    rw [hball t ht ht0]
    field_simp [ht0]
  exact ha.continuousAt.continuousWithinAt.congr' heq.symm

private theorem SpecialPeriods.TauCusp.exists_global_normalized_lift_of_simplePole_cusp (F : ℍ → ℂ)
    (hF : MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) F)
    (h₃ :
      ∀ a : ℍ,
        F a = 0 → ∃ k : ℕ, analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (a : ℂ) = (3 * k : ℕ))
    (h₂ :
      ∀ a : ℍ,
        F a = 1728 →
          ∃ k : ℕ,
            analyticOrderAt (fun z => F (UpperHalfPlane.ofComplex z) - 1728) (a : ℂ) =
              (2 * k : ℕ))
    (w : ℝ) (hw : 0 < w) (Fc : ℂ → ℂ) (hFc : MeromorphicAt Fc 0)
    (horder : meromorphicOrderAt Fc 0 = (-1 : ℤ)) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hsource :
      ∀ z : ℍ,
        ‖Function.Periodic.qParam w (z : ℂ)‖ < r₀ →
          F z = Fc (Function.Periodic.qParam w (z : ℂ))) :
    ∃ c : ℂ,
      c ≠ 0 ∧
        Filter.Tendsto (fun t => t * Fc t) (𝓝[≠] 0) (𝓝 c) ∧
          ∃ τ : ℍ → ℍ,
            ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω τ ∧
              (∀ z : ℍ, SpecialPeriods.modularJ (τ z) = F z) ∧
                ∃ r > 0,
                  r < r₀ ∧
                    r < 1 ∧
                      ∃ h : ℂ → ℂ,
                        AnalyticOnNhd ℂ h (Metric.ball 0 r) ∧
                          h 0 = CuspUniformization.logarithm (1 / c) ∧
                            ∀ z : ℍ,
                              ‖Function.Periodic.qParam w (z : ℂ)‖ < r →
                                (τ z : ℂ) = correctedLogarithmWidth w h (z : ℂ) := by
  obtain ⟨c, hc0, hc⟩ := exists_simplePole_normalized_limit_mo1973_17415 hFc horder
  exact
    ⟨c, hc0, hc,
      exists_global_normalized_lift_of_meromorphic_cusp F hF h₃ h₂ w hw Fc hFc horder hc hr₀
        hsource⟩

end Mathoverflow1973

end
