/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.WeakDerivativeMollification
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Local almost-everywhere constancy of the weak gradient kernel

The classical zero-derivative theorem is applied only to mollifications, never to the
locally integrable original function. Source APIs are Mathlib's
`Analysis/Calculus/BumpFunction/Convolution.lean`
(`ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`) and
`Analysis/Calculus/MeanValue.lean` (`IsOpen.is_const_of_fderiv_eq_zero`).
The local derivative identity is proved in `AlmostSchur.WeakDerivativeMollification`.
-/

@[expose] public noncomputable section

open Set MeasureTheory Metric Filter
open scoped ContDiff Convolution Topology

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A locally integrable function annihilating all compactly supported smooth test
derivatives is almost everywhere constant on any ball with a larger closed ball in its
domain. No classical differentiability of the original function is required. -/
theorem ae_eq_const_on_ball_of_weakDeriv_eq_zero
    {U : Set E} {u : E → ℝ} {a : E} {R r : ℝ}
    (hu : LocallyIntegrableOn u U volume)
    (hweak : ∀ (φ : E → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U → ∀ v : E, ∫ y, u y * fderiv ℝ φ y v = 0)
    (hball : closedBall a R ⊆ U) (hr : 0 < r) (hrR : r < R) :
    ∃ c : ℝ, u =ᵐ[volume.restrict (ball a r)] (fun _ => c) := by
  let f : E → ℝ := (closedBall a R).indicator u
  have hf : LocallyIntegrable f volume :=
    ((integrable_indicator_iff isClosed_closedBall.measurableSet).2
      (hu.integrableOn_compact_subset hball (isCompact_closedBall a R))).locallyIntegrable
  let ε : ℕ → ℝ := fun n => (R - r) / 2 * (1 / 2 : ℝ) ^ n
  have hεpos (n : ℕ) : 0 < ε n := by
    dsimp [ε]
    positivity
  have hεlt (n : ℕ) : ε n < R - r := by
    have hp : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hδ : 0 < (R - r) / 2 := by linarith
    dsimp [ε]
    nlinarith
  let b : ℕ → ContDiffBump (0 : E) := fun n =>
    ⟨ε n / 2, ε n, half_pos (hεpos n), by linarith [hεpos n]⟩
  have hb : Tendsto (fun n => (b n).rOut) atTop (𝓝 0) := by
    simpa [b, ε] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul ((R - r) / 2)
  have hratio : ∀ᶠ n in atTop, (b n).rOut ≤ 2 * (b n).rIn :=
    Eventually.of_forall fun n => by dsimp [b]; linarith
  let m : ℕ → E → ℝ := fun n =>
    f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (b n).normed volume
  have hmconst (n : ℕ) {x y : E} (hx : x ∈ ball a r) (hy : y ∈ ball a r) :
      m n x = m n y := by
    apply isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball a r).isPreconnected
      (((b n).hasCompactSupport_normed.contDiff_convolution_right
        (ContinuousLinearMap.mul ℝ ℝ) hf
        ((b n).contDiff_normed : ContDiff ℝ 1 ((b n).normed volume))).differentiable
          (by simp)).differentiableOn _ hx hy
    intro z hz
    exact fderiv_indicator_convolution_eq_zero hu hweak hball
      (b n).contDiff_normed (b n).hasCompactSupport_normed
      (by rw [(b n).tsupport_normed_eq]) (hεlt n) hz
  have hflip : (ContinuousLinearMap.mul ℝ ℝ).flip = ContinuousLinearMap.lsmul ℝ ℝ := by
    ext
    simp
  have hconv (n : ℕ) :
      ((b n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) = m n := by
    rw [← hflip, convolution_flip]
  have hlim : ∀ᵐ x ∂volume, Tendsto (fun n => m n x) atTop (𝓝 (f x)) := by
    simpa only [hconv] using
      (ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hb hratio hf)
  obtain ⟨x₀, hx₀, hlim₀⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (ne_of_gt (measure_ball_pos volume a hr)) (ae_restrict_of_ae hlim)
  refine ⟨f x₀, ?_⟩
  apply (ae_restrict_iff' isOpen_ball.measurableSet).2
  filter_upwards [hlim] with y hy hymem
  have heq : (fun n => m n y) = (fun n => m n x₀) :=
    funext fun n => hmconst n hymem hx₀
  have hfy : f y = f x₀ := tendsto_nhds_unique hy (heq.symm ▸ hlim₀)
  have hyR : y ∈ closedBall a R :=
    ball_subset_closedBall (ball_subset_ball hrR.le hymem)
  simpa only [f, indicator_of_mem hyR] using hfy

end AlmostSchur
