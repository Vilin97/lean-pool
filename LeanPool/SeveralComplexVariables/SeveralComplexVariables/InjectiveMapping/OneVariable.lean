/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.OpenMapping
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Normed.Module.Connected
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Biholomorphic

/-!
# Nonsingularity of injective holomorphic functions of one variable

The open mapping theorem makes the inverse continuous. Isolated zeros of the derivative make it
holomorphic off the image of the base point, so the removable singularity theorem makes it
holomorphic there too. The chain rule then excludes a zero derivative.

## Main results

`deriv_ne_zero_of_injOn` is nonsingularity of an injective holomorphic function of one complex
variable. `not_eventually_constant_of_injOn_complex` and `not_eventually_deriv_eq_zero_of_injOn`
exclude a locally constant germ and a locally vanishing derivative.
-/

public noncomputable section

open Set Filter Metric Function
open scoped Topology

namespace SeveralComplexVariables

/-- A function injective on a neighborhood in the complex plane is not locally constant. -/
theorem not_eventually_constant_of_injOn_complex {f : ℂ → ℂ} {U : Set ℂ} {a : ℂ}
    (hU : U ∈ 𝓝 a) (hi : InjOn f U) : ¬ ∀ᶠ z in 𝓝 a, f z = f a := by
  intro hc
  have hs : ({a} : Set ℂ) ∈ 𝓝 a := by
    filter_upwards [hU, hc] with z hz he
    exact hi hz (mem_of_mem_nhds hU) he
  have := mem_interior_iff_mem_nhds.mpr hs
  simp at this

/-- The derivative of a locally injective analytic function is not locally identically zero. -/
theorem not_eventually_deriv_eq_zero_of_injOn {f : ℂ → ℂ} {U : Set ℂ} {a : ℂ}
    (hU : U ∈ 𝓝 a) (hi : InjOn f U) (hf : AnalyticAt ℂ f a) :
    ¬ deriv f =ᶠ[𝓝 a] 0 := by
  intro hz
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem hU (hf.eventually_analyticAt.and hz))
  apply not_eventually_constant_of_injOn_complex hU hi
  filter_upwards [ball_mem_nhds a hr] with z hz
  exact isOpen_ball.is_const_of_deriv_eq_zero isPreconnected_ball
    (fun w hw => ((hball hw).2.1).differentiableAt.differentiableWithinAt)
    (fun w hw => (hball hw).2.2) hz (mem_ball_self hr)

/-- An injective holomorphic function of one complex variable has nonzero derivative. -/
theorem deriv_ne_zero_of_injOn {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hi : InjOn f U) {a : ℂ} (ha : a ∈ U) :
    deriv f a ≠ 0 := by
  have hfa := hf.analyticOnNhd hU a ha
  have hopen : 𝓝 (f a) ≤ map f (𝓝 a) :=
    hfa.eventually_constant_or_nhds_le_map_nhds.resolve_left
      (not_eventually_constant_of_injOn_complex (hU.mem_nhds ha) hi)
  let g := invFunOn f U
  have hleft : (g ∘ f) =ᶠ[𝓝 a] id :=
    Filter.mem_of_superset (hU.mem_nhds ha) (fun _ hz => hi.leftInvOn_invFunOn hz)
  have hga : g (f a) = a := hi.leftInvOn_invFunOn ha
  have hgcont : ContinuousAt g (f a) := by
    rw [ContinuousAt, hga]
    have ht : Tendsto (g ∘ f) (𝓝 a) (𝓝 a) := tendsto_id.congr' hleft.symm
    change map (g ∘ f) (𝓝 a) ≤ 𝓝 a at ht
    exact (Filter.map_mono hopen).trans (by rwa [map_map])
  have hisol : ∀ᶠ z in 𝓝[≠] a, deriv f z ≠ 0 :=
    hfa.deriv.eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (not_eventually_deriv_eq_zero_of_injOn (hU.mem_nhds ha) hi hfa)
  have hV : {z | z ∈ U ∧ (z ≠ a → deriv f z ≠ 0)} ∈ 𝓝 a :=
    inter_mem (hU.mem_nhds ha) (eventually_nhdsWithin_iff.mp hisol)
  have hW : f '' {z | z ∈ U ∧ (z ≠ a → deriv f z ≠ 0)} ∈ 𝓝 (f a) :=
    hopen (image_mem_map hV)
  have hgd : ∀ᶠ w in 𝓝[≠] (f a), DifferentiableAt ℂ g w := by
    filter_upwards [nhdsWithin_le_nhds hW, self_mem_nhdsWithin] with w hw hwne
    obtain ⟨z, ⟨hz, hdz⟩, rfl⟩ := hw
    have hzane : z ≠ a := fun h => hwne (by simp [h])
    have hstrict := (hf.analyticOnNhd hU z hz).contDiffAt.hasStrictDerivAt (n := 1) one_ne_zero
    exact (hstrict.to_local_left_inverse (hdz hzane)
      (Filter.mem_of_superset (hU.mem_nhds hz)
        (fun _ ht => hi.leftInvOn_invFunOn ht))).hasDerivAt.differentiableAt
  have hgan := Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hgd hgcont
  have hder : deriv g (f a) * deriv f a = 1 := by
    have hc := hgan.differentiableAt.hasDerivAt.comp a hfa.differentiableAt.hasDerivAt
    exact hc.deriv.symm.trans ((Filter.EventuallyEq.deriv_eq hleft).trans (deriv_id a))
  intro hz
  simp [hz] at hder

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
