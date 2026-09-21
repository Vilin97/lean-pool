/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Bulka
-/

import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.Lifting

/-!
## Entire logarithms for zero-free entire functions

This file provides a basic construction: if `f : ℂ → ℂ` is complex-differentiable everywhere and
never vanishes, then there exists a complex-differentiable function `g` with `f = exp ∘ g`.

We use:
- `Complex.isCoveringMap_exp` to lift `f` (viewed as a map into `ℂˣ`) through `exp`;
- a local inverse of `exp` (inverse function theorem) to upgrade the lift from continuous to
  complex-differentiable.
-/

open Complex Filter Topology
open scoped Topology

namespace EntireLog

theorem entire_has_entire_log_of_no_zeros
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (h0 : ∀ z, f z ≠ 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, f z = Complex.exp (g z) := by
  classical
  -- View `f` as a continuous map into `{z : ℂ // z ≠ 0}`.
  let fSub : ℂ → {z : ℂ // z ≠ 0} := fun z => ⟨f z, h0 z⟩
  have hfSub_cont : Continuous fSub := by
    -- continuity comes from complex differentiability
    exact (hf.continuous.subtype_mk fun z => h0 z)
  let fC : C(ℂ, {z : ℂ // z ≠ 0}) := ⟨fSub, hfSub_cont⟩
  -- Basepoint data for the lift.
  let a0 : ℂ := 0
  let e0 : ℂ := Complex.log (f 0)
  have he0 :
      (fun z : ℂ => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) e0 =
        fC a0 := by
    apply Subtype.ext
    simpa [e0, fC, fSub, a0] using (Complex.exp_log (h0 0))
  -- Lift `fC` through the covering map `exp : ℂ → {z // z ≠ 0}`.
  rcases ((Complex.isCoveringMap_exp).existsUnique_continuousMap_lifts fC a0 e0 he0).exists with
    ⟨F, hF⟩
  have hF0 : F a0 = e0 := hF.1
  have hF_lifts :
      (fun z : ℂ => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) ∘ F = fC :=
    hF.2
  -- Extract the pointwise equation `exp (F z) = f z`.
  have h_exp_F : ∀ z : ℂ, Complex.exp (F z) = f z := by
    intro z
    have := congrArg Subtype.val (congrArg (fun h => h z) hF_lifts)
    -- `Subtype.val (⟨exp (F z), _⟩) = f z`
    simpa [Function.comp_def, fC, fSub] using this
  -- Upgrade the continuous lift `F` to a complex-differentiable function via local inverses of
  -- `exp`.
  have hF_differentiable : Differentiable ℂ (fun z : ℂ => F z) := by
    intro x
    -- Local inverse of `exp` around `F x`.
    let y0 : ℂ := F x
    let f' : ℂ := Complex.exp y0
    have hf_exp : HasStrictDerivAt Complex.exp f' y0 := Complex.hasStrictDerivAt_exp y0
    have hf'_ne : f' ≠ 0 := Complex.exp_ne_zero y0
    let φ : ℂ → ℂ :=
      HasStrictDerivAt.localInverse Complex.exp f' y0 hf_exp hf'_ne
    have hto : HasStrictDerivAt φ f'⁻¹ (Complex.exp y0) :=
      HasStrictDerivAt.to_localInverse
        (f := Complex.exp) (f' := f') (a := y0) (hf := hf_exp) (hf' := hf'_ne)
    have hφ_diff : DifferentiableAt ℂ φ (Complex.exp y0) := hto.hasDerivAt.differentiableAt
    -- `φ (exp y) = y` near `y0`; transport this along `F` using continuity.
    have hleft : (∀ᶠ y in 𝓝 y0, φ (Complex.exp y) = y) := by
      simpa [φ, f', y0] using
        (HasStrictDerivAt.eventually_left_inverse (f := Complex.exp) (f' := f') (a := y0)
          (hf := hf_exp) (hf' := hf'_ne))
    have hFeq : (fun z : ℂ => φ (f z)) =ᶠ[𝓝 x] fun z : ℂ => F z := by
      have hcontAt : ContinuousAt (fun z : ℂ => F z) x := F.continuous.continuousAt
      have hpre : (∀ᶠ z in 𝓝 x, φ (Complex.exp (F z)) = F z) :=
        (hcontAt.tendsto.eventually hleft)
      refine hpre.mono ?_
      intro z hz
      -- rewrite `exp (F z) = f z`
      simpa [h_exp_F z] using hz
    have hφ_diff' : DifferentiableAt ℂ φ (f x) := by
      -- `f x = exp (F x) = exp y0`
      simpa [f', y0, h_exp_F x] using hφ_diff
    have hcomp : DifferentiableAt ℂ (fun z : ℂ => φ (f z)) x :=
      hφ_diff'.comp x (hf x)
    exact DifferentiableAt.congr_of_eventuallyEq hcomp hFeq.symm
  refine ⟨fun z => F z, hF_differentiable, ?_⟩
  intro z
  exact (h_exp_F z).symm

end EntireLog
