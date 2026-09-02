/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# `C^1` compatibility over `ℂ` is holomorphic compatibility

The Radó statement takes its surface hypothesis in Mathlib's standard form,

```
[ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
```

and it is worth recording why that *is* the Riemann-surface hypothesis rather than a
weaker topological one, since the smoothness index `1` invites the opposite reading.

`IsManifold I n X` asks that the chart transitions lie in `contDiffGroupoid n I`, whose
defining property is `ContDiffOn 𝕜 n` for the field `𝕜` of the model `I`. For
`I = modelWithCornersSelf ℂ ℂ` that field is `ℂ`, so the transitions are `C^1` **over
`ℂ`** — complex differentiable, not merely real differentiable. By Goursat a map that is
complex differentiable on an open set is holomorphic, hence analytic, so `C^1`
compatibility over `ℂ` already forces analytic compatibility.

The two results below make that precise, and they are the reason the hypothesis is not a
weakening:

* `contDiffGroupoid_one_le_omega_complex` — the `C^1` groupoid over `ℂ` is contained in
  the analytic one;
* `isManifold_omega_of_one` — hence a `C^1` charted space modelled on `ℂ` is an analytic
  (holomorphic) manifold, i.e. a Riemann surface.

Two contrasts are worth keeping in view. The genuinely topological hypothesis is index
`0`, not `1`: Mathlib proves `contDiffGroupoid_zero_eq : contDiffGroupoid 0 I =
continuousGroupoid H`, so `IsManifold I 0 X` is exactly a topological manifold and carries
no analytic content. And because `1 ≤ ω`, assuming `1` is the *weaker* hypothesis, so
proving Radó's theorem from it is strictly stronger than proving it from `ω`; by
`isManifold_omega_of_one` the two hypotheses are in fact equivalent here.
-/

open scoped Manifold ContDiff
open Set

/-- Over `ℂ`, the `C^1` chart-transition groupoid is contained in the analytic one.
`ContDiffOn ℂ 1` is complex differentiability, and a complex-differentiable map on an
open set is holomorphic, hence analytic. -/
theorem contDiffGroupoid_one_le_omega_complex :
    contDiffGroupoid 1 (modelWithCornersSelf ℂ ℂ)
      ≤ contDiffGroupoid ω (modelWithCornersSelf ℂ ℂ) := by
  intro f hf
  simp only [contDiffGroupoid, Pregroupoid.groupoid, contDiffPregroupoid,
    Set.mem_ofPred_eq] at hf ⊢
  obtain ⟨h1, h2⟩ := hf
  constructor
  · have : AnalyticOnNhd ℂ (f : ℂ → ℂ) f.source := by
      simpa using (ContDiffOn.differentiableOn_one (by simpa using h1)).analyticOnNhd f.open_source
    simpa using this.contDiffOn_of_completeSpace (n := ω)
  · have : AnalyticOnNhd ℂ (f.symm : ℂ → ℂ) f.target := by
      simpa using (ContDiffOn.differentiableOn_one (by simpa using h2)).analyticOnNhd f.open_target
    simpa using this.contDiffOn_of_completeSpace (n := ω)

/-- **The `C^1` hypothesis over `ℂ` is the Riemann-surface hypothesis.** A charted space
modelled on `ℂ` whose transitions are `C^1` over `ℂ` has holomorphic transitions, so it is
an analytic manifold. This is what makes
`[ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]` a faithful rendering of
"`X` is a Riemann surface". -/
theorem isManifold_omega_of_one {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (h : IsManifold (modelWithCornersSelf ℂ ℂ) 1 X) :
    IsManifold (modelWithCornersSelf ℂ ℂ) ω X :=
  { compatible := fun he he' =>
      contDiffGroupoid_one_le_omega_complex (h.compatible he he') }
