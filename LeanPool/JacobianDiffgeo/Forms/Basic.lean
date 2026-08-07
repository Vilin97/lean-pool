/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# Holomorphic 1-forms: the definition (CC1)

This file defines `RS.Form1 X`, the space of global holomorphic 1-forms on a Riemann surface
`X`, as bundled `C^ω` sections of the bundle of `ℂ`-linear maps from the (holomorphic) tangent
bundle to the trivial line bundle. This is the frozen core choice CC1 of
`docs/design/core-choices.md`; the spelling is verified by the compiled spike
`scratch_forms.lean`.

The `AddCommGroup`/`Module ℂ` structure and the `ω`-smooth vector bundle instance for the Hom
bundle are all found by typeclass inference (checked by the `example`s below). Evaluation
`η x v : ℂ` works through the reducible `Bundle.Trivial X ℂ x ≡ ℂ`.
-/

open scoped ContDiff Manifold Bundle

noncomputable section

namespace RS

variable (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The space of global holomorphic 1-forms on `X`: bundled `C^ω` sections of the bundle of
`ℂ`-linear maps from the (holomorphic) tangent bundle to the trivial line bundle.

Downstream units interact with `Form1` exclusively through the chart-coefficient API
`RS.coeffIn` (see `Jacobian/Forms/Coeffs.lean`), never through bundle internals. -/
abbrev Form1 : Type _ :=
  Cₛ^ω⟮𝓘(ℂ); ℂ →L[ℂ] ℂ, fun x : X => TangentSpace 𝓘(ℂ) x →L[ℂ] Bundle.Trivial X ℂ x⟯

variable {X}

-- Sanity checks (spike-verified): the algebraic instances are found by TC inference.
example : AddCommGroup (Form1 X) := inferInstance
example : Module ℂ (Form1 X) := inferInstance

-- The `ω`-smooth vector bundle instance for the Hom bundle is found by TC inference.
example : ContMDiffVectorBundle ω (ℂ →L[ℂ] ℂ)
    (fun x : X => TangentSpace 𝓘(ℂ) x →L[ℂ] Bundle.Trivial X ℂ x) 𝓘(ℂ) := inferInstance

-- Blueprint hazard cleared: finite sums and module operations on forms work.
example {ι : Type*} (s : Finset ι) (f : ι → Form1 X) : Form1 X := ∑ i ∈ s, f i
example (c : ℂ) (η η' : Form1 X) : Form1 X := c • η + η' - η

-- Evaluation lands (definitionally) in `ℂ`.
example (η : Form1 X) (x : X) (v : TangentSpace 𝓘(ℂ) x) : ℂ := η x v

/-- Extensionality for holomorphic 1-forms from pointwise (covector-level) agreement. -/
theorem Form1.ext' {η η' : Form1 X} (h : ∀ x, η x = η' x) : η = η' :=
  ContMDiffSection.ext h

/-- Extensionality for holomorphic 1-forms from pointwise agreement on tangent vectors. -/
theorem Form1.ext_apply {η η' : Form1 X} (h : ∀ x, ∀ v : TangentSpace 𝓘(ℂ) x, η x v = η' x v) :
    η = η' :=
  Form1.ext' fun x => ContinuousLinearMap.ext fun v => h x v

theorem Form1.add_apply (η η' : Form1 X) (x : X) (v : TangentSpace 𝓘(ℂ) x) :
    (η + η') x v = η x v + η' x v := rfl

theorem Form1.smul_apply (c : ℂ) (η : Form1 X) (x : X) (v : TangentSpace 𝓘(ℂ) x) :
    (c • η) x v = c * η x v := rfl

theorem Form1.zero_apply (x : X) (v : TangentSpace 𝓘(ℂ) x) : (0 : Form1 X) x v = 0 := rfl

theorem Form1.sub_apply (η η' : Form1 X) (x : X) (v : TangentSpace 𝓘(ℂ) x) :
    (η - η') x v = η x v - η' x v := rfl

theorem Form1.neg_apply (η : Form1 X) (x : X) (v : TangentSpace 𝓘(ℂ) x) :
    (-η) x v = -(η x v) := rfl

end RS

end
