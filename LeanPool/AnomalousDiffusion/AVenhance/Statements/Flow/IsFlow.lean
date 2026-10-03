/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.Homogenization.Ambient.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Module.Basic

/-! Statement file: `IsFlow` (Flow).
This file contains exactly one declaration of the formalization's public statement surface. -/

@[expose] public section

open Homogenization

namespace AVenhance

/-- Flow of a time-dependent field `b` on `ℝ²`: `X t x s` solves
`∂ₜ X(t,x,s) = b(t, X(t,x,s))` for all `t ∈ ℝ`, with `X(s,x,s) = x`
(source: `e.flow.m.def`, `enhance.tex` 1397-1410). -/
def IsFlow (b : ℝ → Vec 2 → Vec 2) (X : ℝ → Vec 2 → ℝ → Vec 2) : Prop :=
  (∀ x s, X s x s = x) ∧
  (∀ x s t, HasDerivAt (fun r => X r x s) (b t (X t x s)) t)

end AVenhance
