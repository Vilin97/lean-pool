/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty

/-! # AtImInfty -/


@[expose] public section

/-
Probably put this at Analysis/Complex/UpperHalfPlane/FunctionsBoundedAtInfty.lean
-/

open UpperHalfPlane Filter Topology

lemma Filter.eventually_atImInfty {p : ℍ → Prop} :
    (∀ᶠ x in atImInfty, p x) ↔ ∃ A : ℝ, ∀ z : ℍ, A ≤ z.im → p z :=
  atImInfty_mem (setOf p)

lemma Filter.tendsto_im_atImInfty : Tendsto (fun x : ℍ ↦ x.im) atImInfty atTop :=
  tendsto_iff_comap.mpr fun ⦃_⦄ a => a

/-- If f tends to c ≠ 0 at infinity, then f ≠ 0 as a function.

This packages the common argument: if f = 0, then f → 0, but also f → c by hypothesis.
By uniqueness of limits, 0 = c, contradicting c ≠ 0. -/
lemma ne_zero_of_tendsto_ne_zero {f : ℍ → ℂ} {c : ℂ} (hc : c ≠ 0)
    (hf : Tendsto f atImInfty (nhds c)) : f ≠ 0 := fun h =>
  hc (tendsto_nhds_unique tendsto_const_nhds (h ▸ hf)).symm
