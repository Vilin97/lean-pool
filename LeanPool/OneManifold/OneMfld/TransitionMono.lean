/-
Copyright (c) 2026 Jim Fowler, Dennis Sweeney. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jim Fowler, Dennis Sweeney
-/
import Mathlib.Tactic
import Mathlib.Topology.Bornology.Real
import Mathlib.Topology.UniformSpace.Real

/-! # Monotonicity of transition maps

A transition map between interval charts, restricted to (the image of) a component of the
overlap, is continuous and injective on an open interval of `ℝ≥0`, hence strictly
monotone or strictly antitone; and a strictly monotone map of one open interval onto
another sends ends to ends.
-/

open Set Filter Topology

/-- A continuous injective function on an open interval of `ℝ≥0` is strictly monotone or
strictly antitone there. -/
theorem strictMonoOn_or_strictAntiOn_of_injOn_Ioo {p v : NNReal}
    {f : NNReal → NNReal} (hc : ContinuousOn f (Ioo p v)) (hi : InjOn f (Ioo p v)) :
    StrictMonoOn f (Ioo p v) ∨ StrictAntiOn f (Ioo p v) := by
  by_cases hpv : p < v
  · exact ContinuousOn.strictMonoOn_of_injOn_Ioo hpv hc hi
  · left
    intro x hx
    simp [Ioo_eq_empty hpv] at hx

/-- A strictly monotone map of `Ioo p v` onto `Ioo q w` tends to `w` at the top end. -/
theorem tendsto_top_of_strictMonoOn_image {p v q w : NNReal} (hpv : p < v)
    {f : NNReal → NNReal} (hm : StrictMonoOn f (Ioo p v))
    (himg : f '' Ioo p v = Ioo q w) :
    Tendsto f (𝓝[<] v) (𝓝 w) := by
  have hne : (Ioo p v).Nonempty := nonempty_Ioo.2 hpv
  have hqw : q < w := nonempty_Ioo.1 (himg ▸ hne.image f)
  have hbdd : BddAbove (f '' Ioo p v) := himg ▸ bddAbove_Ioo
  have h := MonotoneOn.tendsto_nhdsWithin_Ioo_left hne hm.monotoneOn hbdd
  rwa [himg, csSup_Ioo hqw] at h

/-- A strictly monotone map of `Ioo p v` onto `Ioo q w` tends to `q` at the bottom end. -/
theorem tendsto_bot_of_strictMonoOn_image {p v q w : NNReal} (hpv : p < v)
    {f : NNReal → NNReal} (hm : StrictMonoOn f (Ioo p v))
    (himg : f '' Ioo p v = Ioo q w) :
    Tendsto f (𝓝[>] p) (𝓝 q) := by
  have hne : (Ioo p v).Nonempty := nonempty_Ioo.2 hpv
  have hqw : q < w := nonempty_Ioo.1 (himg ▸ hne.image f)
  have hbdd : BddBelow (f '' Ioo p v) := himg ▸ bddBelow_Ioo
  have h := MonotoneOn.tendsto_nhdsWithin_Ioo_right hne hm.monotoneOn hbdd
  rwa [himg, csInf_Ioo hqw] at h
