/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Order.LeftRightNhds
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Conditional blow-up and obstruction to continuous extension

The terminal inference of Proposition 11.7, independently of the claimed
Navier--Stokes construction. Positive scales approaching zero and a nonzero
limiting profile force divergent velocity norm under a negative real power.
The resulting field cannot be bounded near, or continuously extended to, the
endpoint. No existence theorem for the manuscript's profiles is assumed here.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace NavierStokes.BlowupImplication

/-- A positive scale tending to zero has a divergent negative real power. -/
theorem negative_power_tendsto_atTop {ι : Type*} {l : Filter ι}
    {q : ι → ℝ} {A : ℝ} (hA : 0 < A)
    (hq : Tendsto q l (𝓝[>] (0 : ℝ))) :
    Tendsto (fun t => q t ^ (-A)) l atTop := by
  have h := (tendsto_rpow_atTop hA).comp
    (tendsto_inv_nhdsGT_zero.comp hq)
  refine h.congr' ?_
  filter_upwards [hq.eventually self_mem_nhdsWithin] with t ht
  change (q t)⁻¹ ^ A = q t ^ (-A)
  rw [Real.inv_rpow (le_of_lt ht), Real.rpow_neg (le_of_lt ht)]

/-- The manuscript's positive scalar profile remains divergent with a vanishing
relative error. The error is inside the factor multiplied by `q ^ (-A)`. -/
theorem positive_profile_tendsto_atTop {ι : Type*} {l : Filter ι}
    {q error : ι → ℝ} {A E : ℝ} (hA : 0 < A) (hE : 0 < E)
    (hq : Tendsto q l (𝓝[>] (0 : ℝ)))
    (herror : Tendsto error l (𝓝 0)) :
    Tendsto (fun t => q t ^ (-A) * (E + error t)) l atTop := by
  have hfactor : Tendsto (fun t => E + error t) l (𝓝 E) := by
    simpa only [add_zero] using tendsto_const_nhds.add herror
  exact (negative_power_tendsto_atTop hA hq).atTop_mul_pos hE hfactor

/-- A velocity norm bounded below by the positive leading profile diverges.
This directly applies when the angular component has that leading term. -/
theorem norm_tendsto_atTop_of_profile_lower_bound {ι V : Type*}
    [NormedAddCommGroup V] {l : Filter ι} {q error : ι → ℝ}
    {v : ι → V} {A E : ℝ} (hA : 0 < A) (hE : 0 < E)
    (hq : Tendsto q l (𝓝[>] (0 : ℝ)))
    (herror : Tendsto error l (𝓝 0))
    (hlower : ∀ᶠ t in l, q t ^ (-A) * (E + error t) ≤ ‖v t‖) :
    Tendsto (fun t => ‖v t‖) l atTop := by
  exact tendsto_atTop_mono' l hlower
    (positive_profile_tendsto_atTop hA hE hq herror)

/-- A vector-valued nonzero profile with a perturbation tending to zero also
has divergent norm. This theorem needs no sign choice for a component. -/
theorem nonzero_profile_norm_tendsto_atTop {ι V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {l : Filter ι}
    {q : ι → ℝ} {error : ι → V} {profile : V} {A : ℝ}
    (hA : 0 < A) (hprofile : profile ≠ 0)
    (hq : Tendsto q l (𝓝[>] (0 : ℝ)))
    (herror : Tendsto error l (𝓝 0)) :
    Tendsto (fun t => ‖(q t ^ (-A)) • (profile + error t)‖) l atTop := by
  have hfactor : Tendsto (fun t => ‖profile + error t‖) l (𝓝 ‖profile‖) := by
    simpa only [add_zero] using (tendsto_const_nhds.add herror).norm
  have h := (negative_power_tendsto_atTop hA hq).atTop_mul_pos
    (norm_pos_iff.mpr hprofile) hfactor
  refine h.congr' ?_
  filter_upwards [hq.eventually self_mem_nhdsWithin] with t ht
  simp only [norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos ht (-A))]

/-- Divergence rules out any eventual finite bound, not only a global bound. -/
theorem no_eventual_bound_of_profile {ι V : Type*}
    [NormedAddCommGroup V] {l : Filter ι} [NeBot l]
    {q error : ι → ℝ} {v : ι → V} {A E : ℝ}
    (hA : 0 < A) (hE : 0 < E)
    (hq : Tendsto q l (𝓝[>] (0 : ℝ)))
    (herror : Tendsto error l (𝓝 0))
    (hlower : ∀ᶠ t in l, q t ^ (-A) * (E + error t) ≤ ‖v t‖) :
    ¬ ∃ M : ℝ, ∀ᶠ t in l, ‖v t‖ ≤ M := by
  rintro ⟨M, hM⟩
  have hlarge := (norm_tendsto_atTop_of_profile_lower_bound
    hA hE hq herror hlower).eventually_gt_atTop M
  obtain ⟨t, ht, ht'⟩ := (hlarge.and hM).exists
  exact (not_lt_of_ge ht') ht

/-- A continuous extension along a convergent path contradicts the profile
lower bound. `X` may be spacetime and `path` may move towards the singular point. -/
theorem no_continuous_extension_of_profile {ι X V : Type*}
    [TopologicalSpace X] [NormedAddCommGroup V]
    {l : Filter ι} [NeBot l] {q error : ι → ℝ} {v : ι → V}
    {path : ι → X} {endpoint : X} {A E : ℝ}
    (hA : 0 < A) (hE : 0 < E)
    (hq : Tendsto q l (𝓝[>] (0 : ℝ)))
    (herror : Tendsto error l (𝓝 0))
    (hlower : ∀ᶠ t in l, q t ^ (-A) * (E + error t) ≤ ‖v t‖)
    (hpath : Tendsto path l (𝓝 endpoint)) :
    ¬ ∃ extension : X → V, ContinuousAt extension endpoint ∧
      ∀ᶠ t in l, extension (path t) = v t := by
  rintro ⟨extension, hcontinuous, hagree⟩
  have hv : Tendsto v l (𝓝 (extension endpoint)) :=
    (hcontinuous.tendsto.comp hpath).congr' hagree
  exact not_tendsto_nhds_of_tendsto_atTop
    (norm_tendsto_atTop_of_profile_lower_bound hA hE hq herror hlower)
    ‖extension endpoint‖ hv.norm

/-- The remaining-time scale `T - t` tends to zero through positive values
as `t` approaches `T` from below. -/
theorem remaining_time_tendsto (T : ℝ) :
    Tendsto (fun t : ℝ => T - t) (𝓝[<] T) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have htime : Tendsto (fun t : ℝ => t) (𝓝[<] T) (𝓝 T) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hconst : Tendsto (fun _ : ℝ => T) (𝓝[<] T) (𝓝 T) := tendsto_const_nhds
    simpa only [sub_self] using hconst.sub htime
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact (show 0 < T - t from sub_pos.mpr ht)

/-- Finite-time version of the scalar asymptotic in Proposition 11.7. -/
theorem finite_time_profile_tendsto_atTop {T A E : ℝ} {error : ℝ → ℝ}
    (hA : 0 < A) (hE : 0 < E)
    (herror : Tendsto error (𝓝[<] T) (𝓝 0)) :
    Tendsto (fun t => (T - t) ^ (-A) * (E + error t)) (𝓝[<] T) atTop :=
  positive_profile_tendsto_atTop hA hE (remaining_time_tendsto T) herror

/-- Any size which controls the velocity norm by a fixed
positive multiplicative constant must diverge as well. An actual Sobolev
embedding estimate may be supplied as `hcontrol`; it is not proved here. -/
theorem controlling_quantity_tendsto_atTop {ι V : Type*}
    [NormedAddCommGroup V] {l : Filter ι} {q error quantity : ι → ℝ}
    {v : ι → V} {A E C : ℝ} (hA : 0 < A) (hE : 0 < E) (hC : 0 < C)
    (hq : Tendsto q l (𝓝[>] (0 : ℝ)))
    (herror : Tendsto error l (𝓝 0))
    (hlower : ∀ᶠ t in l, q t ^ (-A) * (E + error t) ≤ ‖v t‖)
    (hcontrol : ∀ᶠ t in l, ‖v t‖ ≤ C * quantity t) :
    Tendsto quantity l atTop := by
  have hdiv : Tendsto (fun t => ‖v t‖ / C) l atTop := by
    simpa only [div_eq_mul_inv] using
      (norm_tendsto_atTop_of_profile_lower_bound hA hE hq herror hlower).atTop_mul_const
        (inv_pos.mpr hC)
  apply tendsto_atTop_mono' l _ hdiv
  filter_upwards [hcontrol] with t ht
  exact (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using ht)

/-- Arbitrarily large velocities occur in every left neighborhood of the
singular time, expressed without limit or boundedness notation. -/
theorem arbitrarily_large_near_time {V : Type*} [NormedAddCommGroup V]
    {v : ℝ → V} {error : ℝ → ℝ} {T A E : ℝ}
    (hA : 0 < A) (hE : 0 < E)
    (herror : Tendsto error (𝓝[<] T) (𝓝 0))
    (hlower : ∀ᶠ t in 𝓝[<] T, (T - t) ^ (-A) * (E + error t) ≤ ‖v t‖)
    (δ : ℝ) (hδ : 0 < δ) (M : ℝ) :
    ∃ t : ℝ, T - δ < t ∧ t < T ∧ M < ‖v t‖ := by
  have hlarge := (norm_tendsto_atTop_of_profile_lower_bound
    hA hE (remaining_time_tendsto T) herror hlower).eventually_gt_atTop M
  have hinterval : Ioo (T - δ) T ∈ 𝓝[<] T := Ioo_mem_nhdsLT (by linarith)
  obtain ⟨t, hbig, ht⟩ := (hlarge.and hinterval).exists
  exact ⟨t, ht.1, ht.2, hbig⟩

/-- The manuscript's radial sampling curve reaches the singular spacetime
point. The zero axial coordinate is suppressed from this pair. -/
theorem concentrating_path_tendsto (T X : ℝ) :
    Tendsto (fun t : ℝ => (t, Real.sqrt (2 * X * (T - t))))
      (𝓝[<] T) (𝓝 (T, (0 : ℝ))) := by
  have htime : Tendsto (fun t : ℝ => t) (𝓝[<] T) (𝓝 T) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hscale : Tendsto (fun t : ℝ => 2 * X * (T - t)) (𝓝[<] T) (𝓝 0) := by
    simpa only [mul_zero] using
      ((remaining_time_tendsto T).mono_right nhdsWithin_le_nhds).const_mul (2 * X)
  have hradius : Tendsto (fun t : ℝ => Real.sqrt (2 * X * (T - t)))
      (𝓝[<] T) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using hscale.sqrt
  exact htime.prodMk_nhds hradius

/-- A field satisfying the profile lower bound along the explicit shrinking
radial curve is discontinuous at the terminal spacetime point. -/
theorem not_continuousAt_concentrating_profile {V : Type*}
    [NormedAddCommGroup V] {T X A E : ℝ} {error : ℝ → ℝ}
    {field : ℝ × ℝ → V} (hA : 0 < A) (hE : 0 < E)
    (herror : Tendsto error (𝓝[<] T) (𝓝 0))
    (hlower : ∀ᶠ t in 𝓝[<] T,
      (T - t) ^ (-A) * (E + error t) ≤
        ‖field (t, Real.sqrt (2 * X * (T - t)))‖) :
    ¬ ContinuousAt field (T, (0 : ℝ)) := by
  intro hcontinuous
  apply no_continuous_extension_of_profile hA hE (remaining_time_tendsto T)
    herror hlower (concentrating_path_tendsto T X)
  exact ⟨field, hcontinuous, Filter.Eventually.of_forall (fun _ => rfl)⟩

end NavierStokes.BlowupImplication
