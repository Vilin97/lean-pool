/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.AnalyticGerm.Factorization

/-!
# Parameter germs and restriction to a fiber

Adding an unused scalar variable preserves irreducible germs. Consequently a nonzero parameter
germ is relatively prime to every germ whose restriction to the scalar fiber is nonzero. This is
the local algebra needed for persistence of relative primality.

## Main results

`basePullback` pulls a parameter germ back along projection, adding an unused scalar variable;
`fiberPullback` restricts a germ to the scalar fiber. `irreducible_basePullback` preserves
irreducibility. `isRelPrime_basePullback_of_fiber_ne_zero` is relative primality of a nonzero
parameter germ to a germ with nonzero fiber restriction. `eventually_fiber_ne_zero_ofAnalyticAt`
is persistence of a nonzero fiber germ.
-/

public noncomputable section

open Filter Set Metric
open scoped Topology

namespace SeveralComplexVariables.AnalyticGerm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Regard a parameter germ as a germ independent of the scalar variable. -/
@[expose] def basePullback (y : E × ℂ) : AnalyticGerm ℂ y.1 →ₐ[ℂ] AnalyticGerm ℂ y :=
  pullback Prod.fst analyticAt_fst

/-- Restrict a germ to the scalar fiber through its base point. -/
def fiberPullback (y : E × ℂ) : AnalyticGerm ℂ y →ₐ[ℂ] AnalyticGerm ℂ y.2 :=
  pullback (fun w : ℂ => (y.1, w)) (analyticAt_const.prod analyticAt_id)

/-- A parameter germ vanishing at its base point restricts to zero on the scalar fiber. -/
theorem fiberPullback_basePullback_eq_zero (y : E × ℂ) {p : AnalyticGerm ℂ y.1}
    (hp : ¬ IsUnit p) : fiberPullback y (basePullback y p) = 0 := by
  obtain ⟨g, hg, rfl⟩ := exists_rep p
  have h0 : g y.1 = 0 := by simpa only [isUnit_iff, eval_ofAnalyticAt, not_not] using hp
  change ofAnalyticAt (fun _ : ℂ => g y.1) analyticAt_const =
    ofAnalyticAt (0 : ℂ → ℂ) analyticAt_const
  apply ofAnalyticAt_eq_iff.mpr
  exact Filter.Eventually.of_forall (fun _ => h0)

/-- Adding an unused scalar variable preserves irreducibility of a parameter germ. -/
theorem irreducible_basePullback (y : E × ℂ) {p : AnalyticGerm ℂ y.1} (hp : Irreducible p) :
    Irreducible (basePullback y p) := by
  let s : AnalyticGerm ℂ y →ₐ[ℂ] AnalyticGerm ℂ y.1 :=
    pullback (fun z : E => (z, y.2)) (analyticAt_id.prod analyticAt_const)
  have hs (q : AnalyticGerm ℂ y.1) : s (basePullback y q) = q := by
    obtain ⟨g, hg, rfl⟩ := exists_rep q
    rfl
  refine ⟨fun hu => hp.not_isUnit ((isUnit_pullback_iff _ _ p).mp hu), ?_⟩
  intro a b hab
  have he : p = s a * s b := by rw [← hs p, hab, map_mul]
  have hu (q : AnalyticGerm ℂ y) : IsUnit (s q) ↔ IsUnit q := by
    simp only [s, isUnit_iff, eval_pullback]
  exact (hp.isUnit_or_isUnit he).imp (hu a).mp (hu b).mp

/-- A nonzero parameter germ is relatively prime to a germ nonzero on its scalar fiber. -/
theorem isRelPrime_basePullback_of_fiber_ne_zero [FiniteDimensional ℂ E]
    (y : E × ℂ) {p : AnalyticGerm ℂ y.1} (hp : p ≠ 0) {f : AnalyticGerm ℂ y}
    (hf : fiberPullback y f ≠ 0) : IsRelPrime (basePullback y p) f := by
  induction p using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact (hp rfl).elim
  | h₂ p hu => exact (hu.map (basePullback y)).isRelPrime_left
  | h₃ p q hp0 hq ih =>
    rw [map_mul]
    apply IsRelPrime.mul_left _ (ih hp0)
    apply (irreducible_basePullback y hq.irreducible).isRelPrime_iff_not_dvd.mpr
    intro hdiv
    have h := map_dvd (fiberPullback y) hdiv
    rw [fiberPullback_basePullback_eq_zero y hq.not_isUnit] at h
    exact hf (zero_dvd_iff.mp h)

/-- A represented analytic germ is nonzero exactly when the representative is not locally zero. -/
theorem ofAnalyticAt_ne_zero_iff {f : E → ℂ} {x : E} (hf : AnalyticAt ℂ f x) :
    ofAnalyticAt f hf ≠ 0 ↔ ¬ f =ᶠ[𝓝 x] 0 := by
  change ofAnalyticAt f hf ≠ ofAnalyticAt (0 : E → ℂ) analyticAt_const ↔ _
  exact not_congr ofAnalyticAt_eq_iff

/-- A nonzero analytic germ has nonzero germs at all sufficiently nearby points. -/
theorem eventually_ne_zero_ofAnalyticAt {f : E → ℂ} {x : E} (hf : AnalyticAt ℂ f x)
    (hne : ofAnalyticAt f hf ≠ 0) :
    ∀ᶠ y in 𝓝 x, ∃ hy : AnalyticAt ℂ f y, ofAnalyticAt f hy ≠ 0 := by
  obtain ⟨r, hr, hfr⟩ := hf.exists_ball_analyticOnNhd
  filter_upwards [ball_mem_nhds x hr] with y hy
  refine ⟨hfr y hy, ?_⟩
  rw [ofAnalyticAt_ne_zero_iff]
  intro hzero
  have he := hfr.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_ball hy hzero
  exact (ofAnalyticAt_ne_zero_iff hf).mp hne
    (Filter.mem_of_superset (ball_mem_nhds x hr) (fun z hz => he hz))

/-- Nonvanishing of the central fiber germ persists for nearby scalar fiber germs. -/
theorem eventually_fiber_ne_zero_ofAnalyticAt {f : E × ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hne : ¬ (fun w : ℂ => f (0, w)) =ᶠ[𝓝 0] 0) :
    ∀ᶠ y in 𝓝 (0 : E × ℂ), ∃ hy : AnalyticAt ℂ f y,
      fiberPullback y (ofAnalyticAt f hy) ≠ 0 := by
  obtain ⟨r, hr, hfr⟩ := hf.exists_ball_analyticOnNhd
  have hprod : AnalyticOnNhd ℂ f (ball (0 : E) r ×ˢ ball (0 : ℂ) r) := by
    simpa only [ball_prod_same, Prod.mk_zero_zero] using hfr
  obtain ⟨w, hw, hfw⟩ : ∃ w ∈ ball (0 : ℂ) r, f (0, w) ≠ 0 := by
    by_contra! h
    exact hne (Filter.mem_of_superset (ball_mem_nhds 0 hr) h)
  have hc : ContinuousAt (fun a : E => f (a, w)) 0 :=
    (hprod (0, w) ⟨mem_ball_self hr, hw⟩).continuousAt.comp_of_eq
      (continuousAt_id.prodMk continuousAt_const) rfl
  have hb : ∀ᶠ y : E × ℂ in 𝓝 0, f (y.1, w) ≠ 0 :=
    (continuous_fst.continuousAt : Tendsto (Prod.fst : E × ℂ → E) (𝓝 0) (𝓝 0)).eventually
      (hc.eventually_ne hfw)
  filter_upwards [((isOpen_ball.prod isOpen_ball).mem_nhds
    (show (0 : E × ℂ) ∈ ball (0 : E) r ×ˢ ball (0 : ℂ) r from
      ⟨mem_ball_self hr, mem_ball_self hr⟩)), hb] with y hy hfyw
  refine ⟨hprod y hy, ?_⟩
  have hslice : AnalyticOnNhd ℂ (fun t : ℂ => f (y.1, t)) (ball 0 r) := by
    intro t ht
    exact (hprod (y.1, t) ⟨hy.1, ht⟩).comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  change ofAnalyticAt (fun t : ℂ => f (y.1, t)) (hslice y.2 hy.2) ≠ 0
  rw [ofAnalyticAt_ne_zero_iff]
  intro hzero
  exact hfyw (hslice.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_ball hy.2 hzero hw)

end SeveralComplexVariables.AnalyticGerm

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
