/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.DomainOfHolomorphy
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.HolomorphicConvexity.BoundaryDistance
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.PolydiscTaylor
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.PowerSeriesConvergence.Analytic

/-!
# Thullen's lemma and the boundary distance of holomorphic hulls

Cauchy bounds on compact families of smaller balls control Taylor coefficients weighted by
powers of a scalar holomorphic radius. These bounds transfer to the holomorphic hull, for
Banach-valued functions by norming functionals, and give Taylor continuation on the indicated
polydisc. Agreement is asserted near the center, not on unrelated components of the overlap.
This proves radius preservation, exact hull boundary distance, and holomorphic convexity for
domains of holomorphy.

References: [Scheidemann][Scheidemann2005] §6.2 and §7.3; [Hörmander][Hormander1973] §2.5;
[Korevaar–Wiegerinck][KorevaarWiegerinck2017] §6.4.

## Main results

`taylor_continuation_on_holomorphicHull` is Thullen's Taylor continuation lemma for
Banach-valued functions. `IsDomainOfHolomorphy.holomorphic_radius_bound` is the weighted radius
bound. `IsDomainOfHolomorphy.hasHolomorphicHullRadiusProperty` and
`hasHolomorphicHullDistanceProperty` are the hull-radius and boundary-distance forms.
`IsDomainOfHolomorphy.isHolomorphicallyConvex` is the forward Cartan–Thullen implication.

## References

* [L. Hörmander, *An Introduction to Complex Analysis in Several Variables*][Hormander1973]
* [J. Korevaar and J. Wiegerinck, *Several Complex Variables*][KorevaarWiegerinck2017]
* [V. Scheidemann, *Introduction to Complex Analysis in Several Variables*][Scheidemann2005]
-/

public noncomputable section

open Set Filter Metric
open scoped Topology ENNReal Pointwise

namespace SeveralComplexVariables

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Mixed derivative bounds transfer to the holomorphic hull of the set on which they hold, for
Banach-valued functions. This elementary step is independent of the Taylor continuation theorem. -/
theorem norm_multiIndexDeriv_le_on_holomorphicHull {U K : Set (Fin n → ℂ)}
    (ho : IsOpen U) {f : (Fin n → ℂ) → F} (hf : AnalyticOnNhd ℂ f U)
    (m : Fin n → ℕ) {M : ℝ} (hM : ∀ z ∈ K, ‖multiIndexDeriv m f z‖ ≤ M) :
    ∀ z ∈ holomorphicHull U K, ‖multiIndexDeriv m f z‖ ≤ M :=
  norm_le_on_holomorphicHull_vector (hf.iteratedPartialDeriv ho (multiIndexList m)) hM

/-- The Taylor sum of a Banach-valued function centered at an arbitrary point, using the normalized
multivariate Taylor coefficients. -/
@[expose] def taylorSumAt (f : (Fin n → ℂ) → F) (a z : Fin n → ℂ) : F :=
  powerSeriesSum (holomorphicTaylorSeries f a) (z - a)

omit [CompleteSpace F] in
/-- Separate analyticity on a closed polydisc from joint analyticity. -/
theorem analyticAt_update_of_analyticOnNhd_closedPolydisc {f : (Fin n → ℂ) → F}
    {a : Fin n → ℂ} {r : ℝ} (hA : AnalyticOnNhd ℂ f (closedPolydisc a (fun _ => r))) :
    ∀ z ∈ closedPolydisc a (fun _ => r), ∀ i,
      AnalyticAt ℂ (fun v => f (Function.update z i v)) (z i) := by
  intro z hz i
  exact hA.analyticAt_update hz i

/-- A bound on a closed coordinate ball bounds each normalized Taylor coefficient. -/
theorem norm_taylorCoeff_le {U : Set (Fin n → ℂ)}
    {f : (Fin n → ℂ) → F} (hf : AnalyticOnNhd ℂ f U)
    {a : Fin n → ℂ} {r M : ℝ} (hr : 0 < r) (hball : closedBall a r ⊆ U)
    (hM : ∀ z ∈ closedBall a r, ‖f z‖ ≤ M) (m : Fin n →₀ ℕ) :
    ‖holomorphicTaylorSeries f a m‖ ≤ M * ∏ i, r⁻¹ ^ m i := by
  have he : closedPolydisc a (fun _ => r) = closedBall a r := by
    rw [closedPolydisc_eq_closedBall hr.le]
  have hA : AnalyticOnNhd ℂ f (closedPolydisc a (fun _ => r)) :=
    hf.mono (he ▸ hball)
  rw [coeff_holomorphicTaylorSeries (fun _ => hr) hA.continuousOn
    (analyticAt_update_of_analyticOnNhd_closedPolydisc hA)]
  exact norm_polydiscCauchyCoeffWithRadii_le (fun _ => hr) (he ▸ hM) m

/-- The normalized Taylor sum of an analytic germ agrees with its representative nearby. -/
theorem taylorSumAt_eventuallyEq {f : (Fin n → ℂ) → F} {a : Fin n → ℂ}
    (hf : AnalyticAt ℂ f a) : taylorSumAt f a =ᶠ[𝓝 a] f := by
  classical
  have hb := hf.continuousAt.norm.eventually_lt_const
    (show ‖f a‖ < ‖f a‖ + 1 by linarith)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hf.eventually_analyticAt.and hb)
  have hr₂ : 0 < r / 2 := half_pos hr
  have hsub : closedPolydisc a (fun _ => r / 2) ⊆ ball a r := by
    rw [closedPolydisc_eq_closedBall hr₂.le]
    exact closedBall_subset_ball (half_lt_self hr)
  have hA : AnalyticOnNhd ℂ f (closedPolydisc a (fun _ => r / 2)) :=
    fun z hz => (hball (hsub hz)).1
  have hs := analyticAt_update_of_analyticOnNhd_closedPolydisc hA
  filter_upwards [ball_mem_nhds a hr₂] with z hz
  have hh : ∀ i, ‖(z - a) i‖ < r / 2 := fun i =>
    (norm_le_pi_norm (z - a) i).trans_lt (by simpa only [mem_ball, dist_eq_norm] using hz)
  have hsum := hasSum_polydiscTaylor (fun _ => hr₂) hh hA.continuousOn hs
    (fun z hz => (hball (hsub hz)).2.le)
  have hc (m : Fin n →₀ ℕ) :
      polydiscCauchyCoeffWithRadii f a (fun _ => r / 2) (Finsupp.equivFunOnFinite m) =
        holomorphicTaylorSeries f a m :=
    (coeff_holomorphicTaylorSeries (fun _ => hr₂) hA.continuousOn hs m).symm
  have H := (Finsupp.equivFunOnFinite.hasSum_iff).mpr hsum
  simpa only [taylorSumAt, powerSeriesSum, Pi.sub_apply, hc,
    add_sub_cancel, Function.comp_apply, Finsupp.equivFunOnFinite_apply] using H.tsum_eq

/-- Shrinking a continuous radius on a compact set gives uniform weighted Cauchy bounds. -/
private theorem exists_bound_taylorCoeff_mul_radius {U K : Set (Fin n → ℂ)}
    (hK : IsCompact K) (hKU : K ⊆ U)
    {q : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) → F} (hq : AnalyticOnNhd ℂ q U)
    (hf : AnalyticOnNhd ℂ f U)
    (hr : ∀ w ∈ K, ball w ‖q w‖ ⊆ U) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (m : Fin n →₀ ℕ) w, w ∈ K →
      ‖holomorphicTaylorSeries f w m‖ * (t * ‖q w‖) ^ (∑ i, m i) ≤ M := by
  classical
  let T := (fun p : (Fin n → ℂ) × (Fin n → ℂ) => p.1 + ((t : ℂ) * q p.1) • p.2) ''
    (K ×ˢ closedBall 0 1)
  have hTc : IsCompact T := (hK.prod (isCompact_closedBall _ _)).image_of_continuousOn
    (continuous_fst.continuousOn.add ((continuousOn_const.mul
      (hq.continuousOn.comp continuous_fst.continuousOn (fun _ h => hKU h.1))).smul
        continuous_snd.continuousOn))
  have hTU : T ⊆ U := by
    rintro _ ⟨⟨w, v⟩, ⟨hw, hv⟩, rfl⟩
    by_cases hq0 : q w = 0
    · simpa [hq0] using hKU hw
    apply hr w hw
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_mul,
      Complex.norm_of_nonneg ht.le]
    have hv' : ‖v‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hv
    calc
      t * ‖q w‖ * ‖v‖ ≤ t * ‖q w‖ * 1 := mul_le_mul_of_nonneg_left hv' (by positivity)
      _ < ‖q w‖ := by nlinarith [norm_pos_iff.mpr hq0]
  have hballT (w) (hw : w ∈ K) : closedBall w (t * ‖q w‖) ⊆ T := by
    intro z hz
    have hz' : z - w ∈ ((t : ℂ) * q w) • closedBall (0 : Fin n → ℂ) 1 := by
      rw [smul_unitClosedBall, norm_mul, Complex.norm_of_nonneg ht.le]
      simpa only [mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero] using hz
    obtain ⟨v, hv, he⟩ := hz'
    dsimp only at he
    exact ⟨(w, v), ⟨hw, hv⟩, by dsimp; rw [he]; abel⟩
  obtain ⟨M, hM⟩ := hTc.exists_bound_of_continuousOn (hf.continuousOn.mono hTU)
  refine ⟨max M 0, le_max_right _ _, fun m w hw => ?_⟩
  by_cases hq0 : q w = 0
  · by_cases hm : m = 0
    · subst m
      simpa [holomorphicTaylorSeries, multiIndexDeriv, multiIndexList, iteratedPartialDeriv]
        using (hM w (hballT w hw (mem_closedBall_self (by positivity)))).trans (le_max_left M 0)
    · have hmpos : 0 < ∑ i, m i := by
        obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hm
        exact (Nat.pos_of_ne_zero hi).trans_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ i))
      simp [hq0, zero_pow hmpos.ne']
  · have hR : 0 < t * ‖q w‖ := mul_pos ht (norm_pos_iff.mpr hq0)
    have hb := norm_taylorCoeff_le hf hR ((hballT w hw).trans hTU)
      (fun z hz => hM z (hballT w hw hz)) m
    have hp : (∏ i, (t * ‖q w‖)⁻¹ ^ m i) * (t * ‖q w‖) ^ (∑ i, m i) = 1 := by
      rw [Finset.prod_pow_eq_pow_sum, ← mul_pow, inv_mul_cancel₀ hR.ne', one_pow]
    calc
      _ ≤ (M * ∏ i, (t * ‖q w‖)⁻¹ ^ m i) * (t * ‖q w‖) ^ (∑ i, m i) := by
        gcongr
      _ = M := by rw [mul_assoc, hp, mul_one]
      _ ≤ max M 0 := le_max_left _ _

/-- **Thullen's lemma, with a holomorphic radius bound.** For a Banach-valued function,
the Taylor series centered at a hull point converges locally uniformly on the indicated
polydisc and continues the original germ. The proof transfers uniform weighted Cauchy bounds
from compact families of smaller balls to the hull, then compares with a product of geometric
series. -/
theorem taylor_continuation_on_holomorphicHull {U K : Set (Fin n → ℂ)}
    (ho : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {q : (Fin n → ℂ) → ℂ} {f : (Fin n → ℂ) → F} (hq : AnalyticOnNhd ℂ q U)
    (hf : AnalyticOnNhd ℂ f U)
    (hr : ∀ w ∈ K, ball w ‖q w‖ ⊆ U) {a : Fin n → ℂ} (ha : a ∈ holomorphicHull U K) :
    AnalyticOnNhd ℂ (taylorSumAt f a) (ball a ‖q a‖) ∧
      taylorSumAt f a =ᶠ[𝓝 a] f ∧
      HasSumLocallyUniformlyOn
        (fun (m : Fin n →₀ ℕ) z => (∏ i, (z i - a i) ^ m i) • holomorphicTaylorSeries f a m)
        (taylorSumAt f a) (ball a ‖q a‖) := by
  classical
  have hbound {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
      ∃ M : ℝ, 0 ≤ M ∧ ∀ m : Fin n →₀ ℕ,
        ‖holomorphicTaylorSeries f a m‖ * (t * ‖q a‖) ^ (∑ i, m i) ≤ M := by
    obtain ⟨M, hM0, hM⟩ := exists_bound_taylorCoeff_mul_radius hK hKU hq hf hr ht ht1
    refine ⟨M, hM0, fun m => ?_⟩
    have hg : AnalyticOnNhd ℂ
        (fun w => ((t : ℂ) * q w) ^ (∑ i, m i) • holomorphicTaylorSeries f w m) U :=
      ((analyticOnNhd_const.mul hq).pow _).smul
        (analyticOnNhd_const.smul (hf.iteratedPartialDeriv ho (multiIndexList m)))
    have hnorm (w) :
        ‖((t : ℂ) * q w) ^ (∑ i, m i) • holomorphicTaylorSeries f w m‖ =
          ‖holomorphicTaylorSeries f w m‖ * (t * ‖q w‖) ^ (∑ i, m i) := by
      rw [norm_smul, norm_pow, norm_mul, Complex.norm_of_nonneg ht.le, mul_comm]
    exact (hnorm a) ▸ norm_le_on_holomorphicHull_vector hg
      (fun w hw => (hnorm w).symm ▸ hM m w hw) a ha
  have habs : ball (0 : Fin n → ℂ) ‖q a‖ ⊆
      powerSeriesAbsConvergenceSet (holomorphicTaylorSeries f a) := by
    intro z hz
    have hzq : ‖z‖ < ‖q a‖ := by simpa only [mem_ball, dist_zero_right] using hz
    obtain ⟨r, hzr, hrq⟩ := exists_between hzq
    have hr0 : 0 < r := (norm_nonneg z).trans_lt hzr
    have hq0 : 0 < ‖q a‖ := hr0.trans hrq
    obtain ⟨M, hM0, hM⟩ := hbound (div_pos hr0 hq0) ((div_lt_one hq0).mpr hrq)
    simp only [div_mul_cancel₀ _ hq0.ne'] at hM
    have hratio : ‖‖z‖ / r‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg _) hr0.le)]
      exact (div_lt_one hr0).mpr hzr
    have hsum := ((hasSum_pi_geometric (fun _ : Fin n => ‖z‖ / r)
      (fun _ => hratio)).summable.mul_left M).comp_injective Finsupp.equivFunOnFinite.injective
    apply hsum.of_nonneg_of_le (fun _ => by positivity)
    intro m
    calc
      ‖holomorphicTaylorSeries f a m‖ * ∏ i, ‖z i‖ ^ m i ≤
          ‖holomorphicTaylorSeries f a m‖ * ∏ i, ‖z‖ ^ m i := by
        gcongr
        exact norm_le_pi_norm z _
      _ = (‖holomorphicTaylorSeries f a m‖ * r ^ (∑ i, m i)) *
          ∏ i, (‖z‖ / r) ^ m i := by
        rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, div_pow]
        field_simp
      _ ≤ M * ∏ i, (‖z‖ / r) ^ m i := by
        apply mul_le_mul_of_nonneg_right (hM m)
        positivity
  have hdom : ball (0 : Fin n → ℂ) ‖q a‖ ⊆
      powerSeriesConvergenceDomain (holomorphicTaylorSeries f a) :=
    isOpen_ball.subset_interior_iff.mpr habs
  have hmaps : MapsTo (fun z => z - a) (ball a ‖q a‖)
      (powerSeriesConvergenceDomain (holomorphicTaylorSeries f a)) := by
    intro z hz
    apply hdom
    simpa only [mem_ball, dist_zero_right, dist_eq_norm, sub_zero] using hz
  refine ⟨(analyticOnNhd_powerSeriesSum _).comp
    (analyticOnNhd_id.sub analyticOnNhd_const) hmaps,
    taylorSumAt_eventuallyEq (hf a ha.1), ?_⟩
  have hs := (hasSumLocallyUniformlyOn_powerSeries (holomorphicTaylorSeries f a)).comp
    (fun z => z - a) hmaps (continuous_id.sub continuous_const).continuousOn
  unfold taylorSumAt
  simpa only [HasSumLocallyUniformlyOn, Function.comp_def, Pi.sub_apply,
    Finset.sum_apply] using hs

/-- The constant-radius form of Thullen's continuation lemma, for Banach-valued functions. -/
theorem exists_continuation_ball_of_mem_holomorphicHull {U K : Set (Fin n → ℂ)}
    (ho : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) {r : ℝ} (hr : 0 < r)
    (hball : ∀ w ∈ K, ball w r ⊆ U) {a : Fin n → ℂ} (ha : a ∈ holomorphicHull U K)
    {f : (Fin n → ℂ) → F} (hf : AnalyticOnNhd ℂ f U) :
    ∃ g : (Fin n → ℂ) → F, AnalyticOnNhd ℂ g (ball a r) ∧ g =ᶠ[𝓝 a] f := by
  have hnorm : ‖(r : ℂ)‖ = r := Complex.norm_of_nonneg hr.le
  have h := taylor_continuation_on_holomorphicHull ho hK hKU
    (q := fun _ => (r : ℂ)) analyticOnNhd_const hf (by simpa only [hnorm] using hball) ha
  exact ⟨taylorSumAt f a, by simpa only [hnorm] using h.1, h.2.1⟩

/-- On a domain of holomorphy, a ball supporting continuation of every germ at its center must lie
in the domain. The overlap is chosen uniformly, independently of the function. -/
theorem IsDomainOfHolomorphy.ball_subset_of_continuation {U : Set (Fin n → ℂ)}
    (hU : IsDomainOfHolomorphy U) (ho : IsOpen U) {a : Fin n → ℂ} (ha : a ∈ U)
    {r : ℝ} (hr : 0 < r)
    (he : ∀ f : (Fin n → ℂ) → ℂ, AnalyticOnNhd ℂ f U →
      ∃ g, AnalyticOnNhd ℂ g (ball a r) ∧ g =ᶠ[𝓝 a] f) : ball a r ⊆ U := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp ho a ha
  let W := ball a (min ε r)
  have haW : a ∈ W := mem_ball_self (lt_min hε hr)
  have hWU : W ⊆ U := (ball_subset_ball (min_le_left _ _)).trans hεU
  have hWV : W ⊆ ball a r := ball_subset_ball (min_le_right _ _)
  apply hU (ball a r) W isOpen_ball (isConnected_ball hr) isOpen_ball ⟨a, haW⟩ hWU hWV
  intro f hf
  obtain ⟨g, hg, heq⟩ := he f hf
  exact ⟨g, hg, (hg.mono hWV).eqOn_of_preconnected_of_eventuallyEq
    (hf.mono hWU) isPreconnected_ball haW heq⟩

/-- A domain of holomorphy preserves every radius bound supplied by a holomorphic function on a
compact set, by Thullen's continuation lemma. -/
theorem IsDomainOfHolomorphy.holomorphic_radius_bound {U K : Set (Fin n → ℂ)}
    (hU : IsDomainOfHolomorphy U) (ho : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {q : (Fin n → ℂ) → ℂ} (hq : AnalyticOnNhd ℂ q U)
    (hr : ∀ w ∈ K, ball w ‖q w‖ ⊆ U) :
    ∀ a ∈ holomorphicHull U K, ball a ‖q a‖ ⊆ U := by
  intro a ha
  by_cases hqa : ‖q a‖ = 0
  · simp [hqa]
  · apply hU.ball_subset_of_continuation ho ha.1 (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hqa))
    intro f hf
    have h := taylor_continuation_on_holomorphicHull ho hK hKU hq hf hr ha
    exact ⟨taylorSumAt f a, h.1, h.2.1⟩

/-- Domains of holomorphy preserve uniform polydisc radii on compact hulls. -/
theorem IsDomainOfHolomorphy.hasHolomorphicHullRadiusProperty {U : Set (Fin n → ℂ)}
    (hU : IsDomainOfHolomorphy U) (ho : IsOpen U) : HasHolomorphicHullRadiusProperty U := by
  intro K hK hKU r hr hball a ha
  exact hU.ball_subset_of_continuation ho ha.1 hr fun _ hf =>
    exists_continuation_ball_of_mem_holomorphicHull ho hK hKU hr hball ha hf

/-- The boundary distance of a compact holomorphic hull equals that of the original compact set in a
domain of holomorphy. -/
theorem IsDomainOfHolomorphy.hasHolomorphicHullDistanceProperty {U : Set (Fin n → ℂ)}
    (hU : IsDomainOfHolomorphy U) (ho : IsOpen U) : HasHolomorphicHullDistanceProperty U :=
  (hU.hasHolomorphicHullRadiusProperty ho).hasHolomorphicHullDistanceProperty

/-- **Cartan–Thullen, forward implication.** A domain of holomorphy is holomorphically
convex, by Thullen's Taylor continuation lemma and the hull-radius criterion. This coordinate
case supplies the proof for general finite-dimensional spaces below. -/
private theorem IsDomainOfHolomorphy.isHolomorphicallyConvex_fin {U : Set (Fin n → ℂ)}
    (hU : IsDomainOfHolomorphy U) (ho : IsOpen U) : IsHolomorphicallyConvex U :=
  (hU.hasHolomorphicHullRadiusProperty ho).isHolomorphicallyConvex ho

/-- **Cartan–Thullen, forward implication.** An open domain of holomorphy in any
finite-dimensional complex normed space is holomorphically convex. Linear transport of hull
compactness is used here; no invariance of numerical boundary distance is asserted. -/
theorem IsDomainOfHolomorphy.isHolomorphicallyConvex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {U : Set E} (hU : IsDomainOfHolomorphy U) (ho : IsOpen U) :
    IsHolomorphicallyConvex U := by
  let L := (Module.finBasis ℂ E).equivFunL
  have h := (hU.image_equiv L).isHolomorphicallyConvex_fin
    (L.toHomeomorph.isOpenMap U ho)
  simpa only [Set.image_image, Function.comp_def, L.symm_apply_apply, Set.image_id'] using
    h.image_equiv L.symm

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
